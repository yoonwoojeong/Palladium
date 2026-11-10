# Substitution-free evaluation and inference

Profiles show that eager substitution (`Store::instantiate`) dominates: ~60% of heavy reduction
(`decide` proofs) and it makes binder/let ladders quadratic. Two changes remove it from the hot
paths. Both are *observationally identical* to the substitution-based code they replace: the
same `TermId` comes back. That makes them testable against the old code as an oracle.

## Part A — the reduction machine (`src/machine.rs`)

A call-by-need Krivine machine over hash-consed terms. It replaces the bodies of `Checker::whnf`
and `Checker::whnf_core`; the old implementations are kept (renamed `whnf_subst`,
`whnf_core_subst`) as the oracle.

### Data (arenas owned by a `Machine` struct inside the `Checker`, reset after every top-level run)

```rust
type EnvId = u32;   // 0 = empty. envs[e] = (parent: EnvId, thunk: ThunkId); bvar 0 = newest
type ThunkId = u32; // thunks[t] = Thunk { term: TermId, env: EnvId, full: ValId|NONE, core: ValId|NONE, back: TermId|NONE }
type ValId = u32;   // vals[v] = Val { head: TermId, env: EnvId, args: (start,len) into val_args: Vec<ThunkId> }
```
* A thunk is a suspended term under an environment. A thunk whose term is closed (`lbr == 0`)
  always gets `env = 0`, and such thunks are interned per run (`TermId -> ThunkId`), so every
  closed subterm is evaluated at most once per run.
* A `Val` is a weak head normal form: `head` is never an `App`, never a `Let`, never a `BVar`
  (variables are looked up), and it is not a redex together with `args`.
* `back` memoises the read-back of the *unevaluated* thunk (below).

### `run(term, env, stack, mode) -> R<ValId>`  (iterative loop; `stack: Vec<ThunkId>`, top = next argument)

`mode`: `Full` (= `whnf`: delta + literal arithmetic), `Core` (= `whnf_core(_, false, false)`),
`CoreCheapProj` (= `whnf_core(_, false, true)`), plus the `cheap_rec` variants if the old code uses them.

| term | action |
|---|---|
| `App(f, a)` | push `thunk(a, env)`; continue with `f` (walk the whole spine in a loop) |
| `Lam(_, b)`, stack non-empty | pop `x`; `env = cons(env, x)`; continue with `b` |
| `Lam`, stack empty | return `Val{head: term, env, args: []}` |
| `Let(_, v, b)` | `env = cons(env, thunk(v, env))`; continue with `b` |
| `BVar(i)` | `th = env[i]`; `v = force(th, mode)`; continue with `(v.head, v.env, v.args ++ stack)` — re-dispatch, since more arguments may enable a rule |
| `Proj(S, i, e)` | force `thunk(e, env)` with the sub-mode the reference prescribes (`Full`, or the cheap core mode under `cheap_proj`); string literal → constructor form; if the value is a constructor application of `S` with enough args: force that field thunk and continue with its value plus the stack; else stuck: `Val{head: term, env, args: stack}` |
| `Const(c, ls)` | recursor/quotient rule if applicable (major premise forced as the reference prescribes; rule rhs is a closed term → continue with `(rhs, env 0, new stack)`); else, in `Full` mode: literal arithmetic if `c` is a Nat builtin applied to exactly its arity (force the args in `Full` mode), else delta-unfold (`(value, env 0, stack)`); else stuck |
| `Local`, `Sort`, `Pi`, `Nat`, `Str` | return `Val{head: term, env, args: stack}` |

`force(th, mode)`: return the cached value for that mode or `run(th.term, th.env, [], mode)` and cache
it (`full` also answers `Core` requests only if the reference would produce the same result — it does
not in general, so keep the two slots separate). Before running a closed thunk in `Full`/`Core` mode,
consult the checker's global `whnf` / `whnf_core` caches (a cached term is decomposed into a `Val`).

Rules that need *terms* (K-like recursors: `to_cnstr_when_K`; structure eta on the major premise;
`is_prop`; anything calling `infer` / `is_def_eq`) read the relevant thunks back to terms and call the
existing `Checker` functions; a resulting term is turned into a `Val` by `run(term, 0, [], mode)`.

### Read-back
`readback_thunk(th) -> TermId` = the term `th.term` with every loose bvar `i` replaced by
`readback_thunk(env[i])` — i.e. the *unevaluated* substitution instance, exactly what eager
substitution would have built. Memoised in `th.back` and, within one read-back, per `(TermId, EnvId)`.
`readback_val(v)` = `mk_app_n(readback(head under v.env), args.map(readback_thunk))`.
Top level: `whnf(t) = readback_val(run(t, 0, [], Full))`, cached in the global cache as before.

Because arguments are read back unevaluated, the result is the same term the reference strategy
produces (weak head reduction is deterministic), so every other part of the checker is unaffected.

### Oracle
With `PALLADIUM_CHECK_MACHINE=1` every top-level `whnf`/`whnf_core` call also runs the `_subst`
implementation and panics with both terms printed if the `TermId`s differ.

## Part B — inference under an environment (`tc.rs`)

`infer` no longer opens binders by substituting into the body. A *context* is a stack of closed
terms `ctx: Vec<TermId>` (one per enclosing binder of the term being inferred: a `Local` for
`Lam`/`Pi` binders, the instantiated value for `Let`), with an interned id per prefix
(`CtxId`: `ctx_ids[(parent CtxId, TermId)]`), and `ctx_ub` = max `local_ub` of its entries.

`infer_ctx(t, check) -> R<TermId>` returns a **closed** type (it may mention the context's locals).
* `lbr(t) == 0` → the context is irrelevant: use the cache keyed by `t` alone.
* otherwise cache on `(t, CtxId)`.
* `BVar(i)` → `infer(ctx[len-1-i])` (a `Local` gives its type; a let value has been checked already).
* `App` → as before, but an argument is instantiated (`inst_ctx(a)`) only when the codomain really
  depends on it (`lbr(body) > 0`), and argument types come from `infer_ctx(a)`.
* `Lam(ty, b)` → `dom = inst_ctx(ty)`; (check: `ensure_sort(infer_ctx(ty))`);
  `x = mk_local(max(ctx_ub, local_ub(dom)), dom)`; push `x`; `B = infer_ctx(b)`; pop;
  result `Pi(dom, abstract_locals(B, [x]))`. `Pi` likewise → `Sort(imax(..))`.
* `Let(ty, v, b)` → check `ty`, `v : ty`; push `inst_ctx(v)`; `infer_ctx(b)`; pop. No abstraction.
* `Proj` → `infer(inst_ctx(t))` on the closed instance.
`inst_ctx(t)` = `t` with bvar `i` ↦ `ctx[len-1-i]`, memoised on `(t, CtxId)` across calls, `t` itself if closed.
Freshness: the new local's depth is ≥ `local_ub` of everything in the context and of its own type,
so it cannot collide with any local that can appear in the instantiated body (design P2, invariant L).

Oracle: `PALLADIUM_CHECK_INFER=1` compares against the old substitution-based `infer` up to
`is_def_eq` (ids may differ because the old code picked binder depths from the term alone).
