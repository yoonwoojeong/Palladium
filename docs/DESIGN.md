# Palladium — design

Palladium is an independent type checker ("kernel") for Lean 4, built for the
[Lean Kernel Arena](https://arena.lean-lang.org). Input: one export file in the
`lean4export` NDJSON format (v3.x). Output: exit code `0` (every declaration is
valid), `1` (some declaration is invalid), `2` (declined), anything else = internal error.

Priorities, in order: **soundness** (never accept an invalid file), **completeness**
on files the official kernel accepts, **speed**, small trusted base.

Rust, edition 2021, **zero external crates** (own JSON reader, own bignum, own hash tables
where it matters). No `unsafe` in the checking core.

## 1. Principles (where Palladium deliberately differs)

P1. **Terms are hash-consed and binder names / binder info are erased.** Alpha-equivalent
    terms have the same `TermId`; syntactic equality is integer equality.

P2. **Canonical typed locals instead of fresh free variables.** Other kernels open a binder
    with a *fresh* fvar (unique id + mutable local context). Then every cache entry about an
    open term is tied to one traversal and identical work under the same binder is redone.
    Palladium opens a binder `λ x:A. b` (a closed-under-bvars term `t`) with the local
    `Local(d, A)` where `d = local_ub(t)` = 1 + the largest depth of any local occurring in
    `t` (0 if none). A local's identity is the pair *(depth, type)*, interned.
    Consequences:
    * A term carries its whole typing context (each local carries its type; invariant
      **L**: `local_ub(type of Local(d,_)) <= d`, asserted in `mk_local`).
      So `infer`, `whnf`, `is_def_eq` are *pure functions of term ids*: there is no local
      context, no depth counter, and every cache is valid for the lifetime of the store.
    * Opening the same binder twice yields the same term, so caches hit across traversals.
    * Freshness: `d >= local_ub(t)` so the new local does not occur in `t`; by invariant L
      it does not occur in the type of any local of `t` either, so abstracting it again is exact.
      When comparing two binders the depth is `max(local_ub(t), local_ub(s))`.
    * Soundness note: a cache keyed on an open term that ignored the types of its variables
      would be unsound (arena test `bugs/open-term-cache-context`); here the types are part
      of the key by construction.

P3. **No let-locals.** `let x:A := v; b` is typed by checking `v : A` and inferring
    `b[v/x]`; hash-consing keeps the DAG small.

P4. **All terms the checker handles at top level are closed** w.r.t. bound variables
    (`lbr == 0`). Hence substitution never needs lifting, and a loose bvar met by `infer`
    is a rejection.

P5. **Universe levels are simplified on construction and compared by a complete decision
    procedure** (§4), not by an incomplete normal form.

P6. **Declarations are checked in parallel.** The whole file is loaded first; then worker
    threads take declarations from a shared counter. A declaration at file position `p` may
    only refer to constants at positions `< p` (plus members of its own inductive block where
    the rules say so). Any reference to a later or missing constant is a rejection. This keeps
    the dependency relation well-founded, so "assume every earlier declaration is valid;
    accept iff every declaration passes" is sound.

P7. **Nothing in the export is trusted.** Recursors, recursor rules, `k`, `numFields`,
    `isRec`, `numNested`, `cidx`, … are all re-derived from the inductive types and
    constructor types and compared with the file. Another thread may *use* the file's copy
    before the owner has validated it; that is fine because a mismatch rejects the whole file
    (and `exit(1)` is immediate). The checker must stay memory-safe and must not hang
    silently on garbage data: recursion depth is counted and overflow is a `Fault`.

P8. Each worker owns a private `Store` (terms, levels, caches). File expressions live in a
    compact shared read-only table and are *imported* into a store on demand.

## 2. Crate layout

```
src/lib.rs        mod declarations
src/bignat.rs     arbitrary precision naturals                      (no deps on other modules)
src/json.rs       minimal JSON pull reader over &[u8]
src/parse.rs      NDJSON export -> RawEnv
src/env.rs        RawEnv, Env (constant table), data types shared by all
src/store.rs      Store: hash-consed terms + levels + substitution
src/level.rs      level simplification, leq/eq, param instantiation (methods on Store)
src/tc.rs         Checker: import, infer, whnf, is_def_eq, declaration checking
src/inductive.rs  inductive blocks: checks + recursor generation + comparison with file
src/quot.rs       the Quot declarations
src/main.rs       CLI, worker threads, exit codes
```

## 3. Shared data (`env.rs`)

```rust
pub type NameId = u32;   // canonical: equal names <=> equal ids. 0 = anonymous
pub type RawExpr = u32;  // index into RawEnv.exprs
pub type RawLevel = u32; // index into RawEnv.levels; 0 = zero
pub enum RawLevelNode { Zero, Succ(RawLevel), Max(RawLevel,RawLevel), IMax(RawLevel,RawLevel), Param(NameId) }
#[repr(u8)] pub enum RawTag { BVar, Sort, Const, App, Lam, Pi, Let, Proj, Nat, Str }
#[derive(Clone,Copy)] pub struct RawNode { pub tag: RawTag, pub a: u32, pub b: u32, pub c: u32 } // 16 bytes
// BVar: a = index (saturate at u32::MAX)      Sort: a = RawLevel
// Const: a = NameId, b = offset into RawEnv.const_levels, c = number of levels
// App: a = fn, b = arg      Lam/Pi: a = binder type, b = body
// Let: a = type, b = value, c = body          Proj: a = struct NameId, b = field index, c = expr
// Nat: a = index into RawEnv.nats             Str: a = index into RawEnv.strs (deduplicated)
// mdata nodes are transparent: the index of an mdata expr maps to its inner expr.
pub struct RawEnv { names, levels, exprs, const_levels, nats: Vec<BigNat>, strs: Vec<String>, decls: Vec<Decl>, ... }
```

`Decl` (one per declaration line, file order; index = *position*):
`Axiom | Def | Thm | Opaque | Quot | Inductive{types, ctors, recs}`, each carrying exactly the
fields of the format spec (names as `NameId`, exprs as `RawExpr`).

`Env` = `RawEnv` + `consts: Vec<Option<ConstInfo>>` indexed by `NameId`, where
`ConstInfo { pos: u32 (position of the declaring Decl), level_params: Vec<NameId>, ty: RawExpr, kind: ConstKind, is_unsafe: bool }`
and `ConstKind` = `Axiom | Def{value,hints} | Thm{value} | Opaque{value} | Quot(QuotKind) |
Induct(InductInfo) | Ctor(CtorInfo) | Rec(RecInfo)` with the file's fields.
A name declared twice anywhere in the file => reject. `Env` also pre-resolves the builtin
names (`Nat`, `Nat.zero`, `Nat.succ`, `Nat.add`, …, `Bool.true`, `String`, `String.ofList`,
`Char.ofNat`, `List.cons`, `List.nil`, `Char`, `Quot*`, `Eq`, `eagerReduce`) to `Option<NameId>`.

Parser rules: names are canonicalised by interning `(prefix, component)`; indices `in`/`il`/`ie`
are arbitrary non-negative integers (sparse, out of order allowed) but an item may only refer
to items defined on earlier lines (else reject). Fast path: indices dense and ascending.
Unknown top-level key or unsupported format major version => decline (exit 2).
Malformed JSON or dangling reference => reject (exit 1).

## 4. Store (`store.rs`, `level.rs`)

```rust
pub type TermId = u32; pub type LevelId = u32; pub type LocalId = u32; pub type LevelsId = u32; pub type NatId = u32;
pub enum Term { BVar(u32), Local(LocalId), Sort(LevelId), Const(NameId, LevelsId), App(TermId,TermId),
                Lam(TermId,TermId), Pi(TermId,TermId), Let(TermId,TermId,TermId), Proj(NameId,u32,TermId),
                Nat(NatId), Str(u32) }
```
Per node metadata, computed at construction: `lbr` (loose bvar range: 0 = closed),
`local_ub` (0 = no locals), `has_param` (mentions a universe parameter).
API (all `&mut self` on `Store`): `mk_*` (hash-consing), `get(TermId) -> Term`, `lbr`, `local_ub`,
`has_param`, `mk_local(depth, ty) -> TermId` (interned on `(depth, ty)`), `local_type(LocalId)`,
`mk_app_n(f, &[args])`, `unfold_app(t, &mut Vec<TermId>) -> head`,
`instantiate(t, xs)` — loose bvar `i` of `t` becomes `xs[xs.len()-1-i]` (so `xs` is in binder
order, outermost first), bvars `>= xs.len()` are lowered; all `xs` must be closed —
`abstract_locals(t, locals: &[TermId])` — inverse: `locals[j]` becomes bvar `n-1-j` (+ binder depth) —
`subst_params(t, params: &[NameId], levels: LevelsId)`. Every traversal is memoised on
`(TermId, binder offset)` and pruned with `lbr` / `local_ub` / `has_param`.

Levels: `Zero | Succ(l) | Max(a,b) | IMax(a,b) | Param(NameId)`, hash-consed, with smart constructors:
`max(a,a)=a`, `max(0,a)=a`, `max` of `succ^m x` and `succ^n x` = the larger, operands ordered by id;
`imax(a,b)`: `b` zero → zero; `b` never zero (`Succ`, or `Max` with a never-zero side, or `IMax` with
never-zero right) → `max(a,b)`; `a` zero → `b`; `a==b` → `a`.
Semantics: a level denotes a function from assignments (params → ℕ) to ℕ, `imax a b = 0 if b = 0 else max a b`.
`leq(a,b)` must hold iff `a <= b` under **every** assignment. Procedure (sound and complete):
1. If either side contains `IMax(_, v)`: rewrite `imax(u, max(v,w)) = max(imax(u,v), imax(u,w))`,
   `imax(u, imax(v,w)) = max(imax(u,w), imax(v,w))` until some `imax(u, Param p)` is exposed; then
   case-split: both `leq(a[p:=0], b[p:=0])` and `leq(a[p:=succ p], b[p:=succ p])` must hold.
2. Otherwise (imax-free) decide `a <= b + k` (k an integer, start 0): `a = max(x,y)` → both;
   `a = succ x` → `x <= b + (k-1)`; `b = succ y` → `a <= y + (k+1)`; `a = 0` → evaluate: true iff
   `min(b) + k >= 0` where `min(b)` is `b` with all params 0; `a = Param p` → true iff `b` contains an
   atom `p + c` (p under `c` succs, through `max`) with `c + k >= 0`.
`level_eq(a,b) = a==b || (leq(a,b) && leq(b,a))`, cached. `is_zero(l) = level_eq(l, zero)`.
Regression tests: `bugs/level-imax-leq`, `bugs/level-imax-normalization`, `bugs/large-elim-param`.

## 5. Checker (`tc.rs`)

`Checker { store, env: &Env, pos: u32, caches… }`. Results are `Result<T, Fail>` with
`Fail::Reject(String)` (the file is invalid) and `Fail::Fault(String)` (resource limit / internal).

*What is accepted* is Lean 4's type theory as implemented by the official kernel; the C++ sources
(`src/kernel/type_checker.cpp`, `inductive.cpp`, `quot.cpp`) are the conformance reference for
the reduction strategy (order of heuristics in `is_def_eq_core`, `lazy_delta_reduction_step`,
`whnf_core`, `reduce_nat`, unit-like and structure eta, `eagerReduce`, projection rules) because
real proofs are tuned to it. *How* it is computed follows §1: no local context, typed canonical
locals, telescopes opened in one pass, substitution of closed terms only.

Lookup rule (P6): `const_info(name)` rejects if the constant is missing, or `info.pos >= self.pos`
unless the checker is inside the inductive block at that position and has explicitly allowed it.
A constant used with the wrong number of universe arguments is a rejection in `infer`, and
"does not reduce" in `whnf`/`is_def_eq`. In checking mode a safe declaration that mentions an
`is_unsafe` (or `partial`) constant is rejected. Unsafe/partial declarations themselves are not checked.

Caches (all keyed by ids, never invalidated): `infer` (checked / infer-only), `whnf`, `whnf_core`,
def-eq successes (union-find), def-eq failures (pair set), instantiated constant types per `(name, levels)`.

Declarations:
* all: no duplicate universe parameter names; every `Param` in type/value is declared; the type
  has no loose bvars and `infer(type)` whnf's to a sort.
* def / opaque: `is_def_eq(infer(value), type)`. theorem: additionally the type's sort is `Prop`.
* quot: the four constants must be exactly `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` with their
  canonical types (built by hand, compared by id), and `Eq` must already be declared with the right shape.
* inductive: §6.

Nat/String literals: `infer` gives `Nat` / `String` (which must be declared before use). The literal
arithmetic extension is only enabled for a builtin whose declaration has the expected type; `Nat` must
be the inductive with constructors `zero : Nat`, `succ : Nat → Nat` in this order.

## 6. Inductive blocks (`inductive.rs`)

Input: the file's block. Output: accept, or reject. Steps: (1) check the types (same universe
params, same parameters, result is a sort, all in one universe); (2) check constructors (parameters
agree, fields live in a small enough universe unless the block is in `Prop`, strict positivity,
result is the inductive applied to the parameters and to index terms free of the block's types);
(3) nested occurrences are translated to an auxiliary mutual block exactly like the reference
(`elim_nested_inductive`), checked, and translated back; (4) large elimination rule; (5) generate
recursor types, rules and `k`; (6) compare **every** field of every `types`/`ctors`/`recs` entry
of the file with the derived value (terms: same id, else `is_def_eq`); a recursor or constructor in
the block that the derivation does not produce is a rejection.

## 7. Driver (`main.rs`)

`palladium [-j N] [-q] <file | ->`. Load → build `Env` → spawn N workers with large stacks →
each loops `fetch_add` on the shared position counter and checks that declaration with a private
`Store` (reset when it grows past a threshold, between declarations only).
First `Reject` anywhere: print the reason to stderr, `exit(1)` immediately. `Fault`s and panics
(caught per declaration) are recorded; at the end: none → `exit(0)`, some → `exit(3)`.
