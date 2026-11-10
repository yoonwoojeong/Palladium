# Checker implementation notes (`tc.rs`, `inductive.rs`, `quot.rs`)

Read `DESIGN.md` first. This file fixes the API and explains how the *behaviour* of the
official kernel (the conformance reference, C++ files `type_checker.cpp`, `inductive.cpp`,
`inductive.h`, `quot.cpp`, `quot.h`) maps onto Palladium's architecture. Where this file and
the reference disagree on *what is accepted*, the reference wins unless marked **(stricter)**.

## 1. API (tc.rs)

```rust
pub enum Fail { Reject(String), Fault(String) }
pub type R<T> = Result<T, Fail>;

pub struct Checker<'e> {
    pub store: Store,
    pub env: &'e Env,
    pub pos: u32,                 // position of the declaration being checked
    pub allow_block: bool,        // inductive.rs: constants with info.pos == pos are visible
    pub safe_mode: bool,          // true while checking a safe declaration: unsafe constants are rejected by infer(check=true)
    pub eager_reduce: bool,
    depth: u32,                   // recursion depth counter; > MAX_DEPTH => Fail::Fault
    // caches, import memo tables ...
}
impl<'e> Checker<'e> {
    pub fn new(env: &'e Env) -> Self;
    pub fn reset(&mut self);                                  // clear store + all caches + import memos
    pub fn check_decl(&mut self, pos: u32) -> R<()>;          // dispatch on env.raw.decls[pos]
    // import of file data into the store (memoised per RawExpr / RawLevel)
    pub fn import_expr(&mut self, e: RawExpr) -> TermId;
    pub fn import_level(&mut self, l: RawLevel) -> LevelId;
    // constants
    pub fn const_info(&self, n: NameId) -> R<&'e ConstInfo>;  // position rule P6; Reject if missing / not yet visible
    pub fn const_info_opt(&self, n: NameId) -> Option<&'e ConstInfo>; // same visibility rule, None instead of Reject
    pub fn const_type(&mut self, n: NameId, ls: LevelsId) -> R<TermId>; // instantiated type, cached per (n, ls); Reject on arity mismatch
    // typing
    pub fn infer(&mut self, t: TermId, check: bool) -> R<TermId>;  // check=false is "infer only": assumes t well typed
    pub fn check(&mut self, t: TermId) -> R<TermId> { self.infer(t, true) }
    pub fn ensure_sort(&mut self, ty: TermId) -> R<LevelId>;  // whnf(ty) must be Sort l
    pub fn ensure_pi(&mut self, ty: TermId) -> R<(TermId, TermId)>; // whnf(ty) must be Pi(dom, body)
    pub fn is_prop(&mut self, ty: TermId) -> R<bool>;         // whnf(infer(ty)) is Sort l with level_is_zero(l)
    // reduction / conversion
    pub fn whnf_core(&mut self, t: TermId, cheap_rec: bool, cheap_proj: bool) -> R<TermId>;
    pub fn whnf(&mut self, t: TermId) -> R<TermId>;
    pub fn is_def_eq(&mut self, a: TermId, b: TermId) -> R<bool>;
    // helpers used by inductive.rs
    pub fn open_binder(&mut self, binder: TermId, extra_ub: u32) -> (TermId /*local*/, TermId /*instantiated body*/);
}
```

`Fail::Reject` propagates with `?` everywhere. Functions that the reference lets return
"none / does not reduce" return `Ok(None)`.

## 2. Mapping rules (reference → Palladium)

M1. **No `m_lctx`, no name generator.** Wherever the reference creates a local declaration for
    the binder of a term `t` (`mk_local_decl`, `mk_binding`-style loops), create
    `store.mk_local(d, dom)` where `dom` is the *instantiated, closed* binder type and
    `d = max(store.local_ub(t), store.local_ub(dom))` for the first binder; when walking a
    telescope the body is instantiated with the locals so far, so recomputing
    `d = max(local_ub(remaining term instantiated), local_ub(dom))` (or simply `d_prev + 1`)
    keeps depths strictly increasing. When two terms are opened together (`is_def_eq_binding`,
    eta) use the max over both. `open_binder` implements the single-binder case
    (`extra_ub` lets the caller raise the depth to cover a second term).
    The reference's delayed instantiation in `infer_lambda`, `infer_pi`, `is_def_eq_binding`
    (collect fvars, `instantiate_rev` once) carries over directly: `store.instantiate(body, &locals)`.
    To close a result over the locals use `store.abstract_locals` and rebuild `Pi`/`Lam` nodes;
    the binder type of the rebuilt node is the *original, un-instantiated* binder type of the input
    (abstracting the instantiated domain gives exactly that back).

M2. **Let.** No let-fvars. `infer(Let(ty, val, body))`: if `check`: `ensure_sort(infer(ty))`,
    `is_def_eq(infer(val), ty)` else Reject; then `infer(instantiate(body, [val]))`.
    `whnf_core(Let)` = `whnf_core(instantiate(body, [val]))`. A `Local` is always in whnf.

M3. **Loose bound variables.** `infer(BVar)` => Reject. Before checking a declaration, Reject
    if the imported type or value has `lbr != 0` (`bugs/loose-bvar-value`).

M4. **Universe parameters.** Before checking a declaration, walk its imported type/value once
    (memoised, pruned by `has_param`) and Reject if a `Level::Param` is not among the declared
    `level_params` (`other/inductive-undeclared-universe`); Reject duplicate names in `level_params`.

M5. **Constants.** `infer(Const(n, ls))`: `const_info(n)?`; Reject if `ls.len() != level_params.len()`;
    if `check && safe_mode && info.is_unsafe` Reject. Type = `subst_params(import_expr(info.ty), params, ls)`.
    `is_delta(t)`: head is a visible (`const_info_opt`) `Def` or `Thm` with matching universe arity;
    `Opaque`, `Axiom`, etc. never unfold. Hints: `Def` has its own; `Thm` counts as `Hints::Opaque`.

M6. **Caches.** Keys are `TermId`s. `infer` has two maps (checked / infer-only; a checked result
    also answers infer-only queries). `whnf_core` is cached only when `!cheap_rec && !cheap_proj`.
    `is_def_eq`: successes in a union-find over `TermId` (path compression; `a ≡ b` if same root),
    failures in a set of ordered pairs — failures are context-free here (design P2), so *every*
    final `false` of `is_def_eq_core` may be cached, but ONLY when `eager_reduce` is false.
    `eager_reduce` only affects the `Bool.true` shortcut; results computed while it is on are sound
    to cache as successes.

M7. **Literals.** `Nat(n)` has type `Const(Nat, [])`, `Str` has type `Const(String, [])`; in check mode
    Reject if that constant is not visible. Literal arithmetic (`reduce_nat`, and the `Nat.succ`/literal
    offset logic `is_def_eq_offset`) is enabled only if `env.builtins` has the names. Results that would
    exceed 2^24 bytes (16 MiB) are a `Fail::Fault` like the reference's "kernel refused" errors;
    `Nat.pow` with exponent > 2^24 does not reduce (return None).
    Strings: `string_lit_to_constructor` builds `String.ofList (List.cons.{0} Char (Char.ofNat (lit c)) … (List.nil.{0} Char))`
    over the Unicode scalar values of `env.raw.strs[idx]`.

M8. **Recursion depth.** Increment `depth` on entry to `infer`, `whnf_core`, `whnf`, `is_def_eq`
    (decrement on exit, also on the error path); `depth > 200_000` => `Fail::Fault("recursion depth")`.
    Worker threads have multi-GB stacks.

M9. **Projection `Proj(S, i, e)`**: follow `infer_proj` exactly (including the `is_prop` restrictions and
    `args.len() == numParams + numIndices`, single constructor) and `reduce_proj_core` (constructor's
    `induct` must equal `S`).

M10. **Recursor reduction** (`inductive_reduce_rec` in `inductive.h` and everything it calls:
    `to_cnstr_when_K`, `to_cnstr_when_structure`, `mk_nullary_cnstr`, nat-literal-to-constructor,
    string literal expansion) and **quotient reduction** (`quot_reduce_rec` in `quot.h`): follow the
    reference; all `RecInfo`/`CtorInfo`/`InductInfo` come from `env` (file data, validated by the owner
    of that inductive block — never index out of bounds on them: use `.get()` and return None).
    A recursor rule's rhs is `subst_params(import_expr(rule.rhs), rec.level_params, ls)`.

M11. **Declarations** (`check_decl`): axiom / def / thm / opaque as in DESIGN §5 (reference:
    `environment.cpp` `add_axiom`, `add_definition`, `add_theorem`, `add_opaque`; theorem type must be a
    `Prop`). Unsafe / partial declarations are skipped (accepted without checking); safe declarations may
    not mention them. `Decl::Quot` → `quot.rs`; `Decl::Inductive` → `inductive.rs`.

## 3. inductive.rs

`pub fn check_inductive(tc: &mut Checker, pos: u32, types: &[NameId], ctors: &[NameId], recs: &[NameId]) -> R<()>`

Port of `inductive.cpp` (`add_inductive_fn`, `elim_nested_inductive_fn`, and the glue in
`environment::add_inductive`) with these differences:

I1. The reference *creates* the declarations; we *derive and compare*. The "declaration" that the
    reference receives (`inductive_decl`: lparams, nparams, list of (name, type, constructors (name,type)))
    is reconstructed from the file: `types` in order, each type's `ctors` list (names) with the types of
    those constructor constants. Everything else in the file is compared against what the port derives:
    per type: `numParams`, `numIndices`, `all`, `ctors`, `numNested`, `isRec`, `isReflexive`;
    per constructor: `induct`, `cidx`, `numParams`, `numFields`; the set of constructors in the block must
    be exactly the union of the types' `ctors` lists (`other/orphan-ctor`); per recursor: name, level
    params (compare as lists), `all`, `numParams`, `numIndices`, `numMotives`, `numMinors`, `k`, type, and
    every rule (`ctor`, `nfields`, `rhs`); the set of recursors must be exactly the derived set
    (`other/extra-rec`, `bugs/orphan-rec`). Terms are compared by `TermId` first, then `is_def_eq`.
    All constants of the block share universe parameter lists as the reference requires (recursors have
    the extra elimination universe first when large-eliminating: its *name* is taken from the file's
    recursor `level_params[0]`, and must differ from the block's parameters).
I2. While checking the block set `tc.allow_block = true` so the block's own type and constructor
    constants (same `pos`) are visible; recursors of the block must NOT be used by reduction during the
    check. Restore afterwards.
I3. Locals follow M1. The reference keeps vectors of fvars for params/indices/motives/minors; here these
    are `Local` terms with strictly increasing depths (start at 0 for the first parameter since
    declaration types are closed and have `local_ub == 0`; when creating a local for a binder always use
    `max(next_depth, local_ub(dom))` and then `next_depth = d + 1`).
I4. **Nested inductives.** The reference temporarily adds auxiliary inductive types to a scratch
    environment and type-checks the translated block there. We cannot add constants to `Env` (shared,
    immutable) — instead keep the auxiliary block *inside the inductive checker*: the checks that the
    reference performs on the translated block (positivity, universe constraints, recursor generation)
    operate on terms in which a nested occurrence `J As (I Bs)…` has been replaced by an application of a
    block-local placeholder constant. Use fresh `NameId`s that cannot clash with file names: allocate them
    above `env.raw.names.len()` (ids `>= names.len()` are "auxiliary names" known only to this
    `check_inductive` call, with a side table `aux: Vec<AuxInfo>`); `const_info` must never see them:
    translate back (`restore_nested`) before calling `infer`/`whnf`/`is_def_eq` on such terms, exactly as
    the reference does for the final recursor types and rules. Typing checks on constructor types are
    done on the ORIGINAL (untranslated) terms against the real environment, with the block's types
    visible — this also checks the arguments of the outer inductive `J` (`bugs/nested-unused-param`).
    (`bugs/nested-name-capture`: file names can never equal auxiliary ids.)
I5. Use the file's metadata of *other, earlier* inductive types (e.g. `J`'s `numParams`, constructors)
    through `tc.const_info` — they are validated by their own block.

## 4. quot.rs

`pub fn check_quot(tc: &mut Checker, pos: u32, name: NameId) -> R<()>`: the four `quot` declarations of a file
(kinds type/ctor/lift/ind) must be named `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, have the level
params and exactly the types the reference's `quot.cpp` builds (build the expected term in the store and
compare `TermId`s with the imported file type; fall back to `is_def_eq`), and `Eq` must be visible and be
an inductive with one universe parameter, 2 params, 1 index, one constructor `Eq.refl` — as checked by
`environment::add_quot` / `quot.cpp::check_eq_type`. Quotient reduction is enabled only when the four
constants are visible.
