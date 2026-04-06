
# Changelog

All notable changes to this project are documented here.

---

## [2026-04-06] — Zermelo axioms as derived theorems

### Added — HFSet Zermelo axioms (Extensionality, Empty Set, Pairs)

Derived the first three Zermelo axioms as theorems over `HFSet` (quotient type),
without postulating them:

- **`HFSet.Mem`**: Membership on HFSet via `Quotient.liftOn₂`, with proof
  that `CList.mem` respects `extEq` in both arguments.
- **`Membership HFSet HFSet` instance**: enables `x ∈ A` notation.
- **`mem_mk`**: reduction lemma `[x] ∈ [A] ↔ CList.mem x A = true`.
- **`extensionality`**: ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B.
- **`not_mem_empty`**: ∀ x, x ∉ ∅.
- **`mkPair` / `pair` / `mem_pair`**: x ∈ {a, b} ↔ x = a ∨ x = b.

All theorems fully proven. **0 sorry, 0 errors, 0 warnings.**

---

## [2026-04-05] — Module split and sorry elimination

### Changed — Full refactor: CSets.lean → CList sub-modules + HFSets.lean

Completely restructured the project from a single monolithic `CSets.lean` into
8 focused modules with Mathlib-style English naming:

- `CList/Basic.lean` — Core type, size, comparison, order, dedup, sort, normalize
- `CList/ExtEq.lean` — Extensional equality: reflexivity, transitivity, commutativity
- `CList/SetEquiv.lean` — Nodup, SetEquiv, dedup properties
- `CList/Order.lean` — lt: irreflexivity, antisymmetry, totality, transitivity
- `CList/Sort.lean` — Sorted, insertionSort preserves sorted/nodup/setEquiv
- `CList/Normalize.lean` — Size bounds, idempotency, uniqueness
- `CList.lean` — Root import aggregating all sub-modules
- `HFSets.lean` — HFSet quotient type, repr, empty

### Fixed — `normalize_eq_of_extEq` sorry eliminated

Proved `normalize_eq_of_extEq` (the last remaining sorry) using well-founded
recursion on `cSize A + cSize B`, combined with `sorted_nodup_setEquiv_eq`.

**Project status: 0 sorry across all modules.**

---

## [2026-04-02] — Lean 4.29.0 migration

### Changed — Lean 4.29.0 migration

Migrated the entire project from Lean **4.28.0** to **4.29.0**. The build now
completes successfully (`lake build` — no errors).

**Breaking changes fixed:**

- `forall_eq_or_imp` removed from core: replaced with a manual `constructor`
  proof in `subs_iff_forall_mem_pertenece`.
- `List.mem_cons_self` is now fully implicit (no arguments): removed `_ _`
  from two call sites.
- `simp_rw` inside tactic `have` blocks no longer works as a rewrite lemma
  source: extracted `subs_iff_forall_mem_pertenece` as a top-level
  `private theorem`.
- `simp only [esIgual_def]` unfolded `esIgual` inside `any`-predicates when
  `SetEquiv` was already unfolded: replaced with targeted `rw [esIgual_def,
  Bool.and_eq_true]` to avoid touching the inner `esIgual` calls.
- `rcases ... with (rfl | ...)` direction change in `reducirDuplicados_set_equiv_self`
  when both sides are free variables: renamed `head → hd` and corrected
  variable usage in the `rfl` branch.
- `induction` inside well-founded `decreasing_by` makes match variables
  abstract: rewrote `normalizar_cSize_le` + `normalizar_cSizeList_le` as a
  `mutual` block with term-level pattern matching so the concrete constructors
  are visible to the termination checker.
- `normalizar` not in scope inside `namespace CSet`: added `open CList` at the
  top of the namespace.

---

## Prior work

### `dd771c9` — Refactor `SetEquiv` theorems

### `462beed` — Fix `reducirDuplicados_nodup`

### `6a434a9` — Size lemmas and normalization bounds

### `8c25f00` — Transitivity and membership lemmas

### `8d0ee07` — `SetEquiv` and `esIgual_mk_iff_setEquiv`

### `698a119` — `reducirDuplicados_nodup` and `SetEquiv` scaffolding

### `d8a0805` — Refactor: remove old definition

### `d1a24e5` — Support lemmas and transitivity

### `46ac00e` — Initial implementation
