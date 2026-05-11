# Changelog

All notable changes to this project are documented here.

---

## [2026-05-11] — Phase 1 complete: Peano integration (PList + omega₀) — 25 modules, 0 sorry

### Added — PList: polymorphic list type with ℕ₀ indexing

- **lakefile.lean**: added `require peanolib from git` (Peano natural numbers library).
- **PList/Basic.lean**: `inductive PList (α : Type)` with `length : PList α → ℕ₀`,
  all standard operations (`map`, `filter`, `append`, `flatMap`, `reverse`, `zipWith`,
  `foldl`, `foldr`, `any`, `all`, `get?`, `getD`), Bool and Prop membership
  (`mem`, `Mem`, `Membership` instance), and `toList`/`ofList` bridges to `List`.
- **PList/Lemmas.lean**: 22 `@[simp]` and supporting lemmas including `length_append`,
  `length_filter_le`, `toList_ofList`, `ofList_toList`, `length_toList` (via Λ bridge).
- **PList/Omega0.lean**: `omega₀` tactic macro — transports linear arithmetic goals over
  ℕ₀ to ℕ via `Ψ : ℕ₀ → ℕ`, then calls `omega`. Includes 6 bridge lemmas in
  `namespace PList.Omega0` and 15 verified test cases.
- **PList.lean**: barrel module importing Basic + Lemmas + Omega0.

### Technical notes

- **`+` ambiguity**: `export Peano.Add(add, ...)` makes both `add n m` and `n + m`
  valid elaborations for ℕ₀ addition under `open Peano`. Solution: use `add n m`
  in theorem statements involving `length`.
- **`Membership` argument order**: in Lean 4.29 `Membership.mem` takes container first
  (`γ → α → Prop`). Instance: `⟨fun l a => Mem a l⟩`.
- **`omega₀` / `Nat.add`**: omega does not recognise `Nat.add a b`; `ψ_add` uses
  `@HAdd.hAdd Nat Nat Nat instHAdd` to avoid `Coe Nat ℕ₀` ambiguity and guarantee
  omega compatibility.

**Project status: 0 sorry, 0 errors, 0 warnings. Phase 1 (Peano foundation) complete.**

---

## [2026-04-10] — Powerset axiom complete — 0 sorry project-wide

### Added — Powerset proofs

- **Operations/Powerset.lean**: Proved `sublists_subset`, `filter_in_sublists`, `mem_right_respects_extEq`, `mem_powersetCList`, and `powersetCList_extEq`. Key insight: use `filter (fun z => mem z y)` as sublists witness for the backward direction of `mem_powersetCList`.
- **Axioms/Powerset.lean**: Proved `mem_powerset` by lifting to CList via `Quotient.exists_rep`, reducing to `mem_powersetCList` + `subset_iff_forall_mem_clist`.

### Changed — Project documentation

- Full projection of all Operations/*, Axioms/*, CList/Filter, and Notation modules into REFERENCE.md.
- Updated all .md files to reflect 0 sorry and Phase 5 completion.

**Project status: 0 sorry, 0 errors, 0 warnings. All 8 Zermelo axioms derived.**

---

## [2026-04-07] — Advanced Operations and Powerset Draft

### Added — Union, Intersection, Setminus, Pair, and Powerset operations

- **Union (HFSet.sUnion)**: Extracted from definitions and proved mem_sUnion.
- **Intersection (HFSet.sInter)**: Defined and proved mem_sInter.
- **Setminus (HFSet.setminus)**: Defined and proved mem_setminus.
- **Separation (HFSet.sep)**: Formalized comprehension/separation.
- **Pair (HFSet.mkPair)**: Refactored into Operations/Pair.lean and Axioms/Pair.lean, fully proved.
- **Powerset (Draft)**: Created Operations/Powerset.lean and Axioms/Powerset.lean. Defined computational behavior via CList.sublists. The proofs powersetCList_extEq and mem_powerset remain as sorry for the next session.

---

## [2026-04-06] — Zermelo axioms as derived theorems

### Added — HFSet Zermelo axioms (Extensionality, Empty Set, Pairs)

Derived the first three Zermelo axioms as theorems over HFSet (quotient type),without postulating them:

- **HFSet.Mem**: Membership on HFSet via Quotient.liftOn₂, with proof
  that CList.mem respects xtEq in both arguments.
- **Membership HFSet HFSet instance**: enables x ∈ A notation.
- **mem_mk**: reduction lemma [x] ∈ [A] ↔ CList.mem x A = true.
- **xtensionality**: ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B.
- **
ot_mem_empty**: ∀ x, x ∉ ∅.
- **mkPair / pair / mem_pair**: x ∈ {a, b} ↔ x = a ∨ x = b.

All theorems fully proven. **0 sorry, 0 errors, 0 warnings.**

---

## [2026-04-05] — Module split and sorry elimination

### Changed — Full refactor: CSets.lean → CList sub-modules + HFSets.lean

Completely restructured the project from a single monolithic CSets.lean into  
8 focused modules with Mathlib-style English naming:

- CList/Basic.lean — Core type, size, comparison, order, dedup, sort, normalize
- CList/ExtEq.lean — Extensional equality: reflexivity, transitivity, commutativity
- CList/SetEquiv.lean — Nodup, SetEquiv, dedup properties
- CList/Order.lean — lt: irreflexivity, antisymmetry, totality, transitivity  
- CList/Sort.lean — Sorted, insertionSort preserves sorted/nodup/setEquiv
- CList/Normalize.lean — Size bounds, idempotency, uniqueness
- CList.lean — Root import aggregating all sub-modules
- HFSets.lean — HFSet quotient type, repr, empty

### Fixed —

ormalize_eq_of_extEq sorry eliminated

Proved
ormalize_eq_of_extEq (the last remaining sorry) using well-founded
recursion on cSize A + cSize B, combined with sorted_nodup_setEquiv_eq.

**Project status: 0 sorry across all modules.**

---

## [2026-04-02] — Lean 4.29.0 migration

### Changed — Lean 4.29.0 migration

Migrated the entire project from Lean **4.28.0** to **4.29.0**. The build now
completes successfully (lake build — no errors).
