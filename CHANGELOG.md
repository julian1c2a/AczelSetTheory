---
# Changelog

All notable changes to this project are documented here.

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
