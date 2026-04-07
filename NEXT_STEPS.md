# Next Steps

**Last updated:** 2026-04-07

The project compiles on Lean 4.29.0 with **2 sorry** remaining, both in the Powerset module.
All other Zermelo axioms (Extensionality, Empty Set, Pairs, Union, Separation, Intersection, Setminus) are
fully derived as theorems over the `HFSet` quotient type.

---

## Completed milestones

- ✅ CList foundations: 7 sub-modules (Basic, ExtEq, SetEquiv, Order, Sort, Normalize, Filter)
- ✅ `normalize_eq_of_extEq` proven — last CList sorry eliminated
- ✅ HFSet quotient type with `repr` and `empty`
- ✅ `HFSet.Mem` and `Membership` instance (∈ notation)
- ✅ Extensionality: ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B
- ✅ Empty Set: ∀ x, x ∉ ∅
- ✅ Pairs: x ∈ {a, b} ↔ x = a ∨ x = b
- ✅ Union: x ∈ ⋃ A ↔ ∃ B ∈ A, x ∈ B  (`HFSet.mem_sUnion`)
- ✅ Separation: x ∈ sep A P ↔ x ∈ A ∧ P x  (`HFSet.mem_sep`)
- ✅ Intersection: x ∈ ⋂ A ↔ ∀ B ∈ A, x ∈ B  (`HFSet.mem_sInter`)
- ✅ Setminus: x ∈ A \ B ↔ x ∈ A ∧ x ∉ B  (`HFSet.mem_setminus`)
- ✅ Architecture split: `Operations/` (CList-level) + `Axioms/` (HFSet-level)

---

## Current blocker: Powerset (Phase 5)

### Sorry 1 — `powersetCList_extEq` ([Operations/Powerset.lean:22](AczelSetTheory/Operations/Powerset.lean))

```lean
theorem powersetCList_extEq (A₁ A₂ : CList) (h : CList.extEq A₁ A₂ = true) :
    CList.extEq (powersetCList A₁) (powersetCList A₂) = true
```

**Proof strategy:**

1. Prove auxiliary: `mem_powersetCList : mem y (powersetCList A) = true ↔ subset y A = true`
   - Forward needs: `sublists_subset : zs ∈ sublists xs → subset (mk zs) (mk xs) = true`  (induction on sublists)
   - Backward needs: `filter_in_sublists : (xs.filter P) ∈ sublists xs` + show `extEq y (mk (xs.filter (fun z => mem z y)))` given `subset y (mk xs)`
2. Use `mem_powersetCList` + `subset`-transitivity: `extEq A₁ A₂ → (y ⊆ A₁ ↔ y ⊆ A₂)` → `extEq (powersetCList A₁) (powersetCList A₂)`.

### Sorry 2 — `mem_powerset` ([Axioms/Powerset.lean:9](AczelSetTheory/Axioms/Powerset.lean))

```lean
theorem mem_powerset (A : HFSet) (B : HFSet) :
    B ∈ powerset A ↔ (∀ x, x ∈ B → x ∈ A)
```

**Proof strategy:** Lift to CList using `Quotient.exists_rep`, reduce to `mem_powersetCList` + `subset_iff_forall_mem_clist`.

---

## Next: Foundation (Regularity) axiom (Phase 6 prerequisite)

```text
∀ A ≠ ∅, ∃ x ∈ A, x ∩ A = ∅
```

- Proof strategy: well-founded induction on `cSize`; element with minimal `cSize` in A is ∈-minimal.

---

## Phase 6: Natural numbers as von Neumann ordinals

- `succ A = A ∪ {A}` via `HFSet.sUnion` + `HFSet.pair`
- `zero = ∅`, `one = {∅}`, `two = {∅, {∅}}`
- Singleton notation `{a}` as sugar for `pair a a`
- Ordered pair `⟨a, b⟩` as `{{a}, {a, b}}`
- Ordinal arithmetic

---

## Future directions

- Replacement axiom
- Axiom of Choice (derivable from finite choice?)
- Decidability results for HFSet predicates
- Computable functions HFSet → HFSet
