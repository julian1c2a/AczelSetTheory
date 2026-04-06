# Next Steps

**Last updated:** 2026-04-06 00:00

The project compiles cleanly on Lean 4.29.0 with **0 sorry** across all 8 modules.
The first three Zermelo axioms (Extensionality, Empty Set, Pairs) are derived as
theorems over the `HFSet` quotient type.

---

## Completed milestones

- ✅ CList foundations: 6 sub-modules (Basic, ExtEq, SetEquiv, Order, Sort, Normalize)
- ✅ `normalize_eq_of_extEq` proven — last sorry eliminated
- ✅ HFSet quotient type with `repr` and `empty`
- ✅ `HFSet.Mem` and `Membership` instance (∈ notation)
- ✅ Extensionality: ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B
- ✅ Empty Set: ∀ x, x ∉ ∅
- ✅ Pairs: x ∈ {a, b} ↔ x = a ∨ x = b

---

## Next: Remaining Zermelo axioms (without infinity/choice)

### Union axiom

```
∀ A, ∃ U, ∀ x, x ∈ U ↔ ∃ B ∈ A, x ∈ B
```

- Requires CList-level `flatten` operation: `mk [mk xs₁, mk xs₂, ...] → mk (xs₁ ++ xs₂ ++ ...)`
- Must prove flatten respects extEq for Quotient lifting
- Define `HFSet.sUnion` via `Quotient.liftOn`

### Separation (Comprehension) axiom

```
∀ A φ, ∃ B, ∀ x, x ∈ B ↔ x ∈ A ∧ φ(x)
```

- Requires CList-level `filter` operation
- Predicate φ must respect extEq (decidable predicate on HFSet)
- Define `HFSet.sep` via `Quotient.liftOn`

### Power Set axiom

```
∀ A, ∃ P, ∀ B, B ∈ P ↔ B ⊆ A
```

- Requires CList-level `sublists` / `powerset` operation
- Most complex: generates all subsets of a CList
- Must prove result respects extEq

### Foundation (Regularity) axiom

```
∀ A ≠ ∅, ∃ x ∈ A, x ∩ A = ∅
```

- Proof strategy: well-founded induction on `cSize`
- An element with minimal `cSize` in A serves as the ∈-minimal element

---

## Future directions

- Singleton notation `{a}` as sugar for `pair a a`
- Ordered pair `⟨a, b⟩` as `{{a}, {a, b}}`
- Natural numbers as von Neumann ordinals
- Ordinal arithmetic
- Decidability results for HFSet predicates
