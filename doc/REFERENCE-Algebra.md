# Technical Reference — Algebra, Lattice & Structural Axioms

**Last updated:** 2026-05-16
**Parent:** [../REFERENCE.md](../REFERENCE.md)
**Related:** [REFERENCE-HFSets.md](REFERENCE-HFSets.md) | [REFERENCE-Relations.md](REFERENCE-Relations.md) | [REFERENCE-VN.md](REFERENCE-VN.md)

@axiom_system: AczelSetTheory
@importance: high

---

## Overview

Structural and algebraic layer: symmetric difference, cardinality, complement,
successor, von Neumann ordinals (predicate only), choice, boolean algebra,
boolean ring, distributive lattice, and supporting axioms (singleton, subset,
foundation, decidability).

**Primary namespace:** `HFSet`

| # | File | Status |
|---|------|--------|
| 40 | `AczelSetTheory/Operations/SymDiff.lean` | ✅ Complete |
| 41 | `AczelSetTheory/Operations/Cardinal.lean` | ✅ Complete |
| 42 | `AczelSetTheory/Axioms/Singleton.lean` | ✅ Complete |
| 43 | `AczelSetTheory/Axioms/Subset.lean` | ✅ Complete |
| 45 | `AczelSetTheory/Axioms/Foundation.lean` | ✅ Complete |
| 46 | `AczelSetTheory/Axioms/Decidable.lean` | ✅ Complete |
| 54 | `AczelSetTheory/Axioms/Succ.lean` | ✅ Complete |
| 55 | `AczelSetTheory/Axioms/SymDiff.lean` | ✅ Complete |
| 56 | `AczelSetTheory/Axioms/Lattice.lean` | ✅ Complete |
| 57 | `AczelSetTheory/Axioms/BooleanAlgebra.lean` | ✅ Complete |
| 58 | `AczelSetTheory/Axioms/BooleanRing.lean` | ✅ Complete |
| 59 | `AczelSetTheory/Axioms/VonNeumann.lean` | ✅ Complete |
| 60 | `AczelSetTheory/Axioms/Choice.lean` | ✅ Complete |
| 61 | `AczelSetTheory/Axioms/Cardinal.lean` | ✅ Complete |
| 71 | `AczelSetTheory/Axioms/Adjunction.lean` | ✅ Complete |
| 72 | `AczelSetTheory/Axioms/Induction.lean` | ✅ Complete |

---

## 4. Definitions

### 4.33 Operations/SymDiff.lean — `namespace HFSet`

#### 4.33.1 `HFSet.symDiff`

```lean
def HFSet.symDiff (A B : HFSet) : HFSet
```

- **Math**: A △ B ≔ (A \ B) ∪ (B \ A)
- Defined via `symDiffCList` (CList-level helper).
- Computable.

---

### 4.34 Operations/Cardinal.lean — `namespace HFSet`

#### 4.34.1 `HFSet.cardCList`

```lean
def HFSet.cardCList (a : CList) : ℕ₀
```

- **Math**: |a| at CList level (counts elements up to extEq, via normalized size)
- Computable.

#### 4.34.2 `HFSet.card`

```lean
def HFSet.card (A : HFSet) : ℕ₀
```

- **Math**: |A| (lifted to quotient via `cardCList_congr`)
- Computable.

---

### 4.36 Axioms/BooleanAlgebra.lean — `namespace HFSet`

#### 4.36.1 `HFSet.compl`

```lean
def HFSet.compl (U X : HFSet) : HFSet := setminus U X
```

- **Math**: Xᶜ ≔ U \ X (complement of X relative to universe U)
- Computable.

---

### 4.37 Axioms/Succ.lean — `namespace HFSet`

#### 4.37.1 `HFSet.succ`

```lean
def HFSet.succ (A : HFSet) : HFSet := union A (singleton A)
```

- **Math**: S(A) ≔ A ∪ {A}  (von Neumann successor)
- Computable.

---

### 4.38 Axioms/VonNeumann.lean — `namespace HFSet`

#### 4.38.1 `HFSet.isTransitive`

```lean
def HFSet.isTransitive (A : HFSet) : Prop := ∀ x, x ∈ A → x ⊆ A
```

- **Math**: A is transitive iff every element is a subset.

#### 4.38.2 `HFSet.isNat`

```lean
inductive HFSet.isNat : HFSet → Prop where
  | zero : isNat empty
  | succ {n : HFSet} : isNat n → isNat (succ n)
```

- **Math**: A is a (von Neumann) natural number iff it is ∅ or S(n) for some natural n.
- Inductive predicate. See [REFERENCE-VN.md](REFERENCE-VN.md) for the map `VN.vN : ℕ₀ → HFSet`.

---

### 4.39 Axioms/Choice.lean — `namespace HFSet`

#### 4.39.1 `HFSet.choose`

```lean
noncomputable def HFSet.choose (A : HFSet) (_ : A ≠ empty) : HFSet
```

- **Math**: ε(A) — some element of A, chosen noncomputably via `Classical.choice`.

---

### 4.43 Axioms/Adjunction.lean + Axioms/Induction.lean — `namespace HFSet`

> No new computable definitions. Both files export theorems only (see §6.52, §6.53).

---

## 6. Theorems

### 6.22 Operations/SymDiff.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `symDiffCList_extEq` | `(a₁ a₂ b₁ b₂ : CList) (ha : CList.extEq a₁ a₂ = true) (hb : CList.extEq b₁ b₂ = true) : CList.extEq (symDiffCList a₁ b₁) (symDiffCList a₂ b₂) = true` |

### 6.23 Axioms/Singleton.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_singleton` | `(x a : HFSet) : x ∈ singleton a ↔ x = a` |

### 6.24 Axioms/Subset.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `subset_iff` | `(A B : HFSet) : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B` |
| 2 | `subset_refl` | `(A : HFSet) : A ⊆ A` |
| 3 | `subset_trans` | `(A B C : HFSet) (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C` |
| 4 | `subset_antisymm` | `(A B : HFSet) (h₁ : A ⊆ B) (h₂ : B ⊆ A) : A = B` |
| 5 | `empty_subset` | `(A : HFSet) : empty ⊆ A` |
| 6 | `subset_union_left` | `(A B : HFSet) : A ⊆ union A B` |
| 7 | `subset_union_right` | `(A B : HFSet) : B ⊆ union A B` |
| 8 | `inter_subset_left` | `(A B : HFSet) : inter A B ⊆ A` |
| 9 | `inter_subset_right` | `(A B : HFSet) : inter A B ⊆ B` |
| 10 | `subset_inter` | `(A B C : HFSet) (h₁ : A ⊆ B) (h₂ : A ⊆ C) : A ⊆ inter B C` |

### 6.26 Axioms/Foundation.lean — `namespace CList` + `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `CList.mem_exists_plist_mem` | `(x : CList) (xs : PList CList) (h : mem x (mk xs) = true) : ∃ y, PList.Mem y xs ∧ extEq x y = true` |
| 2 | `CList.mem_of_plist_mem` | `(y : CList) (xs : PList CList) (h : PList.Mem y xs) : mem y (mk xs) = true` |
| 3 | `foundation` | `(A : HFSet) (hne : A ≠ empty) : ∃ x : HFSet, x ∈ A ∧ ∀ y : HFSet, y ∈ x → ¬ y ∈ A` |

### 6.27 Axioms/Decidable.lean — `namespace HFSet`

| # | Instance | Lean signature |
|---|----------|---------------|
| 1 | `mem_decidable` | `(x A : HFSet) → Decidable (x ∈ A)` |
| 2 | `existsMem_decidable` | `(A : HFSet) → (P : HFSet → Prop) → [DecidablePred P] → Decidable (∃ x, x ∈ A ∧ P x)` |

### 6.35 Axioms/Succ.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_succ` | `(x A : HFSet) : x ∈ succ A ↔ x ∈ A ∨ x = A` |
| 2 | `A_mem_succ_A` | `(A : HFSet) : A ∈ succ A` |
| 3 | `mem_succ_of_mem` | `(x A : HFSet) (h : x ∈ A) : x ∈ succ A` |
| 4 | `A_subset_succ_A` | `(A : HFSet) : A ⊆ succ A` |
| 5 | `succ_ne_empty` | `(A : HFSet) : succ A ≠ empty` |
| 6 | `not_mem_self` | `(A : HFSet) : ¬ (A ∈ A)` |
| 7 | `no_mem_cycle2` | `(A B : HFSet) (hAB : A ∈ B) (hBA : B ∈ A) : False` |
| 8 | `succ_injective` | `(A B : HFSet) (h : succ A = succ B) : A = B` |

### 6.36 Axioms/SymDiff.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_symDiff` | `(A B x : HFSet) : x ∈ symDiff A B ↔ (x ∈ A ∧ ¬ x ∈ B) ∨ (x ∈ B ∧ ¬ x ∈ A)` |

### 6.37 Axioms/Lattice.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `union_comm` | `(A B : HFSet) : union A B = union B A` |
| 2 | `inter_comm` | `(A B : HFSet) : inter A B = inter B A` |
| 3 | `union_assoc` | `(A B C : HFSet) : union (union A B) C = union A (union B C)` |
| 4 | `inter_assoc` | `(A B C : HFSet) : inter (inter A B) C = inter A (inter B C)` |
| 5 | `union_idem` | `(A : HFSet) : union A A = A` |
| 6 | `inter_idem` | `(A : HFSet) : inter A A = A` |
| 7 | `union_inter_absorb` | `(A B : HFSet) : union A (inter A B) = A` |
| 8 | `inter_union_absorb` | `(A B : HFSet) : inter A (union A B) = A` |
| 9 | `union_inter_distrib` | `(A B C : HFSet) : union A (inter B C) = inter (union A B) (union A C)` |
| 10 | `inter_union_distrib` | `(A B C : HFSet) : inter A (union B C) = union (inter A B) (inter A C)` |
| 11 | `union_empty` | `(A : HFSet) : union A empty = A` |
| 12 | `empty_union` | `(A : HFSet) : union empty A = A` |
| 13 | `inter_empty` | `(A : HFSet) : inter A empty = empty` |
| 14 | `empty_inter` | `(A : HFSet) : inter empty A = empty` |
| 15 | `setminus_self` | `(A : HFSet) : setminus A A = empty` |
| 16 | `setminus_empty` | `(A : HFSet) : setminus A empty = A` |
| 17 | `empty_setminus` | `(A : HFSet) : setminus empty A = empty` |

### 6.38 Axioms/BooleanAlgebra.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_compl` | `(U X x : HFSet) : x ∈ compl U X ↔ x ∈ U ∧ ¬ x ∈ X` |
| 2 | `inter_full` | `(U A : HFSet) (hA : A ⊆ U) : inter A U = A` |
| 3 | `full_inter` | `(U A : HFSet) (hA : A ⊆ U) : inter U A = A` |
| 4 | `compl_mem_powerset` | `(U X : HFSet) (_ : X ⊆ U) : compl U X ⊆ U` |
| 5 | `union_compl` | `(U X : HFSet) (hX : X ⊆ U) : union X (compl U X) = U` |
| 6 | `inter_compl` | `(U X : HFSet) (_ : X ⊆ U) : inter X (compl U X) = empty` |
| 7 | `compl_compl` | `(U X : HFSet) (hX : X ⊆ U) : compl U (compl U X) = X` |
| 8 | `compl_empty` | `(U : HFSet) : compl U empty = U` |
| 9 | `compl_self` | `(U : HFSet) : compl U U = empty` |
| 10 | `compl_union` | `(U A B : HFSet) (_ : A ⊆ U) (_ : B ⊆ U) : compl U (union A B) = inter (compl U A) (compl U B)` |
| 11 | `compl_inter` | `(U A B : HFSet) (_ : A ⊆ U) (_ : B ⊆ U) : compl U (inter A B) = union (compl U A) (compl U B)` |
| 12 | `compl_subset_swap` | `(U A B : HFSet) (hA : A ⊆ U) (_ : B ⊆ U) : (A ⊆ B ↔ compl U B ⊆ compl U A)` |
| 13 | `union_compl_inter` | `(U A B : HFSet) (hA : A ⊆ U) (hB : B ⊆ U) : union (inter A B) (inter A (compl U B)) = A` |

### 6.39 Axioms/BooleanRing.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `symDiff_comm` | `(A B : HFSet) : symDiff A B = symDiff B A` |
| 2 | `symDiff_assoc` | `(A B C : HFSet) : symDiff (symDiff A B) C = symDiff A (symDiff B C)` |
| 3 | `symDiff_empty` | `(A : HFSet) : symDiff A empty = A` |
| 4 | `empty_symDiff` | `(A : HFSet) : symDiff empty A = A` |
| 5 | `symDiff_self` | `(A : HFSet) : symDiff A A = empty` |
| 6 | `inter_symDiff_distrib` | `(A B C : HFSet) : inter A (symDiff B C) = symDiff (inter A B) (inter A C)` |
| 7 | `symDiff_eq_union_setminus` | `(A B : HFSet) : symDiff A B = setminus (union A B) (inter A B)` |
| 8 | `symDiff_via_compl` | `(U A B : HFSet) (hA : A ⊆ U) (hB : B ⊆ U) : symDiff A B = union (inter A (compl U B)) (inter B (compl U A))` |

### 6.40 Axioms/VonNeumann.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `isTransitive_empty` | `isTransitive empty` |
| 2 | `isTransitive_succ` | `(A : HFSet) (hT : isTransitive A) : isTransitive (succ A)` |
| 3 | `isNat_zero` | `isNat empty` |
| 4 | `isNat_succ` | `{n : HFSet} (h : isNat n) : isNat (succ n)` |
| 5 | `isNat_zero_or_succ` | `{n : HFSet} (hn : isNat n) : n = empty ∨ ∃ m, isNat m ∧ n = succ m` |
| 6 | `isNat_isTransitive` | `{n : HFSet} (hn : isNat n) : isTransitive n` |
| 7 | `isNat_mem_isNat` | `{n m : HFSet} (hn : isNat n) (hm : m ∈ n) : isNat m` |
| 8 | `isNat_pred` | `{n : HFSet} (hn : isNat (succ n)) : isNat n` |
| 9 | `isNat_induction` | `{n : HFSet} (P : HFSet → Prop) (h0 : P empty) (hs : ∀ k, isNat k → P k → P (succ k)) (hn : isNat n) : P n` |

### 6.41 Axioms/Choice.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `nonempty_of_ne_empty` | `(A : HFSet) (h : A ≠ empty) : ∃ x, x ∈ A` |
| 2 | `choose_mem` | `(A : HFSet) (h : A ≠ empty) : choose A h ∈ A` |
| 3 | `choice_principle` | `(F : HFSet) (hne : ∀ A, A ∈ F → A ≠ empty) : ∃ f : HFSet → HFSet, ∀ A, A ∈ F → f A ∈ A` |

### 6.42 Axioms/Cardinal.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `card_empty` | `card empty = 𝟘` |
| 2 | `card_insert` | `(x A : HFSet) (h : x ∉ A) : card (insert x A) = σ (card A)` |
| 3 | `card_powerset` | `(A : HFSet) : card (powerset A) = pow 𝟚 (card A)` |
### 6.52 Axioms/Adjunction.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_insert` | `(x b A : HFSet) : x ∈ insert b A ↔ x = b ∨ x ∈ A` |
| 2 | `mem_insert_self` | `(b A : HFSet) : b ∈ insert b A` |
| 3 | `insert_ne_empty` | `(b A : HFSet) : insert b A ≠ empty` |

### 6.53 Axioms/Induction.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `eps_induction` | `(P : HFSet → Prop) (h_empty : P empty) (h_adj : ∀ A b, P A → P (insert b A)) : ∀ A, P A` |
| 2 | `strong_eps_induction` | `(P : HFSet → Prop) (h : ∀ A, (∀ x, x ∈ A → P x) → P A) : ∀ A, P A` |
---

## 7. Exports per Module

### Operations/SymDiff.lean

`HFSet.symDiffCList`, `HFSet.symDiff`, `HFSet.symDiffCList_extEq`

### Operations/Cardinal.lean

`HFSet.cardCList`, `HFSet.card`, `HFSet.cardCList_congr`

### Axioms/Singleton.lean

`HFSet.mem_singleton`

### Axioms/Subset.lean

`HFSet.subset_iff`, `HFSet.subset_refl`, `HFSet.subset_trans`, `HFSet.subset_antisymm`, `HFSet.empty_subset`, `HFSet.subset_union_left`, `HFSet.subset_union_right`, `HFSet.inter_subset_left`, `HFSet.inter_subset_right`, `HFSet.subset_inter`

### Axioms/Foundation.lean

`CList.mem_exists_plist_mem`, `CList.mem_of_plist_mem`, `HFSet.foundation`

### Axioms/Decidable.lean

`HFSet.mem_decidable`, `HFSet.existsMem_decidable`

### Axioms/Succ.lean

`HFSet.succ`, `HFSet.mem_succ`, `HFSet.A_mem_succ_A`, `HFSet.mem_succ_of_mem`, `HFSet.A_subset_succ_A`, `HFSet.succ_ne_empty`, `HFSet.not_mem_self`, `HFSet.no_mem_cycle2`, `HFSet.succ_injective`

### Axioms/SymDiff.lean

`HFSet.mem_symDiff`

### Axioms/Lattice.lean

`HFSet.union_comm`, `HFSet.inter_comm`, `HFSet.union_assoc`, `HFSet.inter_assoc`, `HFSet.union_idem`, `HFSet.inter_idem`, `HFSet.union_inter_absorb`, `HFSet.inter_union_absorb`, `HFSet.union_inter_distrib`, `HFSet.inter_union_distrib`, `HFSet.union_empty`, `HFSet.empty_union`, `HFSet.inter_empty`, `HFSet.empty_inter`, `HFSet.setminus_self`, `HFSet.setminus_empty`, `HFSet.empty_setminus`

### Axioms/BooleanAlgebra.lean

`HFSet.compl`, `HFSet.mem_compl`, `HFSet.inter_full`, `HFSet.full_inter`, `HFSet.compl_mem_powerset`, `HFSet.union_compl`, `HFSet.inter_compl`, `HFSet.compl_compl`, `HFSet.compl_empty`, `HFSet.compl_self`, `HFSet.compl_union`, `HFSet.compl_inter`, `HFSet.compl_subset_swap`, `HFSet.union_compl_inter`

### Axioms/BooleanRing.lean

`HFSet.symDiff_comm`, `HFSet.symDiff_assoc`, `HFSet.symDiff_empty`, `HFSet.empty_symDiff`, `HFSet.symDiff_self`, `HFSet.inter_symDiff_distrib`, `HFSet.symDiff_eq_union_setminus`, `HFSet.symDiff_via_compl`

### Axioms/VonNeumann.lean

`HFSet.isTransitive`, `HFSet.isNat`, `HFSet.isTransitive_empty`, `HFSet.isTransitive_succ`, `HFSet.isNat_zero`, `HFSet.isNat_succ`, `HFSet.isNat_zero_or_succ`, `HFSet.isNat_isTransitive`, `HFSet.isNat_mem_isNat`, `HFSet.isNat_pred`, `HFSet.isNat_induction`

### Axioms/Choice.lean

`HFSet.choose`, `HFSet.nonempty_of_ne_empty`, `HFSet.choose_mem`, `HFSet.choice_principle`

### Axioms/Cardinal.lean

`HFSet.card_empty`, `HFSet.card_insert`, `HFSet.card_powerset`

### Axioms/Adjunction.lean

`HFSet.mem_insert`, `HFSet.mem_insert_self`, `HFSet.insert_ne_empty`

### Axioms/Induction.lean

`HFSet.eps_induction`, `HFSet.strong_eps_induction`
