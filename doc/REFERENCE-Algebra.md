# Technical Reference — Algebra, Lattice & Structural Axioms

**Last updated:** 2026-06-02 (Sylow constructivo + Sprint B.2: 0 `noncomputable def` en `Algebra/`)
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
| --- | ------ | -------- |
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
| 75 | `AczelSetTheory/Axioms/Ordinal.lean` | ✅ Complete |
| 77 | `AczelSetTheory/Axioms/OrdinalNat.lean` | ✅ Complete |
| 83 | `AczelSetTheory/Axioms/Rank.lean` | ✅ Complete |
| 87 | `AczelSetTheory/Algebra/Group.lean` | ✅ Complete |
| 88 | `AczelSetTheory/Algebra/Subgroup.lean` | ✅ Complete |
| 89 | `AczelSetTheory/Algebra/GroupHom.lean` | ✅ Complete |
| 90 | `AczelSetTheory/Algebra/Ring.lean` | ✅ Complete |
| 91 | `AczelSetTheory/Algebra/CosetCount.lean` | ✅ Complete |
| 92 | `AczelSetTheory/Algebra/Monoid.lean` | ✅ Complete |
| 93 | `AczelSetTheory/Algebra/RingHom.lean` | ✅ Complete |
| 94 | `AczelSetTheory/Algebra/Field.lean` | ✅ Complete |
| 95 | `AczelSetTheory/Algebra/Module.lean` | ✅ Complete |
| 96 | `AczelSetTheory/Algebra/LinearSpace.lean` | ✅ Complete |
| 97 | `AczelSetTheory/Algebra/Sylow.lean` | ✅ Complete (§1–§32, D.4.D McKay + Cauchy) |

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

### 4.45 Axioms/Ordinal.lean — `namespace HFSet`

#### 4.45.1 `HFSet.isOrdinal`

```lean
def HFSet.isOrdinal (A : HFSet) : Prop :=
  isTransitive A ∧ ∀ x y, x ∈ A → y ∈ A → x ∈ y ∨ x = y ∨ y ∈ x
```

- **Math**: A is a (von Neumann) ordinal iff it is transitive and linearly ordered by ∈.
- Depends on `HFSet.isTransitive` (from `Axioms/VonNeumann.lean`).
- Non-computable (Prop-valued predicate).

---

### 4.46 Axioms/OrdinalNat.lean — `namespace HFSet`

#### 4.46.1 `instDecidableEqHFSet`

```lean
instance : DecidableEq HFSet
```

- **Math**: La igualdad en HFSet es decidible.
- Construida por `Quotient.recOnSubsingleton₂` a partir de `CList.extEq : CList → CList → Bool`.
- Computable.

---

### 4.48 Axioms/Rank.lean — `namespace HFSet`

#### 4.48.1 `HFSet.rank`

```lean
def HFSet.rank (A : HFSet) : ℕ₀
```

- **Math**: ρ(A) — rango de Von Neumann de A. Defined by well-founded recursion on the
  normalized `CList` representative via internal `rankNorm : CList → ℕ₀`
  and `rankNormList : PList CList → ℕ₀` (mutual structural recursion).
  `rank(A) = max{ σ(rank(x)) | x ∈ A }`; `rank(∅) = 0`.
- Lifted to the quotient via `Quotient.liftOn` using `rankCList_congr`.
- Computable.
- Depends on `Operations/Cardinal` (for `orderedInsert`-level helpers), `Axioms/Adjunction`.
- See `VN/RankVN.lean` for `rank_vN : rank (vN n) = n`.

---

## 6. Theorems

### 6.22 Operations/SymDiff.lean — `namespace HFSet`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `symDiffCList_extEq` | `(a₁ a₂ b₁ b₂ : CList) (ha : CList.extEq a₁ a₂ = true) (hb : CList.extEq b₁ b₂ = true) : CList.extEq (symDiffCList a₁ b₁) (symDiffCList a₂ b₂) = true` |

### 6.23 Axioms/Singleton.lean — `namespace HFSet`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `mem_singleton` | `(x a : HFSet) : x ∈ singleton a ↔ x = a` |

### 6.24 Axioms/Subset.lean — `namespace HFSet`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
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
| --- | --------- | --------------- |
| 1 | `CList.mem_exists_plist_mem` | `(x : CList) (xs : PList CList) (h : mem x (mk xs) = true) : ∃ y, PList.Mem y xs ∧ extEq x y = true` |
| 2 | `CList.mem_of_plist_mem` | `(y : CList) (xs : PList CList) (h : PList.Mem y xs) : mem y (mk xs) = true` |
| 3 | `foundation` | `(A : HFSet) (hne : A ≠ empty) : ∃ x : HFSet, x ∈ A ∧ ∀ y : HFSet, y ∈ x → ¬ y ∈ A` |

### 6.27 Axioms/Decidable.lean — `namespace HFSet`

| # | Instance | Lean signature |
| --- | ---------- | --------------- |
| 1 | `mem_decidable` | `(x A : HFSet) → Decidable (x ∈ A)` |
| 2 | `existsMem_decidable` | `(A : HFSet) → (P : HFSet → Prop) → [DecidablePred P] → Decidable (∃ x, x ∈ A ∧ P x)` |
| 3 | `forallMem_decidable` | `(A : HFSet) → (P : HFSet → Prop) → [DecidablePred P] → Decidable (∀ x, x ∈ A → P x)` |
| 4 | `instDecidableEqHFSet` | `DecidableEq HFSet` |
| 5 | `instDecidableEmpty` | `(A : HFSet) → Decidable (A = empty)` |

### 6.35 Axioms/Succ.lean — `namespace HFSet`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
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
| --- | --------- | --------------- |
| 1 | `mem_symDiff` | `(A B x : HFSet) : x ∈ symDiff A B ↔ (x ∈ A ∧ ¬ x ∈ B) ∨ (x ∈ B ∧ ¬ x ∈ A)` |

### 6.37 Axioms/Lattice.lean — `namespace HFSet`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
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
| --- | --------- | --------------- |
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
| --- | --------- | --------------- |
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
| --- | --------- | --------------- |
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
| --- | --------- | --------------- |
| 1 | `nonempty_of_ne_empty` | `(A : HFSet) (h : A ≠ empty) : ∃ x, x ∈ A` |
| 2 | `choose_mem` | `(A : HFSet) (h : A ≠ empty) : choose A h ∈ A` |
| 3 | `choice_principle` | `(F : HFSet) (hne : ∀ A, A ∈ F → A ≠ empty) : ∃ f : HFSet → HFSet, ∀ A, A ∈ F → f A ∈ A` |

### 6.42 Axioms/Cardinal.lean — `namespace HFSet`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `card_empty` | `card empty = 𝟘` |
| 2 | `card_insert` | `(x A : HFSet) (h : x ∉ A) : card (insert x A) = σ (card A)` |
| 3 | `card_powerset` | `(A : HFSet) : card (powerset A) = pow 𝟚 (card A)` |
| 4 | `card_eq_zero_iff` | `{A : HFSet} : card A = 𝟘 ↔ A = empty` |
| 5 | `card_succ` | `(A : HFSet) : card (succ A) = σ (card A)` |

### 6.52 Axioms/Adjunction.lean — `namespace HFSet`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `mem_insert` | `(x b A : HFSet) : x ∈ insert b A ↔ x = b ∨ x ∈ A` |
| 2 | `mem_insert_self` | `(b A : HFSet) : b ∈ insert b A` |
| 3 | `insert_ne_empty` | `(b A : HFSet) : insert b A ≠ empty` |

### 6.53 Axioms/Induction.lean — `namespace HFSet`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `eps_induction` | `(P : HFSet → Prop) (h_empty : P empty) (h_adj : ∀ A b, P A → P (insert b A)) : ∀ A, P A` |
| 2 | `strong_eps_induction` | `(P : HFSet → Prop) (h : ∀ A, (∀ x, x ∈ A → P x) → P A) : ∀ A, P A` |

### 6.56 Axioms/Ordinal.lean — `namespace HFSet`

**Imports:** `AczelSetTheory.Axioms.VonNeumann`, `AczelSetTheory.Axioms.Induction`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `isOrdinal_empty` | `isOrdinal empty` |
| 2 | `isOrdinal_succ` | `{A : HFSet} (hA : isOrdinal A) : isOrdinal (succ A)` |
| 3 | `isNat_isOrdinal` | `{n : HFSet} (hn : isNat n) : isOrdinal n` |
| 4 | `isOrdinal_mem` | `{A x : HFSet} (hA : isOrdinal A) (hx : x ∈ A) : isOrdinal x` |

### 6.58 Axioms/OrdinalNat.lean — `namespace HFSet`

**Imports:** `AczelSetTheory.Axioms.Ordinal`, `AczelSetTheory.Axioms.Cardinal`, `AczelSetTheory.Axioms.Separation`, `AczelSetTheory.Axioms.Decidable`, `AczelSetTheory.Axioms.Setminus`, `AczelSetTheory.PList.Omega0`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `card_le_of_subset` | `{A B : HFSet} (h : A ⊆ B) : card A ≤ card B` |
| 2 | `isOrdinal_isNat` | `{A : HFSet} (hA : isOrdinal A) : isNat A` |
| 3 | `isOrdinal_iff_isNat` | `{A : HFSet} : isOrdinal A ↔ isNat A` |

### 6.64 Axioms/Rank.lean — `namespace HFSet`

**Imports:** `AczelSetTheory.Operations.Cardinal`, `AczelSetTheory.Axioms.Adjunction`
**Opens:** `Peano`

| # | Theorem | Lean signature |
| --- | --------- | --------------- |
| 1 | `rank_empty` | `rank empty = 𝟘` |
| 2 | `rank_insert` | `(x A : HFSet) (h : x ∉ A) : rank (insert x A) = max (σ (rank x)) (rank A)` |

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

`HFSet.mem_decidable`, `HFSet.existsMem_decidable`, `HFSet.forallMem_decidable`, `HFSet.instDecidableEqHFSet`, `HFSet.instDecidableEmpty`

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

`HFSet.card_empty`, `HFSet.card_insert`, `HFSet.card_powerset`, `HFSet.card_eq_zero_iff`, `HFSet.card_succ`

### Axioms/Adjunction.lean

`HFSet.mem_insert`, `HFSet.mem_insert_self`, `HFSet.insert_ne_empty`

### Axioms/Induction.lean

`HFSet.eps_induction`, `HFSet.strong_eps_induction`

### Axioms/Ordinal.lean

`HFSet.isOrdinal`, `HFSet.isOrdinal_empty`, `HFSet.isOrdinal_succ`, `HFSet.isNat_isOrdinal`, `HFSet.isOrdinal_mem`

### Axioms/OrdinalNat.lean

`HFSet.card_le_of_subset`, `HFSet.isOrdinal_isNat`, `HFSet.isOrdinal_iff_isNat`

### Axioms/Rank.lean

`HFSet.rank`, `HFSet.rank_empty`, `HFSet.rank_insert`, `HFSet.mem_rank_lt`, `HFSet.mem_wf`

---

## Group Theory — `Algebra/` subdirectory

**Last projected:** 2026-05-29

**Primary namespaces:** `HFAlgebra`, `HFAlgebra.HFGroup`, `HFAlgebra.HFSubgroup`, `HFAlgebra.HFGroupHom`, `HFAlgebra.HFRing`, `HFAlgebra.HFMonoid`, `HFAlgebra.HFMonoidHom`, `HFAlgebra.HFSubmonoid`, `HFAlgebra.HFRingHom`, `HFAlgebra.HFSubring`, `HFAlgebra.HFField`, `HFAlgebra.HFFieldHom`, `HFAlgebra.HFSubfield`, `HFAlgebra.HFModule`, `HFAlgebra.HFModuleHom`, `HFAlgebra.HFSubmodule`, `HFAlgebra.HFLinearSpace`, `HFAlgebra.HFLinearMap`, `HFAlgebra.HFSubspace`

---

### 4.87 Algebra/Group.lean — `namespace HFAlgebra`

**Imports:** `AczelSetTheory.HFSets`

#### 4.87.1 `HFAlgebra.HFGroup`

```lean
structure HFGroup where
  G   : HFSet
  op  : HFSet → HFSet → HFSet
  e   : HFSet
  inv : HFSet → HFSet
  e_mem       : e ∈ G
  op_closed   : ∀ {a b}, a ∈ G → b ∈ G → op a b ∈ G
  inv_closed  : ∀ {a}, a ∈ G → inv a ∈ G
  op_assoc    : ∀ {a b c}, a ∈ G → b ∈ G → c ∈ G → op (op a b) c = op a (op b c)
  op_id_left  : ∀ {a}, a ∈ G → op e a = a
  op_inv_left : ∀ {a}, a ∈ G → op (inv a) a = e
```

- **Math**: `(G, ·, e, ⁻¹)` — grupo con axiomas mínimos izquierdos.
- Prop-valued structure. Computable carrier.

---

### 4.88 Algebra/Subgroup.lean — `namespace HFAlgebra`

**Imports:** `AczelSetTheory.Algebra.Group`, `AczelSetTheory.Axioms.Separation`, `AczelSetTheory.Axioms.Decidable`, `AczelSetTheory.Axioms.OrdinalNat`, `AczelSetTheory.Axioms.Intersection`

#### 4.88.1 `HFAlgebra.HFSubgroup`

```lean
structure HFSubgroup (grp : HFGroup) where
  H          : HFSet
  H_sub      : ∀ {x}, x ∈ H → x ∈ grp.G
  e_mem      : grp.e ∈ H
  op_closed  : ∀ {a b}, a ∈ H → b ∈ H → grp.op a b ∈ H
  inv_closed : ∀ {a}, a ∈ H → grp.inv a ∈ H
```

- **Math**: H ≤ G — subgrupo de G.

#### 4.88.2 `HFSubgroup.toHFGroup`

```lean
def HFSubgroup.toHFGroup (sub : HFSubgroup grp) : HFGroup
```

- **Math**: Todo subgrupo es un grupo.

#### 4.88.3 `HFSubgroup.inter`

```lean
def HFSubgroup.inter (sub₁ sub₂ : HFSubgroup grp) : HFSubgroup grp
```

- **Math**: H₁ ∩ H₂ ≤ G. (Nota: dentro de `namespace HFSubgroup`, este `inter` sombrea `HFSet.inter`.)

#### 4.88.4 `HFSubgroup.rightCoset`

```lean
def HFSubgroup.rightCoset (sub : HFSubgroup grp) (a : HFSet) : HFSet :=
  HFSet.sep grp.G (fun x => ∃ h ∈ sub.H, x = grp.op h a)
```

- **Math**: Ha = { h·a | h ∈ H } — cosete derecho de H en G por a.
- Computable (separación decidible).

#### 4.88.5 `HFSubgroup.cosetEq`

```lean
def HFSubgroup.cosetEq (sub : HFSubgroup grp) (a b : HFSet) : Prop :=
  grp.op b (grp.inv a) ∈ sub.H
```

- **Math**: a ~_H b iff b·a⁻¹ ∈ H — relación de equivalencia de cosetes.

---

### 4.89 Algebra/GroupHom.lean — `namespace HFAlgebra`

**Imports:** `AczelSetTheory.Algebra.Subgroup`

#### 4.89.1 `HFAlgebra.HFGroupHom`

```lean
structure HFGroupHom (G H : HFGroup) where
  f     : HFSet → HFSet
  f_mem : ∀ {a}, a ∈ G.G → f a ∈ H.G
  f_hom : ∀ {a b}, a ∈ G.G → b ∈ G.G → f (G.op a b) = H.op (f a) (f b)
```

- **Math**: φ : G →ₕ H — homomorfismo de grupos.

#### 4.89.2 `HFGroupHom.ker`

```lean
def HFGroupHom.ker (φ : HFGroupHom G H) : HFSubgroup G
```

- **Math**: ker φ = { a ∈ G | φ(a) = e_H } ≤ G.

#### 4.89.3 `HFGroupHom.image`

```lean
def HFGroupHom.image (φ : HFGroupHom G H) : HFSubgroup H
```

- **Math**: im φ = { φ(a) | a ∈ G } ≤ H.

---

### 4.90 Algebra/Ring.lean — `namespace HFAlgebra`

**Imports:** `AczelSetTheory.Algebra.Group`

#### 4.90.1 `HFAlgebra.HFRing`

```lean
structure HFRing where
  R   : HFSet
  add mul : HFSet → HFSet → HFSet
  zero one : HFSet
  neg  : HFSet → HFSet
  -- cerradura, grupo aditivo abeliano (axiomas izq. + comm), monoide mult. unital, bilinealidad
```

- **Math**: `(R, +, ·, 0, 1, -)` — anillo unitario (no necesariamente conmutativo).
- La conmutatividad aditiva es un axioma explícito (`add_comm`).

#### 4.90.2 `HFRing.toAdditiveHFGroup`

```lean
def HFRing.toAdditiveHFGroup (rng : HFRing) : HFGroup
```

- **Math**: Grupo aditivo subyacente `(R, +, 0, -)`.

---

### 4.91 Algebra/CosetCount.lean — `namespace HFSet` + `namespace HFAlgebra.HFSubgroup`

**Imports:** `AczelSetTheory.Algebra.Subgroup`, `AczelSetTheory.Axioms.OrdinalNat`, `AczelSetTheory.Axioms.Union`, `AczelSetTheory.Axioms.Powerset`, `Peano.PeanoNat.Arith`

**Opens:** `Peano`, `Peano.Arith`

#### 4.91.1 `HFSubgroup.cosets`

```lean
def HFSubgroup.cosets (sub : HFSubgroup grp) : HFSet :=
  sep (powerset grp.G) (fun C => ∃ a ∈ grp.G, C = sub.rightCoset a)
```

- **Math**: El conjunto de todos los cosetes derechos de H en G.
- Computable (separación decidible sobre powerset).

#### 4.91.2 `HFSubgroup.index`

```lean
def HFSubgroup.index (sub : HFSubgroup grp) : ℕ₀ := card sub.cosets
```

- **Math**: [G : H] — índice de H en G.

---

### 6.87 Algebra/Group.lean — `namespace HFAlgebra.HFGroup`

`variable (grp : HFGroup)`

| # | Theorem | Lean signature |
| --- | --------- | ---------------- |
| 1 | `op_inv_left_apply` | `{a b : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) : grp.op (grp.inv a) (grp.op a b) = b` |
| 2 | `left_cancel` | `{x a b : HFSet} (hx : x ∈ grp.G) (ha : a ∈ grp.G) (hb : b ∈ grp.G) (h : grp.op x a = grp.op x b) : a = b` |
| 3 | `op_inv_right` | `{a : HFSet} (ha : a ∈ grp.G) : grp.op a (grp.inv a) = grp.e` |
| 4 | `op_id_right` | `{a : HFSet} (ha : a ∈ grp.G) : grp.op a grp.e = a` |
| 5 | `right_cancel` | `{x a b : HFSet} (hx : x ∈ grp.G) (ha : a ∈ grp.G) (hb : b ∈ grp.G) (h : grp.op a x = grp.op b x) : a = b` |
| 6 | `inv_inv` | `{a : HFSet} (ha : a ∈ grp.G) : grp.inv (grp.inv a) = a` |
| 7 | `inv_e` | `(grp : HFGroup) : grp.inv grp.e = grp.e` |
| 8 | `inv_op` | `{a b : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) : grp.inv (grp.op a b) = grp.op (grp.inv b) (grp.inv a)` |
| 9 | `unique_id` | `{e' : HFSet} (he' : e' ∈ grp.G) (h : ∀ {a}, a ∈ grp.G → grp.op e' a = a) : e' = grp.e` |
| 10 | `unique_inv` | `{a b : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) (h : grp.op b a = grp.e) : b = grp.inv a` |

---

### 6.88 Algebra/Subgroup.lean — `namespace HFAlgebra.HFSubgroup`

`variable {grp : HFGroup}`

| # | Theorem | Lean signature |
| --- | --------- | ---------------- |
| 1 | `mem_rightCoset` | `(sub : HFSubgroup grp) {a x : HFSet} (ha : a ∈ grp.G) : x ∈ sub.rightCoset a ↔ ∃ h ∈ sub.H, x = grp.op h a` |
| 2 | `cosetEq_refl` | `(sub : HFSubgroup grp) {a : HFSet} (ha : a ∈ grp.G) : sub.cosetEq a a` |
| 3 | `cosetEq_symm` | `(sub : HFSubgroup grp) {a b : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) (h : sub.cosetEq a b) : sub.cosetEq b a` |
| 4 | `cosetEq_trans` | `(sub : HFSubgroup grp) {a b c : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) (hc : c ∈ grp.G) (hab : sub.cosetEq a b) (hbc : sub.cosetEq b c) : sub.cosetEq a c` |
| 5 | `cosetEq_iff_rightCoset_eq` | `(sub : HFSubgroup grp) {a b : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) : sub.cosetEq a b ↔ sub.rightCoset a = sub.rightCoset b` |
| 6 | `rightCoset_self_mem` | `(sub : HFSubgroup grp) {a : HFSet} (ha : a ∈ grp.G) : a ∈ sub.rightCoset a` |
| 7 | `rightCoset_nonempty` | `(sub : HFSubgroup grp) {a : HFSet} (ha : a ∈ grp.G) : ∃ x, x ∈ sub.rightCoset a` |
| 8 | `mem_rightCoset_iff` | `(sub : HFSubgroup grp) {a x : HFSet} (ha : a ∈ grp.G) : x ∈ sub.rightCoset a ↔ ∃ h ∈ sub.H, x = grp.op h a` |
| 9 | `rightCoset_eq_iff` | `(sub : HFSubgroup grp) {a b : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) : sub.rightCoset a = sub.rightCoset b ↔ sub.cosetEq a b` |
| 10 | `cosetEq_is_equiv_on_G` | `(sub : HFSubgroup grp) : (∀ {a}, a ∈ grp.G → sub.cosetEq a a) ∧ (∀ {a b}, a ∈ grp.G → b ∈ grp.G → sub.cosetEq a b → sub.cosetEq b a) ∧ (∀ {a b c}, a ∈ grp.G → b ∈ grp.G → c ∈ grp.G → sub.cosetEq a b → sub.cosetEq b c → sub.cosetEq a c)` |
| 11 | `rightCoset_mul_mem` | `(sub : HFSubgroup grp) {a h x : HFSet} (ha : a ∈ grp.G) (hh : h ∈ sub.H) (hx : x ∈ sub.rightCoset a) : grp.op h x ∈ sub.rightCoset a` |
| 12 | `rightCoset_eq_subgroup_of_mem` | `(sub : HFSubgroup grp) {a : HFSet} (haG : a ∈ grp.G) (haH : a ∈ sub.H) : sub.rightCoset a = sub.H` |
| 13 | `rightCoset_equinumerous_H` | `(sub : HFSubgroup grp) {a : HFSet} (haG : a ∈ grp.G) (haH : a ∈ sub.H) : HFSet.card (sub.rightCoset a) = HFSet.card sub.H` |
| 14 | `cosetEq_of_mem_inter_rightCoset` | `(sub : HFSubgroup grp) {a b x : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) (hx : x ∈ HFSet.inter (sub.rightCoset a) (sub.rightCoset b)) : sub.cosetEq a b` |
| 15 | `rightCosets_cover_G` | `(sub : HFSubgroup grp) {x : HFSet} (hx : x ∈ grp.G) : x ∈ sub.rightCoset x` |
| 16 | `rightCoset_eq_or_disjoint` | `(sub : HFSubgroup grp) {a b : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) : sub.rightCoset a = sub.rightCoset b ∨ HFSet.inter (sub.rightCoset a) (sub.rightCoset b) = HFSet.empty` |

---

### 6.89 Algebra/GroupHom.lean — `namespace HFAlgebra.HFGroupHom`

`variable {G H : HFGroup} (φ : HFGroupHom G H)`

| # | Theorem | Lean signature |
| --- | --------- | ---------------- |
| 1 | `hom_e` | `(φ : HFGroupHom G H) : φ.f G.e = H.e` |
| 2 | `hom_inv` | `(φ : HFGroupHom G H) {a : HFSet} (ha : a ∈ G.G) : φ.f (G.inv a) = H.inv (φ.f a)` |

---

### 6.90 Algebra/Ring.lean — `namespace HFAlgebra.HFRing`

`variable (rng : HFRing)`

| # | Theorem | Lean signature |
| --- | --------- | ---------------- |
| 1 | `add_zero` | `{a : HFSet} (ha : a ∈ rng.R) : rng.add a rng.zero = a` |
| 2 | `add_neg` | `{a : HFSet} (ha : a ∈ rng.R) : rng.add a (rng.neg a) = rng.zero` |
| 3 | `neg_neg` | `{a : HFSet} (ha : a ∈ rng.R) : rng.neg (rng.neg a) = a` |
| 4 | `zero_mul` | `{a : HFSet} (ha : a ∈ rng.R) : rng.mul rng.zero a = rng.zero` |
| 5 | `mul_zero` | `{a : HFSet} (ha : a ∈ rng.R) : rng.mul a rng.zero = rng.zero` |
| 6 | `neg_mul` | `{a b : HFSet} (ha : a ∈ rng.R) (hb : b ∈ rng.R) : rng.mul (rng.neg a) b = rng.neg (rng.mul a b)` |
| 7 | `mul_neg` | `{a b : HFSet} (ha : a ∈ rng.R) (hb : b ∈ rng.R) : rng.mul a (rng.neg b) = rng.neg (rng.mul a b)` |

---

### 6.91 Algebra/CosetCount.lean

| # | Theorem | Namespace | Lean signature |
| --- | --------- | ----------- | ---------------- |
| 1 | `sUnion_insert` | `HFSet` | `(C F : HFSet) : sUnion (insert C F) = union C (sUnion F)` |
| 2 | `card_sUnion_uniform_partition` | `HFSet` | `(F : HFSet) (k : ℕ₀) (hunif : ∀ C, C ∈ F → card C = k) (hdisj : ∀ C D, C ∈ F → D ∈ F → C ≠ D → inter C D = empty) : card (sUnion F) = mul (card F) k` |
| 3 | `card_rightCoset_eq_card_H` | `HFAlgebra.HFSubgroup` | `(sub : HFSubgroup grp) {a : HFSet} (ha : a ∈ grp.G) : card (sub.rightCoset a) = card sub.H` |
| 4 | `mem_cosets` | `HFAlgebra.HFSubgroup` | `{sub : HFSubgroup grp} {C : HFSet} : C ∈ sub.cosets ↔ ∃ a ∈ grp.G, C = sub.rightCoset a` |
| 5 | `cosets_cover` | `HFAlgebra.HFSubgroup` | `(sub : HFSubgroup grp) : sUnion sub.cosets = grp.G` |
| 6 | `cosets_pairwise_disjoint` | `HFAlgebra.HFSubgroup` | `(sub : HFSubgroup grp) {C D : HFSet} (hC : C ∈ sub.cosets) (hD : D ∈ sub.cosets) (hCD : C ≠ D) : HFSet.inter C D = HFSet.empty` |
| 7 | `coset_card_eq` | `HFAlgebra.HFSubgroup` | `(sub : HFSubgroup grp) {C : HFSet} (hC : C ∈ sub.cosets) : card C = card sub.H` |
| 8 | `card_G_eq_card_H_mul_index` | `HFAlgebra.HFSubgroup` | `(sub : HFSubgroup grp) : card grp.G = mul (card sub.cosets) (card sub.H)` |
| 9 | `card_subgroup_dvd_card_group` | `HFAlgebra.HFSubgroup` | `(sub : HFSubgroup grp) : card sub.H ∣ card grp.G` — **Teorema de Lagrange** |

> `∣` es `Peano.Arith.Divides` (no `Dvd`): `Divides a b = ∃ k : ℕ₀, b = mul a k`.
> Requiere `import Peano.PeanoNat.Arith` + `open Peano.Arith`.

---

## 7b. Exports — Algebra/ subdirectory

### Algebra/Group.lean

`HFAlgebra.HFGroup`, `HFAlgebra.HFGroup.op_inv_left_apply`, `HFAlgebra.HFGroup.left_cancel`, `HFAlgebra.HFGroup.op_inv_right`, `HFAlgebra.HFGroup.op_id_right`, `HFAlgebra.HFGroup.right_cancel`, `HFAlgebra.HFGroup.inv_inv`, `HFAlgebra.HFGroup.inv_e`, `HFAlgebra.HFGroup.inv_op`, `HFAlgebra.HFGroup.unique_id`, `HFAlgebra.HFGroup.unique_inv`

### Algebra/Subgroup.lean

`HFAlgebra.HFSubgroup`, `HFAlgebra.HFSubgroup.toHFGroup`, `HFAlgebra.HFSubgroup.inter`, `HFAlgebra.HFSubgroup.rightCoset`, `HFAlgebra.HFSubgroup.cosetEq`, `HFAlgebra.HFSubgroup.mem_rightCoset`, `HFAlgebra.HFSubgroup.cosetEq_refl`, `HFAlgebra.HFSubgroup.cosetEq_symm`, `HFAlgebra.HFSubgroup.cosetEq_trans`, `HFAlgebra.HFSubgroup.cosetEq_iff_rightCoset_eq`, `HFAlgebra.HFSubgroup.rightCoset_self_mem`, `HFAlgebra.HFSubgroup.rightCoset_nonempty`, `HFAlgebra.HFSubgroup.mem_rightCoset_iff`, `HFAlgebra.HFSubgroup.rightCoset_eq_iff`, `HFAlgebra.HFSubgroup.cosetEq_is_equiv_on_G`, `HFAlgebra.HFSubgroup.rightCoset_mul_mem`, `HFAlgebra.HFSubgroup.rightCoset_eq_subgroup_of_mem`, `HFAlgebra.HFSubgroup.rightCoset_equinumerous_H`, `HFAlgebra.HFSubgroup.cosetEq_of_mem_inter_rightCoset`, `HFAlgebra.HFSubgroup.rightCosets_cover_G`, `HFAlgebra.HFSubgroup.rightCoset_eq_or_disjoint`

### Algebra/GroupHom.lean

`HFAlgebra.HFGroupHom`, `HFAlgebra.HFGroupHom.hom_e`, `HFAlgebra.HFGroupHom.hom_inv`, `HFAlgebra.HFGroupHom.ker`, `HFAlgebra.HFGroupHom.image`

### Algebra/Ring.lean

`HFAlgebra.HFRing`, `HFAlgebra.HFRing.toAdditiveHFGroup`, `HFAlgebra.HFRing.add_zero`, `HFAlgebra.HFRing.add_neg`, `HFAlgebra.HFRing.neg_neg`, `HFAlgebra.HFRing.zero_mul`, `HFAlgebra.HFRing.mul_zero`, `HFAlgebra.HFRing.neg_mul`, `HFAlgebra.HFRing.mul_neg`

### Algebra/CosetCount.lean

`HFSet.sUnion_insert`, `HFSet.card_sUnion_uniform_partition`, `HFAlgebra.HFSubgroup.card_rightCoset_eq_card_H`, `HFAlgebra.HFSubgroup.cosets`, `HFAlgebra.HFSubgroup.index`, `HFAlgebra.HFSubgroup.mem_cosets`, `HFAlgebra.HFSubgroup.cosets_cover`, `HFAlgebra.HFSubgroup.cosets_pairwise_disjoint`, `HFAlgebra.HFSubgroup.coset_card_eq`, `HFAlgebra.HFSubgroup.card_G_eq_card_H_mul_index`, `HFAlgebra.HFSubgroup.card_subgroup_dvd_card_group`

---

### 4.92 Algebra/Monoid.lean — `namespace HFAlgebra`

**Imports:** `AczelSetTheory.HFSets`, `AczelSetTheory.Axioms.Intersection`

#### 4.92.1 `HFAlgebra.HFMonoid`

```lean
structure HFMonoid where
  M   : HFSet
  op  : HFSet → HFSet → HFSet
  e   : HFSet
  e_mem       : e ∈ M
  op_closed   : ∀ {a b : HFSet}, a ∈ M → b ∈ M → op a b ∈ M
  op_assoc    : ∀ {a b c : HFSet}, a ∈ M → b ∈ M → c ∈ M →
                  op (op a b) c = op a (op b c)
  op_id_left  : ∀ {a : HFSet}, a ∈ M → op e a = a
  op_id_right : ∀ {a : HFSet}, a ∈ M → op a e = a
```

- **Math**: `(M, ·, e)` — monoide con identidad bilateral explícita.
- Prop-valued structure. Computable carrier.
- **Nota**: A diferencia de `HFGroup`, la identidad derecha es un axioma explícito (no derivable sin inversos).

#### 4.92.2 `HFAlgebra.HFMonoidHom`

```lean
structure HFMonoidHom (M N : HFMonoid) where
  f     : HFSet → HFSet
  f_mem : ∀ {a : HFSet}, a ∈ M.M → f a ∈ N.M
  f_hom : ∀ {a b : HFSet}, a ∈ M.M → b ∈ M.M → f (M.op a b) = N.op (f a) (f b)
  f_one : f M.e = N.e
```

- **Math**: φ : M →ₘ N — homomorfismo de monoides.
- `f_one` es axioma explícito (no derivable sin inversos).

#### 4.92.3 `HFMonoidHom.id`

```lean
def HFMonoidHom.id (M : HFMonoid) : HFMonoidHom M M
```

- **Math**: Homomorfismo identidad.

#### 4.92.4 `HFMonoidHom.comp`

```lean
def HFMonoidHom.comp (ψ : HFMonoidHom N P) (φ : HFMonoidHom M N) : HFMonoidHom M P
```

- **Math**: Composición ψ ∘ φ.

#### 4.92.5 `HFAlgebra.HFSubmonoid`

```lean
structure HFSubmonoid (mon : HFMonoid) where
  S         : HFSet
  S_sub     : ∀ {x : HFSet}, x ∈ S → x ∈ mon.M
  e_mem     : mon.e ∈ S
  op_closed : ∀ {a b : HFSet}, a ∈ S → b ∈ S → mon.op a b ∈ S
```

- **Math**: S ≤ M — submonoide de M.

#### 4.92.6 `HFSubmonoid.toHFMonoid`

```lean
def HFSubmonoid.toHFMonoid (sub : HFSubmonoid mon) : HFMonoid
```

- **Math**: Todo submonoide es un monoide.

#### 4.92.7 `HFSubmonoid.inter`

```lean
def HFSubmonoid.inter (sub₁ sub₂ : HFSubmonoid mon) : HFSubmonoid mon
```

- **Math**: S₁ ∩ S₂ ≤ M.

---

### 4.93 Algebra/RingHom.lean — `namespace HFAlgebra`

**Imports:** `AczelSetTheory.Algebra.Ring`, `AczelSetTheory.Axioms.Intersection`

#### 4.93.1 `HFAlgebra.HFRingHom`

```lean
structure HFRingHom (R S : HFRing) where
  f     : HFSet → HFSet
  f_mem : ∀ {a : HFSet}, a ∈ R.R → f a ∈ S.R
  f_add : ∀ {a b : HFSet}, a ∈ R.R → b ∈ R.R → f (R.add a b) = S.add (f a) (f b)
  f_mul : ∀ {a b : HFSet}, a ∈ R.R → b ∈ R.R → f (R.mul a b) = S.mul (f a) (f b)
  f_one : f R.one = S.one
```

- **Math**: φ : R →ᵣ S — homomorfismo de anillos unitarios. `f_one` es axioma explícito.

#### 4.93.2 `HFRingHom.id`

```lean
def HFRingHom.id (R : HFRing) : HFRingHom R R
```

#### 4.93.3 `HFRingHom.comp`

```lean
def HFRingHom.comp (ψ : HFRingHom S T) (φ : HFRingHom R S) : HFRingHom R T
```

#### 4.93.4 `HFAlgebra.HFSubring`

```lean
structure HFSubring (rng : HFRing) where
  S          : HFSet
  S_sub      : ∀ {x : HFSet}, x ∈ S → x ∈ rng.R
  zero_mem   : rng.zero ∈ S
  one_mem    : rng.one ∈ S
  add_closed : ∀ {a b : HFSet}, a ∈ S → b ∈ S → rng.add a b ∈ S
  mul_closed : ∀ {a b : HFSet}, a ∈ S → b ∈ S → rng.mul a b ∈ S
  neg_closed : ∀ {a : HFSet}, a ∈ S → rng.neg a ∈ S
```

- **Math**: S ≤ R — subanillo de R.

#### 4.93.5 `HFSubring.toHFRing`

```lean
def HFSubring.toHFRing (sub : HFSubring rng) : HFRing
```

#### 4.93.6 `HFSubring.inter`

```lean
def HFSubring.inter (sub₁ sub₂ : HFSubring rng) : HFSubring rng
```

---

### 4.94 Algebra/Field.lean — `namespace HFAlgebra`

**Imports:** `AczelSetTheory.Algebra.RingHom`, `AczelSetTheory.Axioms.Intersection`

#### 4.94.1 `HFAlgebra.HFField`

```lean
structure HFField where
  F       : HFSet
  add mul : HFSet → HFSet → HFSet
  zero one : HFSet
  neg inv_mul : HFSet → HFSet
  zero_mem one_mem : _
  add_closed mul_closed neg_closed : _
  inv_closed  : ∀ {a : HFSet}, a ∈ F → inv_mul a ∈ F   -- sin condición a ≠ zero
  add_assoc add_comm zero_add neg_add : _   -- grupo aditivo abeliano
  mul_assoc mul_comm mul_one left_distrib : _
  mul_inv  : ∀ {a : HFSet}, a ∈ F → a ≠ zero → mul a (inv_mul a) = one
  zero_ne_one : zero ≠ one
```

- **Math**: `(F, +, ·, 0, 1, -, ⁻¹)` — cuerpo conmutativo unitario.
- `inv_mul` es una función total con valor basura para `zero` (coherente con `inv_closed` sin condición `a ≠ 0`).

#### 4.94.2 `HFField.toHFRing`

```lean
def HFField.toHFRing (fld : HFField) : HFRing
```

- **Math**: Todo cuerpo es un anillo.

#### 4.94.3 `HFField.toAdditiveHFGroup`

```lean
def HFField.toAdditiveHFGroup (fld : HFField) : HFGroup
```

- **Math**: Grupo aditivo subyacente `(F, +, 0, -)`.

#### 4.94.4 `HFAlgebra.HFFieldHom`

```lean
structure HFFieldHom (F G : HFField) where
  f     : HFSet → HFSet
  f_mem : ∀ {a : HFSet}, a ∈ F.F → f a ∈ G.F
  f_add : ∀ {a b : HFSet}, a ∈ F.F → b ∈ F.F → f (F.add a b) = G.add (f a) (f b)
  f_mul : ∀ {a b : HFSet}, a ∈ F.F → b ∈ F.F → f (F.mul a b) = G.mul (f a) (f b)
  f_one : f F.one = G.one
```

- **Math**: φ : F →ᶠ G — homomorfismo de cuerpos.

#### 4.94.5 `HFFieldHom.toHFRingHom`

```lean
def HFFieldHom.toHFRingHom (φ : HFFieldHom F G) : HFRingHom F.toHFRing G.toHFRing
```

#### 4.94.6 `HFFieldHom.id`, `HFFieldHom.comp`

```lean
def HFFieldHom.id (F : HFField) : HFFieldHom F F
def HFFieldHom.comp (ψ : HFFieldHom G K) (φ : HFFieldHom F G) : HFFieldHom F K
```

#### 4.94.7 `HFAlgebra.HFSubfield`

```lean
structure HFSubfield (fld : HFField) where
  S           : HFSet
  S_sub       : ∀ {x : HFSet}, x ∈ S → x ∈ fld.F
  zero_mem one_mem : _
  add_closed mul_closed neg_closed : _
  inv_closed  : ∀ {a : HFSet}, a ∈ S → fld.inv_mul a ∈ S   -- sin condición a ≠ zero
```

- **Math**: S ≤ F — subcuerpo de F.

#### 4.94.8 `HFSubfield.toHFField`, `HFSubfield.inter`

```lean
def HFSubfield.toHFField (sub : HFSubfield fld) : HFField
def HFSubfield.inter (sub₁ sub₂ : HFSubfield fld) : HFSubfield fld
```

---

### 4.95 Algebra/Module.lean — `namespace HFAlgebra`

**Imports:** `AczelSetTheory.Algebra.Ring`, `AczelSetTheory.Axioms.Intersection`

#### 4.95.1 `HFAlgebra.HFModule`

```lean
structure HFModule (rng : HFRing) where
  M    : HFSet
  add  : HFSet → HFSet → HFSet
  zero : HFSet
  neg  : HFSet → HFSet
  smul : HFSet → HFSet → HFSet   -- r ⊙ m
  zero_mem add_closed neg_closed : _
  smul_closed : ∀ {r m : HFSet}, r ∈ rng.R → m ∈ M → smul r m ∈ M
  add_assoc add_comm zero_add neg_add : _   -- grupo aditivo abeliano
  smul_add  : ∀ {r m n : HFSet}, r ∈ rng.R → m ∈ M → n ∈ M →
                smul r (add m n) = add (smul r m) (smul r n)
  add_smul  : ∀ {r s m : HFSet}, r ∈ rng.R → s ∈ rng.R → m ∈ M →
                smul (rng.add r s) m = add (smul r m) (smul s m)
  mul_smul  : ∀ {r s m : HFSet}, r ∈ rng.R → s ∈ rng.R → m ∈ M →
                smul (rng.mul r s) m = smul r (smul s m)
  one_smul  : ∀ {m : HFSet}, m ∈ M → smul rng.one m = m
```

- **Math**: Módulo izquierdo sobre `rng`. `smul r m` denota `r ⊙ m`.

#### 4.95.2 `HFModule.toAdditiveHFGroup`

```lean
def HFModule.toAdditiveHFGroup {rng : HFRing} (mod : HFModule rng) : HFGroup
```

#### 4.95.3 `HFAlgebra.HFModuleHom`

```lean
structure HFModuleHom (rng : HFRing) (M N : HFModule rng) where
  f      : HFSet → HFSet
  f_mem  : ∀ {m : HFSet}, m ∈ M.M → f m ∈ N.M
  f_add  : ∀ {m n : HFSet}, m ∈ M.M → n ∈ M.M → f (M.add m n) = N.add (f m) (f n)
  f_smul : ∀ {r m : HFSet}, r ∈ rng.R → m ∈ M.M → f (M.smul r m) = N.smul r (f m)
```

- **Math**: φ : M →ᵣ N — homomorfismo R-lineal.

#### 4.95.4 `HFModuleHom.id`, `HFModuleHom.comp`

```lean
def HFModuleHom.id (M : HFModule rng) : HFModuleHom rng M M
def HFModuleHom.comp (ψ : HFModuleHom rng N P) (φ : HFModuleHom rng M N) : HFModuleHom rng M P
```

#### 4.95.5 `HFAlgebra.HFSubmodule`

```lean
structure HFSubmodule (rng : HFRing) (mod : HFModule rng) where
  S           : HFSet
  S_sub       : ∀ {x : HFSet}, x ∈ S → x ∈ mod.M
  zero_mem    : mod.zero ∈ S
  add_closed  : ∀ {m n : HFSet}, m ∈ S → n ∈ S → mod.add m n ∈ S
  neg_closed  : ∀ {m : HFSet}, m ∈ S → mod.neg m ∈ S
  smul_closed : ∀ {r m : HFSet}, r ∈ rng.R → m ∈ S → mod.smul r m ∈ S
```

- **Math**: N ≤ M — submódulo de M.

#### 4.95.6 `HFSubmodule.toHFModule`, `HFSubmodule.inter`

```lean
def HFSubmodule.toHFModule (sub : HFSubmodule rng mod) : HFModule rng
def HFSubmodule.inter (sub₁ sub₂ : HFSubmodule rng mod) : HFSubmodule rng mod
```

---

### 4.96 Algebra/LinearSpace.lean — `namespace HFAlgebra`

**Imports:** `AczelSetTheory.Algebra.Field`, `AczelSetTheory.Axioms.Intersection`

#### 4.96.1 `HFAlgebra.HFLinearSpace`

```lean
structure HFLinearSpace (fld : HFField) where
  V     : HFSet
  add   : HFSet → HFSet → HFSet
  zero  : HFSet
  neg   : HFSet → HFSet
  smul  : HFSet → HFSet → HFSet   -- k ⊙ v
  zero_mem add_closed neg_closed : _
  smul_closed : ∀ {k v : HFSet}, k ∈ fld.F → v ∈ V → smul k v ∈ V
  add_assoc add_comm zero_add neg_add : _   -- grupo aditivo abeliano
  smul_add  : ∀ {k v w : HFSet}, k ∈ fld.F → v ∈ V → w ∈ V →
                smul k (add v w) = add (smul k v) (smul k w)
  add_smul  : ∀ {k l v : HFSet}, k ∈ fld.F → l ∈ fld.F → v ∈ V →
                smul (fld.add k l) v = add (smul k v) (smul l v)
  mul_smul  : ∀ {k l v : HFSet}, k ∈ fld.F → l ∈ fld.F → v ∈ V →
                smul (fld.mul k l) v = smul k (smul l v)
  one_smul  : ∀ {v : HFSet}, v ∈ V → smul fld.one v = v
```

- **Math**: Espacio vectorial sobre `fld`. Definido independientemente de `HFModule` para evitar la conversión `HFField → HFRing`.

#### 4.96.2 `HFLinearSpace.toAdditiveHFGroup`

```lean
def HFLinearSpace.toAdditiveHFGroup {fld : HFField} (vs : HFLinearSpace fld) : HFGroup
```

#### 4.96.3 `HFAlgebra.HFLinearMap`

```lean
structure HFLinearMap (fld : HFField) (V W : HFLinearSpace fld) where
  f      : HFSet → HFSet
  f_mem  : ∀ {v : HFSet}, v ∈ V.V → f v ∈ W.V
  f_add  : ∀ {v w : HFSet}, v ∈ V.V → w ∈ V.V → f (V.add v w) = W.add (f v) (f w)
  f_smul : ∀ {k v : HFSet}, k ∈ fld.F → v ∈ V.V → f (V.smul k v) = W.smul k (f v)
```

- **Math**: φ : V →ₗ W — aplicación lineal.

#### 4.96.4 `HFLinearMap.id`, `HFLinearMap.comp`

```lean
def HFLinearMap.id (V : HFLinearSpace fld) : HFLinearMap fld V V
def HFLinearMap.comp (ψ : HFLinearMap fld W U) (φ : HFLinearMap fld V W) : HFLinearMap fld V U
```

#### 4.96.5 `HFAlgebra.HFSubspace`

```lean
structure HFSubspace (fld : HFField) (vs : HFLinearSpace fld) where
  W           : HFSet
  W_sub       : ∀ {v : HFSet}, v ∈ W → v ∈ vs.V
  zero_mem    : vs.zero ∈ W
  add_closed  : ∀ {v w : HFSet}, v ∈ W → w ∈ W → vs.add v w ∈ W
  neg_closed  : ∀ {v : HFSet}, v ∈ W → vs.neg v ∈ W
  smul_closed : ∀ {k v : HFSet}, k ∈ fld.F → v ∈ W → vs.smul k v ∈ W
```

- **Math**: W ≤ V — subespacio vectorial de V.

#### 4.96.6 `HFSubspace.toHFLinearSpace`, `HFSubspace.inter`

```lean
def HFSubspace.toHFLinearSpace (sub : HFSubspace fld vs) : HFLinearSpace fld
def HFSubspace.inter (sub₁ sub₂ : HFSubspace fld vs) : HFSubspace fld vs
```

---

### 6.92 Algebra/Monoid.lean — `namespace HFAlgebra.HFMonoid`

`variable (mon : HFMonoid)`

| # | Theorem | Lean signature |
| --- | --------- | ---------------- |
| 1 | `unique_id` | `{e' : HFSet} (he' : e' ∈ mon.M) (_hL : ∀ {a : HFSet}, a ∈ mon.M → mon.op e' a = a) (hR : ∀ {a : HFSet}, a ∈ mon.M → mon.op a e' = a) : e' = mon.e` |

---

### 6.93 Algebra/RingHom.lean — `namespace HFAlgebra.HFRingHom`

`variable {R S : HFRing} (φ : HFRingHom R S)`

| # | Theorem | Lean signature |
| --- | --------- | ---------------- |
| 1 | `hom_zero` | `(φ : HFRingHom R S) : φ.f R.zero = S.zero` |
| 2 | `hom_neg` | `(φ : HFRingHom R S) {a : HFSet} (ha : a ∈ R.R) : φ.f (R.neg a) = S.neg (φ.f a)` |

---

### 6.94 Algebra/Field.lean — `namespace HFAlgebra.HFField` + `HFAlgebra.HFFieldHom`

`variable (fld : HFField)`

| # | Theorem | Namespace | Lean signature |
| --- | --------- | ----------- | ---------------- |
| 1 | `one_mul` | `HFAlgebra.HFField` | `{a : HFSet} (ha : a ∈ fld.F) : fld.mul fld.one a = fld.mul a fld.one` |
| 2 | `right_distrib` | `HFAlgebra.HFField` | `{a b c : HFSet} (ha : a ∈ fld.F) (hb : b ∈ fld.F) (hc : c ∈ fld.F) : fld.mul (fld.add a b) c = fld.add (fld.mul a c) (fld.mul b c)` |
| 3 | `mul_inv_left` | `HFAlgebra.HFField` | `{a : HFSet} (ha : a ∈ fld.F) (hne : a ≠ fld.zero) : fld.mul (fld.inv_mul a) a = fld.one` |
| 4 | `hom_zero` | `HFAlgebra.HFFieldHom` | `(φ : HFFieldHom F G) : φ.f F.zero = G.zero` |
| 5 | `hom_neg` | `HFAlgebra.HFFieldHom` | `(φ : HFFieldHom F G) {a : HFSet} (ha : a ∈ F.F) : φ.f (F.neg a) = G.neg (φ.f a)` |
| 6 | `hom_inv` | `HFAlgebra.HFFieldHom` | `(φ : HFFieldHom F G) {a : HFSet} (ha : a ∈ F.F) (hne : a ≠ F.zero) : φ.f (F.inv_mul a) = G.inv_mul (φ.f a)` |

---

### 6.95 Algebra/Module.lean — `namespace HFAlgebra.HFModule` + `HFAlgebra.HFModuleHom`

`variable {rng : HFRing} (mod : HFModule rng)`

| # | Theorem | Namespace | Lean signature |
| --- | --------- | ----------- | ---------------- |
| 1 | `zero_smul` | `HFAlgebra.HFModule` | `{m : HFSet} (hm : m ∈ mod.M) : mod.smul rng.zero m = mod.zero` |
| 2 | `smul_zero` | `HFAlgebra.HFModule` | `{r : HFSet} (hr : r ∈ rng.R) : mod.smul r mod.zero = mod.zero` |
| 3 | `neg_smul` | `HFAlgebra.HFModule` | `{r m : HFSet} (hr : r ∈ rng.R) (hm : m ∈ mod.M) : mod.smul (rng.neg r) m = mod.neg (mod.smul r m)` |
| 4 | `smul_neg` | `HFAlgebra.HFModule` | `{r m : HFSet} (hr : r ∈ rng.R) (hm : m ∈ mod.M) : mod.smul r (mod.neg m) = mod.neg (mod.smul r m)` |
| 5 | `hom_zero` | `HFAlgebra.HFModuleHom` | `(φ : HFModuleHom rng M N) : φ.f M.zero = N.zero` |
| 6 | `hom_neg` | `HFAlgebra.HFModuleHom` | `(φ : HFModuleHom rng M N) {m : HFSet} (hm : m ∈ M.M) : φ.f (M.neg m) = N.neg (φ.f m)` |

---

### 6.96 Algebra/LinearSpace.lean — `namespace HFAlgebra.HFLinearSpace` + `HFAlgebra.HFLinearMap`

`variable {fld : HFField} (vs : HFLinearSpace fld)`

| # | Theorem | Namespace | Lean signature |
| --- | --------- | ----------- | ---------------- |
| 1 | `zero_smul` | `HFAlgebra.HFLinearSpace` | `{v : HFSet} (hv : v ∈ vs.V) : vs.smul fld.zero v = vs.zero` |
| 2 | `smul_zero` | `HFAlgebra.HFLinearSpace` | `{k : HFSet} (hk : k ∈ fld.F) : vs.smul k vs.zero = vs.zero` |
| 3 | `neg_smul` | `HFAlgebra.HFLinearSpace` | `{k v : HFSet} (hk : k ∈ fld.F) (hv : v ∈ vs.V) : vs.smul (fld.neg k) v = vs.neg (vs.smul k v)` |
| 4 | `smul_neg` | `HFAlgebra.HFLinearSpace` | `{k v : HFSet} (hk : k ∈ fld.F) (hv : v ∈ vs.V) : vs.smul k (vs.neg v) = vs.neg (vs.smul k v)` |
| 5 | `hom_zero` | `HFAlgebra.HFLinearMap` | `(φ : HFLinearMap fld V W) : φ.f V.zero = W.zero` |
| 6 | `hom_neg` | `HFAlgebra.HFLinearMap` | `(φ : HFLinearMap fld V W) {v : HFSet} (hv : v ∈ V.V) : φ.f (V.neg v) = W.neg (φ.f v)` |

---

### Algebra/Monoid.lean

`HFAlgebra.HFMonoid`, `HFAlgebra.HFMonoid.unique_id`, `HFAlgebra.HFMonoidHom`, `HFAlgebra.HFMonoidHom.id`, `HFAlgebra.HFMonoidHom.comp`, `HFAlgebra.HFSubmonoid`, `HFAlgebra.HFSubmonoid.toHFMonoid`, `HFAlgebra.HFSubmonoid.inter`

### Algebra/RingHom.lean

`HFAlgebra.HFRingHom`, `HFAlgebra.HFRingHom.hom_zero`, `HFAlgebra.HFRingHom.hom_neg`, `HFAlgebra.HFRingHom.id`, `HFAlgebra.HFRingHom.comp`, `HFAlgebra.HFSubring`, `HFAlgebra.HFSubring.toHFRing`, `HFAlgebra.HFSubring.inter`

### Algebra/Field.lean

`HFAlgebra.HFField`, `HFAlgebra.HFField.one_mul`, `HFAlgebra.HFField.right_distrib`, `HFAlgebra.HFField.mul_inv_left`, `HFAlgebra.HFField.toHFRing`, `HFAlgebra.HFField.toAdditiveHFGroup`, `HFAlgebra.HFFieldHom`, `HFAlgebra.HFFieldHom.toHFRingHom`, `HFAlgebra.HFFieldHom.hom_zero`, `HFAlgebra.HFFieldHom.hom_neg`, `HFAlgebra.HFFieldHom.hom_inv`, `HFAlgebra.HFFieldHom.id`, `HFAlgebra.HFFieldHom.comp`, `HFAlgebra.HFSubfield`, `HFAlgebra.HFSubfield.toHFField`, `HFAlgebra.HFSubfield.inter`

### Algebra/Module.lean

`HFAlgebra.HFModule`, `HFAlgebra.HFModule.toAdditiveHFGroup`, `HFAlgebra.HFModule.zero_smul`, `HFAlgebra.HFModule.smul_zero`, `HFAlgebra.HFModule.neg_smul`, `HFAlgebra.HFModule.smul_neg`, `HFAlgebra.HFModuleHom`, `HFAlgebra.HFModuleHom.hom_zero`, `HFAlgebra.HFModuleHom.hom_neg`, `HFAlgebra.HFModuleHom.id`, `HFAlgebra.HFModuleHom.comp`, `HFAlgebra.HFSubmodule`, `HFAlgebra.HFSubmodule.toHFModule`, `HFAlgebra.HFSubmodule.inter`

### Algebra/LinearSpace.lean

`HFAlgebra.HFLinearSpace`, `HFAlgebra.HFLinearSpace.toAdditiveHFGroup`, `HFAlgebra.HFLinearSpace.zero_smul`, `HFAlgebra.HFLinearSpace.smul_zero`, `HFAlgebra.HFLinearSpace.neg_smul`, `HFAlgebra.HFLinearSpace.smul_neg`, `HFAlgebra.HFLinearMap`, `HFAlgebra.HFLinearMap.hom_zero`, `HFAlgebra.HFLinearMap.hom_neg`, `HFAlgebra.HFLinearMap.id`, `HFAlgebra.HFLinearMap.comp`, `HFAlgebra.HFSubspace`, `HFAlgebra.HFSubspace.toHFLinearSpace`, `HFAlgebra.HFSubspace.inter`

### Algebra/Lattice.lean

`HFAlgebra.HFLattice`, `HFAlgebra.HFLattice.le`, `HFAlgebra.HFLattice.meet_idem`, `HFAlgebra.HFLattice.join_idem`, `HFAlgebra.HFLattice.le_refl`, `HFAlgebra.HFLattice.le_antisymm`, `HFAlgebra.HFLattice.le_trans`, `HFAlgebra.HFLattice.meet_le_left`, `HFAlgebra.HFLattice.meet_le_right`, `HFAlgebra.HFLattice.le_join_left`, `HFAlgebra.HFLattice.le_join_right`, `HFAlgebra.HFBoundedLattice`, `HFAlgebra.HFBoundedLattice.toLattice`, `HFAlgebra.HFBoundedLattice.meet_bot`, `HFAlgebra.HFBoundedLattice.join_top`, `HFAlgebra.HFDistributiveLattice`, `HFAlgebra.HFDistributiveLattice.toLattice`, `HFAlgebra.HFDistributiveLattice.join_distrib`, `HFAlgebra.HFLatHom`, `HFAlgebra.HFLatHom.id`, `HFAlgebra.HFLatHom.comp`, `HFAlgebra.HFSublattice`, `HFAlgebra.HFSublattice.toHFLattice`, `HFAlgebra.HFSublattice.inter`

---

## Algebra/Lattice.lean — Sección detallada

**Fuente:** `AczelSetTheory/Algebra/Lattice.lean`  
**Namespace:** `HFAlgebra`  
**Imports:** `AczelSetTheory.HFSets`, `AczelSetTheory.Axioms.Subset`, `AczelSetTheory.Axioms.Intersection`

### `HFAlgebra.HFLattice`

```lean
structure HFLattice where
  L    : HFSet
  meet : HFSet → HFSet → HFSet          -- ⊓
  join : HFSet → HFSet → HFSet          -- ⊔
  meet_closed : ∀ {a b}, a ∈ L → b ∈ L → meet a b ∈ L
  join_closed : ∀ {a b}, a ∈ L → b ∈ L → join a b ∈ L
  meet_comm   : ∀ {a b}, a ∈ L → b ∈ L → meet a b = meet b a
  join_comm   : ∀ {a b}, a ∈ L → b ∈ L → join a b = join b a
  meet_assoc  : ∀ {a b c}, a ∈ L → b ∈ L → c ∈ L → meet (meet a b) c = meet a (meet b c)
  join_assoc  : ∀ {a b c}, a ∈ L → b ∈ L → c ∈ L → join (join a b) c = join a (join b c)
  meet_absorb : ∀ {a b}, a ∈ L → b ∈ L → meet a (join a b) = a
  join_absorb : ∀ {a b}, a ∈ L → b ∈ L → join a (meet a b) = a
```

- **Math**: `(L, ⊓, ⊔)` — retículo; absorción implica idempotencia.
- Computable carrier. No `noncomputable`.

#### Definición derivada

```lean
def HFLattice.le (lat : HFLattice) (a b : HFSet) : Prop := lat.meet a b = a
-- a ≤ b  ↔  a ⊓ b = a
```

#### Teoremas — `HFLattice`

| Nombre | Enunciado |
|--------|-----------|
| `meet_idem` | `a ∈ L → lat.meet a a = a` |
| `join_idem` | `a ∈ L → lat.join a a = a` |
| `le_refl` | `a ∈ L → lat.le a a` |
| `le_antisymm` | `lat.le a b → lat.le b a → a = b` |
| `le_trans` | `lat.le a b → lat.le b c → lat.le a c` |
| `meet_le_left` | `lat.le (lat.meet a b) a` |
| `meet_le_right` | `lat.le (lat.meet a b) b` |
| `le_join_left` | `lat.le a (lat.join a b)` |
| `le_join_right` | `lat.le b (lat.join a b)` |

### `HFAlgebra.HFBoundedLattice`

```lean
structure HFBoundedLattice where
  L    : HFSet;  meet join : HFSet → HFSet → HFSet;  bot top : HFSet
  -- axiomas de retículo (meet_closed, join_closed, meet_comm, join_comm,
  --   meet_assoc, join_assoc, meet_absorb, join_absorb)
  bot_mem  : bot ∈ L;  top_mem : top ∈ L
  join_bot : ∀ {a}, a ∈ L → join a bot = a    -- a ⊔ ⊥ = a
  meet_top : ∀ {a}, a ∈ L → meet a top = a    -- a ⊓ ⊤ = a
```

```lean
def HFBoundedLattice.toLattice (bl : HFBoundedLattice) : HFLattice
```

#### Teoremas — `HFBoundedLattice`

| Nombre | Enunciado |
|--------|-----------|
| `meet_bot` | `a ∈ L → bl.meet a bl.bot = bl.bot` |
| `join_top` | `a ∈ L → bl.join a bl.top = bl.top` |

### `HFAlgebra.HFDistributiveLattice`

```lean
structure HFDistributiveLattice where
  -- axiomas de retículo (ídem a HFLattice)
  meet_distrib : ∀ {a b c}, a ∈ L → b ∈ L → c ∈ L →
                   meet a (join b c) = join (meet a b) (meet a c)
```

```lean
def HFDistributiveLattice.toLattice (dl : HFDistributiveLattice) : HFLattice
```

#### Teoremas — `HFDistributiveLattice`

| Nombre | Enunciado |
|--------|-----------|
| `join_distrib` | `dl.join a (dl.meet b c) = dl.meet (dl.join a b) (dl.join a c)` |

### `HFAlgebra.HFLatHom`

```lean
structure HFLatHom (L M : HFLattice) where
  f      : HFSet → HFSet
  f_mem  : ∀ {a}, a ∈ L.L → f a ∈ M.L
  f_meet : ∀ {a b}, a ∈ L.L → b ∈ L.L → f (L.meet a b) = M.meet (f a) (f b)
  f_join : ∀ {a b}, a ∈ L.L → b ∈ L.L → f (L.join a b) = M.join (f a) (f b)
```

```lean
def HFLatHom.id (L : HFLattice) : HFLatHom L L
def HFLatHom.comp (ψ : HFLatHom M N) (φ : HFLatHom L M) : HFLatHom L N
```

### `HFAlgebra.HFSublattice`

```lean
structure HFSublattice (lat : HFLattice) where
  S           : HFSet
  S_sub       : ∀ {x}, x ∈ S → x ∈ lat.L
  meet_closed : ∀ {a b}, a ∈ S → b ∈ S → lat.meet a b ∈ S
  join_closed : ∀ {a b}, a ∈ S → b ∈ S → lat.join a b ∈ S
```

```lean
def HFSublattice.toHFLattice (sub : HFSublattice lat) : HFLattice
def HFSublattice.inter (sub₁ sub₂ : HFSublattice lat) : HFSublattice lat
```

---

## `Algebra/Sylow.lean`

**Namespace:** `HFAlgebra`
**Last projected:** 2026-05-29
**Imports:** `AczelSetTheory.Algebra.Subgroup`, `AczelSetTheory.Axioms.OrdinalNat`, `AczelSetTheory.Axioms.Function`, `AczelSetTheory.Axioms.CartProd`, `AczelSetTheory.Axioms.Separation`, `AczelSetTheory.Axioms.CardImage`, `AczelSetTheory.Axioms.Choice`, `AczelSetTheory.Operations.NPow`, `Peano.PeanoNat.Combinatorics.Pow`, `Peano.PeanoNat.Arith`, `Peano.PeanoNat.Primes`, `Peano.Prelim.Classical`
**Opens:** `Peano`, `Peano.Arith`, `Peano.Primes`

Infraestructura para los teoremas de Sylow sobre `HFGroup` finito, vía la prueba combinatorial de McKay (acción cíclica sobre `p`-tuplas con producto = e).

---

### §1–§14. Subgrupos triviales, orden cíclico, carrier de McKay

Incluye: `gpow grp g m` (potencia iterada), `gpowImg grp g m` (imagen `{g^0,...,g^m}`), `cyclicSubgroup grp g` (⟨g⟩ vía orden por WOP), `mckayCarrier grp p` (= `{t ∈ nPow grp.G p | tupleProd t = e}`), `mckayShift grp (σ n) t = ⟪dropHead n t, getHead n t⟫`, `card_mckayCarrier_eq_pow` (D.3: `card (mckayCarrier grp p) = (card grp.G)^(p-1)`).

---

### §15. `predIndex` / `predIter` (índice cíclico decreciente)

```lean
def predIndex (n : ℕ₀) : ℕ₀ → ℕ₀
  | .zero   => n
  | .succ j => j

def predIter (n : ℕ₀) : ℕ₀ → ℕ₀ → ℕ₀
  | .zero,   j => j
  | .succ k, j => predIter n k (predIndex n j)

theorem predIter_zero (n j : ℕ₀) : predIter n 𝟘 j = j
theorem predIter_succ (n k j : ℕ₀) :
    predIter n (σ k) j = predIter n k (predIndex n j)
theorem predIter_succ_right (n k j : ℕ₀) :
    predIter n (σ k) j = predIndex n (predIter n k j)
theorem predIter_add (n a b j : ℕ₀) :
    predIter n (Peano.Add.add a b) j = predIter n b (predIter n a j)
theorem predIter_self_zero (n j : ℕ₀) : predIter n j j = 𝟘
theorem predIter_succ_self (n j : ℕ₀) : predIter n (σ j) j = n
theorem predIter_le_eq_sub (n k j : ℕ₀) (h : le₀ k j) :
    predIter n k j = Peano.Sub.sub j k
theorem sub_sub_self (n j : ℕ₀) (h : le₀ j n) :
    Peano.Sub.sub n (Peano.Sub.sub n j) = j
theorem predIter_period (n j : ℕ₀) (hjn : le₀ j n) :
    predIter n (σ n) j = j
```

---

### §16. `shiftIter_period` (D.4.B parte 2)

```lean
theorem shiftIter_getHead (grp : HFGroup) (n k j : ℕ₀) (h : le₀ j n) (t : HFSet) :
    getHead j (shiftIter grp (σ n) k t) = getHead (predIter n k j) t

theorem shiftIter_period (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    shiftIter grp (σ n) (σ n) t = t
```

---

### §17. Órbitas: definición y cota de cardinal (D.4.C parte 1)

```lean
def orbitEnum (grp : HFGroup) (p : ℕ₀) : ℕ₀ → HFSet → HFSet
  | .zero,   t => HFSet.singleton (shiftIter grp p 𝟘 t)
  | .succ m, t => HFSet.insert (shiftIter grp p (σ m) t) (orbitEnum grp p m t)

def orbitOf (grp : HFGroup) (n : ℕ₀) (t : HFSet) : HFSet :=
  orbitEnum grp (σ n) n t

theorem mem_orbitEnum (grp : HFGroup) (p m : ℕ₀) (t x : HFSet) :
    x ∈ orbitEnum grp p m t ↔ ∃ k : ℕ₀, le₀ k m ∧ x = shiftIter grp p k t
theorem mem_orbitOf (grp : HFGroup) (n : ℕ₀) (t x : HFSet) :
    x ∈ orbitOf grp n t ↔ ∃ k : ℕ₀, le₀ k n ∧ x = shiftIter grp (σ n) k t
theorem orbitEnum_card_le_succ (grp : HFGroup) (p m : ℕ₀) (t : HFSet) :
    le₀ (HFSet.card (orbitEnum grp p m t)) (σ m)
theorem card_orbitOf_le (grp : HFGroup) (n : ℕ₀) (t : HFSet) :
    le₀ (HFSet.card (orbitOf grp n t)) (σ n)
theorem mckayShift_mem_orbitOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) {t' : HFSet}
    (h : t' ∈ orbitOf grp n t) :
    mckayShift grp (σ n) t' ∈ orbitOf grp n t
```

---

### §18. Simetría y partición de órbitas (D.4.C parte 2)

```lean
theorem shiftIter_mem_orbitOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (k : ℕ₀) :
    shiftIter grp (σ n) k t ∈ orbitOf grp n t

def invIdx (n : ℕ₀) : ℕ₀ → ℕ₀
  | .zero    => 𝟘
  | .succ k' => Peano.Sub.sub n k'

theorem invIdx_le (n k : ℕ₀) (h : le₀ k n) : le₀ (invIdx n k) n
theorem shiftIter_invIdx (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (k : ℕ₀) (h : le₀ k n) :
    shiftIter grp (σ n) (invIdx n k) (shiftIter grp (σ n) k t) = t

theorem orbitOf_subset (grp : HFGroup) (n : ℕ₀) (t s : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (hs : s ∈ orbitOf grp n t) :
    orbitOf grp n s ⊆ orbitOf grp n t
theorem orbitOf_eq_of_mem (grp : HFGroup) (n : ℕ₀) (t s : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (hs : s ∈ orbitOf grp n t) :
    orbitOf grp n s = orbitOf grp n t
theorem orbitOf_eq_or_disjoint (grp : HFGroup) (n : ℕ₀) (t s : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (hs : s ∈ HFSet.nPow grp.G (σ n)) :
    orbitOf grp n t = orbitOf grp n s ∨
    (∀ x, ¬ (x ∈ orbitOf grp n t ∧ x ∈ orbitOf grp n s))
```

---

### §19–§21. `periodOf` y sus propiedades

```lean
/-- Período mínimo de `t` bajo el shift: mínimo `k > 0` con `shiftIter k t = t`. -/
def periodOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) : ℕ₀
```

- **Math**: Per(t) = min { k > 0 | shift^k(t) = t }.
- **Computable**: sí, por búsqueda acotada constructiva en `0..σ n`.

| Teorema | Lean signature |
|---------|---------------|
| `periodOf_pos` | `(ht : ...) : lt₀ 𝟘 (periodOf grp n t ht)` |
| `periodOf_ne_zero` | `(ht : ...) : periodOf grp n t ht ≠ 𝟘` |
| `shiftIter_periodOf` | `(ht : ...) : shiftIter grp (σ n) (periodOf grp n t ht) t = t` |
| `periodOf_minimal` | `(ht : ...) (hm_pos : lt₀ 𝟘 m) (hm_eq : shiftIter grp (σ n) m t = t) : le₀ (periodOf grp n t ht) m` |
| `periodOf_le_succ_n` | `(ht : ...) : le₀ (periodOf grp n t ht) (σ n)` |
| `periodOf_dvd_succ_n` | `(ht : ...) : Divides (periodOf grp n t ht) (σ n)` |
| `shiftIter_mul_periodOf` | `(ht : ...) (q : ℕ₀) : shiftIter grp (σ n) (mul q (periodOf grp n t ht)) t = t` |
| `shiftIter_inj_below_period` | `(ht : ...) (i j : ℕ₀) (hi : lt₀ i (periodOf ...)) (hj : lt₀ j (periodOf ...)) : shiftIter ... i t = shiftIter ... j t → i = j` |
| `shiftIter_eq_id_iff_periodOf_dvd` | `(ht : ...) (k : ℕ₀) : shiftIter grp (σ n) k t = t ↔ Divides (periodOf grp n t ht) k` |

---

### §22. D.4.C parte 4: `card (orbitOf) = periodOf`

```lean
theorem card_orbitOf_eq_periodOf (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    HFSet.card (orbitOf grp n t) = periodOf grp n t ht
```

- **Math**: |orb(t)| = Per(t). Vía `orbitOf = periodEnum (σ n) (periodOf) t` y `card_periodEnum_le_period`.

---

### §23. D.4.C parte 5: caso primo — `card (orbitOf) ∈ {𝟙, σ n}`

```lean
theorem card_orbitOf_one_or_succ (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (hprime : Peano.Arith.Prime (σ n)) :
    HFSet.card (orbitOf grp n t) = 𝟙 ∨
    HFSet.card (orbitOf grp n t) = σ n
```

- **Math**: Si `σ n` es primo, Per(t) divide a `σ n`, luego Per(t) ∈ {1, σ n}.

---

### §24. D.4.D parte 1: `card = 1 ↔ t fijo`

```lean
theorem periodOf_eq_one_iff_fixed (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    periodOf grp n t ht = 𝟙 ↔ mckayShift grp (σ n) t = t

theorem card_orbitOf_eq_one_iff_fixed (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) :
    HFSet.card (orbitOf grp n t) = 𝟙 ↔ mckayShift grp (σ n) t = t
```

- **Math**: Per(t) = 1 ↔ shift(t) = t ↔ |orb(t)| = 1.

---

### §25. D.4.D parte 2: no fijo ⇒ `card = σ n`

```lean
theorem card_orbitOf_eq_succ_of_not_fixed (grp : HFGroup) (n : ℕ₀) (t : HFSet)
    (ht : t ∈ HFSet.nPow grp.G (σ n)) (hprime : Peano.Arith.Prime (σ n))
    (hnf : mckayShift grp (σ n) t ≠ t) :
    HFSet.card (orbitOf grp n t) = σ n
```

- **Math**: Si `σ n` primo y `t` no fijo, |orb(t)| = σ n (caso {1, σ n} con 1 descartado).

---

### §26. D.4.D parte 3: `σ n ∣ card S` para S shift-cerrado sin fijos

```lean
theorem succ_n_dvd_card_of_shift_closed_no_fixed
    (grp : HFGroup) (n : ℕ₀) (hprime : Peano.Arith.Prime (σ n)) :
    ∀ (S : HFSet),
      S ⊆ mckayCarrier grp (σ n) →
      (∀ x, x ∈ S → mckayShift grp (σ n) x ≠ x) →
      (∀ x, x ∈ S → mckayShift grp (σ n) x ∈ S) →
      (σ n) ∣ HFSet.card S
```

- **Math**: Si S ⊆ carrier, S cerrado por shift, y S ∩ F = ∅ (sin puntos fijos), entonces `σ n ∣ |S|`.
- **Prueba**: Inducción fuerte (`Peano.WellFounded.strongInductionOn`) sobre `card S`. En cada paso: extraer `t ∈ S` (vía `nonempty_of_ne_empty`), orbita de tamaño `σ n` (§25), `S' = S \ orb(t)` shift-cerrado (§26 helpers), recursión sobre `|S'| < |S|`; combinar vía `divides_add`.

---

### §27. D.4.D conclusión: `σ n ∣ card (mckayFixedPoints)` — **Lema de McKay**

```lean
def mckayFixedPoints (grp : HFGroup) (p : ℕ₀) : HFSet :=
  HFSet.sep (mckayCarrier grp p) (fun t => mckayShift grp p t = t)

theorem mem_mckayFixedPoints (grp : HFGroup) (p : ℕ₀) (t : HFSet) :
    t ∈ mckayFixedPoints grp p
      ↔ t ∈ mckayCarrier grp p ∧ mckayShift grp p t = t

theorem succ_n_dvd_card_mckayFixedPoints
    (grp : HFGroup) (n : ℕ₀) (hprime : Peano.Arith.Prime (σ n))
    (hdvd : (σ n) ∣ HFSet.card grp.G) (hn : n ≠ 𝟘) :
    (σ n) ∣ HFSet.card (mckayFixedPoints grp (σ n))
```

- **Math**: Si `σ n` primo y `σ n ∣ |G|`, entonces `σ n ∣ |F|` donde F = puntos fijos del shift.
- **Prueba**: `|C| = |F| + |S|` (partición carrier = fijos + no-fijos). D.3 da `σ n ∣ |C|`. §26 da `σ n ∣ |S|`. Luego `divides_sub` da `σ n ∣ |F|`.
- **Aplicación**: Cauchy's theorem — existencia de subgrupo de orden p cuando p primo divide |G|.

---

### §28. Punto fijo canónico: `eTuple ∈ mckayFixedPoints`

```lean
theorem eTuple_mem_mckayFixedPoints (grp : HFGroup) (p : ℕ₀) :
    eTuple grp p ∈ mckayFixedPoints grp p
```

- **Math**: La `p`-tupla `(e, e, ..., e)` con todas las componentes iguales al neutro siempre es un punto fijo del shift cíclico.
- **Prueba**: Por inducción en `p`. En el caso base `eTuple grp 0 = ∅` ∈ carrier trivialmente. En el caso sucesor, se verifica que `mckayShift grp (σ n) (eTuple grp (σ n)) = eTuple grp (σ n)` y que `tupleProd grp (σ n) (eTuple grp (σ n)) = e`.

---

### §29–§31. Auxiliares del teorema de Cauchy: orden y subgrupo cíclico

```lean
-- Auxiliares privados (no exportados):
private theorem mckayShift_succ_pair (grp : HFGroup) (m : ℕ₀) (a b : HFSet) :
    mckayShift grp (σ (σ m)) ⟪a, b⟫ = ⟪⟪dropHead m a, b⟫, getHead m a⟫

private theorem shift_fixed_snd_e_implies_eTuple (grp : HFGroup) :
    ∀ (n : ℕ₀) {t : HFSet},
      t ∈ HFSet.nPow grp.G (σ n) → mckayShift grp (σ n) t = t →
      HFSet.snd t = grp.e → t = eTuple grp (σ n)

private theorem shift_fixed_tupleProd_eq_gpow (grp : HFGroup) :
    ∀ (n : ℕ₀) {t : HFSet},
      t ∈ HFSet.nPow grp.G (σ n) → mckayShift grp (σ n) t = t →
      tupleProd grp (σ n) t = gpow grp (HFSet.snd t) (σ n)

-- Exportados:
theorem order_dvd_of_gpow_eq_id (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G)
    (m : ℕ₀) (hm : gpow grp g m = grp.e) : order grp hg ∣ m

theorem order_eq_prime_of_pow (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G)
    {n : ℕ₀} (hp : Peano.Arith.Prime (σ n)) (hg_ne : g ≠ grp.e)
    (hpow : gpow grp g (σ n) = grp.e) : order grp hg = σ n

theorem cyclicCarrier_card_eq_order (grp : HFGroup) {g : HFSet} (hg : g ∈ grp.G) :
    HFSet.card (cyclicCarrier grp hg) = order grp hg
```

- **`order_dvd_of_gpow_eq_id`**: Si `g^m = e`, entonces `order g ∣ m`. Prueba por división euclídea: `m = q · ord + r` con `r < ord`; si `g^r = e`, minimalidad del orden da `r = 0`.
- **`order_eq_prime_of_pow`**: Si `g^p = e`, `p` primo, `g ≠ e`, entonces `order g = p`. Prueba: `ord ∣ p` (por `order_dvd_of_gpow_eq_id`); como `p` primo, `ord = 1` o `ord = p`; `ord = 1 ↔ g = e`, contradicción.
- **`cyclicCarrier_card_eq_order`**: El subgrupo cíclico `⟨g⟩ = {e, g, g², ..., g^(ord-1)}` tiene exactamente `order g` elementos. Prueba: `gpow g i` es inyectiva para `i < ord` (por `gpow_inj_below_order`); la inserción del último elemento cierra en el primero.

---

### §32. Teorema de Cauchy (vía McKay)

```lean
theorem cauchy_minimal (grp : HFGroup) {n : ℕ₀} (hp : Peano.Arith.Prime (σ n))
    (hdvd : σ n ∣ HFSet.card grp.G) :
    ∃ sub : HFSubgroup grp, HFSet.card sub.H = σ n
```

- **Math**: Si `p = σ n` es primo y `p ∣ |G|`, existe un subgrupo de `G` de orden exactamente `p`.
- **Prueba** (argumento de McKay):
  1. El Lema de McKay (§27) da `p ∣ |F|` donde `F = mckayFixedPoints grp p`.
  2. El punto fijo canónico `eTuple grp p ∈ F` (§28) asegura `|F| ≥ 1`.
  3. Como `p ∣ |F|` y `|F| ≥ 1`, se tiene `|F| ≥ p ≥ 2`, así que existe `t ∈ F` con `t ≠ eTuple grp p`.
  4. Para tal `t`: `g = HFSet.snd t ∈ G`, `g ≠ e` (por §29 — si `g = e` entonces `t = eTuple`), y `g^p = e` (por §29 — si `t` es punto fijo, `tupleProd = gpow (snd t) p = e`).
  5. Por §30: `order g = p`. Por §31: `card (cyclicSubgroup g) = p`. ∎

---

### 7c. Exports — `Algebra/Sylow.lean`

**Definiciones públicas:**

`HFAlgebra.pow_dvd_card`, `HFAlgebra.isPSubgroup`, `HFAlgebra.isSylowExponent`, `HFAlgebra.isSylowSubgroup`, `HFAlgebra.HFSubgroup.trivial`, `HFAlgebra.HFSubgroup.trivial_card`, `HFAlgebra.isPSubgroup_of_isSylowSubgroup`, `HFAlgebra.gpow`, `HFAlgebra.gpow_zero`, `HFAlgebra.gpow_succ`, `HFAlgebra.gpow_one`, `HFAlgebra.gpow_mem`, `HFAlgebra.gpow_add`, `HFAlgebra.order`, `HFAlgebra.order_pos`, `HFAlgebra.order_ne_zero`, `HFAlgebra.gpow_order_eq_id`, `HFAlgebra.order_minimal`, `HFAlgebra.order_le_card`, `HFAlgebra.gpow_mul_order_eq_id`, `HFAlgebra.gpow_mod_order`, `HFAlgebra.cyclicCarrier`, `HFAlgebra.cyclicSubgroup`, `HFAlgebra.mckayCarrier`, `HFAlgebra.mckayShift`, `HFAlgebra.mckayFixedPoints`, `HFAlgebra.mem_mckayFixedPoints`, `HFAlgebra.shiftIter`, `HFAlgebra.orbitOf`, `HFAlgebra.periodOf`

**Teoremas D.3 – D.4.D + §28–§32:**

`HFAlgebra.dvd_card_mckayCarrier_succ`, `HFAlgebra.card_orbitOf_eq_periodOf`, `HFAlgebra.card_orbitOf_one_or_succ`, `HFAlgebra.periodOf_eq_one_iff_fixed`, `HFAlgebra.card_orbitOf_eq_one_iff_fixed`, `HFAlgebra.card_orbitOf_eq_succ_of_not_fixed`, `HFAlgebra.succ_n_dvd_card_of_shift_closed_no_fixed`, `HFAlgebra.succ_n_dvd_card_mckayFixedPoints`, `HFAlgebra.eTuple_mem_mckayFixedPoints`, `HFAlgebra.order_dvd_of_gpow_eq_id`, `HFAlgebra.order_eq_prime_of_pow`, `HFAlgebra.cyclicCarrier_card_eq_order`, `HFAlgebra.cauchy_minimal`

---

### 7d. Proyección Sprint B.2 (Computabilidad en cocientes/isomorfismos)

**Módulo base (`Algebra/QuotientGroup.lean`)**

- `HFSubgroup.cosetRep` ahora es **computable** (`def`), implementado por búsqueda efectiva en `grp.G.toList`.
- Nuevos auxiliares privados:
  - `findRepList`
  - `findRepList_sound`
  - `findRepList_complete`
- Revalidado sobre la nueva implementación:
  - `cosetRep_mem_G`
  - `cosetRep_rightCoset_eq`

**Wrappers de cocientes/isomorfismos normalizados a `def`/`abbrev` (sin `noncomputable def`)**

- `Algebra/QuotientGroup.lean`: `quotientOp`, `quotientInv`, `quotientGroup`, `quotientHom`.
- `Algebra/FirstIsomorphism.lean`: `firstIsoFun`, `firstIsoMap`.
- `Algebra/SecondIsomorphism.lean`: `secondIsoFun`, `secondIsoMap`.
- `Algebra/ThirdIsomorphism.lean`: `KmodN_subgroup`, `thirdIsoFun`, `thirdIsoMap`.
- `Algebra/CosetAction.lean`: `cosetAction`.
- `Algebra/CorrespondenceTheorem.lean`: `preimageSubgroup`.

**Estado proyectado (2026-06-02):**

- `Algebra/` queda con **0 `noncomputable def`**.
- Estado global del repositorio: **0 `noncomputable def`** en archivos `.lean` del workspace.
