# Technical Reference — Relations, Functions & Products

**Last updated:** 2026-05-18
**Parent:** [../REFERENCE.md](../REFERENCE.md)
**Related:** [REFERENCE-HFSets.md](REFERENCE-HFSets.md) | [REFERENCE-Algebra.md](REFERENCE-Algebra.md)

@axiom_system: AczelSetTheory
@importance: high

---

## Overview

This file covers the relational and functional layer of the project: ordered pairs (Kuratowski),
binary relations, functions (total, injective, surjective, bijective), relational composition,
inverse, restriction, replacement, and cartesian products.

**Primary namespace:** `HFSet`

| # | File | Status |
|---|------|--------|
| 26 | `AczelSetTheory/Operations/FunctionComp.lean` | ✅ Complete |
| 27 | `AczelSetTheory/Operations/Identity.lean` | ✅ Complete |
| 28 | `AczelSetTheory/Operations/Product.lean` | ✅ Complete |
| 29 | `AczelSetTheory/Axioms/FunctionComp.lean` | ✅ Complete |
| 30 | `AczelSetTheory/Axioms/Identity.lean` | ✅ Complete |
| 31 | `AczelSetTheory/Axioms/Product.lean` | ✅ Complete |
| 32 | `AczelSetTheory/Axioms/Image.lean` | ✅ Complete |
| 33 | `AczelSetTheory/Operations/OrderedPair.lean` | ✅ Complete |
| 34 | `AczelSetTheory/Operations/Relation.lean` | ✅ Complete |
| 35 | `AczelSetTheory/Operations/Function.lean` | ✅ Complete |
| 36 | `AczelSetTheory/Operations/Inverse.lean` | ✅ Complete |
| 37 | `AczelSetTheory/Operations/Restriction.lean` | ✅ Complete |
| 38 | `AczelSetTheory/Operations/Composition.lean` | ✅ Complete |
| 39 | `AczelSetTheory/Operations/Replacement.lean` | ✅ Complete |
| 44 | `AczelSetTheory/Axioms/OrderedPair.lean` | ✅ Complete |
| 47 | `AczelSetTheory/Axioms/Relation.lean` | ✅ Complete |
| 48 | `AczelSetTheory/Axioms/Function.lean` | ✅ Complete |
| 49 | `AczelSetTheory/Axioms/Bijection.lean` | ✅ Complete |
| 50 | `AczelSetTheory/Axioms/Inverse.lean` | ✅ Complete |
| 51 | `AczelSetTheory/Axioms/Composition.lean` | ✅ Complete |
| 52 | `AczelSetTheory/Axioms/Restriction.lean` | ✅ Complete |
| 53 | `AczelSetTheory/Axioms/Replacement.lean` | ✅ Complete |
| 73 | `AczelSetTheory/Operations/CartProd.lean` | ✅ Complete |
| 74 | `AczelSetTheory/Axioms/CartProd.lean` | ✅ Complete |
| 75 | `AczelSetTheory/Operations/NPow.lean` | ✅ Complete |
| 76 | `AczelSetTheory/Axioms/NPow.lean` | ✅ Complete |
| 117 | `AczelSetTheory/Operations/Order.lean` | ✅ Complete |
| 118 | `AczelSetTheory/Axioms/Order.lean` | ✅ Complete |
| 119 | `AczelSetTheory/Axioms/WellOrder.lean` | ✅ Complete |

---

## 4. Definitions

### 4.19 Operations/FunctionComp.lean — `namespace HFSet`

#### 4.19.1 `HFSet.funComp`

```lean
open Classical in
noncomputable def HFSet.funComp (f g : HFSet) : HFSet :=
  HFSet.sep
    (HFSet.powerset (HFSet.powerset
      (HFSet.union (HFSet.sUnion (HFSet.sUnion f)) (HFSet.sUnion (HFSet.sUnion g)))))
    (fun p => ∃ a b c, p = ⟪a, c⟫ ∧ ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f)
```

- **Math**: f ∘f g ≔ {⟪a, c⟫ | ∃ b, ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f}
- Universe: 𝒫(𝒫(⋃⋃f ∪ ⋃⋃g)) — first and second components lie in ⋃⋃f ∪ ⋃⋃g.
- Distinct from `relComp` (which uses a different universe).
- Noncomputable. Notation: `infixl:90 " ∘f "`.

---

### 4.20 Operations/Identity.lean — `namespace HFSet`

#### 4.20.1 `HFSet.idFunc`

```lean
open Classical in
noncomputable def HFSet.idFunc (A : HFSet) : HFSet :=
  HFSet.sep
    (HFSet.powerset (HFSet.powerset A))
    (fun p => ∃ a, a ∈ A ∧ p = HFSet.orderedPair a a)
```

- **Math**: id_A ≔ {⟪a, a⟫ | a ∈ A}
- Universe: 𝒫(𝒫(A)) — because ⟪a, a⟫ = {{a}, {a,a}} and both {a}, {a,a} ⊆ A for any a ∈ A.
- Noncomputable.

---

### 4.21 Operations/Product.lean — `namespace HFSet`

#### 4.21.1 `HFSet.prodHF`

```lean
open Classical in
noncomputable def HFSet.prodHF (A B : HFSet) : HFSet :=
  HFSet.sep
    (HFSet.powerset (HFSet.powerset (HFSet.union A B)))
    (fun p => ∃ a b, a ∈ A ∧ b ∈ B ∧ p = HFSet.orderedPair a b)
```

- **Math**: A × B ≔ {⟪a, b⟫ | a ∈ A ∧ b ∈ B}
- Universe: 𝒫(𝒫(A ∪ B)) — because ⟪a, b⟫ = {{a},{a,b}} and {a},{a,b} ⊆ A ∪ B when a ∈ A, b ∈ B.
- Noncomputable. Notation: `infixl:80 " ×ₛ "`.

---

### 4.22 Axioms/FunctionComp.lean — `namespace HFSet`

No new definitions. Only theorems (see §6.18).

---

### 4.23 Axioms/Identity.lean — `namespace HFSet`

No new definitions. Only theorems (see §6.19).

---

### 4.24 Axioms/Product.lean — `namespace HFSet`

No new definitions. Only theorems (see §6.20).

---

### 4.25 Axioms/Image.lean — `namespace HFSet`

No new definitions. Only theorems (see §6.21).

---

### 4.26 Operations/OrderedPair.lean — `namespace HFSet`

#### 4.26.1 `HFSet.orderedPair`

```lean
def HFSet.orderedPair (a b : HFSet) : HFSet := pair (singleton a) (pair a b)
```

- **Math**: ⟪a, b⟫ ≔ {{a}, {a, b}} (Kuratowski encoding). Notation: `notation "⟪" a ", " b "⟫"`.

#### 4.26.2 `HFSet.fst` / `HFSet.snd`

```lean
noncomputable def HFSet.fst (p : HFSet) (h : ∃ a b, p = ⟪a, b⟫) : HFSet
noncomputable def HFSet.snd (p : HFSet) (h : ∃ a b, p = ⟪a, b⟫) : HFSet
```

- **Math**: projections of an ordered pair; noncomputable, require existence proof.

---

### 4.27 Operations/Relation.lean — `namespace HFSet`

#### 4.27.1 `HFSet.isRelation`

```lean
def HFSet.isRelation (R : HFSet) : Prop := ∀ p, p ∈ R → ∃ a b, p = ⟪a, b⟫
```

- **Math**: R is a relation iff every element is an ordered pair.

#### 4.27.2 `HFSet.domain` / `HFSet.range`

```lean
noncomputable def HFSet.domain (R : HFSet) : HFSet
noncomputable def HFSet.range  (R : HFSet) : HFSet
```

- **Math**: dom(R) = {a | ∃ b, ⟪a, b⟫ ∈ R};  ran(R) = {b | ∃ a, ⟪a, b⟫ ∈ R}.

---

### 4.28 Operations/Function.lean — `namespace HFSet`

#### 4.28.1 `HFSet.isFunction`

```lean
def HFSet.isFunction (f : HFSet) : Prop :=
  isRelation f ∧ ∀ a b₁ b₂, ⟪a, b₁⟫ ∈ f → ⟪a, b₂⟫ ∈ f → b₁ = b₂
```

- **Math**: f is a function iff it is a relation and right-unique.

#### 4.28.2 `HFSet.isTotalFunction`

```lean
def HFSet.isTotalFunction (f A B : HFSet) : Prop :=
  isFunction f ∧ domain f = A ∧ ∀ b, b ∈ range f → b ∈ B
```

- **Math**: f : A → B total function (domain = A, range ⊆ B).

#### 4.28.3 `HFSet.apply`

```lean
noncomputable def HFSet.apply (f a : HFSet) (h : ∃ b, ⟪a, b⟫ ∈ f) : HFSet
```

- **Math**: f(a) — function application; noncomputable via `Classical.choose`.

---

### 4.29 Operations/Inverse.lean — `namespace HFSet`

#### 4.29.1 `HFSet.relInv`

```lean
open Classical in
noncomputable def HFSet.relInv (R : HFSet) : HFSet
```

- **Math**: R⁻¹ ≔ {⟪b, a⟫ | ⟪a, b⟫ ∈ R}. Notation: `postfix:75 "⁻¹ᵣ"`.

---

### 4.30 Operations/Restriction.lean — `namespace HFSet`

#### 4.30.1 `HFSet.restrict` / `HFSet.preimage`

```lean
open Classical in noncomputable def HFSet.restrict (R A : HFSet) : HFSet
open Classical in noncomputable def HFSet.preimage (R B : HFSet) : HFSet
```

- **Math**: R ↾ A ≔ {⟪a, b⟫ ∈ R | a ∈ A}. Notation: `notation:80 R " ↾ " A`.
- preimage R B ≔ {a | ∃ b ∈ B, ⟪a, b⟫ ∈ R}.

---

### 4.31 Operations/Composition.lean — `namespace HFSet`

#### 4.31.1 `HFSet.relComp`

```lean
open Classical in noncomputable def HFSet.relComp (S R : HFSet) : HFSet
```

- **Math**: S ∘ᵣ R ≔ {⟪a, c⟫ | ∃ b, ⟪a, b⟫ ∈ R ∧ ⟪b, c⟫ ∈ S}. Notation: `infixl:90 " ∘ᵣ "`.

#### 4.31.2 `HFSet.imageRel`

```lean
open Classical in noncomputable def HFSet.imageRel (R A : HFSet) : HFSet
```

- **Math**: R[A] ≔ {b | ∃ a ∈ A, ⟪a, b⟫ ∈ R} — relational image of A under R.

---

### 4.32 Operations/Replacement.lean — `namespace HFSet`

#### 4.32.1 `HFSet.image`

```lean
noncomputable def HFSet.image (f A : HFSet) : HFSet
```

- **Math**: f[A] ≔ {y | ∃ x ∈ A, ⟪x, y⟫ ∈ f} — image of A under function f.

---

### 4.44 Operations/CartProd.lean — `namespace HFSet`

#### 4.44.1 `HFSet.mkOrderedPairCList`

```lean
def HFSet.mkOrderedPairCList (a b : CList) : CList :=
  mkPair (mkPair a a) (mkPair a b)
```

- **Math**: ⟨a,b⟩ᵂ ≔ {{a},{a,b}} — Kuratowski ordered pair at CList level.
- Computable.

---

#### 4.44.2 `HFSet.cartProdCList`

```lean
def HFSet.cartProdCList (A B : CList) : CList :=
  match A, B with
  | CList.mk as, CList.mk bs =>
    CList.mk (as.flatMap (fun a => bs.map (fun b => mkOrderedPairCList a b)))
```

- **Math**: A ×_CList B — computable Cartesian product at CList level via `flatMap` and `map`.
- Computable.

---

#### 4.44.3 `HFSet.cartProd`

```lean
def HFSet.cartProd (A B : HFSet) : HFSet :=
  Quotient.liftOn₂ A B
    (fun a b => Quotient.mk CList.Setoid (cartProdCList a b))
    (fun a₁ b₁ a₂ b₂ ha hb =>
      Quotient.sound (cartProdCList_extEq a₁ b₁ a₂ b₂ ha hb))
```

- **Math**: A ×ₕ B — Cartesian product lifted to HFSet quotient.
- Computable. Notation: `infixl:70 " ×ₕ "`.
- Well-defined by internal lemma `cartProdCList_extEq`.

---

### 4.45 Axioms/CartProd.lean — `namespace HFSet`

> No new computable definitions. Exports theorems only (see §6.55).

---

### 4.46 Operations/NPow.lean — `namespace HFSet`

#### 4.46.1 `HFSet.nPow`

```lean
def nPow (A : HFSet) : ℕ₀ → HFSet
  | .zero   => singleton empty
  | .succ n => nPow A n ×ₕ A

@[simp] theorem nPow_zero (A : HFSet) : nPow A 𝟘 = singleton empty := rfl
@[simp] theorem nPow_succ (A : HFSet) (n : ℕ₀) : nPow A (σ n) = nPow A n ×ₕ A := rfl
```

- **Math**: Aⁿ ≔ n-ary Cartesian power of A encoded as nested ordered pairs.
  - A⁰ = {∅}  (the unique 0-tuple)
  - Aⁿ⁺¹ = Aⁿ ×ₕ A  (left-nested pairs)
- Computable. Structural recursion on `n : ℕ₀`.

---

### 4.47 Axioms/NPow.lean — `namespace HFSet`

> No new computable definitions. Exports theorems only (see §6.57).

---

### 4.117 Operations/Order.lean — `namespace HFSet`

#### 4.117.1 Order Properties

Basic predicates for a relation `R` on a set `A`:
- `isReflexive`, `isIrreflexive`
- `isSymmetric`, `isAntisymmetric`
- `isTransitive`
- `isConnected`, `isTotal`, `isTrichotomous`

Compound predicates:
- `isPreorder`, `isEquivRel`, `isPartialOrder`
- `isStrictOrder`, `isTotalOrder`, `isStrictTotalOrder`

Element predicates:
- `isMinimum`, `isMaximum`, `isMinimal`, `isMaximal`
- `isLowerBound`, `isUpperBound`, `isInfimum`, `isSupremum`

Well-foundedness:
- `isWellFounded`: Every non-empty subset has a minimum.
- `isStrictlyWellFounded`: Every non-empty subset has a minimal element.
- `isWellOrder`: Total order and well-founded.

---

### 4.118 Axioms/Order.lean — `namespace HFSet`

> No new definitions. Exports theorems only.

---

### 4.119 Axioms/WellOrder.lean — `namespace HFSet`

> No new definitions. Exports theorems only.

---

## 6. Theorems

### 6.18 Axioms/FunctionComp.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_funComp` | `{f g p : HFSet} : p ∈ f ∘f g ↔ ∃ a b c, p = ⟪a, c⟫ ∧ ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f` |
| 2 | `mem_funComp_pair` | `{f g a c : HFSet} : ⟪a, c⟫ ∈ f ∘f g ↔ ∃ b, ⟪a, b⟫ ∈ g ∧ ⟪b, c⟫ ∈ f` |
| 3 | `funComp_isRelation` | `{f g : HFSet} : isRelation (f ∘f g)` |
| 4 | `isFunction_funComp` | `{f g : HFSet} (hf : isFunction f) (hg : isFunction g) : isFunction (f ∘f g)` |
| 5 | `mem_domain_funComp` | `{f g a : HFSet} : a ∈ domain (f ∘f g) ↔ ∃ b, ⟪a, b⟫ ∈ g ∧ ∃ c, ⟪b, c⟫ ∈ f` |
| 6 | `mem_range_funComp` | `{f g c : HFSet} : c ∈ range (f ∘f g) ↔ ∃ b, b ∈ range g ∧ ⟪b, c⟫ ∈ f` |
| 7 | `isInjective_funComp` | `{f g : HFSet} (hf : isInjective f) (hg : isInjective g) : isInjective (f ∘f g)` |
| 8 | `isSurjective_funComp` | `{f g C : HFSet} (hf : isSurjective f C) (hg : isSurjective g (domain f)) : isSurjective (f ∘f g) C` |
| 9 | `isTotalFunction_funComp` | `{f g A B C : HFSet} (hf : isTotalFunction f B C) (hg : isTotalFunction g A B) : isTotalFunction (f ∘f g) A C` |
| 10 | `isBijective_funComp` | `{f g A B C : HFSet} (hf : isBijective f B C) (hg : isBijective g A B) : isBijective (f ∘f g) A C` |

### 6.19 Axioms/Identity.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_idFunc` | `{A p : HFSet} : p ∈ idFunc A ↔ ∃ a, a ∈ A ∧ p = ⟪a, a⟫` |
| 2 | `mem_idFunc_pair` | `{A a b : HFSet} : ⟪a, b⟫ ∈ idFunc A ↔ a = b ∧ a ∈ A` |
| 3 | `idFunc_isRelation` | `{A : HFSet} : isRelation (idFunc A)` |
| 4 | `isFunction_idFunc` | `{A : HFSet} : isFunction (idFunc A)` |
| 5 | `domain_idFunc` | `{A : HFSet} : domain (idFunc A) = A` |
| 6 | `range_idFunc` | `{A : HFSet} : range (idFunc A) = A` |
| 7 | `isTotalFunction_idFunc` | `{A : HFSet} : isTotalFunction (idFunc A) A A` |
| 8 | `isInjective_idFunc` | `{A : HFSet} : isInjective (idFunc A)` |
| 9 | `isSurjective_idFunc` | `{A : HFSet} : isSurjective (idFunc A) A` |
| 10 | `isBijective_idFunc` | `{A : HFSet} : isBijective (idFunc A) A A` |
| 11 | `mem_funComp_idFunc` | `{f A a c : HFSet} : ⟪a, c⟫ ∈ f ∘f idFunc A ↔ a ∈ A ∧ ⟪a, c⟫ ∈ f` |
| 12 | `mem_idFunc_funComp` | `{f B a c : HFSet} : ⟪a, c⟫ ∈ idFunc B ∘f f ↔ ⟪a, c⟫ ∈ f ∧ c ∈ B` |
| 13 | `funComp_idFunc_eq` | `{f A B : HFSet} (hf : isTotalFunction f A B) : f ∘f idFunc A = f` |
| 14 | `idFunc_funComp_eq` | `{f A B : HFSet} (hf : isTotalFunction f A B) : idFunc B ∘f f = f` |
| 15 | `relInv_idFunc` | `{A : HFSet} : (idFunc A)⁻¹ᵣ = idFunc A` |

### 6.20 Axioms/Product.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_prodHF` | `{A B p : HFSet} : p ∈ A ×ₛ B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ p = ⟪a, b⟫` |
| 2 | `mem_prodHF_pair` | `{A B a b : HFSet} : ⟪a, b⟫ ∈ A ×ₛ B ↔ a ∈ A ∧ b ∈ B` |
| 3 | `prodHF_isRelation` | `{A B : HFSet} : isRelation (A ×ₛ B)` |
| 4 | `fst_of_mem_prodHF` | `{A B a b : HFSet} (h : ⟪a, b⟫ ∈ A ×ₛ B) : a ∈ A` |
| 5 | `snd_of_mem_prodHF` | `{A B a b : HFSet} (h : ⟪a, b⟫ ∈ A ×ₛ B) : b ∈ B` |
| 6 | `prodHF_empty_left` | `{B : HFSet} : empty ×ₛ B = empty` |
| 7 | `prodHF_empty_right` | `{A : HFSet} : A ×ₛ empty = empty` |
| 8 | `isTotalFunction_subset_prodHF` | `{f A B : HFSet} (hf : isTotalFunction f A B) : ∀ p, p ∈ f → p ∈ A ×ₛ B` |

### 6.21 Axioms/Image.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `imageRel_subset_range` | `{f A : HFSet} : imageRel f A ⊆ range f` |
| 2 | `imageRel_mono` | `{f A B : HFSet} (h : A ⊆ B) : imageRel f A ⊆ imageRel f B` |
| 3 | `imageRel_union` | `{f A B : HFSet} : imageRel f (union A B) = union (imageRel f A) (imageRel f B)` |
| 4 | `imageRel_domain_eq_range` | `{f : HFSet} : imageRel f (domain f) = range f` |
| 5 | `imageRel_codomain` | `{f dom cod : HFSet} (hf : isTotalFunction f dom cod) (A : HFSet) : imageRel f A ⊆ cod` |
| 6 | `imageRel_funComp` | `{f g A : HFSet} : imageRel (f ∘f g) A = imageRel f (imageRel g A)` |
| 7 | `imageRel_idFunc` | `{A B : HFSet} : imageRel (idFunc A) B = inter B A` |

### 6.25 Axioms/OrderedPair.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `orderedPair_eq_iff` | `(a b c d : HFSet) : orderedPair a b = orderedPair c d ↔ a = c ∧ b = d` |

### 6.28 Axioms/Relation.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `fst_mem_sUnion_sUnion` | `(a b R : HFSet) (h : ⟪a, b⟫ ∈ R) : a ∈ sUnion (sUnion R)` |
| 2 | `snd_mem_sUnion_sUnion` | `(a b R : HFSet) (h : ⟪a, b⟫ ∈ R) : b ∈ sUnion (sUnion R)` |
| 3 | `mem_domain_iff` | `(R a : HFSet) : a ∈ domain R ↔ ∃ b, ⟪a, b⟫ ∈ R` |
| 4 | `mem_range_iff` | `(R b : HFSet) : b ∈ range R ↔ ∃ a, ⟪a, b⟫ ∈ R` |
| 5 | `domain_empty` | `domain empty = empty` |
| 6 | `range_empty` | `range empty = empty` |
| 7 | `isRelation_empty` | `isRelation empty` |

### 6.29 Axioms/Function.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `apply_mem` | `(f a : HFSet) (h : ∃ b, ⟪a, b⟫ ∈ f) : ⟪a, apply f a h⟫ ∈ f` |
| 2 | `apply_eq_of_mem` | `(f a b : HFSet) (hf : isFunction f) (hab : ⟪a, b⟫ ∈ f) : apply f a ⟨b, hab⟩ = b` |
| 3 | `totalFunction_apply_mem` | `(f A B a : HFSet) (hf : isTotalFunction f A B) (ha : a ∈ A) : ⟪a, apply f a ...⟫ ∈ f` |
| 4 | `isFunction_empty` | `isFunction empty` |
| 5 | `isFunction_unique` | `(f a b₁ b₂ : HFSet) (hf : isFunction f) (h₁ : ⟪a, b₁⟫ ∈ f) (h₂ : ⟪a, b₂⟫ ∈ f) : b₁ = b₂` |
| 6 | `mem_domain_of_mem` | `(f a b : HFSet) (h : ⟪a, b⟫ ∈ f) : a ∈ domain f` |
| 7 | `mem_range_of_mem` | `(f a b : HFSet) (h : ⟪a, b⟫ ∈ f) : b ∈ range f` |

### 6.30 Axioms/Bijection.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `isInjective_empty` | `isInjective empty` |
| 2 | `isInjective_restrict` | `{f A : HFSet} → (hf : isInjective f) → isInjective (f ↾ A)` |
| 3 | `isSurjective_empty_codomain` | `(f : HFSet) → isSurjective f empty` |
| 4 | `isSurjective_range` | `(f : HFSet) → isSurjective f (range f)` |
| 5 | `isSurjective_iff_range_eq` | `{f A B : HFSet} → (hf : isTotalFunction f A B) → (isSurjective f B ↔ range f = B)` |
| 6 | `isBijective_intro` | `{f A B : HFSet} → (hf : isTotalFunction f A B) → (hi : isInjective f) → (hs : isSurjective f B) → isBijective f A B` |
| 7 | `isBijective_isTotalFunction` | `{f A B : HFSet} → (hf : isBijective f A B) → isTotalFunction f A B` |
| 8 | `isBijective_isFunction` | `{f A B : HFSet} → (hf : isBijective f A B) → isFunction f` |
| 9 | `isBijective_isInjective` | `{f A B : HFSet} → (hf : isBijective f A B) → isInjective f` |
| 10 | `isBijective_isSurjective` | `{f A B : HFSet} → (hf : isBijective f A B) → isSurjective f B` |
| 11 | `isBijective_domain_eq` | `{f A B : HFSet} → (hf : isBijective f A B) → domain f = A` |
| 12 | `isBijective_range_eq` | `{f A B : HFSet} → (hf : isBijective f A B) → range f = B` |
| 13 | `isBijective_empty` | `isBijective empty empty empty` |

### 6.31 Axioms/Inverse.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_relInv` | `{R p : HFSet} : p ∈ R⁻¹ᵣ ↔ ∃ a b, ⟪a, b⟫ ∈ R ∧ p = ⟪b, a⟫` |
| 2 | `mem_relInv_pair` | `{R a b : HFSet} : ⟪b, a⟫ ∈ R⁻¹ᵣ ↔ ⟪a, b⟫ ∈ R` |
| 3 | `relInv_isRelation` | `{R : HFSet} : isRelation (R⁻¹ᵣ)` |
| 4 | `domain_relInv` | `{R : HFSet} : domain (R⁻¹ᵣ) = range R` |
| 5 | `range_relInv` | `{R : HFSet} : range (R⁻¹ᵣ) = domain R` |
| 6 | `relInv_relInv` | `{R : HFSet} (hR : isRelation R) : (R⁻¹ᵣ)⁻¹ᵣ = R` |
| 7 | `isFunction_relInv` | `{f : HFSet} (hi : isInjective f) : isFunction (f⁻¹ᵣ)` |
| 8 | `isInjective_relInv` | `{f : HFSet} (hf : isFunction f) : isInjective (f⁻¹ᵣ)` |
| 9 | `isSurjective_relInv` | `{f A : HFSet} (hdom : domain f = A) : isSurjective (f⁻¹ᵣ) A` |
| 10 | `isBijective_relInv` | `{f A B : HFSet} (hf : isBijective f A B) : isBijective (f⁻¹ᵣ) B A` |

### 6.32 Axioms/Composition.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `fst_in` | `(a b R : HFSet) (h : ⟪a, b⟫ ∈ R) : a ∈ sUnion (sUnion R)` |
| 2 | `snd_in` | `(a b R : HFSet) (h : ⟪a, b⟫ ∈ R) : b ∈ sUnion (sUnion R)` |
| 3 | `mem_imageRel` | `{R A b : HFSet} : b ∈ imageRel R A ↔ ∃ a, a ∈ A ∧ ⟪a, b⟫ ∈ R` |
| 4 | `imageRel_empty_rel` | `{A : HFSet} : imageRel empty A = empty` |
| 5 | `imageRel_empty_set` | `{R : HFSet} : imageRel R empty = empty` |
| 6 | `mem_relComp` | `{R S c : HFSet} : c ∈ S ∘ᵣ R ↔ ∃ a b, ⟪a, b⟫ ∈ R ∧ ⟪b, c⟫ ∈ S` |
| 7 | `relComp_empty_left` | `{R : HFSet} : empty ∘ᵣ R = empty` |
| 8 | `relComp_empty_right` | `{S : HFSet} : S ∘ᵣ empty = empty` |

### 6.33 Axioms/Restriction.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_restrict` | `{R A p : HFSet} : p ∈ (R ↾ A) ↔ p ∈ R ∧ ∃ a b, p = ⟪a, b⟫ ∧ a ∈ A` |
| 2 | `restrict_subset` | `{R A : HFSet} : (R ↾ A) ⊆ R` |
| 3 | `restrict_isRelation` | `{R A : HFSet} (hR : isRelation R) : isRelation (R ↾ A)` |
| 4 | `mem_restrict_pair` | `{R A a b : HFSet} : ⟪a, b⟫ ∈ (R ↾ A) ↔ ⟪a, b⟫ ∈ R ∧ a ∈ A` |
| 5 | `mem_preimage` | `{R B a : HFSet} : a ∈ preimage R B ↔ ∃ b, b ∈ B ∧ ⟪a, b⟫ ∈ R` |
| 6 | `preimage_empty_set` | `{R : HFSet} : preimage R empty = empty` |

### 6.34 Axioms/Replacement.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_image` | `(f A y : HFSet) : y ∈ image f A ↔ ∃ x, x ∈ A ∧ ⟪x, y⟫ ∈ f` |
| 2 | `image_empty` | `(f : HFSet) : image f empty = empty` |
| 3 | `image_of_empty` | `(A : HFSet) : image empty A = empty` |
| 4 | `image_subset_range` | `(f A y : HFSet) (h : y ∈ image f A) : y ∈ range f` |
| 5 | `apply_mem_image` | `(f A x : HFSet) (_hf : isFunction f) (hxA : x ∈ A) (hx : ∃ b, ⟪x, b⟫ ∈ f) : apply f x hx ∈ image f A` |
| 6 | `image_totalFunction_subset` | `(f A B y : HFSet) (hf : isTotalFunction f A B) (hy : y ∈ image f A) : y ∈ B` |

### 6.56 Operations/NPow.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `nPow_zero` | `@[simp] (A : HFSet) : nPow A 𝟘 = singleton empty` |
| 2 | `nPow_succ` | `@[simp] (A : HFSet) (n : ℕ₀) : nPow A (σ n) = nPow A n ×ₕ A` |

### 6.57 Axioms/NPow.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_nPow_zero` | `(t A : HFSet) : t ∈ nPow A 𝟘 ↔ t = empty` |
| 2 | `mem_nPow_succ` | `(t A : HFSet) (n : ℕ₀) : t ∈ nPow A (σ n) ↔ ∃ s ∈ nPow A n, ∃ a ∈ A, t = ⟪s, a⟫` |

### 6.118 Axioms/Order.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `isPartialOrder_of_totalOrder` | `{R A : HFSet} (h : isTotalOrder R A) : isPartialOrder R A` |
| 2 | `isConnected_of_isTotal` | `{R A : HFSet} (h : isTotal R A) : isConnected R A` |
| 3 | `isAntisymmetric_of_strictOrder` | `{R A : HFSet} (hirr : isIrreflexive R A) (htr : isTransitive R A) : isAntisymmetric R A` |
| 4 | `isPartialOrder_empty` | `(R : HFSet) : isPartialOrder R empty` |
| 5 | `minimum_unique` | `{R A x y : HFSet} (hanti : isAntisymmetric R A) (hx : isMinimum R A x) (hy : isMinimum R A y) : x = y` |
| 6 | `isMinimal_of_isMinimum` | `{R A x : HFSet} (hanti : isAntisymmetric R A) (hmin : isMinimum R A x) : isMinimal R A x` |
| 7 | `isMinimum_of_isMinimal_total` | `{R A x : HFSet} (htot : isTotalOrder R A) (hmin : isMinimal R A x) : isMinimum R A x` |
| 8 | `isPartialOrder_restrict` | `{R A B : HFSet} (h : isPartialOrder R A) (hB : B ⊆ A) : isPartialOrder R B` |
| 9 | `isWellOrder_restrict` | `{R A B : HFSet} (hwo : isWellOrder R A) (hB : B ⊆ A) : isWellOrder R B` |
| 10 | `isWellOrder_empty` | `(R : HFSet) : isWellOrder R empty` |

### 6.119 Axioms/WellOrder.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `wf_induction` | `{R A : HFSet} (hwf : isStrictlyWellFounded R A) {P : HFSet → Prop} [DecidablePred P] (step : ∀ x ∈ A, (∀ y ∈ A, ⟪y, x⟫ ∈ R → P y) → P x) : ∀ x ∈ A, P x` |
| 2 | `minimum_in_nonempty` | `{R A S : HFSet} (hwo : isWellOrder R A) (hS : S ⊆ A) (hne : S ≠ empty) : ∃ m, isMinimum R S m` |
| 3 | `wellOrder_minimum_unique` | `{R A S x y : HFSet} (hwo : isWellOrder R A) (hS : S ⊆ A) (hx : isMinimum R S x) (hy : isMinimum R S y) : x = y` |
| 4 | `wo_induction` | `{R A : HFSet} (hwo : isWellOrder R A) {P : HFSet → Prop} [DecidablePred P] (step : ∀ x ∈ A, (∀ y ∈ A, ⟪y, x⟫ ∈ R → y ≠ x → P y) → P x) : ∀ x ∈ A, P x` |
| 5 | `no_infinite_descent` | `{R A : HFSet} (hwf : isStrictlyWellFounded R A) {f : ℕ₀ → HFSet} (hf_mem : ∀ n, f n ∈ A) (hf_desc : ∀ n, ⟪f (σ n), f n⟫ ∈ R) : False` |

---

### 6.54 Operations/CartProd.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `orderedPair_eq_mk` | `(a b : CList) : ⟪Quotient.mk CList.Setoid a, Quotient.mk CList.Setoid b⟫ = Quotient.mk CList.Setoid (mkOrderedPairCList a b)` |
| 2 | `mem_cartProdCList_iff` | `(z : CList) (as bs : PList CList) : CList.mem z (cartProdCList (CList.mk as) (CList.mk bs)) = true ↔ ∃ a b : CList, CList.mem a (CList.mk as) = true ∧ CList.mem b (CList.mk bs) = true ∧ CList.extEq z (mkOrderedPairCList a b) = true` |

### 6.55 Axioms/CartProd.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_cartProd` | `(z A B : HFSet) : z ∈ A ×ₕ B ↔ ∃ a b, a ∈ A ∧ b ∈ B ∧ z = ⟪a, b⟫` |
| 2 | `mem_cartProd_pair` | `(a b A B : HFSet) (ha : a ∈ A) (hb : b ∈ B) : ⟪a, b⟫ ∈ A ×ₕ B` |
| 3 | `cartProd_empty_left` | `(B : HFSet) : empty ×ₕ B = empty` |
| 4 | `cartProd_empty_right` | `(A : HFSet) : A ×ₕ empty = empty` |
| 5 | `cartProd_isRelation` | `(A B : HFSet) : ∀ z, z ∈ A ×ₕ B → ∃ a b, z = ⟪a, b⟫` |

---

## 7. Exports per Module

### Operations/FunctionComp.lean

`HFSet.funComp`, notation `∘f` (infixl:90)

### Operations/Identity.lean

`HFSet.idFunc`

### Operations/Product.lean

`HFSet.prodHF`, notation `×ₛ` (infixl:80)

### Axioms/FunctionComp.lean

`HFSet.mem_funComp`, `HFSet.mem_funComp_pair`, `HFSet.funComp_isRelation`, `HFSet.isFunction_funComp`, `HFSet.mem_domain_funComp`, `HFSet.mem_range_funComp`, `HFSet.isInjective_funComp`, `HFSet.isSurjective_funComp`, `HFSet.isTotalFunction_funComp`, `HFSet.isBijective_funComp`

### Axioms/Identity.lean

`HFSet.mem_idFunc`, `HFSet.mem_idFunc_pair`, `HFSet.idFunc_isRelation`, `HFSet.isFunction_idFunc`, `HFSet.domain_idFunc`, `HFSet.range_idFunc`, `HFSet.isTotalFunction_idFunc`, `HFSet.isInjective_idFunc`, `HFSet.isSurjective_idFunc`, `HFSet.isBijective_idFunc`, `HFSet.mem_funComp_idFunc`, `HFSet.mem_idFunc_funComp`, `HFSet.funComp_idFunc_eq`, `HFSet.idFunc_funComp_eq`, `HFSet.relInv_idFunc`

### Axioms/Product.lean

`HFSet.mem_prodHF`, `HFSet.mem_prodHF_pair`, `HFSet.prodHF_isRelation`, `HFSet.fst_of_mem_prodHF`, `HFSet.snd_of_mem_prodHF`, `HFSet.prodHF_empty_left`, `HFSet.prodHF_empty_right`, `HFSet.isTotalFunction_subset_prodHF`

### Axioms/Image.lean

`HFSet.imageRel_subset_range`, `HFSet.imageRel_mono`, `HFSet.imageRel_union`, `HFSet.imageRel_domain_eq_range`, `HFSet.imageRel_codomain`, `HFSet.imageRel_funComp`, `HFSet.imageRel_idFunc`

### Operations/OrderedPair.lean

`HFSet.orderedPair`, `HFSet.fst`, `HFSet.snd`, notation `⟪a, b⟫`

### Operations/Relation.lean

`HFSet.isRelation`, `HFSet.domain`, `HFSet.range`

### Operations/Function.lean

`HFSet.isFunction`, `HFSet.isTotalFunction`, `HFSet.apply`

### Operations/Inverse.lean

`HFSet.relInv`, notation `⁻¹ᵣ`

### Operations/Restriction.lean

`HFSet.restrict`, `HFSet.preimage`, notation `↾`

### Operations/Composition.lean

`HFSet.relComp`, `HFSet.imageRel`, notation `∘ᵣ`

### Operations/Replacement.lean

`HFSet.image`

### Axioms/OrderedPair.lean

`HFSet.orderedPair_eq_iff`

### Axioms/Relation.lean

`HFSet.fst_mem_sUnion_sUnion`, `HFSet.snd_mem_sUnion_sUnion`, `HFSet.mem_domain_iff`, `HFSet.mem_range_iff`, `HFSet.domain_empty`, `HFSet.range_empty`, `HFSet.isRelation_empty`

### Axioms/Function.lean

`HFSet.isInjective`, `HFSet.isSurjective`, `HFSet.isBijective`, `HFSet.apply_mem`, `HFSet.apply_eq_of_mem`, `HFSet.totalFunction_apply_mem`, `HFSet.isFunction_empty`, `HFSet.isFunction_unique`, `HFSet.mem_domain_of_mem`, `HFSet.mem_range_of_mem`

### Axioms/Bijection.lean

`HFSet.isInjective_empty`, `HFSet.isInjective_restrict`, `HFSet.isSurjective_empty_codomain`, `HFSet.isSurjective_range`, `HFSet.isSurjective_iff_range_eq`, `HFSet.isBijective_intro`, `HFSet.isBijective_isTotalFunction`, `HFSet.isBijective_isFunction`, `HFSet.isBijective_isInjective`, `HFSet.isBijective_isSurjective`, `HFSet.isBijective_domain_eq`, `HFSet.isBijective_range_eq`, `HFSet.isBijective_empty`

### Axioms/Inverse.lean

`HFSet.mem_relInv`, `HFSet.mem_relInv_pair`, `HFSet.relInv_isRelation`, `HFSet.domain_relInv`, `HFSet.range_relInv`, `HFSet.relInv_relInv`, `HFSet.isFunction_relInv`, `HFSet.isInjective_relInv`, `HFSet.isSurjective_relInv`, `HFSet.isBijective_relInv`

### Axioms/Composition.lean

`HFSet.fst_in`, `HFSet.snd_in`, `HFSet.mem_imageRel`, `HFSet.imageRel_empty_rel`, `HFSet.imageRel_empty_set`, `HFSet.mem_relComp`, `HFSet.relComp_empty_left`, `HFSet.relComp_empty_right`

### Axioms/Restriction.lean

`HFSet.mem_restrict`, `HFSet.restrict_subset`, `HFSet.restrict_isRelation`, `HFSet.mem_restrict_pair`, `HFSet.mem_preimage`, `HFSet.preimage_empty_set`

### Axioms/Replacement.lean

`HFSet.mem_image`, `HFSet.image_empty`, `HFSet.image_of_empty`, `HFSet.image_subset_range`, `HFSet.apply_mem_image`, `HFSet.image_totalFunction_subset`

### Operations/CartProd.lean

`HFSet.mkOrderedPairCList`, `HFSet.cartProdCList`, `HFSet.cartProd`, `HFSet.orderedPair_eq_mk`, `HFSet.mem_cartProdCList_iff`, notation `×ₕ` (infixl:70)

### Axioms/CartProd.lean

`HFSet.mem_cartProd`, `HFSet.mem_cartProd_pair`, `HFSet.cartProd_empty_left`, `HFSet.cartProd_empty_right`, `HFSet.cartProd_isRelation`

### Operations/NPow.lean

`HFSet.nPow`, `HFSet.nPow_zero`, `HFSet.nPow_succ`

### Axioms/NPow.lean

`HFSet.mem_nPow_zero`, `HFSet.mem_nPow_succ`

### Operations/Order.lean

`HFSet.isReflexive`, `HFSet.isIrreflexive`, `HFSet.isSymmetric`, `HFSet.isAntisymmetric`, `HFSet.isTransitive`, `HFSet.isConnected`, `HFSet.isTotal`, `HFSet.isTrichotomous`, `HFSet.isPreorder`, `HFSet.isEquivRel`, `HFSet.isPartialOrder`, `HFSet.isStrictOrder`, `HFSet.isTotalOrder`, `HFSet.isStrictTotalOrder`, `HFSet.isMinimum`, `HFSet.isMaximum`, `HFSet.isMinimal`, `HFSet.isMaximal`, `HFSet.isLowerBound`, `HFSet.isUpperBound`, `HFSet.isInfimum`, `HFSet.isSupremum`, `HFSet.isWellFounded`, `HFSet.isStrictlyWellFounded`, `HFSet.isWellOrder`

### Axioms/Order.lean

`HFSet.isPartialOrder_of_totalOrder`, `HFSet.isPreorder_of_partialOrder`, `HFSet.isPreorder_of_totalOrder`, `HFSet.isStrictOrder_of_strictTotalOrder`, `HFSet.isConnected_of_isTotal`, `HFSet.isConnected_of_isTrichotomous`, `HFSet.isAntisymmetric_of_strictOrder`, `HFSet.isReflexive_empty`, `HFSet.isIrreflexive_empty`, `HFSet.isSymmetric_empty`, `HFSet.isAntisymmetric_empty`, `HFSet.isTransitive_empty`, `HFSet.isTotal_empty`, `HFSet.isTrichotomous_empty`, `HFSet.isPreorder_empty`, `HFSet.isPartialOrder_empty`, `HFSet.isTotalOrder_empty`, `HFSet.isStrictOrder_empty`, `HFSet.minimum_unique`, `HFSet.maximum_unique`, `HFSet.isMinimal_of_isMinimum`, `HFSet.isMaximal_of_isMaximum`, `HFSet.isMinimum_of_isMinimal_total`, `HFSet.isReflexive_restrict`, `HFSet.isIrreflexive_restrict`, `HFSet.isSymmetric_restrict`, `HFSet.isAntisymmetric_restrict`, `HFSet.isTransitive_restrict`, `HFSet.isTotal_restrict`, `HFSet.isTrichotomous_restrict`, `HFSet.isPreorder_restrict`, `HFSet.isPartialOrder_restrict`, `HFSet.isTotalOrder_restrict`, `HFSet.isStrictOrder_restrict`, `HFSet.isWellFounded_restrict`, `HFSet.isStrictlyWellFounded_restrict`, `HFSet.isWellOrder_restrict`, `HFSet.isWellFounded_empty`, `HFSet.isStrictlyWellFounded_empty`, `HFSet.isWellOrder_empty`, `HFSet.infimum_unique`, `HFSet.supremum_unique`

### Axioms/WellOrder.lean

`HFSet.wf_induction`, `HFSet.minimum_in_nonempty`, `HFSet.wellOrder_minimum_unique`, `HFSet.wo_induction`, `HFSet.no_infinite_descent`

