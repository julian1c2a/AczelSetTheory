# Technical Reference — HFSets (Hereditarily Finite Sets — Core Layer)

**Last updated:** 2026-05-16
**Parent:** [../REFERENCE.md](../REFERENCE.md)
**Related:** [REFERENCE-CList.md](REFERENCE-CList.md) | [REFERENCE-Relations.md](REFERENCE-Relations.md) | [REFERENCE-Algebra.md](REFERENCE-Algebra.md)

@axiom_system: AczelSetTheory
@importance: high

---

## Overview

The `HFSets` layer defines `HFSet := Quotient CList.Setoid`, the main type of the project.
It provides the **Zermelo axioms** (extensionality, empty set, pairs, union, separation,
intersection, set difference, powerset) all as **proven theorems** — not postulated.

**Entry files:**

- [`AczelSetTheory/HFSets.lean`](../AczelSetTheory/HFSets.lean) — core type and membership
- [`AczelSetTheory/Notation.lean`](../AczelSetTheory/Notation.lean) — notation macros and numerals
- [`AczelSetTheory/Operations/`](../AczelSetTheory/Operations/) — computable set operations
- [`AczelSetTheory/Axioms/`](../AczelSetTheory/Axioms/) — derived axiom theorems

**Primary namespace:** `HFSet`
**Depends on:** [REFERENCE-CList.md](REFERENCE-CList.md)

| # | File | Status |
|---|------|--------|
| 9 | `AczelSetTheory/HFSets.lean` | ✅ Complete |
| 10 | `AczelSetTheory/Operations/Union.lean` | ✅ Complete |
| 11 | `AczelSetTheory/Operations/Intersection.lean` | ✅ Complete |
| 12 | `AczelSetTheory/Operations/Setminus.lean` | ✅ Complete |
| 13 | `AczelSetTheory/Operations/Separation.lean` | ✅ Complete |
| 14 | `AczelSetTheory/Operations/Pair.lean` | ✅ Complete |
| 15 | `AczelSetTheory/Operations/Powerset.lean` | ✅ Complete |
| 16 | `AczelSetTheory/Axioms/Union.lean` | ✅ Complete |
| 17 | `AczelSetTheory/Axioms/Intersection.lean` | ✅ Complete |
| 18 | `AczelSetTheory/Axioms/Setminus.lean` | ✅ Complete |
| 19 | `AczelSetTheory/Axioms/Separation.lean` | ✅ Complete |
| 20 | `AczelSetTheory/Axioms/Pair.lean` | ✅ Complete |
| 21 | `AczelSetTheory/Axioms/Powerset.lean` | ✅ Complete |
| 22 | `AczelSetTheory/Notation.lean` | ✅ Complete |
| 78 | `AczelSetTheory/Axioms/Fintype.lean` | ✅ Complete |

---

## 4. Definitions

### 4.8 HFSets.lean

#### 4.8.1 `CList.Setoid`

```lean
def CList.Setoid : Setoid CList where
  r A B := CList.extEq A B = true
  iseqv := { refl := extEq_refl, symm := ..., trans := extEq_trans }
```

- **Math**: A ~ B ⟺ extEq(A, B) = true. Equivalence relation.
- Computable.

#### 4.8.2 `HFSet`

```lean
def HFSet := Quotient CList.Setoid
```

- **Math**: HF ≔ CList / ~  (hereditarily finite sets as equivalence classes)
- Computable.

#### 4.8.3 `HFSet.repr`

```lean
def repr (s : HFSet) : CList :=
  Quotient.lift CList.normalize (fun _ _ h => normalize_eq_of_extEq h) s
```

- **Math**: repr([A]) ≔ norm(A). Well-defined by `normalize_eq_of_extEq`.
- Computable.

#### 4.8.4 `HFSet.empty`

```lean
def empty : HFSet := Quotient.mk CList.Setoid CList.empty
```

- **Math**: ∅_HF ≔ [∅]
- Computable.

#### 4.8.5 `HFSet.Mem`

```lean
def Mem (x A : HFSet) : Prop :=
  Quotient.liftOn₂ x A (fun a b => CList.mem a b = true) ...
```

- **Math**: x ∈ A ⟺ mem(x̃, Ã) = true, where x̃, Ã are any CList representatives.
- Well-defined by `mem_respects` (private).
- Computable (via `Quotient.liftOn₂`).

#### 4.8.6 `Membership HFSet HFSet` instance

```lean
instance : Membership HFSet HFSet where
  mem A x := Mem x A
```

- Enables `x ∈ A` notation on HFSet.

#### 4.8.7 `HFSet.mem_mk`

```lean
theorem mem_mk (x A : CList) :
    (toHFSet x) ∈ (toHFSet A) ↔ CList.mem x A = true
```

- **Math**: [x] ∈ [A] ⟺ mem(x, A) = true
- Reduction lemma connecting quotient membership to CList membership.

---

### 4.9 Operations/Union.lean — `namespace CList`, `namespace HFSet`

#### 4.9.1 `CList.union`

```lean
def union (a b : CList) : CList :=
  match a, b with
  | mk xs, mk ys => mk (xs ++ ys)
```

- **Math**: A ∪ B ≔ {x | x ∈ A ∨ x ∈ B} (via list concatenation)
- Computable. Structural.

#### 4.9.2 `CList.sUnion`

```lean
def sUnion (A : CList) : CList :=
  match A with
  | mk xs => mk (xs.flatMap (fun x => match x with | mk ys => ys))
```

- **Math**: ⋃ A ≔ {x | ∃ B ∈ A, x ∈ B} (generalized union via flatMap)
- Computable. Structural.

#### 4.9.3 `HFSet.union`

```lean
def union (A B : HFSet) : HFSet
```

- **Math**: A ∪ B (lifted to quotient via `union_extEq`)
- Computable.

#### 4.9.4 `HFSet.sUnion`

```lean
def sUnion (A : HFSet) : HFSet
```

- **Math**: ⋃ A (lifted to quotient via `sUnion_extEq`)
- Computable.

---

### 4.10 Operations/Intersection.lean — `namespace HFSet`

#### 4.10.1 `HFSet.interCList`

```lean
def interCList (a b : CList) : CList :=
  match a with
  | CList.mk xs => CList.mk (xs.filter (fun c => CList.mem c b))
```

- **Math**: A ∩ B ≔ {x ∈ A | x ∈ B}
- Computable. Uses `CList.Filter`.

#### 4.10.2 `HFSet.inter`

```lean
def inter (A B : HFSet) : HFSet
```

- **Math**: A ∩ B (lifted via `interCList_extEq_extEq`)
- Computable.

---

### 4.11 Operations/Setminus.lean — `namespace HFSet`

#### 4.11.1 `HFSet.setminusCList`

```lean
def setminusCList (a b : CList) : CList :=
  match a with
  | CList.mk xs => CList.mk (xs.filter (fun c => !(CList.mem c b)))
```

- **Math**: A \ B ≔ {x ∈ A | x ∉ B}
- Computable. Uses `CList.Filter`.

#### 4.11.2 `HFSet.setminus`

```lean
def setminus (A B : HFSet) : HFSet
```

- **Math**: A \ B (lifted via `setminusCList_extEq_extEq`)
- Computable.

---

### 4.12 Operations/Separation.lean — `namespace HFSet`

#### 4.12.1 `HFSet.filterCList`

```lean
def filterCList (P : HFSet → Prop) [DecidablePred P] (A : CList) : CList
```

- **Math**: {x ∈ A | P(x)} at CList level
- Computable (via `decide`).

#### 4.12.2 `HFSet.sep`

```lean
def sep (A : HFSet) (P : HFSet → Prop) [DecidablePred P] : HFSet
```

- **Math**: {x ∈ A | P(x)} (lifted via `filterCList_extEq_extEq`)
- Computable.

---

### 4.13 Operations/Pair.lean — `namespace HFSet`

#### 4.13.1 `HFSet.mkPair`

```lean
def mkPair (a b : CList) : CList := CList.mk [a, b]
```

- **Math**: mkPair(a, b) ≔ {a, b} at CList level.
- Computable.

#### 4.13.2 `HFSet.pair`

```lean
def pair (a b : HFSet) : HFSet
```

- **Math**: {a, b} (lifted via extEq-respecting proof)
- Computable.

---

### 4.14 Operations/Powerset.lean — `namespace CList`, `namespace HFSet`

#### 4.14.1 `CList.sublists`

```lean
def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as => let rest := sublists as; rest ++ rest.map (a :: ·)
```

- **Math**: sublists(l) = all sublists of l (2^|l| elements)
- Computable. Structural recursion.

#### 4.14.2 `HFSet.powersetCList`

```lean
def powersetCList (A : CList) : CList :=
  match A with
  | CList.mk xs => CList.mk (CList.sublists xs |>.map CList.mk)
```

- **Math**: 𝒫(A) ≔ {mk(zs) | zs ∈ sublists(children(A))}
- Computable. Structural.

#### 4.14.3 `HFSet.powerset`

```lean
def powerset (A : HFSet) : HFSet
```

- **Math**: 𝒫(A) (lifted via `powersetCList_extEq`)
- Computable.

---

### 4.15 Notation.lean — `namespace HFSet`

#### 4.15.1 `HFSet.singleton`

```lean
def singleton (a : HFSet) : HFSet := pair a a
```

- **Math**: {a} ≔ {a, a}
- Computable.

#### 4.15.2 `HFSet.insertCList`

```lean
def insertCList (x A : CList) : CList :=
  match A with | CList.mk ys => CList.mk (x :: ys)
```

- **Math**: insert(x, A) ≔ {x} ∪ A at CList level
- Computable.

#### 4.15.3 `HFSet.insert`

```lean
def insert (x A : HFSet) : HFSet
```

- **Math**: {x} ∪ A (lifted via `insertCList_extEq`)
- Computable.

#### 4.15.4 Von Neumann numerals

```lean
def zero : HFSet := ∅
def one   : HFSet := insert zero zero
def two   : HFSet := insert one one
-- ... through nine
```

- **Math**: 0 ≔ ∅, n+1 ≔ {n} ∪ n (von Neumann encoding)
- Computable. With `OfNat` instances for `0` through `9`.

#### 4.15.5 `filterCList` and `sep` (duplicated from Operations/Separation)

Duplicate definitions in Notation.lean for the comprehension syntax macro. Same signatures as §4.12.

---

### 4.16 Axioms/Fintype.lean — top-level + `namespace HFSet`

#### 4.16.1 `Finset`

```lean
structure Finset (α : Type) where
  val   : List α
  nodup : val.Nodup
```

- **Math**: Finₛ(α) ≔ { (l, h) | l : List α, Nodup(l) }. Subconjunto finito de α representado como lista sin duplicados.
- Computable.

#### 4.16.2 `Membership α (Finset α)` instance

```lean
instance {α} : Membership α (Finset α) where
  mem s x := x ∈ s.val
```

- Habilita notación `x ∈ s` para `Finset`. Contenedor primero (s), elemento segundo (x).

#### 4.16.3 `Fintype`

```lean
class Fintype (α : Type) where
  elems    : List α
  complete : ∀ x : α, x ∈ elems
```

- **Math**: α es finito si ∃ l : List α, ∀ x : α, x ∈ l.
- Clase computable de tipos finitos (análogo local sin Mathlib).

#### 4.16.4 `HFSet.toList`

```lean
def toList (A : HFSet) : List HFSet :=
  reprToList A.repr
```

- **Math**: toList(A) ≔ lista de los elementos de A como HFSets (vía representante normalizado).
- Computable. Depende del auxiliar privado `reprToList` y de `HFSet.repr`.

#### 4.16.5 `HFSet.toFinset`

```lean
def toFinset (A : HFSet) : Finset HFSet :=
  ⟨A.toList, A.nodup_toList⟩
```

- **Math**: Finₛ(A) ≔ (toList(A), nodup_toList(A)).
- Computable.

#### 4.16.6 `HFSet.membership_fintype` instance

```lean
instance membership_fintype (A : HFSet) : Fintype {x // x ∈ A} where
  elems    := A.toList.filterMap (fun y => if hy : y ∈ A then some ⟨y, hy⟩ else none)
  complete := fun ⟨x, hx⟩ => by rw [List.mem_filterMap]; exact ⟨x, (mem_toList x A).mpr hx, by rw [dif_pos hx]⟩
```

- **Math**: El subtipo {x : HFSet | x ∈ A} es finito para todo A.
- Computable vía `List.filterMap`.

---

## 6. Theorems

### 6.8 HFSets.lean — `namespace HFSet`

| # | Theorem | Lean signature | Terminated by |
|---|---------|---------------|---------------|
| 1 | `canonicalEq_iff_eq` | `(A B : HFSet) : canonicalEq A B ↔ A = B` | — |
| 2 | `mem_resp_right` | `(x A B : CList) (h : extEq A B = true) : mem x A = true → mem x B = true` | — |
| 3 | `mem_resp_left` | `(x y A : CList) (h : extEq x y = true) : mem x A = true → mem y A = true` | — |
| 4 | `mem_mk` | `(x A : CList) : (Quotient.mk CList.Setoid x) ∈ (Quotient.mk CList.Setoid A) ↔ CList.mem x A = true` | — |
| 5 | `subset_iff_forall_mem_clist` | `(A B : CList) : CList.subset A B = true ↔ ∀ x : CList, CList.mem x A = true → CList.mem x B = true` | — |
| 6 | `extensionality` | `(A B : HFSet) (h : ∀ x : HFSet, x ∈ A ↔ x ∈ B) : A = B` | — |
| 7 | `not_mem_empty` | `(x : HFSet) : ¬ (x ∈ empty)` | — |

### 6.9 Operations/Union.lean — `namespace CList` + `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `CList.mem_union` | `(z a b : CList) : mem z (union a b) = true ↔ mem z a = true ∨ mem z b = true` |
| 2 | `CList.mem_sUnion` | `(z A : CList) : mem z (sUnion A) = true ↔ ∃ Y, mem Y A = true ∧ mem z Y = true` |
| 3 | `CList.union_extEq` | `(a₁ a₂ b₁ b₂ : CList) (ha : extEq a₁ a₂ = true) (hb : extEq b₁ b₂ = true) : extEq (union a₁ b₁) (union a₂ b₂) = true` |
| 4 | `CList.sUnion_extEq` | `(A₁ A₂ : CList) (hA : extEq A₁ A₂ = true) : extEq (sUnion A₁) (sUnion A₂) = true` |

### 6.10 Operations/Intersection.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `interCList_extEq_left` | `(a₁ a₂ b : CList) (ha : CList.extEq a₁ a₂ = true) : CList.extEq (interCList a₁ b) (interCList a₂ b) = true` |
| 2 | `interCList_extEq_right` | `(a b₁ b₂ : CList) (hb : CList.extEq b₁ b₂ = true) : CList.extEq (interCList a b₁) (interCList a b₂) = true` |
| 3 | `interCList_extEq_extEq` | `(a₁ a₂ b₁ b₂ : CList) (ha : CList.extEq a₁ a₂ = true) (hb : CList.extEq b₁ b₂ = true) : CList.extEq (interCList a₁ b₁) (interCList a₂ b₂) = true` |

### 6.11 Operations/Setminus.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `setminusCList_extEq_left` | `(a₁ a₂ b : CList) (ha : CList.extEq a₁ a₂ = true) : CList.extEq (setminusCList a₁ b) (setminusCList a₂ b) = true` |
| 2 | `setminusCList_extEq_right` | `(a b₁ b₂ : CList) (hb : CList.extEq b₁ b₂ = true) : CList.extEq (setminusCList a b₁) (setminusCList a b₂) = true` |
| 3 | `setminusCList_extEq_extEq` | `(a₁ a₂ b₁ b₂ : CList) (ha : CList.extEq a₁ a₂ = true) (hb : CList.extEq b₁ b₂ = true) : CList.extEq (setminusCList a₁ b₁) (setminusCList a₂ b₂) = true` |

### 6.12 Operations/Separation.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `filterCList_extEq_extEq` | `(P : HFSet → Prop) [DecidablePred P] (A₁ A₂ : CList) (hA : CList.extEq A₁ A₂ = true) : CList.extEq (filterCList P A₁) (filterCList P A₂) = true` |

### 6.13 Operations/Powerset.lean — `namespace CList` + `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `CList.sublists_subset` | `(xs zs : List CList) (h : zs ∈ sublists xs) : subset (mk zs) (mk xs) = true` |
| 2 | `CList.filter_in_sublists` | `{α : Type} (P : α → Bool) (xs : List α) : xs.filter P ∈ sublists xs` |
| 3 | `CList.mem_right_respects_extEq` | `(y : CList) : P_respects (fun z => mem z y)` |
| 4 | `HFSet.mem_powersetCList` | `(y A : CList) : CList.mem y (powersetCList A) = true ↔ CList.subset y A = true` |
| 5 | `HFSet.powersetCList_extEq` | `(A₁ A₂ : CList) (h : CList.extEq A₁ A₂ = true) : CList.extEq (powersetCList A₁) (powersetCList A₂) = true` |

### 6.14 Axioms/*.lean — `namespace HFSet` (Zermelo axioms)

All **Zermelo axioms** are proven as theorems (not postulated):

| # | Theorem | File | Lean signature |
|---|---------|------|---------------|
| 1 | `mem_union` | Axioms/Union | `(z A B : HFSet) : z ∈ union A B ↔ z ∈ A ∨ z ∈ B` |
| 2 | `mem_sUnion` | Axioms/Union | `(z A : HFSet) : z ∈ sUnion A ↔ ∃ Y : HFSet, Y ∈ A ∧ z ∈ Y` |
| 3 | `mem_interCList_iff` | Axioms/Intersection | `(a b xc : CList) : CList.mem xc (interCList a b) = true ↔ CList.mem xc a = true ∧ CList.mem xc b = true` |
| 4 | `mem_inter` | Axioms/Intersection | `(A B : HFSet) (x : HFSet) : x ∈ inter A B ↔ x ∈ A ∧ x ∈ B` |
| 5 | `mem_setminusCList_iff` | Axioms/Setminus | `(a b xc : CList) : CList.mem xc (setminusCList a b) = true ↔ CList.mem xc a = true ∧ CList.mem xc b = false` |
| 6 | `mem_setminus` | Axioms/Setminus | `(A B : HFSet) (x : HFSet) : x ∈ setminus A B ↔ x ∈ A ∧ ¬ (x ∈ B)` |
| 6b | `setminus_subset` | Axioms/Setminus | `(A B : HFSet) : setminus A B ⊆ A` |
| 6c | `setminus_setminus_of_subset` | Axioms/Setminus | `{A X : HFSet} (h : A ⊆ X) : setminus X (setminus X A) = A` |
| 7 | `mem_filterCList_iff` | Axioms/Separation | `(a xc : CList) (P : HFSet → Prop) [DecidablePred P] : CList.mem xc (filterCList P a) = true ↔ CList.mem xc a = true ∧ P (Quotient.mk CList.Setoid xc)` |
| 8 | `mem_sep` | Axioms/Separation | `(A : HFSet) (P : HFSet → Prop) [DecidablePred P] (x : HFSet) : x ∈ sep A P ↔ x ∈ A ∧ P x` |
| 9 | `mem_pair` | Axioms/Pair | `(x a b : HFSet) : x ∈ pair a b ↔ x = a ∨ x = b` |
| 10 | `mem_powerset` | Axioms/Powerset | `(A B : HFSet) : B ∈ powerset A ↔ (∀ x, x ∈ B → x ∈ A)` |

**Derived Zermelo axiom summary** (all proven, none postulated):

| Axiom | Theorem | Statement |
|-------|---------|-----------|
| Extensionality | `extensionality` | ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B |
| Empty Set | `not_mem_empty` | ∀ x, x ∉ ∅ |
| Pairs | `mem_pair` | x ∈ {a, b} ↔ x = a ∨ x = b |
| Union | `mem_union` / `mem_sUnion` | z ∈ A ∪ B ↔ z ∈ A ∨ z ∈ B |
| Separation | `mem_sep` | x ∈ {x ∈ A \| P x} ↔ x ∈ A ∧ P x |
| Intersection | `mem_inter` | x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B |
| Set Difference | `mem_setminus` | x ∈ A \ B ↔ x ∈ A ∧ x ∉ B |
| Powerset | `mem_powerset` | B ∈ 𝒫(A) ↔ ∀ x, x ∈ B → x ∈ A |

### 6.15 Notation.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_insertCList_right` | `(x₁ x₂ A₂ : CList) (hx : CList.extEq x₁ x₂ = true) : CList.mem x₁ (insertCList x₂ A₂) = true` |
| 2 | `subset_insertCList_right` | `(A₁ x₂ A₂ : CList) (hA : CList.subset A₁ A₂ = true) : CList.subset A₁ (insertCList x₂ A₂) = true` |
| 3 | `insertCList_subset` | `(x₁ A₁ x₂ A₂ : CList) (hx : CList.extEq x₁ x₂ = true) (hA : CList.subset A₁ A₂ = true) : CList.subset (insertCList x₁ A₁) (insertCList x₂ A₂) = true` |
| 4 | `insertCList_extEq` | `(x₁ A₁ x₂ A₂ : CList) (hx : CList.extEq x₁ x₂ = true) (hA : CList.extEq A₁ A₂ = true) : CList.extEq (insertCList x₁ A₁) (insertCList x₂ A₂) = true` |
| 5 | `filterCList_extEq_extEq` | `(P : HFSet → Prop) [DecidablePred P] (A₁ A₂ : CList) (hA : CList.extEq A₁ A₂ = true) : CList.extEq (filterCList P A₁) (filterCList P A₂) = true` |

### 6.16 Axioms/Fintype.lean — top-level + `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_toList` | `(x A : HFSet) : x ∈ A.toList ↔ x ∈ A` |
| 2 | `nodup_toList` | `(A : HFSet) : A.toList.Nodup` |
| 3 | `mem_toFinset` | `(x A : HFSet) : x ∈ A.toFinset ↔ x ∈ A` |

---

## 7. Exports per Module

### HFSets.lean

`CList.Setoid`, `HFSet`, `HFSet.repr`, `HFSet.canonicalEq`, `HFSet.canonicalEq_iff_eq`, `HFSet.empty`, `HFSet.mem_resp_right`, `HFSet.mem_resp_left`, `HFSet.Mem`, `Membership HFSet HFSet`, `HFSet.mem_mk`, `HFSet.subset_iff_forall_mem_clist`, `HFSet.extensionality`, `HFSet.not_mem_empty`

### Operations/Union.lean

`CList.union`, `CList.mem_union`, `CList.sUnion`, `CList.mem_sUnion`, `CList.union_extEq`, `CList.sUnion_extEq`, `HFSet.union`, `HFSet.sUnion`

### Operations/Intersection.lean

`HFSet.interCList`, `HFSet.interCList_extEq_left`, `HFSet.interCList_extEq_right`, `HFSet.interCList_extEq_extEq`, `HFSet.inter`

### Operations/Setminus.lean

`HFSet.setminusCList`, `HFSet.setminusCList_extEq_left`, `HFSet.setminusCList_extEq_right`, `HFSet.setminusCList_extEq_extEq`, `HFSet.setminus`

### Operations/Separation.lean

`HFSet.filterCList`, `HFSet.filterCList_extEq_extEq`, `HFSet.sep`

### Operations/Pair.lean

`HFSet.mkPair`, `HFSet.pair`

### Operations/Powerset.lean

`CList.sublists`, `CList.sublists_subset`, `CList.filter_in_sublists`, `CList.mem_right_respects_extEq`, `HFSet.powersetCList`, `HFSet.mem_powersetCList`, `HFSet.powersetCList_extEq`, `HFSet.powerset`

### Axioms/Union.lean

`HFSet.mem_union`, `HFSet.mem_sUnion`

### Axioms/Intersection.lean

`HFSet.mem_interCList_iff`, `HFSet.mem_inter`

### Axioms/Setminus.lean

`HFSet.mem_setminusCList_iff`, `HFSet.mem_setminus`, `HFSet.setminus_subset`,
`HFSet.setminus_setminus_of_subset`

### Axioms/Separation.lean

`HFSet.mem_filterCList_iff`, `HFSet.mem_sep`

### Axioms/Pair.lean

`HFSet.mem_pair`

### Axioms/Powerset.lean

`HFSet.mem_powerset`

### Notation.lean

`HFSet.singleton`, `HFSet.insertCList`, `HFSet.insert`, `HFSet.mem_insertCList_right`, `HFSet.subset_insertCList_right`, `HFSet.insertCList_subset`, `HFSet.insertCList_extEq`, `HFSet.filterCList` (redefined), `HFSet.filterCList_extEq_extEq` (redefined), `HFSet.sep` (redefined), `HFSet.zero` … `HFSet.nine`, `OfNat HFSet 0` … `OfNat HFSet 9`

### Axioms/Fintype.lean

`Finset`, `Membership α (Finset α)` (instance), `Fintype`, `HFSet.toList`, `HFSet.mem_toList`, `HFSet.nodup_toList`, `HFSet.toFinset`, `HFSet.mem_toFinset`, `HFSet.membership_fintype` (instance)
