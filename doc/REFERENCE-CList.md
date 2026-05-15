# Technical Reference — CList (Concrete Hereditarily Finite Lists)

**Last updated:** 2026-05-14
**Parent:** [../REFERENCE.md](../REFERENCE.md)
**Related:** [REFERENCE-HFSets.md](REFERENCE-HFSets.md)

@axiom_system: AczelSetTheory
@importance: high

---

## Overview

The `CList` layer is the **concrete implementation** substrate for hereditarily finite sets.
It provides Boolean decision procedures (membership, subset, extensional equality) and a
normalization algorithm (dedup + insertion sort) that feeds into the `HFSet` quotient type.

**Entry file:** [`AczelSetTheory/CList.lean`](../AczelSetTheory/CList.lean) (barrel)
**Namespace:** `CList`
**Used by:** `HFSets.lean` → all of `Operations/*` and `Axioms/*`

| # | File | Status |
|---|------|--------|
| 1 | `AczelSetTheory/CList/Basic.lean` | ✅ Complete |
| 2 | `AczelSetTheory/CList/ExtEq.lean` | ✅ Complete |
| 3 | `AczelSetTheory/CList/Filter.lean` | ✅ Complete |
| 4 | `AczelSetTheory/CList/SetEquiv.lean` | ✅ Complete |
| 5 | `AczelSetTheory/CList/Order.lean` | ✅ Complete |
| 6 | `AczelSetTheory/CList/Sort.lean` | ✅ Complete |
| 7 | `AczelSetTheory/CList/Normalize.lean` | ✅ Complete |
| 8 | `AczelSetTheory/CList.lean` (barrel) | ✅ Complete |

---

## 4. Definitions

### 4.1 CList/Basic.lean — `namespace CList`

#### 4.1.1 Core Type

```lean
inductive CList : Type where
  | mk : List CList → CList
  deriving Repr, Inhabited
```

- **Math**: A ≔ {a₁, a₂, …, aₙ} where each aᵢ is itself a CList
- Computable. No termination proof needed (structural).

#### 4.1.2 Size Functions (mutual)

```lean
mutual
  def cSize : CList → Nat
    | mk xs => 1 + cSizeList xs
  def cSizeList : List CList → Nat
    | [] => 0
    | x :: xs => 1 + cSize x + cSizeList xs
end
```

- **Math**: |A| ≔ 1 + Σᵢ (1 + |aᵢ|)
- Computable. Structural recursion.

#### 4.1.3 `empty`

```lean
def empty : CList := mk []
```

- **Math**: ∅ ≔ {}
- Computable.

#### 4.1.4 Comparison Engine

```lean
inductive CListOp | mem | subset | eq

def evalOp (op : CListOp) (A B : CList) : Bool
```

- **Math**: Dispatches membership (∈), subset (⊆), extensional equality (=ₑ)
- Computable. *Terminated by* `(sizeOf A + sizeOf B) * 3 + opWeight op`.

```lean
def mem (x A : CList) : Bool := evalOp .mem x A
def subset (A B : CList) : Bool := evalOp .subset A B
def extEq (A B : CList) : Bool := evalOp .eq A B
```

- `mem x (mk ys)` = `∃ y ∈ ys, extEq x y`
- `subset (mk xs) B` = `∀ x ∈ xs, mem x B`
- `extEq A B` = `subset A B ∧ subset B A`

#### 4.1.5 BEq Instance

```lean
instance : BEq CList where beq := extEq
```

#### 4.1.6 Total Order

```lean
def lt (A B : CList) : Bool
```

- **Math**: Lexicographic order on the tree structure.
- Computable. *Terminated by* `cSize A + cSize B`.

#### 4.1.7 Deduplication

```lean
def dedupAux (l : List CList) (vistos : List CList) : List CList
def dedup (l : List CList) : List CList := dedupAux l []
```

- **Math**: Remove extensional duplicates, keeping first occurrence.
- Computable. Structural recursion on `l`.

#### 4.1.8 Insertion Sort

```lean
def orderedInsert (x : CList) : List CList → List CList
def insertionSort : List CList → List CList
```

- **Math**: Insertion sort using `lt` with extensional duplicate removal.
- Computable. Structural recursion.

#### 4.1.9 Normalization

```lean
def normalize : CList → CList
  | mk xs => mk (insertionSort (dedup (xs.map normalize)))
```

- **Math**: norm(A) ≔ sort(dedup(map(norm, children(A))))
- Computable. Termination by well-founded recursion on the tree structure.

#### 4.1.10 Test Definitions

```lean
def zero  := empty                                    -- ∅
def one   := mk [zero]                                -- {∅}
def two   := mk [zero, one]                           -- {∅, {∅}}
def three := mk [zero, one, two]                      -- {∅, {∅}, {∅, {∅}}}
def dirty := mk [one, two, zero, three, one, zero, zero, two, three, two]
```

---

### 4.2 CList/ExtEq.lean — `namespace CList`

No new definitions. Only theorems (see §6.2).

---

### 4.3 CList/Filter.lean — `namespace CList`

#### 4.3.1 `P_respects`

```lean
def P_respects (P : CList → Bool) : Prop :=
  ∀ (x y : CList), extEq x y = true → P x = P y
```

- **Math**: P respects extensional equality: A =ₑ B → P(A) = P(B).
- Noncomputable (Prop with universal quantifier).

---

### 4.4 CList/SetEquiv.lean — `namespace CList`

#### 4.4.1 `Nodup`

```lean
def Nodup (l : List CList) : Prop :=
  l.Pairwise (fun a b => extEq a b = false)
```

- **Math**: No two distinct positions i < j satisfy aᵢ =ₑ aⱼ.
- Noncomputable (Prop). Decidable via `extEq`.

#### 4.4.2 `SetEquiv`

```lean
def SetEquiv (l₁ l₂ : List CList) : Prop :=
  ∀ x, (l₁.any (extEq x) = true) ↔ (l₂.any (extEq x) = true)
```

- **Math**: l₁ ≡ l₂ ⟺ ∀ x, (∃ a ∈ l₁, a =ₑ x) ↔ (∃ b ∈ l₂, b =ₑ x)
- Noncomputable (Prop with universal quantifier over CList).

---

### 4.5 CList/Order.lean — `namespace CList`

No new definitions. Only theorems (see §6.5).

---

### 4.6 CList/Sort.lean — `namespace CList`

#### 4.6.1 `Sorted`

```lean
def Sorted : List CList → Prop
  | []               => True
  | [_]              => True
  | a :: b :: rest   => lt a b = true ∧ Sorted (b :: rest)
```

- **Math**: Strictly sorted by `lt`.
- Noncomputable (Prop).

---

### 4.7 CList/Normalize.lean — `namespace CList`

No new definitions. Only theorems (see §6.7).

---

## 6. Theorems

> Only fully proven theorems. No `sorry` remains.

### 6.1 CList/Basic.lean

| # | Theorem | Lean signature | Math | Terminated by |
|---|---------|---------------|------|---------------|
| 1 | `cSize_lt_of_mem` | `{x : CList} {xs : List CList} (h : x ∈ xs) : cSize x < cSize (mk xs)` | x ∈ xs → \|x\| < \|{xs}\| | structural |

---

### 6.2 CList/ExtEq.lean

| # | Theorem | Lean signature | Terminated by |
|---|---------|---------------|---------------|
| 1 | `subset_mono` | `(xs : List CList) (y : CList) (ys : List CList) (h : evalOp .subset (mk xs) (mk ys) = true) : evalOp .subset (mk xs) (mk (y :: ys)) = true` | — |
| 2 | `subset_refl` | `(A : CList) : subset A A = true` | `cSize A` |
| 3 | `extEq_refl` | `(A : CList) : extEq A A = true` | — (uses `subset_refl`) |
| 4 | `extEq_def` | `(A B : CList) : extEq A B = (subset A B && subset B A)` | — |
| 5 | `subset_nil` | `(B : CList) : subset (mk []) B = true` | — |
| 6 | `subset_cons` | `(x : CList) (xs : List CList) (B : CList) : subset (mk (x :: xs)) B = (mem x B && subset (mk xs) B)` | — |
| 7 | `mem_nil` | `(x : CList) : mem x (mk []) = false` | — |
| 8 | `mem_cons` | `(x y : CList) (ys : List CList) : mem x (mk (y :: ys)) = (extEq x y \|\| mem x (mk ys))` | — |

**Mutual block** (*terminated by* weighted sum of `cSize` arguments):

| # | Theorem | Lean signature |
|---|---------|---------------|
| 9 | `extEq_trans` | `(A B C : CList) (h1 : extEq A B = true) (h2 : extEq B C = true) : extEq A C = true` |
| 10 | `subset_trans` | `(A B C : CList) (h1 : subset A B = true) (h2 : subset B C = true) : subset A C = true` |
| 11 | `mem_subset` | `(x B C : CList) (h1 : mem x B = true) (h2 : subset B C = true) : mem x C = true` |
| 12 | `mem_of_extEq` | `(x y C : CList) (h1 : extEq x y = true) (h2 : mem y C = true) : mem x C = true` |

| # | Theorem | Lean signature |
|---|---------|---------------|
| 13 | `extEq_comm` | `(A B : CList) : extEq A B = extEq B A` |

---

### 6.3 CList/Filter.lean

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `subset_filter` | `(P : CList → Bool) (xs : List CList) : subset (mk (xs.filter P)) (mk xs) = true` |
| 2 | `mem_filter_of_mem` | `(P : CList → Bool) (hP_resp : P_respects P) (x : CList) (xs : List CList) (hx : mem x (mk xs) = true) (hPx : P x = true) : mem x (mk (xs.filter P)) = true` |
| 3 | `filter_subset_filter` | `(P : CList → Bool) (hP_resp : P_respects P) (xs ys : List CList) (hsub : subset (mk xs) (mk ys) = true) : subset (mk (xs.filter P)) (mk (ys.filter P)) = true` |
| 4 | `extEq_filter` | `(P : CList → Bool) (hP_resp : P_respects P) (xs ys : List CList) (heq : extEq (mk xs) (mk ys) = true) : extEq (mk (xs.filter P)) (mk (ys.filter P)) = true` |
| 5 | `P_of_mem_filter` | `(P : CList → Bool) (hP_resp : P_respects P) (x : CList) (xs : List CList) (hx : mem x (mk (xs.filter P)) = true) : P x = true` |

---

### 6.4 CList/SetEquiv.lean

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `dedup_nodup` | `(l : List CList) : Nodup (dedup l)` |
| 2 | `SetEquiv.refl` | `(l : List CList) : SetEquiv l l` |
| 3 | `SetEquiv.symm` | `{l₁ l₂ : List CList} (h : SetEquiv l₁ l₂) : SetEquiv l₂ l₁` |
| 4 | `SetEquiv.trans` | `{l₁ l₂ l₃ : List CList} (h₁ : SetEquiv l₁ l₂) (h₂ : SetEquiv l₂ l₃) : SetEquiv l₁ l₃` |
| 5 | `mem_eq_any` | `(x : CList) (l : List CList) : mem x (mk l) = l.any (extEq x)` |
| 6 | `extEq_mk_iff_setEquiv` | `(xs ys : List CList) : extEq (mk xs) (mk ys) = true ↔ SetEquiv xs ys` |
| 7 | `dedup_setEquiv_self` | `(l : List CList) : SetEquiv (dedup l) l` |

---

### 6.5 CList/Order.lean

| # | Theorem | Lean signature | Terminated by |
|---|---------|---------------|---------------|
| 1 | `lt_irrefl` | `(A : CList) : lt A A = false` | `cSize A` |
| 2 | `lt_antisymm` | `(A B : CList) (h1 : lt A B = false) (h2 : lt B A = false) : A = B` | `cSize A + cSize B` |
| 3 | `lt_asymm` | `(A B : CList) (h : lt A B = true) : lt B A = false` | `cSize A + cSize B` |
| 4 | `lt_total` | `(A B : CList) : A ≠ B → lt A B = true ∨ lt B A = true` | `cSize A + cSize B` |
| 5 | `lt_total_extEq` | `(A B : CList) : extEq A B = false → lt A B = true ∨ lt B A = true` | — (uses `lt_total`) |
| 6 | `lt_trans` | `(A B C : CList) (h1 : lt A B = true) (h2 : lt B C = true) : lt A C = true` | `cSize A + cSize B + cSize C` |

---

### 6.6 CList/Sort.lean

| # | Theorem | Lean signature | Dependencies |
|---|---------|---------------|--------------|
| 1 | `insertionSort_sorted` | `(l : List CList) : Sorted (insertionSort l)` | `orderedInsert_sorted` (private) |
| 2 | `insertionSort_mem_subset` | `(z : CList) (l : List CList) : z ∈ insertionSort l → z ∈ l` | `mem_of_mem_orderedInsert` (private) |
| 3 | `insertionSort_nodup` | `(l : List CList) (hl : Nodup l) : Nodup (insertionSort l)` | `orderedInsert_nodup` (private) |
| 4 | `insertionSort_setEquiv` | `(l : List CList) : SetEquiv (insertionSort l) l` | `orderedInsert_setEquiv` (private) |

---

### 6.7 CList/Normalize.lean

| # | Theorem | Lean signature | Terminated by |
|---|---------|---------------|---------------|
| 1 | `cSizeList_dedup_le` | `(l : List CList) : cSizeList (dedup l) ≤ cSizeList l` | — |
| 2 | `cSizeList_insertionSort_le` | `(l : List CList) : cSizeList (insertionSort l) ≤ cSizeList l` | — |
| 3 | `normalize_cSize_le` | `(A : CList) : cSize (normalize A) ≤ cSize A` | `cSize A * 2` (mutual with `normalize_cSizeList_le`) |
| 4 | `dedup_id_of_nodup` | `(l : List CList) (h : Nodup l) : dedup l = l` | — |
| 5 | `insertionSort_id_of_sorted_nodup` | `(l : List CList) (hs : Sorted l) (hn : Nodup l) : insertionSort l = l` | — |
| 6 | `normalize_idem` | `(A : CList) : normalize (normalize A) = normalize A` | `cSize A * 2` (mutual with `normalize_idem_list`) |
| 7 | `mem_of_mem_dedup` | `(l : List CList) (y : CList) (h : y ∈ dedup l) : y ∈ l` | — |
| 8 | `sorted_nodup_setEquiv_eq` | `(l₁ l₂ : List CList) : Sorted l₁ → Sorted l₂ → Nodup l₁ → Nodup l₂ → SetEquiv l₁ l₂ → (∀ a ∈ l₁, ∀ b ∈ l₂, extEq a b = true → a = b) → l₁ = l₂` | structural on `l₁`, `l₂` |
| 9 | `normalize_eq_of_extEq` | `{A B : CList} (h : CList.extEq A B = true) : CList.normalize A = CList.normalize B` | `CList.cSize A + CList.cSize B` |

---

## 7. Exports per Module

### CList/Basic.lean

`CList`, `CList.mk`, `CList.cSize`, `CList.cSizeList`, `CList.cSize_lt_of_mem`, `CList.empty`, `CListOp`, `CList.evalOp`, `CList.mem`, `CList.subset`, `CList.extEq`, `BEq CList`, `CList.lt`, `CList.dedupAux`, `CList.dedup`, `CList.orderedInsert`, `CList.insertionSort`, `CList.normalize`, `CList.zero`, `CList.one`, `CList.two`, `CList.three`, `CList.dirty`

### CList/ExtEq.lean

`CList.subset_mono`, `CList.subset_refl`, `CList.extEq_refl`, `CList.extEq_def`, `CList.subset_nil`, `CList.subset_cons`, `CList.mem_nil`, `CList.mem_cons`, `CList.extEq_trans`, `CList.subset_trans`, `CList.mem_subset`, `CList.mem_of_extEq`, `CList.extEq_comm`

### CList/Filter.lean

`CList.P_respects`, `CList.subset_filter`, `CList.mem_filter_of_mem`, `CList.filter_subset_filter`, `CList.extEq_filter`, `CList.P_of_mem_filter`

### CList/SetEquiv.lean

`CList.Nodup`, `CList.dedup_nodup`, `CList.SetEquiv`, `CList.SetEquiv.refl`, `CList.SetEquiv.symm`, `CList.SetEquiv.trans`, `CList.mem_eq_any`, `CList.extEq_mk_iff_setEquiv`, `CList.dedup_setEquiv_self`

### CList/Order.lean

`CList.lt_irrefl`, `CList.lt_antisymm`, `CList.lt_asymm`, `CList.lt_total`, `CList.lt_total_extEq`, `CList.lt_trans`

### CList/Sort.lean

`CList.Sorted`, `CList.insertionSort_sorted`, `CList.insertionSort_mem_subset`, `CList.insertionSort_nodup`, `CList.insertionSort_setEquiv`

### CList/Normalize.lean

`CList.cSizeList_dedup_le`, `CList.cSizeList_insertionSort_le`, `CList.normalize_cSize_le`, `CList.dedup_id_of_nodup`, `CList.insertionSort_id_of_sorted_nodup`, `CList.normalize_idem`, `CList.mem_of_mem_dedup`, `CList.sorted_nodup_setEquiv_eq`, `CList.normalize_eq_of_extEq`

### CList.lean (barrel)

Imports only: `CList/Basic`, `CList/ExtEq`, `CList/Filter`, `CList/SetEquiv`, `CList/Order`, `CList/Sort`, `CList/Normalize`. No new exports.
