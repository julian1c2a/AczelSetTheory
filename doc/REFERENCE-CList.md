# Technical Reference — CList (Concrete Hereditarily Finite Lists)

**Last updated:** 2026-05-18
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
  | mk : PList CList → CList
  deriving Repr, Inhabited
```

- **Math**: A ≔ {a₁, a₂, …, aₙ} where each aᵢ is itself a CList
- Children stored as a `PList CList` (Peano-indexed list).
- Computable. No termination proof needed (structural).

#### 4.1.2 Size Functions (mutual)

```lean
mutual
  def cSize : CList → ℕ₀
    | mk xs => σ (cSizePList xs)
  def cSizePList : PList CList → ℕ₀
    | .nil      => 𝟘
    | .cons x xs => σ (add (cSize x) (cSizePList xs))
end

@[simp] theorem cSize_mk (xs : PList CList) : cSize (mk xs) = σ (cSizePList xs)
@[simp] theorem cSizePList_nil : cSizePList .nil = 𝟘
@[simp] theorem cSizePList_cons (x : CList) (xs : PList CList) :
    cSizePList (.cons x xs) = σ (add (cSize x) (cSizePList xs))
```

- **Math**: |A| ≔ σ (Σᵢ σ(1 + |aᵢ|))  — size in ℕ₀.
- Computable. Structural recursion.

#### 4.1.3 `empty`

```lean
def empty : CList := mk .nil
```

- **Math**: ∅ ≔ {}

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
def dedupAux (l vistos : PList CList) : PList CList
def dedup (l : PList CList) : PList CList := dedupAux l .nil
```

- **Math**: Remove extensional duplicates, keeping first occurrence.
- Computable. Structural recursion on `l`.

#### 4.1.8 Insertion Sort

```lean
def orderedInsert (x : CList) : PList CList → PList CList
def insertionSort : PList CList → PList CList
```

- **Math**: Insertion sort using `lt` with extensional duplicate removal.
- Computable. Structural recursion.

#### 4.1.9 Normalization

```lean
mutual
  def normalize : CList → CList
    | mk xs => mk (normalizePList xs)
  def normalizePList : PList CList → PList CList
    | .nil      => .nil
    | .cons x xs => insertionSort (dedup (normalizePList xs |>.cons (normalize x)))
end
```

- **Math**: norm(A) ≔ sort(dedup(map(norm, children(A))))
- Computable. Termination by well-founded recursion on `sizeOf`.

#### 4.1.10 Key Lemma

```lean
theorem cSize_lt_of_mem {x : CList} {xs : PList CList} (h : x ∈ xs) :
    cSize x < cSize (mk xs)
```

#### 4.1.11 Test Definitions

```lean
def zero  := empty                                    -- ∅
def one   := mk (.cons zero .nil)                     -- {∅}
def two   := mk (.cons zero (.cons one .nil))          -- {∅, {∅}}
def three := mk (.cons zero (.cons one (.cons two .nil))) -- {∅, {∅}, {∅, {∅}}}
def dirty := mk (...)  -- a list with duplicates and disorder
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
def Nodup : PList CList → Prop
  | .nil      => True
  | .cons x xs => (∀ y ∈ xs, extEq x y = false) ∧ Nodup xs
```

- **Math**: No element in the list is extensionally equal to a later element.
- Noncomputable (Prop). Inductive definition over `PList CList`.

#### 4.4.2 `SetEquiv`

```lean
def SetEquiv (l₁ l₂ : PList CList) : Prop :=
  ∀ x, (PList.any (fun y => extEq x y) l₁ = true) ↔
       (PList.any (fun y => extEq x y) l₂ = true)
```

- **Math**: l₁ ≡ l₂ ⟺ ∀ x, (∃ a ∈ l₁, a =ₑ x) ↔ (∃ b ∈ l₂, b =ₑ x)
- Noncomputable (Prop with universal quantifier over CList).

#### 4.4.3 `mem_eq_any`

```lean
theorem mem_eq_any (x : CList) (l : PList CList) :
    mem x (mk l) = PList.any (fun y => extEq x y) l
```

Bridges Boolean `mem` and `PList.any` for reasoning about SetEquiv.

---

### 4.5 CList/Order.lean — `namespace CList`

No new definitions. Only theorems (see §6.5).

---

### 4.6 CList/Sort.lean — `namespace CList`

#### 4.6.1 `Sorted`

```lean
def Sorted : PList CList → Prop
  | .nil               => True
  | .cons _ .nil       => True
  | .cons a (.cons b rest) => lt a b = true ∧ Sorted (.cons b rest)
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

| # | Theorem | Lean signature | Math |
|---|---------|---------------|------|
| 1 | `cSize_mk` | `@[simp] (xs : PList CList) : cSize (mk xs) = σ (cSizePList xs)` | size of node |
| 2 | `cSizePList_nil` | `@[simp] : cSizePList .nil = 𝟘` | size of empty list |
| 3 | `cSizePList_cons` | `@[simp] (x : CList) (xs : PList CList) : cSizePList (.cons x xs) = σ (add (cSize x) (cSizePList xs))` | size of cons |
| 4 | `cSize_lt_of_mem` | `{x : CList} {xs : PList CList} (h : x ∈ xs) : cSize x < cSize (mk xs)` | x ∈ xs → \|x\| < \|{xs}\| |

---

### 6.2 CList/ExtEq.lean

| # | Theorem | Lean signature | Terminated by |
|---|---------|---------------|---------------|
| 1 | `subset_mono` | `(xs : PList CList) (y : CList) (ys : PList CList) (h : evalOp .subset (mk xs) (mk ys) = true) : evalOp .subset (mk xs) (mk (.cons y ys)) = true` | — |
| 2 | `subset_refl` | `(A : CList) : subset A A = true` | `cSize A` |
| 3 | `extEq_refl` | `(A : CList) : extEq A A = true` | — (uses `subset_refl`) |
| 4 | `extEq_def` | `(A B : CList) : extEq A B = (subset A B && subset B A)` | — |
| 5 | `subset_nil` | `(B : CList) : subset (mk .nil) B = true` | — |
| 6 | `subset_cons` | `(x : CList) (xs : PList CList) (B : CList) : subset (mk (.cons x xs)) B = (mem x B && subset (mk xs) B)` | — |
| 7 | `mem_nil` | `(x : CList) : mem x (mk .nil) = false` | — |
| 8 | `mem_cons` | `(x y : CList) (ys : PList CList) : mem x (mk (.cons y ys)) = (extEq x y \|\| mem x (mk ys))` | — |

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
| 1 | `subset_filter` | `(P : CList → Bool) (xs : PList CList) : subset (mk (PList.filter P xs)) (mk xs) = true` |
| 2 | `mem_filter_of_mem` | `(P : CList → Bool) (hP_resp : P_respects P) (x : CList) (xs : PList CList) (hx : mem x (mk xs) = true) (hPx : P x = true) : mem x (mk (PList.filter P xs)) = true` |
| 3 | `filter_subset_filter` | `(P : CList → Bool) (hP_resp : P_respects P) (xs ys : PList CList) (hsub : subset (mk xs) (mk ys) = true) : subset (mk (PList.filter P xs)) (mk (PList.filter P ys)) = true` |
| 4 | `extEq_filter` | `(P : CList → Bool) (hP_resp : P_respects P) (xs ys : PList CList) (heq : extEq (mk xs) (mk ys) = true) : extEq (mk (PList.filter P xs)) (mk (PList.filter P ys)) = true` |
| 5 | `P_of_mem_filter` | `(P : CList → Bool) (hP_resp : P_respects P) (x : CList) (xs : PList CList) (hx : mem x (mk (PList.filter P xs)) = true) : P x = true` |

---

### 6.4 CList/SetEquiv.lean

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `dedup_nodup` | `(l : PList CList) : Nodup (dedup l)` |
| 2 | `SetEquiv.refl` | `(l : PList CList) : SetEquiv l l` |
| 3 | `SetEquiv.symm` | `{l₁ l₂ : PList CList} (h : SetEquiv l₁ l₂) : SetEquiv l₂ l₁` |
| 4 | `SetEquiv.trans` | `{l₁ l₂ l₃ : PList CList} (h₁ : SetEquiv l₁ l₂) (h₂ : SetEquiv l₂ l₃) : SetEquiv l₁ l₃` |
| 5 | `mem_eq_any` | `(x : CList) (l : PList CList) : mem x (mk l) = PList.any (fun y => extEq x y) l` |
| 6 | `extEq_mk_iff_setEquiv` | `(xs ys : PList CList) : extEq (mk xs) (mk ys) = true ↔ SetEquiv xs ys` |
| 7 | `dedup_setEquiv_self` | `(l : PList CList) : SetEquiv (dedup l) l` |

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
| 1 | `insertionSort_sorted` | `(l : PList CList) : Sorted (insertionSort l)` | `orderedInsert_sorted` (private) |
| 2 | `insertionSort_mem_subset` | `(z : CList) (l : PList CList) : PList.Mem z (insertionSort l) → PList.Mem z l` | `mem_of_mem_orderedInsert` (private) |
| 3 | `insertionSort_nodup` | `(l : PList CList) (hl : Nodup l) : Nodup (insertionSort l)` | `orderedInsert_nodup` (private) |
| 4 | `insertionSort_setEquiv` | `(l : PList CList) : SetEquiv (insertionSort l) l` | `orderedInsert_setEquiv` (private) |
| 5 | `sorted_head_lt_of_mem` | `{a b : CList} {l : PList CList} (hs : Sorted (.cons a l)) (hb : PList.Mem b l) : lt a b = true` | — |
| 6 | `length_orderedInsert_fresh` | `(x : CList) (l : PList CList) (hf : ∀ y ∈ l, extEq x y = false) : PList.length (orderedInsert x l) = σ (PList.length l)` | — |
| 7 | `length_insertionSort_nodup` | `(l : PList CList) (hn : Nodup l) : PList.length (insertionSort l) = PList.length l` | — |

---

### 6.7 CList/Normalize.lean

| # | Theorem | Lean signature | Notes |
|---|---------|---------------|-------|
| 1 | `mem_of_mem_dedup` | `(l : PList CList) (y : CList) (h : PList.Mem y (dedup l)) : PList.Mem y l` | — |
| 2 | `dedup_id_of_nodup` | `(l : PList CList) (h : Nodup l) : dedup l = l` | — |
| 3 | `insertionSort_id_of_sorted_nodup` | `(l : PList CList) (hs : Sorted l) (hn : Nodup l) : insertionSort l = l` | — |
| 4 | `normalize_idem` | `(A : CList) : normalize (normalize A) = normalize A` | mutual with `normalizePList_idem` |
| 5 | `sorted_nodup_setEquiv_eq` | `(l₁ l₂ : PList CList) : Sorted l₁ → Sorted l₂ → Nodup l₁ → Nodup l₂ → SetEquiv l₁ l₂ → (∀ a ∈ l₁, ∀ b ∈ l₂, extEq a b = true → a = b) → l₁ = l₂` | — |
| 6 | `extEq_normalize` | `(A : CList) : extEq A (normalize A) = true` | — |
| 7 | `normalize_eq_of_extEq` | `{A B : CList} (h : CList.extEq A B = true) : CList.normalize A = CList.normalize B` | — |
| 8 | `extEq_iff_normalize_eq` | `{A B : CList} : extEq A B = true ↔ normalize A = normalize B` | — |
| 9 | `dedup_cons_fresh` | `(x : CList) (l : PList CList) (hf : ∀ y ∈ l, extEq x y = false) : dedup (.cons x l) = .cons x (dedup l)` | — |
| 10 | `normalize_cons_fresh` | (related normalization lemma for fresh cons) | — |
| 11 | `normalize_fixed_of_mem_normalize` | (element of normalized list is already normalized) | — |
| 12 | `normalize_mk_of_normalized_sorted_nodup` | `(xs : PList CList) (hn : Nodup xs) (hs : Sorted xs) (hf : ∀ x ∈ xs, normalize x = x) : normalize (mk xs) = mk xs` | — |

---

## 7. Exports per Module

### CList/Basic.lean

`CList`, `CList.mk`, `CList.cSize`, `CList.cSizePList`, `CList.cSize_mk`, `CList.cSizePList_nil`, `CList.cSizePList_cons`, `CList.cSize_lt_of_mem`, `CList.empty`, `CListOp`, `CList.evalOp`, `CList.mem`, `CList.subset`, `CList.extEq`, `BEq CList`, `CList.lt`, `CList.dedupAux`, `CList.dedup`, `CList.orderedInsert`, `CList.insertionSort`, `CList.normalize`, `CList.normalizePList`, `CList.zero`, `CList.one`, `CList.two`, `CList.three`, `CList.dirty`

### CList/ExtEq.lean

`CList.subset_mono`, `CList.subset_refl`, `CList.extEq_refl`, `CList.extEq_def`, `CList.subset_nil`, `CList.subset_cons`, `CList.mem_nil`, `CList.mem_cons`, `CList.extEq_trans`, `CList.subset_trans`, `CList.mem_subset`, `CList.mem_of_extEq`, `CList.extEq_comm`

### CList/Filter.lean

`CList.P_respects`, `CList.subset_filter`, `CList.mem_filter_of_mem`, `CList.filter_subset_filter`, `CList.extEq_filter`, `CList.P_of_mem_filter`

### CList/SetEquiv.lean

`CList.Nodup`, `CList.dedup_nodup`, `CList.SetEquiv`, `CList.SetEquiv.refl`, `CList.SetEquiv.symm`, `CList.SetEquiv.trans`, `CList.mem_eq_any`, `CList.extEq_mk_iff_setEquiv`, `CList.dedup_setEquiv_self`

### CList/Order.lean

`CList.lt_irrefl`, `CList.lt_antisymm`, `CList.lt_asymm`, `CList.lt_total`, `CList.lt_total_extEq`, `CList.lt_trans`

### CList/Sort.lean

`CList.Sorted`, `CList.insertionSort_sorted`, `CList.insertionSort_mem_subset`, `CList.insertionSort_nodup`, `CList.insertionSort_setEquiv`, `CList.sorted_head_lt_of_mem`, `CList.length_orderedInsert_fresh`, `CList.length_insertionSort_nodup`

### CList/Normalize.lean

`CList.mem_of_mem_dedup`, `CList.dedup_id_of_nodup`, `CList.insertionSort_id_of_sorted_nodup`, `CList.normalize_idem`, `CList.sorted_nodup_setEquiv_eq`, `CList.extEq_normalize`, `CList.normalize_eq_of_extEq`, `CList.extEq_iff_normalize_eq`, `CList.dedup_cons_fresh`, `CList.normalize_cons_fresh`, `CList.normalize_fixed_of_mem_normalize`, `CList.normalize_mk_of_normalized_sorted_nodup`

### CList.lean (barrel)

Imports only: `CList/Basic`, `CList/ExtEq`, `CList/Filter`, `CList/SetEquiv`, `CList/Order`, `CList/Sort`, `CList/Normalize`. No new exports.
