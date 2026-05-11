# Technical Reference — AczelSetTheory

**Last updated:** 2026-05-11 00:00
**Author**: Julián Calderón Almendros
**Lean version**: v4.29.0

---

## 0. Naming Conventions Guide for the Reader

This project adopts [Mathlib](https://leanprover-community.github.io/contribute/naming.html)-style naming conventions.
Below are the keys for reading and searching theorems.

### 0.1 Capitalization Rules

- **Theorems/lemmas** (Prop): `snake_case` — `extEq_refl`, `lt_trans`
- **Prop definitions** (predicates): `UpperCamelCase` — `Sorted`, `Nodup`, `SetEquiv`; in theorem names → `lowerCamelCase`: `sorted_nodup_setEquiv_eq`
- **Functions** (returning values): `lowerCamelCase` — `normalize`, `orderedInsert`, `insertionSort`, `dedup`
- **Types**: `UpperCamelCase` — `CList`, `CListOp`, `HFSet`
- **Acronyms**: as group — `HF` (as in `HFSet`)

### 0.2 Symbol-to-Word Dictionary

| Symbol | Name | | Symbol | Name | | Symbol | Name |
|--------|------|---|--------|------|---|--------|------|
| ∈ | `mem` | | ∪ | `union` | | + | `add` |
| ∉ | `not_mem` | | ∩ | `inter` | | * | `mul` |
| ⊆ | `subset` | | ⋃ | `sUnion` | | - | `sub`/`neg` |
| ⊂ | `ssubset` | | ⋂ | `sInter` | | / | `div` |
| 𝒫 | `powerset` | | \ | `sdiff` | | ^ | `pow` |
| σ | `succ` | | △ | `symmDiff` | | ∣ | `dvd` |

---

## 1. Module List

| # | File | Namespace | Status | Depends on | Depended on by |
|---|------|-----------|--------|------------|----------------|
| 1 | `AczelSetTheory/CList/Basic.lean` | `CList` | ✅ Complete | `Init.Data.List.Basic` | ExtEq, SetEquiv, Order, Sort, Normalize, Filter, HFSets, Main |
| 2 | `AczelSetTheory/CList/ExtEq.lean` | `CList` | ✅ Complete | Basic | SetEquiv, Order, Filter |
| 3 | `AczelSetTheory/CList/Filter.lean` | `CList` | ✅ Complete | ExtEq | Operations/Separation, Operations/Intersection, Operations/Setminus |
| 4 | `AczelSetTheory/CList/SetEquiv.lean` | `CList` | ✅ Complete | ExtEq | Sort |
| 5 | `AczelSetTheory/CList/Order.lean` | `CList` | ✅ Complete | ExtEq | Sort |
| 6 | `AczelSetTheory/CList/Sort.lean` | `CList` | ✅ Complete | Order, SetEquiv | Normalize |
| 7 | `AczelSetTheory/CList/Normalize.lean` | `CList` | ✅ Complete | Sort | (via CList root) |
| 8 | `AczelSetTheory/CList.lean` | — | ✅ Complete | Basic, ExtEq, Filter, SetEquiv, Order, Sort, Normalize | HFSets |
| 9 | `AczelSetTheory/HFSets.lean` | `HFSet` | ✅ Complete | CList (all) | Operations/*, Axioms/*, Notation |
| 10 | `AczelSetTheory/Operations/Union.lean` | `CList`, `HFSet` | ✅ Complete | CList/ExtEq, HFSets | Axioms/Union |
| 11 | `AczelSetTheory/Operations/Intersection.lean` | `HFSet` | ✅ Complete | HFSets, CList/Filter | Axioms/Intersection |
| 12 | `AczelSetTheory/Operations/Setminus.lean` | `HFSet` | ✅ Complete | HFSets, CList/Filter | Axioms/Setminus |
| 13 | `AczelSetTheory/Operations/Separation.lean` | `HFSet` | ✅ Complete | HFSets, CList/Filter | Axioms/Separation |
| 14 | `AczelSetTheory/Operations/Pair.lean` | `HFSet` | ✅ Complete | HFSets | Axioms/Pair |
| 15 | `AczelSetTheory/Operations/Powerset.lean` | `CList`, `HFSet` | ✅ Complete | HFSets | Axioms/Powerset |
| 16 | `AczelSetTheory/Axioms/Union.lean` | `HFSet` | ✅ Complete | HFSets, Operations/Union | — |
| 17 | `AczelSetTheory/Axioms/Intersection.lean` | `HFSet` | ✅ Complete | HFSets, Operations/Intersection | — |
| 18 | `AczelSetTheory/Axioms/Setminus.lean` | `HFSet` | ✅ Complete | HFSets, Operations/Setminus | — |
| 19 | `AczelSetTheory/Axioms/Separation.lean` | `HFSet` | ✅ Complete | HFSets, Operations/Separation | — |
| 20 | `AczelSetTheory/Axioms/Pair.lean` | `HFSet` | ✅ Complete | HFSets, Operations/Pair | — |
| 21 | `AczelSetTheory/Axioms/Powerset.lean` | `HFSet` | ✅ Complete | Operations/Powerset, Axioms/Separation | — |
| 22 | `AczelSetTheory/Notation.lean` | `HFSet` | ✅ Complete | HFSets | AczelSetTheory.lean |
| 23 | `AczelSetTheory/PList/Basic.lean` | `PList` | ✅ Complete | `Peano.PeanoNat`, `Peano.PeanoNat.Add` | PList/Lemmas |
| 24 | `AczelSetTheory/PList/Lemmas.lean` | `PList` | ✅ Complete | PList/Basic, `Peano.PeanoNat.{Add,Axioms,Order}` | PList/Omega0 |
| 25 | `AczelSetTheory/PList/Omega0.lean` | `PList.Omega0` | ✅ Complete | PList/Lemmas, `Peano.PeanoNat.{Add,Axioms,Order,StrictOrder}` | — |
| — | `AczelSetTheory/PList.lean` | — | ✅ Complete | PList/{Basic,Lemmas,Omega0} | AczelSetTheory.lean |
| — | `AczelSetTheory.lean` | — | ✅ Complete | PList, CList, HFSets, Operations/*, Axioms/*, Notation | Main |
| — | `Main.lean` | — | ✅ Complete | CList.Basic | — |

---

## 2. Module Dependencies

```
Peano.PeanoNat (+ Add, Axioms, Order, StrictOrder)
  └─ PList/Basic.lean
       └─ PList/Lemmas.lean
            └─ PList/Omega0.lean
PList.lean ── imports Basic + Lemmas + Omega0

Init.Data.List.Basic
  └─ CList/Basic.lean
       ├─ CList/ExtEq.lean
       │    ├─ CList/SetEquiv.lean ──┐
       │    ├─ CList/Order.lean ─────┤
       │    │                        └─ CList/Sort.lean
       │    │                             └─ CList/Normalize.lean
       │    └─ CList/Filter.lean
       └─ (used directly by Main.lean)

CList.lean (root) ── imports all 7 sub-modules
  └─ HFSets.lean
       ├─ Operations/Union.lean ──────────── Axioms/Union.lean
       ├─ Operations/Intersection.lean ───── Axioms/Intersection.lean
       ├─ Operations/Setminus.lean ───────── Axioms/Setminus.lean
       ├─ Operations/Separation.lean ─────── Axioms/Separation.lean ──┐
       ├─ Operations/Pair.lean ───────────── Axioms/Pair.lean         │
       ├─ Operations/Powerset.lean ───────── Axioms/Powerset.lean ◀───┘
       └─ Notation.lean
            └─ AczelSetTheory.lean (project root)
```

---

## 3. Namespaces

| Namespace | Modules | Description |
|-----------|---------|-------------|
| `CList` | Basic, ExtEq, Filter, SetEquiv, Order, Sort, Normalize, Operations/Union (partial), Operations/Powerset (partial) | All CList definitions and theorems |
| `HFSet` | HFSets, Operations/*, Axioms/*, Notation | Quotient type and its API |
| `PList` | PList/Basic, PList/Lemmas | Polymorphic list type with ℕ₀ indexing; bridge to `List` |
| `PList.Omega0` | PList/Omega0 | Bridge lemmas `ψ_*` used internally by the `omega₀` tactic |
| (top-level) | Basic | `CList` inductive type defined at top level, operations inside `namespace CList` |

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

### 4.16 PList/Basic.lean — `namespace PList`

#### 4.16.1 Core Type

```lean
inductive PList (α : Type) : Type where
  | nil  : PList α
  | cons : α → PList α → PList α
  deriving Repr, Inhabited
```

- **Math**: Polymorphic list type; mirror of `List α` with ℕ₀-valued length.
- Computable. Structural.

#### 4.16.2 `length`

```lean
def length : PList α → ℕ₀
  | nil      => 𝟘
  | cons _ t => σ (length t)
```

- **Math**: |nil| ≔ 0; |h :: t| ≔ σ(|t|). Returns `ℕ₀` (Peano natural).
- Computable. Structural recursion.

#### 4.16.3 Structural operations

```lean
def isEmpty : PList α → Bool
def head?   : PList α → Option α
def tail    : PList α → PList α
def get?    : PList α → ℕ₀ → Option α
def getD    : α → PList α → ℕ₀ → α
```

- All computable, structural recursion.

#### 4.16.4 Higher-order operations

```lean
def map     : (α → β) → PList α → PList β
def foldl   : (β → α → β) → β → PList α → β
def foldr   : (α → β → β) → β → PList α → β
def any     : (α → Bool) → PList α → Bool
def all     : (α → Bool) → PList α → Bool
def filter  : (α → Bool) → PList α → PList α
def append  : PList α → PList α → PList α
def flatMap : (α → PList β) → PList α → PList β
def reverse : PList α → PList α
def zipWith : (α → β → γ) → PList α → PList β → PList γ
```

- All computable, structural recursion. `Append (PList α)` instance via `append`.

#### 4.16.5 Membership

```lean
def mem [DecidableEq α] (x : α) : PList α → Bool     -- Bool membership
inductive Mem (a : α) : PList α → Prop where          -- Prop membership
  | head : Mem a (cons a t)
  | tail : Mem a t → Mem a (cons b t)
instance : Membership α (PList α)                     -- enables x ∈ l notation
```

- `Membership.mem` has signature `γ → α → Prop` (container first in Lean 4.29).
- Instance: `⟨fun l a => Mem a l⟩`.

#### 4.16.6 Bridge to `List`

```lean
def toList : PList α → List α
def ofList : List α → PList α
```

- Computable. Structural. `toList ∘ ofList = id` and `ofList ∘ toList = id` (see §6.16).

---

### 4.17 PList/Lemmas.lean — `namespace PList`

No new definitions; only theorems (see §6.16).

**Key technical note**: theorems over `length` use `add n m` (the direct `Peano.Add.add`)
instead of `n + m` to avoid elaboration ambiguity introduced by
`export Peano.Add(add, ...)` making both paths available under `open Peano`.

---

### 4.18 PList/Omega0.lean — `namespace PList.Omega0` + tactic macro

#### 4.18.1 Bridge lemmas

```lean
theorem ψ_eq_iff (n m : ℕ₀) : n = m ↔ Ψ n = Ψ m
theorem ψ_le_iff (n m : ℕ₀) : n ≤ m ↔ Ψ n ≤ Ψ m
theorem ψ_lt_iff (n m : ℕ₀) : n < m ↔ Ψ n < Ψ m
theorem ψ_zero : Ψ (𝟘 : ℕ₀) = (0 : Nat)
theorem ψ_succ (n : ℕ₀) : Ψ (σ n) = Nat.succ (Ψ n)
theorem ψ_add (n m : ℕ₀) :
    Ψ (add n m) = @HAdd.hAdd Nat Nat Nat instHAdd (Ψ n) (Ψ m)
```

- All use `Ψ : ℕ₀ → ℕ` (the Peano isomorphism in the ℕ₀ → ℕ direction).
- `ψ_add` uses `@HAdd.hAdd Nat Nat Nat instHAdd` to avoid `Coe Nat ℕ₀` ambiguity
  and to ensure `omega` recognises the addition (omega does not handle `Nat.add`).

#### 4.18.2 `omega₀` tactic macro

```lean
macro "omega₀" : tactic =>
  `(tactic| (simp only [PList.Omega0.ψ_eq_iff, PList.Omega0.ψ_le_iff,
             PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_zero, PList.Omega0.ψ_succ,
             PList.Omega0.ψ_add] at *; omega))
```

- **Use**: solves linear arithmetic goals over `ℕ₀` by transporting to `ℕ` via `Ψ`.
- Handles `=`, `≤`, `<`, `σ`, `add`, `𝟘` and combinations thereof.

---

## 5. Axioms

None. This project builds constructively from Lean 4 without additional axioms.

---

## 6. Main Theorems

> Only fully proven theorems appear here. No `sorry` remains.

### 6.1 CList/Basic.lean

| # | Theorem | Lean signature | Math | Terminated by |
|---|---------|---------------|------|---------------|
| 1 | `cSize_lt_of_mem` | `{x : CList} {xs : List CList} (h : x ∈ xs) : cSize x < cSize (mk xs)` | x ∈ xs → \|x\| < \|{xs}\| | structural |

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

### 6.3 CList/Filter.lean

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `subset_filter` | `(P : CList → Bool) (xs : List CList) : subset (mk (xs.filter P)) (mk xs) = true` |
| 2 | `mem_filter_of_mem` | `(P : CList → Bool) (hP_resp : P_respects P) (x : CList) (xs : List CList) (hx : mem x (mk xs) = true) (hPx : P x = true) : mem x (mk (xs.filter P)) = true` |
| 3 | `filter_subset_filter` | `(P : CList → Bool) (hP_resp : P_respects P) (xs ys : List CList) (hsub : subset (mk xs) (mk ys) = true) : subset (mk (xs.filter P)) (mk (ys.filter P)) = true` |
| 4 | `extEq_filter` | `(P : CList → Bool) (hP_resp : P_respects P) (xs ys : List CList) (heq : extEq (mk xs) (mk ys) = true) : extEq (mk (xs.filter P)) (mk (ys.filter P)) = true` |
| 5 | `P_of_mem_filter` | `(P : CList → Bool) (hP_resp : P_respects P) (x : CList) (xs : List CList) (hx : mem x (mk (xs.filter P)) = true) : P x = true` |

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

### 6.5 CList/Order.lean

| # | Theorem | Lean signature | Terminated by |
|---|---------|---------------|---------------|
| 1 | `lt_irrefl` | `(A : CList) : lt A A = false` | `cSize A` |
| 2 | `lt_antisymm` | `(A B : CList) (h1 : lt A B = false) (h2 : lt B A = false) : A = B` | `cSize A + cSize B` |
| 3 | `lt_asymm` | `(A B : CList) (h : lt A B = true) : lt B A = false` | `cSize A + cSize B` |
| 4 | `lt_total` | `(A B : CList) : A ≠ B → lt A B = true ∨ lt B A = true` | `cSize A + cSize B` |
| 5 | `lt_total_extEq` | `(A B : CList) : extEq A B = false → lt A B = true ∨ lt B A = true` | — (uses `lt_total`) |
| 6 | `lt_trans` | `(A B C : CList) (h1 : lt A B = true) (h2 : lt B C = true) : lt A C = true` | `cSize A + cSize B + cSize C` |

### 6.6 CList/Sort.lean

| # | Theorem | Lean signature | Dependencies |
|---|---------|---------------|--------------|
| 1 | `insertionSort_sorted` | `(l : List CList) : Sorted (insertionSort l)` | `orderedInsert_sorted` (private) |
| 2 | `insertionSort_mem_subset` | `(z : CList) (l : List CList) : z ∈ insertionSort l → z ∈ l` | `mem_of_mem_orderedInsert` (private) |
| 3 | `insertionSort_nodup` | `(l : List CList) (hl : Nodup l) : Nodup (insertionSort l)` | `orderedInsert_nodup` (private) |
| 4 | `insertionSort_setEquiv` | `(l : List CList) : SetEquiv (insertionSort l) l` | `orderedInsert_setEquiv` (private) |

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

### 6.14 Axioms/*.lean — `namespace HFSet`

All **Zermelo axioms** are proven as theorems (not postulated):

| # | Theorem | File | Lean signature |
|---|---------|------|---------------|
| 1 | `mem_union` | Axioms/Union | `(z A B : HFSet) : z ∈ union A B ↔ z ∈ A ∨ z ∈ B` |
| 2 | `mem_sUnion` | Axioms/Union | `(z A : HFSet) : z ∈ sUnion A ↔ ∃ Y : HFSet, Y ∈ A ∧ z ∈ Y` |
| 3 | `mem_interCList_iff` | Axioms/Intersection | `(a b xc : CList) : CList.mem xc (interCList a b) = true ↔ CList.mem xc a = true ∧ CList.mem xc b = true` |
| 4 | `mem_inter` | Axioms/Intersection | `(A B : HFSet) (x : HFSet) : x ∈ inter A B ↔ x ∈ A ∧ x ∈ B` |
| 5 | `mem_setminusCList_iff` | Axioms/Setminus | `(a b xc : CList) : CList.mem xc (setminusCList a b) = true ↔ CList.mem xc a = true ∧ CList.mem xc b = false` |
| 6 | `mem_setminus` | Axioms/Setminus | `(A B : HFSet) (x : HFSet) : x ∈ setminus A B ↔ x ∈ A ∧ ¬ (x ∈ B)` |
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

### 6.16 PList/Lemmas.lean — `namespace PList`

#### Length

| # | Theorem | Lean signature |
|---|---------|----------------|
| 1 | `length_nil` | `length (α := α) nil = 𝟘` |
| 2 | `length_cons` | `(h : α) (t : PList α) : length (cons h t) = σ (length t)` |
| 3 | `length_eq_zero_iff_nil` | `(l : PList α) : length l = 𝟘 ↔ l = nil` |

#### Append

| # | Theorem | Lean signature |
|---|---------|----------------|
| 4 | `append_nil` | `(l : PList α) : l.append nil = l` |
| 5 | `nil_append` | `(l : PList α) : (nil : PList α).append l = l` |
| 6 | `append_assoc` | `(l₁ l₂ l₃ : PList α) : (l₁.append l₂).append l₃ = l₁.append (l₂.append l₃)` |
| 7 | `length_append` | `(l₁ l₂ : PList α) : length (l₁.append l₂) = add (length l₁) (length l₂)` |

#### Map

| # | Theorem | Lean signature |
|---|---------|----------------|
| 8 | `map_nil` | `(f : α → β) : map f (nil : PList α) = nil` |
| 9 | `map_cons` | `(f : α → β) (h : α) (t : PList α) : map f (cons h t) = cons (f h) (map f t)` |
| 10 | `length_map` | `(f : α → β) (l : PList α) : length (map f l) = length l` |
| 11 | `map_append` | `(f : α → β) (l₁ l₂ : PList α) : map f (l₁.append l₂) = (map f l₁).append (map f l₂)` |

#### Bridge toList/ofList

| # | Theorem | Lean signature |
|---|---------|----------------|
| 12 | `toList_nil` | `toList (α := α) nil = []` |
| 13 | `toList_cons` | `(h : α) (t : PList α) : toList (cons h t) = h :: toList t` |
| 14 | `ofList_nil` | `ofList (α := α) [] = nil` |
| 15 | `ofList_cons` | `(h : α) (t : List α) : ofList (h :: t) = cons h (ofList t)` |
| 16 | `toList_ofList` | `(l : List α) : toList (ofList l) = l` |
| 17 | `ofList_toList` | `(l : PList α) : ofList (toList l) = l` |
| 18 | `length_toList` | `(l : PList α) : Λ (toList l).length = length l` |

#### Membership

| # | Theorem | Lean signature |
|---|---------|----------------|
| 19 | `mem_cons_iff` | `[DecidableEq α] (x h : α) (t : PList α) : mem x (cons h t) = true ↔ x = h ∨ mem x t = true` |
| 20 | `Mem_cons_iff` | `(x h : α) (t : PList α) : Mem x (cons h t) ↔ x = h ∨ Mem x t` |
| 21 | `not_mem_nil` | `(x : α) : ¬ Mem x (nil : PList α)` |

#### Filter

| # | Theorem | Lean signature |
|---|---------|----------------|
| 22 | `length_filter_le` | `(p : α → Bool) (l : PList α) : Peano.Order.le₀ (length (filter p l)) (length l)` |

### 6.17 PList/Omega0.lean — `namespace PList.Omega0`

Bridge lemmas: see §4.18.1. No additional theorems beyond the 6 bridge lemmas and the `omega₀` tactic macro.

---

## 7. Exports per Module

### CList/Basic.lean

`CList`, `CList.mk`, `CList.cSize`, `CList.cSizeList`, `CList.cSize_lt_of_mem`, `CList.empty`, `CListOp`, `CList.evalOp`, `CList.mem`, `CList.subset`, `CList.extEq`, `BEq CList`, `CList.lt`, `CList.dedupAux`, `CList.dedup`, `CList.orderedInsert`, `CList.insertionSort`, `CList.normalize`, `CList.zero`, `CList.one`, `CList.two`, `CList.three`, `CList.dirty`

### CList/ExtEq.lean

`CList.subset_mono`, `CList.subset_refl`, `CList.extEq_refl`, `CList.extEq_def`, `CList.subset_nil`, `CList.subset_cons`, `CList.mem_nil`, `CList.mem_cons`, `CList.extEq_trans`, `CList.subset_trans`, `CList.mem_subset`, `CList.mem_of_extEq`, `CList.extEq_comm`

### CList/SetEquiv.lean

`CList.Nodup`, `CList.dedup_nodup`, `CList.SetEquiv`, `CList.SetEquiv.refl`, `CList.SetEquiv.symm`, `CList.SetEquiv.trans`, `CList.mem_eq_any`, `CList.extEq_mk_iff_setEquiv`, `CList.dedup_setEquiv_self`

### CList/Order.lean

`CList.lt_irrefl`, `CList.lt_antisymm`, `CList.lt_asymm`, `CList.lt_total`, `CList.lt_total_extEq`, `CList.lt_trans`

### CList/Sort.lean

`CList.Sorted`, `CList.insertionSort_sorted`, `CList.insertionSort_mem_subset`, `CList.insertionSort_nodup`, `CList.insertionSort_setEquiv`

### CList/Normalize.lean

`CList.cSizeList_dedup_le`, `CList.cSizeList_insertionSort_le`, `CList.normalize_cSize_le`, `CList.dedup_id_of_nodup`, `CList.insertionSort_id_of_sorted_nodup`, `CList.normalize_idem`, `CList.mem_of_mem_dedup`, `CList.sorted_nodup_setEquiv_eq`, `CList.normalize_eq_of_extEq`

### HFSets.lean

`CList.Setoid`, `HFSet`, `HFSet.repr`, `HFSet.canonicalEq`, `HFSet.canonicalEq_iff_eq`, `HFSet.empty`, `HFSet.mem_resp_right`, `HFSet.mem_resp_left`, `HFSet.Mem`, `Membership HFSet HFSet`, `HFSet.mem_mk`, `HFSet.subset_iff_forall_mem_clist`, `HFSet.extensionality`, `HFSet.not_mem_empty`

### CList/Filter.lean

`CList.P_respects`, `CList.subset_filter`, `CList.mem_filter_of_mem`, `CList.filter_subset_filter`, `CList.extEq_filter`, `CList.P_of_mem_filter`

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

`HFSet.mem_setminusCList_iff`, `HFSet.mem_setminus`

### Axioms/Separation.lean

`HFSet.mem_filterCList_iff`, `HFSet.mem_sep`

### Axioms/Pair.lean

`HFSet.mem_pair`

### Axioms/Powerset.lean

`HFSet.mem_powerset`

### Notation.lean

`HFSet.singleton`, `HFSet.insertCList`, `HFSet.insert`, `HFSet.mem_insertCList_right`, `HFSet.subset_insertCList_right`, `HFSet.insertCList_subset`, `HFSet.insertCList_extEq`, `HFSet.filterCList` (redefined), `HFSet.filterCList_extEq_extEq` (redefined), `HFSet.sep` (redefined), `HFSet.zero` … `HFSet.nine`, `OfNat HFSet 0` … `OfNat HFSet 9`

### PList/Basic.lean

`PList`, `PList.nil`, `PList.cons`, `PList.length`, `PList.isEmpty`, `PList.head?`, `PList.tail`, `PList.get?`, `PList.getD`, `PList.map`, `PList.foldl`, `PList.foldr`, `PList.any`, `PList.all`, `PList.filter`, `PList.append`, `Append (PList α)`, `PList.flatMap`, `PList.reverse`, `PList.zipWith`, `PList.mem`, `PList.Mem`, `Membership α (PList α)`, `PList.toList`, `PList.ofList`

### PList/Lemmas.lean

`PList.length_nil`, `PList.length_cons`, `PList.length_eq_zero_iff_nil`, `PList.append_nil`, `PList.nil_append`, `PList.append_assoc`, `PList.length_append`, `PList.map_nil`, `PList.map_cons`, `PList.length_map`, `PList.map_append`, `PList.toList_nil`, `PList.toList_cons`, `PList.ofList_nil`, `PList.ofList_cons`, `PList.toList_ofList`, `PList.ofList_toList`, `PList.length_toList`, `PList.mem_cons_iff`, `PList.Mem_cons_iff`, `PList.not_mem_nil`, `PList.length_filter_le`

### PList/Omega0.lean

`PList.Omega0.ψ_eq_iff`, `PList.Omega0.ψ_le_iff`, `PList.Omega0.ψ_lt_iff`, `PList.Omega0.ψ_zero`, `PList.Omega0.ψ_succ`, `PList.Omega0.ψ_add`, tactic macro `omega₀`

---

## 8. Notations

| Symbol | Lean definition | Module | Notes |
|--------|----------------|--------|-------|
| `==` | `BEq CList` instance via `extEq` | Basic | Standard Lean `BEq` typeclass |
| `∈` | `Membership HFSet HFSet` instance via `Mem` | HFSets | Standard Lean `Membership` typeclass |
| `∅` | `notation "∅" => empty` | Notation | Empty set |
| `{[a, b]}` | `macro` → `pair $a $b` | Notation | Unordered pair |
| `{[a]}` | `macro` → `singleton $a` | Notation | Singleton |
| `{[a, b, c, ...]}` | `macro_rules` → `insert a {[b, c, ...]}` | Notation | Finite set (3+ elements, recursive) |
| `{[x ∈ A <\|> P]}` | `macro_rules` → `sep A (fun x => P)` | Notation | Separation / comprehension |
| `0` … `9` | `OfNat HFSet n` instances | Notation | Von Neumann numerals |

---

## Projection Log

| Date | Files projected | Projector |
|------|----------------|-----------|
| 2026-04-04 | (stub created) | Julián Calderón Almendros |
| 2026-04-08 | CList/{Basic,ExtEq,SetEquiv,Order,Sort,Normalize}.lean, CList.lean, HFSets.lean | Claude (AI assistant) |
| 2026-04-09 | HFSets.lean (Mem, pair, Zermelo axioms) | Claude (AI assistant) |
| 2026-04-10 | CList/Filter, Operations/{Union,Intersection,Setminus,Separation,Pair,Powerset}, Axioms/{Union,Intersection,Setminus,Separation,Pair,Powerset}, Notation | Claude (AI assistant) |
| 2026-05-11 | PList/{Basic,Lemmas,Omega0} — Phase 1 Peano integration | Claude (AI assistant) |

> To project a file: read it fully, then update sections 1–8 above following AI-GUIDE.md §4–14.
