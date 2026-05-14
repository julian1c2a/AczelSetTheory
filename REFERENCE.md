# Technical Reference — AczelSetTheory

**Last updated:** 2026-05-14 00:00
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
| 1 | [`AczelSetTheory/CList/Basic.lean`](doc/REFERENCE-CList.md) | `CList` | ✅ Complete | `Init.Data.List.Basic` | ExtEq, SetEquiv, Order, Sort, Normalize, Filter, HFSets, Main |
| 2 | [`AczelSetTheory/CList/ExtEq.lean`](doc/REFERENCE-CList.md) | `CList` | ✅ Complete | Basic | SetEquiv, Order, Filter |
| 3 | [`AczelSetTheory/CList/Filter.lean`](doc/REFERENCE-CList.md) | `CList` | ✅ Complete | ExtEq | Operations/Separation, Operations/Intersection, Operations/Setminus |
| 4 | [`AczelSetTheory/CList/SetEquiv.lean`](doc/REFERENCE-CList.md) | `CList` | ✅ Complete | ExtEq | Sort |
| 5 | [`AczelSetTheory/CList/Order.lean`](doc/REFERENCE-CList.md) | `CList` | ✅ Complete | ExtEq | Sort |
| 6 | [`AczelSetTheory/CList/Sort.lean`](doc/REFERENCE-CList.md) | `CList` | ✅ Complete | Order, SetEquiv | Normalize |
| 7 | [`AczelSetTheory/CList/Normalize.lean`](doc/REFERENCE-CList.md) | `CList` | ✅ Complete | Sort | (via CList root) |
| 8 | [`AczelSetTheory/CList.lean`](doc/REFERENCE-CList.md) | — | ✅ Complete | Basic, ExtEq, Filter, SetEquiv, Order, Sort, Normalize | HFSets |
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
| 26 | `AczelSetTheory/Operations/FunctionComp.lean` | `HFSet` | ✅ Complete | Operations/Composition, Operations/Powerset | Axioms/FunctionComp, Axioms/Identity |
| 27 | `AczelSetTheory/Operations/Identity.lean` | `HFSet` | ✅ Complete | Operations/OrderedPair, Operations/Powerset | Axioms/Identity |
| 28 | `AczelSetTheory/Operations/Product.lean` | `HFSet` | ✅ Complete | Operations/OrderedPair, Operations/Powerset, Operations/Union | Axioms/Product |
| 29 | `AczelSetTheory/Axioms/FunctionComp.lean` | `HFSet` | ✅ Complete | Operations/FunctionComp, Axioms/Powerset, Axioms/Separation, Axioms/Union, Axioms/Pair, Axioms/Singleton, Axioms/OrderedPair, Axioms/Bijection, Axioms/Inverse | Axioms/Identity |
| 30 | `AczelSetTheory/Axioms/Identity.lean` | `HFSet` | ✅ Complete | Operations/Identity, Axioms/Powerset, Axioms/Separation, Axioms/Pair, Axioms/Singleton, Axioms/OrderedPair, Axioms/FunctionComp, Axioms/Inverse | Axioms/Image |
| 31 | `AczelSetTheory/Axioms/Product.lean` | `HFSet` | ✅ Complete | Operations/Product, Axioms/Powerset, Axioms/Separation, Axioms/Pair, Axioms/Singleton, Axioms/OrderedPair, Axioms/Union, Axioms/Relation, Axioms/Function | — |
| 32 | `AczelSetTheory/Axioms/Image.lean` | `HFSet` | ✅ Complete | Axioms/Composition, Axioms/FunctionComp, Axioms/Identity, Axioms/Intersection, Axioms/Union | — |
| 33 | `AczelSetTheory/Operations/OrderedPair.lean` | `HFSet` | ✅ Complete | Operations/Pair, Notation | Operations/Relation, Operations/Inverse, Operations/Restriction, Operations/Composition |
| 34 | `AczelSetTheory/Operations/Relation.lean` | `HFSet` | ✅ Complete | Operations/OrderedPair, Operations/Union, Axioms/Decidable | Operations/Function, Operations/Inverse, Operations/Restriction, Operations/Composition, Operations/Replacement |
| 35 | `AczelSetTheory/Operations/Function.lean` | `HFSet` | ✅ Complete | Operations/Relation | Axioms/Function |
| 36 | `AczelSetTheory/Operations/Inverse.lean` | `HFSet` | ✅ Complete | Operations/Relation, Operations/OrderedPair, Operations/Powerset | Axioms/Inverse |
| 37 | `AczelSetTheory/Operations/Restriction.lean` | `HFSet` | ✅ Complete | Operations/Relation | Axioms/Restriction |
| 38 | `AczelSetTheory/Operations/Composition.lean` | `HFSet` | ✅ Complete | Operations/Relation, Operations/OrderedPair | Operations/FunctionComp, Axioms/Composition |
| 39 | `AczelSetTheory/Operations/Replacement.lean` | `HFSet` | ✅ Complete | Operations/Relation, Operations/Separation | Axioms/Replacement |
| 40 | `AczelSetTheory/Operations/SymDiff.lean` | `HFSet` | ✅ Complete | Operations/Setminus, Operations/Union | Axioms/SymDiff |
| 41 | `AczelSetTheory/Operations/Cardinal.lean` | `HFSet` | ✅ Complete | HFSets, Peano.PeanoNat.Combinatorics.Pow | Axioms/Cardinal |
| 42 | `AczelSetTheory/Axioms/Singleton.lean` | `HFSet` | ✅ Complete | Axioms/Pair, Notation | Axioms/OrderedPair, Axioms/Succ, Axioms/Relation, Axioms/Composition |
| 43 | `AczelSetTheory/Axioms/Subset.lean` | `HFSet` | ✅ Complete | HFSets, Axioms/Union, Axioms/Intersection | Axioms/Succ, Axioms/Restriction, Axioms/Lattice |
| 44 | `AczelSetTheory/Axioms/OrderedPair.lean` | `HFSet` | ✅ Complete | Operations/OrderedPair, Axioms/Pair, Axioms/Singleton | Axioms/Relation, Axioms/Inverse, Axioms/Composition, Axioms/Restriction |
| 45 | `AczelSetTheory/Axioms/Foundation.lean` | `HFSet`, `CList` | ✅ Complete | Axioms/Intersection, HFSets | Axioms/Decidable, Axioms/Succ |
| 46 | `AczelSetTheory/Axioms/Decidable.lean` | `HFSet` | ✅ Complete | HFSets, Axioms/Foundation | Operations/Relation, Axioms/BooleanAlgebra, Axioms/BooleanRing |
| 47 | `AczelSetTheory/Axioms/Relation.lean` | `HFSet` | ✅ Complete | Operations/Relation, Axioms/Separation, Axioms/Union, Axioms/Pair, Axioms/Singleton, Axioms/OrderedPair | Axioms/Function, Axioms/Inverse, Axioms/Composition, Axioms/Restriction |
| 48 | `AczelSetTheory/Axioms/Function.lean` | `HFSet` | ✅ Complete | Operations/Function, Axioms/Relation | Axioms/Bijection, Axioms/Inverse, Axioms/Restriction, Axioms/Replacement, Axioms/Choice |
| 49 | `AczelSetTheory/Axioms/Bijection.lean` | `HFSet` | ✅ Complete | Axioms/Function, Axioms/Restriction | Axioms/Inverse, Axioms/FunctionComp, Axioms/Identity, Axioms/Product |
| 50 | `AczelSetTheory/Axioms/Inverse.lean` | `HFSet` | ✅ Complete | Operations/Inverse, Axioms/Relation, Axioms/Powerset, Axioms/Separation, Axioms/Pair, Axioms/Singleton, Axioms/OrderedPair, Axioms/Bijection | Axioms/Identity |
| 51 | `AczelSetTheory/Axioms/Composition.lean` | `HFSet` | ✅ Complete | Operations/Composition, Axioms/Relation, Axioms/Separation, Axioms/Union, Axioms/Pair, Axioms/Singleton, Axioms/OrderedPair | Axioms/FunctionComp, Axioms/Image |
| 52 | `AczelSetTheory/Axioms/Restriction.lean` | `HFSet` | ✅ Complete | Operations/Restriction, Axioms/Composition, Axioms/Separation, Axioms/Subset, Axioms/OrderedPair | Axioms/Bijection, Axioms/Function |
| 53 | `AczelSetTheory/Axioms/Replacement.lean` | `HFSet` | ✅ Complete | Operations/Replacement, Axioms/Function | — |
| 54 | `AczelSetTheory/Axioms/Succ.lean` | `HFSet` | ✅ Complete | Axioms/Union, Axioms/Singleton, Axioms/Foundation, Axioms/Subset | Axioms/VonNeumann, VN/Basic |
| 55 | `AczelSetTheory/Axioms/SymDiff.lean` | `HFSet` | ✅ Complete | Operations/SymDiff, Axioms/Setminus, Axioms/Union | Axioms/BooleanRing |
| 56 | `AczelSetTheory/Axioms/Lattice.lean` | `HFSet` | ✅ Complete | Axioms/Union, Axioms/Intersection, Axioms/Setminus, Axioms/Subset | Axioms/BooleanAlgebra, Axioms/BooleanRing |
| 57 | `AczelSetTheory/Axioms/BooleanAlgebra.lean` | `HFSet` | ✅ Complete | Axioms/Decidable, Axioms/Subset, Axioms/Lattice, Axioms/Setminus | Axioms/BooleanRing |
| 58 | `AczelSetTheory/Axioms/BooleanRing.lean` | `HFSet` | ✅ Complete | Axioms/Decidable, Axioms/Lattice, Axioms/BooleanAlgebra, Axioms/SymDiff | — |
| 59 | `AczelSetTheory/Axioms/VonNeumann.lean` | `HFSet` | ✅ Complete | Axioms/Succ | VN/Basic, VN/IsNat |
| 60 | `AczelSetTheory/Axioms/Choice.lean` | `HFSet` | ✅ Complete | Axioms/Function | — |
| 61 | `AczelSetTheory/Axioms/Cardinal.lean` | `HFSet` | ✅ Complete | Operations/Cardinal, Operations/Powerset, Notation | — |
| 62 | `AczelSetTheory/PList/Fin0.lean` | `Fin₀`, `PList` | ✅ Complete | PList/Omega0, Peano.PeanoNat.{StrictOrder,Order,Axioms} | HFList |
| 63 | `AczelSetTheory/HFList.lean` | `HFList`, `FinList` | ✅ Complete | HFSets, PList/Fin0 | — |
| 64 | `AczelSetTheory/VN/Basic.lean` | `VN` | ✅ Complete | Axioms | VN/Injective, VN/IsNat, VN/Arithmetic |
| 65 | `AczelSetTheory/VN/Injective.lean` | `VN` | ✅ Complete | VN/Basic | VN/Arithmetic |
| 66 | `AczelSetTheory/VN/IsNat.lean` | `VN` | ✅ Complete | VN/Basic | — |
| 67 | `AczelSetTheory/VN/Arithmetic.lean` | `VN` | ✅ Complete | VN/Injective, PList/Omega0 | — |
| — | `AczelSetTheory/VN.lean` | — | ✅ Complete | VN/{Basic,Injective,IsNat,Arithmetic} | AczelSetTheory.lean |
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

### 4.1–4.7 CList modules

> Definitions moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#4-definitions).

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

### 4.33 Operations/SymDiff.lean — `namespace HFSet`

#### 4.33.1 `HFSet.symDiff`

```lean
def HFSet.symDiff (A B : HFSet) : HFSet
```

- **Math**: A △ B ≔ (A \ B) ∪ (B \ A). Defined via `symDiffCList` on the underlying lists.

---

### 4.34 Operations/Cardinal.lean — `namespace HFSet`

#### 4.34.1 `HFSet.card`

```lean
def HFSet.cardCList (a : CList) : ℕ₀
def HFSet.card (A : HFSet) : ℕ₀
```

- **Math**: |A| — cardinality of a hereditarily finite set as a Peano natural number ℕ₀.

---

### 4.35 Axioms/Function.lean — `namespace HFSet` (new predicates)

#### 4.35.1 `HFSet.isInjective` / `isSurjective` / `isBijective`

```lean
def HFSet.isInjective (f : HFSet) : Prop :=
  ∀ a₁ a₂ b, ⟪a₁, b⟫ ∈ f → ⟪a₂, b⟫ ∈ f → a₁ = a₂
def HFSet.isSurjective (f B : HFSet) : Prop := range f = B
def HFSet.isBijective  (f A B : HFSet) : Prop :=
  isTotalFunction f A B ∧ isInjective f ∧ isSurjective f B
```

- **Math**: standard injectivity / surjectivity / bijectivity.

---

### 4.36 Axioms/BooleanAlgebra.lean — `namespace HFSet`

#### 4.36.1 `HFSet.compl`

```lean
def HFSet.compl (U X : HFSet) : HFSet := setminus U X
```

- **Math**: complement of X in universe U — Uᶜ(X) ≔ U \ X.

---

### 4.37 Axioms/Succ.lean — `namespace HFSet`

#### 4.37.1 `HFSet.succ`

```lean
def HFSet.succ (A : HFSet) : HFSet := union A (singleton A)
```

- **Math**: von Neumann successor σ(A) ≔ A ∪ {A}.

---

### 4.38 Axioms/VonNeumann.lean — `namespace HFSet`

#### 4.38.1 `HFSet.isTransitive`

```lean
def HFSet.isTransitive (A : HFSet) : Prop := ∀ x, x ∈ A → x ⊆ A
```

- **Math**: A is a transitive set iff every element of A is also a subset of A.

#### 4.38.2 `HFSet.isNat` (inductive)

```lean
inductive HFSet.isNat : HFSet → Prop where
  | zero : isNat empty
  | succ {n : HFSet} : isNat n → isNat (succ n)
```

- **Math**: n is a von Neumann natural number iff it is ∅ or the successor of a natural number.

---

### 4.39 Axioms/Choice.lean — `namespace HFSet`

#### 4.39.1 `HFSet.choose`

```lean
noncomputable def HFSet.choose (A : HFSet) (_ : A ≠ empty) : HFSet
```

- **Math**: choice function — selects an element from any nonempty set.

---

### 4.40 PList/Fin0.lean — `namespace Fin₀`, `namespace PList`

#### 4.40.1 `Fin₀`

```lean
structure Fin₀ (n : ℕ₀) : Type where
  val  : ℕ₀
  isLt : val < n
```

- **Math**: Peano-indexed bounded natural — analogous to `Fin n` but over ℕ₀.
- Constructor helpers: `Fin₀.zero n`, `Fin₀.succ i`, `Fin₀.last n`.
- Instances: `DecidableEq (Fin₀ n)`, `LT (Fin₀ n)`, `LE (Fin₀ n)`.

#### 4.40.2 `PList.get`

```lean
def PList.get : (l : PList α) → Fin₀ (l.length) → α
```

- **Math**: safe indexing of a `PList` by a bounded Peano index.

---

### 4.41 HFList.lean — `namespace HFList`, `namespace FinList`

#### 4.41.1 `HFList`

```lean
abbrev HFList := PList HFSet
```

- **Math**: an ordered sequence of HF sets (with order, with repetition). Inherits all `PList` operations.

#### 4.41.2 `FinList`

```lean
def FinList (n : ℕ₀) : Type := { l : HFList // l.length = n }
```

- **Math**: an HFList of a fixed Peano length n. Constructor helpers: `FinList.empty`, `FinList.singleton`, `FinList.cons`.

---

### 4.42 VN/Basic.lean — `namespace VN`

#### 4.42.1 `VN.vN`

```lean
def VN.vN : ℕ₀ → HFSet
  | 𝟘   => HFSet.empty
  | σ n => HFSet.succ (vN n)
```

- **Math**: vN(0) = ∅; vN(n+1) = σ(vN(n)). Maps each Peano natural to its von Neumann representative.

---

None. This project builds constructively from Lean 4 without additional axioms.

---

## 6. Main Theorems

> Only fully proven theorems appear here. No `sorry` remains.

### 6.1–6.7 CList theorems

> Theorems moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#6-theorems).

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

### 6.22 Operations/SymDiff.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `symDiffCList_extEq` | `(a₁ a₂ b₁ b₂ : CList) → (ha : CList.extEq a₁ a₂ = true) → (hb : CList.extEq b₁ b₂ = true) → CList.extEq (symDiffCList a₁ b₁) (symDiffCList a₂ b₂) = true` |

### 6.23 Axioms/Singleton.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_singleton` | `(x a : HFSet) : x ∈ singleton a ↔ x = a` |

### 6.24 Axioms/Subset.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `subset_iff` | `(A B : HFSet) : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B` |
| 2 | `subset_refl` | `(A : HFSet) : A ⊆ A` |
| 3 | `subset_trans` | `(A B C : HFSet) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C` |
| 4 | `subset_antisymm` | `(A B : HFSet) (h1 : A ⊆ B) (h2 : B ⊆ A) : A = B` |
| 5 | `empty_subset` | `(A : HFSet) : empty ⊆ A` |
| 6 | `subset_union_left` | `(A B : HFSet) : A ⊆ union A B` |
| 7 | `subset_union_right` | `(A B : HFSet) : B ⊆ union A B` |
| 8 | `inter_subset_left` | `(A B : HFSet) : inter A B ⊆ A` |
| 9 | `inter_subset_right` | `(A B : HFSet) : inter A B ⊆ B` |
| 10 | `subset_inter` | `(A B C : HFSet) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ inter B C` |

### 6.25 Axioms/OrderedPair.lean — `namespace HFSet`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `orderedPair_eq_iff` | `(a b c d : HFSet) : orderedPair a b = orderedPair c d ↔ a = c ∧ b = d` |

### 6.26 Axioms/Foundation.lean — `namespace HFSet`, `namespace CList`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `CList.mem_exists_plist_mem` | `(x : CList) (xs : PList CList) (h : mem x (mk xs) = true) : ∃ y, PList.Mem y xs ∧ extEq x y = true` |
| 2 | `CList.mem_of_plist_mem` | `(y : CList) (xs : PList CList) (h : PList.Mem y xs) : mem y (mk xs) = true` |
| 3 | `foundation` | `(A : HFSet) (hne : A ≠ empty) : ∃ x : HFSet, x ∈ A ∧ ∀ y : HFSet, y ∈ x → ¬ y ∈ A` |

### 6.27 Axioms/Decidable.lean — `namespace HFSet`

| # | Instance | Type |
|---|----------|------|
| 1 | `mem_decidable` | `(x A : HFSet) → Decidable (x ∈ A)` |
| 2 | `existsMem_decidable` | `(A : HFSet) → (P : HFSet → Prop) → [DecidablePred P] → Decidable (∃ x, x ∈ A ∧ P x)` |

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
| 1 | `mem_imageRel` | `{R A b : HFSet} : b ∈ imageRel R A ↔ ∃ a, a ∈ A ∧ ⟪a, b⟫ ∈ R` |
| 2 | `imageRel_empty_rel` | `{A : HFSet} : imageRel empty A = empty` |
| 3 | `imageRel_empty_set` | `{R : HFSet} : imageRel R empty = empty` |
| 4 | `mem_relComp` | `{R S c : HFSet} : c ∈ S ∘ᵣ R ↔ ∃ a b, ⟪a, b⟫ ∈ R ∧ ⟪b, c⟫ ∈ S` |
| 5 | `relComp_empty_left` | `{R : HFSet} : empty ∘ᵣ R = empty` |
| 6 | `relComp_empty_right` | `{S : HFSet} : S ∘ᵣ empty = empty` |

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

| # | Theorem / Def | Lean signature |
|---|--------------|---------------|
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

### 6.43 PList/Fin0.lean — `namespace Fin₀`, `namespace PList`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `Fin₀.elim_zero` | `(i : Fin₀ 𝟘) → False` |
| 2 | `Fin₀.val_lt_bound` | `(i : Fin₀ n) → i.val < n` |
| 3 | `Fin₀.val_le_bound_pred` | `(i : Fin₀ n) → {k : ℕ₀} → (hk : n = σ k) → i.val ≤ k` |
| 4 | `PList.get_eq_get?` | `(l : PList α) → (i : Fin₀ (l.length)) → l.get? i.val = some (l.get i)` |

### 6.44 HFList.lean — `namespace HFList`, `namespace FinList`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `HFList.length_nil` | `length PList.nil = 𝟘` |
| 2 | `HFList.length_cons` | `(h : HFSet) → (t : HFList) → length (PList.cons h t) = σ (length t)` |
| 3 | `HFList.length_append` | `(l₁ l₂ : HFList) → length (l₁ ++ l₂) = add (length l₁) (length l₂)` |
| 4 | `FinList.length_eq` | `(t : FinList n) → t.val.length = n` |
| 5 | `FinList.ext` | `{t s : FinList n} → (h : t.val = s.val) → t = s` |

### 6.45 VN/Basic.lean — `namespace VN`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `vN_zero` | `vN 𝟘 = HFSet.empty` |
| 2 | `vN_succ` | `(n : ℕ₀) → vN (σ n) = HFSet.succ (vN n)` |
| 3 | `vN_succ_ne_empty` | `(n : ℕ₀) → vN (σ n) ≠ HFSet.empty` |
| 4 | `mem_vN_succ` | `(x : HFSet) → (n : ℕ₀) → (x ∈ vN (σ n) ↔ x ∈ vN n ∨ x = vN n)` |
| 5 | `vN_mem_vN_succ` | `(n : ℕ₀) → vN n ∈ vN (σ n)` |
| 6 | `vN_subset_vN_succ` | `(n : ℕ₀) → vN n ⊆ vN (σ n)` |

### 6.46 VN/Injective.lean — `namespace VN`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `vN_injective` | `Function.Injective vN` |

### 6.47 VN/IsNat.lean — `namespace VN`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `isNat_vN` | `(n : ℕ₀) → HFSet.isNat (vN n)` |
| 2 | `vN_mem_range` | `{A : HFSet} → (h : HFSet.isNat A) → ∃ n : ℕ₀, vN n = A` |
| 3 | `isNat_iff_range` | `(A : HFSet) → (HFSet.isNat A ↔ ∃ n : ℕ₀, vN n = A)` |

### 6.48 VN/Arithmetic.lean — `namespace VN`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `mem_vN_iff_lt` | `(m n : ℕ₀) → (vN m ∈ vN n ↔ m < n)` |
| 2 | `vN_mono` | `(m n : ℕ₀) → (h : m ≤ n) → vN m ⊆ vN n` |
| 3 | `vN_le_iff_subset` | `(m n : ℕ₀) → (m ≤ n ↔ vN m ⊆ vN n)` |

---

## 7. Exports per Module

### CList modules (Basic, ExtEq, SetEquiv, Order, Sort, Normalize)

> Exports moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#7-exports-per-module).

### HFSets.lean

`CList.Setoid`, `HFSet`, `HFSet.repr`, `HFSet.canonicalEq`, `HFSet.canonicalEq_iff_eq`, `HFSet.empty`, `HFSet.mem_resp_right`, `HFSet.mem_resp_left`, `HFSet.Mem`, `Membership HFSet HFSet`, `HFSet.mem_mk`, `HFSet.subset_iff_forall_mem_clist`, `HFSet.extensionality`, `HFSet.not_mem_empty`

### CList/Filter.lean

> Exports moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#7-exports-per-module).

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

### Operations/SymDiff.lean

`HFSet.symDiffCList`, `HFSet.symDiff`, `HFSet.symDiffCList_extEq`

### Operations/Cardinal.lean

`HFSet.cardCList`, `HFSet.card`, `HFSet.cardCList_congr`

### Axioms/Singleton.lean

`HFSet.mem_singleton`

### Axioms/Subset.lean

`HFSet.subset_iff`, `HFSet.subset_refl`, `HFSet.subset_trans`, `HFSet.subset_antisymm`, `HFSet.empty_subset`, `HFSet.subset_union_left`, `HFSet.subset_union_right`, `HFSet.inter_subset_left`, `HFSet.inter_subset_right`, `HFSet.subset_inter`

### Axioms/OrderedPair.lean

`HFSet.orderedPair_eq_iff`

### Axioms/Foundation.lean

`CList.mem_exists_plist_mem`, `CList.mem_of_plist_mem`, `HFSet.foundation`

### Axioms/Decidable.lean

`HFSet.mem_decidable`, `HFSet.existsMem_decidable`

### Axioms/Relation.lean

`HFSet.fst_mem_sUnion_sUnion`, `HFSet.snd_mem_sUnion_sUnion`, `HFSet.mem_domain_iff`, `HFSet.mem_range_iff`, `HFSet.domain_empty`, `HFSet.range_empty`, `HFSet.isRelation_empty`

### Axioms/Function.lean

`HFSet.isInjective`, `HFSet.isSurjective`, `HFSet.isBijective`, `HFSet.apply_mem`, `HFSet.apply_eq_of_mem`, `HFSet.totalFunction_apply_mem`, `HFSet.isFunction_empty`, `HFSet.isFunction_unique`, `HFSet.mem_domain_of_mem`, `HFSet.mem_range_of_mem`

### Axioms/Bijection.lean

`HFSet.isInjective_empty`, `HFSet.isInjective_restrict`, `HFSet.isSurjective_empty_codomain`, `HFSet.isSurjective_range`, `HFSet.isSurjective_iff_range_eq`, `HFSet.isBijective_intro`, `HFSet.isBijective_isTotalFunction`, `HFSet.isBijective_isFunction`, `HFSet.isBijective_isInjective`, `HFSet.isBijective_isSurjective`, `HFSet.isBijective_domain_eq`, `HFSet.isBijective_range_eq`, `HFSet.isBijective_empty`

### Axioms/Inverse.lean

`HFSet.mem_relInv`, `HFSet.mem_relInv_pair`, `HFSet.relInv_isRelation`, `HFSet.domain_relInv`, `HFSet.range_relInv`, `HFSet.relInv_relInv`, `HFSet.isFunction_relInv`, `HFSet.isInjective_relInv`, `HFSet.isSurjective_relInv`, `HFSet.isBijective_relInv`

### Axioms/Composition.lean

`HFSet.mem_imageRel`, `HFSet.imageRel_empty_rel`, `HFSet.imageRel_empty_set`, `HFSet.mem_relComp`, `HFSet.relComp_empty_left`, `HFSet.relComp_empty_right`

### Axioms/Restriction.lean

`HFSet.mem_restrict`, `HFSet.restrict_subset`, `HFSet.restrict_isRelation`, `HFSet.mem_restrict_pair`, `HFSet.mem_preimage`, `HFSet.preimage_empty_set`

### Axioms/Replacement.lean

`HFSet.mem_image`, `HFSet.image_empty`, `HFSet.image_of_empty`, `HFSet.image_subset_range`, `HFSet.apply_mem_image`, `HFSet.image_totalFunction_subset`

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

### PList/Fin0.lean

`Fin₀`, `Fin₀.zero`, `Fin₀.succ`, `Fin₀.last`, `Fin₀.ext`, `Fin₀.toFin`, `Fin₀.ofFin`, `Fin₀.elim_zero`, `Fin₀.val_lt_bound`, `Fin₀.val_le_bound_pred`, `PList.get`, `PList.get_eq_get?`

### HFList.lean

`HFList`, `FinList`, `HFList.length_nil`, `HFList.length_cons`, `HFList.length_append`, `FinList.empty`, `FinList.singleton`, `FinList.cons`, `FinList.toHFList`, `FinList.get`, `FinList.length_eq`, `FinList.ext`

### VN/Basic.lean

`VN.vN`, `VN.vN_zero`, `VN.vN_succ`, `VN.vN_succ_ne_empty`, `VN.mem_vN_succ`, `VN.vN_mem_vN_succ`, `VN.vN_subset_vN_succ`

### VN/Injective.lean

`VN.vN_injective`

### VN/IsNat.lean

`VN.isNat_vN`, `VN.vN_mem_range`, `VN.isNat_iff_range`

### VN/Arithmetic.lean

`VN.mem_vN_iff_lt`, `VN.vN_mono`, `VN.vN_le_iff_subset`

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
| `∘f` | `infixl:90 " ∘f " => HFSet.funComp` | Operations/FunctionComp | Functional composition of relations |
| `×ₛ` | `infixl:80 " ×ₛ " => HFSet.prodHF` | Operations/Product | Cartesian product of HF sets |
| `⟪a, b⟫` | `notation "⟪" a ", " b "⟫" => HFSet.orderedPair a b` | Operations/OrderedPair | Kuratowski ordered pair |
| `⁻¹ᵣ` | `postfix:75 "⁻¹ᵣ" => HFSet.relInv` | Operations/Inverse | Relational inverse |
| `↾` | `notation:80 R " ↾ " A => HFSet.restrict R A` | Operations/Restriction | Relation restriction to domain A |
| `∘ᵣ` | `infixl:90 " ∘ᵣ " => HFSet.relComp` | Operations/Composition | Relational composition |

---

## Projection Log

| Date | Files projected | Projector |
|------|----------------|-----------|
| 2026-04-04 | (stub created) | Julián Calderón Almendros |
| 2026-04-08 | CList/{Basic,ExtEq,SetEquiv,Order,Sort,Normalize}.lean, CList.lean, HFSets.lean | Claude (AI assistant) |
| 2026-04-09 | HFSets.lean (Mem, pair, Zermelo axioms) | Claude (AI assistant) |
| 2026-04-10 | CList/Filter, Operations/{Union,Intersection,Setminus,Separation,Pair,Powerset}, Axioms/{Union,Intersection,Setminus,Separation,Pair,Powerset}, Notation | Claude (AI assistant) |
| 2026-05-11 | PList/{Basic,Lemmas,Omega0} — Phase 1 Peano integration | Claude (AI assistant) |
| 2026-05-14 | Operations/{FunctionComp,Identity,Product}, Axioms/{FunctionComp,Identity,Product,Image} — function composition, identity function, cartesian product, image of a set | Claude (AI assistant) |
| 2026-05-14 | Operations/{OrderedPair,Relation,Function,Inverse,Restriction,Composition,Replacement,SymDiff,Cardinal}, Axioms/{Singleton,Subset,OrderedPair,Foundation,Decidable,Relation,Function,Bijection,Inverse,Composition,Restriction,Replacement,Succ,SymDiff,Lattice,BooleanAlgebra,BooleanRing,VonNeumann,Choice,Cardinal}, PList/Fin0, HFList, VN/{Basic,Injective,IsNat,Arithmetic} — mass projection (REVISA_Y_PROYECTA) | Claude (AI assistant) |

> To project a file: read it fully, then update sections 1–8 above following AI-GUIDE.md §4–14.
