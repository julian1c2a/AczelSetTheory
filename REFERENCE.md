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

### 4.8–4.15 HFSets and core operations

> Definitions moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#4-definitions).

---

### 4.16–4.18 PList modules

> Definitions moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#4-definitions).

---

### 4.19–4.32 Relations (functions, ordered pairs, compositions)

> Definitions moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#4-definitions).

---

### 4.33–4.39 Algebra (SymDiff, Cardinal, Boolean, Succ, VonNeumann, Choice)

> Definitions moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#4-definitions).

---

### 4.40 PList/Fin0.lean

> Definitions moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#4-definitions).

---

### 4.41 HFList.lean

> Definitions moved to [doc/REFERENCE-HFList.md](doc/REFERENCE-HFList.md#4-definitions).

---

### 4.42 VN modules

> Definitions moved to [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#4-definitions).

---

None. This project builds constructively from Lean 4 without additional axioms.

---

## 6. Main Theorems

> Only fully proven theorems appear here. No `sorry` remains.

### 6.1–6.7 CList theorems

> Theorems moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#6-theorems).

### 6.8–6.15 HFSets and core operations

> Theorems moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#6-theorems).

### 6.16–6.17 PList modules

> Theorems moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#6-theorems).

### 6.18–6.21 Relations: compositions, identity, products, images

> Theorems moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#6-theorems).

### 6.22–6.24 Algebra: SymDiff, Singleton, Subset

> Theorems moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#6-theorems).

### 6.25 Axioms/OrderedPair

> Theorems moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#6-theorems).

### 6.26–6.27 Algebra: Foundation, Decidable

> Theorems moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#6-theorems).

### 6.28–6.34 Relations: Relation, Function, Bijection, Inverse, Composition, Restriction, Replacement

> Theorems moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#6-theorems).

### 6.35–6.42 Algebra: Succ, SymDiff, Lattice, BooleanAlgebra, BooleanRing, VonNeumann, Choice, Cardinal

> Theorems moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#6-theorems).

### 6.43 PList/Fin0

> Theorems moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#6-theorems).

### 6.44 HFList

> Theorems moved to [doc/REFERENCE-HFList.md](doc/REFERENCE-HFList.md#6-theorems).

### 6.45–6.48 VN modules

> Theorems moved to [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#6-theorems).

## 7. Exports per Module

### CList modules (Basic, ExtEq, SetEquiv, Order, Sort, Normalize)

> Exports moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#7-exports-per-module).

### HFSets.lean

> Exports moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#7-exports-per-module).

### CList/Filter.lean

> Exports moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#7-exports-per-module).

### HFSets operations (Operations/Union–Powerset, Axioms/Union–Powerset, Notation.lean)

> Exports moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#7-exports-per-module).

### Relations modules (Operations and Axioms: FunctionComp, Identity, Product, Image, OrderedPair, Relation, Function, Bijection, Inverse, Composition, Restriction, Replacement)

> Exports moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#7-exports-per-module).

### Algebra modules (Operations/SymDiff, Cardinal; Axioms/Singleton, Subset, Foundation, Decidable, Succ, SymDiff, Lattice, BooleanAlgebra, BooleanRing, VonNeumann, Choice, Cardinal)

> Exports moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#7-exports-per-module).

### PList modules (PList/Basic, Lemmas, Omega0, Fin0)

> Exports moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#7-exports-per-module).

### HFList.lean

> Exports moved to [doc/REFERENCE-HFList.md](doc/REFERENCE-HFList.md#7-exports-per-module).

### VN modules (VN/Basic, Injective, IsNat, Arithmetic)

> Exports moved to [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#7-exports-per-module).

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
