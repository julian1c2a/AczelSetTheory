# Technical Reference — AczelSetTheory

**Last updated:** 2026-06-05
**Author**: Julián Calderón Almendros
**Lean version**: v4.30.0

> **Nota (2026-06-05)**: la tabla §1 lista los 107 módulos del núcleo histórico. Para el inventario completo y al día (175 ficheros `.lean` totales — 172 bajo `AczelSetTheory/` más `Main.lean`, `lakefile.lean` y la raíz `AczelSetTheory.lean`), incluidos `Algebra/{Action,CosetAction,CorrespondenceTheorem,FirstIsomorphism,SecondIsomorphism,ThirdIsomorphism,Lattice,LinearSpace,Module,Monoid,NormalSubgroup,QuotientGroup,RingHom,Sylow,Zassenhaus}`, `Combinatorics/Counting`, varios `VN/*VN`, etc.) consulta [`AUDIT-MODULE-MATRIX.md`](AUDIT-MODULE-MATRIX.md). Documentación detallada por subsistema en [`doc/REFERENCE-Algebra.md`](doc/REFERENCE-Algebra.md), [`doc/REFERENCE-GroupTheory.md`](doc/REFERENCE-GroupTheory.md), [`doc/REFERENCE-Combinatorics.md`](doc/REFERENCE-Combinatorics.md) y [`doc/REFERENCE-VN.md`](doc/REFERENCE-VN.md).

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
| -------- | ------ | --- | -------- | ------ | --- | -------- | ------ |
| ∈ | `mem` | | ∪ | `union` | | + | `add` |
| ∉ | `not_mem` | | ∩ | `inter` | | * | `mul` |
| ⊆ | `subset` | | ⋃ | `sUnion` | | - | `sub`/`neg` |
| ⊂ | `ssubset` | | ⋂ | `sInter` | | / | `div` |
| 𝒫 | `powerset` | | \ | `sdiff` | | ^ | `pow` |
| σ | `succ` | | △ | `symmDiff` | | ∣ | `dvd` |

---

## 1. Module List

| # | File | Namespace | Status | Depends on | Depended on by |
| --- | ------ | ----------- | -------- | ------------ | ---------------- |
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
| 61 | `AczelSetTheory/Axioms/Cardinal.lean` | `HFSet` | ✅ Complete | Operations/Cardinal, Operations/Powerset, Notation | Axioms/OrdinalNat |
| 62 | `AczelSetTheory/PList/Fin0.lean` | `Fin₀`, `PList` | ✅ Complete | PList/Omega0, Peano.PeanoNat.{StrictOrder,Order,Axioms} | HFList |
| 63 | `AczelSetTheory/HFList.lean` | `HFList`, `FinList` | ✅ Complete | HFSets, PList/Fin0 | — |
| 64 | `AczelSetTheory/VN/Basic.lean` | `VN` | ✅ Complete | Axioms | VN/Injective, VN/IsNat, VN/Arithmetic |
| 65 | `AczelSetTheory/VN/Injective.lean` | `VN` | ✅ Complete | VN/Basic | VN/Arithmetic, VN/FSet |
| 66 | `AczelSetTheory/VN/IsNat.lean` | `VN` | ✅ Complete | VN/Basic | VN/FSet, VN/PeanoAxioms |
| 67 | `AczelSetTheory/VN/Arithmetic.lean` | `VN` | ✅ Complete | VN/Injective, PList/Omega0 | VN/PeanoArith |
| 68 | `AczelSetTheory/VN/FSet.lean` | `VN` | ✅ Complete | VN/Injective, VN/IsNat, `Peano.PeanoNat.ListsAndSets.FSet` | — |
| 69 | `AczelSetTheory/VN/PeanoAxioms.lean` | `VN` | ✅ Complete | VN/Injective, VN/IsNat | VN/PeanoArith |
| 70 | `AczelSetTheory/VN/PeanoArith.lean` | `VN` | ✅ Complete | VN/Arithmetic, VN/PeanoAxioms | — |
| 71 | `AczelSetTheory/Axioms/Adjunction.lean` | `HFSet` | ✅ Complete | Notation | Axioms/Induction |
| 72 | `AczelSetTheory/Axioms/Induction.lean` | `HFSet` | ✅ Complete | Axioms/Adjunction, Axioms/Foundation | — |
| 73 | `AczelSetTheory/Operations/CartProd.lean` | `HFSet` | ✅ Complete | Operations/OrderedPair | Axioms/CartProd |
| 74 | `AczelSetTheory/Axioms/CartProd.lean` | `HFSet` | ✅ Complete | Operations/CartProd, Axioms/OrderedPair | — |
| 75 | `AczelSetTheory/Axioms/Ordinal.lean` | `HFSet` | ✅ Complete | Axioms/VonNeumann, Axioms/Induction | Axioms/OrdinalNat |
| 76 | `AczelSetTheory/VN/CardVN.lean` | `VN` | ✅ Complete | VN/IsNat, Axioms/Cardinal | — |
| 77 | `AczelSetTheory/Axioms/OrdinalNat.lean` | `HFSet` | ✅ Complete | Axioms/Ordinal, Axioms/Cardinal, Axioms/Separation, Axioms/Decidable, Axioms/Setminus, PList/Omega0 | — |
| 78 | `AczelSetTheory/Axioms/Fintype.lean` | top-level + `HFSet` | ✅ Complete | Axioms/OrdinalNat, PList/Lemmas | — |
| 79 | `AczelSetTheory/VN/PowVN.lean` | `VN` | ✅ Complete | VN/PeanoArith | — |
| 80 | `AczelSetTheory/VN/SubVN.lean` | `VN` | ✅ Complete | VN/PeanoArith | — |
| 81 | `AczelSetTheory/VN/DivVN.lean` | `VN` | ✅ Complete | VN/PeanoArith | — |
| 82 | `AczelSetTheory/VN/FactorialVN.lean` | `VN` | ✅ Complete | VN/PeanoArith, `Peano.PeanoNat.Combinatorics.Factorial` | — |
| 83 | `AczelSetTheory/Axioms/Rank.lean` | `HFSet` | ✅ Complete | Operations/Cardinal, Axioms/Adjunction | VN/RankVN |
| 84 | `AczelSetTheory/VN/RankVN.lean` | `VN` | ✅ Complete | VN/IsNat, Axioms/Rank | — |
| 85 | `AczelSetTheory/Operations/NPow.lean` | `HFSet` | ✅ Complete | Operations/CartProd, Notation, `Peano.PeanoNat.Combinatorics.Pow` | Axioms/NPow |
| 86 | `AczelSetTheory/Axioms/NPow.lean` | `HFSet` | ✅ Complete | Operations/NPow, Axioms/CartProd, Axioms/Singleton | — |
| 87 | `AczelSetTheory/Algebra/Group.lean` | `HFAlgebra`, `HFAlgebra.HFGroup` | ✅ Complete | AczelSetTheory.HFSets | Algebra/Subgroup, Algebra/GroupHom, Algebra/Ring, Algebra/CosetCount |
| 88 | `AczelSetTheory/Algebra/Subgroup.lean` | `HFAlgebra`, `HFAlgebra.HFSubgroup` | ✅ Complete | Algebra/Group, Axioms/Separation, Axioms/Decidable, Axioms/OrdinalNat, Axioms/Intersection | Algebra/CosetCount |
| 89 | `AczelSetTheory/Algebra/GroupHom.lean` | `HFAlgebra`, `HFAlgebra.HFGroupHom` | ✅ Complete | Algebra/Subgroup | — |
| 90 | `AczelSetTheory/Algebra/Ring.lean` | `HFAlgebra`, `HFAlgebra.HFRing` | ✅ Complete | Algebra/Group | — |
| 91 | `AczelSetTheory/Algebra/CosetCount.lean` | `HFAlgebra.HFSubgroup`, `HFSet` | ✅ Complete | Algebra/Subgroup, Axioms/OrdinalNat, Axioms/Union, Axioms/Powerset, Peano.PeanoNat.Arith | — |
| 92 | `AczelSetTheory/Algebra/Monoid.lean` | `HFAlgebra`, `HFAlgebra.HFMonoid`, `HFAlgebra.HFMonoidHom`, `HFAlgebra.HFSubmonoid` | ✅ Complete | AczelSetTheory.HFSets, Axioms/Intersection | — |
| 93 | `AczelSetTheory/Algebra/RingHom.lean` | `HFAlgebra`, `HFAlgebra.HFRingHom`, `HFAlgebra.HFSubring` | ✅ Complete | Algebra/Ring, Axioms/Intersection | Algebra/Field |
| 94 | `AczelSetTheory/Algebra/Field.lean` | `HFAlgebra`, `HFAlgebra.HFField`, `HFAlgebra.HFFieldHom`, `HFAlgebra.HFSubfield` | ✅ Complete | Algebra/RingHom, Axioms/Intersection | Algebra/LinearSpace |
| 95 | `AczelSetTheory/Algebra/Module.lean` | `HFAlgebra`, `HFAlgebra.HFModule`, `HFAlgebra.HFModuleHom`, `HFAlgebra.HFSubmodule` | ✅ Complete | Algebra/Ring, Axioms/Intersection | — |
| 96 | `AczelSetTheory/Algebra/LinearSpace.lean` | `HFAlgebra`, `HFAlgebra.HFLinearSpace`, `HFAlgebra.HFLinearMap`, `HFAlgebra.HFSubspace` | ✅ Complete | Algebra/Field, Axioms/Intersection | — |
| 97 | `AczelSetTheory/Integers/Basic.lean` | `ℤ₀` | ✅ Complete | PList/Omega0, `Peano.PeanoNat.{Sub,Mul,Decidable}` | Integers/Order, Integers/MobiusLiouville |
| 98 | `AczelSetTheory/Integers/Order.lean` | `ℤ₀` | ✅ Complete | Integers/Basic, `Peano.PeanoNat.Decidable` | Integers/Functions |
| 99 | `AczelSetTheory/Integers/Functions.lean` | `ℤ₀` | ✅ Complete | Integers/Order | Integers/Arithmetic, Integers/Bijection |
| 100 | `AczelSetTheory/Integers/Arithmetic.lean` | `ℤ₀` | ✅ Complete | Integers/Functions, `Peano.PeanoNat.{Div,Arith}` | Integers.lean |
| 101 | `AczelSetTheory/Integers/Bijection.lean` | `ℤ₀` | ✅ Complete | Integers/Functions, `Peano.PeanoNat.Pairing` | Integers.lean |
| 102 | `AczelSetTheory/Integers/PadicVal.lean` | `ℤ₀` | ✅ Complete | PList/Omega0, `Peano.PeanoNat.{Arith,Primes,WellFounded,Div}` | Integers/MobiusLiouville |
| 103 | `AczelSetTheory/Integers/MobiusLiouville.lean` | `ℤ₀` | ✅ Complete | Integers/Basic, Integers/PadicVal | Integers.lean |
| 104 | `AczelSetTheory/Topology/Basic.lean` | `HFTopology` | ✅ Complete | HFSets, Axioms/{Union,Intersection,Setminus,Subset,Singleton} | Topology/Interior, Topology/Neighborhoods, Topology/Subspace |
| 105 | `AczelSetTheory/Topology/Interior.lean` | `HFTopology` | ⚠️ sorry | Topology/Basic, Axioms/{Separation,Intersection,Setminus} | — |
| 106 | `AczelSetTheory/Topology/Neighborhoods.lean` | `HFTopology` | ⚠️ sorry | Topology/Basic, Axioms/{Separation,Powerset} | — |
| 107 | `AczelSetTheory/Topology/Subspace.lean` | `HFTopology` | ⚠️ sorry | Topology/Basic, Axioms/{Separation,Powerset} | — |
| — | `AczelSetTheory/Topology.lean` | — | ✅ Barrel | Topology/{Basic,Interior,Neighborhoods,Subspace} | AczelSetTheory.lean |
| — | `AczelSetTheory/VN.lean` | — | ✅ Complete | VN/{Basic,Injective,IsNat,Arithmetic,FSet,PeanoAxioms,PeanoArith,PowVN,SubVN,DivVN,FactorialVN,CardVN,RankVN} | AczelSetTheory.lean |
| — | `AczelSetTheory/PList.lean` | — | ✅ Complete | PList/{Basic,Lemmas,Omega0} | AczelSetTheory.lean |
| — | `AczelSetTheory/Integers.lean` | — | ✅ Complete | Integers/{Basic,Order,Functions,Arithmetic,Bijection,PadicVal,MobiusLiouville} | AczelSetTheory.lean |
| — | `AczelSetTheory.lean` | — | ✅ Complete | PList, CList, HFSets, Operations/*, Axioms/*, Integers, Notation | Main |
| — | `Main.lean` | — | ✅ Complete | CList.Basic | — |

---

## 2. Module Dependencies

```text
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

PList/Omega0 + Peano.PeanoNat.{Sub,Mul,Decidable}
  └─ Integers/Basic.lean
       └─ Integers/Order.lean
            └─ Integers/Functions.lean
                 ├─ Integers/Arithmetic.lean ─────────┐
                 └─ Integers/Bijection.lean ───────────┤
                                                       └─ Integers.lean
PList/Omega0 + Peano.PeanoNat.{Arith,Primes,WellFounded,Div}
  └─ Integers/PadicVal.lean  ✅ Complete
       └─ Integers/MobiusLiouville.lean ─────────────── Integers.lean
            (also imports Integers/Basic)
```

---

## 3. Namespaces

| Namespace | Modules | Description |
| ----------- | --------- | ------------- |
| `CList` | Basic, ExtEq, Filter, SetEquiv, Order, Sort, Normalize, Operations/Union (partial), Operations/Powerset (partial) | All CList definitions and theorems |
| `HFSet` | HFSets, Operations/*, Axioms/*, Notation | Quotient type and its API |
| `PList` | PList/Basic, PList/Lemmas | Polymorphic list type with ℕ₀ indexing; bridge to `List` |
| `PList.Omega0` | PList/Omega0 | Bridge lemmas `ψ_*` used internally by the `omega₀` tactic |
| `ℤ₀` | Integers/{Basic,Order,Functions,Arithmetic,Bijection,PadicVal,MobiusLiouville} | Integers as quotient `Quotient intSetoid`; ring operations, p-adic val, μ, λ |
| (top-level) | Basic | `CList` inductive type defined at top level, operations inside `namespace CList` |

---

## 4. Definitions

### 4.1–4.7 CList modules

> Definitions moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#4-definitions).

---

### 4.8–4.16 HFSets and core operations

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

### 4.43 Axioms/Adjunction.lean + Axioms/Induction.lean (Phase 7a, 7b)

> Definitions moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#4-definitions).

---

### 4.44 Operations/CartProd.lean + Axioms/CartProd.lean (Phase 7c)

> Definitions moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#4-definitions).

---

### 4.45 Axioms/Ordinal.lean + VN/CardVN.lean (Phase 7d)

> Definitions moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#4-definitions) and [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#4-definitions).

---

### 4.46 Axioms/OrdinalNat.lean (Phase 7e)

> Definitions moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#4-definitions).

---

### 4.47 Axioms/Fintype.lean (Phase F1+F2)

> Definitions moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#4-definitions).

---

### 4.48 VN/PowVN.lean + VN/SubVN.lean + VN/DivVN.lean + VN/FactorialVN.lean (A1–A3, C1)

> Definitions moved to [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#4-definitions).

---

### 4.49 Axioms/Rank.lean + VN/RankVN.lean (B1)

> Definitions moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#4-definitions) and [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#4-definitions).

---

### 4.50 Operations/NPow.lean + Axioms/NPow.lean (Phase 7e + 7g)

> Definitions moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#4-definitions).

---

### 4.51 Integers modules (#92–#98)

> Integers definitions are documented inline in `REFERENCE.md` §1 (module list) and in the source files.
> A dedicated `doc/REFERENCE-Integers.md` is planned once the full API stabilises.

Key symbols:

| Symbol | Kind | File | Notes |
| -------- | ------ | ------ | ------- |
| `ℤ₀` | type alias | Integers/Basic | `Quotient intSetoid`; `CommRing ℤ₀` instance |
| `negOne` | def | Integers/Basic | `mk (𝟘, 𝟙)` = −1 |
| `ofNat` | def | Integers/Basic | embedding ℕ₀ → ℤ₀ |
| `negOnePow` | def | Integers/MobiusLiouville | (−1)^k ∈ ℤ₀, computable |
| `mobius` | def | Integers/MobiusLiouville | Möbius function μ : ℕ₀ → ℤ₀ |
| `liouville` | def | Integers/MobiusLiouville | Liouville function λ : ℕ₀ → ℤ₀ |
| `squarefree` | def | Integers/PadicVal | predicate on ℕ₀ |
| `padicVal` | def | Integers/PadicVal | p-adic valuation ℕ₀ |
| `Omega_prime` | def | Integers/PadicVal | total prime-power exponent Ω : ℕ₀ → ℕ₀ |

---

---

## 6. Main Theorems

> Only fully proven theorems appear here. No `sorry` remains.

### 6.1–6.7 CList theorems

> Theorems moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#6-theorems).

### 6.8–6.16 HFSets and core operations

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

### 6.35–6.42, 6.56, 6.58 Algebra: Succ, SymDiff, Lattice, BooleanAlgebra, BooleanRing, VonNeumann, Choice, Cardinal, Ordinal, OrdinalNat

> Theorems moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#6-theorems).

### 6.43 PList/Fin0

> Theorems moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#6-theorems).

### 6.44 HFList

> Theorems moved to [doc/REFERENCE-HFList.md](doc/REFERENCE-HFList.md#6-theorems).

### 6.45–6.51, 6.57, 6.59–6.63 VN modules (incl. CardVN, PowVN, SubVN, DivVN, FactorialVN, RankVN)

> Theorems moved to [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#6-theorems).

### 6.52–6.53 Axioms/Adjunction + Axioms/Induction (Phase 7a, 7b)

> Theorems moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#6-theorems).

### 6.54–6.55 Operations/CartProd + Axioms/CartProd (Phase 7c)

> Theorems moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#6-theorems).

### 6.64–6.65 Operations/NPow + Axioms/NPow (Phase 7e + 7g)

> Theorems moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#6-theorems).

### 6.66 Integers modules (#92–#98)

Key proven theorems (non-sorry):

| Theorem | Statement |
| --------- | ---------- |
| `negOnePow_zero` | `negOnePow 𝟘 = 1` |
| `negOnePow_succ` | `negOnePow (σ k) = -(negOnePow k)` |
| `negOnePow_one` | `negOnePow 𝟙 = negOne` |
| `negOnePow_two` | `negOnePow 𝟚 = 1` |
| `negOnePow_add` | `negOnePow (a + b) = negOnePow a * negOnePow b` |
| `negOnePow_mul_self` | `negOnePow k * negOnePow k = 1` |
| `mobius_one` | `mobius 𝟙 = 1` |
| `mobius_prime` | `Prime p → mobius p = negOne` |
| `mobius_prime_sq` | `Prime p → mobius (p * p) = 0` |
| `liouville_one` | `liouville 𝟙 = 1` |
| `liouville_prime` | `Prime p → liouville p = negOne` |
| `liouville_sq` | `liouville n * liouville n = 1` |
| `liouville_ne_zero` | `liouville n ≠ 0` |
| `mobius_eq_liouville_of_squarefree` | `squarefree n → mobius n = liouville n` |
| `mobius_sq` | `mobius n * mobius n = if squarefree n then 1 else 0` |
| `liouville_mul` ⚠ | `m ≠ 𝟘 → n ≠ 𝟘 → liouville (m * n) = liouville m * liouville n` (via sorry) |
| `liouville_prime_pow` ⚠ | `Prime p → liouville (p ^ k) = negOnePow k` (via sorry) |

## 7. Exports per Module

### CList modules (Basic, ExtEq, SetEquiv, Order, Sort, Normalize)

> Exports moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#7-exports-per-module).

### HFSets.lean

> Exports moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#7-exports-per-module).

### CList/Filter.lean

> Exports moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#7-exports-per-module).

### HFSets operations (Operations/Union–Powerset, Axioms/Union–Powerset, Notation.lean, Axioms/Fintype.lean)

> Exports moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#7-exports-per-module).

### Relations modules (Operations and Axioms: FunctionComp, Identity, Product, Image, OrderedPair, Relation, Function, Bijection, Inverse, Composition, Restriction, Replacement)

> Exports moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#7-exports-per-module).

### Algebra modules (Operations/SymDiff, Cardinal; Axioms/Singleton, Subset, Foundation, Decidable, Succ, SymDiff, Lattice, BooleanAlgebra, BooleanRing, VonNeumann, Choice, Cardinal)

> Exports moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#7-exports-per-module).

### PList modules (PList/Basic, Lemmas, Omega0, Fin0)

> Exports moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#7-exports-per-module).

### HFList.lean

> Exports moved to [doc/REFERENCE-HFList.md](doc/REFERENCE-HFList.md#7-exports-per-module).

### VN modules (VN/Basic, Injective, IsNat, Arithmetic, FSet, PeanoAxioms, PeanoArith)

> Exports moved to [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#7-exports-per-module).

### Axioms/Adjunction.lean + Axioms/Induction.lean (Phase 7a, 7b)

> Exports moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#7-exports-per-module).

### Operations/CartProd.lean + Axioms/CartProd.lean (Phase 7c)

> Exports moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#7-exports-per-module).

### Axioms/Ordinal.lean + VN/CardVN.lean (Phase 7d)

> Exports moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#7-exports-per-module) and [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#7-exports-per-module).

### VN/PowVN.lean + VN/SubVN.lean + VN/DivVN.lean + VN/FactorialVN.lean + VN/RankVN.lean (A1–A3, C1, B1-VN)

> Exports moved to [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#7-exports-per-module).

### Axioms/Rank.lean (B1-Axioms)

> Exports moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#7-exports-per-module).

### Axioms/OrdinalNat.lean (Phase 7e)

> Exports moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#7-exports-per-module).

### Operations/NPow.lean + Axioms/NPow.lean (Phase 7e + 7g)

> Exports moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#7-exports-per-module).

### Integers modules (#92–#98)

> Full export lists are in each source file and in §6.66 above. A dedicated `doc/REFERENCE-Integers.md` is planned.

**`Integers/MobiusLiouville.lean` (public API):**
`negOnePow`, `negOnePow_zero`, `negOnePow_succ`, `negOnePow_one`, `negOnePow_two`, `negOnePow_add`, `negOnePow_mul_self`, `mobius`, `mobius_one`, `mobius_prime`, `mobius_prime_sq`, `liouville`, `liouville_one`, `liouville_prime`, `liouville_sq`, `liouville_ne_zero`, `mobius_eq_liouville_of_squarefree`, `mobius_sq`, `liouville_mul`, `liouville_prime_pow`

**`Integers/PadicVal.lean` (public API):**
`padicVal`, `padicVal_zero_right`, `padicVal_of_not_cond`, `padicVal_succ_dvd`, `padicVal_prime_self`, `padicVal_prime_of_ndvd`, `squarefree`, `squarefree_one`, `squarefree_prime`, `not_squarefree_prime_sq`, `Omega_prime`, `Omega_prime_zero`, `Omega_prime_one`, `Omega_prime_prime`, `Omega_prime_mul`, `Omega_prime_mul_prime`

---

## 8. Notations

| Symbol | Lean definition | Module | Notes |
| -------- | ---------------- | -------- | ------- |
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
| `×ₕ` | `infixl:70 " ×ₕ " => HFSet.cartProd` | Operations/CartProd | Computable Cartesian product (CList flatMap/map) |

---

## Projection Log

| Date | Files projected | Projector |
| ------ | ---------------- | ----------- |
| 2026-04-04 | (stub created) | Julián Calderón Almendros |
| 2026-04-08 | CList/{Basic,ExtEq,SetEquiv,Order,Sort,Normalize}.lean, CList.lean, HFSets.lean | Claude (AI assistant) |
| 2026-04-09 | HFSets.lean (Mem, pair, Zermelo axioms) | Claude (AI assistant) |
| 2026-04-10 | CList/Filter, Operations/{Union,Intersection,Setminus,Separation,Pair,Powerset}, Axioms/{Union,Intersection,Setminus,Separation,Pair,Powerset}, Notation | Claude (AI assistant) |
| 2026-05-11 | PList/{Basic,Lemmas,Omega0} — Phase 1 Peano integration | Claude (AI assistant) |
| 2026-05-14 | Operations/{FunctionComp,Identity,Product}, Axioms/{FunctionComp,Identity,Product,Image} — function composition, identity function, cartesian product, image of a set | Claude (AI assistant) |
| 2026-05-14 | Operations/{OrderedPair,Relation,Function,Inverse,Restriction,Composition,Replacement,SymDiff,Cardinal}, Axioms/{Singleton,Subset,OrderedPair,Foundation,Decidable,Relation,Function,Bijection,Inverse,Composition,Restriction,Replacement,Succ,SymDiff,Lattice,BooleanAlgebra,BooleanRing,VonNeumann,Choice,Cardinal}, PList/Fin0, HFList, VN/{Basic,Injective,IsNat,Arithmetic} — mass projection (REVISA_Y_PROYECTA) | Claude (AI assistant) |
| 2026-05-15 | VN/{FSet,PeanoAxioms,PeanoArith} — Fases 4+5: FSet embedding, Peano axioms bridge, arithmetic transport | Claude (AI assistant) |
| 2026-05-16 | Axioms/Adjunction, Axioms/Induction (Phase 7a/7b: adjunction axiom, ε-induction), Operations/CartProd, Axioms/CartProd (Phase 7c: computable Cartesian product ×ₕ) | Claude (AI assistant) |
| 2026-05-16 | Axioms/VonNeumann — re-proyección: `isTransitive`, `isNat`, 9 teoremas (`isTransitive_empty`, `isTransitive_succ`, `isNat_zero`, `isNat_succ`, `isNat_zero_or_succ`, `isNat_isTransitive`, `isNat_mem_isNat`, `isNat_pred`, `isNat_induction`) | Claude (AI assistant) |
| 2026-05-16 | Axioms/Ordinal (nuevos: `isOrdinal`, 4 teoremas), VN/CardVN (nuevo: `card_vN`), Axioms/Cardinal (`card_eq_zero_iff`) | Claude (AI assistant) |
| 2026-05-16 | Axioms/Cardinal (`card_succ`), Axioms/OrdinalNat (nuevo módulo: `instDecidableEqHFSet`, `card_le_of_subset`, `isOrdinal_isNat`, `isOrdinal_iff_isNat`) — Phase 7e | Claude (AI assistant) |
| 2026-05-16 | Operations/NPow (#85): `nPow : HFSet → ℕ₀ → HFSet`, `nPow_zero`, `nPow_succ` — potencia cartesiana n-aria (Phase 7e) | Claude (AI assistant) |
| 2026-05-16 | Axioms/Fintype (nuevo módulo #78): `Finset`, `Fintype`, `HFSet.toList`, `HFSet.toFinset`, `HFSet.membership_fintype`, teoremas `mem_toList`, `nodup_toList`, `mem_toFinset` — Phase F1+F2 | Claude (AI assistant) |
| 2026-05-17 | Axioms/NPow (#86): `mem_nPow_zero`, `mem_nPow_succ` — caracterización axiomática de membresía en `nPow` (Phase 7g) | Claude (AI assistant) |
| 2026-05-17 | VN/PowVN (#79): `powVN`, `vN_pow` y 13 teoremas de potenciación; VN/SubVN (#80): 12 teoremas de sustracción acotada; VN/DivVN (#81): 6 teoremas de división euclidiana; VN/FactorialVN (#82): `factVN`, `vN_factorial_succ` y 8 teoremas de factorial — fases A1–A3, C1 | Claude (AI assistant) |
| 2026-05-17 | Axioms/Rank (#83): `HFSet.rank`, `rank_empty`, `rank_insert` (rango de Von Neumann); VN/RankVN (#84): `VN.rank_vN` — fase B1 | Claude (AI assistant) |
| 2026-05-21 | `Integers/PadicVal.lean` (#97), `Integers/MobiusLiouville.lean` (#98): `Omega_prime_mul` y `Omega_prime_mul_prime` probados sin sorry; `liouville_mul`, `liouville_prime_pow` ahora sorry-free; estado de módulos #97 y #98 actualizado a `✅ Complete`; API de PadicVal ampliada con todos los lemas (`padicVal_zero_right`, `padicVal_of_not_cond`, `padicVal_succ_dvd`, `padicVal_prime_self`, `padicVal_prime_of_ndvd`, `squarefree_one`, `squarefree_prime`, `not_squarefree_prime_sq`, `Omega_prime_zero`, `Omega_prime_one`, `Omega_prime_prime`); tabla §6.66 ampliada con 13 nuevos teoremas de PadicVal | Claude (AI assistant) |
| 2026-05-22 | Integers/{Basic,Order,Functions,Arithmetic,Bijection,PadicVal,MobiusLiouville}.lean (#92–#98): entradas de módulos, cadena de dependencias, namespace `ℤ₀`, definiciones clave (negOnePow, mobius, liouville, Omega_prime), 17 teoremas incluyendo `liouville_prime_pow` — actualización_documentación completa de Integers/ | Claude (AI assistant) |
| 2026-06-02 | Algebra/Sylow.lean: migración constructiva de `order` y `periodOf` (búsqueda acotada), limpieza de legado WOP (`order_wop`, `periodOf_wop`); Sprint B inicial en Algebra/{QuotientGroup,FirstIsomorphism,SecondIsomorphism,ThirdIsomorphism,CosetAction,CorrespondenceTheorem} reemplazando wrappers `noncomputable def` por `abbrev/def`; actualización de `doc/REFERENCE-Algebra.md` y matriz `AUDIT-MODULE-MATRIX.md` | GitHub Copilot |
| 2026-06-02 | Sprint B.2 en `Algebra/QuotientGroup.lean`: `cosetRep` migrado a versión constructiva (búsqueda en `grp.G.toList`) con nuevos auxiliares `findRepList`, `findRepList_sound`, `findRepList_complete`; ajuste de `cosetRep_mem_G` y `cosetRep_rightCoset_eq`; actualización de docs y matriz con **0 `noncomputable def`** global | GitHub Copilot |
| 2026-06-02 | Sprint C1/C2: cierre de marcadores `TODO/PEND/FIXME` en `Topology/{Basic,Interior,Neighborhoods,Separation,Subspace}.lean`, `Algebra/Action.lean` y stubs VN (`ActionVN`, `CorrespondenceTheoremVN`, `PermVN`, `SymGroupVN`); regeneración de matriz con **0 `TODO/PEND/FIXME`** y foco restante en `placeholder/stub` | GitHub Copilot |
| 2026-06-02 | Sprint D1: reducción de `placeholder/stub` en `VN/{PermVN,OrbitVN,CountingVN,SignVN}.lean`; matriz regenerada tras cada bloque, quedando **7** módulos con `placeholder/stub` | GitHub Copilot |
| 2026-06-02 | Sprint D2: cierre del residual `placeholder/stub` en `VN/{ActionVN,CorrespondenceTheoremVN,FirstIsomorphismVN,SecondIsomorphismVN,ThirdIsomorphismVN,QuotientGroupVN,NormalSubgroupVN}.lean`; matriz regenerada tras cada cierre individual y estado final en **0** módulos con `placeholder/stub` | GitHub Copilot |
| 2026-06-03 | **Algebra/Sylow.lean §33–§40 + §37-II**: Primer Teorema de Sylow completo (`sylow_first`, `exists_isSylowSubgroup_of_isSylowExponent`, `exists_isPSubgroup_of_isSylowExponent`, `not_dvd_index_of_isSylowSubgroup`, `not_dvd_card_cosets_of_isSylowSubgroup`); Segundo Teorema de Sylow estructura completa (`sylowConjugate`, `SylowConjugateTotal_of_isSylowExponent`, `sylowSecondConjugacyTarget_of_isSylowExponent`) con 1 sorry documentado (punto fijo del p-grupo); proyectado en `doc/REFERENCE-Algebra.md` | GitHub Copilot |
| 2026-06-05 | **M7 Algebra/Zassenhaus.lean** (684 LOC): Lema de la Mariposa completo — `prodSubgroup`, `mem_prodSubgroup_iff`, `inter_N_K_normal_in_inter_H_K`, `inter_H_M_normal_in_inter_H_K`, `prodNKHM`, `prodNKHM_normal`, `prodN_HK`, `prodN_HM`, `prodN_HM_le_prodN_HK`, `prodN_HM_normal_in_prodN_HK`, `zassenhaus_bijection`; cierre del `sorry` residual de Sylow II §37; build limpio (0 errores / 0 warnings / 0 sorry / 0 noncomputable); upgrade a Lean v4.30.0; **FASE A (M1–M7) cerrada**; proyectado en `doc/REFERENCE-Algebra.md` §7 | GitHub Copilot |

> To project a file: read it fully, then update sections 1–8 above following AI-GUIDE.md §4–14.
