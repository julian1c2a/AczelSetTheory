# Paridad de Resultados: Peano → AczelSetTheory

**Fecha de referencia:** 2026-06-04
**Peano (feature-freeze desde 2026-05-10):** `E:\Dropbox\GitHub\lean4\Peano\`
**AczelSetTheory (activo):** `E:\Dropbox\GitHub\lean4\AczelSetTheory\`
**Estado build ambos proyectos:** AczelSetTheory: ✅ **0 sorry** (M6 cerrado 2026-06-04). Peano: ✅ 0 sorry.

---

## Leyenda

| Símbolo | Significado |
|---------|-------------|
| ✅ | Portado completamente (módulo VN o equivalente) |
| ⚠️ | Portado parcialmente o con enfoque distinto |
| ❌ | No portado — falta en AczelSetTheory |
| 🆕 | Nuevo en AczelSetTheory (no existe en Peano) |

---

## 1. Aritmética base y orden (`PeanoNat/`)

| Módulo Peano | Estado | Equivalente en AczelSetTheory | Notas |
|---|---|---|---|
| `PeanoNat/Axioms.lean` | ✅ | `VN/PeanoAxioms.lean` | Los 8 axiomas de Peano verificados sobre `vN : ℕ₀ → HFSet` |
| `PeanoNat/Add.lean` | ✅ | `VN/Arithmetic.lean` | `add_vN`, propiedades de `+` sobre VN |
| `PeanoNat/Mul.lean` | ✅ | `VN/Arithmetic.lean` | `mul_vN`, propiedades de `*` sobre VN |
| `PeanoNat/Sub.lean` | ✅ | `VN/SubVN.lean` | Resta truncada sobre naturales VN |
| `PeanoNat/Arith.lean` | ✅ | `VN/Arithmetic.lean` + `VN/PeanoArith.lean` | Aritmética combinada; `PeanoArith` contiene propiedades de alto nivel |
| `PeanoNat/Order.lean` | ✅ | `VN/Basic.lean` | Orden ≤ sobre VN; `vN_le_iff`, etc. |
| `PeanoNat/StrictOrder.lean` | ✅ | `VN/Basic.lean` | Orden < sobre VN |
| `PeanoNat/WellFounded.lean` | ⚠️ | `VN/Basic.lean` (parcial) | `well_founded_lt` se transfiere desde `ℕ₀` vía `Λ/Ψ`; AczelSetTheory usa recurso del kernel directamente |
| `PeanoNat/Decidable.lean` | ✅ | `Axioms/Decidable.lean` | `DecidableEq HFSet`; membresía decidible |
| `PeanoNat/Isomorph.lean` | ✅ | `VN/Injective.lean` | Embedding `ℕ₀ ↪ HFSet` como VN; injectividad y propiedades |
| `PeanoNat/Div.lean` | ✅ | `VN/DivVN.lean` | División euclídea sobre VN; `div_vN`, `mod_vN` |
| `PeanoNat/Sqrt.lean` | ✅ | `VN/SqrtVN.lean` | Raíz cuadrada entera sobre VN |
| `PeanoNat/Log.lean` | ✅ | `VN/LogVN.lean` | Logaritmo discreto en base 2 sobre VN |
| `PeanoNat/Lattice.lean` | ✅ | `VN/LatticeVN.lean` | `minVN`, `maxVN` sobre VN; propiedades de idempotencia, absorción, comutatividad, asociatividad y cotas de orden (19 teoremas). |
| `PeanoNat/Digits.lean` | ✅ | `VN/DigitsVN.lean` | Representación en base `b` sobre VN |
| `PeanoNat/Tuple.lean` | ✅ | `VN/PairingVN.lean` + `VN/CantorPairingVN.lean` | Pares y tuplas sobre VN |
| `PeanoNat/Pairing.lean` | ✅ | `VN/PairingVN.lean` | Función de emparejamiento de Cantor sobre VN |
| `PeanoNat/Primes.lean` | ✅ | `VN/PrimesVN.lean` + `VN/PrimeVN.lean` | `isPrime`, `Primes`, TFA sobre VN |
| `PeanoNat/NumberSets.lean` | ✅ | `Integers/` (módulo completo) | Enteros como pares de VN; ver §6 |

---

## 2. Combinatoria y álgebra de permutaciones (`PeanoNat/Combinatorics/`)

| Módulo Peano | Estado | Equivalente en AczelSetTheory | Notas |
|---|---|---|---|
| `Combinatorics/Factorial.lean` | ✅ | `VN/FactorialVN.lean` | `factorial_vN`, propiedades básicas |
| `Combinatorics/Fibonacci.lean` | ✅ | `VN/FibVN.lean` | `fib_vN`, propiedades de Fibonacci sobre VN |
| `Combinatorics/Binom.lean` | ✅ | `VN/BinomVN.lean` | Coeficientes binomiales `C(n,k)` sobre VN |
| `Combinatorics/NewtonBinom.lean` | ✅ | `VN/NewtonBinomVN.lean` | Teorema del binomio de Newton sobre VN |
| `Combinatorics/Pow.lean` | ✅ | `VN/PowVN.lean` | Potenciación `vN n ^ vN k` |
| `Combinatorics/Summation.lean` | ✅ | `VN/SummationVN.lean` | Sumas sobre rangos VN |
| `Combinatorics/Product.lean` | ✅ | `VN/ProductVN.lean` | Productos sobre rangos VN |
| `Combinatorics/Counting.lean` | ✅ | `VN/CountingVN.lean` | Equivalente documental: Peano `Counting` quedó como módulo vacío (headers §1/§2/§3); AczelSetTheory conserva la correspondencia estructural para paridad formal. |
| `Combinatorics/Perm.lean` | ✅ | `VN/SymGroupVN.lean` + `VN/PermVN.lean` | `SymGroupVN` cubre §1-§2 de Peano (FunPerm, Sym). §3 (ciclos), §4 (signatura), §5 aún no están materializadas en Peano. `PermVN.lean` registra la correspondencia. |
| `Combinatorics/Orbit.lean` | ✅ | `VN/OrbitVN.lean` | Equivalente documental: Peano `Orbit` quedó como módulo vacío (headers §1/§2/§3); AczelSetTheory conserva la correspondencia. El contenido matemático operativo de órbitas vive en `Algebra/Action.lean` (`HFGroupAction.orb`, `orbits_partition`). |
| `Combinatorics/Sign.lean` | ✅ | `VN/SignVN.lean` | Equivalente documental: Peano `Sign` quedó como módulo vacío (headers §1/§2/§3); AczelSetTheory conserva la correspondencia estructural para paridad formal. |
| `Combinatorics/Group.lean` | ✅ | `Algebra/Group.lean` + `VN/SymGroupVN.lean` | AczelSetTheory tiene `HFGroup` abstracto y `SymVN` concreto: grupo simétrico sobre segmentos VN `vnSeg n`; `SymVN.id`, `SymVN.comp`, `vnSeg_card`, `mem_vnSeg_iff`. |

---

## 3. Teoría de grupos sobre permutaciones (`PeanoNat/Combinatorics/GroupTheory/`)

| Módulo Peano | Estado | Equivalente en AczelSetTheory | Notas |
|---|---|---|---|
| `GroupTheory/Action.lean` | ✅ | `Algebra/Action.lean` + `VN/ActionVN.lean` | `HFGroupAction` abstracta sobre `HFGroup`: `orb`, `stab` (como `HFSubgroup`), `mem_orb_iff`, `mem_stab_iff`, `orb_self`, `orb_eq_of_mem`, `orbits_partition`, `conjugAction` (acción por conjugación), `mem_center_iff_conjug_fixed` (Z(G) = puntos fijos). Alcance no materializado en este módulo: `orbit_stabilizer` (vía Lagrange) y `class_equation` (corolario). |
| `GroupTheory/NormalSubgroup.lean` | ✅ | `Algebra/NormalSubgroup.lean` + `VN/NormalSubgroupVN.lean` | Aczel tiene subgrupos normales *abstractos* en `HFAlgebra` (centralizer, center, normalizer, criterios `N_G(H)=G` y `gH=Hg`, `ker_isNormal`). `VN/NormalSubgroupVN.lean` registra la tabla de correspondencia con Peano. La versión abstracta es más general que la concreta `FinGroup ℕ₀` de Peano. |
| `GroupTheory/QuotientGroup.lean` | ✅ | `Algebra/QuotientGroup.lean` + `VN/QuotientGroupVN.lean` | Aczel tiene grupo cociente `G/H` *abstracto* sobre `HFGroup`: `quotientGroup grp sub hn` (portador = `sub.cosets`, op vía `Classical.choose` representante, bien-definida bajo normalidad), `quotientHom` canónico `π : G → G/H`, `ker_quotientHom_eq : ker π = H`. `VN/QuotientGroupVN.lean` es stub-doc con tabla de correspondencia. |
| `GroupTheory/FirstIsomorphism.lean` | ✅ | `Algebra/FirstIsomorphism.lean` + `VN/FirstIsomorphismVN.lean` | Aczel tiene 1er TI *abstracto* sobre `HFGroup`: `HFGroupHom.firstIsoMap : G/ker φ → im φ` (`firstIsoFun` vía representante, bien-definida) y `firstIsoMap_bijective` (inyectiva + sobreyectiva). Incluye `Injective/Surjective/Bijective`, `quotientHom_surjective`, `imageInclusion`. `VN/FirstIsomorphismVN.lean` es stub-doc. |
| `GroupTheory/SecondIsomorphism.lean` | ✅ | `Algebra/SecondIsomorphism.lean` + `VN/SecondIsomorphismVN.lean` | Aczel tiene 2º TI *abstracto* sobre `HFGroup`: `HFSubgroup.secondIsoMap : H/(H∩N) → HN/N` y `secondIsoMap_bijective`. Incluye `subgroupHN` (con normalidad), `N_in_subgroupHN`/`N_normal_in_subgroupHN`, `interHN_as_subgroup_H`/`interHN_as_subgroup_H_isNormal`. `VN/SecondIsomorphismVN.lean` es stub-doc. |
| `GroupTheory/ThirdIsomorphism.lean` | ✅ | `Algebra/ThirdIsomorphism.lean` + `VN/ThirdIsomorphismVN.lean` | Aczel tiene 3er TI *abstracto* sobre `HFGroup`: `HFSubgroup.KmodN_subgroup` (K/N ≤ G/N), `KmodN_normal`, `HFSubgroup.thirdIsoMap : G/N → G/K` (vía representante de N-coset), `thirdIsoMap_welldefined`, `thirdIsoMap_surjective` y `thirdIsoMap_ker_eq` (ker φ = K/N). `VN/ThirdIsomorphismVN.lean` es stub-doc. |
| `GroupTheory/CorrespondenceTheorem.lean` | ✅ | `Algebra/CorrespondenceTheorem.lean` + `VN/CorrespondenceTheoremVN.lean` | Aczel tiene el 4º TI (Correspondencia) *abstracto* sobre `HFGroup`: `HFSubgroup.preimageSubgroup sub_N hn_N Q` (ψ(Q) = π⁻¹(Q)), `mem_preimageSubgroup_iff`, `N_le_preimageSubgroup` (N ⊆ ψ(Q)), `imageSubgroup_preimage` (φ(ψ(Q)) = Q como HFSet), `preimageSubgroup_image` (ψ(φ(K)) = K como HFSet cuando N ⊆ K). El rol de `imageSubgroup` lo cumple `KmodN_subgroup` de `ThirdIsomorphism.lean`. `VN/CorrespondenceTheoremVN.lean` es stub-doc. Alcance no materializado aquí: `preimage_subgroup_card` (requiere Lagrange sobre HFSubgroup). |
| `GroupTheory/Zassenhaus.lean` | ❌ | — | Lema de Zassenhaus. **Pendiente.** |
| `GroupTheory/Sylow/CosetAction.lean` | ✅ | `Algebra/Sylow.lean` (§9–§18) | McKay carrier `mckayCarrier grp p` (p-tuplas con producto = e), shift cíclico `mckayShift`, `mckayFixedPoints`. D.4.A `shiftIter`, D.4.B `shiftIter_add`/`shiftIter_period`, D.4.C `orbitOf`/`card_orbitOf_le`/`orbitOf_eq_or_disjoint`. Completo. |
| `GroupTheory/Sylow/Cosets.lean` | ✅ | `Algebra/Sylow.lean` (§19–§27) | D.4.D McKay completo: `periodOf`, `card_orbitOf_eq_periodOf` (§22), `card_orbitOf_one_or_succ` (§23), `periodOf_eq_one_iff_fixed`/`card_orbitOf_eq_one_iff_fixed` (§24), `card_orbitOf_eq_succ_of_not_fixed` (§25), `succ_n_dvd_card_of_shift_closed_no_fixed` (§26), **`succ_n_dvd_card_mckayFixedPoints`** (§27, lema principal McKay). 0 sorries. |
| `GroupTheory/Sylow/Sylow.lean` | ✅ | `Algebra/Sylow.lean` (§33–§40, §36-bis, §37-II) | **Sylow I completo** (2026-06-03): `sylow_first` (inducción fuerte sobre \|G\|, 3 ramas), `exists_isSylowSubgroup_of_isSylowExponent`, `exists_isPSubgroup_of_isSylowExponent`, `not_dvd_index_of_isSylowSubgroup`, `not_dvd_card_cosets_of_isSylowSubgroup`. **Sylow II completo** (2026-06-04): `p_group_fixed_point` (§36-bis, inducción fuerte sobre \|X\|), `sylowConjugate`, `SylowConjugateTotal_of_isSylowExponent`, `sylowSecondConjugacyTarget_of_isSylowExponent`; **0 sorries**. Sylow III: `not_dvd_index_of_isSylowSubgroup`, `not_dvd_card_cosets_of_isSylowSubgroup`. |

---

## 4. Teoría de números (`PeanoNat/NumberTheory/`)

| Módulo Peano | Estado | Equivalente en AczelSetTheory | Notas |
|---|---|---|---|
| `NumberTheory/ModEq.lean` | ✅ | `VN/ModEqVN.lean` | Congruencias `a ≡ b [mod n]` sobre VN |
| `NumberTheory/Totient.lean` | ✅ | `VN/TotientVN.lean` | Función totient de Euler `φ(n)` sobre VN |
| `NumberTheory/Fermat.lean` | ✅ | `VN/FermatVN.lean` | Pequeño teorema de Fermat y teorema de Euler sobre VN |
| `NumberTheory/Wilson.lean` | ✅ | `VN/FermatVN.lean` | `vN_wilson` y `vN_wilson_modEq` demostrados en `FermatVN.lean` (bundled con Fermat). Importa `Peano.PeanoNat.NumberTheory.Wilson` y transpone a HFSet. |
| `NumberTheory/ChineseRemainder.lean` | ✅ | `VN/CRTVN.lean` | Teorema chino del resto sobre VN |

---

## 5. Fundamentos (`PeanoNat/Foundation/`)

| Módulo Peano | Estado | Equivalente en AczelSetTheory | Notas |
|---|---|---|---|
| `Foundation/PureAxioms.lean` | ✅ | `VN/PeanoAxioms.lean` | Axiomas de Peano puros verificados sobre `vN` |
| `Foundation/PeanoSystem.lean` | ✅ | `VN/PeanoAxioms.lean` | Sistema de Peano abstracto verificado |
| `Foundation/Foundation.lean` | ✅ | `Axioms/Foundation.lean` | Axioma de fundación para HFSet (∈ bien fundada) |
| `Foundation/CantorPairing.lean` | ✅ | `VN/CantorPairingVN.lean` | Emparejamiento de Cantor `⟨m, n⟩ ↔ ℕ` sobre VN |
| `Foundation/GodelBeta.lean` | ✅ | `VN/GodelBetaVN.lean` | Función Beta de Gödel sobre VN (codificación de secuencias) |
| `Foundation/Initiality.lean` | ✅ | `VN/InitialityVN.lean` | `HFNat` (tipo `{x : HFSet // HFSet.isNat x}`), `HFNatPeanoSystem`, `vN_nat`, `vN_morph` (morfismo de Peano), `vN_morph_unique` (unicidad). Prueba que ℕ₀ es el sistema de Peano inicial en VN. |

---

## 6. Listas y conjuntos finitos (`PeanoNat/ListsAndSets/`)

| Módulo Peano | Estado | Equivalente en AczelSetTheory | Notas |
|---|---|---|---|
| `ListsAndSets/EquivRel.lean` | ⚠️ | `CList/ExtEq.lean` + `CList/SetEquiv.lean` | Peano define `EquivRelOn`: clases de equivalencia, `classOf`, disjunción o igualdad de clases. En AczelSetTheory la teoría de equivalencia está embebida: `CList/ExtEq.lean` provee `extEq`, `CList/SetEquiv.lean` provee equivalencia de conjuntos, y `HFSet` es directamente un tipo cociente `Quotient CList.Setoid`. No hay módulo `EquivRelVN` explícito. |
| `ListsAndSets/FSet.lean` | ✅ | `VN/FSet.lean` | Conjuntos finitos de VN-naturales |
| `ListsAndSets/FSetFunction.lean` | ✅ | `VN/MapBridgeVN.lean` | Funciones sobre conjuntos finitos VN; puente `FSet → HFSet` |
| `ListsAndSets/List.lean` | ✅ | `VN/ListBridgeVN.lean` | Listas de VN-naturales; puente `List ℕ₀ ↔ HFSet` |

---

## 7. Enteros (`PeanoNat/NumberSets.lean` → `Integers/`)

Peano tenía `NumberSets.lean` con la definición de `ℤ_P` como pares. AczelSetTheory lo porta y expande en un módulo completo:

| Módulo AczelSetTheory | Contenido | Estado |
|---|---|---|
| `Integers/Basic.lean` | Tipo `HFInt` = pares VN, representante canónico, `toInt`, `toNat` | ✅ |
| `Integers/Arithmetic.lean` | `+`, `-`, `*`, propiedades algebraicas sobre `HFInt` | ✅ |
| `Integers/Order.lean` | Orden `≤` sobre `HFInt` | ✅ |
| `Integers/Bijection.lean` | Biyección `HFInt ↔ ℤ` (vía isomorfismo con Lean `Int`) | ✅ |
| `Integers/Functions.lean` | Funciones de conversión y auxiliares | ✅ |
| `Integers/MobiusLiouville.lean` | Función de Möbius `μ(n)` y función de Liouville `λ(n)` | ✅ 🆕 |
| `Integers/PadicVal.lean` | Valuación p-ádica `v_p(n)` | ✅ 🆕 |

---

## 8. Prelim y utilidades (`Peano/Prelim/`)

Los módulos `Prelim` son infraestructura lógica de Peano, no contenido matemático que requiera transporte VN. AczelSetTheory los consume vía `import Peano.*` — no hay re-demostración ni módulo dedicado.

| Módulo Peano | Estado | Equivalente en AczelSetTheory | Notas |
|---|---|---|---|
| `Prelim.lean` | ✅ | (importado vía `import Peano`) | Lemas auxiliares de lógica y aritmética básica; disponibles en AczelSetTheory como dependencia directa de Peano |
| `Prelim/Classical.lean` | ✅ | `Classical` (Lean 4 kernel) | `Classical.em`, `Classical.choice`, `Classical.byContradiction`; AczelSetTheory los usa directamente sin puerto |
| `Prelim/ExistsUnique.lean` | ✅ | Lean 4 + `Axioms/Function.lean` | `∃!` es nativo de Lean 4; `Axioms/Function.lean` extiende con `uniqueness` y `ExistsUnique` sobre HFSet |

---

## 9. Nuevo en AczelSetTheory (sin equivalente en Peano)

Estas áreas son nativas de la teoría de conjuntos y no existían en Peano:

### Estructura de datos de HFSet

| Módulo | Descripción |
|---|---|
| `HFSets.lean` | Tipo HFSet = `Quotient CList.Setoid` |
| `CList/` (6 módulos) | Listas con extensionalidad: `ExtEq`, `Sort`, `Normalize`, `Filter`, `Order`, `SetEquiv` |
| `PList/` (4 módulos) | Listas polimórficas: `Basic`, `Fin0`, `Lemmas`, `Omega0` |
| `HFList.lean`, `HFListOps.lean` | Listas sobre HFSet |

### Axiomas de la teoría de conjuntos (`Axioms/`, 35 módulos)

Unión, intersección, separación, reemplazamiento, par, potencia, fundación, ordinales, cardinales, órdenes bien fundados, axioma de elección, etc. — toda la infraestructura axiomática no existía en Peano.

| Módulos destacados | Descripción |
|---|---|
| `Axioms/Ordinal.lean`, `OrdinalNat.lean` | Ordinales como HFSets |
| `Axioms/Cardinal.lean` | Cardinalidad finita sobre HFSet |
| `Axioms/VonNeumann.lean` | Embedding `vN : ℕ₀ → HFSet` y propiedades |
| `Axioms/Rank.lean` | Rango ε de HFSets |
| `Axioms/WellOrder.lean`, `LinearOrder.lean` | Buena ordenación y orden total |
| `Axioms/BooleanAlgebra.lean`, `BooleanRing.lean` | Álgebra booleana de conjuntos |

### VN avanzado (🆕 en AczelSetTheory)

| Módulo | Descripción |
|---|---|
| `VN/IsNat.lean` | Predicado `IsNat : HFSet → Prop` |
| `VN/RankVN.lean` | Rango de VN-naturales |
| `VN/CardVN.lean` | Cardinalidad de conjuntos VN |
| `VN/HFGroupVN.lean` | Estructura de grupo sobre VN-naturales |
| `VN/ProdBridgeVN.lean` | Puente producto VN ↔ HFSet |
| `VN/Injective.lean` | Injectividad del embedding VN |

### Álgebra abstracta (`Algebra/`, 13 módulos)

AczelSetTheory formaliza jerarquías algebraicas sobre HFSet sin precedente en Peano:

| Módulo | Descripción |
|---|---|
| `Algebra/Group.lean` | `HFGroup`: grupos sobre HFSet |
| `Algebra/Monoid.lean` | `HFMonoid` |
| `Algebra/Subgroup.lean` | `HFSubgroup`, cosetes, `cosetEq` |
| `Algebra/NormalSubgroup.lean` | `HFNormalSubgroup` |
| `Algebra/GroupHom.lean` | Homomorfismos de grupo, 1º/2º/3er teorema de isomorfismo |
| `Algebra/Ring.lean` | `HFRing` |
| `Algebra/RingHom.lean` | Homomorfismos de anillo |
| `Algebra/Field.lean` | `HFField` |
| `Algebra/Module.lean` | `HFModule` |
| `Algebra/LinearSpace.lean` | `HFLinearSpace` |
| `Algebra/Lattice.lean` | `HFLattice`, `HFDistributiveLattice` |
| `Algebra/CosetCount.lean` | Teorema de Lagrange y conteo de cosetes |

### Topología (`Topology/`, 5 módulos)

| Módulo | Descripción |
|---|---|
| `Topology/Basic.lean` | `HFTopSpace`, axiomas de topología sobre HFSet |
| `Topology/Interior.lean` | Interior, cierre, frontera |
| `Topology/Neighborhoods.lean` | `HFNeighborSpace`; equivalencia `τ ↔ 𝒩` |
| `Topology/Separation.lean` | Axiomas T₀, T₁, T₂ (Hausdorff) |
| `Topology/Subspace.lean` | Topología de subespacio |

---

## 10. Resumen ejecutivo

### Portado completamente (✅): ~32/53 módulos sustantivos de Peano

Toda la aritmética base, número de teoría (TFA, Fermat+Wilson, CRT, Totient), combinatoria numérica (factorial, Fibonacci, binomios, Newton, sumas, productos), fundamentos (Gödel Beta, Cantor, sistema de Peano), listas/conjuntos finitos, y prelim/utilidades lógicas (disponibles vía dependencia Peano) están portados.

### Portado parcialmente (⚠️): ~5 módulos

Buena fundación sin módulo explícito (fundamentos), relación de equivalencia (integrada en el tipo como `Quotient CList.Setoid`), teoremas de isomorfismo (versión abstracta pero no VN concreta), grupo combinatorio (`FinGroup` ↔ `HFGroup` — abstracto, sin `S_n` concreto).

### No portado (❌): ~13 módulos

**Punto crítico:** algunos módulos de permutaciones y grupos concretos sobre `ℕ₀`/VN aún pendientes:

- Permutaciones (`Perm`, `Sign`, `Orbit`, `Counting`) — equivalentes documentales ✅, contenido matemático operativo aún no
- Grupo simétrico concreto `S_n`
- Lema de Zassenhaus
- Lattice min/max sobre VN (`LatticeVN.lean` pendiente)
- Iniciality formal del sistema de Peano (`InitialityVN.lean` pendiente)

> **Nota 2026-06-03:** `Sylow I` se muda de ❌ a ✅. `Sylow II` a ⚠️ (1 sorry documentado).

### Nuevo en AczelSetTheory (🆕): ~60+ módulos sin equivalente Peano

Axiomática de conjuntos, álgebra abstracta, topología, enteros extendidos (Möbius, Liouville, valuación p-ádica).

---

## 11. Prioridades de portado sugeridas

**Última actualización:** 2026-06-03 — Sylow I completo (`sylow_first` ✅); Sylow II estructura ⚠️ (1 sorry: punto fijo del p-grupo).

1. **Completado (2026-06-03)**:
   - `SylowVN.lean` / Sylow I — `sylow_first` y corolarios completos ✅.
   - Sylow II — estructura lógica demostrada; deuda: partición de órbitas para p-grupo.

2. **Alta prioridad** (siguiente):
   - Cerrar el sorry de Sylow II: infraestructura de partición de órbitas para acciones de p-grupos.
   - `Zassenhaus.lean` — Lema de la Mariposa.

3. **Media prioridad**:
   - `OrbitVN.lean` — ecuación de clases concreta sobre VN.
   - `Integers/Rationals.lean` — ℚ₀ como cociente `HFInt × ℕ₀⁺`; cuerpo ordenado.

4. **Baja prioridad** (matemáticas avanzadas que esperan ASet₁):
   - CRT de grupos, sucesiones de Cauchy, números reales computables, algebraicos.
