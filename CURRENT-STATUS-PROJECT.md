# Current Project Status — AczelSetTheory

**Last updated:** 2026-06-04
**Author**: Julián Calderón Almendros

---

## Executive Summary

| Metric | Value |
|--------|-------|
| Total modules (non-barrel) | 133 |
| Total modules (incl. barrels) | 142 |
| Modules with 0 sorry | 134 / 134 |
| Total sorry | 0 |
| Build status | ✅ Passing — 0 errors, 0 warnings |
| Lean version | v4.30.0 |
| Naming convention | Mathlib-style (see NAMING-CONVENTIONS.md) |

---

## Module Inventory

### CList/ (7 modules)

| Module | Status |
|--------|--------|
| CList/Basic.lean | ✅ |
| CList/ExtEq.lean | ✅ |
| CList/SetEquiv.lean | ✅ |
| CList/Order.lean | ✅ |
| CList/Sort.lean | ✅ |
| CList/Normalize.lean | ✅ |
| CList/Filter.lean | ✅ |

### PList/ (4 modules)

| Module | Status |
|--------|--------|
| PList/Basic.lean | ✅ |
| PList/Fin0.lean | ✅ |
| PList/Lemmas.lean | ✅ |
| PList/Omega0.lean | ✅ |

### Top-level (4 modules)

| Module | Status |
|--------|--------|
| HFSets.lean | ✅ |
| HFList.lean | ✅ |
| HFListOps.lean | ✅ |
| Notation.lean | ✅ |

### Operations/ (21 modules)

| Module | Status |
|--------|--------|
| Operations/Union.lean | ✅ |
| Operations/Intersection.lean | ✅ |
| Operations/Setminus.lean | ✅ |
| Operations/Separation.lean | ✅ |
| Operations/Pair.lean | ✅ |
| Operations/Powerset.lean | ✅ |
| Operations/SymDiff.lean | ✅ |
| Operations/OrderedPair.lean | ✅ |
| Operations/Relation.lean | ✅ |
| Operations/Function.lean | ✅ |
| Operations/Inverse.lean | ✅ |
| Operations/Restriction.lean | ✅ |
| Operations/Composition.lean | ✅ |
| Operations/Replacement.lean | ✅ |
| Operations/Cardinal.lean | ✅ |
| Operations/FunctionComp.lean | ✅ |
| Operations/Identity.lean | ✅ |
| Operations/Product.lean | ✅ |
| Operations/CartProd.lean | ✅ |
| Operations/NPow.lean | ✅ |
| Operations/Order.lean | ✅ |

### Axioms/ (41 modules)

| Module | Status |
|--------|--------|
| Axioms/Union.lean | ✅ |
| Axioms/Intersection.lean | ✅ |
| Axioms/Setminus.lean | ✅ |
| Axioms/Separation.lean | ✅ |
| Axioms/Pair.lean | ✅ |
| Axioms/Powerset.lean | ✅ |
| Axioms/Singleton.lean | ✅ |
| Axioms/SymDiff.lean | ✅ |
| Axioms/OrderedPair.lean | ✅ |
| Axioms/Foundation.lean | ✅ |
| Axioms/Decidable.lean | ✅ (`mem_decidable`, `instDecidableEqHFSet`, `instDecidableEmpty`) |
| Axioms/Subset.lean | ✅ |
| Axioms/Lattice.lean | ✅ |
| Axioms/BooleanAlgebra.lean | ✅ |
| Axioms/BooleanRing.lean | ✅ |
| Axioms/Succ.lean | ✅ |
| Axioms/VonNeumann.lean | ✅ |
| Axioms/Choice.lean | ✅ |
| Axioms/Cardinal.lean | ✅ |
| Axioms/Relation.lean | ✅ |
| Axioms/Function.lean | ✅ |
| Axioms/Bijection.lean | ✅ |
| Axioms/Inverse.lean | ✅ |
| Axioms/Composition.lean | ✅ |
| Axioms/Restriction.lean | ✅ |
| Axioms/Replacement.lean | ✅ |
| Axioms/FunctionComp.lean | ✅ |
| Axioms/Identity.lean | ✅ |
| Axioms/Product.lean | ✅ |
| Axioms/Image.lean | ✅ |
| Axioms/Adjunction.lean | ✅ |
| Axioms/Induction.lean | ✅ |
| Axioms/CartProd.lean | ✅ |
| Axioms/Ordinal.lean | ✅ |
| Axioms/OrdinalNat.lean | ✅ |
| Axioms/Fintype.lean | ✅ |
| Axioms/NPow.lean | ✅ |
| Axioms/Rank.lean | ✅ (`rank`, `rank_empty`, `rank_insert`, `mem_rank_lt`, `instance mem_wf`) |
| Axioms/Order.lean | ✅ |
| Axioms/WellOrder.lean | ✅ |
| Axioms/LinearOrder.lean | ✅ |

### VN/ (35 modules)

| Module | Key exports | Status |
|--------|-------------|--------|
| VN/Basic.lean | `vN : ℕ₀ → HFSet`, `vN_zero`, `vN_succ` | ✅ |
| VN/Injective.lean | `vN_injective` | ✅ |
| VN/IsNat.lean | `isNat_iff_range` | ✅ |
| VN/Arithmetic.lean | `mem_vN_iff_lt`, `vN_mono`, `vN_le_iff_subset` | ✅ |
| VN/FSet.lean | `fsetToHFSet`, `fsetToHFSet_injective` | ✅ |
| VN/PeanoAxioms.lean | PA1/PA2/PA3 as HFSet theorems | ✅ |
| VN/PeanoArith.lean | `addVN`, `vN_add`, arithmetic laws | ✅ |
| VN/PowVN.lean | `powVN`, 14 theorems | ✅ |
| VN/SubVN.lean | `vN_sub_*`, 12 theorems | ✅ |
| VN/DivVN.lean | `vN_divMod_spec`, 6 theorems | ✅ |
| VN/FactorialVN.lean | `factVN`, 10 theorems | ✅ |
| VN/CardVN.lean | `card_vN` | ✅ |
| VN/RankVN.lean | `rank_vN` | ✅ |
| VN/GcdVN.lean | `gcdVN`, `lcmVN`, 13 theorems | ✅ |
| VN/FibVN.lean | `fibVN`, 4 theorems | ✅ |
| VN/BinomVN.lean | `binomVN`, 8 theorems | ✅ |
| VN/SummationVN.lean | `finSumVN`, 8 theorems | ✅ |
| VN/SqrtVN.lean | `sqrtVN`, `sqrtRemVN`, `csqrtVN`, 7 theorems | ✅ |
| VN/LogVN.lean | `logVN`, `logRemVN`, `clogVN`, 7 theorems | ✅ |
| VN/DigitsVN.lean | `numDigitsVN`, `ofDigitsVN`, 4 theorems | ✅ |
| VN/ModEqVN.lean | `ModEq_HF`, `≡ₕ [MODHF]`, 12 theorems | ✅ |
| VN/TotientVN.lean | `totientVN`, 6 theorems | ✅ |
| VN/PrimesVN.lean | `smallestDivisorVN` | ✅ |
| VN/CantorPairingVN.lean | `pairVN`, `fstVN`, `sndVN`, 6 theorems | ✅ |
| VN/PairingVN.lean | `cantorPairVN`, 5 theorems | ✅ |
| VN/NewtonBinomVN.lean | `binomTermVN`, 4 theorems | ✅ |
| VN/ProductVN.lean | `finProdVN`, 7 theorems | ✅ |
| VN/GodelBetaVN.lean | `betaVN`, `vN_beta_of_lt` | ✅ |
| VN/HFGroupVN.lean | `imageGroup : ℕ₀FinGroup → FinGroup HFSet` | ✅ |
| VN/ProdBridgeVN.lean | `prodBridge : ℕ₀ × ℕ₀ → HFSet` | ✅ |
| VN/MapBridgeVN.lean | `mapBridge : MapOn A B → HFSet` | ✅ |
| VN/ListBridgeVN.lean | `listBridge : List ℕ₀ → HFSet` | ✅ |
| VN/PrimeVN.lean | `prime_HF`, `dvd_HF`, TFA, Gauss, 15 theorems | ✅ |
| VN/FermatVN.lean | `vN_fermat_little`, `vN_wilson` | ✅ |
| VN/CRTVN.lean | `vN_chinese_remainder` | ✅ |

### Algebra/ (20 modules)

| Module | Key exports | Status |
|--------|-------------|--------|
| Algebra/Group.lean | `HFAlgebra.HFGroup`, 10 lemas derivados | ✅ |
| Algebra/Subgroup.lean | `HFSubgroup`, `toHFGroup`, `inter`, `rightCoset`, `cosetEq`, 16 teoremas | ✅ |
| Algebra/GroupHom.lean | `HFGroupHom`, `hom_e`, `hom_inv`, `ker`, `image` | ✅ |
| Algebra/NormalSubgroup.lean | `HFNormalSubgroup`, `centralizer`, `center`, `normalizer`, `ker_isNormal` | ✅ |
| Algebra/Ring.lean | `HFRing`, `toAdditiveHFGroup`, 7 lemas derivados | ✅ |
| Algebra/CosetCount.lean | `cosets`, `index`, `card_sUnion_uniform_partition`, Lagrange (9 teoremas) | ✅ |
| Algebra/Monoid.lean | `HFMonoid`, lemas de monoid | ✅ |
| Algebra/RingHom.lean | `HFRingHom`, `hom_zero`, `hom_one`, `ker`, `image` | ✅ |
| Algebra/Field.lean | `HFField`, cociente de campos | ✅ |
| Algebra/Module.lean | `HFModule`, módulo sobre anillo | ✅ |
| Algebra/LinearSpace.lean | `HFLinearSpace`, axiomas de espacio vectorial | ✅ |
| Algebra/Lattice.lean | `HFLattice`, retículo | ✅ |
| Algebra/Action.lean | `HFGroupAction`, `orb`, `stab`, `orbits_partition`, `conjugAction` | ✅ |
| Algebra/CosetAction.lean | acción de G sobre cosetes; lemas de acción transitiva | ✅ |
| Algebra/QuotientGroup.lean | `quotientGroup`, `quotientHom`, `ker_quotientHom_eq` | ✅ |
| Algebra/FirstIsomorphism.lean | `firstIsoMap`, `firstIsoMap_bijective` | ✅ |
| Algebra/SecondIsomorphism.lean | `secondIsoMap`, `secondIsoMap_bijective` | ✅ |
| Algebra/ThirdIsomorphism.lean | `thirdIsoMap`, `thirdIsoMap_ker_eq` | ✅ |
| Algebra/CorrespondenceTheorem.lean | `preimageSubgroup`, `imageSubgroup_preimage`, `preimageSubgroup_image` | ✅ |
| Algebra/Sylow.lean | `mckayCarrier`, `mckayShift`, `orbitOf`, `periodOf`, `succ_n_dvd_card_mckayFixedPoints` (D.4.D McKay), `p_group_fixed_point`, `sylowConjugate`, `SylowConjugateTotal_of_isSylowExponent`, 50+ teoremas | ✅ |

### Integers/ (7 modules)

| Module | Key exports | Status |
|--------|-------------|--------|
| Integers/Basic.lean | `ℤ₀`, ring instances, 18 ring laws, `ofNat` | ✅ |
| Integers/Order.lean | orden en ℤ₀, `≤`, `<`, compatibilidad con operaciones | ✅ |
| Integers/Functions.lean | homomorfismos ℤ₀ → ℤ₀ | ✅ |
| Integers/Arithmetic.lean | GCD, divisibilidad, lemas aritméticos en ℤ₀ | ✅ |
| Integers/Bijection.lean | biyecciones entre ℤ₀ y ℕ₀ | ✅ |
| Integers/PadicVal.lean | `padic_val`, `Omega_prime`, multiplicatividad | ✅ |
| Integers/MobiusLiouville.lean | `μ` (Möbius), `λ` (Liouville), multiplicatividad | ✅ |

### Topology/ (5 modules)

| Module | Key exports | Status |
|--------|-------------|--------|
| Topology/Basic.lean | `HFTopSpace`, `isClosed`, axiomas topológicos | ✅ |
| Topology/Interior.lean | `interior`, `closure`, `exterior`, `boundary`, 15+ teoremas | ✅ |
| Topology/Subspace.lean | `subspace`, `preimage`, `HFContinuous`, `HFContinuous.comp` | ✅ |
| Topology/Neighborhoods.lean | `HFNeighborSpace`, `toNeighborSpace`, `toTopSpace`, equivalencia τ↔𝒩 | ✅ |
| Topology/Separation.lean | `isT0`–`isT4`, `isRegular`, `isNormal`, cadena T₄→…→T₀, `T1_iff_singletons_closed` | ✅ |

---

## Known Sorry Locations

None — **0 sorry** across the entire project.

---

## Recent Achievements (2026-06-04) — M6 completo: Sylow II sorry cerrado

- ✅ **Segundo Teorema de Sylow** completamente demostrado — 0 sorries.
  - `p_group_fixed_point` (private): si `|G| = p^n` y `p ∤ |X|`, existe punto fijo en X.
    Demostrado por inducción fuerte sobre `|X|` con partición de órbitas.
  - `sylowConjugate`: hfixed probado vía `p_group_fixed_point` + `cosetAction K H`.
  - M6 (H13/H14/H15 Sylow) marcado ✅ en PLANNING.md.
- ✅ Build: 88 jobs, **0 errores, 0 sorries**.

## Previous Achievements (2026-06-03) — Sylow I completo + Sylow II estructura

- ✅ **Primer Teorema de Sylow** (`sylow_first`) completamente demostrado sin sorry.
  - Infraestructura: `improperSubgroup`, `subgroupOfSubgroup`, `card_preimage_mul`.
  - Auxiliares internos: rama de subgrupo propio (`§37` interno), Cauchy en Z(G), cociente + preimagen.
  - Corolarios: `exists_isSylowSubgroup_of_isSylowExponent`, `exists_isPSubgroup_of_isSylowExponent`.
  - Sylow III (parcial): `not_dvd_index_of_isSylowSubgroup`, `not_dvd_card_cosets_of_isSylowSubgroup`.
- ✅ **Segundo Teorema de Sylow** — estructura lógica completa (`sylowConjugate`, `SylowConjugateTotal_of_isSylowExponent`, `sylowSecondConjugacyTarget_of_isSylowExponent`).
  - Sorry cerrado en 2026-06-04 (ver arriba).
- ✅ Build (2026-06-03): 87 jobs, 0 errores, 1 sorry (ya cerrado).
- ✅ Documentación: `doc/REFERENCE-Algebra.md` actualizada con §33–§40 + §37-II; `REFERENCE.md` actualizado.

---

## Recent Achievements (2026-06-02) — Sprint C1/C2: TODO/PEND/FIXME en 0

- ✅ Cierre de marcadores textuales en `Topology/{Basic,Interior,Neighborhoods,Separation,Subspace}.lean` y `Algebra/Sylow.lean`.
- ✅ Cierre de marcadores textuales en `Algebra/Action.lean` y stubs VN `ActionVN`, `CorrespondenceTheoremVN`, `PermVN`, `SymGroupVN`.
- ✅ `AUDIT-MODULE-MATRIX.md` regenerada con:
  - `noncomputable def: 0`
  - `Modulos con TODO/PENDIENTE/FIXME: 0`
  - `Modulos con placeholder/stub: 11`
- ✅ Build verificado: `lake build` (35 jobs), sin errores.

## Recent Achievements (2026-06-02) — Sprint D1: placeholder/stub VN inicial (11 → 7)

- ✅ Limpieza de marcadores `placeholder/stub` en `VN/PermVN.lean`, `VN/OrbitVN.lean`, `VN/CountingVN.lean` y `VN/SignVN.lean`.
- ✅ Regeneración de `AUDIT-MODULE-MATRIX.md` tras cada cierre de bloque para trazabilidad incremental.
- ✅ Estado consolidado:
  - `noncomputable def: 0`
  - `Modulos con TODO/PENDIENTE/FIXME: 0`
  - `Modulos con placeholder/stub: 7`

## Recent Achievements (2026-06-02) — Sprint D2: placeholder/stub VN residual (7 → 0)

- ✅ Limpieza final de marcadores `placeholder/stub` en `VN/ActionVN.lean`, `VN/CorrespondenceTheoremVN.lean`, `VN/FirstIsomorphismVN.lean`, `VN/SecondIsomorphismVN.lean`, `VN/ThirdIsomorphismVN.lean`, `VN/QuotientGroupVN.lean` y `VN/NormalSubgroupVN.lean`.
- ✅ Regeneración de `AUDIT-MODULE-MATRIX.md` tras cada cierre individual para trazabilidad fina.
- ✅ Estado consolidado:
  - `noncomputable def: 0`
  - `Modulos con TODO/PENDIENTE/FIXME: 0`
  - `Modulos con placeholder/stub: 0`

---

## Recent Achievements (2026-05-29) — D.4.D McKay completo [`Sylow.lean` §24–§27]

- ✅ **§24**: `periodOf_eq_one_iff_fixed` + `card_orbitOf_eq_one_iff_fixed` (equivalencia período 1 ↔ punto fijo del shift).
- ✅ **§25**: `card_orbitOf_eq_succ_of_not_fixed` (caso primo + no fijo ⇒ `card(orbit) = σ n`).
- ✅ **§26**: `succ_n_dvd_card_of_shift_closed_no_fixed` — WOP fuerte vía `Peano.WellFounded.strongInductionOn` sobre `card S`. En cada paso: orbit de tamaño `σ n`; `S' = S \ orbit` shift-cerrado; recursión.
- ✅ **§27**: `succ_n_dvd_card_mckayFixedPoints` — **Lema de McKay D.4.D**: `σ n primo ∧ σ n ∣ |G| → σ n ∣ card(fixedPoints)`. Partición `|C| = |F| + |S|`; D.3 da `p ∣ |C|`; §26 da `p ∣ |S|`; `divides_sub` + `cancelation_add` cierran.
- ✅ **Documentación** actualizada: header + bloque exports en `Sylow.lean`; `NEXT_STEPS.md`; `CURRENT-STATUS-PROJECT.md`; `doc/REFERENCE-Paridad-Peano-Aczel.md`.
- **Build:** `lake build` → 75 jobs ✅, 0 sorry, 0 warnings.

## Recent Achievements (2026-05-26) — Rank.lean + Decidable.lean

- ✅ **Axioms/Rank.lean** — `theorem mem_rank_lt : ∀ (a b : HFSet), a ∈ b → rank a < rank b` (por `eps_induction` con `lt_self_σ_self`, `lt_of_lt_of_le`, `le_max_left/right`); `instance mem_wf : WellFounded (· ∈ · : HFSet → HFSet → Prop)` vía `Subrelation.wf` + `InvImage.wf rank well_founded_lt`. Bug corregido: patrón `rfl` → `hax` + `rw [hax]` cuando dos vars lambda son fijas y distintas.
- ✅ **Axioms/Decidable.lean** — `instance instDecidableEmpty (A : HFSet) : Decidable (A = empty) := instDecidableEqHFSet A empty`.
- ✅ **Integers/PadicVal.lean** — Confirmado 0 sorry: `Omega_prime_mul` completamente probado (inducción fuerte sobre `n` usando `Omega_prime_mul_prime` y `Omega_prime_step`).

## Recent Achievements (2026-05-23) — Topology/Separation.lean

- ✅ **Topology/Separation.lean** — axiomas de separación T₀–T₄: `isT0`, `isT1`, `isT2`, `isRegular`, `isT3`, `isNormal`, `isT4`; cadena de implicaciones `T4_implies_T3_implies_T2_implies_T1_implies_T0`; caracterización `T1_iff_singletons_closed`. Técnica clave: `X \ {x} = ⋃{U ∈ τ | x ∉ U}` via `HFSet.sep` + `sUnion_mem`.
- ✅ **Topology.lean** (barrel): añadido import de `Topology.Separation`.

---

## Recent Achievements (2026-05-22) — Topology completo

- ✅ **Topology/Basic.lean** — `HFTopSpace` con axiomas mínimos; `isClosed`; teoremas de clausura de abiertos finitos bajo unión e intersección.
- ✅ **Topology/Interior.lean** — `interior`, `closure`, `exterior`, `boundary`; clasificación de puntos (`isInteriorPt`, `isExteriorPt`, `isBoundaryPt`, `isAccumulationPt`, `isAdherencePt`, `isIsolatedPt`); 3 sorries eliminados: `closure_closed`, `closure_eq_of_closed` (+ `hA`), `isAdherencePt_iff_mem_closure` (mpr con `Classical.byContradiction` + `interior_largest`).
- ✅ **Topology/Subspace.lean** — `subspace` τ_A; `preimage`; `HFContinuous` (id + comp); 5 sorries eliminados: 4 campos de `subspace` + `preimage_inter`.
- ✅ **Topology/Neighborhoods.lean** — `HFNeighborSpace`; `toNeighborSpace`, `toTopSpace`; equivalencia completa `τ ↔ 𝒩`; 3 sorries eliminados: `toNeighborSpace_toTopSpace_τ` (→), `toTopSpace_toNeighborSpace_𝒩` (→ y ←). Testigo para ← : `HFSet.sep ns.X (fun y => N ∈ ns.𝒩 y)` inline (let-binding opaco eliminado).
- ✅ **Axioms/Setminus.lean** — `setminus_setminus_of_subset {A X} (h : A ⊆ X) : X \ (X \ A) = A` (lema auxiliar para clausura).
- ✅ **Algebra/** — 4 módulos adicionales integrados en barrel: Monoid, RingHom, Field, Module.
- ✅ **Integers/** — 6 módulos adicionales integrados en barrel: Order, Functions, Arithmetic, Bijection, PadicVal, MobiusLiouville.

## Recent Achievements (2026-05-21) — Álgebra: Subgroup, GroupHom, Ring, CosetCount

- ✅ **Algebra/Subgroup.lean** — `HFAlgebra.HFSubgroup`: subgrupo como estructura, `toHFGroup`, `inter` (intersección), `rightCoset` (cosete derecho Ha), `cosetEq` (relación a ~_H b). 16 teoremas: refl/symm/trans de `cosetEq`, equivalencia con igualdad de cosetes, cubrimiento de G, disyunción de cosetes, cardinalidad de Ha.
- ✅ **Algebra/GroupHom.lean** — `HFAlgebra.HFGroupHom`: φ : G →ₕ H; `hom_e` (φ(e_G) = e_H), `hom_inv` (φ(a⁻¹) = φ(a)⁻¹); `ker` (subgrupo de G), `image` (subgrupo de H).
- ✅ **Algebra/Ring.lean** — `HFAlgebra.HFRing`: anillo unitario con grupo aditivo abeliano; `toAdditiveHFGroup`; 7 lemas derivados: `add_zero`, `add_neg`, `neg_neg`, `zero_mul`, `mul_zero`, `neg_mul`, `mul_neg`.
- ✅ **Algebra/CosetCount.lean** — Lema de partición uniforme (`card_sUnion_uniform_partition`) + **Teorema de Lagrange**: `card_subgroup_dvd_card_group` (⊢ |H| ∣ |G|). Build completo 0 errores.

## Recent Achievements (2026-05-19 – 2026-05-20)

- ✅ **B3: Order theory** — `Operations/Order.lean` (24 definitions: isReflexive…isWellOrder), `Axioms/Order.lean` (~28 theorems: chain of implications, empty/restrict, uniqueness), `Axioms/WellOrder.lean` (`wf_induction`, `wo_induction`, `minimum_in_nonempty`, `no_infinite_descent`).
- ✅ **VN transport groups 1+2+3** — 12 new VN modules: SummationVN, SqrtVN, LogVN, DigitsVN, ModEqVN, TotientVN, PrimesVN, CantorPairingVN, PairingVN, NewtonBinomVN, ProductVN, GodelBetaVN.
- ✅ **VN bridges** — HFGroupVN (`imageGroup`), ProdBridgeVN (`prodBridge`), MapBridgeVN (`mapBridge`), ListBridgeVN (`listBridge`).
- ✅ **Fase A: aritmética completa** — ModEqVN (extendido, `ModEq_HF`), TotientVN (extendido), PrimeVN (TFA, Lema de Gauss, `dvd_HF`/`prime_HF`/`coprime_HF`), FermatVN (Pequeño Teorema de Fermat, Teorema de Wilson), CRTVN (Teorema Chino del Resto).
- ✅ **Algebra/Group.lean** — `HFAlgebra.HFGroup` con axiomas mínimos izquierdos; 10 lemas derivados: `op_inv_left_apply`, `left_cancel`, `op_inv_right`, `op_id_right`, `right_cancel`, `inv_inv`, `inv_e`, `inv_op`, `unique_id`, `unique_inv`.
- ✅ **Axioms/LinearOrder.lean** — `LT HFSet` + `StrictLinearOrder HFSet` vía `CList.lt` en representantes canónicos. Instancias: `instDecidableLt`, `StrictLinearOrder HFSet`.
- ✅ **Integers/Basic.lean** — `ℤ₀ = Quotient intSetoid` (enteros como cociente de ℕ₀ × ℕ₀). Representante canónico `normalize`. Instancias: `Zero`, `One`, `Add`, `Neg`, `Mul`, `Sub`. Leyes de anillo conmutativo completas (18 teoremas). Embedding `ofNat : ℕ₀ → ℤ₀` inyectivo.
- ✅ **Barrel fix** — `HFListOps.lean` añadido a `AczelSetTheory.lean` (era módulo huérfano).

---

## Architecture

```
AczelSetTheory/
  CList/          — Core CList behavior (7 sub-modules)
  PList/          — Polymorphic list type over ℕ₀ (4 modules)
  Operations/     — Constructors and definitions over HFSet (21 modules)
  Axioms/         — Axiomatic properties and theorems over HFSet (41 modules)
  VN/             — Von Neumann embedding vN : ℕ₀ → HFSet (35 modules)
  Algebra/        — Algebraic structures native in HFSet (9 modules)
  Integers/       — Integer type ℤ₀ as quotient of ℕ₀ × ℕ₀ (7 modules)
  Topology/       — Topological spaces over HFSet (4 modules)
  HFSets.lean     — Core HFSet quotient type
  HFList.lean     — Ordered sequences of HFSets (PList HFSet)
  HFListOps.lean  — toHFSet conversions (FinList/HFList → HFSet)
  Notation.lean   — Notation macros, von Neumann numerals 0–9
```

---

## Development Phases

| Phase | Description | Status |
|-------|-------------|--------|
| Phase 1 | CList foundations (7 sub-modules) | ✅ |
| Phase 2 | HFSet quotient, repr, canonical representatives | ✅ |
| Phase 3 | Zermelo axioms: Extensionality, Empty, Pairs | ✅ |
| Phase 4 | Zermelo axioms: Union, Separation, Intersection, Setminus | ✅ |
| Phase 5 | Powerset | ✅ |
| Phase 6 | Relations, functions, injections, bijections, composition, identity | ✅ |
| Phase 6b | Cartesian product `×ₛ`, image `imageRel` | ✅ |
| Phase 6c | Von Neumann embedding `vN : ℕ₀ → HFSet` | ✅ |
| Phase 7 | Adjunction, ε-induction | ✅ |
| Phase 7c | Computable `×ₕ` CartProd via CList flatMap | ✅ |
| Phase 7d | Ordinals + `card_vN` | ✅ |
| Phase 7e | `isOrdinal_iff_isNat` + n-ary `nPow` | ✅ |
| Phase 7f | `Finset`, `Fintype`, `toFinset` (scratch-built) | ✅ |
| Phase 7g | `mem_nPow_zero/succ` | ✅ |
| Phase A1–A3, C1 | PowVN, SubVN, DivVN, FactorialVN | ✅ |
| Phase B1 | Von Neumann rank (`rank : HFSet → ℕ₀`, `rank_vN`) | ✅ |
| Phase B2 | GcdVN, FibVN, BinomVN; HFList/FinList theory | ✅ |
| Phase B3 | Order theory (Operations/Order, Axioms/Order, Axioms/WellOrder) | ✅ |
| VN Groups 1+2+3 | 12 VN transport modules (summation, sqrt, log, digits, …) | ✅ |
| VN Bridges | HFGroupVN, ProdBridgeVN, MapBridgeVN, ListBridgeVN | ✅ |
| Fase A | ModEqVN (ext.), TotientVN (ext.), PrimeVN, FermatVN, CRTVN | ✅ |
| Algebra | `HFAlgebra.HFGroup` with 10 derived lemmas | ✅ |
| LinearOrder | `LT HFSet`, `StrictLinearOrder HFSet` | ✅ |
| Integers | `ℤ₀` commutative ring (quotient ℕ₀ × ℕ₀) + Order, Functions, Arithmetic, Bijection, PadicVal, MobiusLiouville | ✅ |
| Topology | `HFTopSpace`, topología de entornos, subespacio, aplicaciones continuas | ✅ |

> See [NEXT_STEPS.md](NEXT_STEPS.md) for detailed planning and next priorities.

---

## Documentation (2026-05-22)

| Recurso | Descripción |
|---------|-------------|
| `REFERENCE.md` | Índice raíz — catálogo completo de módulos |
| `doc/REFERENCE-*.md` (8 propios) | CList, HFList, HFSets, PList, Relations, Algebra, VN, Topology |
| `doc/REFERENCE-*.md` (7 Peano) | Arithmetic, Combinatorics, Foundation, GroupTheory, ListsAndSets, NumberTheory, Prelim |
| `doc/peano/` | 6 documentos de diseño heredados de Peano + README |
| `CHANGELOG-PEANO.md` | Historial completo del proyecto predecesor Peano |
| `DECISIONS.md` | 11 ADRs con plantilla completa (fecha, estado, rationale) |
| `THOUGHTS.md` | Diario de diseño (1060 líneas, incluye herencia de Peano) |

---

**Author**: Julián Calderón Almendros
*Last updated: 2026-06-02*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
