# Changelog

All notable changes to this project are documented here.

> Para el historial del proyecto predecesor (Peano), ver [CHANGELOG-PEANO.md](CHANGELOG-PEANO.md).

---

## [2026-05-23] — Topology/Separation.lean: axiomas T₀–T₄ (0 sorries)

### Added

- **`Topology/Separation.lean`** — nuevo módulo con axiomas de separación:
  - **Definiciones**: `isT0`, `isT1`, `isT2`, `isRegular`, `isT3`, `isNormal`, `isT4`.
  - **Cadena de implicaciones**: `T2_implies_T1`, `T1_implies_T0`, `T3_implies_T2`, `T4_implies_T3`.
  - **Transitivas**: `T4_implies_T2`, `T3_implies_T1`, `T4_implies_T1`, `T2_implies_T0`, `T3_implies_T0`, `T4_implies_T0`.
  - **Caracterización de T₁**: `singletons_closed_of_T1`, `T1_of_singletons_closed`, `T1_iff_singletons_closed`.
  - Técnica clave: `X \ {x} = ⋃{U ∈ τ | x ∉ U}` con `HFSet.sep` + `sUnion_mem`.
- **`Topology.lean`** (barrel): añadido `import AczelSetTheory.Topology.Separation`.
- **`doc/REFERENCE-Topology.md`**: sección `Topology.Separation` añadida.

## [2026-05-22] — Topology completo: 0 sorries en 4 módulos, lema setminus_setminus_of_subset

### Added / Fixed

- **`Axioms/Setminus.lean`**:
  - Añadido `setminus_setminus_of_subset {A X : HFSet} (h : A ⊆ X) : X \ (X \ A) = A`.
    Usado internamente por `Interior.lean` (clausura) y exportado a `doc/REFERENCE-HFSets.md`.

- **`Topology/Interior.lean`** (3 sorries eliminados):
  - `closure_closed`: `X \ cl(A) = int(X\A)` ∈ τ. Usa `setminus_setminus_of_subset` + `interior_open`.
  - `closure_eq_of_closed`: firma extendida con `(hA : A ⊆ ts.X)`; prueba: `interior_eq_of_open hcl` + `setminus_setminus_of_subset hA`.
  - `isAdherencePt_iff_mem_closure` (mpr): `Classical.byContradiction` + `interior_largest` para la dirección difícil. Firma extendida con `(hA : A ⊆ ts.X)`.

- **`Topology/Subspace.lean`** (5 sorries eliminados):
  - `subspace` (`empty_mem`, `univ_mem`, `sUnion_mem`, `inter_mem`): se probaron usando `HFSet.mem_sep`, `HFSet.mem_inter`, `HFSet.mem_powerset` directamente sin `by_contra`.
  - `HFContinuous.preimage_inter`: reordenamiento de `rw` (preimage → inter LHS → inter RHS → preimage × 2).

- **`Topology/Neighborhoods.lean`** (3 sorries eliminados):
  - `toNeighborSpace_toTopSpace_τ` (→): demostrado expresando `U = sUnion {V ∈ τ | V ⊆ U}`.
  - `toTopSpace_toNeighborSpace_𝒩` (→): nombrar `hNX` para `ns.up_closed`.
  - `toTopSpace_toNeighborSpace_𝒩` (←): testigo `V = {y ∈ X | N ∈ 𝒩(y)}`; se eliminaron `rw` redundante y `let V` (opaco) usando `HFSet.sep ns.X (fun y => N ∈ ns.𝒩 y)` directamente.

### Documentation

- **`doc/REFERENCE-Topology.md`**: eliminados todos los `⚠️ sorry`; corregidas firmas de `𝒩_sub` (tipo real: `N ∈ 𝒩 x → N ⊆ X`), `interior` (axioma: `∀ {y}, y ∈ M → N ∈ 𝒩 y`), `closure_eq_of_closed` (+ `hA`), `isAdherencePt_iff_mem_closure` (+ `hA`); tabla de sorries reemplazada por "0 sorries".
- **`doc/REFERENCE-HFSets.md`**: añadidos `setminus_subset` y `setminus_setminus_of_subset` al catálogo de `Axioms/Setminus.lean`.

**Project status: 0 sorry, 0 errors. 122 non-barrel modules (132 total).**

---

## [2026-05-22] — PadicVal + MobiusLiouville: multiplicatividad de Ω y λ, corrección de bugs pre-existentes

### Added / Fixed

- **`Integers/PadicVal.lean`**:
  - Corregido `padicVal_succ_dvd`: uso de `generalize hv : padicVal p (n/p) = v` antes de `unfold padicVal` para evitar que `unfold` desplegara la llamada recursiva en la RHS.
  - Corregido `Omega_prime_prime`: eliminado paso intermedio `h1` que causaba ambigüedad; prueba directa desde goal `Omega_prime p = 𝟙` con `unfold + rw`.
  - Añadido `mul_div_cancel_right'` (privado), `Omega_prime_mul` (**1 sorry** — requiere `smallestDivisorAux_spec` privado de Peano), `Omega_prime_mul_prime`.

- **`Integers/MobiusLiouville.lean`**:
  - Añadido `liouville_mul`: λ(m·n) = λ(m)·λ(n) para m,n ≠ 0 (usa `Omega_prime_mul`).
  - Añadido `liouville_prime_pow`: λ(p^k) = (-1)^k para p primo (por inducción).
  - Corregido `liouville_ne_zero`: `by omega₀` → `Ne.symm (succ_neq_zero 𝟘)` (omega₀ no prueba ¬(𝟘=𝟙) directamente).
  - Corregido `mobius_sq`: `split_ifs` (no disponible en este entorno) → `by_cases h : squarefree n`.

### Technical notes

- Patrón clave para `unfold` de definiciones WFR con recursión: usar `generalize hv : f rec_arg = v` antes de `unfold f` para que `unfold` solo afecte la llamada de nivel superior.
- `← negOnePow_add` + `congr 1` cierra `negOnePow (add k' 𝟙) = negOnePow (σ k')` sin `omega₀` adicional (la igualdad `add k' 𝟙 = σ k'` se reduce definitivamente via `congr 1`).

---

## [2026-05-21] — Algebra completa: Subgroup, GroupHom, Ring, CosetCount + Teorema de Lagrange, 118 módulos, 0 sorry

### Added

- **`Algebra/Subgroup.lean`** (módulo nuevo): `HFAlgebra.HFSubgroup` — estructura de subgrupo, `toHFGroup`, `inter` (intersección de subgrupos), `rightCoset` (cosete derecho Ha := {h·a | h ∈ H}), `cosetEq` (equivalencia a ~_H b ↔ b·a⁻¹ ∈ H). 16 teoremas: reflexividad/simetría/transitividad, equivalencia cosete-cosetEq, cubrimiento de G, disyunción Ha = Hb ∨ Ha ∩ Hb = ∅.
- **`Algebra/GroupHom.lean`** (módulo nuevo): `HFAlgebra.HFGroupHom` — homomorfismo φ : G →ₕ H; `hom_e` (φ(eG) = eH), `hom_inv` (φ(a⁻¹) = φ(a)⁻¹); `ker` (subgrupo de G), `image` (subgrupo de H).
- **`Algebra/Ring.lean`** (módulo nuevo): `HFAlgebra.HFRing` — anillo unitario con grupo aditivo abeliano (axiomas izq. + comm), monoide multiplicativo, bilinealidad; `toAdditiveHFGroup`; 7 lemas derivados: `add_zero`, `add_neg`, `neg_neg`, `zero_mul`, `mul_zero`, `neg_mul`, `mul_neg`.
- **`Algebra/CosetCount.lean`** (módulo nuevo): `HFSet.sUnion_insert`, `HFSet.card_sUnion_uniform_partition` (cardinalidad de partición uniforme); `HFSubgroup.cosets` (conjunto de cosetes derechos), `HFSubgroup.index` ([G:H]); `cosets_cover` (∪Ha = G), `cosets_pairwise_disjoint`; **`card_subgroup_dvd_card_group`** — **Teorema de Lagrange**: |H| ∣ |G|.

### Documentation

- **`doc/REFERENCE-Algebra.md`** proyectado: nuevas secciones §4.87–§4.91 (definiciones) + §6.87–§6.91 (teoremas) + §7b (exports) para los 5 módulos de `Algebra/`.
- **`REFERENCE.md`**: filas 87–91 añadidas a la tabla de módulos.
- **`CURRENT-STATUS-PROJECT.md`**: actualizado a 118 módulos, sección Algebra/ expandida a 5 módulos.

**Project status: 0 sorry, 0 errors. 118 non-barrel modules (127 total).**

---

## [2026-05-20] — Integers/Basic: ℤ₀, barrel fix, 114 módulos, 0 sorry

### Added

- **`Integers/Basic.lean`** (módulo nuevo): `ℤ₀ = Quotient intSetoid` donde `intEq (a,b) (c,d) ↔ Peano.Add.add a d = Peano.Add.add b c`. Representante canónico `normalize`. Instancias: `Zero`, `One`, `Add`, `Neg`, `Mul`, `Sub`. 18 leyes de anillo conmutativo (tipos escritos con `Add.add`/`Mul.mul` para evitar conflicto con notación global Peano `notation a "+" b => Peano.Add.add a b`). Embedding `ofNat : ℕ₀ → ℤ₀` con `ofNat_injective`, `ofNat_add`, `ofNat_mul`.
- **`AczelSetTheory.lean`** (root barrel): añadido `import AczelSetTheory.HFListOps` — era módulo huérfano no importado desde ningún barrel.

**Project status: 0 sorry, 0 errors. 114 non-barrel modules (123 total).**

---

## [2026-05-19] — B3 + VN grupos 1-3 + Bridges + Fase A + Algebra + LinearOrder, 0 sorry

### Added — Operations/Order + Axioms/Order + Axioms/WellOrder (B3)

- **`Operations/Order.lean`**: 24 definiciones de propiedades de relaciones de orden.
- **`Axioms/Order.lean`**: ~28 teoremas (implicaciones, vacío, unicidad, restricción).
- **`Axioms/WellOrder.lean`**: `wf_induction`, `minimum_in_nonempty`, `wo_induction`, `no_infinite_descent`.

**VN Groups 1–3** (12 módulos): SummationVN, SqrtVN, LogVN, DigitsVN, ModEqVN, TotientVN, PrimesVN, CantorPairingVN, PairingVN, NewtonBinomVN, ProductVN, GodelBetaVN.

**VN Bridges** (4 módulos): HFGroupVN (`imageGroup`), ProdBridgeVN (`prodBridge`), MapBridgeVN (`mapBridge`), ListBridgeVN (`listBridge`).

**Fase A — aritmética en HFSet** (3 módulos):

- **`VN/PrimeVN.lean`**: `dvd_HF`, `prime_HF`, `coprime_HF`, TFA existencia/unicidad, Lema de Gauss.
- **`VN/FermatVN.lean`**: Pequeño Teorema de Fermat, Teorema de Wilson.
- **`VN/CRTVN.lean`**: Teorema Chino del Resto.

**Algebra/Group.lean**: `HFAlgebra.HFGroup`, axiomas mínimos izquierdos, 10 lemas derivados.

**Axioms/LinearOrder.lean**: `LT HFSet`, `StrictLinearOrder HFSet` vía `CList.lt` en representantes canónicos.

**Project status: 0 sorry, 0 errors. 113 non-barrel modules.**

---

## [2026-05-18] — B1 + B2 + B3-prep: Rank, GcdVN, FibVN, BinomVN, HFList/FinList, Order.lean, 0 sorry

### Added

- **`Axioms/Rank.lean`** + **`VN/RankVN.lean`**: rango de Von Neumann.
- **`VN/GcdVN.lean`**, **`VN/FibVN.lean`**, **`VN/BinomVN.lean`**: transport de gcd/lcm, Fibonacci, binomio.
- **`HFList.lean`** extendido: `FinList.append/map/zipWith/head/tail`.
- **`HFListOps.lean`** (nuevo): `HFList.toHFSet`, `FinList.toHFSet`, `mem_toHFSet`.
- **`PList/Lemmas.lean`** (+1): `length_zipWith_same`.

**Project status: 0 sorry, 0 errors. 91 modules (non-barrel).**

---

## [2026-05-16] — Axioms/Fintype: tipos finitos scratch-built (F1+F2), 0 sorry

### Added

- **Axioms/Fintype.lean** (nuevo módulo #78): `Finset α` (estructura `val : List α` + `nodup`),
  `Fintype α` (clase con `elems + complete`), `HFSet.toList` (lista canónica de elementos vía
  representante normalizado), `HFSet.toFinset`, `HFSet.membership_fintype` (instancia
  `Fintype {x // x ∈ A}`). Implementación sin Mathlib usando `Quotient.exists_rep` y
  `List.filterMap`. Teoremas: `mem_toList`, `nodup_toList`, `mem_toFinset`.
- **Axioms.lean** barrel: añadido `import AczelSetTheory.Axioms.Fintype`.
- **Documentación**: proyectado en `doc/REFERENCE-HFSets.md` §4.16, §6.16, §7;
  `REFERENCE.md` módulo #78, §4.8–4.16, §4.47, §6.8–6.16, log de proyección.

**Project status: 0 sorry, 0 errors. 78 modules.**

---

## [2026-05-16] — Re-proyección Axioms/VonNeumann — documentación auditada, 0 sorry

### Verified

- **Axioms/VonNeumann.lean**: Re-proyección completa. Definiciones `isTransitive`, `isNat`
  (inductivo con constructores `zero` y `succ`) y 9 teoremas verificados y documentados en
  `doc/REFERENCE-Algebra.md §4.38` y `§6.40`:
  `isTransitive_empty`, `isTransitive_succ`, `isNat_zero`, `isNat_succ`,
  `isNat_zero_or_succ`, `isNat_isTransitive`, `isNat_mem_isNat`, `isNat_pred`,
  `isNat_induction`.

**Project status: 0 sorry, 0 errors, 0 warnings. 73 modules.**

---

## [2026-05-14] — Function composition, identity, product & image — 32 projected modules, 0 sorry

### Added — Operations layer

- **Operations/FunctionComp.lean**: `HFSet.funComp (f g : HFSet) : HFSet` — functional composition of two relations as HFSets. Universe: `𝒫(𝒫(⋃⋃f ∪ ⋃⋃g))`. Notation `infixl:90 " ∘f "`.
- **Operations/Identity.lean**: `HFSet.idFunc (A : HFSet) : HFSet` — identity function on a set.  Separates ordered pairs `⟪a, a⟫` from `𝒫(𝒫(A))`.
- **Operations/Product.lean**: `HFSet.prodHF (A B : HFSet) : HFSet` — Cartesian product. Separates pairs `⟪a, b⟫` with `a ∈ A`, `b ∈ B`. Notation `infixl:80 " ×ₛ "`.

### Added — Axioms layer

- **Axioms/FunctionComp.lean**: 10 theorems: `mem_funComp`, `mem_funComp_pair`, `funComp_isRelation`, `isFunction_funComp`, `mem_domain_funComp`, `mem_range_funComp`, `isInjective_funComp`, `isSurjective_funComp`, `isTotalFunction_funComp`, `isBijective_funComp`.
- **Axioms/Identity.lean**: 15 theorems including identity laws `funComp_idFunc_eq`, `idFunc_funComp_eq` and `relInv_idFunc`.
- **Axioms/Product.lean**: 8 theorems: membership, relation, projection, empty product lemmas, and `isTotalFunction_subset_prodHF`.
- **Axioms/Image.lean**: 7 theorems: `imageRel_subset_range`, `imageRel_mono`, `imageRel_union`, `imageRel_domain_eq_range`, `imageRel_codomain`, `imageRel_funComp`, `imageRel_idFunc`.

### Updated

- **Operations.lean** barrel: now ends with `import AczelSetTheory.Operations.Product`.
- **Axioms.lean** barrel: now ends with `import AczelSetTheory.Axioms.Image`.
- **REFERENCE.md**: projected all 7 new modules (§1, §4.19–4.25, §6.18–6.21, §7, §8, Projection Log).

**Project status: 0 sorry, 0 errors, 0 warnings. 66 leaf modules.**

---

## [2026-05-11] — Phase 1 complete: Peano integration (PList + omega₀) — 25 modules, 0 sorry

### Added — PList: polymorphic list type with ℕ₀ indexing

- **lakefile.lean**: added `require peanolib from git` (Peano natural numbers library).
- **PList/Basic.lean**: `inductive PList (α : Type)` with `length : PList α → ℕ₀`,
  all standard operations (`map`, `filter`, `append`, `flatMap`, `reverse`, `zipWith`,
  `foldl`, `foldr`, `any`, `all`, `get?`, `getD`), Bool and Prop membership
  (`mem`, `Mem`, `Membership` instance), and `toList`/`ofList` bridges to `List`.
- **PList/Lemmas.lean**: 22 `@[simp]` and supporting lemmas including `length_append`,
  `length_filter_le`, `toList_ofList`, `ofList_toList`, `length_toList` (via Λ bridge).
- **PList/Omega0.lean**: `omega₀` tactic macro — transports linear arithmetic goals over
  ℕ₀ to ℕ via `Ψ : ℕ₀ → ℕ`, then calls `omega`. Includes 6 bridge lemmas in
  `namespace PList.Omega0` and 15 verified test cases.
- **PList.lean**: barrel module importing Basic + Lemmas + Omega0.

### Technical notes

- **`+` ambiguity**: `export Peano.Add(add, ...)` makes both `add n m` and `n + m`
  valid elaborations for ℕ₀ addition under `open Peano`. Solution: use `add n m`
  in theorem statements involving `length`.
- **`Membership` argument order**: in Lean 4.29 `Membership.mem` takes container first
  (`γ → α → Prop`). Instance: `⟨fun l a => Mem a l⟩`.
- **`omega₀` / `Nat.add`**: omega does not recognise `Nat.add a b`; `ψ_add` uses
  `@HAdd.hAdd Nat Nat Nat instHAdd` to avoid `Coe Nat ℕ₀` ambiguity and guarantee
  omega compatibility.

**Project status: 0 sorry, 0 errors, 0 warnings. Phase 1 (Peano foundation) complete.**

---

## [2026-04-10] — Powerset axiom complete — 0 sorry project-wide

### Added — Powerset proofs

- **Operations/Powerset.lean**: Proved `sublists_subset`, `filter_in_sublists`, `mem_right_respects_extEq`, `mem_powersetCList`, and `powersetCList_extEq`. Key insight: use `filter (fun z => mem z y)` as sublists witness for the backward direction of `mem_powersetCList`.
- **Axioms/Powerset.lean**: Proved `mem_powerset` by lifting to CList via `Quotient.exists_rep`, reducing to `mem_powersetCList` + `subset_iff_forall_mem_clist`.

### Changed — Project documentation

- Full projection of all Operations/*, Axioms/*, CList/Filter, and Notation modules into REFERENCE.md.
- Updated all .md files to reflect 0 sorry and Phase 5 completion.

**Project status: 0 sorry, 0 errors, 0 warnings. All 8 Zermelo axioms derived.**

---

## [2026-04-07] — Advanced Operations and Powerset Draft

### Added — Union, Intersection, Setminus, Pair, and Powerset operations

- **Union (HFSet.sUnion)**: Extracted from definitions and proved mem_sUnion.
- **Intersection (HFSet.sInter)**: Defined and proved mem_sInter.
- **Setminus (HFSet.setminus)**: Defined and proved mem_setminus.
- **Separation (HFSet.sep)**: Formalized comprehension/separation.
- **Pair (HFSet.mkPair)**: Refactored into Operations/Pair.lean and Axioms/Pair.lean, fully proved.
- **Powerset (Draft)**: Created Operations/Powerset.lean and Axioms/Powerset.lean. Defined computational behavior via CList.sublists. The proofs powersetCList_extEq and mem_powerset remain as sorry for the next session.

---

## [2026-04-06] — Zermelo axioms as derived theorems

### Added — HFSet Zermelo axioms (Extensionality, Empty Set, Pairs)

Derived the first three Zermelo axioms as theorems over HFSet (quotient type),without postulating them:

- **HFSet.Mem**: Membership on HFSet via Quotient.liftOn₂, with proof
  that CList.mem respects xtEq in both arguments.
- **Membership HFSet HFSet instance**: enables x ∈ A notation.
- **mem_mk**: reduction lemma [x] ∈ [A] ↔ CList.mem x A = true.
- **xtensionality**: ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B.
- **
ot_mem_empty**: ∀ x, x ∉ ∅.
- **mkPair / pair / mem_pair**: x ∈ {a, b} ↔ x = a ∨ x = b.

All theorems fully proven. **0 sorry, 0 errors, 0 warnings.**

---

## [2026-04-05] — Module split and sorry elimination

### Changed — Full refactor: CSets.lean → CList sub-modules + HFSets.lean

Completely restructured the project from a single monolithic CSets.lean into  
8 focused modules with Mathlib-style English naming:

- CList/Basic.lean — Core type, size, comparison, order, dedup, sort, normalize
- CList/ExtEq.lean — Extensional equality: reflexivity, transitivity, commutativity
- CList/SetEquiv.lean — Nodup, SetEquiv, dedup properties
- CList/Order.lean — lt: irreflexivity, antisymmetry, totality, transitivity  
- CList/Sort.lean — Sorted, insertionSort preserves sorted/nodup/setEquiv
- CList/Normalize.lean — Size bounds, idempotency, uniqueness
- CList.lean — Root import aggregating all sub-modules
- HFSets.lean — HFSet quotient type, repr, empty

### Fixed —

ormalize_eq_of_extEq sorry eliminated

Proved
ormalize_eq_of_extEq (the last remaining sorry) using well-founded
recursion on cSize A + cSize B, combined with sorted_nodup_setEquiv_eq.

**Project status: 0 sorry across all modules.**

---

## [2026-04-02] — Lean 4.29.0 migration

### Changed — Lean 4.29.0 migration

Migrated the entire project from Lean **4.28.0** to **4.29.0**. The build now
completes successfully (lake build — no errors).
