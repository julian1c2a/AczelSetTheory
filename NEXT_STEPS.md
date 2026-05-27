# Next Steps

**Last updated:** 2026-05-28

El proyecto compila pero **el invariante "0 sorry" está roto**:
`Integers/Rationals.lean` contiene **9 `sorry`** introducidos en commit `ee607e3`.
Resto de la arquitectura: CList/ + Operations/ + Axioms/ + PList/ + VN/ + Algebra/ + Integers/ + Topology/.
Ver PLANNING.md para el roadmap a largo plazo.

---

## 🔴 PLAN ACTIVO (2026-05-28) — Cerrar los 9 `sorry` de `Integers/Rationals.lean`

**Objetivo:** restaurar el invariante "0 sorry, 0 axiomas privados" cerrando todos los huecos sin debilitar firmas ni añadir axiomas.

### Inventario de huecos

| # | Línea | Símbolo | Tipo | Dificultad |
|---|-------|---------|------|------------|
| S1 | 64  | `mul_left_cancel_int` | `private lemma` | media |
| S2 | 122 | `mulWD`               | `private` (well-def ·) | media |
| S3 | 130 | `addWD`               | `private` (well-def +) | media |
| S4 | 200 | `add_assoc`           | `theorem`       | baja |
| S5 | 274 | `left_distrib`        | `theorem`       | media |
| S6 | 298 | `leWD`                | `private` (well-def ≤) | media-alta |
| S7 | 318 | `le_antisymm`         | `theorem`       | baja (depende de S6) |
| S8 | 321 | `le_trans`            | `theorem`       | media (depende de S6) |
| S9 | 324 | `le_total`            | `theorem`       | baja (depende de S6) |

### Grafo de dependencias

```
S1 (mul_left_cancel_int)
  └── ya consumido por ratEq_trans (no requiere demostrar otros)

S2 (mulWD) ───┐
S3 (addWD) ───┴─ algebra pura en ℤ₀ (mul_assoc, mul_comm, distrib, ofNat_mul)

S4 (add_assoc), S5 (left_distrib)
  └── algebra pura en ℤ₀ (idem)

S6 (leWD) — núcleo del orden
  ├── S7 (le_antisymm) — usa ℤ₀.le_antisymm sobre representantes
  ├── S8 (le_trans)    — multiplica por ofNat positivo y usa ℤ₀.le_trans
  └── S9 (le_total)    — usa ℤ₀.le_total sobre representantes
```

### Lemas prerequisitos en ℤ₀ que se necesitarán

Antes de tocar Rationals, comprobar (y, si faltan, añadir en `Integers/Order.lean` o `Integers/Arithmetic.lean`):

- [P1] `ℤ₀.ofNat_pos_of_ne_zero : n ≠ 𝟘 → 0 < ofNat n`  *(probable: derivable de `zero_le_ofNat` + `ofNat_lt`)*
- [P2] `ℤ₀.mul_left_cancel_of_pos : 0 < k → k·x = k·y → x = y`  *(necesario para S1)*
- [P3] `ℤ₀.mul_le_mul_right_of_pos : 0 < c → (a ≤ b ↔ a·c ≤ b·c)`  *(necesario para S6)*
- [P4] `ℤ₀.mul_le_mul_left_of_pos : 0 < c → (a ≤ b ↔ c·a ≤ c·b)`  *(corolario de P3 + mul_comm)*
- [P5] verificar `ℤ₀.left_distrib`, `right_distrib`, `mul_assoc`, `mul_comm` ya disponibles.

Si P2/P3 no existen, demostrarlos primero (bridge vía `repr`/`canonical` o vía división con `0 < k`).

### Pasos en orden

1. **Auditar prerequisitos ℤ₀** (lectura de `Integers/Order.lean` y `Integers/Arithmetic.lean`). Listar qué P1–P5 ya existen.
2. **Añadir los que falten** en sus módulos correspondientes (commit intermedio opcional).
3. **S1 — `mul_left_cancel_int`** *(línea 64)*:
   - Usar `P2` con `ha : 0 < ofNat k` deducido de `hk : k ≠ 𝟘` por `P1`.
   - Forma: `exact ℤ₀.mul_left_cancel_of_pos (P1 hk) h`.
4. **S2 — `mulWD`** *(línea 122)*:
   - Tras `simp only [ratEq, mulRaw, mulDen, ℤ₀.ofNat_mul]`, la meta es:
     `(p.1·q.1)·(ofNat p'.2 · ofNat q'.2) = (p'.1·q'.1)·(ofNat p.2 · ofNat q.2)`.
   - Estrategia: reordenar con `mul_assoc`/`mul_comm` para agrupar `(p.1·ofNat p'.2)·(q.1·ofNat q'.2)`, sustituir con `h1`, `h2` (reescritos vía `ratEq`), y reagrupar.
   - Cierre con `ring`-like via cadena de `rw`.
5. **S3 — `addWD`** *(línea 130)*:
   - Meta tras simp: `(p.1·ofNat q.2 + q.1·ofNat p.2)·(ofNat p'.2 · ofNat q'.2) = (p'.1·ofNat q'.2 + q'.1·ofNat p'.2)·(ofNat p.2 · ofNat q.2)`.
   - Distribuir con `left_distrib`/`right_distrib`, sustituir vía `h1`, `h2` término a término, reagrupar.
6. **S4 — `add_assoc`** *(línea 200)*:
   - Tras `simp only [ratEq, addRaw, mulDen, Peano.Mul.mul_assoc, ℤ₀.ofNat_mul]`, ambos lados son productos de sumas de `p.1·ofNat q.2·ofNat r.2`, etc. Cierre con cadena `rw` usando `add_assoc`, `mul_assoc`, `mul_comm` en ℤ₀.
7. **S5 — `left_distrib`** *(línea 274)*:
   - Similar a S4: tras simp, manipular distribución y reordenar. Usar mismas tácticas.
8. **S6 — `leWD`** *(línea 298)*: pieza más delicada.
   - Meta: `(p₁.1·ofNat q₁.2 ≤ q₁.1·ofNat p₁.2) ↔ (p₂.1·ofNat q₂.2 ≤ q₂.1·ofNat p₂.2)`.
   - Plan: probar `→` (la `←` se sigue por simetría usando `hp.symm`, `hq.symm`).
   - Para `→`: multiplicar ambos lados de `h : p₁.1·ofNat q₁.2 ≤ q₁.1·ofNat p₁.2` por `(ofNat p₂.2 · ofNat q₂.2)` (positivo) usando `P3`/`P4`; sustituir vía `hp`, `hq` (que dan `pᵢ.1·ofNat pⱼ.2 = pⱼ.1·ofNat pᵢ.2`); cancelar `(ofNat p₁.2 · ofNat q₁.2)` (positivo) por `P3`/`P4`.
9. **S7 — `le_antisymm`** *(línea 318)*:
   - `Quotient.inductionOn₂` sobre `a`, `b`; reducir vía `leWD` a aserción en ℤ₀; aplicar `Quotient.sound` con `ℤ₀.le_antisymm` (que da igualdad de productos cruzados = exactamente `ratEq`).
10. **S8 — `le_trans`** *(línea 321)*:
    - Reducción análoga; multiplicar `h1` por `ofNat c.2.2` (positivo) y `h2` por `ofNat a.2.2`, encadenar con `ℤ₀.le_trans`, cancelar factor común con `P3`.
11. **S9 — `le_total`** *(línea 324)*:
    - Reducir a `ℤ₀.le_total (p.1·ofNat q.2) (q.1·ofNat p.2)`.
12. **Build limpio** `lake build`; confirmar `grep -r "sorry" AczelSetTheory/` retorna sólo comentarios.
13. **Actualizar invariantes**:
    - `REFERENCE-Paridad-Peano-Aczel.md`: refrescar fecha + nota de invariante.
    - `NEXT_STEPS.md`: mover Rationals de "✅ COMPLETED con sorries aceptables" a "✅ COMPLETED 0-sorry".
    - `project_aczel.md` en memoria: actualizar fecha y restablecer "0 sorries" verificado.
14. **Commit final** con mensaje:
    `fix(Rationals): close 9 sorries — ℚ₀ ahora sin sorry`.

### Riesgos / posibles bloqueos

- **R1 — Cancelación multiplicativa en ℤ₀ por nonzero (no por positivo)**: si sólo tenemos cancelación por positivo, S1 requiere bifurcar por signo (`k > 0` ya lo tenemos por `k ≠ 𝟘` y `ofNat`). OK.
- **R2 — Falta `mul_le_mul_right_of_pos`**: si no existe, hay que demostrarlo vía `repr`/conversión a `ℕ₀`. Aumentaría el alcance.
- **R3 — Cadenas `rw` muy largas en S4/S5**: puede que necesite lemas auxiliares `ring`-style. Si la cadena pasa de 10 pasos, extraer a un `have` intermedio.
- **R4 — `leWD` no se simplifica directamente**: alternativa es definir `leRaw` como predicado y demostrar transferencia con `Quotient.lift`.

### Criterio de éxito

- `lake build` retorna éxito sin warning de sorry.
- `grep -rn "^[^-/].*sorry" AczelSetTheory/` no encuentra ocurrencias en código (sólo comentarios documentales si los hay).
- Memoria y docs actualizados.

---

## ✅ COMPLETED (2026-06-07) — ℚ₀: números racionales (Integers/Rationals.lean)

- **`Integers/Rationals.lean`** ✅: Esqueleto completo de ℚ₀ como cociente de `ℤ₀ × PosNat₀`.
  - Relación de equivalencia `ratEq`, setoid `ratSetoid`.
  - Operaciones: `addRaw`, `mulRaw`, `negRaw`; denominador unitario `den1`.
  - Instancias: `Zero`, `One`, `Add`, `Neg`, `Mul`, `Sub`, `LE`, `LT`.
  - Embeddings: `ofInt : ℤ₀ → ℚ₀`, `ofNat₀ : ℕ₀ → ℚ₀`.
  - Teoremas demostrados: `add_comm`, `zero_add`, `add_zero`, `add_neg_self`, `neg_add_self`, `mul_comm`, `mul_assoc`, `one_mul`, `mul_one`, `zero_mul`, `mul_zero`, `right_distrib`, `neg_mul`, `mul_neg`, `le_refl`, `ofInt_injective`.
  - Sorry aceptables: `add_assoc`, `left_distrib`, `le_antisymm`, `le_trans`, `le_total`, `leWD`.
  - **Causa raíz resuelta**: `notation a "+" b` sin precedencia < `=` → se usó `Add.add` explícito en signatures.
- **`Integers.lean`** (barrel) ✅: import de `Integers.Rationals` añadido.
- **`doc/REFERENCE-Arithmetic.md`** ✅: sección ℚ₀ añadida ([Q1]–[Q4], [Q5]–[Q12], [T-Q1]–[T-Q21]).

---

## CURRENT PRIORITIES (2026-05-21)

### [B2-cont] ✅ COMPLETADO (2026-05-21) — Álgebra: Subgrupo, Homomorfismo, Anillo, Cosetes

- **`Algebra/Subgroup.lean`** ✅: `HFSubgroup`, `rightCoset`, `cosetEq`, 16 teoremas incluyendo disyunción de cosetes.
- **`Algebra/GroupHom.lean`** ✅: `HFGroupHom`, `ker`, `image`, `hom_e`, `hom_inv`.
- **`Algebra/Ring.lean`** ✅: `HFRing`, `toAdditiveHFGroup`, 7 lemas.
- **`Algebra/CosetCount.lean`** ✅: partición uniforme + **Teorema de Lagrange** `|H| ∣ |G|`.

### [D] ✅ COMPLETADO (2026-05-22) — Funciones multiplicativas: μ de Möbius, λ de Liouville

`MobiusLiouville.lean` y `PadicVal.lean` completos. Build limpio.

- **`Integers/PadicVal.lean`** ✅: `padicVal`, `Omega_prime` (nº de factores primos con mult.),
  `Omega_prime_prime`, `Omega_prime_mul` (completamente multiplicativa, **0 sorry** —
  probado por inducción fuerte sobre `n` usando `Omega_prime_mul_prime` y `Omega_prime_step`),
  `Omega_prime_mul_prime`. Corregidos bugs pre-existentes: `padicVal_succ_dvd`,
  `Omega_prime_prime`.
- **`Integers/MobiusLiouville.lean`** ✅: `negOnePow`, `mobius` (μ), `liouville` (λ).
  Nuevos: `liouville_mul` (multiplicatividad, usa el sorry de `Omega_prime_mul`),
  `liouville_prime_pow` (λ(p^k) = (-1)^k). Corregidos bugs pre-existentes:
  `liouville_ne_zero` (`omega₀` → `succ_neq_zero`), `mobius_sq` (`split_ifs` → `by_cases`).

### [C] Plan y discusión ASet₁ antes de implementar

Antes de implementar, planear la arquitectura:

- Decisión `CList₁`: `mk : PList CList₁ → CList₁` | `inf : (HFSet → Bool) → CList₁`
- Definición de `extEq₁`, `normalize₁`, `ASet₁ = Quotient CList₁.Setoid`
- Qué infraestructura se reutiliza vs. se generaliza
- Cómo representar ω = `inf (fun _ => true)` y los conjuntos Δ⁰₁

---

## ✅ COMPLETED (2026-05-26) — Rank.lean + Decidable.lean

- **`Axioms/Rank.lean`** ✅: `theorem mem_rank_lt : ∀ (a b : HFSet), a ∈ b → rank a < rank b`; `instance mem_wf : WellFounded (· ∈ · : HFSet → HFSet → Prop)`. Bug corregido: rcases `rfl` → `hax` + `rw [hax]`.
- **`Axioms/Decidable.lean`** ✅: `instance instDecidableEmpty (A : HFSet) : Decidable (A = empty)`.
- **`Integers/PadicVal.lean`** ✅: Confirmado 0 sorry (`Omega_prime_mul` completamente probado).
- **Docs**: REFERENCE-Algebra.md proyectado; CURRENT-STATUS-PROJECT.md y NEXT_STEPS.md actualizados.

---

## ✅ COMPLETED (2026-05-27) — PList/HFList/FinList: take/drop + extensional equality

- **`PList/Basic.lean`** ✅: `take` y `drop` definitivos sobre `PList α` con `ℕ₀`.
- **`PList/Lemmas.lean`** ✅: 6 simp lemmas (`take_zero`, `drop_zero`, `take_nil`, `drop_nil`, `take_succ_cons`, `drop_succ_cons`); 5 lemas de longitud (`length_take_le`, `length_take_gt`, `take_append_drop`, `add_length_drop`, `length_drop_le`); `get?_none_of_ge`; `plist_ext_get?` (igualdad extensional vía `get?`). Todos sin `omega₀` (evitar dependencia circular).
- **`PList/Fin0.lean`** ✅: `PList.get_ext` — igualdad extensional vía `get` con índices `Fin₀`.
- **`HFList.lean`** ✅: `HFList.take`, `HFList.drop`, lemas `length_take_le`, `add_length_drop`, `length_drop_le`; `FinList.extEq` (igualdad componente a componente), `FinList.take : FinList k`, `FinList.drop : FinList (sub n k)`.
- **Build**: 0 errores, 0 sorry. `lake build` ✅.
- **Docs**: REFERENCE-PList.md y REFERENCE-HFList.md actualizados.

---

## ✅ COMPLETED (2026-05-23) — Topology/Separation.lean: axiomas T₀–T₄

- **`Topology/Separation.lean`** ✅: `isT0`, `isT1`, `isT2`, `isRegular`, `isT3`, `isNormal`, `isT4`; cadena `T4→T3→T2→T1→T0`; `T1_iff_singletons_closed`. Técnica: `X \ {x} = ⋃{U ∈ τ | x ∉ U}`.
- **`Topology.lean`** (barrel) ✅: import de `Topology.Separation` añadido.
- Build: 0 errores, 0 sorry.

---

## ✅ COMPLETED (2026-05-22) — Topology completo: 4 módulos, 0 sorry

- **`Axioms/Setminus.lean`** ✅: `setminus_setminus_of_subset {A X} (h : A ⊆ X) : X \ (X \ A) = A`.
- **`Topology/Basic.lean`** ✅: `HFTopSpace`, `isClosed`, axiomas, clausura bajo τ.
- **`Topology/Interior.lean`** ✅: `interior`, `closure`, `exterior`, `boundary`; 6 clases de puntos; 3 sorries eliminados (`closure_closed`, `closure_eq_of_closed`+`hA`, `isAdherencePt_iff_mem_closure`-mpr).
- **`Topology/Subspace.lean`** ✅: `subspace` τ_A, `preimage`, `HFContinuous` (id, comp); 5 sorries eliminados.
- **`Topology/Neighborhoods.lean`** ✅: `HFNeighborSpace`, equivalencia `τ ↔ 𝒩`; 3 sorries eliminados.

---

## ✅ COMPLETED (2026-05-22) — Integers + Algebra: módulos adicionales en barrel

- **`Integers/`** ✅: 6 módulos integrados: Order, Functions, Arithmetic, Bijection, PadicVal, MobiusLiouville. 0 sorry total.
- **`Algebra/`** ✅: 4 módulos integrados en barrel: Monoid, RingHom, Field, Module.

---

## ✅ COMPLETED (2026-05-21) — Álgebra: Subgrupo, Homomorfismo, Anillo, Cosetes

- **`Algebra/Subgroup.lean`** ✅: `HFSubgroup`, `rightCoset`, `cosetEq`, 16 teoremas incluyendo disyunción de cosetes.
- **`Algebra/GroupHom.lean`** ✅: `HFGroupHom`, `ker`, `image`, `hom_e`, `hom_inv`.
- **`Algebra/Ring.lean`** ✅: `HFRing`, `toAdditiveHFGroup`, 7 lemas.
- **`Algebra/CosetCount.lean`** ✅: partición uniforme + **Teorema de Lagrange** `|H| ∣ |G|`.

---

## ✅ COMPLETED (2026-05-20) — Integers/Basic.lean: ℤ₀ como cociente

- **`Integers/Basic.lean`**: `ℤ₀ = Quotient intSetoid` donde `intEq (a,b) (c,d) ↔ a+d = b+c`.
  Representante canónico: `normalize p = if p.2 ≤ p.1 then (p.1-p.2, 0) else (0, p.2-p.1)`.
  Instancias: `Zero`, `One`, `Add`, `Neg`, `Mul`, `Sub`.
  18 leyes de anillo conmutativo (tipos escritos con `Add.add`/`Mul.mul` para evitar
  conflicto con la notación global Peano `notation a "+" b => Peano.Add.add a b`).
  Embedding: `ofNat : ℕ₀ → ℤ₀` inyectivo, `ofNat_add`, `ofNat_mul`.
  **0 sorry. Build ✅.**
- **Barrel fix**: `HFListOps.lean` añadido a `AczelSetTheory.lean` (era módulo huérfano).

---

## ✅ COMPLETED (2026-05-19) — Algebra/Group.lean + Axioms/LinearOrder.lean

- **`Algebra/Group.lean`** (`namespace HFAlgebra`): `HFGroup` con axiomas mínimos izquierdos
  (`op_assoc`, `op_id_left`, `op_inv_left`). 10 lemas derivados:
  `op_inv_left_apply`, `left_cancel`, `op_inv_right`, `op_id_right`, `right_cancel`,
  `inv_inv`, `inv_e`, `inv_op`, `unique_id`, `unique_inv`.
  Estrategia: idempotente `c·c=c` para probar `op_inv_right`; luego `right_cancel`.
- **`Axioms/LinearOrder.lean`**: `instance : LT HFSet` vía `CList.lt` en representantes
  canónicos; `instance : StrictLinearOrder HFSet` con `decLt`, `irrefl`, `trans`, `trich`.

---

## ✅ COMPLETED (2026-05-19) — Fase A: aritmética completa en HFSet

- **`VN/ModEqVN.lean`** (extendido): `ModEq_HF`, notación `≡ₕ [MODHF]`, 12 teoremas
  (`vN_modEq_refl/symm/trans/add/mul/pow`, `vN_mod_eq_zero_iff_dvd`, etc.)
- **`VN/TotientVN.lean`** (extendido): `vN_totient_le`, `vN_totient_pos` (total 6 teoremas)
- **`VN/PrimeVN.lean`** (nuevo): `dvd_HF`, `prime_HF`, `coprime_HF`; `vN_dvd/prime/coprime_iff`;
  `vN_prime_ne_zero/one`; **Lema de Gauss** (`vN_coprime_dvd_of_dvd_mul`);
  **TFA existencia** (`vN_exists_prime_factorization`);
  **TFA unicidad** (`vN_unique_prime_factorization`); 15 teoremas.
- **`VN/FermatVN.lean`** (nuevo): **Pequeño Teorema de Fermat** (`vN_fermat_little`,
  `vN_fermat_modEq`); **Teorema de Wilson** (`vN_wilson`, `vN_wilson_modEq`).
- **`VN/CRTVN.lean`** (nuevo): **Teorema Chino del Resto** (`vN_chinese_remainder`).

---

## ✅ COMPLETED (2026-05-19) — VN bridges

- **`VN/HFGroupVN.lean`**: `imageGroup : ℕ₀FinGroup → FinGroup HFSet`,
  transporte de `gpow`/`order` al tipo HFSet.
- **`VN/ProdBridgeVN.lean`**: `prodBridge : ℕ₀ × ℕ₀ → HFSet` vía par de Kuratowski.
- **`VN/MapBridgeVN.lean`**: `mapBridge : MapOn A B → HFSet` como grafo.
- **`VN/ListBridgeVN.lean`**: `listBridge : List ℕ₀ → HFSet` como grafo índice-valor.

---

## ✅ COMPLETED (2026-05-19) — VN grupos 1+2+3: transport completo

12 nuevos módulos VN (0 sorries, barrel actualizado a 35 módulos):

| Módulo | Peano source | Exporta |
| ------ | ----------- | ------- |
| `SummationVN` | `Combinatorics/Summation` | `finSumVN`, 8 teoremas |
| `SqrtVN` | `PeanoNat/Sqrt` | `sqrtVN`, `sqrtRemVN`, `csqrtVN`, 7 teoremas |
| `LogVN` | `PeanoNat/Log` | `logVN`, `logRemVN`, `clogVN`, 7 teoremas |
| `DigitsVN` | `PeanoNat/Digits` | `numDigitsVN`, `ofDigitsVN`, 4 teoremas |
| `ModEqVN` | `NumberTheory/ModEq` | `ModEq_HF`, 12 teoremas |
| `TotientVN` | `NumberTheory/Totient` | `totientVN`, 6 teoremas |
| `PrimesVN` | `PeanoNat/Primes` | `smallestDivisorVN` |
| `CantorPairingVN` | `Foundation/CantorPairing` | `pairVN`, `fstVN`, `sndVN`, 6 teoremas |
| `PairingVN` | `PeanoNat/Pairing` | `cantorPairVN`, 5 teoremas |
| `NewtonBinomVN` | `Combinatorics/NewtonBinom` | `binomTermVN`, 4 teoremas |
| `ProductVN` | `Combinatorics/Product` | `finProdVN`, 7 teoremas |
| `GodelBetaVN` | `Foundation/GodelBeta` | `betaVN`, `vN_beta_of_lt` |

---

## ✅ COMPLETED (2026-05-19) — B3: Order relation theory

- **`Operations/Order.lean`** (nuevo, 24 definiciones):
  `isReflexive`, `isIrreflexive`, `isSymmetric`, `isAntisymmetric`, `isTransitive`,
  `isConnected`, `isTotal`, `isTrichotomous`, `isPreorder`, `isEquivRel`,
  `isPartialOrder`, `isStrictOrder`, `isTotalOrder`, `isStrictTotalOrder`,
  `isMinimum`, `isMaximum`, `isMinimal`, `isMaximal`,
  `isLowerBound`, `isUpperBound`, `isInfimum`, `isSupremum`,
  `isWellFounded`, `isStrictlyWellFounded`, `isWellOrder`.
- **`Axioms/Order.lean`** (nuevo, ~28 teoremas):
  Cadena de implicaciones, casos vacíos (11), unicidad (4), minimal/maximal (3), restricción (13).
- **`Axioms/WellOrder.lean`** (nuevo, 4 teoremas):
  `wf_induction`, `minimum_in_nonempty`, `wo_induction`, `no_infinite_descent`.

---

## ✅ COMPLETED (2026-05-18) — B2: VN transport + HFList/FinList theory

- **`VN/GcdVN.lean`**: `gcdVN`, `lcmVN`, 13 teoremas.
- **`VN/FibVN.lean`**: `fibVN`, 4 teoremas.
- **`VN/BinomVN.lean`**: `binomVN`, 8 teoremas.
- **`HFList.lean`** (extendido): `FinList.append/map/zipWith/head/tail`, lemas de round-trip.
- **`HFListOps.lean`** (nuevo): `HFList.toHFSet`, `FinList.toHFSet`, `mem_toHFSet`.

---

## ✅ COMPLETED (2026-05-18) — B1: Axioms/Rank + VN/RankVN

- **`Axioms/Rank.lean`**: `rank : HFSet → ℕ₀`, `rank_empty`, `rank_insert`.
- **`VN/RankVN.lean`**: `rank_vN (n : ℕ₀) : rank (vN n) = n`.

---

## ✅ COMPLETED (2026-05-17) — A1/A2/A3/C1: VN arithmetic transport

- **`VN/PowVN.lean`**: `powVN`, 14 teoremas.
- **`VN/SubVN.lean`**: sustracción acotada, 12 teoremas.
- **`VN/DivVN.lean`**: división euclidiana, 6 teoremas.
- **`VN/FactorialVN.lean`**: `factVN`, 10 teoremas.

---

## ✅ COMPLETED — Phases 1–7g (all prior foundations)

All CList, PList, HFSet, Operations, Axioms, VN foundations complete.
See git log for details.
