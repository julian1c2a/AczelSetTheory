# Next Steps

**Last updated:** 2026-06-03

---

## 🔴 ACTIVO — M2B: Completar AbsVal.lean (sprint en curso)

### Diagnóstico: por qué falla `absVal_add_le` dentro de `namespace ℚ₀`

`peanolib/Peano.lean` usa `export Peano.Add (add ...)` y `export Peano.Order (le_trans ...)`
para exponer nombres Peano en el namespace **raíz**. Esto significa que en cualquier archivo
que importe peanolib, los nombres `add`, `le_trans`, `le_total`, etc. están en el namespace
raíz. Cuando dentro de `namespace ℚ₀` se definen helpers privados en el namespace raíz y se
los llama desde dentro del namespace, la resolución de instancias puede confundirse entre
`Add.add : ℕ₀ → ℕ₀ → ℕ₀` (Peano, exportado) y `Add.add : ℚ₀ → ℚ₀ → ℚ₀`.

### Regla de infraestructura derivada

> **Regla M2B-01**: Los teoremas que usan `add_le_add_left/right` de ℚ₀ y
> llaman a helpers privados del namespace raíz deben definirse **fuera** de
> `namespace ℚ₀`, usando nombres completamente cualificados (`ℚ₀.foo`).

### Sub-tareas M2B restantes

| ID | Estado | Tarea |
|----|--------|-------|
| M2B-1 | ✅ DONE | `absVal_sub_comm` — compila sin errores |
| M2B-2 | ✅ DONE | `absVal_mul` — compila sin errores |
| M2B-3 | ❌ TODO | `absVal_add_le` — mover fuera de `namespace ℚ₀` |
| M2B-4 | ❌ TODO | Build completo AczelSetTheory + auditoría 0-errores |
| M2B-5 | ❌ TODO | Commit + push M2B |

### Plan concreto para M2B-3

Extraer de `namespace ℚ₀`:
1. `private theorem le_absVal` → `private theorem q0_le_absVal` al nivel raíz,
   con referencias `ℚ₀.absVal_of_nonneg`, `ℚ₀.le_refl`, `ℚ₀.le_total`, etc.
2. `theorem absVal_add_le` → `theorem ℚ₀.absVal_add_le` al nivel raíz, usando
   `ℚ₀.absVal_of_nonneg`, `ℚ₀.neg_add`, `q0_add_le_add_left`, `ℚ₀.le_trans`, etc.

---

## 🔵 PENDIENTE — M3B: Sucesiones de Cauchy diádicas

**Archivo**: `AczelSetTheory/Reals/IsCauchy.lean`

Sub-tareas:

| ID | Tarea |
|----|-------|
| M3B-1 | `pow2 : ℕ₀ → ℚ₀` — potencias de 2 en ℚ₀ |
| M3B-2 | `IsCauchy (f : ℕ₀ → ℚ₀) : Prop` — |f(n) - f(m)| ≤ 1/2^n para n ≤ m |
| M3B-3 | `IsCauchy₂ (f : ℕ₀ → ℚ₀) : Prop` — def alternativa con 2^(-n) y 2^(-m) |
| M3B-4 | `isCauchy_iff_isCauchy₂` — equivalencia entre las dos definiciones |
| M3B-5 | Build + commit M3B |

**Infraestructura necesaria antes de M3B**:
- `absVal_add_le` (M2B-3) — para probar que suma de Cauchy es Cauchy

---

## 🔵 PENDIENTE — M4B: Representación canónica en ℚ₀

`AczelSetTheory/Reals/CanonicalRep.lean`: `canonicalRep`, `repr`, `Decidable` en ℚ₀.

---

## 🔵 PENDIENTE — M5B: ℤ/Nℤ y campos finitos

`AczelSetTheory/Integers/ZModN.lean`: Bezout extendido → ZModN → IsField (ZModN p).

---

**Last updated (original):** 2026-06-05

🎉 **FASE A — Paridad Peano: COMPLETA (2026-06-05).** El proyecto compila con
invariante "0 sorry, 0 axiomas privados, 0 warnings". Todos los milestones M1–M7 cerrados.
Resto de la arquitectura: CList/ + Operations/ + Axioms/ + PList/ + VN/ + Algebra/ + Integers/ + Topology/.
Ver PLANNING.md para el roadmap a largo plazo (FASE B en adelante).

---

## ⚠️ Directiva maestra (2026-05-30): Peano congelado — teoría nueva en Aczel

**Peano (`peanolib`) no desarrollará más teoría "hacia arriba"** — solo fundamentos
(aritmética de Robinson `Q` / **ROBINSON_PlusPlus**). **Toda la teoría nueva** se construye
**directamente sobre `HFSet` en AczelSetTheory**, capa nativa (p.ej. `Combinatorics/`),
*no* vía transporte `VN/`. Stubs `VN/CountingVN.lean`, `VN/SignVN.lean` huérfanos. Ver
`DECISIONS.md` → ADR-000.

---

## ✅ COMPLETADO — M7 Lema de la Mariposa de Zassenhaus — 2026-06-05

`Algebra/Zassenhaus.lean` (NUEVO, ~727 líneas): prueba completa de
`(H∩K)/[(N∩K)(H∩M)] ≅ N(H∩K)/N(H∩M)`.
- Públicos: `prodSubgroup`, `mem_prodSubgroup_iff`, `prodNKHM`, `prodN_HK`, `prodN_HM`,
  normalidades correspondientes y `zassenhaus_bijection`.
- Build: 35 jobs, 0 errores, 0 warnings, 0 sorries.
- M7 ✅ → **FASE A cerrada.**

---

## ✅ COMPLETADO — Sylow II (punto fijo del p-grupo) — 2026-06-04

`Algebra/Sylow.lean` §36-bis + §37: sorry cerrado en `sylowConjugate.hfixed`.
- `p_group_fixed_point`: demostrado por inducción fuerte sobre `|X|`.
- `sylowConjugate`: completo, 0 sorries. M6 ✅.

---
  - `Modulos con placeholder/stub: 11`
- **Build:** `lake build` ✅ (35 jobs).

## ✅ COMPLETED (2026-06-02) — Sprint D1: bloque VN inicial placeholder/stub

- Cierres aplicados en:
  - `VN/PermVN.lean`
  - `VN/OrbitVN.lean`
  - `VN/CountingVN.lean`
  - `VN/SignVN.lean`
- Matriz regenerada tras cada cierre de bloque.
- Estado consolidado en `AUDIT-MODULE-MATRIX.md`:
  - `noncomputable def: 0`
  - `Modulos con TODO/PENDIENTE/FIXME: 0`
  - `Modulos con placeholder/stub: 7`

## ✅ COMPLETED (2026-06-02) — Sprint D2: bloque VN residual placeholder/stub

- Cierres aplicados en:
  - `VN/ActionVN.lean`
  - `VN/CorrespondenceTheoremVN.lean`
  - `VN/FirstIsomorphismVN.lean`
  - `VN/SecondIsomorphismVN.lean`
  - `VN/ThirdIsomorphismVN.lean`
  - `VN/QuotientGroupVN.lean`
  - `VN/NormalSubgroupVN.lean`
- Matriz regenerada tras cada cierre individual del bloque residual.
- Estado consolidado en `AUDIT-MODULE-MATRIX.md`:
  - `noncomputable def: 0`
  - `Modulos con TODO/PENDIENTE/FIXME: 0`
  - `Modulos con placeholder/stub: 0`

### Siguiente foco inmediato

1. Retomar trabajo sustantivo de paridad/extensión (GroupTheory pendiente y capa nativa `Combinatorics/`) con auditoría incremental por bloque.
2. Mantener proyección documental sincronizada tras cada cierre de bloque (matriz + planning + reference + changelog).

---

## ✅ COMPLETED (2026-05-30) — Sylow I §33–§40 + Lean v4.30.0 + Combinatorics nativo

### Primer Teorema de Sylow (`Sylow.lean` §33–§40)

`sylow_first` demostrado sin `sorry`. `#print axioms sylow_first` → `[propext,
Classical.choice, Quot.sound]` (sin sorryAx). `lake build AczelSetTheory` → 0 sorries.

```lean
theorem sylow_first (grp : HFGroup) (p k : ℕ₀)
    (hp : Peano.Arith.Prime p) (hdvd : p ^ k ∣ HFSet.card grp.G) :
    ∃ sub : HFSubgroup grp, HFSet.card sub.H = p ^ k
```

Inducción fuerte sobre `|G|`; caso `k = σ m` con 3 ramas: (1) ∃ M propio p-divisible
→ HI + `subgroupOfSubgroup`; (2) `|G| = p^k` → `improperSubgroup`; (3) `p ∣ |Z(G)|`
(ecuación de clases) → Cauchy en Z(G) → cociente `G/N` + preimagen `π⁻¹`.

Fixes de compilación aplicados (detalle técnico en memoria `feedback_lean.md`):
§35 `^`=HPow≠Peano.Pow (puente `pow_def`); §36 dirección `mem_center_iff` y `⊆` con
elemento explícito; §37 reescrito sin `k.pred`/`pow_succ_eq`; §38 intro order de
`isNormal`; §39 `mul_cancelation`; §40 `Prime` explícito, `strongInductionOn` con
`refine`, construcción `N` directa. Eliminado código muerto `mul_div_dvd_iff`.

### Lean v4.30.0 (bump desde v4.29.1)

`lean-toolchain` → v4.30.0 (última estable). peanolib (repo Peano) también bumpeado:
`ConstructiveCheck.lean` migrado de `CollectAxioms.collect` (privado en 4.30) a la API
pública `Lean.collectAxioms`. Script `update-toolchain.bash` mejorado (consulta GitHub
API + verifica lib completa). Rutina `/schedule` semanal vigila nuevas versiones.

### Combinatorics nativo (ADR-000)

Nueva capa `AczelSetTheory/Combinatorics/` (teoría nativa, no transporte VN):
- `HFSet.pigeonhole`: f función-clase A→B inyectiva → `card A ≤ card B`.
- `HFSet.exists_collision_of_card_lt`: `card B < card A` → ∃ colisión `x≠y`.

### Lecciones técnicas clave (resumen; completo en `feedback_lean.md`)

1. `^` en Sylow resuelve a `HPow.hPow`, no `Peano.Pow.pow` → puente `pow_def`.
2. `Prime` ambiguo con `open Peano.Arith Peano.Primes` → `Peano.Arith.Prime` explícito.
3. `⊆` en HFSet = `∀ x, x∈A → x∈B`: subset toma elemento explícito (`h x hx`).
4. `isNormal` = `∀ (g n), g∈G → n∈H → …`: intro `g n hg hn`.
5. `prime_ge_two` da `le₀ 𝟚 p`, no `lt₀ 𝟙 p` → puente vía `succ_lt_succ_iff`.
6. `strongInductionOn`: `refine (… ?_ args)`, no `apply … args`.
7. `by_contra` NO existe sin Mathlib → `Classical.byContradiction`.
8. Migración toolchain: APIs internas (`CollectAxioms.collect`) cambian; usar las
   públicas (`Lean.collectAxioms`). Lake compila deps git con el toolchain del raíz.

### Referencias rápidas (lemas peanolib/HFSet verificados)

| Símbolo | Ubicación | Firma |
|---------|-----------|-------|
| `pow_def` | Combinatorics/Pow.lean:402 | `a ^ b = Peano.Pow.pow a b` |
| `pos_of_ne_zero` | StrictOrder.lean:174 | `n ≠ 𝟘 → lt₀ 𝟘 n` |
| `nlt_of_le` | Order.lean:1430 | `le₀ a b → ¬ lt₀ b a` |
| `succ_lt_succ_iff` | StrictOrder.lean:336 | `lt₀ (σ n) (σ m) ↔ lt₀ n m` |
| `le_iff_lt_or_eq` | Order.lean:1418 | `le₀ a b ↔ lt₀ a b ∨ a = b` |
| `div_mul_cancel` | Arith.lean:800 | `b ≠ 𝟘 → b ∣ a → mul (a/b) b = a` |
| `mul_cancelation_left/right` | Mul.lean:163/200 | cancelación por factor ≠ 𝟘 |
| `card_le_of_subset` | OrdinalNat.lean:47 | `A ⊆ B → card A ≤ card B` |
| `card_classImage_inj` | CardImage.lean:39 | inyectiva → `card(img) = card A` |
| `card_eq_of_classBij` | CardImage.lean:110 | biyección-clase → `card A = card B` |
| `card_eq_zero_iff` | Cardinal.lean:148 | `card A = 𝟘 ↔ A = empty` |
| `cauchy_minimal` | Sylow.lean:§32 | `Prime (σ n) → σ n ∣ card G → ∃ sub, card = σ n` |
| `subgroupOfSubgroup` | Sylow.lean:§33 | `sub₂ : Subgrp sub₁.G → Subgrp G` |
| `card_preimage_mul` | Sylow.lean:§34 | `card(π⁻¹ Q) = mul (card Q.H) (card N.H)` |

---

## ✅ COMPLETED (2026-05-29) — Cauchy vía McKay: §28–§32 [`Sylow.lean`]

Completado el **Teorema de Cauchy** mediante el argumento combinatorio de McKay. 0 sorry, 0 warnings.

| § | Teorema | Descripción |
|---|---------|-------------|
| §28 | `eTuple_mem_mckayFixedPoints` | `eTuple grp p ∈ mckayFixedPoints grp p` |
| §29 | `mckayShift_succ_pair` (priv.) | Reducción del shift en pares anidados |
| §29 | `shift_fixed_snd_e_implies_eTuple` (priv.) | `snd t = e ∧ shift-fijo → t = eTuple` |
| §29 | `shift_fixed_tupleProd_eq_gpow` (priv.) | `tupleProd t = gpow (snd t) p` si t fijo |
| §30 | `order_dvd_of_gpow_eq_id` | `g^m = e → order g ∣ m` |
| §30 | `order_eq_prime_of_pow` | primo `p`, `g^p = e`, `g ≠ e` → `order g = p` |
| §31 | `cyclicCarrier_card_eq_order` | `card(⟨g⟩) = order g` |
| §32 | **`cauchy_minimal`** | primo `p`, `p ∣ \|G\|` → `∃ sub, card sub = p` |

Técnicas clave:
- `Classical.byContradiction` (no `by_contra` — no disponible sin Mathlib).
- `intro h; subst h` para derivar `n ≠ 𝟘` desde `hp : Peano.Arith.Prime (σ n)`.
- Sin `let`/`set` (causan type mismatch en have-types sin Mathlib).
- `mckayFixedPoints_subset grp p t ht` — el elemento `t` es argumento explícito.

**Build:** `lake build` → 228 jobs ✅, 0 sorry, 0 warnings.

---

## ✅ COMPLETED (2026-05-29) — D.4.D McKay: `σ n ∣ card(mckayFixedPoints)` [`Sylow.lean` §24–§27]

Cerrado el argumento combinatorio de McKay completo (D.4.D). Todos los §§ sin sorry:

| § | Teorema | Descripción |
|---|---------|-------------|
| §24 | `periodOf_eq_one_iff_fixed` | `period = 1 ↔ mckayShift t = t` |
| §24 | `card_orbitOf_eq_one_iff_fixed` | `card(orbit) = 1 ↔ t fijo` |
| §25 | `card_orbitOf_eq_succ_of_not_fixed` | primo + ¬fijo → `card(orbit) = σ n` |
| §26 | `succ_n_dvd_card_of_shift_closed_no_fixed` | WOP sobre `card S` → `σ n ∣ card S` |
| §27 | `succ_n_dvd_card_mckayFixedPoints` | **D.4.D / Lema de McKay**: `σ n ∣ card(fixedPoints)` |

---

## ✅ PLAN APROBADO (2026-05-28) — Paridad Peano: orden de ejecución

**Estado:** Propuesta aprobada por el usuario el 2026-05-28. Procedemos a ejecución.

### Decisiones fijadas

| # | Pregunta | Decisión |
|---|---|---|
| Q1 | ¿Paralelizar milestones independientes? | **Sí**, paralelizamos donde el grafo lo permita. |
| Q2 | ¿Puente o redemostrar iso theorems (H7–H11)? | **Opción A — especializar abstracto a vN.** Redemostramos sólo si la especialización falla. |
| Q3 | `PermVN` como `Fin n → Fin n` o como `SymVN`? | **Opción A — `PermVN n := SymVN n`** y trabajamos módulo isomorfismo. |
| Q4 | ¿Bundle de iso theorems? | **Agrupamos** H8/H9/H10 en un único `VN/IsomorphismsVN.lean`; H11 (Correspondence) por separado. |
| Q5 | ¿Antes o después de Sylow atacar ℚ₀ extendido? | **Después.** Cerramos los 7 hitos M1–M7 íntegros antes de tocar Racionales. |

### Orden de ejecución acordado

| Paso | Huecos | Hito | Notas |
|------|--------|------|-------|
| 1 | H1 (Counting) | **M1** | Sin dependencias VN nuevas. Arranca aquí. |
| 2 | H6 (NormalSubgroup puente) | **M4 (1ª parte)** | Adelantado: desbloquea H7 antes de M2/M3. |
| 3–4 | H2 (Perm), H3 (Sign) | **M2** | Paralelizable con paso 5–6. |
| 5–6 | H5 (Action), H4 (Orbit) | **M3** | + ActionVN como prerequisito explícito. |
| 7 | H7 (QuotientGroup) | **M4 (2ª parte)** | Cierra M4. |
| 8 | H8, H9, H10 (3 iso theorems) | **M5 (1ª parte)** | Bundle en `IsomorphismsVN.lean`. |
| 9 | H11 (Correspondence) | **M5 (2ª parte)** | Módulo separado. |
| 10 | H13, H14, H15 (Sylow ×3) | **M6** | El bloque más denso. |
| 11 | H12 (Zassenhaus) | **M7** ✅ | Cierre de paridad. **Completado 2026-06-05** (`Algebra/Zassenhaus.lean`). |
| 12 | Schreier, Jordan-Hölder | **MFUTURE** | Fuera de paridad Peano; aplazado. |

### Paralelización aplicable

- **M2 ‖ M3:** una vez completado el paso 2 (H6), M2 (Perm+Sign) y M3 (Action+Orbit) son independientes; se pueden alternar o atacar en ramas paralelas.
- **M5 (paso 8) ‖ M5 (paso 9):** H8/H9/H10 (bundle iso) y H11 (Correspondence) son independientes una vez cerrado H7.

### Tareas de mantenimiento — orden acordado

Antes de tocar ℚ₀ extendido en la Fase B:

1. **T1 — auditar** los ⚠️ residuales (WellFounded §1, EquivRel §6) y decidir caso por caso si se formalizan como módulo VN o se aceptan como "embebidos".
2. **T2 — migrar** `Algebra/CosetCount.lean` (Lagrange abstracto) a un puente VN explícito tras cerrar M4.
3. **T3 — actualizar** `PLANNING.md` y `REFERENCE-Paridad-Peano-Aczel.md` tras cada milestone con: lecciones aprendidas + recálculo de estimación.

### Próxima acción inmediata

**FASE A completa.** Próximo paso: definir prioridades de FASE B (consolidación post-paridad) según `PLANNING.md` §🅱️. Candidatos: ℚ₀ extendido (B1), bridge `ℤ₀ ↔ HFInt` (B2), anillos cocientes concretos (B3), o cierre documental (B4).

---

## 🎯 PROPUESTA (2026-05-28) — Plan de Paridad Peano (corto/medio plazo)

**Objetivo declarado:** que AczelSetTheory **recubra completamente** todos los teoremas de Peano. Hoy quedan ~15 módulos Peano sin equivalente VN (ver `doc/REFERENCE-Paridad-Peano-Aczel.md`).

### Inventario de huecos (estado 2026-05-28)

| # | Módulo Peano | Estado | Módulo VN propuesto | Bloqueante de |
|---|---|---|---|---|
| H1 | `Combinatorics/Counting.lean` | ❌ | `VN/CountingVN.lean` | Sylow, Orbit, ecuación de clases |
| H2 | `Combinatorics/Perm.lean` | ❌ | `VN/PermVN.lean` | Sign, Orbit, Sₙ concreto |
| H3 | `Combinatorics/Sign.lean` | ❌ | `VN/SignVN.lean` | Aₙ, determinante (futuro) |
| H4 | `Combinatorics/Orbit.lean` | ❌ | `VN/OrbitVN.lean` | Sylow |
| H5 | `GroupTheory/Action.lean` | ❌ | `VN/ActionVN.lean` | Orbit, Sylow |
| H6 | `GroupTheory/NormalSubgroup.lean` | ⚠️ | `VN/NormalSubgroupVN.lean` (puente) | QuotientGroup concreto |
| H7 | `GroupTheory/QuotientGroup.lean` | ⚠️ | `VN/QuotientGroupVN.lean` | Iso theorems concretos |
| H8 | `GroupTheory/FirstIsomorphism.lean` | ⚠️ | `VN/FirstIsoVN.lean` | — |
| H9 | `GroupTheory/SecondIsomorphism.lean` | ⚠️ | `VN/SecondIsoVN.lean` | — |
| H10 | `GroupTheory/ThirdIsomorphism.lean` | ⚠️ | `VN/ThirdIsoVN.lean` | — |
| H11 | `GroupTheory/CorrespondenceTheorem.lean` | ⚠️ | `VN/CorrespondenceVN.lean` | — |
| H12 | `GroupTheory/Zassenhaus.lean` | ✅ | `Algebra/Zassenhaus.lean` | Schreier (futuro) |
| H13 | `GroupTheory/Sylow/CosetAction.lean` | ✅ | `Algebra/Sylow.lean` (§9–§27) | McKay carrier + shift + orbitOf + D.4.D completo. |
| H14 | `GroupTheory/Sylow/Cosets.lean` | ✅ | `Algebra/Sylow.lean` (§12–§27) | shiftIter, periodOf, orbitOf, card_orbitOf_eq_periodOf, card ∈ {1,p}, D.4.D. |
| H15 | `GroupTheory/Sylow/Sylow.lean` | 🟡 | `Algebra/Sylow.lean` (parcial) | McKay lema ✅. **Pendiente:** cauchy_minimal + sylow_lift + Sylow I-III. |

### Grafo de dependencias

```
H1 Counting ──┐
              ├──► H2 Perm ──► H3 Sign
              │
              └──► H5 Action ──► H4 Orbit ──┐
                                            │
H6 NormalSubgroup ──► H7 QuotientGroup ──► H8/H9/H10 Iso ──► H11 Correspondence
                                            │
                                            └──► H13/H14/H15 Sylow ──┐
                                                                     ├──► H12 Zassenhaus
                                                                     │
                                                                     └──► (Schreier, Jordan-Hölder)
```

### Hitos propuestos (en orden ejecutable)

- **M1 — Counting (H1).** Pigeonhole, inclusión-exclusión sobre `vN`. Sin dependencias VN nuevas. **Coste:** 1–2 sesiones.
- **M2 — Perm + Sign (H2, H3).** Permutaciones `Fin n → Fin n` transportadas; `sgn` con valores en `{+1, -1} ⊂ ℤ₀`. **Coste:** 2–3 sesiones. *Aprovecha ℤ₀ ya cerrado.*
- **M3 — Action + Orbit (H5, H4).** Acción de `HFGroup` sobre HFSet; ecuación de clases. **Coste:** 2 sesiones.
- **M4 — QuotientGroup concreto (H6, H7).** Puente desde `HFNormalSubgroup` abstracto a `vN`. **Coste:** 1–2 sesiones.
- **M5 — Teoremas de isomorfismo VN (H8, H9, H10, H11).** Concretizar los abstractos ya existentes. **Coste:** 2 sesiones (mayormente especialización).
- **M6 — Sylow (H13, H14, H15).** El más pesado: tres pasos clásicos (existencia, conjugación, conteo). **Coste:** 4–6 sesiones.
- **M7 — Zassenhaus (H12).** Lema sandwich. **Coste:** 1 sesión post-Sylow. ✅ **Completado 2026-06-05.**

**Estimación total:** ~14–18 sesiones para cierre completo de paridad.

### Preguntas abiertas para discutir

1. **¿Orden estricto o paralelizable?** M2 y M3 son independientes; ¿paralelizamos para reducir wall-clock?
2. **¿Hacer "puente" o "redemostrar"?** Para H7–H11 (iso theorems) ya tenemos versión abstracta en `Algebra/`. **Opción A:** especializar el abstracto a `vN` (rápido, frágil si cambia el abstracto). **Opción B:** redemostrar desde cero sobre VN (verboso pero auto-contenido). *Yo recomendaría A salvo donde falle.*
3. **¿`PermVN` como `Fin n → Fin n` o como subconjunto de `Sym(vnSeg n)`?** Ya tenemos `VN/SymGroupVN.lean`. **Opción A:** `PermVN n := SymVN n` y trabajamos modulo isomorfismo. **Opción B:** mantener `PermVN` separado como puente concreto. *Necesito tu lectura aquí.*
4. **¿Bundle de iso theorems en un solo módulo `VN/IsomorphismsVN.lean`?** Los tres juntos son ~300 líneas; separados se duplica boilerplate. *Yo agruparía.*
5. **¿Antes o después de Sylow, atacar `Integers/Rationals` extendido?** ℚ₀ existe pero falta densidad, completitud parcial, valor absoluto. Esto **no** es paridad Peano (Peano no tenía ℚ), pero el usuario podría querer cerrarlo antes. *Pregunto.*

### Criterio de éxito del bloque

- Tabla §1–§4 del REFERENCE de paridad con **0 ❌** (sólo ✅ y 🆕).
- `lake build` ✅, 0 sorry, 0 axiomas privados.
- Cada módulo nuevo con su entrada en `doc/REFERENCE-Paridad-Peano-Aczel.md`.

---

## 📋 Tareas de mantenimiento (paralelas, baja prioridad)

- **T1.** Auditar los ⚠️ residuales en `WellFounded` (§1) y `EquivRel` (§6) — ¿formalizar como módulo VN o aceptar como "embebido"?
- **T2.** Migrar `Algebra/CosetCount.lean` (Lagrange abstracto) a un puente VN explícito una vez completado M4.
- **T3.** Actualizar `PLANNING.md` con un check-in tras cada milestone.

---

## ✅ COMPLETED (2026-05-28) — Cierre de los 9 `sorry` de `Integers/Rationals.lean`

Cerrados todos los huecos S1–S9 sin debilitar firmas ni añadir axiomas:

| # | Símbolo | Estrategia |
|---|---------|------------|
| S1 | `mul_left_cancel_int` | delegación directa a `ℤ₀.mul_left_cancel_ofNat` |
| S2 | `mulWD` | helper `mul_swap_inner` + `h1`/`h2` |
| S3 | `addWD` | `show … from rfl` (HAdd→Add) + `right_distrib` + `congr 1` + cadenas `mul_swap_inner` |
| S4 | `add_assoc` | `show` HAdd→Add + `right_distrib` x2 + cadena `mul_assoc`/`mul_comm` + `add_assoc` |
| S5 | `left_distrib` | `show` HAdd→Add + `left_distrib` + `right_distrib` x2 + cadenas `← mul_assoc` + `mul_swap_inner` |
| S6 | `leWD` | dos `have key1`/`key2` con `mul_le_mul_right_ofNat_pos` + `ofNat_mul` + `mul_swap_inner` + `hp`/`hq`; cierre por `Iff.trans` |
| S7 | `le_antisymm` | `Quotient.inductionOn` x2 + `Quotient.sound` + `ℤ₀.le_antisymm` |
| S8 | `le_trans` | multiplica `h1` por `ofNat r.2`, `h2` por `ofNat p.2`; reordena con `mul_assoc`/`mul_comm`; encadena con `ℤ₀.le_trans`; cancela por `q.2` |
| S9 | `le_total` | reducción directa a `ℤ₀.le_total` |

**Prerrequisitos añadidos en `Integers/Basic.lean` y `Integers/Order.lean`** (commit previo): `mul_left_cancel_ofNat`, `mul_le_mul_right_ofNat_pos`, `mul_le_mul_left_ofNat_pos`, `ofNat_mul`, `repr_mul_ofNat_intEq`.

**Verificación:** `lake build` → 35/35 jobs ✅, sin warnings de sorry; `grep -r "sorry" AczelSetTheory/` → 0 ocurrencias.

---

## ✅ COMPLETED (2026-06-07) — ℚ₀: esqueleto inicial (Integers/Rationals.lean)

- **`Integers/Rationals.lean`** ✅: Esqueleto completo de ℚ₀ como cociente de `ℤ₀ × PosNat₀`.
  - Relación de equivalencia `ratEq`, setoid `ratSetoid`.
  - Operaciones: `addRaw`, `mulRaw`, `negRaw`; denominador unitario `den1`.
  - Instancias: `Zero`, `One`, `Add`, `Neg`, `Mul`, `Sub`, `LE`, `LT`.
  - Embeddings: `ofInt : ℤ₀ → ℚ₀`, `ofNat₀ : ℕ₀ → ℚ₀`.
  - Teoremas demostrados: `add_comm`, `add_assoc`, `zero_add`, `add_zero`, `add_neg_self`, `neg_add_self`, `mul_comm`, `mul_assoc`, `one_mul`, `mul_one`, `zero_mul`, `mul_zero`, `left_distrib`, `right_distrib`, `neg_mul`, `mul_neg`, `le_refl`, `le_antisymm`, `le_trans`, `le_total`, `ofInt_injective`.
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
