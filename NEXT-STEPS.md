# Punto de Reanudación (Next Steps)
> Actualizado: 2026-07-20
> **Nota:** nombre canónico con guión (igual que Peano/FOL/ROBINSON_PlusPlus). El histórico
> de milestones cerrados vive en `CHANGELOG.md` y en `git log`; no se duplica aquí.

## Estado Actual (2026-07-20)

- **Build**: 280 jobs ✅ (`lake build AczelSetTheory`), Lean v4.31.0 contra peanolib viva
  (`E:/Dropbox/GitHub/lean4/Peano`, ya cero-Classical tras su ADR-017 Fase C).
- **211 ficheros `.lean`, 35 274 LOC, 14 `sorry`** (ver `make audit` → `AUDIT-MODULE-MATRIX.md`).
- **PUREZA CONSTRUCTIVA TOTAL**: el gate exhaustivo `Meta/AxiomCheck.lean`
  (`#assert_constructive_footprint`, ADR-020) barre las **3239 declaraciones propias** vía
  `Lean.collectAxioms` y falla el build si alguna tiene un axioma fuera de
  `{propext, Quot.sound}` (+ `sorryAx` tolerado). **Baseline de excepciones = 0.**
- **Gobernanza coherente** (ADR-021 §17 opcional/selectivo, ADR-022 O6 desdoblado + `make audit`).
- **MIGRACIÓN DE TIPOS ℤ₀/ℚ₀ COMPLETA** (ADR-023): los tipos titulares `ℤ₀`/`ℚ₀` (estructuras
  que empaquetan clase + representante canónico + coherencia) tienen ya **paridad práctica** con
  las clases `ℤ₀cls`/`ℚ₀cls`:
  - `ℤ₀`: anillo conmutativo ordenado + teoría de números (Möbius/Liouville, biyección ℤ₀≃ℕ₀) +
    homomorfismo `.cls` completo de todas las operaciones.
  - `ℚ₀`: cuerpo ordenado + valor absoluto + inverso/potencia + sucesiones de Cauchy +
    convergencia + propiedad arquimediana + Newton–Raphson + serie de artanh + bisección.
  - Los consumidores reales (`Reals/Incompleteness`, `Series`, `Polynomial`, `Q0Cauchy`,
    `VN/SignVN`) ya están escritos contra los structs.

### 14 `sorry` reales (deuda aceptada, trazada — no bloquean el frente metateórico)
- 1 en `Rationals/Irrational.lean` (`newton_seq_step_bound` — cota de descenso por paso).
- 4 en `Rationals/Polynomial.lean` (canonicalización tras `add`/`smul`/`mul`/`monomial`).
- 6 en `Rationals/Series.lean` (`sum_add`, `sum_mul_left`, `sum_arithmetic`, `sum_geometric`).
- 3 en `Reals/Incompleteness.lean` (irracionalidad algebraica de √2 y convergencia).

## Próximo Objetivo: FRENTE 1 — Análisis Real Constructivo (`HFReal`)

El cimiento está **completo** tras la migración de tipos: `ℚ₀` es un cuerpo ordenado con teoría
de Cauchy, convergencia y arquimedianidad, y `Rationals/Q0CauchyAlgebra.lean` da el álgebra de
sucesiones de Cauchy sobre `ℚ₀` con testigos constructivos de apartness (`Pos`/`ApartZero`).

### Tareas Inmediatas al Reanudar
1. **Definir `HFReal`**: cociente de `ℚ₀.CauchySeq` bajo `CauchySeq.Equiv` (sucesiones cuya
   diferencia tiende a 0). Reutilizar la maquinaria ya existente en `Q0CauchyAlgebra`.
2. **Aritmética en `HFReal`**: levantar `add`/`neg`/`sub`/`mul` (y `inv`/`div` con testigo de
   apartness) desde `ℚ₀.CauchySeq` al cociente.
3. **Estructura de cuerpo ordenado**: instanciar `HFReal` como cuerpo; definir `<`/`≤` vía los
   testigos `Pos`, y el valor absoluto.
4. **Completitud**: trazar el plan para la completitud de Cauchy de `ℝ` (toda sucesión de Cauchy
   de reales converge).

## FRENTE 2 (tras FRENTE 1) — Topología de `HFReal`
Conexidad, compacidad y convergencia real sobre las bases de `AczelSetTheory/Topology/`.
Depende de que `HFReal` exista como tipo; no iniciar antes.

## Deuda pendiente (menor)
- **Merge de `migracion-tipos` → main**: al cierre de la sesión 2026-07-20 la rama estaba
  pusheada; verificar el estado del merge.
- **Cerrar los 14 `sorry`** del frente `Rationals/`·`Reals/` cuando convenga (no bloquean HFReal).
- Los `sorry` de `Incompleteness.lean` requieren valuación p-ádica avanzada o descenso infinito
  en Peano; aparcados para no bloquear el progreso metateórico.
