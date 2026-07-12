# Punto de Reanudación (Next Steps)
> Actualizado: 2026-07-12
> **Nota:** este fichero sustituye a `NEXT_STEPS.md` (guión bajo, borrado el
> 2026-07-12 tras la auditoría cruzada — ver INFORME-AUDITORIA-2026-07-12.md).
> Ambos coexistían de forma contradictoria; éste es el vigente (nombre canónico
> con guión, igual que en Peano/FOL/ROBINSON_PlusPlus). El histórico completo de
> milestones cerrados que llevaba `NEXT_STEPS.md` (M1B–M8B, Sylow, Zassenhaus,
> etc.) vive en `CHANGELOG.md` y en `git log`; no se duplica aquí.

## Estado Actual (2026-07-12)
- **FRENTE 4 (Racionales y Secuencias de Cauchy)**: COMPLETADO.
- **14 `sorry` reales** en el árbol (no 4 — recuento corregido tras la auditoría
  cruzada 2026-07-12, ver CURRENT-STATUS-PROJECT.md § Known Sorry Locations):
  - 1 en `Irrational.lean:353` (`newton_seq_step_bound` — cota de descenso por paso).
  - 4 en `Polynomial.lean` (canonicalización tras `add`/`smul`/`mul`/`monomial`).
  - 6 en `Series.lean` (`sum_add`, `sum_mul_left`, `sum_arithmetic`, `sum_geometric`).
  - 3 en `Incompleteness.lean` (irracionalidad algebraica profunda de $\sqrt{2}$ y convergencia).
- *Deuda técnica*: los 3 de `Incompleteness.lean` requieren propiedades avanzadas de
  la valuación $p$-ádica (multiplicatividad en paridad) o un lema de descenso
  infinito en Peano. Se mantienen aparcados para no bloquear el progreso
  metateórico. Los de `Polynomial.lean`/`Series.lean` son huecos de un módulo
  recién creado (sin deuda conceptual, solo falta terminarlos).
- **Corregido 2026-07-12**: `Rationals/Irrational.lean:395` (`newton_seq_eventually_lt`)
  usaba `Classical.byContradiction`, violando la directiva de pureza constructiva
  (DECISIONS.md MANDATORY M-1). Reescrito de forma constructiva (búsqueda acotada por
  decidibilidad de `≤` en `ℚ₀`, lema `newton_bounded_search`) y añadido al gate
  `Meta/AxiomCheck.lean` para que una regresión futura falle el build.

## Próximo Objetivo: Iniciar el FRENTE 1
Al retomar el trabajo, nuestro objetivo es arrancar el **FRENTE 1: Análisis Real Constructivo**.

### Tareas Inmediatas al Reanudar:
1. **Definir `HFReal`**:
   - Crear el tipo de los Números Reales como el cociente de las Sucesiones de Cauchy en `HFRat` bajo la relación de equivalencia estándar (sucesiones cuya diferencia tiende a cero).
2. **Aritmética en `HFReal`**:
   - Levantar las operaciones de suma, multiplicación y negación desde las sucesiones de Cauchy al espacio cociente `HFReal`.
3. **Estructura de Cuerpo y Métrica**:
   - Instanciar `HFReal` como un cuerpo (`HFField`).
   - Definir la noción de distancia/valor absoluto en los reales.
4. **Planificación de Completitud**:
   - Trazar el plan para demostrar que toda sucesión de Cauchy de números reales converge a un número real (Completitud de Cauchy de $\mathbb{R}$).

## FRENTE 2 (tras FRENTE 1) — heredado de `NEXT_STEPS.md`
- **Propiedades topológicas de ℝ₀ / `HFReal`**: explorar conexidad, compacidad y
  convergencia real utilizando las bases ya establecidas en `AczelSetTheory/Topology/`.
  Depende de que `HFReal` exista como tipo (FRENTE 1); no iniciar antes.

## Deuda documental pendiente (ver INFORME-AUDITORIA-2026-07-12.md)
- `doc/REFERENCE-Rationals.md` no cubre `HFRatCauchyAlgebra.lean`, `Series.lean`,
  `Polynomial.lean` ni el subsistema `Reals/`.
- `AUDIT-MODULE-MATRIX.md` no se regenera desde 2026-06-10.
- Unificación pendiente de `AI-GUIDE.md`/`NAMING-CONVENTIONS.md`/`DECISIONS.md`/
  `DEPENDENCIES.md` con los proyectos hermanos (Peano, FOL, ROBINSON_PlusPlus) vía
  `lean4-project-template` — propuesta en discusión, ver memoria de sesión.
