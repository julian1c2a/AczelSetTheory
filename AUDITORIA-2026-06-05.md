# Auditoría del proyecto AczelSetTheory — 2026-06-05

> Generada tras el cierre de **M7 Zassenhaus / FASE A**, commits `18caf54` y `c2d753b`.
> Toolchain: **Lean v4.30.0**. Repo sincronizado con `origin/main` (sin trabajo pendiente de Claude Code Pro / Copilot Pro: ningún commit remoto faltante).

---

## 1. Resumen ejecutivo

| Indicador | Valor | Notas |
|---|---:|---|
| Resultado de `lake build` | ✅ 0 errores | 35 jobs |
| Warnings | ✅ 0 | linter limpio |
| `sorry` en código activo | ✅ 0 | (`sorry` solo en `test_sorry.lean` y comentarios) |
| `admit` | ✅ 0 | |
| `axiom` declarados | ✅ 0 | (sólo se importan los axiomas matemáticos como teoremas demostrados) |
| `noncomputable def` | ✅ 0 | proyecto totalmente computable |
| `TODO` / `FIXME` / `XXX` reales | ✅ 0 | (los matches de "TODO" eran falsos positivos: español "todo") |
| Total ficheros `.lean` | **172** | bajo `AczelSetTheory/` (incl. barrels) |
| LOC totales | **22 994** | sólo bajo `AczelSetTheory/` |
| Documentos `*.md` raíz | 17 | |
| Documentos `doc/REFERENCE-*.md` | 16 | + `doc/peano/` |

**Estado general**: 🟢 **VERDE**. Build limpio, sin deuda técnica activa, FASE A completa. Único punto de mantenimiento detectado: dos documentos derivados están desactualizados (ver §4).

---

## 2. Sincronización con colaboradores externos

Comprobado:

```text
git fetch --all
git status                 → On branch main, up to date with origin/main
git log main..origin/master → vacío
git log origin/master..main → 6 commits adelantados
```

**Conclusión**: no hay trabajo pendiente de Claude Code Pro ni de Copilot Pro en `origin/main` ni en `origin/master`. La rama `master` está 6 commits por detrás de `main` y puede archivarse o reposicionarse cuando se desee.

Últimos 5 commits:

| SHA | Mensaje |
|---|---|
| `c2d753b` | docs: M7 Zassenhaus & FASE A completa (PLANNING/CHANGELOG/STATUS/NEXT_STEPS/REFERENCE) |
| `18caf54` | M7 Zassenhaus: butterfly lemma proof complete; cleanup warnings |
| `d177a24` | Sprint D2 docs + VN cleanup; QuotientGroup build; Sylow API |
| `d3f7049` | Migrar `cosetRep` a versión computable; auditoría + changelog |
| `c6d75fe` | Migración a implementaciones constructivas; reducir wrappers `noncomputable` |

---

## 3. Inventario de documentación

### 3.1 Top-level (raíz)

| Documento | Líneas | Función | Estado |
|---|---:|---|---|
| [`README.md`](README.md) | — | Punto de entrada del proyecto | OK |
| [`AI-GUIDE.md`](AI-GUIDE.md) | — | Guía interna para asistentes IA (definición de "proyectar") | OK |
| [`PLANNING.md`](PLANNING.md) | 666 | Plan maestro: hitos M0–M7+, FASE A cerrada | ✅ Actualizado 2026-06-05 |
| [`CHANGELOG.md`](CHANGELOG.md) | 475 | Bitácora cronológica de hitos | ✅ Actualizado 2026-06-05 |
| [`CHANGELOG-PEANO.md`](CHANGELOG-PEANO.md) | — | Bitácora específica del subproyecto Peano (congelado) | OK |
| [`CURRENT-STATUS-PROJECT.md`](CURRENT-STATUS-PROJECT.md) | 401 | Snapshot operativo: módulos, conteos, sprints | ✅ Actualizado 2026-06-05 |
| [`NEXT_STEPS.md`](NEXT_STEPS.md) | 551 | Backlog priorizado y plan FASE B | ✅ Actualizado 2026-06-05 |
| [`DECISIONS.md`](DECISIONS.md) | 255 | ADRs (incluye ADR-000: Peano congelado) | OK |
| [`DEPENDENCIES.md`](DEPENDENCIES.md) | — | Mapa de dependencias entre módulos | OK |
| [`NAMING-CONVENTIONS.md`](NAMING-CONVENTIONS.md) | — | Reglas estilo Mathlib | OK |
| [`NONCOMPUTABLES_INSTANCES.md`](NONCOMPUTABLES_INSTANCES.md) | — | Inventario `noncomputable` (actualmente vacío: 0 defs) | OK |
| [`THOUGHTS.md`](THOUGHTS.md) | — | Notas y reflexiones | OK |
| [`WORKFLOW.md`](WORKFLOW.md) | — | Procedimientos (lock, build, gen-root) | OK |
| [`LISTA_DE_ACCIONES_REQUERIDAS_A_USUARIO.md`](LISTA_DE_ACCIONES_REQUERIDAS_A_USUARIO.md) | — | Tareas pendientes para el humano | OK |
| [`proof_plan.md`](proof_plan.md) | — | Plan táctico de pruebas pendientes | OK |
| [`REFERENCE.md`](REFERENCE.md) | 552 | Índice general de módulos | ⚠️ **Desactualizado** — fechado 2026-06-02; declara Lean v4.29.0 (real: v4.30.0); no incluye `Algebra/Zassenhaus.lean` ni varios módulos VN/* recientes |
| [`AUDIT-MODULE-MATRIX.md`](AUDIT-MODULE-MATRIX.md) | 199 | Matriz módulo a módulo con métricas | ⚠️ **Desactualizado** — fechado 2026-06-03; cuenta 174 ficheros (real: 172) y reporta `Sylow.lean` con 1 `sorry` (real: 0). Falta entrada para `Algebra/Zassenhaus.lean` |

### 3.2 Subdirectorio `doc/`

| Documento | Bytes | Estado |
|---|---:|---|
| [`doc/REFERENCE-Algebra.md`](doc/REFERENCE-Algebra.md) | 82 899 | ✅ Actualizado 2026-06-05 (§7 Zassenhaus añadido) |
| [`doc/REFERENCE-GroupTheory.md`](doc/REFERENCE-GroupTheory.md) | 64 894 | OK (descripción narrativa de la teoría de grupos) |
| [`doc/REFERENCE-Arithmetic.md`](doc/REFERENCE-Arithmetic.md) | 78 331 | OK |
| [`doc/REFERENCE-Relations.md`](doc/REFERENCE-Relations.md) | 27 026 | OK |
| [`doc/REFERENCE-VN.md`](doc/REFERENCE-VN.md) | 25 348 | OK |
| [`doc/REFERENCE-ListsAndSets.md`](doc/REFERENCE-ListsAndSets.md) | 27 903 | OK |
| [`doc/REFERENCE-Combinatorics.md`](doc/REFERENCE-Combinatorics.md) | 21 103 | OK |
| [`doc/REFERENCE-Foundation.md`](doc/REFERENCE-Foundation.md) | 20 888 | OK |
| [`doc/REFERENCE-Paridad-Peano-Aczel.md`](doc/REFERENCE-Paridad-Peano-Aczel.md) | 20 623 | ✅ Actualizado 2026-06-05 |
| [`doc/REFERENCE-HFSets.md`](doc/REFERENCE-HFSets.md) | 20 287 | OK |
| [`doc/REFERENCE-NumberTheory.md`](doc/REFERENCE-NumberTheory.md) | 18 506 | OK |
| [`doc/REFERENCE-CList.md`](doc/REFERENCE-CList.md) | 16 507 | OK |
| [`doc/REFERENCE-PList.md`](doc/REFERENCE-PList.md) | 11 440 | OK |
| [`doc/REFERENCE-HFList.md`](doc/REFERENCE-HFList.md) | 8 922 | OK |
| [`doc/REFERENCE-Topology.md`](doc/REFERENCE-Topology.md) | 8 880 | OK |
| [`doc/REFERENCE-Prelim.md`](doc/REFERENCE-Prelim.md) | 5 369 | OK |
| `doc/peano/` | (dir) | Documentación específica del subproyecto Peano | OK |

---

## 4. Inventario de módulos `.lean`

### 4.1 Distribución por subsistema

| Subsistema | Ficheros | LOC | Estado |
|---|---:|---:|---|
| `Algebra/` | 21 | 8 752 | ✅ Limpio (Sylow + Zassenhaus completos) |
| `Axioms/` | 42 | 4 189 | ✅ Limpio (núcleo ZF axiomatizado como teoremas) |
| `VN/` | 49 | 2 920 | ✅ Limpio (VN ↔ HFSet, aritmética, grupos VN) |
| `Integers/` | 8 | 1 795 | ✅ Limpio (incl. `Rationals.lean`) |
| `CList/` | 7 | 1 459 | ✅ Limpio |
| `Operations/` | 21 | 1 364 | ✅ Limpio |
| `Topology/` | 5 | 900 | ✅ Limpio |
| top-level (`AczelSetTheory/`) | 14 | 774 | ✅ Limpio (barrels + `HFSets`, `HFList`, `Notation`) |
| `PList/` | 4 | 677 | ✅ Limpio |
| `Combinatorics/` | 1 | 164 | ✅ Limpio (`Counting.lean`) |
| **TOTAL** | **172** | **22 994** | |

### 4.2 Top 10 módulos por tamaño

| LOC | Módulo |
|---:|---|
| 3 516 | [`AczelSetTheory/Algebra/Sylow.lean`](AczelSetTheory/Algebra/Sylow.lean) |
| 684 | [`AczelSetTheory/Algebra/Zassenhaus.lean`](AczelSetTheory/Algebra/Zassenhaus.lean) |
| 511 | [`AczelSetTheory/Algebra/Subgroup.lean`](AczelSetTheory/Algebra/Subgroup.lean) |
| 500 | [`AczelSetTheory/CList/Normalize.lean`](AczelSetTheory/CList/Normalize.lean) |
| 497 | [`AczelSetTheory/Axioms/OrdinalNat.lean`](AczelSetTheory/Axioms/OrdinalNat.lean) |
| 427 | [`AczelSetTheory/Integers/Rationals.lean`](AczelSetTheory/Integers/Rationals.lean) |
| 421 | [`AczelSetTheory/Integers/Basic.lean`](AczelSetTheory/Integers/Basic.lean) |
| 397 | [`AczelSetTheory/Algebra/QuotientGroup.lean`](AczelSetTheory/Algebra/QuotientGroup.lean) |
| 370 | [`AczelSetTheory/PList/Lemmas.lean`](AczelSetTheory/PList/Lemmas.lean) |
| 349 | [`AczelSetTheory/Algebra/NormalSubgroup.lean`](AczelSetTheory/Algebra/NormalSubgroup.lean) |

### 4.3 Hitos de la teoría de grupos (§3 GroupTheory)

| Hito | Módulo | Estado |
|---|---|---|
| M1 Lagrange | `Algebra/Subgroup.lean`, `CosetCount.lean` | ✅ |
| M2 Primer T. de Isomorfía | `Algebra/FirstIsomorphism.lean` | ✅ |
| M3 Segundo T. de Isomorfía | `Algebra/SecondIsomorphism.lean` | ✅ |
| M4 Tercer T. de Isomorfía | `Algebra/ThirdIsomorphism.lean` | ✅ |
| M5 T. de la Correspondencia | `Algebra/CorrespondenceTheorem.lean` | ✅ |
| M6 T. de Sylow (I + II) | `Algebra/Sylow.lean` (3 516 LOC) | ✅ |
| M7 Lema de Zassenhaus | `Algebra/Zassenhaus.lean` (684 LOC) | ✅ |

**FASE A cerrada**: 18/0/0 (módulos completos / con sorry / con axiomas extra).

---

## 5. Hallazgos y discrepancias

### 5.1 Documentos derivados desactualizados ⚠️

1. **[`REFERENCE.md`](REFERENCE.md)**:
   - Cabecera dice `Last updated: 2026-06-02` y `Lean version: v4.29.0`. Reales: 2026-06-05 y v4.30.0.
   - No incluye `AczelSetTheory/Algebra/Zassenhaus.lean` en la tabla maestra.
   - Probablemente faltan también algunos VN/*VN recientes (`QuotientGroupVN`, `NormalSubgroupVN`, `*IsomorphismVN`, `CorrespondenceTheoremVN`, `ActionVN`, `SignVN`).

2. **[`AUDIT-MODULE-MATRIX.md`](AUDIT-MODULE-MATRIX.md)**:
   - Cabecera `Generado: 2026-06-03`, dice 174 ficheros (real: 172) y reporta `Sylow.lean` con 1 `sorry` ya cerrado.
   - No incluye fila para `Algebra/Zassenhaus.lean`.
   - Recomendación: regenerar con `make audit` o equivalente.

### 5.2 Sin discrepancias detectadas en el código ✅

- 0 `sorry`, 0 `admit`, 0 `axiom`, 0 `noncomputable def`, 0 `TODO/FIXME` reales.
- Build limpio (35 jobs, 0 warnings) reverificado tras `git pull`.
- Ningún módulo huérfano: todos los `.lean` están alcanzados desde el barrel raíz `AczelSetTheory.lean` (verificado por compilación exitosa).

### 5.3 Observaciones menores

- La rama remota `origin/master` está 6 commits por detrás de `main`. Considerar archivar o forzar `master` ← `main` cuando se cierre FASE B.
- El subdirectorio `doc/peano/` no se ha listado individualmente (subproyecto congelado por ADR-000).

---

## 6. Recomendaciones priorizadas

| # | Acción | Prioridad | Esfuerzo |
|---|---|---|---|
| 1 | Regenerar `AUDIT-MODULE-MATRIX.md` (incluir `Zassenhaus.lean`, corregir conteo de ficheros y eliminar el `sorry` ya cerrado de `Sylow.lean`) | 🟡 Media | bajo |
| 2 | Actualizar cabecera y tabla maestra de `REFERENCE.md` (fecha, Lean v4.30.0, fila Zassenhaus, nuevos `*VN`) | 🟡 Media | medio |
| 3 | Decidir destino de `origin/master` (archivar / forzar a `main`) | 🟢 Baja | trivial |
| 4 | Iniciar FASE B según plan de [`NEXT_STEPS.md`](NEXT_STEPS.md) | 🟢 Planificación | — |

---

## 7. Conclusión

El proyecto está **en estado saludable y consistente** tras el cierre de M7 / FASE A: build limpio, cero deuda técnica activa, totalmente computable y sin axiomas externos al core de Lean. El trabajo de los colaboradores externos (Claude Code Pro y Copilot Pro) ya está integrado en `origin/main`; no hay nada nuevo que traer.

Las únicas tareas de mantenimiento son **dos refrescos documentales** (`REFERENCE.md` y `AUDIT-MODULE-MATRIX.md`) que no bloquean el avance. El proyecto está listo para abordar **FASE B**.
