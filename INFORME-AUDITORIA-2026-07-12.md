# Informe de Auditoría Cruzada — 2026-07-12

**Fecha:** 2026-07-12
**Auditor:** Claude Sonnet 5 (IA), vía 3 subagentes de exploración read-only
**Alcance:** (A) Estado real vs. documentado de **AczelSetTheory**. (B) Comparativa de
gobernanza documental entre AczelSetTheory, **Peano**, **FOL**, **ROBINSON_PlusPlus** y
**FOL_CompStructs** (proyectos hermanos en `E:/dropbox/github/lean4/`). (C) Propuesta de
formato unificado para `AI-GUIDE.md`, `NAMING-CONVENTIONS.md`, `DECISIONS.md`,
`DEPENDENCIES.md`.
**Método:** lectura directa + grep/git-log del árbol real; ningún fichero fue modificado
durante la auditoría.

---

## Resumen ejecutivo

| Indicador | AczelSetTheory | Peano | FOL | ROBINSON_PlusPlus | FOL_CompStructs |
|---|---|---|---|---|---|
| `.lean` trackeados (excl. `.lake`) | 204 (201 en HEAD) | 74 | 70 | 77 | 5 |
| LOC | ~34 194 | ~37 564 | ~8 323 | ~24 729 | 297 |
| `sorry` reales | **14** (working tree) / 4 (HEAD) | 0 | 0 | 0 | 0 |
| `Classical.*` | 1 fichero (violación no cubierta por el gate) | 8 ficheros (permitido, sin mandato) | 42 usos / 12 `noncomputable` | 2 usos | 0 |
| Documentación de estado al día | ❌ (varios docs desincronizados, uno con dato falso desde su origen) | ❌ (~7 semanas sin sincronizar) | ⚠️ parcial (badge de sorry obsoleto, lib fantasma) | ✅ la más viva de las 4, con desfase menor | N/A (sin aparato de gobernanza) |
| Mecanismo lock/freeze usado en la práctica | Nunca (ficheros vacíos desde el primer commit) | Roto (rutas fantasma) | Vacío + basura (`"an"`) | Vacío pero limpio | No existe |

**Hallazgo transversal más importante:** los 4 proyectos con aparato de gobernanza completo
comparten el mismo patrón de fallo — *el detalle técnico (ADRs, tablas de exports,
REFERENCE.md) está mejor cuidado que el resumen ejecutivo (README, CURRENT-STATUS-PROJECT,
CHANGELOG)*, y el sistema de lock/freeze documentado extensamente en `WORKFLOW.md`/
`AI-GUIDE.md` **nunca se ha usado de forma persistida en ninguno de los 4 proyectos**.

---

## Parte A — AczelSetTheory: estado real vs. documentado

### A.1 Inventario real

- **204** ficheros `.lean` en el working tree (201 en HEAD), **34 194 LOC**.
- **`sorry` reales: 14** — no 0 como afirma la documentación — repartidos en:
  `Rationals/Irrational.lean:355`, `Rationals/Polynomial.lean:59,71,81,112`,
  `Rationals/Series.lean:26,36,40,44,76,82`, `Reals/Incompleteness.lean:31,44,53`.
  4 de ellos (Irrational + Incompleteness) ya estaban en HEAD; 10 corresponden a
  `Polynomial.lean`/`Series.lean`, **ya en el índice de git (staged)** sin commitear.
- `noncomputable` real: **0** (única mención es un comentario en `Algebra/HFMatrix.lean:12`).
- `README.md:8` ("4 sorry, 0 noncomputable, 200 archivos, ~33 500 LOC") coincide con HEAD
  pero no con el working tree — **severidad menor**, es deuda de "próximo commit".

### A.2 Hallazgos críticos

1. **`CURRENT-STATUS-PROJECT.md` afirma "0 sorry / 153/153 módulos limpios" siendo falso
   ya en el commit que lo escribió** (`6a64640`, 2026-07-06 — en ese momento ya existían
   los 4 sorry de Irrational/Incompleteness). Su propia cabecera "Last updated: 2026-06-29"
   tampoco coincide con la fecha real de su último commit. **Severidad: crítica.**

2. **Contradicción frontal entre `README.md` y `DECISIONS.md`/ADR-018 sobre la directiva
   fundacional "cero Classical"**: `README.md:25` afirma explícitamente que el footprint
   `{propext, Classical.choice, Quot.sound}` es aceptable y "igual que en Mathlib", mientras
   que `DECISIONS.md:22` (MANDATORY M-1) prohíbe `Classical.*` por completo y fija como
   objetivo `{propext, Quot.sound}` sin `Classical.choice`. El README normaliza justo lo
   que la directiva fundacional prohíbe. Además hay una **violación real y activa** no
   detectada por el gate: `Rationals/Irrational.lean:395` usa
   `apply Classical.byContradiction` dentro de `newton_seq_eventually_lt` (introducido en
   `98ad0bb`, 2026-07-08, posterior al cierre de "Fase 3" de pureza constructiva). El gate
   `Meta/AxiomCheck.lean` solo cubre símbolos de `CList`/`HFSet`/`HFAlgebra`; no cubre
   `Rationals/`/`Reals/`. **Severidad: crítica.**

3. **`REFERENCE.md` documenta 3 ficheros que ya no existen** (`Reals/CauchySeq.lean`,
   `Reals/Arithmetic.lean`, `Reals/Order.lean`, borrados en `173add2` el 2026-07-05) como
   "✅ Complete", con **4 pares de IDs de fila duplicados** (108c–108f reutilizados para
   módulos distintos en el commit `d1a5693`) y una cabecera de fecha desfasada un mes
   respecto a su propia última edición. También describe el barrel `Rationals.lean` con
   solo 4 dependencias documentadas cuando el fichero real importa 19. **Severidad: crítica.**

### A.3 Hallazgos medios

4. **`NEXT_STEPS.md` (guión bajo) y `NEXT-STEPS.md` (guión)** coexisten como ficheros de
   "punto de reanudación" vigentes y **contradictorios**: el primero (última edición
   2026-07-08 19:12) fija como próximo paso cerrar los sorries de `Incompleteness.lean`;
   el segundo (creado 2 horas después, 21:13, tras borrar y recrear un `NEXT-STEPS.md`
   anterior) trata esos mismos sorries como "deuda aparcada intencionalmente" y fija un
   objetivo distinto (iniciar `HFReal`/análisis real). Ninguno referencia al otro.

5. `frozen_files.txt` y `locked_files.txt` están **vacíos desde el primer commit** — el
   protocolo de "un fichero desbloqueado a la vez" de `WORKFLOW.md` nunca se ha aplicado
   de forma persistida.

6. `.gitignore` tiene su línea `/.worktrees` **corrupta en UTF-16** (bytes nulos
   intercalados) — `git check-ignore -v .worktrees` no produce coincidencia, es decir
   `.worktrees/` no está realmente ignorado pese a la intención.

7. 13 ficheros `scratch*.lean`/`temp_check*.lean` + `fix-ref.ps1` están **commiteados en
   la raíz** (todos añadidos de golpe en `d1a5693`), contradiciendo `WORKFLOW.md:117`
   ("Stage specific files (avoid `git add -A`)").

8. `AI-GUIDE.md` exige timestamps `YYYY-MM-DD HH:MM` en toda la documentación técnica;
   **ningún** documento del proyecto cumple ese formato (todos usan solo `YYYY-MM-DD` o
   ninguna fecha).

9. `NAMING-CONVENTIONS.md` no menciona en absoluto la convención `*VN.lean`/namespace `VN`
   (~35 ficheros reales la usan) ni se corresponde con la práctica real: su "REGLA 13"
   (sufijos de dominio tipo `addZ`/`mulQ`) no se usa nunca — el código usa consistentemente
   namespaces anidados (`ℤ₀`, `ℚ₀`) tal como sí describe `AI-GUIDE.md §3.5`.

10. `CHANGELOG.md`, `DECISIONS.md` y `AUDIT-MODULE-MATRIX.md` llevan entre 9 y 53 commits
    de desfase respecto a HEAD, incluyendo la creación completa de `Rationals/` →
    `Reals/` (HFRat, Bisection, Convergence, Archimedean, Irrational, Series, Polynomial)
    sin ninguna entrada.

11. Los 3 ficheros nuevos de `Rationals/` (staged, sin commitear) no aparecen en
    `REFERENCE.md`, `CURRENT-STATUS-PROJECT.md`, `CHANGELOG.md` ni ninguno de los dos
    `NEXT-STEPS`, y carecen del bloque descriptivo post-copyright que sí llevan sus
    módulos hermanos (`Bisection.lean`, `Canonical.lean`).

### A.4 Hallazgos menores

- `check-sorry.bash` cuenta con `grep -c 'sorry'` sin excluir comentarios → falsos
  positivos en `Bezout.lean`/`Canonical.lean`/`HFMatrix.lean`.
- Uso de `Nat` (tipo nativo) limitado a los casos ya amparados por la excepción M-2
  (puentes `Ψ/Λ`, `termination_by`) — **sin violación sustantiva** de "ℕ₀ siempre".
- Dos CHANGELOGs (`CHANGELOG.md` + `CHANGELOG-PEANO.md`) están justificados y
  autodocumentados — no es una inconsistencia, es partición intencional.

---

## Parte B — Comparativa de gobernanza entre proyectos hermanos

### B.1 Dos linajes de `AI-GUIDE.md`

Existen **dos versiones estructuralmente distintas** de `AI-GUIDE.md` en la familia de
proyectos, no una sola plantilla compartida:

- **Linaje A (español, más simple)** — AczelSetTheory y Peano: título *"Guía Maestra de
  la IA — Estándares de Documentación y Desarrollo"*, 23 puntos numerados (0–23), sin
  sección de naming embebida, comandos: `actualiza doc`, `actualiza_documentacion`,
  `pon_al_dia_el_plan`, `revisa_pensamientos`, `compila_y_comprueba`, `dame_situación`,
  `proyecta`, `repasa_y_proyecta`, `guarda_y_sube`. AczelSetTheory añade un punto extra
  (16b, "Regla de Directorio Raíz") que Peano no tiene — es decir, ni siquiera dentro del
  mismo linaje están sincronizados.
- **Linaje B (inglés, más completo)** — FOL y ROBINSON_PlusPlus: título *"AI Assistant
  Guide — Documentation Standards"*, con más de 30 puntos, **incluye una sección de
  Naming Conventions embebida** (NC-1 a NC-10, con diccionario de símbolos y tabla
  resumen), sección "Export/Glob Architecture" (bloques `export`, mantenimiento,
  barrels), "Annotation System for REFERENCE.md", "Cross-Reference Files"
  (NAMING-CONVENTIONS.md / NEXT-STEPS.md / PLANNING.md / THOUGHTS.md), y una plantilla
  literal para el comando `dame situación` (con encabezados `### Build`, `### Sorries
  vigentes`, etc.) que el linaje A no tiene.

**Consecuencia problemática dentro del propio Linaje B**: FOL/ROBINSON tienen **dos
fuentes de verdad para las convenciones de nombres que pueden divergir entre sí** — la
sección NC-1..NC-10 embebida en `AI-GUIDE.md` (inglés, resumen) y el fichero independiente
`NAMING-CONVENTIONS.md` (inglés, 12 reglas "RULE 1"–"RULE 12", con tablas de conversión) —
ninguno de los dos documentos remite al otro ni declara cuál es autoritativo en caso de
conflicto.

### B.2 `NAMING-CONVENTIONS.md`

- AczelSetTheory y Peano comparten **exactamente la misma estructura** (13 "REGLA N",
  español, diccionario de símbolos, tabla de variables, typeclasses) — buena señal de
  linaje compartido, pero ambos con placeholders `YYYY-MM-DD`/`[Nombre del Autor]` sin
  rellenar en su cabecera desde la creación.
- FOL y ROBINSON comparten otra estructura distinta (12 "RULE N", inglés, orientada a
  tablas de "quick reference" conversión antes/después) — placeholders de cabecera
  también sin rellenar.
- Ningún proyecto tiene ambas versiones (13-reglas-ES vs. 12-reglas-EN) documentando lo
  mismo con la misma numeración — son dos familias de contenido genuinamente distintas,
  no solo traducciones.

### B.3 `DECISIONS.md`

- **AczelSetTheory** es el único con una sección **"MANDATORIES"** (M-1 a M-5) y llega a
  ADR-019 — el más maduro y específico de los 4, con directivas fundacionales explícitas
  (pureza constructiva, ℕ₀ exclusivo) que **ningún otro proyecto hermano declara**.
- **Peano** tiene 12 ADRs propios, coherentes con su arquitectura, sin mandato "cero
  Classical" (de hecho permite `Classical.*` en 8 módulos sin más discusión).
- **FOL** tiene solo **7 ADRs, todos genéricos de plantilla**, con el título literal sin
  sustituir (**`# Design Decisions — ProjectName`**) y la rationale de ADR-001 sin
  rellenar (`[Explain why — e.g., educational goals...]`). Ninguno decide algo específico
  de la lógica de primer orden.
- **ROBINSON_PlusPlus** hereda los mismos 7 ADRs genéricos de FOL (con el mismo título
  `ProjectName` sin sustituir) **más 2 ADRs propios y sustanciosos** (ADR-008 sobre los
  meta-axiomas de `Minimal/Axioms.lean`, ADR-009 sobre la corrección de un axioma falso
  con contraejemplo) — el estándar de calidad más alto de justificación matemática real
  entre los 4, pese a arrastrar el defecto de plantilla sin limpiar.

### B.4 `DEPENDENCIES.md`

- **AczelSetTheory**: honesto sobre su propia obsolescencia — incluye una nota explícita
  ("alcance histórico... no refleja los ~165 módulos añadidos") y redirige a
  `REFERENCE.md`/`AUDIT-MODULE-MATRIX.md`/`lake graph`. Buena práctica de "no mentir",
  aunque implica que el documento es decorativo para 9 de cada 10 módulos reales.
- **Peano**: grafo Mermaid + tabla completa, con marcador `<!-- AUTO-UPDATE-2026-05-10 -->`,
  pero contiene **módulos fantasma** (`FSetFSet`, `ListList`, eliminados y documentados
  como tales en README.md) y **omite módulos reales** (`EquivRel`, `ThirdIsomorphism`,
  `Fractions`).
- **ROBINSON_PlusPlus**: el más completo y mejor estructurado de los 4 — grafo Mermaid,
  tabla de niveles, tabla de exports por módulo, sección "Notable cross-module facts" con
  justificación histórica de decisiones de ubicación de lemas. Buen modelo a imitar.
- **FOL**: **100% plantilla sin adaptar** — título `# Dependency Diagram — ProjectName`,
  ejemplos ficticios (`Prelim.lean`, `Core/Basic.lean`, `Topic/Advanced.lean`) que no
  existen en el proyecto real de 70 ficheros / 5 sub-librerías. Es el hallazgo más claro
  de que el comando `actualiza_documentacion` nunca se ejecutó sobre este fichero.

### B.5 Otros hallazgos transversales relevantes

- **Sistema lock/freeze**: documentado extensamente en los 4 proyectos grandes, pero
  `frozen_files.txt`/`locked_files.txt` están vacíos en los 4 (o con basura: FOL tiene la
  cadena suelta `"an"`) — el mecanismo de protección más fuerte de la gobernanza nunca se
  usa en la práctica en ninguno de ellos. En Peano, además, el `chmod a-w` que debería
  aplicar `git-lock.bash` **no tiene efecto real en NTFS/Windows** (verificado:
  `IsReadOnly = False` en un fichero listado como bloqueado).
- **Módulos/sub-librerías fantasma en documentación**: `FOL_poli` (5ª `lean_lib` de FOL)
  no aparece en ningún `.md`; `Peano/PeanoNat/Fractions.lean` tampoco, en ningún documento
  de Peano.
- **Ficheros scratch/temp commiteados permanentemente en la raíz**: presentes en los 3
  proyectos grandes (AczelSetTheory 13, Peano 7 + 2 scripts `fix_*.py`), sin que ningún
  `WORKFLOW.md` tenga una norma que lo permita, prohíba o exija limpiar.
- **FOL_CompStructs** (aparato de gobernanza mínimo: solo README.md + REQUIREMENTS.md)
  es el contraste útil de "spec-first" ligero — su `REQUIREMENTS.md` ya audita el uso
  real de listas/tuplas en `Peano` y en el propio `AczelSetTheory/PList/Basic.lean` antes
  de escribir código.

---

## Parte C — Propuesta de formato unificado

El objetivo es que `AI-GUIDE.md`, `NAMING-CONVENTIONS.md`, `DECISIONS.md` y
`DEPENDENCIES.md` tengan **la misma estructura de secciones** en los 5 proyectos, de modo
que una IA (o el propio usuario) pueda saltar de uno a otro sin reaprender el formato, y
que exista un único "molde" a copiar al crear un proyecto Lean 4 nuevo.

### C.1 Decisión de linaje base

Recomiendo partir del **Linaje B** (`AI-GUIDE.md` de FOL/ROBINSON_PlusPlus) como
esqueleto — es estrictamente más completo (incluye Export/Glob Architecture, Annotation
System, protocolo de freeze detallado, plantilla de `dame situación`) — pero:

1. **Traducirlo al español**, ya que el idioma de trabajo real del usuario y de 3 de los
   5 proyectos (AczelSetTheory, Peano, y el propio flujo de sesión) es español.
2. **Añadir la sección "MANDATORIES"** que hoy solo tiene `DECISIONS.md` de
   AczelSetTheory — cada proyecto debería poder declarar (o declarar vacía) su propia
   lista de directivas no negociables (p.ej. "cero Classical" en AczelSetTheory, "cero
   axiomas espurios" de facto en ROBINSON vía ADR-008/009) en un lugar visible y
   homogéneo de `DECISIONS.md`, en vez de que cada proyecto invente su propia convención
   (AczelSetTheory la puso en `DECISIONS.md`; ROBINSON la tiene implícita solo en 2 ADRs
   sueltos).
3. **Eliminar la duplicidad NC embebida vs. `NAMING-CONVENTIONS.md` standalone** del
   Linaje B: la sección de naming debe vivir **solo** en `NAMING-CONVENTIONS.md`;
   `AI-GUIDE.md` debe limitarse a referenciarlo (tal como ya hace el Linaje A).
4. **Unificar las 13/12 reglas de `NAMING-CONVENTIONS.md`** en un único conjunto de
   reglas (recomiendo partir de las 13 reglas del Linaje A, que son las más recientes y
   las que ya sigue el código de AczelSetTheory, y fusionar las tablas "quick reference"
   de conversión antes/después del Linaje B, que son más útiles como referencia rápida).

### C.2 Esqueleto propuesto — `AI-GUIDE.md`

```
0. Naturaleza de la documentación (no pedagógica, para IA/expertos Lean 4)
1. Arquitectura en árbol de REFERENCE.md (doc/REFERENCE-{tema}.md)
2. Catálogo de módulos · dependencias · namespaces · definiciones · axiomas · teoremas
3. Formato estricto para axiomas/definiciones/teoremas (firma Lean 4 + notación matemática)
4. Prohibición de contenido no probado en REFERENCE.md
5. Trazabilidad: timestamp YYYY-MM-DD HH:MM obligatorio en TODOS los .md técnicos
6. Formato y estilo de código (implícitos, one-liner term-mode)
7. Arquitectura de exportaciones y directorios (export blocks, barrels)
8. Sistema de bloqueo de archivos (lock temporal / freeze permanente)
   — con nota de limitación conocida: chmod no es efectivo en NTFS/Windows;
     el lock es un contrato social + hook pre-commit, no una protección de FS.
9. Encabezado de copyright + autoría
10. MANDATORIES del proyecto (remite a DECISIONS.md §MANDATORIES — puede estar vacía)
11. Referencia a NAMING-CONVENTIONS.md (sin duplicar contenido aquí)
12. Ficheros de referencia cruzada (NEXT-STEPS.md, PLANNING.md, THOUGHTS.md — un único
    nombre canónico, ver C.4)
13. Comandos interactivos para la IA (actualiza doc, proyecta, dame situación con
    plantilla, guarda y sube, pon al día el plan)
```

### C.3 Esqueleto propuesto — `NAMING-CONVENTIONS.md` / `DECISIONS.md` / `DEPENDENCIES.md`

- **`NAMING-CONVENTIONS.md`**: cabecera con fecha real (no plantilla) + reglas 1–13 (base
  Linaje A) + tablas "quick reference" de conversión (base Linaje B) + sección obligatoria
  de convenciones **locales** del proyecto (p.ej. sufijo `VN` en AczelSetTheory, `Block_N`
  en ROBINSON) que hoy no está en ningún documento de ningún proyecto.
- **`DECISIONS.md`**: cabecera con fecha real + sección **MANDATORIES** (aunque esté
  vacía) + ADRs numerados sin huecos, título con el nombre real del proyecto (nunca
  `ProjectName`) + plantilla de ADR al final.
- **`DEPENDENCIES.md`**: cabecera con fecha real + diagrama Mermaid **de nivel de
  subsistema** (no módulo-a-módulo si el proyecto supera ~50 módulos — el propio patrón
  que ya usa AczelSetTheory) + tabla de dependencias por módulo + nota explícita de
  alcance/vigencia + comandos de verificación (`lake build`, `grep sorry`).

### C.4 Decisiones pendientes de tu parte

Antes de generar/propagar estas plantillas a los 5 proyectos necesito que decidas:

1. ¿Base en español (Linaje A) o inglés (Linaje B) para el `AI-GUIDE.md` unificado?
2. ¿`NEXT-STEPS.md` (guión) o `NEXT_STEPS.md` (guión bajo) como nombre canónico único?
   (AczelSetTheory tiene ambos hoy, activos y contradictorios — hay que elegir uno y
   fusionar antes de propagar el estándar).
3. ¿Quieres que aplique ya estos cambios a los 4-5 repos (son repos git independientes,
   cada uno con su propio historial — lo trataría como una serie de commits "docs:
   unificar plantilla de gobernanza" por repo, revisable antes de cada uno), o prefieres
   revisar primero un borrador único de las 4 plantillas nuevas antes de tocar ningún
   repositorio?

---

## Notas metodológicas

Esta auditoría fue realizada por 3 subagentes de exploración en paralelo (uno por
AczelSetTheory, uno por Peano, uno por FOL+ROBINSON_PlusPlus+FOL_CompStructs), cuyos
hallazgos fueron verificados por referencia cruzada de rutas/líneas/commits citados. No se
modificó ningún fichero de código ni de documentación durante la auditoría; este informe
es, en sí mismo, el único artefacto nuevo creado.
