# Informe de Auditoría — AczelSetTheory — 2026-07-15

**Fecha:** 2026-07-15
**Auditor:** Claude Opus 4.8 (IA), sesión interactiva
**Alcance solicitado por el usuario:**
1. Lectura de `AI-GUIDE.md`, `NAMING-CONVENTIONS.md`, `DECISIONS.md`, `DEPENDENCIES.md`.
2. Auditoría del proyecto sobre el **código real**.
3. Auditoría de la **compilación** contra la **dependencia actual de PEANO**.
4. Auditoría de la **documentación**.
5. Auditoría de las **dependencias OCULTAS de `Classical`** (vía núcleo de Lean 4),
   replicando la metodología aplicada en el proyecto Peano (ADR-017 Fase C).

**Método:** lectura directa + `git`/`grep` del árbol real; `lake build` real contra la
Peano viva; verificación de footprint con `#print axioms`; **barrido exhaustivo** de las
3043 declaraciones propias de AczelSetTheory con `Lean.collectAxioms` (meta-comando
`#audit_hidden_classical`, ver §5.2). Se compiló el proyecto y se ejecutaron scripts de
auditoría temporales (ya borrados); **no** se modificó ningún fichero `.lean` de
producción ni de documentación salvo la creación de este informe.

---

## Resumen ejecutivo

| Indicador | Documentado | **Real (2026-07-15)** | Veredicto |
|---|---|---|---|
| `.lean` (working tree = HEAD) | 204 | **204** | ✅ |
| LOC | ~34 250 | **34 253** | ✅ |
| Build | ✅ 266 jobs, 0 err, **0 warn** | ✅ **273 jobs, 0 err, 19 warn** | ⚠️ jobs y warnings desfasados |
| `sorry` reales | 14 | **14** (todos en `Rationals/`·`Reals/`) | ✅ |
| `noncomputable def` | 0 | **0** | ✅ |
| `Classical.*` **explícito** en código | 0 | **0** (solo comentarios + gate) | ✅ |
| `Classical.choice` **oculto** (footprint) | 0 (implícito) | **9 símbolos** | 🔴 **VIOLACIÓN M-1 no detectada** |
| Axioma `native_decide` (compiler-trust) | 0 (implícito) | **≥1**, heredado de Peano Wilson | 🔴 nuevo, fuera de `{propext, Quot.sound}` |
| `sorryAx` (radio de impacto) | — | **21 símbolos** (todos `Rationals/`·`Reals/`) | ℹ️ |
| Compila contra Peano frozen actual (07-14) | — | **✅ sí** (verificado) | ✅ |

**Titular positivo:** el proyecto **compila limpio (273 jobs, exit 0)** contra la Peano
*feature-frozen* actual (`bf6d550`, 2026-07-14), que ya es **cero-`Classical`** tras su
ADR-017. El footprint de los teoremas nucleares centrales (`extensionality`,
`sylow_first`, `cauchy_minimal`, `wf_induction`) es **exactamente `{propext, Quot.sound}`**
— la tesis constructiva se sostiene de extremo a extremo en el núcleo del proyecto.

**Titular crítico (respuesta directa a la tarea 5):** existen **9 símbolos públicos que
dependen de `Classical.choice` de forma oculta** — invisibles a un `grep 'Classical\.'` y
**NO cubiertos por el gate** `Meta/AxiomCheck.lean`, que solo vigila ~30 símbolos
seleccionados a mano (todos limpios). El gate da, por tanto, una **falsa sensación de
seguridad**. Es el mismo fenómeno que Peano documentó en su Fase C.9 (“2 de 5 hallazgos
invisibles a grep de `Classical\.`”).

> ### ✅ Seguimiento (misma sesión, 2026-07-15)
> Tras la auditoría se ejecutaron dos de las recomendaciones:
> - **Recomendación #1 (gate exhaustivo) HECHA** — `Meta/AxiomCheck.lean` reescrito como
>   `#assert_constructive_footprint` (barre las 3042 decls; baseline de **11** excepciones =
>   los 9 `Classical.choice` + `VN.vN_totient_one/two` que solo tienen `native_decide`).
>   Registrado en **ADR-020**. Verificado: build verde (273 jobs) + prueba negativa.
> - **Recomendaciones #4–#7 (documentación) HECHAS** — README/CURRENT-STATUS/CHANGELOG/DECISIONS
>   corregidos (273 jobs · 19 warnings; contradicción Inventory↔Architecture; enlace roto;
>   doble fecha; tabla Integers); **44 cabeceras de copyright añadidas** (§21 → 0 sin cabecera).
>
> **Saneo en curso (Clase B):**
> - ✅ **`HFAlgebra.orbitOf_eq_or_disjoint` HECHO** (2026-07-15): reescrito constructivo — la
>   disyunción se decide por `DecidableEq HFSet` sobre `inter = ∅` (órbitas finitas) en vez de
>   `by_cases` sobre el `∀ x : HFSet` no acotado; testigo del caso no-disjunto vía
>   `nonempty_of_ne_empty`. Footprint verificado: `{propext, Quot.sound}`.
> - ✅ **`HFTopology…interior_exterior_boundary_partition` HECHO** (2026-07-15): el teorema es
>   `P ∨ Q ∨ ¬(P∨Q)` (excluded middle para `isInteriorPt ∨ isExteriorPt`). Se añadieron instancias
>   `Decidable` para `isInteriorPt`/`isExteriorPt` vía `isInteriorPt_iff` (equivalen a membresía en
>   el HFSet `int(A)`, decidible por `mem_decidable`); el `by_cases` original las recoge y deja de
>   caer en `Classical`. Footprint verificado: `{propext, Quot.sound}`.
> - ✅ **`HFSet.mem_wf` + `HFSet.mem_rank_lt` HECHO** (2026-07-15): `Axioms/Rank.lean` NO importaba
>   `Axioms.Decidable`, así que `by_cases hxA : x ∈ A` (líneas 158/163) caía en `Classical.propDecidable`
>   (diagnóstico: `mem_decidable` era *unknown* / `Decidable (x∈A)` no sintetizaba; `well_founded_lt`→`[propext]`,
>   `eps_induction`→`[propext,Quot.sound]` ya limpios). Fix de una línea: `+import Axioms.Decidable`.
>   Footprint verificado: ambos `{propext, Quot.sound}`.
> - ✅ **`PList.get_ext` + `FinList.extEq` + `HFAlgebra.HFMatrixRing` HECHO** (2026-07-15):
>   `by_cases hlt : i < n` sobre el `<` de ℕ₀ caía en `Classical.propDecidable` (dato clave: aunque
>   `infer_instance` halla un `Decidable (i<n)`, el `by_cases` NO localiza el `decidableLt` de Peano
>   —está sobre `lt₀`, no sobre `LT.lt`— y usa `Classical.propDecidable`). Fix: sustituir el `by_cases`
>   por la dicotomía constructiva `Peano.Order.lt_or_ge : lt₀ a b ∨ le₀ b a` (sin axiomas) + `rcases`.
>   `HFMatrixRing` quedó limpio **automáticamente** (dependía transitivamente de esos lemas de indexación;
>   el propio gate lo avisó como "excepción baseline ya limpia"). Footprint: los tres `{propext, Quot.sound}`.
>
> - ✅ **Clase A (4, heredada de Peano) SANEADA AGUAS ARRIBA** (2026-07-15): `vN_wilson`,
>   `vN_wilson_modEq`, `vN_totient_one/two` heredaban su footprint sucio de `Peano.Wilson.wilson`
>   (`Classical.choice` + `native_decide`) y `Peano.Totient.totient_{one,two}` (`native_decide`).
>   Arreglado **en Peano** (worktree `limpieza` → merge a master `9b6241d`, ADR-017):
>   - El `Classical.choice` de `wilson` provenía de **tres lemas de `List.erase` del CORE de Lean 4.31**
>     (`List.length_erase_of_mem`, `List.mem_erase_of_ne`, `List.Nodup.not_mem_erase`), NO de Peano.
>     Reemplazados por versiones constructivas locales (`mem_erase_of_ne_c`/`not_mem_erase_c` +
>     `List.erase_sublist.length_le`). El `native_decide` del caso p=3 → reducción estructural + `modEq_refl`.
>   - `totient_{one,two}`: `native_decide` → prueba constructiva (el kernel no reduce `gcd`, WF).
>   - El gate de Peano (`#assert_constructive`) se endureció para rechazar también `native_decide`.
>   Tras rebuild de AczelSetTheory contra la Peano arreglada: los 4 `vN_*` → `{propext, Quot.sound}`.
>
> **✅✅ PUREZA CONSTRUCTIVA TOTAL. Baseline 11 → 0.** Las 3044 declaraciones propias de AczelSetTheory
> — y la dependencia Peano — tienen footprint **⊆ {propext, Quot.sound}** (+ `sorryAx` de los 14 sorry
> activos de Rationals/Reals). La MANDATORY M-1 se cumple de extremo a extremo. Gate verde a 0 excepciones.

---

## Parte 1 — Documentos base (lectura)

| Documento | Estado | Nota |
|---|---|---|
| `AI-GUIDE.md` | Leído | Protocolo de 23 puntos; redirige obligatoriamente a `DECISIONS.md §MANDATORIES` antes de tocar cualquier `.lean`. |
| `NAMING-CONVENTIONS.md` | Leído | 13 reglas estilo Mathlib. **No** documenta la convención real `*VN`/namespace `VN` (~34 ficheros la usan); su “REGLA 13” (sufijos `addZ`/`mulQ`) no se usa nunca — el código usa namespaces anidados `ℤ₀`/`ℚ₀`. |
| `DECISIONS.md` | Leído | 20 ADRs (000–019) + 5 MANDATORIES (M-1…M-5). El más maduro de la familia. Cabecera 2026-06-10. |
| `DEPENDENCIES.md` | Leído | Autodeclarado histórico (2026-05-11); redirige honestamente a `lake graph`/`REFERENCE.md`. Decorativo para ~9 de cada 10 módulos. |

---

## Parte 2 — Auditoría del código real

### 2.1 Inventario

- **204** ficheros `.lean`, **34 253 LOC**. Working tree **limpio** e idéntico a HEAD
  (`95136fa`, 2026-07-12).
- **14 `sorry` reales** (confirmados por el build, `declaration uses sorry`), todos en el
  frente activo `Rationals/`·`Reals/`:

  | Fichero | Líneas (decl.) | Nº | Contexto |
  |---|---|---|---|
  | `Rationals/Irrational.lean` | 353 | 1 | `newton_seq_step_bound` (cota de descenso Newton) |
  | `Rationals/Polynomial.lean` | 57, 69, 80, 110 | 4 | canonicalización `trimZeros` tras add/smul/mul/monomial |
  | `Rationals/Series.lean` | 17, 28, 38, 42, 70, 78 | 6 | `sum_add`, `sum_mul_left`, `sum_arithmetic`, `sum_geometric` |
  | `Reals/Incompleteness.lean` | 28, 42, 48 | 3 | irracionalidad de √2 y convergencia |

- **0 `noncomputable def`** (única mención es un comentario en `Algebra/HFMatrix.lean:12`).

### 2.2 MANDATORIES

| MANDATORY | Verificación de código | Resultado |
|---|---|---|
| **M-1** cero `Classical.*` | grep explícito | ✅ 0 usos explícitos… **PERO** 🔴 9 dependencias ocultas (ver §5) |
| **M-2** `ℕ₀` siempre, nunca `Nat` | grep `\bNat\b` | ✅ 25 usos, **todos** dentro de la excepción (puentes `Ψ/Λ`, `sizeOf`, `termination_by`, lemas kernel `Nat.*` para `omega`) — sin violación sustantiva |
| **M-3** medidas lexicográficas | revisión `termination_by` | ✅ `CList.evalOp`/`extEq` con medida `(sizeOf, fase)` lexicográfica |
| **M-4** reutilizar tipos peanolib | grep `{.*: ℕ₀ //` | ✅ sin subtipos privados redefinidos (`ℕ₁`/`ℕ₂` reutilizados) |
| **M-5** dependencia exclusiva peanolib | revisión imports | ✅; además ahora **mitigado en origen**: Peano es cero-`Classical` (ver §3.3) |

### 2.3 Namespaces

Estructura semántica y limpia (namespaces con prefijo `HF`, no espejo de directorios):
`HFSet` (66), `VN` (34), `HFAlgebra` (24), `ℚ₀` (15), `HFSubgroup` (11), `ℤ₀` (10),
`CList` (10), `HFTopology` (5), `HFRat` (5), + un símbolo por estructura algebraica.
**Sin colisiones de tipo directorio-espejo.** El commit `95136fa` (2026-07-12) ya adaptó
los namespaces a los renombrados de Peano (GroupTheory/Foundation).

---

## Parte 3 — Auditoría de compilación contra la dependencia PEANO

### 3.1 Configuración

- `lean-toolchain`: **`leanprover/lean4:v4.31.0`** (idéntico en Aczel y Peano).
- `lakefile.lean`: `require peanolib from "E:/Dropbox/GitHub/lean4/Peano"` (**path dependency**).
- `lake-manifest.json`: `dir: E:/Dropbox/GitHub/lean4/Peano`, `fixedToolchain: false`.

### 3.2 Resultado del build

**`lake build AczelSetTheory` → 273 jobs, exit 0, 0 errores.** ✅

- **19 warnings** (NO “0 warnings” como afirma la doc):
  - **5 variables no referenciadas**: 3 en Peano (`Div.lean:508`, `Pow.lean:147`,
    `Group.lean:316`), 2 en Aczel (`Irrational.lean:358` `h_delta`,
    `CauchySeqAlgebra.lean:399` `hd`).
  - **14 `declaration uses sorry`** (los 14 sorry de §2.1).

### 3.3 Contra QUÉ Peano compila (verificación decisiva)

**Peano fue reescrito y congelado el 2026-07-14** (`bf6d550`), un día después del último
commit de Aczel. Su ADR-017 Fase C eliminó `Classical.choice` de Sylow, GödelBeta,
`Group.order`, etc. — Peano es ahora **cero-`Classical` activo** (grep: 8 matches, todos
comentarios/gate).

Se verificó que Lake compila contra la **Peano viva** (no contra una copia obsoleta):
- La Peano viva tiene **61 `.olean` recompilados hoy** (post 2026-07-14 12:00).
- El warning `Group.lean:316:34 hg is not explicitly referenced` corresponde a la
  definición **nueva** `def order … (hg) := Λ ((orderFind …).getD 0)` (que ignora `hg`),
  no a la versión antigua `theorem gpow_mod_order`.

**Conclusión:** AczelSetTheory compila correctamente contra la Peano frozen actual. La
migración de namespaces (GroupTheory/Foundation) y el endurecimiento constructivo de
Peano no rompen el build.

### 3.4 Footprint verificado (`#print axioms`)

| Símbolo | Axiomas | Veredicto |
|---|---|---|
| `HFSet.extensionality` | `{propext, Quot.sound}` | ✅ limpio |
| `HFAlgebra.sylow_first` | `{propext, Quot.sound}` | ✅ limpio (¡vía Peano Sylow, antes con Classical!) |
| `HFAlgebra.cauchy_minimal` | `{propext, Quot.sound}` | ✅ limpio |
| `HFSet.wf_induction` | `{propext, Quot.sound}` | ✅ limpio |
| `ℚ₀.newton_seq_eventually_lt` | `{propext, sorryAx, Quot.sound}` | ⚠️ sin Classical, pero con `sorry` transitivo |

### 3.5 Hallazgo de higiene: copia stale de peanolib

`.lake/packages/peanolib` es una **copia OBSOLETA de 27 MB** de Peano (fechada 2026-06-06),
**no un junction** (`fsutil` confirma que no es reparse point; `md5` de su `Group.lean`
difiere de la Peano viva). Tiene **0 `.olean` recompilados hoy** → **Lake NO la usa**
(usa el `dir` del manifiesto). Es un huérfano inofensivo para el build, pero:
- Puede **confundir a futuras auditorías/herramientas** (grep/find recursivos la ven).
- Ocupa 27 MB innecesarios en el árbol.
- **Recomendación:** `lake clean` de peanolib o borrado manual de `.lake/packages/peanolib`
  (Lake lo recreará como referencia al path si hace falta).

---

## Parte 4 — Auditoría de la documentación

### 4.1 Corregido desde la auditoría del 2026-07-12 (crédito)

| Hallazgo previo | Estado |
|---|---|
| README normalizaba `Classical.choice` (contradecía M-1) | ✅ corregido (`d61c615`) — ahora “cero `Classical`” |
| `Classical.byContradiction` activo en `Irrational.lean:395` | ✅ eliminado (`b34de4b`), reescrito constructivo + añadido al gate |
| `REFERENCE.md`: 3 filas fantasma Reals + IDs duplicados 108c–f + barrel Rationals con 4 deps | ✅ corregido (filas reales, IDs únicos, 19 deps) |
| `NEXT_STEPS.md`/`NEXT-STEPS.md` duplicados y contradictorios | ✅ `NEXT_STEPS.md` (guión bajo) borrado; queda el canónico con guión |
| 13 ficheros scratch/temp + `fix-ref.ps1` en la raíz | ✅ eliminados (raíz limpia: solo `AczelSetTheory.lean`, `Main.lean`, `lakefile.lean`) |
| `CURRENT-STATUS`: “0 sorry” falso | ✅ corregido a 14 en el resumen ejecutivo |

### 4.2 Aún incorrecto / desincronizado

**C-1 (medio-crítico). “0 warnings” es FALSO.** `README.md:8` y
`CURRENT-STATUS-PROJECT.md:23` afirman “0 errors, 0 warnings”. El build real emite **19
warnings** (5 variables no usadas + 14 sorry). Es 0 *errores*, no 0 *warnings*.

**C-2 (menor). Conteo de jobs desfasado.** README, CURRENT-STATUS y CHANGELOG dicen
**266 jobs**; el real es **273**.

**C-3 (medio). `CURRENT-STATUS-PROJECT.md` con contradicciones internas:**
- Enlace roto (línea 481): `See [NEXT_STEPS.md](NEXT_STEPS.md)` → apunta al fichero
  **borrado** (guión bajo).
- Doble “last updated”: cabecera **2026-07-12** vs. pie de página **2026-06-02**.
- El “Module Inventory” (VN 49, Algebra 23, Integers 9, Topology 5) **contradice** la
  sección “Architecture” del **mismo fichero** (VN 35, Algebra 9, Integers 7, Topology 4).
- La tabla `Integers/` lista 9 módulos y **omite** `Canonical`, `HFInt`, `HFIntOps`
  (README dice 12).
- El “Module Inventory” **omite por completo** `Rationals/` (21) y `Reals/` (1)
  — reconocido en la nota de cabecera, pero sigue siendo un hueco.

**C-4 (medio). `CHANGELOG.md` sin historial de creación de `Rationals/`·`Reals/`.** La
entrada 2026-07-12 documenta las *correcciones* de auditoría, pero **no** existe entrada
para el desarrollo del subsistema completo (HFRat, Newton-Raphson, Bisection, Convergence,
Archimedean, Irrational, Series, Polynomial — commits del 5–8 de julio).

**C-5 (medio, NUEVO — no estaba en la auditoría del 07-12). 44 ficheros `.lean` sin
cabecera de copyright**, violando `AI-GUIDE.md §21` (“Todos los archivos .lean sin
excepción deben comenzar con [bloque copyright]”). ≈22 % del árbol. Incluye barrels
(`VN.lean`, `CList.lean`, `PList.lean`, `Algebra.lean`, `Integers.lean`, `Topology.lean`,
`Notation.lean`), `HFSets.lean`, varios `Axioms/*`, `Operations/*`, `Topology/*`,
`Rationals/*`, `VN/*`. (Verificado: `head -8` de `HFSets.lean`/`VN.lean`/`Archimedean.lean`
empieza directamente por `import`.)

**C-6 (menor). Timestamps sin `HH:MM`.** `AI-GUIDE.md §20` exige `YYYY-MM-DD HH:MM` en
toda la doc técnica; prácticamente ningún documento lo cumple (usan solo `YYYY-MM-DD`).

**C-7 (menor, reconocido). Nodos temáticos y matrices sin regenerar:**
- `doc/REFERENCE-Rationals.md` no cubre `HFRatCauchyAlgebra`, `Series`, `Polynomial`, `Reals/`.
- `AUDIT-MODULE-MATRIX.md` sin regenerar desde 2026-06-10.
- `DECISIONS.md` (cabecera 2026-06-10): sin ADR que registre la extensión Fase 5 del gate
  ni el hito “Peano cero-Classical” (que hace obsoleta la preocupación de M-5 sobre módulos
  no-constructivos de peanolib).

**C-8 (higiene). `.gitignore` con `/.worktrees` corrupto en UTF-16** (bytes nulos) —
reportado el 07-12, sin verificar corrección en esta pasada.

---

## Parte 5 — Auditoría de dependencias OCULTAS de `Classical` (tarea 5)

### 5.1 Contexto: qué descubrió Peano

En su ADR-017 Fase C, Peano documentó **dos clases de `Classical` oculto** invisibles a
`grep 'Classical\.'`:

1. **Primitivas del núcleo (Lean 4.31).** `String.drop` / `String.extract` /
   `String.toList` **dependen de `Classical.choice` en el kernel**. Peano reescribió sus
   instancias `Repr` (`tupleReprInner`, `natsTupleReprInner`, `HTupleRepr`) para evitarlas
   (Fase C.6, `Tuple.lean:152-218`).
2. **Fallback táctico silencioso.** `by_cases` / `decide` / `omega` / `simp` sobre una
   proposición **sin instancia `Decidable` en contexto** cae en `Classical.propDecidable`
   → `Classical.choice`, **sin que “Classical” aparezca en el código** (Fase C.9: 2 de 5
   hallazgos fueron así). El caso paradigmático: `by_cases` sobre `∃/∀ … P …` con `P`
   arbitrario o cuantificador no acotado.

Peano respondió con `ConstructiveCheck.lean` (**2023 líneas**), que corre
`#assert_constructive` sobre **todo símbolo exportado** del proyecto (cobertura exhaustiva),
no sobre una lista curada.

### 5.2 Metodología aplicada a AczelSetTheory

El gate actual de Aczel (`Meta/AxiomCheck.lean`) solo cubre **~30 símbolos** — insuficiente.
Se ejecutó un **barrido exhaustivo** con un meta-comando que recorre TODA declaración cuyo
módulo de definición está bajo `AczelSetTheory.*` (filtrando por `env.const2ModIdx`,
saltando nombres internos) y aplica `Lean.collectAxioms`, reportando dependencias de
`Classical.choice` y `sorryAx`:

```lean
elab "#audit_hidden_classical" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut classicalHits : Array Name := #[]
  let mut sorryHits : Array Name := #[]
  for (name, _info) in env.constants.toList do
    if name.isInternalDetail then continue
    let some modIdx := env.const2ModIdx[name]? | continue
    unless (`AczelSetTheory).isPrefixOf mods[modIdx.toNat]! do continue
    let axs ← collectAxioms name
    if axs.contains ``Classical.choice then classicalHits := classicalHits.push name
    if axs.contains ``sorryAx then sorryHits := sorryHits.push name
  ...
```

**Resultado:** 3043 declaraciones propias escaneadas → **9 con `Classical.choice`**,
**21 con `sorryAx`**.

### 5.3 Los 9 símbolos con `Classical.choice` oculto

Confirmados individualmente con `#print axioms`:

#### Clase A — heredado de Peano (2 símbolos)

| Símbolo Aczel | Axiomas | Raíz |
|---|---|---|
| `VN.vN_wilson` | `{propext, Classical.choice, Quot.sound, native_decide.ax…}` | **`Peano.Wilson.wilson`** |
| `VN.vN_wilson_modEq` | idem | idem |

- Raíz confirmada: `Peano.Wilson.wilson` → `{propext, Classical.choice, Quot.sound,
  Peano.Wilson.factorial_pred_pred_one._native.native_decide.ax_1_4}`.
- **Doble contaminación:** además de `Classical.choice`, arrastra un **axioma
  `native_decide`** (confianza en el compilador) — que está **fuera** incluso del
  footprint diana `{propext, Quot.sound}`. Es una tercera clase de axioma no-constructivo.
- Coherente con el propio `Peano/ConstructiveCheck.lean:302-308`, que **deja Wilson sin
  `#assert_constructive`** (nunca se certificó constructivo). `Peano.Wilson.modInv` (la API
  expuesta por ADR-017) **sí** es limpia (`{propext, Quot.sound}`).
- **Consumido en Aczel por** `VN/FermatVN.lean` (`vN_wilson`, `vN_wilson_modEq`).

#### Clase B — nativo de AczelSetTheory (7 símbolos)

`{propext, Classical.choice, Quot.sound}` (sin `native_decide`) — patrón “by_cases/decide
sobre proposición no decidible en contexto”:

| Símbolo | Módulo | Táctica sospechosa (línea) |
|---|---|---|
| `HFAlgebra.orbitOf_eq_or_disjoint` | `Algebra/Sylow.lean` | `by_cases hdisj : ∀ x, ¬(…)` sobre **∀ no acotado** (`:1690`) |
| `HFTopology.HFTopSpace.interior_exterior_boundary_partition` | `Topology/Interior.lean` | `by_cases` sobre `isInteriorPt`/`isExteriorPt` sin `Decidable` (`:221-223`) |
| `HFSet.mem_wf` | `Axioms/Rank.lean` | instancia `WellFounded (·∈·)` / `by_cases x ∈ A` con `Decidable` fuera de scope (`:158-174`) |
| `HFSet.mem_rank_lt` | `Axioms/Rank.lean` | idem cadena `rank`/`by_cases` (`:158-163`) |
| `HFAlgebra.HFMatrixRing` | `Algebra/HFMatrix.lean` | `by_cases h : k = j` sobre índices (`:149,164,176`) |
| `PList.get_ext` | `PList/*` | `by_cases`/indexado sin instancia (por confirmar línea) |
| `FinList.extEq` | `HFListOps.lean`/`HFList.lean` | `by_cases`/extEq sin instancia (por confirmar línea) |

**Raíz genérica (Clase B):** el patrón Peano-Fase-C.9. El caso más nítido y confirmado es
`Algebra/Sylow.lean:1690`, `by_cases hdisj : ∀ x, ¬ (x ∈ orbitOf … ∧ x ∈ orbitOf …)`: un
`∀ x : HFSet` es **infinito**, no tiene `Decidable` automático → `Classical.propDecidable`
→ `Classical.choice`. Análogo en Topology (predicados topológicos sin instancia). En Rank y
HFMatrix, aunque `∈`/`=` sí son decidibles, la instancia `Decidable` puede no estar en el
scope del módulo en el punto del `by_cases` (dependiente del orden de `import`), forzando el
fallback clásico — exactamente el subcaso `decidableExistsLe`/`decidableBExLe_of_bool` que
Peano tuvo que arreglar en su Fase C.6.

> **Nota importante sobre el gate.** `HFSet.wf_induction` (cubierto por el gate) es limpio,
> pero `HFSet.mem_wf` (la instancia `WellFounded` hermana) es sucio. Coexisten dos caminos
> de buena-fundación, uno limpio y uno contaminado. Cualquier consumidor de `mem_wf` hereda
> `Classical.choice` sin que el gate lo note.

### 5.4 Los 21 símbolos con `sorryAx` (radio de impacto de los 14 sorry)

Todos en `Rationals/`·`Reals/`; útil para dimensionar la deuda:

`ℝ₀.sqrt2_irrational`, `ℝ₀.sqrt2CauchySeq`, `ℝ₀.sqrt2CauchySeq_has_no_limit`,
`ℝ₀.sqrt2Seq_isCauchy`, `ℚ₀.newton_seq_eventually_lt`, `ℚ₀.newton_seq_apart_gt`,
`ℚ₀.newton_seq_step_bound`, `HFRat.Polynomial.{add,mul,smul,monomial,instAdd,instMul}`,
`HFRat.{sum_add,sum_mul_left,sum_arithmetic,sum_geometric}`,
`ℚ₀.{sum_add,sum_mul_left,sum_arithmetic,sum_geometric}`.

Es decir: los 14 huecos de `Rationals/Series.lean`·`Polynomial.lean`·`Irrational.lean` +
`Reals/Incompleteness.lean` contaminan **21 símbolos públicos** aguas abajo (incluido el
teorema-objetivo `sqrt2_irrational`).

---

## Parte 6 — Recomendaciones priorizadas

### Prioridad 1 — Pureza constructiva (M-1)

1. **Convertir el gate en exhaustivo** (como `Peano/ConstructiveCheck.lean`). Adoptar el
   meta-comando `#audit_hidden_classical` de §5.2 (que también detecta `native_decide` y
   `sorryAx`) como parte del build. Sin esto, cada nueva prueba puede reintroducir Classical
   oculto sin detección.
2. **Arreglar los 7 nativos (Clase B).** Patrón general: añadir `[DecidablePred P]` /
   instancias `Decidable` reales, o sustituir `by_cases` sobre `∀/∃` no acotados por una
   descomposición constructiva. Empezar por `Algebra/Sylow.lean:1690` (confirmado) y
   `Axioms/Rank.lean` (infraestructura nuclear: `mem_wf`).
3. **Decidir la política sobre `VN.vN_wilson` (Clase A).** O bien (a) certificar
   constructivamente `Peano.Wilson.wilson` en Peano (eliminando su `Classical.choice` y su
   `native_decide`) — trabajo en Peano, hoy frozen; o (b) marcar explícitamente
   `vN_wilson`/`vN_wilson_modEq` como excepción documentada (como Peano hizo con
   Initiality/PureAxioms) si Wilson se considera metateórico. **Ojo:** el axioma
   `native_decide` es aparte y también viola el footprint diana.

### Prioridad 2 — Documentación

4. Corregir “0 warnings” → “0 errores; N warnings” y **266 → 273 jobs** en README /
   CURRENT-STATUS / CHANGELOG (C-1, C-2).
5. Sanear `CURRENT-STATUS-PROJECT.md`: enlace roto a `NEXT_STEPS.md`, doble fecha,
   contradicción Inventory↔Architecture, tabla Integers incompleta, ausencia de
   Rationals/Reals (C-3).
6. Añadir al `CHANGELOG` el historial de creación de `Rationals/`·`Reals/` (C-4).
7. Añadir la cabecera de copyright a los **44 ficheros** que la omiten (C-5).

### Prioridad 3 — Higiene

8. Eliminar la copia stale `.lake/packages/peanolib` (27 MB) (§3.5).
9. Regenerar `AUDIT-MODULE-MATRIX.md` y `doc/REFERENCE-Rationals.md`; añadir ADR que
   registre Fase 5 del gate y el hito Peano-cero-Classical (C-7).
10. Corregir `.gitignore` UTF-16 (C-8).

---

## Notas metodológicas

- Build real: `lake build AczelSetTheory` → 273 jobs, exit 0.
- Footprint: `#print axioms` sobre símbolos clave.
- Barrido exhaustivo: meta-comando `Lean.collectAxioms` sobre 3043 declaraciones propias.
- Todos los scripts de auditoría temporales (`_audit_*.lean`, `build_report.txt`) fueron
  **borrados** tras su uso; el working tree quedó limpio. Este informe es el único
  artefacto nuevo persistido.
- La memoria de proyecto (`MEMORY.md`) indica “182 ficheros, 0 sorry”; el real es **204
  ficheros, 14 sorry** — la memoria debe actualizarse.
