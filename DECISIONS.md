# Design Decisions — AczelSetTheory

**Last updated:** 2026-07-20
**Author**: Julián Calderón Almendros

Architectural Decision Records (ADR) for this project.
Each entry records *what* was decided and *why*, for future reference.

> ADRs marcados **[heredado de Peano]** fueron adoptados originalmente en el proyecto
> predecesor y se aplican sin cambios a AczelSetTheory.

---

## ⚠️ MANDATORIES (reglas vinculantes — lectura obligatoria)

Estas reglas son **vinculantes**, no preferencias de estilo. Su incumplimiento es un
**defecto de build**. [`AI-GUIDE.md`](AI-GUIDE.md) redirige obligatoriamente aquí antes
de tocar cualquier `.lean`. Cada regla enlaza a su ADR justificativo.

| # | MANDATORY | ADR | Verificación |
|---|---|---|---|
| **M-1** | **Lógica constructiva pura: CERO `Classical.*`.** Prohibido `Classical.byContradiction`, `Classical.em`, `Classical.propDecidable`, `Classical.choice`, `Classical.choose`, `open Classical`. Usar `Decidable.byContradiction`, `by_cases` (sobre instancia `Decidable`), `decidable_of_iff`. Footprint diana `#print axioms ⊆ {propext, Quot.sound}`. | [ADR-018](#adr-018), [ADR-020](#adr-020) | gate EXHAUSTIVO `Meta/AxiomCheck.lean` (`#assert_constructive_footprint`) — barre las 3044 decls propias; **baseline VACÍO (0)** desde 2026-07-15: los 11 símbolos iniciales saneados (4 vía Peano commit `9b6241d`). Footprint ⊆ {propext, Quot.sound} en todo el proyecto + Peano |
| **M-2** | **`ℕ₀` (peanolib) siempre, nunca `Nat`** de Lean salvo kernel estrictamente inevitable (`sizeOf`, literales internos, `omega`). Aritmética/orden desde peanolib; metas con `omega₀`. | [ADR-018](#adr-018) | revisión + grep `\bNat\b` |
| **M-3** | **Medidas de terminación lexicográficas `(Σ sizeOf, fase)`, NUNCA aritméticas ponderadas** (`sizeOf·k + peso`): estas últimas introducen `Classical.choice`. | [ADR-018](#adr-018) | gate + revisión de `termination_by` |
| **M-4** | **Reutilizar los tipos públicos de peanolib** (`ℕ₁ = {n:ℕ₀ // n≠𝟘}`, `ℕ₂ = {n:ℕ₁ // n.val≠𝟙}`, …). **Prohibido redefinir subtipos privados que ya existen en Peano.** | [ADR-019](#adr-019) | revisión + grep `{.*: ℕ₀ //` |
| **M-5** | **Dependencia matemática EXCLUSIVA de peanolib** para los naturales. `Nat` no es dependencia conceptual. Evitar módulos no-constructivos de peanolib (FSet/Perm/Sign/Wilson…) cuando contaminen el footprint. | [ADR-018](#adr-018) | revisión de imports |

---

## ADR-000: Peano congelado — toda la teoría nueva en AczelSetTheory

**Date**: 2026-05-30
**Status**: Accepted (directiva del usuario, reiterada)

**Decision**: El proyecto predecesor **Peano (`peanolib`) no desarrollará más teoría
"hacia arriba"**. Solo se admite trabajo **fundacional/metamatemático**: la aritmética
de Robinson `Q` y su extensión **ROBINSON_PlusPlus**. **Toda la teoría matemática nueva**
(conteo, signatura de permutaciones, álgebra adicional, topología, …) se construye
**directamente sobre `HFSet` en AczelSetTheory**, en la capa nativa — *no* vía el
transporte `congrArg vN` de los módulos `VN/`.

**Why**: La fase de "paridad Peano↔Aczel" (replicar Peano en Aczel vía el embedding de
Von Neumann) fue *bootstrapping* ya completado. Aczel tiene mayor potencia expresiva;
una vez pagado el coste de construir su infraestructura nativa (cardinalidad, grupos,
cocientes…), la teoría nueva se hace directamente ahí, sin la doble escritura
Peano→VN.

**Consequences**:
- No crear módulos de teoría nueva en `peanolib` ni en `AczelSetTheory/VN/` (transporte).
  La teoría nueva vive en capas nativas (`AczelSetTheory/Combinatorics/`, paralela a
  `Algebra/` y `Topology/`).
- Los stubs `VN/CountingVN.lean` y `VN/SignVN.lean` (espejos de stubs de Peano que nunca
  se materializarán) quedan huérfanos → re-etiquetar o retirar.
- Los módulos `VN/` existentes se conservan como puente histórico de la fase de bootstrapping.

---

## ADR-001: No Mathlib dependency

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: This project does not depend on Mathlib.

**Rationale**: Educational and research goals — formalize set theory from scratch using only
Lean 4's core. Building all infrastructure (CList, HFSet, quotient type, Zermelo axioms) without
external libraries ensures that every result is traceable to first principles and that
the dependency footprint remains minimal.

**Consequences**: All necessary infrastructure must be built from scratch. Standard library
tactics (`omega`, `decide`) are allowed; Mathlib tactics and theorems are not.

---

## ADR-002: autoImplicit = false [heredado de Peano]

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: `moreServerArgs := #["-DautoImplicit=false"]` is set in `lakefile.lean`.

**Rationale**: Explicit type annotations prevent accidental universe polymorphism issues
and make code easier to read and maintain.

**Consequences**: All variables must be explicitly declared or annotated. Implicit arguments
must appear in `{...}` or `[...]` binders.

---

## ADR-003: File locking system [heredado de Peano]

**Date**: 2026-04-08
**Status**: Accepted

**Decision**: Use `git-lock.bash` + `locked_files.txt` + pre-commit hook to prevent
accidental edits to completed modules.

**Rationale**: Lean 4 proofs are fragile — small changes to completed modules can break
dependent proofs. The locking system makes this explicit. Bash scripts are cross-platform
(Windows Git Bash + Linux/macOS).

**Consequences**: Workflow requires locking/unlocking files before committing. See AI-GUIDE.md §20.

---

## ADR-004: Mathlib naming conventions [heredado de Peano]

**Date**: 2026-04-08
**Status**: Accepted

**Decision**: All identifiers follow Mathlib4 naming conventions as documented in
NAMING-CONVENTIONS.md.

**Rationale**: Consistency with the broader Lean 4 ecosystem. Makes theorems discoverable
by name pattern (`subject_predicate`). Facilitates future Mathlib integration if desired.

**Consequences**: See NAMING-CONVENTIONS.md for the full dictionary and 12 formation rules.

---

## ADR-005: Module directory = AczelSetTheory

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: Source modules live in `AczelSetTheory/` while the lean_lib name is
`«AczelSetTheory»` and the root file is `AczelSetTheory.lean`. Imports use `AczelSetTheory.`
prefix. Namespaces use `HF` prefix (e.g., `HFSet`, `HFAlgebra`).

**Rationale**: Historical architecture from the project's inception. The `AczelSetTheory`
directory name reflects the library's mathematical content (Aczel's set theory over
hereditarily finite sets).

**Consequences**: Scripts (`gen-root.bash`, `new-module.bash`) detect the module directory
from `Glob.submodules` in lakefile.lean.

---

## ADR-006: CList as canonical list representation for sets

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: Sets are represented as canonical sorted lists without duplicates (`CList`).
`CList` is a `structure` with a `List` and a `Sorted` + `Nodup` invariant.

**Rationale**: The sorted-list approach keeps all operations computable (no `noncomputable`
needed), gives canonical representatives for equality (`CList.extEq`), and is directly
amenable to decidable equality. The Quotient-only approach would make `DecidableEq` noncomputable.

**Consequences**: All `CList` operations (insert, union, intersection, filter) must preserve
the sorted+nodup invariant. `HFSet` is then defined as `Quotient CList.Setoid` for
set-theoretic extensionality.

---

## ADR-007: HFSet as quotient type over CList

**Date**: 2026-04-06
**Status**: Accepted

**Decision**: The Zermelo axioms are derived as theorems over the `HFSet` quotient type
(`HFSet = Quotient CList.Setoid`), not postulated as axioms.

**Rationale**: Maximum rigor — all 8+ Zermelo axioms are proven theorems, not assumptions.
The quotient construction gives extensional equality (`∀ x, x ∈ A ↔ x ∈ B → A = B`) for free.

**Consequences**: Operations must be defined via `Quotient.lift`/`Quotient.lift₂` and proven
well-defined. Membership proofs use `rw [HFSet.mem_...]` patterns (never `.mpr`/`.mp` directly
on quotient membership lemmas — they must go through `rw` first).

---

## ADR-008: Separation of Operations/ and Axioms/

**Date**: 2026-04-07
**Status**: Accepted

**Decision**: The project is split into `Operations/` and `Axioms/` modules for all HFSet
functionalities (Union, Separation, Intersection, Setminus, Pair, Powerset, etc.).

**Rationale**: `Operations/` handles the CList-level implementation and the lift to HFSet.
`Axioms/` is devoted solely to stating the canonical form of the set-theory axiom over the
HFSet quotient representation, without worrying about implementation details.

**Consequences**: The architecture is strongly modular. Each set-theoretic concept has two
files: an implementation file in `Operations/` and an axiom file in `Axioms/`. This separation
makes locating proof failures significantly easier.

---

## ADR-009: Thematic subdirectories for module organization [heredado de Peano]

**Date**: 2026-04-07
**Status**: Accepted

**Decision**: Modules are grouped into thematic subdirectories: `CList/`, `Operations/`,
`Axioms/`, `PList/`, `VN/`, `HFSets/`, `Algebra/`, `Integers/`, `Topology/`.

**Rationale**: With 118+ modules, flat organization is unmanageable. Subdirectories mirror
mathematical domains and enable focused navigation.

**Consequences**: Imports use full paths (`AczelSetTheory.Axioms.Union`). `AczelSetTheory.lean`
barrel file imports all sub-modules via intermediate barrels (`Axioms.lean`, `Operations.lean`,
etc.).

---

## ADR-010: Documentation tree doc/REFERENCE-{tema}.md [heredado de Peano]

**Date**: 2026-05-10 (adoptado en AczelSetTheory 2026-05-22)
**Status**: Accepted

**Decision**: Technical export documentation is organized at two levels: `REFERENCE.md` as
root index (module table, namespace, build metrics) and `doc/REFERENCE-{tema}.md` as thematic
nodes (12 fields per symbol: type, signature, module, importance). The `doc/` directory was
first introduced in Peano in this date with `REFERENCE-GroupTheory.md`.

**Rationale**: `REFERENCE.md` as monolith was growing unmanageable (>1000 lines). The tree
architecture allows focused navigation, domain independence and incremental per-module updates.
Each thematic node is self-contained for code review within its domain.

**Consequences**: Every new `.lean` file must be projected into the corresponding thematic
node (`doc/REFERENCE-{tema}.md`). If the node does not exist, create it. `REFERENCE.md` index
is updated with the new module row and job count. The `doc/` directory is versioned.

---

## ADR-011: mapOn_bijective_cast — bridge lemma with free variable [heredado de Peano]

**Date**: 2026-05-10
**Status**: Accepted

**Decision**: When `▸` (transport by equality) over a `MapOn` fails at the usage site because
both sides of the equality are concrete terms (constructed via `sortFSetList` or similar),
extract a private general lemma with free variables `{B C : FSet β}` where `subst heq` works:

```lean
private theorem mapOn_bijective_cast
    {α β : Type} [DecidableEq α] [LT α] [DecidableEq β] [LT β]
    {A : FSet α} {B C : FSet β} (f : MapOn A B) (h : f.Bijective) (heq : B = C) :
    (heq ▸ f).Bijective := by
  subst heq; exact h
```

**Rationale**: Lean 4 cannot discharge `sortFSetList (...) = sortFSetList (...)` automatically
for `cases`/`subst`/`rcases rfl` at a concrete usage site. Dependent elimination needs the
variable to be free (metavariable) in the local context. By extracting to a lemma where
`B : FSet β` is genuinely free, `subst heq` substitutes `C := B` without issues.

**Consequences**: Reusable pattern whenever `f.Bijective : (heq ▸ f).Bijective` or similar
must be transported and `heq` connects concrete types. In those cases, direct solutions
(`cases heq`, `subst heq`, `rcases rfl`, `▸` in term mode) will always fail; the bridge
lemma is necessary.

---

## ADR-012: ⚠️ residuales en paridad Peano↔Aczel — política de "embebido documentado"

**Date**: 2026-06-05
**Status**: Accepted (FASE B / M1B-T1)

**Context**: La matriz de paridad `doc/REFERENCE-Paridad-Peano-Aczel.md` arrastraba dos
módulos marcados ⚠️ ("portado parcialmente o con enfoque distinto"):

1. **§1 `PeanoNat/WellFounded.lean`** — Peano lo expone como módulo dedicado; en
   AczelSetTheory `well_founded_lt` sobre `ℕ₀` se obtiene del kernel de Lean 4 (los
   inductivos generan principios de buena fundación automáticos) y se usa puntualmente
   en `VN/Basic.lean` y derivados sin necesidad de un módulo `WellFoundedVN.lean`.
2. **§6 `ListsAndSets/EquivRel.lean`** — Peano construye `EquivRelOn`, `classOf`,
   etc., como teoría manual; en AczelSetTheory toda la maquinaria de equivalencia está
   absorbida por `Quotient` del kernel (`HFSet := Quotient CList.Setoid`,
   `CList/ExtEq.lean`, `CList/SetEquiv.lean`).

**Decision**: Para ambos casos se **adopta la opción (b) "embebido documentado"** del
plan FASE B §4.1: no se crea módulo dedicado, no se reformula como `Axioms/*.lean`, no
se descarta del registro. Se actualiza la matriz de paridad para etiquetar estas filas
como ✅ con el sufijo **"[embebido]"** y referencia a este ADR, dejando explícito que
la paridad se cumple por absorción en infraestructura nativa (kernel + cocientes) en
lugar de un módulo espejo.

**Rationale**:
- Crear `Axioms/WellFoundedNat.lean` o `Axioms/EquivRel.lean` *ad hoc* duplicaría sin
  ganancia: el kernel ya provee `WellFounded`/`Acc` y `Quotient` con sus principios.
- Descartarlos rompería la trazabilidad histórica con Peano.
- El criterio rector es: *paridad de **resultados**, no paridad de **organización de
  archivos***. Un teorema cubierto por el kernel sigue siendo "cubierto".

**Consequences**:
- `doc/REFERENCE-Paridad-Peano-Aczel.md` queda **0 ⚠️** tras actualizar §1 y §6.
- Se establece precedente: futuros casos donde Peano tenga un módulo y AczelSetTheory
  resuelva el contenido vía kernel/cociente serán ✅ [embebido] + cita de ADR-012.
- No hay cambio de código; cambio puramente documental.

---

## ADR-013: Aritmética fundacional `ℕ₀` desde Peano ≠ "teoría nueva en Peano"

**Date**: 2026-06-05
**Status**: Accepted (FASE B / M1B-T2, refinamiento de ADR-000)

**Context**: ADR-000 congeló Peano e impuso que "toda la teoría matemática nueva se
construye directamente sobre `HFSet`". Durante la auditoría de M1B-T2 se observó que
`AczelSetTheory/Algebra/CosetCount.lean` contiene:

```lean
import Peano.PeanoNat.Arith
open Peano.Arith
```

usado para operaciones básicas (`mul`, `add`) sobre `ℕ₀ = Peano.PeanoNat`. El plan
inicial de FASE B sugería "eliminar la indirección residual a Peano". Tras revisión,
esa simplificación era **apresurada**: `ℕ₀` *es* el tipo natural de Peano, y su
aritmética básica es una capa **fundacional**, no "teoría nueva".

**Decision**: ADR-000 **no prohíbe consumir aritmética fundacional de Peano** sobre
`ℕ₀` desde AczelSetTheory. Lo que prohíbe es **desarrollar teoría nueva** dentro del
proyecto Peano. Por tanto:

- `import Peano.PeanoNat.Arith` y `open Peano.Arith` son **lícitos** cuando se usan
  exclusivamente para operaciones aritméticas básicas sobre `ℕ₀` (`+`, `*`, `≤`,
  `add_assoc`, `mul_comm`, etc.).
- `Algebra/CosetCount.lean` se conserva **sin migrar**: su dependencia es legítima.
- Se considera "teoría nueva en Peano" cualquier definición/teorema **añadido a
  archivos Peano** posterior al congelamiento (2026-05-10), o cualquier puerto VN
  desarrollado para soportar nueva teoría.

**Rationale**:
- `ℕ₀` está definido en Peano por la arquitectura del proyecto (Peano-as-foundation).
  Reimplementar `add`/`mul` sobre `ℕ₀` desde AczelSetTheory sería duplicación pura.
- La distinción "consumir fundación" vs "extender teoría" es operativa: la primera
  es apilar trabajo nuevo *encima* de bases congeladas; la segunda añadiría trabajo
  *dentro* de las bases.
- Los módulos `VN/` de AczelSetTheory ya cumplen el rol de "espejo aritmético": no
  necesitamos eliminar `import Peano.PeanoNat.Arith` mientras `mul`/`add` de `ℕ₀`
  sigan viniendo de allí.

**Consequences**:
- `Algebra/CosetCount.lean` **no se migra** en M1B; queda registrado en plan.
- Cualquier futura auditoría que detecte `import Peano.PeanoNat.*` en código Aczel
  debe usar este ADR para distinguir consumo legítimo (✅) de violación de ADR-000
  (❌, p.ej. desarrollar nuevos lemas aritméticos *dentro* de `Peano/`).
- M1B-T2 se cierra como **auditoría sin cambios de código**.

---

## ADR-014: ℤ₀ como único entero canónico (sin `HFInt`) + representante normal

**Date**: 2026-06-05
**Status**: Accepted (FASE B / M4B, decisión del usuario 2026-06-05)

**Context**: Durante el diseño de FASE B se planteó si introducir un tipo paralelo
`HFInt` (entero como `HFSet`) además de `ℤ₀ := Quotient intSetoid`. Mantener dos tipos
duplicaría API, biyecciones y lemas algebraicos sin ganancia conceptual.

**Decision**:
1. **No se introduce `HFInt`.** El único entero del proyecto es `ℤ₀`.
2. Para soportar igualdad decidible eficiente y representación normalizada se añade
   en `Integers/Canonical.lean` una **función de representante canónico** que devuelve
   el par `(0, n)` (negativos), `(0, 0)` (cero) o `(n, 0)` (positivos).

**API mínima** (a desarrollar en M4B):
- `canonicalRep : ℕ₀ × ℕ₀ → ℕ₀ × ℕ₀`
- `canonicalRep_idempotent`
- `canonicalRep_equiv` (relación con `intEq`)
- `canonicalRep_unique` (∀ p q, intEq p q → canonicalRep p = canonicalRep q)
- `ℤ₀.repr : ℤ₀ → ℕ₀ × ℕ₀` (lift al cociente)
- `ℤ₀.mk_repr` (sección)

**Rationale**:
- Un entero como par `(a-b)` con `b ≤ a` o `(b-a)` con `a ≤ b` da una representación
  normal trivial sin cambiar el tipo subyacente.
- Permite definir `DecidableEq ℤ₀` reduciendo a igualdad de pares canónicos sin
  invocar la maquinaria del cociente en cada chequeo.
- Compatible con M5B.0 (Bézout) y M5B (cuerpo `ZModN p`): los algoritmos extendidos
  pueden operar directamente sobre representantes canónicos.

**Consequences**:
- Cualquier referencia a "entero como `HFSet`" en documentación o pruebas se redirige
  a `ℤ₀` con `canonicalRep` cuando se necesite forma normal.
- ADR-014 supersede cualquier diseño previo no escrito sobre `HFInt`.
- `Integers/Canonical.lean` queda como módulo dedicado al representante; `Basic.lean`
  no se reescribe.

---

## ADR-015: Política de notaciones con ámbito (scoped notations, estilo Mathlib)

**Date**: 2026-06-06
**Status**: Accepted

**Context**:
La biblioteca dependiente `peanolib` declara `notation a "+" b => Peano.Add.add a b`
(y análogamente para `*`) **sin `scoped`**, haciendo que estas notaciones sean globales
en Lean 4. Esto causa ambigüedades inmediatas en cualquier módulo que opere sobre tipos
distintos de `ℕ₀` (p.ej. `ℤ₀`, `ℚ₀`) porque `a + b` puede resolverse como
`HAdd.hAdd` o como `Peano.Add.add`, generando errores "overloaded, failed to synthesize".
El problema afecta a todos los módulos de `Integers/` y `Integers/Rationals/`.

Existen dos estrategias canónicas en Lean 4 para evitar esto:
- **A. Namespaces anidados** (`ℤ₀.Add.add` vs `ℕ₀.Add.add`): adoptado por peanolib.
- **B. Scoped notations**: `scoped infixl:65 " + " => Add.add` dentro de `namespace ℤ₀`.

**Decision**:
Este proyecto adopta la **Opción B — scoped notations** (estilo Mathlib) como
estrategia oficial para todos los tipos nuevos que se introduzcan.

La migración completa de los módulos existentes (`ℤ₀`, `ℚ₀`) queda pendiente (coste
alto, ~1000 líneas afectadas). **Durante el período de migración**, la regla de
compatibilidad es:
> En enunciados de teoremas que mezclen `ℤ₀`/`ℚ₀` con `ℕ₀`, usar siempre
> `Add.add`, `Mul.mul`, `Neg.neg` explícitos — nunca `+`, `*`, `-`.

**Rationale**:
- Scoped notations son el estándar de Mathlib y la recomendación oficial de Lean 4.
- Son ergonómicas: activas dentro del namespace, transparentes fuera.
- El coste de la refactorización completa es proporcional al tamaño del proyecto;
  para un proyecto en crecimiento activo, se paga progresivamente.
- La regla de transición (usar funciones base explícitas) es mecánica y verificable
  automáticamente por el elaborador de Lean.

**Consequences**:
- Todo tipo nuevo (p.ej. `ZModN`) declara sus operadores con `scoped notation`.
- Los módulos existentes (`Basic.lean`, `Order.lean`, etc.) se migran oportunamente,
  módulo a módulo, sin bloquear el avance matemático.
- El REFERENCE y AI-GUIDE reflejan esta política (ver regla 3.5 en AI-GUIDE.md).
- Queda registrado que `peanolib` usa Opción A (namespaces anidados) y AczelSetTheory
  usa Opción B; la interfaz entre ambos se gestiona con `open` selectivo.

---

## ADR-016: Anillo cociente genérico sobre `HFRing` (no sobre `ℤ₀`)

**Date**: 2026-06-06
**Status**: Accepted

**Context**:
El plan M5B preveía construir `ZModN` (enteros módulo n) definiendo primero un
`HFRing_of_ℤ₀ : HFRing` y luego su cociente. Esto es **imposible**: el portador de
un `HFRing` es `R : HFSet`, y `HFSet := Quotient CList.Setoid` es
**hereditariamente finito**. Como `ℤ₀` es infinito, no puede ser el portador `R` de
ningún `HFRing`. No existe en el proyecto ningún `HFRing` concreto de carrier
infinito (sólo conversiones `toHFRing` de estructuras ya finitas).

**Decision**:
Se construye un **constructor genérico de anillo cociente** sobre cualquier
`HFRing` arbitrario, no ligado a `ℤ₀`:
- `HFIdeal (rng : HFRing)`: ideal bilátero (subgrupo aditivo + absorción bilateral).
- `HFRing.quotient (rng) (J : HFIdeal rng) : HFRing`: el anillo cociente `R/I`.

La parte **aditiva** se hereda íntegra de `quotientGroup rng.toAdditiveHFGroup
J.toAddSubgroup hn` (todo ideal es normal en el grupo aditivo abeliano). Sólo se
define la **multiplicación** sobre cosets, con buena-definición vía la absorción del
ideal: `(g'·h') − (g·h) = g'·(h'−h) + (g'−g)·h ∈ I`.

**Rationale**:
- Respeta la restricción de finitud hereditaria de `HFSet` sin hacks.
- Maximiza reutilización: toda la maquinaria de cosets/representantes de
  `QuotientGroup.lean` se aprovecha para la estructura aditiva.
- Es la construcción matemáticamente correcta y reutilizable (sirve para cualquier
  anillo finito futuro: `ZModN` sobre un `HFRing` finito de `ℤ/nℤ`, anillos de
  matrices finitas, etc.).

**Consequences**:
- `ZModN` sobre `ℤ₀` requerirá primero un `HFRing` **finito** que represente
  `ℤ/nℤ` (carrier `{0,…,n−1}` finito), y luego aplicar `HFRing.quotient` o una
  construcción directa; queda como trabajo futuro.
- El módulo `Integers/ZModN.lean` (esqueleto) no se desarrolla en esta fase.
- `HFRing.quotient` es no-conmutativo por defecto (igual que `HFRing`); el cociente
  de un anillo conmutativo es conmutativo, pero `HFRing` no rastrea conmutatividad.

---

## ADR-017: Exposición pública de `Wilson.modInv` en peanolib

**Date**: 2026-06-07
**Status**: Accepted

**Context**:
`ZModFieldP` requiere calcular el inverso multiplicativo de `a` en ℤ/pℤ usando la
fórmula de Fermat: `modInv p a = a^(p−2) mod p`. Esta función y sus lemas asociados
(`modInv_lt`, `modInv_mul`, `modInv_pos`) existían en peanolib como definiciones
**privadas** en `Peano.PeanoNat.NumberTheory.Wilson`. Sin exponerlos, la implementación
de `ZModFieldP` en AczelSetTheory no podía importar ni usar estos resultados.

**Decision**:
Se realiza un commit en peanolib (`0f5dd7b`) que hace públicos los cuatro símbolos:

- `Peano.Wilson.modInv (p a : ℕ₀) : ℕ₀` — `a^(p−2) mod p`
- `Peano.Wilson.modInv_lt (hp : Prime p) : modInv p a < p`
- `Peano.Wilson.modInv_mul (hp : Prime p) (ha_pos : 0 < a) (ha_lt : a < p) : a * modInv p a ≡ 1 [MOD p]`
- `Peano.Wilson.modInv_pos (hp : Prime p) (ha_ne : a ≠ 0) : 0 < modInv p a`

**Rationale**:
- `modInv` es la única manera computable de obtener el inverso en ℤ/pℤ sin recurrir
  a `Classical.choose` (que violaría el invariante `0 noncomputable def`).
- Los lemas privados ya estaban demostrados; el commit solo cambia visibilidad.
- ADR-001 (sin Mathlib) impide usar `ZMod` de Mathlib; la implementación propia
  en peanolib es la alternativa legítima.

**Consequences**:
- `Integers/ZModN.lean` puede importar `Peano.PeanoNat.NumberTheory.Wilson` y usar
  directamente `modInv`, `modInv_lt`, `modInv_mul`.
- Cualquier módulo futuro que necesite inverso modular en ℕ₀ debe usar esta API.
- Commit `0f5dd7b` está en `origin/master` de peanolib (verificado 2026-06-08).
- Este ADR documenta la razón por la que peanolib recibió un commit de "solo visibilidad"
  después del congelamiento declarado en ADR-000 — el congelamiento afecta a teoría nueva,
  no a la exposición de infraestructura ya existente.

---

## ADR-018: Pureza constructiva (cero `Classical`) + dependencia exclusiva de peanolib/ℕ₀

**Date**: 2026-06-10
**Status**: Accepted

**Context**: El motivo fundacional del proyecto es formalizar la teoría de conjuntos de
Aczel con **lógica intuicionista/constructiva pura** y aritmética propia (`ℕ₀` de peanolib).
Una auditoría de axiomas (`#print axioms`) reveló que **prácticamente todo el desarrollo
depende de `Classical.choice`**, incluso `HFSet.extensionality`. La raíz se localizó en
`CList.evalOp` (motor de `mem`/`subset`/`extEq`): su `termination_by` usa una **medida
ponderada `sizeOf·3 + opWeight`** con un paso recursivo (`.eq→.subset`) que no decrece el
argumento estructural; eso introduce `Classical.choice`, que `HFSet = Quotient CList.Setoid`
propaga a todo. (Verificado: `CList.lt`, con medida `sizeOf` pura, es limpio; peanolib es
limpio — `add_comm → [propext]`, `le_total → sin axiomas`.)

**Decision**:
1. **Cero `Classical.*`** en todo AczelSetTheory. Footprint diana de axiomas:
   `#print axioms ⊆ {propext, Quot.sound}` (ambos no-clásicos, compatibles con lógica
   intuicionista; no se exige eliminarlos). Toda prueba que use `Classical.byContradiction`/
   `em`/`propDecidable`/`choice`/`choose` se reconvierte a constructiva, **aunque no produzca
   una `noncomputable def`**.
2. **ℕ₀ (peanolib) siempre, nunca `Nat`** de Lean, salvo donde el kernel lo imponga
   inevitablemente (`sizeOf`, literales internos, `omega`). La aritmética y el orden se toman
   de peanolib (`Peano.Add`, `Peano.Order`), las medidas de terminación de `cSize : ℕ₀` y la
   aritmética de metas de `omega₀`.
3. **Dependencia matemática exclusiva de peanolib** para los naturales; `Nat` no es una
   dependencia conceptual, solo un detalle técnico de kernel aislado y documentado.

**Rationale**: El valor del proyecto descansa en ser teoría de conjuntos de Aczel
constructiva/computable verificada; admitir lógica clásica o `Nat` de Lean como dependencia
matemática traiciona la tesis fundacional. El arreglo de la raíz es viable y barato:
separar `evalOp` en `mem`/`subset`/`eq` estructurales (con `eq A B := subset A B && subset B A`,
no recursivo) es **axiom-free** (verificado en experimento standalone).

**Consequences**:
- Plan de ejecución en [`PLANNING-CONSTRUCTIVE.md`](PLANNING-CONSTRUCTIVE.md) (Fases 0–4).
- Se añade un verificador `#assert_no_classical` (vía `Lean.collectAxioms`) como gate de build.
- Refuerza y endurece el Principio 3 de PLANNING.md y complementa ADR-000.
- Las excepciones técnicas de `Nat` inevitables se enumeran explícitamente en el plan.
- Trabajo estimado: ~6–8 sesiones; mayor impacto en Fase 1 (raíz `evalOp`).

---

## ADR-019: Reutilizar los tipos públicos de peanolib (`ℕ₁`, `ℕ₂`, …) — no redefinir subtipos

**Date**: 2026-06-10
**Status**: Accepted (MANDATORY M-4)

**Context**: En `Integers/Rationals.lean` se encontró `private abbrev PosNat₀ := {n : ℕ₀ // n ≠ 𝟘}`,
que es **exactamente** `Peano.ℕ₁` (tipo público de peanolib). Redefinir subtipos comunes en
matemáticas (positivos, ≥ 2, etc.) de forma privada y local:
- duplica definiciones que ya existen y están probadas en peanolib;
- impide reutilizar el aparato (lemas, instancias, notación `∣₁`, `gcd₁`, etc.);
- fragmenta el proyecto y contradice ADR-000/M-5 (dependencia exclusiva de peanolib).

Tipos públicos relevantes de peanolib (`Peano/PeanoNat.lean`):

```lean
def ℕ₁ : Type := {n : ℕ₀ // n ≠ ℕ₀.zero}              -- positivos (≠ 0)
def ℕ₂ : Type := {n : ℕ₁ // n.val ≠ ℕ₀.succ ℕ₀.zero}  -- ≥ 2 (factores propios)
```

`ℕ₂` ya se usa en AczelSetTheory (`VN/DigitsVN.lean`: `base : ℕ₂`), confirmando que son
importables y operativos.

**Decision**: **Prohibido redefinir** subtipos de `ℕ₀`/`ℤ₀` que ya existan en peanolib.
Usar `Peano.ℕ₁`, `Peano.ℕ₂` (y futuros tipos públicos) directamente. Si se necesita un
subtipo nuevo no presente en peanolib, evaluarse primero si debe añadirse a peanolib
(fundacional) en lugar de localmente.

**Rationale**: Maximiza reutilización, coherencia y el principio «peanolib es la única
fuente de los naturales y sus refinamientos». Reduce superficie de mantenimiento.

**Consequences**:
- `PosNat₀` se reemplaza por `Peano.ℕ₁` (ver plan de limpieza en `PLANNING.md` §Limpieza).
- Revisión periódica con `grep "{.*: ℕ₀ //"` para detectar reincidencias.
- Verificación incluida en MANDATORY M-4.

---

## ADR-020: Gate constructivo EXHAUSTIVO (barrido de axiomas de todo el árbol)

**Date**: 2026-07-15
**Status**: Accepted

**Context**: El gate `Meta/AxiomCheck.lean` original (ADR-018) verificaba una lista
**curada a mano de ~30 símbolos** con `#assert_no_classical`. La auditoría del 2026-07-15
(`INFORME-AUDITORIA-2026-07-15.md` §5), replicando la metodología de Peano (ADR-017 Fase C),
ejecutó un barrido exhaustivo con `Lean.collectAxioms` sobre las 3042 declaraciones propias
y encontró **11 símbolos con footprint no-constructivo que el gate curado NO cubría**:

- 9 con `Classical.choice` **oculto** (invisible a `grep 'Classical\.'`): 2 heredados de
  `Peano.Wilson.wilson`, 7 nativos por `by_cases`/`decide` sobre una proposición sin instancia
  `Decidable` en contexto (∀/∃ no acotado, o instancia fuera de scope → `Classical.propDecidable`).
- 2 con `native_decide` (`VN.vN_totient_one/two` ← `Peano.Totient.totient_{one,two}`), un axioma
  de confianza en el compilador que está **fuera** incluso del footprint diana `{propext, Quot.sound}`.

El gate curado daba, por tanto, una **falsa sensación de seguridad**.

**Decision**: Se reescribe `Meta/AxiomCheck.lean` como **gate exhaustivo**
(`#assert_constructive_footprint`):

1. Recorre **toda** declaración cuyo módulo de definición esté bajo `AczelSetTheory.*`
   (filtro por `env.const2ModIdx`, saltando nombres internos), vía `Lean.collectAxioms`.
2. **Falla el build** si algún símbolo tiene un axioma fuera de `{propext, Quot.sound}`
   (`sorryAx` se tolera: es la deuda de los 14 `sorry` activos, ya avisada por el compilador),
   **salvo** un `baselineNonConstructive` explícito de las 11 excepciones actuales, cada una
   justificada en el informe.
3. **Avisa** (warning) si una excepción del baseline ya está limpia, para poder retirarla.
4. Para ver todas las declaraciones sin ciclo, el módulo importa todos los barrels de
   subsistema (no el barrel raíz, que a su vez lo importa el último).

**Rationale**:
- Un gate curado no escala ni detecta el Classical oculto; el barrido automático no requiere
  mantenimiento (descubre símbolos nuevos solo).
- El patrón *baseline + fallo en regresiones nuevas* es la forma estándar de introducir un
  gate estricto sobre una base que aún no está 100 % limpia: se congela la deuda conocida y
  se impide que crezca.
- Coste medido: ~2.6 s por build (los `.olean` ya están compilados; `collectAxioms` es barato).

**Consequences**:
- El **objetivo** es vaciar `baselineNonConstructive`. Cada símbolo saneado se retira de la lista
  (el propio gate avisa cuándo una excepción ya está limpia).
- Clase A (heredado de Peano, `Peano` frozen por ADR-000): requiere certificar constructivamente
  `Wilson.wilson`/`Totient.totient_*` aguas arriba, o aceptarlos como excepción metateórica.
- Clase B (nativo): reescribir los `by_cases`/`decide` con `[DecidablePred P]`/instancias reales
  o descomposición constructiva (trabajo planificado, ver informe §6 Prioridad 1).
- Supersede el mecanismo de lista curada de ADR-018 (que se conserva como herramienta puntual
  `#assert_no_classical`, útil para comprobar un símbolo concreto).

---

## ADR-021: Regla 17 (bloques `export`) redefinida — incompatible con namespaces semánticos + ADR-004

**Date**: 2026-07-16
**Status**: Accepted (redefine AI-GUIDE §17 y §11-14; **retira** NAMING-CONVENTIONS REGLA 13)

**Context**:
La auditoría 2026-07-15/16 (`INFORME-AUDITORIA-2026-07-15.md`) constató que AI-GUIDE §17
(«Todo módulo de producción (hoja) DEBE terminar con un bloque `export` que liste todas las
definiciones, teoremas y lemas públicos») **la incumplen 200 de 204 módulos**: solo la
cumplen `Algebra/Subgroup.lean`, `Axioms/Order.lean`, `Axioms/WellOrder.lean` y
`Operations/Order.lean`.

Al intentar aplicarla project-wide se descubrió que **es técnicamente inaplicable con el
diseño de este proyecto**:

- Los `export` del repo van **a raíz**: `export HFSet (wf_induction)` crea `_root_.wf_induction`.
- ADR-004 (convención Mathlib) prescribe **no repetir el namespace en el miembro**, así que
  el mismo nombre existe **legítimamente** en varios namespaces:

  ```
  add_comm ×6   add_assoc ×6   add_zero ×5   zero_mul ×5
  mul_comm ×4   mul_one ×4     zero_add ×4
  ofNat ×11     inter ×8       id ×7   comp ×7   get ×6
  ```

- Exportarlos todos a raíz crearía **aliases ambiguos** (`_root_.add_comm` con 6 orígenes) y
  los usos de nombres desnudos (hay `open Peano` en muchos módulos) fallarían con
  *"ambiguous, possible interpretations"* → **rompe el build**.
- Los 4 módulos conformes lo son precisamente porque sus símbolos tienen nombre **único**
  (`wf_induction`, `isSubgroupProp`, `isReflexive`…). **El patrón no escala.**

La única forma de sostener §17 con export-a-raíz sería adoptar NAMING **REGLA 13** (sufijos
de dominio: `addZ`, `mulQ`) generalizada a lemas (`add_commQ`, `add_commZ`…), lo cual:
contradice **ADR-004** (Mathlib usa `Nat.add_comm`/`Int.add_comm` y **no** exporta a raíz);
contradice **AI-GUIDE §3.5 / ADR-015** (namespaces anidados); exigiría renombrar cientos de
símbolos y todos sus usos en 204 ficheros **sin beneficio funcional** (los namespaces ya
desambiguan); y resucita una regla que la auditoría 2026-07-12 constató **nunca usada**.

**Decision**:

1. **§17 deja de ser obligatoria y universal.** El bloque `export` es **opcional y selectivo**:
   se usa solo para el «API titular» de un módulo y **solo con símbolos cuyo nombre sea único
   en el proyecto** — que es exactamente la práctica de los 4 módulos conformes. **No exportar
   nada es conforme.**
2. **NAMING REGLA 13 (sufijos de dominio) se retira** como regla universal; queda como
   convención local, a documentar únicamente si algún día se usa de verdad.
3. **Reglas 11-14 reformuladas**: la fuente de verdad de la proyección al sistema REFERENCE
   deja de ser el bloque `export` y pasa a ser **el conjunto de declaraciones no-`private`**
   del módulo. El índice de lo público lo provee `doc/REFERENCE-*.md` §7 («Exports per
   Module»), que ya existe y no colisiona.
4. El patrón real correcto es `export <Namespace> (sym₁ sym₂ …)` a raíz. El ejemplo del
   AI-GUIDE (`export PROJECT_NAME.SubModulo (...)`) **era erróneo** y se corrige.

**Rationale**:
- El problema **no es el naming** —que es correcto y Mathlib-conforme— sino una regla que
  exige **aplanarlo a raíz**, destruyendo la desambiguación que los namespaces ya aportan.
- Una regla que incumple el 98 % del código y que, aplicada, **rompe el build**, no es una
  norma: es deuda documental. O se hace cumplible o se retira.
- El sistema REFERENCE ya cumple la función que §17 pretendía (índice navegable de lo
  público) sin colisionar.

**Consequences**:
- No hay que tocar 200 módulos ni renombrar ningún símbolo.
- Los 4 módulos con `export` siguen siendo válidos: son el patrón selectivo de referencia.
- La proyección al REFERENCE se hace desde las declaraciones no-`private`, sujeta a la
  regla (8) («nada que no esté probado entra en REFERENCE»).
- Se actualizan `AI-GUIDE.md` (§17, §11-14) y `NAMING-CONVENTIONS.md` (REGLA 13).
- Un `export` exhaustivo en el futuro exigiría antes adoptar un esquema de nombres
  globalmente único (REGLA 13) y aceptar el conflicto con ADR-004: **no recomendado**.

---

## ADR-022: Invariante O6 desdoblado — 0/0/0 duro + frente de `sorry` acotado y declarado

**Date**: 2026-07-16
**Status**: Accepted (enmienda a O6 de `PLANNING-FASE-B.md`; no reescribe su enunciado histórico)

**Context**:
O6 (`PLANNING-FASE-B.md`) exige «0 sorry / 0 noncomputable / 0 axiom / 0 warnings», verificado
con `lake build && make audit` tras cada milestone. La auditoría 2026-07-15/16 encontró tres
defectos:

1. **`make audit` nunca existió**: era un target fantasma. Tres documentos mandaban ejecutarlo
   (`AUDITORIA-2026-06-05.md`, `INFORME-AUDITORIA-2026-06-08.md`, `PLANNING-FASE-B.md`) pero el
   `Makefile` no lo definía. **El invariante no se verificaba: no había con qué.**
2. **`AUDIT-MODULE-MATRIX.md` declaraba `sorry: 0`** mientras el árbol tiene **14**. La matriz
   cubría 182 de 204 módulos y — la ironía — **los 14 `sorry` viven exactamente en los
   subsistemas que la matriz no cubría** (`Rationals/`, `Reals/`). O6 «se mantenía» porque el
   inventario era ciego.
3. O6 está violado también en **warnings**: el build real emite 19 (5 unused-variable + 14 sorry),
   no 0.

Los 14 `sorry` no son un descubrimiento: están documentados y aceptados en
`CURRENT-STATUS-PROJECT.md` §Known Sorry Locations, en `NEXT-STEPS.md`, y el gate de axiomas los
tolera explícitamente (`sorryAx ∈ allowedAxioms`, ADR-020). Son el **frente de trabajo activo**
(análisis real constructivo), no deuda oculta.

**Decision**:
O6 se **desdobla** en tres invariantes verificables. Su enunciado histórico en
`PLANNING-FASE-B.md` **no se reescribe** (falsearía el registro); se enmienda por referencia a
este ADR.

- **O6a — duro, global, sin excepciones**: `0 axiom`, `0 admit`, `0 noncomputable def`, y
  footprint de axiomas ⊆ `{propext, Quot.sound}` (+ `sorryAx`). Verificado mecánicamente por
  `gen-audit-matrix.bash` y por el gate exhaustivo de ADR-020.
- **O6b — frente de `sorry` acotado**: `0 sorry` **fuera del frente declarado**. El frente vive
  en `SORRY_BASELINE` de `gen-audit-matrix.bash` (hoy: Series 6, Polynomial 4, Incompleteness 3,
  Irrational 1 = 14) y **solo puede encoger**: `make audit` **falla** ante cualquier `sorry`
  nuevo o fuera de la lista, y **avisa** cuando una cota queda obsoleta.
- **O6c — warnings**: los 5 unused-variable quedan como deuda menor declarada; «0 warnings» se
  reinterpreta como «**0 warnings nuevos**».

**Rationale**:
- Es **el mismo patrón que ADR-020** (baseline explícito + fallo ante regresiones), que este
  proyecto ya adoptó y que le funcionó para llevar el footprint de 11 excepciones a 0.
- Un `sorry: 0` **falso** es estrictamente peor que una deuda **declarada y acotada**: lo primero
  no se puede vigilar; lo segundo falla el build en cuanto crece.
- Regenerar la matriz no «rompe» O6: **revela** que O6 llevaba desde 2026-06-10 sin verificarse.
  La honestidad del inventario es condición previa a cualquier invariante.

**Consequences**:
- `AUDIT-MODULE-MATRIX.md` dice `sorry: 14`, y eso es **correcto**, no una regresión.
- El cierre de FASE B (M8B) no queda bloqueado: O6a se cumple y O6b está acotado. `Rationals/`
  y `Reals/` son FRENTE 1 (post-FASE B), no perímetro de FASE B.
- Cada `sorry` cerrado **baja la cota** en `SORRY_BASELINE`; el propio `make audit` avisa.
- Queda cerrada la acción «regenerar con `make audit`» que reclamaban los informes de
  2026-06-05 y 2026-06-08 (esos documentos son históricos y **no se editan**).

---

## ADR-023: El nombre titular `ℤ₀`/`ℚ₀` pasa al tipo empaquetado (antes `HFInt`/`HFRat`)

**Date**: 2026-07-16
**Status**: Accepted (decisión del usuario)

**Context**:
El proyecto tenía **tres** presentaciones de cada número, y el **nombre bueno lo tenía la
representación interna**, no la que usa el consumidor:

```lean
structure HFInt where          structure HFRat where
  cls  : ℤ₀                      cls  : ℚ₀        -- la CLASE de equivalencia (quotient)
  pair : ℤ₀'                     pair : ℚ₀'       -- el par CANÓNICO
  hEq  : pair.val = cls.repr     hEq  : ℚ₀'.toQ0 pair = cls   -- coherencia entre ambas
```

Es decir: `ℤ₀`/`ℚ₀` (el cociente) y `ℤ₀'`/`ℚ₀'` (el par canónico) son **dos representaciones**;
`HFInt`/`HFRat` es el tipo que **empaqueta ambas con su prueba de coherencia** y es el que el
resto del proyecto debe usar. Los propios nombres de campo (`cls`, `pair`) ya lo decían.

**Decision**:
El nombre titular pasa al tipo empaquetado; las representaciones se cualifican por su rol:

| Antes | Ahora | Rol |
|---|---|---|
| `ℤ₀` | **`ℤ₀cls`** | cociente / clase de equivalencia (`Quotient intSetoid`) |
| `ℤ₀'` | **`ℤ₀can`** | par canónico |
| `HFInt` | **`ℤ₀`** | **titular**: clase + par canónico + coherencia |
| `ℚ₀` | **`ℚ₀cls`** | cociente / clase de equivalencia |
| `ℚ₀'` | **`ℚ₀can`** | par canónico |
| `HFRat` | **`ℚ₀`** | **titular**: clase + par canónico + coherencia |

Arrastra la cascada completa:
- **Derivados ASCII** (~223 usos): `toQ0`/`toZ0` → `toCls`, `ofQ0`/`ofZ0` → `ofCls`,
  `toQ0Seq` → `toClsSeq`, `toQ0CauchySeq` → `toClsCauchySeq`, `toQ0Pos` → `toClsPos`,
  `toQ0ApartZero` → `toClsApartZero`, y los lemas de ida-y-vuelta `toQ0_ofQ0` → `toCls_ofCls`,
  `ofQ0_toQ0` → `ofCls_toCls`.
- **Ficheros/módulos** (6): `Integers/HFInt.lean` → `Integers/Z0.lean`, `HFIntOps` → `Z0Ops`;
  `Rationals/HFRat.lean` → `Rationals/Q0.lean`, `HFRatOps` → `Q0Ops`, `HFRatCauchy` → `Q0Cauchy`,
  `HFRatCauchyAlgebra` → `Q0CauchyAlgebra`. ASCII, por el precedente `PList/Fin0.lean` y porque
  los módulos/ficheros no deben llevar unicode. `Basic.lean` **no se mueve**: sigue albergando el
  cociente (`ℚ₀cls`), por la regla NAMING de definiciones fundamentales.

**Rationale**:
- **El consumidor debe escribir `ℚ₀`, no `HFRat`.** `HFRat`/`HFInt` eran nombres de andamio
  («HF» = hereditariamente finito) filtrados a la API pública.
- La distinción `cls`/`can` es **la que el código ya hacía** en sus campos: el renombrado se
  limita a que los tipos digan lo que los campos ya decían.
- Elimina la ambigüedad de tener `ℚ₀` (cociente) y `HFRat` (empaquetado) compitiendo por ser
  «el racional», que obligaba a recordar cuál usar en cada API.

**Consequences**:
- ~3000 ocurrencias reescritas en 36 ficheros `.lean` + 6 renombrados. Build verificado.
- **Los documentos históricos NO se reescriben** (informes de auditoría 2026-06-05/06-08/07-12/
  07-15, entradas pasadas del CHANGELOG, y los cuerpos de ADR anteriores): describen el estado
  en su fecha y reescribirlos falsearía el registro. **Esta tabla de mapeo es la clave de
  lectura** para interpretarlos. En particular, ADR-014 («ℤ₀ como único entero canónico, sin
  `HFInt`») debe leerse con el mapeo: su `ℤ₀` es hoy `ℤ₀cls`.
- Los documentos vivos (README, REFERENCE + nodos, CURRENT-STATUS, NEXT-STEPS, DEPENDENCIES,
  PLANNING) sí se actualizan a la nomenclatura nueva.
- `AUDIT-MODULE-MATRIX.md` recoge los ficheros nuevos automáticamente vía `make audit` (ADR-022).

---

## ADR-024: Migración de tipos vía coerción + homomorfismo `.cls` + bridges `ext` (sin tocar la clase)

**Date**: 2026-07-20
**Status**: Accepted (decisión del usuario)

**Context**: Tras ADR-023 (el nombre titular `ℤ₀`/`ℚ₀` pasa al struct empaquetado), había que
hacer que el proyecto **use** los structs donde antes usaba las clases `ℤ₀cls`/`ℚ₀cls`, sin
reescribir ni arriesgar las pruebas originales (que son válidas y están sobre la clase).

**Decision**: completar el API de `ℤ₀`/`ℚ₀` como una **fachada** sobre la clase, en tres capas:
1. **Coerción olvidadiza** `Coe ℤ₀ ℤ₀cls := ⟨.cls⟩` (ídem `ℚ₀`): permite usar el struct donde se
   espera la clase, sin ambigüedad.
2. **Homomorfismo `.cls` `@[simp]`**: las ops del struct son `ofCls (op sobre cls)` (o fijan
   `cls := op`), así que `cls_add`/`cls_mul`/… son `rfl`. Con `@[ext]` (que reduce la igualdad del
   struct a la de la clase) esto convierte cualquier hecho de la clase en su versión struct en 1 línea.
3. **Bridges** term-mode/`ext` sobre cada lema de la clase — sin duplicar pruebas.
Regla operativa: en las firmas de bridges usar `Add.add`/`Mul.mul`/`Neg.neg`/`Sub.sub` **explícito**
(el elaborador de `+`/`*` choca con la coerción `ℕ₀→ℤ₀`). Los predicados (Cauchy, convergencia) se
**redefinen nativamente** sobre el struct y se atan a la clase con un `iff`.

**Rationale**: mantener las clases como el *núcleo probado* y los structs como la *cara pública* da
paridad práctica sin riesgo ni deuda de prueba; el gate exhaustivo (ADR-020) garantiza que la fachada
no introduce axiomas. Alternativa descartada: reescribir la teoría directamente sobre los structs
(coste enorme, riesgo de regresión, y los cocientes siguen siendo la construcción natural).

**Consequences**: `ℤ₀` es anillo conmutativo ordenado + teoría de números; `ℚ₀` es cuerpo ordenado
con Cauchy/convergencia/arquimediano/raíces. El gate pasó de 3042 a 3239 decls, baseline 0. La regla
8 (nada con `sorry` en REFERENCE) se aplica por footprint de axiomas también a la fachada. La igualdad
del struct **no** es definicionalmente la de la clase: hace falta `ext` en un sentido y `congrArg .cls`
en el otro (de ahí `eq_iff_cls`/`ne_zero_iff_cls`).

---

## Template for new decisions

## ADR-NNN: [Title]

**Date**: YYYY-MM-DD
**Status**: [Proposed | Accepted | Deprecated | Superseded by ADR-XXX]

**Context**: [Why is this decision needed?]

**Decision**: [What was decided?]

**Rationale**: [Why this choice over alternatives?]

**Consequences**: [What are the trade-offs?]
