# Design Decisions — AczelSetTheory

**Last updated:** 2026-06-08
**Author**: Julián Calderón Almendros

Architectural Decision Records (ADR) for this project.
Each entry records *what* was decided and *why*, for future reference.

> ADRs marcados **[heredado de Peano]** fueron adoptados originalmente en el proyecto
> predecesor y se aplican sin cambios a AczelSetTheory.

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

## Template for new decisions

## ADR-NNN: [Title]

**Date**: YYYY-MM-DD
**Status**: [Proposed | Accepted | Deprecated | Superseded by ADR-XXX]

**Context**: [Why is this decision needed?]

**Decision**: [What was decided?]

**Rationale**: [Why this choice over alternatives?]

**Consequences**: [What are the trade-offs?]
