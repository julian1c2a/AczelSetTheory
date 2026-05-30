# Design Decisions — AczelSetTheory

**Last updated:** 2026-05-22
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

## Template for new decisions

## ADR-NNN: [Title]

**Date**: YYYY-MM-DD
**Status**: [Proposed | Accepted | Deprecated | Superseded by ADR-XXX]

**Context**: [Why is this decision needed?]

**Decision**: [What was decided?]

**Rationale**: [Why this choice over alternatives?]

**Consequences**: [What are the trade-offs?]
