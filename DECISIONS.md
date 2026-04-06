# Design Decisions — AczelSetTheory

**Last updated:** 2026-04-06 00:00
**Author**: Julián Calderón Almendros

Architectural Decision Records (ADR) for this project.
Each entry records *what* was decided and *why*, for future reference.

---

## ADR-001: No Mathlib dependency

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: This project does not depend on Mathlib.

**Rationale**: Educational and research goals — the formalization of Aczel Set Theory must be built from first principles to understand its constructive foundations. Avoiding Mathlib API churn also makes the project more stable.

**Consequences**: All necessary infrastructure (ordering, lists, decidability, etc.) must be built from scratch within the project.

---

## ADR-002: Canonical list representation for sets (CList)

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: Sets are represented as canonical sorted lists without duplicates (`CList`). A `CList` is a `List CList` (hereditarily finite sets) in canonical (sorted, deduplicated) form.

**Rationale**: Canonical representation enables decidable equality and membership without classical axioms. Sorting provides a canonical form that makes equality of sets identical to structural equality of their list representations.

**Consequences**: All set operations must preserve the canonical invariant. The `normalizar` function maintains this invariant. The main challenge is the mutual recursive structure of `CList` and the ordering on it.

---

## ADR-003: File locking system

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: Use `git-lock.bash` + `locked_files.txt` + pre-commit hook to prevent accidental edits to completed modules.

**Rationale**: Lean 4 proofs are fragile — small changes to completed modules can break dependent proofs. The locking system makes this explicit and prevents accidental regressions.

**Consequences**: Workflow requires locking/unlocking files. See AI-GUIDE.md §20.

---

## ADR-004: Mathlib naming conventions

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: All identifiers follow Mathlib4 naming conventions as documented in NAMING-CONVENTIONS.md.

**Rationale**: Consistency with the broader Lean 4 ecosystem. Makes theorems discoverable by name pattern (`mem_X_iff`, `subject_predicate`). Facilitates future Mathlib integration if desired.

**Consequences**: Existing names may need migration. See NAMING-CONVENTIONS.md for the full dictionary and 12 formation rules.

---

## ADR-005: Directory-aligned namespaces

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: Each subdirectory corresponds to a sub-namespace: `AczelSetTheory/Foo/Bar.lean` → `namespace AczelSetTheory.Foo.Bar`.

**Rationale**: Clear 1:1 mapping between file system and namespace hierarchy. Reduces confusion about where definitions live. Scales well as the project grows.

**Consequences**: `new-module.bash` handles subdirectory creation. `gen-root.bash` scans recursively.

---

## ADR-006: Annotation system in REFERENCE.md

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: REFERENCE.md entries include `@axiom_system` and `@importance` annotations.

**Rationale**: Helps AI assistants prioritize which modules/theorems to load for context. Provides quick classification without reading module code.

**Consequences**: Annotations must be maintained when modules are updated. See AI-GUIDE.md §24-25.

---

## ADR-007: Axiom prefix `AST_`

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: All axioms use the `AST_` prefix (Aczel Set Theory) + `UpperCamelCase` descriptor.

**Rationale**: Signals axiomatic (unproven) status at a glance. Consistent with the convention in sibling projects (MK_, ZF_, etc.).

**Consequences**: Axioms are immediately distinguishable from theorems. See AI-GUIDE.md NC-5.

---

## ADR-008: Module split — CList sub-modules

**Date**: 2026-04-05
**Status**: Accepted

**Decision**: Split the monolithic `CSets.lean` into 6 focused sub-modules under `CList/` (Basic, ExtEq, SetEquiv, Order, Sort, Normalize), aggregated by `CList.lean`.

**Rationale**: The single file exceeded 2000 lines. Dependencies between theorem groups (ordering, sorting, normalization) are naturally hierarchical. Smaller files are easier to lock, freeze, and review.

**Consequences**: Build parallelism improved. Each module can be frozen independently. Naming migrated from Spanish (`esIgual`, `normalizar`) to Mathlib-style English (`extEq`, `normalize`).

---

## ADR-009: Zermelo axioms as derived theorems

**Date**: 2026-04-06
**Status**: Accepted

**Decision**: The Zermelo axioms (Extensionality, Empty Set, Pairs, etc.) are derived as theorems over the `HFSet` quotient type, not postulated as Lean `axiom`s.

**Rationale**: The CList+normalize infrastructure provides enough structure to prove these properties constructively. Derived axioms strengthen trust in the formalization and confirm the model is correct.

**Consequences**: Each "axiom" requires a proof. ADR-007 (`AST_` prefix for axioms) does not apply to these — they are ordinary theorems with Mathlib-style names (`extensionality`, `not_mem_empty`, `mem_pair`).

---

## Template for new decisions

## ADR-NNN: [Title]

**Date**: YYYY-MM-DD
**Status**: [Proposed | Accepted | Deprecated | Superseded by ADR-XXX]

**Context**: [Why is this decision needed?]

**Decision**: [What was decided?]

**Rationale**: [Why this choice over alternatives?]

**Consequences**: [What are the trade-offs?]
