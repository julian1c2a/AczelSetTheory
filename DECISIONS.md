# Design Decisions — AczelSetTheory

**Last updated:** 2026-04-10 00:00
**Author**: Julián Calderón Almendros

Architectural Decision Records (ADR) for this project.
Each entry records *what* was decided and *why*, for future reference.

---

## ADR-010: Separation of Operations and Axioms

**Date**: 2026-04-07
**Status**: Accepted

**Decision**: The project is split into Operations/ and Axioms/ modules for all HFSet functionalities (Union, Separation, Intersection, Setminus, Pair, Powerset).

**Rationale**: Operations/ handles the CList implementation and lifts to HFSet. Axioms/ is solely devoted to stating the canonical form of the set-theory axiom over the HFSet quotient representation without worrying about the internal details.

**Consequences**: The architecture is strongly modular. Powerset and Pair are naturally untangled from HFSets.lean.

---

## ADR-001: No Mathlib dependency

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: This project does not depend on Mathlib.

**Rationale**: Educational and research goals.

---

## ADR-002: Canonical list representation for sets (CList)

**Date**: 2026-04-04
**Status**: Accepted

**Decision**: Sets are represented as canonical sorted lists without duplicates CList.

---

## ADR-009: Zermelo axioms as derived theorems

**Date**: 2026-04-06
**Status**: Accepted

**Decision**: The Zermelo axioms are derived as theorems over the HFSet quotient type.
