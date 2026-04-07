# Current Project Status — AczelSetTheory

**Last updated:** 2026-04-07 00:00
**Author**: Julián Calderón Almendros

---

## Executive Summary

| Metric | Value |
|--------|-------|
| Total modules | 16 |
| Modules with 0 sorry | 14 / 16 |
| Total sorry | 2 (powersetCList_extEq, mem_powerset) |
| Build status | ⚠️ Passing with warnings (2 sorries) |
| Lean version | v4.29.0 |
| Naming convention | Mathlib-style (see NAMING-CONVENTIONS.md) |

---

## Status by Module

| Module | Sorry | Status |
|--------|-------|--------|
| AczelSetTheory/CList sub-modules | 0 | ✅ Complete |
| AczelSetTheory/HFSets.lean | 0 | ✅ Complete |
| AczelSetTheory/Operations/Union.lean | 0 | ✅ Complete |
| AczelSetTheory/Axioms/Union.lean | 0 | ✅ Complete |
| AczelSetTheory/Operations/Separation.lean | 0 | ✅ Complete |
| AczelSetTheory/Axioms/Separation.lean | 0 | ✅ Complete |
| AczelSetTheory/Operations/Intersection.lean | 0 | ✅ Complete |
| AczelSetTheory/Axioms/Intersection.lean | 0 | ✅ Complete |
| AczelSetTheory/Operations/Setminus.lean | 0 | ✅ Complete |
| AczelSetTheory/Axioms/Setminus.lean | 0 | ✅ Complete |
| AczelSetTheory/Operations/Pair.lean | 0 | ✅ Complete |
| AczelSetTheory/Axioms/Pair.lean | 0 | ✅ Complete |
| AczelSetTheory/Operations/Powerset.lean | 1 | 🔄 In progress |
| AczelSetTheory/Axioms/Powerset.lean | 1 | 🔄 In progress |

*Status codes*: ✅ Complete · 🧊 Frozen · 🔶 Partial · 🔄 In progress · ❌ Pending 

---

## Known Sorry Locations

1. AczelSetTheory/Operations/Powerset.lean: powersetCList_extEq
2. AczelSetTheory/Axioms/Powerset.lean: mem_powerset

---

## Recent Achievements

- Formalized advanced set operations: Union (sUnion), Intersection (sInter), Setminus.
- Extracted and formalized Pair cleanly in its own modules.
- Created architectural foundations for operations and axioms.

---

## Pending Work

- [ ] Resolving powersetCList_extEq and mem_powerset.
- [ ] Define singleton notation
- [ ] Natural numbers as hereditarily finite sets
- [ ] Explore ordinal arithmetic
- [ ] Regularity, Replacement, Axiom of Choice proofs.

---

## Architecture

`
AczelSetTheory/
  CList/             — Core CList behavior
  Operations/        — Constructors mapping CList -> HFSet
  Axioms/            — Axiomatic properties mapping HFSet -> HFSet
`

---

## Development Phases

| Phase | Description | Status |
|-------|-------------|--------|
| Phase 1: CList foundations | 6 sub-modules — canonical lists, sorting, normalization | ✅ Complete |
| Phase 2: HFSet quotient | Quotient type, repr, canonical representatives | ✅ Complete |
| Phase 3: Zermelo axioms (basic) | Extensionality, Empty Set, Pairs | ✅ Complete |
| Phase 4: Zermelo axioms (advanced) | Union, Separation, Intersection, Setminus | ✅ Complete |
| Phase 5: Powerset | Combinatorics over CList and sublists | 🔄 In progress |
| Phase 6: Natural numbers | Von Neumann ordinals as HFSets | ❌ Pending |       

> See [NEXT_STEPS.md](NEXT_STEPS.md) for detailed planning.

---

**Author**: Julián Calderón Almendros
*Last updated: 2026-04-07 00:00*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)