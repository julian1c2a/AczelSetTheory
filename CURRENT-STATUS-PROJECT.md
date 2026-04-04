# Current Project Status — AczelSetTheory

**Last updated:** 2026-04-04 00:00
**Author**: Julián Calderón Almendros

---

## Executive Summary

| Metric | Value |
|--------|-------|
| Total modules | 1 |
| Modules with 0 sorry | 0 / 1 |
| Total sorry | 1 (in `normalizar_eq_of_eq`) |
| Build status | ✅ Passing |
| Lean version | v4.29.0 |
| Naming convention | Mathlib-style (see NAMING-CONVENTIONS.md) |

---

## Status by Module

| Module | Sorry | Status |
|--------|-------|--------|
| `AczelSetTheory/CSets.lean` | 1 | 🔄 In progress |

*Status codes*: ✅ Complete · 🧊 Frozen · 🔶 Partial · 🔄 In progress · ❌ Pending

---

## Known Sorry Locations

| File | Function/Theorem | Note |
|------|-----------------|------|
| `AczelSetTheory/CSets.lean` | `normalizar_eq_of_eq` | Pending proof |

---

## Recent Achievements

- Migrated project to Lean 4.29.0 (2026-04-02)
- Added theorems for uniqueness and membership in `ordenarLista`
- Improved `esMenor_total` comparison logic
- Added theorems about comparison properties in CList
- Optimized mutual termination logic in `cSize` and `cSizeList`

---

## Pending Work

- [ ] Prove `normalizar_eq_of_eq` (remove last sorry)
- [ ] Project `CSets.lean` into `REFERENCE.md`
- [ ] Design next module structure (ordinals, axioms, etc.)

---

## Architecture

```
AczelSetTheory/
└── CSets.lean      # Level 0: canonical set representation (CList/CSet)
```

---

## Development Phases

| Phase | Description | Status |
|-------|-------------|--------|
| Phase 1: CList foundations | `CSets.lean` — canonical lists, sorting, normalization | 🔄 In progress |
| Phase 2: Set axioms | Extensionality, pairing, union, powerset | ❌ Pending |
| Phase 3: Naming migration | Adopt Mathlib naming conventions fully | ❌ Pending |
| Phase 4: REFERENCE.md | Project CSets.lean fully into REFERENCE.md | ❌ Pending |

> See [NEXT_STEPS.md](NEXT_STEPS.md) for detailed phase planning.

---

**Author**: Julián Calderón Almendros
*Last updated: 2026-04-04 00:00*

[![License](https://img.shields.io/badge/license-MIT-green)](LICENSE)
