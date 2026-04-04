# Technical Reference — AczelSetTheory

**Last updated:** 2026-04-04 00:00
**Author**: Julián Calderón Almendros
**Lean version**: v4.29.0

---

## 0. Naming Conventions Guide for the Reader

This project adopts [Mathlib](https://leanprover-community.github.io/contribute/naming.html)-style naming conventions.
Below are the keys for reading and searching theorems.

### 0.1 Capitalization Rules

- **Theorems/lemmas** (Prop): `snake_case` — `union_comm`, `mem_clist_iff`
- **Prop definitions** (predicates): `UpperCamelCase` — `IsSorted`, `CSet`; in theorem names → `lowerCamelCase`: `isSorted_nil`
- **Functions** (returning values): `lowerCamelCase` — `normalizar`, `insertarOrdenado`, `ordenarLista`
- **Acronyms**: as group — `CZF` (namespace), `czf` (in snake_case)

### 0.2 Symbol-to-Word Dictionary

| Symbol | Name | | Symbol | Name | | Symbol | Name |
|--------|------|---|--------|------|---|--------|------|
| ∈ | `mem` | | ∪ | `union` | | + | `add` |
| ∉ | `not_mem` | | ∩ | `inter` | | * | `mul` |
| ⊆ | `subset` | | ⋃ | `sUnion` | | - | `sub`/`neg` |
| ⊂ | `ssubset` | | ⋂ | `sInter` | | / | `div` |
| 𝒫 | `powerset` | | \ | `sdiff` | | ^ | `pow` |
| σ | `succ` | | △ | `symmDiff` | | ∣ | `dvd` |

---

## 1. Module List

| File | Namespace | Status | @axiom_system | @importance |
|------|-----------|--------|---------------|-------------|
| `AczelSetTheory/CSets.lean` | `AczelSetTheory` | 🔄 In progress | `none` | `foundational` |

---

## 2. Module Dependencies

### AczelSetTheory/CSets.lean

- **Depends on**: Lean 4 standard library (`List`, `Repr`, `BEq`, `Ord`)
- **Depended on by**: `Main.lean`, `AczelSetTheory.lean` (root)
- **Namespace**: `AczelSetTheory`

---

## 3. Definitions

> **Note**: This section is a stub. Run the "proyectar" protocol (AI-GUIDE.md §12)
> after reading `AczelSetTheory/CSets.lean` to populate this section fully.

### AczelSetTheory/CSets.lean — `namespace AczelSetTheory`

**@axiom_system**: `none`
**@importance**: `foundational`
**Last projected**: 2026-04-04 (stub only — full projection pending)

#### Core Types

```lean
-- CList: hereditarily finite set represented as a canonical sorted list
inductive CList where
  | mk : List CList → CList
```

*(Full signatures to be projected from CSets.lean)*

#### Key Functions

- `normalizar : CList → CList` — returns canonical form (sorted, deduplicated)
- `insertarOrdenado : CList → List CList → List CList` — insert maintaining order
- `ordenarLista : List CList → List CList` — sort a list of CLists

*(Full signatures, termination arguments, and computability to be projected)*

---

## 4. Axioms

*(None currently — this project builds constructively from Lean 4 without additional axioms)*

---

## 5. Notations

*(To be projected from CSets.lean)*

---

## 6. Main Theorems

> **Note**: Only proven theorems appear here. Populate after full projection of CSets.lean.

*(To be projected from CSets.lean — includes theorems about sorting, normalization, membership, uniqueness)*

---

## 7. Exports

*(To be projected from CSets.lean)*

---

## Projection Log

| Date | File projected | Projector |
|------|---------------|-----------|
| 2026-04-04 | (stub created) | Julián Calderón Almendros |

> To project a file: read it fully, then update sections 1–7 above following AI-GUIDE.md §4–14.
