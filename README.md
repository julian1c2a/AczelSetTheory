# AczelSetTheory

## Aczel's Set Theory in Lean 4

**Author**: Julián Calderón Almendros
**License**: MIT
**Lean version**: v4.29.0
**Build status**: ⚠️ 2 `sorry` remaining (Powerset) — 0 errors, 0 warnings

---

### What it is

This repository formalizes Aczel's constructive set theory in Lean 4. The central object is `CList` — a computable representation of hereditarily finite sets as nested lists — together with a provably correct normalization procedure that yields canonical representatives. The quotient type `HFSet` identifies extensionally equal `CList`s.

The Zermelo axioms (Extensionality, Empty Set, Pairs, Union, Separation, Intersection, Setminus) are **derived as theorems**, not postulated. Powerset is in progress.

Key properties of this set theory:

- **Constructive**: no axiom of choice, no excluded middle (fully intuitionistic)
- **Computable**: all definitions are decidable and executable
- **No axiom of infinity**: natural numbers are constructed from sets
- **Well-founded recursion and induction** over sets
- **Axiom-free**: Zermelo axioms are derived theorems, not axioms

### Derived Zermelo Axioms

| Axiom | Theorem | Statement | Status |
|-------|---------|-----------|--------|
| Extensionality | `HFSet.extensionality` | ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B | ✅ |
| Empty Set | `HFSet.not_mem_empty` | ∀ x, x ∉ ∅ | ✅ |
| Pairs | `HFSet.mem_pair` | x ∈ {a, b} ↔ x = a ∨ x = b | ✅ |
| Union | `HFSet.mem_sUnion` | x ∈ ⋃ A ↔ ∃ B ∈ A, x ∈ B | ✅ |
| Separation | `HFSet.mem_sep` | x ∈ sep A P ↔ x ∈ A ∧ P x | ✅ |
| Intersection | `HFSet.mem_sInter` | x ∈ ⋂ A ↔ ∀ B ∈ A, x ∈ B | ✅ |
| Setminus | `HFSet.mem_setminus` | x ∈ A \ B ↔ x ∈ A ∧ x ∉ B | ✅ |
| Powerset | `HFSet.mem_powerset` | B ∈ 𝒫 A ↔ ∀ x, x ∈ B → x ∈ A | 🔄 |

### Module structure

```
AczelSetTheory/
  CList/
    Basic.lean       — CList type, size, comparison, order, dedup, sort, normalize
    ExtEq.lean       — Extensional equality: reflexivity, transitivity, commutativity
    SetEquiv.lean    — Nodup, SetEquiv, dedup properties
    Order.lean       — lt: irreflexivity, antisymmetry, asymmetry, totality, transitivity
    Sort.lean        — Sorted, insertionSort preserves sorted/nodup/setEquiv
    Normalize.lean   — Size bounds, idempotency, uniqueness (sorted_nodup_setEquiv_eq)
  CList.lean         — Root module importing all CList sub-modules
  HFSets.lean        — HFSet quotient type, membership, Zermelo axioms
```

### Key types

| Type | Definition | Module |
|------|-----------|--------|
| `CList` | `inductive CList \| mk : List CList → CList` | Basic |
| `HFSet` | `Quotient CList.Setoid` | HFSets |

### Core pipeline

```
CList  ──normalize──▶  CList (canonical form)
  │                        │
  └──Quotient.mk──▶  HFSet ◀──repr──┘
```

1. **`normalize`**: recursively normalizes children, deduplicates, sorts → canonical form
2. **`normalize_idem`**: normalization is idempotent
3. **`normalize_eq_of_extEq`**: extensionally equal CLists have the same normal form
4. **`HFSet.repr`**: extracts the canonical representative via `Quotient.lift`
5. **`HFSet.Mem`**: membership lifted to quotient via `Quotient.liftOn₂`

### Building

```bash
lake build AczelSetTheory
```

Requires Lean v4.29.0 (see `lean-toolchain`).

### Running

```bash
lake build Main && lake env lean --run Main.lean
```

### Documentation

- [AI-GUIDE.md](AI-GUIDE.md) — Documentation protocol and naming conventions
- [REFERENCE.md](REFERENCE.md) — Complete technical reference (all definitions, theorems, signatures)
- [NAMING-CONVENTIONS.md](NAMING-CONVENTIONS.md) — Extended naming rules and symbol dictionary
- [CHANGELOG.md](CHANGELOG.md) — Change history
- [CURRENT-STATUS-PROJECT.md](CURRENT-STATUS-PROJECT.md) — Project status overview
- [DEPENDENCIES.md](DEPENDENCIES.md) — Module dependency diagram
- [NEXT_STEPS.md](NEXT_STEPS.md) — Development roadmap

### Credits

- Peter Aczel — *Non-Well-Founded Sets* (foundational theory)
- Lean 4 / Mathlib community — language and conventions
- AI assistance: Claude (Anthropic), GitHub Copilot
