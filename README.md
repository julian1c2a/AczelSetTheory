# AczelSetTheory

## Aczel's Set Theory in Lean 4

**Author**: Julián Calderón Almendros
**License**: MIT
**Lean version**: v4.29.0
**Build status**: ✅ All proofs complete — 0 `sorry`, 0 errors, 0 warnings

---

### What it is

This repository formalizes Aczel's constructive set theory in Lean 4. The central object is `CList` — a computable representation of hereditarily finite sets as nested lists — together with a provably correct normalization procedure that yields canonical representatives. The quotient type `HFSet` identifies extensionally equal `CList`s.

Key properties of this set theory:

- **Constructive**: no axiom of choice, no excluded middle (fully intuitionistic)
- **Computable**: all definitions are decidable and executable
- **No axiom of infinity**: natural numbers are constructed from sets
- **Well-founded recursion and induction** over sets

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
  HFSets.lean        — HFSet quotient type, repr, empty
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
- [NEXT_STEPS.md](NEXT_STEPS.md) — Development roadmap

### Credits

- Peter Aczel — *Non-Well-Founded Sets* (foundational theory)
- Lean 4 / Mathlib community — language and conventions
- AI assistance: Claude (Anthropic), GitHub Copilot
