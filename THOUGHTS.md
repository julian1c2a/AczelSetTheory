# Thoughts — AczelSetTheory

**Last updated:** 2026-04-04 00:00
**Author**: Julián Calderón Almendros

> This is an informal design journal. Record ideas, alternatives considered,
> open questions, and future directions here. Not normative — purely exploratory.
> Useful for AI context on "why" decisions were made.

---

## Design Philosophy

- **Constructive foundations**: Aczel Set Theory (CZF/IZF) is inherently constructive.
  Lean 4's type theory is a natural fit — we avoid `Classical.choice` where possible.
- **Canonical representation**: Sets are represented as sorted, deduplicated lists (`CList`).
  This makes equality decidable and gives a unique canonical form for each set.
- **No Mathlib**: Building from scratch forces a deep understanding of the constructive
  foundations. It also makes the project self-contained and stable.
- **Mutual recursion challenge**: `CList` and its ordering are mutually recursive.
  This is the main technical challenge — Lean 4's termination checker requires careful
  structuring of the recursion (via `cSize`/`cSizeList` measures).

---

## Ideas and Alternatives

### 2026-04-04 — Representation of sets

**Alternatives considered**:
1. `Finset` (Mathlib) — rejected: requires Mathlib, and `Finset` is quotient-based (extensional equality by default), which is harder to control constructively
2. `List CList` without canonicalization — rejected: equality becomes undecidable (any permutation is the same set)
3. Sorted `List CList` without deduplication — rejected: `[a, a]` and `[a]` would represent the same set but be unequal
4. **Sorted + deduplicated `List CList`** ✅ — canonical form, decidable equality, constructive

### 2026-04-04 — Termination for mutual recursion

The `CList` type and its comparison are mutually recursive. Getting termination to go
through required introducing size measures (`cSize`, `cSizeList`) and using them as
termination arguments. This is documented in the git history (commit 5e4b3f3).

---

## Open Questions

- [ ] Should we introduce a `CSet` type alias for `CList` with a `Sorted`+`NoDup` invariant,
      or keep it as a plain `CList`?
- [ ] When is it appropriate to use `Classical.choice` for existence theorems vs. staying
      fully constructive?
- [ ] What axioms of CZF can we state and prove directly from the `CList` representation?
- [ ] How should `normalizar_eq_of_eq` be proved? (Current sorry — main pending work)

---

## Lessons Learned

### Mutual Recursion in Lean 4

- Lean 4's termination checker for mutual recursion is strict — you need explicit
  measure functions that decrease on every recursive call
- `cSize : CList → Nat` and `cSizeList : List CList → Nat` as mutual measures worked
- The key insight: prove that size is strictly decreasing before the termination checker
  accepts the definition

### Canonical Form Proofs

- Proving that `normalizar` is idempotent requires careful case analysis
- The `insertarOrdenado_sorted` theorem is foundational — all other sorting properties follow from it
- Uniqueness proofs (a `CList` has only one canonical form) require induction on the
  size of the `CList`

### Naming Conventions

- Mathlib naming conventions significantly improve searchability
- The `subject_predicate` pattern is natural for sorting/normalization theorems:
  `insertarOrdenado_sorted`, `normalizar_unique`

---

## Future Directions

- **Axiomatic phase**: Once `CSets.lean` is complete, formalize CZF axioms:
  Extensionality, Pairing, Union, Powerset, Infinity, Strong Collection, Subset Collection
- **Set operations**: union, intersection, difference, powerset — all preserving canonicality
- **Ordinals**: Build ordinals as hereditarily transitive sets (HTSets) within the CList framework
- **Relation to IZF**: Explore which results require full IZF (Infinity + Power Set without
  restrictions) vs. CZF's weaker axioms
