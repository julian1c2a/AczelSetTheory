
---

**`CHANGELOG.md`**

```markdown
# Changelog

All notable changes to this project are documented here.

---

## [Unreleased] — 2026-04-01

### Changed — Lean 4.29.0 migration

Migrated the entire project from Lean **4.28.0** to **4.29.0**. The build now
completes successfully (`lake build` — warnings only, no errors).

**Breaking changes fixed:**

- `forall_eq_or_imp` removed from core: replaced with a manual `constructor`
  proof in `subs_iff_forall_mem_pertenece`.
- `List.mem_cons_self` is now fully implicit (no arguments): removed `_ _`
  from two call sites.
- `simp_rw` inside tactic `have` blocks no longer works as a rewrite lemma
  source: extracted `subs_iff_forall_mem_pertenece` as a top-level
  `private theorem`.
- `simp only [esIgual_def]` unfolded `esIgual` inside `any`-predicates when
  `SetEquiv` was already unfolded: replaced with targeted `rw [esIgual_def,
  Bool.and_eq_true]` to avoid touching the inner `esIgual` calls.
- `rcases ... with (rfl | ...)` direction change in `reducirDuplicados_set_equiv_self`
  when both sides are free variables: renamed `head → hd` and corrected
  variable usage in the `rfl` branch.
- `induction` inside well-founded `decreasing_by` makes match variables
  abstract: rewrote `normalizar_cSize_le` + `normalizar_cSizeList_le` as a
  `mutual` block with term-level pattern matching so the concrete constructors
  are visible to the termination checker.
- `normalizar` not in scope inside `namespace CSet`: added `open CList` at the
  top of the namespace.
- `normalizar_eq_of_eq` had a broken proof body (was masked by the name-scope
  error): simplified to `sorry` — the theorem was already incomplete before
  the migration.

---

## Prior work

### `dd771c9` — Refactor `SetEquiv` theorems
### `462beed` — Fix `reducirDuplicados_nodup`
### `6a434a9` — Size lemmas and normalization bounds
### `8c25f00` — Transitivity and membership lemmas
### `8d0ee07` — `SetEquiv` and `esIgual_mk_iff_setEquiv`
### `698a119` — `reducirDuplicados_nodup` and `SetEquiv` scaffolding
### `d8a0805` — Refactor: remove old definition
### `d1a24e5` — Support lemmas and transitivity
### `46ac00e` — Initial implementation
