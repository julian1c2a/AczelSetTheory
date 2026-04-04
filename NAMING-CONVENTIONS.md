# Naming Conventions — Mathlib Style

> Permanent reference document for this project.
> All rules are based on the
> [Mathlib Naming Conventions](https://leanprover-community.github.io/contribute/naming.html),
> adapted to the project's specific domain.

**Last updated:** 2026-04-04 00:00
**Author**: Julián Calderón Almendros

---

## 1. Capitalization Rules

| Declaration type | Convention | Example |
|------------------|------------|---------|
| Theorems, lemmas (Prop terms) | `snake_case` | `union_comm`, `mem_clist_iff` |
| Types, Props, Structures, Classes | `UpperCamelCase` | `CList`, `CSet`, `IsSorted` |
| Functions returning `Type` | by return type | `normalizar` (→ CList → `snake`), `IsSorted` (→ Prop → `Upper`) |
| Other `Type` terms | `lowerCamelCase` | `insertarOrdenado`, `ordenarLista` |
| Acronyms | as group upper/lower | `CZF` (namespace), `czf` (in snake_case) |

---

## 2. Symbol-to-Word Dictionary

| Symbol | In names | Notes |
|--------|----------|-------|
| ∈ | `mem` | `x ∈ A` → `mem` |
| ∉ | `not_mem` | |
| ∪ | `union` | binary |
| ∩ | `inter` | binary |
| ⋃ | `sUnion` | `s` = "set of sets" |
| ⋂ | `sInter` | idem |
| ⊆ | `subset` | non-strict |
| ⊂ | `ssubset` | strict (extra `s`) |
| 𝒫 | `powerset` | |
| σ | `succ` | |
| ∅ | `empty` | |
| △ | `symmDiff` | |
| ᶜ | `compl` | complement |
| \ | `sdiff` | set difference |
| ×ₛ | `prod` | cartesian product |
| ⟂ | `disjoint` | |
| = | `eq` | often omitted |
| ≠ | `ne` | |
| → | `of` / implicit | conclusion goes first |
| ↔ | `iff` | suffix |
| ¬ | `not` | |
| ∃ | `exists` | |
| ∀ | `forall` | |
| ∘ | `comp` | composition |
| ⁻¹ | `inv` | inverse |
| + | `add` | |
| \* / · | `mul` | |
| − | `sub` (binary) / `neg` (unary) | |
| ^ | `pow` | |
| / | `div` | |
| ∣ | `dvd` | divides |
| ≤ | `le` | |
| < | `lt` | |
| ≥ | `ge` | only for argument swap |
| > | `gt` | only for argument swap |
| 0 | `zero` | |
| 1 | `one` | |

---

## 3. Name Formation Rules (12 rules)

### RULE 1 — Conclusion first, hypotheses with `_of_`

The name describes **what is proved**, not how. Hypotheses are added with `_of_`:

```
-- Pattern: A → B → C
-- Name:    c_of_a_of_b
-- Order:   conclusion_of_hypothesis1_of_hypothesis2

-- Example:
-- Theorem: IsSorted l → IsSorted (insertarOrdenado x l)
-- Name:    insertarOrdenado_sorted_of_sorted
--          ^^^^^^^^^^^^^^^^^^^^^ ^^^^^^^^^^^^^
--          conclusion             hypothesis
```

### RULE 2 — Biconditionals carry suffix `_iff`

```
-- Theorem: x ∈ (𝒫 A) ↔ x ⊆ A
-- Name:    mem_powerset_iff
--          ^^^ ^^^^^^^^ ^^^
--          ∈    𝒫        ↔
```

### RULE 3 — Eliminate `_wc` — Use `.mp` / `.mpr` or `_of_`

The `_wc` suffix is replaced by Mathlib convention:

```
-- For forward direction of an iff:
--    mem_clist_iff.mp
-- For backward direction:
--    mem_clist_iff.mpr
-- As standalone theorem:
--    mem_of_clist    (conclusion_of_hypothesis)
```

### RULE 4 — Algebraic properties → short axiomatic name

```
-- commutativity:   union_comm, inter_comm
-- associativity:   inter_assoc, union_assoc
-- absorption:      union_inter_self
-- distributivity:  union_inter_distrib_left
```

**Standard axiomatic suffixes (Mathlib):**

| Suffix | Meaning | Example |
|--------|---------|---------|
| `_comm` | commutativity | `union_comm` |
| `_assoc` | associativity | `inter_assoc` |
| `_refl` | reflexivity | `subset_refl` |
| `_irrefl` | irreflexivity | `ssubset_irrefl` |
| `_symm` | symmetry | `disjoint_symm` |
| `_trans` | transitivity | `subset_trans` |
| `_antisymm` | antisymmetry | `subset_antisymm` |
| `_asymm` | asymmetry | `ssubset_asymm` |
| `_inj` | injectivity (iff) | `succ_inj` |
| `_injective` | injectivity (pred) | `succ_injective` |
| `_self` | operation with itself | `union_self` (A ∪ A = A) |
| `_left` / `_right` | lateral variant | `union_subset_left` |
| `_cancel` | cancellation | `add_left_cancel` |
| `_mono` | monotonicity | `powerset_mono` |

### RULE 5 — Predicates as prefix, operations in infix order

```
-- Predicate as prefix:   isSorted_nil (not nil_is_sorted)
-- Exception:             succ_injective (_injective, _surjective are always suffix)
```

### RULE 6 — Standard abbreviations for frequent conditions

| Instead of | Use | Meaning |
|-----------|-----|---------|
| `zero_lt_x` | `pos` | x > 0 |
| `x_lt_zero` | `neg` | x < 0 |
| `x_le_zero` | `nonpos` | x ≤ 0 |
| `zero_le_x` | `nonneg` | x ≥ 0 |

### RULE 7 — Definitions with `Is` for Prop predicates

```
-- Definition (Prop): def IsSorted (l : List CList) : Prop := ...  (UpperCamelCase)
-- In theorem names:  isSorted_nil, isSorted_cons, isSorted_of_mem (lowerCamelCase in snake_case)
```

### RULE 8 — Functions/constructors non-Prop: `lowerCamelCase`

```
-- normalizar (not NormalizarCList)  — lowerCamelCase
-- insertarOrdenado (not InsertSorted)
-- ordenarLista (not SortList)
```

### RULE 9 — Specifications: `_iff` and `mem_X_iff`

```
-- mem_normalizar_iff      (membership in normalized form)
-- mem_clist_iff           (membership in CList)
-- insertarOrdenado_mem_iff
```

### RULE 10 — Uniqueness and existence

```
-- normalizar_unique   (canonical form is unique)
-- clist_unique        (canonical list is unique for given set)
```

### RULE 11 — Names with `_left` / `_right`

```
-- subset_union_left    — A ⊆ (A ∪ B), subset is left argument
-- subset_union_right   — B ⊆ (A ∪ B), subset is right argument
```

### RULE 12 — Named theorems (proper names)

```
-- cantor_no_surjection          — proper name + description (OK in Mathlib)
```

> **NOTE:** Mathematical proper names are kept as-is in Mathlib.
> Only operational words are normalized (`mem`, `union`, etc.).

---

## 4. Quick Reference Tables

### 4.1 Definitions — common naming patterns in this project

| Raw name | Mathlib-style name | Rationale |
|----------|--------------------|-----------|
| `CList` | `CList` | UpperCamelCase type |
| `CList.normalizar` | `normalizar` | lowerCamelCase function |
| `insertarOrdenado` | `insertarOrdenado` | lowerCamelCase (OK, established name) |
| `ordenarLista` | `ordenarLista` | lowerCamelCase (OK, established name) |
| `IsSorted` / `Sorted` | `Sorted` | follow List.Sorted convention |

### 4.2 Theorems — specification pattern

| Pattern | Example |
|---------|---------|
| `mem_X_iff` | `mem_normalizar_iff` |
| `X_sorted` | `insertarOrdenado_sorted` |
| `X_unique` | `normalizar_unique` |
| `X_of_Y` | `mem_of_normalizar` |

### 4.3 Theorems — algebraic properties

| Pattern | Example |
|---------|---------|
| `X_comm` | `union_comm` |
| `X_assoc` | `inter_assoc` |
| `X_refl` | `subset_refl` |
| `X_trans` | `subset_trans` |

---

## 5. Migration Note

During development, names are renamed progressively following these conventions.
Priority order for migration:

1. Base types: `CList`, `CSet`, core operations
2. Sorting and normalization: `insertarOrdenado`, `normalizar`, `ordenarLista`
3. Set operations: membership, subset, union, intersection
4. Derived structures: ordinals, cardinals (future)

Each rename is verified with full compilation before proceeding.
