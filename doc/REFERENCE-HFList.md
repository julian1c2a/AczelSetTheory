# Technical Reference — HFList (Hereditarily Finite Lists)

**Last updated:** 2026-05-18
**Parent:** [../REFERENCE.md](../REFERENCE.md)
**Related:** [REFERENCE-PList.md](REFERENCE-PList.md) | [REFERENCE-HFSets.md](REFERENCE-HFSets.md)

@axiom_system: AczelSetTheory
@importance: medium

---

## Overview

`HFList` is an abbreviation for `PList HFSet` — an ordered, possibly-repeating
sequence of hereditarily finite sets. `FinList n` wraps `HFList` with a static
length proof. `HFListOps` provides the conversion from ordered lists to the
extensional `HFSet` world.

**Contrast with HFSet:**

| Type | Constructors | Order | Duplicates |
|------|-------------|-------|------------|
| `HFSet` | Quotient of `CList` | ✗ | ✗ |
| `HFList` | `PList HFSet` | ✓ | ✓ |
| `FinList n` | `{ l : HFList // l.length = n }` | ✓ | ✓ |

**Primary namespaces:** `HFList`, `FinList`

| # | File | Status |
|---|------|--------|
| 63 | `AczelSetTheory/HFList.lean` | ✅ Complete |
| 64 | `AczelSetTheory/HFListOps.lean` | ✅ Complete |

---

## 4. Definitions

### 4.41 HFList.lean

#### 4.41.1 `HFList`

```lean
abbrev HFList := PList HFSet
```

All `PList` operations apply directly (see [REFERENCE-PList.md](REFERENCE-PList.md)).

Concrete aliases defined inside `namespace HFList`:

| Name | Definition | Type |
|------|-----------|------|
| `HFList.nil` | `PList.nil` | `HFList` |
| `HFList.cons` | `PList.cons` | `HFSet → HFList → HFList` |
| `HFList.append` | `PList.append` | `HFList → HFList → HFList` |
| `HFList.length` | `PList.length` | `HFList → ℕ₀` |
| `HFList.get?` | `PList.get?` | `HFList → ℕ₀ → Option HFSet` |
| `HFList.get` | `PList.get` | `(l : HFList) → Fin₀ (l.length) → HFSet` |
| `HFList.Mem` | `PList.Mem` | `HFSet → HFList → Prop` |

`Append HFList` and `Membership HFSet HFList` instances are provided.

#### 4.41.2 `FinList`

```lean
def FinList (n : ℕ₀) : Type := { l : HFList // l.length = n }
```

Statically-sized n-tuple of HFSets.

**Constructors and smart builders:**

| Name | Type | Notes |
|------|------|-------|
| `FinList.empty` | `FinList 𝟘` | Unique 0-tuple |
| `FinList.singleton` | `HFSet → FinList (σ 𝟘)` | 1-tuple |
| `FinList.cons` | `HFSet → FinList n → FinList (σ n)` | Prepend; raises arity by 1 |

**Accessors:**

| Name | Type | Notes |
|------|------|-------|
| `FinList.toHFList` | `FinList n → HFList` | Underlying `HFList` (forget proof) |
| `FinList.get` | `(t : FinList n) → Fin₀ n → HFSet` | Total bounded access |
| `FinList.head` | `FinList (σ n) → HFSet` | First component |
| `FinList.tail` | `FinList (σ n) → FinList n` | All but first component |

**Operations:**

| Name | Type | Notes |
|------|------|-------|
| `FinList.append` | `FinList n → FinList m → FinList (add n m)` | Concatenation |
| `FinList.map` | `(HFSet → HFSet) → FinList n → FinList n` | Pointwise unary op |
| `FinList.zipWith` | `(HFSet → HFSet → HFSet) → FinList n → FinList n → FinList n` | Pointwise binary op |

---

### 4.42 HFListOps.lean

#### 4.42.1 `HFList.toHFSet`

```lean
def HFList.toHFSet : HFList → HFSet
  | .nil      => HFSet.empty
  | .cons h t => HFSet.insert h (toHFSet t)
```

Converts an ordered list to a set by forgetting order and eliminating duplicates.

#### 4.42.2 `FinList.toHFSet`

```lean
def FinList.toHFSet (t : FinList n) : HFSet := t.val.toHFSet
```

Converts a static n-tuple to an `HFSet`.

---

## 6. Theorems

### 6.44 HFList.lean — `namespace HFList`

**Length**

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `length_nil` | `@[simp] length PList.nil = 𝟘` |
| 2 | `length_cons` | `@[simp] (h : HFSet) (t : HFList) : length (PList.cons h t) = σ (length t)` |
| 3 | `length_append` | `(l₁ l₂ : HFList) : length (l₁ ++ l₂) = add (length l₁) (length l₂)` |

**Membership**

| # | Theorem | Lean signature |
|---|---------|---------------|
| 4 | `not_mem_nil` | `(x : HFSet) : ¬ x ∈ (nil : HFList)` |
| 5 | `mem_cons_iff` | `(x h : HFSet) (t : HFList) : x ∈ HFList.cons h t ↔ x = h ∨ x ∈ t` |

**get? computation**

| # | Theorem | Lean signature |
|---|---------|---------------|
| 6 | `get?_nil` | `@[simp] (i : ℕ₀) : (nil : HFList).get? i = none` |
| 7 | `get?_cons_zero` | `@[simp] (h : HFSet) (t : HFList) : (cons h t).get? 𝟘 = some h` |
| 8 | `get?_cons_succ` | `@[simp] (h : HFSet) (t : HFList) (i : ℕ₀) : (cons h t).get? (σ i) = get? t i` |

---

### 6.44 HFList.lean — `namespace FinList`

**Equality**

| # | Theorem | Lean signature |
|---|---------|---------------|
| 9 | `ext` | `{t s : FinList n} → t.val = s.val → t = s` |
| 10 | `ext_iff` | `{t s : FinList n} : t = s ↔ t.val = s.val` |
| 11 | `length_eq` | `(t : FinList n) : t.val.length = n` |

**Append**

| # | Theorem | Lean signature |
|---|---------|---------------|
| 12 | `length_append` | `(t : FinList n) (s : FinList m) : (t.append s).val.length = add n m` |

**head / tail**

| # | Theorem | Lean signature |
|---|---------|---------------|
| 13 | `head_cons` | `@[simp] (x : HFSet) (t : FinList n) : head (cons x t) = x` |
| 14 | `tail_cons` | `@[simp] (x : HFSet) (t : FinList n) : tail (cons x t) = t` |
| 15 | `cons_head_tail` | `(t : FinList (σ n)) : cons (head t) (tail t) = t` |

**zipWith**

| # | Theorem | Lean signature |
|---|---------|---------------|
| 16 | `zipWith_nil` | `@[simp] zipWith f (empty : FinList 𝟘) empty = empty` |
| 17 | `zipWith_cons` | `@[simp] (x y : HFSet) (t s : FinList n) : zipWith f (cons x t) (cons y s) = cons (f x y) (zipWith f t s)` |

---

### 6.45 HFListOps.lean — `namespace HFList`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `toHFSet_nil` | `@[simp] toHFSet nil = HFSet.empty` |
| 2 | `toHFSet_cons` | `@[simp] (h : HFSet) (t : HFList) : toHFSet (cons h t) = HFSet.insert h (toHFSet t)` |
| 3 | `mem_toHFSet` | `{x : HFSet} {l : HFList} : x ∈ toHFSet l ↔ x ∈ l` |
| 4 | `mem_toHFSet_of_mem` | `{x : HFSet} {l : HFList} : x ∈ l → x ∈ toHFSet l` |

### 6.45 HFListOps.lean — `namespace FinList`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 5 | `toHFSet_empty` | `@[simp] (FinList.empty : FinList 𝟘).toHFSet = HFSet.empty` |
| 6 | `toHFSet_cons` | `@[simp] (x : HFSet) (t : FinList n) : (FinList.cons x t).toHFSet = HFSet.insert x t.toHFSet` |
| 7 | `mem_toHFSet` | `{x : HFSet} {t : FinList n} : x ∈ t.toHFSet ↔ x ∈ t.val` |

---

### 6.46 PList/Lemmas.lean — addition for FinList support

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `PList.length_zipWith_same` | `(f : α → β → γ) (l₁ : PList α) (l₂ : PList β) : l₁.length = l₂.length → (zipWith f l₁ l₂).length = l₁.length` |

---

## 7. Exports per Module

### HFList.lean

`HFList`, `HFList.nil`, `HFList.cons`, `HFList.append`, `HFList.length`, `HFList.get?`, `HFList.get`, `HFList.Mem`, `Append HFList`, `Membership HFSet HFList`,
`HFList.length_nil`, `HFList.length_cons`, `HFList.length_append`,
`HFList.not_mem_nil`, `HFList.mem_cons_iff`,
`HFList.get?_nil`, `HFList.get?_cons_zero`, `HFList.get?_cons_succ`,
`FinList`, `FinList.empty`, `FinList.singleton`, `FinList.cons`, `FinList.toHFList`, `FinList.get`, `FinList.head`, `FinList.tail`,
`FinList.append`, `FinList.map`, `FinList.zipWith`,
`FinList.ext`, `FinList.ext_iff`, `FinList.length_eq`, `FinList.length_append`,
`FinList.head_cons`, `FinList.tail_cons`, `FinList.cons_head_tail`,
`FinList.zipWith_nil`, `FinList.zipWith_cons`

### HFListOps.lean

`HFList.toHFSet`, `HFList.toHFSet_nil`, `HFList.toHFSet_cons`, `HFList.mem_toHFSet`, `HFList.mem_toHFSet_of_mem`,
`FinList.toHFSet`, `FinList.toHFSet_empty`, `FinList.toHFSet_cons`, `FinList.mem_toHFSet`
