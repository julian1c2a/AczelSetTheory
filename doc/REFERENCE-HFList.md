# Technical Reference — HFList (Hereditarily Finite Lists)

**Last updated:** 2026-05-14
**Parent:** [../REFERENCE.md](../REFERENCE.md)
**Related:** [REFERENCE-PList.md](REFERENCE-PList.md) | [REFERENCE-HFSets.md](REFERENCE-HFSets.md)

@axiom_system: AczelSetTheory
@importance: medium

---

## Overview

`HFList` is an abbreviation for `PList HFSet` — a list of hereditarily finite
sets. `FinList n` wraps `HFList` with a length proof, providing statically-sized
containers.

**Primary namespaces:** `HFList`, `FinList`

| # | File | Status |
|---|------|--------|
| 63 | `AczelSetTheory/HFList.lean` | ✅ Complete |

---

## 4. Definitions

### 4.41 HFList.lean

#### 4.41.1 `HFList`

```lean
abbrev HFList := PList HFSet
```

All `PList` operations apply directly (see [REFERENCE-PList.md](REFERENCE-PList.md)).

#### 4.41.2 `FinList`

```lean
def FinList (n : ℕ₀) : Type := { l : HFList // l.length = n }
```

Statically-sized list of HFSets with Peano length `n`.

Constructor helpers:

| Name | Type | Notes |
|------|------|-------|
| `FinList.empty` | `FinList 𝟘` | The unique empty list |
| `FinList.singleton` | `HFSet → FinList (σ 𝟘)` | Singleton list |
| `FinList.cons` | `HFSet → FinList n → FinList (σ n)` | Prepend element |

Accessors:

| Name | Type | Notes |
|------|------|-------|
| `FinList.toHFList` | `FinList n → HFList` | Forget the length proof |
| `FinList.get` | `FinList n → Fin₀ n → HFSet` | Bounded total access |

---

## 6. Theorems

### 6.44 HFList.lean — `namespace HFList` / `namespace FinList`

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `HFList.length_nil` | `length PList.nil = 𝟘` |
| 2 | `HFList.length_cons` | `(h : HFSet) → (t : HFList) → length (PList.cons h t) = σ (length t)` |
| 3 | `HFList.length_append` | `(l₁ l₂ : HFList) → length (l₁ ++ l₂) = add (length l₁) (length l₂)` |
| 4 | `FinList.length_eq` | `(t : FinList n) → t.val.length = n` |
| 5 | `FinList.ext` | `{t s : FinList n} → (h : t.val = s.val) → t = s` |

---

## 7. Exports

### HFList.lean

`HFList`, `FinList`, `HFList.length_nil`, `HFList.length_cons`, `HFList.length_append`, `FinList.empty`, `FinList.singleton`, `FinList.cons`, `FinList.toHFList`, `FinList.get`, `FinList.length_eq`, `FinList.ext`
