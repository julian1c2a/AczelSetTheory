# Technical Reference — PList (Peano-indexed Lists)

**Last updated:** 2026-05-27
**Parent:** [../REFERENCE.md](../REFERENCE.md)
**Related:** [REFERENCE-HFList.md](REFERENCE-HFList.md) | [REFERENCE-VN.md](REFERENCE-VN.md)

@axiom_system: AczelSetTheory
@importance: high

---

## Overview

`PList` is a polymorphic singly-linked list type whose length is measured in Peano
naturals (`ℕ₀`). It serves as the backbone of `CList` and, by extension, `HFSet`.
`PList/Omega0.lean` provides the `omega₀` tactic for Peano-length arithmetic.
`PList/Fin0.lean` adds bounded indexing (`Fin₀`) so that `PList.get` can be
defined as a total function.

**Primary namespace:** `PList`
**External dependency:** `ℕ₀` = `PeanoNat` from `.lake/packages/peanolib`.
Notation: `𝟘` = zero, `σ n` = successor, `𝟚` = two.

| # | File | Status |
|---|------|--------|
| 23 | `AczelSetTheory/PList/Basic.lean` | ✅ Complete |
| 24 | `AczelSetTheory/PList/Lemmas.lean` | ✅ Complete |
| 25 | `AczelSetTheory/PList/Omega0.lean` | ✅ Complete |
| 62 | `AczelSetTheory/PList/Fin0.lean` | ✅ Complete |

---

## 4. Definitions

### 4.16 PList/Basic.lean — `namespace PList`

#### 4.16.1 `PList` (type)

```lean
inductive PList (α : Type) : Type where
  | nil  : PList α
  | cons : α → PList α → PList α
  deriving Repr, Inhabited
```

#### 4.16.2 Structural operations

| Name | Signature | Notes |
|------|-----------|-------|
| `length` | `PList α → ℕ₀` | `nil ↦ 𝟘`, `cons _ t ↦ σ (length t)` |
| `isEmpty` | `PList α → Bool` | |
| `head?` | `PList α → Option α` | |
| `tail` | `PList α → PList α` | |
| `get?` | `PList α → ℕ₀ → Option α` | |
| `getD` | `(dflt : α) → PList α → ℕ₀ → α` | default on out-of-bounds |

All computable, structurally recursive.

#### 4.16.3 Higher-order operations

| Name | Signature | Notes |
|------|-----------|-------|
| `map` | `(f : α → β) → PList α → PList β` | |
| `foldl` | `(f : β → α → β) → β → PList α → β` | left fold |
| `foldr` | `(f : α → β → β) → β → PList α → β` | right fold |
| `any` | `(p : α → Bool) → PList α → Bool` | |
| `all` | `(p : α → Bool) → PList α → Bool` | |
| `filter` | `(p : α → Bool) → PList α → PList α` | |
| `append` | `PList α → PList α → PList α` | `Append (PList α)` instance |
| `flatMap` | `(f : α → PList β) → PList α → PList β` | |
| `reverse` | `PList α → PList α` | |
| `zipWith` | `(f : α → β → γ) → PList α → PList β → PList γ` | stops at shorter |

All computable, structurally recursive.

#### 4.16.5 Slicing

| Name | Signature | Notes |
|------|-----------|-------|
| `take` | `ℕ₀ → PList α → PList α` | First `k` elements; `take 𝟘 l = nil`, `take k nil = nil` |
| `drop` | `ℕ₀ → PList α → PList α` | Skip first `k` elements; `drop 𝟘 l = l`, `drop k nil = nil` |

#### 4.16.4 Membership

```lean
def  PList.mem [DecidableEq α] (x : α) : PList α → Bool

inductive PList.Mem (a : α) : PList α → Prop where
  | head : Mem a (cons a t)
  | tail : Mem a t → Mem a (cons b t)

instance : Membership α (PList α) := ⟨fun l a => Mem a l⟩
```

#### 4.16.5 List bridge

```lean
def PList.toList  : PList α → List α
def PList.ofList  : List α  → PList α
```

---

### 4.17 PList/Lemmas.lean

No new definitions. Theorems only (see §6.16).

> **Note:** Theorems use `add n m` (direct `Peano.Add.add`) instead of `n + m`
> to avoid elaboration ambiguity with the `HAdd` instance.

---

### 4.18 PList/Omega0.lean — `namespace PList.Omega0`

Bridge lemmas between `ℕ₀` and `ℕ` via `Ψ : ℕ₀ → ℕ`:

| Name | Statement |
|------|-----------|
| `ψ_eq_iff` | `(m n : ℕ₀) : m = n ↔ Ψ m = Ψ n` |
| `ψ_le_iff` | `(m n : ℕ₀) : m ≤ n ↔ Ψ m ≤ Ψ n` |
| `ψ_lt_iff` | `(m n : ℕ₀) : m < n ↔ Ψ m < Ψ n` |
| `ψ_zero` | `Ψ 𝟘 = 0` |
| `ψ_succ` | `(n : ℕ₀) : Ψ (σ n) = Ψ n + 1` |
| `ψ_add` | uses `@HAdd.hAdd Nat Nat Nat instHAdd` explicitly |

#### 4.18.1 `omega₀` tactic

```lean
macro "omega₀" : tactic =>
  `(tactic| (simp only [PList.Omega0.ψ_eq_iff, PList.Omega0.ψ_le_iff,
               PList.Omega0.ψ_lt_iff, ...] at *; omega))
```

Reduces goals about `ℕ₀` to `ℕ` and closes them with `omega`.

---

### 4.40 PList/Fin0.lean

#### 4.40.1 `Fin₀`

```lean
structure Fin₀ (n : ℕ₀) : Type where
  val  : ℕ₀
  isLt : val < n
```

Instances: `DecidableEq`, `LT`, `LE`.

Constructor helpers:

| Name | Type |
|------|------|
| `Fin₀.zero` | `(n : ℕ₀) → Fin₀ (σ n)` |
| `Fin₀.succ` | `Fin₀ n → Fin₀ (σ n)` |
| `Fin₀.last` | `(n : ℕ₀) → Fin₀ (σ n)` |

#### 4.40.2 `PList.get`

```lean
def PList.get : (l : PList α) → Fin₀ (l.length) → α
```

Total bounded access. Contrast with `get? : PList α → ℕ₀ → Option α`.

---

## 6. Theorems

### 6.16 PList/Lemmas.lean — `namespace PList`

**Length**

| Theorem | Statement |
|---------|-----------|
| `length_nil` | `length (nil : PList α) = 𝟘` |
| `length_cons` | `(x : α) (t : PList α) : length (cons x t) = σ (length t)` |
| `length_eq_zero_iff_nil` | `(l : PList α) : length l = 𝟘 ↔ l = nil` |

**Append**

| Theorem | Statement |
|---------|-----------|
| `append_nil` | `(l : PList α) : l ++ nil = l` |
| `nil_append` | `(l : PList α) : nil ++ l = l` |
| `append_assoc` | `(l₁ l₂ l₃ : PList α) : (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃)` |
| `length_append` | `(l₁ l₂ : PList α) : length (l₁ ++ l₂) = add (length l₁) (length l₂)` |

**take / drop — simp lemmas**

| Theorem | Statement |
|---------|-----------|
| `take_zero` | `@[simp] (l : PList α) : take 𝟘 l = nil` |
| `drop_zero` | `@[simp] (l : PList α) : drop 𝟘 l = l` |
| `take_nil` | `@[simp] (k : ℕ₀) : take k (nil : PList α) = nil` |
| `drop_nil` | `@[simp] (k : ℕ₀) : drop k (nil : PList α) = nil` |
| `take_succ_cons` | `@[simp] (k : ℕ₀) (h : α) (t : PList α) : take (σ k) (cons h t) = cons h (take k t)` |
| `drop_succ_cons` | `@[simp] (k : ℕ₀) (h : α) (t : PList α) : drop (σ k) (cons h t) = drop k t` |

**take / drop — length lemmas**

| Theorem | Statement |
|---------|-----------|
| `length_take_le` | `(k : ℕ₀) (l : PList α) (h : k ≤ length l) : length (take k l) = k` |
| `length_take_gt` | `(k : ℕ₀) (l : PList α) (h : length l < k) : length (take k l) = length l` |
| `take_append_drop` | `(k : ℕ₀) (l : PList α) : (take k l).append (drop k l) = l` |
| `add_length_drop` | `(k : ℕ₀) (l : PList α) (h : k ≤ length l) : Peano.Add.add k (length (drop k l)) = length l` |
| `length_drop_le` | `(k : ℕ₀) (l : PList α) (h : k ≤ length l) : length (drop k l) = Peano.Sub.sub (length l) k` |

**Extensional equality**

| Theorem | Statement |
|---------|-----------|
| `get?_none_of_ge` | `(l : PList α) (i : ℕ₀) (h : length l ≤ i) : l.get? i = none` |
| `plist_ext_get?` | `(l₁ l₂ : PList α) (h : ∀ i : ℕ₀, l₁.get? i = l₂.get? i) : l₁ = l₂` |

### 6.40 PList/Fin0.lean — `namespace PList`

| Theorem | Statement |
|---------|-----------|
| `get_eq_get?` | `(l : PList α) (i : Fin₀ (l.length)) : l.get? i.val = some (l.get i)` |
| `get_ext` | `(l₁ l₂ : PList α) (heq : l₁.length = l₂.length) (h : ∀ i : Fin₀ (l₁.length), l₁.get i = l₂.get ⟨i.val, heq ▸ i.isLt⟩) : l₁ = l₂` |

**Map**

| Theorem | Statement |
|---------|-----------|
| `map_nil` | `(f : α → β) : map f nil = nil` |
| `map_cons` | `(f : α → β) (x : α) (t : PList α) : map f (cons x t) = cons (f x) (map f t)` |
| `length_map` | `(f : α → β) (l : PList α) : length (map f l) = length l` |
| `map_append` | `(f : α → β) (l₁ l₂ : PList α) : map f (l₁ ++ l₂) = map f l₁ ++ map f l₂` |

**List bridge** (`Λ` denotes the `ℕ₀ → ℕ` coercion)

| Theorem | Statement |
|---------|-----------|
| `toList_nil` | `toList (nil : PList α) = []` |
| `toList_cons` | `(x : α) (t : PList α) : toList (cons x t) = x :: toList t` |
| `ofList_nil` | `ofList ([] : List α) = nil` |
| `ofList_cons` | `(x : α) (t : List α) : ofList (x :: t) = cons x (ofList t)` |
| `toList_ofList` | `(l : List α) : toList (ofList l) = l` |
| `ofList_toList` | `(l : PList α) : ofList (toList l) = l` |
| `length_toList` | `(l : PList α) : (toList l).length = Λ (length l)` |

**Membership**

| Theorem | Statement |
|---------|-----------|
| `mem_cons_iff` | `[DecidableEq α] (x y : α) (t : PList α) : mem x (cons y t) = true ↔ x = y ∨ mem x t = true` |
| `Mem_cons_iff` | `(x y : α) (t : PList α) : Mem x (cons y t) ↔ x = y ∨ Mem x t` |
| `not_mem_nil` | `(x : α) : ¬ Mem x nil` |

**Any**

| Theorem | Statement |
|---------|-----------|
| `any_cons` | `@[simp] (p : α → Bool) (h : α) (t : PList α) : any p (cons h t) = (p h \|\| any p t)` |
| `any_eq_true` | `(p : α → Bool) (l : PList α) : any p l = true ↔ ∃ x, Mem x l ∧ p x = true` |

**Filter**

| Theorem | Statement |
|---------|-----------|
| `length_filter_le` | `[DecidablePred p] (l : PList α) : length (filter p l) ≤ length l` (uses `Peano.Order.le₀`) |

---

### 6.17 PList/Omega0.lean

Bridge lemmas only (see §4.18). No independent theorems.

---

### 6.43 PList/Fin0.lean

| # | Theorem | Lean signature |
|---|---------|---------------|
| 1 | `Fin₀.elim_zero` | `(i : Fin₀ 𝟘) → False` |
| 2 | `Fin₀.val_lt_bound` | `(i : Fin₀ n) → i.val < n` |
| 3 | `Fin₀.val_le_bound_pred` | `(i : Fin₀ n) → {k : ℕ₀} → (hk : n = σ k) → i.val ≤ k` |
| 4 | `PList.get_eq_get?` | `(l : PList α) → (i : Fin₀ (l.length)) → l.get? i.val = some (l.get i)` |

---

## 7. Exports per Module

### PList/Basic.lean

`PList`, `PList.nil`, `PList.cons`, `PList.length`, `PList.isEmpty`, `PList.head?`, `PList.tail`, `PList.get?`, `PList.getD`, `PList.map`, `PList.foldl`, `PList.foldr`, `PList.any`, `PList.all`, `PList.filter`, `PList.append`, `Append (PList α)`, `PList.flatMap`, `PList.reverse`, `PList.zipWith`, `PList.mem`, `PList.Mem`, `Membership α (PList α)`, `PList.toList`, `PList.ofList`

### PList/Lemmas.lean

`PList.length_nil`, `PList.length_cons`, `PList.length_eq_zero_iff_nil`, `PList.append_nil`, `PList.nil_append`, `PList.append_assoc`, `PList.length_append`, `PList.map_nil`, `PList.map_cons`, `PList.length_map`, `PList.map_append`, `PList.toList_nil`, `PList.toList_cons`, `PList.ofList_nil`, `PList.ofList_cons`, `PList.toList_ofList`, `PList.ofList_toList`, `PList.length_toList`, `PList.mem_cons_iff`, `PList.Mem_cons_iff`, `PList.not_mem_nil`, `PList.any_cons`, `PList.any_eq_true`, `PList.length_filter_le`

### PList/Omega0.lean

`PList.Omega0.ψ_eq_iff`, `PList.Omega0.ψ_le_iff`, `PList.Omega0.ψ_lt_iff`, `PList.Omega0.ψ_zero`, `PList.Omega0.ψ_succ`, `PList.Omega0.ψ_add`, tactic macro `omega₀`

### PList/Fin0.lean

`Fin₀`, `Fin₀.zero`, `Fin₀.succ`, `Fin₀.last`, `Fin₀.ext`, `Fin₀.toFin`, `Fin₀.ofFin`, `Fin₀.elim_zero`, `Fin₀.val_lt_bound`, `Fin₀.val_le_bound_pred`, `PList.get`, `PList.get_eq_get?`
