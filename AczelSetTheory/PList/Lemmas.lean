/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/PList/Lemmas.lean
-- Lemas fundamentales sobre PList: longitud, append, map y puentes.

import AczelSetTheory.PList.Basic
import Peano.PeanoNat.Add
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.Order
import Peano.PeanoNat.Sub

-- Use `add` (from Peano export) rather than `+` to avoid elaboration ambiguity:
-- `export Peano.Add(add, ...)` in Add.lean puts both the function `add` and the
-- typeclass-based `+` in scope simultaneously when `open Peano` is active.
open Peano

namespace PList

variable {α β : Type}

-- ─────────────────────────────────────────────────────────────────
-- length
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem length_nil :
    length (α := α) nil = 𝟘 := rfl

@[simp] theorem length_cons (h : α) (t : PList α) :
    length (cons h t) = σ (length t) := rfl

theorem length_eq_zero_iff_nil (l : PList α) :
    length l = 𝟘 ↔ l = nil := by
  constructor
  · intro h
    match l with
    | nil      => rfl
    | cons _ _ => simp [length] at h
  · intro h
    subst h
    simp

-- ─────────────────────────────────────────────────────────────────
-- append
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem append_nil (l : PList α) :
    l.append nil = l := by
  induction l with
  | nil      => rfl
  | cons h t ih => simp [append, ih]

@[simp] theorem nil_append (l : PList α) :
    (nil : PList α).append l = l := rfl

theorem append_assoc (l₁ l₂ l₃ : PList α) :
    (l₁.append l₂).append l₃ = l₁.append (l₂.append l₃) := by
  induction l₁ with
  | nil      => rfl
  | cons h t ih => simp [append, ih]

-- NOTE: uses `add` (Peano.Add.add) not `+` to avoid elaboration ambiguity.
theorem length_append (l₁ l₂ : PList α) :
    length (l₁.append l₂) = add (length l₁) (length l₂) := by
  induction l₁ with
  | nil =>
      simp [append, length]
      exact (Peano.Add.zero_add (length l₂)).symm
  | cons h t ih =>
      simp [append, length]
      rw [ih]
      exact (Peano.Add.succ_add (length t) (length l₂)).symm

-- ─────────────────────────────────────────────────────────────────
-- map
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem map_nil (f : α → β) :
    map f (nil : PList α) = nil := rfl

@[simp] theorem map_cons (f : α → β) (h : α) (t : PList α) :
    map f (cons h t) = cons (f h) (map f t) := rfl

theorem length_map (f : α → β) (l : PList α) :
    length (map f l) = length l := by
  induction l with
  | nil      => rfl
  | cons _ _ ih => simp [ih]

theorem map_append (f : α → β) (l₁ l₂ : PList α) :
    map f (l₁.append l₂) = (map f l₁).append (map f l₂) := by
  induction l₁ with
  | nil      => rfl
  | cons h t ih => simp [append, map, ih]

-- ─────────────────────────────────────────────────────────────────
-- zipWith
-- ─────────────────────────────────────────────────────────────────

theorem length_zipWith_same (f : α → β → γ) :
    ∀ (l₁ : PList α) (l₂ : PList β),
    length l₁ = length l₂ → length (zipWith f l₁ l₂) = length l₁ := by
  intro l₁
  induction l₁ with
  | nil => intro _ _; rfl
  | cons h t ih =>
      intro l₂ hl
      cases l₂ with
      | nil =>
          simp only [length_cons, length_nil] at hl
          exact absurd hl (Peano.Axioms.succ_neq_zero _)
      | cons h' t' =>
          simp only [zipWith, length_cons]
          congr 1
          apply ih
          simp only [length_cons] at hl
          exact Peano.Axioms.succ_injective _ _ hl

-- ─────────────────────────────────────────────────────────────────
-- toList / ofList
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem toList_nil :
    toList (α := α) nil = [] := rfl

@[simp] theorem toList_cons (h : α) (t : PList α) :
    toList (cons h t) = h :: toList t := rfl

@[simp] theorem ofList_nil :
    ofList (α := α) [] = nil := rfl

@[simp] theorem ofList_cons (h : α) (t : List α) :
    ofList (h :: t) = cons h (ofList t) := rfl

theorem toList_ofList (l : List α) :
    toList (ofList l) = l := by
  induction l with
  | nil      => rfl
  | cons h t ih => simp [ih]

theorem ofList_toList (l : PList α) :
    ofList (toList l) = l := by
  induction l with
  | nil      => rfl
  | cons h t ih => simp [ih]

-- Bridge: length via Λ isomorphism.
-- Λ : Nat → ℕ₀ converts List.length (Nat) to ℕ₀.
theorem length_toList (l : PList α) :
    Λ (toList l).length = length l := by
  induction l with
  | nil =>
      simp [toList, length, Peano.Axioms.isomorph_0_Λ]
  | cons _ _ ih =>
      simp [toList, List.length_cons, length]
      rw [← ih]
      exact Peano.Axioms.isomorph_σ_Λ _

-- ─────────────────────────────────────────────────────────────────
-- Membresía
-- ─────────────────────────────────────────────────────────────────

theorem mem_cons_iff [DecidableEq α] (x h : α) (t : PList α) :
    mem x (cons h t) = true ↔ x = h ∨ mem x t = true := by
  simp [mem]

theorem Mem_cons_iff (x h : α) (t : PList α) :
    Mem x (cons h t) ↔ x = h ∨ Mem x t := by
  constructor
  · intro hmem
    cases hmem with
    | head   => exact Or.inl rfl
    | tail p => exact Or.inr p
  · intro h
    cases h with
    | inl heq => subst heq; exact Mem.head
    | inr hmem => exact Mem.tail hmem

theorem not_mem_nil (x : α) : ¬ Mem x (nil : PList α) := by
  intro h; cases h

-- ─────────────────────────────────────────────────────────────────
-- append (cons case)
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem cons_append (h : α) (t ys : PList α) :
    cons h t ++ ys = cons h (t ++ ys) := rfl

-- ─────────────────────────────────────────────────────────────────
-- flatMap
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem flatMap_nil (f : α → PList β) :
    flatMap f (nil : PList α) = nil := rfl

@[simp] theorem flatMap_cons (f : α → PList β) (h : α) (t : PList α) :
    flatMap f (cons h t) = (f h) ++ flatMap f t := rfl

-- ─────────────────────────────────────────────────────────────────
-- Mem / append / map membership
-- ─────────────────────────────────────────────────────────────────

theorem Mem_append {α : Type} (x : α) (l₁ l₂ : PList α) :
    Mem x (l₁ ++ l₂) ↔ Mem x l₁ ∨ Mem x l₂ := by
  induction l₁ with
  | nil =>
    constructor
    · intro h; exact Or.inr h
    · rintro (h | h)
      · exact absurd h (not_mem_nil _)
      · exact h
  | cons h t ih =>
    simp only [cons_append, Mem_cons_iff]
    constructor
    · rintro (rfl | ht)
      · exact Or.inl (Or.inl rfl)
      · rcases ih.mp ht with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · rintro ((rfl | ht) | h)
      · exact Or.inl rfl
      · exact Or.inr (ih.mpr (Or.inl ht))
      · exact Or.inr (ih.mpr (Or.inr h))

theorem Mem_map {α β : Type} (f : α → β) (x : β) (l : PList α) :
    Mem x (map f l) ↔ ∃ y, Mem y l ∧ f y = x := by
  induction l with
  | nil =>
    constructor
    · intro h; exact absurd h (not_mem_nil _)
    · rintro ⟨y, hy, _⟩; exact absurd hy (not_mem_nil _)
  | cons h t ih =>
    simp only [map_cons, Mem_cons_iff]
    constructor
    · rintro (rfl | ht)
      · exact ⟨h, Or.inl rfl, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := ih.mp ht
        exact ⟨y, Or.inr hy, rfl⟩
    · rintro ⟨y, (rfl | hy), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (ih.mpr ⟨y, hy, rfl⟩)

-- ─────────────────────────────────────────────────────────────────
-- any / all
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem any_nil (p : α → Bool) : any p nil = false := rfl

@[simp] theorem any_cons (p : α → Bool) (h : α) (t : PList α) :
    any p (cons h t) = (p h || any p t) := rfl

@[simp] theorem all_nil (p : α → Bool) : all p nil = true := rfl

@[simp] theorem all_cons (p : α → Bool) (h : α) (t : PList α) :
    all p (cons h t) = (p h && all p t) := rfl

theorem any_eq_true (p : α → Bool) (l : PList α) :
    any p l = true ↔ ∃ x, Mem x l ∧ p x = true := by
  induction l with
  | nil => simp [any_nil, not_mem_nil]
  | cons h t ih =>
    simp only [any_cons, Bool.or_eq_true, Mem_cons_iff]
    constructor
    · rintro (hp | ht)
      · exact ⟨h, Or.inl rfl, hp⟩
      · obtain ⟨x, hx, hpx⟩ := ih.mp ht
        exact ⟨x, Or.inr hx, hpx⟩
    · rintro ⟨x, rfl | hx, hpx⟩
      · exact Or.inl hpx
      · exact Or.inr (ih.mpr ⟨x, hx, hpx⟩)

theorem all_eq_true (p : α → Bool) (l : PList α) :
    all p l = true ↔ ∀ x, Mem x l → p x = true := by
  induction l with
  | nil => simp [not_mem_nil]
  | cons h t ih =>
    simp only [all_cons, Bool.and_eq_true, Mem_cons_iff]
    constructor
    · rintro ⟨hph, ht⟩ x (rfl | hx)
      · exact hph
      · exact (ih.mp ht) x hx
    · intro hall
      exact ⟨hall h (Or.inl rfl), ih.mpr (fun x hx => hall x (Or.inr hx))⟩

-- ─────────────────────────────────────────────────────────────────
-- filter
-- ─────────────────────────────────────────────────────────────────

theorem length_filter_le (p : α → Bool) (l : PList α) :
    Peano.Order.le₀ (length (filter p l)) (length l) := by
  induction l with
  | nil =>
      simp [filter, length]
      exact Peano.Order.le_refl 𝟘
  | cons h t ih =>
      simp only [filter, length]
      by_cases hp : p h
      · simp [hp]
        exact Peano.Order.succ_le_succ_if_wp ih
      · simp [hp]
        exact Peano.Order.le_succ _ _ ih

-- ─────────────────────────────────────────────────────────────────
-- take / drop: simp lemmas básicos
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem take_zero (l : PList α) : take 𝟘 l = nil := rfl

@[simp] theorem drop_zero (l : PList α) : drop 𝟘 l = l := rfl

@[simp] theorem take_nil (k : ℕ₀) : take k (nil : PList α) = nil := by
  cases k <;> rfl

@[simp] theorem drop_nil (k : ℕ₀) : drop k (nil : PList α) = nil := by
  cases k <;> rfl

@[simp] theorem take_succ_cons (k : ℕ₀) (h : α) (t : PList α) :
    take (σ k) (cons h t) = cons h (take k t) := rfl

@[simp] theorem drop_succ_cons (k : ℕ₀) (h : α) (t : PList α) :
    drop (σ k) (cons h t) = drop k t := rfl

-- ─────────────────────────────────────────────────────────────────
-- take / drop: longitud
-- ─────────────────────────────────────────────────────────────────

/-- Si `k ≤ length l`, los primeros `k` elementos tienen longitud `k`. -/
theorem length_take_le (k : ℕ₀) (l : PList α) (h : k ≤ length l) :
    length (take k l) = k := by
  induction k generalizing l with
  | zero => simp [take]
  | succ k' ih =>
    cases l with
    | nil => exact absurd h (Peano.Order.not_succ_le_zero k')
    | cons head tail =>
      simp only [take_succ_cons, length_cons]
      congr 1
      exact ih tail (Peano.Order.succ_le_succ_then h)

/-- Si `length l < k`, `take k l` devuelve toda la lista. -/
theorem length_take_gt (k : ℕ₀) (l : PList α) (h : length l < k) :
    length (take k l) = length l := by
  induction k generalizing l with
  | zero => exact absurd h (Peano.StrictOrder.nlt_n_0 (length l))
  | succ k' ih =>
    cases l with
    | nil => simp [take]
    | cons head tail =>
      simp only [take_succ_cons, length_cons] at *
      congr 1
      exact ih tail ((Peano.StrictOrder.succ_lt_succ_iff (length tail) k').mp h)

/-- `take k l ++ drop k l = l` para todo `k`. -/
theorem take_append_drop (k : ℕ₀) (l : PList α) :
    (take k l).append (drop k l) = l := by
  induction k generalizing l with
  | zero => simp [take, drop]
  | succ k' ih =>
    cases l with
    | nil => simp [take, drop]
    | cons head tail =>
      simp only [take_succ_cons, drop_succ_cons]
      exact congrArg (cons head) (ih tail)

/-- `add k (length (drop k l)) = length l` cuando `k ≤ length l`. -/
theorem add_length_drop (k : ℕ₀) (l : PList α) (h : k ≤ length l) :
    Peano.Add.add k (length (drop k l)) = length l := by
  induction k generalizing l with
  | zero =>
    simp only [drop_zero]
    exact Peano.Add.zero_add (length l)
  | succ k' ih =>
    cases l with
    | nil => exact absurd h (Peano.Order.not_succ_le_zero k')
    | cons head tail =>
      simp only [drop_succ_cons, length_cons]
      rw [Peano.Add.succ_add]
      congr 1
      exact ih tail (Peano.Order.succ_le_succ_then h)

/-- Longitud de `drop k l` cuando `k ≤ length l`. -/
theorem length_drop_le (k : ℕ₀) (l : PList α) (h : k ≤ length l) :
    length (drop k l) = Peano.Sub.sub (length l) k := by
  induction k generalizing l with
  | zero =>
    simp only [drop_zero]
    exact (Peano.Sub.sub_zero (length l)).symm
  | succ k' ih =>
    cases l with
    | nil => exact absurd h (Peano.Order.not_succ_le_zero k')
    | cons head tail =>
      simp only [drop_succ_cons, length_cons]
      rw [ih tail (Peano.Order.succ_le_succ_then h)]
      exact Peano.Sub.sub_succ_succ_eq (length tail) k'

-- ─────────────────────────────────────────────────────────────────
-- get?: ningún índice ≥ length devuelve valor
-- ─────────────────────────────────────────────────────────────────

/-- Si `length l ≤ i`, entonces `l.get? i = none`. -/
theorem get?_none_of_ge (l : PList α) (i : ℕ₀) (h : length l ≤ i) :
    l.get? i = none := by
  induction l generalizing i with
  | nil => rfl
  | cons head tail ih =>
    cases i with
    | zero => exact absurd h (Peano.Order.not_succ_le_zero (length tail))
    | succ i' =>
      exact ih i' (Peano.Order.succ_le_succ_then h)

-- ─────────────────────────────────────────────────────────────────
-- Igualdad extensional vía get?
-- ─────────────────────────────────────────────────────────────────

/-- Dos `PList`s son iguales si y solo si coinciden en cada índice. -/
theorem plist_ext_get? (l₁ l₂ : PList α)
    (h : ∀ i : ℕ₀, l₁.get? i = l₂.get? i) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons head tail =>
      have h0 := h 𝟘; simp [get?] at h0
  | cons head₁ tail₁ ih =>
    cases l₂ with
    | nil =>
      have h0 := h 𝟘; simp [get?] at h0
    | cons head₂ tail₂ =>
      have hhead : head₁ = head₂ := by
        have h0 := h 𝟘; simp [get?] at h0; exact h0
      have htail : tail₁ = tail₂ := ih tail₂ (fun i => by
        have hi := h (σ i); simp [get?] at hi; exact hi)
      rw [hhead, htail]

end PList
