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
-- any / all
-- ─────────────────────────────────────────────────────────────────

@[simp] theorem any_nil (p : α → Bool) : any p nil = false := rfl

@[simp] theorem any_cons (p : α → Bool) (h : α) (t : PList α) :
    any p (cons h t) = (p h || any p t) := rfl

@[simp] theorem all_nil (p : α → Bool) : all p nil = true := rfl

@[simp] theorem all_cons (p : α → Bool) (h : α) (t : PList α) :
    all p (cons h t) = (p h && all p t) := rfl

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

end PList
