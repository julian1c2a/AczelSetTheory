/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/PList/Fin0.lean
-- Fin₀: tipo índice acotado sobre ℕ₀, análogo de Lean's `Fin` pero en la
-- jerarquía de Peano.  Proporciona además `PList.get` (acceso total).

import AczelSetTheory.PList.Omega0
import Peano.PeanoNat
import Peano.PeanoNat.StrictOrder
import Peano.PeanoNat.Order
import Peano.PeanoNat.Axioms

open Peano

-- ─────────────────────────────────────────────────────────────────
-- Definición principal
-- ─────────────────────────────────────────────────────────────────

/-- Índice acotado en ℕ₀: análogo de `Fin n` pero sobre el tipo de Peano ℕ₀.
    `Fin₀ 𝟘` es un tipo vacío (ningún `val` satisface `val < 𝟘`).
    `Fin₀ (σ n)` tiene exactamente `σ n` habitantes: `𝟘, σ 𝟘, …, n`. -/
structure Fin₀ (n : ℕ₀) : Type where
  val  : ℕ₀
  isLt : val < n
  deriving Repr

namespace Fin₀

variable {n m : ℕ₀}

-- ─────────────────────────────────────────────────────────────────
-- Constructores canónicos
-- ─────────────────────────────────────────────────────────────────

/-- El índice 0 en `Fin₀ (σ n)`. -/
def zero (n : ℕ₀) : Fin₀ (σ n) :=
  ⟨𝟘, Peano.StrictOrder.lt_zero_succ n⟩

/-- El sucesor de un índice de `Fin₀ n` vive en `Fin₀ (σ n)`. -/
def succ (i : Fin₀ n) : Fin₀ (σ n) :=
  ⟨σ i.val, by
    have h := i.isLt
    simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at *
    omega⟩

/-- El último índice: `n` en `Fin₀ (σ n)`. -/
def last (n : ℕ₀) : Fin₀ (σ n) :=
  ⟨n, Peano.StrictOrder.lt_succ_self n⟩

-- ─────────────────────────────────────────────────────────────────
-- Igualdad
-- ─────────────────────────────────────────────────────────────────

theorem ext {i j : Fin₀ n} (h : i.val = j.val) : i = j := by
  cases i; cases j; simp_all

instance : DecidableEq (Fin₀ n) := fun i j =>
  if h : i.val = j.val then .isTrue (ext h) else .isFalse (fun heq => h (congrArg val heq))

-- ─────────────────────────────────────────────────────────────────
-- Orden
-- ─────────────────────────────────────────────────────────────────

instance : LT (Fin₀ n) := ⟨fun i j => i.val < j.val⟩
instance : LE (Fin₀ n) := ⟨fun i j => i.val ≤ j.val⟩

-- ─────────────────────────────────────────────────────────────────
-- Puentes con Lean's `Fin` via el isomorfismo Ψ : ℕ₀ → ℕ
-- ─────────────────────────────────────────────────────────────────

/-- Convierte `Fin₀ n` en el `Fin (Ψ n)` de Lean. -/
def toFin (i : Fin₀ n) : Fin (Ψ n) :=
  ⟨Ψ i.val, (PList.Omega0.ψ_lt_iff i.val n).mp i.isLt⟩

/-- Convierte un `Fin (Ψ n)` de Lean en `Fin₀ n`. -/
def ofFin (i : Fin (Ψ n)) : Fin₀ n :=
  ⟨Λ i.val, by
    have h := i.isLt
    simp only [PList.Omega0.ψ_lt_iff]
    have hsurj : i.val = Ψ (Λ i.val) := Peano.Axioms.Ψ_surj i.val
    omega⟩

-- ─────────────────────────────────────────────────────────────────
-- Lemas básicos
-- ─────────────────────────────────────────────────────────────────

/-- `Fin₀ 𝟘` está vacío. -/
theorem elim_zero (i : Fin₀ 𝟘) : False := by
  have h := i.isLt
  simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_zero] at h
  omega

theorem val_lt_bound (i : Fin₀ n) : i.val < n := i.isLt

theorem val_le_bound_pred (i : Fin₀ n) {k : ℕ₀} (hk : n = σ k) : i.val ≤ k := by
  subst hk
  have h := i.isLt
  simp only [PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at h
  simp only [PList.Omega0.ψ_le_iff]
  omega

end Fin₀

-- ─────────────────────────────────────────────────────────────────
-- PList.get : acceso total garantizado por Fin₀
-- ─────────────────────────────────────────────────────────────────

namespace PList

variable {α : Type}

/-- Acceso total a una `PList` usando un índice `Fin₀ (l.length)`.
    El caso `nil` es estructuralmente imposible porque `Fin₀ 𝟘` está vacío. -/
def get : (l : PList α) → Fin₀ (l.length) → α
  | cons h _,  ⟨.zero,   _⟩   => h
  | cons _ t,  ⟨.succ i, hi⟩  =>
      get t ⟨i, by
        simp only [length_cons, PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hi
        simp only [PList.Omega0.ψ_lt_iff]
        omega⟩
  -- Caso nil: imposible porque Fin₀ 𝟘 está vacío
  | nil, i => absurd i.isLt (by
      simp only [length_nil, PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_zero]
      omega)

/-- `get` es coherente con `get?`: el valor devuelto es el que `get?` encontraría. -/
theorem get_eq_get? (l : PList α) (i : Fin₀ (l.length)) :
    l.get? i.val = some (l.get i) := by
  induction l with
  | nil => exact absurd i.isLt (by
      simp only [length_nil, PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_zero]; omega)
  | cons h t ih =>
    cases i with
    | mk v hv =>
      cases v with
      | zero => simp [get?, get]
      | succ v' =>
        simp only [get?, get]
        exact ih ⟨v', by
          simp only [length_cons, PList.Omega0.ψ_lt_iff, PList.Omega0.ψ_succ] at hv
          simp only [PList.Omega0.ψ_lt_iff]
          omega⟩

end PList
