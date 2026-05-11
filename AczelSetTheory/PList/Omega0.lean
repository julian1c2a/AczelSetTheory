/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/PList/Omega0.lean
-- omega₀: táctica que transporta metas lineales sobre ℕ₀ a ℕ via Ψ y llama omega.

import AczelSetTheory.PList.Lemmas
import Peano.PeanoNat
import Peano.PeanoNat.Add
import Peano.PeanoNat.Axioms
import Peano.PeanoNat.Order
import Peano.PeanoNat.StrictOrder

open Peano

-- ─────────────────────────────────────────────────────────────────
-- Lemas puente ℕ₀ ↔ ℕ via Ψ (sin @[simp] global)
-- ─────────────────────────────────────────────────────────────────

namespace PList.Omega0

theorem ψ_eq_iff (n m : ℕ₀) : n = m ↔ Ψ n = Ψ m :=
  ⟨fun h => h ▸ rfl, Peano.Axioms.Ψ_inj n m⟩

theorem ψ_le_iff (n m : ℕ₀) : n ≤ m ↔ Ψ n ≤ Ψ m :=
  (Peano.Order.isomorph_Ψ_le n m).symm

theorem ψ_lt_iff (n m : ℕ₀) : n < m ↔ Ψ n < Ψ m :=
  Peano.StrictOrder.isomorph_Ψ_lt n m

theorem ψ_zero : Ψ (𝟘 : ℕ₀) = (0 : Nat) :=
  Peano.Axioms.isomorph_0_Ψ

theorem ψ_succ (n : ℕ₀) : Ψ (σ n) = Nat.succ (Ψ n) :=
  Peano.Axioms.isomorph_σ_Ψ n

-- @HAdd.hAdd evita la ambigüedad con Coe Nat ℕ₀ y garantiza que omega reconozca la suma.
theorem ψ_add (n m : ℕ₀) :
    Ψ (add n m) = @HAdd.hAdd Nat Nat Nat instHAdd (Ψ n) (Ψ m) :=
  Peano.Add.isomorph_Ψ_add n m

end PList.Omega0

-- ─────────────────────────────────────────────────────────────────
-- Táctica
-- ─────────────────────────────────────────────────────────────────

/-- Resuelve metas aritméticas lineales sobre ℕ₀ transportándolas a ℕ via Ψ y llamando omega. -/
macro "omega₀" : tactic =>
  `(tactic| (simp only [PList.Omega0.ψ_eq_iff, PList.Omega0.ψ_le_iff, PList.Omega0.ψ_lt_iff,
             PList.Omega0.ψ_zero, PList.Omega0.ψ_succ, PList.Omega0.ψ_add] at *; omega))

-- ─────────────────────────────────────────────────────────────────
-- Tests
-- ─────────────────────────────────────────────────────────────────

section omega₀_tests

variable (n m k : ℕ₀)

example : 𝟘 ≤ n                                          := by omega₀
example : n ≤ n                                           := by omega₀
example (h : n ≤ m) (h' : m ≤ n) : n = m                 := by omega₀
example : n ≤ σ n                                         := by omega₀
example (h : n ≤ m) : n ≤ σ m                             := by omega₀
example (h : n < m) : n ≤ m                               := by omega₀
example (h : n < m) (h' : m ≤ k) : n < k                 := by omega₀
example (h : n ≤ m) : σ n ≤ σ m                           := by omega₀
example (h₁ : n ≤ m) (h₂ : m ≤ k) : n ≤ k               := by omega₀
example : n ≤ add n m                                     := by omega₀
example : add n m = add m n                               := by omega₀
example : add (add n m) k = add n (add m k)               := by omega₀
example (h : σ n = σ m) : n = m                           := by omega₀
example : 𝟘 ≤ add m k                                     := by omega₀
example (h : n < m) (h' : m < k) : σ n ≤ k               := by omega₀

end omega₀_tests
