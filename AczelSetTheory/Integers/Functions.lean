/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Functions.lean
-- Funciones básicas sobre ℤ₀: signo, valor absoluto, truncación, sucesor/predecesor, potencia.
--
-- Público:
--   ℤ₀.sign     : ℤ₀ → ℤ₀   (−1, 0, 1)
--   ℤ₀.abs      : ℤ₀ → ℤ₀   (valor absoluto)
--   ℤ₀.toNat    : ℤ₀ → ℕ₀   (parte positiva del representante canónico)
--   ℤ₀.succZ    : ℤ₀ → ℤ₀   (z + 1)
--   ℤ₀.predZ    : ℤ₀ → ℤ₀   (z − 1)
--   ℤ₀.powZ     : ℤ₀ → ℕ₀ → ℤ₀
--   Lemas: sign_zero, sign_ofNat, sign_neg
--          abs_ofNat, abs_nonneg, abs_neg
--          toNat_ofNat, toNat_neg
--          succZ_pred, predZ_succ
--          powZ_zero, powZ_succ, powZ_one

import AczelSetTheory.Integers.Order

namespace ℤ₀

open Peano Peano.Add Peano.Sub Peano.Mul Peano.Order

-- ─────────────────────────────────────────────────────────────────────────────
-- Lemas privados auxiliares
-- ─────────────────────────────────────────────────────────────────────────────

private theorem neg_zero : Neg.neg (0 : ℤ₀) = 0 :=
  (add_zero (Neg.neg (0 : ℤ₀))).symm.trans (neg_add_self 0)

private theorem neg_le_zero_of_zero_le {z : ℤ₀} (h : 0 ≤ z) : Neg.neg z ≤ 0 := by
  have := neg_le_neg h; rwa [neg_zero] at this

private theorem zero_le_neg_of_le_zero {z : ℤ₀} (h : z ≤ 0) : 0 ≤ Neg.neg z := by
  have := neg_le_neg h; rwa [neg_zero] at this

-- ─────────────────────────────────────────────────────────────────────────────
-- sign
-- ─────────────────────────────────────────────────────────────────────────────

/-- Signo de z: 1 si z > 0, −1 si z < 0, 0 si z = 0. -/
def sign (z : ℤ₀) : ℤ₀ :=
  if (0 : ℤ₀) < z then 1 else if z < (0 : ℤ₀) then -1 else 0

theorem sign_zero : sign (0 : ℤ₀) = 0 := by
  simp only [sign]
  have h : ¬ (0 : ℤ₀) < 0 := fun h => h.2 (le_refl 0)
  rw [if_neg h, if_neg h]

theorem sign_ofNat (n : ℕ₀) (hn : n ≠ 𝟘) : sign (ofNat n) = 1 := by
  simp only [sign]
  rw [if_pos]
  exact ⟨zero_le_ofNat n, fun hle => hn (by
    have h : ofNat n ≤ ofNat 𝟘 := hle
    rw [le_ofNat_iff] at h; omega₀)⟩

theorem sign_neg (z : ℤ₀) (hz : z < 0) : sign z = -1 := by
  simp only [sign]
  have h1 : ¬ (0 : ℤ₀) < z := fun h => hz.2 h.1
  rw [if_neg h1, if_pos hz]

-- ─────────────────────────────────────────────────────────────────────────────
-- abs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Valor absoluto: z si z ≥ 0, −z si z < 0. -/
def abs (z : ℤ₀) : ℤ₀ := if 0 ≤ z then z else -z

theorem abs_ofNat (n : ℕ₀) : abs (ofNat n) = ofNat n := by
  simp [abs, zero_le_ofNat]

theorem abs_nonneg (z : ℤ₀) : 0 ≤ abs z := by
  simp only [abs]
  by_cases h : (0 : ℤ₀) ≤ z
  · rw [if_pos h]; exact h
  · rw [if_neg h]
    exact zero_le_neg_of_le_zero ((le_total z 0).resolve_right h)

theorem abs_neg (z : ℤ₀) : abs (-z) = abs z := by
  simp only [abs]
  by_cases hz : (0 : ℤ₀) ≤ z
  · by_cases hnz : (0 : ℤ₀) ≤ -z
    · rw [if_pos hz, if_pos hnz]
      have h1 : -z ≤ 0 := neg_le_zero_of_zero_le hz
      have h2 : -z = 0    := le_antisymm h1 hnz
      have h3 : z = 0     := by have := neg_neg z; rw [h2, neg_zero] at this; exact this.symm
      rw [h2, h3]
    · rw [if_neg hnz, if_pos hz, neg_neg]
  · by_cases hnz : (0 : ℤ₀) ≤ -z
    · rw [if_pos hnz, if_neg hz]
    · exfalso
      exact hnz (zero_le_neg_of_le_zero ((le_total z 0).resolve_right hz))

-- ─────────────────────────────────────────────────────────────────────────────
-- toNat
-- ─────────────────────────────────────────────────────────────────────────────

/-- Parte positiva del representante canónico (cero si z ≤ 0). -/
def toNat (z : ℤ₀) : ℕ₀ := z.repr.1

theorem toNat_ofNat (n : ℕ₀) : toNat (ofNat n) = n := by
  simp [toNat, repr_ofNat]

theorem toNat_neg (n : ℕ₀) : toNat (Neg.neg (ofNat n)) = 𝟘 := by
  simp only [toNat]
  have heq := repr_neg_intEq (ofNat n)
  rw [repr_ofNat] at heq
  simp only [] at heq
  rcases repr_normalized (Neg.neg (ofNat n)) with h | h
  · exact h
  · simp only [h] at heq; omega₀

-- ─────────────────────────────────────────────────────────────────────────────
-- succZ / predZ
-- ─────────────────────────────────────────────────────────────────────────────

/-- Sucesor entero: z + 1. -/
def succZ (z : ℤ₀) : ℤ₀ := Add.add z 1

/-- Predecesor entero: z − 1. -/
def predZ (z : ℤ₀) : ℤ₀ := Add.add z (-1)

theorem succZ_pred (z : ℤ₀) : predZ (succZ z) = z := by
  simp only [succZ, predZ]
  rw [add_assoc, add_neg_self, add_zero]

theorem predZ_succ (z : ℤ₀) : succZ (predZ z) = z := by
  simp only [succZ, predZ]
  rw [add_assoc, neg_add_self, add_zero]

-- ─────────────────────────────────────────────────────────────────────────────
-- powZ
-- ─────────────────────────────────────────────────────────────────────────────

/-- Potencia entera: z^n para n : ℕ₀. -/
def powZ (z : ℤ₀) : ℕ₀ → ℤ₀
  | .zero   => 1
  | .succ n => Mul.mul (powZ z n) z

theorem powZ_zero (z : ℤ₀) : powZ z 𝟘 = 1 := rfl

theorem powZ_succ (z : ℤ₀) (n : ℕ₀) : powZ z (σ n) = Mul.mul (powZ z n) z := rfl

theorem powZ_one (z : ℤ₀) : powZ z 𝟙 = z := by
  rw [show (𝟙 : ℕ₀) = σ 𝟘 from rfl, powZ_succ, powZ_zero, one_mul]

end ℤ₀
