/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/FactorialVN.lean
-- Transporte del factorial de Peano a HFSet mediante vN.
--
-- Define factVN como imagen directa vN(n!) y exporta las leyes
-- algebraicas transportadas vía el embedding inyectivo vN : ℕ₀ → HFSet.
--
-- Contenido:
--   factVN                  : ℕ₀ → HFSet   (imagen directa de vN)
--   factVN_def              : factVN n = vN (factorial n)
--   vN_factorial_zero       : vN (factorial 𝟘) = vN 𝟙
--   vN_factorial_one        : vN (factorial 𝟙) = vN 𝟙
--   vN_factorial_two        : vN (factorial 𝟚) = vN 𝟚
--   vN_factorial_succ       : vN (factorial (σ n)) = vN (mul (factorial n) (σ n))
--   vN_factorial_ne_zero    : factVN n ≠ vN 𝟘
--   vN_factorial_pos        : lt₀ 𝟘 (factorial n)
--   vN_factorial_ge_one     : le₀ 𝟙 (factorial n)
--   vN_factorial_le_succ    : vN (factorial n) ≤ₑ vN (factorial (σ n))   [HFSet ∈]
--   vN_factorial_mono       : le₀ m n → le₀ (factorial m) (factorial n)

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Combinatorics.Factorial
open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definición: factorial en la imagen de vN
-- ─────────────────────────────────────────────────────────────────

/-- Factorial de von Neumann: imagen de `n!` bajo el embedding vN. -/
def factVN (n : ℕ₀) : HFSet := vN (factorial n)

theorem factVN_def (n : ℕ₀) : factVN n = vN (factorial n) := rfl

-- ─────────────────────────────────────────────────────────────────
-- Leyes transportadas vía congrArg vN
-- ─────────────────────────────────────────────────────────────────

/-- Base: `vN (factorial 𝟘) = vN 𝟙`. -/
theorem vN_factorial_zero : vN (factorial 𝟘) = vN 𝟙 :=
  congrArg vN factorial_zero

/-- Caso uno: `vN (factorial 𝟙) = vN 𝟙`. -/
theorem vN_factorial_one : vN (factorial 𝟙) = vN 𝟙 :=
  congrArg vN factorial_one

/-- Caso dos: `vN (factorial 𝟚) = vN 𝟚`. -/
theorem vN_factorial_two : vN (factorial 𝟚) = vN 𝟚 :=
  congrArg vN factorial_two

/-- Recurrencia: `vN (factorial (σ n)) = vN (mul (factorial n) (σ n))`. -/
theorem vN_factorial_succ (n : ℕ₀) :
    vN (factorial (σ n)) = vN (mul (factorial n) (σ n)) :=
  congrArg vN (factorial_succ n)

-- ─────────────────────────────────────────────────────────────────
-- Positividad y orden
-- ─────────────────────────────────────────────────────────────────

/-- El factorial es siempre estrictamente positivo: `𝟘 < factorial n`. -/
theorem vN_factorial_pos (n : ℕ₀) : lt₀ 𝟘 (factorial n) :=
  factorial_pos n

/-- El factorial es siempre al menos 1: `𝟙 ≤ factorial n`. -/
theorem vN_factorial_ge_one (n : ℕ₀) : le₀ 𝟙 (factorial n) :=
  factorial_ge_one n

/-- El factorial nunca es cero: `factVN n ≠ vN 𝟘`. -/
theorem vN_factorial_ne_zero (n : ℕ₀) : factVN n ≠ vN 𝟘 := by
  intro h
  have := vN_injective h
  exact factorial_ne_zero n this

/-- El factorial es monótono: `m ≤ n → factorial m ≤ factorial n`. -/
theorem vN_factorial_mono {m n : ℕ₀} (h : le₀ m n) : le₀ (factorial m) (factorial n) :=
  factorial_le_mono h

/-- El factorial crece al aplicar sucesor: `factorial n ≤ factorial (σ n)`. -/
theorem vN_factorial_le_succ (n : ℕ₀) : le₀ (factorial n) (factorial (σ n)) :=
  factorial_le_succ n

end VN
