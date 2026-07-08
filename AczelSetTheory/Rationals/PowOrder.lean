/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/PowOrder.lean
-- Lemas de orden para la potencia natural `ℚ₀.pow` (definida en Roots.lean).
--
-- API:
--   pow_zero, pow_succ, pow_one, one_pow
--   pow_add        : pow x (m + n) = pow x m * pow x n
--   zero_le_one    : (0 : ℚ₀) ≤ 1
--   pow_nonneg     : 0 ≤ x → 0 ≤ pow x n
--   pow_le_pow_left: 0 ≤ x → x ≤ y → pow x n ≤ pow y n
--   one_le_pow     : 1 ≤ x → 1 ≤ pow x n
--   absVal_pow     : |x^n| = |x|^n
--
-- Nota: `pow` está definida con `Mul.mul`; enunciamos `pow_succ` con `*` (HMul,
-- defeq) para que los lemas de anillo de ℚ₀ (en forma `*`) encajen por `rw`.
--
-- Dependencies: AczelSetTheory.Rationals.Roots, AczelSetTheory.Rationals.AbsVal
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Rationals.Roots
import AczelSetTheory.Rationals.AbsVal

namespace ℚ₀

-- ============================================================
-- Sección 1: Cómputo básico de pow
-- ============================================================

theorem pow_zero (x : ℚ₀) : pow x 𝟘 = 1 := rfl

theorem pow_succ (x : ℚ₀) (n : ℕ₀) : pow x (σ n) = x * pow x n := rfl

theorem pow_one (x : ℚ₀) : pow x 𝟙 = x := by
  show x * pow x 𝟘 = x
  rw [pow_zero, mul_one]


theorem pow_add (x : ℚ₀) (m n : ℕ₀) :
    pow x (Peano.Add.add m n) = pow x m * pow x n := by
  induction n with
  | zero => rw [Peano.Add.add_zero, pow_zero, mul_one]
  | succ k ih =>
    rw [Peano.Add.add_succ, pow_succ, ih, pow_succ,
        ← mul_assoc, mul_comm x (pow x m), mul_assoc]

-- ============================================================
-- Sección 2: Positividad y monotonía
-- ============================================================

theorem zero_le_one : (0 : ℚ₀) ≤ 1 := ofNat₀_nonneg 𝟙

theorem pow_nonneg {x : ℚ₀} (hx : 0 ≤ x) (n : ℕ₀) : 0 ≤ pow x n := by
  induction n with
  | zero => rw [pow_zero]; exact zero_le_one
  | succ k ih => rw [pow_succ]; exact mul_nonneg hx ih

theorem pow_le_pow_left {x y : ℚ₀} (hx : 0 ≤ x) (hxy : x ≤ y) (n : ℕ₀) :
    pow x n ≤ pow y n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact le_refl 1
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul hxy ih hx (pow_nonneg hx k)

theorem one_le_pow {x : ℚ₀} (hx : 1 ≤ x) (n : ℕ₀) : 1 ≤ pow x n := by
  induction n with
  | zero => rw [pow_zero]; exact le_refl 1
  | succ k ih =>
    rw [pow_succ]
    calc (1 : ℚ₀) = (1 : ℚ₀) * 1 := (mul_one (1 : ℚ₀)).symm
      _ ≤ x * pow x k := mul_le_mul hx ih zero_le_one zero_le_one

-- ============================================================
-- Sección 3: Valor absoluto y potencia
-- ============================================================

theorem absVal_pow (x : ℚ₀) (n : ℕ₀) : absVal (pow x n) = pow (absVal x) n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, absVal_of_nonneg zero_le_one]
  | succ k ih => rw [pow_succ, pow_succ, absVal_mul, ih]

end ℚ₀
