/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/SqrtVN.lean
-- Transporte de la raíz cuadrada entera (sqrt/csqrt) de Peano a HFSet vía vN.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Sqrt

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definiciones
-- ─────────────────────────────────────────────────────────────────

/-- Raíz cuadrada entera inferior transportada: vN ⌊√n⌋. -/
def sqrtVN (n : ℕ₀) : HFSet := vN (sqrt n)

/-- Resto de la raíz: vN (n - sqrt(n)²). -/
def sqrtRemVN (n : ℕ₀) : HFSet := vN (sqrtRem n)

/-- Raíz cuadrada entera superior transportada: vN ⌈√n⌉. -/
def csqrtVN (n : ℕ₀) : HFSet := vN (csqrt n)

-- ─────────────────────────────────────────────────────────────────
-- Casos base
-- ─────────────────────────────────────────────────────────────────

theorem vN_sqrt_zero : vN (sqrt 𝟘) = vN 𝟘 :=
  congrArg vN sqrt_zero

theorem vN_sqrtRem_zero : vN (sqrtRem 𝟘) = vN 𝟘 :=
  congrArg vN sqrtRem_zero

theorem vN_sqrt_one : vN (sqrt 𝟙) = vN 𝟙 :=
  congrArg vN sqrt_one

theorem vN_sqrtRem_one : vN (sqrtRem 𝟙) = vN 𝟘 :=
  congrArg vN sqrtRem_one

-- ─────────────────────────────────────────────────────────────────
-- Especificación: n = sqrt(n)² + sqrtRem(n)
-- ─────────────────────────────────────────────────────────────────

theorem vN_sqrtMod_spec (n : ℕ₀) :
    vN n = vN (add (Peano.Pow.pow (sqrt n) 𝟚) (sqrtRem n)) :=
  congrArg vN (sqrtMod_spec n)

-- ─────────────────────────────────────────────────────────────────
-- Raíz superior (csqrt)
-- ─────────────────────────────────────────────────────────────────

theorem vN_csqrt_zero : vN (csqrt 𝟘) = vN 𝟘 :=
  congrArg vN csqrt_zero

theorem vN_csqrt_one : vN (csqrt 𝟙) = vN 𝟙 :=
  congrArg vN csqrt_one

end VN
