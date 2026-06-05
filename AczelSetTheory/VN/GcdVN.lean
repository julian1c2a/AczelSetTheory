/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/GcdVN.lean
-- Transporte del MCD y MCM de Peano a HFSet mediante vN.
--
-- Contenido:
--   gcdVN               : ℕ₀ → ℕ₀ → HFSet   (imagen directa de vN)
--   lcmVN               : ℕ₀ → ℕ₀ → HFSet
--   vN_gcd_comm         : vN (gcd m n) = vN (gcd n m)
--   vN_gcd_zero_right   : vN (gcd m 𝟘) = vN m
--   vN_gcd_zero_left    : vN (gcd 𝟘 m) = vN m
--   vN_gcd_one_right    : vN (gcd m 𝟙) = vN 𝟙
--   vN_gcd_one_left     : vN (gcd 𝟙 m) = vN 𝟙
--   vN_gcd_self         : vN (gcd m m) = vN m
--   vN_gcd_assoc        : vN (gcd (gcd m n) k) = vN (gcd m (gcd n k))
--   vN_gcd_mul_lcm      : vN (mul (gcd m n) (lcm m n)) = vN (mul m n)
--   vN_lcm_comm         : vN (lcm m n) = vN (lcm n m)
--   vN_lcm_zero_left    : vN (lcm 𝟘 m) = vN 𝟘
--   vN_lcm_zero_right   : vN (lcm m 𝟘) = vN 𝟘
--   vN_lcm_self         : vN (lcm m m) = vN m
--   gcdVN_ne_zero_left  : m ≠ 𝟘 → gcdVN m n ≠ vN 𝟘
--   gcdVN_ne_zero_right : n ≠ 𝟘 → gcdVN m n ≠ vN 𝟘

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Arith

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definiciones: MCD y MCM en la imagen de vN
-- ─────────────────────────────────────────────────────────────────

/-- Máximo común divisor de von Neumann: imagen de `gcd m n` bajo el embedding vN. -/
def gcdVN (m n : ℕ₀) : HFSet := vN (gcd m n)

/-- Mínimo común múltiplo de von Neumann: imagen de `lcm m n` bajo el embedding vN. -/
def lcmVN (m n : ℕ₀) : HFSet := vN (lcm m n)

theorem gcdVN_def (m n : ℕ₀) : gcdVN m n = vN (gcd m n) := rfl
theorem lcmVN_def (m n : ℕ₀) : lcmVN m n = vN (lcm m n) := rfl

-- ─────────────────────────────────────────────────────────────────
-- Leyes del MCD transportadas vía congrArg vN
-- ─────────────────────────────────────────────────────────────────

theorem vN_gcd_comm (m n : ℕ₀) : vN (gcd m n) = vN (gcd n m) :=
  congrArg vN (gcd_comm m n)

theorem vN_gcd_zero_right (m : ℕ₀) : vN (gcd m 𝟘) = vN m :=
  congrArg vN (gcd_zero_right m)

theorem vN_gcd_zero_left (m : ℕ₀) : vN (gcd 𝟘 m) = vN m :=
  congrArg vN (gcd_zero_left m)

theorem vN_gcd_one_right (m : ℕ₀) : vN (gcd m 𝟙) = vN 𝟙 :=
  congrArg vN (gcd_one_right m)

theorem vN_gcd_one_left (m : ℕ₀) : vN (gcd 𝟙 m) = vN 𝟙 :=
  congrArg vN (gcd_one_left m)

theorem vN_gcd_self (m : ℕ₀) : vN (gcd m m) = vN m :=
  congrArg vN (gcd_self m)

theorem vN_gcd_assoc (m n k : ℕ₀) :
    vN (gcd (gcd m n) k) = vN (gcd m (gcd n k)) :=
  congrArg vN (gcd_assoc m n k)

-- ─────────────────────────────────────────────────────────────────
-- Leyes del MCM transportadas vía congrArg vN
-- ─────────────────────────────────────────────────────────────────

theorem vN_lcm_comm (m n : ℕ₀) : vN (lcm m n) = vN (lcm n m) :=
  congrArg vN (lcm_comm m n)

theorem vN_lcm_zero_left (m : ℕ₀) : vN (lcm 𝟘 m) = vN 𝟘 :=
  congrArg vN (lcm_zero_left m)

theorem vN_lcm_zero_right (m : ℕ₀) : vN (lcm m 𝟘) = vN 𝟘 :=
  congrArg vN (lcm_zero_right m)

theorem vN_lcm_self (m : ℕ₀) : vN (lcm m m) = vN m :=
  congrArg vN (lcm_self m)

-- ─────────────────────────────────────────────────────────────────
-- Relación entre MCD y MCM
-- ─────────────────────────────────────────────────────────────────

/-- `vN (gcd m n · lcm m n) = vN (m · n)`. -/
theorem vN_gcd_mul_lcm (m n : ℕ₀) :
    vN (mul (gcd m n) (lcm m n)) = vN (mul m n) :=
  congrArg vN (gcd_mul_lcm m n)

-- ─────────────────────────────────────────────────────────────────
-- Positividad / no-nulidad
-- ─────────────────────────────────────────────────────────────────

/-- Si `m ≠ 𝟘`, entonces `gcdVN m n ≠ vN 𝟘`. -/
theorem gcdVN_ne_zero_left {m n : ℕ₀} (hm : m ≠ 𝟘) : gcdVN m n ≠ vN 𝟘 :=
  fun h => absurd (vN_injective h) (gcd_ne_zero_left hm)

/-- Si `n ≠ 𝟘`, entonces `gcdVN m n ≠ vN 𝟘`. -/
theorem gcdVN_ne_zero_right {m n : ℕ₀} (hn : n ≠ 𝟘) : gcdVN m n ≠ vN 𝟘 :=
  fun h => absurd (vN_injective h) (gcd_ne_zero_right hn)

end VN
