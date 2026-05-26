/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/LatticeVN.lean
--
-- Transporte de mínimo y máximo de Peano a HFSet mediante el embedding vN.
--
-- Contenido:
--   minVN                   : ℕ₀ → ℕ₀ → HFSet  (imagen de min bajo vN)
--   maxVN                   : ℕ₀ → ℕ₀ → HFSet  (imagen de max bajo vN)
--   vN_min_idem             : vN (min n n) = vN n
--   vN_max_idem             : vN (max n n) = vN n
--   vN_min_zero_left        : vN (min 𝟘 n) = vN 𝟘
--   vN_min_zero_right       : vN (min n 𝟘) = vN 𝟘
--   vN_max_zero_left        : vN (max 𝟘 n) = vN n
--   vN_max_zero_right       : vN (max n 𝟘) = vN n
--   vN_min_comm             : vN (min m n) = vN (min n m)
--   vN_max_comm             : vN (max m n) = vN (max n m)
--   vN_min_assoc            : vN (min (min m n) k) = vN (min m (min n k))
--   vN_max_assoc            : vN (max (max m n) k) = vN (max m (max n k))
--   vN_eq_of_max_eq_min     : max m n = min m n → vN m = vN n
--   vN_le_then_max_eq_right : le₀ m n → vN (max m n) = vN n
--   vN_le_then_max_eq_left  : le₀ n m → vN (max m n) = vN m
--   vN_le_then_min_eq_left  : le₀ m n → vN (min m n) = vN m
--   vN_le_then_min_eq_right : le₀ n m → vN (min m n) = vN n
--   vN_le_max_left          : le₀ n (max n m)
--   vN_le_max_right         : le₀ m (max n m)
--   vN_min_le_left          : le₀ (min n m) n
--   vN_min_le_right         : le₀ (min n m) m

import AczelSetTheory.VN.Basic
import Peano.PeanoNat.Lattice

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definiciones: mínimo y máximo en la imagen de vN
-- ─────────────────────────────────────────────────────────────────

/-- Mínimo de von Neumann: imagen de `min m n` bajo el embedding vN. -/
def minVN (m n : ℕ₀) : HFSet := vN (min m n)

/-- Máximo de von Neumann: imagen de `max m n` bajo el embedding vN. -/
def maxVN (m n : ℕ₀) : HFSet := vN (max m n)

theorem minVN_def (m n : ℕ₀) : minVN m n = vN (min m n) := rfl
theorem maxVN_def (m n : ℕ₀) : maxVN m n = vN (max m n) := rfl

-- ─────────────────────────────────────────────────────────────────
-- Leyes idempotentes
-- ─────────────────────────────────────────────────────────────────

theorem vN_min_idem (n : ℕ₀) : vN (min n n) = vN n :=
  congrArg vN (min_idem n)

theorem vN_max_idem (n : ℕ₀) : vN (max n n) = vN n :=
  congrArg vN (max_idem n)

-- ─────────────────────────────────────────────────────────────────
-- Absorción del cero
-- ─────────────────────────────────────────────────────────────────

theorem vN_min_zero_left (n : ℕ₀) : vN (min 𝟘 n) = vN 𝟘 :=
  congrArg vN (min_abs_0 n)

theorem vN_min_zero_right (n : ℕ₀) : vN (min n 𝟘) = vN 𝟘 :=
  congrArg vN (min_0_abs n)

theorem vN_max_zero_left (n : ℕ₀) : vN (max 𝟘 n) = vN n :=
  congrArg vN (max_not_0 n)

theorem vN_max_zero_right (n : ℕ₀) : vN (max n 𝟘) = vN n :=
  congrArg vN (max_0_not n)

-- ─────────────────────────────────────────────────────────────────
-- Conmutatividad
-- ─────────────────────────────────────────────────────────────────

theorem vN_min_comm (m n : ℕ₀) : vN (min m n) = vN (min n m) :=
  congrArg vN (min_comm m n)

theorem vN_max_comm (m n : ℕ₀) : vN (max m n) = vN (max n m) :=
  congrArg vN (max_comm m n)

-- ─────────────────────────────────────────────────────────────────
-- Asociatividad
-- ─────────────────────────────────────────────────────────────────

theorem vN_min_assoc (m n k : ℕ₀) :
    vN (min (min m n) k) = vN (min m (min n k)) :=
  congrArg vN (min_assoc m n k)

theorem vN_max_assoc (m n k : ℕ₀) :
    vN (max (max m n) k) = vN (max m (max n k)) :=
  congrArg vN (max_assoc m n k)

-- ─────────────────────────────────────────────────────────────────
-- Igualdad vía max = min
-- ─────────────────────────────────────────────────────────────────

theorem vN_eq_of_max_eq_min (m n : ℕ₀) :
    max m n = min m n → vN m = vN n :=
  fun h => congrArg vN (eq_of_max_eq_min m n h)

-- ─────────────────────────────────────────────────────────────────
-- Monotonía respecto al orden ≤₀
-- ─────────────────────────────────────────────────────────────────

theorem vN_le_then_max_eq_right (m n : ℕ₀) (h : le₀ m n) :
    vN (max m n) = vN n :=
  congrArg vN (le_then_max_eq_right m n h)

theorem vN_le_then_max_eq_left (m n : ℕ₀) (h : le₀ n m) :
    vN (max m n) = vN m :=
  congrArg vN (le_then_max_eq_left m n h)

theorem vN_le_then_min_eq_left (m n : ℕ₀) (h : le₀ m n) :
    vN (min m n) = vN m :=
  congrArg vN (le_then_min_eq_left m n h)

theorem vN_le_then_min_eq_right (m n : ℕ₀) (h : le₀ n m) :
    vN (min m n) = vN n :=
  congrArg vN (le_then_min_eq_right m n h)

-- ─────────────────────────────────────────────────────────────────
-- Cotas del orden
-- ─────────────────────────────────────────────────────────────────

theorem vN_le_max_left (n m : ℕ₀) : le₀ n (max n m) := le_max_left n m
theorem vN_le_max_right (n m : ℕ₀) : le₀ m (max n m) := le_max_right n m
theorem vN_min_le_left (n m : ℕ₀) : le₀ (min n m) n := min_le_left n m
theorem vN_min_le_right (n m : ℕ₀) : le₀ (min n m) m := min_le_right n m

end VN
