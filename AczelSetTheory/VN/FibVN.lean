/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/FibVN.lean
-- Transporte de la sucesión de Fibonacci de Peano a HFSet mediante vN.
--
-- Contenido:
--   fibVN               : ℕ₀ → HFSet   (imagen directa de vN)
--   fibVN_def           : fibVN n = vN (fib n)
--   vN_fib_zero         : vN (fib 𝟘) = vN 𝟘
--   vN_fib_one          : vN (fib 𝟙) = vN 𝟙
--   vN_fib_two          : vN (fib 𝟚) = vN 𝟙
--   vN_fib_succ_succ    : vN (fib (σ (σ n))) = vN (add (fib n) (fib (σ n)))

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Combinatorics.Fibonacci

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definición: Fibonacci en la imagen de vN
-- ─────────────────────────────────────────────────────────────────

/-- Fibonacci de von Neumann: imagen de `fib n` bajo el embedding vN. -/
def fibVN (n : ℕ₀) : HFSet := vN (fib n)

theorem fibVN_def (n : ℕ₀) : fibVN n = vN (fib n) := rfl

-- ─────────────────────────────────────────────────────────────────
-- Casos base y recurrencia transportados vía congrArg vN
-- ─────────────────────────────────────────────────────────────────

/-- Caso cero: `vN (fib 𝟘) = vN 𝟘`. -/
theorem vN_fib_zero : vN (fib 𝟘) = vN 𝟘 :=
  congrArg vN fib_zero

/-- Caso uno: `vN (fib 𝟙) = vN 𝟙`. -/
theorem vN_fib_one : vN (fib 𝟙) = vN 𝟙 :=
  congrArg vN fib_one

/-- Caso dos: `vN (fib 𝟚) = vN 𝟙`. -/
theorem vN_fib_two : vN (fib 𝟚) = vN 𝟙 :=
  congrArg vN fib_two

/-- Recurrencia: `vN (fib (σ (σ n))) = vN (add (fib n) (fib (σ n)))`. -/
theorem vN_fib_succ_succ (n : ℕ₀) :
    vN (fib (σ (σ n))) = vN (add (fib n) (fib (σ n))) :=
  congrArg vN (fib_succ_succ n)

end VN
