/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/ModEqVN.lean
-- Transporte de propiedades del módulo y congruencia modular de Peano a HFSet vía vN.
-- ModEq es Prop; se transportan los lemas sobre mod que producen ℕ₀.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.NumberTheory.ModEq

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Propiedades del módulo (valores ℕ₀)
-- ─────────────────────────────────────────────────────────────────

theorem vN_mod_zero_right (a : ℕ₀) : vN (mod a 𝟘) = vN 𝟘 :=
  congrArg vN (mod_zero_right a)

theorem vN_mod_zero_left (n : ℕ₀) : vN (mod 𝟘 n) = vN 𝟘 :=
  congrArg vN (mod_zero_left n)

theorem vN_mod_self (n : ℕ₀) : vN (mod n n) = vN 𝟘 :=
  congrArg vN (mod_self n)

theorem vN_mod_mod (a n : ℕ₀) : vN (mod (mod a n) n) = vN (mod a n) :=
  congrArg vN (mod_mod a n)

theorem vN_add_mod (a b n : ℕ₀) :
    vN (mod (add a b) n) = vN (mod (add (mod a n) (mod b n)) n) :=
  congrArg vN (add_mod a b n)

theorem vN_mul_mod (a b n : ℕ₀) :
    vN (mod (mul a b) n) = vN (mod (mul (mod a n) (mod b n)) n) :=
  congrArg vN (mul_mod a b n)

end VN
