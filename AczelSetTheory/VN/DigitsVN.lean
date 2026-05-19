/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/DigitsVN.lean
-- Transporte de la representación en base b (numDigits, ofDigits) de Peano a HFSet vía vN.
-- digits devuelve List (Fin₀ b), no ℕ₀; se transportan numDigits y ofDigits.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Digits

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definiciones
-- ─────────────────────────────────────────────────────────────────

/-- Número de dígitos de n en base base: vN (numDigits base n). -/
def numDigitsVN (base : ℕ₂) (n : ℕ₀) : HFSet := vN (numDigits base n)

/-- Reconstrucción desde lista de dígitos: vN (ofDigits b ds). -/
def ofDigitsVN (b : ℕ₀) (ds : List ℕ₀) : HFSet := vN (ofDigits b ds)

-- ─────────────────────────────────────────────────────────────────
-- numDigits: caso base
-- ─────────────────────────────────────────────────────────────────

theorem vN_numDigits_zero (base : ℕ₂) : vN (numDigits base 𝟘) = vN 𝟘 :=
  congrArg vN (numDigits_zero base)

-- ─────────────────────────────────────────────────────────────────
-- ofDigits: ecuaciones de recursión
-- ─────────────────────────────────────────────────────────────────

theorem vN_ofDigits_nil (b : ℕ₀) : vN (ofDigits b []) = vN 𝟘 :=
  congrArg vN (ofDigits_nil b)

theorem vN_ofDigits_cons (b d : ℕ₀) (ds : List ℕ₀) :
    vN (ofDigits b (d :: ds)) = vN (add d (mul b (ofDigits b ds))) :=
  congrArg vN (ofDigits_cons b d ds)

-- ─────────────────────────────────────────────────────────────────
-- Round-trip: ofDigitsFin (digits base n) = n
-- ─────────────────────────────────────────────────────────────────

theorem vN_ofDigitsFin_digits (base : ℕ₂) (n : ℕ₀) :
    vN (ofDigitsFin base.val.val (digits base n)) = vN n :=
  congrArg vN (ofDigitsFin_digits base n)

end VN
