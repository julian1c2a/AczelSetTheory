/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/CRTVN.lean
-- Transporte del Teorema Chino del Resto (CRT) a HFSet vía vN.
--
-- Público:
--   vN_chinese_remainder : para m, n coprimos y a, b arbitrarios,
--     ∃ x : ℕ₀, vN(x) ≡ₕ vN(a) [MODHF vN(m)] ∧ vN(x) ≡ₕ vN(b) [MODHF vN(n)]

import AczelSetTheory.VN.PrimeVN
import AczelSetTheory.VN.ModEqVN
import Peano.PeanoNat.NumberTheory.ChineseRemainder

open Peano Peano.Arith Peano.Primes Peano.CRT

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Teorema Chino del Resto
-- ─────────────────────────────────────────────────────────────────

/-- Teorema Chino del Resto en HFSet:
    para `m`, `n` con `gcd(m,n) = 1` y cualesquiera `a`, `b`,
    existe `x` tal que `vN x ≡ₕ vN a [MODHF vN m]` y `vN x ≡ₕ vN b [MODHF vN n]`. -/
theorem vN_chinese_remainder {m n : ℕ₀} (hcop : coprime_HF (vN m) (vN n))
    (a b : ℕ₀) :
    ∃ x : ℕ₀,
      vN x ≡ₕ vN a [MODHF vN m] ∧
      vN x ≡ₕ vN b [MODHF vN n] := by
  rw [vN_coprime_iff] at hcop
  obtain ⟨x, hx1, hx2⟩ :=
    chinese_remainder ((gcd_eq_one_iff_coprime m n).mp hcop) a b
  exact ⟨x, vN_modEq_iff.mpr hx1, vN_modEq_iff.mpr hx2⟩

end VN
