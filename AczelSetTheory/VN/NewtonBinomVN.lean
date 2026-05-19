/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/NewtonBinomVN.lean
-- Transporte del binomio de Newton (binomTerm, newton_binom) de Peano a HFSet vía vN.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Combinatorics.NewtonBinom

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definición
-- ─────────────────────────────────────────────────────────────────

/-- Término del binomio de Newton: vN (binomTerm a b n k). -/
def binomTermVN (a b n k : ℕ₀) : HFSet := vN (binomTerm a b n k)

-- ─────────────────────────────────────────────────────────────────
-- Casos base de binomTerm
-- ─────────────────────────────────────────────────────────────────

theorem vN_binomTerm_zero (a b n : ℕ₀) :
    vN (binomTerm a b n 𝟘) = vN (Peano.Pow.pow b n) :=
  congrArg vN (binomTerm_zero a b n)

theorem vN_binomTerm_self (a b n : ℕ₀) :
    vN (binomTerm a b n n) = vN (Peano.Pow.pow a n) :=
  congrArg vN (binomTerm_self a b n)

-- ─────────────────────────────────────────────────────────────────
-- Teorema del Binomio de Newton
-- ─────────────────────────────────────────────────────────────────

theorem vN_newton_binom (a b n : ℕ₀) :
    vN (Peano.Pow.pow (add a b) n) = vN (finSum (binomTerm a b n) n) :=
  congrArg vN (newton_binom a b n)

-- ─────────────────────────────────────────────────────────────────
-- Suma de coeficientes binomiales = 2^n
-- ─────────────────────────────────────────────────────────────────

theorem vN_sum_binom_eq_pow_two (n : ℕ₀) :
    vN (finSum (fun k => C(n, k)) n) = vN (Peano.Pow.pow 𝟚 n) :=
  congrArg vN (sum_binom_eq_pow_two n)

end VN
