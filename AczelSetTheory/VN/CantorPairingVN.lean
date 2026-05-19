/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/CantorPairingVN.lean
-- Transporte del apareamiento de Cantor (pair, fst, snd, triag) de Peano a HFSet vía vN.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Foundation.CantorPairing

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definiciones
-- ─────────────────────────────────────────────────────────────────

/-- Número triangular T(n) = n(n+1)/2 transportado. -/
def triagVN (n : ℕ₀) : HFSet := vN (Foundation.triag n)

/-- Apareamiento de Cantor pair(m,n) transportado. -/
def pairVN (m n : ℕ₀) : HFSet := vN (Foundation.pair m n)

/-- Anti-diagonal transportado. -/
def antidiagVN (z : ℕ₀) : HFSet := vN (Foundation.antidiag z)

/-- Primera proyección transportada. -/
def fstVN (z : ℕ₀) : HFSet := vN (Foundation.fst z)

/-- Segunda proyección transportada. -/
def sndVN (z : ℕ₀) : HFSet := vN (Foundation.snd z)

-- ─────────────────────────────────────────────────────────────────
-- triag: casos base y recursión
-- ─────────────────────────────────────────────────────────────────

theorem vN_triag_zero : vN (Foundation.triag 𝟘) = vN 𝟘 :=
  congrArg vN Foundation.triag_zero

theorem vN_triag_succ (n : ℕ₀) :
    vN (Foundation.triag (σ n)) = vN (add (Foundation.triag n) (σ n)) :=
  congrArg vN (Foundation.triag_succ n)

-- ─────────────────────────────────────────────────────────────────
-- pair / fst / snd: inversas
-- ─────────────────────────────────────────────────────────────────

theorem vN_pair_fst (m n : ℕ₀) : vN (Foundation.fst (Foundation.pair m n)) = vN m :=
  congrArg vN (Foundation.pair_fst m n)

theorem vN_pair_snd (m n : ℕ₀) : vN (Foundation.snd (Foundation.pair m n)) = vN n :=
  congrArg vN (Foundation.pair_snd m n)

theorem vN_pair_surj (z : ℕ₀) :
    vN (Foundation.pair (Foundation.fst z) (Foundation.snd z)) = vN z :=
  congrArg vN (Foundation.pair_surj z)

-- ─────────────────────────────────────────────────────────────────
-- antidiag
-- ─────────────────────────────────────────────────────────────────

theorem vN_antidiag_pair (m n : ℕ₀) :
    vN (Foundation.antidiag (Foundation.pair m n)) = vN (add m n) :=
  congrArg vN (Foundation.antidiag_pair m n)

end VN
