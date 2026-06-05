/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/PairingVN.lean
-- Transporte del apareamiento de Cantor (tri, cantorPair) de Peano.Pairing a HFSet vía vN.
-- cantorUnpair devuelve ℕ₀ × ℕ₀ y no se puede transportar directamente.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Pairing

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definiciones
-- ─────────────────────────────────────────────────────────────────

/-- Número triangular T(n) transportado (Pairing.tri). -/
def triVN (n : ℕ₀) : HFSet := vN (tri n)

/-- Apareamiento de Cantor cantorPair(a,b) transportado. -/
def cantorPairVN (a b : ℕ₀) : HFSet := vN (cantorPair a b)

-- ─────────────────────────────────────────────────────────────────
-- tri: casos base y recursión
-- ─────────────────────────────────────────────────────────────────

theorem vN_tri_zero : vN (tri 𝟘) = vN 𝟘 :=
  congrArg vN tri_zero

theorem vN_tri_succ (n : ℕ₀) : vN (tri (σ n)) = vN (add (tri n) (σ n)) :=
  congrArg vN (tri_succ n)

-- ─────────────────────────────────────────────────────────────────
-- cantorPair: caso base
-- ─────────────────────────────────────────────────────────────────

theorem vN_cantorPair_zero_zero : vN (cantorPair 𝟘 𝟘) = vN 𝟘 :=
  congrArg vN cantorPair_zero_zero

-- ─────────────────────────────────────────────────────────────────
-- Proyecciones de cantorUnpair (como valores ℕ₀)
-- ─────────────────────────────────────────────────────────────────

theorem vN_cantorUnpair_fst_cantorPair (a b : ℕ₀) :
    vN (cantorUnpair (cantorPair a b)).1 = vN a :=
  congrArg vN (congrArg Prod.fst (cantorUnpair_cantorPair a b))

theorem vN_cantorUnpair_snd_cantorPair (a b : ℕ₀) :
    vN (cantorUnpair (cantorPair a b)).2 = vN b :=
  congrArg vN (congrArg Prod.snd (cantorUnpair_cantorPair a b))

end VN
