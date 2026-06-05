/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/FermatVN.lean
-- Transporte del Pequeño Teorema de Fermat y el Teorema de Wilson a HFSet.
--
-- Público:
--   vN_fermat_little : vN(a^p mod p) = vN(a mod p)   para p primo
--   vN_fermat_modEq  : vN(a^p) ≡ₕ vN(a) [MODHF vN(p)]
--   vN_wilson        : dvd_HF (vN p) (vN((p-1)! + 1))  para p primo
--   vN_wilson_modEq  : vN((p-1)! + 1) ≡ₕ vN(0) [MODHF vN(p)]

import AczelSetTheory.VN.PrimeVN
import AczelSetTheory.VN.ModEqVN
import AczelSetTheory.VN.FactorialVN
import Peano.PeanoNat.NumberTheory.Fermat
import Peano.PeanoNat.NumberTheory.Wilson

open Peano Peano.Arith Peano.ModEq

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Pequeño Teorema de Fermat
-- ─────────────────────────────────────────────────────────────────

/-- Pequeño Teorema de Fermat: `vN(a^p mod p) = vN(a mod p)` para `p` primo. -/
theorem vN_fermat_little (a p : ℕ₀) (hp : Arith.Prime p) :
    vN (mod (pow a p) p) = vN (mod a p) :=
  congrArg vN (Peano.Fermat.fermat_little_theorem a p hp)

/-- Pequeño Teorema de Fermat en forma de congruencia HFSet:
    `vN(a^p) ≡ₕ vN(a) [MODHF vN(p)]`. -/
theorem vN_fermat_modEq (a p : ℕ₀) (hp : Arith.Prime p) :
    vN (pow a p) ≡ₕ vN a [MODHF vN p] :=
  vN_modEq_iff.mpr (Peano.Fermat.fermat_little_theorem a p hp)

-- ─────────────────────────────────────────────────────────────────
-- Teorema de Wilson
-- ─────────────────────────────────────────────────────────────────

/-- Teorema de Wilson: `p ∣ₕ vN((p-1)! + 1)` para `p` primo. -/
theorem vN_wilson {p : ℕ₀} (hp : Arith.Prime p) :
    dvd_HF (vN p) (vN (add (factorial (Peano.Sub.sub p 𝟙)) 𝟙)) := by
  rw [vN_dvd_iff]
  exact Peano.Wilson.wilson hp

/-- Teorema de Wilson en forma de congruencia HFSet:
    `vN((p-1)! + 1) ≡ₕ vN(0) [MODHF vN(p)]`. -/
theorem vN_wilson_modEq {p : ℕ₀} (hp : Arith.Prime p) :
    vN (add (factorial (Peano.Sub.sub p 𝟙)) 𝟙) ≡ₕ vN 𝟘 [MODHF vN p] := by
  rw [vN_modEq_iff]
  exact (modEq_zero_iff_dvd (prime_ne_zero hp)).mpr (Peano.Wilson.wilson hp)

end VN
