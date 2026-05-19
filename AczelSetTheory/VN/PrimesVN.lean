/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/PrimesVN.lean
-- Transporte de la aritmética de primos (smallestDivisor, isPrimeb) de Peano a HFSet vía vN.
-- Prime es Prop; se transporta smallestDivisor que produce ℕ₀.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Primes

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definición
-- ─────────────────────────────────────────────────────────────────

/-- Divisor mínimo de n (n ≥ 2) transportado: vN (smallestDivisor n). -/
def smallestDivisorVN (n : ℕ₀) : HFSet := vN (smallestDivisor n)

end VN
