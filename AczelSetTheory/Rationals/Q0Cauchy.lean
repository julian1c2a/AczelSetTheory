/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.Q0Ops
import AczelSetTheory.Rationals.IsCauchy
import AczelSetTheory.Rationals.CauchySeqAlgebra

namespace ℚ₀

def pow2 (n : ℕ₀) : ℚ₀ :=
  { cls  := ℚ₀cls.pow2 n
    pair := ℚ₀can.ofCls (ℚ₀cls.pow2 n)
    hEq  := by rw [ℚ₀can.toCls_ofCls] }

def IsCauchy (f : ℕ₀ → ℚ₀) : Prop :=
  ∀ n m : ℕ₀, absVal (f n - f m) ≤ pow2 (Peano.Lattice.min n m)

def IsCauchy₂ (f : ℕ₀ → ℚ₀) : Prop :=
  ∀ n m : ℕ₀, n ≤ m → absVal (f m - f n) ≤ pow2 n

-- Función para extraer la secuencia subyacente de clases de equivalencia
def toClsSeq (f : ℕ₀ → ℚ₀) : ℕ₀ → ℚ₀cls := fun n => (f n).cls

theorem isCauchy_iff_q0_isCauchy (f : ℕ₀ → ℚ₀) : IsCauchy f ↔ ℚ₀cls.IsCauchy (toClsSeq f) := by
  apply Iff.intro
  · intro h n m
    have h_hf := h n m
    change (absVal (f n - f m)).cls ≤ (pow2 (Peano.Lattice.min n m)).cls at h_hf
    -- The definition of ℚ₀ operations ensures that:
    -- (absVal (f n - f m)).cls = ℚ₀cls.absVal ((f n).cls - (f m).cls)
    -- and (pow2 k).cls = ℚ₀cls.pow2 k
    exact h_hf
  · intro h n m
    have h_q0 := h n m
    -- reverse the same definition
    exact h_q0

def CauchySeq := { f : ℕ₀ → ℚ₀ // IsCauchy f }

end ℚ₀
