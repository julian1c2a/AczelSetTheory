import AczelSetTheory.Rationals.HFRatOps
import AczelSetTheory.Rationals.IsCauchy
import AczelSetTheory.Rationals.CauchySeqAlgebra

namespace HFRat

def pow2 (n : ℕ₀) : HFRat :=
  { cls  := ℚ₀.pow2 n
    pair := ℚ₀'.ofQ0 (ℚ₀.pow2 n)
    hEq  := by rw [ℚ₀'.toQ0_ofQ0] }

def IsCauchy (f : ℕ₀ → HFRat) : Prop :=
  ∀ n m : ℕ₀, absVal (f n - f m) ≤ pow2 (Peano.Lattice.min n m)

def IsCauchy₂ (f : ℕ₀ → HFRat) : Prop :=
  ∀ n m : ℕ₀, n ≤ m → absVal (f m - f n) ≤ pow2 n

-- Función para extraer la secuencia subyacente de clases de equivalencia
def toQ0Seq (f : ℕ₀ → HFRat) : ℕ₀ → ℚ₀ := fun n => (f n).cls

theorem isCauchy_iff_q0_isCauchy (f : ℕ₀ → HFRat) : IsCauchy f ↔ ℚ₀.IsCauchy (toQ0Seq f) := by
  apply Iff.intro
  · intro h n m
    have h_hf := h n m
    change (absVal (f n - f m)).cls ≤ (pow2 (Peano.Lattice.min n m)).cls at h_hf
    -- The definition of HFRat operations ensures that:
    -- (absVal (f n - f m)).cls = ℚ₀.absVal ((f n).cls - (f m).cls)
    -- and (pow2 k).cls = ℚ₀.pow2 k
    exact h_hf
  · intro h n m
    have h_q0 := h n m
    -- reverse the same definition
    exact h_q0

def CauchySeq := { f : ℕ₀ → HFRat // IsCauchy f }

end HFRat
