import AczelSetTheory.Rationals.IsCauchy

open Peano
open Peano.Axioms

theorem pow2_nonneg_proof (n : ℕ₀) : (0 : ℚ₀) ≤ ℚ₀.pow2 n := by
  sorry

theorem pow2_succ_add_proof (n : ℕ₀) : Add.add (ℚ₀.pow2 (σ n)) (ℚ₀.pow2 (σ n)) = ℚ₀.pow2 n := by
  sorry
