import AczelSetTheory.Rationals.IsCauchy

open Peano
open Peano.Axioms

theorem pow2_succ_add_proof (n : ℕ₀) : Add.add (ℚ₀.pow2 (σ n)) (ℚ₀.pow2 (σ n)) = ℚ₀.pow2 n := by
  dsimp [ℚ₀.pow2]
  rw [ℚ₀.add_mk]
  rw [ℚ₀.mk_eq_iff]
  -- Let's print the goal
  sorry
