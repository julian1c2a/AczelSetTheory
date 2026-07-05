import AczelSetTheory.Rationals.CauchySeqAlgebra

namespace ℚ₀

theorem cauchy_mul_is_cauchy_scratch (f g : CauchySeq) (K : ℕ₀) (hK : CauchySeq.mulBound f g ≤ K) :
    ℚ₀.IsCauchy (fun n => f.val (Peano.Add.add n K) * g.val (Peano.Add.add n K)) := by
  intro n m
  have h_bound_f : ∀ k, ℚ₀.absVal (f.val k) ≤ f.boundVal := f.boundVal_prop
  have h_bound_g : ∀ k, ℚ₀.absVal (g.val k) ≤ g.boundVal := g.boundVal_prop
  
  have h_triangle := ℚ₀.absVal_mul_sub_mul (f.val (Peano.Add.add n K)) (g.val (Peano.Add.add n K)) (f.val (Peano.Add.add m K)) (g.val (Peano.Add.add m K))
  
  have h_f_cauchy := f.property (Peano.Add.add n K) (Peano.Add.add m K)
  have h_g_cauchy := g.property (Peano.Add.add n K) (Peano.Add.add m K)
  
  -- Necesitamos probar que min (n + K) (m + K) = (min n m) + K
  -- have h_min_add : Peano.Lattice.min (Peano.Add.add n K) (Peano.Add.add m K) = Peano.Add.add (Peano.Lattice.min n m) K := sorry
  
  -- Necesitamos probar que pow2 (a + b) <= pow2 a * pow2 b
  -- y que (f.boundVal + g.boundVal) * pow2 K <= 1
  
  sorry

end ℚ₀
