import AczelSetTheory.Reals.Arithmetic

namespace ℝ₀

theorem CauchySeq.isBounded_of_isCauchy_proof (f : CauchySeq) : CauchySeq.IsBounded f := by
  let M : ℚ₀ := Add.add (ℚ₀.pow2 𝟘) (ℚ₀.absVal (f.val 𝟘))
  exists M
  intro n
  
  have h_cauchy := f.property n 𝟘
  have h_min : Peano.Lattice.min n 𝟘 = 𝟘 := Peano.Lattice.min_0_abs n
  rw [h_min] at h_cauchy
  
  let fn := f.val n
  let f0 := f.val 𝟘
  
  have h_tri : ℚ₀.absVal fn ≤ Add.add (ℚ₀.absVal (Add.add fn (Neg.neg f0))) (ℚ₀.absVal f0) := by
    have h_eq : fn = Add.add (Add.add fn (Neg.neg f0)) f0 := by
      calc
        fn = Add.add fn 0 := by rw [ℚ₀.add_zero fn]
        _ = Add.add fn (Add.add (Neg.neg f0) f0) := by rw [ℚ₀.neg_add_self f0]
        _ = Add.add (Add.add fn (Neg.neg f0)) f0 := by rw [ℚ₀.add_assoc fn (Neg.neg f0) f0]
    
    have h_abs_eq : ℚ₀.absVal fn = ℚ₀.absVal (Add.add (Add.add fn (Neg.neg f0)) f0) := by
      exact congrArg ℚ₀.absVal h_eq
      
    rw [h_abs_eq]
    exact ℚ₀.absVal_add_le (Add.add fn (Neg.neg f0)) f0
    
  have h_add_le : Add.add (ℚ₀.absVal (Add.add fn (Neg.neg f0))) (ℚ₀.absVal f0) ≤ Add.add (ℚ₀.pow2 𝟘) (ℚ₀.absVal f0) := 
    ℚ₀.add_le_add_right h_cauchy (ℚ₀.absVal f0)
    
  exact ℚ₀.le_trans h_tri h_add_le

end ℝ₀
