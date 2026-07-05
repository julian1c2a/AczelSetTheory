import AczelSetTheory.Rationals.CauchySeqAlgebra
import Peano.PeanoNat.Arith

namespace ℚ₀

theorem boundVal_nonneg (f : CauchySeq) : 0 ≤ f.boundVal := by
  have h1 : (0 : ℚ₀) ≤ pow2 𝟘 := pow2_nonneg 𝟘
  have h2 : (0 : ℚ₀) ≤ absVal (f.val 𝟘) := absVal_nonneg _
  have h_add : Add.add 0 0 ≤ Add.add (pow2 𝟘) (absVal (f.val 𝟘)) := add_le_add h1 h2
  rw [add_zero] at h_add
  exact h_add

theorem cauchy_mul_is_cauchy_test (f g : CauchySeq) (K : ℕ₀) (hK : CauchySeq.mulBound f g ≤ K) :
    ℚ₀.IsCauchy (fun n => f.val (Peano.Add.add n K) * g.val (Peano.Add.add n K)) := by
  intro n m
  have h_bound_f : ∀ k, ℚ₀.absVal (f.val k) ≤ f.boundVal := f.boundVal_prop
  have h_bound_g : ∀ k, ℚ₀.absVal (g.val k) ≤ g.boundVal := g.boundVal_prop
  
  let fnK := f.val (Peano.Add.add n K)
  let gnK := g.val (Peano.Add.add n K)
  let fmK := f.val (Peano.Add.add m K)
  let gmK := g.val (Peano.Add.add m K)
  
  have h_triangle : ℚ₀.absVal (fnK * gnK - fmK * gmK) ≤ 
    (ℚ₀.absVal fnK * ℚ₀.absVal (gnK - gmK)) + (ℚ₀.absVal gmK * ℚ₀.absVal (fnK - fmK)) := 
      ℚ₀.absVal_mul_sub_mul fnK gnK fmK gmK
      
  have h_f_cauchy := f.property (Peano.Add.add n K) (Peano.Add.add m K)
  have h_g_cauchy := g.property (Peano.Add.add n K) (Peano.Add.add m K)
  
  have h_min : Peano.Lattice.min (Peano.Add.add n K) (Peano.Add.add m K) = Peano.Add.add (Peano.Lattice.min n m) K :=
    Peano.Arith.min_add_add_right n m K
    
  rw [h_min] at h_f_cauchy h_g_cauchy
  
  have h_pow2_add : ℚ₀.pow2 (Peano.Add.add (Peano.Lattice.min n m) K) = 
    ℚ₀.pow2 (Peano.Lattice.min n m) * ℚ₀.pow2 K := ℚ₀.pow2_add _ _
    
  rw [h_pow2_add] at h_f_cauchy h_g_cauchy
  
  -- Bound the parts
  have h_part1 : Mul.mul (ℚ₀.absVal fnK) (ℚ₀.absVal (gnK - gmK)) ≤ Mul.mul f.boundVal (ℚ₀.pow2 (Peano.Lattice.min n m) * ℚ₀.pow2 K) := by
    apply ℚ₀.mul_le_mul (h_bound_f _) h_g_cauchy (ℚ₀.absVal_nonneg _) (ℚ₀.absVal_nonneg _)
    
  have h_part2 : Mul.mul (ℚ₀.absVal gmK) (ℚ₀.absVal (fnK - fmK)) ≤ Mul.mul g.boundVal (ℚ₀.pow2 (Peano.Lattice.min n m) * ℚ₀.pow2 K) := by
    apply ℚ₀.mul_le_mul (h_bound_g _) h_f_cauchy (ℚ₀.absVal_nonneg _) (ℚ₀.absVal_nonneg _)
    
  have h_parts_add : Add.add (Mul.mul (ℚ₀.absVal fnK) (ℚ₀.absVal (gnK - gmK))) (Mul.mul (ℚ₀.absVal gmK) (ℚ₀.absVal (fnK - fmK))) ≤ 
    Add.add (Mul.mul f.boundVal (ℚ₀.pow2 (Peano.Lattice.min n m) * ℚ₀.pow2 K)) (Mul.mul g.boundVal (ℚ₀.pow2 (Peano.Lattice.min n m) * ℚ₀.pow2 K)) := by
    exact ℚ₀.add_le_add h_part1 h_part2
    
  exact 1

end ℚ₀
