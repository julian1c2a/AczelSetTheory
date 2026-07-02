import AczelSetTheory.Reals.CauchySeq

namespace ℝ₀

theorem ℚ₀.add_le_add {a b c d : ℚ₀} (h1 : a ≤ c) (h2 : b ≤ d) : Add.add a b ≤ Add.add c d := by
  have h3 := ℚ₀.add_le_add_left h1 b
  have h4 := ℚ₀.add_le_add_right h2 c
  exact ℚ₀.le_trans h3 h4

theorem ℚ₀.sub_add_sub_cancel (a b c : ℚ₀) : Add.add (Sub.sub a b) (Sub.sub b c) = Sub.sub a c := by
  have h1 : Sub.sub a b = Add.add a (Neg.neg b) := rfl
  have h2 : Sub.sub b c = Add.add b (Neg.neg c) := rfl
  have h3 : Sub.sub a c = Add.add a (Neg.neg c) := rfl
  rw [h1, h2, h3]
  rw [ℚ₀.add_assoc]
  have h4 : Add.add (Neg.neg b) (Add.add b (Neg.neg c)) = Add.add (Add.add (Neg.neg b) b) (Neg.neg c) := (ℚ₀.add_assoc (Neg.neg b) b (Neg.neg c)).symm
  rw [h4]
  have h5 : Add.add (Neg.neg b) b = 0 := ℚ₀.neg_add_self b
  rw [h5]
  have h6 : Add.add 0 (Neg.neg c) = Neg.neg c := ℚ₀.zero_add (Neg.neg c)
  rw [h6]
  rfl

theorem CauchySeq.Equiv_trans_proof {f g h : CauchySeq} (h1 : CauchySeq.Equiv f g) (h2 : CauchySeq.Equiv g h) : CauchySeq.Equiv f h := by
  intro k
  rcases h1 (σ k) with ⟨N1, hN1⟩
  rcases h2 (σ k) with ⟨N2, hN2⟩
  exists Peano.Lattice.max N1 N2
  intro m hm
  have hN1_le : le₀ N1 m := Peano.Order.le_trans N1 (Peano.Lattice.max N1 N2) m (Peano.Lattice.le_max_left N1 N2) hm
  have hN2_le : le₀ N2 m := Peano.Order.le_trans N2 (Peano.Lattice.max N1 N2) m (Peano.Lattice.le_max_right N1 N2) hm
  have h_bound1 := hN1 m hN1_le
  have h_bound2 := hN2 m hN2_le
  
  have h_sub : Sub.sub (f.val m) (h.val m) = Add.add (Sub.sub (f.val m) (g.val m)) (Sub.sub (g.val m) (h.val m)) := by
    exact (ℚ₀.sub_add_sub_cancel (f.val m) (g.val m) (h.val m)).symm
  
  rw [h_sub]
  have h_tri := ℚ₀.absVal_add_le (Sub.sub (f.val m) (g.val m)) (Sub.sub (g.val m) (h.val m))
  have h_add_le := ℚ₀.add_le_add h_bound1 h_bound2
  have h_trans := ℚ₀.le_trans h_tri h_add_le
  have h_pow_add := ℚ₀.pow2_succ_add k
  
  -- now h_trans is: absVal (...) ≤ pow2 (σ k) + pow2 (σ k)
  -- we want it to be ≤ pow2 k
  rw [h_pow_add] at h_trans
  exact h_trans

end ℝ₀
