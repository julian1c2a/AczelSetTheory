import AczelSetTheory.Rationals.IsCauchy

namespace ℚ₀

theorem pow2_nonneg (n : ℕ₀) : (0 : ℚ₀) ≤ pow2 n := by
  dsimp [pow2]
  rw [zero_le_iff_num_nonneg (ℤ₀.ofNat (σ 𝟘), ⟨Peano.Pow.pow (σ (σ 𝟘)) n, Peano.Pow.pow_ne_zero (by decide) n⟩)]
  exact ℤ₀.zero_le_ofNat _

end ℚ₀
