import Peano.PeanoNat.Div
open Peano Peano.Div

theorem div_one (a : ℕ₀) : a / 𝟙 = a := by
  change div a 𝟙 = a
  unfold div divMod
  split
  · contradiction
  · split
    · rw [‹a = 𝟘›]
    · split
      · rfl
      · contradiction
