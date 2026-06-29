import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Integers.Functions

namespace ℚ₀

open Peano Peano.Axioms Peano.Add Peano.Mul Peano.Order

private def absNat (z : ℤ₀) : ℕ₀ := ℤ₀.toNat (ℤ₀.abs z)

noncomputable section

open Classical

private noncomputable def invDen (z : ℤ₀) : ℕ₁ :=
  if h : z = 0 then ⟨𝟙, succ_neq_zero 𝟘⟩
  else ⟨absNat z, sorry⟩

private noncomputable def invRaw (p : ℤ₀ × ℕ₁) : ℤ₀ × ℕ₁ :=
  if p.1 = 0 then (0, ⟨𝟙, succ_neq_zero 𝟘⟩)
  else if 0 ≤ p.1 then (ℤ₀.ofNat p.2.val, invDen p.1)
  else (- ℤ₀.ofNat p.2.val, invDen p.1)

private theorem invWD (p q : ℤ₀ × ℕ₁) (h : Mul.mul p.1 (ℤ₀.ofNat q.2.val) = Mul.mul q.1 (ℤ₀.ofNat p.2.val)) :
    Mul.mul (invRaw p).1 (ℤ₀.ofNat (invRaw q).2.val) = Mul.mul (invRaw q).1 (ℤ₀.ofNat (invRaw p).2.val) := by
  sorry

def inv (a : ℚ₀) : ℚ₀ := Quotient.liftOn a
  (fun p => mk (invRaw p).1 (invRaw p).2)
  (fun p q h => Quotient.sound (invWD p q h))

instance : Inv ℚ₀ := ⟨inv⟩

instance : Div ℚ₀ := ⟨fun a b => a * b⁻¹⟩

end

end ℚ₀
