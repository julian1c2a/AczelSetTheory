-- BezoutDebug.lean: diagnóstico mínimo
import AczelSetTheory.Integers.Basic
-- import AczelSetTheory.Integers.Arithmetic
-- import AczelSetTheory.Integers.Order
-- import Peano.PeanoNat.Arith

namespace ℤ₀

theorem test1 (a b : ℤ₀) : ∃ x y : ℤ₀, a * x + b * y = 0 := ⟨0, 0, by simp⟩

end ℤ₀
