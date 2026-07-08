import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Canonical
import AczelSetTheory.Integers.HFInt
import AczelSetTheory.Rationals.HFRat
open Peano Peano.Arith

namespace Temp

theorem ofQ0_toQ0 (p : ℚ₀') : ℚ₀'.ofQ0 (ℚ₀'.toQ0 p) = p := by
  unfold ℚ₀'.ofQ0 ℚ₀'.toQ0
  have hr : ℚ₀.repr (ℚ₀.mk p.val.1.cls p.val.2) = (p.val.1.cls, p.val.2) := by
    rw [ℚ₀.mk_repr] -- wait, mk_repr is mk (repr r) = r.
    -- repr (mk n d) = reduce (n, d)
    sorry
  sorry

end Temp
