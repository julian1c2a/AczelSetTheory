import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.Bijection
import AczelSetTheory.Integers.Order
import AczelSetTheory.Integers.HFInt

open Peano Peano.Add Peano.Sub Peano.Mul

theorem ofNat_sub_ofNat_mk (a b : N0) : Sub.sub (Z0.ofNat a) (Z0.ofNat b) = Z0.mk (a, b) := by
  show Z0.mk (addRaw (a, ??) (negRaw (b, ??))) = Z0.mk (a, b)
  rw [Z0.mk_eq_iff]
  unfold Z0.intEq Z0.addRaw Z0.negRaw
  omega0

theorem repr_mk_normalized (p : N0 × N0) (h : p.1 = ?? ? p.2 = ??) : (Z0.mk p).repr = p := by
  -- Z0.mk_repr says Z0.mk z.repr = z. But we need (Z0.mk p).repr = p.
  -- Wait, Z0.repr (Z0.mk p) is Z0.normalize p.
  -- Is 
ormalize public? Let's check.
  sorry

