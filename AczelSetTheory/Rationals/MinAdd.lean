/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.Basic

namespace Peano
namespace Arith

theorem min_add_add_right (n m k : ℕ₀) : Lattice.min (Add.add n k) (Add.add m k) = Add.add (Lattice.min n m) k := by
  cases Order.le_total n m with
  | inl hnm =>
    have h_n_le_m : Order.le₀ n m := hnm
    have h_nk_le_mk : Order.le₀ (Add.add n k) (Add.add m k) := by
      rw [Add.add_comm n k, Add.add_comm m k]
      exact add_le_add_left n m k h_n_le_m
    have h_min1 : Lattice.min (Add.add n k) (Add.add m k) = Add.add n k := Lattice.le_then_min_eq_left _ _ h_nk_le_mk
    have h_min2 : Lattice.min n m = n := Lattice.le_then_min_eq_left _ _ h_n_le_m
    rw [h_min1, h_min2]
  | inr hmn =>
    have h_m_le_n : Order.le₀ m n := hmn
    have h_mk_le_nk : Order.le₀ (Add.add m k) (Add.add n k) := by
      rw [Add.add_comm m k, Add.add_comm n k]
      exact add_le_add_left m n k h_m_le_n
    have h_min1 : Lattice.min (Add.add n k) (Add.add m k) = Add.add m k := by
      rw [Lattice.min_comm]
      exact Lattice.le_then_min_eq_left _ _ h_mk_le_nk
    have h_min2 : Lattice.min n m = m := by
      rw [Lattice.min_comm]
      exact Lattice.le_then_min_eq_left _ _ h_m_le_n
    rw [h_min1, h_min2]

theorem min_add_add_left (k n m : ℕ₀) : Lattice.min (Add.add k n) (Add.add k m) = Add.add k (Lattice.min n m) := by
  rw [Add.add_comm k n, Add.add_comm k m, Add.add_comm k (Lattice.min n m)]
  exact min_add_add_right n m k

end Arith
end Peano
