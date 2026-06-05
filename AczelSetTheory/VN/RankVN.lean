/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/RankVN.lean
-- Rango de los naturales de Von Neumann.
--
-- Público:
--   rank_vN : ∀ n : ℕ₀, rank (vN n) = n
--
-- Consecuencia directa de rank_empty, rank_insert, y not_mem_self.
-- Conecta la función vN : ℕ₀ → HFSet con el rango de Von Neumann.

import AczelSetTheory.VN.IsNat

open Peano VN

namespace VN

/-- El rango del n-ésimo natural de Von Neumann es n. -/
theorem rank_vN (n : ℕ₀) : HFSet.rank (vN n) = n := by
  induction n with
  | zero =>
    rw [vN_zero]
    exact HFSet.rank_empty
  | succ k ih =>
    rw [vN_succ]
    have h_eq : HFSet.succ (vN k) = HFSet.insert (vN k) (vN k) :=
      HFSet.extensionality _ _ fun x => by
        rw [HFSet.mem_succ, HFSet.mem_insert]
        exact or_comm
    rw [h_eq, HFSet.rank_insert (vN k) (vN k) (HFSet.not_mem_self (vN k)), ih]
    rw [max_comm, max_eq_of_lt (lt_succ_self k)]

end VN
