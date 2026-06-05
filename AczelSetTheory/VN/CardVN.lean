/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/CardVN.lean
-- Cardinalidad de los naturales de Von Neumann.
--
-- Público:
--   card_vN : ∀ n : ℕ₀, card (vN n) = n
--
-- Consecuencia directa de card_empty, card_insert, y not_mem_self.
-- Conecta la función vN : ℕ₀ → HFSet con la cardinalidad de HFSet.

import AczelSetTheory.VN.IsNat

open Peano VN

namespace VN

/-- La cardinalidad del n-ésimo natural de Von Neumann es n. -/
theorem card_vN (n : ℕ₀) : HFSet.card (vN n) = n := by
  induction n with
  | zero =>
    rw [vN_zero]
    exact HFSet.card_empty
  | succ k ih =>
    rw [vN_succ]
    -- succ(vN k) = insert(vN k)(vN k) como HFSets
    have h_eq : HFSet.succ (vN k) = HFSet.insert (vN k) (vN k) :=
      HFSet.extensionality _ _ fun x => by
        rw [HFSet.mem_succ, HFSet.mem_insert]
        exact or_comm
    rw [h_eq,
        HFSet.card_insert (vN k) (vN k) (HFSet.not_mem_self (vN k)),
        ih]

end VN
