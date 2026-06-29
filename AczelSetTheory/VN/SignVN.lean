/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/SignVN.lean
--
-- Signatura de permutaciones sobre el embedding de Von Neumann.
--

import AczelSetTheory.VN.SymGroupVN
import Peano.PeanoNat.Combinatorics.Sign
import AczelSetTheory.Integers.Basic

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace Sign

      noncomputable section
      open Classical

      /-- Inversiones de una permutación `f` sobre `vN n`.
          Son los pares ordenados `(x, y)` donde `x ∈ y` (`x < y`) pero `f(y) ∈ f(x)` (`f(y) < f(x)`). -/
      def inversions (n : ℕ₀) (f : HFSet) : HFSet :=
        have : DecidablePred (fun (p : HFSet) => ∃ x ∈ VN.vN n, ∃ y ∈ VN.vN n,
          p = HFSet.orderedPair x y ∧ x ∈ y ∧ (HFSet.apply f y) ∈ (HFSet.apply f x)) := fun _ => propDecidable _
        HFSet.sep (HFSet.cartProd (VN.vN n) (VN.vN n))
          (fun (p : HFSet) => ∃ x ∈ VN.vN n, ∃ y ∈ VN.vN n,
            p = HFSet.orderedPair x y ∧ x ∈ y ∧ (HFSet.apply f y) ∈ (HFSet.apply f x))

      /-- La signatura devuelve `1` si el número de inversiones es par, y `-1` si es impar. -/
      def sign (n : ℕ₀) (f : HFSet) : ℤ₀ :=
        let invs := inversions n f
        let c := HFSet.card invs
        have is_even : Prop := ∃ k : ℕ₀, c = Peano.Add.add k k
        if is_even then (1 : ℤ₀) else ℤ₀.negOne

      end

    end Sign
  end VN
end AczelSetTheory
