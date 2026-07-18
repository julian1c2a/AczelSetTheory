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
import Peano.PeanoNat.Arith
import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.Z0

set_option autoImplicit false

namespace AczelSetTheory
  namespace VN
    namespace Sign



      /-- Inversiones de una permutación `f` sobre `vN n`.
          Son los pares ordenados `(x, y)` donde `x ∈ y` (`x < y`) pero `f(y) ∈ f(x)` (`f(y) < f(x)`). -/
      def inversions (n : ℕ₀) (f : HFSet) : HFSet :=
        HFSet.sep (HFSet.cartProd (VN.vN n) (VN.vN n))
          (fun (p : HFSet) => ∃ x ∈ VN.vN n, ∃ y ∈ VN.vN n,
            p = HFSet.orderedPair x y ∧ x ∈ y ∧ (HFSet.apply f y) ∈ (HFSet.apply f x))

      /-- La signatura devuelve `1` si el número de inversiones es par, y `-1` si es impar.
          Devuelve el entero empaquetado `ℤ₀` (migración de tipos ADR-023); se apoya en la
          teoría de `ℤ₀cls` vía la coerción `ℤ₀ → ℤ₀cls`. -/
      def sign (n : ℕ₀) (f : HFSet) : ℤ₀ :=
        let invs := inversions n f
        let c := HFSet.card invs
        if Peano.Arith.IsEven c then (1 : ℤ₀) else ℤ₀.negOne

    end Sign
  end VN
end AczelSetTheory
