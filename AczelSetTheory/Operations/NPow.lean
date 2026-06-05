/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Operations/NPow.lean
-- Potencia cartesiana n-aria de un conjunto finito hereditario.
--
-- nPow A n  es el conjunto de n-tuplas de elementos de A,
-- codificadas como listas anidadas mediante el producto cartesiano.
--
-- Públicos:
--   nPow       : HFSet → ℕ₀ → HFSet
--   nPow_zero  : nPow A 𝟘 = singleton empty
--   nPow_succ  : nPow A (σ n) = nPow A n ×ₕ A

import AczelSetTheory.Operations.CartProd
import AczelSetTheory.Notation
import Peano.PeanoNat.Combinatorics.Pow

open Peano

namespace HFSet

/-- Potencia cartesiana n-aria:
    - `nPow A 0 = {∅}`         (el conjunto con solo la "tupla vacía")
    - `nPow A (n+1) = nPow A n ×ₕ A` -/
def nPow (A : HFSet) : ℕ₀ → HFSet
  | .zero   => singleton empty
  | .succ n => nPow A n ×ₕ A

@[simp]
theorem nPow_zero (A : HFSet) : nPow A 𝟘 = singleton empty := rfl

@[simp]
theorem nPow_succ (A : HFSet) (n : ℕ₀) : nPow A (σ n) = nPow A n ×ₕ A := rfl

end HFSet
