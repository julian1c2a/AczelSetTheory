/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Reals/RealAxioms.lean

import AczelSetTheory.Reals.CauchySeq

namespace AczelSetTheory.RealAxioms

/--
  Axioma temporal para aislar la demostración de que el producto de
  sucesiones de Cauchy (adecuadamente desplazadas) es Cauchy.
  Requiere formalizar propiedades sobre valores absolutos y desigualdades en ℚ₀.
-/
axiom cauchy_mul_is_cauchy (f g : ℝ₀.CauchySeq) (K : ℕ₀) :
    ℚ₀.IsCauchy (fun n => f.val (Peano.Add.add n K) * g.val (Peano.Add.add n K))

/--
  Axioma temporal para aislar la demostración de que el inverso de una
  sucesión de Cauchy alejada de cero es también una sucesión de Cauchy.
  La condición h expresa que f está alejada de cero (Pos f ∨ Pos (-f)).
-/
axiom cauchy_inv_is_cauchy (f : ℝ₀.CauchySeq)
    (h : (∃ k N : ℕ₀, ∀ m : ℕ₀, Peano.Order.le₀ N m → ℚ₀.pow2 k ≤ f.val m) ∨
         (∃ k N : ℕ₀, ∀ m : ℕ₀, Peano.Order.le₀ N m → ℚ₀.pow2 k ≤ Neg.neg (f.val m))) :
    ℚ₀.IsCauchy (fun n => (f.val n)⁻¹)

end AczelSetTheory.RealAxioms
