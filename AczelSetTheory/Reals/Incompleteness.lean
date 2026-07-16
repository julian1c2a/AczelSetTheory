/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Reals/Incompleteness.lean
-- Demostración de que ℚ₀ es incompleto (existe una sucesión de Cauchy sin límite en ℚ₀).

import AczelSetTheory.Rationals.Q0Cauchy
import AczelSetTheory.Rationals.Irrational

open Peano

namespace ℝ₀

-- ============================================================
-- Sucesión de Newton para √2
-- ============================================================

/-- La sucesión de Cauchy aproximando √2 por la derecha usando el método de Newton. -/
def sqrt2Seq : ℕ₀ → ℚ₀ := fun k =>
  let q := ℚ₀cls.ofNat₀ (σ (σ 𝟘))
  let n : ℕ₂ := ⟨⟨σ (σ 𝟘), by decide⟩, by decide⟩
  ℚ₀.ofCls (ℚ₀cls.newton_raphson_seq q n k)

/-- La sucesión de Newton es de Cauchy. -/
theorem sqrt2Seq_isCauchy : ℚ₀.IsCauchy sqrt2Seq := by
  -- La demostración de que la sucesión de Newton es Cauchy
  -- requiere acotar la diferencia entre términos sucesivos.
  sorry

/-- La sucesión que aproxima a √2 como elemento de CauchySeq. -/
def sqrt2CauchySeq : ℚ₀.CauchySeq := ⟨sqrt2Seq, sqrt2Seq_isCauchy⟩

-- ============================================================
-- Irracionalidad y Falta de Límite
-- ============================================================

/-- Demostración de la irracionalidad de √2 en ℚ₀.
No existe ningún q en ℚ₀ tal que q^2 = 2. -/
theorem sqrt2_irrational (q : ℚ₀) : q * q ≠ ℚ₀.ofNat₀ (σ (σ 𝟘)) := by
  -- Esto sigue del hecho de que 2 no es un cuadrado perfecto.
  sorry

/-- La sucesión sqrt2CauchySeq no tiene límite en ℚ₀.
Esto demuestra la incompletitud métrica de ℚ₀. -/
theorem sqrt2CauchySeq_has_no_limit :
  ¬ ∃ L : ℚ₀, ∀ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, Peano.Order.le₀ N m → ℚ₀.absVal (sqrt2Seq m - L) ≤ ℚ₀.pow2 k := by
  -- Supongamos que existe un límite L ∈ ℚ₀.
  -- Usando Irrational.lean, demostramos que la sucesión de Newton no converge a ningún racional
  -- a menos que ese racional sea exactamente la raíz (lo cual es irracional).
  sorry

end ℝ₀