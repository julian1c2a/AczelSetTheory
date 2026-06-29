/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Reals/CauchySeq.lean
-- Base type for computable numbers: Cauchy sequences over ℚ₀.

import AczelSetTheory.Rationals.IsCauchy
import AczelSetTheory.Rationals.Inv

namespace ℝ₀

/-- El tipo de sucesiones de Cauchy en ℚ₀, base para los números computables. -/
def CauchySeq := { f : ℕ₀ → ℚ₀ // ℚ₀.IsCauchy f }

/-- Relación de equivalencia diádica: f ∼ g si el límite de f - g es 0.
En formato constructivo: ∀ k, ∃ N, ∀ m ≥ N, |f(m) - g(m)| ≤ 1/2^k. -/
def CauchySeq.Equiv (f g : CauchySeq) : Prop :=
  ∀ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, le₀ N m → ℚ₀.absVal (f.val m - g.val m) ≤ ℚ₀.pow2 k

-- Lema auxiliar: pow2 es siempre mayor o igual que 0.
theorem pow2_nonneg (k : ℕ₀) : (0 : ℚ₀) ≤ ℚ₀.pow2 k := by
  exact ℚ₀.pow2_nonneg k

theorem CauchySeq.Equiv_refl (f : CauchySeq) : CauchySeq.Equiv f f := by
  intro k
  exists 𝟘
  intro m _
  have hzero : f.val m - f.val m = 0 := ℚ₀.add_neg_self (f.val m)
  rw [hzero, ℚ₀.absVal_zero]
  exact pow2_nonneg k

theorem CauchySeq.Equiv_symm {f g : CauchySeq} (h : CauchySeq.Equiv f g) : CauchySeq.Equiv g f := by
  intro k
  rcases h k with ⟨N, hN⟩
  exists N
  intro m hm
  have hsym : ℚ₀.absVal (g.val m - f.val m) = ℚ₀.absVal (f.val m - g.val m) := ℚ₀.absVal_sub_comm (g.val m) (f.val m)
  rw [hsym]
  exact hN m hm

-- Para la transitividad f ∼ g ∧ g ∼ h → f ∼ h, necesitaríamos que
-- 1/2^(k+1) + 1/2^(k+1) = 1/2^k, pero esto requerirá teoría adicional sobre pow2.
theorem CauchySeq.Equiv_trans {f g h : CauchySeq} (h1 : CauchySeq.Equiv f g) (h2 : CauchySeq.Equiv g h) : CauchySeq.Equiv f h := by
  sorry

end ℝ₀
