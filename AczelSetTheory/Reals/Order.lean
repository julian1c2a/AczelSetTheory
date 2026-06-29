/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Reals/Order.lean
-- Relación de orden para sucesiones de Cauchy.

import AczelSetTheory.Reals.CauchySeq
import AczelSetTheory.Reals.Arithmetic

namespace ℝ₀

-- ============================================================
-- Propiedad Positiva y Orden
-- ============================================================

/-- Una sucesión f es estrictamente positiva si existe k y N tal que
f(m) ≥ 1/2^k para todo m ≥ N. -/
def CauchySeq.Pos (f : CauchySeq) : Prop :=
  ∃ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, le₀ N m → ℚ₀.pow2 k ≤ f.val m

/-- Relación de orden estricto f < g ↔ Pos (g - f). -/
def CauchySeq.LT (f g : CauchySeq) : Prop :=
  CauchySeq.Pos (g - f)

instance : LT CauchySeq := ⟨CauchySeq.LT⟩

/-- Relación de orden parcial f ≤ g ↔ ¬(g < f). -/
def CauchySeq.LE (f g : CauchySeq) : Prop :=
  ¬ (g < f)

instance : LE CauchySeq := ⟨CauchySeq.LE⟩

-- ============================================================
-- Inverso (División)
-- ============================================================

/-- El inverso de una sucesión de Cauchy está definido si la sucesión
está estrictamente alejada de cero (Pos f ∨ Pos (-f)). -/
noncomputable def CauchySeq.inv (f : CauchySeq) (h : CauchySeq.Pos f ∨ CauchySeq.Pos (-f)) : CauchySeq :=
  ⟨fun n => (f.val n)⁻¹, by
    -- Demostrar que el inverso de una sucesión alejada de 0 es de Cauchy.
    -- Dado que f está alejada de 0, |f(n)| >= 1/2^k para n >= N.
    sorry⟩

/-- División de sucesiones de Cauchy. f / g = f * g⁻¹ -/
noncomputable def CauchySeq.div (f g : CauchySeq) (h : CauchySeq.Pos g ∨ CauchySeq.Pos (-g)) : CauchySeq :=
  f * CauchySeq.inv g h

end ℝ₀
