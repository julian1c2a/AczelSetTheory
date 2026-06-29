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
def CauchySeq.inv (f : CauchySeq) (h : CauchySeq.Pos f ∨ CauchySeq.Pos (-f)) : CauchySeq :=
  ⟨fun n => if ℚ₀.absVal (f.val n) ≤ 0 then 0 else (sorry : ℚ₀), by
    -- Demostrar que el inverso de una sucesión alejada de 0 es de Cauchy.
    -- Se usaría la cota inferior estricta para acotar el denominador.
    sorry⟩

end ℝ₀
