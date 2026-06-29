/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Reals/Arithmetic.lean
-- Operaciones aritméticas sobre sucesiones de Cauchy en ℚ₀.

import AczelSetTheory.Reals.CauchySeq

namespace ℝ₀

-- ============================================================
-- Suma, Resta y Negación (Término a Término)
-- ============================================================

/-- Suma de sucesiones de Cauchy. -/
def CauchySeq.add (f g : CauchySeq) : CauchySeq :=
  ⟨fun n => f.val n + g.val n, by
    -- Demostrar que f+g es de Cauchy requiere la desigualdad triangular
    -- y que (1/2^(k+1)) + (1/2^(k+1)) = 1/2^k.
    sorry⟩

instance : Add CauchySeq := ⟨CauchySeq.add⟩

/-- Negación de una sucesión de Cauchy. -/
def CauchySeq.neg (f : CauchySeq) : CauchySeq :=
  ⟨fun n => - (f.val n), by
    -- |-f(n) - (-f(m))| = |f(m) - f(n)| = |f(n) - f(m)| ≤ 1/2^k
    sorry⟩

instance : Neg CauchySeq := ⟨CauchySeq.neg⟩

/-- Resta de sucesiones de Cauchy. -/
def CauchySeq.sub (f g : CauchySeq) : CauchySeq :=
  f + (-g)

instance : Sub CauchySeq := ⟨CauchySeq.sub⟩

-- ============================================================
-- Acotación (Boundedness)
-- ============================================================

/-- Una sucesión f en ℚ₀ está acotada si existe M tal que ∀ n, |f(n)| ≤ M. -/
def CauchySeq.IsBounded (f : CauchySeq) : Prop :=
  ∃ M : ℚ₀, ∀ n : ℕ₀, ℚ₀.absVal (f.val n) ≤ M

theorem CauchySeq.isBounded_of_isCauchy (f : CauchySeq) : CauchySeq.IsBounded f := by
  -- Toda sucesión de Cauchy es acotada. Se toma N para ε=1 y M = max(|f(0)|, ..., |f(N)|) + 1.
  sorry

-- ============================================================
-- Multiplicación (Término a Término)
-- ============================================================

/-- Multiplicación de sucesiones de Cauchy. -/
def CauchySeq.mul (f g : CauchySeq) : CauchySeq :=
  ⟨fun n => f.val n * g.val n, by
    -- Usando que f y g están acotadas (|f| ≤ M_f, |g| ≤ M_g),
    -- |f(n)g(n) - f(m)g(m)| ≤ |f(n)||g(n) - g(m)| + |g(m)||f(n) - f(m)|
    --                       ≤ M_f * 1/2^k + M_g * 1/2^k.
    -- Ajustando el k según M_f y M_g obtenemos la cota deseada.
    sorry⟩

instance : Mul CauchySeq := ⟨CauchySeq.mul⟩

end ℝ₀
