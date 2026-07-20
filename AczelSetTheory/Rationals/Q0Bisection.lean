/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Q0Bisection.lean
-- Método de bisección diádica sobre ℚ₀ (ADR-023).
--
-- Migra `Rationals/Bisection.lean` (ℚ₀cls). `isCauchy_of_dyadic_step` es un bridge limpio.
-- `bisectSeq` se define vía `ofCls` de la versión de la clase (adaptando el decisor con la
-- coerción); esto da `bisectSeq_isCauchy` gratis, pero NO expone la recurrencia `bisectSeq_succ`
-- (su condición `bif` depende del decisor aplicado al tipo, que no atraviesa `ofCls` por `rfl`).
-- Un consumidor que necesite calcular la recurrencia debe usar `ℚ₀cls.bisectSeq`.

import AczelSetTheory.Rationals.Q0Convergence
import AczelSetTheory.Rationals.Bisection

namespace ℚ₀

/-- Toda sucesión con pasos diádicos decrecientes `|f(σk) − f k| ≤ 2⁻⁽ᵏ⁺¹⁾` es de Cauchy. -/
theorem isCauchy_of_dyadic_step {f : ℕ₀ → ℚ₀}
    (h : ∀ k : ℕ₀, absVal (Sub.sub (f (σ k)) (f k)) ≤ pow2 (σ k)) : IsCauchy f :=
  (isCauchy_iff_q0_isCauchy f).mpr (ℚ₀cls.isCauchy_of_dyadic_step (fun k => h k))

/-- Bisección diádica dinámica dirigida por el decisor `g`. Definida sobre la clase (el decisor
    se adapta con `ofCls`); es de Cauchy por construcción. -/
def bisectSeq (g : ℕ₀ → ℚ₀ → Bool) (a₀ : ℚ₀) : ℕ₀ → ℚ₀ :=
  fun k => ofCls (ℚ₀cls.bisectSeq (fun n q => g n (ofCls q)) a₀.cls k)

@[simp] theorem cls_bisectSeq (g : ℕ₀ → ℚ₀ → Bool) (a₀ : ℚ₀) (k : ℕ₀) :
    (bisectSeq g a₀ k).cls = ℚ₀cls.bisectSeq (fun n q => g n (ofCls q)) a₀.cls k := rfl

theorem bisectSeq_isCauchy (g : ℕ₀ → ℚ₀ → Bool) (a₀ : ℚ₀) : IsCauchy (bisectSeq g a₀) :=
  (isCauchy_iff_q0_isCauchy (bisectSeq g a₀)).mpr
    (ℚ₀cls.bisectSeq_isCauchy (fun n q => g n (ofCls q)) a₀.cls)

end ℚ₀
