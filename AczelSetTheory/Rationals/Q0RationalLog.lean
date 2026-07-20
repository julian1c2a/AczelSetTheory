/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Q0RationalLog.lean
-- Serie de `artanh` (base de logaritmos racionales) sobre ℚ₀ (ADR-023).
--
-- Migra al struct la teoría de `Rationals/RationalLog.lean` (ℚ₀cls). `oddIdx : ℕ₀ → ℕ₀` es
-- ℕ₀-puro y no se bridgea; se migran `artanhTerm`/`artanhSeq` (defs `ofCls`) y sus lemas de
-- Cauchy. Bridges triviales sobre ℚ₀cls.

import AczelSetTheory.Rationals.Q0Convergence
import AczelSetTheory.Rationals.Q0Roots
import AczelSetTheory.Rationals.RationalLog

namespace ℚ₀

/-- El `j`-ésimo término de la serie de artanh: `u^(2j+1)/(2j+1)`. -/
def artanhTerm (u : ℚ₀) (j : ℕ₀) : ℚ₀ := ofCls (ℚ₀cls.artanhTerm u.cls j)

/-- Sumas parciales de la serie de artanh en `u`. -/
def artanhSeq (u : ℚ₀) : ℕ₀ → ℚ₀ := fun k => ofCls (ℚ₀cls.artanhSeq u.cls k)

@[simp] theorem cls_artanhTerm (u : ℚ₀) (j : ℕ₀) :
    (artanhTerm u j).cls = ℚ₀cls.artanhTerm u.cls j := rfl
@[simp] theorem cls_artanhSeq (u : ℚ₀) (k : ℕ₀) :
    (artanhSeq u k).cls = ℚ₀cls.artanhSeq u.cls k := rfl

-- ── Lemas de potencia diádica auxiliares ──
theorem pow2_zero : pow2 𝟘 = 1 := ext _ _ ℚ₀cls.pow2_zero
theorem pow_pow2_one (m : ℕ₀) : (pow2 𝟙).pow m = pow2 m := ext _ _ (ℚ₀cls.pow_pow2_one m)
theorem pow_absVal_le_pow2 {u : ℚ₀} (hu : absVal u ≤ pow2 𝟙) (m : ℕ₀) :
    (absVal u).pow m ≤ pow2 m := ℚ₀cls.pow_absVal_le_pow2 hu m
theorem ofNat₀_ne_zero {m : ℕ₀} (hm : m ≠ 𝟘) : ofNat₀ m ≠ 0 :=
  ne_zero_iff_cls.mpr (ℚ₀cls.ofNat₀_ne_zero hm)

-- ── La serie de artanh es de Cauchy ──
theorem artanhTerm_bound {u : ℚ₀} (hu : absVal u ≤ pow2 𝟙) (k : ℕ₀) :
    absVal (artanhTerm u (σ k)) ≤ pow2 (σ k) := ℚ₀cls.artanhTerm_bound hu k
theorem artanhSeq_step {u : ℚ₀} (hu : absVal u ≤ pow2 𝟙) (k : ℕ₀) :
    absVal (Sub.sub (artanhSeq u (σ k)) (artanhSeq u k)) ≤ pow2 (σ k) :=
  ℚ₀cls.artanhSeq_step hu k
theorem artanhSeq_isCauchy {u : ℚ₀} (hu : absVal u ≤ pow2 𝟙) : IsCauchy (artanhSeq u) :=
  (isCauchy_iff_q0_isCauchy (artanhSeq u)).mpr (ℚ₀cls.artanhSeq_isCauchy hu)

end ℚ₀
