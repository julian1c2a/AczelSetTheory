/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Q0Convergence.lean
-- Teoría de convergencia y propiedad arquimediana sobre el racional empaquetado ℚ₀ (ADR-023).
--
-- Estilo de la casa (como Q0Cauchy): los predicados `IsBounded`/`ConvergesTo`/`IsConvergent`
-- se REDEFINEN nativamente sobre ℚ₀ y se atan a `ℚ₀cls` con un `iff`; los teoremas se
-- transportan a través de esos `iff` + `isCauchy_iff_q0_isCauchy`. Los lemas de `pow2` y la
-- propiedad arquimediana son bridges directos (el orden y las ops del struct = los de `.cls`).

import AczelSetTheory.Rationals.Q0Cauchy
import AczelSetTheory.Rationals.Q0Order
import AczelSetTheory.Rationals.Convergence
import AczelSetTheory.Rationals.Archimedean

namespace ℚ₀

-- ─────────────────────────────────────────────────────────────────────────────
-- Lemas de `pow2` sobre ℚ₀ (bridges directos / ext sobre ℚ₀cls)
-- ─────────────────────────────────────────────────────────────────────────────

@[simp] theorem cls_pow2 (n : ℕ₀) : (pow2 n).cls = ℚ₀cls.pow2 n := rfl

theorem pow2_nonneg (n : ℕ₀) : 0 ≤ pow2 n := ℚ₀cls.pow2_nonneg n
theorem pow2_ne_zero (k : ℕ₀) : pow2 k ≠ 0 := ne_zero_iff_cls.mpr (ℚ₀cls.pow2_ne_zero k)
theorem pow2_succ_add (n : ℕ₀) : Add.add (pow2 (σ n)) (pow2 (σ n)) = pow2 n :=
  ext _ _ (ℚ₀cls.pow2_succ_add n)
theorem pow2_add (n m : ℕ₀) : pow2 (Peano.Add.add n m) = Mul.mul (pow2 n) (pow2 m) :=
  ext _ _ (ℚ₀cls.pow2_add n m)
theorem pow2_le_one (k : ℕ₀) : pow2 k ≤ ofNat₀ 𝟙 := ℚ₀cls.pow2_le_one k
theorem pow2_bound (K : ℕ₀) : Mul.mul (ofNat₀ K) (pow2 K) ≤ ofNat₀ 𝟙 := ℚ₀cls.pow2_bound K
theorem pow2_step (n : ℕ₀) : pow2 (σ n) ≤ pow2 n := ℚ₀cls.pow2_step n
theorem pow2_add_le (a d : ℕ₀) : pow2 (Peano.Add.add a d) ≤ pow2 a := ℚ₀cls.pow2_add_le a d
theorem pow2_le_of_le {a b : ℕ₀} (h : Peano.Order.le₀ a b) : pow2 b ≤ pow2 a :=
  ℚ₀cls.pow2_le_of_le h

-- ─────────────────────────────────────────────────────────────────────────────
-- Predicados de convergencia sobre ℚ₀ + puentes `iff` a ℚ₀cls
-- ─────────────────────────────────────────────────────────────────────────────

/-- `f` está **acotada**: ∃ M, ∀ n, |f n| ≤ M. -/
def IsBounded (f : ℕ₀ → ℚ₀) : Prop := ∃ M : ℚ₀, ∀ n : ℕ₀, absVal (f n) ≤ M

/-- `f` **converge a `L`** a ritmo diádico: |f n − L| ≤ 1/2^(n+1). -/
def ConvergesTo (f : ℕ₀ → ℚ₀) (L : ℚ₀) : Prop :=
  ∀ n : ℕ₀, absVal (Sub.sub (f n) L) ≤ pow2 (σ n)

/-- `f` es **convergente** si converge a algún `L : ℚ₀`. -/
def IsConvergent (f : ℕ₀ → ℚ₀) : Prop := ∃ L : ℚ₀, ConvergesTo f L

theorem isBounded_iff (f : ℕ₀ → ℚ₀) : IsBounded f ↔ ℚ₀cls.IsBounded (toClsSeq f) := by
  constructor
  · rintro ⟨M, hM⟩; exact ⟨M.cls, fun n => hM n⟩
  · rintro ⟨M, hM⟩; exact ⟨ℚ₀.ofCls M, fun n => hM n⟩

theorem convergesTo_iff (f : ℕ₀ → ℚ₀) (L : ℚ₀) :
    ConvergesTo f L ↔ ℚ₀cls.ConvergesTo (toClsSeq f) L.cls := Iff.rfl

theorem isConvergent_iff (f : ℕ₀ → ℚ₀) :
    IsConvergent f ↔ ℚ₀cls.IsConvergent (toClsSeq f) := by
  constructor
  · rintro ⟨L, hL⟩; exact ⟨L.cls, (convergesTo_iff f L).mp hL⟩
  · rintro ⟨L, hL⟩; exact ⟨ℚ₀.ofCls L, (convergesTo_iff f (ℚ₀.ofCls L)).mpr hL⟩

theorem isCauchy₂_iff (f : ℕ₀ → ℚ₀) :
    IsCauchy₂ f ↔ ℚ₀cls.IsCauchy₂ (toClsSeq f) := Iff.rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- Teoremas transportados vía los `iff`
-- ─────────────────────────────────────────────────────────────────────────────

theorem isBounded_of_isCauchy {f : ℕ₀ → ℚ₀} (h : IsCauchy f) : IsBounded f :=
  (isBounded_iff f).mpr (ℚ₀cls.isBounded_of_isCauchy ((isCauchy_iff_q0_isCauchy f).mp h))

theorem isCauchy_of_convergesTo {f : ℕ₀ → ℚ₀} {L : ℚ₀} (h : ConvergesTo f L) : IsCauchy f :=
  (isCauchy_iff_q0_isCauchy f).mpr (ℚ₀cls.isCauchy_of_convergesTo ((convergesTo_iff f L).mp h))

theorem isCauchy₂_of_convergesTo {f : ℕ₀ → ℚ₀} {L : ℚ₀} (h : ConvergesTo f L) : IsCauchy₂ f :=
  (isCauchy₂_iff f).mpr (ℚ₀cls.isCauchy₂_of_convergesTo ((convergesTo_iff f L).mp h))

theorem isCauchy_of_isConvergent {f : ℕ₀ → ℚ₀} (h : IsConvergent f) : IsCauchy f :=
  (isCauchy_iff_q0_isCauchy f).mpr (ℚ₀cls.isCauchy_of_isConvergent ((isConvergent_iff f).mp h))

theorem isBounded_of_convergesTo {f : ℕ₀ → ℚ₀} {L : ℚ₀} (h : ConvergesTo f L) : IsBounded f :=
  (isBounded_iff f).mpr (ℚ₀cls.isBounded_of_convergesTo ((convergesTo_iff f L).mp h))

theorem isBounded_of_isConvergent {f : ℕ₀ → ℚ₀} (h : IsConvergent f) : IsBounded f :=
  (isBounded_iff f).mpr (ℚ₀cls.isBounded_of_isConvergent ((isConvergent_iff f).mp h))

theorem convergesTo_unique {f : ℕ₀ → ℚ₀} {L₁ L₂ : ℚ₀}
    (h1 : ConvergesTo f L₁) (h2 : ConvergesTo f L₂) : L₁ = L₂ :=
  ext L₁ L₂ (ℚ₀cls.convergesTo_unique ((convergesTo_iff f L₁).mp h1) ((convergesTo_iff f L₂).mp h2))

theorem eq_zero_of_le_pow2_all {q : ℚ₀} (hq : 0 ≤ q) (h : ∀ n : ℕ₀, q ≤ pow2 n) : q = 0 :=
  ext q 0 (ℚ₀cls.eq_zero_of_le_pow2_all hq (fun n => h n))

-- ─────────────────────────────────────────────────────────────────────────────
-- Propiedad arquimediana
-- ─────────────────────────────────────────────────────────────────────────────

theorem archimedean (x y : ℚ₀) (hx : 0 < x) : ∃ N : ℕ₀, y < Mul.mul (ofNat₀ N) x :=
  _root_.archimedean x.cls y.cls hx

end ℚ₀
