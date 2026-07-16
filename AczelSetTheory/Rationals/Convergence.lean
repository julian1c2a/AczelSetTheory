/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Convergence.lean
-- Sucesiones acotadas y convergentes en ℚ₀cls, y las implicaciones básicas:
--   Cauchy      ⟹ acotada (con cota explícita 1 + |f 0|)
--   convergente ⟹ Cauchy
--   convergente ⟹ acotada (con cota explícita 1 + |L|)
--
-- La convergencia se formula con **tasa diádica fija**: `|f n - L| ≤ 1/2^(n+1)`,
-- coherente con el estilo de `IsCauchy` (tasa `1/2^(min n m)`). Con esta tasa,
-- convergente ⟹ Cauchy aterriza EXACTAMENTE en `IsCauchy` vía `pow2_succ_add`.
--
-- API:
--   pow2_step       : pow2 (σ n) ≤ pow2 n
--   pow2_add_le     : pow2 (a + d) ≤ pow2 a
--   pow2_le_of_le   : a ≤ b → pow2 b ≤ pow2 a          (antítona)
--   IsBounded       : (ℕ₀ → ℚ₀cls) → Prop
--   ConvergesTo     : (ℕ₀ → ℚ₀cls) → ℚ₀cls → Prop
--   IsConvergent    : (ℕ₀ → ℚ₀cls) → Prop
--   isBounded_of_isCauchy
--   isCauchy₂_of_convergesTo / isCauchy_of_convergesTo / isCauchy_of_isConvergent
--   isBounded_of_convergesTo / isBounded_of_isConvergent
--
-- Dependencies: AczelSetTheory.Rationals.IsCauchy
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Rationals.IsCauchy
import AczelSetTheory.PList.Omega0

namespace ℚ₀cls

-- ============================================================
-- Sección 1: Monotonía (antítona) de pow2
-- ============================================================

/-- `1/2^(n+1) ≤ 1/2^n`. -/
theorem pow2_step (n : ℕ₀) : pow2 (σ n) ≤ pow2 n :=
  calc pow2 (σ n)
      = Add.add (pow2 (σ n)) 0 := (add_zero (pow2 (σ n))).symm
    _ ≤ Add.add (pow2 (σ n)) (pow2 (σ n)) :=
          add_le_add_left (pow2_nonneg (σ n)) (pow2 (σ n))
    _ = pow2 n := pow2_succ_add n

/-- `1/2^(a+d) ≤ 1/2^a`. -/
theorem pow2_add_le (a d : ℕ₀) : pow2 (Peano.Add.add a d) ≤ pow2 a := by
  induction d with
  | zero => rw [Peano.Add.add_zero]; exact le_refl _
  | succ d' ih =>
    rw [Peano.Add.add_succ]
    exact le_trans (pow2_step (Peano.Add.add a d')) ih

/-- `pow2` es antítona: `a ≤ b → 1/2^b ≤ 1/2^a`. -/
theorem pow2_le_of_le {a b : ℕ₀} (h : Peano.Order.le₀ a b) : pow2 b ≤ pow2 a := by
  have hk := Peano.Sub.sub_k_add_k b a h
  have hb : pow2 b = pow2 (Peano.Add.add a (Peano.Sub.sub b a)) := by
    rw [Peano.Add.add_comm a (Peano.Sub.sub b a), hk]
  rw [hb]
  exact pow2_add_le a (Peano.Sub.sub b a)

-- ============================================================
-- Sección 2: Definiciones
-- ============================================================

/-- Una sucesión `f : ℕ₀ → ℚ₀cls` está **acotada** si existe `M` con `|f n| ≤ M` ∀n. -/
def IsBounded (f : ℕ₀ → ℚ₀cls) : Prop :=
  ∃ M : ℚ₀cls, ∀ n : ℕ₀, absVal (f n) ≤ M

/-- `f` **converge a `L`** a ritmo diádico fijo: `|f n - L| ≤ 1/2^(n+1)`. -/
def ConvergesTo (f : ℕ₀ → ℚ₀cls) (L : ℚ₀cls) : Prop :=
  ∀ n : ℕ₀, absVal (f n - L) ≤ pow2 (σ n)

/-- `f` es **convergente** si converge a algún límite `L : ℚ₀cls`. -/
def IsConvergent (f : ℕ₀ → ℚ₀cls) : Prop :=
  ∃ L : ℚ₀cls, ConvergesTo f L

-- ============================================================
-- Sección 3: Cauchy ⟹ acotada (cota explícita 1 + |f 0|)
-- ============================================================

theorem isBounded_of_isCauchy {f : ℕ₀ → ℚ₀cls} (h : IsCauchy f) : IsBounded f := by
  refine ⟨Add.add (pow2 𝟘) (absVal (f 𝟘)), fun n => ?_⟩
  have hc := h n 𝟘
  have hmin : Peano.Lattice.min n 𝟘 = 𝟘 := Peano.Lattice.min_0_abs n
  rw [hmin] at hc
  have h_eq : f n = Add.add (Add.add (f n) (Neg.neg (f 𝟘))) (f 𝟘) := by
    calc f n
        = Add.add (f n) 0 := (add_zero (f n)).symm
      _ = Add.add (f n) (Add.add (Neg.neg (f 𝟘)) (f 𝟘)) := by rw [neg_add_self (f 𝟘)]
      _ = Add.add (Add.add (f n) (Neg.neg (f 𝟘))) (f 𝟘) := by
            rw [add_assoc (f n) (Neg.neg (f 𝟘)) (f 𝟘)]
  have h_abs_eq : absVal (f n)
      = absVal (Add.add (Add.add (f n) (Neg.neg (f 𝟘))) (f 𝟘)) := congrArg absVal h_eq
  rw [h_abs_eq]
  have h_tri := absVal_add_le (Add.add (f n) (Neg.neg (f 𝟘))) (f 𝟘)
  have h_add_le : Add.add (absVal (Add.add (f n) (Neg.neg (f 𝟘)))) (absVal (f 𝟘))
      ≤ Add.add (pow2 𝟘) (absVal (f 𝟘)) := add_le_add_right hc (absVal (f 𝟘))
  exact le_trans h_tri h_add_le

-- ============================================================
-- Sección 4: convergente ⟹ Cauchy
-- ============================================================

theorem isCauchy₂_of_convergesTo {f : ℕ₀ → ℚ₀cls} {L : ℚ₀cls} (h : ConvergesTo f L) :
    IsCauchy₂ f := by
  intro n m hnm
  have hbm : absVal (Add.add (f m) (Neg.neg L)) ≤ pow2 (σ m) := h m
  have hbn : absVal (Add.add (f n) (Neg.neg L)) ≤ pow2 (σ n) := h n
  have h_eq : Add.add (f m) (Neg.neg (f n))
      = Add.add (Add.add (f m) (Neg.neg L)) (Add.add L (Neg.neg (f n))) := by
    calc Add.add (f m) (Neg.neg (f n))
        = Add.add (f m) (Add.add 0 (Neg.neg (f n))) := by rw [zero_add (Neg.neg (f n))]
      _ = Add.add (f m) (Add.add (Add.add (Neg.neg L) L) (Neg.neg (f n))) := by
            rw [neg_add_self L]
      _ = Add.add (f m) (Add.add (Neg.neg L) (Add.add L (Neg.neg (f n)))) := by
            rw [add_assoc (Neg.neg L) L (Neg.neg (f n))]
      _ = Add.add (Add.add (f m) (Neg.neg L)) (Add.add L (Neg.neg (f n))) := by
            rw [add_assoc (f m) (Neg.neg L) (Add.add L (Neg.neg (f n)))]
  have h_tri : absVal (Add.add (f m) (Neg.neg (f n)))
      ≤ Add.add (absVal (Add.add (f m) (Neg.neg L)))
                (absVal (Add.add L (Neg.neg (f n)))) := by
    rw [h_eq]
    exact absVal_add_le (Add.add (f m) (Neg.neg L)) (Add.add L (Neg.neg (f n)))
  have h_swap : absVal (Add.add L (Neg.neg (f n)))
      = absVal (Add.add (f n) (Neg.neg L)) := absVal_sub_comm L (f n)
  have hbn' : absVal (Add.add L (Neg.neg (f n))) ≤ pow2 (σ n) := by rw [h_swap]; exact hbn
  have hpm : pow2 (σ m) ≤ pow2 (σ n) := pow2_le_of_le (Peano.Order.succ_le_succ_if hnm)
  have step1 : Add.add (absVal (Add.add (f m) (Neg.neg L)))
                       (absVal (Add.add L (Neg.neg (f n))))
      ≤ Add.add (pow2 (σ n)) (pow2 (σ n)) := by
    have ha := add_le_add_right hbm (absVal (Add.add L (Neg.neg (f n))))
    have hb1 := add_le_add_right hpm (absVal (Add.add L (Neg.neg (f n))))
    have hb2 := add_le_add_left hbn' (pow2 (σ n))
    exact le_trans ha (le_trans hb1 hb2)
  have h_final := le_trans h_tri step1
  rw [pow2_succ_add n] at h_final
  exact h_final

theorem isCauchy_of_convergesTo {f : ℕ₀ → ℚ₀cls} {L : ℚ₀cls} (h : ConvergesTo f L) :
    IsCauchy f :=
  (isCauchy_iff_isCauchy₂ f).mpr (isCauchy₂_of_convergesTo h)

theorem isCauchy_of_isConvergent {f : ℕ₀ → ℚ₀cls} (h : IsConvergent f) : IsCauchy f := by
  obtain ⟨L, hL⟩ := h
  exact isCauchy_of_convergesTo hL

-- ============================================================
-- Sección 5: convergente ⟹ acotada (cota explícita 1 + |L|)
-- ============================================================

theorem isBounded_of_convergesTo {f : ℕ₀ → ℚ₀cls} {L : ℚ₀cls} (h : ConvergesTo f L) :
    IsBounded f := by
  refine ⟨Add.add (pow2 𝟘) (absVal L), fun n => ?_⟩
  have hn : absVal (Add.add (f n) (Neg.neg L)) ≤ pow2 (σ n) := h n
  have h_eq : f n = Add.add (Add.add (f n) (Neg.neg L)) L := by
    calc f n
        = Add.add (f n) 0 := (add_zero (f n)).symm
      _ = Add.add (f n) (Add.add (Neg.neg L) L) := by rw [neg_add_self L]
      _ = Add.add (Add.add (f n) (Neg.neg L)) L := by rw [add_assoc (f n) (Neg.neg L) L]
  have h_abs_eq : absVal (f n)
      = absVal (Add.add (Add.add (f n) (Neg.neg L)) L) := congrArg absVal h_eq
  rw [h_abs_eq]
  have h_tri := absVal_add_le (Add.add (f n) (Neg.neg L)) L
  have h_step1 : Add.add (absVal (Add.add (f n) (Neg.neg L))) (absVal L)
      ≤ Add.add (pow2 (σ n)) (absVal L) := add_le_add_right hn (absVal L)
  have h_step2 : Add.add (pow2 (σ n)) (absVal L)
      ≤ Add.add (pow2 𝟘) (absVal L) :=
    add_le_add_right (pow2_le_of_le (Peano.Order.zero_le (σ n))) (absVal L)
  exact le_trans h_tri (le_trans h_step1 h_step2)

theorem isBounded_of_isConvergent {f : ℕ₀ → ℚ₀cls} (h : IsConvergent f) : IsBounded f := by
  obtain ⟨L, hL⟩ := h
  exact isBounded_of_convergesTo hL

-- ============================================================
-- Sección 6: Propiedad arquimediana y unicidad del límite
-- ============================================================

/-- **Sin infinitesimales**: un racional no negativo acotado por todos los
`1/2^n` es cero. (Propiedad arquimediana diádica de ℚ₀cls.) -/
theorem eq_zero_of_le_pow2_all : ∀ {q : ℚ₀cls}, 0 ≤ q → (∀ n : ℕ₀, q ≤ pow2 n) → q = 0 := by
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    intro hq0 h
    -- numerador no negativo
    have hc0 : (0 : ℤ₀cls) ≤ p.1 := by
      have h0 := (mk_le_mk 0 p.1 den1 p.2).mp hq0
      rwa [ℤ₀cls.zero_mul, show ℤ₀cls.ofNat den1.val = (1 : ℤ₀cls) from rfl, ℤ₀cls.mul_one] at h0
    have hc : p.1 = ℤ₀cls.ofNat (ℤ₀cls.toNat p.1) := ℤ₀cls.nonneg_eq_ofNat hc0
    -- ∀ n, (toNat p.1) · 2^n ≤ p.2.val
    have hkey : ∀ n : ℕ₀,
        Peano.Mul.mul (ℤ₀cls.toNat p.1) (Peano.Pow.pow (σ (σ 𝟘)) n) ≤ p.2.val := by
      intro n
      have hn := (mk_le_mk p.1 (ℤ₀cls.ofNat (σ 𝟘)) p.2 (pow2_den n)).mp (h n)
      rw [show ℤ₀cls.ofNat (σ 𝟘) = (1 : ℤ₀cls) from rfl, ℤ₀cls.one_mul, hc, ← ℤ₀cls.ofNat_mul] at hn
      exact ℤ₀cls.le_ofNat_iff.mp hn
    -- el numerador (en ℕ₀) es cero
    have hnum0 : ℤ₀cls.toNat p.1 = 𝟘 := by
      by_cases hz : ℤ₀cls.toNat p.1 = 𝟘
      · exact hz
      · exfalso
        have h1 : (σ 𝟘 : ℕ₀) ≤ ℤ₀cls.toNat p.1 := by omega₀
        have hd := hkey (σ p.2.val)
        have hpow : Peano.Order.le₀ (σ p.2.val)
            (Peano.Pow.pow (σ (σ 𝟘)) (σ p.2.val)) := Peano.Pow.n_le_two_pow_n (σ p.2.val)
        have hmono : Peano.Order.le₀ (Peano.Pow.pow (σ (σ 𝟘)) (σ p.2.val))
            (Peano.Mul.mul (ℤ₀cls.toNat p.1) (Peano.Pow.pow (σ (σ 𝟘)) (σ p.2.val))) := by
          have hm := Peano.Mul.mul_le_mono_right (Peano.Pow.pow (σ (σ 𝟘)) (σ p.2.val)) h1
          rwa [show Peano.Mul.mul (σ 𝟘) (Peano.Pow.pow (σ (σ 𝟘)) (σ p.2.val))
                = Peano.Pow.pow (σ (σ 𝟘)) (σ p.2.val) from Peano.Mul.one_mul _] at hm
        have hchain : (σ p.2.val : ℕ₀) ≤ p.2.val :=
          Peano.Order.le_trans _ _ _ hpow (Peano.Order.le_trans _ _ _ hmono hd)
        omega₀
    have hp1 : p.1 = 0 := by rw [hc, hnum0]; rfl
    show mk p.1 p.2 = 0
    exact mk_eq_zero_iff.mpr hp1

/-- **Unicidad del límite**: si `f` converge a `L₁` y a `L₂`, entonces `L₁ = L₂`. -/
theorem convergesTo_unique {f : ℕ₀ → ℚ₀cls} {L₁ L₂ : ℚ₀cls}
    (h1 : ConvergesTo f L₁) (h2 : ConvergesTo f L₂) : L₁ = L₂ := by
  have hbound : ∀ n : ℕ₀, absVal (L₁ - L₂) ≤ pow2 n := by
    intro n
    have hb1 : absVal (Add.add L₁ (Neg.neg (f n))) ≤ pow2 (σ n) := by
      rw [show absVal (Add.add L₁ (Neg.neg (f n)))
            = absVal (Add.add (f n) (Neg.neg L₁)) from absVal_sub_comm L₁ (f n)]
      exact h1 n
    have hb2 : absVal (Add.add (f n) (Neg.neg L₂)) ≤ pow2 (σ n) := h2 n
    have h_eq : Add.add L₁ (Neg.neg L₂)
        = Add.add (Add.add L₁ (Neg.neg (f n))) (Add.add (f n) (Neg.neg L₂)) := by
      calc Add.add L₁ (Neg.neg L₂)
          = Add.add L₁ (Add.add 0 (Neg.neg L₂)) := by rw [zero_add (Neg.neg L₂)]
        _ = Add.add L₁ (Add.add (Add.add (Neg.neg (f n)) (f n)) (Neg.neg L₂)) := by
              rw [neg_add_self (f n)]
        _ = Add.add L₁ (Add.add (Neg.neg (f n)) (Add.add (f n) (Neg.neg L₂))) := by
              rw [add_assoc (Neg.neg (f n)) (f n) (Neg.neg L₂)]
        _ = Add.add (Add.add L₁ (Neg.neg (f n))) (Add.add (f n) (Neg.neg L₂)) := by
              rw [add_assoc L₁ (Neg.neg (f n)) (Add.add (f n) (Neg.neg L₂))]
    have h_tri : absVal (Add.add L₁ (Neg.neg L₂))
        ≤ Add.add (absVal (Add.add L₁ (Neg.neg (f n))))
                  (absVal (Add.add (f n) (Neg.neg L₂))) := by
      rw [h_eq]
      exact absVal_add_le (Add.add L₁ (Neg.neg (f n))) (Add.add (f n) (Neg.neg L₂))
    have hsum : Add.add (absVal (Add.add L₁ (Neg.neg (f n))))
                        (absVal (Add.add (f n) (Neg.neg L₂)))
        ≤ Add.add (pow2 (σ n)) (pow2 (σ n)) := by
      have ha := add_le_add_right hb1 (absVal (Add.add (f n) (Neg.neg L₂)))
      have hb := add_le_add_left hb2 (pow2 (σ n))
      exact le_trans ha hb
    have hfin := le_trans h_tri hsum
    rw [pow2_succ_add n] at hfin
    exact hfin
  have hz : absVal (L₁ - L₂) = 0 := eq_zero_of_le_pow2_all (absVal_nonneg _) hbound
  have hsub0 : L₁ - L₂ = 0 := (absVal_zero_iff (L₁ - L₂)).mp hz
  calc L₁
      = Add.add L₁ 0 := (add_zero L₁).symm
    _ = Add.add L₁ (Add.add (Neg.neg L₂) L₂) := by rw [neg_add_self L₂]
    _ = Add.add (Add.add L₁ (Neg.neg L₂)) L₂ := by rw [add_assoc L₁ (Neg.neg L₂) L₂]
    _ = Add.add (L₁ - L₂) L₂ := rfl
    _ = Add.add 0 L₂ := by rw [hsub0]
    _ = L₂ := zero_add L₂

end ℚ₀cls
