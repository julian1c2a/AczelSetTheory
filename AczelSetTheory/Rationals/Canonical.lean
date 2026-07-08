/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Canonical.lean
-- Representante canónico (forma reducida) para ℚ₀.
--
-- Forma canónica de un par (n : ℤ₀, d : ℕ₁):
--   g := gcd |n| d ; num := sign(n) · (|n| / g) ; den := d / g.
--   Si n = 0 ⇒ g = d ⇒ num = 0, den = 1 (regla "num 0 ⇒ den 1", automática).
--   Si n ≠ 0 ⇒ num, den coprimos.
--
-- ESTADO: PASO 1 (reduce + reduce_ratEq + reduce_reduced).
--
-- API (paso 1):
--   ℚ₀.reduce          : ℤ₀ × ℕ₁ → ℤ₀ × ℕ₁
--   ℚ₀.reduce_ratEq    : n · ofNat (reduce p).den = (reduce p).num · ofNat p.den
--   ℚ₀.reduce_reduced  : Coprime |«num de reduce»| (reduce p).den
--
-- Dependencies: AczelSetTheory.Rationals.Basic, Integers.Functions, Peano gcd/Primes
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Integers.Functions
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Primes

open Peano Peano.Axioms Peano.Add Peano.Mul Peano.Order Peano.Arith Peano.Primes

namespace ℚ₀

-- ============================================================
-- Sección 0: Lemas auxiliares sobre ℕ₀ y ℤ₀
-- ============================================================

/-- `𝟘 / d = 𝟘` para `d ≠ 𝟘`. -/
private theorem zero_div_eq {d : ℕ₀} (hd : d ≠ 𝟘) : (𝟘 : ℕ₀) / d = 𝟘 :=
  Peano.Order.le_zero_eq_wp (Peano.Div.div_le_self 𝟘 d hd)

/-- Intercambio de división por gcd: `A · (d/g) = (A/g) · d` cuando `g ∣ A`, `g ∣ d`. -/
private theorem mul_div_swap {A d g : ℕ₀} (hgA : g ∣ A) (hgd : g ∣ d) (hg : g ≠ 𝟘) :
    mul A (d / g) = mul (A / g) d := by
  have hA : mul (A / g) g = A := div_mul_cancel hg hgA
  have hd : mul (d / g) g = d := div_mul_cancel hg hgd
  calc mul A (d / g)
      = mul (mul (A / g) g) (d / g) := by rw [hA]
    _ = mul (A / g) (mul g (d / g)) := by rw [Peano.Mul.mul_assoc]
    _ = mul (A / g) (mul (d / g) g) := by rw [Peano.Mul.mul_comm g (d / g)]
    _ = mul (A / g) d := by rw [hd]

/-- Un entero se descompone como signo · magnitud: `z = sign z · ofNat |z|`. -/
theorem self_eq_sign_mul_toNat_abs (z : ℤ₀) :
    z = Mul.mul (ℤ₀.sign z) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs z))) := by
  have hAbsEq : ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs z)) = ℤ₀.abs z :=
    (ℤ₀.nonneg_eq_ofNat (ℤ₀.abs_nonneg z)).symm
  rw [hAbsEq]
  by_cases hpos : (0 : ℤ₀) < z
  · have hs : ℤ₀.sign z = 1 := by unfold ℤ₀.sign; rw [if_pos hpos]
    have habs : ℤ₀.abs z = z := by unfold ℤ₀.abs; rw [if_pos hpos.1]
    rw [hs, habs, ℤ₀.one_mul]
  · by_cases hlt : z < (0 : ℤ₀)
    · have hs : ℤ₀.sign z = -1 := ℤ₀.sign_neg z hlt
      have habs : ℤ₀.abs z = -z := by unfold ℤ₀.abs; rw [if_neg hlt.2]
      rw [hs, habs, ℤ₀.neg_mul, ℤ₀.one_mul, ℤ₀.neg_neg]
    · have hz : z = 0 := by
        rcases ℤ₀.le_total 0 z with h | h
        · by_cases hle : z ≤ 0
          · exact ℤ₀.le_antisymm hle h
          · exact absurd (show (0 : ℤ₀) < z from ⟨h, hle⟩) hpos
        · by_cases hge : (0 : ℤ₀) ≤ z
          · exact ℤ₀.le_antisymm h hge
          · exact absurd (show z < (0 : ℤ₀) from ⟨h, hge⟩) hlt
      rw [hz, ℤ₀.sign_zero, ℤ₀.zero_mul]

/-- `|sign z · ofNat m| = m` (magnitud recuperada), con la salvedad `z = 0 ⇒ m = 𝟘`. -/
private theorem toNat_abs_sign_mul_ofNat (z : ℤ₀) (m : ℕ₀) (hz0 : z = 0 → m = 𝟘) :
    ℤ₀.toNat (ℤ₀.abs (Mul.mul (ℤ₀.sign z) (ℤ₀.ofNat m))) = m := by
  by_cases hpos : (0 : ℤ₀) < z
  · have hs : ℤ₀.sign z = 1 := by unfold ℤ₀.sign; rw [if_pos hpos]
    rw [hs, ℤ₀.one_mul, ℤ₀.abs_ofNat, ℤ₀.toNat_ofNat]
  · by_cases hlt : z < (0 : ℤ₀)
    · have hs : ℤ₀.sign z = -1 := ℤ₀.sign_neg z hlt
      rw [hs, ℤ₀.neg_mul, ℤ₀.one_mul, ℤ₀.abs_neg, ℤ₀.abs_ofNat, ℤ₀.toNat_ofNat]
    · have hz : z = 0 := by
        rcases ℤ₀.le_total 0 z with h | h
        · by_cases hle : z ≤ 0
          · exact ℤ₀.le_antisymm hle h
          · exact absurd (show (0 : ℤ₀) < z from ⟨h, hle⟩) hpos
        · by_cases hge : (0 : ℤ₀) ≤ z
          · exact ℤ₀.le_antisymm h hge
          · exact absurd (show z < (0 : ℤ₀) from ⟨h, hge⟩) hlt
      rw [hz0 hz, ℤ₀.ofNat_zero, ℤ₀.mul_zero,
          show ℤ₀.abs (0 : ℤ₀) = 0 from ℤ₀.abs_eq_zero_iff.mpr rfl,
          show ℤ₀.toNat (0 : ℤ₀) = 𝟘 from by rw [← ℤ₀.ofNat_zero, ℤ₀.toNat_ofNat]]

/-- Al dividir por el gcd se obtienen coprimos: `Coprime (A/gcd A d) (d/gcd A d)`. -/
private theorem coprime_div_gcd {A d : ℕ₀} (hd : d ≠ 𝟘) :
    Coprime (A / gcd A d) (d / gcd A d) := by
  have hg0 : gcd A d ≠ 𝟘 := gcd_ne_zero_right hd
  have hgA : gcd A d ∣ A := gcd_dvd_left A d
  have hgd : gcd A d ∣ d := gcd_dvd_right A d
  have hAg : A = mul (A / gcd A d) (gcd A d) := (div_mul_cancel hg0 hgA).symm
  have hdg : d = mul (d / gcd A d) (gcd A d) := (div_mul_cancel hg0 hgd).symm
  rw [← gcd_eq_one_iff_coprime]
  -- Todo divisor común del par reducido divide a la unidad.
  have key : ∀ c : ℕ₀, c ∣ (A / gcd A d) → c ∣ (d / gcd A d) → c ∣ 𝟙 := by
    intro c hcA hcd
    obtain ⟨k, hk⟩ := hcA
    obtain ⟨j, hj⟩ := hcd
    have hcgA : mul c (gcd A d) ∣ A :=
      ⟨k, by
        calc A = mul (A / gcd A d) (gcd A d) := hAg
          _ = mul (mul c k) (gcd A d) := by rw [hk]
          _ = mul (mul c (gcd A d)) k := by
                rw [Peano.Mul.mul_assoc, Peano.Mul.mul_comm k (gcd A d),
                    ← Peano.Mul.mul_assoc]⟩
    have hcgd : mul c (gcd A d) ∣ d :=
      ⟨j, by
        calc d = mul (d / gcd A d) (gcd A d) := hdg
          _ = mul (mul c j) (gcd A d) := by rw [hj]
          _ = mul (mul c (gcd A d)) j := by
                rw [Peano.Mul.mul_assoc, Peano.Mul.mul_comm j (gcd A d),
                    ← Peano.Mul.mul_assoc]⟩
    have hcg_g : mul c (gcd A d) ∣ gcd A d := dvd_gcd hcgA hcgd
    obtain ⟨m, hm⟩ := hcg_g
    have hstep : mul (mul c m) (gcd A d) = gcd A d := by
      calc mul (mul c m) (gcd A d)
          = mul c (mul m (gcd A d)) := by rw [Peano.Mul.mul_assoc]
        _ = mul c (mul (gcd A d) m) := by rw [Peano.Mul.mul_comm m (gcd A d)]
        _ = mul (mul c (gcd A d)) m := by rw [← Peano.Mul.mul_assoc]
        _ = gcd A d := hm.symm
    have hcm : mul c m = 𝟙 :=
      Peano.Mul.mul_cancelation_right (mul c m) 𝟙 (gcd A d) hg0
        (by rw [Peano.Mul.one_mul]; exact hstep)
    exact ⟨m, hcm.symm⟩
  exact antisymm_divides
    (key (gcd (A / gcd A d) (d / gcd A d)) (gcd_dvd_left _ _) (gcd_dvd_right _ _))
    (one_divides _)

/-- Identidad núcleo del respeto de `reduce` por la equivalencia (a nivel ℤ₀). -/
private theorem ratEq_core (s : ℤ₀) {A d g : ℕ₀}
    (hgA : g ∣ A) (hgd : g ∣ d) (hg : g ≠ 𝟘) :
    Mul.mul (Mul.mul s (ℤ₀.ofNat A)) (ℤ₀.ofNat (d / g))
      = Mul.mul (Mul.mul s (ℤ₀.ofNat (A / g))) (ℤ₀.ofNat d) := by
  rw [ℤ₀.mul_assoc s (ℤ₀.ofNat A) (ℤ₀.ofNat (d / g)),
      ℤ₀.mul_assoc s (ℤ₀.ofNat (A / g)) (ℤ₀.ofNat d),
      ← ℤ₀.ofNat_mul A (d / g), ← ℤ₀.ofNat_mul (A / g) d,
      mul_div_swap hgA hgd hg]

-- ============================================================
-- Sección 1: La función reduce
-- ============================================================

/-- El denominador reducido `d / gcd |n| d` es no nulo. -/
private theorem reduceDen_ne_zero (n : ℤ₀) (d : ℕ₁) :
    d.val / gcd (ℤ₀.toNat (ℤ₀.abs n)) d.val ≠ 𝟘 := by
  intro h
  have hg0 : gcd (ℤ₀.toNat (ℤ₀.abs n)) d.val ≠ 𝟘 := gcd_ne_zero_right d.property
  have hdvd : gcd (ℤ₀.toNat (ℤ₀.abs n)) d.val ∣ d.val := gcd_dvd_right _ _
  have hcancel :
      mul (d.val / gcd (ℤ₀.toNat (ℤ₀.abs n)) d.val)
          (gcd (ℤ₀.toNat (ℤ₀.abs n)) d.val) = d.val :=
    div_mul_cancel hg0 hdvd
  rw [h, Peano.Mul.zero_mul] at hcancel
  exact d.property hcancel.symm

/-- Forma reducida de un par `(n, d)`: numerador `sign n · (|n|/g)`, denominador `d/g`
    con `g = gcd |n| d`. -/
def reduce (p : ℤ₀ × ℕ₁) : ℤ₀ × ℕ₁ :=
  ( Mul.mul (ℤ₀.sign p.1)
      (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1) / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)),
    ⟨p.2.val / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val, reduceDen_ne_zero p.1 p.2⟩ )

-- ============================================================
-- Sección 2: reduce respeta la equivalencia
-- ============================================================

/-- `reduce p` es equivalente a `p`: cruce `n · den' = num' · d`. -/
theorem reduce_ratEq (p : ℤ₀ × ℕ₁) :
    Mul.mul p.1 (ℤ₀.ofNat (reduce p).2.val)
      = Mul.mul (reduce p).1 (ℤ₀.ofNat p.2.val) := by
  have e1 : (reduce p).1
      = Mul.mul (ℤ₀.sign p.1)
          (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1)
            / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)) := rfl
  have e2 : (reduce p).2.val
      = p.2.val / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val := rfl
  rw [e1, e2]
  have hdec : p.1 = Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1))) :=
    self_eq_sign_mul_toNat_abs p.1
  calc Mul.mul p.1 (ℤ₀.ofNat (p.2.val / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val))
      = Mul.mul (Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1))))
                (ℤ₀.ofNat (p.2.val / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)) :=
        congrArg
          (fun t => Mul.mul t (ℤ₀.ofNat (p.2.val / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)))
          hdec
    _ = Mul.mul (Mul.mul (ℤ₀.sign p.1)
            (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1) / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)))
          (ℤ₀.ofNat p.2.val) :=
        ratEq_core (ℤ₀.sign p.1)
          (gcd_dvd_left (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)
          (gcd_dvd_right (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)
          (gcd_ne_zero_right p.2.property)

-- ============================================================
-- Sección 3: reduce produce numerador/denominador coprimos
-- ============================================================

/-- El par reducido tiene numerador (en magnitud) y denominador coprimos. -/
theorem reduce_reduced (p : ℤ₀ × ℕ₁) :
    Coprime (ℤ₀.toNat (ℤ₀.abs (reduce p).1)) (reduce p).2.val := by
  have e1 : (reduce p).1
      = Mul.mul (ℤ₀.sign p.1)
          (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1)
            / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)) := rfl
  have e2 : (reduce p).2.val
      = p.2.val / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val := rfl
  rw [e1, e2]
  have hm : ℤ₀.toNat (ℤ₀.abs (Mul.mul (ℤ₀.sign p.1)
      (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1) / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val))))
      = ℤ₀.toNat (ℤ₀.abs p.1) / gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val := by
    apply toNat_abs_sign_mul_ofNat
    intro hz
    have hA0 : ℤ₀.toNat (ℤ₀.abs p.1) = 𝟘 := by
      rw [hz, show ℤ₀.abs (0 : ℤ₀) = 0 from ℤ₀.abs_eq_zero_iff.mpr rfl,
          show ℤ₀.toNat (0 : ℤ₀) = 𝟘 from by rw [← ℤ₀.ofNat_zero, ℤ₀.toNat_ofNat]]
    rw [hA0, zero_div_eq (gcd_ne_zero_right p.2.property)]
  rw [hm]
  exact coprime_div_gcd p.2.property

-- ============================================================
-- Sección 4: Multiplicatividad de |·| y toNat (para unicidad)
-- ============================================================

private theorem int_abs_of_nonneg {z : ℤ₀} (h : (0 : ℤ₀) ≤ z) : ℤ₀.abs z = z := by
  unfold ℤ₀.abs; rw [if_pos h]

private theorem int_neg_zero : Neg.neg (0 : ℤ₀) = 0 := by
  have h := ℤ₀.neg_add_self (0 : ℤ₀); rwa [ℤ₀.add_zero] at h

private theorem int_abs_of_nonpos {z : ℤ₀} (h : z ≤ 0) : ℤ₀.abs z = -z := by
  by_cases h0 : (0 : ℤ₀) ≤ z
  · have hz : z = 0 := ℤ₀.le_antisymm h h0
    rw [hz, ℤ₀.abs_eq_zero_iff.mpr rfl, int_neg_zero]
  · unfold ℤ₀.abs; rw [if_neg h0]

private theorem int_mul_nonpos_of_nonpos_of_nonneg {a b : ℤ₀}
    (ha : a ≤ 0) (hb : (0 : ℤ₀) ≤ b) : Mul.mul a b ≤ 0 := by
  have h := ℤ₀.mul_nonpos_of_nonneg_of_nonpos hb ha
  rwa [ℤ₀.mul_comm b a] at h

/-- Valor absoluto multiplicativo en ℤ₀. -/
private theorem int_abs_mul (x y : ℤ₀) :
    ℤ₀.abs (Mul.mul x y) = Mul.mul (ℤ₀.abs x) (ℤ₀.abs y) := by
  by_cases hx : (0 : ℤ₀) ≤ x <;> by_cases hy : (0 : ℤ₀) ≤ y
  · rw [int_abs_of_nonneg hx, int_abs_of_nonneg hy,
        int_abs_of_nonneg (ℤ₀.mul_nonneg hx hy)]
  · have hy' : y ≤ 0 := (ℤ₀.le_total y 0).resolve_right hy
    rw [int_abs_of_nonneg hx, int_abs_of_nonpos hy',
        int_abs_of_nonpos (ℤ₀.mul_nonpos_of_nonneg_of_nonpos hx hy'), ℤ₀.mul_neg]
  · have hx' : x ≤ 0 := (ℤ₀.le_total x 0).resolve_right hx
    rw [int_abs_of_nonpos hx', int_abs_of_nonneg hy,
        int_abs_of_nonpos (int_mul_nonpos_of_nonpos_of_nonneg hx' hy), ℤ₀.neg_mul]
  · have hx' : x ≤ 0 := (ℤ₀.le_total x 0).resolve_right hx
    have hy' : y ≤ 0 := (ℤ₀.le_total y 0).resolve_right hy
    rw [int_abs_of_nonpos hx', int_abs_of_nonpos hy',
        int_abs_of_nonneg (ℤ₀.mul_nonneg_of_nonpos_of_nonpos hx' hy'),
        ℤ₀.neg_mul, ℤ₀.mul_neg, ℤ₀.neg_neg]

/-- `toNat ∘ abs` es multiplicativo. -/
private theorem toNat_abs_mul (x y : ℤ₀) :
    ℤ₀.toNat (ℤ₀.abs (Mul.mul x y))
      = mul (ℤ₀.toNat (ℤ₀.abs x)) (ℤ₀.toNat (ℤ₀.abs y)) := by
  have hax : ℤ₀.abs x = ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs x)) :=
    ℤ₀.nonneg_eq_ofNat (ℤ₀.abs_nonneg x)
  have hay : ℤ₀.abs y = ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs y)) :=
    ℤ₀.nonneg_eq_ofNat (ℤ₀.abs_nonneg y)
  have key : ℤ₀.abs (Mul.mul x y)
      = ℤ₀.ofNat (mul (ℤ₀.toNat (ℤ₀.abs x)) (ℤ₀.toNat (ℤ₀.abs y))) :=
    calc ℤ₀.abs (Mul.mul x y)
        = Mul.mul (ℤ₀.abs x) (ℤ₀.abs y) := int_abs_mul x y
      _ = Mul.mul (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs x)))
              (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs y))) := by rw [← hax, ← hay]
      _ = ℤ₀.ofNat (mul (ℤ₀.toNat (ℤ₀.abs x)) (ℤ₀.toNat (ℤ₀.abs y))) :=
            (ℤ₀.ofNat_mul _ _).symm
  rw [key, ℤ₀.toNat_ofNat]

/-- Cancelación multiplicativa por `ofNat k` positivo (lado derecho) en ℤ₀. -/
private theorem int_mul_right_cancel_ofNat {k : ℕ₀} (hk : k ≠ 𝟘) {x y : ℤ₀}
    (h : Mul.mul x (ℤ₀.ofNat k) = Mul.mul y (ℤ₀.ofNat k)) : x = y := by
  have h1 : x ≤ y :=
    (ℤ₀.mul_le_mul_right_ofNat_pos hk x y).mpr (by rw [h]; exact ℤ₀.le_refl _)
  have h2 : y ≤ x :=
    (ℤ₀.mul_le_mul_right_ofNat_pos hk y x).mpr (by rw [h]; exact ℤ₀.le_refl _)
  exact ℤ₀.le_antisymm h1 h2

-- ============================================================
-- Sección 5: Unicidad de la fracción reducida (ℕ₀) y reduce_unique
-- ============================================================

/-- Dos fracciones coprimas iguales son idénticas: `a·e = c·b`, `Coprime a b`,
    `Coprime c e`, `e ≠ 𝟘` ⟹ `a = c ∧ b = e`. -/
private theorem nat_frac_unique {a b c e : ℕ₀}
    (hab : Coprime a b) (hce : Coprime c e) (he : e ≠ 𝟘)
    (h : mul a e = mul c b) : a = c ∧ b = e := by
  have hbdvd : b ∣ mul a e := by rw [h]; exact ⟨c, Peano.Mul.mul_comm c b⟩
  have hbe' : b ∣ e := coprime_dvd_of_dvd_mul (coprime_comm.mp hab) hbdvd
  have hedvd : e ∣ mul c b := by rw [← h]; exact ⟨a, Peano.Mul.mul_comm a e⟩
  have heb' : e ∣ b := coprime_dvd_of_dvd_mul (coprime_comm.mp hce) hedvd
  have hbe : b = e := antisymm_divides hbe' heb'
  have hae : mul a e = mul c e := by rw [h, hbe]
  exact ⟨mul_cancelation_right a c e he hae, hbe⟩

/-- **Unicidad del reducido**: pares equivalentes tienen la misma forma reducida. -/
theorem reduce_unique (p q : ℤ₀ × ℕ₁)
    (h : Mul.mul p.1 (ℤ₀.ofNat q.2.val) = Mul.mul q.1 (ℤ₀.ofNat p.2.val)) :
    reduce p = reduce q := by
  -- Cruce de los reducidos vía mk_eq_iff (público).
  have hmkp : mk (reduce p).1 (reduce p).2 = mk p.1 p.2 :=
    (mk_eq_iff (reduce p).1 p.1 (reduce p).2 p.2).mpr (reduce_ratEq p).symm
  have hmkq : mk (reduce q).1 (reduce q).2 = mk q.1 q.2 :=
    (mk_eq_iff (reduce q).1 q.1 (reduce q).2 q.2).mpr (reduce_ratEq q).symm
  have hpq : mk p.1 p.2 = mk q.1 q.2 := (mk_eq_iff p.1 q.1 p.2 q.2).mpr h
  have hstar : Mul.mul (reduce p).1 (ℤ₀.ofNat (reduce q).2.val)
             = Mul.mul (reduce q).1 (ℤ₀.ofNat (reduce p).2.val) :=
    (mk_eq_iff (reduce p).1 (reduce q).1 (reduce p).2 (reduce q).2).mp
      (hmkp.trans (hpq.trans hmkq.symm))
  -- Magnitudes.
  have hmag : mul (ℤ₀.toNat (ℤ₀.abs (reduce p).1)) (reduce q).2.val
            = mul (ℤ₀.toNat (ℤ₀.abs (reduce q).1)) (reduce p).2.val := by
    have hraw : ℤ₀.toNat (ℤ₀.abs (Mul.mul (reduce p).1 (ℤ₀.ofNat (reduce q).2.val)))
              = ℤ₀.toNat (ℤ₀.abs (Mul.mul (reduce q).1 (ℤ₀.ofNat (reduce p).2.val))) :=
      congrArg (fun z => ℤ₀.toNat (ℤ₀.abs z)) hstar
    rw [toNat_abs_mul, toNat_abs_mul,
        show ℤ₀.toNat (ℤ₀.abs (ℤ₀.ofNat (reduce q).2.val)) = (reduce q).2.val from by
          rw [ℤ₀.abs_ofNat, ℤ₀.toNat_ofNat],
        show ℤ₀.toNat (ℤ₀.abs (ℤ₀.ofNat (reduce p).2.val)) = (reduce p).2.val from by
          rw [ℤ₀.abs_ofNat, ℤ₀.toNat_ofNat]] at hraw
    exact hraw
  -- Unicidad nat.
  obtain ⟨_, hden⟩ :=
    nat_frac_unique (reduce_reduced p) (reduce_reduced q) (reduce q).2.property hmag
  have hden1 : (reduce p).2 = (reduce q).2 := Subtype.ext hden
  have hnum : (reduce p).1 = (reduce q).1 := by
    rw [← hden] at hstar
    exact int_mul_right_cancel_ofNat (reduce p).2.property hstar
  exact Prod.ext hnum hden1

-- ============================================================
-- Sección 6: Representante canónico de ℚ₀ (lift al cociente)
-- ============================================================

/-- Representante canónico (numerador entero, denominador positivo coprimos). -/
def repr : ℚ₀ → ℤ₀ × ℕ₁ :=
  Quotient.lift reduce (fun a b hab => reduce_unique a b hab)

/-- Numerador canónico de un racional. -/
def num (r : ℚ₀) : ℤ₀ := (repr r).1

/-- Denominador canónico (positivo) de un racional. -/
def den (r : ℚ₀) : ℕ₁ := (repr r).2

theorem mk_repr (r : ℚ₀) : mk (repr r).1 (repr r).2 = r := by
  refine Quotient.inductionOn r (fun p => ?_)
  show mk (reduce p).1 (reduce p).2 = mk p.1 p.2
  exact (mk_eq_iff (reduce p).1 p.1 (reduce p).2 p.2).mpr (reduce_ratEq p).symm

theorem repr_inj {a b : ℚ₀} (h : repr a = repr b) : a = b := by
  have ha := mk_repr a
  have hb := mk_repr b
  rw [← ha, ← hb, h]

/-- El representante canónico tiene numerador (en magnitud) y denominador coprimos. -/
theorem repr_reduced (r : ℚ₀) :
    Coprime (ℤ₀.toNat (ℤ₀.abs (repr r).1)) (repr r).2.val := by
  refine Quotient.inductionOn r (fun p => ?_)
  exact reduce_reduced p

end ℚ₀
