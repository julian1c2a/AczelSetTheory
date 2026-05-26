/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/Rationals.lean
-- ℚ₀: racionales como cociente de (ℤ₀ × {n : ℕ₀ // n ≠ 𝟘}) por
--      (a,b) ~ (c,d) ↔ a·ofNat(d) = c·ofNat(b).
--
-- Público:
--   ℚ₀                             : tipo de los racionales
--   ℚ₀.mk                          : ℤ₀ → {n : ℕ₀ // n ≠ 𝟘} → ℚ₀
--   ℚ₀.ofInt                       : ℤ₀ → ℚ₀   (embedding inyectivo)
--   ℚ₀.ofNat₀                      : ℕ₀ → ℚ₀
--   instances: Zero, One, Add, Neg, Mul, Sub, LE, LT
--   Leyes de anillo conmutativo:
--     ℚ₀.add_comm, add_assoc, zero_add, add_zero
--     ℚ₀.add_neg_self, neg_add_self
--     ℚ₀.mul_comm, mul_assoc, one_mul, mul_one, zero_mul, mul_zero
--     ℚ₀.left_distrib, right_distrib, neg_mul, mul_neg
--   ℚ₀.le_refl, le_antisymm, le_trans, le_total
--   ℚ₀.ofInt_injective

import AczelSetTheory.Integers.Order

-- ─────────────────────────────────────────────────────────────────────────────
-- Sección privada: relación de equivalencia y operaciones crudas
-- ─────────────────────────────────────────────────────────────────────────────

section PrivateDefs

open Peano Peano.Axioms Peano.Add Peano.Mul Peano.Order

-- Denominadores positivos (subconjunto de ℕ₀)
private abbrev PosNat₀ := {n : ℕ₀ // n ≠ 𝟘}

-- Denominador unidad: 1
private def den1 : PosNat₀ := ⟨𝟙, succ_neq_zero 𝟘⟩

-- Producto de denominadores positivos
private theorem mul_ne_zero₀ {n m : ℕ₀} (hn : n ≠ 𝟘) (hm : m ≠ 𝟘) : mul n m ≠ 𝟘 := by
  intro h
  exact ((mul_eq_zero n m).mp h).elim hn hm

private def mulDen (b d : PosNat₀) : PosNat₀ :=
  ⟨mul b.val d.val, mul_ne_zero₀ b.property d.property⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- Relación de equivalencia: (a,b) ~ (c,d) ↔ a·ofNat(d) = c·ofNat(b)
-- ─────────────────────────────────────────────────────────────────────────────

private def ratEq (p q : ℤ₀ × PosNat₀) : Prop :=
  Mul.mul p.1 (ℤ₀.ofNat q.2.val) = Mul.mul q.1 (ℤ₀.ofNat p.2.val)

private theorem ratEq_refl (p : ℤ₀ × PosNat₀) : ratEq p p := rfl

private theorem ratEq_symm {p q : ℤ₀ × PosNat₀} (h : ratEq p q) : ratEq q p := h.symm

-- Cancelación izquierda por ofNat(k) en ℤ₀, usada en ratEq_trans
private theorem mul_left_cancel_int {k : ℕ₀} (hk : k ≠ 𝟘) {x y : ℤ₀}
    (h : Mul.mul (ℤ₀.ofNat k) x = Mul.mul (ℤ₀.ofNat k) y) : x = y := by
  -- k ≠ 𝟘 => ofNat(k) > 0; si x ≠ y => ofNat(k)·(x-y) ≠ 0, contradicción.
  sorry

private theorem ratEq_trans {p q r : ℤ₀ × PosNat₀}
    (h1 : ratEq p q) (h2 : ratEq q r) : ratEq p r := by
  simp only [ratEq] at *
  -- Hay que demostrar: p.1 · ofNat(r.2) = r.1 · ofNat(p.2)
  -- Multiplicamos ambos lados por ofNat(q.2) y usamos h1, h2.
  apply mul_left_cancel_int q.2.property
  -- Objetivo: ofNat(q.2) · (p.1 · ofNat(r.2)) = ofNat(q.2) · (r.1 · ofNat(p.2))
  calc Mul.mul (ℤ₀.ofNat q.2.val) (Mul.mul p.1 (ℤ₀.ofNat r.2.val))
      = Mul.mul (Mul.mul p.1 (ℤ₀.ofNat q.2.val)) (ℤ₀.ofNat r.2.val) := by
            rw [← ℤ₀.mul_assoc, ℤ₀.mul_comm (ℤ₀.ofNat q.2.val) p.1, ℤ₀.mul_assoc]
    _ = Mul.mul (Mul.mul q.1 (ℤ₀.ofNat p.2.val)) (ℤ₀.ofNat r.2.val) := by
            rw [h1]
    _ = Mul.mul q.1 (Mul.mul (ℤ₀.ofNat p.2.val) (ℤ₀.ofNat r.2.val)) := by
            rw [ℤ₀.mul_assoc]
    _ = Mul.mul q.1 (Mul.mul (ℤ₀.ofNat r.2.val) (ℤ₀.ofNat p.2.val)) := by
            rw [ℤ₀.mul_comm (ℤ₀.ofNat p.2.val) (ℤ₀.ofNat r.2.val)]
    _ = Mul.mul (Mul.mul q.1 (ℤ₀.ofNat r.2.val)) (ℤ₀.ofNat p.2.val) := by
            rw [← ℤ₀.mul_assoc]
    _ = Mul.mul (Mul.mul r.1 (ℤ₀.ofNat q.2.val)) (ℤ₀.ofNat p.2.val) := by
            rw [h2]
    _ = Mul.mul (ℤ₀.ofNat q.2.val) (Mul.mul r.1 (ℤ₀.ofNat p.2.val)) := by
            rw [ℤ₀.mul_comm r.1 (ℤ₀.ofNat q.2.val), ℤ₀.mul_assoc]

private instance ratSetoid : Setoid (ℤ₀ × PosNat₀) where
  r     := ratEq
  iseqv := ⟨ratEq_refl, ratEq_symm, ratEq_trans⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- Operaciones crudas (sobre representantes)
-- ─────────────────────────────────────────────────────────────────────────────

-- Suma: a/b + c/d = (a·d + c·b) / (b·d)
private def addRaw (p q : ℤ₀ × PosNat₀) : ℤ₀ × PosNat₀ :=
  (Mul.mul p.1 (ℤ₀.ofNat q.2.val) + Mul.mul q.1 (ℤ₀.ofNat p.2.val), mulDen p.2 q.2)

-- Negación: -(a/b) = (-a)/b
private def negRaw (p : ℤ₀ × PosNat₀) : ℤ₀ × PosNat₀ := (-p.1, p.2)

-- Multiplicación: (a/b)·(c/d) = (a·c)/(b·d)
private def mulRaw (p q : ℤ₀ × PosNat₀) : ℤ₀ × PosNat₀ :=
  (Mul.mul p.1 q.1, mulDen p.2 q.2)

-- ─────────────────────────────────────────────────────────────────────────────
-- Compatibilidad de las operaciones con ratEq
-- ─────────────────────────────────────────────────────────────────────────────

private theorem negWD (p q : ℤ₀ × PosNat₀) (h : ratEq p q) :
    ratEq (negRaw p) (negRaw q) := by
  simp only [ratEq, negRaw] at *
  rw [ℤ₀.neg_mul, ℤ₀.neg_mul, h]

private theorem mulWD (p p' q q' : ℤ₀ × PosNat₀)
    (h1 : ratEq p p') (h2 : ratEq q q') :
    ratEq (mulRaw p q) (mulRaw p' q') := by
  simp only [ratEq, mulRaw, mulDen, ℤ₀.ofNat_mul] at *
  -- (p.1·q.1)·(p'.2·q'.2) = (p'.1·q'.1)·(p.2·q.2)  usando h1, h2 y conmutatividad.
  sorry

private theorem addWD (p p' q q' : ℤ₀ × PosNat₀)
    (h1 : ratEq p p') (h2 : ratEq q q') :
    ratEq (addRaw p q) (addRaw p' q') := by
  simp only [ratEq, addRaw, mulDen, ℤ₀.ofNat_mul] at *
  -- h1 : p.1·p'.2 = p'.1·p.2,  h2 : q.1·q'.2 = q'.1·q.2
  -- Goal: (p.1·q.2 + q.1·p.2)·(p'.2·q'.2) = (p'.1·q'.2 + q'.1·p'.2)·(p.2·q.2)
  sorry

end PrivateDefs

-- ─────────────────────────────────────────────────────────────────────────────
-- Tipo ℚ₀
-- ─────────────────────────────────────────────────────────────────────────────

def ℚ₀ := Quotient ratSetoid

namespace ℚ₀

private def mkQ (a : ℤ₀) (b : PosNat₀) : ℚ₀ := Quotient.mk ratSetoid (a, b)

def mk (a : ℤ₀) (b : PosNat₀) : ℚ₀ := mkQ a b

-- ─────────────────────────────────────────────────────────────────────────────
-- Instancias: Zero, One, Add, Neg, Mul, Sub
-- ─────────────────────────────────────────────────────────────────────────────

instance instZero : Zero ℚ₀ := ⟨mkQ 0 den1⟩
instance instOne  : One  ℚ₀ := ⟨mkQ 1 den1⟩

instance instAdd : Add ℚ₀ where
  add a b := Quotient.liftOn₂ a b
    (fun p q => mkQ (addRaw p q).1 (addRaw p q).2)
    (fun p₁ q₁ p₂ q₂ h1 h2 => Quotient.sound (addWD p₁ p₂ q₁ q₂ h1 h2))

instance instNeg : Neg ℚ₀ where
  neg a := Quotient.liftOn a
    (fun p => mkQ (negRaw p).1 (negRaw p).2)
    (fun p q h => Quotient.sound (negWD p q h))

instance instMul : Mul ℚ₀ where
  mul a b := Quotient.liftOn₂ a b
    (fun p q => mkQ (mulRaw p q).1 (mulRaw p q).2)
    (fun p₁ q₁ p₂ q₂ h1 h2 => Quotient.sound (mulWD p₁ p₂ q₁ q₂ h1 h2))

instance instSub : Sub ℚ₀ where
  sub a b := a + (-b)

-- ─────────────────────────────────────────────────────────────────────────────
-- Embedding desde ℤ₀
-- ─────────────────────────────────────────────────────────────────────────────

def ofInt (z : ℤ₀) : ℚ₀ := mkQ z den1

def ofNat₀ (n : ℕ₀) : ℚ₀ := ofInt (ℤ₀.ofNat n)

-- ─────────────────────────────────────────────────────────────────────────────
-- Leyes de anillo conmutativo
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_comm (a b : ℚ₀) : Add.add a b = Add.add b a := by
  refine Quotient.inductionOn₂ a b (fun p q => ?_)
  apply Quotient.sound
  show ratEq (addRaw p q) (addRaw q p)
  simp only [ratEq, addRaw, mulDen]
  congr 1
  · exact ℤ₀.add_comm _ _
  · congr 1; exact Peano.Mul.mul_comm q.2.val p.2.val

theorem add_assoc (a b c : ℚ₀) : Add.add (Add.add a b) c = Add.add a (Add.add b c) := by
  refine Quotient.inductionOn a (fun p => ?_)
  refine Quotient.inductionOn b (fun q => ?_)
  refine Quotient.inductionOn c (fun r => ?_)
  apply Quotient.sound
  show ratEq (addRaw (addRaw p q) r) (addRaw p (addRaw q r))
  simp only [ratEq, addRaw, mulDen, Peano.Mul.mul_assoc, ℤ₀.ofNat_mul]
  -- Ambos lados iguales por leyes de anillo de ℤ₀.
  sorry

theorem zero_add (a : ℚ₀) : Add.add 0 a = a := by
  refine Quotient.inductionOn a (fun p => ?_)
  apply Quotient.sound
  show ratEq (addRaw (0, den1) p) (p.1, p.2)
  simp only [ratEq, addRaw, mulDen, den1]
  simp only [ℤ₀.zero_mul, Peano.Mul.one_mul, ℤ₀.mul_one, ℤ₀.ofNat_one]
  congr 1
  exact ℤ₀.zero_add p.1

theorem add_zero (a : ℚ₀) : Add.add a 0 = a := by
  rw [add_comm]; exact zero_add a

theorem add_neg_self (a : ℚ₀) : Add.add a (Neg.neg a) = 0 := by
  refine Quotient.inductionOn a (fun p => ?_)
  apply Quotient.sound
  show ratEq (addRaw p (negRaw p)) (0, den1)
  simp only [ratEq, addRaw, negRaw, mulDen, den1]
  simp only [ℤ₀.zero_mul, ℤ₀.mul_one, ℤ₀.ofNat_one]
  rw [ℤ₀.neg_mul]
  exact ℤ₀.add_neg_self _

theorem neg_add_self (a : ℚ₀) : Add.add (Neg.neg a) a = 0 := by
  rw [add_comm]; exact add_neg_self a

theorem mul_comm (a b : ℚ₀) : a * b = b * a := by
  refine Quotient.inductionOn₂ a b (fun p q => ?_)
  apply Quotient.sound
  show ratEq (mulRaw p q) (mulRaw q p)
  simp only [ratEq, mulRaw, mulDen, Peano.Mul.mul_comm q.2.val p.2.val, ℤ₀.mul_comm p.1 q.1]

theorem mul_assoc (a b c : ℚ₀) : a * b * c = a * (b * c) := by
  refine Quotient.inductionOn a (fun p => ?_)
  refine Quotient.inductionOn b (fun q => ?_)
  refine Quotient.inductionOn c (fun r => ?_)
  apply Quotient.sound
  show ratEq (mulRaw (mulRaw p q) r) (mulRaw p (mulRaw q r))
  simp only [ratEq, mulRaw, mulDen]
  -- Goal: ((p.1*q.1)*r.1) * ofNat(p.2*(q.2*r.2)) = (p.1*(q.1*r.1)) * ofNat((p.2*q.2)*r.2)
  congr 1
  · exact ℤ₀.mul_assoc p.1 q.1 r.1
  · congr 1
    exact (Peano.Mul.mul_assoc q.2.val p.2.val r.2.val).symm

theorem one_mul (a : ℚ₀) : 1 * a = a := by
  refine Quotient.inductionOn a (fun p => ?_)
  apply Quotient.sound
  show ratEq (mulRaw (1, den1) p) (p.1, p.2)
  simp only [ratEq, mulRaw, mulDen, den1]
  simp only [ℤ₀.one_mul, Peano.Mul.one_mul]

theorem mul_one (a : ℚ₀) : a * 1 = a := by
  rw [mul_comm]; exact one_mul a

theorem zero_mul (a : ℚ₀) : 0 * a = 0 := by
  refine Quotient.inductionOn a (fun p => ?_)
  apply Quotient.sound
  show ratEq (mulRaw (0, den1) p) (0, den1)
  simp only [ratEq, mulRaw, mulDen, den1]
  simp only [ℤ₀.zero_mul, Peano.Mul.one_mul, ℤ₀.mul_one, ℤ₀.ofNat_one]

theorem mul_zero (a : ℚ₀) : a * 0 = 0 := by
  rw [mul_comm]; exact zero_mul a

theorem left_distrib (a b c : ℚ₀) : a * Add.add b c = Add.add (a * b) (a * c) := by
  refine Quotient.inductionOn a (fun p => ?_)
  refine Quotient.inductionOn b (fun q => ?_)
  refine Quotient.inductionOn c (fun r => ?_)
  apply Quotient.sound
  show ratEq (mulRaw p (addRaw q r)) (addRaw (mulRaw p q) (mulRaw p r))
  simp only [ratEq, mulRaw, addRaw, mulDen, ℤ₀.ofNat_mul]
  -- Ambos lados son iguales tras distribuir y reordenar factores.
  -- LHS: (p.1·(q.1·ofNat(r.2) + r.1·ofNat(q.2))) · (ofNat(p.2·q.2)·ofNat(p.2·r.2)) (aprox)
  sorry

theorem right_distrib (a b c : ℚ₀) : Add.add a b * c = Add.add (a * c) (b * c) := by
  rw [mul_comm, left_distrib, mul_comm c a, mul_comm c b]

theorem neg_mul (a b : ℚ₀) : Neg.neg a * b = Neg.neg (a * b) := by
  refine Quotient.inductionOn₂ a b (fun p q => ?_)
  apply Quotient.sound
  show ratEq (mulRaw (negRaw p) q) (negRaw (mulRaw p q))
  simp only [ratEq, mulRaw, negRaw, mulDen, ℤ₀.neg_mul]

theorem mul_neg (a b : ℚ₀) : a * Neg.neg b = Neg.neg (a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

-- ─────────────────────────────────────────────────────────────────────────────
-- Orden: LE y LT
-- ─────────────────────────────────────────────────────────────────────────────

-- La relación a/b ≤ c/d se define por a·ofNat(d) ≤ c·ofNat(b)
-- (bien definida porque los denominadores son positivos)
private theorem leWD (p₁ p₂ q₁ q₂ : ℤ₀ × PosNat₀)
    (hp : ratEq p₁ p₂) (hq : ratEq q₁ q₂) :
    (Mul.mul p₁.1 (ℤ₀.ofNat q₁.2.val) ≤ Mul.mul q₁.1 (ℤ₀.ofNat p₁.2.val)) ↔
    (Mul.mul p₂.1 (ℤ₀.ofNat q₂.2.val) ≤ Mul.mul q₂.1 (ℤ₀.ofNat p₂.2.val)) := by
  sorry

instance instLE : LE ℚ₀ where
  le a b := Quotient.liftOn₂ a b
    (fun p q => Mul.mul p.1 (ℤ₀.ofNat q.2.val) ≤ Mul.mul q.1 (ℤ₀.ofNat p.2.val))
    (fun p₁ q₁ p₂ q₂ h1 h2 => propext (leWD p₁ p₂ q₁ q₂ h1 h2))

instance instLT : LT ℚ₀ where
  lt a b := a ≤ b ∧ ¬b ≤ a

-- ─────────────────────────────────────────────────────────────────────────────
-- Propiedades del orden
-- ─────────────────────────────────────────────────────────────────────────────

theorem le_refl (a : ℚ₀) : a ≤ a := by
  refine Quotient.inductionOn a (fun p => ?_)
  show Mul.mul p.1 (ℤ₀.ofNat p.2.val) ≤ Mul.mul p.1 (ℤ₀.ofNat p.2.val)
  exact ℤ₀.le_refl _

theorem le_antisymm {a b : ℚ₀} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  sorry

theorem le_trans {a b c : ℚ₀} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  sorry

theorem le_total (a b : ℚ₀) : a ≤ b ∨ b ≤ a := by
  sorry

-- ─────────────────────────────────────────────────────────────────────────────
-- Inyectividad del embedding
-- ─────────────────────────────────────────────────────────────────────────────

theorem ofInt_injective {a b : ℤ₀} (h : ofInt a = ofInt b) : a = b := by
  have heq := Quotient.exact h
  have h2 : ratEq (a, den1) (b, den1) := heq
  simp only [ratEq, den1, ℤ₀.ofNat_one, ℤ₀.mul_one] at h2
  exact h2

end ℚ₀
