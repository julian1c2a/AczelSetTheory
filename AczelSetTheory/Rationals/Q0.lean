/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/HFRat.lean
--
-- HFRat: Tipo canónico para los racionales.
-- Encapsula un ℚ₀ junto con su representante canónico en ℚ₀', transformando
-- las igualdades observacionales en proposicionales por reflexividad.

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Canonical
import AczelSetTheory.Rationals.AbsVal
import AczelSetTheory.Integers.HFInt
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Primes

open Peano

namespace HFInt

/-- Valor absoluto de HFInt como natural. -/
def absNat (a : HFInt) : ℕ₀ := ℤ₀.toNat (ℤ₀.abs a.cls)

/-- Decidibilidad de igualdad con 0. -/
instance (a : HFInt) : Decidable (a = 0) := instDecidableEq a 0

end HFInt

/-- El conjunto de representantes canónicos para los racionales. -/
def ℚ₀' := { p : HFInt × ℕ₁ // (p.1 = 0 ∧ p.2.val = 𝟙) ∨ (p.1 ≠ 0 ∧ Peano.Arith.gcd (p.1.absNat) p.2.val = 𝟙) }

namespace ℚ₀'

theorem gcd_eq_one_of_coprime {a b : ℕ₀} (h : Peano.Arith.Coprime a b) : Peano.Arith.gcd a b = 𝟙 := by
  have hg := Peano.Arith.IsGCD_gcd a b
  have hd : Peano.Arith.gcd a b ∣ 𝟙 := h.2.2 (Peano.Arith.gcd a b) ⟨hg.1, hg.2.1⟩
  rcases hd with ⟨c, hc⟩
  exact (Peano.Primes.mul_eq_one hc.symm).1

def ofQ0 (q : ℚ₀) : ℚ₀' :=
  let r := ℚ₀.repr q
  let n : HFInt := HFInt.ofZ0 r.1
  let d : ℕ₁ := r.2
  have h_gcd : Peano.Arith.gcd n.absNat d.val = 𝟙 := gcd_eq_one_of_coprime (ℚ₀.repr_reduced q)
  ⟨(n, d), by
    by_cases hn : n = 0
    · left
      have hn_cls : n.cls = 0 := by
        have hz : (0 : HFInt).cls = 0 := rfl
        rw [← hz]
        exact congrArg HFInt.cls hn
      have hn_abs : n.absNat = 𝟘 := by
        unfold HFInt.absNat
        rw [hn_cls]
        have ha0 : ℤ₀.abs 0 = 0 := ℤ₀.abs_eq_zero_iff.mpr rfl
        have hz : (0 : ℤ₀) = ℤ₀.ofNat 0 := rfl
        rw [ha0, hz]
        exact ℤ₀.toNat_ofNat 0
      have hd1 : d.val = 𝟙 := by
        rw [hn_abs, Peano.Arith.gcd_zero_left d.val] at h_gcd
        exact h_gcd
      exact ⟨hn, hd1⟩
    · right
      exact ⟨hn, h_gcd⟩⟩

def toQ0 (p : ℚ₀') : ℚ₀ := ℚ₀.mk p.val.1.cls p.val.2

theorem toQ0_ofQ0 (q : ℚ₀) : toQ0 (ofQ0 q) = q := ℚ₀.mk_repr q

theorem div_one (a : ℕ₀) : a / 𝟙 = a := by
  change Peano.Div.div a 𝟙 = a
  unfold Peano.Div.div Peano.Div.divMod
  split
  · contradiction
  · split
    · rw [‹a = 𝟘›]
    · split
      · rfl
      · contradiction

private theorem reduce_id (p : ℤ₀ × ℕ₁)
    (h : (p.1 = 0 ∧ p.2.val = 𝟙) ∨ (p.1 ≠ 0 ∧ Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = 𝟙)) :
    ℚ₀.reduce p = p := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h_abs : ℤ₀.toNat (ℤ₀.abs p.1) = 𝟘 := by
      rw [h1, ℤ₀.abs_eq_zero_iff.mpr rfl]
      have hz : (0 : ℤ₀) = ℤ₀.ofNat 0 := rfl
      rw [hz]
      exact ℤ₀.toNat_ofNat 0
    have h_gcd : Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = 𝟙 := by
      rw [h_abs, h2, Peano.Arith.gcd_zero_left]
    apply Prod.ext
    · change Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1) / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)) = p.1
      rw [h1, ℤ₀.sign_zero, ℤ₀.zero_mul]
    · apply Subtype.ext
      change p.2.val / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = p.2.val
      rw [h_gcd, div_one]
  · apply Prod.ext
    · change Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1) / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val)) = p.1
      have hs : p.1 = Mul.mul (ℤ₀.sign p.1) (ℤ₀.ofNat (ℤ₀.toNat (ℤ₀.abs p.1))) :=
        ℚ₀.self_eq_sign_mul_toNat_abs p.1
      rw [h2, div_one]
      exact hs.symm
    · apply Subtype.ext
      change p.2.val / Peano.Arith.gcd (ℤ₀.toNat (ℤ₀.abs p.1)) p.2.val = p.2.val
      rw [h2, div_one]

theorem ofQ0_toQ0 (p : ℚ₀') : ofQ0 (toQ0 p) = p := by
  have H : ℚ₀.repr (toQ0 p) = (p.val.1.cls, p.val.2) := by
    change ℚ₀.reduce (p.val.1.cls, p.val.2) = (p.val.1.cls, p.val.2)
    apply reduce_id
    have hp := p.property
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have h1_cls : p.val.1.cls = 0 := by
        have h_cls : p.val.1.cls = (0 : HFInt).cls := by rw [h1]
        exact h_cls
      exact ⟨h1_cls, h2⟩
    · right
      have h1_cls : p.val.1.cls ≠ 0 := by
        intro h
        apply h1
        apply HFInt.ext
        exact h
      exact ⟨h1_cls, h2⟩
  apply Subtype.ext
  apply Prod.ext
  · apply HFInt.ext
    change (HFInt.ofZ0 (ℚ₀.repr (toQ0 p)).1).cls = p.val.1.cls
    rw [H]
    rfl
  · change (ℚ₀.repr (toQ0 p)).2 = p.val.2
    rw [H]

instance : Zero ℚ₀' where zero := ofQ0 0
instance : One  ℚ₀' where one  := ofQ0 1
instance : Add  ℚ₀' where add a b := ofQ0 (Add.add (toQ0 a) (toQ0 b))
instance : Mul  ℚ₀' where mul a b := ofQ0 (Mul.mul (toQ0 a) (toQ0 b))
instance : Neg  ℚ₀' where neg a := ofQ0 (Neg.neg (toQ0 a))
instance : Sub  ℚ₀' where sub a b := ofQ0 (Sub.sub (toQ0 a) (toQ0 b))

instance : LE ℚ₀' where le a b := toQ0 a ≤ toQ0 b
instance : LT ℚ₀' where lt a b := toQ0 a < toQ0 b

instance instDecidableEq (a b : ℚ₀') : Decidable (a = b) :=
  match decEq (toQ0 a) (toQ0 b) with
  | isTrue h  => isTrue (by rw [←ofQ0_toQ0 a, ←ofQ0_toQ0 b, h])
  | isFalse h => isFalse (fun heq => h (by rw [heq]))

instance instDecidableLE (a b : ℚ₀') : Decidable (a ≤ b) := inferInstanceAs (Decidable (toQ0 a ≤ toQ0 b))
instance instDecidableLT (a b : ℚ₀') : Decidable (a < b) := inferInstanceAs (Decidable (toQ0 a < toQ0 b))

theorem add_comm (a b : ℚ₀') : Add.add a b = Add.add b a := by
  change ofQ0 (Add.add (toQ0 a) (toQ0 b)) = ofQ0 (Add.add (toQ0 b) (toQ0 a))
  rw [ℚ₀.add_comm]

theorem add_assoc (a b c : ℚ₀') : Add.add (Add.add a b) c = Add.add a (Add.add b c) := by
  change ofQ0 (Add.add (toQ0 (ofQ0 (Add.add (toQ0 a) (toQ0 b)))) (toQ0 c)) =
         ofQ0 (Add.add (toQ0 a) (toQ0 (ofQ0 (Add.add (toQ0 b) (toQ0 c)))))
  rw [toQ0_ofQ0, toQ0_ofQ0, ℚ₀.add_assoc]

end ℚ₀'

/-- La estructura HFRat agrupa la clase de equivalencia ℚ₀ y su representante canónico ℚ₀'. -/
structure HFRat where
  cls  : ℚ₀
  pair : ℚ₀'
  hEq  : ℚ₀'.toQ0 pair = cls

namespace HFRat

/-- Construye un HFRat a partir de su clase de equivalencia ℚ₀.
    (Por ahora esto usa el mismo par canónico para mantener las propiedades de ambas clases,
    para poder explorar la ergonomía de los teoremas primero). -/
def ofQ0 (q : ℚ₀) : HFRat where
  cls  := q
  pair := ℚ₀'.ofQ0 q
  hEq  := ℚ₀'.toQ0_ofQ0 q

/-- Construye un HFRat a partir de su representante canónico ℚ₀'. -/
def ofQ0' (p : ℚ₀') : HFRat where
  cls  := ℚ₀'.toQ0 p
  pair := p
  hEq  := rfl

/-- Dos HFRat son iguales si sus clases subyacentes son iguales. -/
@[ext]
theorem ext (a b : HFRat) (h : a.cls = b.cls) : a = b := by
  -- La igualdad de las clases implica la igualdad de los pares canónicos.
  have h_pair : a.pair = b.pair := by
    rw [← ℚ₀'.ofQ0_toQ0 a.pair, ← ℚ₀'.ofQ0_toQ0 b.pair]
    have ha : ℚ₀'.toQ0 a.pair = a.cls := a.hEq
    have hb : ℚ₀'.toQ0 b.pair = b.cls := b.hEq
    rw [ha, hb, h]
  cases a
  cases b
  simp only [mk.injEq]
  constructor
  · exact h
  · exact h_pair

-- ─────────────────────────────────────────────────────────────────────────────
-- Instancias Algebraicas
-- ─────────────────────────────────────────────────────────────────────────────

instance : Zero HFRat where zero := ofQ0 0
instance : One  HFRat where one  := ofQ0 1
instance : Add HFRat where
  add a b :=
    { cls  := a.cls + b.cls
      pair := a.pair + b.pair
      hEq  := by
        change ℚ₀'.toQ0 (ℚ₀'.ofQ0 (ℚ₀'.toQ0 a.pair + ℚ₀'.toQ0 b.pair)) = a.cls + b.cls
        rw [ℚ₀'.toQ0_ofQ0, a.hEq, b.hEq] }

instance : Mul HFRat where
  mul a b :=
    { cls  := a.cls * b.cls
      pair := a.pair * b.pair
      hEq  := by
        change ℚ₀'.toQ0 (ℚ₀'.ofQ0 (ℚ₀'.toQ0 a.pair * ℚ₀'.toQ0 b.pair)) = a.cls * b.cls
        rw [ℚ₀'.toQ0_ofQ0, a.hEq, b.hEq] }

instance : Neg HFRat where
  neg a :=
    { cls  := -a.cls
      pair := -a.pair
      hEq  := by
        change ℚ₀'.toQ0 (ℚ₀'.ofQ0 (-ℚ₀'.toQ0 a.pair)) = -a.cls
        rw [ℚ₀'.toQ0_ofQ0, a.hEq] }

instance : Sub HFRat where
  sub a b :=
    { cls  := a.cls - b.cls
      pair := a.pair - b.pair
      hEq  := by
        change ℚ₀'.toQ0 (ℚ₀'.ofQ0 (ℚ₀'.toQ0 a.pair - ℚ₀'.toQ0 b.pair)) = a.cls - b.cls
        rw [ℚ₀'.toQ0_ofQ0, a.hEq, b.hEq] }

-- ─────────────────────────────────────────────────────────────────────────────
-- Lemas de anillo (heredados trivialmente de ℚ₀)
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_comm (a b : HFRat) : Add.add a b = Add.add b a := by
  apply ext
  exact ℚ₀.add_comm a.cls b.cls

theorem add_assoc (a b c : HFRat) : Add.add (Add.add a b) c = Add.add a (Add.add b c) := by
  apply ext
  exact ℚ₀.add_assoc a.cls b.cls c.cls

theorem zero_add (a : HFRat) : Add.add 0 a = a := by
  apply ext
  exact ℚ₀.zero_add a.cls

theorem add_zero (a : HFRat) : Add.add a 0 = a := by
  apply ext
  exact ℚ₀.add_zero a.cls

theorem add_neg_self (a : HFRat) : Add.add a (Neg.neg a) = 0 := by
  apply ext
  exact ℚ₀.add_neg_self a.cls

theorem neg_add_self (a : HFRat) : Add.add (Neg.neg a) a = 0 := by
  apply ext
  exact ℚ₀.neg_add_self a.cls

theorem mul_comm (a b : HFRat) : Mul.mul a b = Mul.mul b a := by
  apply ext
  exact ℚ₀.mul_comm a.cls b.cls

theorem mul_assoc (a b c : HFRat) : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c) := by
  apply ext
  exact ℚ₀.mul_assoc a.cls b.cls c.cls

theorem one_mul (a : HFRat) : Mul.mul 1 a = a := by
  apply ext
  exact ℚ₀.one_mul a.cls

theorem mul_one (a : HFRat) : Mul.mul a 1 = a := by
  apply ext
  exact ℚ₀.mul_one a.cls

theorem zero_mul (a : HFRat) : Mul.mul 0 a = 0 := by
  apply ext
  exact ℚ₀.zero_mul a.cls

theorem mul_zero (a : HFRat) : Mul.mul a 0 = 0 := by
  apply ext
  exact ℚ₀.mul_zero a.cls

theorem left_distrib (a b c : HFRat) : Mul.mul a (Add.add b c) = Add.add (Mul.mul a b) (Mul.mul a c) := by
  apply ext
  exact ℚ₀.left_distrib a.cls b.cls c.cls

theorem right_distrib (a b c : HFRat) : Mul.mul (Add.add a b) c = Add.add (Mul.mul a c) (Mul.mul b c) := by
  apply ext
  exact ℚ₀.right_distrib a.cls b.cls c.cls

theorem neg_mul (a b : HFRat) : Mul.mul (Neg.neg a) b = Neg.neg (Mul.mul a b) := by
  apply ext
  exact ℚ₀.neg_mul a.cls b.cls

theorem mul_neg (a b : HFRat) : Mul.mul a (Neg.neg b) = Neg.neg (Mul.mul a b) := by
  apply ext
  exact ℚ₀.mul_neg a.cls b.cls

instance instDecidableEq (a b : HFRat) : Decidable (a = b) :=
  match decEq a.cls b.cls with
  | isTrue h  => isTrue (ext a b h)
  | isFalse h => isFalse (fun heq => h (by rw [heq]))

instance : LE HFRat where le a b := a.cls ≤ b.cls
instance : LT HFRat where lt a b := a.cls < b.cls

theorem le_pair_iff (a b : HFRat) : a ≤ b ↔ a.pair ≤ b.pair := by
  change a.cls ≤ b.cls ↔ ℚ₀'.toQ0 a.pair ≤ ℚ₀'.toQ0 b.pair
  rw [a.hEq, b.hEq]

theorem lt_pair_iff (a b : HFRat) : a < b ↔ a.pair < b.pair := by
  change a.cls < b.cls ↔ ℚ₀'.toQ0 a.pair < ℚ₀'.toQ0 b.pair
  rw [a.hEq, b.hEq]

instance instDecidableLE (a b : HFRat) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.cls ≤ b.cls))
instance instDecidableLT (a b : HFRat) : Decidable (a < b) := inferInstanceAs (Decidable (a.cls < b.cls))

-- ─────────────────────────────────────────────────────────────────────────────
-- Valor Absoluto
-- ─────────────────────────────────────────────────────────────────────────────

def absVal (q : HFRat) : HFRat := ofQ0 (ℚ₀.absVal q.cls)

-- ─────────────────────────────────────────────────────────────────────────────
-- Subtipos Estructurados
-- ─────────────────────────────────────────────────────────────────────────────

/-- Elementos no nulos (HFRat^*) -/
def NonZero := { x : HFRat // x ≠ 0 }

/-- Unidades de HFRat (coincide con NonZero al ser un cuerpo) -/
abbrev Units := NonZero

/-- Kernel de HFRat (0, 1 y -1) -/
def Kernel := { x : HFRat // x = 0 ∨ x = 1 ∨ x = -1 }

/-- Elementos fuera del kernel -/
def OutKernel := { x : HFRat // x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 }

/-- Estrictamente positivos -/
def Pos := { x : HFRat // 0 < x }

/-- Estrictamente negativos -/
def Neg := { x : HFRat // x < 0 }

/-- No negativos -/
def NonNeg := { x : HFRat // 0 ≤ x }

/-- Racionales con módulo estrictamente entre 0 y 1 -/
def PuncturedUnitBall := { x : HFRat // 0 < absVal x ∧ absVal x < 1 }

/-- Racionales con módulo mayor que 1 -/
def OutsideBall := { x : HFRat // 1 < absVal x }

-- Coerciones para usar los subtipos como HFRat directamente
instance : Coe NonZero HFRat where coe := Subtype.val
instance : Coe Kernel HFRat where coe := Subtype.val
instance : Coe OutKernel HFRat where coe := Subtype.val
instance : Coe Pos HFRat where coe := Subtype.val
instance : Coe Neg HFRat where coe := Subtype.val
instance : Coe NonNeg HFRat where coe := Subtype.val
instance : Coe PuncturedUnitBall HFRat where coe := Subtype.val
instance : Coe OutsideBall HFRat where coe := Subtype.val

end HFRat
