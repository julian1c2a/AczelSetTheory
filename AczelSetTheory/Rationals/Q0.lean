/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/ℚ₀.lean
--
-- ℚ₀: Tipo canónico para los racionales.
-- Encapsula un ℚ₀cls junto con su representante canónico en ℚ₀can, transformando
-- las igualdades observacionales en proposicionales por reflexividad.

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Canonical
import AczelSetTheory.Rationals.AbsVal
import AczelSetTheory.Integers.Z0
import Peano.PeanoNat.Arith
import Peano.PeanoNat.Primes

open Peano

namespace ℤ₀

/-- Valor absoluto de ℤ₀ como natural. -/
def absNat (a : ℤ₀) : ℕ₀ := ℤ₀cls.toNat (ℤ₀cls.abs a.cls)

/-- Decidibilidad de igualdad con 0. -/
instance (a : ℤ₀) : Decidable (a = 0) := instDecidableEq a 0

end ℤ₀

/-- El conjunto de representantes canónicos para los racionales. -/
def ℚ₀can := { p : ℤ₀ × ℕ₁ // (p.1 = 0 ∧ p.2.val = 𝟙) ∨ (p.1 ≠ 0 ∧ Peano.Arith.gcd (p.1.absNat) p.2.val = 𝟙) }

namespace ℚ₀can

theorem gcd_eq_one_of_coprime {a b : ℕ₀} (h : Peano.Arith.Coprime a b) : Peano.Arith.gcd a b = 𝟙 := by
  have hg := Peano.Arith.IsGCD_gcd a b
  have hd : Peano.Arith.gcd a b ∣ 𝟙 := h.2.2 (Peano.Arith.gcd a b) ⟨hg.1, hg.2.1⟩
  rcases hd with ⟨c, hc⟩
  exact (Peano.Primes.mul_eq_one hc.symm).1

def ofCls (q : ℚ₀cls) : ℚ₀can :=
  let r := ℚ₀cls.repr q
  let n : ℤ₀ := ℤ₀.ofCls r.1
  let d : ℕ₁ := r.2
  have h_gcd : Peano.Arith.gcd n.absNat d.val = 𝟙 := gcd_eq_one_of_coprime (ℚ₀cls.repr_reduced q)
  ⟨(n, d), by
    by_cases hn : n = 0
    · left
      have hn_cls : n.cls = 0 := by
        have hz : (0 : ℤ₀).cls = 0 := rfl
        rw [← hz]
        exact congrArg ℤ₀.cls hn
      have hn_abs : n.absNat = 𝟘 := by
        unfold ℤ₀.absNat
        rw [hn_cls]
        have ha0 : ℤ₀cls.abs 0 = 0 := ℤ₀cls.abs_eq_zero_iff.mpr rfl
        have hz : (0 : ℤ₀cls) = ℤ₀cls.ofNat 0 := rfl
        rw [ha0, hz]
        exact ℤ₀cls.toNat_ofNat 0
      have hd1 : d.val = 𝟙 := by
        rw [hn_abs, Peano.Arith.gcd_zero_left d.val] at h_gcd
        exact h_gcd
      exact ⟨hn, hd1⟩
    · right
      exact ⟨hn, h_gcd⟩⟩

def toCls (p : ℚ₀can) : ℚ₀cls := ℚ₀cls.mk p.val.1.cls p.val.2

theorem toCls_ofCls (q : ℚ₀cls) : toCls (ofCls q) = q := ℚ₀cls.mk_repr q

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

private theorem reduce_id (p : ℤ₀cls × ℕ₁)
    (h : (p.1 = 0 ∧ p.2.val = 𝟙) ∨ (p.1 ≠ 0 ∧ Peano.Arith.gcd (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val = 𝟙)) :
    ℚ₀cls.reduce p = p := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h_abs : ℤ₀cls.toNat (ℤ₀cls.abs p.1) = 𝟘 := by
      rw [h1, ℤ₀cls.abs_eq_zero_iff.mpr rfl]
      have hz : (0 : ℤ₀cls) = ℤ₀cls.ofNat 0 := rfl
      rw [hz]
      exact ℤ₀cls.toNat_ofNat 0
    have h_gcd : Peano.Arith.gcd (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val = 𝟙 := by
      rw [h_abs, h2, Peano.Arith.gcd_zero_left]
    apply Prod.ext
    · change Mul.mul (ℤ₀cls.sign p.1) (ℤ₀cls.ofNat (ℤ₀cls.toNat (ℤ₀cls.abs p.1) / Peano.Arith.gcd (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val)) = p.1
      rw [h1, ℤ₀cls.sign_zero, ℤ₀cls.zero_mul]
    · apply Subtype.ext
      change p.2.val / Peano.Arith.gcd (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val = p.2.val
      rw [h_gcd, div_one]
  · apply Prod.ext
    · change Mul.mul (ℤ₀cls.sign p.1) (ℤ₀cls.ofNat (ℤ₀cls.toNat (ℤ₀cls.abs p.1) / Peano.Arith.gcd (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val)) = p.1
      have hs : p.1 = Mul.mul (ℤ₀cls.sign p.1) (ℤ₀cls.ofNat (ℤ₀cls.toNat (ℤ₀cls.abs p.1))) :=
        ℚ₀cls.self_eq_sign_mul_toNat_abs p.1
      rw [h2, div_one]
      exact hs.symm
    · apply Subtype.ext
      change p.2.val / Peano.Arith.gcd (ℤ₀cls.toNat (ℤ₀cls.abs p.1)) p.2.val = p.2.val
      rw [h2, div_one]

theorem ofCls_toCls (p : ℚ₀can) : ofCls (toCls p) = p := by
  have H : ℚ₀cls.repr (toCls p) = (p.val.1.cls, p.val.2) := by
    change ℚ₀cls.reduce (p.val.1.cls, p.val.2) = (p.val.1.cls, p.val.2)
    apply reduce_id
    have hp := p.property
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have h1_cls : p.val.1.cls = 0 := by
        have h_cls : p.val.1.cls = (0 : ℤ₀).cls := by rw [h1]
        exact h_cls
      exact ⟨h1_cls, h2⟩
    · right
      have h1_cls : p.val.1.cls ≠ 0 := by
        intro h
        apply h1
        apply ℤ₀.ext
        exact h
      exact ⟨h1_cls, h2⟩
  apply Subtype.ext
  apply Prod.ext
  · apply ℤ₀.ext
    change (ℤ₀.ofCls (ℚ₀cls.repr (toCls p)).1).cls = p.val.1.cls
    rw [H]
    rfl
  · change (ℚ₀cls.repr (toCls p)).2 = p.val.2
    rw [H]

instance : Zero ℚ₀can where zero := ofCls 0
instance : One  ℚ₀can where one  := ofCls 1
instance : Add  ℚ₀can where add a b := ofCls (Add.add (toCls a) (toCls b))
instance : Mul  ℚ₀can where mul a b := ofCls (Mul.mul (toCls a) (toCls b))
instance : Neg  ℚ₀can where neg a := ofCls (Neg.neg (toCls a))
instance : Sub  ℚ₀can where sub a b := ofCls (Sub.sub (toCls a) (toCls b))

instance : LE ℚ₀can where le a b := toCls a ≤ toCls b
instance : LT ℚ₀can where lt a b := toCls a < toCls b

instance instDecidableEq (a b : ℚ₀can) : Decidable (a = b) :=
  match decEq (toCls a) (toCls b) with
  | isTrue h  => isTrue (by rw [←ofCls_toCls a, ←ofCls_toCls b, h])
  | isFalse h => isFalse (fun heq => h (by rw [heq]))

instance instDecidableLE (a b : ℚ₀can) : Decidable (a ≤ b) := inferInstanceAs (Decidable (toCls a ≤ toCls b))
instance instDecidableLT (a b : ℚ₀can) : Decidable (a < b) := inferInstanceAs (Decidable (toCls a < toCls b))

theorem add_comm (a b : ℚ₀can) : Add.add a b = Add.add b a := by
  change ofCls (Add.add (toCls a) (toCls b)) = ofCls (Add.add (toCls b) (toCls a))
  rw [ℚ₀cls.add_comm]

theorem add_assoc (a b c : ℚ₀can) : Add.add (Add.add a b) c = Add.add a (Add.add b c) := by
  change ofCls (Add.add (toCls (ofCls (Add.add (toCls a) (toCls b)))) (toCls c)) =
         ofCls (Add.add (toCls a) (toCls (ofCls (Add.add (toCls b) (toCls c)))))
  rw [toCls_ofCls, toCls_ofCls, ℚ₀cls.add_assoc]

end ℚ₀can

/-- La estructura ℚ₀ agrupa la clase de equivalencia ℚ₀cls y su representante canónico ℚ₀can. -/
structure ℚ₀ where
  cls  : ℚ₀cls
  pair : ℚ₀can
  hEq  : ℚ₀can.toCls pair = cls

namespace ℚ₀

/-- Construye un ℚ₀ a partir de su clase de equivalencia ℚ₀cls.
    (Por ahora esto usa el mismo par canónico para mantener las propiedades de ambas clases,
    para poder explorar la ergonomía de los teoremas primero). -/
def ofCls (q : ℚ₀cls) : ℚ₀ where
  cls  := q
  pair := ℚ₀can.ofCls q
  hEq  := ℚ₀can.toCls_ofCls q

/-- Construye un ℚ₀ a partir de su representante canónico ℚ₀can. -/
def ofCls' (p : ℚ₀can) : ℚ₀ where
  cls  := ℚ₀can.toCls p
  pair := p
  hEq  := rfl

/-- Dos ℚ₀ son iguales si sus clases subyacentes son iguales. -/
@[ext]
theorem ext (a b : ℚ₀) (h : a.cls = b.cls) : a = b := by
  -- La igualdad de las clases implica la igualdad de los pares canónicos.
  have h_pair : a.pair = b.pair := by
    rw [← ℚ₀can.ofCls_toCls a.pair, ← ℚ₀can.ofCls_toCls b.pair]
    have ha : ℚ₀can.toCls a.pair = a.cls := a.hEq
    have hb : ℚ₀can.toCls b.pair = b.cls := b.hEq
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

instance : Zero ℚ₀ where zero := ofCls 0
instance : One  ℚ₀ where one  := ofCls 1
instance : Add ℚ₀ where
  add a b :=
    { cls  := a.cls + b.cls
      pair := a.pair + b.pair
      hEq  := by
        change ℚ₀can.toCls (ℚ₀can.ofCls (ℚ₀can.toCls a.pair + ℚ₀can.toCls b.pair)) = a.cls + b.cls
        rw [ℚ₀can.toCls_ofCls, a.hEq, b.hEq] }

instance : Mul ℚ₀ where
  mul a b :=
    { cls  := a.cls * b.cls
      pair := a.pair * b.pair
      hEq  := by
        change ℚ₀can.toCls (ℚ₀can.ofCls (ℚ₀can.toCls a.pair * ℚ₀can.toCls b.pair)) = a.cls * b.cls
        rw [ℚ₀can.toCls_ofCls, a.hEq, b.hEq] }

instance : Neg ℚ₀ where
  neg a :=
    { cls  := -a.cls
      pair := -a.pair
      hEq  := by
        change ℚ₀can.toCls (ℚ₀can.ofCls (-ℚ₀can.toCls a.pair)) = -a.cls
        rw [ℚ₀can.toCls_ofCls, a.hEq] }

instance : Sub ℚ₀ where
  sub a b :=
    { cls  := a.cls - b.cls
      pair := a.pair - b.pair
      hEq  := by
        change ℚ₀can.toCls (ℚ₀can.ofCls (ℚ₀can.toCls a.pair - ℚ₀can.toCls b.pair)) = a.cls - b.cls
        rw [ℚ₀can.toCls_ofCls, a.hEq, b.hEq] }

-- ─────────────────────────────────────────────────────────────────────────────
-- Lemas de anillo (heredados trivialmente de ℚ₀cls)
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_comm (a b : ℚ₀) : Add.add a b = Add.add b a := by
  apply ext
  exact ℚ₀cls.add_comm a.cls b.cls

theorem add_assoc (a b c : ℚ₀) : Add.add (Add.add a b) c = Add.add a (Add.add b c) := by
  apply ext
  exact ℚ₀cls.add_assoc a.cls b.cls c.cls

theorem zero_add (a : ℚ₀) : Add.add 0 a = a := by
  apply ext
  exact ℚ₀cls.zero_add a.cls

theorem add_zero (a : ℚ₀) : Add.add a 0 = a := by
  apply ext
  exact ℚ₀cls.add_zero a.cls

theorem add_neg_self (a : ℚ₀) : Add.add a (Neg.neg a) = 0 := by
  apply ext
  exact ℚ₀cls.add_neg_self a.cls

theorem neg_add_self (a : ℚ₀) : Add.add (Neg.neg a) a = 0 := by
  apply ext
  exact ℚ₀cls.neg_add_self a.cls

theorem mul_comm (a b : ℚ₀) : Mul.mul a b = Mul.mul b a := by
  apply ext
  exact ℚ₀cls.mul_comm a.cls b.cls

theorem mul_assoc (a b c : ℚ₀) : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c) := by
  apply ext
  exact ℚ₀cls.mul_assoc a.cls b.cls c.cls

theorem one_mul (a : ℚ₀) : Mul.mul 1 a = a := by
  apply ext
  exact ℚ₀cls.one_mul a.cls

theorem mul_one (a : ℚ₀) : Mul.mul a 1 = a := by
  apply ext
  exact ℚ₀cls.mul_one a.cls

theorem zero_mul (a : ℚ₀) : Mul.mul 0 a = 0 := by
  apply ext
  exact ℚ₀cls.zero_mul a.cls

theorem mul_zero (a : ℚ₀) : Mul.mul a 0 = 0 := by
  apply ext
  exact ℚ₀cls.mul_zero a.cls

theorem left_distrib (a b c : ℚ₀) : Mul.mul a (Add.add b c) = Add.add (Mul.mul a b) (Mul.mul a c) := by
  apply ext
  exact ℚ₀cls.left_distrib a.cls b.cls c.cls

theorem right_distrib (a b c : ℚ₀) : Mul.mul (Add.add a b) c = Add.add (Mul.mul a c) (Mul.mul b c) := by
  apply ext
  exact ℚ₀cls.right_distrib a.cls b.cls c.cls

theorem neg_mul (a b : ℚ₀) : Mul.mul (Neg.neg a) b = Neg.neg (Mul.mul a b) := by
  apply ext
  exact ℚ₀cls.neg_mul a.cls b.cls

theorem mul_neg (a b : ℚ₀) : Mul.mul a (Neg.neg b) = Neg.neg (Mul.mul a b) := by
  apply ext
  exact ℚ₀cls.mul_neg a.cls b.cls

instance instDecidableEq (a b : ℚ₀) : Decidable (a = b) :=
  match decEq a.cls b.cls with
  | isTrue h  => isTrue (ext a b h)
  | isFalse h => isFalse (fun heq => h (by rw [heq]))

instance : LE ℚ₀ where le a b := a.cls ≤ b.cls
instance : LT ℚ₀ where lt a b := a.cls < b.cls

theorem le_pair_iff (a b : ℚ₀) : a ≤ b ↔ a.pair ≤ b.pair := by
  change a.cls ≤ b.cls ↔ ℚ₀can.toCls a.pair ≤ ℚ₀can.toCls b.pair
  rw [a.hEq, b.hEq]

theorem lt_pair_iff (a b : ℚ₀) : a < b ↔ a.pair < b.pair := by
  change a.cls < b.cls ↔ ℚ₀can.toCls a.pair < ℚ₀can.toCls b.pair
  rw [a.hEq, b.hEq]

instance instDecidableLE (a b : ℚ₀) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.cls ≤ b.cls))
instance instDecidableLT (a b : ℚ₀) : Decidable (a < b) := inferInstanceAs (Decidable (a.cls < b.cls))

-- ─────────────────────────────────────────────────────────────────────────────
-- Valor Absoluto
-- ─────────────────────────────────────────────────────────────────────────────

def absVal (q : ℚ₀) : ℚ₀ := ofCls (ℚ₀cls.absVal q.cls)

-- ─────────────────────────────────────────────────────────────────────────────
-- Subtipos Estructurados
-- ─────────────────────────────────────────────────────────────────────────────

/-- Elementos no nulos (ℚ₀^*) -/
def NonZero := { x : ℚ₀ // x ≠ 0 }

/-- Unidades de ℚ₀ (coincide con NonZero al ser un cuerpo) -/
abbrev Units := NonZero

/-- Kernel de ℚ₀ (0, 1 y -1) -/
def Kernel := { x : ℚ₀ // x = 0 ∨ x = 1 ∨ x = -1 }

/-- Elementos fuera del kernel -/
def OutKernel := { x : ℚ₀ // x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 }

/-- Estrictamente positivos -/
def Pos := { x : ℚ₀ // 0 < x }

/-- Estrictamente negativos -/
def Neg := { x : ℚ₀ // x < 0 }

/-- No negativos -/
def NonNeg := { x : ℚ₀ // 0 ≤ x }

/-- Racionales con módulo estrictamente entre 0 y 1 -/
def PuncturedUnitBall := { x : ℚ₀ // 0 < absVal x ∧ absVal x < 1 }

/-- Racionales con módulo mayor que 1 -/
def OutsideBall := { x : ℚ₀ // 1 < absVal x }

-- Coerciones para usar los subtipos como ℚ₀ directamente
instance : Coe NonZero ℚ₀ where coe := Subtype.val
instance : Coe Kernel ℚ₀ where coe := Subtype.val
instance : Coe OutKernel ℚ₀ where coe := Subtype.val
instance : Coe Pos ℚ₀ where coe := Subtype.val
instance : Coe Neg ℚ₀ where coe := Subtype.val
instance : Coe NonNeg ℚ₀ where coe := Subtype.val
instance : Coe PuncturedUnitBall ℚ₀ where coe := Subtype.val
instance : Coe OutsideBall ℚ₀ where coe := Subtype.val

end ℚ₀
