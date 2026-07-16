/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/HFInt.lean
--
-- HFInt: Tipo canónico para los enteros.
-- Encapsula un ℤ₀ junto con su par representante canónico en ℤ₀' (donde uno de los
-- componentes es 𝟘), lo que permite convertir igualdades observacionales en proposicionales.

import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.Bijection
import AczelSetTheory.Integers.Order
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Decidable

/-- El tipo de los pares normalizados de ℕ₀ × ℕ₀, donde al menos uno es 𝟘. -/
def ℤ₀' := { p : ℕ₀ × ℕ₀ // p.1 = 𝟘 ∨ p.2 = 𝟘 }

namespace ℤ₀'

/-- Convierte una clase ℤ₀ a su representante canónico ℤ₀'. -/
def ofZ0 (z : ℤ₀) : ℤ₀' := ⟨z.repr, ℤ₀.repr_normalized z⟩

/-- Convierte el representante canónico ℤ₀' de vuelta a la clase ℤ₀. -/
def toZ0 (p : ℤ₀') : ℤ₀ := Sub.sub (ℤ₀.ofNat p.val.1) (ℤ₀.ofNat p.val.2)

theorem toZ0_ofZ0 (z : ℤ₀) : toZ0 (ofZ0 z) = z := ℤ₀.ofNat_sub_repr z
theorem ofZ0_toZ0 (p : ℤ₀') : ofZ0 (toZ0 p) = p := by
  apply Subtype.ext
  have hp : p.val.1 = 𝟘 ∨ p.val.2 = 𝟘 := p.property
  have H : toZ0 p = ℤ₀.mk p.val := by
    show ℤ₀.mk (ℤ₀.addRaw (p.val.1, 𝟘) (ℤ₀.negRaw (p.val.2, 𝟘))) = ℤ₀.mk p.val
    rw [ℤ₀.mk_eq_iff]
    unfold intEq ℤ₀.addRaw ℤ₀.negRaw
    omega₀
  change (toZ0 p).repr = p.val
  rw [H, ℤ₀.repr_mk]
  unfold ℤ₀.normalize
  by_cases h : p.val.2 ≤ p.val.1
  · rw [if_pos h]
    rcases hp with hp1 | hp2
    · have h0 : p.val.2 = 𝟘 := by omega₀
      apply Prod.ext
      · rw [h0]; exact Peano.Sub.sub_zero p.val.1
      · rw [h0]
    · apply Prod.ext
      · rw [hp2]; exact Peano.Sub.sub_zero p.val.1
      · rw [hp2]
  · rw [if_neg h]
    rcases hp with hp1 | hp2
    · apply Prod.ext
      · rw [hp1]
      · rw [hp1]; exact Peano.Sub.sub_zero p.val.2
    · exfalso; omega₀

instance : Zero ℤ₀' where zero := ofZ0 0
instance : One  ℤ₀' where one  := ofZ0 1
instance : Add  ℤ₀' where add a b := ofZ0 (Add.add (toZ0 a) (toZ0 b))
instance : Mul  ℤ₀' where mul a b := ofZ0 (Mul.mul (toZ0 a) (toZ0 b))
instance : Neg  ℤ₀' where neg a := ofZ0 (Neg.neg (toZ0 a))
instance : Sub  ℤ₀' where sub a b := ofZ0 (Sub.sub (toZ0 a) (toZ0 b))

instance : LE ℤ₀' where le a b := toZ0 a ≤ toZ0 b
instance : LT ℤ₀' where lt a b := toZ0 a < toZ0 b
instance instDecidableEq (a b : ℤ₀') : Decidable (a = b) :=
  match decEq (toZ0 a) (toZ0 b) with
  | isTrue h  => isTrue (by rw [←ofZ0_toZ0 a, ←ofZ0_toZ0 b, h])
  | isFalse h => isFalse (fun heq => h (by rw [heq]))

instance instDecidableLE (a b : ℤ₀') : Decidable (a ≤ b) := inferInstanceAs (Decidable (toZ0 a ≤ toZ0 b))
instance instDecidableLT (a b : ℤ₀') : Decidable (a < b) := inferInstanceAs (Decidable (toZ0 a < toZ0 b))

-- Ejemplo de transporte de estructura
theorem add_comm (a b : ℤ₀') : Add.add a b = Add.add b a := by
  change ofZ0 (Add.add (toZ0 a) (toZ0 b)) = ofZ0 (Add.add (toZ0 b) (toZ0 a))
  rw [ℤ₀.add_comm]

theorem add_assoc (a b c : ℤ₀') : Add.add (Add.add a b) c = Add.add a (Add.add b c) := by
  change ofZ0 (Add.add (toZ0 (ofZ0 (Add.add (toZ0 a) (toZ0 b)))) (toZ0 c)) =
         ofZ0 (Add.add (toZ0 a) (toZ0 (ofZ0 (Add.add (toZ0 b) (toZ0 c)))))
  rw [toZ0_ofZ0, toZ0_ofZ0, ℤ₀.add_assoc]

end ℤ₀'

/-- La estructura HFInt agrupa la clase de equivalencia ℤ₀ y su representante canónico ℤ₀'. -/
structure HFInt where
  cls  : ℤ₀
  pair : ℤ₀'
  hEq  : pair.val = cls.repr

namespace HFInt

/-- Construye un HFInt a partir de un entero estándar ℤ₀. -/
def ofZ0 (z : ℤ₀) : HFInt where
  cls  := z
  pair := ⟨z.repr, ℤ₀.repr_normalized z⟩
  hEq  := rfl

/-- Construye un HFInt a partir de su representante canónico ℤ₀'. -/
def ofZ0' (p : ℤ₀') : HFInt where
  cls  := ℤ₀'.toZ0 p
  pair := p
  hEq  := (congrArg Subtype.val (ℤ₀'.ofZ0_toZ0 p)).symm

theorem ofZ0_cls (z : ℤ₀) : (ofZ0 z).cls = z := rfl

/-- Dos HFInt son iguales si sus clases subyacentes son iguales. -/
@[ext]
theorem ext (a b : HFInt) (h : a.cls = b.cls) : a = b := by
  have h_repr : a.cls.repr = b.cls.repr := by rw [h]
  have h_val : a.pair.val = b.pair.val := by
    rw [a.hEq, b.hEq, h_repr]
  have h_pair : a.pair = b.pair := Subtype.ext h_val
  cases a
  cases b
  simp only [mk.injEq]
  constructor
  · exact h
  · exact h_pair

-- ─────────────────────────────────────────────────────────────────────────────
-- Instancias Algebraicas
-- ─────────────────────────────────────────────────────────────────────────────

instance : Zero HFInt where zero := ofZ0 0
instance : One  HFInt where one  := ofZ0 1
instance : Add  HFInt where add a b := ofZ0 (Add.add a.cls b.cls)
instance : Mul  HFInt where mul a b := ofZ0 (Mul.mul a.cls b.cls)
instance : Neg  HFInt where neg a := ofZ0 (Neg.neg a.cls)
instance : Sub  HFInt where sub a b := ofZ0 (Sub.sub a.cls b.cls)

def ofNat (n : ℕ₀) : HFInt := ofZ0 (ℤ₀.ofNat n)

-- ─────────────────────────────────────────────────────────────────────────────
-- Lemas de anillo (heredados trivialmente de ℤ₀)
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_comm (a b : HFInt) : Add.add a b = Add.add b a := by
  apply ext
  exact ℤ₀.add_comm a.cls b.cls

theorem add_assoc (a b c : HFInt) : Add.add (Add.add a b) c = Add.add a (Add.add b c) := by
  apply ext
  exact ℤ₀.add_assoc a.cls b.cls c.cls

theorem zero_add (a : HFInt) : Add.add 0 a = a := by
  apply ext
  exact ℤ₀.zero_add a.cls

theorem add_zero (a : HFInt) : Add.add a 0 = a := by
  apply ext
  exact ℤ₀.add_zero a.cls

theorem add_neg_self (a : HFInt) : Add.add a (Neg.neg a) = 0 := by
  apply ext
  exact ℤ₀.add_neg_self a.cls

theorem neg_add_self (a : HFInt) : Add.add (Neg.neg a) a = 0 := by
  apply ext
  exact ℤ₀.neg_add_self a.cls

theorem neg_neg (a : HFInt) : Neg.neg (Neg.neg a) = a := by
  apply ext
  exact ℤ₀.neg_neg a.cls

theorem mul_comm (a b : HFInt) : Mul.mul a b = Mul.mul b a := by
  apply ext
  exact ℤ₀.mul_comm a.cls b.cls

theorem mul_assoc (a b c : HFInt) : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c) := by
  apply ext
  exact ℤ₀.mul_assoc a.cls b.cls c.cls

theorem one_mul (a : HFInt) : Mul.mul 1 a = a := by
  apply ext
  exact ℤ₀.one_mul a.cls

theorem mul_one (a : HFInt) : Mul.mul a 1 = a := by
  apply ext
  exact ℤ₀.mul_one a.cls

theorem zero_mul (a : HFInt) : Mul.mul 0 a = 0 := by
  apply ext
  exact ℤ₀.zero_mul a.cls

theorem mul_zero (a : HFInt) : Mul.mul a 0 = 0 := by
  apply ext
  exact ℤ₀.mul_zero a.cls

theorem left_distrib (a b c : HFInt) : Mul.mul a (Add.add b c) = Add.add (Mul.mul a b) (Mul.mul a c) := by
  apply ext
  exact ℤ₀.left_distrib a.cls b.cls c.cls

theorem right_distrib (a b c : HFInt) : Mul.mul (Add.add a b) c = Add.add (Mul.mul a c) (Mul.mul b c) := by
  apply ext
  exact ℤ₀.right_distrib a.cls b.cls c.cls

theorem neg_mul (a b : HFInt) : Mul.mul (Neg.neg a) b = Neg.neg (Mul.mul a b) := by
  apply ext
  exact ℤ₀.neg_mul a.cls b.cls

theorem mul_neg (a b : HFInt) : Mul.mul a (Neg.neg b) = Neg.neg (Mul.mul a b) := by
  apply ext
  exact ℤ₀.mul_neg a.cls b.cls

-- ─────────────────────────────────────────────────────────────────────────────
-- Decidibilidad de la Igualdad
-- ─────────────────────────────────────────────────────────────────────────────

instance instDecidableEq (a b : HFInt) : Decidable (a = b) :=
  match decEq a.cls b.cls with
  | isTrue h  => isTrue (ext a b h)
  | isFalse h => isFalse (fun heq => h (by rw [heq]))

instance : LE HFInt where le a b := a.cls ≤ b.cls
instance : LT HFInt where lt a b := a.cls < b.cls

instance instDecidableLE (a b : HFInt) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.cls ≤ b.cls))
instance instDecidableLT (a b : HFInt) : Decidable (a < b) := inferInstanceAs (Decidable (a.cls < b.cls))

-- ─────────────────────────────────────────────────────────────────────────────
-- Subtipos Estructurados
-- ─────────────────────────────────────────────────────────────────────────────

/-- Elementos no nulos (HFInt^*) -/
def NonZero := { x : HFInt // x ≠ 0 }

/-- Unidades de HFInt (solo 1 y -1) -/
def Units := { x : HFInt // x = 1 ∨ x = -1 }

/-- Kernel de HFInt (0, 1 y -1) -/
def Kernel := { x : HFInt // x = 0 ∨ x = 1 ∨ x = -1 }

/-- Elementos fuera del kernel -/
def OutKernel := { x : HFInt // x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 }

/-- Estrictamente positivos -/
def Pos := { x : HFInt // 0 < x }

/-- Estrictamente negativos -/
def Neg := { x : HFInt // x < 0 }

/-- No negativos (imagen de ℕ₀) -/
def NonNeg := { x : HFInt // 0 ≤ x }

-- Coerciones para usar los subtipos como HFInt directamente
instance : Coe NonZero HFInt where coe := Subtype.val
instance : Coe Units HFInt where coe := Subtype.val
instance : Coe Kernel HFInt where coe := Subtype.val
instance : Coe OutKernel HFInt where coe := Subtype.val
instance : Coe Pos HFInt where coe := Subtype.val
instance : Coe Neg HFInt where coe := Subtype.val
instance : Coe NonNeg HFInt where coe := Subtype.val

instance : Coe Peano.ℕ₀ HFInt where coe := ofNat

end HFInt
