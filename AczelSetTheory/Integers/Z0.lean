/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Integers/ℤ₀.lean
--
-- ℤ₀: Tipo canónico para los enteros.
-- Encapsula un ℤ₀cls junto con su par representante canónico en ℤ₀can (donde uno de los
-- componentes es 𝟘), lo que permite convertir igualdades observacionales en proposicionales.

import AczelSetTheory.Integers.Basic
import AczelSetTheory.Integers.Bijection
import AczelSetTheory.Integers.Order
import Peano.PeanoNat.Sub
import Peano.PeanoNat.Decidable

/-- El tipo de los pares normalizados de ℕ₀ × ℕ₀, donde al menos uno es 𝟘. -/
def ℤ₀can := { p : ℕ₀ × ℕ₀ // p.1 = 𝟘 ∨ p.2 = 𝟘 }

namespace ℤ₀can

/-- Convierte una clase ℤ₀cls a su representante canónico ℤ₀can. -/
def ofCls (z : ℤ₀cls) : ℤ₀can := ⟨z.repr, ℤ₀cls.repr_normalized z⟩

/-- Convierte el representante canónico ℤ₀can de vuelta a la clase ℤ₀cls. -/
def toCls (p : ℤ₀can) : ℤ₀cls := Sub.sub (ℤ₀cls.ofNat p.val.1) (ℤ₀cls.ofNat p.val.2)

theorem toCls_ofCls (z : ℤ₀cls) : toCls (ofCls z) = z := ℤ₀cls.ofNat_sub_repr z
theorem ofCls_toCls (p : ℤ₀can) : ofCls (toCls p) = p := by
  apply Subtype.ext
  have hp : p.val.1 = 𝟘 ∨ p.val.2 = 𝟘 := p.property
  have H : toCls p = ℤ₀cls.mk p.val := by
    show ℤ₀cls.mk (ℤ₀cls.addRaw (p.val.1, 𝟘) (ℤ₀cls.negRaw (p.val.2, 𝟘))) = ℤ₀cls.mk p.val
    rw [ℤ₀cls.mk_eq_iff]
    unfold intEq ℤ₀cls.addRaw ℤ₀cls.negRaw
    omega₀
  change (toCls p).repr = p.val
  rw [H, ℤ₀cls.repr_mk]
  unfold ℤ₀cls.normalize
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

instance : Zero ℤ₀can where zero := ofCls 0
instance : One  ℤ₀can where one  := ofCls 1
instance : Add  ℤ₀can where add a b := ofCls (Add.add (toCls a) (toCls b))
instance : Mul  ℤ₀can where mul a b := ofCls (Mul.mul (toCls a) (toCls b))
instance : Neg  ℤ₀can where neg a := ofCls (Neg.neg (toCls a))
instance : Sub  ℤ₀can where sub a b := ofCls (Sub.sub (toCls a) (toCls b))

instance : LE ℤ₀can where le a b := toCls a ≤ toCls b
instance : LT ℤ₀can where lt a b := toCls a < toCls b
instance instDecidableEq (a b : ℤ₀can) : Decidable (a = b) :=
  match decEq (toCls a) (toCls b) with
  | isTrue h  => isTrue (by rw [←ofCls_toCls a, ←ofCls_toCls b, h])
  | isFalse h => isFalse (fun heq => h (by rw [heq]))

instance instDecidableLE (a b : ℤ₀can) : Decidable (a ≤ b) := inferInstanceAs (Decidable (toCls a ≤ toCls b))
instance instDecidableLT (a b : ℤ₀can) : Decidable (a < b) := inferInstanceAs (Decidable (toCls a < toCls b))

-- Ejemplo de transporte de estructura
theorem add_comm (a b : ℤ₀can) : Add.add a b = Add.add b a := by
  change ofCls (Add.add (toCls a) (toCls b)) = ofCls (Add.add (toCls b) (toCls a))
  rw [ℤ₀cls.add_comm]

theorem add_assoc (a b c : ℤ₀can) : Add.add (Add.add a b) c = Add.add a (Add.add b c) := by
  change ofCls (Add.add (toCls (ofCls (Add.add (toCls a) (toCls b)))) (toCls c)) =
         ofCls (Add.add (toCls a) (toCls (ofCls (Add.add (toCls b) (toCls c)))))
  rw [toCls_ofCls, toCls_ofCls, ℤ₀cls.add_assoc]

end ℤ₀can

/-- La estructura ℤ₀ agrupa la clase de equivalencia ℤ₀cls y su representante canónico ℤ₀can. -/
structure ℤ₀ where
  cls  : ℤ₀cls
  pair : ℤ₀can
  hEq  : pair.val = cls.repr

namespace ℤ₀

/-- Construye un ℤ₀ a partir de un entero estándar ℤ₀cls. -/
def ofCls (z : ℤ₀cls) : ℤ₀ where
  cls  := z
  pair := ⟨z.repr, ℤ₀cls.repr_normalized z⟩
  hEq  := rfl

/-- Construye un ℤ₀ a partir de su representante canónico ℤ₀can. -/
def ofCls' (p : ℤ₀can) : ℤ₀ where
  cls  := ℤ₀can.toCls p
  pair := p
  hEq  := (congrArg Subtype.val (ℤ₀can.ofCls_toCls p)).symm

theorem ofCls_cls (z : ℤ₀cls) : (ofCls z).cls = z := rfl

/-- Dos ℤ₀ son iguales si sus clases subyacentes son iguales. -/
@[ext]
theorem ext (a b : ℤ₀) (h : a.cls = b.cls) : a = b := by
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

instance : Zero ℤ₀ where zero := ofCls 0
instance : One  ℤ₀ where one  := ofCls 1

/-- `-1` empaquetado. Bridge trivial sobre `ℤ₀cls.negOne` (migración de tipos, ADR-023). -/
def negOne : ℤ₀ := ofCls ℤ₀cls.negOne
instance : Add  ℤ₀ where add a b := ofCls (Add.add a.cls b.cls)
instance : Mul  ℤ₀ where mul a b := ofCls (Mul.mul a.cls b.cls)
instance : Neg  ℤ₀ where neg a := ofCls (Neg.neg a.cls)
instance : Sub  ℤ₀ where sub a b := ofCls (Sub.sub a.cls b.cls)

def ofNat (n : ℕ₀) : ℤ₀ := ofCls (ℤ₀cls.ofNat n)

-- ─────────────────────────────────────────────────────────────────────────────
-- Lemas de anillo (heredados trivialmente de ℤ₀cls)
-- ─────────────────────────────────────────────────────────────────────────────

theorem add_comm (a b : ℤ₀) : Add.add a b = Add.add b a := by
  apply ext
  exact ℤ₀cls.add_comm a.cls b.cls

theorem add_assoc (a b c : ℤ₀) : Add.add (Add.add a b) c = Add.add a (Add.add b c) := by
  apply ext
  exact ℤ₀cls.add_assoc a.cls b.cls c.cls

theorem zero_add (a : ℤ₀) : Add.add 0 a = a := by
  apply ext
  exact ℤ₀cls.zero_add a.cls

theorem add_zero (a : ℤ₀) : Add.add a 0 = a := by
  apply ext
  exact ℤ₀cls.add_zero a.cls

theorem add_neg_self (a : ℤ₀) : Add.add a (Neg.neg a) = 0 := by
  apply ext
  exact ℤ₀cls.add_neg_self a.cls

theorem neg_add_self (a : ℤ₀) : Add.add (Neg.neg a) a = 0 := by
  apply ext
  exact ℤ₀cls.neg_add_self a.cls

theorem neg_neg (a : ℤ₀) : Neg.neg (Neg.neg a) = a := by
  apply ext
  exact ℤ₀cls.neg_neg a.cls

theorem mul_comm (a b : ℤ₀) : Mul.mul a b = Mul.mul b a := by
  apply ext
  exact ℤ₀cls.mul_comm a.cls b.cls

theorem mul_assoc (a b c : ℤ₀) : Mul.mul (Mul.mul a b) c = Mul.mul a (Mul.mul b c) := by
  apply ext
  exact ℤ₀cls.mul_assoc a.cls b.cls c.cls

theorem one_mul (a : ℤ₀) : Mul.mul 1 a = a := by
  apply ext
  exact ℤ₀cls.one_mul a.cls

theorem mul_one (a : ℤ₀) : Mul.mul a 1 = a := by
  apply ext
  exact ℤ₀cls.mul_one a.cls

theorem zero_mul (a : ℤ₀) : Mul.mul 0 a = 0 := by
  apply ext
  exact ℤ₀cls.zero_mul a.cls

theorem mul_zero (a : ℤ₀) : Mul.mul a 0 = 0 := by
  apply ext
  exact ℤ₀cls.mul_zero a.cls

theorem left_distrib (a b c : ℤ₀) : Mul.mul a (Add.add b c) = Add.add (Mul.mul a b) (Mul.mul a c) := by
  apply ext
  exact ℤ₀cls.left_distrib a.cls b.cls c.cls

theorem right_distrib (a b c : ℤ₀) : Mul.mul (Add.add a b) c = Add.add (Mul.mul a c) (Mul.mul b c) := by
  apply ext
  exact ℤ₀cls.right_distrib a.cls b.cls c.cls

theorem neg_mul (a b : ℤ₀) : Mul.mul (Neg.neg a) b = Neg.neg (Mul.mul a b) := by
  apply ext
  exact ℤ₀cls.neg_mul a.cls b.cls

theorem mul_neg (a b : ℤ₀) : Mul.mul a (Neg.neg b) = Neg.neg (Mul.mul a b) := by
  apply ext
  exact ℤ₀cls.mul_neg a.cls b.cls

-- ─────────────────────────────────────────────────────────────────────────────
-- Decidibilidad de la Igualdad
-- ─────────────────────────────────────────────────────────────────────────────

instance instDecidableEq (a b : ℤ₀) : Decidable (a = b) :=
  match decEq a.cls b.cls with
  | isTrue h  => isTrue (ext a b h)
  | isFalse h => isFalse (fun heq => h (by rw [heq]))

instance : LE ℤ₀ where le a b := a.cls ≤ b.cls
instance : LT ℤ₀ where lt a b := a.cls < b.cls

-- ─────────────────────────────────────────────────────────────────────────────
-- Homomorfismo `.cls` — BASE DEL API BRIDGE (ADR-023, migración de tipos)
--
-- Las operaciones del struct están definidas como `ofCls (op sobre cls)`, así que la
-- proyección `.cls` conmuta con TODAS ellas por `rfl`. Estos `@[simp]` + `@[ext]`
-- convierten cualquier hecho de `ℤ₀cls` en su versión sobre `ℤ₀` en una línea:
--   theorem foo (a b : ℤ₀) : a ⊕ b = b ⊕ a := by ext; simp; exact ℤ₀cls.foo a.cls b.cls
-- y el orden vía `le_iff_cls`/`lt_iff_cls`. La teoría original sobre `ℤ₀cls` no se toca.
-- ─────────────────────────────────────────────────────────────────────────────

@[simp] theorem cls_zero   : (0 : ℤ₀).cls = 0 := rfl
@[simp] theorem cls_one    : (1 : ℤ₀).cls = 1 := rfl
@[simp] theorem cls_negOne : negOne.cls = ℤ₀cls.negOne := rfl
@[simp] theorem cls_add (a b : ℤ₀) : (a + b).cls = a.cls + b.cls := rfl
@[simp] theorem cls_mul (a b : ℤ₀) : (a * b).cls = a.cls * b.cls := rfl
@[simp] theorem cls_neg (a : ℤ₀)   : (-a).cls   = -a.cls := rfl
@[simp] theorem cls_sub (a b : ℤ₀) : (a - b).cls = a.cls - b.cls := rfl

/-- El orden del struct es, por definición, el de sus clases. -/
theorem le_iff_cls (a b : ℤ₀) : a ≤ b ↔ a.cls ≤ b.cls := Iff.rfl
theorem lt_iff_cls (a b : ℤ₀) : a < b ↔ a.cls < b.cls := Iff.rfl

instance instDecidableLE (a b : ℤ₀) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.cls ≤ b.cls))
instance instDecidableLT (a b : ℤ₀) : Decidable (a < b) := inferInstanceAs (Decidable (a.cls < b.cls))

-- ─────────────────────────────────────────────────────────────────────────────
-- Subtipos Estructurados
-- ─────────────────────────────────────────────────────────────────────────────

/-- Elementos no nulos (ℤ₀^*) -/
def NonZero := { x : ℤ₀ // x ≠ 0 }

/-- Unidades de ℤ₀ (solo 1 y -1) -/
def Units := { x : ℤ₀ // x = 1 ∨ x = -1 }

/-- Kernel de ℤ₀ (0, 1 y -1) -/
def Kernel := { x : ℤ₀ // x = 0 ∨ x = 1 ∨ x = -1 }

/-- Elementos fuera del kernel -/
def OutKernel := { x : ℤ₀ // x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 }

/-- Estrictamente positivos -/
def Pos := { x : ℤ₀ // 0 < x }

/-- Estrictamente negativos -/
def Neg := { x : ℤ₀ // x < 0 }

/-- No negativos (imagen de ℕ₀) -/
def NonNeg := { x : ℤ₀ // 0 ≤ x }

-- Coerciones para usar los subtipos como ℤ₀ directamente
instance : Coe NonZero ℤ₀ where coe := Subtype.val
instance : Coe Units ℤ₀ where coe := Subtype.val
instance : Coe Kernel ℤ₀ where coe := Subtype.val
instance : Coe OutKernel ℤ₀ where coe := Subtype.val
instance : Coe Pos ℤ₀ where coe := Subtype.val
instance : Coe Neg ℤ₀ where coe := Subtype.val
instance : Coe NonNeg ℤ₀ where coe := Subtype.val

instance : Coe Peano.ℕ₀ ℤ₀ where coe := ofNat

/-- Coerción olvidadiza `ℤ₀ → ℤ₀cls` (proyección al campo `cls`): permite usar un `ℤ₀`
    (entero empaquetado) allí donde se espera la clase de equivalencia `ℤ₀cls`. Es el
    homomorfismo natural — las operaciones del struct están definidas como
    `ofCls (op sobre cls)`, así que `(a ⊕ b).cls = a.cls ⊕ b.cls` por `rfl` (ver `ofCls_cls`).
    Con esto, migrar un consumidor a `ℤ₀` no obliga a reescribir su teoría: sigue apoyándose
    en la de `ℤ₀cls` vía esta coerción (ADR-023 / migración de tipos). -/
instance : Coe ℤ₀ ℤ₀cls where coe := ℤ₀.cls

end ℤ₀
