/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/Field.lean
-- Cuerpos nativos en HFSet: estructura, homomorfismos y subcuerpos.
--
-- Público:
--   HFField                   : cuerpo conmutativo unitario con inverso multiplicativo
--   HFField.right_distrib     : distributividad derecha (de left_distrib + mul_comm)
--   HFField.mul_inv_left      : inv_mul a · a = 1  (de mul_inv + mul_comm)
--   HFField.toHFRing          : todo cuerpo es un anillo
--   HFField.toAdditiveHFGroup : grupo aditivo del cuerpo
--   HFFieldHom                : homomorfismo de cuerpos f : F → G
--   HFFieldHom.hom_zero       : f(0F) = 0G
--   HFFieldHom.hom_neg        : f(-a) = -f(a)
--   HFFieldHom.hom_inv        : f(inv_mul a) = inv_mul (f a)  (a ≠ 0)
--   HFFieldHom.comp           : composición de homomorfismos
--   HFSubfield                : subcuerpo de HFField
--   HFSubfield.toHFField      : subcuerpo como HFField
--   HFSubfield.inter          : intersección de subcuerpos

import AczelSetTheory.Algebra.RingHom
import AczelSetTheory.Axioms.Intersection

namespace HFAlgebra

-- ─────────────────────────────────────────────────────────────────
-- Estructura principal
-- ─────────────────────────────────────────────────────────────────

/-- Cuerpo algebraico nativo en HFSet.
    Es un anillo conmutativo con unidad en el que todo elemento no nulo
    tiene inverso multiplicativo (por la derecha; la izquierda se deriva
    de la conmutatividad). -/
structure HFField where
  F       : HFSet
  add     : HFSet → HFSet → HFSet
  mul     : HFSet → HFSet → HFSet
  zero    : HFSet
  one     : HFSet
  neg     : HFSet → HFSet
  inv_mul : HFSet → HFSet   -- inverso multiplicativo (junk en zero)
  -- pertenencia
  zero_mem    : zero ∈ F
  one_mem     : one ∈ F
  add_closed  : ∀ {a b : HFSet}, a ∈ F → b ∈ F → add a b ∈ F
  mul_closed  : ∀ {a b : HFSet}, a ∈ F → b ∈ F → mul a b ∈ F
  neg_closed  : ∀ {a : HFSet}, a ∈ F → neg a ∈ F
  inv_closed  : ∀ {a : HFSet}, a ∈ F → inv_mul a ∈ F
  -- grupo aditivo abeliano (axiomas izquierdos + comm)
  add_assoc   : ∀ {a b c : HFSet}, a ∈ F → b ∈ F → c ∈ F →
                  add (add a b) c = add a (add b c)
  add_comm    : ∀ {a b : HFSet}, a ∈ F → b ∈ F → add a b = add b a
  zero_add    : ∀ {a : HFSet}, a ∈ F → add zero a = a
  neg_add     : ∀ {a : HFSet}, a ∈ F → add (neg a) a = zero
  -- monoide multiplicativo conmutativo
  mul_assoc   : ∀ {a b c : HFSet}, a ∈ F → b ∈ F → c ∈ F →
                  mul (mul a b) c = mul a (mul b c)
  mul_comm    : ∀ {a b : HFSet}, a ∈ F → b ∈ F → mul a b = mul b a
  mul_one     : ∀ {a : HFSet}, a ∈ F → mul a one = a
  -- distributividad izquierda (la derecha se deriva de mul_comm)
  left_distrib : ∀ {a b c : HFSet}, a ∈ F → b ∈ F → c ∈ F →
                   mul a (add b c) = add (mul a b) (mul a c)
  -- inverso multiplicativo para no-cero
  mul_inv      : ∀ {a : HFSet}, a ∈ F → a ≠ zero → mul a (inv_mul a) = one
  -- el cuerpo no es trivial
  zero_ne_one  : zero ≠ one

namespace HFField

variable (fld : HFField)

-- ─────────────────────────────────────────────────────────────────
-- Lemas inmediatos derivados de mul_comm
-- ─────────────────────────────────────────────────────────────────

theorem one_mul {a : HFSet} (ha : a ∈ fld.F) : fld.mul fld.one a = fld.mul a fld.one :=
  fld.mul_comm fld.one_mem ha

theorem right_distrib {a b c : HFSet} (ha : a ∈ fld.F) (hb : b ∈ fld.F) (hc : c ∈ fld.F) :
    fld.mul (fld.add a b) c = fld.add (fld.mul a c) (fld.mul b c) :=
  calc fld.mul (fld.add a b) c
      = fld.mul c (fld.add a b)                   := fld.mul_comm (fld.add_closed ha hb) hc
    _ = fld.add (fld.mul c a) (fld.mul c b)       := fld.left_distrib hc ha hb
    _ = fld.add (fld.mul a c) (fld.mul b c)       := by
          rw [fld.mul_comm hc ha, fld.mul_comm hc hb]

theorem mul_inv_left {a : HFSet} (ha : a ∈ fld.F) (hne : a ≠ fld.zero) :
    fld.mul (fld.inv_mul a) a = fld.one :=
  (fld.mul_comm (fld.inv_closed ha) ha).trans (fld.mul_inv ha hne)

-- ─────────────────────────────────────────────────────────────────
-- Todo cuerpo es un anillo
-- ─────────────────────────────────────────────────────────────────

/-- El cuerpo `fld` visto como HFRing. -/
def toHFRing : HFRing where
  R             := fld.F
  add           := fld.add
  mul           := fld.mul
  zero          := fld.zero
  one           := fld.one
  neg           := fld.neg
  zero_mem      := fld.zero_mem
  one_mem       := fld.one_mem
  add_closed    := fld.add_closed
  mul_closed    := fld.mul_closed
  neg_closed    := fld.neg_closed
  add_assoc     := fld.add_assoc
  add_comm      := fld.add_comm
  zero_add      := fld.zero_add
  neg_add       := fld.neg_add
  mul_assoc     := fld.mul_assoc
  mul_one       := fld.mul_one
  one_mul       := fun ha => (fld.mul_comm fld.one_mem ha).trans (fld.mul_one ha)
  left_distrib  := fld.left_distrib
  right_distrib := fld.right_distrib

/-- El grupo aditivo del cuerpo. -/
def toAdditiveHFGroup : HFGroup :=
  fld.toHFRing.toAdditiveHFGroup

end HFField

-- ─────────────────────────────────────────────────────────────────
-- Homomorfismo de cuerpos
-- ─────────────────────────────────────────────────────────────────

/-- Homomorfismo de HFField.
    Un homomorfismo de cuerpos es un homomorfismo del anillo subyacente
    (que preserva suma, producto y unidad). La inyectividad se deriva. -/
structure HFFieldHom (F G : HFField) where
  f     : HFSet → HFSet
  f_mem : ∀ {a : HFSet}, a ∈ F.F → f a ∈ G.F
  f_add : ∀ {a b : HFSet}, a ∈ F.F → b ∈ F.F → f (F.add a b) = G.add (f a) (f b)
  f_mul : ∀ {a b : HFSet}, a ∈ F.F → b ∈ F.F → f (F.mul a b) = G.mul (f a) (f b)
  f_one : f F.one = G.one

namespace HFFieldHom

variable {F G K : HFField} (φ : HFFieldHom F G)

-- vista como HFRingHom
def toHFRingHom : HFRingHom F.toHFRing G.toHFRing where
  f     := φ.f
  f_mem := φ.f_mem
  f_add := φ.f_add
  f_mul := φ.f_mul
  f_one := φ.f_one

-- ─────────────────────────────────────────────────────────────────
-- f(0F) = 0G,  f(-a) = -f(a)
-- ─────────────────────────────────────────────────────────────────

theorem hom_zero : φ.f F.zero = G.zero :=
  φ.toHFRingHom.hom_zero

theorem hom_neg {a : HFSet} (ha : a ∈ F.F) : φ.f (F.neg a) = G.neg (φ.f a) :=
  φ.toHFRingHom.hom_neg ha

-- ─────────────────────────────────────────────────────────────────
-- f(inv_mul a) = inv_mul (f a)  para a ≠ 0
-- ─────────────────────────────────────────────────────────────────

theorem hom_inv {a : HFSet} (ha : a ∈ F.F) (hne : a ≠ F.zero) :
    φ.f (F.inv_mul a) = G.inv_mul (φ.f a) := by
  have hfa   : φ.f a ∈ G.F             := φ.f_mem ha
  have hfinv : φ.f (F.inv_mul a) ∈ G.F := φ.f_mem (F.inv_closed ha)
  -- f(a) ≠ 0G: si f(a) = 0G entonces 1G = f(1F) = f(a · inv a) = f(a)·f(inv a) = 0G
  -- lo que contradice zero_ne_one de G (hom inyectivo en cuerpos, pero lo hacemos explícito)
  -- mostramos: f(inv_mul a) · f(a) = 1G
  have hkey : G.mul (φ.f (F.inv_mul a)) (φ.f a) = G.one :=
    calc G.mul (φ.f (F.inv_mul a)) (φ.f a)
        = φ.f (F.mul (F.inv_mul a) a) := (φ.f_mul (F.inv_closed ha) ha).symm
      _ = φ.f F.one                   := by rw [F.mul_inv_left ha hne]
      _ = G.one                       := φ.f_one
  -- necesitamos f(a) ≠ 0G para usar mul_inv
  have hfa_ne : φ.f a ≠ G.zero := by
    intro heq
    have : G.one = G.zero :=
      calc G.one = G.mul (φ.f (F.inv_mul a)) (φ.f a) := hkey.symm
        _ = G.mul (φ.f (F.inv_mul a)) G.zero         := by rw [heq]
        _ = G.zero                                    := G.toHFRing.mul_zero hfinv
    exact G.zero_ne_one this.symm
  -- G.inv_mul (f a) es el inverso derecho de f(a): f(a) · G.inv_mul(f a) = 1
  -- f(inv a) también: f(inv a) · f(a) = 1
  -- por unicidad del inverso en el grupo multiplicativo de G:
  -- usamos: f(inv a) · f(a) = 1 = G.inv_mul(f a) · f(a) → iguales por cancelación
  have hrhs : G.mul (G.inv_mul (φ.f a)) (φ.f a) = G.one := G.mul_inv_left hfa hfa_ne
  -- Ambos son inversosizquierdos de f(a); como G es conmutativo, mul_inv a = único
  -- g₁ · x = 1 ∧ g₂ · x = 1 → g₁ = g₂   (en un grupo, por cancelación derecha)
  -- Construimos el HFGroup multiplicativo de G (no-cero): usamos el grupo aditivo como proxy
  -- En su lugar: g₁ · x = g₂ · x → g₁ = g₂  si x tiene inverso derecho
  -- g₁ · x = 1 = g₂ · x, y x · (G.inv_mul x) = 1,  entonces
  -- g₁ = g₁ · 1 = g₁ · (x · inv x) = (g₁ · x) · inv x = 1 · inv x = inv x
  -- g₂ = inv x  similarly  →  g₁ = g₂
  have hinvx : G.mul (φ.f a) (G.inv_mul (φ.f a)) = G.one := G.mul_inv hfa hfa_ne
  calc φ.f (F.inv_mul a)
      = G.mul (φ.f (F.inv_mul a)) G.one                         := (G.mul_one hfinv).symm
    _ = G.mul (φ.f (F.inv_mul a)) (G.mul (φ.f a) (G.inv_mul (φ.f a))) := by rw [hinvx]
    _ = G.mul (G.mul (φ.f (F.inv_mul a)) (φ.f a)) (G.inv_mul (φ.f a)) :=
          (G.mul_assoc hfinv hfa (G.inv_closed hfa)).symm
    _ = G.mul G.one (G.inv_mul (φ.f a))                         := by rw [hkey]
    _ = G.mul (G.inv_mul (φ.f a)) G.one                         := G.mul_comm G.one_mem (G.inv_closed hfa)
    _ = G.inv_mul (φ.f a)                                       := G.mul_one (G.inv_closed hfa)

-- ─────────────────────────────────────────────────────────────────
-- Identidad y composición
-- ─────────────────────────────────────────────────────────────────

/-- La identidad es un homomorfismo de cuerpos. -/
def id (F : HFField) : HFFieldHom F F where
  f     := fun a => a
  f_mem := fun ha => ha
  f_add := fun _ _ => rfl
  f_mul := fun _ _ => rfl
  f_one := rfl

/-- Composición de homomorfismos de cuerpos. -/
def comp (ψ : HFFieldHom G K) (φ : HFFieldHom F G) : HFFieldHom F K where
  f     := fun a => ψ.f (φ.f a)
  f_mem := fun ha => ψ.f_mem (φ.f_mem ha)
  f_add := fun ha hb => by rw [φ.f_add ha hb, ψ.f_add (φ.f_mem ha) (φ.f_mem hb)]
  f_mul := fun ha hb => by rw [φ.f_mul ha hb, ψ.f_mul (φ.f_mem ha) (φ.f_mem hb)]
  f_one := by rw [φ.f_one, ψ.f_one]

end HFFieldHom

-- ─────────────────────────────────────────────────────────────────
-- Subcuerpo
-- ─────────────────────────────────────────────────────────────────

/-- Subcuerpo de un HFField.
    Nota: la clausura del inverso multiplicativo requiere la hipótesis
    de que el elemento sea no nulo (condición en el axioma). -/
structure HFSubfield (fld : HFField) where
  S           : HFSet
  S_sub       : ∀ {x : HFSet}, x ∈ S → x ∈ fld.F
  zero_mem    : fld.zero ∈ S
  one_mem     : fld.one ∈ S
  add_closed  : ∀ {a b : HFSet}, a ∈ S → b ∈ S → fld.add a b ∈ S
  mul_closed  : ∀ {a b : HFSet}, a ∈ S → b ∈ S → fld.mul a b ∈ S
  neg_closed  : ∀ {a : HFSet}, a ∈ S → fld.neg a ∈ S
  inv_closed  : ∀ {a : HFSet}, a ∈ S → fld.inv_mul a ∈ S

namespace HFSubfield

variable {fld : HFField}

/-- Todo subcuerpo es un cuerpo, heredando las operaciones del cuerpo ambiente. -/
def toHFField (sub : HFSubfield fld) : HFField where
  F            := sub.S
  add          := fld.add
  mul          := fld.mul
  zero         := fld.zero
  one          := fld.one
  neg          := fld.neg
  inv_mul      := fld.inv_mul
  zero_mem     := sub.zero_mem
  one_mem      := sub.one_mem
  add_closed   := sub.add_closed
  mul_closed   := sub.mul_closed
  neg_closed   := sub.neg_closed
  inv_closed   := sub.inv_closed
  add_assoc    := fun ha hb hc =>
    fld.add_assoc (sub.S_sub ha) (sub.S_sub hb) (sub.S_sub hc)
  add_comm     := fun ha hb =>
    fld.add_comm (sub.S_sub ha) (sub.S_sub hb)
  zero_add     := fun ha => fld.zero_add (sub.S_sub ha)
  neg_add      := fun ha => fld.neg_add (sub.S_sub ha)
  mul_assoc    := fun ha hb hc =>
    fld.mul_assoc (sub.S_sub ha) (sub.S_sub hb) (sub.S_sub hc)
  mul_comm     := fun ha hb =>
    fld.mul_comm (sub.S_sub ha) (sub.S_sub hb)
  mul_one      := fun ha => fld.mul_one (sub.S_sub ha)
  left_distrib := fun ha hb hc =>
    fld.left_distrib (sub.S_sub ha) (sub.S_sub hb) (sub.S_sub hc)
  mul_inv      := fun ha hne => fld.mul_inv (sub.S_sub ha) hne
  zero_ne_one  := fld.zero_ne_one

/-- La intersección de dos subcuerpos del mismo cuerpo es un subcuerpo. -/
def inter (sub₁ sub₂ : HFSubfield fld) : HFSubfield fld where
  S          := HFSet.inter sub₁.S sub₂.S
  S_sub      := fun hx => by rw [HFSet.mem_inter] at hx; exact sub₁.S_sub hx.1
  zero_mem   := by rw [HFSet.mem_inter]; exact ⟨sub₁.zero_mem, sub₂.zero_mem⟩
  one_mem    := by rw [HFSet.mem_inter]; exact ⟨sub₁.one_mem, sub₂.one_mem⟩
  add_closed := fun ha hb => by
    rw [HFSet.mem_inter] at ha hb ⊢
    exact ⟨sub₁.add_closed ha.1 hb.1, sub₂.add_closed ha.2 hb.2⟩
  mul_closed := fun ha hb => by
    rw [HFSet.mem_inter] at ha hb ⊢
    exact ⟨sub₁.mul_closed ha.1 hb.1, sub₂.mul_closed ha.2 hb.2⟩
  neg_closed := fun ha => by
    rw [HFSet.mem_inter] at ha ⊢
    exact ⟨sub₁.neg_closed ha.1, sub₂.neg_closed ha.2⟩
  inv_closed := fun ha => by
    rw [HFSet.mem_inter] at ha ⊢
    exact ⟨sub₁.inv_closed ha.1, sub₂.inv_closed ha.2⟩

end HFSubfield

end HFAlgebra
