/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/Group.lean
-- Grupos nativos en HFSet: estructura HFGroup y lemas derivados.
--
-- Público:
--   HFGroup                   : estructura con axiomas minimales (izquierdos)
--   HFGroup.op_inv_left_apply : inv a · (a · b) = b
--   HFGroup.left_cancel       : x · a = x · b → a = b
--   HFGroup.op_inv_right      : a · inv a = e
--   HFGroup.op_id_right       : a · e = a
--   HFGroup.right_cancel      : a · x = b · x → a = b
--   HFGroup.inv_inv            : inv (inv a) = a
--   HFGroup.inv_e              : inv e = e
--   HFGroup.inv_op             : inv (a · b) = inv b · inv a
--   HFGroup.unique_id          : unicidad del neutro
--   HFGroup.unique_inv         : unicidad del inverso

import AczelSetTheory.HFSets

namespace HFAlgebra

-- ─────────────────────────────────────────────────────────────────
-- Estructura principal
-- ─────────────────────────────────────────────────────────────────

/-- Grupo algebraico nativo en HFSet.
    Los axiomas son los mínimos izquierdos:
    identidad izquierda e inverso izquierdo. -/
structure HFGroup where
  G   : HFSet
  op  : HFSet → HFSet → HFSet
  e   : HFSet
  inv : HFSet → HFSet
  e_mem       : e ∈ G
  op_closed   : ∀ {a b : HFSet}, a ∈ G → b ∈ G → op a b ∈ G
  inv_closed  : ∀ {a : HFSet}, a ∈ G → inv a ∈ G
  op_assoc    : ∀ {a b c : HFSet}, a ∈ G → b ∈ G → c ∈ G →
                  op (op a b) c = op a (op b c)
  op_id_left  : ∀ {a : HFSet}, a ∈ G → op e a = a
  op_inv_left : ∀ {a : HFSet}, a ∈ G → op (inv a) a = e

namespace HFGroup

variable (grp : HFGroup)

-- ─────────────────────────────────────────────────────────────────
-- Lema clave: inv a · (a · b) = b
-- ─────────────────────────────────────────────────────────────────

theorem op_inv_left_apply {a b : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) :
    grp.op (grp.inv a) (grp.op a b) = b :=
  calc grp.op (grp.inv a) (grp.op a b)
      = grp.op (grp.op (grp.inv a) a) b := (grp.op_assoc (grp.inv_closed ha) ha hb).symm
    _ = grp.op grp.e b                  := by rw [grp.op_inv_left ha]
    _ = b                               := grp.op_id_left hb

-- ─────────────────────────────────────────────────────────────────
-- Cancelación por la izquierda
-- ─────────────────────────────────────────────────────────────────

theorem left_cancel {x a b : HFSet} (hx : x ∈ grp.G) (ha : a ∈ grp.G) (hb : b ∈ grp.G)
    (h : grp.op x a = grp.op x b) : a = b :=
  (grp.op_inv_left_apply hx ha).symm.trans
    ((congrArg (grp.op (grp.inv x)) h).trans (grp.op_inv_left_apply hx hb))

-- ─────────────────────────────────────────────────────────────────
-- Inverso por la derecha: a · inv a = e
-- ─────────────────────────────────────────────────────────────────

theorem op_inv_right {a : HFSet} (ha : a ∈ grp.G) : grp.op a (grp.inv a) = grp.e := by
  have hinva : grp.inv a ∈ grp.G := grp.inv_closed ha
  have hc : grp.op a (grp.inv a) ∈ grp.G := grp.op_closed ha hinva
  -- (a · inv a) · (a · inv a) = a · inv a  (idempotent)
  have hcc : grp.op (grp.op a (grp.inv a)) (grp.op a (grp.inv a)) = grp.op a (grp.inv a) :=
    calc grp.op (grp.op a (grp.inv a)) (grp.op a (grp.inv a))
        = grp.op a (grp.op (grp.inv a) (grp.op a (grp.inv a))) :=
              grp.op_assoc ha hinva (grp.op_closed ha hinva)
      _ = grp.op a (grp.inv a) := by rw [grp.op_inv_left_apply ha hinva]
  -- inv c · c = e  (left inverse)
  have h1 : grp.op (grp.inv (grp.op a (grp.inv a))) (grp.op a (grp.inv a)) = grp.e :=
    grp.op_inv_left hc
  -- inv c · c = c  (because c · c = c)
  have h2 : grp.op (grp.inv (grp.op a (grp.inv a))) (grp.op a (grp.inv a)) =
            grp.op a (grp.inv a) := by
    have step := grp.op_inv_left_apply hc hc
    rw [hcc] at step
    exact step
  -- Therefore c = e
  exact h2.symm.trans h1

-- ─────────────────────────────────────────────────────────────────
-- Identidad por la derecha: a · e = a
-- ─────────────────────────────────────────────────────────────────

theorem op_id_right {a : HFSet} (ha : a ∈ grp.G) : grp.op a grp.e = a :=
  calc grp.op a grp.e
      = grp.op a (grp.op (grp.inv a) a) := by rw [← grp.op_inv_left ha]
    _ = grp.op (grp.op a (grp.inv a)) a := (grp.op_assoc ha (grp.inv_closed ha) ha).symm
    _ = grp.op grp.e a                  := by rw [grp.op_inv_right ha]
    _ = a                               := grp.op_id_left ha

-- ─────────────────────────────────────────────────────────────────
-- Cancelación por la derecha
-- ─────────────────────────────────────────────────────────────────

theorem right_cancel {x a b : HFSet} (hx : x ∈ grp.G) (ha : a ∈ grp.G) (hb : b ∈ grp.G)
    (h : grp.op a x = grp.op b x) : a = b :=
  calc a
      = grp.op a grp.e                   := (grp.op_id_right ha).symm
    _ = grp.op a (grp.op x (grp.inv x)) := by rw [grp.op_inv_right hx]
    _ = grp.op (grp.op a x) (grp.inv x) := (grp.op_assoc ha hx (grp.inv_closed hx)).symm
    _ = grp.op (grp.op b x) (grp.inv x) := by rw [h]
    _ = grp.op b (grp.op x (grp.inv x)) := grp.op_assoc hb hx (grp.inv_closed hx)
    _ = grp.op b grp.e                  := by rw [grp.op_inv_right hx]
    _ = b                               := grp.op_id_right hb

-- ─────────────────────────────────────────────────────────────────
-- Doble inverso: inv (inv a) = a
-- ─────────────────────────────────────────────────────────────────

theorem inv_inv {a : HFSet} (ha : a ∈ grp.G) : grp.inv (grp.inv a) = a := by
  apply grp.right_cancel (grp.inv_closed ha) (grp.inv_closed (grp.inv_closed ha)) ha
  rw [grp.op_inv_left (grp.inv_closed ha), grp.op_inv_right ha]

-- ─────────────────────────────────────────────────────────────────
-- Inverso del neutro: inv e = e
-- ─────────────────────────────────────────────────────────────────

theorem inv_e : grp.inv grp.e = grp.e :=
  have h1 : grp.op (grp.inv grp.e) grp.e = grp.e :=
    grp.op_inv_left grp.e_mem
  have h2 : grp.op (grp.inv grp.e) grp.e = grp.inv grp.e :=
    grp.op_id_right (grp.inv_closed grp.e_mem)
  h2.symm.trans h1

-- ─────────────────────────────────────────────────────────────────
-- Antiautomorfismo del inverso: inv (a · b) = inv b · inv a
-- ─────────────────────────────────────────────────────────────────

theorem inv_op {a b : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G) :
    grp.inv (grp.op a b) = grp.op (grp.inv b) (grp.inv a) := by
  have hinva  : grp.inv a ∈ grp.G                       := grp.inv_closed ha
  have hinvb  : grp.inv b ∈ grp.G                       := grp.inv_closed hb
  have hab    : grp.op a b ∈ grp.G                      := grp.op_closed ha hb
  have hinvba : grp.op (grp.inv b) (grp.inv a) ∈ grp.G := grp.op_closed hinvb hinva
  -- (inv b · inv a) · (a · b) = e
  have key : grp.op (grp.op (grp.inv b) (grp.inv a)) (grp.op a b) = grp.e :=
    calc grp.op (grp.op (grp.inv b) (grp.inv a)) (grp.op a b)
        = grp.op (grp.inv b) (grp.op (grp.inv a) (grp.op a b)) :=
              grp.op_assoc hinvb hinva (grp.op_closed ha hb)
      _ = grp.op (grp.inv b) b  := by rw [grp.op_inv_left_apply ha hb]
      _ = grp.e                  := grp.op_inv_left hb
  -- right_cancel with (a · b): inv (a · b) = inv b · inv a
  exact grp.right_cancel hab (grp.inv_closed hab) hinvba
    ((grp.op_inv_left hab).trans key.symm)

-- ─────────────────────────────────────────────────────────────────
-- Unicidad del neutro
-- ─────────────────────────────────────────────────────────────────

/-- Si `e'` es una identidad izquierda en `G`, entonces `e' = e`. -/
theorem unique_id {e' : HFSet} (he' : e' ∈ grp.G)
    (h : ∀ {a : HFSet}, a ∈ grp.G → grp.op e' a = a) : e' = grp.e :=
  (grp.op_id_right he').symm.trans (h grp.e_mem)

-- ─────────────────────────────────────────────────────────────────
-- Unicidad del inverso
-- ─────────────────────────────────────────────────────────────────

/-- Si `b · a = e`, entonces `b = inv a`. -/
theorem unique_inv {a b : HFSet} (ha : a ∈ grp.G) (hb : b ∈ grp.G)
    (h : grp.op b a = grp.e) : b = grp.inv a :=
  grp.right_cancel ha hb (grp.inv_closed ha) (h.trans (grp.op_inv_left ha).symm)

end HFGroup

end HFAlgebra
