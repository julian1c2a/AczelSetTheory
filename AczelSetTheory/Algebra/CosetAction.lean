/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/CosetAction.lean
-- Acción izquierda de un subgrupo H sobre el conjunto de cosetes derechos
-- K\G de otro subgrupo K, dada por right-mult-por-inverso:
--   act h (K·a) := K·(a · h⁻¹)
-- Bien definida porque K(ah⁻¹) sólo depende de Ka:
--   Ka = Kb  ⇒  (ah⁻¹)(bh⁻¹)⁻¹ = a·b⁻¹ ∈ K  ⇒  K(ah⁻¹) = K(bh⁻¹).
--
-- Público:
--   HFSubgroup.rightCoset_mulRight_eq
--     : Ka = Kb  →  K(a·c) = K(b·c)
--   HFAlgebra.cosetAction (sub_H sub_K : HFSubgroup grp)
--     : HFGroupAction sub_H.toHFGroup sub_K.cosets
--   HFAlgebra.cosetAction_act_cosetOf
--     : (cosetAction _ _).act h (K·a) = K·(a·h⁻¹)
--
-- Correspondencia con Peano/Combinatorics/GroupTheory/Sylow/CosetAction.lean:
--   Peano `cosetAction G H K` (acción izquierda h·(aK) := (h·a)K sobre
--   cosetes izquierdos) ↔ HFAlgebra.cosetAction (cosetes derechos vía
--   multiplicación por la derecha por h⁻¹). Las dos convenciones son
--   isomorfas vía a ↦ a⁻¹.

import AczelSetTheory.Algebra.Action
import AczelSetTheory.Algebra.QuotientGroup

namespace HFAlgebra

variable {grp : HFGroup}

namespace HFSubgroup

/-- Si `Ka = Kb` entonces `K(a·c) = K(b·c)` (la multiplicación a derecha
    por un elemento fijo preserva la igualdad de cosetes derechos). -/
theorem rightCoset_mulRight_eq (sub : HFSubgroup grp) {a b c : HFSet}
    (ha : a ∈ grp.G) (hb : b ∈ grp.G) (hc : c ∈ grp.G)
    (heq : sub.rightCoset a = sub.rightCoset b) :
    sub.rightCoset (grp.op a c) = sub.rightCoset (grp.op b c) := by
  have hab : sub.cosetEq a b := (sub.cosetEq_iff_rightCoset_eq ha hb).mpr heq
  -- hab : op b (inv a) ∈ H
  apply (sub.cosetEq_iff_rightCoset_eq
    (grp.op_closed ha hc) (grp.op_closed hb hc)).mp
  show grp.op (grp.op b c) (grp.inv (grp.op a c)) ∈ sub.H
  have hinva := grp.inv_closed ha
  have hinvc := grp.inv_closed hc
  -- (b·c)·(a·c)⁻¹ = (b·c)·(c⁻¹·a⁻¹) = b·(c·c⁻¹)·a⁻¹ = b·a⁻¹
  have key : grp.op (grp.op b c) (grp.inv (grp.op a c)) = grp.op b (grp.inv a) := by
    rw [grp.inv_op ha hc]
    calc grp.op (grp.op b c) (grp.op (grp.inv c) (grp.inv a))
        = grp.op b (grp.op c (grp.op (grp.inv c) (grp.inv a))) :=
              grp.op_assoc hb hc (grp.op_closed hinvc hinva)
      _ = grp.op b (grp.op (grp.op c (grp.inv c)) (grp.inv a)) := by
              rw [← grp.op_assoc hc hinvc hinva]
      _ = grp.op b (grp.op grp.e (grp.inv a)) := by rw [grp.op_inv_right hc]
      _ = grp.op b (grp.inv a) := by rw [grp.op_id_left hinva]
  rw [key]
  exact hab

end HFSubgroup

-- ─────────────────────────────────────────────────────────────────
-- Acción cosetActFun de H sobre K.cosets
-- ─────────────────────────────────────────────────────────────────

/-- Acción izquierda de `sub_H` (como grupo) sobre los cosetes derechos
    de `sub_K`: `act h (K·a) := K·(a · h⁻¹)`. -/
noncomputable def cosetAction (sub_H sub_K : HFSubgroup grp) :
    HFGroupAction sub_H.toHFGroup sub_K.cosets where
  act h C := sub_K.rightCoset (grp.op (sub_K.cosetRep C) (grp.inv h))
  act_closed := fun {h C} hh hC => by
    have hh_G : h ∈ grp.G := sub_H.H_sub hh
    have hr_G : sub_K.cosetRep C ∈ grp.G := sub_K.cosetRep_mem_G hC
    have hinvh : grp.inv h ∈ grp.G := grp.inv_closed hh_G
    have hop : grp.op (sub_K.cosetRep C) (grp.inv h) ∈ grp.G :=
      grp.op_closed hr_G hinvh
    exact sub_K.cosetOf_mem_cosets hop
  act_id := fun {C} hC => by
    show sub_K.rightCoset (grp.op (sub_K.cosetRep C) (grp.inv grp.e)) = C
    have hr_G : sub_K.cosetRep C ∈ grp.G := sub_K.cosetRep_mem_G hC
    rw [grp.inv_e, grp.op_id_right hr_G]
    exact sub_K.cosetRep_rightCoset_eq hC
  act_compat := fun {g h C} hg hh hC => by
    show sub_K.rightCoset
            (grp.op (sub_K.cosetRep
                      (sub_K.rightCoset (grp.op (sub_K.cosetRep C) (grp.inv h))))
                    (grp.inv g))
       = sub_K.rightCoset (grp.op (sub_K.cosetRep C) (grp.inv (grp.op g h)))
    have hg_G : g ∈ grp.G := sub_H.H_sub hg
    have hh_G : h ∈ grp.G := sub_H.H_sub hh
    have hinvg : grp.inv g ∈ grp.G := grp.inv_closed hg_G
    have hinvh : grp.inv h ∈ grp.G := grp.inv_closed hh_G
    have hr_G : sub_K.cosetRep C ∈ grp.G := sub_K.cosetRep_mem_G hC
    have hrinvh : grp.op (sub_K.cosetRep C) (grp.inv h) ∈ grp.G :=
      grp.op_closed hr_G hinvh
    have hD_mem :
        sub_K.rightCoset (grp.op (sub_K.cosetRep C) (grp.inv h)) ∈ sub_K.cosets :=
      sub_K.cosetOf_mem_cosets hrinvh
    have hrD_G :
        sub_K.cosetRep
            (sub_K.rightCoset (grp.op (sub_K.cosetRep C) (grp.inv h))) ∈ grp.G :=
      sub_K.cosetRep_mem_G hD_mem
    have hrD_eq :
        sub_K.rightCoset
            (sub_K.cosetRep
              (sub_K.rightCoset (grp.op (sub_K.cosetRep C) (grp.inv h))))
          = sub_K.rightCoset (grp.op (sub_K.cosetRep C) (grp.inv h)) :=
      sub_K.cosetRep_rightCoset_eq hD_mem
    -- Paso 1: substituir cosetRep (Krh⁻¹) por (r·h⁻¹) tras mult por inv g.
    have step1 :
        sub_K.rightCoset
            (grp.op (sub_K.cosetRep
                (sub_K.rightCoset (grp.op (sub_K.cosetRep C) (grp.inv h))))
                (grp.inv g))
          = sub_K.rightCoset
              (grp.op (grp.op (sub_K.cosetRep C) (grp.inv h)) (grp.inv g)) :=
      sub_K.rightCoset_mulRight_eq hrD_G hrinvh hinvg hrD_eq
    rw [step1, grp.inv_op hg_G hh_G, grp.op_assoc hr_G hinvh hinvg]

/-- Forma con `cosetOf` (alias) del valor de la acción sobre `K·a`. -/
theorem cosetAction_act_cosetOf
    (sub_H sub_K : HFSubgroup grp) {h a : HFSet}
    (hh : h ∈ sub_H.H) (ha : a ∈ grp.G) :
    (cosetAction sub_H sub_K).act h (sub_K.cosetOf a)
      = sub_K.cosetOf (grp.op a (grp.inv h)) := by
  show sub_K.rightCoset (grp.op (sub_K.cosetRep (sub_K.cosetOf a)) (grp.inv h))
     = sub_K.rightCoset (grp.op a (grp.inv h))
  have hh_G : h ∈ grp.G := sub_H.H_sub hh
  have hinvh : grp.inv h ∈ grp.G := grp.inv_closed hh_G
  have hKa_mem : sub_K.cosetOf a ∈ sub_K.cosets := sub_K.cosetOf_mem_cosets ha
  have hrep_G : sub_K.cosetRep (sub_K.cosetOf a) ∈ grp.G :=
    sub_K.cosetRep_mem_G hKa_mem
  have hrep_eq :
      sub_K.rightCoset (sub_K.cosetRep (sub_K.cosetOf a))
        = sub_K.rightCoset a :=
    sub_K.cosetRep_rightCoset_eq hKa_mem
  exact sub_K.rightCoset_mulRight_eq hrep_G ha hinvh hrep_eq

end HFAlgebra
