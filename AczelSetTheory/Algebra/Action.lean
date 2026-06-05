/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/Action.lean
-- Acciones de grupo sobre HFSet: GroupAction, órbita, estabilizador, partición.
--
-- Público:
--   HFGroupAction                : estructura de acción izquierda G ↷ X
--   HFGroupAction.orb            : órbita de un elemento
--   HFGroupAction.mem_orb_iff    : caracterización de pertenencia a la órbita
--   HFGroupAction.stab           : estabilizador como HFSubgroup
--   HFGroupAction.mem_stab_iff   : caracterización de pertenencia al estabilizador
--   HFGroupAction.orb_self       : x ∈ orb x
--   HFGroupAction.orbits_partition : dos órbitas son iguales o disjuntas
--   HFGroupAction.orbit_stabilizer : card(orb x) · card(stab x) = card G
--   conjugAction                 : acción por conjugación G ↷ G
--   center_eq_fixed              : Z(G) = puntos fijos de conjugAction
--   HFGroupAction.orbit_stabilizer : card(orb x) · card(stab x) = card G
--   HFGroupAction.card_orb_dvd_card_G : card(orb x) ∣ card G (existencial)
--   class_equation               : card G = card Z(G) + card (G \ Z(G))
--
-- Correspondencia con Peano/Combinatorics/GroupTheory/Action.lean:
--   FinGroup G ↔ HFGroup grp
--   FSet β X ↔ X : HFSet (subconjunto invariante)
--   GroupAction.act g x ↔ ψ.act g x
--   GroupAction.orb x ↔ ψ.orb x
--   GroupAction.stab x ↔ ψ.stab x
--   orbit_stabilizer (Peano) ↔ HFGroupAction.orbit_stabilizer
--   class_equation (Peano)   ↔ HFAlgebra.class_equation (forma con setminus;
--                                la forma Σ card(orb r) requiere card_sUnion
--                                no-uniforme, no incluido aquí).
--
-- Nota de alcance (paridad completa con Peano):
--   class_equation (Σ): card G = card Z(G) + Σ card(orb r)  (r reps no centrales)
--     (requiere `card_sUnion` para particiones no uniformes; la forma con
--      `setminus` arriba es suficiente para el argumento estándar de Sylow)

import AczelSetTheory.Algebra.NormalSubgroup
import AczelSetTheory.Algebra.QuotientGroup
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.CardImage

namespace HFAlgebra

variable {grp : HFGroup}

-- ─────────────────────────────────────────────────────────────────
-- §1. HFGroupAction: acción izquierda de un HFGroup sobre un HFSet
-- ─────────────────────────────────────────────────────────────────

/-- Acción izquierda de un grupo `grp` sobre un conjunto `X : HFSet`:
    una función `act : HFSet → HFSet → HFSet` que satisface:
    - `act` cerrada sobre `X`,
    - `act e x = x`,
    - `act g (act h x) = act (g·h) x`. -/
structure HFGroupAction (grp : HFGroup) (X : HFSet) where
  act        : HFSet → HFSet → HFSet
  act_closed : ∀ {g x : HFSet}, g ∈ grp.G → x ∈ X → act g x ∈ X
  act_id     : ∀ {x : HFSet}, x ∈ X → act grp.e x = x
  act_compat : ∀ {g h x : HFSet}, g ∈ grp.G → h ∈ grp.G → x ∈ X →
                  act g (act h x) = act (grp.op g h) x

namespace HFGroupAction

variable {X : HFSet}

-- ─────────────────────────────────────────────────────────────────
-- §2. Órbita
-- ─────────────────────────────────────────────────────────────────

/-- Órbita de `x` bajo la acción `ψ`:
    `Orb(x) = { y ∈ X | ∃ g ∈ G, act g x = y }`. -/
def orb (ψ : HFGroupAction grp X) (x : HFSet) : HFSet :=
  HFSet.sep X (fun y => ∃ g ∈ grp.G, ψ.act g x = y)

theorem mem_orb_iff (ψ : HFGroupAction grp X) (x y : HFSet) :
    y ∈ ψ.orb x ↔ y ∈ X ∧ ∃ g ∈ grp.G, ψ.act g x = y := by
  show y ∈ HFSet.sep X (fun y => ∃ g ∈ grp.G, ψ.act g x = y) ↔ _
  exact HFSet.mem_sep ..

/-- `x ∈ orb x` (la órbita contiene su representante). -/
theorem orb_self (ψ : HFGroupAction grp X) {x : HFSet} (hx : x ∈ X) :
    x ∈ ψ.orb x :=
  (ψ.mem_orb_iff x x).mpr ⟨hx, grp.e, grp.e_mem, ψ.act_id hx⟩

-- ─────────────────────────────────────────────────────────────────
-- §3. Estabilizador como HFSubgroup
-- ─────────────────────────────────────────────────────────────────

/-- Estabilizador de `x` en `grp`:
    `Stab(x) = { g ∈ G | act g x = x }`. Es un subgrupo. -/
def stab (ψ : HFGroupAction grp X) {x : HFSet} (hx : x ∈ X) : HFSubgroup grp where
  H := HFSet.sep grp.G (fun g => ψ.act g x = x)
  H_sub := fun hg => by rw [HFSet.mem_sep] at hg; exact hg.1
  e_mem := by
    rw [HFSet.mem_sep]
    exact ⟨grp.e_mem, ψ.act_id hx⟩
  op_closed := by
    intro a b ha hb
    rw [HFSet.mem_sep] at ha hb ⊢
    refine ⟨grp.op_closed ha.1 hb.1, ?_⟩
    rw [← ψ.act_compat ha.1 hb.1 hx, hb.2, ha.2]
  inv_closed := by
    intro a ha
    rw [HFSet.mem_sep] at ha ⊢
    refine ⟨grp.inv_closed ha.1, ?_⟩
    -- act(a⁻¹, x) = x: aplicar act g a both sides of act a x = x: act a (act a⁻¹ x) = act a x = x
    -- but act a (act a⁻¹ x) = act (a · a⁻¹) x = act e x = x. So act a (act a⁻¹ x) = x.
    -- combined with act a x = x: act a (act a⁻¹ x) = act a x, then by inverse: act a⁻¹ x = x... we need injectivity
    -- Better: use act a⁻¹ to ψ.act_compat and ha.2:
    -- act a⁻¹ x = act a⁻¹ (act a x) = act (a⁻¹ · a) x = act e x = x
    have hinva := grp.inv_closed ha.1
    calc ψ.act (grp.inv a) x
        = ψ.act (grp.inv a) (ψ.act a x) := by rw [ha.2]
      _ = ψ.act (grp.op (grp.inv a) a) x := ψ.act_compat hinva ha.1 hx
      _ = ψ.act grp.e x := by rw [grp.op_inv_left ha.1]
      _ = x := ψ.act_id hx

theorem mem_stab_iff (ψ : HFGroupAction grp X) {x : HFSet} (hx : x ∈ X) (g : HFSet) :
    g ∈ (ψ.stab hx).H ↔ g ∈ grp.G ∧ ψ.act g x = x := by
  show g ∈ HFSet.sep grp.G (fun g => ψ.act g x = x) ↔ _
  exact HFSet.mem_sep ..

-- ─────────────────────────────────────────────────────────────────
-- §4. Relación de equivalencia: dos órbitas son iguales o disjuntas
-- ─────────────────────────────────────────────────────────────────

/-- Si `y ∈ orb x` con `x, y ∈ X`, entonces `orb y = orb x`. -/
theorem orb_eq_of_mem (ψ : HFGroupAction grp X) {x y : HFSet}
    (hx : x ∈ X) (hy : y ∈ X) (hyx : y ∈ ψ.orb x) :
    ψ.orb y = ψ.orb x := by
  obtain ⟨_, g₀, hg₀, hg₀_eq⟩ := (ψ.mem_orb_iff x y).mp hyx
  apply HFSet.extensionality
  intro z
  rw [ψ.mem_orb_iff y z, ψ.mem_orb_iff x z]
  constructor
  · rintro ⟨hz, h, hh, hh_eq⟩
    refine ⟨hz, grp.op h g₀, grp.op_closed hh hg₀, ?_⟩
    rw [← ψ.act_compat hh hg₀ hx, hg₀_eq, hh_eq]
  · rintro ⟨hz, h, hh, hh_eq⟩
    refine ⟨hz, grp.op h (grp.inv g₀), grp.op_closed hh (grp.inv_closed hg₀), ?_⟩
    -- act (h · g₀⁻¹) y = act h (act g₀⁻¹ y) = act h (act g₀⁻¹ (act g₀ x)) = act h x = z
    have hinvg₀ := grp.inv_closed hg₀
    calc ψ.act (grp.op h (grp.inv g₀)) y
        = ψ.act h (ψ.act (grp.inv g₀) y) := (ψ.act_compat hh hinvg₀ hy).symm
      _ = ψ.act h (ψ.act (grp.inv g₀) (ψ.act g₀ x)) := by rw [hg₀_eq]
      _ = ψ.act h (ψ.act (grp.op (grp.inv g₀) g₀) x) := by
            rw [ψ.act_compat hinvg₀ hg₀ hx]
      _ = ψ.act h (ψ.act grp.e x) := by rw [grp.op_inv_left hg₀]
      _ = ψ.act h x := by rw [ψ.act_id hx]
      _ = z := hh_eq

/-- Dos órbitas son iguales o disjuntas (partición). -/
theorem orbits_partition (ψ : HFGroupAction grp X) {x y : HFSet}
    (hx : x ∈ X) (hy : y ∈ X) :
    ψ.orb x = ψ.orb y ∨ HFSet.inter (ψ.orb x) (ψ.orb y) = HFSet.empty := by
  by_cases hxy : ∃ z, z ∈ ψ.orb x ∧ z ∈ ψ.orb y
  · left
    obtain ⟨z, hzx, hzy⟩ := hxy
    have hz_X : z ∈ X := ((ψ.mem_orb_iff x z).mp hzx).1
    -- z ∈ orb x → orb z = orb x; z ∈ orb y → orb z = orb y. So orb x = orb y.
    have h1 := ψ.orb_eq_of_mem hx hz_X hzx
    have h2 := ψ.orb_eq_of_mem hy hz_X hzy
    exact h1.symm.trans h2
  · right
    apply HFSet.extensionality
    intro z
    rw [HFSet.mem_inter]
    constructor
    · intro ⟨h1, h2⟩
      exact absurd ⟨z, h1, h2⟩ hxy
    · intro hz; exact absurd hz (HFSet.not_mem_empty z)

-- ─────────────────────────────────────────────────────────────────
-- §5. Acción por conjugación: grp ↷ grp.G
-- ─────────────────────────────────────────────────────────────────

/-- La acción de un grupo sobre sí mismo por conjugación:
    `act g x = g · x · g⁻¹`. -/
def conjugAction (grp : HFGroup) : HFGroupAction grp grp.G where
  act g x := grp.op (grp.op g x) (grp.inv g)
  act_closed := fun hg hx =>
    grp.op_closed (grp.op_closed hg hx) (grp.inv_closed hg)
  act_id := fun hx => by
    show grp.op (grp.op grp.e _) (grp.inv grp.e) = _
    rw [grp.op_id_left hx, grp.inv_e, grp.op_id_right hx]
  act_compat := fun {g h x} hg hh hx => by
    show grp.op (grp.op g (grp.op (grp.op h x) (grp.inv h))) (grp.inv g) =
         grp.op (grp.op (grp.op g h) x) (grp.inv (grp.op g h))
    have hghx := grp.op_closed (grp.op_closed hg hh) hx
    have hhx := grp.op_closed hh hx
    have hhinv := grp.inv_closed hh
    have hginv := grp.inv_closed hg
    rw [grp.inv_op hg hh]
    calc grp.op (grp.op g (grp.op (grp.op h x) (grp.inv h))) (grp.inv g)
        = grp.op (grp.op (grp.op g (grp.op h x)) (grp.inv h)) (grp.inv g) := by
              rw [← grp.op_assoc hg hhx hhinv]
      _ = grp.op (grp.op (grp.op (grp.op g h) x) (grp.inv h)) (grp.inv g) := by
              rw [← grp.op_assoc hg hh hx]
      _ = grp.op (grp.op (grp.op g h) x) (grp.op (grp.inv h) (grp.inv g)) :=
              grp.op_assoc hghx hhinv hginv

-- ─────────────────────────────────────────────────────────────────
-- §6. Caracterización del centro como puntos fijos de la conjugación
-- ─────────────────────────────────────────────────────────────────

/-- Un elemento `x ∈ G` está en el centro `Z(G)` sii es fijo por la acción
    de conjugación: `∀ g ∈ G, g·x·g⁻¹ = x`. -/
theorem mem_center_iff_conjug_fixed (grp : HFGroup) {x : HFSet} (hx : x ∈ grp.G) :
    x ∈ (center grp).H ↔ ∀ g, g ∈ grp.G → (conjugAction grp).act g x = x := by
  rw [mem_center_iff]
  constructor
  · intro ⟨_, hcomm⟩ g hg
    show grp.op (grp.op g x) (grp.inv g) = x
    rw [← hcomm g hg, grp.op_assoc hx hg (grp.inv_closed hg),
        grp.op_inv_right hg, grp.op_id_right hx]
  · intro hfix
    refine ⟨hx, fun g hg => ?_⟩
    have hact : grp.op (grp.op g x) (grp.inv g) = x := hfix g hg
    have hgx := grp.op_closed hg hx
    calc grp.op x g
        = grp.op (grp.op (grp.op g x) (grp.inv g)) g := by rw [hact]
      _ = grp.op (grp.op g x) (grp.op (grp.inv g) g) :=
              grp.op_assoc hgx (grp.inv_closed hg) hg
      _ = grp.op (grp.op g x) grp.e := by rw [grp.op_inv_left hg]
      _ = grp.op g x := grp.op_id_right hgx

-- ─────────────────────────────────────────────────────────────────
-- §7. Teorema órbita-estabilizador: card(orb x) · card(stab x) = card G
-- ─────────────────────────────────────────────────────────────────

open Peano Peano.Arith

/-- Teorema órbita-estabilizador:
    `card(orb x) · card(stab x) = card G`. La prueba construye la biyección
    `(stab x).cosets ↔ orb x`,  `C ↦ act (cosetRep C)⁻¹ x`, y combina con
    Lagrange. -/
theorem orbit_stabilizer
    (ψ : HFGroupAction grp X) {x : HFSet} (hx : x ∈ X) :
    mul (HFSet.card (ψ.orb x)) (HFSet.card (ψ.stab hx).H) =
      HFSet.card grp.G := by
  -- (1) Biyección clase (ψ.stab hx).cosets ↔ ψ.orb x.
  have hcard_eq : HFSet.card (ψ.stab hx).cosets = HFSet.card (ψ.orb x) := by
    apply HFSet.card_eq_of_classBij
        (f := fun C => ψ.act (grp.inv ((ψ.stab hx).cosetRep C)) x)
    · -- into: f(C) ∈ orb x.
      intro C hC
      have hr_G : (ψ.stab hx).cosetRep C ∈ grp.G :=
        (ψ.stab hx).cosetRep_mem_G hC
      have hinvr : grp.inv ((ψ.stab hx).cosetRep C) ∈ grp.G :=
        grp.inv_closed hr_G
      rw [ψ.mem_orb_iff]
      exact ⟨ψ.act_closed hinvr hx,
             grp.inv ((ψ.stab hx).cosetRep C), hinvr, rfl⟩
    · -- inj
      intro C₁ C₂ hC₁ hC₂ hfeq
      let r₁ : HFSet := (ψ.stab hx).cosetRep C₁
      let r₂ : HFSet := (ψ.stab hx).cosetRep C₂
      have hr₁_G : r₁ ∈ grp.G := (ψ.stab hx).cosetRep_mem_G hC₁
      have hr₂_G : r₂ ∈ grp.G := (ψ.stab hx).cosetRep_mem_G hC₂
      change ψ.act (grp.inv r₁) x = ψ.act (grp.inv r₂) x at hfeq
      have hinvr₁ := grp.inv_closed hr₁_G
      have hinvr₂ := grp.inv_closed hr₂_G
      -- Derivar  ψ.act (r₁ · r₂⁻¹) x = x  aplicando ψ.act r₁ a hfeq.
      have hstab : ψ.act (grp.op r₁ (grp.inv r₂)) x = x := by
        have h1 : ψ.act r₁ (ψ.act (grp.inv r₁) x) = ψ.act r₁ (ψ.act (grp.inv r₂) x) := by
          rw [hfeq]
        rw [ψ.act_compat hr₁_G hinvr₁ hx,
            ψ.act_compat hr₁_G hinvr₂ hx,
            grp.op_inv_right hr₁_G,
            ψ.act_id hx] at h1
        exact h1.symm
      -- Por mem_stab_iff: r₁ · r₂⁻¹ ∈ stab.H.
      have hmem : grp.op r₁ (grp.inv r₂) ∈ (ψ.stab hx).H := by
        rw [ψ.mem_stab_iff hx]
        exact ⟨grp.op_closed hr₁_G hinvr₂, hstab⟩
      -- Pasar a igualdad de rightCoset y deducir C₁ = C₂.
      have hcoseq : (ψ.stab hx).rightCoset r₂ = (ψ.stab hx).rightCoset r₁ :=
        ((ψ.stab hx).cosetEq_iff_rightCoset_eq hr₂_G hr₁_G).mp hmem
      have e₁ : (ψ.stab hx).rightCoset r₁ = C₁ :=
        (ψ.stab hx).cosetRep_rightCoset_eq hC₁
      have e₂ : (ψ.stab hx).rightCoset r₂ = C₂ :=
        (ψ.stab hx).cosetRep_rightCoset_eq hC₂
      exact (e₂.symm.trans (hcoseq.trans e₁)).symm
    · -- surj
      intro y hy
      rw [ψ.mem_orb_iff] at hy
      obtain ⟨_hy_X, g, hg, hgx⟩ := hy
      have hinvg : grp.inv g ∈ grp.G := grp.inv_closed hg
      let C : HFSet := (ψ.stab hx).rightCoset (grp.inv g)
      have hC_mem : C ∈ (ψ.stab hx).cosets :=
        (ψ.stab hx).cosetOf_mem_cosets hinvg
      refine ⟨C, hC_mem, ?_⟩
      let r : HFSet := (ψ.stab hx).cosetRep C
      have hr_G : r ∈ grp.G := (ψ.stab hx).cosetRep_mem_G hC_mem
      have hinvr : grp.inv r ∈ grp.G := grp.inv_closed hr_G
      -- rightCoset r = C = rightCoset (inv g)
      have hrc : (ψ.stab hx).rightCoset r = (ψ.stab hx).rightCoset (grp.inv g) :=
        (ψ.stab hx).cosetRep_rightCoset_eq hC_mem
      -- cosetEq r (inv g)  ↔  op (inv g) (inv r) ∈ stab.H
      have hmem : grp.op (grp.inv g) (grp.inv r) ∈ (ψ.stab hx).H :=
        ((ψ.stab hx).cosetEq_iff_rightCoset_eq hr_G hinvg).mpr hrc
      have hstab : ψ.act (grp.op (grp.inv g) (grp.inv r)) x = x :=
        ((ψ.mem_stab_iff hx _).mp hmem).2
      -- ψ.act (inv g) (ψ.act (inv r) x) = x
      have hcomp : ψ.act (grp.inv g) (ψ.act (grp.inv r) x) = x := by
        rw [ψ.act_compat hinvg hinvr hx]; exact hstab
      -- Aplicar ψ.act g y simplificar.
      have happ : ψ.act g (ψ.act (grp.inv g) (ψ.act (grp.inv r) x))
                = ψ.act (grp.inv r) x := by
        rw [ψ.act_compat hg hinvg (ψ.act_closed hinvr hx),
            grp.op_inv_right hg,
            ψ.act_id (ψ.act_closed hinvr hx)]
      -- y = ψ.act (inv r) x.
      have hy_eq : ψ.act (grp.inv r) x = y := by
        rw [← happ, hcomp]; exact hgx
      exact hy_eq.symm
  -- (2) Combinar con Lagrange  card G = card cosets · card H.
  have hlag : HFSet.card grp.G
            = mul (HFSet.card (ψ.stab hx).cosets) (HFSet.card (ψ.stab hx).H) :=
    (ψ.stab hx).card_G_eq_card_H_mul_index
  rw [hcard_eq] at hlag
  exact hlag.symm

/-- Corolario: `card(orb x) ∣ card G` (existencialmente). -/
theorem card_orb_dvd_card_G
    (ψ : HFGroupAction grp X) {x : HFSet} (hx : x ∈ X) :
    ∃ k : ℕ₀, HFSet.card grp.G = mul (HFSet.card (ψ.orb x)) k :=
  ⟨HFSet.card (ψ.stab hx).H, (ψ.orbit_stabilizer hx).symm⟩

end HFGroupAction

-- ─────────────────────────────────────────────────────────────────
-- §8. Ecuación de clases (forma básica) — paridad con Peano
-- ─────────────────────────────────────────────────────────────────

open HFSet

/-- **Ecuación de clases** (forma básica):
    `card G = card Z(G) + card (G \ Z(G))`. La parte no-central es la unión
    disjunta de las órbitas de conjugación con más de un elemento, pero esa
    forma fuerte requiere `card_sUnion` para particiones no uniformes; aquí
    presentamos la forma equivalente con `setminus`, suficiente para el
    argumento estándar de Sylow vía `card_orb_dvd_card_G` sobre cada órbita
    no central de la acción de conjugación. -/
theorem class_equation (grp : HFGroup) :
    HFSet.card grp.G =
      add (HFSet.card (center grp).H)
          (HFSet.card (HFSet.setminus grp.G (center grp).H)) := by
  have h_inter : HFSet.inter grp.G (center grp).H = (center grp).H := by
    apply HFSet.extensionality; intro x
    rw [HFSet.mem_inter]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(center grp).H_sub h, h⟩⟩
  have hpart := HFSet.card_partition grp.G (center grp).H
  rw [h_inter] at hpart
  exact hpart

end HFAlgebra
