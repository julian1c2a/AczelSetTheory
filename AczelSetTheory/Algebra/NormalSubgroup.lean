/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Algebra/NormalSubgroup.lean
-- Subgrupos normales, cosetes izquierdos, centralizador, centro y normalizador.
--
-- Público:
--   HFSubgroup.isNormal           : H ⊴ G — ∀ g ∈ G, ∀ n ∈ H, g·n·g⁻¹ ∈ H
--   HFSubgroup.leftCoset          : aH = { x ∈ G | ∃ h ∈ H, x = a·h }
--   HFSubgroup.mem_leftCoset      : x ∈ aH ↔ ∃ h ∈ H, x = a·h
--   centralizer                   : C_G(H) = { g ∈ G | ∀ h ∈ H, g·h = h·g }
--   center                        : Z(G) = { g ∈ G | ∀ h ∈ G, g·h = h·g }
--   normalizer                    : N_G(H) como HFSubgroup
--   mem_centralizer_iff           : caracterización de C_G(H)
--   mem_center_iff                : caracterización de Z(G)
--   mem_normalizer_iff            : caracterización de N_G(H)
--   H_subset_normalizer           : H ⊆ N_G(H)
--   isNormal_iff_normalizer_eq_G  : H ⊴ G ↔ N_G(H).H = G.G
--   isNormal_iff_cosets_eq        : H ⊴ G ↔ ∀ g ∈ G, aH = Ha
--   HFGroupHom.ker_isNormal       : ker φ ⊴ G
--
-- Correspondencia con Peano/GroupTheory/NormalSubgroup.lean:
--   Peano FSet.filter pred S     → HFSet.sep S pred       (con open Classical)
--   Peano List.mem_filter        → HFSet.mem_sep
--   Peano List.all_eq_true       → (decidibilidad clásica; sin simp necesario)
--   Peano G.carrier.elems        → G.G
--   Peano H.carrier.elems        → sub.H
--   Peano H.subset a ha          → sub.H_sub ha
--   Peano G.id                   → G.e
--   Peano (G.op_id a ha).2       → G.op_id_left ha
--   Peano (G.op_id a ha).1       → G.op_id_right ha
--   Peano (G.op_inv a ha).2      → G.op_inv_left ha
--   Peano (G.op_inv a ha).1      → G.op_inv_right ha
--   Peano inv_inv_eq G ha        → G.inv_inv ha
--   Peano inv_id_eq G            → G.inv_e
--   Peano inv_op_eq G ha hb      → G.inv_op ha hb
--   Peano op_mem G ha hb         → G.op_closed ha hb
--   Peano inv_mem G ha           → G.inv_closed ha

import AczelSetTheory.Algebra.GroupHom
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Intersection
import AczelSetTheory.Axioms.OrdinalNat

namespace HFAlgebra

variable {grp : HFGroup}

-- ─────────────────────────────────────────────────────────────────
-- §1. Predicado de normalidad
-- ─────────────────────────────────────────────────────────────────

/-- `sub` es normal en `grp`:
    para todo `g ∈ G` y `n ∈ H`, el conjugado `g·n·g⁻¹ ∈ H`. -/
def HFSubgroup.isNormal (sub : HFSubgroup grp) : Prop :=
  ∀ (g n : HFSet), g ∈ grp.G → n ∈ sub.H → grp.op (grp.op g n) (grp.inv g) ∈ sub.H

-- ─────────────────────────────────────────────────────────────────
-- §2. Cosete izquierdo aH = { x ∈ G | ∃ h ∈ H, x = a·h }
-- ─────────────────────────────────────────────────────────────────

/-- Cosete izquierdo de `a` en `sub`: `aH = { x ∈ G | ∃ h ∈ H, x = a·h }`. -/
def HFSubgroup.leftCoset (sub : HFSubgroup grp) (a : HFSet) : HFSet :=
  HFSet.sep grp.G (fun x => ∃ h ∈ sub.H, x = grp.op a h)

theorem HFSubgroup.mem_leftCoset (sub : HFSubgroup grp) {a x : HFSet} (ha : a ∈ grp.G) :
    x ∈ sub.leftCoset a ↔ ∃ h ∈ sub.H, x = grp.op a h := by
  show x ∈ HFSet.sep grp.G (fun x => ∃ h ∈ sub.H, x = grp.op a h) ↔ _
  rw [HFSet.mem_sep]
  constructor
  · intro ⟨_, hx⟩; exact hx
  · intro hx
    refine ⟨?_, hx⟩
    obtain ⟨h, hh, rfl⟩ := hx
    exact grp.op_closed ha (sub.H_sub hh)

-- ─────────────────────────────────────────────────────────────────
-- §3. Centralizador C_G(H) = { g ∈ G | ∀ h ∈ H, g·h = h·g }
-- ─────────────────────────────────────────────────────────────────

/-- Centralizador de `sub` en `grp`:
    `C_G(H) = { g ∈ G | ∀ h ∈ H, g·h = h·g }`. -/
def centralizer (sub : HFSubgroup grp) : HFSubgroup grp where
  H          := HFSet.sep grp.G (fun g => ∀ h, h ∈ sub.H → grp.op g h = grp.op h g)
  H_sub      := fun hg => by rw [HFSet.mem_sep] at hg; exact hg.1
  e_mem      := by
    rw [HFSet.mem_sep]
    exact ⟨grp.e_mem, fun h hh =>
      (grp.op_id_left (sub.H_sub hh)).trans (grp.op_id_right (sub.H_sub hh)).symm⟩
  op_closed  := by
    intro a b ha hb
    rw [HFSet.mem_sep] at ha hb ⊢
    refine ⟨grp.op_closed ha.1 hb.1, fun h hh => ?_⟩
    have hh_G := sub.H_sub hh
    calc grp.op (grp.op a b) h
        = grp.op a (grp.op b h) := grp.op_assoc ha.1 hb.1 hh_G
      _ = grp.op a (grp.op h b) := by rw [hb.2 h hh]
      _ = grp.op (grp.op a h) b := (grp.op_assoc ha.1 hh_G hb.1).symm
      _ = grp.op (grp.op h a) b := by rw [ha.2 h hh]
      _ = grp.op h (grp.op a b) := grp.op_assoc hh_G ha.1 hb.1
  inv_closed := by
    intro a ha
    rw [HFSet.mem_sep] at ha ⊢
    refine ⟨grp.inv_closed ha.1, fun h hh => ?_⟩
    have hh_G  := sub.H_sub hh
    have ha_G  := ha.1
    have hinva := grp.inv_closed ha_G
    -- Queremos: a⁻¹·h = h·a⁻¹
    -- Basta: a·(a⁻¹·h) = a·(h·a⁻¹), luego left_cancel por a.
    apply grp.left_cancel ha_G (grp.op_closed hinva hh_G) (grp.op_closed hh_G hinva)
    have lhs : grp.op a (grp.op (grp.inv a) h) = h := by
      rw [← grp.op_assoc ha_G hinva hh_G, grp.op_inv_right ha_G, grp.op_id_left hh_G]
    have rhs : grp.op a (grp.op h (grp.inv a)) = h := by
      rw [← grp.op_assoc ha_G hh_G hinva, ha.2 h hh,
          grp.op_assoc hh_G ha_G hinva, grp.op_inv_right ha_G, grp.op_id_right hh_G]
    exact lhs.trans rhs.symm

/-- Caracterización: `g ∈ C_G(H) ↔ g ∈ G ∧ ∀ h ∈ H, g·h = h·g`. -/
theorem mem_centralizer_iff (sub : HFSubgroup grp) (g : HFSet) :
    g ∈ (centralizer sub).H ↔
    g ∈ grp.G ∧ ∀ h, h ∈ sub.H → grp.op g h = grp.op h g := by
  show g ∈ HFSet.sep grp.G (fun g => ∀ h, h ∈ sub.H → grp.op g h = grp.op h g) ↔ _
  rw [HFSet.mem_sep]

-- ─────────────────────────────────────────────────────────────────
-- §4. Centro Z(G) = { g ∈ G | ∀ h ∈ G, g·h = h·g }
-- ─────────────────────────────────────────────────────────────────

/-- Centro de `grp`:
    `Z(G) = { g ∈ G | ∀ h ∈ G, g·h = h·g }`. -/
def center (grp : HFGroup) : HFSubgroup grp where
  H          := HFSet.sep grp.G (fun g => ∀ h, h ∈ grp.G → grp.op g h = grp.op h g)
  H_sub      := fun hg => by rw [HFSet.mem_sep] at hg; exact hg.1
  e_mem      := by
    rw [HFSet.mem_sep]
    exact ⟨grp.e_mem, fun h hh =>
      (grp.op_id_left hh).trans (grp.op_id_right hh).symm⟩
  op_closed  := by
    intro a b ha hb
    rw [HFSet.mem_sep] at ha hb ⊢
    refine ⟨grp.op_closed ha.1 hb.1, fun h hh => ?_⟩
    calc grp.op (grp.op a b) h
        = grp.op a (grp.op b h) := grp.op_assoc ha.1 hb.1 hh
      _ = grp.op a (grp.op h b) := by rw [hb.2 h hh]
      _ = grp.op (grp.op a h) b := (grp.op_assoc ha.1 hh hb.1).symm
      _ = grp.op (grp.op h a) b := by rw [ha.2 h hh]
      _ = grp.op h (grp.op a b) := grp.op_assoc hh ha.1 hb.1
  inv_closed := by
    intro a ha
    rw [HFSet.mem_sep] at ha ⊢
    refine ⟨grp.inv_closed ha.1, fun h hh => ?_⟩
    have ha_G  := ha.1
    have hinva := grp.inv_closed ha_G
    apply grp.left_cancel ha_G (grp.op_closed hinva hh) (grp.op_closed hh hinva)
    have lhs : grp.op a (grp.op (grp.inv a) h) = h := by
      rw [← grp.op_assoc ha_G hinva hh, grp.op_inv_right ha_G, grp.op_id_left hh]
    have rhs : grp.op a (grp.op h (grp.inv a)) = h := by
      rw [← grp.op_assoc ha_G hh hinva, ha.2 h hh,
          grp.op_assoc hh ha_G hinva, grp.op_inv_right ha_G, grp.op_id_right hh]
    exact lhs.trans rhs.symm

/-- Caracterización: `g ∈ Z(G) ↔ g ∈ G ∧ ∀ h ∈ G, g·h = h·g`. -/
theorem mem_center_iff (g : HFSet) :
    g ∈ (center grp).H ↔
    g ∈ grp.G ∧ ∀ h, h ∈ grp.G → grp.op g h = grp.op h g := by
  show g ∈ HFSet.sep grp.G (fun g => ∀ h, h ∈ grp.G → grp.op g h = grp.op h g) ↔ _
  rw [HFSet.mem_sep]

-- ─────────────────────────────────────────────────────────────────
-- §5. Normalizador N_G(H) = { g ∈ G | ∀ h ∈ H, ghg⁻¹ ∈ H ∧ g⁻¹hg ∈ H }
-- ─────────────────────────────────────────────────────────────────

/-- Normalizador de `sub` en `grp`:
    `N_G(H) = { g ∈ G | (∀ h ∈ H, g·h·g⁻¹ ∈ H) ∧ (∀ h ∈ H, g⁻¹·h·g ∈ H) }`. -/
def normalizer (sub : HFSubgroup grp) : HFSubgroup grp where
  H := HFSet.sep grp.G (fun g =>
    (∀ h, h ∈ sub.H → grp.op (grp.op g h) (grp.inv g) ∈ sub.H) ∧
    (∀ h, h ∈ sub.H → grp.op (grp.op (grp.inv g) h) g ∈ sub.H))
  H_sub := fun hg => by rw [HFSet.mem_sep] at hg; exact hg.1
  e_mem := by
    rw [HFSet.mem_sep]
    refine ⟨grp.e_mem, ?_, ?_⟩
    · intro h hh
      -- e·h·e⁻¹ = e·h·e = h ∈ H
      rw [grp.op_id_left (sub.H_sub hh), grp.inv_e, grp.op_id_right (sub.H_sub hh)]
      exact hh
    · intro h hh
      -- e⁻¹·h·e = e·h·e = h ∈ H
      rw [grp.inv_e, grp.op_id_left (sub.H_sub hh), grp.op_id_right (sub.H_sub hh)]
      exact hh
  op_closed := by
    intro a b ha hb
    rw [HFSet.mem_sep] at ha hb ⊢
    refine ⟨grp.op_closed ha.1 hb.1, ?_, ?_⟩
    · -- Condición 1: (a·b)·h·(a·b)⁻¹ = a·(b·h·b⁻¹)·a⁻¹ ∈ H
      intro h hh
      have hinva := grp.inv_closed ha.1
      have hinvb := grp.inv_closed hb.1
      have hh_G  := sub.H_sub hh
      have hbhb  := hb.2.1 h hh   -- b·h·b⁻¹ ∈ H
      have key   := ha.2.1 _ hbhb -- a·(b·h·b⁻¹)·a⁻¹ ∈ H
      rw [grp.inv_op ha.1 hb.1]
      -- Igualdad: ((a·b)·h)·(b⁻¹·a⁻¹) = (a·(b·h·b⁻¹))·a⁻¹
      have assoc_eq :
          grp.op (grp.op (grp.op a b) h) (grp.op (grp.inv b) (grp.inv a)) =
          grp.op (grp.op a (grp.op (grp.op b h) (grp.inv b))) (grp.inv a) := by
        rw [grp.op_assoc (grp.op_closed ha.1 hb.1) hh_G (grp.op_closed hinvb hinva),
            grp.op_assoc ha.1 hb.1 (grp.op_closed hh_G (grp.op_closed hinvb hinva)),
            ← grp.op_assoc hb.1 hh_G (grp.op_closed hinvb hinva),
            ← grp.op_assoc (grp.op_closed hb.1 hh_G) hinvb hinva,
            ← grp.op_assoc ha.1 (grp.op_closed (grp.op_closed hb.1 hh_G) hinvb) hinva]
      rw [assoc_eq]; exact key
    · -- Condición 2: (a·b)⁻¹·h·(a·b) = b⁻¹·(a⁻¹·h·a)·b ∈ H
      intro h hh
      have hinva := grp.inv_closed ha.1
      have hinvb := grp.inv_closed hb.1
      have hh_G  := sub.H_sub hh
      have haha  := ha.2.2 h hh   -- a⁻¹·h·a ∈ H
      have key   := hb.2.2 _ haha -- b⁻¹·(a⁻¹·h·a)·b ∈ H
      rw [grp.inv_op ha.1 hb.1]
      -- Igualdad: ((b⁻¹·a⁻¹)·h)·(a·b) = (b⁻¹·(a⁻¹·h·a))·b
      have assoc_eq2 :
          grp.op (grp.op (grp.op (grp.inv b) (grp.inv a)) h) (grp.op a b) =
          grp.op (grp.op (grp.inv b) (grp.op (grp.op (grp.inv a) h) a)) b := by
        rw [grp.op_assoc (grp.op_closed hinvb hinva) hh_G (grp.op_closed ha.1 hb.1),
            grp.op_assoc hinvb hinva (grp.op_closed hh_G (grp.op_closed ha.1 hb.1)),
            ← grp.op_assoc hinva hh_G (grp.op_closed ha.1 hb.1),
            ← grp.op_assoc (grp.op_closed hinva hh_G) ha.1 hb.1,
            ← grp.op_assoc hinvb (grp.op_closed (grp.op_closed hinva hh_G) ha.1) hb.1]
      rw [assoc_eq2]; exact key
  inv_closed := by
    intro a ha
    rw [HFSet.mem_sep] at ha ⊢
    refine ⟨grp.inv_closed ha.1, ?_, ?_⟩
    · -- (a⁻¹)·h·(a⁻¹)⁻¹ = a⁻¹·h·a ∈ H  (segunda condición de ha)
      intro h hh
      rw [grp.inv_inv ha.1]
      exact ha.2.2 h hh
    · -- (a⁻¹)⁻¹·h·a⁻¹ = a·h·a⁻¹ ∈ H  (primera condición de ha)
      intro h hh
      rw [grp.inv_inv ha.1]
      exact ha.2.1 h hh

-- ─────────────────────────────────────────────────────────────────
-- §6. Caracterizaciones y subconjunto
-- ─────────────────────────────────────────────────────────────────

/-- Caracterización: `g ∈ N_G(H) ↔ g ∈ G ∧ (∀ h ∈ H, ghg⁻¹ ∈ H) ∧ (∀ h ∈ H, g⁻¹hg ∈ H)`. -/
theorem mem_normalizer_iff (sub : HFSubgroup grp) (g : HFSet) :
    g ∈ (normalizer sub).H ↔
    g ∈ grp.G ∧
    (∀ h, h ∈ sub.H → grp.op (grp.op g h) (grp.inv g) ∈ sub.H) ∧
    (∀ h, h ∈ sub.H → grp.op (grp.op (grp.inv g) h) g ∈ sub.H) := by
  show g ∈ HFSet.sep grp.G (fun g =>
      (∀ h, h ∈ sub.H → grp.op (grp.op g h) (grp.inv g) ∈ sub.H) ∧
      (∀ h, h ∈ sub.H → grp.op (grp.op (grp.inv g) h) g ∈ sub.H)) ↔ _
  rw [HFSet.mem_sep]

/-- `H` está contenido en su propio normalizador: `H ⊆ N_G(H)`. -/
theorem H_subset_normalizer (sub : HFSubgroup grp) :
    ∀ h, h ∈ sub.H → h ∈ (normalizer sub).H := by
  intro h hh
  rw [mem_normalizer_iff]
  refine ⟨sub.H_sub hh, ?_, ?_⟩
  · -- ∀ k ∈ H, h·k·h⁻¹ ∈ H
    intro k hk
    exact sub.op_closed (sub.op_closed hh hk) (sub.inv_closed hh)
  · -- ∀ k ∈ H, h⁻¹·k·h ∈ H
    intro k hk
    exact sub.op_closed (sub.op_closed (sub.inv_closed hh) hk) hh

-- ─────────────────────────────────────────────────────────────────
-- §7. Normalidad ↔ N_G(H) = G
-- ─────────────────────────────────────────────────────────────────

/-- `H ⊴ G ↔ N_G(H).H = G.G`. -/
theorem isNormal_iff_normalizer_eq_G (sub : HFSubgroup grp) :
    sub.isNormal ↔ (normalizer sub).H = grp.G := by
  constructor
  · intro hN
    apply HFSet.extensionality
    intro g
    constructor
    · exact fun hg => ((mem_normalizer_iff sub g).mp hg).1
    · intro hg
      exact (mem_normalizer_iff sub g).mpr
        ⟨hg,
         fun h hh => hN g h hg hh,
         fun h hh => by
           have := hN (grp.inv g) h (grp.inv_closed hg) hh
           rwa [grp.inv_inv hg] at this⟩
  · intro heq g n hg hn
    have hg_norm : g ∈ (normalizer sub).H := by rw [heq]; exact hg
    exact ((mem_normalizer_iff sub g).mp hg_norm).2.1 n hn

-- ─────────────────────────────────────────────────────────────────
-- §8. Normalidad ↔ cosetes izquierdos = cosetes derechos
-- ─────────────────────────────────────────────────────────────────

/-- `H ⊴ G ↔ ∀ g ∈ G, gH = Hg`. -/
theorem isNormal_iff_cosets_eq (sub : HFSubgroup grp) :
    sub.isNormal ↔ ∀ g, g ∈ grp.G → sub.leftCoset g = sub.rightCoset g := by
  constructor
  · intro hN g hg
    apply HFSet.extensionality
    intro x
    rw [sub.mem_leftCoset hg, sub.mem_rightCoset hg]
    constructor
    · -- x ∈ gH: x = g·h, ponemos h' = g·h·g⁻¹ ∈ H y x = h'·g
      intro ⟨h, hh, hx⟩
      subst hx
      refine ⟨grp.op (grp.op g h) (grp.inv g), hN g h hg hh, ?_⟩
      -- g·h = (g·h·g⁻¹)·g
      calc grp.op g h
          = grp.op (grp.op g h) grp.e :=
                (grp.op_id_right (grp.op_closed hg (sub.H_sub hh))).symm
        _ = grp.op (grp.op g h) (grp.op (grp.inv g) g) := by rw [grp.op_inv_left hg]
        _ = grp.op (grp.op (grp.op g h) (grp.inv g)) g :=
                (grp.op_assoc (grp.op_closed hg (sub.H_sub hh)) (grp.inv_closed hg) hg).symm
    · -- x ∈ Hg: x = h·g, ponemos h' = g⁻¹·h·g ∈ H y x = g·h'
      intro ⟨h, hh, hx⟩
      subst hx
      have hconj : grp.op (grp.op (grp.inv g) h) g ∈ sub.H := by
        have := hN (grp.inv g) h (grp.inv_closed hg) hh
        rwa [grp.inv_inv hg] at this
      refine ⟨grp.op (grp.op (grp.inv g) h) g, hconj, ?_⟩
      -- h·g = g·(g⁻¹·h·g)
      calc grp.op h g
          = grp.op grp.e (grp.op h g) :=
                (grp.op_id_left (grp.op_closed (sub.H_sub hh) hg)).symm
        _ = grp.op (grp.op g (grp.inv g)) (grp.op h g) := by rw [grp.op_inv_right hg]
        _ = grp.op g (grp.op (grp.inv g) (grp.op h g)) :=
                grp.op_assoc hg (grp.inv_closed hg) (grp.op_closed (sub.H_sub hh) hg)
        _ = grp.op g (grp.op (grp.op (grp.inv g) h) g) := by
                rw [← grp.op_assoc (grp.inv_closed hg) (sub.H_sub hh) hg]
  · intro hcoe g n hg hn
    -- g·n ∈ gH; como gH = Hg, g·n ∈ Hg, luego ∃ h ∈ H, g·n = h·g
    have hgn_inleft : grp.op g n ∈ sub.leftCoset g := by
      rw [sub.mem_leftCoset hg]
      exact ⟨n, hn, rfl⟩
    rw [hcoe g hg] at hgn_inleft
    obtain ⟨h, hh, heq⟩ := (sub.mem_rightCoset hg).mp hgn_inleft
    -- heq : g·n = h·g  →  g·n·g⁻¹ = h ∈ H
    have : grp.op (grp.op g n) (grp.inv g) = h :=
      calc grp.op (grp.op g n) (grp.inv g)
          = grp.op (grp.op h g) (grp.inv g) := by rw [heq]
        _ = grp.op h (grp.op g (grp.inv g)) :=
                grp.op_assoc (sub.H_sub hh) hg (grp.inv_closed hg)
        _ = grp.op h grp.e := by rw [grp.op_inv_right hg]
        _ = h := grp.op_id_right (sub.H_sub hh)
    rw [this]; exact hh

-- ─────────────────────────────────────────────────────────────────
-- §9. El núcleo de un homomorfismo es normal
-- ─────────────────────────────────────────────────────────────────

/-- El núcleo de cualquier homomorfismo de grupos es un subgrupo normal. -/
theorem HFGroupHom.ker_isNormal {G H : HFGroup} (φ : HFGroupHom G H) :
    φ.ker.isNormal := by
  intro g n hg hn
  -- hn : n ∈ ker.H = HFSet.sep G.G (fun a => φ.f a = H.e)
  have hn' : n ∈ G.G ∧ φ.f n = H.e :=
    (HFSet.mem_sep G.G (fun a => φ.f a = H.e) n).mp hn
  apply (HFSet.mem_sep G.G (fun a => φ.f a = H.e) _).mpr
  refine ⟨G.op_closed (G.op_closed hg hn'.1) (G.inv_closed hg), ?_⟩
  -- φ(g·n·g⁻¹) = φ(g)·φ(n)·φ(g)⁻¹ = φ(g)·H.e·φ(g)⁻¹ = φ(g)·φ(g)⁻¹ = H.e
  rw [φ.f_hom (G.op_closed hg hn'.1) (G.inv_closed hg),
      φ.f_hom hg hn'.1, hn'.2,
      H.op_id_right (φ.f_mem hg),
      φ.hom_inv hg,
      H.op_inv_right (φ.f_mem hg)]

end HFAlgebra
