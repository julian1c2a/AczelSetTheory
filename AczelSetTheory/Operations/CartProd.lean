/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Operations/CartProd.lean
-- Producto cartesiano computable a nivel CList, levantado a HFSet.

import AczelSetTheory.Operations.OrderedPair

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- Par ordenado de Kuratowski a nivel CList
-- ─────────────────────────────────────────────────────────────────

/-- Par ordenado de Kuratowski a nivel CList: mkOrderedPairCList a b = {{a}, {a,b}}. -/
def mkOrderedPairCList (a b : CList) : CList :=
  mkPair (mkPair a a) (mkPair a b)

/-- El par ordenado HFSet-level se reduce a mkOrderedPairCList por rfl. -/
theorem orderedPair_eq_mk (a b : CList) :
    ⟪Quotient.mk CList.Setoid a, Quotient.mk CList.Setoid b⟫ =
    Quotient.mk CList.Setoid (mkOrderedPairCList a b) := rfl

-- ─────────────────────────────────────────────────────────────────
-- Auxiliares PList/CList privados
-- ─────────────────────────────────────────────────────────────────

/-- PList.Mem y → CList.mem y. -/
private theorem clist_mem_of_plist_mem (y : CList) (xs : PList CList)
    (h : PList.Mem y xs) : CList.mem y (CList.mk xs) = true := by
  induction xs with
  | nil => exact absurd h (PList.not_mem_nil _)
  | cons z zs ih =>
    rw [CList.mem_cons, Bool.or_eq_true]
    cases h with
    | head => exact Or.inl (CList.extEq_refl y)
    | tail ht => exact Or.inr (ih ht)

/-- CList.mem → existencia de testigo PList.Mem + extEq. -/
private theorem clist_mem_exists_plist_mem (x : CList) (xs : PList CList)
    (h : CList.mem x (CList.mk xs) = true) :
    ∃ y, PList.Mem y xs ∧ CList.extEq x y = true := by
  induction xs with
  | nil => simp [CList.mem_nil] at h
  | cons z zs ih =>
    rw [CList.mem_cons, Bool.or_eq_true] at h
    rcases h with h_eq | h_mem
    · exact ⟨z, PList.Mem.head, h_eq⟩
    · obtain ⟨y, hy_mem, hy_eq⟩ := ih h_mem
      exact ⟨y, PList.Mem.tail hy_mem, hy_eq⟩

/-- Membresía en flatMap. -/
private theorem Mem_flatMap {α β : Type} (f : α → PList β) (x : β) (l : PList α) :
    PList.Mem x (PList.flatMap f l) ↔ ∃ a, PList.Mem a l ∧ PList.Mem x (f a) := by
  induction l with
  | nil =>
    simp only [PList.flatMap_nil]
    exact ⟨fun h => absurd h (PList.not_mem_nil _),
           fun ⟨_, ha, _⟩ => absurd ha (PList.not_mem_nil _)⟩
  | cons head tail ih =>
    simp only [PList.flatMap_cons, PList.Mem_append, ih, PList.Mem_cons_iff]
    constructor
    · rintro (hx | ⟨a, ha, hxa⟩)
      · exact ⟨head, Or.inl rfl, hx⟩
      · exact ⟨a, Or.inr ha, hxa⟩
    · rintro ⟨a, (rfl | ha), hxa⟩
      · exact Or.inl hxa
      · exact Or.inr ⟨a, ha, hxa⟩

-- ─────────────────────────────────────────────────────────────────
-- mkPair y mkOrderedPairCList respetan extEq
-- ─────────────────────────────────────────────────────────────────

private theorem mkPair_extEq {a₁ a₂ b₁ b₂ : CList}
    (ha : CList.extEq a₁ a₂ = true) (hb : CList.extEq b₁ b₂ = true) :
    CList.extEq (mkPair a₁ b₁) (mkPair a₂ b₂) = true := by
  simp only [mkPair, CList.extEq_def, Bool.and_eq_true]
  constructor
  · rw [CList.subset_cons, Bool.and_eq_true]
    exact ⟨by rw [CList.mem_cons, CList.mem_cons, CList.mem_nil, Bool.or_false,
                   Bool.or_eq_true]; exact Or.inl ha,
           by rw [CList.subset_cons, Bool.and_eq_true]
              exact ⟨by rw [CList.mem_cons, CList.mem_cons, CList.mem_nil, Bool.or_false,
                              Bool.or_eq_true]; exact Or.inr hb,
                     CList.subset_nil _⟩⟩
  · rw [CList.subset_cons, Bool.and_eq_true]
    exact ⟨by rw [CList.mem_cons, CList.mem_cons, CList.mem_nil, Bool.or_false,
                   Bool.or_eq_true]
              exact Or.inl (by rw [CList.extEq_comm]; exact ha),
           by rw [CList.subset_cons, Bool.and_eq_true]
              exact ⟨by rw [CList.mem_cons, CList.mem_cons, CList.mem_nil, Bool.or_false,
                              Bool.or_eq_true]
                        exact Or.inr (by rw [CList.extEq_comm]; exact hb),
                     CList.subset_nil _⟩⟩

private theorem mkOrderedPairCList_extEq {a₁ a₂ b₁ b₂ : CList}
    (ha : CList.extEq a₁ a₂ = true) (hb : CList.extEq b₁ b₂ = true) :
    CList.extEq (mkOrderedPairCList a₁ b₁) (mkOrderedPairCList a₂ b₂) = true :=
  mkPair_extEq (mkPair_extEq ha ha) (mkPair_extEq ha hb)

-- ─────────────────────────────────────────────────────────────────
-- Producto cartesiano a nivel CList
-- ─────────────────────────────────────────────────────────────────

/-- Producto cartesiano computable a nivel CList, como flatMap/map. -/
def cartProdCList (A B : CList) : CList :=
  match A, B with
  | CList.mk as, CList.mk bs =>
    CList.mk (as.flatMap (fun a => bs.map (fun b => mkOrderedPairCList a b)))

-- ─────────────────────────────────────────────────────────────────
-- Bien-definición: cartProdCList respeta extEq
-- ─────────────────────────────────────────────────────────────────

private theorem cartProdCList_subset_of_subset_subset
    (as₁ as₂ bs₁ bs₂ : PList CList)
    (hA : CList.subset (CList.mk as₁) (CList.mk as₂) = true)
    (hB : CList.subset (CList.mk bs₁) (CList.mk bs₂) = true) :
    CList.subset (cartProdCList (CList.mk as₁) (CList.mk bs₁))
                 (cartProdCList (CList.mk as₂) (CList.mk bs₂)) = true := by
  simp only [cartProdCList]
  rw [subset_iff_forall_mem_clist]
  intro z hz
  obtain ⟨p, hp_mem, hp_eq⟩ := clist_mem_exists_plist_mem z _ hz
  rw [Mem_flatMap] at hp_mem
  obtain ⟨a, ha_mem, hp_in_map⟩ := hp_mem
  rw [PList.Mem_map] at hp_in_map
  obtain ⟨b, hb_mem, rfl⟩ := hp_in_map
  -- hp_eq : CList.extEq z (mkOrderedPairCList a b) = true
  -- a ∈ as₁, b ∈ bs₁
  have ha_clist : CList.mem a (CList.mk as₁) = true := clist_mem_of_plist_mem a as₁ ha_mem
  have hb_clist : CList.mem b (CList.mk bs₁) = true := clist_mem_of_plist_mem b bs₁ hb_mem
  have ha₂ : CList.mem a (CList.mk as₂) = true :=
    CList.mem_subset a (CList.mk as₁) (CList.mk as₂) ha_clist hA
  have hb₂ : CList.mem b (CList.mk bs₂) = true :=
    CList.mem_subset b (CList.mk bs₁) (CList.mk bs₂) hb_clist hB
  obtain ⟨a', ha'_plist, ha'_eq⟩ := clist_mem_exists_plist_mem a as₂ ha₂
  obtain ⟨b', hb'_plist, hb'_eq⟩ := clist_mem_exists_plist_mem b bs₂ hb₂
  have hprod_eq : CList.extEq (mkOrderedPairCList a b) (mkOrderedPairCList a' b') = true :=
    mkOrderedPairCList_extEq ha'_eq hb'_eq
  have hz_a'b' : CList.extEq z (mkOrderedPairCList a' b') = true :=
    CList.extEq_trans z (mkOrderedPairCList a b) (mkOrderedPairCList a' b') hp_eq hprod_eq
  have ha'b'_plist : PList.Mem (mkOrderedPairCList a' b')
      (as₂.flatMap (fun a'' => bs₂.map (fun b'' => mkOrderedPairCList a'' b''))) := by
    rw [Mem_flatMap]
    refine ⟨a', ha'_plist, ?_⟩
    rw [PList.Mem_map]
    exact ⟨b', hb'_plist, rfl⟩
  exact CList.mem_of_extEq z (mkOrderedPairCList a' b') _
    hz_a'b' (clist_mem_of_plist_mem _ _ ha'b'_plist)

private theorem cartProdCList_extEq (A₁ B₁ A₂ B₂ : CList)
    (hA : CList.extEq A₁ A₂ = true) (hB : CList.extEq B₁ B₂ = true) :
    CList.extEq (cartProdCList A₁ B₁) (cartProdCList A₂ B₂) = true := by
  cases A₁ with | mk as₁ =>
  cases B₁ with | mk bs₁ =>
  cases A₂ with | mk as₂ =>
  cases B₂ with | mk bs₂ =>
  rw [CList.extEq_def, Bool.and_eq_true] at hA hB
  rw [CList.extEq_def, Bool.and_eq_true]
  exact ⟨cartProdCList_subset_of_subset_subset as₁ as₂ bs₁ bs₂ hA.1 hB.1,
         cartProdCList_subset_of_subset_subset as₂ as₁ bs₂ bs₁ hA.2 hB.2⟩

-- ─────────────────────────────────────────────────────────────────
-- Definición de cartProd a nivel HFSet
-- ─────────────────────────────────────────────────────────────────

/-- Producto cartesiano computable de HFSets. -/
def cartProd (A B : HFSet) : HFSet :=
  Quotient.liftOn₂ A B
    (fun a b => Quotient.mk CList.Setoid (cartProdCList a b))
    (fun a₁ b₁ a₂ b₂ ha hb =>
      Quotient.sound (cartProdCList_extEq a₁ b₁ a₂ b₂ ha hb))

/-- Notación A ×ₕ B para el producto cartesiano computable. -/
infixl:70 " ×ₕ " => cartProd

-- ─────────────────────────────────────────────────────────────────
-- Membresía en cartProdCList (expuesta para Axioms/CartProd.lean)
-- ─────────────────────────────────────────────────────────────────

/-- Caracterización de la membresía en cartProdCList vía CList.mem. -/
theorem mem_cartProdCList_iff (z : CList) (as bs : PList CList) :
    CList.mem z (cartProdCList (CList.mk as) (CList.mk bs)) = true ↔
    ∃ a b : CList, CList.mem a (CList.mk as) = true ∧
                   CList.mem b (CList.mk bs) = true ∧
                   CList.extEq z (mkOrderedPairCList a b) = true := by
  simp only [cartProdCList]
  constructor
  · intro hz
    obtain ⟨p, hp_mem, hp_eq⟩ := clist_mem_exists_plist_mem z _ hz
    rw [Mem_flatMap] at hp_mem
    obtain ⟨a, ha_mem, hp_in_map⟩ := hp_mem
    rw [PList.Mem_map] at hp_in_map
    obtain ⟨b, hb_mem, rfl⟩ := hp_in_map
    exact ⟨a, b, clist_mem_of_plist_mem a as ha_mem,
                 clist_mem_of_plist_mem b bs hb_mem, hp_eq⟩
  · rintro ⟨a, b, ha_mem, hb_mem, hz_eq⟩
    obtain ⟨a', ha'_plist, ha'_eq⟩ := clist_mem_exists_plist_mem a as ha_mem
    obtain ⟨b', hb'_plist, hb'_eq⟩ := clist_mem_exists_plist_mem b bs hb_mem
    have hprod_eq : CList.extEq (mkOrderedPairCList a b) (mkOrderedPairCList a' b') = true :=
      mkOrderedPairCList_extEq ha'_eq hb'_eq
    have hz_a'b' : CList.extEq z (mkOrderedPairCList a' b') = true :=
      CList.extEq_trans z (mkOrderedPairCList a b) (mkOrderedPairCList a' b') hz_eq hprod_eq
    have ha'b'_plist : PList.Mem (mkOrderedPairCList a' b')
        (as.flatMap (fun a'' => bs.map (fun b'' => mkOrderedPairCList a'' b''))) := by
      rw [Mem_flatMap]
      refine ⟨a', ha'_plist, ?_⟩
      rw [PList.Mem_map]
      exact ⟨b', hb'_plist, rfl⟩
    exact CList.mem_of_extEq z (mkOrderedPairCList a' b') _
      hz_a'b' (clist_mem_of_plist_mem _ _ ha'b'_plist)

end HFSet
