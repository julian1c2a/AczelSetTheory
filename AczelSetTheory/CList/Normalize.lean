/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.CList.Sort

-- ==========================================
-- Normalización: cotas de tamaño, idempotencia,
-- sorted_nodup_setEquiv_eq
-- ==========================================

namespace CList

-- ─────────────────────────────────────────────────────────────────
-- Helper: plist_any_eq_true (reproduced locally; private in SetEquiv)
-- ─────────────────────────────────────────────────────────────────

private theorem plist_any_cons {α : Type} (p : α → Bool) (h : α) (t : PList α) :
    PList.any p (.cons h t) = (p h || PList.any p t) := rfl

private theorem plist_any_eq_true {α : Type} (p : α → Bool) (l : PList α) :
    PList.any p l = true ↔ ∃ x, PList.Mem x l ∧ p x = true := by
  induction l with
  | nil =>
    constructor
    · intro h; simp [PList.any] at h
    · intro ⟨x, hx, _⟩; exact absurd hx (PList.not_mem_nil _)
  | cons h t ih =>
    simp only [plist_any_cons, Bool.or_eq_true]
    constructor
    · rintro (hp | ht)
      · exact ⟨h, PList.Mem.head, hp⟩
      · obtain ⟨x, hx, hpx⟩ := ih.mp ht
        exact ⟨x, PList.Mem.tail hx, hpx⟩
    · rintro ⟨x, hx, hpx⟩
      cases hx with
      | head => exact Or.inl hpx
      | tail hxt => exact Or.inr (ih.mpr ⟨x, hxt, hpx⟩)

-- ─────────────────────────────────────────────────────────────────
-- Helper: membership in normalizePList
-- ─────────────────────────────────────────────────────────────────

private theorem mem_normalizePList {y : CList} {xs : PList CList} :
    PList.Mem y (normalizePList xs) ↔ ∃ x, PList.Mem x xs ∧ y = normalize x := by
  induction xs with
  | nil =>
    simp only [normalizePList]
    exact ⟨fun h => absurd h (PList.not_mem_nil _),
           fun ⟨_, hx, _⟩ => absurd hx (PList.not_mem_nil _)⟩
  | cons x rest ih =>
    simp only [normalizePList]
    constructor
    · intro hy
      cases hy with
      | head => exact ⟨x, PList.Mem.head, rfl⟩
      | tail hy' =>
          obtain ⟨w, hw, rfl⟩ := ih.mp hy'
          exact ⟨w, PList.Mem.tail hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      cases hw with
      | head => exact PList.Mem.head
      | tail hw' => exact PList.Mem.tail (ih.mpr ⟨w, hw', rfl⟩)

-- ==================================================================
-- sizeOf helper lemmas: relate sizeOf (CList.mk) and PList.cons
-- to arithmetic so omega can reason about sizes.
-- ==================================================================

-- For PList (non-nested parameterized inductive), rfl holds.
private theorem sizeOf_pcons_eq (x : CList) (xs : PList CList) :
    @Eq Nat (sizeOf (PList.cons x xs : PList CList)) (Nat.succ (sizeOf x + sizeOf xs)) := by
  simp_wf; omega

private theorem sizeOf_pnil_eq :
    sizeOf (PList.nil : PList CList) = (1 : Nat) := rfl

-- For CList (nested inductive), use simp_wf which includes the
-- relevant sizeOf reduction lemma.
private theorem sizeOf_mk_eq (xs : PList CList) :
    sizeOf (CList.mk xs) = (1 + sizeOf xs : Nat) := by simp_wf

-- ==================================================================
-- Size bounds (sizeOf : CList / PList CList → Nat) for termination
-- ==================================================================

private theorem sizeOf_lt_of_mem {x : CList} {xs : PList CList}
    (h : PList.Mem x xs) : sizeOf x < sizeOf (mk xs) := by
  induction h with
  | head => simp_wf; omega
  | tail _ ih =>
      simp only [sizeOf_mk_eq] at ih
      simp_wf
      omega

private theorem sizeOf_orderedInsert_le (x : CList) (l : PList CList) :
    sizeOf (orderedInsert x l) ≤ sizeOf (PList.cons x l) := by
  induction l with
  | nil => simp [orderedInsert]
  | cons y ys ih =>
    unfold orderedInsert
    by_cases hlt : lt x y = true
    · rw [if_pos hlt]; exact Nat.le_refl _
    · rw [if_neg hlt]
      by_cases heq : extEq x y = true
      · rw [if_pos heq]
        simp only [sizeOf_pcons_eq]; omega
      · rw [if_neg heq]
        simp only [sizeOf_pcons_eq] at *; omega

private theorem sizeOf_insertionSort_le (l : PList CList) :
    sizeOf (insertionSort l) ≤ sizeOf l := by
  induction l with
  | nil => simp [insertionSort]
  | cons x t ih =>
    simp only [insertionSort]
    have h := sizeOf_orderedInsert_le x (insertionSort t)
    simp only [sizeOf_pcons_eq] at *; omega

private theorem sizeOf_dedup_le (l : PList CList) :
    sizeOf (dedup l) ≤ sizeOf l := by
  suffices h : ∀ (l' vistos : PList CList), sizeOf (dedupAux l' vistos) ≤ sizeOf l' from by
    unfold dedup; exact h l .nil
  intro l'
  induction l' with
  | nil => intros; simp [dedupAux]
  | cons x xs ih =>
    intro vistos
    simp only [dedupAux]
    by_cases h : PList.any (fun y => extEq x y) vistos = true
    · rw [if_pos h]
      have h_ih := ih vistos
      simp only [sizeOf_pcons_eq] at *; omega
    · rw [if_neg h]
      have h_ih := ih (.cons x vistos)
      simp only [sizeOf_pcons_eq] at *; omega

mutual
  private theorem normalize_sizeOf_le (A : CList) : sizeOf (normalize A) ≤ sizeOf A :=
    match A with
    | mk xs => by
        have h1 := normalizePList_sizeOf_le xs
        have h2 := sizeOf_dedup_le (normalizePList xs)
        have h3 := sizeOf_insertionSort_le (dedup (normalizePList xs))
        show sizeOf (CList.mk (insertionSort (dedup (normalizePList xs)))) ≤ sizeOf (CList.mk xs)
        simp only [sizeOf_mk_eq]
        omega
  termination_by Nat.add (sizeOf A) (sizeOf A)
  decreasing_by all_goals simp_wf; all_goals omega

  private theorem normalizePList_sizeOf_le (xs : PList CList) :
      sizeOf (normalizePList xs) ≤ sizeOf xs :=
    match xs with
    | .nil      => by simp [normalizePList]
    | .cons x t => by
        have hx := normalize_sizeOf_le x
        have ht := normalizePList_sizeOf_le t
        show sizeOf (PList.cons (normalize x) (normalizePList t)) ≤ sizeOf (PList.cons x t)
        simp only [sizeOf_pcons_eq]
        omega
  termination_by Nat.add (Nat.add (sizeOf xs) (sizeOf xs)) 1
  decreasing_by all_goals simp_wf; all_goals omega
end

-- ==================================================================
-- mem_of_mem_dedup
-- ==================================================================

private theorem mem_of_mem_dedupAux :
    ∀ (l : PList CList) (vistos : PList CList) (y : CList),
    PList.Mem y (dedupAux l vistos) → PList.Mem y l
  | .nil, _, _, h => absurd h (PList.not_mem_nil _)
  | .cons x xs, vistos, y, h => by
      simp only [dedupAux] at h
      by_cases hseen : PList.any (fun z => extEq x z) vistos = true
      · rw [if_pos hseen] at h
        exact PList.Mem.tail (mem_of_mem_dedupAux xs vistos y h)
      · rw [if_neg hseen] at h
        cases h with
        | head => exact PList.Mem.head
        | tail h' => exact PList.Mem.tail (mem_of_mem_dedupAux xs (.cons x vistos) y h')

theorem mem_of_mem_dedup
    (l : PList CList) (y : CList) (h : PList.Mem y (dedup l)) :
    PList.Mem y l :=
  mem_of_mem_dedupAux l .nil y h

-- ==================================================================
-- Idempotencia de dedup e insertionSort
-- ==================================================================

theorem dedup_id_of_nodup
    (l : PList CList) (h : Nodup l) :
    dedup l = l := by
  suffices ∀ (l' : PList CList) (vistos : PList CList),
      Nodup l' →
      (∀ x ∈ l', PList.any (fun v => extEq x v) vistos = false) →
      dedupAux l' vistos = l' by
    unfold dedup
    exact this l .nil h (fun _ _ => rfl)
  intro l'
  induction l' with
  | nil => intros; rfl
  | cons x xs ih =>
    intro vistos hnd hfresh
    obtain ⟨hx_nd, hxs_nd⟩ := hnd
    have hx_fresh : PList.any (fun v => extEq x v) vistos = false :=
      hfresh x PList.Mem.head
    have hx_not_seen : ¬PList.any (fun v => extEq x v) vistos = true :=
      Bool.eq_false_iff.mp hx_fresh
    simp only [dedupAux, if_neg hx_not_seen]
    congr 1
    apply ih (.cons x vistos) hxs_nd
    intro y hy
    have hy_fresh := hfresh y (PList.Mem.tail hy)
    simp only [plist_any_cons, Bool.or_eq_false_iff]
    exact ⟨by rw [extEq_comm]; exact hx_nd y hy, hy_fresh⟩

theorem insertionSort_id_of_sorted_nodup
    (l : PList CList) (hs : Sorted l) (hn : Nodup l) :
    insertionSort l = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    match xs, hs, hn with
    | .nil, _, _ => simp [insertionSort, orderedInsert]
    | .cons y ys, hs, hn =>
      have hxy     : lt x y = true       := hs.1
      have hs_tail : Sorted (.cons y ys) := hs.2
      obtain ⟨_, hn_tail⟩ := hn
      show orderedInsert x (insertionSort (.cons y ys)) = .cons x (.cons y ys)
      rw [ih hs_tail hn_tail]
      unfold orderedInsert
      rw [if_pos hxy]

-- ==================================================================
-- Idempotencia de normalize
-- ==================================================================

private theorem normalizePList_fixed :
    ∀ (xs : PList CList), (∀ y ∈ xs, normalize y = y) → normalizePList xs = xs
  | .nil, _ => rfl
  | .cons x rest, h => by
      simp only [normalizePList, PList.cons.injEq]
      exact ⟨h x PList.Mem.head,
             normalizePList_fixed rest (fun y hy => h y (PList.Mem.tail hy))⟩

mutual
  theorem normalize_idem :
    (A : CList) → normalize (normalize A) = normalize A
    | mk xs => by
        have h_fixed : ∀ y ∈ insertionSort (dedup (normalizePList xs)), normalize y = y :=
          fun y hy => normalize_idem_plist xs y
            (mem_of_mem_dedup _ y (insertionSort_mem_subset y _ hy))
        have h_nodup  := insertionSort_nodup _ (dedup_nodup (normalizePList xs))
        have h_sorted := insertionSort_sorted (dedup (normalizePList xs))
        simp only [normalize]
        congr 1
        rw [normalizePList_fixed _ h_fixed,
            dedup_id_of_nodup _ h_nodup,
            insertionSort_id_of_sorted_nodup _ h_sorted h_nodup]
  termination_by A => Nat.add (sizeOf A) (sizeOf A)
  decreasing_by all_goals simp_wf; all_goals omega

  private theorem normalize_idem_plist :
    (xs : PList CList) → (y : CList) → PList.Mem y (normalizePList xs) → normalize y = y
    | .nil, _, h => absurd h (PList.not_mem_nil _)
    | .cons x rest, y, h => by
        unfold normalizePList at h
        cases h with
        | head => exact normalize_idem x
        | tail hy => exact normalize_idem_plist rest y hy
  termination_by xs _ _ => Nat.add (Nat.add (sizeOf xs) (sizeOf xs)) 1
  decreasing_by all_goals simp_wf; all_goals omega
end

-- ==================================================================
-- Unicidad: sorted_nodup_setEquiv_eq
-- ==================================================================

private theorem Sorted.tail {a : CList} {l : PList CList}
    (h : Sorted (.cons a l)) : Sorted l :=
  match l with
  | .nil      => trivial
  | .cons _ _ => h.2

private theorem sorted_mem_lt {a : CList} {l : PList CList}
    (hs : Sorted (.cons a l)) (hm : PList.Mem b l) : lt a b = true :=
  match l, hm with
  | .cons _ _,    .head      => hs.1
  | .cons c rest, .tail hrest => lt_trans a c b hs.1 (sorted_mem_lt hs.2 hrest)
termination_by sizeOf l
decreasing_by simp_wf; simp [sizeOf]; omega

theorem sorted_nodup_setEquiv_eq :
    ∀ (l₁ l₂ : PList CList),
    Sorted l₁ → Sorted l₂ →
    Nodup l₁ → Nodup l₂ →
    SetEquiv l₁ l₂ →
    (∀ a ∈ l₁, ∀ b ∈ l₂, extEq a b = true → a = b) →
    l₁ = l₂
  | .nil, l₂, _, _, _, _, hequiv, _ => by
      cases l₂ with
      | nil => rfl
      | cons y ys =>
          exfalso
          have hmem : PList.any (fun z => extEq y z) (.cons y ys) = true := by
            simp [PList.any_cons, extEq_refl]
          have := (hequiv y).mpr hmem
          simp [PList.any_nil] at this
  | .cons x xs, .nil, _, _, _, _, hequiv, _ => by
      exfalso
      have hmem : PList.any (fun z => extEq x z) (.cons x xs) = true := by
        simp [PList.any_cons, extEq_refl]
      have := (hequiv x).mp hmem
      simp [PList.any_nil] at this
  | .cons x xs, .cons y ys, hs1, hs2, hn1, hn2, hequiv, hprop => by
      -- Step 1: extEq x y = true
      have hxy_extEq : extEq x y = true := by
        have hx_in : PList.any (fun z => extEq x z) (.cons y ys) = true :=
          (hequiv x).mp (by simp [PList.any_cons, extEq_refl])
        simp only [PList.any_cons, Bool.or_eq_true] at hx_in
        rcases hx_in with h | h
        · exact h
        · have hy_in_l1 : PList.any (fun z => extEq y z) (.cons x xs) = true :=
            (hequiv y).mpr (by simp [PList.any_cons, extEq_refl])
          simp only [PList.any_cons, Bool.or_eq_true] at hy_in_l1
          rcases hy_in_l1 with h_yx | h_yx
          · rwa [extEq_comm]
          · obtain ⟨w, hw_mem, hw_eq⟩ := (plist_any_eq_true _ _).mp h_yx
            have hw_eq_y : w = y :=
              hprop w (PList.Mem.tail hw_mem) y PList.Mem.head
                (by rwa [extEq_comm])
            have hy_in_xs : PList.Mem y xs := hw_eq_y ▸ hw_mem
            obtain ⟨v, hv_mem, hv_eq⟩ := (plist_any_eq_true _ _).mp h
            have hv_eq_x : x = v :=
              hprop x PList.Mem.head v (PList.Mem.tail hv_mem) hv_eq
            have hx_in_ys : PList.Mem x ys := hv_eq_x.symm ▸ hv_mem
            exact absurd (sorted_mem_lt hs2 hx_in_ys)
              (by rw [lt_asymm x y (sorted_mem_lt hs1 hy_in_xs)]; simp)
      -- Step 2: x = y
      have hxy_eq : x = y :=
        hprop x PList.Mem.head y PList.Mem.head hxy_extEq
      -- Step 3: tails are SetEquiv
      have htail_equiv : SetEquiv xs ys := by
        intro z
        have hfull := hequiv z
        simp only [PList.any_cons, Bool.or_eq_true] at hfull
        constructor
        · intro hz_xs
          rcases hfull.mp (Or.inr hz_xs) with h | h
          · exfalso
            obtain ⟨w, hw_mem, hw_eq⟩ := (plist_any_eq_true _ _).mp hz_xs
            obtain ⟨hx_nd, _⟩ := hn1
            have hxw : extEq x w = true := extEq_trans x z w (by
              have hzx : extEq z x = true := by rwa [hxy_eq]
              rwa [extEq_comm]) hw_eq
            simp [hx_nd w hw_mem] at hxw
          · exact h
        · intro hz_ys
          rcases hfull.mpr (Or.inr hz_ys) with h | h
          · exfalso
            obtain ⟨w, hw_mem, hw_eq⟩ := (plist_any_eq_true _ _).mp hz_ys
            obtain ⟨hy_nd, _⟩ := hn2
            have hyw : extEq y w = true := extEq_trans y z w (by
              have hzy : extEq z y = true := by rwa [← hxy_eq]
              rwa [extEq_comm]) hw_eq
            simp [hy_nd w hw_mem] at hyw
          · exact h
      -- Step 4: IH on tails
      have hs1' : Sorted xs := hs1.tail
      have hs2' : Sorted ys := hs2.tail
      obtain ⟨_, hn1'⟩ := hn1
      obtain ⟨_, hn2'⟩ := hn2
      have hprop' : ∀ a ∈ xs, ∀ b ∈ ys, extEq a b = true → a = b :=
        fun a ha b hb hab =>
          hprop a (PList.Mem.tail ha) b (PList.Mem.tail hb) hab
      have htails := sorted_nodup_setEquiv_eq xs ys hs1' hs2' hn1' hn2' htail_equiv hprop'
      rw [hxy_eq, htails]

theorem extEq_normalize
    (A : CList) :
    extEq A (normalize A) = true := by
  match A with
  | mk xs =>
    simp only [normalize]
    rw [extEq_mk_iff_setEquiv]
    have ih_all : ∀ w ∈ xs, extEq w (normalize w) = true := fun w hw =>
      have : sizeOf w < sizeOf (mk xs) := sizeOf_lt_of_mem hw
      extEq_normalize w
    apply SetEquiv.trans (l₂ := normalizePList xs)
    · intro z
      constructor
      · intro hz
        obtain ⟨w, hw_mem, hw_eq⟩ := (plist_any_eq_true _ _).mp hz
        apply (plist_any_eq_true _ _).mpr
        exact ⟨normalize w, mem_normalizePList.mpr ⟨w, hw_mem, rfl⟩,
               extEq_trans z w (normalize w) hw_eq (ih_all w hw_mem)⟩
      · intro hz
        obtain ⟨w_norm, hw_norm_mem, hw_norm_eq⟩ := (plist_any_eq_true _ _).mp hz
        obtain ⟨w, hw_mem, rfl⟩ := mem_normalizePList.mp hw_norm_mem
        apply (plist_any_eq_true _ _).mpr
        have hw_ih : extEq (normalize w) w = true := by
          rw [extEq_comm]; exact ih_all w hw_mem
        exact ⟨w, hw_mem, extEq_trans z (normalize w) w hw_norm_eq hw_ih⟩
    · apply SetEquiv.trans (l₂ := dedup (normalizePList xs))
      · exact SetEquiv.symm (dedup_setEquiv_self _)
      · exact SetEquiv.symm (insertionSort_setEquiv _)
termination_by sizeOf A
decreasing_by
  all_goals simp_wf
  all_goals have h := sizeOf_lt_of_mem hw
  all_goals simp only [sizeOf_mk_eq] at h
  all_goals omega

/-!
Dadas dos CList A y B que son extensionalmente iguales,
sus formas normales son idénticas.
-/
theorem normalize_eq_of_extEq {A B : CList}
    (h : CList.extEq A B = true) :
    CList.normalize A = CList.normalize B := by
  match A, B with
  | CList.mk xs, CList.mk ys =>
    simp only [CList.normalize]
    congr 1
    apply sorted_nodup_setEquiv_eq
    -- (1) Sorted
    · exact insertionSort_sorted _
    · exact insertionSort_sorted _
    -- (2) Nodup
    · exact insertionSort_nodup _ (dedup_nodup _)
    · exact insertionSort_nodup _ (dedup_nodup _)
    -- (3) SetEquiv
    · have h_nxs_nys : SetEquiv (normalizePList xs) (normalizePList ys) := by
        rw [extEq_mk_iff_setEquiv] at h
        intro z
        constructor
        · intro hz
          obtain ⟨w, hw_mem, hw_eq⟩ := (plist_any_eq_true _ _).mp hz
          obtain ⟨xi, hxi_mem, rfl⟩ := mem_normalizePList.mp hw_mem
          have hxi_in_ys :=
            (h xi).mp ((plist_any_eq_true _ _).mpr ⟨xi, hxi_mem, extEq_refl xi⟩)
          obtain ⟨yj, hyj_mem, hyj_eq⟩ := (plist_any_eq_true _ _).mp hxi_in_ys
          have hIH : normalize xi = normalize yj := normalize_eq_of_extEq hyj_eq
          exact (plist_any_eq_true _ _).mpr
            ⟨normalize yj, mem_normalizePList.mpr ⟨yj, hyj_mem, rfl⟩, hIH ▸ hw_eq⟩
        · intro hz
          obtain ⟨w, hw_mem, hw_eq⟩ := (plist_any_eq_true _ _).mp hz
          obtain ⟨yj, hyj_mem, rfl⟩ := mem_normalizePList.mp hw_mem
          have hyj_in_xs :=
            (h yj).mpr ((plist_any_eq_true _ _).mpr ⟨yj, hyj_mem, extEq_refl yj⟩)
          obtain ⟨xi, hxi_mem, hxi_eq⟩ := (plist_any_eq_true _ _).mp hyj_in_xs
          have hIH : normalize yj = normalize xi := normalize_eq_of_extEq hxi_eq
          exact (plist_any_eq_true _ _).mpr
            ⟨normalize xi, mem_normalizePList.mpr ⟨xi, hxi_mem, rfl⟩, hIH ▸ hw_eq⟩
      exact SetEquiv.trans (insertionSort_setEquiv _)
        (SetEquiv.trans (dedup_setEquiv_self _)
          (SetEquiv.trans h_nxs_nys
            (SetEquiv.trans (SetEquiv.symm (dedup_setEquiv_self _))
              (SetEquiv.symm (insertionSort_setEquiv _)))))
    -- (4) extEq a b = true → a = b  for elements of the two sorted lists
    · intro a ha b hb hab
      have ha' := mem_of_mem_dedup _ a (insertionSort_mem_subset a _ ha)
      obtain ⟨xi, hxi_mem, rfl⟩ := mem_normalizePList.mp ha'
      have hb' := mem_of_mem_dedup _ b (insertionSort_mem_subset b _ hb)
      obtain ⟨yj, hyj_mem, rfl⟩ := mem_normalizePList.mp hb'
      have hIH := normalize_eq_of_extEq hab
      rwa [normalize_idem, normalize_idem] at hIH
termination_by Nat.add (sizeOf A) (sizeOf B)
decreasing_by
  all_goals simp_wf
  all_goals have h3 := sizeOf_lt_of_mem hxi_mem
  all_goals have h4 := sizeOf_lt_of_mem hyj_mem
  all_goals (try have h1 := normalize_sizeOf_le xi)
  all_goals (try have h2 := normalize_sizeOf_le yj)
  all_goals simp only [sizeOf_mk_eq] at h3 h4
  all_goals omega

theorem extEq_iff_normalize_eq {A B : CList} :
    extEq A B = true ↔ normalize A = normalize B := by
  constructor
  · exact normalize_eq_of_extEq
  · intro h
    have ha : extEq A (normalize A) = true := extEq_normalize A
    have hb : extEq B (normalize B) = true := extEq_normalize B
    have hb_symm : extEq (normalize B) B = true := by rw [extEq_comm]; exact hb
    have h1 : extEq A (normalize B) = true := by rw [h] at ha; exact ha
    exact extEq_trans A (normalize B) B h1 hb_symm

end CList
