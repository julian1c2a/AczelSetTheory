import AczelSetTheory.CList.ExtEq
import AczelSetTheory.HFSets

namespace CList

def union (a b : CList) :
  CList
    :=
  match a, b with
  | mk xs, mk ys => mk (xs ++ ys)

theorem mem_union (z a b : CList) :
    mem z (union a b) = true ↔ mem z a = true ∨ mem z b = true := by
  cases a with | mk xs =>
  cases b with | mk ys =>
  induction xs with
  | nil =>
    simp only [union, List.nil_append, mem_nil]
    constructor
    · intro h
      exact Or.inr h
    · rintro (h1 | h2)
      · contradiction
      · exact h2
  | cons x xs ih =>
    simp only [union, List.cons_append, mem_cons, Bool.or_eq_true]
    constructor
    · rintro (hx | hxs_ys)
      · exact Or.inl (Or.inl hx)
      · rcases ih.mp hxs_ys with hxs | hys
        · exact Or.inl (Or.inr hxs)
        · exact Or.inr hys
    · rintro (hx_xs | hys)
      · rcases hx_xs with hx | hxs
        · exact Or.inl hx
        · exact Or.inr (ih.mpr (Or.inl hxs))
      · exact Or.inr (ih.mpr (Or.inr hys))

def sUnion (A : CList) :
  CList
    :=
  match A with
  | mk xs => mk (xs.flatMap (fun x => match x with | mk ys => ys))

theorem mem_sUnion (z A : CList) :
  mem z (sUnion A) = true ↔ ∃ Y, mem Y A = true ∧ mem z Y = true
    := by
  cases A with
  | mk xs =>
  induction xs with
  | nil =>
    simp only [sUnion, List.flatMap_nil, mem_nil]
    constructor
    · intro h; contradiction
    · rintro ⟨Y, hY, _⟩; contradiction
  | cons Y xs ih =>
    cases Y with | mk ys =>
    simp only [sUnion, List.flatMap_cons, mem_cons, Bool.or_eq_true]
    -- mem z (mk (ys ++ xs.flatMap ...)) = true
    have h_union : mem z (mk (ys ++ xs.flatMap (fun x => match x with | mk zs => zs))) = true ↔
      mem z (mk ys) = true ∨ mem z (mk (xs.flatMap (fun x => match x with | mk zs => zs))) = true := by
      exact mem_union z (mk ys) (mk (xs.flatMap (fun x => match x with | mk zs => zs)))
    rw [h_union]
    constructor
    · rintro (hy | hxs)
      · exact ⟨mk ys, Or.inl (extEq_refl _), hy⟩
      · rcases ih.mp hxs with ⟨Y', hY', hzY'⟩
        exact ⟨Y', Or.inr hY', hzY'⟩
    · rintro ⟨Y', hY' | hY', hzY'⟩
      · exact Or.inl (HFSet.mem_resp_right z Y' (mk ys) hY' hzY')
      · exact Or.inr (ih.mpr ⟨Y', hY', hzY'⟩)

theorem union_extEq
  (a₁ a₂ b₁ b₂ : CList) (ha : extEq a₁ a₂ = true) (hb : extEq b₁ b₂ = true) :
    extEq (union a₁ b₁) (union a₂ b₂) = true
      := by
  rw [extEq_def, Bool.and_eq_true]
  constructor
  · rw [HFSet.subset_iff_forall_mem_clist]
    intro x hx
    rw [mem_union] at hx ⊢
    cases hx with
    | inl h1 => exact Or.inl (mem_of_extEq x x a₂ (extEq_refl _) ((HFSet.mem_resp_right x a₁ a₂ ha) h1))
    | inr h2 => exact Or.inr (mem_of_extEq x x b₂ (extEq_refl _) ((HFSet.mem_resp_right x b₁ b₂ hb) h2))
  · rw [HFSet.subset_iff_forall_mem_clist]
    intro x hx
    rw [mem_union] at hx ⊢
    cases hx with
    | inl h1 => exact Or.inl (mem_of_extEq x x a₁ (extEq_refl _) ((HFSet.mem_resp_right x a₂ a₁ (by rw [extEq_comm]; exact ha)) h1))
    | inr h2 => exact Or.inr (mem_of_extEq x x b₁ (extEq_refl _) ((HFSet.mem_resp_right x b₂ b₁ (by rw [extEq_comm]; exact hb)) h2))

theorem sUnion_extEq
  (A₁ A₂ : CList) (hA : extEq A₁ A₂ = true) :
    extEq (sUnion A₁) (sUnion A₂) = true
      := by
  rw [extEq_def, Bool.and_eq_true]
  constructor
  · rw [HFSet.subset_iff_forall_mem_clist]
    intro x hx
    rw [mem_sUnion] at hx ⊢
    rcases hx with ⟨Y, hY, hxY⟩
    have hY_A2 : mem Y A₂ = true := HFSet.mem_resp_right Y A₁ A₂ hA hY
    exact ⟨Y, hY_A2, hxY⟩
  · rw [HFSet.subset_iff_forall_mem_clist]
    intro x hx
    rw [mem_sUnion] at hx ⊢
    rcases hx with ⟨Y, hY, hxY⟩
    have hY_A1 : mem Y A₁ = true := HFSet.mem_resp_right Y A₂ A₁ (by rw [extEq_comm]; exact hA) hY
    exact ⟨Y, hY_A1, hxY⟩

end CList

namespace HFSet

def union (A B : HFSet) :
  HFSet
    :=
  Quotient.liftOn₂ A B (fun a b => Quotient.mk CList.Setoid (CList.union a b))
    (fun _ _ _ _ ha hb => by
      apply Quotient.sound
      exact CList.union_extEq _ _ _ _ ha hb)

def sUnion (A : HFSet) :
  HFSet
    :=
  Quotient.liftOn A (fun a => Quotient.mk CList.Setoid (CList.sUnion a))
    (fun _ _ ha => by
      apply Quotient.sound
      exact CList.sUnion_extEq _ _ ha)

end HFSet
