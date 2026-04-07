import AczelSetTheory.HFSets

namespace CList

def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | a :: as =>
    let rest := sublists as
    rest ++ rest.map (a :: ·)

/-- Toda sublista de `xs` es subconjunto de `mk xs`. -/
theorem sublists_subset (xs : List CList) (zs : List CList)
    (h : zs ∈ sublists xs) :
    subset (mk zs) (mk xs) = true := by
  induction xs with
  | nil =>
    simp only [sublists, List.mem_cons, List.mem_nil_iff, or_false] at h
    rw [h]; exact subset_nil (mk [])
  | cons x xs' ih =>
    simp only [sublists, List.mem_append, List.mem_map] at h
    rcases h with h_in_rest | ⟨ws, h_ws_in_rest, rfl⟩
    · exact subset_mono zs x xs' (ih zs h_in_rest)
    · rw [subset_cons, Bool.and_eq_true]
      constructor
      · rw [mem_cons, Bool.or_eq_true]; exact Or.inl (extEq_refl x)
      · exact subset_mono ws x xs' (ih ws h_ws_in_rest)

/-- `List.filter P xs` es miembro de `sublists xs`. -/
theorem filter_in_sublists {α : Type} (P : α → Bool) (xs : List α) :
    xs.filter P ∈ sublists xs := by
  induction xs with
  | nil => simp [sublists, List.filter_nil]
  | cons a as ih =>
    simp only [sublists, List.mem_append, List.mem_map, List.filter_cons]
    split
    · -- P a = true: filter = a :: filter P as
      exact Or.inr ⟨as.filter P, ih, rfl⟩
    · -- P a = false: filter = filter P as
      exact Or.inl ih

/-- `fun z => mem z y` respeta la igualdad extensional. -/
theorem mem_right_respects_extEq (y : CList) :
    P_respects (fun z => mem z y) := by
  intro a b hab
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro ha
    exact mem_of_extEq b a y (by rw [extEq_comm]; exact hab) ha
  · intro hb
    exact mem_of_extEq a b y hab hb

end CList

namespace HFSet

def powersetCList (A : CList) : CList :=
  match A with
  | CList.mk xs => CList.mk (CList.sublists xs |>.map CList.mk)

/-- Caracterización fundamental de la pertenencia al powerset a nivel CList:
    `y ∈ powerset(A) ↔ y ⊆ A`. -/
theorem mem_powersetCList (y A : CList) :
    CList.mem y (powersetCList A) = true ↔ CList.subset y A = true := by
  match A with
  | CList.mk xs =>
    constructor
    · -- Forward: y ∈ powerset(A) → y ⊆ A
      intro h
      simp only [powersetCList] at h
      rw [CList.mem_eq_any, List.any_eq_true] at h
      obtain ⟨w, hw, hyw⟩ := h
      rw [List.mem_map] at hw
      obtain ⟨zs, hzs, rfl⟩ := hw
      have h_sub_zs : CList.subset (CList.mk zs) (CList.mk xs) = true :=
        CList.sublists_subset xs zs hzs
      have h_sub_y : CList.subset y (CList.mk zs) = true := by
        rw [CList.extEq_def, Bool.and_eq_true] at hyw; exact hyw.1
      exact CList.subset_trans y (CList.mk zs) (CList.mk xs) h_sub_y h_sub_zs
    · -- Backward: y ⊆ A → y ∈ powerset(A)
      intro h
      let P := fun z => CList.mem z y
      have hP_resp : CList.P_respects P := CList.mem_right_respects_extEq y
      -- filtered ∈ sublists xs
      have h_filtered : xs.filter P ∈ CList.sublists xs :=
        CList.filter_in_sublists P xs
      -- subset y (mk filtered): todo elem de y está en el filtrado
      have h_sub1 : CList.subset y (CList.mk (xs.filter P)) = true := by
        rw [CList.subset_iff_forall_mem_clist]
        intro w hw
        have hw_xs : CList.mem w (CList.mk xs) = true :=
          CList.mem_subset w y (CList.mk xs) hw h
        exact CList.mem_filter_of_mem P hP_resp w xs hw_xs hw
      -- subset (mk filtered) y: todo elem del filtrado está en y
      have h_sub2 : CList.subset (CList.mk (xs.filter P)) y = true := by
        rw [CList.subset_iff_forall_mem_clist]
        intro w hw
        exact CList.P_of_mem_filter P hP_resp w xs hw
      -- extEq y (mk filtered)
      have h_extEq : CList.extEq y (CList.mk (xs.filter P)) = true := by
        rw [CList.extEq_def, Bool.and_eq_true]; exact ⟨h_sub1, h_sub2⟩
      -- mem y (powersetCList (mk xs))
      simp only [powersetCList]
      rw [CList.mem_eq_any, List.any_eq_true]
      exact ⟨CList.mk (xs.filter P),
             List.mem_map_of_mem CList.mk h_filtered,
             h_extEq⟩

theorem powersetCList_extEq (A₁ A₂ : CList) (h : CList.extEq A₁ A₂ = true) :
    CList.extEq (powersetCList A₁) (powersetCList A₂) = true := by
  rw [CList.extEq_def, Bool.and_eq_true]
  have h12 : CList.subset A₁ A₂ = true := by
    rw [CList.extEq_def, Bool.and_eq_true] at h; exact h.1
  have h21 : CList.subset A₂ A₁ = true := by
    rw [CList.extEq_def, Bool.and_eq_true] at h; exact h.2
  constructor
  · rw [CList.subset_iff_forall_mem_clist]
    intro y hy
    rw [mem_powersetCList] at hy ⊢
    exact CList.subset_trans y A₁ A₂ hy h12
  · rw [CList.subset_iff_forall_mem_clist]
    intro y hy
    rw [mem_powersetCList] at hy ⊢
    exact CList.subset_trans y A₂ A₁ hy h21

def powerset (A : HFSet) : HFSet :=
  Quotient.liftOn A
    (fun a => Quotient.mk CList.Setoid (powersetCList a))
    (fun a₁ a₂ ha => by
      apply Quotient.sound
      exact powersetCList_extEq a₁ a₂ ha)

end HFSet
