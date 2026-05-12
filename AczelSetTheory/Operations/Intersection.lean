import AczelSetTheory.HFSets
import AczelSetTheory.CList.Filter

namespace HFSet

def interCList (a b : CList) : CList :=
  match a with
  | CList.mk xs => CList.mk (xs.filter (fun c => CList.mem c b))

theorem interCList_extEq_left
  (a₁ a₂ b : CList) (ha : CList.extEq a₁ a₂ = true) :
    CList.extEq (interCList a₁ b) (interCList a₂ b) = true
      := by
  cases a₁ with | mk xs₁ =>
  cases a₂ with | mk xs₂ =>
  have hP_resp : CList.P_respects (fun c => CList.mem c b) := by
    intro x y heq
    dsimp
    cases h1 : CList.mem x b
    · cases h2 : CList.mem y b
      · rfl
      · have := (mem_resp_left x y b heq).mpr h2
        rw [h1] at this; contradiction
    · cases h2 : CList.mem y b
      · have := (mem_resp_left x y b heq).mp h1
        rw [h2] at this; contradiction
      · rfl
  exact CList.extEq_filter (fun c => CList.mem c b) hP_resp xs₁ xs₂ ha

theorem interCList_extEq_right
  (a b₁ b₂ : CList) (hb : CList.extEq b₁ b₂ = true) :
    CList.extEq (interCList a b₁) (interCList a b₂) = true
      := by
  cases a with | mk xs =>
  dsimp [interCList]
  have h_eq : (fun c => CList.mem c b₁) = (fun c => CList.mem c b₂) := by
    funext c
    dsimp
    have h1 : CList.mem c b₁ = true → CList.mem c b₂ = true := mem_resp_right c b₁ b₂ hb
    have hb_symm : CList.extEq b₂ b₁ = true := by
      rw [CList.extEq_comm]
      exact hb
    have h2 : CList.mem c b₂ = true → CList.mem c b₁ = true := mem_resp_right c b₂ b₁ hb_symm
    cases hc1 : CList.mem c b₁
    · cases hc2 : CList.mem c b₂
      · rfl
      · specialize h2 hc2; rw [hc1] at h2; contradiction
    · cases hc2 : CList.mem c b₂
      · specialize h1 hc1; rw [hc2] at h1; contradiction
      · rfl
  rw [h_eq]
  exact CList.extEq_refl (CList.mk (xs.filter (fun c => CList.mem c b₂)))

theorem interCList_extEq_extEq
  (a₁ a₂ b₁ b₂ : CList) (ha : CList.extEq a₁ a₂ = true) (hb : CList.extEq b₁ b₂ = true) :
    CList.extEq (interCList a₁ b₁) (interCList a₂ b₂) = true
      := by
  have h1 : CList.extEq (interCList a₁ b₁) (interCList a₂ b₁) = true := interCList_extEq_left a₁ a₂ b₁ ha
  have h2 : CList.extEq (interCList a₂ b₁) (interCList a₂ b₂) = true := interCList_extEq_right a₂ b₁ b₂ hb
  exact CList.extEq_trans (interCList a₁ b₁) (interCList a₂ b₁) (interCList a₂ b₂) h1 h2

/-- Operación Intersección para HFSet -/
def inter (A B : HFSet) : HFSet :=
  Quotient.liftOn₂ A B
    (fun a b => Quotient.mk CList.Setoid (interCList a b))
    (fun a₁ b₁ a₂ b₂ ha hb => by
      apply Quotient.sound
      exact interCList_extEq_extEq a₁ a₂ b₁ b₂ ha hb)

-- ─────────────────────────────────────────────────────────────────
-- Big intersection ⋂F
-- ─────────────────────────────────────────────────────────────────

private theorem sInterPred_respects (xs : PList CList) :
    CList.P_respects (fun z => PList.all (fun a => CList.mem z a) xs) := by
  intro z z' heq
  induction xs with
  | nil => rfl
  | cons a t ih =>
    simp only [PList.all_cons]
    have h1 : CList.mem z a = CList.mem z' a := by
      cases h : CList.mem z a <;> cases h' : CList.mem z' a <;>
        simp_all [mem_resp_left z z' a heq]
    congr 1

private theorem mem_of_plist_mem_aux
    (y : CList) (xs : PList CList) (h : PList.Mem y xs) :
    CList.mem y (CList.mk xs) = true := by
  induction xs with
  | nil => exact absurd h (PList.not_mem_nil _)
  | cons z zs ih =>
    rw [CList.mem_cons, Bool.or_eq_true]
    cases h with
    | head => exact Or.inl (CList.extEq_refl y)
    | tail h' => exact Or.inr (ih h')

def sInterCList (F : CList) : CList :=
  match F with
  | CList.mk .nil => CList.empty
  | CList.mk (.cons (CList.mk ys) xs) =>
    CList.mk (ys.filter (fun z => PList.all (fun a => CList.mem z a) xs))

@[simp] private theorem sInterCList_nil :
    sInterCList (CList.mk .nil) = CList.empty := rfl

@[simp] private theorem sInterCList_cons (ys xs : PList CList) :
    sInterCList (CList.mk (.cons (CList.mk ys) xs)) =
    CList.mk (ys.filter (fun z => PList.all (fun a => CList.mem z a) xs)) := rfl

private theorem all_mem_of_mem
    (z Y : CList) (xs : PList CList)
    (hall : PList.all (fun a => CList.mem z a) xs = true)
    (hY : CList.mem Y (CList.mk xs) = true) :
    CList.mem z Y = true := by
  induction xs with
  | nil => simp [CList.mem_nil] at hY
  | cons a t ih =>
    simp only [PList.all_cons, Bool.and_eq_true] at hall
    simp only [CList.mem_cons, Bool.or_eq_true] at hY
    cases hY with
    | inl heq =>
      have haY : CList.extEq a Y = true := by rw [CList.extEq_comm]; exact heq
      exact mem_resp_right z a Y haY hall.1
    | inr hmem => exact ih hall.2 hmem

theorem mem_sInterCList_iff (z F : CList) :
    CList.mem z (sInterCList F) = true ↔
    (∃ x, CList.mem x F = true) ∧ ∀ Y, CList.mem Y F = true → CList.mem z Y = true := by
  cases F with | mk xs =>
  cases xs with
  | nil =>
    constructor
    · intro h
      simp only [sInterCList_nil, CList.empty, CList.mem_nil] at h
      exact absurd h (by decide)
    · rintro ⟨⟨x, hx⟩, _⟩; simp [CList.mem_nil] at hx
  | cons x xs =>
    cases x with | mk ys =>
    simp only [sInterCList_cons]
    constructor
    · intro h
      have hPz : PList.all (fun a => CList.mem z a) xs = true :=
        CList.P_of_mem_filter _ (sInterPred_respects xs) z ys h
      have hzy : CList.mem z (CList.mk ys) = true :=
        CList.mem_subset z _ _ h (CList.subset_filter _ ys)
      refine ⟨⟨CList.mk ys, by simp [CList.mem_cons, CList.extEq_refl]⟩, fun Y hY => ?_⟩
      simp only [CList.mem_cons, Bool.or_eq_true] at hY
      cases hY with
      | inl heq =>
        exact mem_resp_right z (CList.mk ys) Y (by rw [CList.extEq_comm]; exact heq) hzy
      | inr hY' => exact all_mem_of_mem z Y xs hPz hY'
    · rintro ⟨_, hall⟩
      have hzy : CList.mem z (CList.mk ys) = true :=
        hall (CList.mk ys) (by simp [CList.mem_cons, CList.extEq_refl])
      have hPz : PList.all (fun a => CList.mem z a) xs = true := by
        rw [PList.all_eq_true]
        intro a ha
        apply hall a
        simp only [CList.mem_cons, Bool.or_eq_true]
        exact Or.inr (mem_of_plist_mem_aux a xs ha)
      exact CList.mem_filter_of_mem _ (sInterPred_respects xs) z ys hzy hPz

theorem sInterCList_extEq (F₁ F₂ : CList) (hF : CList.extEq F₁ F₂ = true) :
    CList.extEq (sInterCList F₁) (sInterCList F₂) = true := by
  rw [CList.extEq_def, Bool.and_eq_true]
  constructor <;> rw [subset_iff_forall_mem_clist] <;> intro z hz
  · rw [mem_sInterCList_iff] at hz ⊢
    obtain ⟨⟨x, hx⟩, hall⟩ := hz
    exact ⟨⟨x, mem_resp_right x F₁ F₂ hF hx⟩,
           fun Y hY => hall Y (mem_resp_right Y F₂ F₁ (by rw [CList.extEq_comm]; exact hF) hY)⟩
  · rw [mem_sInterCList_iff] at hz ⊢
    obtain ⟨⟨x, hx⟩, hall⟩ := hz
    exact ⟨⟨x, mem_resp_right x F₂ F₁ (by rw [CList.extEq_comm]; exact hF) hx⟩,
           fun Y hY => hall Y (mem_resp_right Y F₁ F₂ hF hY)⟩

/-- Intersección grande ⋂F para HFSet -/
def sInter (A : HFSet) : HFSet :=
  Quotient.liftOn A (fun a => Quotient.mk CList.Setoid (sInterCList a))
    (fun _ _ ha => Quotient.sound (sInterCList_extEq _ _ ha))

end HFSet
