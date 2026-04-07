import AczelSetTheory.HFSets
import AczelSetTheory.CList.Filter

namespace HFSet

def interCList (a b : CList) : CList :=
  match a with
  | CList.mk xs => CList.mk (xs.filter (fun c => CList.mem c b))

theorem interCList_extEq_left (a₁ a₂ b : CList) (ha : CList.extEq a₁ a₂ = true) :
    CList.extEq (interCList a₁ b) (interCList a₂ b) = true := by
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

theorem interCList_extEq_right (a b₁ b₂ : CList) (hb : CList.extEq b₁ b₂ = true) :
    CList.extEq (interCList a b₁) (interCList a b₂) = true := by
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

theorem interCList_extEq_extEq (a₁ a₂ b₁ b₂ : CList) (ha : CList.extEq a₁ a₂ = true) (hb : CList.extEq b₁ b₂ = true) :
    CList.extEq (interCList a₁ b₁) (interCList a₂ b₂) = true := by
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

end HFSet
