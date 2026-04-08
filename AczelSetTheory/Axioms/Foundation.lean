import AczelSetTheory.Axioms.Intersection
import AczelSetTheory.HFSets

namespace CList

/-- Si `mem x (mk xs) = true`, entonces existe `y ∈ xs` con `extEq x y = true`. -/
theorem mem_exists_list_mem
  (x : CList) (xs : List CList) (h : mem x (mk xs) = true) :
    ∃ y, y ∈ xs ∧ extEq x y = true
      := by
  induction xs with
  | nil => simp [mem_nil] at h
  | cons z zs ih =>
    rw [mem_cons, Bool.or_eq_true] at h
    rcases h with h_eq | h_mem
    · exact ⟨z, List.mem_cons_self, h_eq⟩
    · obtain ⟨y, hy_mem, hy_eq⟩ := ih h_mem
      exact ⟨y, List.mem_cons_of_mem z hy_mem, hy_eq⟩

/-- Si `y ∈ xs` (a nivel lista), entonces `mem y (mk xs) = true`. -/
theorem mem_of_list_mem
  (y : CList) (xs : List CList) (h : y ∈ xs) :
    mem y (mk xs) = true
      := by
  induction xs with
  | nil => exact absurd h List.not_mem_nil
  | cons z zs ih =>
    rw [mem_cons, Bool.or_eq_true]
    rcases List.mem_cons.mp h with rfl | h_tail
    · exact Or.inl (extEq_refl y)
    · exact Or.inr (ih h_tail)

end CList

namespace HFSet

/-- Lema auxiliar para Fundación por inducción sobre un número natural n ≥ cSize B. -/
private theorem foundation_aux
  (n : Nat) :
    ∀ (B A : CList),
      CList.cSize B ≤ n → CList.mem B A = true →
      ∃ e, CList.mem e A = true ∧ ∀ y, CList.mem y e = true → CList.mem y A = false
        := by
  induction n with
  | zero =>
    intro B A hle _
    cases B with | mk bs =>
    simp [CList.cSize] at hle
  | succ n ih =>
    intro B A hle hB
    cases B with | mk bs =>
    by_cases h_any : bs.any (fun b => CList.mem b A) = true
    · rw [List.any_eq_true] at h_any
      obtain ⟨b, hb_list, hb_A⟩ := h_any
      have hb_lt : CList.cSize b < CList.cSize (CList.mk bs) :=
        CList.cSize_lt_of_mem hb_list
      exact ih b A (by omega) hb_A
    · refine ⟨CList.mk bs, hB, fun y hy => ?_⟩
      obtain ⟨b, hb_list, hb_eq⟩ := CList.mem_exists_list_mem y bs hy
      have hb_not_A : ¬ (CList.mem b A = true) := by
        intro hb_A
        exact h_any (List.any_eq_true.mpr ⟨b, hb_list, hb_A⟩)
      cases h : CList.mem y A with
      | false => rfl
      | true =>
        exact absurd
          ((mem_resp_left b y A (by rw [CList.extEq_comm]; exact hb_eq)).mpr h)
          hb_not_A

/-- **Axioma de Fundación (Regularidad)**:
    Todo conjunto no vacío A contiene un elemento x tal que x ∩ A = ∅.
    Equivalentemente: ∃ x ∈ A, ∀ y ∈ x, y ∉ A. -/
theorem foundation
  (A : HFSet) (hne : A ≠ empty) :
    ∃ x : HFSet, x ∈ A ∧ ∀ y : HFSet, y ∈ x → ¬ y ∈ A
      := by
  rcases Quotient.exists_rep A with ⟨a, rfl⟩
  cases a with | mk as =>
  cases as with
  | nil => exact absurd rfl hne
  | cons x xs =>
    have hx_mem : CList.mem x (CList.mk (x :: xs)) = true :=
      CList.mem_of_list_mem x (x :: xs) List.mem_cons_self
    obtain ⟨e, he_mem, he_disj⟩ :=
      foundation_aux (CList.cSize x) x (CList.mk (x :: xs)) (Nat.le_refl _) hx_mem
    refine ⟨Quotient.mk CList.Setoid e, he_mem, ?_⟩
    intro y hy
    rcases Quotient.exists_rep y with ⟨yc, rfl⟩
    intro hy_A
    have hy' : CList.mem yc e = true := hy
    have hy_A' : CList.mem yc (CList.mk (x :: xs)) = true := hy_A
    exact absurd hy_A' (by rw [he_disj yc hy']; exact Bool.false_ne_true)

end HFSet
