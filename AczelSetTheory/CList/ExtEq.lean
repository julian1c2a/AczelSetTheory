import AczelSetTheory.CList.Basic

-- ==========================================
-- Propiedades de ExtEq y transitividad mutua
-- ==========================================

namespace CList

-- Si mk xs ⊆ mk ys, entonces mk xs ⊆ mk (y::ys)
theorem subset_mono (xs : List CList) (y : CList) (ys : List CList)
    (h : evalOp .subset (mk xs) (mk ys) = true) :
    evalOp .subset (mk xs) (mk (y :: ys)) = true := by
  induction xs with
  | nil => simp [evalOp]
  | cons z zs ih =>
    simp only [evalOp, Bool.and_eq_true] at h ⊢
    exact ⟨by simp [h.1], ih h.2⟩

-- A ⊆ A para todo CList (recursión bien fundada por cSize)
theorem subset_refl (A : CList) : subset A A = true := by
  match A with
  | mk [] => simp [subset, evalOp]
  | mk (x :: xs) =>
    have hx  : subset x x = true             := subset_refl x
    have hxs : subset (mk xs) (mk xs) = true := subset_refl (mk xs)
    simp only [subset] at hx hxs
    simp only [subset, evalOp, Bool.and_eq_true]
    exact ⟨by simp [hx], subset_mono xs x xs hxs⟩
termination_by cSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [cSize, cSizeList]
  all_goals omega

-- extEq A A = true (no recursivo: usa subset_refl)
theorem extEq_refl (A : CList) : extEq A A = true := by
  simp only [extEq, evalOp, Bool.and_eq_true]
  exact ⟨subset_refl A, subset_refl A⟩


-- ==============================================================
-- DEMOSTRACIÓN DE TRANSITIVIDAD (El Santo Grial Estructural)
-- ==============================================================

-- Lemas de apoyo genéricos
private def bool_and_split {a b : Bool} (h : a && b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

private def bool_or_split {a b : Bool} (h : a || b = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all

private def bool_and_join {a b : Bool} (ha : a = true) (hb : b = true) : a && b = true := by
  simp [ha, hb]

private def bool_or_join_left {a b : Bool} (ha : a = true) : a || b = true := by
  simp [ha]

private def bool_or_join_right {a b : Bool} (hb : b = true) : a || b = true := by
  simp [hb]

-- Lemas de reducción (necesarios porque evalOp usa recursión bien fundada)
theorem extEq_def (A B : CList) :
    extEq A B = (subset A B && subset B A) := by
  simp only [extEq, subset, evalOp]

theorem subset_nil (B : CList) :
    subset (mk []) B = true := by
  simp only [subset, evalOp]

theorem subset_cons (x : CList) (xs : List CList) (B : CList) :
    subset (mk (x :: xs)) B = (mem x B && subset (mk xs) B) := by
  simp only [subset, mem, evalOp]

theorem mem_nil (x : CList) :
    mem x (mk []) = false := by
  simp only [mem, evalOp]

theorem mem_cons (x y : CList) (ys : List CList) :
    mem x (mk (y :: ys)) = (extEq x y || mem x (mk ys)) := by
  simp only [mem, extEq, evalOp]

-- Transitividad mutua (tactic mode para compatibilidad con Lean 4.28)
mutual
  theorem extEq_trans :
    (A B C : CList) → (extEq A B = true) → (extEq B C = true) → (extEq A C = true)
    | A, B, C, h1, h2 => by
      simp only [extEq_def, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨subset_trans A B C h1.1 h2.1, subset_trans C B A h2.2 h1.2⟩
  termination_by A B C _ _ => (cSize A + cSize B + cSize C) * 2 + 1
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega

  theorem subset_trans : (A B C : CList) → subset A B = true → subset B C = true → subset A C = true
    | mk [], _, _, _, _ => subset_nil _
    | mk (x :: xs), B, C, h1, h2 => by
      simp only [subset_cons, Bool.and_eq_true] at h1 ⊢
      exact ⟨mem_subset x B C h1.1 h2, subset_trans (mk xs) B C h1.2 h2⟩
  termination_by A B C _ _ => (cSize A + cSize B + cSize C) * 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega

  theorem mem_subset : (x B C : CList) → mem x B = true → subset B C = true → mem x C = true
    | _, mk [], _, h1, _ => by simp [mem_nil] at h1
    | x, mk (y :: ys), C, h1, h2 => by
      simp only [mem_cons, Bool.or_eq_true] at h1
      simp only [subset_cons, Bool.and_eq_true] at h2
      cases h1 with
      | inl h1_eq => exact mem_of_extEq x y C h1_eq h2.1
      | inr h1_mem => exact mem_subset x (mk ys) C h1_mem h2.2
  termination_by x B C _ _ => (cSize x + cSize B + cSize C) * 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega

  theorem mem_of_extEq : (x y C : CList) → extEq x y = true → mem y C = true → mem x C = true
    | _, _, mk [], _, h2 => by simp [mem_nil] at h2
    | x, y, mk (z :: zs), h1, h2 => by
      simp only [mem_cons, Bool.or_eq_true] at h2 ⊢
      cases h2 with
      | inl h2_eq => exact Or.inl (extEq_trans x y z h1 h2_eq)
      | inr h2_mem => exact Or.inr (mem_of_extEq x y (mk zs) h1 h2_mem)
  termination_by x y C _ _ => (cSize x + cSize y + cSize C) * 2
  decreasing_by
    all_goals simp_wf
    all_goals try simp [cSize, cSizeList]
    all_goals try omega
end

theorem extEq_comm (A B : CList) : extEq A B = extEq B A := by
  simp [extEq_def, Bool.and_comm]

end CList
