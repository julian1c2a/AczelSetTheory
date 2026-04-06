import AczelSetTheory.CList.ExtEq

-- ==========================================
-- Propiedades de lt: irrefl, antisymm, trans
-- ==========================================

namespace CList

theorem lt_irrefl (A : CList) : lt A A = false :=
  match A with
  | mk [] => by unfold lt; simp
  | mk (x :: xs) => by
      unfold lt
      have hx := lt_irrefl x
      rw [if_neg (by simp [hx]), if_neg (by simp [hx])]
      exact lt_irrefl (mk xs)
termination_by cSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [cSize, cSizeList]
  all_goals omega

-- lt_antisymm: the new lt is antisymmetric (¬lt A B ∧ ¬lt B A → A = B)
theorem lt_antisymm (A B : CList) (h1 : lt A B = false) (h2 : lt B A = false) : A = B := by
  match A, B with
  | mk [], mk [] => rfl
  | mk [], mk (_ :: _) => simp [lt] at h1
  | mk (_ :: _), mk [] => simp [lt] at h2
  | mk (x :: xs), mk (y :: ys) =>
    unfold lt at h1 h2
    by_cases hxy : lt x y = true
    · rw [if_pos hxy] at h1; simp at h1
    · rw [if_neg hxy] at h1
      by_cases hyx : lt y x = true
      · rw [if_pos hyx] at h2; simp at h2
      · rw [if_neg hyx] at h1
        rw [if_neg hyx] at h2
        by_cases hxy' : lt x y = true
        · exact absurd hxy' hxy
        · rw [if_neg hxy'] at h2
          have heq_heads := lt_antisymm x y (Bool.eq_false_iff.mpr hxy) (Bool.eq_false_iff.mpr hyx)
          have heq_tails := lt_antisymm (mk xs) (mk ys) h1 h2
          subst heq_heads
          exact congrArg (mk ∘ (x :: ·)) (mk.inj heq_tails)
termination_by cSize A + cSize B
decreasing_by
  all_goals simp_wf
  all_goals simp [cSize, cSizeList]
  all_goals omega

-- lt_asymm: lt A B = true → lt B A = false
theorem lt_asymm (A B : CList) (h : lt A B = true) : lt B A = false := by
  match A, B with
  | mk [], mk [] => simp [lt] at h
  | mk [], mk (_ :: _) =>
    unfold lt; simp
  | mk (_ :: _), mk [] =>
    simp [lt] at h
  | mk (x :: xs), mk (y :: ys) =>
    unfold lt at h ⊢
    by_cases hxy : lt x y = true
    · rw [if_pos hxy] at h
      have hyx := lt_asymm x y hxy
      rw [if_neg (Bool.eq_false_iff.mp hyx)]
      rw [if_pos hxy]
    · rw [if_neg hxy] at h
      by_cases hyx : lt y x = true
      · rw [if_pos hyx] at h; simp at h
      · rw [if_neg hyx] at h
        -- lt x y = false, lt y x = false, so x = y by antisymmetry
        have heq := lt_antisymm x y (Bool.eq_false_iff.mpr hxy) (Bool.eq_false_iff.mpr hyx)
        subst heq
        rw [if_neg hxy, if_neg hxy]
        exact lt_asymm (mk xs) (mk ys) h
termination_by cSize A + cSize B
decreasing_by
  all_goals simp_wf
  all_goals simp [cSize, cSizeList]
  all_goals omega

theorem lt_total (A B : CList) :
    A ≠ B → lt A B = true ∨ lt B A = true := by
  intro h_neq
  match A, B with
  | mk [], mk [] => exact absurd rfl h_neq
  | mk [], mk (_ :: _) => left; unfold lt; simp
  | mk (_ :: _), mk [] => right; unfold lt; simp
  | mk (x :: xs), mk (y :: ys) =>
    by_cases hxy : lt x y = true
    · left; unfold lt; rw [if_pos hxy]
    · by_cases hyx : lt y x = true
      · right; unfold lt; rw [if_pos hyx]
      · -- x = y by antisymmetry
        have heq := lt_antisymm x y (Bool.eq_false_iff.mpr hxy) (Bool.eq_false_iff.mpr hyx)
        subst heq
        -- Need mk xs ≠ mk ys
        have h_tails : mk xs ≠ mk ys := by
          intro h
          have : x :: xs = x :: ys := List.cons_eq_cons.mpr ⟨rfl, mk.inj h⟩
          exact h_neq (congrArg mk this)
        rcases lt_total (mk xs) (mk ys) h_tails with h | h
        · left; unfold lt; simp only [if_neg hxy]; exact h
        · right; unfold lt; simp only [if_neg hxy]; exact h
termination_by cSize A + cSize B
decreasing_by
  all_goals simp_wf
  all_goals simp [cSize, cSizeList]
  all_goals omega

-- Compatibility with old lt_total form for orderedInsert proofs
theorem lt_total_extEq (A B : CList) :
    extEq A B = false → lt A B = true ∨ lt B A = true := by
  intro h_neq
  apply lt_total
  intro heq; subst heq; simp [extEq_refl] at h_neq

-- lt_trans: the new lt is transitive
theorem lt_trans (A B C : CList) (h1 : lt A B = true) (h2 : lt B C = true) : lt A C = true := by
  match A, B, C with
  | mk [], mk [], _ => simp [lt] at h1
  | mk [], mk (_ :: _), mk [] => simp [lt] at h2
  | mk [], mk (_ :: _), mk (_ :: _) => unfold lt; simp
  | mk (_ :: _), mk [], _ => simp [lt] at h1
  | mk (_ :: _), mk (_ :: _), mk [] => simp [lt] at h2
  | mk (a :: as), mk (b :: bs), mk (c :: cs) =>
    unfold lt at h1 h2 ⊢
    by_cases hab : lt a b = true
    · rw [if_pos hab] at h1
      by_cases hbc : lt b c = true
      · rw [if_pos hbc] at h2
        rw [if_pos (lt_trans a b c hab hbc)]
      · rw [if_neg hbc] at h2
        by_cases hcb : lt c b = true
        · rw [if_pos hcb] at h2; simp at h2
        · rw [if_neg hcb] at h2
          -- b = c by antisymmetry
          have hbc_eq := lt_antisymm b c (Bool.eq_false_iff.mpr hbc) (Bool.eq_false_iff.mpr hcb)
          subst hbc_eq
          rw [if_pos hab]
    · rw [if_neg hab] at h1
      by_cases hba : lt b a = true
      · rw [if_pos hba] at h1; simp at h1
      · rw [if_neg hba] at h1
        -- a = b by antisymmetry
        have hab_eq := lt_antisymm a b (Bool.eq_false_iff.mpr hab) (Bool.eq_false_iff.mpr hba)
        subst hab_eq
        -- h1 : lt (mk as) (mk bs) = true, h2 involves b and c
        by_cases hbc : lt a c = true
        · rw [if_pos hbc]
        · rw [if_neg hbc]
          by_cases hca : lt c a = true
          · -- lt c a and lt a c is false: check h2
            -- h2: if lt a c then true else if lt c a then false else lt(mk bs)(mk cs)
            rw [if_neg hbc] at h2
            rw [if_pos hca] at h2; simp at h2
          · rw [if_neg hca]
            -- a = c by antisymmetry... no, that's wrong. a = b, and we need lt(mk as)(mk cs)
            -- h2: if lt a c then ... else if lt c a then ... else lt(mk bs)(mk cs)
            rw [if_neg hbc] at h2; rw [if_neg hca] at h2
            -- h1: lt (mk as) (mk bs), h2: lt (mk bs) (mk cs)
            exact lt_trans (mk as) (mk bs) (mk cs) h1 h2
termination_by cSize A + cSize B + cSize C
decreasing_by
  all_goals simp_wf
  all_goals simp [cSize, cSizeList]
  all_goals omega

end CList
