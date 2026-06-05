/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.CList.ExtEq

-- ==========================================
-- Propiedades de lt: irrefl, antisymm, trans
-- ==========================================

namespace CList

theorem lt_irrefl (A : CList) : lt A A = false :=
  match A with
  | mk .nil => by unfold lt; simp
  | mk (.cons x xs) => by
      unfold lt
      have hx := lt_irrefl x
      rw [if_neg (by simp [hx]), if_neg (by simp [hx])]
      exact lt_irrefl (mk xs)
termination_by (sizeOf A : Nat)
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

theorem lt_antisymm
    (A B : CList) (h1 : lt A B = false) (h2 : lt B A = false) :
    A = B := by
  match A, B with
  | mk .nil, mk .nil => rfl
  | mk .nil, mk (.cons _ _) => simp [lt] at h1
  | mk (.cons _ _), mk .nil => simp [lt] at h2
  | mk (.cons x xs), mk (.cons y ys) =>
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
          exact congrArg (fun ys => mk (.cons x ys)) (mk.inj heq_tails)
termination_by (sizeOf A + sizeOf B : Nat)
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

theorem lt_asymm
    (A B : CList) (h : lt A B = true) :
    lt B A = false := by
  match A, B with
  | mk .nil, mk .nil => simp [lt] at h
  | mk .nil, mk (.cons _ _) => unfold lt; simp
  | mk (.cons _ _), mk .nil => simp [lt] at h
  | mk (.cons x xs), mk (.cons y ys) =>
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
        have heq := lt_antisymm x y (Bool.eq_false_iff.mpr hxy) (Bool.eq_false_iff.mpr hyx)
        subst heq
        rw [if_neg hxy, if_neg hxy]
        exact lt_asymm (mk xs) (mk ys) h
termination_by (sizeOf A + sizeOf B : Nat)
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

theorem lt_total
    (A B : CList) :
    A ≠ B → lt A B = true ∨ lt B A = true := by
  intro h_neq
  match A, B with
  | mk .nil, mk .nil => exact absurd rfl h_neq
  | mk .nil, mk (.cons _ _) => left; unfold lt; simp
  | mk (.cons _ _), mk .nil => right; unfold lt; simp
  | mk (.cons x xs), mk (.cons y ys) =>
    by_cases hxy : lt x y = true
    · left; unfold lt; rw [if_pos hxy]
    · by_cases hyx : lt y x = true
      · right; unfold lt; rw [if_pos hyx]
      · have heq := lt_antisymm x y (Bool.eq_false_iff.mpr hxy) (Bool.eq_false_iff.mpr hyx)
        subst heq
        have h_tails : mk xs ≠ mk ys := by
          intro h
          exact h_neq (congrArg mk (congrArg (PList.cons x) (mk.inj h)))
        rcases lt_total (mk xs) (mk ys) h_tails with h | h
        · left; unfold lt; simp only [if_neg hxy]; exact h
        · right; unfold lt; simp only [if_neg hxy]; exact h
termination_by (sizeOf A + sizeOf B : Nat)
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

theorem lt_total_extEq
    (A B : CList) :
    extEq A B = false → lt A B = true ∨ lt B A = true := by
  intro h_neq
  apply lt_total
  intro heq; subst heq; simp [extEq_refl] at h_neq

theorem lt_trans
    (A B C : CList) (h1 : lt A B = true) (h2 : lt B C = true) :
    lt A C = true := by
  match A, B, C with
  | mk .nil, mk .nil, _ => simp [lt] at h1
  | mk .nil, mk (.cons _ _), mk .nil => simp [lt] at h2
  | mk .nil, mk (.cons _ _), mk (.cons _ _) => unfold lt; simp
  | mk (.cons _ _), mk .nil, _ => simp [lt] at h1
  | mk (.cons _ _), mk (.cons _ _), mk .nil => simp [lt] at h2
  | mk (.cons a as), mk (.cons b bs), mk (.cons c cs) =>
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
          have hbc_eq := lt_antisymm b c (Bool.eq_false_iff.mpr hbc) (Bool.eq_false_iff.mpr hcb)
          subst hbc_eq
          rw [if_pos hab]
    · rw [if_neg hab] at h1
      by_cases hba : lt b a = true
      · rw [if_pos hba] at h1; simp at h1
      · rw [if_neg hba] at h1
        have hab_eq := lt_antisymm a b (Bool.eq_false_iff.mpr hab) (Bool.eq_false_iff.mpr hba)
        subst hab_eq
        by_cases hbc : lt a c = true
        · rw [if_pos hbc]
        · rw [if_neg hbc]
          by_cases hca : lt c a = true
          · rw [if_neg hbc] at h2
            rw [if_pos hca] at h2; simp at h2
          · rw [if_neg hca]
            rw [if_neg hbc] at h2; rw [if_neg hca] at h2
            exact lt_trans (mk as) (mk bs) (mk cs) h1 h2
termination_by Nat.add (Nat.add (sizeOf A) (sizeOf B)) (sizeOf C)
decreasing_by
  all_goals simp_wf
  all_goals try simp [sizeOf]
  all_goals try omega

end CList
