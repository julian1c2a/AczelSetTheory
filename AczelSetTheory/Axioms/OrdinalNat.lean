/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Axioms/OrdinalNat.lean
-- En V_ω, los ordinales de Von Neumann son exactamente los naturales:
--   isOrdinal A → isNat A   (la dirección recíproca ya está en Ordinal.lean)
--
-- Públicos:
--   card_le_of_subset   : A ⊆ B → card A ≤ card B
--   isOrdinal_isNat     : isOrdinal A → isNat A
--   isOrdinal_iff_isNat : isOrdinal A ↔ isNat A

import AczelSetTheory.Axioms.Ordinal
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Cardinal
import AczelSetTheory.Axioms.Decidable
import AczelSetTheory.Axioms.Setminus
import AczelSetTheory.Axioms.SymDiff
import AczelSetTheory.Axioms.CartProd
import AczelSetTheory.Operations.NPow
import AczelSetTheory.PList.Omega0

open Peano

namespace HFSet

-- ==================================================================
-- Lema auxiliar: insert b A = A cuando b ∈ A
-- ==================================================================

private theorem insert_mem_eq {b A : HFSet} (h : b ∈ A) : insert b A = A :=
  extensionality _ _ fun x =>
    ⟨fun hx => by
       rcases (mem_insert x b A).mp hx with rfl | hxA
       · exact h
       · exact hxA,
     fun hx => (mem_insert x b A).mpr (Or.inr hx)⟩

-- ==================================================================
-- Cardinalidad y subconjuntos
-- ==================================================================

/-- Si A ⊆ B entonces card A ≤ card B. -/
theorem card_le_of_subset {A B : HFSet} (h : A ⊆ B) : card A ≤ card B := by
  -- Inducción eps sobre A
  revert h B
  apply eps_induction (fun A => ∀ B, A ⊆ B → card A ≤ card B)
  · -- Base: A = ∅
    intro B _
    rw [card_empty]
    omega₀
  · -- Paso: A = insert b A', con IH : ∀ B, A' ⊆ B → card A' ≤ card B
    intro A' b IH B hAB
    have hbB  : b ∈ B := hAB b (mem_insert_self b A')
    have hA'B : A' ⊆ B := fun x hx => hAB x ((mem_insert x b A').mpr (Or.inr hx))
    by_cases hbA' : b ∈ A'
    · -- b ya estaba en A': insert b A' = A'
      rw [insert_mem_eq hbA']
      exact IH B hA'B
    · -- b es nuevo: card (insert b A') = σ(card A')
      rw [card_insert b A' hbA']
      -- Definir B' = B \ {b}
      let B' : HFSet := sep B (fun x => x ≠ b)
      -- b ∉ B'
      have hbB' : b ∉ B' := by
        intro h
        exact ((mem_sep B (fun x => x ≠ b) b).mp h).2 rfl
      -- B = insert b B'
      have hBB' : B = insert b B' :=
        extensionality _ _ fun x => by
          simp only [mem_insert, B', mem_sep]
          constructor
          · intro hxB
            by_cases hxb : x = b
            · exact Or.inl hxb
            · exact Or.inr ⟨hxB, hxb⟩
          · rintro (rfl | ⟨hxB, _⟩)
            · exact hbB
            · exact hxB
      -- card B = σ(card B')
      have hcardB : card B = σ (card B') := by
        rw [hBB']; exact card_insert b B' hbB'
      -- A' ⊆ B'
      have hA'B' : A' ⊆ B' := by
        intro x hxA'
        simp only [B', mem_sep]
        exact ⟨hA'B x hxA', fun hxb => hbA' (hxb ▸ hxA')⟩
      -- Concluir por IH y monotonicidad de σ
      rw [hcardB]
      have := IH B' hA'B'
      omega₀

theorem card_inter_le (A B : HFSet) : card (inter A B) ≤ card A :=
  card_le_of_subset (inter_subset_left A B)

theorem card_inter_le_right (A B : HFSet) : card (inter A B) ≤ card B :=
  card_le_of_subset (inter_subset_right A B)

theorem card_setminus_le (A B : HFSet) : card (setminus A B) ≤ card A :=
  card_le_of_subset (setminus_subset A B)

-- ==================================================================
-- Cardinalidad de unión disjunta y partición (C1-C3)
-- ==================================================================

/-- Unión disjunta: si A ∩ B = ∅ entonces card(A ∪ B) = card A + card B. -/
theorem card_union_disjoint (A B : HFSet) (h : inter A B = empty) :
    card (union A B) = add (card A) (card B) := by
  revert B
  apply eps_induction (fun A => ∀ B, inter A B = empty → card (union A B) = add (card A) (card B))
  · intro B _
    have hunion : union empty B = B :=
      extensionality _ _ fun x => by
        rw [mem_union]
        exact ⟨fun h' => h'.elim (absurd · (not_mem_empty x)) id, Or.inr⟩
    rw [hunion, card_empty]; omega₀
  · intro A' b IH B hAB
    by_cases hbA' : b ∈ A'
    · rw [insert_mem_eq hbA'] at hAB ⊢; exact IH B hAB
    · have hbB : b ∉ B := fun hb => by
        have hmem : b ∈ inter (insert b A') B :=
          (mem_inter (insert b A') B b).mpr ⟨mem_insert_self b A', hb⟩
        rw [hAB] at hmem; exact not_mem_empty b hmem
      have hA'B : inter A' B = empty :=
        extensionality _ _ fun x => by
          constructor
          · intro hx
            have ⟨hxA', hxB⟩ := (mem_inter A' B x).mp hx
            have hmem : x ∈ inter (insert b A') B :=
              (mem_inter (insert b A') B x).mpr ⟨(mem_insert x b A').mpr (Or.inr hxA'), hxB⟩
            rw [hAB] at hmem; exact absurd hmem (not_mem_empty x)
          · intro hx; exact absurd hx (not_mem_empty x)
      have hunion : union (insert b A') B = insert b (union A' B) :=
        extensionality _ _ fun x => by
          simp only [mem_union, mem_insert]
          constructor
          · rintro ((hxb | hxA') | hxB)
            · exact Or.inl hxb
            · exact Or.inr (Or.inl hxA')
            · exact Or.inr (Or.inr hxB)
          · rintro (hxb | hxA' | hxB)
            · exact Or.inl (Or.inl hxb)
            · exact Or.inl (Or.inr hxA')
            · exact Or.inr hxB
      have hbunion : b ∉ union A' B := fun hb => by
        rcases (mem_union b A' B).mp hb with h' | h'
        · exact hbA' h'
        · exact hbB h'
      rw [hunion, card_insert b (union A' B) hbunion, card_insert b A' hbA']
      have := IH B hA'B; omega₀

/-- Partición: card A = card(A ∩ B) + card(A \ B). -/
theorem card_partition (A B : HFSet) :
    card A = add (card (inter A B)) (card (setminus A B)) := by
  have hpart : A = union (inter A B) (setminus A B) :=
    extensionality _ _ fun x => by
      simp only [mem_union, mem_inter, mem_setminus]
      constructor
      · intro hxA
        by_cases hxB : x ∈ B
        · exact Or.inl ⟨hxA, hxB⟩
        · exact Or.inr ⟨hxA, hxB⟩
      · rintro (⟨hxA, _⟩ | ⟨hxA, _⟩) <;> exact hxA
  have hdisj : inter (inter A B) (setminus A B) = empty :=
    extensionality _ _ fun x => by
      constructor
      · intro hx
        rcases (mem_inter (inter A B) (setminus A B) x).mp hx with ⟨h1, h2⟩
        exact absurd ((mem_inter A B x).mp h1).2 ((mem_setminus A B x).mp h2).2
      · intro hx; exact absurd hx (not_mem_empty x)
  calc card A
      = card (union (inter A B) (setminus A B)) := congrArg card hpart
    _ = add (card (inter A B)) (card (setminus A B)) := card_union_disjoint _ _ hdisj

/-- Diferencia simétrica: card(A △ B) = card(A \ B) + card(B \ A). -/
theorem card_symDiff (A B : HFSet) :
    card (symDiff A B) = add (card (setminus A B)) (card (setminus B A)) := by
  have hsd : symDiff A B = union (setminus A B) (setminus B A) :=
    extensionality _ _ fun x => by
      simp only [mem_symDiff, mem_union, mem_setminus]
  have hdisj : inter (setminus A B) (setminus B A) = empty :=
    extensionality _ _ fun x => by
      constructor
      · intro hx
        rcases (mem_inter (setminus A B) (setminus B A) x).mp hx with ⟨h1, h2⟩
        exact absurd ((mem_setminus B A x).mp h2).1 ((mem_setminus A B x).mp h1).2
      · intro hx; exact absurd hx (not_mem_empty x)
  rw [hsd]
  exact card_union_disjoint _ _ hdisj

-- ==================================================================
-- Cardinalidad del producto cartesiano
-- ==================================================================

/-- La fila `{a} ×ₕ B` tiene la misma cardinalidad que B.
    Prueba por inducción sobre B usando eps_induction. -/
private theorem card_singleton_cartProd (a : HFSet) : ∀ B : HFSet,
    card ((insert a empty) ×ₕ B) = card B := by
  apply eps_induction (fun B => card ((insert a empty) ×ₕ B) = card B)
  · rw [cartProd_empty_right, card_empty]
  · intro B' b IH
    by_cases hbB' : b ∈ B'
    · rw [insert_mem_eq hbB']; exact IH
    · have hnotin : ⟪a, b⟫ ∉ (insert a empty) ×ₕ B' := by
        intro h
        rw [mem_cartProd] at h
        obtain ⟨_, y, _, hy, hpair⟩ := h
        have heq : b = y := ((orderedPair_eq_iff _ _ _ _).mp hpair).2
        exact hbB' (heq ▸ hy)
      have heq_set : (insert a empty) ×ₕ (insert b B') =
          insert ⟪a, b⟫ ((insert a empty) ×ₕ B') := by
        apply extensionality; intro z
        constructor
        · intro hz
          rw [mem_cartProd_insert] at hz
          rcases hz with ⟨y, hy, hz_eq⟩ | hmem
          · rw [mem_insert] at hy
            rcases hy with rfl | hyB'
            · exact (mem_insert z _ _).mpr (Or.inl hz_eq)
            · exact (mem_insert z _ _).mpr (Or.inr
                ((mem_cartProd _ _ _).mpr ⟨a, y, (mem_insert a a empty).mpr (Or.inl rfl), hyB', hz_eq⟩))
          · rw [mem_cartProd] at hmem
            obtain ⟨x, y, hxs, hy, hz_eq⟩ := hmem
            exact absurd hxs (not_mem_empty x)
        · intro hz
          rw [mem_insert] at hz
          rcases hz with hz_eq | hmem
          · rw [mem_cartProd_insert]
            exact Or.inl ⟨b, (mem_insert b b B').mpr (Or.inl rfl), hz_eq⟩
          · rw [mem_cartProd_insert]
            rw [mem_cartProd] at hmem
            obtain ⟨x, y, hxs, hy, hz_eq⟩ := hmem
            rw [mem_insert] at hxs
            rcases hxs with rfl | hxe
            · exact Or.inl ⟨y, (mem_insert y b B').mpr (Or.inr hy), hz_eq⟩
            · exact absurd hxe (not_mem_empty x)
      rw [heq_set, card_insert _ _ hnotin, IH, card_insert b B' hbB']

/-- Cardinalidad del producto cartesiano: card(A ×ₕ B) = mul (card A) (card B). -/
theorem card_cartProd (A B : HFSet) :
    card (A ×ₕ B) = mul (card A) (card B) := by
  revert A
  apply eps_induction (fun A => card (A ×ₕ B) = mul (card A) (card B))
  · simp only [cartProd_empty_left, card_empty, zero_mul]
  · intro A' a IH
    by_cases haA' : a ∈ A'
    · rw [insert_mem_eq haA']; exact IH
    · have heq_set : (insert a A') ×ₕ B = union (A' ×ₕ B) ((insert a empty) ×ₕ B) := by
        apply extensionality; intro z
        rw [mem_union]
        constructor
        · intro hz
          rw [mem_cartProd_insert] at hz
          rcases hz with ⟨y, hy, hz_eq⟩ | hmem
          · exact Or.inr ((mem_cartProd _ _ _).mpr
              ⟨a, y, (mem_insert a a empty).mpr (Or.inl rfl), hy, hz_eq⟩)
          · exact Or.inl hmem
        · rintro (hmem | hmem)
          · rw [mem_cartProd_insert]
            exact Or.inr hmem
          · rw [mem_cartProd_insert]
            rw [mem_cartProd] at hmem
            obtain ⟨x, y, hxs, hy, hz_eq⟩ := hmem
            rw [mem_insert] at hxs
            rcases hxs with rfl | hxe
            · exact Or.inl ⟨y, hy, hz_eq⟩
            · exact absurd hxe (not_mem_empty x)
      have hdisj : inter (A' ×ₕ B) ((insert a empty) ×ₕ B) = empty := by
        apply extensionality; intro z
        constructor
        · intro hz
          rw [mem_inter] at hz
          obtain ⟨h1, h2⟩ := hz
          rw [mem_cartProd] at h1 h2
          obtain ⟨x, y, hxA', _, hz_eq⟩ := h1
          obtain ⟨x', _, hxs, _, hz_eq'⟩ := h2
          have hxx' : x = x' :=
            ((orderedPair_eq_iff _ _ _ _).mp (hz_eq.symm.trans hz_eq')).1
          rw [mem_insert] at hxs
          rcases hxs with rfl | hxe
          · exact absurd (hxx' ▸ hxA') haA'
          · exact absurd hxe (not_mem_empty x')
        · intro hz; exact absurd hz (not_mem_empty z)
      rw [heq_set, card_union_disjoint _ _ hdisj, IH,
          card_singleton_cartProd a B, card_insert a A' haA', succ_mul]

/-- Si A ⊆ B y b ∈ B \ A, entonces card A < card B. -/
private theorem card_lt_of_ssubset {A B : HFSet} (hAB : A ⊆ B)
    (b : HFSet) (hbB : b ∈ B) (hbA : b ∉ A) : card A < card B := by
  have h_ins : insert b A ⊆ B := fun x hx => by
    rcases (mem_insert x b A).mp hx with rfl | hxA
    · exact hbB
    · exact hAB x hxA
  have h_card : card (insert b A) = σ (card A) := card_insert b A hbA
  have h_le   : card (insert b A) ≤ card B := card_le_of_subset h_ins
  rw [h_card] at h_le
  omega₀

-- ==================================================================
-- Existencia de elemento máximo en un conjunto finito con tricotomía
-- ==================================================================

/-- Lema central: si A tiene tricotomía, todos sus elementos son ordinales
    (lo que garantiza transitividad) y A ≠ ∅, entonces A tiene un ∈-máximo.
    La prueba procede por inducción sobre n con Ψ(card A) ≤ n. -/
private theorem has_max_le (n : Nat) : ∀ A : HFSet,
    (∀ x y, x ∈ A → y ∈ A → x ∈ y ∨ x = y ∨ y ∈ x) →
    (∀ x,   x ∈ A → isOrdinal x) →
    A ≠ empty →
    Ψ (card A) ≤ n →
    ∃ m, m ∈ A ∧ ∀ x ∈ A, x ∈ m ∨ x = m := by
  induction n with
  | zero =>
    -- Ψ(card A) ≤ 0  →  card A = 𝟘  →  A = ∅
    intro A _ _ hne hle
    have hcard0 : card A = (𝟘 : ℕ₀) := by omega₀
    exact False.elim (hne (card_eq_zero_iff.mp hcard0))
  | succ k ih =>
    intro A htri hord hne hle
    -- Extraer cualquier elemento a ∈ A mediante Foundation
    obtain ⟨a, haA, _⟩ := foundation A hne
    -- A' = {x ∈ A | a ∈ x}
    let A' : HFSet := sep A (fun x => a ∈ x)
    by_cases hA'ne : A' = empty
    · -- ============================================================
      -- Caso A' = ∅: para todo x ∈ A, a ∉ x, luego x ∈ a ∨ x = a
      -- ============================================================
      refine ⟨a, haA, fun x hxA => ?_⟩
      rcases htri x a hxA haA with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · -- a ∈ x → x ∈ A' → contradicción con A' = ∅
        have : x ∈ A' := (mem_sep A (fun z => a ∈ z) x).mpr ⟨hxA, h⟩
        rw [hA'ne] at this; exact absurd this (not_mem_empty x)
    · -- ============================================================
      -- Caso A' ≠ ∅: encontrar el máximo m de A' y ver que es el de A
      -- ============================================================
      -- A' ⊆ A
      have hA'A : A' ⊆ A := fun x hx =>
        ((mem_sep A (fun z => a ∈ z) x).mp hx).1
      -- a ∉ A' (pues a ∉ a por Fundación)
      have haA' : a ∉ A' := by
        intro h
        exact absurd ((mem_sep A (fun z => a ∈ z) a).mp h).2 (not_mem_self a)
      -- card A' < card A
      have hlt : card A' < card A := card_lt_of_ssubset hA'A a haA haA'
      -- Ψ(card A') ≤ k
      have hle' : Ψ (card A') ≤ k := by
        have h1 := (PList.Omega0.ψ_lt_iff (card A') (card A)).mp hlt
        omega
      -- tricotomía de A' (heredada de A)
      have htri' : ∀ x y, x ∈ A' → y ∈ A' → x ∈ y ∨ x = y ∨ y ∈ x :=
        fun x y hx hy => htri x y (hA'A x hx) (hA'A y hy)
      -- elementos de A' son ordinales (heredado de A)
      have hord' : ∀ z, z ∈ A' → isOrdinal z :=
        fun z hz => hord z (hA'A z hz)
      -- Aplicar HI: A' tiene un máximo m
      obtain ⟨m, hmA', hm_max⟩ := ih A' htri' hord' hA'ne hle'
      -- m ∈ A
      have hmA : m ∈ A := hA'A m hmA'
      -- a ∈ m  (pues m ∈ A' significa a ∈ m)
      have haM : a ∈ m := ((mem_sep A (fun z => a ∈ z) m).mp hmA').2
      -- isOrdinal m  →  isTransSet m
      have hTm : isTransSet m := (hord m hmA).1
      -- m es el máximo de A
      refine ⟨m, hmA, fun x hxA => ?_⟩
      -- Clasificar x según si a ∈ x
      by_cases hax : a ∈ x
      · -- x ∈ A'  →  x ∈ m ∨ x = m  (por max de A')
        exact hm_max x ((mem_sep A (fun z => a ∈ z) x).mpr ⟨hxA, hax⟩)
      · -- ¬(a ∈ x): por tricotomía de A, x ∈ a ∨ x = a
        rcases htri x a hxA haA with h | h | h
        · -- x ∈ a  →  x ∈ m  (por transitividad de m: a ∈ m y x ∈ a)
          exact Or.inl (hTm a haM x h)
        · -- x = a  →  x = a ∈ m  →  x ∈ m
          exact Or.inl (h ▸ haM)
        · -- h : a ∈ x  —  contradicción con hax
          exact absurd h hax

/-- En todo ordinal no vacío existe un ∈-máximo. -/
private theorem ordinal_has_max (A : HFSet) (hA : isOrdinal A) (hne : A ≠ empty) :
    ∃ m, m ∈ A ∧ ∀ x ∈ A, x ∈ m ∨ x = m :=
  has_max_le (Ψ (card A)) A hA.2 (fun _ hx => isOrdinal_mem hA hx) hne (Nat.le_refl _)

-- ==================================================================
-- El ordinal es el sucesor de su máximo
-- ==================================================================

private theorem ordinal_eq_succ_max {A m : HFSet} (hA : isOrdinal A)
    (hmA : m ∈ A) (hm_max : ∀ x ∈ A, x ∈ m ∨ x = m) : A = succ m :=
  extensionality _ _ fun x => by
    rw [mem_succ]
    constructor
    · -- x ∈ A  →  x ∈ m ∨ x = m  (max)  →  x ∈ m ∨ x = m  ✓
      intro hxA
      rcases hm_max x hxA with h | h
      · exact Or.inl h
      · exact Or.inr h
    · -- x ∈ m ∨ x = m  →  x ∈ A
      rintro (hxm | rfl)
      · -- x ∈ m y m ∈ A, A transitivo
        exact hA.1 m hmA x hxm
      · -- m ∈ A
        exact hmA

-- ==================================================================
-- Teorema principal: isOrdinal → isNat
-- ==================================================================

/-- En V_ω, todo ordinal de Von Neumann es un número natural. -/
theorem isOrdinal_isNat {A : HFSet} (hA : isOrdinal A) : isNat A := by
  revert hA
  apply strong_eps_induction (fun A => isOrdinal A → isNat A)
  intro A IH hA
  -- IH : ∀ x ∈ A, isOrdinal x → isNat x
  by_cases he : A = empty
  · rw [he]; exact isNat.zero
  · -- A ≠ ∅ y es un ordinal → tiene máximo m
    obtain ⟨m, hmA, hm_max⟩ := ordinal_has_max A hA he
    -- isNat m (por HI, m ∈ A y isOrdinal m)
    have hm_nat : isNat m := IH m hmA (isOrdinal_mem hA hmA)
    -- A = succ m
    have hA_eq : A = succ m := ordinal_eq_succ_max hA hmA hm_max
    rw [hA_eq]
    exact isNat.succ hm_nat

/-- En V_ω: isOrdinal A ↔ isNat A. -/
theorem isOrdinal_iff_isNat {A : HFSet} : isOrdinal A ↔ isNat A :=
  ⟨isOrdinal_isNat, isNat_isOrdinal⟩

-- ==================================================================
-- Tricotomía y orden entre ordinales (A1 + A2)
-- ==================================================================

/-- Helper: dos conjuntos isNat con la misma cardinalidad son iguales. -/
private theorem isNat_card_eq (n : Nat) : ∀ {A B : HFSet}, isNat A → isNat B →
    Ψ (card A) = n → card A = card B → A = B := by
  induction n with
  | zero =>
    intro A B _ _ hn heq
    have hAe : A = empty := card_eq_zero_iff.mp (by omega₀)
    have hBe : B = empty := card_eq_zero_iff.mp (heq ▸ card_eq_zero_iff.mpr hAe)
    rw [hAe, hBe]
  | succ k ihk =>
    intro A B hA hB hn heq
    rcases isNat_zero_or_succ hA with rfl | ⟨A', hA', rfl⟩
    · simp only [card_empty, PList.Omega0.ψ_zero] at hn; omega
    · rcases isNat_zero_or_succ hB with rfl | ⟨B', hB', rfl⟩
      · simp only [card_empty, card_succ] at heq; omega₀
      · simp only [card_succ, PList.Omega0.ψ_succ] at hn
        simp only [card_succ] at heq
        exact congrArg succ (ihk hA' hB' (by omega) (by omega₀))

/-- Helper: para conjuntos isNat, menor cardinalidad implica pertenencia. -/
private theorem isNat_lt_card_mem (k : Nat) : ∀ {A B : HFSet}, isNat A → isNat B →
    Ψ (card B) = k → Ψ (card A) < Ψ (card B) → A ∈ B := by
  induction k with
  | zero =>
    intro _ _ _ _ hBk hlt
    omega
  | succ m ihm =>
    intro A B hA hB hBk hlt
    rcases isNat_zero_or_succ hB with rfl | ⟨B', hB', rfl⟩
    · simp only [card_empty, PList.Omega0.ψ_zero] at hBk; omega
    · simp only [card_succ, PList.Omega0.ψ_succ] at hlt hBk
      -- hBk : Ψ(card B') + 1 = m + 1, hlt : Ψ(card A) < Ψ(card B') + 1
      have hle  : Ψ (card A) ≤ m  := by omega
      have hB'k : Ψ (card B') = m := by omega
      rcases Nat.eq_or_lt_of_le hle with h' | h'
      · exact (mem_succ A B').mpr (Or.inr (isNat_card_eq m hA hB' (by omega) (by omega₀)))
      · exact (mem_succ A B').mpr (Or.inl (ihm hA hB' hB'k (by omega)))

/-- En V_ω, dos ordinales satisfacen la tricotomía de pertenencia:
    A ∈ B ∨ A = B ∨ B ∈ A. -/
theorem isOrdinal_trichotomy {A B : HFSet} (hA : isOrdinal A) (hB : isOrdinal B) :
    A ∈ B ∨ A = B ∨ B ∈ A := by
  rw [isOrdinal_iff_isNat] at hA hB
  rcases Nat.lt_trichotomy (Ψ (card A)) (Ψ (card B)) with h | h | h
  · exact Or.inl (isNat_lt_card_mem (Ψ (card B)) hA hB rfl h)
  · exact Or.inr (Or.inl (isNat_card_eq (Ψ (card A)) hA hB rfl ((PList.Omega0.ψ_eq_iff _ _).mpr h)))
  · exact Or.inr (Or.inr (isNat_lt_card_mem (Ψ (card A)) hB hA rfl h))

/-- Para ordinales en V_ω, A ∈ B ↔ A ⊆ B ∧ A ≠ B. -/
theorem isOrdinal_lt_iff_mem {A B : HFSet} (hA : isOrdinal A) (hB : isOrdinal B) :
    A ∈ B ↔ A ⊆ B ∧ A ≠ B := by
  constructor
  · intro hAmemB
    exact ⟨hB.1 A hAmemB, fun hAeqB => not_mem_self B (hAeqB ▸ hAmemB)⟩
  · intro ⟨hAsubB, hAneB⟩
    rcases isOrdinal_trichotomy hA hB with h | h | h
    · exact h
    · exact absurd h hAneB
    · exact absurd (subset_antisymm A B hAsubB (hA.1 B h)) hAneB

/-- Para ordinales en V_ω, A ⊆ B ↔ A = B ∨ A ∈ B. -/
theorem isOrdinal_le_iff {A B : HFSet} (hA : isOrdinal A) (hB : isOrdinal B) :
    A ⊆ B ↔ A = B ∨ A ∈ B := by
  constructor
  · intro hAsubB
    rcases isOrdinal_trichotomy hA hB with h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · exact absurd (subset_antisymm A B hAsubB (hA.1 B h) ▸ h) (not_mem_self A)
  · rintro (rfl | hAmemB)
    · exact subset_refl A
    · exact hB.1 A hAmemB

-- ==================================================================
-- Cardinalidad de la potencia cartesiana n-aria (E2)
-- ==================================================================

private theorem card_singleton_empty : card (singleton empty) = (𝟙 : ℕ₀) := by
  have heq : singleton empty = insert empty empty :=
    extensionality _ _ fun z => by
      rw [mem_singleton, mem_insert]
      exact ⟨fun h => Or.inl h,
             fun h => h.elim id (absurd · (not_mem_empty z))⟩
  rw [heq, card_insert empty empty (not_mem_empty empty), card_empty]
  rfl

theorem card_nPow (A : HFSet) : ∀ n : ℕ₀, card (nPow A n) = (card A) ^ n := by
  intro n
  induction n with
  | zero =>
    rw [nPow_zero, card_singleton_empty]
    exact (Peano.Pow.pow_zero (card A)).symm
  | succ k ih =>
    rw [nPow_succ, card_cartProd, ih]
    exact (Peano.Pow.pow_succ (card A) k).symm

end HFSet
