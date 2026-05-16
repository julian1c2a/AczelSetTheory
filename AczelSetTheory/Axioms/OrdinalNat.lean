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
import AczelSetTheory.PList.Omega0

open Peano

namespace HFSet

-- ==================================================================
-- Instancia DecidableEq HFSet
-- ==================================================================

/-- La igualdad en HFSet es decidible (heredada de CList.extEq : Bool). -/
instance : DecidableEq HFSet :=
  fun x y => Quotient.recOnSubsingleton₂ x y fun xc yc =>
    if h : CList.extEq xc yc = true then
      isTrue (Quotient.sound h)
    else
      isFalse (fun heq => h (Quotient.exact heq))

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
    have hcard0 : card A = 𝟘 := by omega₀
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
      -- isOrdinal m  →  isTransitive m
      have hTm : isTransitive m := (hord m hmA).1
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
  has_max_le (Ψ (card A)) A hA.2 (fun x hx => isOrdinal_mem hA hx) hne (Nat.le_refl _)

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

end HFSet
