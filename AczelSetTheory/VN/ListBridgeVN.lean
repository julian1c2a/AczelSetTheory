/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/ListBridgeVN.lean
-- Bridge: List ℕ₀ → HFSet como grafo índice-valor.
--
-- listBridge l := { ⟪vN (Λ j), vN (l[j])⟫ | j < l.length }
--
-- Nota: ℕ en este entorno = ℕ₀ (Peano); usamos `Nat` explícitamente
--       para índices de lista.  List.get? no existe en este Lean.
--
-- Público:
--   listBridge             : List ℕ₀ → HFSet
--   listBridge_nil         : listBridge [] = ∅
--   mem_listBridge_head    : ⟪vN 𝟘, vN h⟫ ∈ listBridge (h :: t)
--   mem_listBridge_succ    : ⟪vN (σ i), vN v⟫ ∈ listBridge (h :: t) ↔ ⟪vN i, vN v⟫ ∈ listBridge t
--   listBridge_isFunction  : isFunction (listBridge l)

import AczelSetTheory.VN.FSet
import AczelSetTheory.Axioms.LinearOrder
import AczelSetTheory.Axioms.OrderedPair
import AczelSetTheory.Axioms.Function

open Peano VN

namespace HFSet

-- ─────────────────────────────────────────────────────────────────
-- Definición (start : Nat, distinto de ℕ = ℕ₀)
-- ─────────────────────────────────────────────────────────────────

private def listBridgeAux : Nat → List ℕ₀ → HFSet
  | _,     []     => ∅
  | i,  v :: l    => insert ⟪vN (Λ i), vN v⟫ (listBridgeAux (i + 1) l)

/-- Encoda una lista como grafo índice-valor en HFSet. -/
def listBridge (l : List ℕ₀) : HFSet := listBridgeAux 0 l

-- ─────────────────────────────────────────────────────────────────
-- Auxiliar: σ inyectiva vía Ψ
-- ─────────────────────────────────────────────────────────────────

private theorem peano_succ_inj {i j : ℕ₀} (h : σ i = σ j) : i = j := by
  have h1 : Nat.succ (Ψ i) = Nat.succ (Ψ j) :=
    calc Nat.succ (Ψ i) = Ψ (σ i) := (isomorph_σ_Ψ i).symm
         _ = Ψ (σ j)               := congrArg Ψ h
         _ = Nat.succ (Ψ j)        := isomorph_σ_Ψ j
  have h2 : Ψ i = Ψ j := by omega
  calc i = Λ (Ψ i) := (ΛΨ i).symm
       _ = Λ (Ψ j) := congrArg Λ h2
       _ = j        := ΛΨ j

-- ─────────────────────────────────────────────────────────────────
-- Auxiliar: primera coord de pares en listBridgeAux s l es vN (Λ k), k ≥ s
-- ─────────────────────────────────────────────────────────────────

private theorem listBridgeAux_fst_lb (s : Nat) :
    ∀ (l : List ℕ₀) (x y : HFSet),
    ⟪x, y⟫ ∈ listBridgeAux s l → ∃ k : Nat, s ≤ k ∧ x = vN (Λ k) := by
  intro l
  induction l generalizing s with
  | nil =>
    intro x y h
    simp only [listBridgeAux] at h
    exact absurd h (not_mem_empty _)
  | cons v t ih =>
    intro x y h
    simp only [listBridgeAux, mem_insert] at h
    rcases h with heq | hmem
    · rw [orderedPair_eq_iff] at heq
      exact ⟨s, Nat.le_refl s, heq.1⟩
    · obtain ⟨k, hk, hx⟩ := ih (s + 1) x y hmem
      exact ⟨k, Nat.le_trans (Nat.le_succ s) hk, hx⟩

-- ─────────────────────────────────────────────────────────────────
-- Auxiliar: shift de índice
-- ─────────────────────────────────────────────────────────────────

private theorem mem_listBridgeAux_shift (s : Nat) :
    ∀ (l : List ℕ₀) (i v : ℕ₀),
    ⟪vN (σ i), vN v⟫ ∈ listBridgeAux (s + 1) l ↔
    ⟪vN i, vN v⟫ ∈ listBridgeAux s l := by
  intro l
  induction l generalizing s with
  | nil =>
    intro i v
    simp only [listBridgeAux]
    exact ⟨fun h => absurd h (not_mem_empty _), fun h => absurd h (not_mem_empty _)⟩
  | cons w t ih =>
    intro i v
    simp only [listBridgeAux, mem_insert, ih (s + 1)]
    constructor
    · rintro (heq | hmem)
      · left
        rw [orderedPair_eq_iff] at heq ⊢
        refine ⟨congrArg vN ?_, heq.2⟩
        -- heq.1 : vN (σ i) = vN (Λ (s+1)); need i = Λ s
        exact peano_succ_inj ((vN_injective heq.1).trans (isomorph_σ_Λ s))
      · right; exact hmem
    · rintro (heq | hmem)
      · left
        rw [orderedPair_eq_iff] at heq ⊢
        refine ⟨congrArg vN ?_, heq.2⟩
        -- heq.1 : vN i = vN (Λ s); need σ i = Λ (s+1)
        have hi : i = Λ s := vN_injective heq.1
        rw [hi]
        exact (isomorph_σ_Λ s).symm
      · right; exact hmem

-- ─────────────────────────────────────────────────────────────────
-- Lemas estructurales públicos
-- ─────────────────────────────────────────────────────────────────

theorem listBridge_nil : listBridge ([] : List ℕ₀) = ∅ := by
  show listBridgeAux 0 [] = ∅
  simp [listBridgeAux]

theorem mem_listBridge_head (h : ℕ₀) (t : List ℕ₀) :
    ⟪vN 𝟘, vN h⟫ ∈ listBridge (h :: t) := by
  show ⟪vN 𝟘, vN h⟫ ∈ listBridgeAux 0 (h :: t)
  simp only [listBridgeAux, mem_insert]
  left; rw [isomorph_0_Λ]

/-- El shift de índice en la cola de la lista corresponde a σ del índice. -/
theorem mem_listBridge_succ (h : ℕ₀) (t : List ℕ₀) (i v : ℕ₀) :
    ⟪vN (σ i), vN v⟫ ∈ listBridge (h :: t) ↔ ⟪vN i, vN v⟫ ∈ listBridge t := by
  show ⟪vN (σ i), vN v⟫ ∈ listBridgeAux 0 (h :: t) ↔
       ⟪vN i, vN v⟫ ∈ listBridgeAux 0 t
  simp only [listBridgeAux, mem_insert]
  constructor
  · rintro (heq | hmem)
    · exfalso
      rw [orderedPair_eq_iff] at heq
      have h0 := vN_injective heq.1
      have : Ψ (σ i) = Ψ (Λ 0) := congrArg Ψ h0
      simp [isomorph_σ_Ψ, isomorph_0_Ψ, isomorph_0_Λ] at this
    · exact (mem_listBridgeAux_shift 0 t i v).mp hmem
  · intro hmem
    right
    exact (mem_listBridgeAux_shift 0 t i v).mpr hmem

-- ─────────────────────────────────────────────────────────────────
-- isFunction
-- ─────────────────────────────────────────────────────────────────

private theorem listBridgeAux_isFunction :
    ∀ (start : Nat) (l : List ℕ₀), isFunction (listBridgeAux start l) := by
  intro start l
  induction l generalizing start with
  | nil =>
    simp only [listBridgeAux]
    exact ⟨fun x hx => absurd hx (not_mem_empty x),
           fun a b₁ b₂ h₁ _ => absurd h₁ (not_mem_empty _)⟩
  | cons v t ih =>
    simp only [listBridgeAux]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [mem_insert] at hx
      rcases hx with rfl | hx
      · exact ⟨vN (Λ start), vN v, rfl⟩
      · exact (ih (start + 1)).1 x hx
    · intro a b₁ b₂ h₁ h₂
      rw [mem_insert] at h₁ h₂
      obtain (heq₁ | hmem₁) := h₁ <;> obtain (heq₂ | hmem₂) := h₂
      · rw [orderedPair_eq_iff] at heq₁ heq₂
        exact heq₁.2.trans heq₂.2.symm
      · rw [orderedPair_eq_iff] at heq₁
        obtain ⟨k, hk, hx⟩ := listBridgeAux_fst_lb (start + 1) t a b₂ hmem₂
        have hΛ : Λ start = Λ k := vN_injective (heq₁.1.symm.trans hx)
        have : start = k := by
          have := congrArg Ψ hΛ; rw [ΨΛ, ΨΛ] at this; exact this
        omega
      · rw [orderedPair_eq_iff] at heq₂
        obtain ⟨k, hk, hx⟩ := listBridgeAux_fst_lb (start + 1) t a b₁ hmem₁
        have hΛ : Λ start = Λ k := vN_injective (heq₂.1.symm.trans hx)
        have : start = k := by
          have := congrArg Ψ hΛ; rw [ΨΛ, ΨΛ] at this; exact this
        omega
      · exact (ih (start + 1)).2 a b₁ b₂ hmem₁ hmem₂

theorem listBridge_isFunction (l : List ℕ₀) : isFunction (listBridge l) :=
  listBridgeAux_isFunction 0 l

end HFSet
