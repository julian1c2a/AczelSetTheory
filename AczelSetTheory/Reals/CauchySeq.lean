/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Reals/CauchySeq.lean
-- Base type for computable numbers: Cauchy sequences over ℚ₀.

import AczelSetTheory.Rationals.IsCauchy
import AczelSetTheory.Rationals.Inv

namespace ℝ₀

/-- El tipo de sucesiones de Cauchy en ℚ₀, base para los números computables. -/
def CauchySeq := { f : ℕ₀ → ℚ₀ // ℚ₀.IsCauchy f }

/-- Relación de equivalencia diádica: f ∼ g si el límite de f - g es 0.
En formato constructivo: ∀ k, ∃ N, ∀ m ≥ N, |f(m) - g(m)| ≤ 1/2^k. -/
def CauchySeq.Equiv (f g : CauchySeq) : Prop :=
  ∀ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, le₀ N m → ℚ₀.absVal (f.val m - g.val m) ≤ ℚ₀.pow2 k

-- Lema auxiliar: pow2 es siempre mayor o igual que 0.
theorem pow2_nonneg (k : ℕ₀) : (0 : ℚ₀) ≤ ℚ₀.pow2 k := by
  exact ℚ₀.pow2_nonneg k

theorem CauchySeq.Equiv_refl (f : CauchySeq) : CauchySeq.Equiv f f := by
  intro k
  exists 𝟘
  intro m _
  have hzero : f.val m - f.val m = 0 := ℚ₀.add_neg_self (f.val m)
  rw [hzero, ℚ₀.absVal_zero]
  exact pow2_nonneg k

theorem CauchySeq.Equiv_symm {f g : CauchySeq} (h : CauchySeq.Equiv f g) : CauchySeq.Equiv g f := by
  intro k
  rcases h k with ⟨N, hN⟩
  exists N
  intro m hm
  have hsym : ℚ₀.absVal (g.val m - f.val m) = ℚ₀.absVal (f.val m - g.val m) := ℚ₀.absVal_sub_comm (g.val m) (f.val m)
  rw [hsym]
  exact hN m hm

theorem CauchySeq.Equiv_trans {f g h : CauchySeq} (h1 : CauchySeq.Equiv f g) (h2 : CauchySeq.Equiv g h) : CauchySeq.Equiv f h := by
  intro k
  rcases h1 (σ k) with ⟨N1, hN1⟩
  rcases h2 (σ k) with ⟨N2, hN2⟩
  exists Peano.Lattice.max N1 N2
  intro m hm
  have hN1_le : le₀ N1 m := Peano.Order.le_trans N1 (Peano.Lattice.max N1 N2) m (Peano.Lattice.le_max_left N1 N2) hm
  have hN2_le : le₀ N2 m := Peano.Order.le_trans N2 (Peano.Lattice.max N1 N2) m (Peano.Lattice.le_max_right N1 N2) hm
  have h_bound1 := hN1 m hN1_le
  have h_bound2 := hN2 m hN2_le
  
  let a : ℚ₀ := f.val m
  let b : ℚ₀ := g.val m
  let c : ℚ₀ := h.val m
  
  have h_bound1_let : (Add.add a (-b)).absVal ≤ ℚ₀.pow2 (σ k) := h_bound1
  have h_bound2_let : (Add.add b (-c)).absVal ≤ ℚ₀.pow2 (σ k) := h_bound2
  
  have h_eq : Add.add a (-c) = Add.add (Add.add a (-b)) (Add.add b (-c)) := by
    calc
      Add.add a (-c) = Add.add a (Add.add 0 (-c)) := by rw [ℚ₀.zero_add (-c)]
      _ = Add.add a (Add.add (Add.add (-b) b) (-c)) := by rw [ℚ₀.neg_add_self b]
      _ = Add.add a (Add.add (-b) (Add.add b (-c))) := by rw [ℚ₀.add_assoc (-b) b (-c)]
      _ = Add.add (Add.add a (-b)) (Add.add b (-c)) := by rw [ℚ₀.add_assoc a (-b) (Add.add b (-c))]

  have h_tri : (Add.add a (-c)).absVal ≤ Add.add (Add.add a (-b)).absVal (Add.add b (-c)).absVal := by
    rw [h_eq]
    exact ℚ₀.absVal_add_le (Add.add a (-b)) (Add.add b (-c))
    
  have h_add_le : Add.add (Add.add a (-b)).absVal (Add.add b (-c)).absVal ≤ Add.add (ℚ₀.pow2 (σ k)) (ℚ₀.pow2 (σ k)) := by
    have ha : Add.add (Add.add a (-b)).absVal (Add.add b (-c)).absVal ≤ Add.add (ℚ₀.pow2 (σ k)) (Add.add b (-c)).absVal := 
      ℚ₀.add_le_add_right h_bound1_let (Add.add b (-c)).absVal
    have hb : Add.add (ℚ₀.pow2 (σ k)) (Add.add b (-c)).absVal ≤ Add.add (ℚ₀.pow2 (σ k)) (ℚ₀.pow2 (σ k)) := 
      ℚ₀.add_le_add_left h_bound2_let (ℚ₀.pow2 (σ k))
    exact ℚ₀.le_trans ha hb

  have h_trans := ℚ₀.le_trans h_tri h_add_le
  have h_pow_add := ℚ₀.pow2_succ_add k
  
  rw [h_pow_add] at h_trans
  exact h_trans

end ℝ₀
