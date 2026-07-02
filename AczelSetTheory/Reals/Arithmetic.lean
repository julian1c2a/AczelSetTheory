/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Reals/Arithmetic.lean
-- Operaciones aritméticas sobre sucesiones de Cauchy en ℚ₀.

import AczelSetTheory.Reals.CauchySeq
import AczelSetTheory.Reals.RealAxioms

namespace ℝ₀

-- ============================================================
-- Suma, Resta y Negación (Término a Término)
-- ============================================================

/-- Suma de sucesiones de Cauchy. -/
def CauchySeq.add (f g : CauchySeq) : CauchySeq :=
  ⟨fun n => Add.add (f.val (σ n)) (g.val (σ n)), by
    intro n m
    let a := f.val (σ n)
    let b := g.val (σ n)
    let c := f.val (σ m)
    let d := g.val (σ m)
    
    have h_bound_f : (Add.add a (-c)).absVal ≤ ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m)) := f.property (σ n) (σ m)
    have h_bound_g : (Add.add b (-d)).absVal ≤ ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m)) := g.property (σ n) (σ m)
    
    have h_eq : Add.add (Add.add a b) (Neg.neg (Add.add c d)) = Add.add (Add.add a (-c)) (Add.add b (-d)) := by
      calc
        Add.add (Add.add a b) (Neg.neg (Add.add c d)) = Add.add (Add.add a b) (Add.add (-c) (-d)) := by rw [ℚ₀.neg_add c d]
        _ = Add.add a (Add.add b (Add.add (-c) (-d))) := by rw [ℚ₀.add_assoc a b (Add.add (-c) (-d))]
        _ = Add.add a (Add.add (Add.add b (-c)) (-d)) := by rw [(ℚ₀.add_assoc b (-c) (-d)).symm]
        _ = Add.add a (Add.add (Add.add (-c) b) (-d)) := by rw [ℚ₀.add_comm b (-c)]
        _ = Add.add a (Add.add (-c) (Add.add b (-d))) := by rw [ℚ₀.add_assoc (-c) b (-d)]
        _ = Add.add (Add.add a (-c)) (Add.add b (-d)) := by rw [(ℚ₀.add_assoc a (-c) (Add.add b (-d))).symm]

    have h_tri : (Add.add (Add.add a b) (Neg.neg (Add.add c d))).absVal ≤ Add.add (Add.add a (-c)).absVal (Add.add b (-d)).absVal := by
      rw [h_eq]
      exact ℚ₀.absVal_add_le (Add.add a (-c)) (Add.add b (-d))
      
    have h_add_le : Add.add (Add.add a (-c)).absVal (Add.add b (-d)).absVal ≤ Add.add (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) := by
      have ha : Add.add (Add.add a (-c)).absVal (Add.add b (-d)).absVal ≤ Add.add (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) (Add.add b (-d)).absVal := 
        ℚ₀.add_le_add_right h_bound_f (Add.add b (-d)).absVal
      have hb : Add.add (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) (Add.add b (-d)).absVal ≤ Add.add (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m))) := 
        ℚ₀.add_le_add_left h_bound_g (ℚ₀.pow2 (Peano.Lattice.min (σ n) (σ m)))
      exact ℚ₀.le_trans ha hb

    have h_trans := ℚ₀.le_trans h_tri h_add_le
    
    have h_min_succ : Peano.Lattice.min (σ n) (σ m) = σ (Peano.Lattice.min n m) := by
      exact Peano.Lattice.min_succ_succ n m
      
    rw [h_min_succ] at h_trans
    have h_pow_add := ℚ₀.pow2_succ_add (Peano.Lattice.min n m)
    rw [h_pow_add] at h_trans
    exact h_trans⟩

instance : Add CauchySeq := ⟨CauchySeq.add⟩

/-- Negación de una sucesión de Cauchy. -/
def CauchySeq.neg (f : CauchySeq) : CauchySeq :=
  ⟨fun n => Neg.neg (f.val n), by
    intro n m
    let a := f.val n
    let b := f.val m
    have h_bound : (Add.add a (Neg.neg b)).absVal ≤ ℚ₀.pow2 (Peano.Lattice.min n m) := f.property n m
    
    have h_eq : Add.add (Neg.neg a) (Neg.neg (Neg.neg b)) = Neg.neg (Add.add a (Neg.neg b)) := by
      exact (ℚ₀.neg_add a (Neg.neg b)).symm
      
    have h_abs_eq : (Add.add (Neg.neg a) (Neg.neg (Neg.neg b))).absVal = (Add.add a (Neg.neg b)).absVal := by
      rw [h_eq]
      exact ℚ₀.absVal_neg (Add.add a (Neg.neg b))
      
    change (Add.add (Neg.neg a) (Neg.neg (Neg.neg b))).absVal ≤ ℚ₀.pow2 (Peano.Lattice.min n m)
    rw [h_abs_eq]
    exact h_bound⟩

instance : Neg CauchySeq := ⟨CauchySeq.neg⟩

/-- Resta de sucesiones de Cauchy. -/
def CauchySeq.sub (f g : CauchySeq) : CauchySeq :=
  f + (-g)

instance : Sub CauchySeq := ⟨CauchySeq.sub⟩

-- ============================================================
-- Acotación (Boundedness)
-- ============================================================

/-- Una sucesión f en ℚ₀ está acotada si existe M tal que ∀ n, |f(n)| ≤ M. -/
def CauchySeq.IsBounded (f : CauchySeq) : Prop :=
  ∃ M : ℚ₀, ∀ n : ℕ₀, ℚ₀.absVal (f.val n) ≤ M

theorem CauchySeq.isBounded_of_isCauchy (f : CauchySeq) : CauchySeq.IsBounded f := by
  let M : ℚ₀ := Add.add (ℚ₀.pow2 𝟘) (ℚ₀.absVal (f.val 𝟘))
  exists M
  intro n
  
  have h_cauchy := f.property n 𝟘
  have h_min : Peano.Lattice.min n 𝟘 = 𝟘 := Peano.Lattice.min_0_abs n
  rw [h_min] at h_cauchy
  
  let fn := f.val n
  let f0 := f.val 𝟘
  
  have h_tri : ℚ₀.absVal fn ≤ Add.add (ℚ₀.absVal (Add.add fn (Neg.neg f0))) (ℚ₀.absVal f0) := by
    have h_eq : fn = Add.add (Add.add fn (Neg.neg f0)) f0 := by
      calc
        fn = Add.add fn 0 := by rw [ℚ₀.add_zero fn]
        _ = Add.add fn (Add.add (Neg.neg f0) f0) := by rw [ℚ₀.neg_add_self f0]
        _ = Add.add (Add.add fn (Neg.neg f0)) f0 := by rw [ℚ₀.add_assoc fn (Neg.neg f0) f0]
    
    have h_abs_eq : ℚ₀.absVal fn = ℚ₀.absVal (Add.add (Add.add fn (Neg.neg f0)) f0) := by
      exact congrArg ℚ₀.absVal h_eq
      
    rw [h_abs_eq]
    exact ℚ₀.absVal_add_le (Add.add fn (Neg.neg f0)) f0
    
  have h_add_le : Add.add (ℚ₀.absVal (Add.add fn (Neg.neg f0))) (ℚ₀.absVal f0) ≤ Add.add (ℚ₀.pow2 𝟘) (ℚ₀.absVal f0) := 
    ℚ₀.add_le_add_right h_cauchy (ℚ₀.absVal f0)
    
  exact ℚ₀.le_trans h_tri h_add_le
-- ============================================================
-- Multiplicación (Término a Término)
-- ============================================================

/-- Computa la cota constructiva de la sucesión. -/
def CauchySeq.boundVal (f : CauchySeq) : ℚ₀ := Add.add (ℚ₀.pow2 𝟘) (ℚ₀.absVal (f.val 𝟘))

/-- Encuentra un K tal que M_f + M_g <= 2^K aproximado usando division entera. -/
def CauchySeq.mulBound (f g : CauchySeq) : ℕ₀ :=
  ℚ₀.boundNat (Add.add (f.boundVal) (g.boundVal))

/-- Multiplicación de sucesiones de Cauchy. -/
def CauchySeq.mul (f g : CauchySeq) : CauchySeq :=
  let K := CauchySeq.mulBound f g
  ⟨fun n => f.val (Peano.Add.add n K) * g.val (Peano.Add.add n K), by
    -- Usando que f y g están acotadas, la diferencia se ajusta con el desplazamiento K
    -- para garantizar el ritmo de convergencia diádico 1/2^n.
    exact AczelSetTheory.RealAxioms.cauchy_mul_is_cauchy f g K⟩

instance : Mul CauchySeq := ⟨CauchySeq.mul⟩

end ℝ₀
