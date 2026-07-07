/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Rationals/Bisection.lean
-- Andamiaje diádico para construir sucesiones de Cauchy en ℚ₀.
--
-- Núcleo reutilizable: si los términos CONSECUTIVOS de una sucesión distan
-- a lo sumo 1/2^(n+1), entonces la sucesión es de Cauchy (diádica).
-- Esto vale por igual para:
--   * bisección (los puntos medios se acercan a mitad de intervalo cada paso), y
--   * sumas parciales de series con cola geométrica/factorial (p. ej. artanh).
--
-- API:
--   ℚ₀.isCauchy_of_dyadic_step : (∀ k, |f (σ k) - f k| ≤ 1/2^(k+1)) → IsCauchy f
--
-- Dependencies: AczelSetTheory.Rationals.Convergence
-- @axiom_system: ZF (sin elección)
-- @importance: high

import AczelSetTheory.Rationals.Convergence

namespace ℚ₀

-- ============================================================
-- Sección 0: Identidades aditivas auxiliares en ℚ₀
-- ============================================================

/-- `a + (-b) ≤ a` cuando `0 ≤ b`. -/
private theorem sub_le_self {a b : ℚ₀} (hb : 0 ≤ b) : Add.add a (Neg.neg b) ≤ a := by
  have hnb : Neg.neg b ≤ 0 := by
    have h := neg_le_neg hb
    rwa [neg_zero] at h
  have hh := add_le_add_left hnb a
  rwa [add_zero] at hh

/-- `a + (b - 2a) = b - a` (identidad del grupo aditivo). -/
private theorem add_neg_add_self (a b : ℚ₀) :
    Add.add a (Add.add b (Neg.neg (Add.add a a))) = Add.add b (Neg.neg a) := by
  rw [neg_add]
  calc Add.add a (Add.add b (Add.add (Neg.neg a) (Neg.neg a)))
      = Add.add (Add.add a b) (Add.add (Neg.neg a) (Neg.neg a)) := (add_assoc a b _).symm
    _ = Add.add (Add.add (Add.add a b) (Neg.neg a)) (Neg.neg a) :=
          (add_assoc (Add.add a b) (Neg.neg a) (Neg.neg a)).symm
    _ = Add.add (Add.add (Add.add b a) (Neg.neg a)) (Neg.neg a) := by rw [add_comm a b]
    _ = Add.add (Add.add b (Add.add a (Neg.neg a))) (Neg.neg a) := by rw [add_assoc b a (Neg.neg a)]
    _ = Add.add (Add.add b 0) (Neg.neg a) := by rw [add_neg_self a]
    _ = Add.add b (Neg.neg a) := by rw [add_zero b]

/-- Descomposición `x - z = (x - y) + (y - z)`. -/
private theorem sub_decomp (x y z : ℚ₀) :
    Add.add x (Neg.neg z)
      = Add.add (Add.add x (Neg.neg y)) (Add.add y (Neg.neg z)) := by
  calc Add.add x (Neg.neg z)
      = Add.add x (Add.add 0 (Neg.neg z)) := by rw [zero_add]
    _ = Add.add x (Add.add (Add.add (Neg.neg y) y) (Neg.neg z)) := by rw [neg_add_self y]
    _ = Add.add x (Add.add (Neg.neg y) (Add.add y (Neg.neg z))) := by rw [add_assoc]
    _ = Add.add (Add.add x (Neg.neg y)) (Add.add y (Neg.neg z)) := by rw [← add_assoc]

-- ============================================================
-- Sección 1: Telescopio diádico
-- ============================================================

/-- Si los pasos consecutivos distan ≤ 1/2^(k+1), la distancia entre `f (n+d)`
    y `f n` está acotada por `1/2^n - 1/2^(n+d)` (suma geométrica telescópica). -/
private theorem dyadic_telescope {f : ℕ₀ → ℚ₀}
    (h : ∀ k : ℕ₀, absVal (Add.add (f (σ k)) (Neg.neg (f k))) ≤ pow2 (σ k)) (n : ℕ₀) :
    ∀ d : ℕ₀, absVal (Add.add (f (Peano.Add.add n d)) (Neg.neg (f n)))
      ≤ Add.add (pow2 n) (Neg.neg (pow2 (Peano.Add.add n d))) := by
  intro d
  induction d with
  | zero =>
    rw [Peano.Add.add_zero, add_neg_self (f n), absVal_zero, add_neg_self (pow2 n)]
    exact le_refl 0
  | succ d' ih =>
    rw [Peano.Add.add_succ]
    have halg : Add.add (pow2 (σ (Peano.Add.add n d')))
                  (Add.add (pow2 n) (Neg.neg (pow2 (Peano.Add.add n d'))))
              = Add.add (pow2 n) (Neg.neg (pow2 (σ (Peano.Add.add n d')))) := by
      rw [show pow2 (Peano.Add.add n d')
            = Add.add (pow2 (σ (Peano.Add.add n d'))) (pow2 (σ (Peano.Add.add n d')))
          from (pow2_succ_add (Peano.Add.add n d')).symm]
      exact add_neg_add_self (pow2 (σ (Peano.Add.add n d'))) (pow2 n)
    rw [sub_decomp (f (σ (Peano.Add.add n d'))) (f (Peano.Add.add n d')) (f n)]
    have hcomb := le_trans
      (absVal_add_le (Add.add (f (σ (Peano.Add.add n d'))) (Neg.neg (f (Peano.Add.add n d'))))
                     (Add.add (f (Peano.Add.add n d')) (Neg.neg (f n))))
      (add_le_add (h (Peano.Add.add n d')) ih)
    rw [halg] at hcomb
    exact hcomb

-- ============================================================
-- Sección 2: Núcleo — paso diádico ⇒ Cauchy
-- ============================================================

/-- **Núcleo diádico**: si términos consecutivos distan ≤ `1/2^(k+1)`, la sucesión
    es de Cauchy. Base común para bisección y para series de cola rápida. -/
theorem isCauchy_of_dyadic_step {f : ℕ₀ → ℚ₀}
    (h : ∀ k : ℕ₀, absVal (f (σ k) - f k) ≤ pow2 (σ k)) : IsCauchy f := by
  refine (isCauchy_iff_isCauchy₂ f).mpr ?_
  intro n m hnm
  have hd : m = Peano.Add.add n (Peano.Sub.sub m n) := by
    have hk := Peano.Sub.sub_k_add_k m n hnm
    rw [Peano.Add.add_comm] at hk
    exact hk.symm
  have htel := dyadic_telescope h n (Peano.Sub.sub m n)
  rw [← hd] at htel
  exact le_trans htel (sub_le_self (pow2_nonneg m))

-- ============================================================
-- Sección 3: Bisección diádica dinámica
-- ============================================================

/-- **Bisección diádica dinámica**: en el paso `n`, un oráculo `g` decide, según
    el valor parcial actual, si añadir el bit `1/2^(n+1)`. Sea cual sea `g`, la
    sucesión resultante es de Cauchy (los pasos consecutivos distan 0 o
    `1/2^(n+1)`). El oráculo concreto (raíz q-ésima, log, …) fija a qué converge. -/
def bisectSeq (g : ℕ₀ → ℚ₀ → Bool) (a₀ : ℚ₀) : ℕ₀ → ℚ₀
  | 𝟘 => a₀
  | σ n => bif g n (bisectSeq g a₀ n) then Add.add (bisectSeq g a₀ n) (pow2 (σ n))
                                       else bisectSeq g a₀ n

theorem bisectSeq_succ (g : ℕ₀ → ℚ₀ → Bool) (a₀ : ℚ₀) (n : ℕ₀) :
    bisectSeq g a₀ (σ n)
      = bif g n (bisectSeq g a₀ n) then Add.add (bisectSeq g a₀ n) (pow2 (σ n))
                                   else bisectSeq g a₀ n := rfl

private theorem bisectSeq_step (g : ℕ₀ → ℚ₀ → Bool) (a₀ : ℚ₀) (n : ℕ₀) :
    absVal (Add.add (bisectSeq g a₀ (σ n)) (Neg.neg (bisectSeq g a₀ n))) ≤ pow2 (σ n) := by
  rw [bisectSeq_succ]
  cases hb : g n (bisectSeq g a₀ n) with
  | false =>
    simp only [cond_false]
    rw [add_neg_self (bisectSeq g a₀ n), absVal_zero]
    exact pow2_nonneg (σ n)
  | true =>
    simp only [cond_true]
    have hx : Add.add (Add.add (bisectSeq g a₀ n) (pow2 (σ n))) (Neg.neg (bisectSeq g a₀ n))
            = pow2 (σ n) := by
      calc Add.add (Add.add (bisectSeq g a₀ n) (pow2 (σ n))) (Neg.neg (bisectSeq g a₀ n))
          = Add.add (Add.add (pow2 (σ n)) (bisectSeq g a₀ n)) (Neg.neg (bisectSeq g a₀ n)) := by
                rw [add_comm (bisectSeq g a₀ n) (pow2 (σ n))]
        _ = Add.add (pow2 (σ n)) (Add.add (bisectSeq g a₀ n) (Neg.neg (bisectSeq g a₀ n))) := by
                rw [add_assoc]
        _ = Add.add (pow2 (σ n)) 0 := by rw [add_neg_self]
        _ = pow2 (σ n) := by rw [add_zero]
    rw [hx, absVal_of_nonneg (pow2_nonneg (σ n))]
    exact le_refl (pow2 (σ n))

/-- La sucesión de bisección dinámica es de Cauchy, para cualquier oráculo. -/
theorem bisectSeq_isCauchy (g : ℕ₀ → ℚ₀ → Bool) (a₀ : ℚ₀) :
    IsCauchy (bisectSeq g a₀) :=
  isCauchy_of_dyadic_step (bisectSeq_step g a₀)

end ℚ₀
