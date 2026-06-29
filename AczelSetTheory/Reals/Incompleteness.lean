/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/Reals/Incompleteness.lean
-- Demostración de que ℚ₀ es incompleto (existe una sucesión de Cauchy sin límite en ℚ₀).

import AczelSetTheory.Reals.CauchySeq

namespace ℝ₀

-- ============================================================
-- Sucesión de Bisección para √2
-- ============================================================

/-- Un paso del algoritmo de bisección. Toma un intervalo [a, b] y
devuelve la mitad izquierda o derecha dependiendo de si el punto medio
al cuadrado es mayor o menor que 2. -/
def bisectionStep (ab : ℚ₀ × ℚ₀) : ℚ₀ × ℚ₀ :=
  let a := ab.1
  let b := ab.2
  -- m = (a + b) / 2
  -- En ℚ₀ la división por 2 se hace multiplicando por 1/2.
  -- Usamos (a+b) * pow2 1
  let m := (a + b) * (ℚ₀.pow2 (σ 𝟘))
  
  -- if m^2 < 2 then (m, b) else (a, m)
  if m * m < (ℚ₀.ofNat₀ (σ (σ 𝟘))) then
    (m, b)
  else
    (a, m)

/-- La sucesión de intervalos generada por bisección empezando en [1, 2]. -/
def sqrt2Intervals (n : ℕ₀) : ℚ₀ × ℚ₀ :=
  match n with
  | 𝟘 => (1, ℚ₀.ofNat₀ (σ (σ 𝟘)))
  | σ k => bisectionStep (sqrt2Intervals k)

/-- La sucesión de Cauchy aproximando √2 por la izquierda. -/
def sqrt2Seq : ℕ₀ → ℚ₀ := fun n => (sqrt2Intervals n).1

/-- La sucesión de bisección converge a ritmo diádico, por lo que es de Cauchy. -/
theorem sqrt2Seq_isCauchy : ℚ₀.IsCauchy sqrt2Seq := by
  -- El tamaño del intervalo en el paso n es 1/2^n.
  -- La demostración requeriría verificar que b - a = 1/2^n y 
  -- que a_n es creciente y b_n decreciente.
  sorry

/-- La sucesión que aproxima a √2 como elemento de CauchySeq. -/
def sqrt2CauchySeq : CauchySeq := ⟨sqrt2Seq, sqrt2Seq_isCauchy⟩

-- ============================================================
-- Irracionalidad y Falta de Límite
-- ============================================================

/-- Demostración (clásica) de la irracionalidad de √2 en ℚ₀.
No existe ningún q en ℚ₀ tal que q^2 = 2. -/
theorem sqrt2_irrational (q : ℚ₀) : q * q ≠ ℚ₀.ofNat₀ (σ (σ 𝟘)) := by
  -- Requiere la factorización única en ℤ₀.
  sorry

/-- La sucesión sqrt2CauchySeq no tiene límite en ℚ₀.
Esto demuestra la incompletitud métrica de ℚ₀. -/
theorem sqrt2CauchySeq_has_no_limit :
  ¬ ∃ L : ℚ₀, ∀ k : ℕ₀, ∃ N : ℕ₀, ∀ m : ℕ₀, le₀ N m → ℚ₀.absVal (sqrt2Seq m - L) ≤ ℚ₀.pow2 k := by
  -- Supongamos que existe un límite L ∈ ℚ₀.
  -- Entonces L^2 = 2 (dado que lim (a_n)^2 = 2).
  -- Por sqrt2_irrational, L^2 ≠ 2. Contradicción.
  sorry

end ℝ₀
