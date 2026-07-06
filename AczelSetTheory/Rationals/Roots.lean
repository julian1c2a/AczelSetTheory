/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import AczelSetTheory.Rationals.Basic
import AczelSetTheory.Rationals.Inv

namespace ℚ₀

/--
Potencia n-ésima natural de un número racional.
x^n definido por inducción sobre ℕ₀.
-/
def pow (x : ℚ₀) : ℕ₀ → ℚ₀
  | 𝟘 => ofNat₀ 𝟙
  | σ k => Mul.mul x (pow x k)

/--
Aproximación por el método de Newton-Raphson.
Para calcular la raíz n-ésima de m, se itera:
x_{k+1} = (1 / n) * ((n - 1) * x_k + m / (x_k ^ (n - 1)))
-/
def newton_raphson_step (m : ℕ₀) (n : Peano.ℕ₂) (x : ℚ₀) : ℚ₀ :=
  -- Si m = 0 o m = 1, la sucesión es constante y vale m (evitamos divisiones por cero u otras indefiniciones)
  if m = 𝟘 ∨ m = 𝟙 then
    ofNat₀ m
  else
    -- Queremos calcular: (1/n) * [ (n-1)*x + m * inv (x^(n-1)) ]
    let n_val := n.val.val
    let inv_n := inv (ofNat₀ n_val)
    -- Nota: n_minus_one = n - 1
    let n_minus_one := Peano.Sub.sub n_val 𝟙
    let part1 := Mul.mul (ofNat₀ n_minus_one) x
    let part2 := Mul.mul (ofNat₀ m) (inv (pow x n_minus_one))
    Mul.mul inv_n (Add.add part1 part2)

/--
Sucesión de aproximaciones de Newton-Raphson para la raíz n-ésima de m.
Comienza con la semilla x_0 = m.
-/
def newton_raphson_seq (m : ℕ₀) (n : Peano.ℕ₂) : ℕ₀ → ℚ₀
  | 𝟘 => ofNat₀ m
  | σ k => newton_raphson_step m n (newton_raphson_seq m n k)

end ℚ₀
