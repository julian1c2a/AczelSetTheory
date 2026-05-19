/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- AczelSetTheory/VN/ProductVN.lean
-- Transporte del producto finito (finProd) y producto de lista (product_list)
-- de Peano a HFSet vía vN.

import AczelSetTheory.VN.PeanoArith
import Peano.PeanoNat.Combinatorics.Product

open Peano

namespace VN

-- ─────────────────────────────────────────────────────────────────
-- Definiciones
-- ─────────────────────────────────────────────────────────────────

/-- Producto de lista: vN (product_list ds). -/
def productListVN (ds : List ℕ₀) : HFSet := vN (product_list ds)

/-- Producto finito: vN (finProd f n). -/
def finProdVN (f : ℕ₀ → ℕ₀) (n : ℕ₀) : HFSet := vN (finProd f n)

-- ─────────────────────────────────────────────────────────────────
-- product_list: ecuaciones de recursión
-- ─────────────────────────────────────────────────────────────────

theorem vN_product_nil : vN (product_list []) = vN 𝟙 :=
  congrArg vN product_nil

theorem vN_product_cons (d : ℕ₀) (ds : List ℕ₀) :
    vN (product_list (d :: ds)) = vN (mul d (product_list ds)) :=
  congrArg vN (product_cons d ds)

-- ─────────────────────────────────────────────────────────────────
-- finProd: ecuaciones de recursión
-- ─────────────────────────────────────────────────────────────────

theorem vN_finProd_zero (f : ℕ₀ → ℕ₀) : vN (finProd f 𝟘) = vN (f 𝟘) :=
  congrArg vN (finProd_zero f)

theorem vN_finProd_succ (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
    vN (finProd f (σ n)) = vN (mul (finProd f n) (f (σ n))) :=
  congrArg vN (finProd_succ f n)

theorem vN_finProd_one_fn (n : ℕ₀) :
    vN (finProd (fun _ => 𝟙) n) = vN 𝟙 :=
  congrArg vN (finProd_one_fn n)

theorem vN_finProd_zero_fn (n : ℕ₀) :
    vN (finProd (fun _ => 𝟘) n) = vN 𝟘 :=
  congrArg vN (finProd_zero_fn n)

theorem vN_finProd_succ_left (f : ℕ₀ → ℕ₀) (n : ℕ₀) :
    vN (finProd f (σ n)) = vN (mul (f 𝟘) (finProd (fun k => f (σ k)) n)) :=
  congrArg vN (finProd_succ_left f n)

end VN
