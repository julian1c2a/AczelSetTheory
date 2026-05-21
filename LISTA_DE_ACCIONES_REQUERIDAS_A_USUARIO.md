# Lista de Acciones Requeridas al Usuario — Peano Library

**Fecha:** 2026-05-21  
**Repositorio Peano:** `https://github.com/julian1c2a/Peano`  
**Rev. actual fijada:** `9493fe0eb69b8de15847fdd2a8e18b71f357905d` (branch `master`)  
**Objetivo:** Desbloquear `Omega_prime_mul` en `AczelSetTheory/Integers/PadicVal.lean` (actualmente `sorry`)  
**y en consecuencia:** `liouville_mul` y `liouville_prime_pow` en `MobiusLiouville.lean`.

---

## Contexto del bloqueo

`Omega_prime` se define recursivamente mediante `smallestDivisor`:

```lean
noncomputable def Omega_prime (n : ℕ₀) : ℕ₀ :=
  if h : le₀ 𝟚 n then σ (Omega_prime (n / smallestDivisor n))
  else 𝟘
```

La prueba de `Omega_prime_mul` necesita:

1. Saber que `smallestDivisor n` es **primo** para `n ≥ 2`.
2. Saber que `smallestDivisor n` es el **mínimo** divisor primo (minimalidad).
3. Que un primo que divide a `a * b` divide a `a` o a `b`.
4. Un lema de división: `(a * b) / c = (a / c) * b` cuando `c ∣ a` y `c ≠ 0`.

Todos estos ingredientes están **demostrados internamente** en `Peano/PeanoNat/Primes.lean`
pero como `private`. Solo se requiere exponerlos o añadir wrappers públicos.

---

## ACCIÓN 1 — Exponer minimalidad de `smallestDivisor` (Primes.lean)

**Archivo:** `Peano/PeanoNat/Primes.lean`  
**Ubicación sugerida:** justo después de `smallestDivisor_le` (línea ~474)

**Añadir el siguiente teorema público:**

```lean
/-- `smallestDivisor n` es el *menor* divisor ≥ 2 de `n`:
    ningún `e` con `2 ≤ e < smallestDivisor n` divide a `n`. -/
theorem smallestDivisor_not_dvd_of_lt {n e : ℕ₀} (hn : le₀ 𝟚 n)
    (he2 : le₀ 𝟚 e) (hlt : lt₀ e (smallestDivisor n)) : ¬(e ∣ n) := by
  unfold smallestDivisor
  have hfuel : le₀ n (add 𝟚 n) :=
    le_trans n (add n 𝟚) (add 𝟚 n)
      (Or.inl (lt_self_add_r n 𝟚 (succ_neq_zero 𝟙)))
      (le_of_eq_wp (add_comm n 𝟚))
  obtain ⟨_, _, _, h_min⟩ :=
    smallestDivisorAux_spec n hn 𝟚 n (le_refl 𝟚) hn hfuel
  intro hdvd
  have h_false := h_min e he2 hlt
  exact absurd (dvd_imp_dividesb_true (by
    intro h0; rw [h0] at he2
    exact lt_zero 𝟚 (Or.resolve_right he2 (succ_neq_zero 𝟙))) hdvd)
    (Bool.eq_false_iff.mp h_false)
```

> **Nota:** `dvd_imp_dividesb_true` es `private` en el mismo archivo; la prueba de este
> teorema puede ir directamente en el bloque `private section` justo después de
> `smallestDivisorAux_spec`, o puedes usar el truco de llamar a `smallestDivisorAux_spec`
> desde dentro del mismo archivo donde `private` es visible.

**Alternativa mínima** si no quieres reescribir la demostración:
cambia `private theorem smallestDivisorAux_spec` a `theorem smallestDivisorAux_spec`
(quitar el `private`) y añade el wrapper con la forma más ergonómica arriba.

---

## ACCIÓN 2 — Añadir `smallestDivisor_prime` (Primes.lean)

**Archivo:** `Peano/PeanoNat/Primes.lean`  
**Ubicación sugerida:** después de la Acción 1.

```lean
/-- `smallestDivisor n` es primo para todo `n ≥ 2`. -/
theorem smallestDivisor_prime {n : ℕ₀} (hn : le₀ 𝟚 n) :
    Prime (smallestDivisor n) := by
  -- sd(n) ≥ 2, sd(n) ∣ n, sd(n) ≤ n
  have hge2 := smallestDivisor_ge_two hn
  have hdvd := smallestDivisor_dvd hn
  have hle  := smallestDivisor_le hn
  -- sd(n) ≠ 0
  have hne0 : smallestDivisor n ≠ 𝟘 := by
    intro h0; rw [h0] at hge2
    exact lt_zero 𝟚 (Or.resolve_right hge2 (succ_neq_zero 𝟙))
  -- Basta probar que sd(n) es irreducible, luego irreducible_imp_prime lo convierte.
  apply irreducible_imp_prime hne0
  refine ⟨?_, fun a b hab => ?_⟩
  · -- sd(n) ≠ 1
    intro h1; rw [h1] at hge2
    exact le_then_ngt 𝟚 𝟙 hge2 (lt_succ_self 𝟙)
  · -- Si sd(n) = a * b, entonces a = 1 ó b = 1.
    -- Suponer a ≠ 1 y b ≠ 1 lleva a a ≥ 2 y a < sd(n), pero a ∣ sd(n) ∣ n.
    by_cases ha1 : a = 𝟙
    · exact Or.inl ha1
    · right
      -- Mostrar b = 1 por contradicción:
      -- Si b ≠ 1 entonces b ≥ 2 → a ≤ sd(n)/b ≤ sd(n)/2 < sd(n)
      -- y a ∣ sd(n) ∣ n con a ≥ 2 → contradice minimalidad.
      by_contra hb1
      have ha0 : a ≠ 𝟘 := by
        intro h0; rw [h0, zero_mul] at hab; exact hne0 hab
      have hb0 : b ≠ 𝟘 := by
        intro h0; rw [h0, mul_zero] at hab; exact hne0 hab
      have ha2 : le₀ 𝟚 a := by
        rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 ha0) with h | h
        · exact lt_then_le_succ_wp h
        · exact absurd h.symm ha1
      have hb2 : le₀ 𝟚 b := by
        rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 hb0) with h | h
        · exact lt_then_le_succ_wp h
        · exact absurd h.symm hb1
      -- a < sd(n): a * b = sd(n) y b ≥ 2 → a < sd(n)
      have ha_lt : lt₀ a (smallestDivisor n) := by
        rw [← hab]
        exact lt_of_lt_of_le
          (show lt₀ a (mul a 𝟚) by
            have := mul_lt_right a 𝟚 ha0 (lt_succ_self 𝟙)
            rwa [mul_comm] at this)
          (mul_le_mono_left a hb2)
      -- a ∣ sd(n) ∣ n → a ∣ n
      have ha_dvd_sd : a ∣ smallestDivisor n := ⟨b, hab.symm⟩
      have ha_dvd_n  : a ∣ n := divides_trans ha_dvd_sd hdvd
      -- Contradice smallestDivisor_not_dvd_of_lt
      exact smallestDivisor_not_dvd_of_lt hn ha2 ha_lt ha_dvd_n
```

---

## ACCIÓN 3 — Añadir `prime_dvd_mul` público (Primes.lean)

**Archivo:** `Peano/PeanoNat/Primes.lean`  
**Ubicación sugerida:** después de `prime_dvd_product_list` (§4).

Actualmente existe `irreducible_prime_dvd_mul` (`private`) y `prime_dvd_product_list` (público
pero para listas). Hace falta la versión de dos factores:

```lean
/-- Un número primo que divide a un producto divide a alguno de los factores. -/
theorem prime_dvd_mul {p a b : ℕ₀} (hp : Prime p) (hdvd : p ∣ mul a b) :
    p ∣ a ∨ p ∣ b :=
  hp.2.2 a b hdvd
```

> **Nota:** `Prime p` en la librería Peano se define como
> `p ≠ 0 ∧ Irreducible p ∧ (∀ a b, p ∣ a*b → p ∣ a ∨ p ∣ b)`,
> así que `hp.2.2` es exactamente la tercera componente — la prueba es trivial.
> Si la definición es diferente (Irreducible first, then proven prime), usa
> `irreducible_prime_dvd_mul (prime_imp_irreducible hp) hdvd`.

---

## ACCIÓN 4 — Añadir `smallestDivisor_le_of_prime_dvd` (Primes.lean)

**Archivo:** `Peano/PeanoNat/Primes.lean`  
**Ubicación sugerida:** después de la Acción 1.

```lean
/-- Si `p` es primo y `p ∣ n` con `n ≥ 2`, entonces `smallestDivisor n ≤ p`. -/
theorem smallestDivisor_le_of_prime_dvd {n p : ℕ₀} (hn : le₀ 𝟚 n)
    (hp : Prime p) (hdvd : p ∣ n) : le₀ (smallestDivisor n) p := by
  -- Si sd(n) > p, entonces p < sd(n), p ≥ 2, p ∣ n → contradice minimalidad.
  by_contra h
  push_neg at h   -- h : lt₀ p (smallestDivisor n)  [en Lean 4: ¬(le₀ sd n p)]
  exact smallestDivisor_not_dvd_of_lt hn (prime_ge_two hp) h hdvd
```

> **Nota `push_neg`:** si `push_neg` no está disponible en el entorno Peano,
> reemplazar por:
>
> ```lean
> have h_lt : lt₀ p (smallestDivisor n) := lt_of_le_neq_wp
>   (lt_nm_then_le_nm_wp (lt_of_not_le h)) ...
> ```
>
> o razona directamente por `rcases (lt_or_le p (smallestDivisor n))`.

---

## ACCIÓN 5 — Añadir `mul_div_of_dvd_left` (Arith.lean o Div.lean)

**Archivo:** `Peano/PeanoNat/Arith.lean`  
**Ubicación sugerida:** cerca de `div_mul_cancel` (línea ~800).

```lean
/-- Si `c ∣ a` y `c ≠ 0`, entonces `(a * b) / c = (a / c) * b`. -/
theorem mul_div_of_dvd_left {a c : ℕ₀} (hc : c ≠ 𝟘) (hdvd : c ∣ a) (b : ℕ₀) :
    mul a b / c = mul (a / c) b := by
  apply mul_cancelation_right _ _ c hc
  calc mul (mul (a / c) b) c
      = mul (a / c) (mul b c) := mul_assoc _ _ _
    _ = mul (a / c) (mul c b) := by rw [mul_comm b c]
    _ = mul (mul (a / c) c) b := (mul_assoc _ _ _).symm
    _ = mul a b               := by rw [div_mul_cancel hc hdvd]
```

---

## ACCIÓN 6 — Actualizar `lake-manifest.json` en AczelSetTheory

Después de realizar las acciones 1–5 en el repositorio Peano y hacer `git push`:

1. **Copiar el nuevo hash de commit** (SHA de 40 caracteres del push a `master`).

2. **Editar `lake-manifest.json`** en este proyecto:

   ```json
   {
     "url": "https://github.com/julian1c2a/Peano",
     "type": "git",
     "rev": "<NUEVO_HASH_AQUÍ>",
     ...
   }
   ```

3. **Actualizar el paquete local:**

   ```powershell
   lake update peanolib
   # O si falla: borrar .lake/packages/peanolib y hacer lake build
   ```

---

## ACCIÓN 7 — Quitar el `sorry` en PadicVal.lean y escribir la prueba

Una vez actualizada la librería, editar
`AczelSetTheory/Integers/PadicVal.lean` línea 191:

**Reemplazar:**

```lean
theorem Omega_prime_mul {m n : ℕ₀} (hm : m ≠ 𝟘) (hn : n ≠ 𝟘) :
    Omega_prime (Peano.Mul.mul m n) =
    Peano.Add.add (Omega_prime m) (Omega_prime n) := by
  sorry
```

**Por la prueba completa** (inducción bien fundada en `n`):

```lean
theorem Omega_prime_mul {m n : ℕ₀} (hm : m ≠ 𝟘) (hn : n ≠ 𝟘) :
    Omega_prime (Peano.Mul.mul m n) =
    Peano.Add.add (Omega_prime m) (Omega_prime n) := by
  -- Primero necesitamos Omega_prime_mul_prime independientemente.
  -- Ver estrategia en el comentario del archivo.
  -- Inducción en n:
  induction n using Peano.WellFounded.well_founded_lt.induction with
  | _ n ih => ?_
  -- Caso n = 1:
  by_cases hn1 : n = 𝟙
  · subst hn1; simp [Omega_prime_one, add_zero, mul_one]
  -- Caso n ≥ 2:
  · have hn2 : le₀ 𝟚 n := by
      rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 hn) with h | h
      · exact lt_then_le_succ_wp h
      · exact absurd h.symm hn1
    -- q = sd(n), primo, q ∣ n
    set q := smallestDivisor n with hq_def
    have hq_prime := smallestDivisor_prime hn2          -- ACCIÓN 2
    have hq_dvd   := smallestDivisor_dvd hn2
    have hq_ge2   := smallestDivisor_ge_two hn2
    have hq_ne0   : q ≠ 𝟘 := prime_ne_zero hq_prime
    -- n/q < n
    have hn_div_lt : lt₀ (n / q) n :=
      div_lt_self n q (le_succ_then_lt 𝟙 q hq_ge2) hn
    have hn_div_ne0 : n / q ≠ 𝟘 := by
      intro h0
      have := div_mul_cancel hq_ne0 hq_dvd
      rw [h0, zero_mul] at this; exact hn this.symm
    -- m * n = (m * (n/q)) * q
    have h_factored : Peano.Mul.mul m n =
        Peano.Mul.mul (Peano.Mul.mul m (n / q)) q := by
      have : Peano.Mul.mul (n / q) q = n := div_mul_cancel hq_ne0 hq_dvd
      rw [← this, ← mul_assoc]
    -- Ω(m*n) = 1 + Ω(m*(n/q))  [via Omega_prime_mul_prime — ver abajo]
    rw [h_factored, Omega_prime_mul_prime hq_prime
          (mul_ne_zero_of_ne_zero m (n/q) hm hn_div_ne0)]
    -- Ω(n) = 1 + Ω(n/q)
    have h_Omega_n : Omega_prime n = σ (Omega_prime (n / q)) := by
      unfold Omega_prime; rw [dif_pos hn2, hq_def]
    -- IH: Ω(m*(n/q)) = Ω(m) + Ω(n/q)
    have ih_step := ih (n / q) hn_div_lt hm hn_div_ne0
    rw [ih_step, h_Omega_n]
    -- Ahora: σ(Ω(m) + Ω(n/q)) = Ω(m) + σ(Ω(n/q))
    rw [add_succ]
```

> **Nota:** `mul_ne_zero_of_ne_zero` puede no existir en Peano con ese nombre exacto;
> búscalo como `mul_pos`/`neq_0_then_lt_0` + `mul_ne_zero` o demuéstralo inline.
> `Omega_prime_mul_prime` también debe re-probarse sin usar `Omega_prime_mul`
> (ver ACCIÓN 7b más abajo).

---

## ACCIÓN 7b — Re-probar `Omega_prime_mul_prime` independientemente (PadicVal.lean)

El teorema actual usa `Omega_prime_mul` (con sorry). La prueba directa:

```lean
theorem Omega_prime_mul_prime {m p : ℕ₀} (hp : Peano.Arith.Prime p) (hm : m ≠ 𝟘) :
    Omega_prime (Peano.Mul.mul m p) = σ (Omega_prime m) := by
  -- Inducción en m.
  induction m using Peano.WellFounded.well_founded_lt.induction with
  | _ m ihm => ?_
  -- Caso m = 1:
  by_cases hm1 : m = 𝟙
  · subst hm1; rw [one_mul, Omega_prime_prime hp, Omega_prime_one]; rfl
  -- Caso m ≥ 2:
  · have hm2 : le₀ 𝟚 m := by
      rcases lt_0n_then_le_1n_wp (neq_0_then_lt_0 hm) with h | h
      · exact lt_then_le_succ_wp h
      · exact absurd h.symm hm1
    have hmp_ge2 : le₀ 𝟚 (Peano.Mul.mul m p) := by
      exact le_trans 𝟚 m _ hm2
        (le_trans m (Peano.Mul.mul m 𝟙) _
          (le_of_eq_wp (mul_one m).symm)
          (mul_le_mono_left m (prime_ge_two hp)))
    -- r = sd(m*p)
    set r := smallestDivisor (Peano.Mul.mul m p)
    have hr_prime := smallestDivisor_prime hmp_ge2   -- ACCIÓN 2
    have hr_dvd   := smallestDivisor_dvd hmp_ge2
    -- r ∣ m*p y r primo → r ∣ m ó r ∣ p
    rcases prime_dvd_mul hr_prime hr_dvd with hr_m | hr_p  -- ACCIÓN 3
    · -- Caso r ∣ m: r = sd(m) (minimalidad en ambos sentidos)
      -- r ≤ sd(m) por ser r primo y r ∣ m (ACCIÓN 4):
      have hr_le_sdm := smallestDivisor_le_of_prime_dvd hm2 hr_prime hr_m
      -- sd(m) ≤ r: sd(m) ∣ m ∣ m*p, sd(m) primo, sd(m) es factor primo de m*p
      have hsdm_le_r : le₀ (smallestDivisor m) r :=
        smallestDivisor_le_of_prime_dvd hmp_ge2
          (smallestDivisor_prime hm2)   -- ACCIÓN 2
          (divides_trans (smallestDivisor_dvd hm2)
                         ⟨p, mul_comm m p⟩)
      -- r = sd(m)
      have hr_eq : r = smallestDivisor m := le_antisymm _ _ hr_le_sdm hsdm_le_r
      -- Ω(m*p) = 1 + Ω((m*p)/r) = 1 + Ω((m*p)/sd(m))
      unfold Omega_prime
      rw [dif_pos hmp_ge2, ← hr_eq]  -- unfold with r = sd(m*p)
      -- (m*p)/r = (m/r)*p  (ACCIÓN 5)
      rw [show Peano.Mul.mul m p / r = Peano.Mul.mul (m / r) p from
            mul_div_of_dvd_left (prime_ne_zero hr_prime) hr_m p]  -- ACCIÓN 5
      -- m/r < m (para IH)
      have hm_div_lt : lt₀ (m / r) m :=
        div_lt_self m r (le_succ_then_lt 𝟙 r (smallestDivisor_ge_two hmp_ge2 ▸ hr_eq ▸ le_refl r)) hm
      -- IH: Ω((m/r)*p) = σ(Ω(m/r))
      have hm_div_ne0 : m / r ≠ 𝟘 := by
        intro h0
        have := div_mul_cancel (prime_ne_zero hr_prime) hr_m
        rw [h0, zero_mul] at this; exact hm this.symm
      rw [ihm (m / r) hm_div_lt hm_div_ne0]
      -- Ω(m) = 1 + Ω(m/sd(m)) = 1 + Ω(m/r)
      have hOm : Omega_prime m = σ (Omega_prime (m / r)) := by
        unfold Omega_prime
        rw [dif_pos hm2, hr_eq]
      rw [hOm, add_succ]
    · -- Caso r ∣ p y r primo y p primo → r = p
      rcases prime_divisors hp hr_p with h1 | heq
      · -- r = 1: imposible, r ≥ 2
        have := smallestDivisor_ge_two hmp_ge2
        rw [h1] at this
        exact absurd this (lt_then_ngt 𝟙 (σ 𝟙) (lt_succ_self 𝟙))
      · -- r = p
        -- (m*p)/r = (m*p)/p = m
        unfold Omega_prime
        rw [dif_pos hmp_ge2, heq]
        rw [show Peano.Mul.mul m p / p = m from mul_div_cancel_right' (prime_ne_zero hp)]
        -- `mul_div_cancel_right'` ya es privado en PadicVal.lean;
        -- usar directamente mul_cancelation_right o añadir al barrel
```

---

## Resumen de cambios por archivo

| Acción | Archivo en Peano | Tipo | Nombre del teorema |
| ------ | --------------- | ---- | ------------------ |
| 1 | `Peano/PeanoNat/Primes.lean` | nuevo público | `smallestDivisor_not_dvd_of_lt` |
| 2 | `Peano/PeanoNat/Primes.lean` | nuevo público | `smallestDivisor_prime` |
| 3 | `Peano/PeanoNat/Primes.lean` | nuevo público | `prime_dvd_mul` |
| 4 | `Peano/PeanoNat/Primes.lean` | nuevo público | `smallestDivisor_le_of_prime_dvd` |
| 5 | `Peano/PeanoNat/Arith.lean` | nuevo público | `mul_div_of_dvd_left` |
| 6 | `lake-manifest.json` (AczelSetTheory) | editar | actualizar `rev` |
| 7a | `Integers/PadicVal.lean` | editar | quitar `sorry` de `Omega_prime_mul` |
| 7b | `Integers/PadicVal.lean` | editar | re-probar `Omega_prime_mul_prime` |

---

## Orden de implementación recomendado

```text
ACCIÓN 1  →  ACCIÓN 2  →  ACCIÓN 3  →  ACCIÓN 4  →  ACCIÓN 5
       (todas en Peano, pueden hacerse en un solo commit)
               ↓
          ACCIÓN 6 (actualizar rev en AczelSetTheory)
               ↓
     ACCIÓN 7b (re-probar Omega_prime_mul_prime)
               ↓
     ACCIÓN 7a (probar Omega_prime_mul)
               ↓
    lake build AczelSetTheory.Integers.PadicVal
    lake build AczelSetTheory.Integers.MobiusLiouville
```

---

## Dependencias secundarias que podrían faltar

Al implementar ACCIÓN 7a/7b puede que se necesiten además:

- **`mul_ne_zero`** — `a ≠ 0 → b ≠ 0 → a * b ≠ 0`  
  Verificar si existe en `Peano.Mul`; si no, añadir.

- **`mul_assoc`** — asociatividad de multiplicación  
  Probablemente ya existe como `Peano.Mul.mul_assoc`.

- **`div_lt_self` con hipótesis distintas** — ya existe en `Div.lean` línea 204.

- **`le_antisymm`** — ya existe en `Order` o `Peano.Order`.

Si alguna de estas falla, identificarla en el mensaje de error de `lake build` y añadirla
también al Peano antes de actualizar el manifest.
