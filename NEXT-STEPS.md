# NEXT-STEPS — Sylow.lean §33–§40: Estado y plan de acción

**Fecha**: 2026-05-29  
**Archivo principal**: `AczelSetTheory/Algebra/Sylow.lean`  
**Objetivo inmediato**: Eliminar todos los errores de compilación y el `sorry` de `sylow_first`.  
**Invariante**: 0 sorries en todo el proyecto.

---

## Estado actual

El archivo compila con errores en 5 lugares:

| Sección | Líneas | Problema |
|---------|--------|---------|
| §35 | 2457, 2460 | `rw [pow_zero]` y `rw [pow_succ]` fallan |
| §37 | 2768–2769 | `k.pred` y `pow_succ_eq` no existen en ℕ₀/peanolib |
| §38 | 2799–2833 | intro order wrong, hcomm_gpow broken, hconj_eq reversed, `rw [HFAlgebra.isNormal]` invalid |
| §39 | 2844, 2862, 2867 | `pow_succ_eq`, `hp_ne_zero`, `div_mul_cancel` wrong |
| §40 | 2873–2936 | `Prime` ambiguity, `lt_or_eq_of_le`, `succ_ne_zero`, `p'.pred`, `sorry` |

Además: línea 2704 usa `HFSet.card_pos_iff_ne_empty` que no existe.

---

## Lema clave: `^` vs HPow (raíz de §35)

En `Sylow.lean` con `open Peano Peano.Arith`, el `^` para ℕ₀ resuelve a
`HPow.hPow` (vía `instance : Pow ℕ₀ ℕ₀ where pow := Peano.Pow.pow`).

Los lemas `pow_zero` y `pow_succ` (de `Peano.Pow`) usan la notación
`scoped infix:80 " ^ " => Peano.Pow.pow`, por lo que sus patrones de
reescritura no coinciden con el `^` = `HPow.hPow` del contexto de Sylow.

**Puente**: `@[simp] theorem pow_def (a b : ℕ₀) : a ^ b = Peano.Pow.pow a b := rfl`
(en `.lake/packages/peanolib/Peano/PeanoNat/Combinatorics/Pow.lean`, línea 402).

---

## FIX §35 — `prime_dvd_of_dvd_prime_pow` (líneas 2452–2464)

**Problema**: `rw [pow_zero] at hd_pow` y `rw [pow_succ, mul_comm] at hd_pow` fallan.

**Fix**: Usar equivalencias definitionales. `p ^ 𝟘 = 𝟙` es `rfl` a través del
puente HPow, por lo que el caso `zero` puede probarse directamente.
Para `succ`, usar `show` con `rw [pow_def]`.

```lean
private theorem prime_dvd_of_dvd_prime_pow {p : ℕ₀} (hp : Peano.Arith.Prime p)
    (k : ℕ₀) {d : ℕ₀} (hd_pow : d ∣ p ^ k) (hd1 : d ≠ 𝟙) : p ∣ d := by
  induction k with
  | zero =>
    -- p ^ 𝟘 = 𝟙 por rfl (a través del puente HPow/Peano.Pow.pow)
    exact absurd (antisymm_divides hd_pow (one_divides d)) hd1
  | succ k' ih =>
    have hps : p ^ σ k' = mul (p ^ k') p := by
      rw [pow_def]; exact Peano.Pow.pow_succ p k'
    rw [hps, mul_comm] at hd_pow
    rcases prime_coprime_or_dvd hp (n := d) with hdvd | hcop
    · exact hdvd
    · exact ih (coprime_dvd_of_dvd_mul (coprime_symm hcop) hd_pow)
```

---

## FIX §36 / línea 2704 — `card_pos_iff_ne_empty` no existe

En `p_dvd_card_orbit_closed_set`, línea 2704:
```lean
have hO_pos : lt₀ 𝟘 (HFSet.card O) := by rwa [← HFSet.card_pos_iff_ne_empty]
```

**Fix**: Usar `pos_of_ne_zero` (existe en peanolib) y `card_eq_zero_iff`:
```lean
have hO_pos : lt₀ 𝟘 (HFSet.card O) :=
  pos_of_ne_zero _ (fun h => hO_ne (HFSet.card_eq_zero_iff.mp h))
```

---

## FIX §37 — `p_dvd_center_of_no_proper` (líneas 2768–2769)

**Problema**: `k.pred` no existe en ℕ₀; `pow_succ_eq` no existe.

La línea `have hp_G := divides_trans ...` no se usa más abajo (el resto del
proof no la necesita — usa directamente `hdvd` y `hp_sm`).

**Fix**: Eliminar completamente las líneas 2768–2769.

```lean
-- ELIMINAR:
--  have hp_G := divides_trans (by exact ⟨p ^ (k.pred), by rw [← pow_succ_eq]; congr 1;
--    exact (succ_pred hk).symm⟩) hdvd
-- El resto del proof funciona sin hp_G.
```

---

## FIX §38 — `cyclicSubgroup_of_central_isNormal` (líneas 2795–2833)

### Bug 1: intro order erróneo (línea 2799)

`isNormal` se define como:
```lean
def HFSubgroup.isNormal (sub : HFSubgroup grp) : Prop :=
  ∀ (g n : HFSet), g ∈ grp.G → n ∈ sub.H → grp.op (grp.op g n) (grp.inv g) ∈ sub.H
```

Intro correcto: `intro g n hg hn` (no `intro g hg n hn`).

### Bug 2: hcomm_gpow succ case roto (líneas 2815–2818)

`← grp.op_assoc (...) |>.symm` es sintaxis inválida.

**Proof correcto** (calc chain):
```lean
| succ m' ihm' =>
  rw [gpow_succ]
  have pm := gpow_mem grp hz m'
  calc grp.op h (grp.op (gpow grp hz m') z)
      = grp.op (grp.op h (gpow grp hz m')) z := by
            rw [grp.op_assoc hh pm hz_center.1]
    _ = grp.op (grp.op (gpow grp hz m') h) z := by rw [ihm']
    _ = grp.op (gpow grp hz m') (grp.op h z) := by
            rw [← grp.op_assoc pm hh hz_center.1]
    _ = grp.op (gpow grp hz m') (grp.op z h) := by rw [hz_center.2 h hh]
    _ = grp.op (grp.op (gpow grp hz m') z) h := by
            rw [grp.op_assoc pm hz_center.1 hh]
```

### Bug 3: hconj_eq dirección incorrecta (línea 2826)

`rw [← hn_comm g hg]` busca `op n g` → `op g n` pero el goal tiene `op g n`.

**Fix**: `rw [hn_comm g hg]` (sin `←`).

### Bug 4: `rw [HFAlgebra.isNormal] at *` (línea 2829)

`isNormal` es una `Prop`, no un teorema de igualdad. No se puede usar en `rw`.

**Fix**: Eliminar líneas 2829–2831. Tras `hconj_eq`:
```lean
rw [hconj_eq]
exact hn
```

### Proof completo de §38:

```lean
private theorem cyclicSubgroup_of_central_isNormal {grp : HFGroup} {z : HFSet}
    (hz : z ∈ grp.G) (hz_center : z ∈ (center grp).H) :
    (cyclicSubgroup grp hz).isNormal := by
  intro g n hg hn        -- ORDEN CORRECTO: g n hg hn
  have hn_comm : ∀ h ∈ grp.G, grp.op h n = grp.op n h := by
    rw [HFAlgebra.mem_center_iff] at hz_center
    intro h hh
    have hcomm_gpow : ∀ m : ℕ₀, grp.op h (gpow grp hz m) = grp.op (gpow grp hz m) h := by
      intro m; induction m with
      | zero =>
        rw [gpow_zero, grp.op_id_right hh, grp.op_id_left hh]
      | succ m' ihm' =>
        rw [gpow_succ]
        have pm := gpow_mem grp hz m'
        calc grp.op h (grp.op (gpow grp hz m') z)
            = grp.op (grp.op h (gpow grp hz m')) z := by rw [grp.op_assoc hh pm hz_center.1]
          _ = grp.op (grp.op (gpow grp hz m') h) z := by rw [ihm']
          _ = grp.op (gpow grp hz m') (grp.op h z) := by rw [← grp.op_assoc pm hh hz_center.1]
          _ = grp.op (gpow grp hz m') (grp.op z h) := by rw [hz_center.2 h hh]
          _ = grp.op (grp.op (gpow grp hz m') z) h := by rw [grp.op_assoc pm hz_center.1 hh]
    obtain ⟨k, hk⟩ := (cyclicMem_iff grp hz n).mp hn
    rw [← hk]; exact hcomm_gpow k
  have hconj_eq : grp.op (grp.op g n) (grp.inv g) = n := by
    have hn_G : n ∈ grp.G := (cyclicSubgroup grp hz).H_sub hn
    rw [hn_comm g hg]   -- op g n → op n g
    rw [grp.op_assoc hn_G hg (grp.inv_closed hg)]
    rw [grp.op_inv_right hg, grp.op_id_right hn_G]
  rw [hconj_eq]
  exact hn
```

---

## FIX §39 — `mul_div_dvd_iff` (línea 2844)

`pow_succ_eq` no existe. El nombre correcto es `pow_succ`.

Pero `pow_succ` usa `Peano.Pow.pow`, no `HPow.hPow`. Fix:

```lean
private theorem mul_div_dvd_iff {p q n k : ℕ₀} (hp : Prime p) (hpq : mul p q = n)
    (h : p ^ k ∣ q) : p ^ (σ k) ∣ n := by
  rw [← hpq]
  have hps : p ^ σ k = mul (p ^ k) p := by rw [pow_def]; exact Peano.Pow.pow_succ p k
  rw [hps]
  exact ⟨h.choose, by rw [mul_assoc, ← h.choose_spec]⟩
```

---

## FIX §39 — `card_quotient_cyclic` (líneas 2860–2867)

### Bug 1: `hp_ne_zero` (línea 2862)

`hp_ne_zero` no existe. Fix:

```lean
have hcycne : HFSet.card (cyclicSubgroup grp hz).H ≠ 𝟘 := by
  rw [hcyc_card]; exact hord ▸ order_ne_zero grp hz
```

### Bug 2: `div_mul_cancel` argumento erróneo (línea 2867)

`div_mul_cancel {a b : ℕ₀} (hb : b ≠ 𝟘) (h : b ∣ a) : mul (a / b) b = a`.

El divisor es `b`, no `a`. `⟨_, hlag.symm⟩` da `p ∣ card G` cuando
`hlag : card G = mul cosets p`. Fix:

```lean
show HFSet.card (cyclicSubgroup grp hz).cosets = div (HFSet.card grp.G) _
-- hlag : card G = mul cosets p  (tras rw [hcyc_card] at hlag)
have hp_dvd : p ∣ HFSet.card grp.G := ⟨_, hlag.symm⟩
exact (mul_cancelation_right _ _ p hcycne
  ((div_mul_cancel hcycne hp_dvd).trans hlag)).symm
```

---

## FIX §40 — `sylow_first` (líneas 2873–2936)

Esta sección requiere la mayor cantidad de trabajo.

### Bug 0: `open Peano.Primes` causa ambigüedad de `Prime` (línea 2873)

Con `open Peano Peano.Arith Peano.Primes`, tanto `Peano.Arith.Prime` como
`Peano.Primes.Prime` son visibles. Fix: quitar `Peano.Primes`:

```lean
open Peano Peano.Arith in
```

Y en la signatura usar `Peano.Arith.Prime`:

```lean
theorem sylow_first (grp : HFGroup) (p k : ℕ₀)
    (hp : Peano.Arith.Prime p) (hdvd : p ^ k ∣ HFSet.card grp.G) : ...
```

### Bug 1: `lt_or_eq_of_le` no existe (línea 2898)

Fix: `(le_iff_lt_or_eq _ _).mp`:

```lean
rcases (le_iff_lt_or_eq _ _).mp (HFSet.card_le_of_subset M.H_sub) with h | h
```

### Bug 2: `rwa [HFSubgroup.toHFGroup] at hM_dvd` (línea 2902)

`toHFGroup` es una `def`, no un teorema de igualdad. `M.toHFGroup.G = M.H`
definitionally, así que `hM_dvd` ya tiene el tipo correcto.

```lean
have ⟨sub_M, hsub_M⟩ := ih (HFSet.card M.H) hM_lt M.toHFGroup rfl p' (σ m) hp' hM_dvd
```

### Bug 3: `subgroupOfSubgroup M ⟨sub_M.H, ...⟩` (línea 2903)

`sub_M : HFSubgroup M.toHFGroup` ya es un `HFSubgroup`. Fix:

```lean
exact ⟨subgroupOfSubgroup M sub_M, hsub_M⟩
```

(`subgroupOfSubgroup M sub_M : HFSubgroup grp'` con `card = card sub_M.H = p'^(σm)` por def.)

### Bug 4: `succ_ne_zero m` (línea 2918)

Nombre correcto en peanolib: `succ_neq_zero m`.

```lean
p_dvd_center_of_no_proper hp' (succ_neq_zero m) hdvd' h_no_proper
```

### Bug 5: `cauchy_minimal ... (n := p'.pred)` (líneas 2920–2925)

ℕ₀ no tiene `.pred`. `cauchy_minimal` tiene `{n : ℕ₀}` implícito con
`(hp : Peano.Arith.Prime (σ n))`. Para pasar `p'` debemos primero extraer
`p' = σ p'_pred` (dado que los primos son ≥ 2):

```lean
-- Eliminar el bloque entero con p'.pred y reemplazar por:
cases p' with
| zero =>
  exact absurd (prime_ge_two hp') (by decide)  -- 0 < 2 pero 2 ≤ 0 absurdo
| succ p'_pred =>
  obtain ⟨z_sub, hz_card⟩ := cauchy_minimal (center grp').toHFGroup
      (hp := hp')          -- hp' : Prime (σ p'_pred) ✓
      (hdvd := hp_center)  -- hp_center : σ p'_pred ∣ card (center grp').H
                            -- = card (center grp').toHFGroup.G definitionally
```

(Nota: `(center grp').toHFGroup.G = (center grp').H` definitionally.)

### Bug 6: El `sorry` — estrategia completa post-Cauchy

**Variables disponibles** tras Cauchy:
- `p' = σ p'_pred`
- `z_sub : HFSubgroup (center grp').toHFGroup`
- `hz_card : HFSet.card z_sub.H = σ p'_pred = p'`

**Plan**:

```lean
-- 1. Levantar z_sub a subgrupo de grp'
let N := subgroupOfSubgroup (center grp') z_sub  -- : HFSubgroup grp'
-- N.H = z_sub.H definitionally

-- 2. Cardinalidad de N
have hN_card : HFSet.card N.H = p' := hz_card

-- 3. N es normal en G' (porque N ≤ Z(G'))
have hN_normal : N.isNormal := by
  intro g n hg hn
  -- hn : n ∈ N.H = z_sub.H
  have hn_cH : n ∈ (center grp').H := z_sub.H_sub hn
  -- (center grp').toHFGroup.G = (center grp').H definitionally
  have hn_G : n ∈ grp'.G := (center grp').H_sub hn_cH
  rw [HFAlgebra.mem_center_iff] at hn_cH
  have hconj : grp'.op (grp'.op g n) (grp'.inv g) = n := by
    rw [hn_cH.2 g hg, grp'.op_assoc hn_G hg (grp'.inv_closed hg),
        grp'.op_inv_right hg, grp'.op_id_right hn_G]
  rw [hconj]; exact hn

-- 4. Quotient Q = G'/N
-- quotientGroup : G := sub.cosets (por def)
have hQ_lag := N.card_G_eq_card_H_mul_index
-- hQ_lag : card grp'.G = mul (card N.cosets) (card N.H)
--        = mul (card N.cosets) p'
rw [hN_card] at hQ_lag

-- 5. |Q| = card G' / p'
have hpne : p' ≠ 𝟘 := succ_neq_zero p'_pred
have hQ_G_card : HFSet.card (quotientGroup grp' N hN_normal).G = div (HFSet.card grp'.G) p' := by
  -- (quotientGroup ...).G = N.cosets definitionally
  show HFSet.card N.cosets = div (HFSet.card grp'.G) p'
  have hpdvd : p' ∣ HFSet.card grp'.G := ⟨_, hQ_lag.symm⟩
  exact (mul_cancelation_right _ _ p' hpne
    ((div_mul_cancel hpne hpdvd).trans hQ_lag)).symm

-- 6. p'^m ∣ |Q|
have hQ_dvd : p' ^ m ∣ HFSet.card (quotientGroup grp' N hN_normal).G := by
  rw [hQ_G_card]
  obtain ⟨c, hc⟩ := hdvd'
  -- hdvd' : p'^(σm) ∣ card G'; hc : card G' = mul (p'^(σm)) c
  have hps : p' ^ σ m = mul (p' ^ m) p' := by rw [pow_def]; exact Peano.Pow.pow_succ p' m
  rw [hps] at hc
  -- card G' = mul (mul (p'^m) p') c = mul p' (mul (p'^m) c)  [by mul_assoc, mul_comm]
  -- div (card G') p' = mul (p'^m) c
  use mul c (p' ^ m)
  ...

-- 7. |Q| < n
have hQ_lt : lt₀ (HFSet.card (quotientGroup grp' N hN_normal).G) n := by
  rw [hQ_G_card, ← hcard']
  -- mul_lt_left : n ≠ 0 → lt₀ 1 m → lt₀ n (mul n m)
  -- card G' = mul (card cosets) p' ; p' ≥ 2 > 1 ; card cosets ≠ 0
  have hcosets_ne : HFSet.card N.cosets ≠ 𝟘 := by
    intro h; rw [HFSet.card_eq_zero_iff] at h
    have := N.e_mem_cosets; rw [h] at this
    exact HFSet.not_mem_empty _ this
  have hp_gt1 : lt₀ 𝟙 p' := by
    have := prime_ge_two hp'
    exact this  -- prime_ge_two gives Le 𝟚 p', which equals lt₀ 𝟙 p'
  rw [← hQ_lag]  -- rewrite as card G' / p' < card G'
  -- card G' = mul (card cosets) p' ← from hQ_lag
  -- card cosets < mul (card cosets) p'  by mul_lt_left
  apply div_lt_of_mul_eq_and_gt_one hpne hp_gt1 hQ_lag.symm hcosets_ne
  -- (or manual: mul_lt_left says cosets < cosets * p')
  ...

-- 8. Aplicar HI a Q
let Q_grp := quotientGroup grp' N hN_normal
obtain ⟨sub_Q, hsub_Q⟩ := ih (HFSet.card Q_grp.G) hQ_lt Q_grp rfl p' m hp' hQ_dvd

-- 9. Preimagen P = π⁻¹(sub_Q) ≤ G'
let P := HFSubgroup.preimageSubgroup N hN_normal sub_Q

-- 10. |P| = p'^m * p' = p'^(σm)
have hP_card : HFSet.card P.H = p' ^ σ m := by
  rw [card_preimage_mul, hsub_Q, hN_card]
  -- card P.H = mul (card sub_Q.H) (card N.H) = mul (p'^m) p' = p'^(σm)
  have hps : p' ^ σ m = mul (p' ^ m) p' := by rw [pow_def]; exact Peano.Pow.pow_succ p' m
  exact hps.symm

exact ⟨P, hP_card⟩
```

**Notas sobre hQ_dvd y hQ_lt**: Algunos pasos intermedios pueden necesitar
lemas auxiliares que habrá que buscar/adaptar. En particular:
- Para `hQ_dvd`: de `card G' = mul (p'^m) p' * c` se sigue `div (card G') p' = mul (p'^m) c`.
- Para `hQ_lt`: de `card G' = mul cosets p'` con `p' > 1` y `cosets > 0` se sigue `cosets < card G'`.

El lema `mul_lt_left (n m : ℕ₀) (hn : n ≠ 𝟘) (hm : lt₀ 𝟙 m) : lt₀ n (mul n m)` da
`lt₀ cosets (mul cosets p')` = `lt₀ cosets (card G')`. Y `div (card G') p' = cosets`.
Así `lt₀ (div (card G') p') (card G')` = `lt₀ (card Q.G) (card G') = lt₀ (card Q.G) n`. ✓

---

## Orden de edición

1. **Línea 2704** — Fix `card_pos_iff_ne_empty`
2. **Líneas 2455–2464** — Fix §35 `prime_dvd_of_dvd_prime_pow`
3. **Líneas 2768–2769** — Fix §37 eliminar `have hp_G`
4. **Líneas 2799–2833** — Fix §38 `cyclicSubgroup_of_central_isNormal` (rewrite completo)
5. **Líneas 2843–2845** — Fix §39 `mul_div_dvd_iff`
6. **Líneas 2860–2867** — Fix §39 `card_quotient_cyclic`
7. **Líneas 2873–2936** — Fix §40 `sylow_first` (rewrite completo)

---

## Verificación

```bash
lake build AczelSetTheory.Algebra.Sylow
```

Objetivo: 0 errores, 0 warnings, 0 sorries.

---

## Post-build

1. Actualizar el bloque de exports en `Sylow.lean` para incluir `sylow_first`.
2. Commit: "feat(Sylow): §35–§40 — Primer Teorema de Sylow completo (0 sorry)"
3. Push a main.
4. **Siguiente fase**: Paridad Peano (CountingVN) — verificar CardinalUn.lean / Symm.lean.

---

## Referencias técnicas rápidas

| Símbolo | Ubicación | Firma |
|---------|-----------|-------|
| `pow_def` | peanolib/Pow.lean:402 | `a ^ b = Peano.Pow.pow a b` |
| `Peano.Pow.pow_zero` | peanolib/Pow.lean | `n ^ 𝟘 = 𝟙` |
| `Peano.Pow.pow_succ` | peanolib/Pow.lean | `n ^ σ m = mul (n ^ m) n` |
| `pos_of_ne_zero` | peanolib/StrictOrder.lean:174 | `n ≠ 𝟘 → lt₀ 𝟘 n` |
| `succ_neq_zero` | peanolib/doc/REFERENCE | `σ n ≠ 𝟘` |
| `le_iff_lt_or_eq` | peanolib/Combinatorics/Binom.lean | `le₀ k n ↔ lt₀ k n ∨ k = n` |
| `prime_ge_two` | peanolib | `Prime p → le₀ 𝟚 p` |
| `mul_lt_left` | peanolib/Mul.lean | `n ≠ 𝟘 → lt₀ 𝟙 m → lt₀ n (mul n m)` |
| `div_mul_cancel` | peanolib/Arith.lean:800 | `b ≠ 𝟘 → b ∣ a → mul (a / b) b = a` |
| `mul_cancelation_right` | peanolib | `c ≠ 𝟘 → mul a c = mul b c → a = b` |
| `card_G_eq_card_H_mul_index` | CosetCount.lean:315 | `card G = mul (card cosets) (card H)` |
| `card_preimage_mul` | Sylow.lean:2403 | `card (preimage N hn Q).H = mul (card Q.H) (card N.H)` |
| `cauchy_minimal` | Sylow.lean:2313 | `{n} → Prime (σ n) → σ n ∣ card G → ∃ sub, card sub.H = σ n` |
| `subgroupOfSubgroup` | Sylow.lean:2389 | `sub₁ : Subgrp G → sub₂ : Subgrp sub₁.G → Subgrp G; .H = sub₂.H` |
| `isNormal` | NormalSubgroup.lean:58 | `∀ (g n : HFSet), g ∈ G → n ∈ H → op (op g n) (inv g) ∈ H` |
| `HFSet.card_eq_zero_iff` | Axioms/Cardinal.lean:148 | `card A = 𝟘 ↔ A = empty` |
