# NEXT-STEPS — Estado del proyecto AczelSetTheory

**Última actualización**: 2026-05-30
**Archivo principal recién completado**: `AczelSetTheory/Algebra/Sylow.lean`

> ⚠️ **Nota**: este archivo (`NEXT-STEPS.md`, con guion) duplica al canónico
> `NEXT_STEPS.md` (con guion bajo). Pendiente consolidar en uno solo.

---

## ⚠️ Directiva maestra (2026-05-30): Peano congelado — teoría nueva en Aczel

**Peano (`peanolib`) no desarrollará más teoría "hacia arriba"** — solo fundamentos
(aritmética de Robinson `Q` / **ROBINSON_PlusPlus**). **Toda la teoría nueva** se construye
**directamente sobre `HFSet` en AczelSetTheory**, capa nativa (p.ej. `Combinatorics/`),
*no* vía transporte `VN/`. Ver `DECISIONS.md` → ADR-000.

---

## ✅ COMPLETADO: Primer Teorema de Sylow (§33–§40)

`sylow_first` está **demostrado sin `sorry`**. Verificado:

```
lake build AczelSetTheory.Algebra.Sylow   →  Build completed successfully (0 errores, 0 warnings)
lake build                                →  Build completed successfully (proyecto entero)
grep sorry AczelSetTheory/                →  0 sorries en todo el proyecto
#print axioms sylow_first                 →  [propext, Classical.choice, Quot.sound]
                                             (NO depende de sorryAx)
```

**Enunciado**:
```lean
theorem sylow_first (grp : HFGroup) (p k : ℕ₀)
    (hp : Peano.Arith.Prime p) (hdvd : p ^ k ∣ HFSet.card grp.G) :
    ∃ sub : HFSubgroup grp, HFSet.card sub.H = p ^ k
```

**Estructura de la prueba** (inducción fuerte sobre `|G|`):
- `k = 0`: subgrupo trivial (`sylow_first_zero`).
- `k = σ m`, tres ramas:
  1. ∃ M propio con `p^(σm) ∣ |M|` → aplicar HI a `M.toHFGroup`, levantar con `subgroupOfSubgroup`.
  2. `|G| = p^(σm)` → `improperSubgroup` (el grupo entero).
  3. ∀ M propio `p^(σm) ∤ |M|` → `p ∣ |Z(G)|` (ecuación de clases) → Cauchy da `N ≤ Z(G)` de orden `p` → `N` normal → cociente `Q = G/N` con `p^m ∣ |Q|` y `|Q| < |G|` → HI da `sub_Q ≤ Q` → preimagen `π⁻¹(sub_Q)` tiene orden `p^m · p = p^(σm)`.

---

## Historial de fixes aplicados en esta sesión

| Sección | Problema raíz | Fix |
|---------|--------------|-----|
| §35 `prime_dvd_of_dvd_prime_pow` | `^` = `HPow.hPow` ≠ `Peano.Pow.pow`; `rw [pow_zero/pow_succ]` fallan | caso zero por igualdad definitional; caso succ con `pow_def` + `Peano.Pow.pow_succ` |
| §36 `noncentral_of_orb_noncentral` | `hy_center.2` dirección invertida; `show` con igualdad invertida | `.symm` en los puntos correctos; `rw [hy_conj]` para hacer `act g x` sintáctico |
| §36 `p_dvd_orbit_of_no_proper` | `eq_of_subset_of_card_eq` inexistente; dvd proof con `mul_comm` mal | `{x,y}` tiene card 2 > 1; `coprime_dvd_of_dvd_mul h_cop ⟨r, h_os.trans hr⟩` |
| §36 `p_dvd_card_orbit_closed_set` | `apply` no unifica + llamadas `⊆` con args al revés | `refine (... ?_ S rfl ...)`; pasar elemento explícito antes de membership |
| §37 `p_dvd_center_of_no_proper` | `k.pred`, `pow_succ_eq` inexistentes | reescrito con `add_cancel` + `sub_k_add_k` + `lt_self_add_l` + `divides_sub` |
| §38 `cyclicSubgroup_of_central_isNormal` | intro order; `hcomm_gpow`; `rw [isNormal]` | intro `g n hg hn`; calc chain; eliminar `rw [isNormal]` |
| §39 `card_quotient_cyclic` | `hp_ne_zero`, `div_mul_cancel` args | `hcyc_card ▸ hcycne`; `mul_cancelation_right` + `div_mul_cancel` |
| §40 `sylow_first` | `Prime` ambiguo, `lt_or_eq_of_le`, `p'.pred`, `sorry` | `Peano.Arith.Prime`; `le_iff_lt_or_eq`; `cases p'`; construcción `N` directa |

**Código muerto eliminado**: `mul_div_dvd_iff` (huérfano de la estrategia anterior).

---

## Lecciones técnicas clave (ver memoria `feedback_lean.md`)

1. **`^` en Sylow.lean resuelve a `HPow.hPow`**, no a `Peano.Pow.pow`. Puente:
   `@[simp] theorem pow_def (a b : ℕ₀) : a ^ b = Peano.Pow.pow a b := rfl`.
   Para reescribir potencias: `rw [pow_def]; exact Peano.Pow.pow_succ a b`.
2. **`Prime` ambiguo** con `open Peano.Arith Peano.Primes`: usar `Peano.Arith.Prime` explícito.
3. **`⊆` en HFSet** = `∀ x, x ∈ A → x ∈ B`: las pruebas de subset toman elemento explícito
   primero, luego la membership (`hT_sub x hx`, no `hT_sub hx`).
4. **`isNormal`** = `∀ (g n : HFSet), g ∈ G → n ∈ H → ...`: intro `g n hg hn`.
5. **`prime_ge_two`** da `le₀ 𝟚 p`, no `lt₀ 𝟙 p`. Puente: `(succ_lt_succ_iff 𝟘 _).mpr (pos_of_ne_zero ...)`.
6. **strongInductionOn**: usar `refine (... ?_ args...)`, no `apply ... args`.
7. **`def`/`toHFGroup`** se reducen definitionally: `M.toHFGroup.G = M.H`, `(quotientGroup ...).G = N.cosets`.

---

## Siguiente fase: Paridad Peano / CountingVN

Pendiente de arrancar. Objetivo: formalizar la paridad en el contexto de los naturales de
von Neumann (CountingVN). Por investigar:
- ¿Qué módulos existen ya? (`CardinalUn.lean`, `Symm.lean`, ...)
- ¿Cuál es el enunciado objetivo de "Paridad Peano"?

---

## Referencias técnicas (lemas peanolib verificados)

| Símbolo | Ubicación | Firma |
|---------|-----------|-------|
| `pow_def` | Combinatorics/Pow.lean:402 | `a ^ b = Peano.Pow.pow a b` |
| `Peano.Pow.pow_succ` | Combinatorics/Pow.lean | `n ^ σ m = mul (n ^ m) n` |
| `pos_of_ne_zero` | StrictOrder.lean:174 | `n ≠ 𝟘 → lt₀ 𝟘 n` |
| `succ_neq_zero` | Axioms.lean:178 | `σ n ≠ 𝟘` (no exportado; usar `(zero_ne_succ _).symm`) |
| `zero_ne_succ` | (exportado) | `𝟘 ≠ σ n` |
| `succ_lt_succ_iff` | StrictOrder.lean:336 | `lt₀ (σ n) (σ m) ↔ lt₀ n m` |
| `le_iff_lt_or_eq` | Order.lean:1418 | `le₀ a b ↔ lt₀ a b ∨ a = b` |
| `prime_ge_two` | (peanolib) | `Prime p → le₀ 𝟚 p` |
| `Mul.mul_lt_left` | Mul.lean:313 | `n ≠ 𝟘 → lt₀ 𝟙 m → lt₀ n (mul n m)` |
| `Add.lt_self_add_l` | Add.lean | `a ≠ 𝟘 → lt₀ b (add a b)` |
| `div_mul_cancel` | Arith.lean:800 | `b ≠ 𝟘 → b ∣ a → mul (a / b) b = a` |
| `mul_cancelation_left` | Mul.lean:163 | `n ≠ 𝟘 → mul n m = mul n k → m = k` |
| `mul_cancelation_right` | Mul.lean:200 | `k ≠ 𝟘 → mul n k = mul m k → n = m` |
| `Sub.sub_k_add_k` | Sub.lean:286 | `le₀ k n → add (sub n k) k = n` |
| `Add.add_cancel` | Add.lean:364 | `add n m = add n k → m = k` |
| `divides_sub` | Arith.lean:291 | `lt₀ b a → c ∣ a → c ∣ b → c ∣ sub a b` |
| `coprime_dvd_of_dvd_mul` | (peanolib) | `Coprime a b → a ∣ mul b c → a ∣ c` |
| `card_G_eq_card_H_mul_index` | CosetCount.lean:315 | `card G = mul (card cosets) (card H)` |
| `card_preimage_mul` | Sylow.lean:§34 | `card(π⁻¹(Q)) = mul (card Q.H) (card N.H)` |
| `cauchy_minimal` | Sylow.lean:§32 | `Prime (σ n) → σ n ∣ card G → ∃ sub, card sub.H = σ n` |
| `subgroupOfSubgroup` | Sylow.lean:§33 | `sub₂ : Subgrp sub₁.G → Subgrp G; .H = sub₂.H` |
| `cosetOf_mem_cosets` | QuotientGroup.lean:57 | `g ∈ G → sub.cosetOf g ∈ sub.cosets` |
| `card_eq_zero_iff` | Axioms/Cardinal.lean:148 | `card A = 𝟘 ↔ A = empty` |
