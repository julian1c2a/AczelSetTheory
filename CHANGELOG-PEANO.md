# Changelog — Peano (proyecto predecesor)

> Este es el historial del proyecto **Peano** (`https://github.com/julian1c2a/Peano`),
> predecesor directo de AczelSetTheory. Peano está en feature-freeze desde 2026-05-10.
> Para el historial de AczelSetTheory, ver [CHANGELOG.md](CHANGELOG.md).

---

## [Unreleased]

### Added (2026-05-21)

- **Primes.lean — 4 nuevos teoremas sobre divisor mínimo y primalidad (0 sorry)**:
  - `prime_dvd_mul` — p primo y p ∣ a·b ⇒ p ∣ a ∨ p ∣ b (lema de Gauss, forma binaria).
  - `smallestDivisor_not_dvd_of_lt` — n ≥ 2 ∧ 2 ≤ e < smallestDivisor(n) ⇒ e ∤ n.
  - `smallestDivisor_le_of_prime_dvd` — p primo y p ∣ n ⇒ smallestDivisor(n) ≤ p.
  - `smallestDivisor_prime` — n ≥ 2 ⇒ smallestDivisor(n) es primo.
  - Dependencias: `smallestDivisor_not_dvd_of_lt` apoya a `smallestDivisor_le_of_prime_dvd`; `smallestDivisor_le_of_prime_dvd` apoya a `smallestDivisor_prime`.
  - Build: **19 jobs · 0 sorry · 0 errores**.

- **Arith.lean — 1 nuevo teorema sobre división (0 sorry)**:
  - `mul_div_of_dvd_left` — c ∣ a ∧ c ≠ 0 ⇒ (a·b)/c = (a/c)·b.
  - Build: incluido en los 19 jobs anteriores.

- **doc/REFERENCE-Arithmetic.md — proyección completa (7 símbolos)**:
  - `[T12.35a] mul_div_of_dvd_left` (§12 Arith.lean)
  - `[T13.17a] prime_dvd_mul` (§13 Primes.lean)
  - `[D13.6b] smallestDivisor`, `[D13.6c] factorize` (nueva sección §13.6b)
  - `[T13.21b] smallestDivisor_not_dvd_of_lt`
  - `[T13.21c] smallestDivisor_le_of_prime_dvd`
  - `[T13.21d] smallestDivisor_prime`

### Added (2026-05-10)

- **Phase 6 — `zassenhaus_bijection_extremes` demostrado (0 sorry)**:
  - `GroupTheory/Zassenhaus.lean` — último teorema público del fichero: biyección
    $N(H\cap K)/N(H\cap M) \cong M(K\cap H)/M(K\cap N)$.
  - **Técnica clave**: lema privado `mapOn_bijective_cast` permite `subst heq` sobre una hipótesis
    de igualdad de codominio (`B = C`) cuando `B` es una variable libre en el enunciado.
    En el sitio de uso, ambos lados eran términos concretos de tipo `FSet (FSet ℕ₀)` construidos
    via `sortFSetList`; allí `cases`/`subst` fallan por eliminación dependiente. Extraer a un lema
    con variable libre resuelve el bloqueo.
  - **Prueba**: `f₂.comp (hquo_eq ▸ f₁_inv)` con `MapOn.comp_bijective` y `mapOn_bijective_cast`.
  - Build: **27 jobs · 0 sorry · 0 errores**.

- **Phase 5 — Polimorfismo completo de FinGroup/FSet/EquivRel**:
  - `ListsAndSets/EquivRel.lean` — nuevo módulo: `EquivRelOn`, `classOf`, `classOf_eq_of_mem_classOf`, `classOf_eq_or_disjoint`, `ClassFamily`, `canonicalClassFamily`, `classes`, `classes_cover`; 17 símbolos exportados.
  - `ListsAndSets/FSet.lean` — añadidos `eq_of_mem_iff'` (genérico), `sortedInsert'`, `sortList'`, `FSet.ofList` y lemas auxiliares.
  - `Combinatorics/Group.lean` — instancias `instDecidableEqSubgroup`, `instLTSubgroup`, `instStrictLinearOrderSubgroup`; permite `FSet (Subgroup G)`.
  - `GroupTheory/Sylow/Cosets.lean` — completamente refactorizado: `leftCoset`, `cosetRel`, `cosetEquivRel`, `cosetClasses`, `lagrange`; polimórfico sobre `{α : Type}`.
  - `GroupTheory/Action.lean` — completamente refactorizado: `GroupAction`, `orb`, `stab`, `orbit_stabilizer`, `orbits_partition`; polimórfico sobre `{α β : Type}`.
  - Build: **64 jobs · 0 errores · 0 sorry · 2 warnings** (variables sin usar).

- **Sylow.lean — `wielandt_fixed_point_exists` demostrado (axioma privado eliminado)**:
  - Demostrado como `private theorem` completo (0 sorry, 0 axioma privado).
  - Argumento: G actúa sobre Ω por traslación; p∤|Ω| → `wielandt_exists_nondvd_orbit_aux` da órbita de tamaño no divisible por p → tamaño 1 → estabilizador tiene orden p^(m+1).
  - Pendientes: `wielandt_p_ndvd_r` (caso `succ m'`), `sylow_third_mod`, `sylow_third_dvd`.

### Added (2026-05-06)

- **Sylow.lean — Wielandt Pieza A completada (4 teoremas, 0 sorry)**:
  - `wieldandtAct_gpow_add` — `act (g^a) · act (g^b) = act (g^(a+b))` sobre Ω.
  - `wieldandtAct_gpow_fixed_of_gcd_one` — si `gcd(|G|, p) = 1` entonces g^|G| fija todo S ∈ Ω.
  - `wielandt_orbit_remove` — extrae exactamente p elementos de la p-órbita de S en Ω (6 propiedades).
  - `wielandt_orbit_partition` — `|Ω| = |fix(Ω)| + p·k`; elimina el axioma privado.
  - Infraestructura: `wielandt_exists_nondvd_orbit_aux` (inducción estructural sobre |Ω|).

- **Foundation/GodelBeta.lean — completado (Phase F.2, 0 sorry)**:
  - `godel_beta_seq`, `encodeList`, `decodeList`, `encode_decode`.
  - Cierra la cadena Peano → Aczel → ZFC: `List ℕ₀ ≃ ℕ₀` formalizado sobre axiomas de Peano.

### Added (2026-05-05)

- **GroupTheory/CorrespondenceTheorem.lean — Cuarto Teorema de Isomorfismo (0 sorry, 0 axiomas privados)**:
  - `noncomputable def preimageSubgroup (G) (N) (hn) (Q)` — preimagen `ψ(Q) = π⁻¹(Q) ⊂ G` de un subgrupo `Q ≤ G/N`.
  - `def SubgroupAbove (G) (N) (_hn)` — subtipo de subgrupos de `G` que contienen a `N`.
  - `noncomputable def correspondencePhi` / `correspondencePsi` — las dos funciones inversas de la biyección.
  - `theorem imageSubgroup_preimage` — `φ(ψ(Q)) = Q`.
  - `theorem preimageSubgroup_image` — `ψ(φ(K)) = K` cuando `N ≤ K`.
  - `theorem correspondencePhi_psi`, `correspondencePsi_phi` — identidades de composición.
  - `theorem correspondenceInjective`, `correspondenceSurjective` — biyectividad de `φ`.
  - Lemas auxiliares privados: `sorted_list_unique`, `FSet_eq_of_mem_iff`, `leftCoset_inv_eq`, `subgroup_ext_mem`, `qsubgroup_ext_mem`.
  - **Trampa documentada**: `Function.Bijective` no existe sin Mathlib — workaround: dos teoremas separados `correspondenceInjective` + `correspondenceSurjective`.
  - **Trampa documentada**: `SubgroupAbove` usa `_hn` con guión bajo porque el tipo resultante (`Type`) no depende del valor de `hn` en Lean 4.
  - Build: 64 jobs · 0 errores · 0 warnings nuevos · 0 sorry.

- **NumberTheory/Wilson.lean — Teorema de Wilson (0 sorry)**:
  - `theorem wilson {p : ℕ₀} (hp : Prime p) : p ∣ add (factorial (sub p 𝟙)) 𝟙`
  - Estrategia: pairing argument sobre `{2, …, p−2}`. Cada elemento se empareja con su inverso modular, salvo los puntos fijos 1 y p−1. Producto del rango interior ≡ 1 (mod p); luego (p−1)! ≡ −1 (mod p).

- **GroupTheory/NormalSubgroup.lean** (sesiones anteriores, ahora en build):
  - `def centralizer (G) (H)` — centralizador `C_G(H)`.
  - `def normalizer (G) (H)` — normalizador `N_G(H)`.
  - `def rightCoset (G) (H) (g)` — coseto derecho `Hg`.
  - Criterios: `isNormal_iff_normalizer_eq_G`, `isNormal_iff_leftCoset_eq_rightCoset`.

- **GroupTheory/QuotientGroup.lean** (sesiones anteriores):
  - `quotientCarrier`, `quotientOp`, `quotientInv`, `quotientId`, `quotientGroup` — estructura de grupo cociente `G/N`.
  - `quotientHomomorphism` — homomorfismo canónico `π : G → G/N`.
  - `imageSubgroup` — imagen de un subgrupo `K ≥ N` en `G/N`.
  - 29 nombres exportados en total.

- **GroupTheory/FirstIsomorphism.lean** (sesiones anteriores):
  - `homKer`, `homImg` — núcleo e imagen de un homomorfismo.
  - `homKer_isNormal`, `quotientHomomorphism_surjective`.
  - `firstIsoMap` — isomorfismo `G/ker(φ) ≅ Im(φ)`, bijective.

- **GroupTheory/SecondIsomorphism.lean** (sesiones anteriores):
  - `subgroupHN` — subgrupo `HN = { h*n | h ∈ H, n ∈ N }`.
  - `interHN_as_subgroup_H`, `interHN_as_subgroup_H_isNormal` — `H ∩ N ⊴ H`.
  - `secondIsoMap` — isomorfismo `H/(H∩N) ≅ HN/N`, bijective.

### Added (2026-05-02)

- **Foundation/CantorPairing.lean — biyección ℕ₀×ℕ₀ ≅ ℕ₀ completada (Phase F.1, 0 sorry)**:
  - `triag (n : ℕ₀) : ℕ₀ := mul n (σ n) / 𝟚` — número triangular T(n) = n·(n+1)/2.
  - `pair (m n : ℕ₀) : ℕ₀ := add (triag (add m n)) m` — función de apareamiento de Cantor.
  - `antidiag`, `fst`, `snd` — inversa de `pair` (noncomputable, vía `choose_unique`).
  - Demostrados 13 teoremas públicos: `triag_zero`, `triag_succ`, `triag_strict_mono`,
    `triag_le_of_le`, `triag_le_pair`, `pair_lt_triag_succ`, `antidiag_exists`,
    `antidiag_unique`, `antidiag_spec`, `antidiag_pair`, `pair_fst`, `pair_snd`, `pair_surj`.
  - Lemas privados auxiliares: `two_dvd_mul_succ` (2 ∣ n·(n+1) por inducción), `mul_two_div_two` (2·m/2 = m).
  - **Trampa documentada**: `mul_succ` está probado por `rfl` (igualdad definitional),
    por lo que `congr 1` cierra la meta inmediatamente dejando sin goals el `rw` posterior.
    Solución: reescribir el calc usando `mul_succ` + `succ_mul` + `add_assoc` + `two_mul`.
  - **Trampa documentada**: operadores `*`, `+`, `-` son ambiguos (notación explícita + instancia
    typeclass). Solución: usar siempre `mul`, `add`, `sub` como llamadas de función.
  - `sub` requiere `open Peano.Sub` (no está en el export del namespace raíz).
  - Build: 51 jobs · 0 errores · 0 warnings · 0 sorry.

### Added (2026-04-28)

- **Sylow.lean — `wielandt_omega_card` demostrado (axioma → teorema)**:
  - Definida `private def sublistsOfLength : List ℕ₀ → ℕ₀ → List (List ℕ₀)` con tres casos: `(_, 𝟘) => [[]]`, `([], σ _) => []`, `(x :: xs, σ n) => map (x::·) (sublistsOfLength xs n) ++ sublistsOfLength xs (σ n)`.
  - Demostradas 6 propiedades: `_mem_len` (longitud = n), `_mem_sub` (elementos en elems), `_mem_sorted` (sublistas heredan orden), `_nodup_result` (lista de listas sin duplicados), `_complete` (todas las sublistas válidas están), `_card` (cardinalidad = `binom (lengthₚ elems) n` por inducción vía Pascal).
  - `wielandt_omega_card` convierte Ω en `sublistsOfLength G.carrier.elems N` y prueba las cuatro propiedades requeridas.
  - **Trampas Lean 4.29.0 documentadas**: `rcases h with rfl` sobre `a = x` (variable de inducción) puede eliminar `x` en lugar de `a`; usar `cases` + `rw` explícito. `congrArg σ` falla porque `σ` es notación; usar `rw [ih ...]` directamente. `List.mem_cons_self` tiene args implícitos. `List.nodup_singleton` no existe; usar `List.Pairwise.cons`. `lt_trans` tiene args explícitos; usar `lt_trans_wp`.
  - Reducción: **6 axiomas privados → 5**.

- **Sylow.lean — conclusión de `wielandt_fixed_point_exists` corregida**:
  - La conclusión anterior `∃ S ∈ Ω, ∀ g ∈ G, ∀ x ∈ S, G.op g x ∈ S` era matemáticamente falsa: la multiplicación izquierda es biyección G→G, forzando S = G.
  - Nueva conclusión correcta: `∃ H : Subgroup G, H.carrier.card = N` (estabilizador Stab_G(S₀) del argumento de Wielandt).
  - `sylow_center_step_wielandt` simplificada a una línea.

### Added (2026-04-27)

- **FinGroup polimórfico sobre tipo arbitrario (ADR-010)**:
  - `FinGroup (α : Type) [DecidableEq α] [LT α] [StrictLinearOrder α]` — carrier es `FSet α`, id es `α`. Alias `abbrev ℕ₀FinGroup := FinGroup ℕ₀` para compatibilidad.
  - `Action.lean`, `Cosets.lean`, `Sylow.lean`: signaturas actualizadas a `(G : FinGroup ℕ₀)` — cambio mecánico, pruebas intactas.
  - `Group.lean`: todos los teoremas generalizados sobre `{α} [DecidableEq α] [LT α] [StrictLinearOrder α]`.

- **StrictOrder.lean — instancia bridge `instIrreflLTOfSLO`**:
  - `instIrreflLTOfSLO : IrreflLT α` derivada automáticamente de `StrictLinearOrder α`.
  - Permite que `FSet α` resuelva `IrreflLT` sin instancia explícita para cada tipo.

- **sortedInsert generalizado a `[StrictLinearOrder α]`** (List.lean y FSet.lean):
  - `sortedInsert {α : Type} [LT α] [DecidableEq α] [StrictLinearOrder α] : α → List α → List α`
  - `sorted_sortedInsert` y `mem_sortedInsert_iff` generalizados.
  - `FSet (Tuple ℕ₀ n)` funciona automáticamente vía `instStrictLinearOrderTuple`.

- **ListList.lean y FSetFSet.lean eliminados**:
  - Contenido de `ListList.lean` fusionado en `List.lean` (§11–15: instancias LE, LT, DecidableRel, Repr).
  - Contenido de `FSetFSet.lean` fusionado en `FSet.lean`.
  - Build: 52 → 51 jobs, 0 errores, 0 warnings.

- **Tuple.lean — `instStrictLinearOrderTuple`**:
  - Instancia `StrictLinearOrder (Tuple α n)` derivada de `StrictLinearOrder α`.
  - Torre de tipos completa verificada en `TestTorre.lean`: `FSet (Tuple ℕ₀ n)`, `List (FSet (List ℕ₀))`, `FSet (FSet ℕ₀)`.

### Added (2026-04-24)

- **Binom.lean — `binom_prime_row` demostrado (T16.10)**:
  - `binom_prime_row {p r : ℕ₀} (hp : p ≠ 𝟘) (hr : r ≠ 𝟘) : C(mul p r, p) = mul r (C(sub (mul p r) 𝟙, sub p 𝟙))` — la identidad de fila C(p·r, p) = r · C(p·r−1, p−1).
  - Prueba: via `binom_mul_factorials` aplicado dos veces (stepA sobre C(n,p), stepB sobre n·C(n−1,p−1)), seguida de cancelación de factores comunes por `mul_cancelation_right` y `mul_cancelation_left`.
  - Auxiliar privado `binom_prime_row_aux (p' r' : ℕ₀)` aísla el caso succ/succ para evitar `set` y `conv_lhs` (no disponibles en Lean 4.29.0 sin Mathlib).
  - Trampa resuelta: `rw [← h]` reescribe **todas** las ocurrencias incluyendo sub-expresiones → solución con `congrArg factorial h.symm` para apuntar solo el argumento exterior.
  - Build: 52 jobs · 0 errores · 0 warnings.

### Added (2026-04-23)

- **Binom.lean — `prime_dvd_binom_prime` demostrado (T16.9)**:
  - Nuevos lemas privados: `prime_not_dvd_of_pos_lt {p a : ℕ₀} (ha_pos ha_lt) : ¬ (p ∣ a)` (0 < a < p implica p ∤ a) y `prime_not_dvd_factorial {p : ℕ₀} (hp : Prime p) : ∀ k, k < p → ¬ (p ∣ k!)` (por inducción).
  - `prime_dvd_binom_prime {p k : ℕ₀} (hp : Prime p) (hk_pos hk_lt) : p ∣ C(p, k)` — p primo, 0 < k < p ⇒ p ∣ C(p,k).
  - Estrategia: C(p,k)·k!·(p−k)! = p! via `binom_mul_factorials`; p | p! via `factorial_succ` + `divides_mul_left`; p ∤ k! y p ∤ (p−k)! via lemas privados; Euclides `hp.2.2` aplicado dos veces.
  - Trampa resuelta: ambigüedad de `Prime` entre `Arith.Prime` y `Primes.Prime` resuelta con `private abbrev Prime := Peano.Primes.Prime` (patrón ya presente en Sylow.lean línea 47).
  - Nueva dependencia: `Binom.lean` importa `Peano.PeanoNat.Primes` (actualizado en tabla de módulos y cabecera §16).

- **Sylow.lean — todos los teoremas de Sylow formalmente cerrados (0 sorry, 5 axiomas privados)**:
  - `cauchy_minimal` — demostrado por el argumento de órbitas de McKay: conteo módulo p sobre p-tuplos del grupo, con `mckay_orbit_count` y `mckay_orbit_remove`.
  - `sylow_lift_from_cauchy` — demostrado por inducción fuerte sobre |G|: caso base trivial, caso p^(n+1) | |G| delegado al axioma privado `sylow_center_step`, caso p^(n+1) ∤ |G| via subgrupos propios.
  - `sylow_first` — demostrado vía `sylow_lift_from_cauchy` + `cauchy_minimal`.
  - `sylow_second` — demostrado con dos axiomas privados temporales (`sylow_card_eq`, `sylow_second_incl`).
  - `sylow_third` — demostrado con dos axiomas privados temporales (`sylow_third_mod`, `sylow_third_dvd`).
  - **5 axiomas privados pendientes**: `sylow_center_step` (paso inductivo, ruta Wielandt), `sylow_card_eq`, `sylow_second_incl`, `sylow_third_mod`, `sylow_third_dvd`.
  - Infraestructura añadida: `subgroupToFinGroup`, `subgroupOfSubgroup`, `mckay_p_dvd_powEqId`, `mckay_orbit_remove`.
  - Build: 52 jobs · 0 errores · 0 warnings.

- **NEXT-STEPS.md — ruta de Wielandt documentada**:
  - 5 pasos para eliminar `sylow_center_step`: `p | C(p,k)` → C(pr,p) = r·C(pr−1,p−1) → C(pr,p) ≡ r (mod p) → Lucas → argumento de punto fijo de Wielandt.
  - Roadmaps para los otros 4 axiomas privados.
  - Plan a largo plazo de polimorfismo de `FinGroup` sobre tipo arbitrario.

### Added (2026-04-22)

- **Sylow.lean — `mckay_orbit_remove` demostrado sin sorry**:
  - Prueba completa del lema privado `mckay_orbit_remove`: dado un elemento `v ∈ S` no fijo bajo `rotateVector`, extrae su órbita de tamaño exactamente `p` y produce `S' = S \ orbit(v)` con cuatro propiedades garantizadas por tipos: `S'.Nodup`, cierre bajo rotación, `|S| = |S'| + p`, y `fix(S) = fix(S')`.
  - Sublemmas internos completamente demostrados: `orb_inj` (inyectividad de la órbita), `orbit_no_fixed` (ningún elemento de la órbita es fijo), `rl_inj` (inyectividad de `rotateList` para listas de longitud `p`), `orbit_preimage` (preimagen bajo `rotateVector` permanece en la órbita), `orbit_closed_rv` (cierre de la órbita bajo `rotateVector`), `nodup_sub_len` (lista nodup de sublista tiene longitud ≤), `filter_part` (partición de lista por predicado booleano).
  - Obstáculos técnicos resueltos: doble-reescritura de `p` en `rw [← hpj]`, cálculo de motive para `▸`, `Nat.add` opaco para `omega` (solucionado con `simp only [Nat.add_eq]`), `linarith` ausente sin Mathlib (reemplazado por `omega`), `List.Nodup.filter` inexistente (reemplazado por `List.filter_sublist.nodup`), dirección de `congrArg Subtype.val`.
  - Build: 52 jobs, 0 errores, 4 sorry warnings (sin cambio en el número de sorrys públicos).

### Added (2026-04-20)

- **Sylow.lean — Infraestructura para el argumento de McKay (Cauchy)**:
  - Añadido el tipo `Vector α n` para listas de longitud fija garantizada por tipos.
  - Añadidas instancias de `DecidableEq`, `LT` y `DecidableRel` para `Vector`.
  - Añadido el generador combinatorio `allVectorsList`.
  - Formalizada la operación de rotación de McKay: `mckayShiftList` y `mckayShift`.
  - Demostrada la preservación del grupo: `mckayShiftList_mem`.
  - Demostrada la inyectividad de la operación: `mckayShiftList_inj` y lema auxiliar `append_singleton_inj`.
  - Build verificado: 52 jobs, 0 errores, 4 sorry warnings (reducidos los errores previos).

### Added (2026-04-19)

- **Sylow.lean — lemas privados para `cauchy_minimal` completamente formalizados (sin sorry)**:
  - `card_pos_of_mem_aux`: si `x ∈ S.elems` entonces `lt₀ 𝟘 S.card` (usando `unfold FSet.card` + `cases` sobre la lista).
  - `order_dvd_of_pow_eq_id`: si `g^m = e` y `m > 0` entonces `ord(g) ∣ m`.
  - `order_eq_prime_of_pow`: si `g ≠ e`, `g^p = e`, `p` primo, entonces `ord(g) = p` (vía `prime_imp_irreducible`).
  - `gpow_lt_p_mem_cyclic`: si `i < p` y `p ∣ |G|`, entonces `g^i ∈ ⟨g⟩`.
  - `cyclicSubgroup_card_eq_prime`: construye biyección explícita `Fin₀Set(p) → ⟨g⟩` (inyectividad + sobreyectividad) y concluye `|⟨g⟩| = p`.
  - `cauchy_minimal` formalizado condicionalmente: la conclusión final sigue en sorry (argumento de McKay — conteo módulo p sobre p-tuplos).
  - **Todos los lemas auxiliares: 0 sorry.**

- **Sylow.lean — correcciones de infraestructura**:
  - Añadido `open Peano.Sub` (faltaba `sub` en scope).
  - Añadido `private abbrev Prime := Peano.Primes.Prime` para resolver la ambigüedad entre `Arith.Prime` (exportado por `Arith.lean`) y `Primes.Prime` (exportado por `Primes.lean`).
  - Sustituido `by_contra` (no válido en este proyecto) por estructura directa `rcases trichotomy ... / exfalso` en la prueba de inyectividad.
  - Corregidos patrones `rcases ... with h | rfl` cuando la variable ya no era libre tras la sustitución.
  - `simp only [f] at h_eq` añadido para desdoblar `f.toFun` antes de reescribir en la prueba de inyectividad.
  - Corregida la orientación de `h_card` en `cyclicSubgroup_card_eq_prime` (`h_card.symm`).

- **AI-GUIDE.md — sección de Comandos**:
  - Añadida § 29 "Commands" con definición formal del comando `actualiza doc` (10 pasos).
  - El comando describe el workflow completo de sincronización de documentación tras una sesión de desarrollo.

- **Estado de build (snapshot 2026-04-19)**:
  - `lake build`: 0 errores, 52 jobs.
  - Sorry activos: 4 (todos en `Sylow.lean`: `cauchy_minimal`, `sylow_lift_from_cauchy`, `sylow_first` n>0, `sylow_third`).
  - `check-sorry.bash`: 8 sorry en 3 archivos (4 Sylow.lean + 2 Perm.lean comentados + 2 Primes.lean comentados).
  - Warnings no-sorry: 4 (1 `unused variable` en Sylow.lean + 3 en Group.lean).

- **ListsAndSets/FSet.lean + FSetFunction.lean — cierre de infraestructura para Lagrange**:
  - `FSet.eq_of_mem_iff` añadido y exportado en `FSet.lean` (extensionalidad por pertenencia en `FSet ℕ₀`).
  - `ℕ₀FSet` y `ℕ₁FSet` añadidos explícitamente en `FSet.lean`.
  - `card_eq_mul_of_uniform_fibers` añadido y exportado en `FSetFunction.lean` (§ 3d/3e).
  - Soporte interno: lema auxiliar de descomposición por filtros complementarios + inducción sobre fibras uniformes.
  - `FSetFunction.lean` importa `Peano.PeanoNat.Mul` para el cierre aritmético del conteo.

- **Documentación técnica sincronizada**:
  - `REFERENCE.md` reproyectado con la API pública actual de `FSet.lean` y `FSetFunction.lean`.
  - `NEXT-STEPS.md` simplificado y reorientado a pendientes reales (Cosets/Action/Sylow).

- **Estado de build actualizado (snapshot de sesión)**:
  - `lake build`: 0 errores.
  - Sorries activos: 6 (`Action`: 2, `Cosets`: 1, `Sylow`: 3).
  - Warnings no-sorry: 3 variables no usadas en `Group.lean`.

- **Group.lean § 4d — Orden de elemento de grupo (B2.3)**:
  - `gpow_sub_eq_id`: si `gpow g m = gpow g n` con `n ≤ m` entonces `gpow g (m-n) = id`.
  - `orderExists` (private): existencia del mínimo `k ≥ 1` con `gpow g k = id`,
    usando `collision_of_card_lt` (palomar) + `well_ordering_principle`.
  - `order_wop` (private): mínimo k > 0 con `gpow g k = id`.
  - `order` (noncomputable): el orden de `g` en `G`, `order G g : ℕ₀`.
  - `order_pos`: `1 ≤ order G g` para todo `g ∈ G`.
  - `gpow_order_eq_id`: `gpow G g (order G g) = G.id`.
  - `order_minimal`: `order G g` es el mínimo positivo con `gpow g k = id`.
  - `order_le_card`: `order G g ≤ G.carrier.card` (de `collision_of_card_lt`).
  - `gpow_mul_order_eq_id`: `gpow G g (mul n (order G g)) = G.id` para todo `n`.
  - `gpow_mod_order`: `gpow G g n = gpow G g (n % (order G g))`.
  - Imports añadidos: `Peano.Prelim`, `Peano.PeanoNat.Sub`, `Peano.PeanoNat.Mul`, `Peano.PeanoNat.Div`.
  - Opened: `Peano.Sub` para acceder a `sub`.

- **Group.lean § 5 — Subgrupo cíclico completo (B3)** (commit `413c6e3`, 8→5 sorry):
  - `cyclicSubgroup` sorry eliminado: cierre por `op · inv⁻¹` usando `gpow_mod_order`.
  - `cyclicSubgroup'` sorrys eliminados: `op_closed` y `inv_closed` vía `gpow_mod_order`.
  - Build: 51 jobs, 0 errores, **5 sorry warnings** (−3 respecto a 2026-04-16).

- **Perm.lean + FSetFunction.lean — B1a** (commit `9a17a8e`, 9→8 sorry):
  - `perm_map_of_injective_on_nodup` añadido a `FSetFunction.lean` § 3f.
  - `FunPerm.comp is_perm` demostrado en `Perm.lean` vía inyectividad de composición.

### Added (2026-04-16)

- **FSetFunction.lean \u00a7 3b \u2014 Palomar con colisi\u00f3n expl\u00edcita**:
  - `not_injective_of_card_lt`: contrapositivo de `card_le_of_injective` \u2014
    si `B.card < A.card` entonces ninguna `f : A \u2192 B` puede ser inyectiva.
  - `collision_of_card_lt`: principio del palomar con testigos expl\u00edcitos \u2014
    `\u2203 a\u2081 a\u2082, a\u2081 \u2208 A \u2227 a\u2082 \u2208 A \u2227 a\u2081 \u2260 a\u2082 \u2227 f(a\u2081) = f(a\u2082)` cuando `B.card < A.card`.
  - Ambos exportados en el bloque export de FSetFunction.lean.
  - Proof: term-mode v\u00eda `Classical.byContradiction` (no existe `by_contra` en el proyecto).
  - **Uso clave**: son la base para demostrar `orderExists` en B2.3 (orden de elemento de grupo).
  - Build: 51 jobs, 0 errores, 9 sorry warnings.

- **Group.lean \u2014 Bloques B2.2 completo + B3 (subgrupos)**:
  - **B2.2**: `gpow_comm_single` (`gpow G g n \u00b7 g = g \u00b7 gpow G g n`),
    `gpow_inv` (`gpow G (G.inv g) n = G.inv (gpow G g n)`). Ambos sorry-free.
  - **B3.1**: `trivialSubgroup`, `improperSubgroup`, `Subgroup.IsTrivial`, `Subgroup.IsProper`.
  - **B3.2**: `cyclicCarrier` (private), `cyclicCarrier_id_in`, `cyclicCarrier_mem_iff`,
    `cyclicSubgroup` (1 sorry: cierre por op\u00b7inv\u207b\u00b9), `cyclicSubgroup'` (1 sorry: inv_closed).
    Ambos sorry bloqueados en B2.3 `order`.
  - **B3.3**: `Subgroup.IsNormal`, `trivialSubgroup_normal`, `improperSubgroup_normal`.
  - **B3.6**: `Subgroup.inter`, `inter_subset_left`, `inter_subset_right`,
    `inter_normal_of_normal`.
  - Build: 51 jobs, 0 errores, 9 sorry warnings (7 preexistentes + 2 nuevos en cyclic).

### Added (2026-04-15)

- **Phase 25 — Teoría de grupos finitos**:
  - **Combinatorics/Counting.lean**: Conteo combinatorio.
  - **Combinatorics/Perm.lean**: Tipo de permutaciones (⚠ 1 sorry).
  - **Combinatorics/Sign.lean**: Signo de permutaciones (paridad de transposiciones).
  - **Combinatorics/Orbit.lean**: Órbitas de elementos bajo permutaciones.
  - **Combinatorics/Group.lean**: Grupo simétrico Sym(A) (⚠ 1 sorry).
  - **Combinatorics/GroupTheory/Action.lean**: Acciones de grupo (⚠ 2 sorry).
  - **Combinatorics/GroupTheory/Sylow/Cosets.lean**: Coclases (⚠ 1 sorry).
  - **Combinatorics/GroupTheory/Sylow/Sylow.lean**: Teoremas de Sylow (⚠ 3 sorry).
  - Build inicial: 51 jobs, 14 sorry warnings, 0 errors. (Reducido a 9 sorry en sesión 2026-04-15–16.)

- **Phase 24 — Conjuntos finitos y funciones**:
  - **ListsAndSets/ListList.lean**: Listas de listas.
  - **ListsAndSets/FSetFSet.lean**: Conjuntos de conjuntos finitos.
  - **ListsAndSets/FSetFunction.lean** (~90 declaraciones exportadas, ampliadas a ~92 en 2026-04-16):
    - `MapOn`: funciones totales entre FSet, `id`, `comp`, `comp_assoc`.
    - `Im`: imagen, cardinalidad de la imagen.
    - Inyectividad, sobreyectividad, biyectividad con iff de cardinalidad.
    - `leftInverse`, `rightInverse`, `inverse` para biyecciones, `inverse_involution`.
    - Principio del Palomar: desigualdades de cardinalidad.
    - `PreIm`, fibras, restricción.
    - `BinOpOn`: operaciones binarias sobre FSet.
    - Endomorfismos (`EndoOn`), especialización para A → A.
    - `Perm`: tipo de permutaciones biyectivas, inversas, composición.
  - List.lean y FSet.lean migrados a `ListsAndSets/` subdirectory.

- **Phase 21.6 — Fermat.lean**:
  - **NumberTheory/Fermat.lean**: `fermat_little` — Pequeño Teorema de Fermat
    ($a^{p-1} \equiv 1 \pmod{p}$ si $p$ primo y $p \nmid a$).
  - Estrategia: reducción a coprimalidad + Euler + totient_prime.

- **Phase 21.1–21.2 — Digits y Pairing**:
  - **Digits.lean**: `digits`, `ofDigits`, `numDigits` — representación en base *b*.
  - **Pairing.lean**: `cantorPair`, `cantorUnpair` — emparejamiento de Cantor con inversas.

- **Prelim refactoring**:
  - `Prelim.lean` dividido en `Prelim/ExistsUnique.lean` (constructivo) y `Prelim/Classical.lean` (noncomputable).
  - **ConstructiveCheck.lean**: Módulo de verificación de constructividad.

- **MapOn.comp_assoc**: Asociatividad general de la composición de funciones entre FSet (proof: `rfl`).

### Added (2026-04-09)

- **Phase 21.7b — Orden avanzado**:
  - **Order.lean**: `lt_or_ge (a b : ℕ₀) : Lt a b ∨ Le b a`,
    `le_or_lt (a b : ℕ₀) : Le a b ∨ Lt b a` + exportados.
  - **WellFounded.lean**: `noncomputable strongRecOn {C : ℕ₀ → Sort _} (n) (h) : C n`
    (recursión fuerte), `strongInductionOn {P : ℕ₀ → Prop} (n) (h) : P n` (inducción
    fuerte). Ambos vía `well_founded_lt.recursion`.
  - **Decidable.lean**: `instance : DecidableRel (@LT.lt ℕ₀ _)` (envuelve `decidableLt`),
    `instance : DecidableRel (@LE.le ℕ₀ _)` (envuelve `decidableLe`).
  - Build: 33 jobs, 0 warnings, 0 sorry.

- **Phase 21 — Decidable Prime**:
  - **Primes.lean**: `prime_imp_smallestDivisor_eq_self` (p primo ⇒ smallestDivisor p = p),
    `isPrimeb` (test booleano: `ble 𝟚 n && decide (smallestDivisor n = n)`),
    `isPrimeb_iff` (iff a `Prime n`), `decidablePrime (n : ℕ₀) : Decidable (Prime n)`.
  - Build: 33 jobs, 0 warnings, 0 sorry.

- **Phase 21.8 — IsEven/IsOdd**:
  - **Arith.lean**: `IsEven (n) := n % 𝟚 = 𝟘`, `IsOdd (n) := n % 𝟚 = 𝟙`,
    `decidableIsEven`, `decidableIsOdd`, `even_zero`, `odd_one`, `even_or_odd`,
    `not_even_and_odd`, `not_even_iff_odd`, `not_odd_iff_even`. Exportados 12 símbolos nuevos.
  - Build: 33 jobs, 0 warnings, 0 sorry.

### Added (2026-04-09) [earlier]

- **Isomorfismos Nat↔ℕ₀ completos para mul, div, mod, pow, gcd, lcm (§ 20.5)**:
  Completados los 14 teoremas de isomorfismo restantes en 4 módulos:
  - **Mul.lean**: `isomorph_Ψ_mul`, `isomorph_Λ_mul` (inducción sobre `m`, cadena `calc`)
  - **Div.lean**: `isomorph_Ψ_div` (vía `Nat.div_eq_of_lt_le`),
    `isomorph_Ψ_mod` (requiere `m ≠ 𝟘`, vía `Nat.add_left_cancel` + `Nat.div_add_mod`),
    `isomorph_Λ_div`, `isomorph_Λ_mod` (patrón `congrArg Λ`)
  - **Pow.lean**: `isomorph_Ψ_pow`, `isomorph_Λ_pow` (inducción sobre `m`, cadena `calc`)
  - **Arith.lean**: `isomorph_Ψ_gcd` (inducción bien fundada + `gcd_step`),
    `isomorph_Λ_gcd`, `isomorph_Ψ_lcm` (`unfold` + rewrite), `isomorph_Λ_lcm`
  - **Isomorph.lean**: Actualizado con imports de Mul, Div, Pow, Arith + 6 bloques export nuevos.
  - **Peano.lean**: Exports actualizados para los 14 nuevos teoremas.
  - **Nota**: `isomorph_Ψ_mod` requiere `hm : m ≠ 𝟘` porque Peano define `mod n 𝟘 = 𝟘`
    mientras Lean core define `Nat.mod n 0 = n`.
  - Build: 30 jobs, 0 warnings, 0 sorry.

### Added (2026-04-10)

- **Log.lean — Logaritmo entero con resto (§ 20)**:
  Nuevo módulo `Peano/PeanoNat/Log.lean` (`namespace Peano.Log`).
  Definiciones: `logMod`, `log`, `logRem` — piso del logaritmo en base `b` con resto.
  Patrón `(k, r)` tal que `n = b^k + r` y `n < b^{k+1}`.
  Exacto (`n` potencia de `b`) sii `r = 0`.
  11 símbolos exportados: `logMod`, `log`, `logRem`, `log_zero`, `logRem_zero`,
  `log_of_lt`, `logRem_of_lt`, `log_one`, `logRem_one`, `logMod_spec`, `log_upper_bound`.
  Build: 14 jobs, 0 warnings, 0 sorry.

- **Sqrt.lean — Raíz cuadrada entera con resto (§ 21)**:
  Nuevo módulo `Peano/PeanoNat/Sqrt.lean` (`namespace Peano.Sqrt`).
  Definiciones: `sqrtMod`, `sqrt`, `sqrtRem` — piso de raíz cuadrada con resto.
  Patrón `(k, r)` tal que `n = k² + r` y `r < 2k + 1`.
  Exacto (cuadrado perfecto) sii `r = 0`.
  10 símbolos exportados: `sqrtMod`, `sqrt`, `sqrtRem`, `sqrt_zero`, `sqrtRem_zero`,
  `sqrt_one`, `sqrtRem_one`, `sqrtMod_spec`, `sqrtRem_lt`, `sqrt_upper_bound`.
  Build: 14 jobs, 0 warnings, 0 sorry.

### Changed (2026-04-09)

- **Arith.lean GCD/LCM/Coprime Mathlib-style extensions (§ 8)**:
  Made `gcd_comm`, `gcd_divides_left`, `gcd_divides_right` public (were private).
  Added 25 new theorems: `gcd_dvd_left`, `gcd_dvd_right`, `dvd_gcd`,
  `gcd_zero_right`, `gcd_zero_left`, `gcd_one_right`, `gcd_one_left`, `gcd_self`,
  `gcd_eq_zero_iff`, `gcd_ne_zero_left`, `gcd_ne_zero_right`, `dvd_gcd_iff`,
  `gcd_assoc`, `IsGCD_gcd`, `div_mul_cancel`, `gcd_mul_lcm`, `lcm_comm`,
  `lcm_zero_left`, `lcm_zero_right`, `dvd_lcm_left`, `dvd_lcm_right`, `lcm_self`,
  `coprime_comm`, `coprime_one_right`, `coprime_one_left`.
  Updated export blocks in Arith.lean and Peano.lean.
  Build: 28 jobs, 0 warnings, 0 sorry.

- **Rename MaxMin → Lattice**: `Peano/PeanoNat/MaxMin.lean` renamed to
  `Peano/PeanoNat/Lattice.lean`. Namespace `Peano.MaxMin` → `Peano.Lattice`.
  All imports, opens, exports, and fully-qualified references updated across
  8 dependent files. Documentation updated in all `.md` files.

- **Lattice.lean Mathlib-style extensions (§ 7)**:
  Added 18 new theorems: `max_min_self`, `min_max_self` (absorption Mathlib naming),
  `min_le_max`, `max_eq_left_iff`, `max_eq_right_iff`, `min_eq_left_iff`,
  `min_eq_right_iff`, `max_le_iff`, `le_min_iff`, `max_le_max`, `min_le_min`,
  `max_left_comm`, `min_left_comm`, `max_right_comm`, `min_right_comm`,
  `max_succ_succ`, `min_succ_succ`. Export block: 74 symbols total.
  Build: 28 jobs, 0 warnings, 0 sorry.

- **FSet.lean warning fix**: Removed unused `hu` parameter from
  `uniqueKeys_factListAddFactor`.

### Changed (2026-04-10)

- **Phase 17 — Factor Combinatorics subdirectory**: Moved `Pow.lean`,
  `Factorial.lean`, `Binom.lean`, `NewtonBinom.lean` into
  `Peano/PeanoNat/Combinatorics/`. All internal cross-imports updated.
  - `Peano.lean` imports updated to `Peano.PeanoNat.Combinatorics.*`.
  - Build: 22/22 jobs, 0 sorry, 0 warnings.

- **Phase 16 — Factor Decidable module**: New reexport module
  `Peano/PeanoNat/Decidable.lean` that collects all Decidable instances
  (`decidableLt`, `decidableGt`, `decidableLe`, `decidableGe`), boolean
  comparison functions (`blt`, `bgt`, `ble`, `bge`), and their iff
  equivalence theorems from StrictOrder and Order into a single import.
  - Build: 22/22 jobs, 0 sorry, 0 warnings.

- **Phase 15 — Create Isomorph.lean**: New reexport module
  `Peano/PeanoNat/Isomorph.lean` that collects all 30 Nat↔ℕ₀ isomorphism
  theorems (Λ/Ψ injectivity, bijectivity, composition, commutativity with
  σ/τ, and operation-level isomorphisms for lt/le/max/min/add/sub) from
  6 source modules into a single import point.
  - `Peano.lean` updated with `import Peano.PeanoNat.Isomorph`.
  - Build: 21/21 jobs, 0 sorry, 0 warnings.

- **Phase 14 — Extract Prelim.lean**: Extracted `ExistsUnique`, `choose`,
  `choose_spec`, `choose_unique`, `choose_spec_unique`, `choose_uniq` and
  `∃¹` syntax macros from `PeanoNat.lean` into new `Peano/Prelim.lean`.
  - `PeanoNat.lean` now imports `Peano.Prelim` instead of `Init.Classical`.
  - `Peano.lean` updated with `import Peano.Prelim` + separate export block.
  - DEPENDENCIES.md updated (new Prelim node in dependency graph).
  - Build: 20/20 jobs, 0 sorry, 0 warnings.

### Changed (2026-04-08)

- **Phase 13 — Subdirectory restructure**: Moved 15 `PeanoNat*.lean` files into
  `Peano/PeanoNat/` subdirectory with stripped prefix names.
  - `PeanoNatAxioms.lean` → `PeanoNat/Axioms.lean`, `PeanoNatAdd.lean` → `PeanoNat/Add.lean`, etc.
  - All imports updated: `Peano.PeanoNatXxx` → `Peano.PeanoNat.Xxx`.
  - `PeanoNat.lean` remains as barrel module at `Peano/PeanoNat.lean`.
  - DEPENDENCIES.md updated with new paths and module names.
  - AI-GUIDE.md §22 updated with new directory structure + §22.1 Prelim.lean standard.
  - AI-GUIDE-update.md created as cross-project template document.
  - Build: 19/19 jobs, 0 sorry, 0 warnings.
- **Phase 11 — Warning cleanup**: Removed unused `Nat.sub` simp arg in Sub.lean:484.
  Build: 19/19, 0 warnings.

### Changed (2026-04-09)

- **Fase 10 — Migración de nombres de identificadores**: Todos los identificadores
  públicos migrados a convenciones Mathlib4 (NAMING-CONVENTIONS.md).
  - **PeanoNat.lean**: `EqFnGen`→`eqFnGen`, `Comp`→`comp`, `EqFn`→`eqFn`,
    `EqFn2`→`eqFn2`, `EqFnNat`→`eqFnNat`.
  - **PeanoNatAxioms.lean**: `AXIOM_*` prefijos eliminados (→ `isNat_zero`,
    `isNat_succ`, `zero_ne_succ`, `succ_isNat`, `succ_congr`, `succ_injective`,
    `induction_principle`), `is_zero`→`isZero`, `is_succ`→`isSucc`,
    `return_branch`→`returnBranch`.
  - **PeanoNatStrictOrder.lean**: `BLt`→`blt`, `BGt`→`bgt`, `nlt_0_0`→`not_lt_zero`,
    `lt_0_n`→`pos_of_ne_zero`, `lt_then_neq`→`ne_of_lt`.
  - **PeanoNatOrder.lean**: `BLe`→`ble`, `BGe`→`bge`, `Le'`→`le'`.
  - **PeanoNatMaxMin.lean**: `Lt_of_not_le`→`lt_of_not_le`, `eq_max_min_then_eq`→
    `eq_of_max_eq_min`, `if_neq_then_max_xor`→`max_ne_min_of_ne`,
    `neq_args_then_lt_min_max`→`lt_max_of_ne`, `nexists_max_abs`→`not_exists_max`.
  - **PeanoNatAdd.lean**: `add_cancelation`→`add_cancel`.
  - **PeanoNatMul.lean**: `mul_ldistr`→`mul_add`, `mul_rdistr`→`add_mul`,
    `mul_eq_zero_wp`→`eq_zero_of_mul_eq_zero`,
    `mul_le_then_exists_max_factor`→`exists_factor_of_mul_le`.
  - **PeanoNatDiv.lean**: `divMod_eq`→`divMod_spec`, `mod_lt_divisor`→`mod_lt`,
    `div_of_lt_snd_interval`→`div_eq_two`.
  - **PeanoNatArith.lean**: `Factors_of`→`factorsOf`.
  - Peano.lean export blocks actualizados.
  - Build verificado: 19/19 jobs, 0 sorry.

### Changed (2026-04-08)

- **Fase 8 — Archivo renombrado**: `Peano/PeanoNatLib.lean` → `Peano/PeanoNat.lean`.
  - Imports actualizados en los 15 módulos dependientes + `Peano.lean` + `_template.lean`.
  - `frozen_files.txt`, `locked_files.txt`, `new-module.bash` actualizados.
  - Documentación actualizada (README, CURRENT-STATUS-PROJECT, NEXT-STEPS).
  - Build verificado: 19/19 jobs, 0 sorry.
- **Directorio renombrado**: `PeanoNatLib/` → `Peano/` — todos los imports, scripts y documentación actualizados.
- **Copyright headers**: Añadidos a los 9 módulos que no los tenían (AI-GUIDE §19).
- **Comentarios de ruta**: `PeanoNatLib/` → `Peano/` en las cabeceras de los 16 módulos.
- **Scripts**: `gen-root.bash`, `new-module.bash`, `git-lock.bash`, `copiar_txt.bash` — referencias actualizadas.
- **lakefile.lean** y **Peano.lean**: Comentarios actualizados.
- **.gitignore**: Añadido `LSP_*.log`.
- **README.md**: Versión de Lean corregida `v4.23.0` → `v4.29.0`.
- **CURRENT-STATUS-PROJECT.md**: Añadidos 6 módulos faltantes (Pow, Factorial, Binom, NewtonBinom, Primes, PeanoNatLib), actualizada a 19 jobs.
- **NEXT-STEPS.md**: Reescrito con Fases 7–10 detalladas (plan de renombrado de archivo, namespaces, migración de identificadores).
- Build verificado: 19/19 jobs, 0 sorry.

### Added (2026-03-16)

- **`Peano/PeanoNatPrimes.lean`** — módulo completamente demostrado, **cero `sorry`**.
  - `unique_prime_factorization` — **TFA unicidad** completamente probado. Dos errores de compilación resueltos en las ramas `p = p₀` y `p ≠ p₀` del `by_cases` final: la rama positiva requería `simp [DList.filter, DList.length]` en lugar de `simp` simple; la rama negativa requería `simp [DList.filter, Ne.symm h_pp₀]` + `rw [filter_count_neq …]` (dirección directa) en lugar del `simp only` + `rw [← …]` insuficiente.
  - `coprime_dvd_of_dvd_mul` (**Lema de Gauss**) — demostración completa. Los `sorry` de aritmética con resta saturada se sustituyeron por `sub_k_add_k`, `add_k_sub_k`, `lt_self_add_r` y `sub_pos_iff_lt`.
  - `irreducible_imp_prime`, `prime_iff_irreducible`, `prime_iff_has_exactly_two_divisors` — demostradas sin `sorry`, dependiendo de `coprime_dvd_of_dvd_mul`.
  - Estado del módulo actualizado: el comentario de cabecera ya no indica ningún `sorry` legítimo.
- **`REFERENCE.md`** — sección 12 actualizada: eliminados todos los marcadores ⚠️ sorry de T12.10, T12.11, T12.14, T12.19 y T12.28; estado del módulo corregido a "completamente demostrado".

- **`Peano/PeanoNatNewtonBinom.lean`** — módulo completado sin ningún `sorry`.
  - `finSum_succ_left (f n)` — desplazamiento a la izquierda: Σ_{k=0}^{n+1} f(k) = f(0) + Σ_{k=0}^{n} f(k+1).
  - `finSum_reverse (f n)` — invariancia por inversión del índice: Σ_{k=0}^{n} f(k) = Σ_{k=0}^{n} f(n−k).
  - `sum_binom_eq_pow_two (n)` — **demostrado**: Σ_{k=0}^{n} C(n,k) = 2ⁿ. Prueba por inducción con `finSum_succ_left` y Pascal.
  - `newton_binom (a b n)` — **demostrado**: (a+b)ⁿ = Σ_{k=0}^{n} C(n,k)·aᵏ·b^(n−k). Prueba por inducción; paso usa `binomTerm_pascal_step`, `finSum_mul_const_right`, `finSum_add_fn` y álgebra.
  - `exists_nm_growth` — **demostrado** con testigo n=2, m=1: ∀k≥1, 2+k < 2·2ᵏ. Prueba por inducción en k con lema auxiliar privado `lt_add_double_of_lt_of_pos`.
  - Eliminados todos los `sorry` del módulo.
- **`REFERENCE.md`** — sección 17 actualizada: añadidos T17.9b (`finSum_succ_left`), T17.9c (`finSum_reverse`); eliminados marcadores ⚠️ sorry de T17.10, T17.13, T17.15; estado del módulo actualizado a "completamente demostrado"; testigo de `exists_nm_growth` corregido a n=2, m=1.
- **`README.md`** — sección `Peano.NewtonBinom` actualizada; eliminados marcadores ⚠️ sorry de `sum_binom_eq_pow_two`, `newton_binom`, `exists_nm_growth`.

### Added (2026-03-15)

- **`Peano/PeanoNatNewtonBinom.lean`** — módulo nuevo, `namespace Peano.NewtonBinom`.
  - `finSum (f : ℕ₀ → ℕ₀) : ℕ₀ → ℕ₀` — sumatorio finito Σ_{k=0}^{n} f(k); computable, recursión estructural.
  - Propiedades demostradas: `finSum_zero`, `finSum_succ`, `finSum_zero_fn`, `finSum_add_fn` (linealidad), `finSum_mul_const`, `finSum_mul_const_right` (escalado), `finSum_le_of_le` (monotonía), `finSum_pos` (positividad), `finSum_const` (suma constante = (n+1)·c).
  - `binomTerm a b n k` = C(n,k)·aᵏ·b^(n−k) — término k-ésimo del binomio; con `binomTerm_zero` y `binomTerm_self`.
  - `sum_binom_eq_pow_two (n)` — Σ_{k=0}^{n} C(n,k) = 2ⁿ. ⚠️ sorry en reindexación con Pascal.
  - `newton_binom (a b n)` — (a+b)ⁿ = Σ_{k=0}^{n} C(n,k)·aᵏ·b^(n−k). ⚠️ sorry en convolución de sumatorios (caso base demostrado).
  - `pow_add_split (n m k)` — nᵐ⁺ᵏ = nᵐ·nᵏ.
  - `exists_nm_growth` — ∃n=4, m=2, ∀k≥1, (n+k)ᵐ < n^(m+k). ⚠️ sorry en cota exponencial.
- **`Peano.lean`** — añadidos imports y re-exports de `PeanoNatPow`, `PeanoNatFactorial`, `PeanoNatBinom`, `PeanoNatNewtonBinom`.
- **`REFERENCE.md`** — secciones 13 (Pow, completada T13.7–T13.23), 14 (Factorial, nueva), 15 (Binom, nueva), 16 (Peano.lean raíz actualizada), 17 (NewtonBinom, nueva); tabla de módulos y namespaces ampliada.

### Added (2026-03-03)

- `PeanoNatArith.lean`: Teorema `antisymm_divides {a b : ℕ₀} : a ∣ b → b ∣ a → a = b` — antisimetría de la divisibilidad en `ℕ₀`.
- `PeanoNatArith.lean`: Lema privado `gcd_divides_left (a b : ℕ₀) : gcd a b ∣ a` (y `gcd_divides_right`).
- `PeanoNatArith.lean`: Teorema `gcd_divides_max (a b : ℕ₀) : gcd a b ∣ max a b` y `gcd_divides_min`.
- `PeanoNatArith.lean`: Teorema `gcd_divides_linear_combo (a b n m : ℕ₀) : gcd a b ∣ (a * n + b * m)`.
- `PeanoNatArith.lean`: Lema privado `gcd_step (a b : ℕ₀) (hb : b ≠ 𝟘) : gcd a b = gcd b (a % b)` — paso de reducción euclideo; demostrado con `antisymm_divides` + `gcd_greatest`.
- `PeanoNatArith.lean`: Lema privado `bezout_additive` — forma OR de la identidad de Bézout (`∃ n m, G + n*min = m*max ∨ G + n*max = m*min`). Inducción bien fundada con 5 ramas; alternancia OR propagada en la rama recursiva.
- `PeanoNatArith.lean`: Teorema `bezout_natform (a b : ℕ₀) : ∃ n m, gcd a b = n * a - m * b ∨ gcd a b = n * b - m * a` — identidad de Bézout en forma natural (coeficientes ℕ₀).
- `PeanoNatArith.lean`: Lema privado `gcd_comm (a b : ℕ₀) : gcd a b = gcd b a` — conmutatividad del MCD en `ℕ₀`.
- `PeanoNatArith.lean` \[sección ℕ₁\]: Definiciones `Divides₁`, `IsGCD₁`, `gcd₁`, `Coprime₁` para el subtipo `ℕ₁ = {n : ℕ₀ // n ≠ 𝟘}`.
- `PeanoNatArith.lean` \[sección ℕ₁\]: Teoremas `divides₁_refl`, `divides₁_trans`, `divides₁_antisymm`.
- `PeanoNatArith.lean` \[sección ℕ₁\]: Lema privado `mod_eq_zero_iff_divides {a b : ℕ₁} : a.val % b.val = 𝟘 ↔ b ∣₁ a`.
- `PeanoNatArith.lean` \[sección ℕ₁\]: Lema privado `gcd₁_val_eq (a b : ℕ₁) : (gcd₁ a b).val = gcd a.val b.val` — puente entre `gcd₁` sobre `ℕ₁` y `gcd` sobre `ℕ₀`. La definición de `gcd₁` usa `dite` directo (sin `let r := …`) para que `unfold` + `dif_pos`/`dif_neg` funcionen sin que el elaborador desdoble el cuerpo recursivo.
- `PeanoNatArith.lean` \[sección ℕ₁\]: Teoremas `gcd₁_comm`, `gcd₁_divides_left`, `gcd₁_divides_right`, `gcd₁_divides_both`.
- **`PeanoNatArith.lean` completamente demostrado** — cero `sorry`.
- `REFERENCE.md`: Actualizada con todos los teoremas nuevos y sección ℕ₁.

### Added (2026-03-02)

- `PeanoNatMul.lean`: Teorema `mul_sub (c a b : ℕ₀) (h_lt : Lt b a) : mul c (sub a b) = sub (mul c a) (mul c b)` — distributividad de la multiplicación sobre la resta truncada bajo condición `b < a`.
- `PeanoNatMul.lean`: Exportados `mul_le_mono_right`, `mul_sub` y `lt_of_lt_of_le` desde `Peano.Mul`.
- `PeanoNatArith.lean`: Teorema `divides_sub {a b c : ℕ₀} (h_lt : Lt b a) (ha : c ∣ a) (hb : c ∣ b) : c ∣ (sub a b)` — divisibilidad se preserva bajo la resta truncada.
- `PeanoNatArith.lean`: Teorema `divides_mod {a b c : ℕ₀} (ha : c ∣ a) (hb : c ∣ b) : c ∣ (a % b)` — si `c` divide `a` y `b`, también divide el resto `a % b`.
- `PeanoNatArith.lean`: Demostración completa de `gcd_greatest (a b c : ℕ₀) : (c ∣ a ∧ c ∣ b) → c ∣ gcd a b` usando inducción bien fundada con patrón `H` doblemente generalizado.
- `PeanoNatArith.lean`: Exportados `divides_sub`, `divides_mod` y `gcd_greatest` desde `Peano.NatArith`.
- `REFERENCE.md`: Actualizada con los nuevos teoremas.
