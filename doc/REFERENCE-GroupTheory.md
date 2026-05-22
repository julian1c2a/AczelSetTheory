# Referencia Técnica — Teoría de Grupos Finitos (`Peano.GroupTheory`)

**Última actualización:** 2026-05-10  
**Autor:** Julián Calderón Almendros  
**Retorno:** [REFERENCE.md](../REFERENCE.md)

> Documentación de los símbolos públicos del módulo
> `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`.
> Solo contiene lo completamente probado (requisito 8 del AI-GUIDE).
> **Actualización 2026-05-10**: `zassenhaus_bijection` completamente demostrado (tipo completo, 0 sorry).
> `zassenhaus_bijection_symm` demostrado (one-liner).
> **Actualización 2026-05-10 (sesión 2)**: `zassenhaus_bijection_extremes` demostrado — 0 sorry.
> Técnica: lema puente `mapOn_bijective_cast` (privado) permite `subst` sobre variable libre,
> evitando el bloqueo de eliminación dependiente sobre términos concretos de tipo `FSet (FSet ℕ₀)`.

---

## Módulo: `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`

- **Namespace:** `Peano.GroupTheory`
- **Import:** `Peano.PeanoNat.Combinatorics.GroupTheory.SecondIsomorphism`
- **Opens:** `Peano.FSet`, `Peano.FSetFunction`, `Peano.Group`, `Peano.Mul`
- **Tema:** Lema de la Mariposa de Zassenhaus (lemas preparatorios y normalidad)

---

## §1. Subgrupo producto `N · S`

### `prodSubgroup`

- **Tipo:** `def` (computable)
- **Notación matemática:** $N \cdot S = \{n \cdot s \mid n \in N,\; s \in S\}$ como subgrupo de $G$,  
  válido cuando $N, S \leq H \leq G$ y $N \trianglelefteq H$.
- **Firma Lean 4:**

  ```lean
  def prodSubgroup
      (G : FinGroup ℕ₀) (N S H : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems) :
      Subgroup G
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

### `mem_prodSubgroup_iff`

- **Tipo:** `theorem`
- **Notación matemática:** $x \in N \cdot S \iff x \in G \;\land\; \exists n \in N,\; \exists s \in S,\; n \cdot s = x$
- **Firma Lean 4:**

  ```lean
  theorem mem_prodSubgroup_iff
      (G : FinGroup ℕ₀) (N S H : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (x : ℕ₀) :
      x ∈ (prodSubgroup G N S H hNH hSH hNN).carrier.elems ↔
      x ∈ G.carrier.elems ∧
      ∃ n ∈ N.carrier.elems, ∃ s ∈ S.carrier.elems, G.op n s = x
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`

---

### `N_le_prodSubgroup`

- **Tipo:** `theorem`
- **Notación matemática:** $N \leq N \cdot S$ (inclusión del primer factor).  
  $n \in N \Rightarrow n \in N \cdot S$.
- **Firma Lean 4:**

  ```lean
  theorem N_le_prodSubgroup
      (G : FinGroup ℕ₀) (N S H : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (n : ℕ₀) (hn : n ∈ N.carrier.elems) :
      n ∈ (prodSubgroup G N S H hNH hSH hNN).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`

---

### `S_le_prodSubgroup`

- **Tipo:** `theorem`
- **Notación matemática:** $S \leq N \cdot S$ (inclusión del segundo factor).  
  $s \in S \Rightarrow s \in N \cdot S$.
- **Firma Lean 4:**

  ```lean
  theorem S_le_prodSubgroup
      (G : FinGroup ℕ₀) (N S H : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hSH : ∀ a, a ∈ S.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (s : ℕ₀) (hs : s ∈ S.carrier.elems) :
      s ∈ (prodSubgroup G N S H hNH hSH hNN).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`

---

## §2. $N \cap K \trianglelefteq H \cap K$

### `inter_N_K_normal_in_inter_H_K`

- **Tipo:** `theorem`
- **Notación matemática:** Si $N \trianglelefteq H$ y $K \leq G$, entonces $N \cap K \trianglelefteq H \cap K$.  
  Formalmente: $\forall g \in H \cap K,\; \forall x \in N \cap K,\quad g x g^{-1} \in N \cap K$.
- **Firma Lean 4:**

  ```lean
  theorem inter_N_K_normal_in_inter_H_K
      (G : FinGroup ℕ₀) (H K N : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems) :
      ∀ g x,
        g ∈ (H.inter K).carrier.elems →
        x ∈ (N.inter K).carrier.elems →
        G.op (G.op g x) (G.inv g) ∈ (N.inter K).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

## §3. $H \cap M \trianglelefteq H \cap K$

### `inter_H_M_normal_in_inter_H_K`

- **Tipo:** `theorem`
- **Notación matemática:** Si $M \trianglelefteq K$ y $H \leq G$, entonces $H \cap M \trianglelefteq H \cap K$.  
  Formalmente: $\forall g \in H \cap K,\; \forall x \in H \cap M,\quad g x g^{-1} \in H \cap M$.
- **Firma Lean 4:**

  ```lean
  theorem inter_H_M_normal_in_inter_H_K
      (G : FinGroup ℕ₀) (H K M : Subgroup G)
      (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
             G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
      ∀ g x,
        g ∈ (H.inter K).carrier.elems →
        x ∈ (H.inter M).carrier.elems →
        G.op (G.op g x) (G.inv g) ∈ (H.inter M).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

## §4. $(N \cap K)(H \cap M) \trianglelefteq H \cap K$

### `prodNKHM`

- **Tipo:** `def` (computable)
- **Notación matemática:** El subgrupo $(N \cap K)(H \cap M) \leq H \cap K$,  
  definido como `prodSubgroup G (N∩K) (H∩M) (H∩K) …`, dado $N \trianglelefteq H$ y $M \trianglelefteq K$.
- **Firma Lean 4:**

  ```lean
  def prodNKHM
      (G : FinGroup ℕ₀) (H K N M : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
             G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
      Subgroup G
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

### `prodNKHM_normal`

- **Tipo:** `theorem`
- **Notación matemática:** $(N \cap K)(H \cap M) \trianglelefteq H \cap K$.  
  $\forall g \in H \cap K,\; \forall x \in (N \cap K)(H \cap M),\quad g x g^{-1} \in (N \cap K)(H \cap M)$.
- **Firma Lean 4:**

  ```lean
  theorem prodNKHM_normal
      (G : FinGroup ℕ₀) (H K N M : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
             G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
      ∀ g x,
        g ∈ (H.inter K).carrier.elems →
        x ∈ (prodNKHM G H K N M hNH hMK hNN hMM).carrier.elems →
        G.op (G.op g x) (G.inv g) ∈ (prodNKHM G H K N M hNH hMK hNN hMM).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

## §5. Subgrupos producto $N(H \cap K)$ y $N(H \cap M)$

### `prodN_HK`

- **Tipo:** `def` (computable)
- **Notación matemática:** $N(H \cap K)$ = subgrupo producto de $N$ con $H \cap K$,  
  dado $N \leq H$ y $N \trianglelefteq H$.
- **Firma Lean 4:**

  ```lean
  def prodN_HK
      (G : FinGroup ℕ₀) (H K N : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems) :
      Subgroup G
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

### `prodN_HM`

- **Tipo:** `def` (computable)
- **Notación matemática:** $N(H \cap M)$ = subgrupo producto de $N$ con $H \cap M$,  
  dado $N \leq H$, $M \leq H$ y $N \trianglelefteq H$.
- **Firma Lean 4:**

  ```lean
  def prodN_HM
      (G : FinGroup ℕ₀) (H M N : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems) :
      Subgroup G
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

## §6. $N(H \cap M) \trianglelefteq N(H \cap K)$

### `prodN_HM_le_prodN_HK`

- **Tipo:** `theorem`
- **Notación matemática:** $N(H \cap M) \leq N(H \cap K)$, dado $M \leq K$.  
  $x \in N(H \cap M) \Rightarrow x \in N(H \cap K)$.
- **Firma Lean 4:**

  ```lean
  theorem prodN_HM_le_prodN_HK
      (G : FinGroup ℕ₀) (H K M N : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (x : ℕ₀) :
      x ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems →
      x ∈ (prodN_HK G H K N hNH hNN).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`

---

### `prodN_HM_normal_in_prodN_HK`

- **Tipo:** `theorem`
- **Notación matemática:** $N(H \cap M) \trianglelefteq N(H \cap K)$,  
  dado $N \trianglelefteq H$ y $M \trianglelefteq K$.  
  $\forall g \in N(H \cap K),\; \forall y \in N(H \cap M),\quad g y g^{-1} \in N(H \cap M)$.
- **Estrategia de prueba:**
  Escribir $g = n_g k_g$ con $n_g \in N$, $k_g \in H \cap K$; y $y = n_y m_y$ con $n_y \in N$, $m_y \in H \cap M$.  
  Definir $m_y' = k_g m_y k_g^{-1} \in H \cap M$ (por $M \trianglelefteq K$, $k_g \in K$).  
  Definir $\alpha = m_y' n_g^{-1} m_y'^{-1} \in N$ (conjugado de $n_g^{-1}$ por $m_y' \in H$).  
  Entonces $n_{\mathrm{pair}} = n_g \cdot (k_g n_y k_g^{-1}) \cdot \alpha \in N$,  
  y la identidad $n_{\mathrm{pair}} \cdot m_y' = g y g^{-1}$ da la membresía en $N(H \cap M)$.
- **Firma Lean 4:**

  ```lean
  theorem prodN_HM_normal_in_prodN_HK
      (G : FinGroup ℕ₀) (H K M N : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : ∀ g n, g ∈ H.carrier.elems → n ∈ N.carrier.elems →
             G.op (G.op g n) (G.inv g) ∈ N.carrier.elems)
      (hMM : ∀ g m, g ∈ K.carrier.elems → m ∈ M.carrier.elems →
             G.op (G.op g m) (G.inv g) ∈ M.carrier.elems) :
      ∀ g y,
        g ∈ (prodN_HK G H K N hNH hNN).carrier.elems →
        y ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems →
        G.op (G.op g y) (G.inv g) ∈ (prodN_HM G H M N hNH hMH hNN).carrier.elems
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

## Resumen de símbolos del módulo

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `prodSubgroup` | `def` | ✅ | alta |
| `mem_prodSubgroup_iff` | `theorem` | — | media |
| `N_le_prodSubgroup` | `theorem` | — | media |
| `S_le_prodSubgroup` | `theorem` | — | media |
| `inter_N_K_normal_in_inter_H_K` | `theorem` | — | alta |
| `inter_H_M_normal_in_inter_H_K` | `theorem` | — | alta |
| `prodNKHM` | `def` | ✅ | alta |
| `prodNKHM_normal` | `theorem` | — | alta |
| `prodN_HK` | `def` | ✅ | alta |
| `prodN_HM` | `def` | ✅ | alta |
| `prodN_HM_le_prodN_HK` | `theorem` | — | media |
| `prodN_HM_normal_in_prodN_HK` | `theorem` | — | alta |
| `zassenhaus_bijection` | `theorem` | — | alta |
| `zassenhaus_bijection_symm` | `theorem` | — | alta |
| `zassenhaus_bijection_extremes` | `theorem` (0 sorry) | — | alta |

> **No proyectados** (privados): `mem_inter_iff`, `inter_subset_left_aux`, `inter_subset_right_aux`,
> `NormalIn`, `HK`, `NK`, `HM`, `N_normal_in_prodN_HK`, `prodNKHM_in_HK`, `prodN_HM_in_prodN_HK`,
> `mapOn_bijective_cast` (lema puente para transporte de biyectividad, ver §7),
> `inter_comm_lem`, `prodNKHM_carrier_eq`, `quotientCarrier_inter_eq`.

---

## §7. Lema de la Mariposa de Zassenhaus — biyecciones

### `zassenhaus_bijection`

- **Tipo:** `theorem` (0 sorry)
- **Notación matemática:** Existe una biyección
  $$(H \cap K) / [(N \cap K)(H \cap M)] \;\xrightarrow{\sim}\; N(H \cap K) / N(H \cap M)$$
  dado $N \trianglelefteq H$ y $M \trianglelefteq K$.
- **Firma Lean 4:**

  ```lean
  theorem zassenhaus_bijection
      (G : FinGroup ℕ₀) (H K N M : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : NormalIn G N H)
      (hMM : NormalIn G M K) :
      ∃ (f : MapOn
          (quotientCarrier (Subgroup.toFinGroup (H.inter K))
                           (prodNKHM_in_HK G H K N M hNH hMK hNN hMM))
          (quotientCarrier (Subgroup.toFinGroup (prodN_HK G H K N hNH hNN))
                           (prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN))),
        f.Bijective
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

### `zassenhaus_bijection_symm`

- **Tipo:** `theorem` (0 sorry)
- **Notación matemática:** Intercambiando los roles $(H, N) \leftrightarrow (K, M)$, existe una biyección
  $$(K \cap H) / [(M \cap H)(K \cap N)] \;\xrightarrow{\sim}\; M(K \cap H) / M(K \cap N)$$
  dado $N \trianglelefteq H$, $M \trianglelefteq K$ y la hipótesis extra $N \leq K$.
- **Prueba:** Aplicación directa de `zassenhaus_bijection G K H M N hMK hNK hNH hMM hNN`.
- **Firma Lean 4:**

  ```lean
  theorem zassenhaus_bijection_symm
      (G : FinGroup ℕ₀) (H K N M : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hNK : ∀ a, a ∈ N.carrier.elems → a ∈ K.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : NormalIn G N H)
      (hMM : NormalIn G M K) :
      ∃ (f : MapOn
          (quotientCarrier (Subgroup.toFinGroup (K.inter H))
                           (prodNKHM_in_HK G K H M N hMK hNH hMM hNN))
          (quotientCarrier (Subgroup.toFinGroup (prodN_HK G K H M hMK hMM))
                           (prodN_HM_in_prodN_HK G K H N M hMK hNK hNH hMM))),
        f.Bijective
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

### `zassenhaus_bijection_extremes`

- **Tipo:** `theorem` (0 sorry)
- **Notación matemática:** Existe una biyección
  $$N(H \cap K) / N(H \cap M) \;\xrightarrow{\sim}\; M(K \cap H) / M(K \cap N)$$
  dado $N \trianglelefteq H$, $M \trianglelefteq K$, $N \leq K$, $M \leq H$.
- **Estrategia de prueba:**
  1. `f₁` = biyección de `zassenhaus_bijection` con dominio $(H\cap K)/[(N\cap K)(H\cap M)]$.
  2. `f₁_inv` = `MapOn.inverse f₁ hf₁ dflt` — inversa de `f₁` con codominio $(H\cap K)/[\ldots]$.
  3. `hquo_eq` = `quotientCarrier_inter_eq` — igualdad $(H\cap K)/[\ldots] = (K\cap H)/[\ldots]$.
  4. Lema puente `mapOn_bijective_cast` (privado): transporta `f₁_inv.Bijective` a través de `hquo_eq`
     usando `subst heq` (posible porque la variable `B : FSet β` es libre en el enunciado general,
     aunque en el sitio de uso sea un término concreto `FSet (FSet ℕ₀)`).
  5. `f₂` = biyección de `zassenhaus_bijection_symm`; dominio = codominio de `hquo_eq ▸ f₁_inv`.
  6. Resultado: `f₂.comp (hquo_eq ▸ f₁_inv)` con `MapOn.comp_bijective`.
- **Firma Lean 4:**

  ```lean
  theorem zassenhaus_bijection_extremes
      (G : FinGroup ℕ₀) (H K N M : Subgroup G)
      (hNH : ∀ a, a ∈ N.carrier.elems → a ∈ H.carrier.elems)
      (hMH : ∀ a, a ∈ M.carrier.elems → a ∈ H.carrier.elems)
      (hNK : ∀ a, a ∈ N.carrier.elems → a ∈ K.carrier.elems)
      (hMK : ∀ a, a ∈ M.carrier.elems → a ∈ K.carrier.elems)
      (hNN : NormalIn G N H)
      (hMM : NormalIn G M K) :
      ∃ (f : MapOn
          (quotientCarrier (Subgroup.toFinGroup (prodN_HK G H K N hNH hNN))
                           (prodN_HM_in_prodN_HK G H K M N hNH hMH hMK hNN))
          (quotientCarrier (Subgroup.toFinGroup (prodN_HK G K H M hMK hMM))
                           (prodN_HM_in_prodN_HK G K H N M hMK hNK hNH hMM))),
        f.Bijective
  ```

- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Zassenhaus.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`

---

# Módulo: `NormalSubgroup.lean`

> **Archivo**: `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
> **Namespace**: `Peano.GroupTheory`
> *(Sin bloque `export`; símbolos identificados por inspección directa.)*

## §7. Centralizador, Centro y Normalizador

### `centralizer`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def centralizer (G : FinGroup ℕ₀) (H : Subgroup G) : Subgroup G
  ```

- **Notación matemática:** $C_G(H) = \{ g \in G \mid \forall h \in H,\ g \cdot h = h \cdot g \}$.
- **Dependencias directas:** `Group.lean` (Subgroup, FinGroup)

---

### `mem_centralizer_iff`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem mem_centralizer_iff (G : FinGroup ℕ₀) (H : Subgroup G) (g : ℕ₀) :
      g ∈ (centralizer G H).carrier.elems ↔
        g ∈ G.carrier.elems ∧ ∀ h, h ∈ H.carrier.elems → G.op g h = G.op h g
  ```

- **Notación matemática:** $g \in C_G(H) \iff g \in G \land \forall h \in H,\ gh = hg$.

---

### `center`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def center (G : FinGroup ℕ₀) : Subgroup G :=
    centralizer G (improperSubgroup G)
  ```

- **Notación matemática:** $Z(G) = C_G(G)$, el centro de $G$.

---

### `mem_center_iff`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem mem_center_iff (G : FinGroup ℕ₀) (g : ℕ₀) :
      g ∈ (center G).carrier.elems ↔
        g ∈ G.carrier.elems ∧ ∀ x, x ∈ G.carrier.elems → G.op g x = G.op x g
  ```

- **Notación matemática:** $g \in Z(G) \iff g \in G \land \forall x \in G,\ gx = xg$.

---

### `center_isNormal`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem center_isNormal (G : FinGroup ℕ₀) : (center G).IsNormal
  ```

- **Notación matemática:** $Z(G) \trianglelefteq G$.

---

### `central_subgroup_isNormal`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem central_subgroup_isNormal (G : FinGroup ℕ₀) (H : Subgroup G)
      (h_central : ∀ h, h ∈ H.carrier.elems → h ∈ (center G).carrier.elems) :
      H.IsNormal
  ```

- **Notación matemática:** $H \subseteq Z(G) \Rightarrow H \trianglelefteq G$.

---

### `normalizer`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def normalizer (G : FinGroup ℕ₀) (H : Subgroup G) : Subgroup G
  ```

- **Notación matemática:** $N_G(H) = \{ g \in G \mid gHg^{-1} \subseteq H \land g^{-1}Hg \subseteq H \}$.

---

### `mem_normalizer_iff`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem mem_normalizer_iff (G : FinGroup ℕ₀) (H : Subgroup G) (g : ℕ₀) :
      g ∈ (normalizer G H).carrier.elems ↔
        g ∈ G.carrier.elems ∧
        (∀ h, h ∈ H.carrier.elems → G.op (G.op g h) (G.inv g) ∈ H.carrier.elems) ∧
        (∀ h, h ∈ H.carrier.elems → G.op (G.op (G.inv g) h) g ∈ H.carrier.elems)
  ```

- **Notación matemática:** $g \in N_G(H) \iff g \in G \land gHg^{-1} \subseteq H \land g^{-1}Hg \subseteq H$.

---

### `H_subset_normalizer`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem H_subset_normalizer (G : FinGroup ℕ₀) (H : Subgroup G) :
      ∀ h, h ∈ H.carrier.elems → h ∈ (normalizer G H).carrier.elems
  ```

- **Notación matemática:** $H \subseteq N_G(H)$.

---

### `isNormal_iff_normalizer_eq_G`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/NormalSubgroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem isNormal_iff_normalizer_eq_G (G : FinGroup ℕ₀) (H : Subgroup G) :
      H.IsNormal ↔ (normalizer G H).carrier = G.carrier
  ```

- **Notación matemática:** $H \trianglelefteq G \iff N_G(H) = G$.

---

## Resumen de símbolos — `NormalSubgroup.lean`

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `centralizer` | `def` | ✅ | alta |
| `mem_centralizer_iff` | `theorem` | — | media |
| `center` | `def` | ✅ | alta |
| `mem_center_iff` | `theorem` | — | media |
| `center_isNormal` | `theorem` | — | alta |
| `central_subgroup_isNormal` | `theorem` | — | media |
| `normalizer` | `def` | ✅ | alta |
| `mem_normalizer_iff` | `theorem` | — | media |
| `H_subset_normalizer` | `theorem` | — | media |
| `isNormal_iff_normalizer_eq_G` | `theorem` | — | alta |

---

# Módulo: `Sylow/Cosets.lean`

> **Archivo**: `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
> **Namespace**: `Peano.GroupTheory`

## §8. Cosetos y Lema de Lagrange

### `leftCoset`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def leftCoset {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      (G : FinGroup α) (H : Subgroup G) (g : α) : FSet α
  ```

- **Notación matemática:** $gH = \{ g \cdot h \mid h \in H \}$.

---

### `mem_leftCoset_iff`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem mem_leftCoset_iff {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      (G : FinGroup α) (H : Subgroup G) (g x : α)
      (hg : g ∈ G.carrier.elems) :
      x ∈ (leftCoset G H g).elems ↔ ∃ h, h ∈ H.carrier.elems ∧ G.op g h = x
  ```

- **Notación matemática:** $x \in gH \iff \exists h \in H,\ g \cdot h = x$.

---

### `coset_card_eq_subgroup_card`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem coset_card_eq_subgroup_card {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      (G : FinGroup α) (H : Subgroup G) (g : α)
      (hg : g ∈ G.carrier.elems) :
      (leftCoset G H g).card = H.carrier.card
  ```

- **Notación matemática:** $|gH| = |H|$ para todo $g \in G$.

---

### `cosetRel`

- **Tipo:** `def` (proposición decidible)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def cosetRel {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      (G : FinGroup α) (H : Subgroup G) (a b : α) : Prop :=
    G.op (G.inv a) b ∈ H.carrier.elems
  ```

- **Notación matemática:** $a \sim_H b \iff a^{-1}b \in H$.

---

### `cosetRel_refl` / `cosetRel_symm` / `cosetRel_trans`

- **Tipo:** `theorem` (×3)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Notación matemática:** Reflexividad, simetría y transitividad de $\sim_H$ sobre $G$.

---

### `cosetEquivRel`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def cosetEquivRel {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      (G : FinGroup α) (H : Subgroup G) : EquivRelOn G.carrier
  ```

- **Notación matemática:** Relación de equivalencia sobre $G$ inducida por $\sim_H$.

---

### `classOf_cosetEquivRel_eq_leftCoset`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem classOf_cosetEquivRel_eq_leftCoset
      {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      (G : FinGroup α) (H : Subgroup G) (g : α)
      (hg : g ∈ G.carrier.elems) :
      (cosetEquivRel G H).classOf g = leftCoset G H g
  ```

- **Notación matemática:** La clase de equivalencia de $g$ por $\sim_H$ coincide con $gH$.

---

### `cosetClasses`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def cosetClasses {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      (G : FinGroup α) (H : Subgroup G) : List (FSet α) :=
    (cosetEquivRel G H).classes
  ```

- **Notación matemática:** Lista de todos los cosetos izquierdos distintos de $G$ módulo $H$.

---

### `lagrange`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Cosets.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem lagrange {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      (G : FinGroup α) (H : Subgroup G) :
      ∃ k : ℕ₀, mul H.carrier.card k = G.carrier.card
  ```

- **Notación matemática:** **Lema de Lagrange**: $|H| \cdot [G:H] = |G|$, en particular $|H| \mid |G|$.
- **Dependencias directas:** `FSetFunction`, `EquivRel`, `cosetClasses`, `coset_card_eq_subgroup_card`

---

## Resumen de símbolos — `Sylow/Cosets.lean`

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `leftCoset` | `def` | ✅ | alta |
| `mem_leftCoset_iff` | `theorem` | — | alta |
| `coset_card_eq_subgroup_card` | `theorem` | — | alta |
| `cosetRel` | `def` | ✅ | alta |
| `cosetRel_refl` | `theorem` | — | media |
| `cosetRel_symm` | `theorem` | — | media |
| `cosetRel_trans` | `theorem` | — | media |
| `cosetEquivRel` | `def` | ✅ | alta |
| `mem_classOf_cosetEquivRel_iff_leftCoset` | `theorem` | — | media |
| `classOf_cosetEquivRel_eq_leftCoset` | `theorem` | — | alta |
| `classOf_cosetEquivRel_card_eq_subgroup_card` | `theorem` | — | media |
| `cosetClassFamily` | `def` | ✅ | media |
| `cosetClasses` | `def` | ✅ | alta |
| `card_eq_subgroup_card_of_mem_cosetClasses` | `theorem` | — | media |
| `mem_some_cosetClasses` | `theorem` | — | media |
| `cosetClass_eq_classOf_of_mem` | `theorem` | — | media |
| `leftCoset_subset_of_rel` | `theorem` | — | media |
| `leftCoset_eq_of_rel` | `theorem` | — | media |
| `mem_some_cosetClassFamily_class` | `theorem` | — | media |
| `lagrange` | `theorem` | — | alta |

---

# Módulo: `QuotientGroup.lean`

> **Archivo**: `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean`
> **Namespace**: `Peano.GroupTheory`

## §9. Grupo Cociente G/H

### `quotientCarrier`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def quotientCarrier (G : FinGroup ℕ₀) (H : Subgroup G) : Nat0FSetFSet
  ```

- **Notación matemática:** Portador de $G/H$: conjunto ordenado de cosetos $\{gH \mid g \in G\}$.

---

### `mem_quotientCarrier_iff`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem mem_quotientCarrier_iff (G : FinGroup ℕ₀) (H : Subgroup G) (C : ℕ₀FSet) :
      C ∈ (quotientCarrier G H).elems ↔ C ∈ cosetClasses G H
  ```

---

### `cosetRepOf`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def cosetRepOf (G : FinGroup ℕ₀) (H : Subgroup G)
      (C : ℕ₀FSet) (hC : C ∈ (quotientCarrier G H).elems) : ℕ₀
  ```

- **Notación matemática:** Representante canónico de un coseto $C \in G/H$ (la cabeza de la lista ordenada).

---

### `quotientOp`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def quotientOp (G : FinGroup ℕ₀) (H : Subgroup G)
      (hn : H.IsNormal) (A B : ℕ₀FSet) : ℕ₀FSet
  ```

- **Notación matemática:** Operación binaria del cociente: $(aH) \cdot (bH) = (ab)H$.

---

### `quotientGroup`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def quotientGroup (G : FinGroup ℕ₀) (H : Subgroup G)
      (hn : H.IsNormal) : FinGroup ℕ₀FSet
  ```

- **Notación matemática:** $G/H$ como grupo finito, dado $H \trianglelefteq G$.

---

### `quotient_card`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem quotient_card (G : FinGroup ℕ₀) (H : Subgroup G) (hn : H.IsNormal) :
      (quotientGroup G H hn).carrier.card = div G.carrier.card H.carrier.card
  ```

- **Notación matemática:** $|G/H| = |G| / |H|$.

---

### `quotientHomomorphism`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def quotientHomomorphism (G : FinGroup ℕ₀) (H : Subgroup G)
      (hn : H.IsNormal) : GroupHom G (quotientGroup G H hn)
  ```

- **Notación matemática:** $\pi : G \twoheadrightarrow G/H$, homomorfismo canónico de proyección.

---

### `quotientHomomorphism_kernel`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Notación matemática:** $\ker(\pi) = H$.

---

### `imageSubgroup`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/QuotientGroup.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def imageSubgroup (G H : FinGroup ℕ₀) (φ : GroupHom G H) : Subgroup H
  ```

- **Notación matemática:** $\operatorname{Im}(\varphi) = \{ \varphi(g) \mid g \in G \}$ como subgrupo de $H$.

---

## Resumen de símbolos — `QuotientGroup.lean`

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `quotientCarrier` | `def` | ✅ | alta |
| `mem_quotientCarrier_iff` | `theorem` | — | media |
| `mem_quotientCarrier_is_leftCoset` | `theorem` | — | media |
| `coset_nonempty_of_mem_quotientCarrier` | `theorem` | — | baja |
| `leftCoset_mem_cosetClasses` | `theorem` | — | media |
| `leftCoset_mem_quotientCarrier` | `theorem` | — | media |
| `leftCoset_id_mem_quotientCarrier` | `theorem` | — | baja |
| `cosetRel_of_leftCoset_eq` | `theorem` | — | media |
| `leftCoset_eq_iff_cosetRel` | `theorem` | — | media |
| `cosetRepOf` | `def` | ✅ | alta |
| `cosetRepOf_eq_head` | `theorem` | — | media |
| `cosetRepOf_mem_C` | `theorem` | — | media |
| `cosetRepOf_mem_G` | `theorem` | — | media |
| `cosetRepOf_leftCoset_eq` | `theorem` | — | media |
| `quotientOp_welldefined` | `theorem` | — | alta |
| `quotientOp` | `def` | ✅ | alta |
| `quotientInv` | `def` | ✅ | alta |
| `quotientId` | `def` | ✅ | alta |
| `quotientId_mem` | `theorem` | — | media |
| `quotientOp_assoc` | `theorem` | — | alta |
| `quotientOp_id` | `theorem` | — | alta |
| `quotientOp_inv` | `theorem` | — | alta |
| `quotientGroup` | `def` | ✅ | alta |
| `quotient_card` | `theorem` | — | alta |
| `quotientHomomorphism` | `def` | ✅ | alta |
| `quotientHomomorphism_op` | `theorem` | — | alta |
| `quotientHomomorphism_kernel` | `theorem` | — | alta |
| `imageSubgroup` | `def` | ✅ | alta |

---

# Módulo: `FirstIsomorphism.lean`

> **Archivo**: `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean`
> **Namespace**: `Peano.GroupTheory`

## §10. Primer Teorema de Isomorfismo

$G/\ker(\varphi) \cong \operatorname{Im}(\varphi)$.

### `Subgroup.toFinGroup`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def Subgroup.toFinGroup (G : FinGroup ℕ₀) (H : Subgroup G) : FinGroup ℕ₀
  ```

- **Notación matemática:** Todo subgrupo $H \leq G$ es un grupo finito por sí mismo.

---

### `homKer`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def homKer (G H : FinGroup ℕ₀) (φ : GroupHom G H) : Subgroup G
  ```

- **Notación matemática:** $\ker(\varphi) = \{ g \in G \mid \varphi(g) = e_H \}$.

---

### `mem_homKer_iff`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem mem_homKer_iff (G H : FinGroup ℕ₀) (φ : GroupHom G H) (g : ℕ₀) :
      g ∈ (homKer G H φ).carrier.elems ↔
        g ∈ G.carrier.elems ∧ φ.map g = H.id
  ```

- **Notación matemática:** $g \in \ker(\varphi) \iff g \in G \land \varphi(g) = e_H$.

---

### `homImg`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def homImg (G H : FinGroup ℕ₀) (φ : GroupHom G H) : Subgroup H
  ```

- **Notación matemática:** $\operatorname{Im}(\varphi) = \{ \varphi(g) \mid g \in G \}$ como subgrupo de $H$.

---

### `homKer_isNormal`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem homKer_isNormal (G H : FinGroup ℕ₀) (φ : GroupHom G H) :
      (homKer G H φ).IsNormal
  ```

- **Notación matemática:** $\ker(\varphi) \trianglelefteq G$.

---

### `quotientHomomorphism_surjective`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Notación matemática:** $\pi : G \twoheadrightarrow G/H$ es sobreyectivo.

---

### `homImgInclusion`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Notación matemática:** Inclusión canónica $\iota : \operatorname{Im}(\varphi) \hookrightarrow H$.

---

### `firstIsoMap`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def firstIsoMap (G H : FinGroup ℕ₀) (φ : GroupHom G H) :
      ℕ₀FSet → ℕ₀
  ```

- **Notación matemática:** $\bar{\varphi} : G/\ker(\varphi) \to \operatorname{Im}(\varphi)$, definida por $\bar{\varphi}(g\ker\varphi) = \varphi(g)$.

---

### `firstIsoMap_bijective`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/FirstIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Notación matemática:** **Primer Teorema de Isomorfismo**: $G/\ker(\varphi) \cong \operatorname{Im}(\varphi)$.

---

## Resumen de símbolos — `FirstIsomorphism.lean`

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `Subgroup.toFinGroup` | `def` | ✅ | alta |
| `homKer` | `def` | ✅ | alta |
| `mem_homKer_iff` | `theorem` | — | media |
| `homImg` | `def` | ✅ | alta |
| `mem_homImg_iff` | `theorem` | — | media |
| `homKer_isNormal` | `theorem` | — | alta |
| `quotientHomomorphism_surjective` | `theorem` | — | alta |
| `homImgInclusion` | `def` | ✅ | alta |
| `homImgInclusion_injective` | `theorem` | — | alta |
| `firstIsoMap` | `def` | ✅ | alta |
| `firstIsoMap_welldefined` | `theorem` | — | alta |
| `firstIsoMap_op` | `theorem` | — | alta |
| `firstIsoMap_injective` | `theorem` | — | alta |
| `firstIsoMap_surjective` | `theorem` | — | alta |
| `firstIsoMap_bijective` | `theorem` | — | alta |

---

# Módulo: `SecondIsomorphism.lean`

> **Archivo**: `Peano/PeanoNat/Combinatorics/GroupTheory/SecondIsomorphism.lean`
> **Namespace**: `Peano.GroupTheory`

## §11. Segundo Teorema de Isomorfismo

$(H \cap N) \trianglelefteq H$ y $H/(H \cap N) \cong HN/N$.

### `subgroupHN`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/SecondIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def subgroupHN (G : FinGroup ℕ₀) (H N : Subgroup G)
      (hNN : N.IsNormal) : Subgroup G
  ```

- **Notación matemática:** $HN = \{ hn \mid h \in H,\ n \in N \}$ como subgrupo de $G$.

---

### `N_normal_in_subgroupHN`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/SecondIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Notación matemática:** $N \trianglelefteq HN$.

---

### `interHN_as_subgroup_H_isNormal`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/SecondIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Notación matemática:** $H \cap N \trianglelefteq H$.

---

### `secondIsoMap_bijective`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/SecondIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Notación matemática:** **Segundo Teorema de Isomorfismo**: $H/(H \cap N) \cong HN/N$.

---

## Resumen de símbolos — `SecondIsomorphism.lean`

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `subgroupHN` | `def` | ✅ | alta |
| `mem_subgroupHN_iff` | `theorem` | — | media |
| `H_le_subgroupHN` | `theorem` | — | media |
| `N_le_subgroupHN` | `theorem` | — | media |
| `N_in_subgroupHN` | `theorem` | — | media |
| `N_normal_in_subgroupHN` | `theorem` | — | alta |
| `interHN_as_subgroup_H` | `def` | ✅ | alta |
| `interHN_as_subgroup_H_isNormal` | `theorem` | — | alta |
| `secondIsoMap` | `def` | ✅ | alta |
| `secondIsoMap_welldefined` | `theorem` | — | alta |
| `secondIsoMap_injective` | `theorem` | — | alta |
| `secondIsoMap_surjective` | `theorem` | — | alta |
| `secondIsoMap_bijective` | `theorem` | — | alta |

---

# Módulo: `ThirdIsomorphism.lean`

> **Archivo**: `Peano/PeanoNat/Combinatorics/GroupTheory/ThirdIsomorphism.lean`
> **Namespace**: `Peano.GroupTheory`

## §12. Tercer Teorema de Isomorfismo

Dados $N \trianglelefteq K \trianglelefteq G$, se tiene $(G/N)/(K/N) \cong G/K$.

### `cosetRel_N_imp_K`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/ThirdIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Notación matemática:** $a \sim_N b \Rightarrow a \sim_K b$ cuando $N \leq K$.

---

### `KmodN_normal`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/ThirdIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Notación matemática:** $K/N \trianglelefteq G/N$ cuando $N \trianglelefteq K \trianglelefteq G$.

---

### `thirdIsoMap`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/ThirdIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Notación matemática:** $\theta : G/N \to G/K$, definida por $gN \mapsto gK$.

---

### `thirdIsoGroupHom`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/ThirdIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Notación matemática:** El isomorfismo $\theta$ como homomorfismo de grupos finitos.

---

### `thirdIsoMap_kernel`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/ThirdIsomorphism.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Notación matemática:** $\ker(\theta) = K/N$, lo que implica $(G/N)/(K/N) \cong G/K$.

---

## Resumen de símbolos — `ThirdIsomorphism.lean`

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `cosetRel_N_imp_K` | `theorem` | — | media |
| `KmodN_normal` | `theorem` | — | alta |
| `thirdIsoMap` | `def` | ✅ | alta |
| `thirdIsoMap_welldefined` | `theorem` | — | alta |
| `thirdIsoMap_op` | `theorem` | — | alta |
| `thirdIsoMap_id` | `theorem` | — | media |
| `thirdIsoMap_inv` | `theorem` | — | media |
| `thirdIsoGroupHom` | `def` | ✅ | alta |
| `thirdIsoMap_surjective` | `theorem` | — | alta |
| `thirdIsoMap_kernel` | `theorem` | — | alta |

---

# Módulo: `CorrespondenceTheorem.lean`

> **Archivo**: `Peano/PeanoNat/Combinatorics/GroupTheory/CorrespondenceTheorem.lean`
> **Namespace**: `Peano.GroupTheory`

## §13. Teorema de Correspondencia

Biyección entre subgrupos de $G/N$ y subgrupos de $G$ que contienen a $N$.

### `preimageSubgroup`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/CorrespondenceTheorem.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def preimageSubgroup (G : FinGroup ℕ₀) (N : Subgroup G) (hN : N.IsNormal)
      (K : Subgroup (quotientGroup G N hN)) : Subgroup G
  ```

- **Notación matemática:** $\Psi(\bar{K}) = \pi^{-1}(\bar{K}) = \{ g \in G \mid gN \in \bar{K} \}$.

---

### `SubgroupAbove`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/CorrespondenceTheorem.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Notación matemática:** Colección de subgrupos $H$ de $G$ con $N \leq H$.

---

### `correspondencePhi`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/CorrespondenceTheorem.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Notación matemática:** $\Phi(H) = H/N$ — manda subgrupos de $G$ con $N \leq H$ a subgrupos de $G/N$.

---

### `correspondencePsi`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/CorrespondenceTheorem.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Notación matemática:** $\Psi(\bar{K}) = \pi^{-1}(\bar{K})$ — manda subgrupos de $G/N$ a subgrupos de $G$ con $N \leq$.

---

### `correspondencePhi_psi` / `correspondencePsi_phi`

- **Tipo:** `theorem` (×2)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/CorrespondenceTheorem.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Notación matemática:** $\Phi \circ \Psi = \mathrm{id}$ y $\Psi \circ \Phi = \mathrm{id}$ — $\Phi$ y $\Psi$ son inversas biyectivas.

---

### `preimage_subgroup_card`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/CorrespondenceTheorem.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Notación matemática:** $|\Psi(\bar{K})| = |\bar{K}| \cdot |N|$.

---

## Resumen de símbolos — `CorrespondenceTheorem.lean`

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `preimageSubgroup` | `def` | ✅ | alta |
| `mem_preimageSubgroup_iff` | `theorem` | — | media |
| `N_le_preimageSubgroup` | `theorem` | — | media |
| `imageSubgroup_preimage` | `theorem` | — | media |
| `preimageSubgroup_image` | `theorem` | — | media |
| `SubgroupAbove` | `def` | ✅ | alta |
| `correspondencePhi` | `def` | ✅ | alta |
| `correspondencePsi` | `def` | ✅ | alta |
| `correspondencePhi_psi` | `theorem` | — | alta |
| `correspondencePsi_phi` | `theorem` | — | alta |
| `correspondenceInjective` | `theorem` | — | alta |
| `correspondenceSurjective` | `theorem` | — | alta |
| `preimage_subgroup_card` | `theorem` | — | media |

---

# Módulo: `Action.lean`

> **Archivo**: `Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean`
> **Namespace**: `Peano.GroupTheory`
> *(Sin bloque `export`; símbolos identificados por inspección directa.)*

## §14. Acciones de Grupo

### `GroupAction`

- **Tipo:** `structure`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  structure GroupAction
      {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
      (G : FinGroup α) (X : FSet β) where
    act        : α → β → β
    act_closed : ∀ g x, g ∈ G.carrier.elems → x ∈ X.elems → act g x ∈ X.elems
    act_id     : ∀ x, x ∈ X.elems → act G.id x = x
    act_compat : ∀ g h x,
                   g ∈ G.carrier.elems → h ∈ G.carrier.elems → x ∈ X.elems →
                   act (G.op g h) x = act g (act h x)
  ```

- **Notación matemática:** Acción de grupo $\psi : G \times X \to X$ con $\psi(e, x) = x$ y $\psi(gh, x) = \psi(g, \psi(h, x))$.

---

### `GroupAction.orb`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def GroupAction.orb
      {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
      {G : FinGroup α} {X : FSet β}
      (ψ : GroupAction G X) (x : β) : FSet β
  ```

- **Notación matemática:** $\mathrm{Orb}(x) = \{ \psi(g, x) \mid g \in G \}$.

---

### `mem_orb_iff`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem mem_orb_iff
      {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
      {G : FinGroup α} {X : FSet β}
      (ψ : GroupAction G X) (x y : β) (hx : x ∈ X.elems) :
      y ∈ (ψ.orb x).elems ↔ ∃ g, g ∈ G.carrier.elems ∧ ψ.act g x = y
  ```

- **Notación matemática:** $y \in \mathrm{Orb}(x) \iff \exists g \in G,\ \psi(g, x) = y$.

---

### `GroupAction.stab`

- **Tipo:** `def` (computable)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** ✅
- **Firma Lean 4:**

  ```lean
  def GroupAction.stab
      {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
      {G : FinGroup α} {X : FSet β}
      (ψ : GroupAction G X) (x : β) (hx : x ∈ X.elems) : Subgroup G
  ```

- **Notación matemática:** $\mathrm{Stab}(x) = \{ g \in G \mid \psi(g, x) = x \}$.

---

### `orbit_stabilizer`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem orbit_stabilizer
      {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
      {G : FinGroup α} {X : FSet β}
      (ψ : GroupAction G X) (x : β) (hx : x ∈ X.elems) :
      mul (ψ.orb x).card (ψ.stab x hx).carrier.card = G.carrier.card
  ```

- **Notación matemática:** $|\mathrm{Orb}(x)| \cdot |\mathrm{Stab}(x)| = |G|$.
- **Dependencias directas:** `Cosets.lean` (coset_card_eq_subgroup_card), `FSetFunction`

---

### `orbits_partition`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Action.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem orbits_partition
      {α : Type} [DecidableEq α] [LT α] [StrictLinearOrder α]
      {β : Type} [DecidableEq β] [LT β] [StrictLinearOrder β]
      {G : FinGroup α} {X : FSet β}
      (ψ : GroupAction G X) :
      (∀ x, x ∈ X.elems → ∃ y, y ∈ X.elems ∧ x ∈ (ψ.orb y).elems) ∧
      (∀ x y, x ∈ X.elems → y ∈ X.elems →
        (ψ.orb x).elems = (ψ.orb y).elems ∨
        ∀ z, z ∉ (ψ.orb x).elems ∨ z ∉ (ψ.orb y).elems)
  ```

- **Notación matemática:** $X$ se descompone en una partición de órbitas disjuntas.

---

## Resumen de símbolos — `Action.lean`

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `GroupAction` | `structure` | ✅ | alta |
| `GroupAction.orb` | `def` | ✅ | alta |
| `mem_orb_iff` | `theorem` | — | media |
| `GroupAction.stab` | `def` | ✅ | alta |
| `orbit_stabilizer` | `theorem` | — | alta |
| `orbits_partition` | `theorem` | — | alta |

---

# Módulo: `Sylow/CosetAction.lean`

> **Archivo**: `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/CosetAction.lean`
> **Namespace**: `Peano.GroupTheory`

## §15. Acción sobre Cosetos y Punto Fijo de p-grupos

### `coset_conjugate_exists`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/CosetAction.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem coset_conjugate_exists
      (G : FinGroup ℕ₀) (H K : Subgroup G) (p n k : ℕ₀)
      (hp     : Prime p)
      (hH_card : H.carrier.card = pow p n)
      (hK_card : K.carrier.card = pow p n)
      (hGK    : mul (pow p n) k = G.carrier.card)
      (hndvd  : ¬ p ∣ k) :
      ∃ r, r ∈ G.carrier.elems ∧
        ∀ h, h ∈ H.carrier.elems → G.op (G.inv r) (G.op h r) ∈ K.carrier.elems
  ```

- **Notación matemática:** Si $|H| = |K| = p^n$ y $p \nmid [G:K]$, existe $r \in G$ con $r^{-1}Hr \subseteq K$.
- **Nota:** Reemplaza el antiguo axioma privado `sylow_second_incl`. Usa el teorema de punto fijo de p-grupos.
- **Dependencias directas:** `Action.lean`, `Cosets.lean`, lema de Lagrange

---

## Resumen de símbolos — `Sylow/CosetAction.lean`

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `coset_conjugate_exists` | `theorem` | — | alta |

---

# Módulo: `Sylow/Sylow.lean`

> **Archivo**: `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
> **Namespace**: `Peano.GroupTheory`

## §16. Teoremas de Sylow

### `dvd_card`

- **Tipo:** `def` (Prop)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  def dvd_card (p : ℕ₀) (H : ℕ₀FSet) : Prop :=
    ∃ k : ℕ₀, Mul.mul p k = H.card
  ```

- **Notación matemática:** $p \mid |H|$.

---

### `pow_dvd_card`

- **Tipo:** `def` (Prop)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: medium`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  def pow_dvd_card (p k : ℕ₀) (H : ℕ₀FSet) : Prop :=
    ∃ m : ℕ₀, Mul.mul (p ^ k) m = H.card
  ```

- **Notación matemática:** $p^k \mid |H|$.

---

### `isPSubgroup`

- **Tipo:** `def` (Prop)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  def isPSubgroup (G : FinGroup ℕ₀) (H : Subgroup G) (p : ℕ₀) : Prop :=
    ∃ k : ℕ₀, H.carrier.card = p ^ k
  ```

- **Notación matemática:** $H$ es un $p$-subgrupo de $G$: $|H| = p^k$ para algún $k \in \mathbb{N}$.

---

### `isSylowExponent`

- **Tipo:** `def` (Prop)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  def isSylowExponent (G : FinGroup ℕ₀) (p n : ℕ₀) : Prop :=
    pow_dvd_card p n G.carrier ∧ ¬ pow_dvd_card p (σ n) G.carrier
  ```

- **Notación matemática:** $p^n \mid |G|$ pero $p^{n+1} \nmid |G|$ (máxima potencia de $p$ que divide $|G|$).

---

### `isSylowSubgroup`

- **Tipo:** `def` (Prop)
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  def isSylowSubgroup (G : FinGroup ℕ₀) (H : Subgroup G) (p : ℕ₀) : Prop :=
    ∃ n, isSylowExponent G p n ∧ H.carrier.card = p ^ n
  ```

- **Notación matemática:** $H$ es un subgrupo de Sylow $p$: $|H| = p^n$ con $p^n \| |G|$.

---

### `cauchy_minimal`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem cauchy_minimal (G : FinGroup ℕ₀) (p : ℕ₀)
      (hp : Prime p)
      (hdvd : ∃ t : ℕ₀, Mul.mul p t = G.carrier.card) :
      ∃ K : Subgroup G, K.carrier.card = p
  ```

- **Notación matemática:** **Teorema de Cauchy**: si $p$ primo divide $|G|$, entonces existe $K \leq G$ con $|K| = p$.

---

### `sylow_first`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem sylow_first (G : FinGroup ℕ₀) (p n : ℕ₀)
      (hp : Prime p)
      (hdvd : pow_dvd_card p n G.carrier) :
      ∃ H : Subgroup G, H.carrier.card = p ^ n
  ```

- **Notación matemática:** **Primer Teorema de Sylow**: si $p^n \mid |G|$, existe $H \leq G$ con $|H| = p^n$.
- **Dependencias directas:** `cauchy_minimal`, `sylow_lift_from_cauchy`

---

### `sylow_second`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem sylow_second (G : FinGroup ℕ₀) (p : ℕ₀)
      (hp : Prime p)
      (H K : Subgroup G)
      (hH : isSylowSubgroup G H p) (hK : isSylowSubgroup G K p) :
      ∃ g, g ∈ G.carrier.elems ∧
        ∀ x, x ∈ K.carrier.elems ↔
          ∃ h, h ∈ H.carrier.elems ∧ G.op (G.op g h) (G.inv g) = x
  ```

- **Notación matemática:** **Segundo Teorema de Sylow**: todos los subgrupos de Sylow $p$ son conjugados. $\exists g \in G,\ K = gHg^{-1}$.
- **Dependencias directas:** `coset_conjugate_exists` (CosetAction.lean)

---

### `sylow_third`

- **Tipo:** `theorem`
- **Módulo:** `Peano/PeanoNat/Combinatorics/GroupTheory/Sylow/Sylow.lean`
- **Namespace:** `Peano.GroupTheory`
- **Importancia:** `@importance: high`
- **Computable:** — (proposición)
- **Firma Lean 4:**

  ```lean
  theorem sylow_third (G : FinGroup ℕ₀) (p : ℕ₀)
      (hp : Prime p)
      (sylows : List (Subgroup G))
      (h_all_sylow : ∀ H ∈ sylows, isSylowSubgroup G H p)
      (h_all_included : ∀ H : Subgroup G, isSylowSubgroup G H p → H ∈ sylows)
      (h_nodup : sylows.Nodup) :
      (∃ k : ℕ₀, lengthₚ sylows = Peano.Add.add (Peano.Mul.mul p k) 𝟙) ∧
      (∀ H ∈ sylows, ∃ k : ℕ₀, Mul.mul (lengthₚ sylows) k = G.carrier.card)
  ```

- **Notación matemática:** **Tercer Teorema de Sylow**: si $n_p$ = número de subgrupos de Sylow $p$, entonces $n_p \equiv 1 \pmod{p}$ y $n_p \mid |G|$.

---

## Resumen de símbolos — `Sylow/Sylow.lean`

| Símbolo | Tipo | Computable | Importancia |
|---|---|---|---|
| `dvd_card` | `def` (Prop) | — | media |
| `pow_dvd_card` | `def` (Prop) | — | media |
| `isPSubgroup` | `def` (Prop) | — | alta |
| `isSylowExponent` | `def` (Prop) | — | alta |
| `isSylowSubgroup` | `def` (Prop) | — | alta |
| `cauchy_minimal` | `theorem` | — | alta |
| `sylow_lift_from_cauchy` | `theorem` | — | alta |
| `sylow_first` | `theorem` | — | alta |
| `sylow_second` | `theorem` | — | alta |
| `sylow_third` | `theorem` | — | alta |

---

## Resumen general de `doc/REFERENCE-GroupTheory.md`

| Módulo | Símbolos públicos |
|---|---|
| `Zassenhaus.lean` | 15 (12 sin sorry + 2 nuevos + 1 con sorry) |
| `NormalSubgroup.lean` | 10 |
| `Sylow/Cosets.lean` | 20 |
| `QuotientGroup.lean` | 28 |
| `FirstIsomorphism.lean` | 15 |
| `SecondIsomorphism.lean` | 13 |
| `ThirdIsomorphism.lean` | 10 |
| `CorrespondenceTheorem.lean` | 13 |
| `Action.lean` | 6 |
| `Sylow/CosetAction.lean` | 1 |
| `Sylow/Sylow.lean` | 10 |
| **Total** | **138** |
