# Plan de demostración: Powerset

## Estado actual del archivo (2026-04-10 00:00)

Build: **✅ 0 sorry, 0 errores, 0 warnings.**

| Teorema | Estado | Ubicación |
|---|---|---|
| powersetCList_extEq | ✅ Probado | Operations/Powerset.lean |
| mem_powerset | ✅ Probado | Axioms/Powerset.lean |

**Ambos sorry resueltos el 2026-04-10.**

---

## Técnica de demostración utilizada

### powersetCList_extEq

Se probó mediante el lema intermedio `mem_powersetCList`:

```
mem y (powersetCList A) = true ↔ subset y A = true
```

- **Dirección →**: Si `y ∈ powersetCList A`, existe `zs ∈ sublists xs` tal que `extEq y (mk zs)`. Por `sublists_subset`, `subset (mk zs) (mk xs)`, y por `subset_trans`, `subset y A`.
- **Dirección ←**: Si `subset y A`, construimos testigo `xs.filter (fun z => mem z y)` que está en `sublists xs` (por `filter_in_sublists`) y es `extEq` a `y` (vía `mem_right_respects_extEq` + propiedades de filter).

Una vez con `mem_powersetCList`, la prueba de `powersetCList_extEq` se reduce a `subset_trans`.

### mem_powerset

Levantamiento a CList vía `Quotient.exists_rep`, reducción a `mem_powersetCList` + `subset_iff_forall_mem_clist`.
