# Next Steps

The project compiles cleanly on Lean 4.29.0. The single remaining `sorry` is
in `CSet.normalizar_eq_of_eq`. Closing it requires a chain of supporting
lemmas, ordered by dependency below.

## The open goal

```lean
theorem normalizar_eq_of_eq {A B : CList} (h : esIgual A B = true) :
    normalizar A = normalizar B
```

Key insight: if normalizar is idempotent, then esIgual na nb = true
implies na = nb (propositional equality) for normalized na, nb. With
that, both sides become permutations of the same finite set; with Sorted +
Nodup, they are equal lists.

Step 1 — normalizar_idem (highest priority)
theorem normalizar_idem (A : CList) : normalizar (normalizar A) = normalizar A

Needs: Steps 2a, 2b, 2c, and normalizar_cSize_le (already proved ✅).

Step 2 — Lemmas about ordenarLista / reducirDuplicados
2a ordenarLista_nodup — insertarOrdenado never inserts duplicates
2b reducirDuplicados_id_of_nodup — identity on duplicate-free lists
2c ordenarLista_id_of_sorted_nodup — identity on sorted+nodup lists (needs Step 3)
Step 3 — Order properties of esMenor
3a esMenor_irrefl — straightforward
3b esMenor_total — hardest; requires induction on the recursive structure of esMenor
3c ordenarLista_sorted — needs esMenor_total
Step 4 — Close the sorry
With Steps 1–3: prove sorted_nodup_setequiv_eq (two sorted nodup lists that
are SetEquiv with propositionally equal elements must be equal), then apply
it inside normalizar_eq_of_eq.

Dependency graph
esMenor_total (3b) ──────────────────────────────┐
                                                  │
ordenarLista_sorted (3c) ◄────────────────────────┤
ordenarLista_nodup (2a)                           │
                                                  │
ordenarLista_id_of_sorted_nodup (2c) ◄────────────┘
reducirDuplicados_id_of_nodup (2b)

normalizar_idem (1) ◄── 2a, 2b, 2c
                     ◄── normalizar_cSize_le  ✅

normalizar_eq_of_eq sorry ◄── normalizar_idem (1) + esMenor_total (3b)

Optional future work
esMenor_trans — needed for the "minimum element" argument
Union, intersection, powerset
Natural numbers as sets (Peano axioms)
