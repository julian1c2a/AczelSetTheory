# Matriz de Auditoria Modulo por Modulo

Generado: 2026-07-16 por `gen-audit-matrix.bash` (`make audit`)

## Resumen Global

- Archivos Lean: 204
- Lineas totales: 34581
- sorry: 14  (deuda aceptada del frente activo Rationals/Reals — ver ADR-022)
- admit: 0
- axiom: 0
- noncomputable def: 0
- Modulos con TODO/FIXME/PENDIENTE: 0
- Modulos con placeholder/stub: 0

> Nota: los conteos de sorry/admit/axiom/noncomputable se calculan tras
> despojar comentarios de linea (`--`) y de bloque (`/- -/`, anidados); las menciones
> de esas palabras en prosa/comentarios no se contabilizan.
>
> Los `sorry` estan acotados y declarados en `SORRY_BASELINE` (gen-audit-matrix.bash);
> `make audit` FALLA si aparece uno fuera del frente o por encima de su cota (ADR-022).
> El invariante duro 0 axiom / 0 admit / 0 noncomputable (O6a) no admite excepciones.

## Matriz

| Modulo | Subsistema | Lineas | sorry | admit | axiom | noncomputable def | TODO/FIXME/PEND | placeholder/stub | Estado |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|
| AczelSetTheory\Algebra.lean | Algebra.lean | 29 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\Action.lean | Algebra | 361 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\CorrespondenceTheorem.lean | Algebra | 169 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\CosetAction.lean | Algebra | 142 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\CosetCount.lean | Algebra | 353 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\Field.lean | Algebra | 305 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\FirstIsomorphism.lean | Algebra | 208 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\Group.lean | Algebra | 182 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\GroupHom.lean | Algebra | 94 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\HFMatrix.lean | Algebra | 720 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\Lattice.lean | Algebra | 316 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\LinearSpace.lean | Algebra | 272 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\Module.lean | Algebra | 286 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\Monoid.lean | Algebra | 133 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\NormalSubgroup.lean | Algebra | 376 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\QuotientGroup.lean | Algebra | 433 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\QuotientRing.lean | Algebra | 401 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\Ring.lean | Algebra | 165 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\RingHom.lean | Algebra | 158 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\SecondIsomorphism.lean | Algebra | 369 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\Subgroup.lean | Algebra | 613 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\Sylow.lean | Algebra | 3791 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\ThirdIsomorphism.lean | Algebra | 246 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Algebra\Zassenhaus.lean | Algebra | 727 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms.lean | Axioms.lean | 53 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Adjunction.lean | Axioms | 39 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Bijection.lean | Axioms | 138 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\BooleanAlgebra.lean | Axioms | 126 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\BooleanRing.lean | Axioms | 91 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\CardImage.lean | Axioms | 124 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Cardinal.lean | Axioms | 168 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\CartProd.lean | Axioms | 110 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Choice.lean | Axioms | 101 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Composition.lean | Axioms | 94 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Decidable.lean | Axioms | 75 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\DecidableFunction.lean | Axioms | 113 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Fintype.lean | Axioms | 195 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Foundation.lean | Axioms | 96 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Function.lean | Axioms | 181 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\FunctionComp.lean | Axioms | 199 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Identity.lean | Axioms | 214 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Image.lean | Axioms | 129 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Induction.lean | Axioms | 77 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Intersection.lean | Axioms | 64 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Inverse.lean | Axioms | 163 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Lattice.lean | Axioms | 180 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\LinearOrder.lean | Axioms | 71 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\NPow.lean | Axioms | 51 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Order.lean | Axioms | 263 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\OrderedPair.lean | Axioms | 72 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Ordinal.lean | Axioms | 131 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\OrdinalNat.lean | Axioms | 534 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Pair.lean | Axioms | 30 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Powerset.lean | Axioms | 29 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Product.lean | Axioms | 122 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Rank.lean | Axioms | 179 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Relation.lean | Axioms | 128 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Replacement.lean | Axioms | 77 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Restriction.lean | Axioms | 75 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Separation.lean | Axioms | 42 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Setminus.lean | Axioms | 73 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Singleton.lean | Axioms | 19 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Subset.lean | Axioms | 51 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Succ.lean | Axioms | 83 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\SymDiff.lean | Axioms | 31 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\Union.lean | Axioms | 43 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\VonNeumann.lean | Axioms | 101 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Axioms\WellOrder.lean | Axioms | 264 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\CList.lean | CList.lean | 14 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\CList\Basic.lean | CList | 185 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\CList\ExtEq.lean | CList | 146 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\CList\Filter.lean | CList | 100 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\CList\Normalize.lean | CList | 540 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\CList\Order.lean | CList | 164 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\CList\SetEquiv.lean | CList | 223 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\CList\Sort.lean | CList | 249 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Combinatorics.lean | Combinatorics.lean | 10 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Combinatorics\Counting.lean | Combinatorics | 246 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\HFList.lean | HFList.lean | 418 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\HFListOps.lean | HFListOps.lean | 90 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\HFSets.lean | HFSets.lean | 157 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers.lean | Integers.lean | 18 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\Arithmetic.lean | Integers | 96 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\Basic.lean | Integers | 515 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\Bezout.lean | Integers | 300 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\Bijection.lean | Integers | 73 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\Canonical.lean | Integers | 117 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\Functions.lean | Integers | 251 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\MobiusLiouville.lean | Integers | 227 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\Order.lean | Integers | 358 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\PadicVal.lean | Integers | 298 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\Z0.lean | Integers | 260 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\Z0Ops.lean | Integers | 173 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Integers\ZModN.lean | Integers | 256 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Meta\AxiomCheck.lean | Meta | 137 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Notation.lean | Notation.lean | 140 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations.lean | Operations.lean | 31 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Cardinal.lean | Operations | 57 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\CartProd.lean | Operations | 217 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Composition.lean | Operations | 23 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Function.lean | Operations | 31 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\FunctionComp.lean | Operations | 22 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Identity.lean | Operations | 16 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Intersection.lean | Operations | 186 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Inverse.lean | Operations | 20 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\NPow.lean | Operations | 39 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Order.lean | Operations | 165 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\OrderedPair.lean | Operations | 52 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Pair.lean | Operations | 47 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Powerset.lean | Operations | 346 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Product.lean | Operations | 20 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Relation.lean | Operations | 35 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Replacement.lean | Operations | 19 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Restriction.lean | Operations | 19 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Separation.lean | Operations | 43 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Setminus.lean | Operations | 75 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\SymDiff.lean | Operations | 36 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Operations\Union.lean | Operations | 136 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\PList.lean | PList.lean | 12 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\PList\Basic.lean | PList | 149 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\PList\Fin0.lean | PList | 165 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\PList\Lemmas.lean | PList | 438 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\PList\Omega0.lean | PList | 80 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals.lean | Rationals.lean | 30 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\AbsVal.lean | Rationals | 282 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Archimedean.lean | Rationals | 196 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Basic.lean | Rationals | 753 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Bisection.lean | Rationals | 157 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Canonical.lean | Rationals | 382 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\CauchySeqAlgebra.lean | Rationals | 538 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Convergence.lean | Rationals | 267 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Density.lean | Rationals | 32 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Inv.lean | Rationals | 285 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Irrational.lean | Rationals | 499 | 1 | 0 | 0 | 0 | 0 | 0 | SORRY:1 (frente activo) |
| AczelSetTheory\Rationals\IsCauchy.lean | Rationals | 218 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\MinAdd.lean | Rationals | 40 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Polynomial.lean | Rationals | 116 | 4 | 0 | 0 | 0 | 0 | 0 | SORRY:4 (frente activo) |
| AczelSetTheory\Rationals\PowOrder.lean | Rationals | 88 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Q0.lean | Rationals | 377 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Q0Cauchy.lean | Rationals | 43 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Q0CauchyAlgebra.lean | Rationals | 123 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Q0Ops.lean | Rationals | 44 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\RationalLog.lean | Rationals | 137 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Roots.lean | Rationals | 635 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Rationals\Series.lean | Rationals | 84 | 6 | 0 | 0 | 0 | 0 | 0 | SORRY:6 (frente activo) |
| AczelSetTheory\Reals.lean | Reals.lean | 12 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Reals\Incompleteness.lean | Reals | 54 | 3 | 0 | 0 | 0 | 0 | 0 | SORRY:3 (frente activo) |
| AczelSetTheory\Topology.lean | Topology.lean | 11 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Topology\Basic.lean | Topology | 159 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Topology\Interior.lean | Topology | 247 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Topology\Neighborhoods.lean | Topology | 249 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Topology\Separation.lean | Topology | 221 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\Topology\Subspace.lean | Topology | 189 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN.lean | VN.lean | 55 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\ActionVN.lean | VN | 50 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\Arithmetic.lean | VN | 72 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\Basic.lean | VN | 64 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\BinomVN.lean | VN | 75 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\CRTVN.lean | VN | 39 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\CantorPairingVN.lean | VN | 69 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\CardVN.lean | VN | 39 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\CorrespondenceTheoremVN.lean | VN | 53 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\CountingVN.lean | VN | 49 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\DigitsVN.lean | VN | 54 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\DivVN.lean | VN | 67 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\FSet.lean | VN | 101 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\FactorialVN.lean | VN | 88 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\FermatVN.lean | VN | 58 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\FibVN.lean | VN | 55 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\FirstIsomorphismVN.lean | VN | 47 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\GcdVN.lean | VN | 111 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\GodelBetaVN.lean | VN | 35 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\HFGroupVN.lean | VN | 134 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\InitialityVN.lean | VN | 152 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\Injective.lean | VN | 30 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\IsNat.lean | VN | 25 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\LatticeVN.lean | VN | 139 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\ListBridgeVN.lean | VN | 187 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\LogVN.lean | VN | 67 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\MapBridgeVN.lean | VN | 114 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\ModEqVN.lean | VN | 131 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\NewtonBinomVN.lean | VN | 52 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\NormalSubgroupVN.lean | VN | 59 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\OrbitVN.lean | VN | 46 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\PairingVN.lean | VN | 57 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\PeanoArith.lean | VN | 147 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\PeanoAxioms.lean | VN | 76 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\PermVN.lean | VN | 67 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\PowVN.lean | VN | 117 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\PrimeVN.lean | VN | 175 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\PrimesVN.lean | VN | 25 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\ProdBridgeVN.lean | VN | 59 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\ProductVN.lean | VN | 62 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\QuotientGroupVN.lean | VN | 49 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\RankVN.lean | VN | 37 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\SecondIsomorphismVN.lean | VN | 49 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\SignVN.lean | VN | 40 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\SqrtVN.lean | VN | 64 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\SubVN.lean | VN | 93 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\SummationVN.lean | VN | 69 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\SymGroupVN.lean | VN | 163 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\ThirdIsomorphismVN.lean | VN | 48 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\VN\TotientVN.lean | VN | 57 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
| AczelSetTheory\_template.lean | _template.lean | 54 | 0 | 0 | 0 | 0 | 0 | 0 | OK |
