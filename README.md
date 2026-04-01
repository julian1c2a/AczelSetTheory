# AczelSetTheory

## Aczel's Set Theory in Lean 4

This repository contains an implementation of Aczel's set theory in Lean 4, which is an implementation of Axiomatic Set Theory that is constructible, computable, and representable. The main file is `CSets.lean`, which defines the basic concepts and operations of Aczel's sets, such as membership, equality, union, intersection, and so on. The file also includes some examples and properties of these sets.

It is equivalent to a ZF set theory, where we do not have the axiom of infinity, nor the axiom of choice, nor the axiom of regularity. What it does add is recursion and induction over sets, which allows defining recursive functions and proving properties by induction. Moreover, this set theory is constructive, which means that all proofs and definitions are effectively computable.

The used logic is intuitionistic, which means that we do not assume the law of excluded middle, and we do not have classical reasoning. This allows us to work with sets in a less flexible way, but it allows us to avoid some paradoxes and inconsistencies that arise in classical set theory.

Lean 4 is ideal for this implementation, because the core of the language is restrictively constructible. This means that all definitions and proofs must be effectively computable, and we cannot use any non-constructive principles. This allows us to ensure that all the sets and operations we define are well-defined and computable.

This axiomatic system allows developing a theory of sets and a theory of numbers together, where we can define natural numbers as sets, and we can prove properties of numbers using the properties of sets. The incompleteness results of Gödel are applicable to this system, and we can prove that there are true statements about sets that cannot be proven within the system itself.
