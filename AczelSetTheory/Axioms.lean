/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Barrel module: imports all Axioms sub-modules
-- Public API: mem_sep, mem_union, mem_sUnion, mem_inter, mem_setminus,
--             mem_pair, mem_powerset, mem_symDiff, foundation, mem_singleton,
--             orderedPair_eq_iff, mem_decidable, subset_refl, subset_antisymm,
--             union_comm, inter_comm, ..., mem_image, choose, choose_mem, ...

import AczelSetTheory.Axioms.BooleanAlgebra
import AczelSetTheory.Axioms.BooleanRing
import AczelSetTheory.Axioms.Choice
import AczelSetTheory.Axioms.Decidable
import AczelSetTheory.Axioms.Foundation
import AczelSetTheory.Axioms.Function
import AczelSetTheory.Axioms.Intersection
import AczelSetTheory.Axioms.Lattice
import AczelSetTheory.Axioms.OrderedPair
import AczelSetTheory.Axioms.Pair
import AczelSetTheory.Axioms.Powerset
import AczelSetTheory.Axioms.Relation
import AczelSetTheory.Axioms.Replacement
import AczelSetTheory.Axioms.Separation
import AczelSetTheory.Axioms.Setminus
import AczelSetTheory.Axioms.Singleton
import AczelSetTheory.Axioms.Subset
import AczelSetTheory.Axioms.Succ
import AczelSetTheory.Axioms.SymDiff
import AczelSetTheory.Axioms.Union
import AczelSetTheory.Axioms.VonNeumann
