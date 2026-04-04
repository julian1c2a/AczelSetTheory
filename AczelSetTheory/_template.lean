/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- REFERENCE.md: project this file after every modification.
-- See AI-GUIDE.md §12 for the "proyectar" protocol.
-- See NAMING-CONVENTIONS.md for naming rules.
--
-- Dependencies: AczelSetTheory.CSets (add more as needed)
-- @axiom_system: none
-- @importance: medium

import AczelSetTheory.CSets
-- import AczelSetTheory.OtherModule

namespace AczelSetTheory.ModuleName

-- ============================================================
-- Section 1: Definitions
-- ============================================================
-- Naming: UpperCamelCase for Prop predicates (IsXxx)
--         lowerCamelCase for functions/constructors

-- def myDef : Type := ...

-- ============================================================
-- Section 2: Basic Properties
-- ============================================================
-- Naming: subject_predicate pattern (snake_case)
--         Suffixes: _iff, _eq, _of_, _mem, _subset, _ne

-- theorem myTheorem : ... := by ...

-- ============================================================
-- Section 3: Advanced Theorems
-- ============================================================
-- Naming: conclusion_of_hypothesis pattern
--         Use .mp/.mpr for iff directions

-- ============================================================
-- Section 4: Exports
-- ============================================================

end AczelSetTheory.ModuleName

export AczelSetTheory.ModuleName (
  -- myDef
  -- myTheorem
)
