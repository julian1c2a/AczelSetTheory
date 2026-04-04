# AI Assistant Guide — Documentation Standards

**Last updated:** 2026-04-04 00:00
**Author**: Julián Calderón Almendros

This document establishes requirements and standards for technical documentation of this Lean 4 project.

> **This file is the first document an AI assistant should read.**
> It defines the project's documentation protocol, naming conventions,
> file locking policy, and compliance checklist. Read it fully before
> touching any `.lean` file or documentation.

---

## Requirements for REFERENCE.md

### (0.) **This documentation is technical, not user-facing.** It is a reference for AI assistants and experienced Lean 4 developers. Clear, precise, complete — but not pedagogical

### (1.) **Lean modules**: List all `.lean` files in both root and subdirectories, with location, namespace, dependencies, and documentation status

### (2.) **Module dependencies**: Each module must clearly document which modules it depends on, and which modules depend on it. Critical for AI navigation without loading the full project

### (3.) **Namespaces and their relationships**: Namespaces are not necessarily equal to modules. Document which namespaces exist, which modules they belong to, and how they relate

### (4.) **Introduced definitions**: For each module and namespace, document all definitions with location, dependencies, mathematical notation, and Lean 4 signature

#### (4.1.) **How to document definitions**: Include the Lean 4 signature plus mathematical notation (no explanations — the audience is mathematicians and Lean 4 experts). Include module, namespace, and dependencies

#### (4.2.) **Computability**: Indicate whether the definition is computable or noncomputable, and whether it has a boolean counterpart, and if it is decidable or not

#### (4.3.) **Well-foundedness**: Indicate whether the definition includes a termination proof (*terminated by*)

#### (4.4.) **Notation**: Record introduced notation: infix/prefix/other, symbols used, priorities, so it can be used correctly in proofs and documentation

### (5.) **Introduced axioms and their references**: Each axiom must document its location (module, namespace, declaration order) and relationship to definitions

### (6.) For **axioms** and **definitions**, provide

#### (6.1.) **Mathematical notation** (not Lean code) for human readability. No explanations — mathematical language suffices

#### (6.2.) **Lean 4 signature** for correct usage in proofs and constructions

#### (6.3.) **Dependencies** required to build the definition or axiom

### (7.) Main theorems **without proof of any kind**, with reference to location (module, namespace, declaration order)

#### (7.1.) **Mathematical notation** (not Lean code)

#### (7.2.) **Lean 4 signature**

#### (7.3.) **Dependencies** required to prove the theorem

### (8.) **Nothing unproven goes in REFERENCE.md** — no pending theorems, no TODOs in this file. Only what is already proven or constructed in `.lean` files

### (9.) **Update REFERENCE.md each time you load a `.lean` file** and find something new. Record the date and the last modification date of the `.lean` file for traceability

### (10.) **REFERENCE.md must be self-sufficient** — enough to write new modules or documentation without loading the full project. This file **REFERENCE.md** is the primary purpose of the file for AI assistants

### (11.) **When reading a `.lean` file, add or verify its REFERENCE.md header comment** reminding the reader to project the file

### (12.) **"Projecting" a `.lean` file into REFERENCE.md** means updating REFERENCE.md with all relevant information proven or constructed in that file, following the points above

### (13.) **Relevant information** means all non-private definitions, notations, axioms, theorems, and any other content necessary to understand the project, use it as reference, or build further proofs

### (14.) **Everything exportable in a `.lean` module must be projected into REFERENCE.md** and must appear in the module's export block

---

## Timestamps

### (15.) All technical documentation files must include timestamps in `YYYY-MM-DD HH:MM` format (ISO 8601 abbreviated)

Applied to: REFERENCE.md, CHANGELOG.md, DEPENDENCIES.md, CURRENT-STATUS-PROJECT.md, and any technical summary file.

Purpose: Track how outdated a file is relative to REFERENCE.md, even within a single work session.

---

## Authorship and License

### (16.) All principal documentation files (README.md, REFERENCE.md, CURRENT-STATUS-PROJECT.md) must clearly state the author

### (17.) Credits visible in README.md: educational resources, bibliographic references, AI tools used

### (18.) License: MIT. Indicated in LICENSE, README.md, CURRENT-STATUS-PROJECT.md footer, and README.md badge

### (19.) **All `.lean` files must include a copyright header** before any `import`

```lean
/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
```

Placement: lines 1–5 of every `.lean` file, no exceptions (including the root module).

---

## File Locking System

`git-lock.bash` implements two levels of write protection.

### Protection levels

| Level | Command | Reversible | Purpose |
| ------- | --------- | ---------- | ------- |
| **Lock** | `lock` / `unlock` | Yes | One-file-at-a-time during development |
| **Freeze** | `freeze` / `thaw --confirm` | Emergency only | Module completed — immutable forever |

Tracking files:

- `locked_files.txt` — all locked files (lock + freeze)
- `frozen_files.txt` — permanently frozen modules only

### (20.) Session locking protocol

At most one `.lean` file unlocked at any time.

```bash
bash git-lock.bash lock   AczelSetTheory/Module.lean   # temporary lock
bash git-lock.bash unlock AczelSetTheory/Module.lean   # temporary unlock
bash git-lock.bash list                                # show all locked and frozen files
bash git-lock.bash init                                # install/reinstall pre-commit hook
```

Session protocol:

1. **Session start**: Run `list`. Lock all files except the target.
2. **Switching files**: Lock the current file **before** unlocking the next.
3. **Session end**: Lock **all** modified `.lean` files. Commit `locked_files.txt`.
4. **Pre-commit hook**: Blocks commits touching locked or frozen files.

Violation: If more than one file is unlocked, lock all and restart with the correct file.

### (21.) Module freeze protocol — immutable completed modules

When a module reaches ✅ Complete status in REFERENCE.md, it must be **frozen**.
A frozen module is permanently immutable: it cannot be unlocked, only extended.

```bash
bash git-lock.bash freeze AczelSetTheory/Module.lean   # mark as permanently frozen
bash git-lock.bash list                                 # shows [frozen] vs [locked]
```

**Attempting to unlock a frozen module is blocked** with a message pointing to
the extension protocol. The pre-commit hook also blocks any staged changes to
frozen files, distinguishing them from ordinary locked files.

**Emergency only** — thawing a frozen module:

```bash
bash git-lock.bash thaw AczelSetTheory/Module.lean --confirm
```

The `--confirm` flag is required. After thawing, update REFERENCE.md status
and document the reason for reopening the module.

#### Extension protocol for frozen modules

When a frozen module `Foo.lean` needs new content:

1. Create `FooExt.lean` in the same directory.

2. Import the frozen module and reopen its namespace:

   ```lean
   /-
   Copyright (c) 2026. All rights reserved.
   Author: Julián Calderón Almendros
   License: MIT
   -/
   import AczelSetTheory.Foo

   namespace AczelSetTheory   -- same namespace as Foo.lean
   -- new definitions and theorems here
   end AczelSetTheory
   ```

3. Add `FooExt.lean` to `AczelSetTheory.lean` (root import) and to REFERENCE.md.

4. `Foo.lean` remains frozen and untouched.

**Naming rule** (see NC-1): extension files follow `UpperCamelCase`:

| Base module | Extension |
| ----------- | --------- |
| `CSets.lean` | `CSetsExt.lean` |
| `CoreAxioms.lean` | `CoreAxiomsExt.lean` |
| `Ordinals.lean` | `OrdinalsArithmetic.lean` (content-named preferred) |

Content-named extensions (`OrdinalsArithmetic.lean`, `OrdinalsLimit.lean`) are
preferred over numbered ones (`OrdinalsExt1.lean`) when the topic is clear.

#### REFERENCE.md status codes with freeze

| Code | Meaning |
| ---- | ------- |
| ✅ Complete | Fully projected. May still be locked (temporary). |
| 🧊 Frozen | Permanently frozen. Extensions only via `*Ext.lean`. |
| 🔶 Partial | Documented partially. |
| 🔄 In progress | Actively being developed. |
| ❌ Pending | Not yet started. |

A module transitions: 🔄 → 🔶 → ✅ → 🧊. The 🧊 state is final.

---

## Available Scripts

| Script | Purpose |
| ------ | ------- |
| `bash git-lock.bash lock/unlock <file>` | Temporary file lock |
| `bash git-lock.bash freeze <file>` | Permanent module freeze |
| `bash git-lock.bash thaw <file> --confirm` | Emergency unfreeze |
| `bash git-lock.bash list` | Show locked and frozen files |
| `bash git-lock.bash init` | Install/reinstall pre-commit hook |
| `bash new-module.bash ModuleName` | Create new module from template |
| `bash gen-root.bash` | Regenerate root import file |
| `bash check-sorry.bash` | Find all sorry statements |
| `bash update-toolchain.bash v4.x.x` | Update Lean toolchain with build verification |
| `make help` | Show all Makefile targets |

---

## Naming Conventions

These rules apply to all `.lean` files in this project. Names are in **English** (or mathematical Spanish where established in the codebase).
The scheme follows Mathlib4 conventions.

> **A separate file `NAMING-CONVENTIONS.md`** contains extended examples,
> detailed rules (12 formation rules), a symbol-to-word dictionary, and
> migration tables. That file is the canonical reference for renaming.
> The summary below is kept in sync with it.

---

### Symbol-to-Word Dictionary (quick reference)

| Symbol | Name | | Symbol | Name | | Symbol | Name |
|--------|------|---|--------|------|---|--------|------|
| ∈ | `mem` | | ∪ | `union` | | + | `add` |
| ∉ | `not_mem` | | ∩ | `inter` | | * | `mul` |
| ⊆ | `subset` | | ⋃ | `sUnion` | | - | `sub`/`neg` |
| ⊂ | `ssubset` | | ⋂ | `sInter` | | / | `div` |
| 𝒫 | `powerset` | | \ | `sdiff` | | ^ | `pow` |
| σ | `succ` | | △ | `symmDiff` | | ∣ | `dvd` |
| ∅ | `empty` | | ᶜ | `compl` | | ≤ | `le` |
| = | `eq` | | ⟂ | `disjoint` | | < | `lt` |
| ≠ | `ne` | | ↔ | `iff` | | 0 | `zero` |
| ¬ | `not` | | → | `of` | | 1 | `one` |

### Theorem Name Formation Rules (summary)

1. **Conclusion first, hypotheses with `_of_`**: `c_of_a_of_b` — conclusion goes first, then `_of_hypothesis`
2. **Biconditionals carry `_iff`**: `mem_powerset_iff` (∈ 𝒫 ↔ ⊆)
3. **Use `.mp`/`.mpr` instead of `_wc` suffixes**: `inter_eq_empty_iff_disjoint.mp`
4. **Algebraic properties → axiomatic suffix**: `union_comm`, `inter_assoc`, `subset_refl`
5. **Predicates as prefix, operations in infix order**: `isNat_zero` (not `zero_is_nat`)
6. **Standard abbreviations**: `pos` (> 0), `neg` (< 0), `nonpos` (≤ 0), `nonneg` (≥ 0)
7. **`Is` prefix for Prop definitions**: `def IsNat` (UpperCamelCase); in theorem names → `lowerCamelCase`: `isNat_zero`
8. **Functions/constructors**: `lowerCamelCase` — `powerset`, `union`, `sep`, `comp`
9. **Specification pattern**: `mem_X_iff` — `mem_succ_iff`, `mem_inter_iff`, `mem_union_iff`
10. **Uniqueness/existence**: `inter_unique`, `powerset_unique`
11. **Lateral variants**: `_left`/`_right` — `subset_union_left`, `union_inter_distrib_left`
12. **Named theorems**: proper names kept as-is — `cantor_no_surjection`, `cantor_schroeder_bernstein`

### Standard Axiomatic Suffixes

| Suffix | Meaning | | Suffix | Meaning |
|--------|---------|---|--------|---------|
| `_comm` | commutativity | | `_self` | op with itself |
| `_assoc` | associativity | | `_left`/`_right` | lateral variant |
| `_refl` | reflexivity | | `_cancel` | cancellation |
| `_trans` | transitivity | | `_mono` | monotonicity |
| `_antisymm` | antisymmetry | | `_inj` | injectivity (iff) |
| `_symm` | symmetry | | `_injective` | injectivity (pred) |
| `_irrefl` | irreflexivity | | `_surjective` | surjectivity |

---

### (NC-1) Modules (`.lean` files)

`UpperCamelCase`. Named after mathematical content, not technical role.

| Pattern | Example |
| ------- | ------- |
| `UpperCamelCase.lean` | `CSets.lean`, `CoreAxioms.lean`, `Ordinals.lean` |

- Root entry point: `AczelSetTheory.lean` — imports only, no definitions.
- Template: `_template.lean` — underscore prefix marks non-imported utility files.
- Extension of frozen module: `FooExt.lean` — imports `Foo.lean`, reopens its namespace.
- Content-named extensions preferred: `OrdinalsArithmetic.lean` over `OrdinalsExt1.lean`.

---

### (NC-2) Namespaces

`UpperCamelCase`. Mirror the module file hierarchy.

| Level | Pattern | Example |
| ----- | ------- | ------- |
| Root | `AczelSetTheory` | `namespace AczelSetTheory` |
| Sub | `AczelSetTheory.Topic` | `namespace AczelSetTheory.Ordinals` |

- One namespace per module as a rule.
- Do not create sub-namespaces solely for grouping within a file — use `section` instead.
- `private` declarations do not need their own namespace.

---

### (NC-3) Types and Prop-predicates (`def` returning `Type` or `Prop`)

`UpperCamelCase`. Matches Mathlib's convention for `IsEmpty`, `IsClosed`, `Finset`, etc.

| Kind | Example |
| ---- | ------- |
| Sort/Type | `CList`, `CSet` |
| Prop predicate | `IsSet`, `IsEmpty`, `IsFun` |

---

### (NC-4) Functions and term-level definitions (`def` returning a value)

`lowerCamelCase`.

| Kind | Example |
| ---- | ------- |
| Constructor | `normalizar`, `insertarOrdenado` |
| Accessor | `dom`, `img`, `fst`, `snd` |

---

### (NC-5) Axioms

Prefix `AST_` (Aczel Set Theory) + `UpperCamelCase` descriptor.
The prefix signals axiomatic (unproven) status and distinguishes axioms from theorems at a glance.

| Pattern | Example |
| ------- | ------- |
| `AST_ShortName` | `AST_Ext`, `AST_Found`, `AST_Pair` |

---

### (NC-6) Exportable theorems and lemmas

Follow Mathlib4's **subject\_predicate** pattern, all `lowerCamelCase` with underscores.

```text
[subject]_[predicate]
[subject]_[predicate]_[object]
[subject]_[predicate]_of_[hypothesis]
```

---

### (NC-7) Private and auxiliary declarations

Use the `private` keyword. Optionally append `_aux` for intermediate steps.

```lean
private lemma foo_of_bar_aux : … := …
```

---

### (NC-8) Notations

Document every introduced notation in REFERENCE.md §5 with: symbol, priority, scope, expansion.

---

### (NC-9) Section names

`UpperCamelCase`, descriptive.

```lean
section Extensionality
section PairingLemmas
```

---

### (NC-10) Summary table

| Entity | Convention | Example |
| ------ | ---------- | ------- |
| Module (`.lean` file) | `UpperCamelCase` | `CSets.lean` |
| Namespace | `UpperCamelCase` | `AczelSetTheory`, `AczelSetTheory.Ordinals` |
| Type / Prop predicate | `UpperCamelCase` | `CList`, `IsFun` |
| Function / value def | `lowerCamelCase` | `normalizar`, `insertarOrdenado` |
| Axiom | `AST_ShortName` | `AST_Ext`, `AST_Found` |
| Exportable theorem | `subject_predicate` | `mem_pair_iff` |
| Private / auxiliary | `private` + optional `_aux` | `private lemma foo_aux` |
| Section | `UpperCamelCase` | `section Pairing` |
| Notation | `local notation` preferred | `local notation:50 …` |

---

## Compliance

Verify that REFERENCE.md, `.lean` files, and documentation files comply with all points
(0–21) and naming conventions (NC-1–NC-10) before considering documentation complete
and up to date.

---

## Directory Structure and Subdirectories

### (22.) Module organization by subdirectory

As the project grows, organize modules into **thematic subdirectories** inside `AczelSetTheory/`.
Each subdirectory groups related modules and corresponds to a sub-namespace.

Example structure:

```
AczelSetTheory/
├── CSets.lean                # Level 0: canonical set representation
├── _template.lean            # Template (not imported)
├── Core/
│   └── Basic.lean            # AczelSetTheory.Core.Basic
├── Axiom/
│   ├── Extension.lean        # AczelSetTheory.Axiom.Extension
│   └── Pairing.lean          # AczelSetTheory.Axiom.Pairing
└── Nat/
    └── Basic.lean            # AczelSetTheory.Nat.Basic
```

Rules:

- Subdirectory names: `UpperCamelCase`, matching the sub-namespace.
- `new-module.bash` supports paths: `bash new-module.bash Nat/Add` creates `AczelSetTheory/Nat/Add.lean`.
- `gen-root.bash` automatically scans subdirectories.
- Namespace mirrors path: `AczelSetTheory/Nat/Add.lean` → `namespace AczelSetTheory.Nat.Add`.

### (23.) Barrel modules (optional)

For a subdirectory `Foo/` with many modules, you may create `Foo.lean` at the same level
that re-exports all submodules:

```lean
-- AczelSetTheory/Foo.lean
import AczelSetTheory.Foo.Basic
import AczelSetTheory.Foo.Advanced
```

---

## Annotation System for REFERENCE.md

### (24.) Module-level annotations

Each module entry in REFERENCE.md §3 may include the following metadata:

```markdown
**@axiom_system**: `CZF` | `IZF` | `none`
**@importance**: `foundational` | `high` | `medium` | `low`
```

- `@axiom_system`: Which formal system the module primarily belongs to.
- `@importance`: How critical the module is to the project's dependency chain.

### (25.) Theorem-level annotations

Individual theorems or definitions in REFERENCE.md may be annotated:

```markdown
**@importance**: `high` | `medium` | `low`
```

- `high`: Used by 3+ other modules, or is a key axiom/definition.
- `medium`: Used by 1–2 other modules.
- `low`: Internal utility, only used within its own module.

Purpose: Helps AI assistants prioritize which theorems to load for context.

---

## Cross-Reference Files

### (26.) NAMING-CONVENTIONS.md

A standalone file with the full naming dictionary, 12 formation rules,
migration tables, and detailed examples. Canonical reference for renaming.
Updated whenever naming conventions evolve.

### (27.) NEXT-STEPS.md

A living document tracking planned development phases. Each phase includes:

- Name and objective
- List of modules to create/modify
- Dependencies on prior phases
- Estimated complexity (simple/medium/complex)

### (28.) THOUGHTS.md

An informal design journal for recording ideas, alternatives considered,
open questions, and future directions. Not normative — purely exploratory.
Useful for AI context on "why" decisions were made.
