# AI-GUIDE Update — Export/Glob Architecture

**Date:** 2026-04-08
**Source project:** AczelSetTheory
**Target:** lean4-project-template AI-GUIDE.md

---

## Summary

New norms added to AI-GUIDE.md. These should be replicated in the
`lean4-project-template` repository.

### Changed section

**§23 — Barrel modules**: changed from "optional" to **mandatory** for any
subdirectory with 2+ modules.

### New sections

**§30 — Export blocks in leaf modules**
**§31 — Export block maintenance**
**§32 — Barrel files and exports**
**§33 — Template compliance**

### Compliance section update

The Compliance paragraph now references `(23, 30–33)` in addition to `(0–21)` and `(NC-1–NC-10)`.

---

## Full text to insert in template AI-GUIDE.md

Replace the existing `### (23.) Barrel modules (optional)` section and add the
`## Export/Glob Architecture` section immediately after `### (23.)`.

```markdown
### (23.) Barrel modules (mandatory for subdirectories)

Every subdirectory containing 2 or more `.lean` modules **MUST** have a barrel file.
The barrel file:

- Sits at the same level as the directory, named `DirName.lean` (e.g., `Operations.lean` for `Operations/`).
- Imports ALL production sub-modules in the directory (excludes `test_*.lean` and `Test*.lean`).
- Contains NO definitions, theorems, or proofs — only `import` statements and an optional header comment.
- Serves as the **single import point** for the subdirectory.

```lean
-- ProjectName/Operations.lean (barrel file)
import ProjectName.Operations.Union
import ProjectName.Operations.Intersection
import ProjectName.Operations.Setminus
-- ... all production modules in Operations/
```

The root barrel file (`ProjectName.lean`) **prefers barrel imports** over individual
sub-modules when a barrel exists:

```lean
-- ProjectName.lean (root barrel)
import ProjectName.CList          -- barrel for CList/
import ProjectName.Operations     -- barrel for Operations/
import ProjectName.Axioms         -- barrel for Axioms/
import ProjectName.HFSets         -- top-level module (no barrel needed)
import ProjectName.Notation       -- top-level module
```

`gen-root.bash` detects barrel files and emits the barrel import instead of listing
each sub-module individually.

---

## Export/Glob Architecture

### (30.) Export blocks in leaf modules

Every production module (not barrels, not test files) **MUST** end with an `export` block
that lists all public (non-private) definitions, theorems, lemmas, and instances from the
module's namespace. This makes declarations available to importers without requiring
`open Namespace`.

**Pattern:**

```lean
namespace MyNamespace

def myDef : Type := ...

theorem myTheorem : ... := ...

end MyNamespace

-- Export: all public declarations from this module
export MyNamespace (myDef myTheorem)
```

**Rules:**

1. The `export` statement goes AFTER `end namespace`, at the top level of the file.
2. List ALL non-private `def`, `theorem`, `lemma`, `instance` names.
3. Do NOT export `private` declarations, `_aux` helpers, or intermediate lemmas prefixed with `private`.
4. Keep the export list **sorted alphabetically** within each namespace.
5. If a module contributes to multiple namespaces, use one `export` per namespace.
6. `notation`, `macro`, `syntax` are NOT listed in `export` — they propagate automatically on `import`.

**Effect:** After `import ProjectName.Axioms.Union`, downstream code can write
`mem_union` directly instead of `MyNamespace.mem_union`.

### (31.) Export block maintenance

- **Adding** a new public declaration requires adding it to the `export` block.
- **Renaming** a declaration requires updating the `export` block.
- **Deleting** a public declaration requires removing it from the `export` block.
- When **projecting** a module to REFERENCE.md (§14), verify the export list matches.
- The export list is the **canonical list** of a module's public API.

### (32.) Barrel files and exports

Barrel files (`DirName.lean`) do **not** add their own `export` blocks — the leaf modules
handle their own exports. The barrel file's sole job is aggregation via `import`.

However, a barrel file **may** include a top-level comment cataloguing the public API:

```lean
-- ProjectName/Operations.lean
-- Public API: union, inter, setminus, pair, powerset, symDiff, orderedPair,
--             sep, sUnion, dom, range, comp, image, ...
import ProjectName.Operations.Union
import ProjectName.Operations.Intersection
-- ...
```

### (33.) Template compliance

The `_template.lean` file must reflect the export pattern. Section 4 ("Exports") in the
template shows the `export` block after `end namespace`. New modules created by
`new-module.bash` inherit this structure.

---
```

## Also update

1. **Compliance section**: Add `, and export/glob rules (23, 30–33)` to the verification list.
2. **`_template.lean`**: Section 4 comment should reference `AI-GUIDE.md §30–31`.
3. **`gen-root.bash`**: Make barrel-aware (detect `DirName.lean` + `DirName/` pairs).

---

## gen-root.bash changes

The script was rewritten to:

1. Detect barrel files: if `ProjectName/Foo.lean` exists AND `ProjectName/Foo/` is a directory, then `Foo.lean` is a barrel.
2. Import barrels instead of individual sub-modules.
3. Exclude `test_*`, `Test*`, `_template` files.
4. Report barrel count in output.

The full updated `gen-root.bash` is in the AczelSetTheory repository.
