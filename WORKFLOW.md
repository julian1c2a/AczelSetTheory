# Development Workflow — AczelSetTheory

**Author**: Julián Calderón Almendros
*Last updated: 2026-04-04*

Complete guide for daily development on this project.

---

## Part 1: Setup (once per machine/clone)

### Step 1 — Install the git hook

```bash
bash git-lock.bash init
```

This installs the pre-commit hook that:

- Blocks commits that touch locked `.lean` files
- Warns about `sorry` statements in staged files

> **Note**: Run this once per machine/clone. The hook lives in `.git/hooks/` which is not versioned.

---

## Part 2: Daily Development Workflow

### Starting a work session

```bash
# 1. Check which files are unlocked
bash git-lock.bash list

# If more than one file is unlocked from a previous session, lock all:
# bash git-lock.bash lock AczelSetTheory/CSets.lean

# 2. Check current sorry status
make sorry
```

### Creating a new module

```bash
# Creates AczelSetTheory/ModuleName.lean from _template.lean
# and adds the import to AczelSetTheory.lean
make new NAME=ModuleName

# For nested modules:
make new NAME=Axiom/Extension
```

Then edit the generated file. When done:

```bash
bash git-lock.bash lock AczelSetTheory/ModuleName.lean
```

### Editing an existing module

```bash
# 1. Unlock the file
bash git-lock.bash unlock AczelSetTheory/CSets.lean

# 2. Edit...

# 3. Lock when done
bash git-lock.bash lock AczelSetTheory/CSets.lean
```

### The one-file rule

> **At most one `.lean` file may be unlocked at any time.**

If you need to switch to a different file mid-session:

```bash
bash git-lock.bash lock AczelSetTheory/CurrentModule.lean
bash git-lock.bash unlock AczelSetTheory/NextModule.lean
```

### Building

```bash
make build          # compile full project
make rebuild        # clean + compile
```

### Checking proofs

```bash
make sorry          # list all sorry in project
make status         # lock status + sorry count
```

---

## Part 3: Commit Protocol

### Before committing

```bash
# 1. Verify only the intended files are unlocked
bash git-lock.bash list

# 2. Check for sorry
make sorry

# 3. Update REFERENCE.md
#    Project modified .lean files → REFERENCE.md
#    (See AI-GUIDE.md §12)
```

### Committing

```bash
# Stage specific files (avoid git add -A to prevent accidents)
git add AczelSetTheory/ModuleName.lean REFERENCE.md CHANGELOG.md

git commit -m "feat: add ModuleName with N definitions and M theorems"
```

### After committing — lock all modified .lean files

```bash
bash git-lock.bash lock AczelSetTheory/ModuleName.lean

# Commit the updated locked_files.txt
git add locked_files.txt
git commit -m "chore: lock ModuleName after completion"
```

### Ending a session

```bash
# Lock ALL modified .lean files
bash git-lock.bash list   # verify none remain unlocked

git push origin master
```

---

## Part 4: Updating the Lean Toolchain

```bash
# Try a new version — automatically builds and commits on success
bash update-toolchain.bash v4.30.0

# On failure it restores the previous version automatically
```

---

## Part 5: Regenerating the Root Module

If you add/remove modules manually without using `new-module.bash`:

```bash
bash gen-root.bash
```

This scans `AczelSetTheory/` for all `.lean` files (excluding `_template.lean`)
and rewrites `AczelSetTheory.lean` with the full import list.

---

## Part 6: AI Assistant Sessions (Claude Code)

When starting a session with an AI assistant:

1. **Point to AI-GUIDE.md** — the AI reads this first
2. **Point to REFERENCE.md** — the AI uses this instead of loading all `.lean` files
3. **Remind the one-file rule** — unlock only the target module
4. **At session end** — AI locks all modified files and updates `REFERENCE.md`, `CHANGELOG.md`

Key commands to tell the AI:

```
bash git-lock.bash list                            # what is currently unlocked?
bash git-lock.bash unlock AczelSetTheory/File.lean # unlock for editing
bash git-lock.bash lock AczelSetTheory/File.lean   # lock after completion
make sorry                                         # any sorry left?
```

---

## Quick Reference

```bash
bash git-lock.bash init              # install git hook (once per clone)
bash git-lock.bash list              # show locked files
bash git-lock.bash lock File.lean    # lock a file
bash git-lock.bash unlock File.lean  # unlock a file
make new NAME=Module                 # create new module
make build                           # compile
make sorry                           # check for sorry
make status                          # lock + sorry status
bash gen-root.bash                   # regenerate root imports
bash update-toolchain.bash vX.Y.Z    # update Lean version
```
