$f = "E:\Dropbox\GitHub\lean4\AczelSetTheory\REFERENCE.md"
$lines = [System.IO.File]::ReadAllLines($f, [System.Text.Encoding]::UTF8)
$n = $lines.Length
Write-Host "Total lines read: $n"
if ($n -ne 1744) { Write-Host "ERROR: Expected 1744 lines, got $n. Aborting."; exit 1 }

# Verify key boundaries
Write-Host "idx 164: $($lines[164])"   # last line before §4.8
Write-Host "idx 942: $($lines[942])"   # first transition line after §4.42
Write-Host "idx 956: $($lines[956])"   # last transition line
Write-Host "idx 957: $($lines[957])"   # first line of §6.8
Write-Host "idx 1461: $($lines[1461])" # last line of §6 content
Write-Host "idx 1462: $($lines[1462])" # ## 7. Exports per Module
Write-Host "idx 1706: $($lines[1706])" # last content line of VN/Arithmetic
Write-Host "idx 1707: $($lines[1707])" # blank after §7
Write-Host "idx 1708: $($lines[1708])" # ---
Write-Host "idx 1710: $($lines[1710])" # ## 8. Notations

# en-dash character (U+2013)
$en = [char]0x2013

# §4 redirect block (replaces indices 165-941)
$sec4 = @(
    "### 4.8${en}4.15 HFSets and core operations",
    "",
    "> Definitions moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#4-definitions).",
    "",
    "---",
    "",
    "### 4.16${en}4.18 PList modules",
    "",
    "> Definitions moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#4-definitions).",
    "",
    "---",
    "",
    "### 4.19${en}4.32 Relations (functions, ordered pairs, compositions)",
    "",
    "> Definitions moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#4-definitions).",
    "",
    "---",
    "",
    "### 4.33${en}4.39 Algebra (SymDiff, Cardinal, Boolean, Succ, VonNeumann, Choice)",
    "",
    "> Definitions moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#4-definitions).",
    "",
    "---",
    "",
    "### 4.40 PList/Fin0.lean",
    "",
    "> Definitions moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#4-definitions).",
    "",
    "---",
    "",
    "### 4.41 HFList.lean",
    "",
    "> Definitions moved to [doc/REFERENCE-HFList.md](doc/REFERENCE-HFList.md#4-definitions).",
    "",
    "---",
    "",
    "### 4.42 VN modules",
    "",
    "> Definitions moved to [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#4-definitions)."
)

# §6 redirect block (replaces indices 957-1461)
$sec6 = @(
    "### 6.8${en}6.15 HFSets and core operations",
    "",
    "> Theorems moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#6-theorems).",
    "",
    "### 6.16${en}6.17 PList modules",
    "",
    "> Theorems moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#6-theorems).",
    "",
    "### 6.18${en}6.21 Relations: compositions, identity, products, images",
    "",
    "> Theorems moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#6-theorems).",
    "",
    "### 6.22${en}6.24 Algebra: SymDiff, Singleton, Subset",
    "",
    "> Theorems moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#6-theorems).",
    "",
    "### 6.25 Axioms/OrderedPair",
    "",
    "> Theorems moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#6-theorems).",
    "",
    "### 6.26${en}6.27 Algebra: Foundation, Decidable",
    "",
    "> Theorems moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#6-theorems).",
    "",
    "### 6.28${en}6.34 Relations: Relation, Function, Bijection, Inverse, Composition, Restriction, Replacement",
    "",
    "> Theorems moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#6-theorems).",
    "",
    "### 6.35${en}6.42 Algebra: Succ, SymDiff, Lattice, BooleanAlgebra, BooleanRing, VonNeumann, Choice, Cardinal",
    "",
    "> Theorems moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#6-theorems).",
    "",
    "### 6.43 PList/Fin0",
    "",
    "> Theorems moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#6-theorems).",
    "",
    "### 6.44 HFList",
    "",
    "> Theorems moved to [doc/REFERENCE-HFList.md](doc/REFERENCE-HFList.md#6-theorems).",
    "",
    "### 6.45${en}6.48 VN modules",
    "",
    "> Theorems moved to [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#6-theorems)."
)

# §7 redirect block (replaces indices 1462-1706)
$sec7 = @(
    "## 7. Exports per Module",
    "",
    "### CList modules (Basic, ExtEq, SetEquiv, Order, Sort, Normalize)",
    "",
    "> Exports moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#7-exports-per-module).",
    "",
    "### HFSets.lean",
    "",
    "> Exports moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#7-exports-per-module).",
    "",
    "### CList/Filter.lean",
    "",
    "> Exports moved to [doc/REFERENCE-CList.md](doc/REFERENCE-CList.md#7-exports-per-module).",
    "",
    "### HFSets operations (Operations/Union${en}Powerset, Axioms/Union${en}Powerset, Notation.lean)",
    "",
    "> Exports moved to [doc/REFERENCE-HFSets.md](doc/REFERENCE-HFSets.md#7-exports-per-module).",
    "",
    "### Relations modules (Operations and Axioms: FunctionComp, Identity, Product, Image, OrderedPair, Relation, Function, Bijection, Inverse, Composition, Restriction, Replacement)",
    "",
    "> Exports moved to [doc/REFERENCE-Relations.md](doc/REFERENCE-Relations.md#7-exports-per-module).",
    "",
    "### Algebra modules (Operations/SymDiff, Cardinal; Axioms/Singleton, Subset, Foundation, Decidable, Succ, SymDiff, Lattice, BooleanAlgebra, BooleanRing, VonNeumann, Choice, Cardinal)",
    "",
    "> Exports moved to [doc/REFERENCE-Algebra.md](doc/REFERENCE-Algebra.md#7-exports-per-module).",
    "",
    "### PList modules (PList/Basic, Lemmas, Omega0, Fin0)",
    "",
    "> Exports moved to [doc/REFERENCE-PList.md](doc/REFERENCE-PList.md#7-exports-per-module).",
    "",
    "### HFList.lean",
    "",
    "> Exports moved to [doc/REFERENCE-HFList.md](doc/REFERENCE-HFList.md#7-exports-per-module).",
    "",
    "### VN modules (VN/Basic, Injective, IsNat, Arithmetic)",
    "",
    "> Exports moved to [doc/REFERENCE-VN.md](doc/REFERENCE-VN.md#7-exports-per-module)."
)

$new = New-Object System.Collections.ArrayList

# Part 1: before §4.8 (indices 0-164)
foreach ($line in $lines[0..164]) { [void]$new.Add($line) }

# Part 2: §4 redirects (replaces indices 165-941)
foreach ($line in $sec4) { [void]$new.Add($line) }

# Part 3: transition lines (indices 942-956): blank + --- + blank + axioms note + blank + --- + blank + ## 6. + ... + §6.1-6.7 redirect + blank
foreach ($line in $lines[942..956]) { [void]$new.Add($line) }

# Part 4: §6 redirects (replaces indices 957-1461)
foreach ($line in $sec6) { [void]$new.Add($line) }

# Part 5: blank line before §7 (index 1462 is "## 7." but we output sec7 which starts with "## 7.")
# Skip index 1462 (## 7. Exports per Module) — sec7 already has it
# But first add the blank line that was between §6.48 redirect and ## 7.
# Actually index 1461 = last line of §6.48 content (kept at end of sec6),
# and the blank between §6 and §7 is at index ... let's check:
# idx 1461 = last line kept from §6 (the "Theorems moved to REFERENCE-VN.md" line)
# idx 1462 = blank (should be blank between §6 and §7)
# Wait — original file: the §6 content ends and then ## 7. is at line 1463 (idx 1462).
# So idx 1462 = "## 7. Exports per Module"
# There was NO blank between end of §6.48 and ## 7. in the original?
# Let's check: sec6 ends with the VN redirect line (no trailing blank).
# The transition would need a blank before ## 7.
# Add a blank line before sec7 to separate from sec6
[void]$new.Add("")

# Part 5: §7 redirects (replaces indices 1462-1706)
foreach ($line in $sec7) { [void]$new.Add($line) }

# Part 6: rest of file from index 1707 (blank + --- + blank + ## 8. Notations + ...)
foreach ($line in $lines[1707..($n-1)]) { [void]$new.Add($line) }

Write-Host "New total lines: $($new.Count)"
[System.IO.File]::WriteAllLines($f, [string[]]$new, (New-Object System.Text.UTF8Encoding $false))
Write-Host "Done."
