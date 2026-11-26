# Project instructions — lean-NASC

Before working, read and follow [the shared Lean instructions](../lean-codes/AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`.
- Build output: `.lake/build-NASC`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/NASC-build.log 2>&1`.
- `.lake` points to the shared `/export/scratch1/braams/lean-codes-lake` on local disk.
  NASC uses the shared `.lake/packages` checkouts.
  The pins in `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`
  are authoritative.
- In this project the library search order is Mathlib → pinned TauCeti → local project code.

## Project

This project is in the area of numerical analysis and scientific computing (NASC). The
project follows the style of the sibling ~/lean-{CKSD,MSSS,MSBT,ASGT} projects that each have
their own focus areas. In each of these projects the first order of business is to assemble
a bibliography, and here it will be in the file ./NASC-bib.md. This file is meant for the
human reader. Its items are graduate level textbooks, research monographs, review articles,
and sometimes edited collections. But we try to keep it concise and focused on what is
valuable for defining the core knowledge. A volume of conference proceedings is probably not
a good entry for the bibliography.

PDF files for some of the references are or will be in the directory ../lean-NASC/References/.

There may be additional files, for example `*.json`, for precise bibliographical data.

There will be a file `SYNOPSIS.md` that describes the core mathematical content of the
references in the project area. This file is meant for the human mathematician reader; it does
not reference any technical Lean concepts. Proofs are outside the scope of the synopsis.

Coverage of the synopsis in Lean Mathlib and TauCeti will be documented in the file
`STRUCTURE.md` following the style of the various STRUCTURE files in the mentioned sibling
projects. File `GAPS.md` restates the principal results that none of the libraries proves.

Following the bibliographical work and the development of the inventories the project continues
with the formalization of content of `GAPS.md`. The Lean codes for this formalization are
developed in the subdirectory NASC. The Lean codes created there should all live in a NASC
namespace. Within that namespace the naming should adhere to Mathlib standards. (I have in mind
that at some point this becomes a TauCeti project, and then the namespace NASC will be replaced
by namespace TauCeti.) So one task is to go through all of `GAPS.md` and for the identified gaps,
create code according to Mathlib standards in the NASC subdirectory. At first any such code may
only be admitted, but in time the `sorry`s should be removed.

You may be asked to edit, revise or expand any of the files in the project directory or to create
new files.
- Keep changes narrowly related to the request.
- Preserve unrelated user changes.
- Do not commit changes unless explicitly requested.

## File length

A Lean file of about 1000 lines is a candidate for splitting along a natural mathematical seam;
1500 lines is the hard limit, and a longer Lean file must be split.

## Documentation consistency

- Describe the present mathematical content and coverage. Do not include development histories,
  review rounds, or accounts of additions, removals, renumbering, or changes in inventory counts.
  Retain source provenance and the library revisions needed to interpret coverage claims.
- Treat each numbered SYNOPSIS statement as the mathematical source for its restatements in
  GAPS.md. Propagate corrections to hypotheses, conventions, and conclusions to every affected
  restatement and STRUCTURE assessment. A Scope or Argument paragraph must not silently add a
  missing hypothesis to a Statement paragraph.
- After changing statements or selections, recount synopsis entries, coverage classifications,
  selected gaps, easy entries, and Scope paragraphs. Update the indexes and library summaries,
  and check local Markdown links. New entries take the next free identifier.
