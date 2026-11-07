# Residual definitions: first 78-record slice

This bounded audit examines the exact 78 IDs in the accompanying
[per-record evidence](residual-definition-audit-a.json), selected from the
residual cohort at `3fe6d92dc9b96d7693e5e52b4be4b549f40b39da`. The current
inspection base is `e6d8fa5f92223faba91eb37f0fdc37cc86a04ffc`.
None of these 78 is one of the reserved Q14 reception definitions.

“Residual” means absent from an argument's `definition_ids` and from those
arguments' premise/conclusion statements' definition links at that snapshot.
It does **not** mean unused in Lean or absent from every statement. The report
lists every direct current statement reference and argument consumer for each
record. All 78 still lack an argument consumer at the inspection base; eleven
have a definition-side or directly linked statement Lean declaration. Their
listed declaration bodies were inspected. For the remaining records, the audit
examines the unbound glossary scope without claiming that no analogous Lean
vocabulary exists elsewhere.

## Three corrections

| Definition | Correction and meaning boundary |
| --- | --- |
| `DEF-AD1-COLLECTIVE-ACTUAL-GOOD` | The linked declaration is a conditional production schema over independent `DrawsGoodFromEvils` and `GoodIn` parameters. It is not the definition of either relation and asserts no actual permission or good outcome by itself. The collective/distributive distinction remains. |
| `DEF-HUME-TEST-BEGINNING` | `NarrowWithholding` is `¬ refutes uncausedBeginning`. It constrains a supplied description/refutation interpretation; it does not define a temporal beginning, Lean provability or metaphysical impossibility. |
| `DEF-PROCLUS-UNITY-PARTICIPATION` | The primary locator now names `Vocabulary.Participates` on the very same dictionary consumed by the Proclus projection. `ParticipantUnityContrast` separately constrains participation by received unity and nonidentity. Shared vocabulary is not historical or philosophical equivalence with Plato's Form interpretation. |

The other 75 records retain their meanings and locators. Their per-ID
boundaries matter: examples include capacity versus actual exercise,
intellectual will versus passive creaturely appetite, individual versus common
knower, per-truth possibility versus a rigid individual, simple versus temporal
priority, opinion opposition versus logical negation, and a source account of
self-evidence versus corpus floor approval. No new fork is invented merely to
categorize a glossary entry. The report identifies what was inspected and
what remains open rather than asserting all definitions adequate in reality.

## Evidence limits

This is a prose/type/navigation audit, not renewed source interpretation or
independent verification of all downstream proof bodies. Existing source
claims, attribution, theorem evidence and frozen Challenges remain unchanged.
The intentionally unbound source glossaries remain unbound. A future
load-bearing use must still choose and justify its exact typed interpretation;
no alternate framework is eliminated by a textual similarity or a shared
field name.

The JSON is a static snapshot of this slice, with current record hashes,
complete direct metadata references, inspected declaration files and concise
per-record dispositions. It is not a proof-status registry or a second
handoff. The coordinator's `docs/definitions-audit.md` remains the overall
audit authority; the rest of the 234-record residual assignment and the wider
repository audit are not completed by this slice.

No Lean source, philosophical proposition, inference, source claim or floor
changes. The expected premise effect is none; the delivered PR records the
actual computed `corpus.py frontier-diff` comparison. Existing successful proof
checks are reused because their inputs are unchanged; no Lean build or
verification was needed for these metadata corrections.
