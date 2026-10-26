# Ayer: verification and self-application boundary

This is a blocked primary-source investigation for #185 and #363, not a
refutation of Ayer, empiricism or expressivism. It adds no source claim,
formal result, theory answer map, or root-path discharge. The existing
`AYER-LTL-EMOTIVISM` candidate retains both the ethical reading and this
verification obligation; neither issue is complete.

## Conditional inference already available

`TruthCore.Logic.SelfApplication.Norm.selfApplication` and the certified wrapper
`TruthCore.Results.Logic.SelfApplication.Dilemma.selfApplicationDilemma`
(`LOGIC-SELF-APPLICATION-DILEMMA`) already supply the inference. A proposed
instance would use a type of sentences, an independently specified scope,
`Acceptable := literally/cognitively meaningful`, and
`standard s := analytic s ∨ empiricallyVerifiable s`. These are analytical
placeholders, not a sourced account of Ayer's criterion. No truth predicate,
assertion of the criterion, or identification of its formulation with its
semantic content is built into the schema.

For a designated formulation `v`, the exact additional obligations are
`scope v`, `¬ analytic v`, and `¬ empiricallyVerifiable v`. The last two imply
failure of the disjunctive standard. The existing theorem then gives:

- if the norm holds, `v` is not meaningful;
- if `v` is meaningful, it is a counterexample to the norm.

A contradiction requires both that the norm holds and that `v` is meaningful.
Merely calling a sentence meaningless does not prove its negation. The schema
supplies none of these philosophical premises. A source-specific application
must distinguish factual significance from literal significance, conclusive
verification from weak verification, and practical verification from
verification in principle. In particular, failure of conclusive verification
does not supply failure of weak verification; nonempirical status alone does
not supply nonanalyticity. These are remaining reading obligations, not claims
about what Ayer actually asserts.

## Strongest proposal control remains open

A proposed linguistic rule need not be an asserted sentence within the domain
whose cognitive content it regulates. A faithful typed treatment would keep
sentences and proposals distinct, with an adoption relation on proposals and
a meaning predicate on sentences. Adoption of a proposal does not by itself
supply a meaningful sentence asserting that proposal's universal correctness.
Nor does a report that someone adopted it supply that assertion. A bridge
connecting these categories must be defended explicitly if used.

This differs from retaining an acceptable sentence while exempting it from its
own norm. The existing theorem
`TruthCore.Results.Logic.SelfApplication.ScopeNeeded.scopePremiseNeeded`
(`LOGIC-SELF-APPLICATION-SCOPE-NEEDED`) already shows that omitting scope permits
a norm to hold while an acceptable out-of-scope claim fails its standard.
`TruthCore.Results.Logic.SelfApplication.DemarcationOutsideConsistent.demarcationOutsideConsistent`
(`LOGIC-DEMARCATION-OUTSIDE-CONSISTENT`) provides the restricted-domain control.
Those are formal models, not evidence that Ayer adopts either reply. In the
restricted-sentence case, an acceptable out-of-domain sentence failing the
standard defeats the *unrestricted* norm; in the nonassertive-proposal case,
no such acceptable sentence has yet been supplied. Neither model proves the
proposal useful, faithful to ordinary language, or capable of ruling out the
case's metaphysical claims. The proposal variant therefore remains a live
rival obligation requiring its own sourced commitments and answer map.

## Source search, 2026-10-26

A public FIU faculty course syllabus links Joel Velasco's primary excerpt:

- Teaching context: https://faculty.fiu.edu/~harrisk/1261%20PHI3400%20Lesson%20Plan.htm
  (week 2, Canvas Readings, “The Elimination of Metaphysics”).
- Excerpt: https://joelvelasco.net/teaching/3330/Ayer-elimmetaphysics.pdf
  (three physical PDF pages; HTTP retrieval succeeded, 287511 bytes).
- Retrieved-byte SHA-256:
  `e8f75892ead36a8197cdb90459640e174f8ed06dcb769796a6a57d3167ccbebb`.

This records a retrieval lead, **not a verified passage witness or a license
to redistribute the excerpt**. `pdftotext` extracts only page separators.
The repository command
`python3 scripts/source_evidence.py web-hashes https://joelvelasco.net/teaching/3330/Ayer-elimmetaphysics.pdf --encoding utf-8 --pdf-pages 1:3`
fails with “extracted PDF text is empty (image-only pages need a different
witness)”. The PDF adapter performs no OCR (`docs/source-evidence.md`). No
passage was materialized and no reading is attributed from this scan.

The indexed teaching excerpt at
https://danielwharris.com/teaching/364online/weeks/13/Ayer.pdf
returns HTTP 404 through both browsing and curl. Random full-book scan hosts
and the already documented archive lending copies do not establish legitimate
hosting for this task. Search snippets, secondary summaries, and memory do not
substitute for reading the required pinned primary text. Secondary orientation
also raises the definition/convention reply; it does not license attributing
that reply or its precise scope without primary materialization.

Next work: obtain an admissible text-bearing primary excerpt of chapter 1 and
the 1946 Introduction, materialize it, inspect its immediate context, and fix
edition/page locators before adding source claims. Chapter 6 remains separately
necessary for the ethical theory. The strongest proposal reply and each
self-application bridge must be recorded independently; the existing generic
proofs need no restatement as new premises. No new inference was missing from
the repository; the unsatisfied boundary is sourcing and interpretation.
