# Correctness, independent criteria and the private diary

This bounded investigation reads the Anscombe translation of *Philosophical
Investigations* I.239–274. The source is
`WITTGENSTEIN-PHILOSOPHICAL-INVESTIGATIONS`; the byte-verified passage is
`WITTGENSTEIN-PI-PRIVATE-CRITERION-CONTEXT` (physical PDF pages 5–12, printed
88e–95e). Run
`python3 scripts/source_evidence.py materialize WITTGENSTEIN-PI-PRIVATE-CRITERION-CONTEXT`.
The university teaching excerpt was fetched twice with identical hashes.
Poppler includes fragments from adjacent cropped pages; the complete main
paragraphs, including the continuation of I.265 on 94e, remain readable.
No PDF or extracted translation is committed. Wayback's CDX search returned
no status-200 PDF capture; the save request timed out without a response, so
this witness has no archival fallback.

## The argument read

I.258 imagines a diarist introducing a sign by concentrating on a sensation.
The proposed remembered connection is challenged because the case supplies
no criterion separating correct from apparently correct application. I.259
contrasts a standard with an impression of a standard. I.265 considers
checking one recollection against an imagined dictionary or timetable:
the second recollection must itself be testable for correctness; multiplying
copies of one report does not provide that check. These are readings of
particular arguments, not a general assertion that memory always fails.
I.257 and I.260–262 also question the presupposed grammar, function and
technique of the sign. Reducing the passage to memory unreliability would
omit these concerns.

The surrounding text constrains stronger interpretations. I.241 distinguishes
agreement in language from agreement in opinions; it does not define truth
by majority verdict. I.243 distinguishes monologue from a language in principle
unintelligible to anyone else. I.244 distinguishes replacing crying from
merely describing crying. I.269 distinguishes thinking one understands from
understanding correctly. I.270–271 ask what difference a purported private
identification makes within an established use. These do not establish that
private sensations do not exist, that every solitary speaker is impossible,
or that whatever a community accepts is correct. No Kripkean skeptical
solution is attributed to Wittgenstein here. The present range is not a
complete reading of the book's rule-following discussion.

## The analytical result

`STMT-CORRECTION-CRITERION-EXACT-FACTORIZATION` is **stipulative analysis**, not
a source-derived formal claim. No corpus claim says Wittgenstein asserted
this theorem. The existing causal response-table models and moral-correction
records have different semantics; their vocabulary is not identified with
rule correctness.

Let `observe : State → Evidence` be the complete data allowed to a proposed
classifier, and let `Correct : State → Prop` be a separately supplied norm.
An exact criterion is some predicate `K : Evidence → Prop` satisfying
`K (observe s) ↔ Correct s` at every state. Such a criterion exists exactly
when states with identical data agree on correctness. The reverse implication
constructs `K e := ∃ s, observe s = e ∧ Correct s`. It needs neither classical
choice nor decidable correctness. It yields an extensional classification,
not an algorithm or an agent's knowledge of the norm.

The controls use two Boolean states with opposite correctness. Their two
reports are both positive in both states. No classifier using that whole
report pair is exact. Identity data do admit an exact classifier for the
same nonconstant norm. The pair can illustrate agreement or duplicated
recollection, but the model contains no speakers, histories, sensations or
social institution: it proves neither an impossibility of community nor a
possibility of a solitary private language.

## The discriminating fork and surviving rivals

Fix a particular projection `observe`. These commitments are incompatible:

1. Equal projected data can occur in two states that differ in correctness.
2. An exact correctness criterion uses only that projection.

This is a consequence of the characterization, not a ranking of its members.
An internalist realist may retain the first commitment and deny that all
correctness is exactly classifiable from the chosen data. A defender of exact
public criteria must defend correctness invariance under the **specified**
public projection, or enrich that projection. A defender of an independent
internal standard may enrich the data without adding another speaker. Each
remains a live philosophical proposal; the theorem supplies no actual
projection, no argument that its data are exhaustive, and no warrant for
trusting its classifier. Community agreement alone does not supply the
missing invariance. Nor does the theorem show that an internalist's proposed
extra norm is meaningful, accessible or independently justified.

The strongest private/internalist proposal is therefore not identified with
whatever presently seems right: it postulates a stable norm possibly
outrunning current checks. The strongest public/practice proposal is not
majoritarianism: it requires independently correctable applications in a
practice. Whether the text excludes the former or establishes the latter
needs a richer account of use, independence and warrant. That is the candidate
`WITTGENSTEIN-CORRECTNESS-AND-INDEPENDENT-CRITERIA`, not a discharged premise.

## Premise and verification boundary

The theorem has no philosophical premises; it universally quantifies the
stipulated mathematical profile. Root-path open premises: retained all,
added none, removed none; route costs unchanged. It settles no Catholic-case
node. The dossier and successful derivation attempt record analytical work,
not source-interpretive or philosophical closure. Development diagnostics
and delivered-head CI evidence belong in the PR; until Comparator passes,
this note is not a claim of mechanical certification.
