# Research review calibration cases

Teaching examples from modal-spine cycles 2–3, subordinate to the [systematic research loop](../systematic-corpus-loop.md). They exercise reviewer and synthesizer judgment; they add no truth status, schema, tracker or code gate. Model selection is empirical and role-specific. Use a bounded comparison when choosing or revising an assignment, not a compulsory benchmark every cycle; these examples establish no model-performance claim.

## Preparing a comparison

Give each fresh reviewer only selected candidate paragraphs below, their notation and frozen primary-source references (including needed imports). Do not send this whole note, the answer key, provenance notes, previous verdicts or old review transcripts. Ask for a decision on each claim, the exact evidence, and a minimal repair if needed. For a synthesizer comparison, ask instead for a short integrated assessment that preserves supported findings and repairs unsupported ones. Keep evidence access and budgets comparable and record the model/version and role.

Include correct controls as well as errors. Score substantiated errors missed, unsupported findings/false alarms, successful repairs without newly introduced errors, and elapsed time plus available cost data. Record denominators and evidence for disputed scoring in the existing handoff or run log; do not grade a philosophical preference as truth. Compare review and synthesis separately. Once a model has seen these examples or their answers, use unexposed variants with independently checked answers; repetition measures familiarity, not generalization.

## Candidate briefs — copy selected cases only

Notation for the frame cases: `F2′ = EuclideanAt frame w`, `F2 = Euclidean frame`, and `4@w = TransitiveAt frame w`. Read their quantifiers in [the frame definitions][frame] and [the local conditions][local]. For deletion cases, `D(w)` abbreviates `∀ x, Concrete x → ExistsAt w x → ∃ u, access w u ∧ ¬ ExistsAt u x`: individual deletion relative to `w`, not joint deletion of the roster. This abbreviation is local to the exercise.

### A. Local frame consequence

“`F2′` and `4@w` imply that every successor of `w` is Euclidean. Reflexivity at `w` is unnecessary for this conclusion.” Sources: [frame][frame], [local conditions][local], [proof][local-proof].

### B. Local and global difference

“If `F2′` holds but `F2` fails, `4@w` must fail.” Sources: [frame][frame], [local conditions and controls][local], [proofs][local-proof].

### C. Deletion scope

“Every actual concrete individual can be absent at some world accessible from `actual`, so no concrete individual exists necessarily relative to any world.” Test this inference using `D(actual)` and the five-world `Control.faithful`. Sources: [origin model][origin], [necessity definition][necessity].

### D. Adding an assumption

“Strengthen deletion to `∀ v, D(v)`. This excludes the necessary individual at the temporal witness, so the existing five-world countermodel survives only vacuously and no longer challenges the original omission of `F2′`.” Sources: [origin model][origin], [control proof][origin-proof], [`earlierNecessary`][temporal-proof], [necessity][necessity].

### E. Scope of a witness

“The five-world model satisfies the four encoded origin commitments, actual reflexivity, presence-to-existence, inert emptiness and the possible contingent-free past, while `EuclideanAt` and `NecessaryConcreteAt` fail at `actual`. It witnesses non-entailment for that bundle. Applicability of its stipulated absences, temporal profile and access biconditional to metaphysical possibility remains open.” Sources: [origin model and certificate][origin], [control proof][origin-proof], [statement][origin-statement].

### F. Survey conclusion

“A finite survey considered unverified sketches of potentiality, ersatz and chained-tolerance accounts. No completeness argument or verified attribution was supplied. Together with the local frame theorem, this establishes that no serious rival accepts `F2′` while rejecting `F2`; the weakening has no dialectical value.” Treat the described survey limits as supplied facts, not verified claims about those accounts. Sources: [frame][frame], [local conditions][local], [local proof][local-proof].

### G. Definition coverage

"The origin-access statement links `6f7a4ccc-10de-52fb-af44-41dcb793d8c9`, so its origin and tolerance vocabulary has adequate definitions." Inspect what the link actually defines. Sources: [statement and links][origin-access-statement], [linked definition][necessary-if], [origin interface][origin].

### H. Provisional assessment

“On 2026-11-10 at the supplied evidence revision, for the modal-spine inert-emptiness arrival, the formal weakening from global to actual-world Euclidean access is supported, but its metaphysical warrant and dialectical advantage remain underdetermined. The encoded origin countermodel survives; the access biconditional, stipulated absences and stronger deletion premise remain live objections to its applicability. I retain that qualified assessment without changing frontier closure. A defended rival account or justified persistence/deletion bridge would reopen it; the next discriminating step is to assess that bridge.” Sources: [frame][frame], [weakening and controls][frame-proof], [origin model][origin], [origin proof][origin-proof].

## Coordinator answer key — withhold from candidates

These answers assess the stated claims at the frozen revision. Evidence can correct an answer; neither this key nor reviewer agreement is philosophical authority.

| Case | Evidence-backed resolution |
|---|---|
| A | Accept. `euclideanOnSuccessors` takes only `EuclideanAt frame w` and `TransitiveAt frame w`. From `wRv`, `vRa`, `vRb`, local transitivity gives `wRa` and `wRb`; local Euclideanness gives `aRb`. Adding reflexivity is a false alarm. Do not import the different hypotheses of the existence-transport theorem. |
| B | Reject. `Control.appendix` and `controls` give `F2′ ∧ 4@w ∧ ¬F2` at `actual`. Only `far` has the offending extra edge, `far → actual`; `actual` does not see `far`. Repair: local transitivity forces Euclideanness at successors, while global failure can remain outside them. |
| C | Reject the world-quantifier shift. In `faithful`, `actual` accesses `bMinus` without `a` and `aMinus` without `b`, so `D(actual)` holds. Yet `b` exists at `plus` and every successor of `plus`: `actual`, `plus`, `bMinus`, `bPlus`; its sole absence is at inaccessible `aMinus`. Repair: deletion at `actual` excludes an actual necessary concrete individual, not necessity at other worlds. This is direct evaluation of `exists'`, `far` and `NecessaryAt`, not a new registered theorem. |
| D | Reject the substitution of assumption bundles. `∀ v, D(v)` fails in this witness at `plus`. `earlierNecessary` supplies an existing necessary concrete individual at the temporal witness from the original presence, inertness and contingent-free-past conditions; worldwise deletion contradicts it. Thus the strengthened bundle is inconsistent, while the original bundle retains its actual model. Repair: report that conditional incompatibility and leave independent warrant for the stronger premise open. This deduction does not make the old countermodel vacuous or defeat the rival under its original commitments. |
| E | Accept at the stated scope. `faithfulControls : Control.Certificate` supplies the conjunction and failed conclusion. Unknown metaphysical applicability does not invalidate the mathematical non-entailment. The origin biconditional's “if” half, rigid identity, absences and temporal assignment are encoded commitments; no result covers every origin-essentialist interpretation or worldwise deletion. |
| F | Reject the universal and warrant claims. The theorem restricts frame structure, not which philosophical views are serious; the supplied survey has no coverage or attribution warrant. Repair: “No defended example was found within this bounded survey; the formal weakening is strict, while its dialectical benefit remains unresolved.” Do not score a rival as unserious merely because the reviewer dislikes it. |
| G | Reject. The linked record defines `NecessaryIf = □(G → □G)` for an arbitrary world predicate. It does not define world/individual origins, tolerance or origin-based access. Repair the mapping to the actual `OriginInterface` and `OriginDeterminesAccess` meanings; flag the missing semantic coverage. An existing JSON link does not supply it, and this defect does not invalidate the independently checked control proof. |
| H | Accept as an explicit provisional judgment with reasons, objections, scope and reopening conditions. The lack of a preferred metaphysical winner is not a defect. Preserve both the formal result and unresolved warrant; do not promote the assessment to establishment or silently replace “underdetermined” with a stronger conclusion. |

## Frozen source references

All references below use [PR #1367's evidence head](https://github.com/moritzbrantner/truth-core/commit/8e63e617ae36021f981d65cd932442933c41b827). Send only references needed for the selected brief and their import dependencies. The [cycle-2 surrogate at the PR #1365 baseline](https://github.com/moritzbrantner/truth-core/blob/27d2eab83f789dd6e7726e7f64f7c5de5305b299/TruthCore/Causality/ToleranceOriginRival.lean) preserves the earlier empty-world interpretation boundary. The [cycle-3 frame attempt](https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/corpus/attempts/ca49ceb8-a02e-4f49-8dd8-12704afb1220.json) and [origin attempt](https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/corpus/attempts/f2b3c229-43cb-4dd5-939e-bce66655fa78.json) explain the provenance; their verdicts and review history are for coordinators, not blind candidate packets. Candidate claims are calibration formulations, not quotations of those records.

[frame]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/TruthCore/Causality/ActualEuclidean.lean
[frame-proof]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/TruthCore/Results/Causality/ActualEuclidean/Solution.lean
[local]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/TruthCore/Causality/ActualOnlyEuclidean.lean
[local-proof]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/TruthCore/Results/Causality/ActualOnlyEuclidean/Solution.lean
[origin]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/TruthCore/Causality/OriginToleranceIdentity.lean
[origin-proof]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/TruthCore/Results/Causality/OriginToleranceIdentity/Solution.lean
[temporal-proof]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/TruthCore/Results/Causality/InertEmptiness/Solution.lean
[necessity]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/TruthCore/German/Kant/CosmologicalInference.lean
[origin-statement]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/corpus/statements/745d0d4c-71f3-4593-83eb-a719eeaf8912.json
[origin-access-statement]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/corpus/statements/5389a062-70dc-4802-a163-92faa1f1c915.json
[necessary-if]: https://github.com/moritzbrantner/truth-core/blob/8e63e617ae36021f981d65cd932442933c41b827/corpus/definitions/necessary-if-existent-profile.json
