# Existence-PSR scope: two countermodels

This is a small, axiom-free **model-theoretic test**, not an assertion that the
principle of sufficient reason is true. It advances the distinction in #312 and
retains the separate causation and explanation questions in #310 and #311.

## Reuse and formal boundary

`TruthCore.Explanation.ExistencePSR` reuses `Ontic`, `ContingentAt` and
`NecessaryBeing` from `TruthCore.German.Kant.CosmologicalInference`. An
`ExistenceFact.fact x` is a tagged candidate proposition, true at world `w`
just when `ExistsAt w x`. The *explanation* relation has type
`World → Reason Being → ExistenceFact Being → Prop`; the separate causal
relation remains `Ontic.Causes : World → Being → Being → Prop`.

`Sound` prevents explanations for false existence facts. It does **not** impose
a philosophical test of explanatory sufficiency. `ExistencePSR` is universal
over *existence facts*, not over every actual truth. `ContingentPSR` covers
only actual individuals with an accessible world in which they fail to exist.
`EveryExistentExternallyCaused` instead requires a distinct actual causal
predecessor for each individual.

## The models

The advertised theorem `psrScopeBoundary` proves `PsrScopeBoundary`, whose
type certifies exactly this, for two universally accessible, sound models on
two Boolean worlds and two candidate individuals:

- **Case 1:** `ExistencePSR` holds and a necessary individual exists at world
  `false`, yet `EveryExistentExternallyCaused` fails: *at least one* existent
  at some world lacks a distinct existing cause.
- **Case 2:** `ContingentPSR` holds, `true` is contingent at world `false` and
  a necessary individual exists there, yet `ExistencePSR` fails: *some*
  existent at some world lacks any explanation.

The type does not certify that no existent is caused, that any explanation is
intrinsic, or which existent in case 2 is unexplained. The concrete witnesses
in `Solution.lean` have those stronger properties, described below for
orientation only:

1. **Existence-PSR without external causation of every existent.** Only
   `false` exists, at both worlds. Its existence has a stipulated `intrinsic` reason at each world.
   There are no causal arrows at all (a witness property, not certified).
   `NecessaryBeing` and `ExistencePSR` hold; `EveryExistentExternallyCaused`
   does not.
2. **Contingent-only PSR without existence-PSR.** The individual `false`
   exists in both worlds, but `true` exists only at world
   `false` and has a stipulated `circumstance` reason there. The necessary
   individual has no assigned explanation anywhere (a witness property, not
   certified). `ContingentPSR` holds non-vacuously and a necessary individual
   exists, but `ExistencePSR` fails.

Consequences of the certified type:

- An unrestricted-over-existents PSR does *not by itself* entail that every
  existent has been caused by some **other** existing individual. A claim
  that every explanation requires such a distinct cause needs an independent
  bridge.
- A contingent-only PSR does *not by itself* entail the existence-PSR, even in
  a model that has a necessary individual. (The certified type does not
  locate the unexplained existent; that the witness leaves the necessary
  individual unexplained is not certified.) An opponent applying an explanatory demand to a necessary being must
  identify why that demand applies if their accepted PSR was contingent-only.
- Conversely (an uncertified remark, not part of the theorem), someone who
  grants brute contingent existence yet demands that necessary existence have
  a further explanation owes an **independent scope-sensitive reason** for
  this asymmetry. The countermodels do not refute that possible reason.

## Premise comparison and frontier

- **Retained:** world-relative existence, modal contingency/necessity and
  distinct causal relations, with universal accessibility for both models.
- **Added as definitions, not metaphysical premises:** tagged existence facts,
  candidate explanation tokens, soundness, the two PSR variants, and the
  separate external-cause predicate.
- **New open philosophical obligations:** whether intrinsic explanations can
  be sufficiently informative and non-circular; whether a fully unrestricted
  PSR applies to necessary existence and to every other kind of fact; whether
  an explanation must be causal or well-founded; and whether a necessary
  existent is actual. Nothing here proves that a God exists.

This result discharges the *formal non-entailment* tests only. It connects
conceptual alternatives around #312; it does not close an argument to the
Truth Core root. The infinite borrowed-power actuality and whole-chain
explanation investigations (#310, #311) remain open.

## Necessitarianism boundary: reuse audit (#312, 2026-10-28)

A fresh inventory found that the tempting necessity-transfer proof is already
present. No additional theorem is needed to state that transfer. The precise
reuse is:

| Question | Existing Lean evidence | Additional commitment still needed |
| --- | --- | --- |
| Does a necessary reason yield a necessary selected existent? | `Causality.BruteFoundationExplanations.necessaryReasonAndNecessitation` | `NecessitatesExistenceAt` for that reason and that same existent, in addition to `NecessaryReasonAt` |
| Is actual contingency compatible with both those conditions? | `Causality.BruteFoundationExplanations.contingentExcludesNecessaryNecessitatingReason` derives `False` | Applicability of both conditions, rather than their stipulation |
| Do necessary abstract reasons plus sound local explanatory coverage supply a necessary concrete being? | `Causality.BruteFoundationExplanations.abstractReasonCoverageInsufficient` retains coverage, soundness and necessary reason truth but lacks a necessary concrete individual | A real reason-to-bearer or reason-to-effect bridge; a reason token is not an ontic individual |
| Does worldwise existence-PSR supply one stable explanation token? | `Modal.WorldwiseExplanation.worldwiseWithoutStable` refutes that shift; `worldwise_and_invariance_implies_stable` states a sufficient repair with an existence witness | `ReasonInvariant` for the selected being; even a stable token is not modal sufficiency |
| Does the same act force the same effect? | `Results.Modal.SelectedEffectBridge.selectedEffectNecessary` uses stable output; its varying-output control retains same act and local uniqueness | Cross-world output stability, or the separately explicit fixed-full-conditions response law |
| Does a necessary reason discriminate histories? | `Modal.HistoryContrastive.constant_not_discriminating`, `internal_discriminates`, and `necessary_discriminating_excludes_rival` | An entailing discrimination requirement; the successful internal reason is contingent |

The full namespace prefix is `TruthCore`. These are existing theorem and
control names, not new results or a claim that every helper has a separate
Comparator result record. The reason sorts in `ExistencePSR.Model` and
`BruteFoundationExplanations.ExplanationProfile` differ. The table compares
explicit questions; it supplies no definitional identification between their
reason tokens, bearer beings or explanatory relations.

The strongest necessitarian case adds two substantive commitments: every
selected adequate reason is necessary, and adequate sufficiency entails the
selected effect throughout the accessible worlds. The first row then already
establishes necessity **of that effect**. Universalizing that conclusion over
existence facts still does not establish necessity of every true proposition:
`ExistencePSR` quantifies over existing individuals, not arbitrary facts. A
full modal-collapse claim needs its own scope bridge. Factivity, which rules
out an explanatory assignment to a false explanandum at the same world, is
weaker than that cross-world entailment requirement.

Two replies remain distinct. A nonnecessitating explanation can retain a
necessary reason without the strong entailment condition; the abstract-reason
control tests this formally but does not demonstrate metaphysical sufficiency.
Alternatively, a full reason can include contingent conditions; necessitation
then does not give necessity of the effect unless the full reason is itself
necessary. The history and selected-act controls expose these different
commitments without ranking either reply as true. Merely calling a reason
"sufficient", "intrinsic" or "complete" settles none of those adequacy questions.

This audit rejects a duplicate proof that only packages the already explicit
bridges. It introduces no historical attribution, new theorem, new metaphysical
premise or root connection. All 63 reaching-root open premises remain; the eight
route costs remain 31/32/36/38/39/39/40/41. The unresolved task is independent
defense or rejection of the necessity, entailment and scope commitments, not
further transcription of their consequence.
