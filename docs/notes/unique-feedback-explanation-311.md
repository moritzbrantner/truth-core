# Unique feedback and whole-chain explanation (#311)

The state equations `a = !b`, `b = a && b` have one satisfying
Boolean pair, `(true,false)`. Their gates are nonconstant: negation
changes across its two inputs; conjunction changes when either input varies
with the other held true. These are logical constraints. They are not
world-local causal edges, temporal evolution, pure copying of plans, or
borrowed instrumental powers. Sensitivity is a truth-table property, not
an assertion that each single-bit perturbation at the solution changes
both outputs.

| a | b | First equation | Second equation |
|---|---|---|---|
| false | false | fails | holds |
| false | true | holds | fails |
| true | false | holds | holds |
| true | true | fails | holds |

`UniqueFeedback.Controls` certifies sensitivity, the satisfying witness,
and equality of every consistent state with it. The proof does not select
an observed boundary value or assume uniqueness. It eliminates the other
three states. This is a nonvacuous satisfiability/uniqueness control; no
explanation predicate is present.

## Reuse and nonduplication

- Merged #299's `EssentialPowerUnderdetermined.essentialPowerUnderdetermined`
  gives all-on/off solutions and cut responses. Its local rule is preserved.
- `LocalObservationSelectsSolution.localObservationSelectsSolution` supplies
  determinacy only after fixing an observation. This control needs none.
- `RegressDomains.CycleAndConverseBoundary` admits equal least/greatest fixed
  points on an intrinsic self-loop. That supplied intrinsic predicate is not
  used here; neither fixed-point selection convention is used.
- Pending #619 owns complete-presence-history contrasts and differing reason
  assignments on the same memberwise structure. It is comparison evidence,
  with no dependency on its unmerged declarations. Those assignments are not
  repeated here.

No existing philosophical conclusion is imported as a fresh premise.
The previous theorems are comparison evidence; the new result proves only
its own distinct finite control.

## Surviving explanation question

Mathematical solution multiplicity cannot be the entire objection to logical
feedback: the constraints here are satisfied and have no second solution.
This does not prove an adequate ontological explanation or prove its absence.
The strongest rival says that the intrinsic global structural fact explains
the satisfying state. A brute global fact and a non-well-founded grounding
account are distinct further answers. None is eliminated by this table.

To reject the structural answer, one must specify which obtaining fact needs
explanation, what counts as sufficient explanation of it, and why satisfying
these global constraints does not meet that norm. A whole-series PSR or a
contrastive requirement must enter explicitly; neither automatically implies
externality or rules out explanatory circularity. No notion of explanation
is defined to prohibit loops. Conversely, uniqueness alone supplies no
independent defense of those norms or of the global structural answer.

The issue's original plans bootstrap still requires a richer interpretation:
these gates are not an inventor-free copying history. No inference from lack
of an inventor to impossibility, from consistency to metaphysical possibility,
or from explanatory dissatisfaction to an original causal source is made.
EXP-SCOPE, EXP-LOCAL-TO-GLOBAL, EXP-NONCIRCULAR and EXP-ULTIMATE remain open.
Source attribution remains paused; no historical claim is added.

## Premises, verification and service evidence

Intended and actual root-path open-premise delta: zero. The closed certificate
has no ordinary premises and no new root connection. All root philosophical
premises are retained; none is discharged.

The Challenge was frozen before proof work, SHA256
`80249ef71f3aa529bc97d4343b15e5af74788f8de1b0b631226a2b897a91325d`.
The shared persistent service accepted repeated full-content edits without
mutating its checkout/imports, at workspace
`/home/brantner/privat/truth-core-sprint-proof`, head
`75192b1c3efdf19f25601e52a06116e706420f11`, session `causal-harvest`,
path `Scratch/issue311.lean`. HTTP 200, final content SHA256
`d9a641f7007215a7884b0ec70d00651952546916e250d2df5e99cb870ae8c949`;
no errors and `#print axioms` reports no axioms. Initial implicit unfolding
failed; explicit unfolding and direct Boolean contradiction proofs fixed it.
Lease wait was 0.000010s, first request 0.836s, corrected warm request 0.230s.
Retain the warm serialized service for small edits; no second session or
benchmark rerun was needed. These are interactive diagnostics, not final
Comparator verification.

Canonical final CI owns build, binding, Comparator and NanoDa. After build,
reproduce the result gate with
`python3 scripts/worker_env.py -- scripts/verify-result.sh UNIQUE-FEEDBACK-CONTROL`.
The attempt record retains rejected interpretations and precise evidence.

## Explanatory-adequacy audit: what an endless series is asked to explain

The renewed Agrippa/Münchhausen question is about whether a regress supplies
what an inquiry requires, not whether an infinite set is contradictory. The
explanatory version in #311 has a specific primary-source argument. The pinned
Latta translation of *Monadology* §§31–45 was materialized and read in full
(`LEIBNIZ-MONADOLOGY-31-45`, text SHA256
`48c8019d588af3c5d262323ea365382be7021bf4f4ee23f7f0b68eb6650b6d04`).
This is an explanatory argument, not a historical attribution of Agrippa's
modes to Leibniz and not an inference from skeptical suspension to causal
impossibility.

### The source's demand and proposed answer

1. **Scope, §32:** a real/existing fact or true statement calls for a sufficient
   reason why it is so rather than otherwise. A reason may be unknown to us;
   lack of discovery is not absence of explanation. This is the stated PSR,
   not something the existing mathematical controls establish.
2. **Necessary truths, §§33–35:** their reasons are sought by analysis into
   simpler truths, terminating in primary identity principles whose opposites
   contradict. This is a proposed nonarbitrary analytical terminus, not a
   license to stop at any favored assertion. Its legitimacy still needs
   defense against rival epistemologies.
3. **The explanandum, §36:** contingent truths include the sequence or
   connection of created things. The example of the present act of writing
   allows infinitely detailed efficient and final causes. Thus the argument
   does not simply demand finitely many prior events or deny infinite detail.
4. **The insufficiency step, §37:** those further contingent details again
   require analysis for their reasons. Leibniz takes that renewal to leave
   the final question unsettled and concludes that the sufficient final
   reason lies outside the contingent series, however infinite it is.
5. **Proposed ground, §§38,45:** the conclusion is a necessary substance;
   §45 describes this proposed necessary being as having the reason for its
   existence in itself. This is not efficient self-production. Necessary-truth
   analysis in step 2, a de re modal existence predicate, and a sufficient
   intrinsic existence reason are not interchangeable.

These are sourced argument steps and open commitments, not a newly certified
inference application. The existing
`STMT-LEIBNIZ-SERIES-SUFFICIENT-REASON` already records the final
outside-the-series conclusion. The new readings expose what drives it rather
than registering the desired conclusion as another bridge assumption.

The distinctive criticism is **explanatory deferment**: an account of why
this contingent reason obtains merely introduces a further contingent reason
whose obtaining remains owed an account under the same norm. An endless
sequence of these local answers does not, *on Leibniz's stated view*, finish
the original why-question. Its length alone is not the defect; the alleged
unresolved explanatory dependence is. The burden is therefore to defend the
whole-sequence demand and why no admissible global or non-well-founded account
can satisfy it, rather than to point at infinity or assume that all adequate
explanation has a finite proof tree.

### What is already checked, and what remains a philosophical premise

| Existing certificate | What it settles | What it leaves open |
| --- | --- | --- |
| `TruthCore.Results.Causality.UniqueFeedback.controls` | Nonconstant global equations can have a unique consistent solution without observed boundary data. | Why these equations obtain; whether their structural fact is an intrinsic sufficient explanation. |
| `TruthCore.Results.Modal.HistoryContrastive.controls` | The same infinite memberwise causal/explanatory labels admit a necessary nondiscriminator or a contingent internal discriminator. | Whether discrimination is required or sufficient; whether the internal marker explains its own obtaining. |
| `TruthCore.Causality.BruteFoundationExplanations.necessaryReasonAndNecessitation` | A necessary reason plus explicit necessitation makes the specified individual's existence necessary. | Whether adequate explanation necessitates; why the full reason is necessary; independent sufficiency of a proposed necessary ground. |
| `TruthCore.Logic.Regress.Graph.grounded_eq_lfp` and `TruthCore.Results.Logic.RegressSchema.regressSchemaPackage` | Inductive finite grounding is the least fixed point, distinct from a source-free all-on successor assignment in the greatest fixed point. | Why actual power, epistemic warrant or complete explanation must meet that inductive norm. |

None needs to be reproved here. In particular, the Boolean uniqueness control
is not a counterexample to the *source's whole-series PSR*: it contains no
adequacy interpretation. Conversely it prevents dismissing a global-structure
reply merely because local copying equations can have multiple solutions.
The history discriminator is a separate minimal test, not the answer to the
stronger question of why its own contingent premises obtain.

### Strongest replacement accounts face the same question

These are explicit rival answer profiles, not new historical attributions or
certificates of metaphysical possibility.

| Account | Positive answer offered | Commitment it rejects or must defend |
| --- | --- | --- |
| Leibnizian final reason | The contingent order has a sufficient reason outside that order, in a proposed necessary being with an intrinsic reason. | Defend unrestricted/whole-series scope, the deferment-to-externality step, actual instantiation and intrinsic sufficiency. Necessity alone does not discharge these. |
| Memberwise sufficiency | An account of each member and its relations accounts for the series; there is no additional obtaining fact left over just by collecting the members. | Defend that sufficiency and the treatment of totality. The reply challenges the independent whole-series explanandum, not simply the existence of a first event. |
| Intrinsic global structure | The actual laws/whole constraints explain their jointly determined state, rather than one member originating it. | Explain or justify primitiveness of the constraints' obtaining, or defend an intrinsic account of that obtaining. A unique solution relative to supplied constraints establishes neither adequacy nor its absence. |
| Non-well-founded explanation | A whole pattern of explanatory dependence can be adequate without an inductive terminus. | Give a non-question-begging adequacy criterion and address vicious circularity/deferral. An infinite graph or local label assignment alone does not establish this reply. |
| Brute global fact | The complete obtaining contingent structure is a primitive fact, not an unexplained gap within a claimed total PSR account. | Reject or restrict the PSR openly. This leaves the why-question unanswered on the PSR standard; it does not become logically inconsistent merely for declining that demand. |

The first account is held to the same standard: calling a ground necessary,
self-existent or divine does not by itself show why its nature is instantiated
or why its intrinsic reason is sufficient. §45 proposes such an answer; it is
not established by the notation `NecessaryAt` or by the source's assertion.
Likewise, an epistemic foundationalist may defend noninferential warrant, an
infinitist available reasons, or a coherentist a holistic criterion. Their
justificatory standards must not be imported into ontic causation without an
independently defended cross-domain bridge.

### Exact open obligations and premise comparison

- **EXP-SCOPE:** defend why the contingent sequence's obtaining is a live
  explanandum beyond the supplied local facts, and which PSR applies to it.
- **EXP-LOCAL-TO-GLOBAL:** decide whether memberwise explanation, together with
  explicit totality/closure principles, answers that question. Neither a
  predecessor count nor a copied value is a sufficient argument.
- **EXP-NONCIRCULAR / EXP-ULTIMATE:** defend the exclusion of a global intrinsic
  or non-well-founded final reason rather than build externality into the word
  explanation. §37 takes the outside-the-series step; the rival can contest it.
- **Intrinsic adequacy and actuality:** establish the proposed necessary
  ground and its reason, without turning necessary status into an existence
  proof or an exception to the universal demand.
- **ACT-GROUND and temporal scope:** remain separate. Explanatory
  insufficiency does not itself show that a source-free causal system cannot
  act, and neither result would by itself forbid an unbounded temporal past.

Intended and actual root-path change: none. All 63 counted open premises and
the eight route costs are retained; no argument/result or root connection is
added. The five source readings are prose-only and do not certify the norms
they report. The dossier-linked attempt and the
`CONTINGENT-SERIES-EXPLANATION-ADEQUACY` candidate preserve the unresolved
burden. The next decisive task is an argument for or against that norm on a
shared global-structure case, rather than another solution-counting example.
