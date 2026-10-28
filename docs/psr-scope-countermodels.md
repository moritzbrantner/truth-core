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

## Intrinsic existence reasons: the positive case and its parity test

This source follow-up concerns `STMT-NECESSARY-GROUND-HAS-INTRINSIC-REASON`,
not a new interpretation of the model's `intrinsic` constructor. Reuse search
and its dossier recover the existing Leibniz readings and explanatory-regress
attempt. The complete pinned Elwes witness `SPINOZA-ETHICS-ELWES-FULL` was
materialized and read at I definitions 1–8, axioms 1–7, propositions 1–11,
including I8 notes and all I11 proofs and note. The Latin witnesses
`AQUINAS-ST-I-Q3-A4`, `AQUINAS-ST-I-Q44-A1` and Latta
`LEIBNIZ-MONADOLOGY-31-45` were also materialized and read. These are source
interpretations and an uncertified philosophical comparison, not additional
corpus claims or a Lean argument.

**What the strongest positive proposal says.** An intrinsic reason answers
why this actual being exists by what it really is, without a distinct producer
or a further item that joins a separately specifiable nature to existence.
It does not mean that the being first produces itself. Spinoza I definition1
explicitly interprets causa sui through essence involving existence;
definition7 distinguishes determination through one's nature from external
constraint. His I6 corollary denies external production of substance; I7
then moves to existence belonging to substance's nature. That move requires
explanatory exhaustiveness: independence alone would also fit brute existence
if existence need not have a reason. It is not an independent proof of PSR.
I8 noteII makes the cause-of-each-individual demand and internal/external
exhaustion explicit.

The strongest foundation reply is therefore more substantial than “it exists
necessarily.” Suppose an actual independent witness has been established by a
separate argument, and its real nature has independently been shown to be
subsistent actuality rather than a recipient whose existence needs another
actualizer. Understanding that nature could explain why its existence is
underived: there is no distinct received actuality left for a producer to
supply. An explanation need not re-prove all its presuppositions. Starting
with an actual witness does not make every explanation of it circular, just
as explaining an actual figure's property can presuppose the figure.
However, neither the witness nor the modal necessity predicate establishes
that account of its real nature. Nor does absence of a composition gap alone
establish that its nature is a sufficient reason why it exists at all. This
last positive explanatory step remains open.

Aquinas q3a4 supplies an importantly different route: its first proof excludes
caused esse from essential principles alone, then uses first efficient
causality to infer identity; its second uses act/potency. Neither proof says
that efficient self-production explains God. The reply ad2 distinguishes
knowing the truth that God exists from knowing the divine act of being or
nature. Consequently this proposed essential explanation may exceed what
those arguments make intelligible to us. q44a1 ad2 explicitly retains causes
of necessities; necessity does not waive the reason demand. Its ad3 separates
mathematical abstraction from the being of mathematical subjects. These
passages support keeping the questions distinct, rather than identifying
Aquinas' esse with Spinoza's conception of substance.

**A new constraint from Spinoza's own near-misses.** I8 noteII says the nature
of humanity does not explain why exactly twenty humans exist, and the
definition of a triangle specifies no number of triangles. I11's second proof
says a triangle's existence comes from the order of extended nature, not its
figure's nature. Thus an essential account must reach the actual individual,
including any multiplicity or individuation left unexplained. A generic
conditional “whatever is N exists necessarily” is insufficient if nothing
establishes an actual N, and “this actual thing has label N” adds no reason.
This connects to the individuality gaps investigated in #681/#684 and the
Compendium/De ente audit #683/#685, without closing them: excluding several
instances of one generic nature does not exclude two different whole essences,
each claimed to explain its own existence. A uniqueness inference would still
need to exclude or identify those different essences.
Conversely, where an actual witness is independently available, demanding a
second existence proof is stronger than demanding explanation. The relevant
question is whether its independently characterized nature genuinely explains
this witness's actuality, rather than merely redescribes it.

Necessary mathematical properties illustrate how an essence can explain a
property without an earlier efficient cause: a Euclidean triangle's angles
summing to two right angles follows from geometrical structure and background
postulates. This is an illustrative analogy, not a new historical attribution
or a claim that the property follows from the word triangle alone. It supports
the intelligibility of nonproductive explanation, but does not establish a
concrete triangle, the background geometry, or a concrete necessary being.
No generally accepted concrete example of intrinsic explanation of existence
itself is supplied here. The proposed divine or Spinozist substance is the
disputed example, not independent confirmation of the proposal.

**The independent debts in the existence proofs.** Spinoza I11's first proof
uses I7; its second strengthens the explanatory demand to nonexistence too,
excludes an external preventing reason, and denies an internal contradiction
in an absolutely infinite perfect nature. The absence of an internal
contradiction is a substantive commitment, not a consequence of calling the
nature perfect. The third proof and note connect degree of reality with power
of existence and appeal to our existence. Ordinary observations of stronger
agents or enduring objects do not independently warrant that unrestricted
reality-to-existence-power bridge. The note explicitly distinguishes externally
produced things from substance, so an induction from familiar produced things
would miss its intended domain. Leibniz §§33–35 provides analytical reasons
for necessary truths; §§44–45 additionally connects real possibility with
actuality for the proposed necessary being. Mathematical analysis alone does
not justify that additional bridge. Neither author's positive case is fairly
reduced to an arbitrary stable tag, but their substantive bridges remain
contestable.

**Parity with a positive infinitist rival.** A foundation theorist may say
that an intrinsic real nature ends explanatory deferral without an arbitrary
unexplained link. A serious infinitist may instead propose that the whole
infinite structure, rather than a local predecessor token, intrinsically
explains its existence. Both may allow explanations to presuppose actual
subjects. Therefore “every item in your chain still needs explanation” does
not by itself discriminate them if the foundation's own intrinsic account is
accepted without an independent adequacy argument. Equally, a bare chain of
conditional dependencies does not acquire such an account merely through
infinity. A brute whole accepts an unexplained fact; a structural account
claims an explanation and owes a defense. These are different rivals.

The narrower useful commitment is **individual adequacy**: an alleged intrinsic
reason must independently characterize the actual subject in a way that
explains its actuality and any relevant individuation, not merely its modal
status or properties conditional on instantiation. This is a proposed
philosophical test, not a sufficient formal criterion or a new Boolean field.
It applies equally to a simple foundation and an infinite whole. It does not
require every explanation to be external or every explanans to be known.
Nothing here independently establishes transitivity, asymmetry or
well-foundedness of explanation; applying those structural properties to
intrinsic explanation would need further defense. Ordinary property
explanations motivate the possibility of intelligible nonproductive reasons,
while generalizing them to concrete existence remains the decisive disputed
step. A rival that accepts an independently characterized real nature as
explanatory but allows the infinite whole the same resource remains unrefuted.

Intended and actual root-premise delta: **zero**. No source claim, statement,
definition, theorem, argument, model or closure flag changes. Retained are the
unrestricted existence demand, actual-witness requirement and distinction
between efficient causation and reasons. The gain is a positive proposal and
a symmetric individuation test, not a defense of intrinsic adequacy. Stop this
line until an argument independently establishes that a particular actual
nature, or a particular global structure, meets that test; another necessity
lemma or stable explanation-token assignment would repeat known boundaries.
