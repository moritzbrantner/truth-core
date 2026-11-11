---
phase: batch-1
premise: `STMT-ACT-SIMPLY-PRIOR-TO-POTENCY`
rival: `STMT-POTENCY-PRIOR-TO-ACT` (*Met.* XII.6, 1071b22-28: the reputable view; theologians from Night); its sourced bundle `STMT-NIGHT-UNPRECEDED-POTENCY-ACTUALIZED` (the unpreceded potency is actualized)
class: inconsistency, partial: Aristotle's reply covers only potencies being actualized (#352, finding 4)
status: open; sourced; Night bundle eliminated given open {`STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-BEING-IN-ACT`, `STMT-NOTHING-MOVES-ITSELF-IN-SAME-RESPECT`, `STMT-ACTUAL-MOVER-IS-SIMPLY-PRIOR`} (`GENERATION-FROM-NIGHT-REFUTED`, #497); the bare rival survives as an unpreceded potency never actualized
---

Triage (#497, `ATTEMPT-RIVAL-TRIAGE-497`): the recorded rival is the bare contradictory of the premise. Strongest sourced rival theory: the position reported in *Met.* XII.6, 1071b22-28 (pinned, `ARIST-MET-1071B-POTENCY-PRIOR-A`): whatever acts is able, but not everything able acts, so potency is prior (the theologians' generation from Night).

Bundle elimination (#497, `ATTEMPT-NIGHT-COSMOGONY-BUNDLE-ELIMINATION`): the Night cosmogony as Aristotle presents it (`ARIST-MET-1071B-NIGHT-GENERATION-A`) commits to more than the bare rival: an unpreceded potency is actualized, since Aristotle asks "how will it be moved?". That bundle is inconsistent with an inclusion-minimal core of three open premises, and the core does not use this premise. The first member is Aristotle's reply ("how will it be moved, if there is not some cause in actuality?", 1071b28-29, new supporting claim). The second, nothing moved moves itself in the same respect, is sourced to Aquinas; Aristotle's "matter will not move itself" (1071b29-31) says it only of matter. The third is the unattributed bridge `STMT-ACTUAL-MOVER-IS-SIMPLY-PRIOR`. The root-path premises reduction-by-a-mover, moves-only-as-in-act and non-simultaneity give the same elimination with the bridge. The bare rival survives the core (`MODEL-NIGHT-COSMOGONY-RESIDUAL`): a potency that nothing in act precedes and that is never actualized, the gap of #352, finding 4. Floor: no core member meets a criterion. The bridge is the cheapest to source (*Met.* IX.8, 1049b24-29 and 1050a4-b6). On the temporal reading of "prior" the position is no rival (`DISAMB-PRIORITY-SIMPLE-OR-IN-TIME`).

*Met.* IX.8 does not source the bridge (`ATTEMPT-MET-IX-8-ACTUAL-MOVER-PRIORITY`, #497 first-closure hunt). 1049b24-27 ("the mover already exists actually") proves priority in time, and only in species. 1050a4-b2 is the priority in substance of a thing's own act over its own potency, not of a mover over what it moves. 1050b3-6 is temporal again, and 1050b6-8 sets eternal beings before perishable ones. Reading any of these as simple priority of the mover would pass between the senses of `DISAMB-PRIORITY-SIMPLE-OR-IN-TIME` or change the relata. The premise's recorded rival is its bare contradictory, so it closes only by a proof from closed premises. The Night core is not enough (`MODEL-NIGHT-COSMOGONY-RESIDUAL`): it would also need a premise that every potency is related to some actualization.

## Necessary actual root to pure act: warrant reassessment (2026-11-11)

**Scope and proposed judgment.** Conditional on a supplied **same** actual
concrete root `n` at `w`, necessary at accessible worlds, the current evidence
does not warrant attributing absence of passive potency in **all relevant
respects** to it. The existing positive deduction is sound under its explicit
interfaces. The best remaining work concerns the applicability of those
interfaces to a dormant capacity; it is not another proof of the conditional
or an existence claim. This assessment leaves upstream existence, relation
adequacy and all philosophical premise establishment open. Independent semantic
challenge accepted the complete draft at `1ddf79280f3a56b72ed9fb2adeb52c90a415be44`
with these qualifications. The same reviewer accepted the scope clarifications
at `df4ffb048991da834acec69e5b50cf67bde88c2c` in targeted pass 1 with no new
findings. These reviews assess the stated reasoning and limits; they establish
no philosophical premise and do not replace final CI.

### Exact connection and existing proof boundary

Target `593d7307-c8e1-5863-9776-a26cfe09d20c`
(`STMT-NECESSARY-FIRST-BEING-PURE-ACT`) is consumed by the existing
necessary-first-attributes and classical-God routes. Its endpoint is
`NecessaryActualFirstPureActAt`: one witness is `ActualRoot`, `NecessaryAt`,
`IsFirstBeing`, and `PureAct InPotency`. Rootness excludes incoming
**actual-concrete selected grounds at w**; necessity concerns the same
individual's existence, not all its states or all-world rootness. `PureAct`
quantifies over the supplied `Respect` type. Neither positive `InAct`
perfections nor the completeness of that type follows from this negative
predicate. Applying the endpoint to all philosophically relevant respects
therefore retains an interpretation/coverage burden; this assessment introduces
no exhaustive classification.

**History/state scope.** In the intended modal route, w represents a complete
alternative history, not an instant. References here to a present capacity or
a variation of intrinsic state require an additional selected-state
interpretation of the non-world-indexed `InAct` and `CanBe` parameters within
that history. The rival comparison is not a checked joint history/state model;
no transport from a capacity at one state to existence or rootness at a different
state or history has been established.

Under the adopted potency analysis, `InAct n esse` excludes
`CanBe n esse ∧ ¬ InAct n esse` for a contingent actual being just as for a
necessary one. With that selected present-esse interpretation, this exclusion
adds no divine attribute. It is neither receptive-potency-freeness nor inability
to cease existing; those require their own interpretations and premises.

The exact existing proof is
`TruthCore.Results.Causality.NecessaryFirstBeing.necessaryFirstPureAct`:
whole-roster existence inputs furnish `n`; the bridge
`SimplyPriorIsActualConcreteGround` turns any **distinct** simple predecessor
of n into an incoming selected ground; firstness follows. Broad
`ActSimplyPriorToPotencyReading` then supplies a prior being in act in each
respect in which n has potency; firstness makes it n and same-respect
non-overlap yields contradiction. The alternative
`TruthCore.Results.Causality.StrictPriorityPureAct.necessaryFirstPureAct`
uses irreflexivity of this **same** priority relation instead of non-overlap.
Its proof discards the actuality witness, but still needs broad act-priority
and the same bridge into actual selected grounds. Irreflexivity does not
supply their warrant.

For a root **already supplied**, the last reasoning does not use modal
necessity or any other-world root property. This is a direct reading of the
existing proof, not a newly registered theorem or a weakened corpus argument.
No reason is gained by demanding all-world rootness here. The first-mover route
to `6c18d52b-2456-59ae-995f-13440f8c808d` has a separate
first-mover-to-first-being bridge. Actual rootness supplies neither outgoing
motion nor identity with that mover. Likewise
`ff2cf972-3f5b-5595-9397-afa4c91b10f1` checks pure-determination/uniqueness
interfaces on finite roots; it does not infer passive-potency-freeness from
no incoming ground. `Has/Pure` strict purity is not `PureAct InPotency`.

### Strongest positive route: ground the capacity, not every exercise

The existing non-motion argument is already available:
`TruthCore.Results.Causality.Round4Revisited.actPriorFromGround`. It composes
three jointly necessary inputs in that argument:

| Existing premise | Positive independent rationale | Remaining warrant burden for this application |
| --- | --- | --- |
| `8a1d7012-3a77-5c78-a5b1-30006aa4ae8c`, `PotencyHasGround` | A real directed capacity is more than an arbitrary possibility: the bearer's determinate nature can explain why this manifestation, rather than an unrelated one, is available. This favors looking for a present basis even when nothing happens. | This rationale permits an intrinsic basis in n, and distinguishes grounding possession of a capacity from an available agent able to actualize it. It does not ensure a distinct present being in the selected grounding domain. |
| `bf374f2e-df3b-5e8f-bea8-9fcfe680141b`, `GroundOfPotencyIsInAct` | An actual basis, rather than a merely possible basis, is needed if the current capacity is to be explained by it. A producer must have sufficient actuality to produce its effect. | Actuality **as a basis of the capacity** is not formal actuality **of its absent manifestation r**. Virtual possession is a defensible alternative but must be used consistently in the potency analysis and non-overlap; it is not an unannounced repair. |
| `a4606a6b-8209-58d9-b221-a26a7f31b0e1`, `GroundOfPotencyIsSimplyPrior` | If capacity possession depends on an independently actual source, that source has explanatory priority with respect to that capacity. | Dependence of a power is not yet dependence of the bearer for bare esse. Internal constitution, a historical generator, a current actualizer and a current existence-ground have different relata and scope. The same actual-concrete-ground bridge must be defended, not inferred from the word priority. |

These premises are, respectively, supported, supported, and bare in the
inspected dossiers; none is established. These status descriptions are not
philosophical credibility rankings. The independent rationale above makes the
first premise more substantial than a demand that every capacity is presently
exercised. It does not justify the full three-premise bundle. The existing
`DEF-POTENCY-GROUND` (`66914b47-5881-5d7f-a18b-8b22447fb71c`) offers both a
possible actualizer and a source of the capacity as examples. A fire that could
heat water illustrates an available actualizer; the water's constitution
illustrates a basis of its thermal capacity. Neither example alone certifies
all three interfaces on one relation. The definition is retained unchanged;
its application to this route remains open.

This walks the strongest positive argument beyond the dormant-potency
countermodel. If the capacity is received from something else, ask what is
received: the subject's existence, its constitution, its power, or a particular
state. If the receipt is constitutive, ask why that constitution requires a
**distinct actual concrete** ground of the subject at w. If its source is
intrinsic, ask why dependence on its own nature must be efficient
self-origination rather than noncausal intelligibility. Finally ask why that
nature could not be necessary while some manifestations remain unrealized.
Each question identifies a separate bridge; none is answered by renaming the
source pure act.

### What the selected primary passages support

The existing pinned witnesses were materialized and the **whole articles**
read for this assessment: `AQUINAS-ST-I-Q3-A1`, `-Q3-A4`, `-Q4-A1`,
`-Q4-A2`, and all seven paragraphs of `AQUINAS-SCG-I-16-EN`. No source claim,
passage manifest or historical attribution record is added. The q3/q4 witness
is SCTA/Leonine revision `f9065dc8ce7bc790b8c972e49ee19d661f028be6`,
q3 blob `9204053aec597c5ea95b77543135e641ce4cfdeb`, q4 blob
`405ca53f12c06c28d14edee495f75a946b4f1a1c`. Exact extraction selectors remain
in the existing passage manifests. These are selected readings, not a full
source verification campaign. The existing #319 scope audit remains the
reference for its other source findings.

* Q3 a1 co., second proof, explicitly asserts act's broad priority and the
  first being's no-potency conclusion. Its stated reduction-to-act reason
  supports actualization, while applying that reason to every dormant capacity
  remains the substantive extension already isolated by `ActPriorFromMotion`.
  This is a gap in the offered independent defense, not an accusation that
  Aquinas asserted only the narrower premise.
* Q3 a4 co., first proof, argues that esse distinct from essence has an
  external efficient cause by causal exhaustiveness and exclusion of essential
  efficient self-origination. An intrinsic explanation of why an already
  existent nature has a capacity is not that efficient self-origination. The
  second proof argues **from** no potentiality to essence/esse identity. It
  does not license reversing that implication. Even conditional equality of
  the existing profile's represented maps says nothing about every accidental
  state or the `CanBe` relation. The independent identity investigation is
  neither changed nor presumed resolved here.
* Q4 a1 co. distinguishes first material and first efficient principles; an
  agent is actual **qua agent**. Ad2's seed example offers a real generative
  explanation, but its generator and the reducer of an arbitrary later
  potency are not thereby the same. Ad3's point that actuality presupposes
  being supports `InAct x r → InAct x esse`, not its converse and not the
  claim that every existent is actual in every respect.
* Q4 a2 co., first proof, gives effect-perfection preexistence formally or
  eminently and presupposes the first efficient cause of things in its divine
  application. Eminent possession explains how an active source need not have
  the effect's finite form. It does not require every possible effect to be
  produced. The second proof starts from subsistent esse and argues for the
  fullness of being by the subsistent-heat analogy. This is a serious positive
  proposal: an unreceived act is not contracted by a receiving nature. But
  applying it to n needs a defense of subsistence/nonreception and of why every
  relevant passive capacity would be such a contraction. Modal existence and
  no selected incoming edge do not themselves supply those claims. Reusing
  both proofs as independent confirmations would also conceal their different
  prior causal/subsistence commitments.
* SCG I16[2] excludes potency to being on its everlasting-substance argument;
  [3] asserts unrestricted act-priority but gives the reduction reason;
  [4] invokes necessity through itself and causal commitments, not merely
  `NecessaryAt`; [5] appeals to the **first agent**, whole-essence activity and
  participation; [6] appeals to already established absolute impassibility and
  immutability; [7] starts from actual transitions and regress. These routes
  supply distinct positive explanations conditional on their own starting
  points. None identifies a merely supplied actual selected root with all
  those roles. In particular [5] cannot be shortened to “some intrinsic power,
  therefore no passive potency”; [6] cannot use immutability derived downstream
  from pure act as independent corroboration.

Receptive potency of a principle to already received esse is separately typed
(`ReceptivePotencyTo : Principle → Principle → Prop`); adopted unactualized
potency is `CanBe x r ∧ ¬InAct x r`. Existing
`DISAMB-RECEPTIVE-POTENCY` and the reception assessment in
[causal-perfection-transfer](../../notes/causal-perfection-transfer.md#reception-real-constitution-and-actualized-receptive-potency-2026-10-31)
preserve that difference. Receipt of a determination does not become
unactualized potency of the existent bearer by changing the label. Conversely,
non-overlap of adopted potency does not eliminate a received act/recipient
constitution. No new bridge between those types is assumed.

### Strongest standing rival and further commitments

The serious rival is an actual, intrinsically determinate necessary nature
with its powers grounded in what it is, not in a further existence supporter.
It is not a free-floating uninstantiated possibility. It may produce effects
when conditions obtain without changing its own intrinsic state; **that
active power alone is not a counterexample to pure act**. To oppose the present
all-respects conclusion, the stronger rival must additionally allow a genuine
passive capacity for an intrinsic state F that n does not presently have,
using formal `InAct` and the same respect in `CanBe` and `¬InAct`. If a virtual
or inclusive sense of `InAct` is chosen instead, the rival must be reassessed
in that sense; “not presently manifesting” alone no longer proves adopted
potency. This fixes the sense rather than slipping from power to passivity.

Its positive explanation has three levels: a necessary nature grounds stable
capacity possession; manifestation depends on a suitable interaction or
condition; the nature need not be efficiently producing its own existence.
A different being could actualize an intrinsic state without continuously
grounding n's bare esse. That admits a limitation in the independence of its
states, while preserving the stipulated existential rootness. Alternatively,
spontaneous intrinsic realization would owe a positive account of transition
rather than silently rejecting the actualization principle. The conditioned
version is the stronger rival considered here because it need not reject that
principle merely to survive. No new Lean model is claimed for either version.

“No proper parts” does not refute this rival: it may be mereologically simple
while having contingent intrinsic states. A thesis of **no real metaphysical
constitution whatsoever** is stronger. If the rival accepts a real act/recipient
composition for every passive capacity, it cannot simultaneously claim that
strong noncomposition. It must either permit that constitution or defend a
nonconstituent account of dispositional state variation. Even permitting
constitution is not by itself inconsistent with a root: the claim that such
constitution requires a distinct actual concrete esse-ground is still open.
The cost is thus specified in commitments, not dismissed as an unreasonable
metaphysical price. No supplied accepted floor item or the rival's own stated
commitments has here been shown to contradict its necessary nature plus
condition-dependent states. This is an unexcluded account, not a demonstrated
metaphysical possibility or a verified joint model of the full root framework.

Descending to the next explanatory question, a necessary dispositional nature
may explain **which states are possible** without fully explaining **why this
state is actual**. A contrastive demand for the latter may motivate a further
reason or condition. But a cause of that state does not yet cause n's existence;
a law/state reason is not automatically a concrete bearer, just as the existing
#786 necessary-fact result does not produce a necessary individual. Rejecting
primitive natures merely for terminating that explanation would need a warrant
standard applied equally to the proposed subsistent act. The classical positive
answer is that esse itself is intrinsically actual rather than waiting for a
receiver. Its open burden is why n has that mode of actuality and why it
exhausts all independently specified passive respects; writing `PureAct` does
not answer it.

### Provisional judgment, failed routes and reopening conditions

The **conditional classical bridge remains useful**, but the application from
actual necessary root to all-respects pure act is not independently secured.
The evidence favors requiring a real basis for a genuine capacity over a
free-floating possibility. It does not favor the further claim that every such
basis is a distinct actual-concrete ground of the bearer's bare existence, in
the same sense and world used to define rootness. This is a provisional warrant
judgment, not a proof of the rival or the falsity of act-priority.

Three attempted defenses reach precise different obstacles: the actualization
route covers exercised potency; the capacity-ground route needs same-respect
actuality and capacity-to-bearer existence transfer; the subsistent-esse route
needs nonreception and contraction/coverage. Reversing q3 a4's second proof,
using mere existence as every-perfection actuality, and replacing a real passive
capacity by unused active power are rejected approaches. The first mover,
first efficient cause, pure actual selected root and bare necessary bearer
cannot exchange roles without their bridges. Prior finite controls and
`ActPriorFromMotionFacts` already preserve the logical gaps; new primitive
truth assignments would add no warrant and are not supplied.

The next discriminating test is a substantive defense of **one specified
relation**: show why an intrinsic basis of an unfulfilled passive capacity
must either be a distinct actual concrete existence-ground at w, or introduce
a real constitution that itself requires such a ground. Keep the passive state,
capacity possession, nature and bare esse distinct. Test the conditioned
necessary-nature rival against that defense; an available agent capable of F
or a cause only of a later F-state is insufficient. A successful account would
revise this judgment. A faithful account establishing subsistent nonreception
and showing every relevant passive capacity to be incompatible with it would
also reopen it. A demonstrated incoherence in the rival's own explicit state
and nature commitments would count; another formal omission model or a new
name for the universal bridge would not.

No materially different deductive next step is presently identified within
this slice: the generic compositions and controls already exist. Continuing
requires selecting and defending that constitutive/existential transfer or
the nonreception route, rather than recertifying the same conditionals. Those
are substantive dependencies for coordinator reassessment; research as a whole
is not declared exhausted. No statement, argument, result, definition, source
claim, approval or proof status changes; **no premise change**. Existing proof
checks remain reusable on unchanged inputs; offline record checks and final
publication CI do not certify this philosophical judgment.
