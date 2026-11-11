# Borrowed causal power and its actual exercise (#741)

Question: do locally sufficient transfers of derivative power jointly explain the
actual exercise of that power, or does an instrument need a source? The check
result is a fork, not an answer. Formal module:
`TruthCore/Explanation/BorrowedExercise.lean`, result
`BORROWED-EXERCISE-CERTIFICATE`. Root delta: none.

## Meaning of the relation

`cap s e` is a supplied profile: the bearer of `e` has the power for that exercise
at scenario `s`. `occurs` is the exercise. A record lends at `s` when it is admitted,
has a contributor, all its contributors occur at `s`, and at the actual scenario it
is also exercised. In ordinary words:

- *borrowed*: wherever the power is there, a lender is there too;
- *retained*: the power is there somewhere with no lender;
- *instrument*: borrowed, exercised, lender actual;
- *secondary cause*: retained, exercised, lender actual;
- *self-exercising*: exercised with no actual lender.

Illustrations of scope, not empirical laws or source readings. A stick pushing a
stone has no pushing power when the hand stops; a fire keeps its heat when not
touching wood, and heats only on contact; a charged lamp battery keeps its power
when the switch is open. Near misses: a hand that holds a stick still (power and
lender without that exercise); a closed switch on a dead supply (a member occurs,
no contributor does). Counterexamples to the tempting identifications: the battery's
power came from a charger, so *retained is not underived*; a hand's exercise may be
caused by nerves not recorded in the exercise, so *self-exercising is not uncaused*.

Near neighbours kept apart: a #733 record's membership (an event can be a member and
not lend); #734 `LocalPower` (an unselected equation); `Supply` (a proposed
inductive standard); graph sourcehood; and `intrinsicPower` of the older boundary
profile (DISAMB-POWER-CAPACITY-EXERCISE).

Structural properties: lending is not assumed transitive, asymmetric or well-founded.
None is needed. Cycles and regresses are witnessed. The generalization from
ordinary instruments to metaphysics is exactly what is not made: real agents are
assigned no profile.

## What is proved

For an exercise and profile, with the actual scenario allowed and each actual
exercise having its power, an occurring event is exactly one of instrument,
secondary cause, self-exercising. Then two forks:

- **exercise fork** (no profile needed): Supply from self-exercising events, or a
  self-contained set of occurring lent events;
- **power fork**: Supply from exercised retained powers, or such a set consisting of
  instruments.

The branches exclude each other through #734 `trap_obstruction`. A descent yields a
chain that is injective or revisits an event. Nothing in the fork defines borrowing
through a source, so the source does not follow from a definition: the source-free
witnesses satisfy every hypothesis. Under the reading `MovedMoversInstruments` the
two standards coincide. It is refuted on `SecondaryRegress` as a claim about all
exercises, and it is not refuted as a claim about real agents.

| Witness | Profile | Labels | Own-power Supply | Self-exercise Supply |
| --- | --- | --- | --- | --- |
| #734 `unrooted` | power when exercised | all instruments, injective chain | no | no |
| #734 `unrooted` | power at every scenario | all secondary causes | all | no |
| `unrooted`, on scenario only | power at every scenario | all instruments | no | not stated |
| #634 `rooted` | power when exercised | source self-exercising; branch instruments | source yes, branch no | not stated |
| #734 `circle` | power when exercised | all instruments, revisiting chain | no | not stated |
| #734 `finite` | essential source or not | effect an instrument | effect yes | not stated |
| #734 `finite` | power at every scenario | effect a secondary cause | effect yes | effect yes |

## The decisive step on the First Way route

`AQUINAS-SCG-I-13-MOVED-MOVERS-INSTRUMENTS` reads SCG I.13 [15] as: every mover in an
infinite series counts as instrumental because it is a moved mover. Pinned translation
read through `AQUINAS-SCG-I-13-EN`. In Phys. VIII lect. 9 n. 1038
(`AQUINAS-IN-PHYS-VIII-L9-EN`) divides a mover that moves by its own power from one
that moves not by its own power but because moved, and n. 1044 is presented there as
a probable argument. The existing claims already record that the SCG text does not
consider a mover moved only in a respect irrelevant to its moving.

The checked finding: an actual lender does not give borrowed power. The same
exercise has every event lent and is all instruments or all secondary causes
depending only on the profile. So the step from *moved mover* to *instrument* is
additional content in this vocabulary, not a consequence of the order of the series. This repeats no
statement about what Aquinas meant: `MovedMoversInstruments` is an analyst reading
compared with STMT-WHATEVER-MOVES-AND-IS-MOVED-MOVES-AS-INSTRUMENT, not its
formalization, and no source claim was added.

A reply through concurrence does not escape the distinction. The reading of
q.105 a.5 recorded in `docs/notes/causal-perfection-transfer.md` has God giving powers
*and applying them to operation*. That targets exercise, not retained power, and so
corresponds to the self-exercise standard: the secondary chain lacks that Supply.
But it needs that standard, which the rival can reject; no theorem here derives it.
On the existential-support route the same machinery would need a separate profile for
that respect. No clause carries a result from a motion profile to an existence
profile.

## Three rivals

**Intrinsic source.** Founded branch. It pays a price: `FoundedControls` has a source
with essential power whose exercise does not occur at every allowed scenario, with
Supply of the effect all the same. Supply therefore does not record why the source
exercised. `RootedBranch` has a source whose exercise occurs at every allowed
scenario.

**Brute actual power.** Two forms. A contingent self-exerciser (`capOccurs` on
`finite`) has the same own-power Supply as an essential one. Exercise with no power at
all falls outside the power fork (`PowerOmission`), and the exercise fork classes it
as self-exercising. So `PowerRequired` is what excludes that form, and it is OPEN, not derived.

**Source-free global structure.** Strongest infinitist reply: an all-on beginningless
network of instruments is the whole explanation, and demanding Supply begs the
question against it; a chain's power is received at each link and the whole has a
lawful organization. It grants the descent branch and denies that it is defective. The
witnesses are coherent, jointly sufficient and locally powered, and the
`HistorySelection` boundary discussed in `docs/notes/derivative-joint-power-734.md` is
untouched. The fork does not refute this. What it does
is fix the reply's cost: for that branch to be occupied by *instruments* rather than
secondary causes, each power exists only under a lender, all the way, with no exercise
anywhere that is not lent. The reply owes why that exercise occurs rather than the
allowed all-off scenario, or else restricts scenarios as `SelectedCollapse` does, which
#734 records as selection and not a supply derivation. The
secondary-cause infinitist has a cheaper position on power and the same debt on exercise.

Humean and regularity accounts reject a profile that goes beyond occurrence. Then
`capOccurs` is their natural choice, making every lent event formally an instrument,
which they would read as a mere label. Nothing here refutes them.

## Open bridges and limits

OPEN: that real productive exercise satisfies either Supply standard (equivalently
that the descent branch is defective); which profile holds of real agents; that
`PowerRequired` holds of real exercises; passage from motion to existence.
A fork certifies coverage under its hypotheses; it does not choose a branch, and
hypothesis minimality is not claimed beyond the stated omissions.

The #310 limit-source control is not consumed here; #734 already carries it unchanged
in `LegacyControls`, and it was not reimplemented. `AtContext` was not applied; one
selected time and respect is held fixed only by the fixtures having no time data.
ExplanatoryAdequacy (#769) is not imported: its `Arena` has no profile or records, so
a bridge would need a new interpretation map. `JointCooperation.NecessaryIn` and the
#752 pair are reused.

## Does derivation of an essential power reach the bearer?

Analyst investigation. Take an actual bearer x and one active power P, a
capacity to bring about a specified kind of effect. Distinguish what accounts
for x exercising P, what accounts for x possessing P, and what accounts for
x existing. Use *external ground* here for an explanation of the specified
fact by something outside x. A trigger, a suitable recipient, and mere
covariation with P do not by themselves supply that explanation.

**Dependence in power.** If something external accounts for x's possession
of P, x is derivative with respect to P. If P belongs to x by nature, this
dependence concerns a natural capacity of x. It reaches further than
dependence on a condition for exercise. This suffices against an
underivedness claim that explicitly includes the source of x's essential
powers. A claim of underivedness in both respects would add a power requirement
to the exclusion of incoming existential support.

**Dependence in existence.** The tempting argument is that x could not exist
without P, so what grounds possession of P also grounds x's existence.
The first clause gives a condition on worlds in which x exists. The second
needs an explanatory direction that the condition does not provide. In a
nature-first account, the actual bearer and its nature explain its powers.
A power can follow from a nature in every world in which the nature is
instantiated while remaining distinct from the constitution of the bearer.
Aquinas's treatment of created soul powers gives a concrete motivation for
that distinction (ST I q.77 aa.1, 6). For a being whose power, essence and
existence are really identical, as Aquinas holds of God (ST I q.25 a.1
ad 2), a different argument is available. It would still need to establish
that the alleged external explanation targets that very actuality rather
than a relational or descriptive fact about it. Divine simplicity cannot
serve here as an assumed property of every first source.

The strongest positive route starts with a claim about constitution. If an
external principle partly grounds the fact that x has an actual constituent
and that very fact partly grounds x's existence, then that principle partly
grounds x's existence if partial grounding is transitive for those links.
The hard premise is that the externally grounded possession of P is that
same constitutive fact, or that possession of P partly grounds that fact.
A power consequent on a nature can be inseparable from it without meeting
that premise. A Thomistic
nature-first account instead looks upstream from the power to the nature
or the bearer's received actuality, and asks directly whether either is
derived. A powers-first account can take the constitutive route, with an
independent argument for what constitutes this bearer.

### Application to a first cause

The existing [power and existence boundary](../../corpus/statements/power-existence-simplicity-scope-boundary.json)
already gives the converse warning. A source with intrinsic power in one
respect can have existential support in its model. The
[borrowed-exercise certificate](../../corpus/statements/borrowed-exercise-certificate.json)
distinguishes a supplied capacity from its exercise. Neither checks the
proposed lift from grounded possession to grounded existence.

For the [underived concrete source route](../../corpus/statements/necessary-concrete-underived-at.json),
the next substantive test is whether the power under discussion is a
consequence of the source's nature or enters into what constitutes the
source. Even a successful constitution argument needs a separate
correspondence to the route's selected grounding relation and its
concrete-supporter and world conditions. A qualifying incoming link would
exclude the selected bearer as a witness. Excluding every candidate would require a separate argument. A common
exercise condition does not establish the lift without a case that it
accounts for the powers or actuality.
The distinction matters for an individual source even if no plural-source
theory is under consideration.

Provisional judgment: accept dependence in the specified power as a
conditional conclusion. Keep existential dependence open on the
constitutive and relation-mapping premises. This comparison is analyst
reasoning with source locators for orientation and no new corpus
attribution or Lean certificate.
