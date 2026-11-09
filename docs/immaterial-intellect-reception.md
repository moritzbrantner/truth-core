# Immateriality and the aptitude for another's form

Issue #355, intellect only. The target remains
`STMT-IMMATERIAL-IS-INTELLECTUAL`; this batch does not derive or replace it.
The will obligation and all root-route signatures remain unchanged.

## Verified reading

`python3 scripts/source_evidence.py materialize AQUINAS-ST-I-Q14-A1`
materialized the full article, including objections and replies, from the
pinned Latin SCTA witness. The existing passage manifest records revision
`f9065dc8ce7bc790b8c972e49ee19d661f028be6`, blob
`313acd7bdc7586fb9c92f75dfc5441ab37f028ec`, and the exact TEI article node.
The complete article was read, rather than just the immateriality sentence.

At I q.14 a.1 co., the distinction between knowers and non-knowers introduces
aptitude to have another thing's form. The source then attributes contraction
of form to matter and links degrees of cognition to degrees of immateriality.
Sense receives species without matter; intellect is still more separated.
The final application puts God at the summit of cognition because of supreme
immateriality. Replies 1–3 remove created habit, potency, multiplicity and
created modes of knowing from divine predication. They prevent treating God's
knowing as passive acquisition of information from creatures.

Two narrow readings are now recorded independently: cognitive nature entails
aptitude for another thing's form, and sense has without-matter receptivity.
They preserve source content without making these statements sufficient for
the old intellect bridge. They are attributed commitments, not established
premise truths. No additional source passage or source kind was introduced.

## Exact types and the useful local consequence

In `FormReception.Model Being Form`, `CanHaveForm x f mode` is a capacity,
not an actual reception event. `ForeignForm x f` says that f is a form of
another thing; it does not require a different species from x's own form.
`Form` ranges over possible capacity objects, without asserting the actual
existence of their external bearers. Cognitive, sensory and intellectual
capacities remain separate predicates.

| Item | Lean content |
| --- | --- |
| `STMT-Q14-COGNITIVE-FORM-APTITUDE` | `∀ x, m.Cognitive x → ∃ f, m.ForeignForm x f ∧ ∃ mode, m.CanHaveForm x f mode` |
| `STMT-Q14-SENSE-WITHOUT-MATTER` | `∀ x, m.Sensory x → ∃ f, m.ForeignForm x f ∧ m.CanHaveForm x f .withoutMatter` |
| `NoMaterialReception m x` | `∀ f, ¬ m.CanHaveForm x f .withMatter` |
| `availableFormWithoutMatter` | `ForeignFormCapacity m x → NoMaterialReception m x → WithoutMatterCapacity m x` |

The last consequence is constructive case analysis on the reception mode.
It needs positive aptitude independently of excluding material reception.
It proves neither cognitive nature nor intellectual grade. It was originally an internal interface lemma. The conditional comparison
below now registers it through the exact two-input mode-elimination result.
No claim of mechanically verified philosophical consequence is made for the
old target.

`CognitiveAptitudeReading` retains only one direction of the source's
contrast. In particular, the source's description of non-knowers as having
only their own form has not been silently converted into a theorem that any
negative condition on reception produces a positive cognitive capacity.

## Omission controls and rejected shortcuts

`availabilityOmission` exhibits an empty capacity relation. It satisfies the
two source readings and has no material reception, while lacking all aptitude
for another's form. The source readings hold vacuously because its cognitive
and sensory predicates are false. This is precisely the missing positive
availability control, not an explanation of an actual immaterial being.

`intellectualGradeOmission` has sensory and cognitive aptitude without matter
but a false intellectual predicate. It satisfies both source readings and
excludes material reception. Thus without-matter receptivity alone cannot
identify sense with intellect. The source itself distinguishes them.

`oldTargetOmission` gives the empty recipient a false matter/form-composition
predicate and false component relation. Its intellectual predicate is still
false. The existing target therefore fails in this unconstrained formal
schema. These are omission controls, not claims that such models are
metaphysically possible or that the Thomistic conclusion is false.

Rejected shortcuts:

- Defining immateriality as cognitive or intellectual capacity would hide the
  target in its antecedent. `NoMaterialReception` is only a negative local
  restriction and is not identified with the old structural antecedent.
- Actual reception availability is stronger than the source's aptitude
  wording. Even a positive aptitude bridge would require a separate defense;
  no actual event or actual external object is manufactured here.
- The q.75 human principle's universal bodily cognition cannot be reused as
  God's reception capacity. Its cognitive scope and constitutive-interference
  relations have different meanings and do not encode these reception modes.
- An operational account of information acquisition is a comparison sense,
  not a translation of aptitude or a conclusion that cognition is computational.
  `DISAMB-Q14-RECEPTION-SENSES` keeps this sense, sense cognition and intellect
  apart. The existing primitive `HasIntellect` is unchanged.

## Scoped analyst proposals and conditional connections

The resumed logic-first batch reuses the original model and all four existing
lemmas without changing their source readings. The existing `Intellectual`
predicate is not redefined. Three OPEN calibration propositions compare it,
on one explicitly admitted scope, with foreign-form capacity, without-matter
capacity and an occurring foreign-form **state-change proxy**.

The proxy requires an occurring event, its same receiver and a foreign form,
and unequal before/after states. It supplies no input-causes-change theory,
capacity, semantic understanding or actual external source object. In
particular, a failed proxy calibration does not refute a serious acquisition,
functional or computational account. The broader original information-
acquisition comparison remains unformalized in that respect.

`NamedMenu` says at least one of these three calibrations holds. It is an OPEN
coverage assumption, not a census of adequate theories. `Remaining` explicitly
says all three fail on the same dictionary and scope. The structural coverage
result uses excluded middle as an explicit input; it establishes neither
branch. Named elimination is labelled logical transcription. The proposal
calibrations can overlap; no exclusivity of the three proposals is claimed.

The old target has three separate **transcription/assembly** routes. They use
the same `m.Intellectual` predicate and preserve the old structural antecedent:

| Branch | Independent OPEN inputs |
| --- | --- |
| Foreign-form capacity | Every structurally free receiver is in scope; structural freedom supplies positive capacity; the scoped capacity/intellect calibration. |
| Without-matter capacity | Scope coverage; positive capacity; structural freedom excludes material reception; the scoped without-matter/intellect calibration. The old mode case analysis is imported. |
| State-change proxy | Scope coverage; structural freedom supplies an actual occurring proxy change; the scoped proxy/intellect calibration. No event is manufactured from aptitude. |

These are conditional maps, not independent warrant for any intellectual
identification. A scope cannot silently discard old structurally free receivers.
No source is attributed any new calibration, coverage or availability claim.
The pointwise without-matter capacity really entails unspecified-mode capacity;
the **calibrations**, which compare their entire extensions to intellect, do not
inherit a strength ordering merely from that pointwise implication.

The checked control statement exports separate interpretations, not a joint
worldview. It retains all three old omission controls exactly. A material-only
receiver distinguishes the pointwise strengths. A dormant primitive-intellect
assignment has positive without-matter capacity and both capacity calibrations
but no actual proxy event; it exports the full positive scope/availability/mode
background and exact old target. Another profile separately supplies an actual
proxy and its full positive assembly background. An event in the empty-capacity
profile does not manufacture capacity. Finally, a nonempty admitted profile
with a positive primitive-intellect assignment lies outside all three proposed
extensions, explicitly witnessing the remaining branch rather than selecting
a preferred winner. These are API interpretations, not actual immaterial beings,
metaphysical possibilities or defeats of complete worldviews.

The new Challenges were frozen before Solutions in `9ce52e79`. Their later
ordinary-file header normalization is packaging compliance only: theorem text,
types and namespaces were preserved byte-for-byte, and Solution inputs stayed
unchanged. The affected Challenge comparisons were rerun.

## Remaining gap and premise comparison

The source expressly asserts the graded immateriality argument, but neither
the two narrow capacity readings nor the case-analysis lemma explains how the
old component-free antecedent ensures positive cognitive aptitude, reaches
the intellectual grade, and binds that grade to the existing `HasIntellect`.
The term "more separated" has not been formalized by simply assigning its
highest point the desired predicate. Those steps remain the research target
in `AQUINAS-Q14-IMMATERIAL-INTELLECT-BRIDGE`. Any necessary change to the old
meaning is a cross-cutting decision to coordinate before altering signatures.
The future q.14 a.2, a.4–5 and a.8 range in the candidate is a research pointer,
not a claim to have read or verified those articles in this batch.

The original source-reading batch had no root-path premise change. The resumed
batch adds three conditional assembly routes to the existing target. Against
`7c89dd9abecb2e1da4cf89b4250e506a8c6e1539`, the computed `frontier-diff` reports
128 → 138 open premises, 67 → 77 bare, with supported/stated counts unchanged
at 18/43. It adds the ten explicit OPEN menu, calibration/failure, scope and
structural availability/mode/event premises; removes and relocates none. The
cheapest root route stays at cost 30 and reports no route-cost changes. These
are new conditional connections, not discharges. Existing arguments and old
Lean interfaces retain their premises; no source statement is independently
established. The PR carries the complete machine-computed delta against its
final merge base.

## Bounded bridge audit, 2026-11-09 (#355)

This continuation inspected the exact `Article1.lean`,
`ReceptionDefinitionFork.lean`, `IntellectWill.lean`, and
`Q14ReceptionFork/FromWithoutMatter/Solution.lean` declarations, the existing
reception sense declarations, the target dossier and the without-matter result
context. It adds no formal result and does not repeat #1179's controls.

Write `S x` here only as prose shorthand for the unchanged antecedent
`¬ matterForm x ∧ (∀ y, ¬ component x y)`. The old target quantifies over
all `Being`; it has no existence, concreteness, life or operation hypothesis.
Consequently, calling this antecedent “subsistent immateriality” must not
silently import those positive conditions. In particular:

- An abstract immaterial object is not excluded by either negative conjunct.
  This is a statement about the signature, not an assertion that abstract
  objects exist or satisfy the intended metaphysical interpretation.
- A concrete but nonliving immaterial bearer would present a different burden:
  excluding abstract objects alone would not provide life, operations or
  foreign-form capacity. Neither the Q14 model nor its structural antecedent
  has a concreteness or life field.
- A living or operating bearer still needs an independently articulated
  distinction between sensory reception and intellectual reception. The
  certified `intellectualGradeOmission` already prevents identifying the
  without-matter mode with intellect. An arbitrary operation or state change
  supplies no such distinction.

The exact existing proof `oldTargetOfWithoutMatter` uses
`(hCalibration x (hScope x ...)).mpr` once. It uses neither the converse
(intellect implies reception) nor calibration on receivers outside `S`.
Its candidate weaker obligation is thus, on the same dictionary,
`∀ x, S x → WithoutMatterCapacity m x → m.Intellectual x`, together with
positive availability and material-mode exclusion on `S`. This is a proposed
proof-input minimization, **not a registered strength relation or a new
certified theorem**. Merely registering it would be another transcription;
it would supply no explanation of intellectual grade.

A life-restricted replacement would need two separate bridges: `S` implies
the chosen concrete/living scope, and operations on that scope support a
specified intellectual reception structure. The first has to confront both
abstract objects and nonliving concrete bearers. The second must constrain
what forms are represented and how representation supports intellectual
rather than merely sensory discrimination, with omission controls preserving
positive operation while denying that structure. Neither bridge follows from
the present Q14 declarations. An opaque `Living` flag, an opaque operation
flag, or a bridge whose consequent is just `m.Intellectual` would leave the
same explanatory gap. No such flags or new taxonomy were added.

The next discriminating investigation is an operation/representation profile
with a positive non-intellectual operating rival on the **same** background,
then a separate explicit connection to `HAS_INTELLECT_1`. Applicability to
subsistent immaterial beings remains open. This audit has not constructed or
certified that joint rival model, and does not claim that the life distinction
already has a formal encoding. The existing independent Unit controls are
not a joint worldview or an abstract/nonliving/living partition.

Claim/type self-sweep: all named theorem descriptions above retain their
original capacity, scope and omission boundaries. No source interpretation,
sense identity, God binding, Challenge, argument, or result changed. No premise
is retained or removed by a new argument because there is no new argument;
this is a persisted unsuccessful bridge investigation, not conditional proof
progress or root closure.
