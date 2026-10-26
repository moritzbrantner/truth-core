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
It proves neither cognitive nature nor intellectual grade. It is an internal
interface lemma, not a new advertised corpus argument or a Comparator result.
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

Intended and actual root-path open-premise change: **none**. No premises were
retained/added/removed in any existing argument. The target remains sourced
but undefended, no relocation or discharge is claimed, and the two new source
statements lie outside all root routes. The branch baseline's frontier reports
46 open premises (4 bare, 42 sourced-undefended), with route costs
28/29/33/35/36/36/37/38. The issue's historical 37-premise count is not used as
the current baseline. The new records and generated import add no root path.
