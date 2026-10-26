# Human intellect: the first q.75 a.2 inference

Issue #419 begins a philosophy-of-mind comparison, with one argument rather
than a general refutation of naturalism. The result
`AQUINAS-ST-I-Q75-A2-INTELLECT-NOT-BODY` derives the first subconclusion of
ST I q.75 a.2: the designated human intellectual principle is not a body.
It does not derive the later claims of non-organic operation, per-se
subsistence or immortality. Not being a body does not exclude every physical
process, functional organization or physical realization of a capacity.

## Verified source and reuse

The complete q.75 a.1–2, including the question prologue, objections and replies,
and complete q.76 a.1 were materialized from the Latin Corpus Thomisticum page
`sth1075.html`: Leonine 1889, Busa transcription, Alarcón revision. Two live
fetches were byte-identical; two fetches of the fixed 2026-02-14 Wayback capture
have the same bytes and extraction hashes. The source is the Latin electronic
edition, not a translation and not a claim that the web publication date is
the historical edition date. Only metadata and hashes are committed.

The existing `ImmaterialIsIntellectualReading` in `IntellectWill.lean` runs in
the opposite direction and uses a stronger highest-immateriality antecedent.
`HasIntellect` is primitive there: it has no cognitive-domain operations from
which this argument could be inferred. `DEF-HAS-INTELLECT` remains unchanged.
The local `HumanIntellect.Model` supplies only the additional relations needed
by this first inference, without identifying human and divine knowing.
`DEF-MEREO-SOUL-AS-FORM` is an independent proposed unity account, not an
already established theorem about the human intellect. No existing theorem is
restated as a new premise, and no earlier proof has the content needed here.

## Prose beside the Lean types

For a typed model `m` and designated principle `i`:

| Statement | Exact content |
| --- | --- |
| `STMT-HUMAN-INTELLECT-UNIVERSAL-BODILY-COGNITION` | `∀ n, m.BodilyNature n → m.CanUnderstand i n` |
| `STMT-EVERY-BODY-HAS-DETERMINATE-NATURE` | `∀ b, m.IsBody b → ∃ n, m.BodilyNature n ∧ m.HasNaturally b n` |
| `STMT-INTRINSIC-BODILY-NATURE-BLOCKS-UNIVERSAL-COGNITION` | `∀ n, m.BodilyNature n → m.HasNaturally i n → ¬ UniversalBodilyCognition m i` |
| `STMT-HUMAN-INTELLECT-IS-NOT-A-BODY` | `¬ m.IsBody i` |

All three premises are source-attributed open commitments. Suppose `i` is a
body. Determinacy supplies a nature naturally possessed by `i`. Interference
then denies the universal capacity supplied by the cognitive premise. This
reductio is constructive: it does not infer an existential unknowable object
from a negated universal. The Solution and frozen Challenge use the same type.

The three omission theorems each give an explicit one-point model with a
bodily designated subject, the other two premises, and failure of the omitted
premise. These are finite formal-schema controls, not metaphysically possible
worlds. In particular, the interference-omission model allows bodily
constitution and universal cognitive capacity together. Its primitive
`CanUnderstand` relation is not an explanation of intentional content.

## Fidelity critique and rejected readings

- **Capacity, not exercise.** The Latin attributes an ability across the
  natures of bodies. The formal universal is distributive capacity, not actual
  omniscience, a single simultaneous act, or knowledge of every fact. The
  universality of this capacity remains disputable.
- **Constitution, not content.** `HasNaturally` means a bodily nature is
  constitutive of the knower. It is not inferred from knowing or representing
  that nature. The q.75 a.1 ad 2 distinction between a likeness in potency and
  what is naturally actual motivates this separation. Neither predicate is
  defined so as to force the disputed interference premise.
- **Scope of interference.** The source explicitly asserts that a bodily
  nature in intellect would prevent cognition of all bodies. The restricted
  formal premise retains this asserted consequence; it does not formalize a
  proof that the taste/sight analogies apply to intellect. Replacing it with
  general receptor-bias terminology would not discharge that obligation.
- **No premature substance dualism.** Q.75 a.2 ad 1–2 distinguishes a subsistent
  part from a complete human being, and q.76 a.1 calls the intellective soul the
  form of the human body. This result supplies neither an independently
  complete Cartesian person nor the component-free highest immateriality of
  the divine case.
- **No brain-independence inference.** Q.75 a.2 ad 3 still requires bodily
  phantasms on the side of the object. The different claim that understanding
  is not exercised through a bodily organ belongs to the remaining source
  range. No modern neurological finding is asserted here.

## The strongest reply at this boundary

Pasnau's author-hosted chapter, pp.353–357, was separately pinned and
materialized. His p.355 objection is recorded as
`PASNAU-Q75-COGNITIVE-PLASTICITY-REPLY`: the sensory illustrations do not
establish an analogous limitation for brain-based intellect. It attacks the
support for interference; it does not deny the encoded argument's validity.
His later content/constitution objection concerns the separate argument from
universal concepts and is not silently attributed to this first inference.

A positive physicalist research proposal is that a physically constituted
system can implement flexible representations whose object-range differs
from its constitutive properties. This is a proposal for comparison, not a
source attribution to Pasnau, a proved cognitive theory, or a claim that our
one-point model implements such a system. The burden remains to explain
representation, semantic correctness and unrestricted conceptual capacity.
The source interference premise also remains to be defended independently.

| Shared local question | Thomistic account in this batch | Positive physicalist proposal and remaining gap |
| --- | --- | --- |
| Why is cognition widely generalizable? | Universal intellectual capacity is asserted as a premise. | Flexible representations are proposed; unrestricted semantic capacity is unexplained by the toy model. |
| Must bodily constitution restrict cognitive scope? | The open interference premise says yes. | No automatic restriction is accepted; an actual realization and theory of content remain to be supplied. |
| What bodily dependence is admitted? | Phantasms are required on the object side; organ independence is a separate step. | A bodily realization is proposed; this batch supplies no empirical model. |
| What unifies the human being? | Q.76 a.1 provides the soul-as-form context, not a proof in this batch. | An organizational account would be needed; no whole-worldview replacement is yet encoded. |
| What explains consciousness and semantic norms? | Not answered by the first q.75 inference. | Not answered by the omission model. |

Reductive and nonreductive physicalism, functionalism, eliminativism,
naturalism and monism are not interchangeable. A functional description alone
need not settle its substrate's metaphysics; monism may be idealist or neutral.
Nothing here refutes those whole positions. The comparison therefore remains
open rather than winning by subtracting the interference premise.

The Utrecht-hosted Putnam *Psychological Predicates* PDF and Pasnau's
*Content Fallacy* author PDF were image-only under the repository's
`pdftotext` materializer. They were not admitted as witnesses, OCR'd outside the
contract, or replaced by search snippets. The existing candidate records the
remaining source search. The accessible Pasnau chapter is the actual witness
for the criticism recorded in this batch.

## Premise comparison and next step

Intended and actual root-path premise change: **none**. The new conditional
result is outside all existing root routes. It neither establishes its three
premises nor discharges an existing case obligation. Its conclusion is narrower
than the later anti-reductionist operation claim, and there is no argument
from it to God or Catholicism. The conditional theorem is a typed reductio,
not an opaque-atom transcription; its scope and premises are explicit.

The organ argument has since been formalized separately; see
[the bodily-organ inference](human-intellect-organ-operation.md).
`HUMAN-INTELLECT-ORGAN-INDEPENDENCE` now retains the next contiguous source
range, starting at per-se operation and subsistence in q.75 a.2. It also
retains the requirement for an affirmative rival account and the missing justification of the alleged
cognitive restriction. Subsequent subsistence and immortality claims require
separate source readings and arguments.
