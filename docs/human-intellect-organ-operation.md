# Human intellect: the bodily-organ inference

The second q.75 a.2 inference is distinct from the first result in
[the non-bodyhood note](human-intellect-incorporeal.md).
`AQUINAS-ST-I-Q75-A2-INTELLECT-NONORGANIC` conditionally excludes a bodily
instrument of intellectual exercise. It reuses `HumanIntellect.Model`,
`UniversalBodilyCognition` and `BodilyDeterminacy`, without redefining the
existing relations or restating the old conclusion as a premise.

## Verified reading

The full Latin `AQUINAS-ST-I-Q75-A1-A2` and `AQUINAS-ST-I-Q76-A1` witnesses
were materialized and read, including objections and replies. Q.75 a.2 co.,
Corpus Thomisticum anchor **31460**, first denies that the intellectual
principle itself is a body, then separately denies intellectual exercise
through a bodily organ. The organ's determinate nature is said to impede
cognition of all bodies, with the colored-vessel illustration.

The two interference readings have different subjects. The old
`NaturalBodilyInterference` concerns the nature constitutively present in the
intellectual principle. The new `OrganBodilyInterference` concerns the nature
present in an instrument through which that principle's intellectual
operation can be exercised. Neither predicate follows just by naming the
other. The new operation relation is additional vocabulary, without changing
the shared `Model`.

Q.75 a.2 ad 3, anchor **31463**, expressly requires the body on the side of the
object, comparing phantasms to color for sight. It distinguishes this from an
organ through which the intellectual action is exercised. Q.76 a.1 ad 1,
anchor **31513**, restates the non-organic operation claim while retaining the
soul as the body's form. These contexts rule out reading this result as the
absence of every bodily condition or as a complete Cartesian human person.

## Prose beside Lean types

For an existing cognitive model `m`, a designated principle `i`, and a typed
relation `through : Principle → Principle → Prop`:

| Record | Type/content |
| --- | --- |
| Existing `STMT-HUMAN-INTELLECT-UNIVERSAL-BODILY-COGNITION` | `∀ n, m.BodilyNature n → m.CanUnderstand i n` |
| Existing `STMT-EVERY-BODY-HAS-DETERMINATE-NATURE` | `∀ b, m.IsBody b → ∃ n, m.BodilyNature n ∧ m.HasNaturally b n` |
| `STMT-ORGAN-BODILY-NATURE-BLOCKS-UNIVERSAL-COGNITION` | `∀ b n, through i b → m.IsBody b → m.BodilyNature n → m.HasNaturally b n → ¬ UniversalBodilyCognition m i` |
| `STMT-HUMAN-INTELLECT-USES-NO-BODILY-ORGAN` | `¬ ∃ b, m.IsBody b ∧ through i b` |

`through i b` is capacity for intellectual exercise through an instrument,
not just one actual episode. The conclusion therefore negates that capacity
for each body, rather than merely saying that no present episode happens to
use one. It does not quantify over every modern notion of physical
realization. Cognitive scope remains distributive capacity across bodily
natures, not actual omniscience or simultaneous knowledge of all facts.

Assume an organ exists. Bodily determinacy provides its naturally constitutive
nature. The open organ-interference premise then denies the universal
capacity supplied by the first premise. This constructive contradiction
establishes the conclusion without selecting a particular unknowable object
from a negated universal. The earlier `intellectIsNotBody` theorem has a
different conclusion and is not used where its content would not suffice.

The frozen Challenge and separate Solution also contain three omission
controls. Two one-point models explicitly exhibit an organ and failure of
the omitted scope or determinacy premise while retaining the other premises.
The third model has two individuals: `false` is a non-bodily intellect, and
`true` is a bodily instrument. It satisfies universal scope, bodily
determinacy, the old `NaturalBodilyInterference`, and `IntellectIsNotBody`,
while the new organ-interference premise fails. Thus even the already proved
non-bodyhood conclusion and its interference premise cannot silently supply
the organ-level constraint. These models demonstrate formal-schema
non-entailment only; their primitive relations implement neither a cognitive
system nor a metaphysically possible world.

## Fidelity, criticism and rejected shortcuts

- The colored-vessel example illustrates organ interference. It is not
  encoded as a proof that every bodily organ must restrict intellectual
  scope. The universal application remains an explicit open premise.
- Bodily constitution and represented cognitive objects remain different
  relations. Neither having a thought about a nature nor representing it
  implies possessing it constitutively.
- Non-bodyhood, non-organic exercise, object-side bodily dependence and
  per-se subsistence are separate claims. No step from the first to the
  second is hidden in the definition of the operation relation. No step from
  the second to subsistence is supplied here.
- The Latin's subsequent per-se-operation and subsistence passages have not
  been silently incorporated into this conclusion. They remain the next
  source range in `HUMAN-INTELLECT-ORGAN-INDEPENDENCE`.

The already pinned and materialized Pasnau chapter, **p.355**, explicitly
criticizes both interference premises, (2a) and (2b): the taste and sight
illustrations do not establish an analogous cognitive limitation if intellect
relies on a brain. The existing claim `PASNAU-Q75-COGNITIVE-PLASTICITY-REPLY`
therefore also attacks the new organ-interference statement. This is a reused
criticism, not a new source attribution or a proof of a physicalist theory.

The affirmative rival proposal remains that a physically constituted system
can sustain flexible representations whose objects differ from its own
constitutive properties. The new finite control shows why the remaining
formal premises do not exclude such an interpretation, but does not explain
semantic content, correctness, cognitive range or conscious experience. A
complete physicalist, functionalist or naturalist account still needs those
answers; monism and physicalism are not identified. Neither side wins by
omitting an open premise or by treating a sensory analogy as a demonstrated
universal law.

## Premise comparison

Intended and actual root-path change: **none**. This conditional argument is
outside the existing Catholicism routes. It reuses two existing open premises
and adds a separately sourced, still open organ-interference premise. No root
premise is discharged and no refutation of physicalism, naturalism or monism
is claimed. The result is a typed reductio with an actual organ-nature
witness, not an opaque-atom or single-application transcription.

Issue #419 remains open. The next step concerns the meaning of intellectual
operation *per se* and the inference to subsistence, alongside the outstanding
justification of both interference premises and the affirmative rival account.
