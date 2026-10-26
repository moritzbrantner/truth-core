# Human intellect: qualified subsistence in q.75 a.2

The result `AQUINAS-ST-I-Q75-A2-INTELLECT-SUBSISTENCE` is a
**transcription (instantiation)** of the remaining conditional inference.
It composes the exact existing `intellectIsNotBody` and
`intellectUsesNoBodilyOrgan` theorems. It does not establish the two further
source principles, close a root obligation, or complete issue #419.

## Verified reading

The entire pinned `AQUINAS-ST-I-Q75-A1-A2` and `AQUINAS-ST-I-Q76-A1`
were materialized and read. At 31460 (q.75 a.2 co.) Aquinas moves from
non-bodyhood and no bodily organ to operation of the intellectual principle
itself, without bodily participation, then invokes correspondence between
manner of operation and manner of being. The second inference is not proved
by calling the first inference incorporeality. Our explicit attribution
premise preserves this missing positive step.

At 31461–31462 (ad 1–2), non-inherence as accident or material form is
distinguished from completeness in a species. A part can be called subsistent
in the former qualified sense; more properly the human being understands
through the soul. The conclusion formalizes only that weak non-inherence.
At 31463 (ad 3) bodily phantasms remain required on the object side. This
is compatible with denying bodily participation as an instrument of exercise.
At 31512–31517 (q.76 a.1 co. and replies) the soul remains form of the human
body. Non-inherence here cannot be read as absence of all dependence,
componenthood, or every form–body relation. Although the surrounding source
also discusses persistence after bodily destruction, that is not a theorem
of this batch; q.75 a.6 requires its own reading and argument.

## Prose and types

For the reused model `m`, instrumental relation `through`, additional
operation-attribution interface `a` and designated principle `i`:

| Proposition | Lean content |
| --- | --- |
| Own intellectual operation | `∃ op, a.IntellectualExercise i op ∧ ¬ a.BodyShares op` |
| Attribution bridge | `IntellectIsNotBody m i → IntellectUsesNoBodilyOrgan m through i → PerSeIntellectualOperation a i` |
| Operation/existence correspondence | `∀ p, PerSeIntellectualOperation a p → SubsistsInWeakSense a p` |
| Weak subsistence | `¬ a.InheresAsAccidentOrMaterialForm i` |
| Complete subsistence, never concluded | `SubsistsInWeakSense a i ∧ a.CompleteInSpecies i` |

The operation domain indexes exercise kinds, rather than asserting an actual
thinking episode at a particular time. The existential still needs a witness:
a universal cognitive capacity or a negative no-organ statement cannot supply
one. The attribution premise bears that entire burden. An empty operation
domain or a model with no attributed exercise fails the bridge whenever the
two antecedents hold. No nonemptiness hypothesis is hidden. The
`attributionOmission` model explicitly preserves all four old premises and
the operation/existence principle while lacking any intellectual-exercise
witness and failing subsistence. `existenceCorrespondenceOmission` preserves
all four old premises and positive attribution while failing subsistence.
These are finite schema controls, not metaphysically possible worlds.
The completeness control shows that weak subsistence and own operation
remain compatible with failure of species completeness. No model supplies
an empirical theory of representation, consciousness or personal unity.

The proof applies the two prior reductios, then the attribution conditional,
then instantiates the operation/existence principle. Because the last premise
already asserts the relevant consequence, the result is flagged transcription;
the typed vocabulary and prior reductios do not turn this into an independent
defense of that principle.

## Strongest reply and rejected shortcuts

`PASNAU-MIND-HUMAN-NATURE-353-357` was separately materialized and read.
On p.353 Pasnau distinguishes independent operation, possible separate
existence and immortality: the latter conclusions need supplementary
principles. He calls those supplementary principles disputable; his p.355
sensory-analogy objection continues to challenge the earlier interference
premises. This note does not attribute a developed positive physicalist model
to that criticism.

An affirmative rival proposal is that a human organism has cognitive powers
realized by flexible bodily organization; an abstract description of an
operation or its object-range need not determine the mode of existence of
its bearer. At this boundary it may contest attribution to a distinct
non-inhering principle and the operation/existence correspondence, rather
than deny the conditional theorem. This proposal still owes an account of
semantic correctness, broad conceptual capacity, conscious experience and
human unity. No sourced realization or whole-worldview comparison is supplied
here. Hylomorphism's own reply preserves operation attribution through an
incomplete part while retaining the human composite as the proper agent;
that distinction constrains the interpretation but does not independently
establish its metaphysics.

Rejected shortcuts: absence of a bodily organ is not an exercise witness;
absence of a body predicate is not non-inherence; object-side dependence is
not bodily instrumental participation; subsistent part is not complete person;
subsistence is not immortality. Nor does any of this infer God or Catholicism.

## Premise comparison and continuation

Intended and actual root-route change: **none**. The argument remains outside
all root routes. Its six open premises are the existing universal bodily
cognitive capacity, bodily determinacy, intrinsic bodily interference, organ
bodily interference, plus the explicit operation-attribution bridge and
operation/existence correspondence. Four earlier premises are retained, two
are added, none is discharged. This is a connection, with no claimed root
relocation. The omission controls establish the necessity of the two added
premises for this schema, not closure of any premise.

The existing `HUMAN-INTELLECT-ORGAN-INDEPENDENCE` candidate continues the same
range: defend the attribution and operation/existence principles, and supply
a pinned affirmative rival with comparable semantics. Q.75 a.6 is a separate
future argument, not an automatic consequence of these records. Issue #419
remains open.

The affirmative-source search and the next interference obligation are updated
in [the rival assessment](human-intellect-rival-assessment.md). The new witness
partly fills the source gap; it does not discharge any of these six premises.
