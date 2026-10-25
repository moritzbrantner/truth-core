# Platonic Forms: bounded readings and open commitments

The foundation for #257 uses one shared vocabulary in
`TruthCore/Greek/Plato/Forms.lean` and five bundles in
`TruthCore/Comparison/PlatonicForms.lean`. These are independently evaluable
research readings, not a claim that Plato held every conjunct in every dialogue.
No bundle entails an incompatibility with Catholicism by definition.

All requested ranges were read from materialized Burnet Greek witnesses at
PerseusDL/canonical-greekLit revision
`a065c359aab33c33bd17ddc2cac7d27fdc9cd870`:

| Range | Reading and limits |
| --- | --- |
| Phaedo 99d–102a | Hypothetical inquiry; Forms as explanatory causes; the safe answer at 100c–e leaves the manner of participation open. Thin predicative and explanatory readings are siblings. Beautiful-itself has literal self-predicative and essential-characterization siblings; neither supports universal self-predication without an additional premise. |
| Parmenides 128e–130e | The young Socrates distinguishes Forms from their participants and accepts separate justice, beauty and goodness. Numerical distinction and ontological independence are separate readings of 130b. The human/fire/water range is uncertain, and hair/mud/dirt are resisted; Parmenides challenges this hesitation. No universal range is silently adopted. |
| Republic V 475e–480a | Many sensible F things contrast with the stable Form; the knower distinguishes Form and participants. Opposite appearances at 479 are not encoded as a contradiction in one respect. The epistemic context is recorded in prose rather than claimed as a proved epistemology. |
| Republic X 596a–598c | One Form over many commonly named things; bed/table Forms guide artisans. The artifact-domain exemplar reading does not identify a painter’s copying of an artifact’s appearance with directly copying a Form. |
| Timaeus 27d–29b | Being/becoming and a stable intelligible model for the cosmos. Reuses the existing page-28 witness and the independent `STMT-CAUSE-PRINCIPLE-BROAD`, `STMT-CAUSE-PRINCIPLE-DISTINCT` and `STMT-COSMOS-GENERATED` records; a cause of generation is not the Phaedo cause of being F or automatically the exemplar. |
| Timaeus 51b–52d | Intellect/true opinion and three kinds: intelligible being, sensible image, receptacle. The Lean projection records intelligibility/stability and exemplar relations; the contextual claims retain the third kind and epistemic argument without pretending to formalize them. |

The passage manifests cover whole Stephanus pages, including context beyond the
precise locators. Existing `PLATO-TIM-28` remains the only witness binding 28.
For example, run `python3 scripts/source_evidence.py materialize PLATO-PHAEDO-100`.
Greek source readings have no translation basis flag. A hash verifies the consulted
bytes, not the correctness of an interpretation.

## Commitments and variants

Forms and particulars share an entity type. `FormOf`, `Exemplifies` and
`Participates` assert no theory merely by being fields. A quality can include a
respect; being large relative to one person and small relative to another is not
an unrestricted contradiction. `Admitted` specifies each reading’s range; it is
not every predicate. Separate artifact and ethical-quality readings use separate
interpretations of this parameter.

| Bundle | Explicit commitments |
| --- | --- |
| Classificatory | At least two F particulars; a common Form for each admitted quality; uniqueness; predicative participation; Form/participant nonidentity. Explanation and independence remain open. |
| SeparatedCausal | The preceding commitments plus ontological independence and explanatory participation, with no mechanism settled. |
| Exemplar | The causal synthesis plus directed model/copy relations and intelligible, unchanging Forms, for the selected domain. |
| SelfPredicating | The exemplar synthesis plus the **unattributed open generalization** that each Form itself exemplifies its quality in the ordinary sense. |
| Essential | The exemplar synthesis plus the **unattributed open generalization** that each Form has its essential characterization. No bridge to ordinary exemplification is assumed, and ordinary self-predication is not denied. |

Every conjunct has its own statement. Source-specific beauty self-predication is
kept separate from the universal generalization. `HumanFormAdmitted` is another
optional open commitment, not a claim that Socrates settled the question.
Definitions and disambiguations distinguish form, participation, likeness, cause,
man/human, is F, and the two senses of separation. Definitions describe this
relational interface stipulatively; they do not substitute for proofs of its
philosophical adequacy.

## What the formal result establishes

`PLATONIC-SELF-PREDICATING-CONSISTENT` constructs a model with one Form (0), two
distinct particulars (1 and 2), and one admitted quality. All three exemplify the
quality, and only the particulars participate in the Form. The ten conjuncts of
`SelfPredicating` hold together. The argument’s `commitment_statement_ids` lists
exactly those conjuncts; there are no truth premises or permitted axioms.

The proof checks explicit relational extensions, not unconstrained propositional
letters. It establishes **compatibility of this encoding only**. Its explanation,
independence and intelligibility predicates have extensions, not a theory proving
that those extensions are adequate philosophical explanations. It does not prove
Platonism, close a Catholic-case premise, or establish consistency after further
assumptions are added. In particular, one-over-many ranges over particulars;
it does not apply to every collection containing a Form merely because the Form
self-predicates. Generic likeness and essential characterization are unused in
this result and are interpreted as false in this witness.

## Comparison questions and next branches

| Question | Current answer |
| --- | --- |
| Why do many particulars share a property? | A common Form supplies classification; the causal variant additionally proposes participation as explanation. Its adequacy remains open. |
| Why does this bearer participate and another not? | Unexplained here; [#260](https://github.com/moritzbrantner/truth-core/issues/260) studies explanatory grounding versus classification. |
| Is the Form independent of its bearers? | Explicit open commitment in the separated variants; numerical nonidentity alone gives no answer. |
| Is the Form itself F? | Two optional senses and two source-specific beauty readings; no automatic universal answer. |
| Does self-predication generate a regress? | No verdict here. [#258](https://github.com/moritzbrantner/truth-core/issues/258) studies Third Man and likeness regresses with each added assumption exposed. |
| Can participation be whole/part sharing, and how can separated Forms be known? | Unexplained formally; [#259](https://github.com/moritzbrantner/truth-core/issues/259) studies these difficulties and responses. |
| What explains cosmic order? | The Timaeus cosmos exemplar is a sourced proposed answer; the existing generated-cosmos/cause statements remain independent. No adequate cosmology is proved. |
| Existence as a whole, mind, moral obligation, historical revelation? | Unexplained by these bounded bundles. A Form of goodness is not by itself an account of moral obligation or Catholic revelation. |

The later issues are argument branches, not automatic verdicts on every variant.
They should import this shared vocabulary, reuse statement IDs only when their
meanings coincide, and source any additional premises before claiming a refutation.
