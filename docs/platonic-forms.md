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

## Phaedo's positive explanatory proposal and its scope (#360)

The 2026-10-28 comparison reread the **complete materialized Greek pages
99–102**, not an isolated participation formula. It reuses the existing
`PLATO-PHAEDO-99` through `PLATO-PHAEDO-102` witnesses at the immutable Burnet
edition revision above, blob `d76020aa770f5a005e04a6ef0ae3ba60cf1faf86`.
No translation, new edition, or competing passage binding was added.

Four source readings expose the work the proposed account is meant to do:

| Locator and claim | Positive proposal and exact limit |
| --- | --- |
| 99a–b, `PLATO-PHAEDO-99A-ENABLING-BODY` | Socrates grants that bones, sinews and the other bodily prerequisites are needed to carry out his decisions, while refusing to replace the explanation of his intelligent action by those conditions rather than his choice of what is best. This is not a denial of bodily necessity or a proof that every physical explanation is inadequate. |
| 99b–c, `PLATO-PHAEDO-99BC-EXPLANATORY-SEARCH` | He wants an account connecting the arrangement of things to what is best and fitting, but says he has not found or learned it before offering the second voyage. The acknowledged explanatory aspiration must not be silently counted as fulfilled by the subsequent safe answer. |
| 100b, `PLATO-PHAEDO-100B-FORMS-HYPOTHESIS` | Beauty itself, goodness, greatness and the like are the proposed starting hypothesis, granted by Cebes for the argument. This is not an independent demonstration of their existence, uniqueness or maximal degree; neither does its hypothetical role show that Socrates disbelieves them. |
| 101b–c, `PLATO-PHAEDO-101BC-TWONESS-SAFE-ANSWER` | The safe answer appeals to twoness for being or becoming two, setting aside addition and division as the answer to that question. It proposes an intelligible account of the relevant character, rather than merely asserting that a conventional word applies. It does not supply a productive mechanism or show that addition and division never happen. |

Read together with the existing 100c–e explanatory and manner-open claims,
this is an affirmative proposal: particulars are F through a relevant Form,
while the way participation occurs remains unsettled. It asks for more than a
list of indispensable circumstances or a name convention. The distinct issue is
whether the proposed Form actually supplies that explanatory advantage. The
presence of an `Explains` relation in a formal model does not answer that issue.
Nor does the safe answer alone prove a complete cosmology, universal efficient
production, a numerical maximum, or a highest unique source.

### Strong replies answer different parts of the question

The following are comparison options, not extra historical claims attributed
to this Phaedo range. The immanent and concept/sign proposals need their own
source-specific arguments; neither is identified with `Forms.FormOf` merely
because it can answer a related question.

| Shared question | Separate-Form proposal | Immanent-form proposal | Concept/sign proposal |
| --- | --- | --- | --- |
| Why are several bearers F? | A common intelligible Form is proposed as the explanation through participation. Its independence and explanatory adequacy need defense. | The bearers' intrinsic organization or nature supplies the relevant character. The structure, its actual application and its explanatory sufficiency need defense. | Correctly applicable concepts can classify many individuals without an additional shared entity. Why this concept applies to these individuals, and whether classification exhausts the explanation of being F, remain separate questions. |
| What brings an F thing about? | A proposed standard or being-F account is not automatically a producer. | A generative account can explain the acquisition of a structure, with its actual mechanism and conditions still required. | Denying a separate Form does not remove the obligation to give whatever productive explanation the phenomenon requires. |
| How can F things be known? | Intelligibility is a positive proposed resource, not an established account of our reliable access. | Cognition of intrinsic features is a proposed route; adequacy and reliability are open. | Mental or linguistic representation is a proposed route; its correctness and reliability are open, rather than guaranteed by predicability. |
| Does this yield a maximal or ultimate being? | The Phaedo safe answer does not supply a degree order or a theorem identifying a maximum and its causal scope. | Intrinsic structure alone is not such a theorem either. | An account of common predication alone is not an answer to the ultimate-explanation question. |

These replies therefore cannot be ranked by counting their missing words or
rejecting one preferred premise. A stronger comparison needs a defended common
explanandum and application conditions. A concept/sign account might deny the
need for the separate entity while still offering an explanation of shared
predication. An immanent account might retain intelligible natures while
rejecting their independent existence. The separated account can insist that
neither reply yet explains the unity or intelligibility it invokes. None of
those challenges is already resolved by the present source readings.

### Exact theorem reuse and remaining bridges

No new formal theorem is advertised for this batch. The relevant checked
discriminators already exist:

- `TruthCore.Results.Greek.Plato.ParticipationGrounding.groundingIndependent`
  (`PARTICIPATION-GROUNDING-INDEPENDENT`) holds the shared classificatory and
  Form commitments fixed while varying separately interpreted directed
  grounding, formation and identification. It prevents treating those
  explanatory roles as the definition of participation. It does not show that
  no richer participation account could supply them.
- `TruthCore.Results.Greek.Plato.ThirdMan.Sensitivity.sensitivityModels`
  (`THIRD-MAN-SENSITIVITY`) preserves relevant core commitments in explicit
  omission controls, including essential characterization without ordinary
  self-predication. Thus ordinary self-predication, unrestricted formation and
  iteration cannot be silently appended to obtain a refutation of all
  Platonism.

`Forms.ParticipationPredication` and `Forms.ExplanatoryParticipation` retain
their exact meanings. The former concerns ordinary predication; the latter
adds a putative explanation, without establishing its truth or adequacy.
Neither is identified here with Aquinas's degree order, genus relation, causal
preexistence, or efficient-cause relation. To advance the Fourth Way targets in
#360, one must still justify those **interpretive and philosophical bridges**,
including any ordered scale, existence of a maximum, and the claim that the
maximum causes the others. A proof in the separate degree-order arena is not
a joint participation model or an automatic Plato-to-Aquinas adapter.

The existing candidates `PARTICIPATION-ESSENCE`,
`PARTICIPATION-EXEMPLAR-CONTRIBUTION` and `PARTICIPATION-PRIMITIVE` retain the
decisive selection/constitution, exemplar-contribution and primitive-tie
questions. No candidate is closed merely because the Phaedo proposes a safe
answer. `ATTEMPT-PLATONISM-PHAEDO-EXPLANATORY-SCOPE` records the exact source
reading and rejected shortcuts.

Premise comparison: **no existing premise added, removed or discharged** on
any root route. Four independent prose source readings and their sense records
clarify the positive proposal and its limits; they introduce no argument,
result, axiom or new dependency. Source integrity, source fidelity and formal
consequence remain separate. The bounded Phaedo investigation does not close
#360 or adjudicate all Platonism.
