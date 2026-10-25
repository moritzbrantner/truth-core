# What selects the participants? (#260)

A participation account can consistently classify some candidate beings as F
and others as not F. A classification is not yet an account of why those
beings participate. The four formal tests here isolate that gap and the extra
commitments that would address it. They do not refute Platonism, establish the
truth of a premise, or decide that every explanation must have another ground.

## Source evidence and reading boundaries

The complete materialized witnesses consulted before formalization were
`PLATO-PHAEDO-100`, `PLATO-PARM-130`, `PLATO-PARM-131`, `PLATO-PARM-132`,
`PLATO-PARM-133`, and `ARIST-MET-I-9`. Immediate alternative resources were read
in `ARIST-PHYS-II-1` and `PLATO-TIM-28`. The manifests pin the original Greek;
no translation or search snippet substitutes for these witnesses.

* **Phaedo 100c–e.** The existing thin and explanatory participation claims remain
  distinct. Socrates says beautiful things are beautiful through the beautiful,
  but does not insist on presence, communion, or another manner. The existing
  claim `PLATO-PHAEDO-100D-MANNER-OPEN` is reused. An unspecified manner is not an
  assertion that the tie is primitive, inexplicable, or ultimately adequate.
* **Parmenides 130e–131e.** Attribution through participation leads into the
  whole/part dilemma. The day analogy and sail response concern how a unity
  could be in many; the resulting impasse does not establish an exhaustive
  impossibility of nonspatial participation. The whole/part reconstruction is
  owned by #259 and is not duplicated here.
* **Parmenides 132d–133a.** The paradigm proposal is initially directed: other
  things are made like Forms. Mutual likeness and the common-Form step are
  further commitments in the exchange. Its conclusion calls for a different
  account of participation, rather than announcing the impossibility of every
  constitutive tie. The source readings and regress tests are owned by #258.
* **Metaphysics I.9, 991a8–19.** Aristotle distinguishes contributions to change,
  knowledge and being. The noninherence criticism is an argument with its own
  premises, not permission to identify all three questions. #259 records that
  bounded criticism. At 991a20–b3 the paradigm criticism asks what works looking
  to the Ideas, and distinguishes being alike from being made in imitation.
* **Metaphysics I.9, 991b3–9.** The new claim
  `ARIST-MET-991B-MOVER-REQUIRED` records the generation objection: even if Forms
  exist, participants do not come to be without something initiating movement.
  This does not show that a Form cannot explain what a thing is.
* **Physics II.1, 193a30–193b12.** Existing claims distinguish definitional form,
  separable in account, from matter and point to same-kind generation. They
  motivate an immanent-structure resource; they do not assert the synthesis of
  that resource with a separate exemplar proposed below.
* **Timaeus 28a–b.** A maker using a model is a productive role plus a standard.
  A model is not automatically a producing agent. The distinct roles do not by
  themselves entail numerically distinct entities or a universal mechanism
  selecting participants in every Form.

The stronger replies below are philosophical reconstructions with explicit open
commitments. None is attributed wholesale to a dialogue. In particular the young
Socrates' hesitation over a human Form at 130c is preserved; “Humanity” is a
conditional example of an admitted quality, not a newly sourced admission.

## Four questions and the typed interface

The module `TruthCore.Greek.Plato.ParticipationGrounding` imports the shared
`Forms.Vocabulary`; it does not create a competing Form or bearer ontology.
Entities include both Forms and particulars. Their nonidentity is a commitment.
Quality and feature types are distinct parameters.

| Question | Representation | What is not obtained automatically |
| --- | --- | --- |
| Which candidates are F? | `Exemplifies`, `Participates`, `Coextension` | A dependence or productive mechanism |
| What makes their participation obtain? | `Grounds` between tagged facts | Asymmetry, actuality, causal production |
| What produces a bearer or its structure? | `Produces` | Constitutive grounding or identification |
| How does an agent identify a bearer as F? | `Identifies` | Being F or infallible knowledge |

The existing `Forms.Explains` remains a putative explanation-of-being relation.
Its extension alone supplies no selector. `Fact.base`, `Fact.participation` and
`Fact.exemplification` give the grounding relation distinct typed relata.
A token is not an assertion that a fact obtains. `Base x g` is an independently
supplied model input, not an abbreviation for `Exemplifies x human`.

`SelectionLaw` additionally asserts participation iff the selected base feature.
`GroundedSelection` additionally asserts base-to-participation dependence.
Neither is part of `Coextension`. Calling the feature “essence,” “organization,”
or “relevant likeness” supplies neither law. `AsymmetricGround` is an optional
norm for the specified metaphysical relation; it is not imposed on resemblance,
material implication, knowledge, or all uses of the word “cause.”

## The mechanically checked consequences

Each row has a frozen Challenge theorem, separate Solution, argument, inference,
result record and Comparator configuration with no permitted axioms. These are
structured finite model constructions or equivalence/relational deductions,
not opaque propositional transcriptions. Lean and Comparator verify only the
stated formal consequences.

| Result | Premises and steps | Narrow conclusion |
| --- | --- | --- |
| `PARTICIPATION-UNDERDETERMINED` / `assignmentUnderdetermined` | No external premise. Build two four-entity interpretations satisfying `Generic`, with the same stipulated background and one fixed base interpretation, and different assignments. | The listed principles and base do not select the participants. |
| `PARTICIPATION-GROUNDING-INDEPENDENT` / `groundingIndependent` | No external premise. Give one assignment both an empty explanatory account and a base-to-participation account. Distinct fact constructors exclude reverse edges; productive and identification relations differ too. | A selection biconditional does not determine grounding, production or identification. A noncircular enriched interpretation is compatible. |
| `PARTICIPATION-NO-CIRCLE` / `noCircularExplanation` | Explicit open `AsymmetricGround` premise. The two ground edges for one bearer, Form and quality contradict that premise. | The specified two-edge explanatory circle is excluded under this norm. An iff alone is not such a circle. |
| `PARTICIPATION-AGREEMENT` / `selectorAgreement` | Explicit open `SharedSelector` premise: coextension in each interpretation, matching base extensions, and selection laws. Compose F ↔ participation ↔ base ↔ participation ↔ F. | Independent selectors with those laws determine classification on common admitted Forms and particulars. They do not yet ground it. |

`Generic` comprises property instances, one-over-many, uniqueness,
participation-predication, nonidentity, ontological separation, putative
explanation, exemplar participation, intelligibility/stability, essential
characterization and coextension. This is a limited synthesis for testing,
not the definition of all realism. The two interpretations fix even `Explains`
to True. That generous stipulation tests whether *adding the label* constrains
the assignment; it does not establish that the interpretation explains anything.

In the first model 0 is the Form, 1 and 2 are candidate beings and 3 an additional
bearer. Interpretation A selects 1 and 3; B selects 2 and 3. Their fixed base
holds of 1 and 3. The same-background predicate lists exactly the fixed fields.
Only assignment A obeys the corresponding base-selection law. Thus adding that
law would exclude B, as the agreement theorem confirms. Nothing changes real
biological facts while claiming that Socrates remains biologically human:
“Socrates” and “horse” are only optional mnemonics for candidate labels 1 and 2.
The question concerns candidate beings before classification, not why some
already classified humans are human.

In the second construction the richer account has base-to-participation edges,
a productive extension and an identification extension; the empty account has
none. Both have exactly the same F/participation vocabulary and base. This
noncircular model is a formal strongest-case possibility, not an independently
sourced or adequate metaphysical mechanism. In particular finite `Produces`
and `Identifies` extensions do not encode a full theory of generation or knowledge.

## Strong replies and the remaining burden

| Reply | Best version and source bearing | Effect and additional commitment |
| --- | --- | --- |
| Primitive participation | A constitutive tie is a legitimate explanatory stopping point; the further question need not always have a deeper answer. Phaedo's open manner and Parmenides' call for another participation account leave room for this proposal without asserting it. | Avoids the specified circle by withholding a reverse grounding edge. It accepts a primitive distribution and must defend its adequacy or reject the demand for further selection explanation. Consistency is not adequacy. |
| Exemplification through essence | A bearer is F in virtue of its constitutive nature; the separate Form articulates what F is rather than mechanically pushing an F-label onto a bare thing. The essential reading of “beautiful itself” and Aristotle's definitional-form resource motivate distinct components. | A substantive independent essence can be the base; its selection and grounding bridges need defense. Essential characterization of the Form alone does not discriminate between candidate bearers, as the first model shows. The synthesized account is not attributed to Plato or Aristotle. |
| Imitation or resemblance | A bearer is made like a paradigm in a specified respect. Directed imitation need not be reciprocal generic likeness; the 132d proposal is stronger than a bare shared adjective. | Requires a relevant-respect account and a reason this bearer is made like this exemplar. #258 tests the additional reciprocal-likeness/common-Form premises of the regress. Withholding them prevents that argument, but does not itself supply the participant-selector. |
| Immanent structure plus separate exemplar | The actual structure constitutes F-ness; the separate Form supplies its intelligible standard. Physics II.1 supports the immanent component and Timaeus 28 the model resource. | Can be noncircular, as the directed model illustrates. Requires the base-selection and grounding commitments and an account of what the separate exemplar contributes beyond the immanent structure. Aristotle's form separable in account is not identified with a separate Platonic entity. |
| Formative causes | An agent or natural generative process makes the relevant structure, using an exemplar as standard where appropriate. Same-kind generation and Timaeus' maker/model distinction are concrete resources. | Addresses the selection question only with an actual mechanism, relevant conditions and application to candidate beings. Aristotle's mover objection shows why merely adding a paradigm does not complete a generation account. Constitution, production and epistemic recognition remain different tasks. |

The strongest combined reply uses an independently described constitutive
structure, a defended base-selection law, a directed grounding commitment and,
where generation is at issue, formative conditions explaining how that structure
arises. It can retain a separate exemplar as the intelligible standard while
withholding the reverse explanatory edge that would produce the tested circle.
The second model shows compatibility of these ingredients; it does not justify
their truth or establish the necessity of the separate exemplar. A primitive-tie
reply remains an alternative if the stronger explanatory demand is rejected.

The residual frontier is therefore **which actual feature or mechanism selects
these candidates, why its grounding/selection laws hold, and what explanatory
work the separate Form performs**. `STMT-PARTICIPATION-SELECTION-LAW`,
`STMT-PARTICIPATION-GROUNDED-SELECTION`, the reply statements and
`STMT-PARTICIPATION-RESIDUAL` retain those obligations. Source `supports` links
record evidential bearing, not entailment. `attacks` links record the explanatory
objection without replacing an inference application or marking all Platonism
refuted. The three residual candidates identify the primitive, essence-selector
and exemplar-contribution investigations. No root premise about Catholicism is
closed by an unexplained participation label.

## Fidelity self-sweep and reproducibility

The formal proofs are accepted as consequences of the displayed meanings:
the model witnesses have explicit predicate extensions; the circularity test
uses two grounding edges rather than two material implications; the selector
test composes five biconditionals. The new source claim is narrower than a
universal causal refutation. The reply syntheses and all selection/grounding
bridges are explicitly unattributed. Shared and new definition/disambiguation
links distinguish every load-bearing sense, including immanent/separate form,
essential/ordinary predication and the four explanatory questions.

Shared conventions resolved at source revision
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`. Source integrity, interpretive fidelity
and formal consequence remain independent review boundaries.
