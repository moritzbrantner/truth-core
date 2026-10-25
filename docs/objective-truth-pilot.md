# Objective truth pilot

The explorer's `/objective-truth/` reading guide groups a small set of canonical
statements and shows their statuses from `corpus.py frontier --json`. It is the
research demonstration requested in #207, alongside the Catholicism campaign,
not a new theory engine or a philosophical verdict.

## What is proved

`LOGIC-SOME-PROPOSITION-HOLDS` proves exactly `∃ P : Prop, P`, with `True` as
witness. `LOGIC-NOT-EVERY-PROPOSITION-FAILS` composes that theorem to prove
`¬ (∀ P : Prop, ¬ P)`. Neither has a premise or a permitted axiom. These are
facts of the encoded logic, under `DEF-LEAN-PROPOSITION-HOLDING`; there is no
inference here to ontological, robust, minimal, or attitude-independent truth.
`DISAMB-TRUE` keeps those senses separate.

The two propositions retain separate statement IDs. The explicit A → B result
uses the existential witness to contradict universal failure. The B → A result
uses B itself as the witnessed proposition. The reverse argument is not the
same thing as an identity merge. The fixture in
`scripts/testdata/objective-truth-pilot.json` compares the same canonical
statements and conditional results with no verifier records, with just the
reciprocal results, and with an independent premise-free proof of A. Python's
frontier computation establishes neither proposition in the first two cases
and both in the third. The complete corpus also has its own premise-free proof
of B; omitting its verifier record in this fixture is a comparison scenario,
not a claim that the proof ceased to exist.

## Source readings and reuse

Before extracting the four new readings, materialize `ARIST-MET-IV-5` from the
same pinned Ross/Perseus Greek snapshot already used for IV.4 and IV.7. The
whole IV.5 range and the IV.4/IV.7 context were consulted. The new readings are:

- IV.5, 1009a6–15: Aristotle's reported all-opinions-true target, with one
  unindexed truth predicate. This is not automatically modern indexed
  relativism, or a direct quotation from Protagoras.
- IV.5, 1009a9–12: the weaker opposed-opinion reading and a sibling
  contradictory-content reading suggested by the following being/not-being
  conclusion. Neither opposition nor an operation on expressed contents is
  silently equated with logical negation (`DISAMB-PILOT-OPPOSITION`).
- IV.5, 1009b9–12: Aristotle reports Democritus's alternative, no truth or truth
  at least unclear to us. This remains a source proposition without an invented
  universal quantification over knowledge.

Reuse `STMT-EXCLUDED-MIDDLE`, `STMT-EXCLUDED-MIDDLE-IRREFUTABLE`,
`STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM`, the existing IV.4/IV.7 witness
records, `TruthCore.Logic.ExcludedMiddle`, and the existing `DISAMB-TRUE` and
`DEF-OBJECTIVE-TRUTH` contrast. No second excluded-middle proposition or
redefinition of ontological truth is introduced. The pilot does not refute
withheld assent: absence of endorsement is distinct from endorsement of a
negation, just as the earlier retorsion results distinguish denial from
intuitionist withholding.

## What the tests leave open

The profile models have two agents and two test sentences. A profile assigns
endorsement propositions; an interpretation separately assigns a proposition
to each sentence at each profile. These are stipulated semantics, not a sourced
complete worldview. The earlier explanation-order `Data` fixture fixes moral
facts over selected practices; importing that bundle here would add irrelevant
moral/privation commitments. This pilot quantifies over all endorsement
profiles instead, so it uses its own narrow profile vocabulary. `DISAMB-PILOT-RELATIVITY` separates global variation, local
variation, epistemic limitation/disagreement, and the all-opinions-true schema.

- A stable logical sentence excludes the **global** claim that every sentence
  varies across profiles. The stability bridge is an explicit open premise.
- A model combines that stable sentence with **local** variation of a taste
  sentence. One logical truth does not refute every local thesis.
- Another model satisfies global variation when the logical-sentence stability
  bridge is absent. Thus that bare schema is not unconditionally self-refuting.
- A model combines disagreement and limited knowledge with profile-invariant
  truth. Neither epistemic difference alone forces relative truth.
- The all-opinions-true contradiction test requires both conflicting opinions
  and the open interpretation bridge from expressed negation to logical
  negation. Its conclusion is conditional, not a `refutes` relation against
  every relativism or a complete rival worldview. Two Boolean-content
  countermodels in that Solution keep all opinions true while dropping each
  advertised premise in turn, showing why neither may be omitted.

The two research candidates name the missing stability/negation translation
bridges and direct witnesses for the global/local/epistemic theses. The page
links these precise blockers to the synchronized graph and existing candidate
queue. The pilot closes no philosophical frontier node on the Catholicism root
path merely by adding these logical results and models.
