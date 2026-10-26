# Retorsion arguments as dilemmas

Issue #397 adds a reusable self-application schema and applies it to
relativism about truth (Plato, *Theaetetus* 170a–172b; Aristotle,
*Metaphysics* IV.8) and to scientism. Every result below is constructive and
checked with `permitted_axioms: []`. No statement is marked self-evident and
no `refutes` relation is recorded (see "Refuted or surviving" below).

## The schema (`TruthCore.Logic.SelfApplication`)

Three typed layers. Later instances (Clifford #376, verificationism #363,
Hume's scopes, global skepticism, eliminativism, EAAN) should be short
applications of them.

| Layer | Declarations | What it says |
| --- | --- | --- |
| Norm | `Norm Claim` (`scope`, `standard`), `Norm.Holds N Acceptable`, `Norm.Counterexample` | A norm holds for an acceptance predicate when every acceptable claim in scope meets the standard. |
| Dilemma | `Norm.selfApplication`, `Norm.not_holds_and_acceptable`, `Norm.not_holds_of_counterexample`; advertised as `SelfApplicationDilemma` (`LOGIC-SELF-APPLICATION-DILEMMA`) | If `self` is in scope and fails the standard: if the norm holds, `self` is not acceptable (horn 1); if `self` is acceptable, it is a counterexample (horn 2). |
| Scope needed | `ScopePremiseNeeded` (`LOGIC-SELF-APPLICATION-SCOPE-NEEDED`) | When the scope premise is dropped, a model satisfies all the rest. |
| Assertion | `TruthSense` (`absolute`, `relativeTo a`), `TruthSemantics` (`trueAbs`, `trueFor`), `TruthSemantics.trueIn`, `AssertionCommitment`, `Disquotes` | Asserting `p` in sense `s` commits the speaker to `p` being true in `s`. No bridge between absolute and relative truth is built in. |
| Demarcation | `Norm.Demarcation` (`inDomain`), `Norm.restrict`, `Norm.Concedes`, `Norm.holds_restrict`, `Norm.counterexample_of_concedes`, `Norm.demarcationTest`; advertised as `DemarcationTest` (`LOGIC-DEMARCATION-TEST`) and `DemarcationOutsideConsistent` (`LOGIC-DEMARCATION-OUTSIDE-CONSISTENT`) | A weak thesis is the strong norm restricted to a domain. Second-order test: if the weak thesis (or its criterion's statement) is inside its domain, the strong dilemma returns; if it is outside and acceptable, it is a concession, and the strong norm fails. Outside the domain the weak thesis is consistent. |

To apply the schema, choose the claim type, the norm's scope and standard, and
the acceptance predicate. Then state the scope premise (`self` in scope) and
the failure premise (`self` fails the standard) as their own named
definitions, so that `corpus.py bind-check` can bind them to statements. Then
call `selfApplicationDilemma` or `demarcationTest`, as
`RELATIVISM-NO-ABSOLUTE-TRUTH-SELF-FALSIFYING` and `SCIENTISM-STRONG-DILEMMA`
do. For a strong/weak pair (owner method, 2026-10-26), also record three
things: the demarcation criterion (sourced when attributed), the second-order
case split, and what the weak side concedes. The concession goes in as a
statement, linked by `supports` from the sourced claim that concedes it.

## Relativism

**"There is no absolute truth"** (`STMT-NO-ABSOLUTE-TRUTH-SCOPED`, global form
`STMT-GLOBAL-NO-ABSOLUTE-TRUTH`, unattributed). This is the norm with an
unmeetable standard and absolute truth as its acceptance predicate.

- Horn 1 (`RELATIVISM-NO-ABSOLUTE-TRUTH-SELF-FALSIFYING`): the thesis is in its
  own scope (`STMT-NO-ABSOLUTE-TRUTH-THESIS-IN-OWN-SCOPE`) and disquotes
  (`STMT-NO-ABSOLUTE-TRUTH-THESIS-DISQUOTES`). From these it follows that the
  thesis is not absolutely true, so an absolute assertion of it is incoherent.
  Aristotle IV.8, 1012b13-18 ("he who says all is false makes himself false
  too") is the sourced form, with unindexed truth.
- Horn 2 and the exemption (`RELATIVISM-NO-ABSOLUTE-TRUTH-MODELS`): asserted as
  true for its speaker, the self-applying thesis is consistent, but it is not
  true for the other agent. With the thesis exempted from its own scope, it can
  even be asserted absolutely.
- Cost of the exemption (`ARIST-MET-IV-8-EXEMPTION-REGRESS`, IV.8, 1012b18-22):
  given truth ascent, every iterate "… is true" of the exempted thesis must be
  exempted as well.

**The Theaetetus peritropē.** The witness is `PLATO-THEAET-169`…`172`; all of
169d–172b was read. Two sibling claims preserve the two readings of 171a-c:

- Unqualified (`PLATO-THEAET-171A-171C-PERITROPE-UNQUALIFIED-A`, horn 1,
  `PLATO-THEAET-PERITROPE-ABSOLUTE-HORN`): Protagoras holds the thesis, someone
  denies it, and "all opine what is" covers both. The scope premise is sourced
  as the rival's own commitment (`PLATO-THEAET-171A-SELF-APPLICATION-A`). Given
  also that unindexed truth respects negation, the unqualified doctrine fails.
  The proof composes the pilot's `conflictingOpinionsTest` and places the
  conflict in the thesis itself. Aristotle IV.8, 1012b15-17 is the parallel.
- Qualified (`PLATO-THEAET-171A-171C-PERITROPE-QUALIFIED-B`, horn 2,
  `PLATO-THEAET-PERITROPE-RELATIVE-HORN`): every "for X" is kept. The thesis is
  true for Protagoras; the denial is true for the denier, and the thesis is not
  true for the denier. This involves no contradiction, and the holder's
  relative truth gives the denier no reason (`DEF-REASON-TRANSFER`). On this
  reading, 171c's "true for no one, not even himself" does not follow.
- `PLATO-THEAET-PERITROPE-MODELS`: exempting the denial makes horn 1's premises
  consistent. Horn 2's premises are consistent even with nothing absolutely
  true.

**Local relativism (demarcation).** Socrates' retreat (171d-172b,
`STMT-RESTRICTED-MEASURE`) puts perceptual qualities, and the just and holy as
each city decrees them, on the relative side. Health and advantage go on the
other side, where judgements differ "toward truth". The parts are:

- Criterion (`STMT-RESTRICTED-MEASURE-CRITERION`, 172b): in the just and holy
  nothing has by nature a being of its own. Advantage, by contrast, answers to
  how things turn out.
- Concession (`STMT-RESTRICTED-MEASURE-CONCESSION`, 171e-172a): outside the
  domain, seeming does not make true-for. `PLATO-THEAET-CONCESSION-DEFEATS-MEASURE`
  proves that this defeats the unrestricted doctrine. The claim also `supports`
  `STMT-SOME-ABSOLUTE-TRUTH`, with a note. The bridge from "not made true by
  seeming" to absolute truth is open.
- Second-order test (`RELATIVISM-LOCAL-SECOND-ORDER`): if the local thesis is
  inside its own domain, it falls back to horn 2. If it is outside and
  absolutely true, it is itself an absolute truth, and global relativism fails.
  Plato's restricted doctrine is a thesis about which domains are relative, not
  about the hot or the just. So it sits outside its domain, unless its holder
  relativizes it too.

## Scientism

No witnesses yet. The defenders and critics are in copyright, and
bibliographic citation is pending (#378); candidate
`SCIENTISM-SELF-APPLICATION-WITNESSES` holds the work. The statements are
explicitly unattributed.

- Strong scientism (`STMT-STRONG-SCIENTISM`), `SCIENTISM-STRONG-DILEMMA`: the
  thesis is in its own scope and is not itself empirically established (open
  premise). If it holds, it is not established. If it is established, it is a
  counterexample. So it is not both true and established.
- Weak (restricted) scientism (`STMT-WEAK-SCIENTISM-RESTRICTED`),
  `SCIENTISM-WEAK-DEMARCATION`: if its formulation is inside its domain, horn 1
  returns. If it is outside and established, it concedes non-empirical
  knowledge (`STMT-SOME-NON-EMPIRICAL-ESTABLISHED`), and strong scientism
  fails. `SCIENTISM-WEAK-CONSISTENT` shows that the weak thesis survives.
  Its demarcation criterion (which questions science is the sole route for) is
  not sourced yet. The comparative reading ("science is the most reliable
  source") is not a norm on acceptability, and self-application does not touch
  it.

## Refuted or surviving

| Rival | Horns | Scope premise | Verdict |
| --- | --- | --- | --- |
| Global "no absolute truth" (`STMT-GLOBAL-NO-ABSOLUTE-TRUTH`, alternative to `STMT-SOME-ABSOLUTE-TRUTH`) | 1 proved; 2 consistent | unsourced for the modern thesis; Aristotle's "all" for his target | **survives** as a private relative thesis; cost: gives no one else a reason, and exemption costs a regress |
| Unqualified all-opinions-true (alternative to its failure) | 1 proved | sourced (171a) | **refuted conditionally**: open negation bridge `STMT-PILOT-NEGATION-RESPECTED`, so no `refutes` |
| Qualified measure doctrine (alternative to `STMT-MEASURE-DOCTRINE-FAILS`) | 2 consistent | — | **survives**; defeated only if its holder makes the 172a concession |
| Strong scientism (alternative to `STMT-SOME-NON-EMPIRICAL-ESTABLISHED`) | both proved | unsourced | **refuted as an established thesis, conditionally**: open non-empirical premise; scientism true but unestablished remains |
| Weak scientism | test proved; model | — | **survives**; cost: concedes non-empirical knowledge when its formulation lies outside its domain |

`refutes` is withheld everywhere for a mechanical reason. `corpus.py frontier`
counts a `refutes` relation as soon as its argument has a result, whatever the
status of that argument's premises. A `refutes` from a conditional argument
would therefore close an alternative on an open premise. A future `refutes`
needs premise-free arguments, or arguments whose premises are all closed.

## Ad hoc or independently motivated?

This is a judgement, not a theorem. The question is whether a demarcation
criterion is independently motivated or drawn just to keep the weak thesis out
of its own domain. Plato's criterion has motivation in the text: the
conventional has no nature of its own, while advantage is tested by outcomes
(172b). It does not say why the restricted doctrine itself belongs to neither
side. For weak scientism no criterion is sourced yet. A criterion that excludes
exactly the thesis's own formulation, and nothing else, is the textbook ad hoc
case. That objection is recorded here and in the candidate, not proved.

## Rejected or unencoded readings

- Reading 170a as a biconditional (seeming iff true-for). 171a uses the
  converse, but 170a states one direction only. The converse is not needed.
- Identifying absolute truth with `DEF-OBJECTIVE-TRUTH` (attitude-independence).
  An unindexed predicate could still depend on attitudes, so the two are kept
  apart (`DISAMB-ASSERTED-TRUTH-SENSE`).
- Reading 172a's "toward truth" as an explicit endorsement of absolute truth.
  This is recorded only as `supports`, with the bridge open.
- Aristotle's all-true exemption (the contrary alone not true) is symmetric to
  the encoded all-false exemption and is not separately formalized.
