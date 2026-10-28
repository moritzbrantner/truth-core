# Natural goodness: function, due perfection and practical authority

This #369 slice distinguishes positive proposals and their remaining bridges.
It adds source commitments, not a proof of moral realism, an additional
verified result, or a claim that a complete rival has been eliminated.

## Witnesses read

The following complete pinned ranges were materialized and read before these
readings. The manifest retains the exact edition, immutable revision and blob;
the quotations below are only short identifying phrases.

- `ARIST-EN-I-7`: *Nicomachean Ethics* I.7, Greek Perseus edition
  `urn:cts:greekLit:tlg0086.tlg010.perseus-grc2`, especially
  1097b22–1098a20; the whole chapter supplies finality/self-sufficiency and
  the function argument's context. The new selector uses the existing
  `ARIST-EN` snapshot, not an unpinned modern translation.
- `AQUINAS-ST-I-Q5-A1`: the complete Leonine/SCTA article, including ad 1.
- `AQUINAS-ST-I-II-Q94-A2`: the complete Leonine/SCTA article, including ad 2.

The materialization commands are `python3 scripts/source_evidence.py materialize`
followed by the passage ID. Source integrity identifies the consulted text;
it does not settle the interpretation or truth of the account.

## What the positive argument actually supplies

Aristotle first asks what the specifically human function is; he does not
simply identify whatever happens to be preferred with human good. He contrasts
vegetative and perceptual life with rational activity, distinguishes a
practitioner from a good practitioner by excellence of exercise, and concludes
with excellent activity of soul across a complete life. Thus the positive
proposal offers a standard capable of correcting a current preference: ask
whether the agent's activity realizes the appropriate excellence of its
characteristic function. The analogy is a proposed reason for this account,
not a Lean proof that humans have that function or that distinctively human
activity is automatically normatively superior.

The exact new readings are deliberately limited:

| Reading | Bound type, with primitive predicate arguments suppressed | What it leaves open |
|---|---|---|
| `STMT-FUNCTION-EXCELLENCE-NECESSARY` | `∀ x r f, ExerciseOfRole x r → HasFunction r f → GoodQuaRole x r → ExcellentExercise x f` | Which roles/functions are appropriate and which excellence standard is correct. This assesses an exercise, not the claim that a skilled practitioner always acts well, and implies no moral verdict on the person. |
| `STMT-HUMAN-GOOD-ACTIVITY-CONDITIONS` | `∀ life, HumanGood life → RationalActivity life ∧ VirtuousActivity life ∧ CompleteLife life` | Function identification, virtue ordering, sufficiency, an actual happy-life witness and practical authority. |
| `STMT-ULTIMATE-DUE-PERFECTION-REQUIRED` | `∀ x, ¬ UltimateDuePerfection x → ¬ GoodSimply x` | What perfection is due, whether anything lacks it, and the positive/converse directions; no classical contraposition is silently added. |
| `STMT-REASON-REGULATED-INCLINATIONS-NATURAL-LAW` | `∀ i, HumanNaturalInclination i → RegulatedByReason i → PertainsToNaturalLaw i` | What correct rational regulation consists in and why it is authoritative. |

`VirtuousActivity` in the second type means activity according to the
appropriate virtue, with Aristotle's best/most-complete qualification where
several virtues are at issue. The formalization does not independently model
that ordering. The source condition is preserved as the predicate's stated
meaning, rather than advertised as a theorem about arbitrary excellence.

Aquinas' q.5 ad 1 is an important control on the positive proposal. First
substantial actuality makes something *being simpliciter*, but ultimate due
perfection is relevant to *good simpliciter*. Having some actuality is not
therefore already an all-things-considered verdict of excellence. The existing
`GoodnessIsActualityReading` is explicitly **per perfection** and already says
its type does not formalize the ad 1 distinction. No repair or strengthening of
that existing claim is warranted. This slice adds a sibling reading instead.

The q.94 ad 2 qualification also matters: natural inclinations, including
concupiscible and irascible appetite, pertain to natural law **insofar as
regulated by reason**. Reading it as approval of every actual urge would drop
a source condition. Conversely, merely defining correct reason as conformity
to the desired conclusion would not defend the account.

## Symmetric comparison of replacement accounts

The source-backed naturalistic proposals and their precise locators are already
recorded in [the naturalistic-realism comparison](../naturalistic-moral-realism.md).
They are affirmative rivals, not the denial of evaluative facts.

| Shared question | Function/teleological account in this slice | Railton/Boyd's existing naturalistic proposals | Attitude/plan-based alternative |
|---|---|---|---|
| What fixes an assessment? | Appropriate function and excellence; for Aquinas, due ultimate perfection and rationally ordered human goods. | Railton: objective interests and a distinct impartial rightness criterion. Boyd: human goods and sustaining homeostatic mechanisms. | Endorsement and reason-sensitive practical commitments may fix standards rather than detecting a mind-independent human end. This describes a rival option, not a new historical attribution. |
| Can present preferences be wrong? | Yes under the proposed appropriate standard; establishing that standard remains substantive. | Yes; existing cognitive-error models witness the formal compatibility, and the source theories propose fallible correction. | A sophisticated plan-based account can reject incoherent or ill-informed endorsements; it need not endorse every urge. Whether that earns robust stance-independent correctness remains disputed. |
| What remains to be defended? | Objective function assignment, why the human function has the proposed normative priority, warranted virtue/ordering and correct reason. | Adequacy of interests/cluster and causal access; the impartial criterion or normative role is not derived from biology alone. | Why these endorsements or constraints have authority and whether the earned semantic/normative resources suffice. |
| Does this supply categorical authority? | The first precept gives a sourced practical commitment, not a consequence proved from role-success or bare actuality here. | The recorded accounts give substantive reason proposals; neither their natural criteria nor the current finite models entail every agent has a universal instrumental reason. | Guidance follows under explicit normative commitments; deriving an ought from a purely descriptive factual constraint is not supplied. |

No column receives an aggregate score. A sourced answer is an answer even
when its defense remains open. A model of encoded behavior or error is not an
explanation proven adequate in reality. Conversely, independence from present
approval is not the same as independence from every fact about human psychology.

## Exact reuse and rejected duplicate proofs

- `TruthCore.Results.Aquinas.SummaTheologiae.GoodnessFromDesirability.goodnessIsActualityFromDesirability`
  already derives `GoodnessIsActualityReading` from the three recorded
  good/desirable, desirable/perfect and perfect/actuality biconditionals.
  `premisesNeeded` records their omission controls. Their fidelity and truth
  remain open; this source batch does not replace them with an analytic definition.
- `TruthCore.Results.Comparison.NaturalisticRealism.RailtonConsistent.railtonConsistent`
  and the corresponding `BoydConsistent.boydConsistent` already witness the
  recorded fragments with a right/good act lacking a universal instrumental
  reason link. Their strengthened ascription results require genuine ascription
  witnesses. Repeating a generic good-does-not-entail-reasons model would add no
  new constraint.
- `DESCRIPTIVE-PLAN-BOUNDARY` and the existing plan-state work already isolate
  descriptive support from normative guidance. No static supervenience or
  factorization theorem was manufactured for this slice.

The next decisive issue is the independent warrant for the human function and
its appropriate standard, followed by the practical-authority bridge. The
candidate `NATURAL-GOODNESS-HUMAN-FUNCTION-AUTHORITY` keeps that investigation
explicit. It does not assert that the bridge is false or that the opposing
view has already answered every question.

## Premise and verification boundary

Intended and actual root-premise change: **none**. All existing root-route
leaves remain open on the same routes. The four new readings are attributed
commitments, not established premises or argument results. There is no new
Challenge/Solution, inference edge, result or Comparator certificate because
no new argument is advertised.

The three new source-reading modules elaborated with no diagnostics through
the shared Lean service at preview `de591c1d405b7279d470d06d4ebb1160e61f78ad`;
combined exact-content SHA-256
`b30edcdda8303cdb09e8cb38ae5b6c7a822ff9e3ffc0c3ddf7527797525658c0`.
Final CI checks the delivered imports and corpus. Existing proof evidence is
reused rather than rerun for unchanged results.
