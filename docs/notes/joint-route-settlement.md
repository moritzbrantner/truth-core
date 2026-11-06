# Joint route settlement

Owner design: [#1119](https://github.com/moritzbrantner/truth-core/issues/1119).
The reusable pattern is `ROOT-FROM-JOINT-FAILURE-INCOMPATIBILITY`, in
`TruthCore/Logic/JointRouteFailure.lean`. It is a logical template over opaque
proposition families, not a philosophical derivation or a settlement of the
Catholicism root.

For fixed premise families `left : I → Prop` and `right : J → Prop`,
`Complete left` means every left premise holds. `Failure left` means at least
one indexed premise fails. Empty routes are complete. Failure implies
incompleteness constructively; the converse uses the explicit shared
`ExcludedMiddle` premise. There is no classical axiom in the proof.

`EveryFailureEntails left X` requires **each** failed premise to entail X.
Together with `EveryFailureEntails right Y` and `¬(X ∧ Y)`, it gives
`Complete left ∨ Complete right`. Two checked implications from those complete
routes to the same conclusion then give that conclusion. Route derivations,
failure consequences, incompatibility and any background assumptions must all
be instantiated under one semantic profile. The general template supplies none
of their philosophical content or independent warrant.

Two boundaries are checked alongside the pattern:

- `sampledFailureControl`: the Boolean-indexed family `fun b => b = true` has
  one true and one false premise. The true premise's failure implies False
  vacuously, so **some** failure-mode implication to False holds even though
  the route really fails. Universal failure coverage to False fails. A chosen
  sample therefore cannot certify an exhaustive failure consequence.
- `shared_obligation`: if a proposition is required by each of the two
  complete routes, their disjunction still requires it. Joint settlement of
  these fixed bundles cannot evade a common obligation.

## Current root roster

At main `fb573ed19bebc950d61b6ff35cbe41ab5430e2e5`, the authoritative frontier
reports 23 verified root-route bundles. Their pairwise intersections contain
17–39 open leaves, and 15 leaves appear in every reported bundle. In particular,
`STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE` is shared. There are no disjoint
pairs in this roster. These are facts about the **currently reported sufficient
bundles**, not a proof that every possible route to the root must use these
premises. The frontier selects one deterministic, greedy set of open leaves
per derived statement; it does not enumerate all sufficient premise sets.

Reproduce against any later revision, retaining its exact HEAD with the report:

```bash
python3 scripts/corpus.py frontier --json > /tmp/frontier.json
python3 - <<'PY'
import itertools, json
r = json.load(open('/tmp/frontier.json'))
bundles = [set(x['open_premise_statement_ids'])
           for x in r['routes']['routes'] if x['verified']]
pairs = [len(a & b) for a, b in itertools.combinations(bundles, 2)]
print('verified routes:', len(bundles))
print('shared by all:', sorted(set.intersection(*bundles)) if bundles else [])
print('pair overlap range:', (min(pairs), max(pairs)) if pairs else None)
PY
```

A concrete cross-route result remains open. It needs complete failure-mode
consequences and an incompatibility resting on established premises, rather
than unrelated model witnesses or an informal list of rival worldviews. No
floor item is proposed or approved by this rule template. The owner-facing
floor register and next-work view are separate projections of frontier evidence;
neither is a new closure authority.


## Concrete shared-failure control

`CLASSICAL-GOD-REVELATION-BOUNDARY` is a populated boundary, not another
joint-settlement schema. Its `Control` retains the **entire** existing
`NecessaryClassicalGodRootControl.Control`, whose `checks` proof is imported
unchanged. The supplied excluded middle and the old24 nonlogical interfaces
make the original full25 input configuration. The exact same model, source,
`RetainedInputs`, `SourceWitness`, old18 concurrent positive control, necessary
root endpoint, unique classical God, and necessary non-God effect survive.
Nothing is reinterpreted to align unrelated models.

On that SAME existing `signature` the new checked export additionally states:

| Component | Exact scope |
| --- | --- |
| `GodExists signature.IsGod` | The assigned `.source` is God. |
| `GodHasClassicalAttributes signature` | Every assigned God is that same source; its existing exact nine-predicate/primitive-field witness is retained. |
| `¬ RevelationPossibleAndRecognizable signature` | Evaluating capability at the God source gives False. |
| `¬ CatholicismTrue signature` | The root's God-founded-teaching-authority conjunct fails because `FoundedAsTeachingAuthority` is False everywhere. |

The last two negatives have **different** proofs. Revelation is not a conjunct
of the phase1 root definition, and its failure alone is not used to infer root
failure. The historical and Creed fields were already false placeholders in
the old fixture; they are evaluated here, not newly assigned. These checks add
a useful explicit boundary to the existing positive interface; they do not
explain a real failure of divine capability or establish a possible theology.
No source attribution is added.

For a concrete pair in the reported roster, inspect the unchanged Challenges:

- `TruthCore/Results/Causality/NecessaryClassicalGodCase/Challenge.lean`,
  theorem `derive`: its full25 configuration is followed by exactly seven
  revelation/historical/teaching inputs, including
  `hRevelation : RevelationPossibleAndRecognizable σ`.
- `TruthCore/Results/Case/Catholicism/FromQuartaViaWithoutTruthBridge/Challenge.lean`,
  theorem `catholicismFromQuartaViaWithoutTruthBridge`: a different natural-
  theology route also takes that exact `hRevelation` on its SAME `σ`.

Both bind the existing statement
`STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE`. Instantiating this common obligation
at the fixture signature makes each of these fixed bundles incomplete,
regardless of how its other premises are valued. Their disjunction cannot
remove that obligation: this is exactly the existing `shared_obligation`
constraint. The current greedy roster confirms the same shared leaf in every
reported pair; it is not coverage of every possible proof of Catholicism.
There is no profile equivalence assumption here: the shared stage3 predicate
is literally the same function of the same signature.

The positive fixture does **not** satisfy all other leaves of both bundles or
every floor. Its act dictionary is universally true and potency empty on two
supplied respects; the Quarta Via grade/maximum interfaces and other route
conditions are not all certified by its full25 inputs. No complete-respects,
composition-to-potency, cognitive, historical, or real-world applicability
bridge is supplied. Thus this is a strong explicit positive God/attributes
configuration with a common failure, not a model isolating revelation as the
only missing premise of every route.

In particular, failure of a full Catholicism bundle cannot simply be labeled
“no God”: a bundle can fail its revelation input while this fixture retains
God and all its certified attributes. The proposed joint-failure method still
needs consequences covering **every** failed input and a genuinely checked
incompatibility under one dictionary. Those are not supplied by these two
route derivations or by the shared-failure witness. The decisive remaining
work lies in the stage3 recognizability interface (and the explicitly retained
historical/teaching interfaces), rather than counting alternative stage1
proofs as a joint settlement. No root premise, floor, or old Challenge changes.
