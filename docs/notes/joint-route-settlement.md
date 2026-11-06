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

At main `0367eebc5b98263ba16d87a2ddd0e9388d10056e`, the authoritative frontier
reports 12 verified root-route bundles. Their pairwise intersections contain
18–39 open leaves, and 16 leaves appear in every reported bundle. In particular,
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
