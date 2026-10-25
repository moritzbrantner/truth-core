# T: possible collapse can leave the root contingent

Issue #264 uses the existing modal fixture and the merged K results. Every model
and atomic valuation here is stipulated mathematics. There is no source claim
about Hume, no conceivability premise, and no claim that one of these models is
metaphysically possible. These results close no Catholic-case frontier node.

`MC F D w` says that each admissible predicate true at `w` persists along every
edge from `w`. Actual, possible and necessary collapse mean respectively
`MC F D w`, `Dia F (MC F D) w` and `Box F (MC F D) w`, with the same domain and
root. T assumes only `Reflexive F`: every world accesses itself. In particular,
T does not make accessibility symmetric or transitive.

## Valid T consequences

`TruthCore.Results.Modal.T.Laws.checks` proves:

- Over all world predicates, MC at a T world holds exactly when its accessible
  successors are precisely itself. The proof composes the K successor-identity
  theorem with reflexivity; it does not assume a separate world-extensionality
  principle.
- Full MC is equivalent to necessary full MC on a T frame, and implies possible
  full MC. The forward direction transports MC along successor identity. The
  backward direction uses the root's self-edge.
- In every explicitly supplied proposition domain, necessary MC implies actual
  MC, and actual MC implies possible MC. These implications use the self-edge;
  they do not establish the converse from possible to actual MC.

The K dead-end/fork results already delimit the reflexivity assumption: K can
have necessary MC without actual MC and actual MC without possible MC. Those
proved conclusions are reused, not restated as new premises. No excluded middle
or classical host axiom is used in the new T proofs.

## Smallest branching witness

`TruthCore.Results.Modal.T.Branching.checks` reuses
`ResearchFinite.branching` without changing it. There are two labels, `false`
(the root) and `true` (the endpoint):

| world | successors | independent atom P | full MC | fixed-language MC |
| --- | --- | --- | --- | --- |
| root | root, endpoint | true | false | false |
| endpoint | endpoint | false | true | true |

Both rows have self-edges. At the root, possible MC holds and actual MC fails in
both domains. Necessary MC fails because the root accesses itself. Independently
of any collapse definition, the atom has a positive witness at the root and a
negative witness at the endpoint: `◇P ∧ ◇¬P`. Thus the collapsed accessible world
coexists with a distinct contingent alternative at the same root.

Possibility entails actuality also fails: `◇¬P` is true at the root but `¬P` is
false there. The deterministic evaluator reproduces both witness lists:
`witnesses ... P = [false]` and `witnesses ... ¬P = [true]`.

The atom distinguishes the two labels, so the entire fixed formula language is
world-extensional in this model. Consequently the failed implication
`◇MC → MC` survives adding the optional world-extensionality condition. It also
fails when that condition is simply not imposed. This frame happens to be
transitive as well, but the valid T theorem does not use that extra property.

## A T frame that is not S4 or B

`TruthCore.Results.Modal.T.FrameBoundary.checks` supplies a separate three-world
model, so transitivity is not silently assumed:

| world | successors | independent atom P | full MC | fixed-language MC |
| --- | --- | --- | --- | --- |
| root | root, middle | false | false | false |
| middle | middle, endpoint | false | false | false |
| endpoint | endpoint | true | true | true |

The missing root-to-endpoint edge refutes transitivity. The missing
middle-to-root edge refutes symmetry. Root and middle are separated in the fixed
language by `¬◇P`; middle and endpoint by `¬P`.

At the root, one-step possible MC fails in both domains, while possible possible
full MC holds via middle and endpoint. Likewise `◇P` is false and `◇◇P` is true.
Necessary MC fails in both domains. A diamond quantifies over a single edge, not
an implicit transitive closure or all mathematical worlds.

## Proposition scope and identity

`TruthCore.Results.Modal.T.ScopeBoundary.checks` composes the existing K proofs
for `ResearchFinite.duplicates`: two distinct labels with universal reflexive
access and the same constant atomic valuation. Formula induction establishes
agreement on **every formula in the specified language**, not merely the current
corpus's finite inventory. The configuration is:

| proposition domain at root | MC | possible MC | necessary MC | possibility implies actuality |
| --- | --- | --- | --- | --- |
| all world predicates | false | false | false | false |
| fixed formula language | true | true | true | true |

Language world extensionality fails in this duplicate model. Equality predicates
in the full domain distinguish the labels. With the optional extensionality
condition imposed, this model is excluded; it is not a model of that condition
and its negation. The branching witness above remains available with that
condition imposed. The existing K scope theorem states the separate assumptions
(excluded middle, negation closure and world extensionality) that suffice to
upgrade domain-relative MC to full MC; none is silently introduced here.

## Verification and self-sweep

Four frozen Challenges bind the four advertised bundle types in `TResearch`;
Solutions derive them by self-access, equality transport, formula semantics and
explicit finite cases. Their corpus argument records have no external premise
statements. The bundled mathematical assumptions are universally quantified
inside the conclusions, not theological facts or hidden source commitments.

Definitions cover frame/domain/MC/identity/agreement/extensionality, independent
contingency, possibility entails actuality and the three exact T configurations.
The linked disambiguations keep proposition scope, collapse modes, root-relative
reachability and world identity distinct. No historical attribution or stronger
metaphysical reading needs a new source claim. The shared fixture and K results
remain unchanged; every reused result is imported as a theorem.

The finite tables are proved in Lean and reproduced with the shared evaluator.
To inspect the ordered edge, truth and witness report, evaluate
`TruthCore.Modal.TResearch.report` after importing `TruthCore.Modal.TResearch`.
The report computes over the explicit world lists; it does not enumerate every
Prop-valued predicate. Full-predicate statements are proved by equality and
quantified reasoning, separately from finite evaluation.
