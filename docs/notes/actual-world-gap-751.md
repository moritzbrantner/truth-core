# Actual-world gap: local causal records and the total history (#751)

Question: if each member of a complete history has a local causal record, does
anything remain to explain about why this history obtains rather than a rival?
Lean: `TruthCore/Explanation/ActualWorldGap.lean`, results
`ACTUAL-WORLD-GAP-SCHEMA` and `ACTUAL-WORLD-GAP-CONTROLS`. This is a connection,
not a discharge, and not a refutation of physicalism.

## Finding

"Local completeness leaves the history unselected" is ambiguous, and the formal
results split it.

1. **Named records select.** Given `LocalRecord` at both worlds, same edge table
   iff same presence and edge table. If it holds at `a` and at each accessible
   world, the table is a #736 reason-vector with an evidence-only selector at `a`. The strongest physicalist case is therefore right
   about information: nothing is unselected by the entire named record.
2. **But that selector tracks the total.** A fact coextensive with same-table on
   accessible worlds is coextensive with the total fact there. Three controls
   violate one `LocalRecord` clause each and break the agreement.
3. **Names erased, nothing selects.** The same table without names has the same
   truth at actual and rival, so #736's `no_selection` applies at every world.
4. **The fork.** With a rival and true reasons: no reason; or a reason true at the
   rival; or a reason false there, and then contingent. This is coverage, not
   exclusivity. Each disjunct is witnessed.
5. **Two inconsistent bundles.** {rival, reason true on all accessible worlds and
   at `a`, entailment on accessible worlds}. {rival, `ContrastiveClosure`, well-
   founded reasons at `a`}. Each forces rejecting some member, not a chosen one.

## Survivors under the one question

All on the same tagged forms, with universal accessibility unless noted.

| Answer | Reason for total at `actual` | Contingent PSR | Independent of total | Closure | Note |
| --- | --- | --- | --- | --- | --- |
| `brute` | none | fails | n/a | fails | on the chain every existent has a reason; `MemberLift` fails |
| `internal` | member 0 | holds on chain | no, in this fixture | iff chain | chain not well-founded; single and plural well-founded |
| `copy` | record | holds on chain | no | holds on chain | member lift holds on chain |
| `ground` | ground, true at rival | holds on every form | yes | fails | not necessitating |
| `law` | contingent marker, entails | fails | yes | fails | marker has no reason at `actual` |
| isolation | n/a, no rival | n/a | n/a | vacuous | total not contingent |

Failed discriminator: rejecting closure is common to `brute`, `ground` and `law`.
The contingent PSR is shared by `internal` and `copy` on the chain and `ground` on every form. In this
fixture, only `ground` is shown to have both the contingent PSR and a reason
independent of the total. That does not favour theism by itself: the model has no
predicate separating a personal ground from an impersonal one, or a natural
necessity from a supernatural one. The internal and copy models are fixture-bound:
a domain with partial-history worlds, as in #755's `history`, gives members that
are not coextensive with the whole.

## Decisive experiments in the issue

1. **Populated histories, same local evidence.** `tagged` and `taggedExercise`
   copy #735 records. Erased evidence fails to select, consuming #736.
2. **Changed index, same unpointed structure.** Each world's own total holds at it,
   while the rigid total of `a` is contingent. The indexical reply is right about
   the diagonal and does not touch the rigid reading. It remains open which one a
   real why-question asks; `Case` has no designated-index field.
3. **Positive controls.** Independent differentiator: `law`. Structure with no
   accessible rival: isolation. Formal uniqueness and actual instantiation stay separate
   per #743; an internal actuality marker stays separate per #736's omissions.
4. **Same question for rivals.** Source and regress forms are `Kind`. Nonnecessitating
   contingent explanation, including free choice, has the `ground` structure and
   survives; this model does not represent choice as such.

## Semantic grounding

- *Reason* is #755's uninterpreted relation. Fire has the spark and fuel among its
  reasons; a coincidence of two events need not be a reason for either. It is not
  causation: `ground` has edges, `copy` has a record reason with no edge.
- *Rigid total* is true at the worlds agreeing with `a`, and is not "the world I am
  at". Example: this game was played; near miss: the game described is the one
  described.
- *Contrastive closure*: separating facts have separating reasons. Spark rather
  than no spark illustrates it; indeterministic decay is a standing
  counterexample if there is no separating feature. Transitivity, asymmetry and
  well-foundedness are not assumed. Well-foundedness enters only as a named member
  of a bundle, and the chain shows an infinite regress can meet closure.
- Generalization from ordinary to total explananda is exactly what is not assumed:
  `MemberLift` fails in `brute` on the chain and holds in `copy` on the chain.
- Rivals: Hume-Edwards (no remainder; `MemberLift`, `copy`), brute (`brute`),
  necessitarian (isolation), indexical (diagonal), and contingent-reason accounts
  (`ground`, `law`). A probabilistic account is not modelled.

## Rejected readings

- Local coverage entails no selection: false for the named table.
- Selection answers the question: entailment is one of several conditions, and
  `law` passes it while its marker has no reason at `actual`.
- A necessary reason cannot explain the total: only entailing plus rival is
  excluded; `ground` is a true nonentailing reason in the model.
- Accessibility as real possibility: modelled worlds show satisfiable bundles only.

## Sources

Reread `OPPY-UNIVERSE-NO-CAUSE-13-22` (pinned 2020 witness). §I, p.14 proposes that
every possible world shares laws and initial history with the actual world,
differing through objective chance; §VI, pp.19-21 compares restricted answers to
"Why is there something rather than nothing?". The existing claims
`OPPY-2020-SHARED-LAWS-INITIAL-HISTORY` and `OPPY-2020-NECESSITY-COMPARATIVE-COST`
are reused and no new claim is added. Analyst analogy, not attribution: a fact true
at all worlds on that restricted modality that does not entail the history has the
fork position of `ground`. Oppy is not attributed `Reason`, closure or the fork.
`MemberLift` is named after the Hume-Edwards reply but has no pinned witness; it
needs a passage before any claim, so none is made.

## Premises and gaps

No premise of a root route is added, changed or removed; both arguments have empty
premise lists. Not a transcription: conclusions are derived from typed structure,
and controls show that the conditions can fail.

Open: an independent defence of a relevance or adequacy bridge (#750). Why must a
reason be independent of, entail or separate the total? How far does closure reach?
Not modelled: rivals sharing an initial segment, as Oppy's proposal has;
probabilistic explanation; presence varying under a fixed table; personal agency.
Fixture features such as disjoint rivals and coextensive member reasons are not
general results.
