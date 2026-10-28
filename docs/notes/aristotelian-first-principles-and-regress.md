# Aristotle: first principles and the regress of demonstration

## Question and primary witness

Does stopping at an undemonstrated principle amount to arbitrary concession,
or can knowing have a non-demonstrative basis? This is a positive alternative
to the skeptical and infinitist positions examined in the current
Agrippa/Münchhausen investigation, not an inference from an epistemic regress
to the impossibility of an actual causal series.

The primary witness is the complete Greek *Posterior Analytics* I.2–3,
materialized as `ARIST-APOST-I-2` and `ARIST-APOST-I-3`. The First1KGreek
Bekker 1837 edition has an electronic title of *Analytica priora*, but its
actual `posteriora` division contains both books of the *Posterior Analytics*.
The manifest preserves that division, book and chapter rather than treating
Prior and Posterior Analytics locators as interchangeable. Consulted revision
`ed91552c52530c8f5a3ddf2dd767e899372a804c`, blob
`66f6b6a902e7e24bfbc70b91104f8ce509e2ce8d`, CC BY-SA 4.0. Both complete
chapters were read; no English translation is the witness for these claims.

Six independent prose readings are recorded, with no new Lean theorem:

| Claim | Locator | Scoped reading |
| --- | --- | --- |
| `ARIST-APOST-71B-DEMONSTRATIVE-PREMISES` | I.2, 71b17–72a8 | Scientific demonstration needs true, immediate, prior and better-known explanatory premises; formal syllogistic consequence alone is insufficient. |
| `ARIST-APOST-72B-SHARED-DEMONSTRATIVISM` | I.3, 72b5–18 | The two opposed positions share the restriction that knowing occurs only through demonstration. |
| `ARIST-APOST-72B-REGRESS-CONDITIONAL-KNOWLEDGE` | I.3, 72b7–15 | Under that restriction and the traversal/priority demand, endless ascent or unknown stopping points leaves conclusions only conditional on starting points. |
| `ARIST-APOST-72B-IMMEDIATE-KNOWLEDGE` | I.3, 72b18–25 | Aristotle's replacement affirms undemonstrated knowledge of immediates and a starting principle for knowing defining terms. |
| `ARIST-APOST-72B-SAME-RESPECT-PRIORITY` | I.3, 72b25–32 | Circular demonstration conflicts with same-respect priority; priority relative to us and priority without qualification are distinguished. |
| `ARIST-APOST-72B-CIRCULAR-SELF-RETURN` | I.3, 72b32–73a20 | Returning to the starting proposition supplies a conditional on that proposition; restricted reciprocal syllogisms do not make everything demonstrable. |

## The argument and what it still owes

I.2 requires more than a valid inference. Demonstrative *episteme* requires
appropriate explanatory starting points that are true and better known than
the conclusion. The requirement is a substantive epistemic norm, not a
corollary of logical entailment. Its distinction between what is prior by
nature and initially more familiar to us also blocks a silent translation
into temporal possession of reasons.

I.3 reconstructs two positions. The first demands knowledge of prior premises,
rejects traversal of an endless ascent and treats an undemonstrated stopping
point as unknown. The second retains the claim that all knowing is
through demonstration but permits reciprocal demonstrations. Aristotle rejects
both positions and their common restriction.

His positive response is that immediate principles can be known without
being demonstrated. The accompanying necessity argument retains two
commitments: prior premises must be known, and the sequence terminates at
immediates. The alleged necessity of that replacement does not establish every
chosen immediate proposition or independently settle the adequacy of its
acquisition. This batch neither marks a premise self-evident nor treats
calling a proposition immediate as sufficient to warrant it. II.19 is a
successor access/acquisition question; its account is not attributed from
memory or inferred from I.3.

The circularity argument likewise needs its epistemic order. A statement and
its alleged demonstrative basis cannot each be prior to the other in the same
respect. Reciprocal logical consequence is possible in the specified cases;
it does not thereby provide unconditional demonstrative knowledge. A
coherentist's global support relation is not refuted merely by renaming it
Aristotelian demonstration. The argument must first establish that this
same-respect priority norm governs the rival's proposed warrant.

## Strongest rival replies and common burdens

| Account | Positive replacement | Commitment still needing defense |
| --- | --- | --- |
| Aristotle's non-demonstrative reply | Appropriate immediate principles can be known, allowing demonstration to begin without pretending the principles are themselves demonstrated. | Why actual principles are independently knowable and true; why the source's prior-premise and terminating-immediates requirements govern the case. |
| Skeptical renewed demand | Withhold unconditional acceptance when purported prior entitlement has not been supplied. | Scope of the demand: undemonstrated knowledge must not be ruled out merely because demonstration is the only permitted entitlement. Suspension is not a proof that nothing can be known. |
| Infinitist reply | A reason sequence may be available/dispositional without actual psychological traversal; the positive account owes conditions beyond endless noncircular graph shape. | Why those availability and reason-status conditions yield the relevant justification, and why strict prior reason-enhancement is not required. |
| Holistic/coherentist reply | Mutual support can be assessed as a whole rather than as a cycle of strictly prior Aristotelian demonstrations. | Why the whole is epistemically adequate, rather than merely consistent or mutually entailing. |

The infinitist comparison uses the scoped distinctions preserved in
[PR #669](https://github.com/moritzbrantner/truth-core/pull/669), not a new
historical claim about the 1999 Klein paper. A supporting reason that is not
*yet reason-enhanced* is not thereby wholly unjustified. That matters here:
Aristotle's immediate knowledge and the infinitist's reason-status account
cannot simply be identified, and the latter cannot be treated as an
all-borrowed causal-power interpretation. Each position owes an account of
entitlement, with different commitments about which status must be prior.

## Exact reuse and proof boundaries

- `STMT-SCIENTIFIC-KNOWLEDGE-THROUGH-FIRST-PRINCIPLES` binds
  `TruthCore.Greek.Aristotle.Physics.ScientificKnowledgeThroughFirstPrinciplesReading`.
  Physics I.1 supplies a methodological requirement for inquiry into
  structured subjects. It does not already express the An.Post. I.3
  non-demonstrative-entitlement thesis, so no statement identity was merged.
- `STMT-REGRESS-JUSTIFICATION-TRANSFER` binds
  `TruthCore.Logic.RegressDomains.JustificationTransfer`; its certificate is
  `TruthCore.Results.Logic.RegressSchema.justificationTransfer`. Under the
  stipulated all-premise `GeneratedWarrant` and nonempty rule premises, it
  extracts one finite projected path to a foundation. This is necessary only,
  not independent epistemic justification, global graph well-foundedness or
  a uniformly finite/finitely branching total proof tree.
- `TruthCore.Logic.RegressDomains.CrossDomainBoundary`, included in
  `TruthCore.Results.Logic.RegressSchema.regressSchemaPackage`, keeps absent
  foundationalist warrant compatible with separately stipulated local causal
  activity. It neither defends all actual causal activity without a source
  nor shows that Aristotle's norm transfers to a causal relation.
- `TruthCore.Logic.Regress.Graph.grounded_eq_lfp` concerns the explicitly
  supplied intrinsic predicate and existential predecessor-transmission
  operator. Its mathematical least-fixed-point identification does not
  establish which norm all epistemic knowledge must satisfy. It is not
  substituted for the different all-premise warrant construction.

Those results already supply the structural controls needed here. Repeating
one as a new source-labeled regress theorem would not defend the missing norm.
No Challenge, Solution, result or claim of new mechanical verification is
introduced.

## Rejected shortcuts and premise comparison

Rejected: all knowledge is demonstrative by definition; immediate means
arbitrary dogma; an endless available sequence must have been psychologically
traversed; non-prior reason-enhancement means no justification of any kind;
reciprocity is always logical contradiction; a finite necessary branch gives
a globally finite proof; and an epistemic no-regress argument establishes
causal finitism or a bounded temporal past.

Intended and actual root-route open-premise change: none. All 63 current
root-reaching leaves and all eight route costs are retained. The six source
readings remain open propositions, and no new root edge is added. The concrete
advance is an explicit positive alternative to bare stopping and an isolated
entitlement/priority dispute. `ARISTOTELIAN-IMMEDIATE-ENTITLEMENT` records the
next access question; `ATTEMPT-ARISTOTELIAN-FIRST-PRINCIPLES-REGRESS` preserves
source reading, rejected identifications and exact proof boundaries.
