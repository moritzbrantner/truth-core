# Choosing the next research step

This note describes the existing UI and runtime. Its owner-decision labels and
floor workflow are legacy behavior, not current directions to choose philosophical
premises. Follow the [systematic research loop](../systematic-corpus-loop.md):
reasoned provisional judgments can guide priorities and qualified assessments;
personal approval is not philosophical warrant. This qualification changes no
runtime schema, approval metadata or computed status.

The [next-work view](https://moritzbrantner.github.io/truth-core/next/) starts at
`STMT-CATHOLICISM-TRUE`, highlights established statements and additional
verified conditional support bundles, and lets the reader follow each argument
to its premises. Expanded open-premise cost is retained as a **diagnostic**, not
the progress KPI. The CLI returns
exactly the same presentation:

```sh
python3 scripts/corpus.py next-steps --json
python3 scripts/corpus.py next-steps --root STMT-CATHOLICISM-TRUE
```

Both consumers read the `next_steps` projection of `corpus.py frontier --json`.
Closure, established status, source depth, counted refutations and route cost
continue to have one authority. A theorem can be verified and still depend on
open premises. In particular, a `proved_unestablished` route leaf also retains
its source depth (bare, supported or stated); the proof status does not erase
that distinction.

The `support_options` field in the authoritative `frontier --json` report
includes each root-reaching premise, with a direct-assumption choice when
unestablished, and groups its verified non-transcription arguments by distinct
premise bundles. Established premises keep their support bundles in the count,
so settlement does not look like lost argument progress. For example `A ∧ B → P1` adds an option under `P1` even if
the expanded-route cost rises from one open leaf to two. The number of
alternatives is neither an established-premise count nor proof of genuine
philosophical independence. The Explorer renders these options before the
cost-based route and leaf diagnostics.

## Settlement and impact

In the existing runtime, a floor item needs its recorded basis and any required
owner approval. A derivation needs a verified argument whose premises are all
established. A defense needs counted refutations of every recorded rival,
resting only on established premises. No rival list is presumed to exhaust every
possible rival. An empty list does not defend a premise.

For each route leaf, the frontier temporarily **assumes it established**,
runs its own least fixpoint (including newly counted refutations and their
consequences), and runs its own route-cost algorithm. The view reports the
before/after costs of every affected verified route. This is a counterfactual,
not a proof, a floor approval, or a witness that the enlarged background is
consistent. It can differ from merely counting how many routes mention a leaf:
settling one leaf can enable a refutation that settles another. The actual
frontier and corpus remain unchanged. The cost algorithm retains its existing
deterministic greedy proof selection; this view does not claim a new global
minimum-set-cover metric.

The legacy UI marks the proposed floor path as an owner decision for every open
leaf. This is a recorded navigation action; it does not require the owner to
accept a premise before research continues. Linked definitions identify where a
definition decision would require a check of all uses. Optional
`settlement_actions` on an existing statement record can link an approved or
pending floor/definition decision. These are navigation hints: they never
establish the statement or alter `self_evident`.

## Case splits and joint settlement

An optional `case_split` annotation on an existing result names its target,
exact Lean case declarations, any independently identified case statements, and
a surviving-case result. The existing frozen coverage theorem, its bound
premises and the result's verification remain the evidence. An annotation is
not a second proof-status registry and cannot certify that arbitrary cases
cover a target. Claim/type review must check that the bound theorem actually
has the advertised disjunction. Without a separately identified case statement,
the view cannot count a case refutation; it shows that gap explicitly.

The initial annotation exposes the existing potency-analysis partition and its
three rival cells. The coverage theorem uses excluded middle; each cell has the
existing joint floor-survival witness, within that witness's stated scope. A
future adopted potency definition may settle an adopted-sense sibling without
refuting these cells in the original independent-predicate interpretation.
The view reads current route and statement IDs and does not assume a fixed
number of routes or silently merge those interpretations.

For each route pair the view lists the shared open leaves and **all** leaf
failure modes. A route's failure is a disjunction: covering just one missing
premise is insufficient. Recorded rival consequences retain their complete
argument premises; a rival is not automatically the logical negation of the
leaf. Pairwise overlap is a search aid, not an incompatibility certificate.
The view also computes the intersection of open premises across every *reported
verified* route, when at least two exist. A disjunction of those fixed
conjunctive bundles still entails each common premise. This identifies shared
obligations which cannot be bypassed by combining the displayed routes. It is
not an exhaustive enumeration of every possible proof route, a claim that a
premise is philosophically necessary, or a closure certificate. The CLI and UI
use the same `joint_settlement_summary` projection; no new proof-status field
or independent computation is introduced.
Until exact failure-coverage, consequence, incompatibility and composition
certificates exist, the pair remains unresolved. A result marked
`joint_settlement_schema: true` is linked as a reusable logical schema, not a
certificate for a concrete pair or a reason to close the root.

## One explicit floor register

The corpus's existing `self_evident` markings are the one floor register. The
same next-work page renders every marking with its basis, owner-approval link,
recorded rivals and dependent arguments/statements. Reproduce that register
without maintaining a second table:

```sh
python3 scripts/corpus.py next-steps --json | python3 -c \
  'import json,sys; print(json.dumps(json.load(sys.stdin)["floor_register"], indent=2))'
```

Under that legacy workflow, candidate suggestions and navigation hints do not
enter this register until the owner's decision is recorded through the existing
floor workflow. This describes record handling, not independent warrant.
