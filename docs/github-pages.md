# GitHub Pages

`apps/corpus-explorer` is a static Next.js export and is deployed by `.github/workflows/pages.yml` on every push to `main`. The site shows the commit it was built from, the commit time and the build time, in the footer and on the state page.

## What the site shows

- `/` and `/graph` — the **epistemic frontier**: a full-width network of proposition dots and explicit inference junctions, with the open premises highlighted and a synchronized research queue. `/graph` retains saved deep links and proof-exploration state.
- `/state` — the **state of the case** (#200): the root and the six stages with their status, the open premises that reach the root (bare first, then sourced), the closed statements on the root's paths, the verified derivations on those paths, and the recorded alternatives (refuted or not) and objections.
- `/statements/<ID>` — one statement: where it stands, what establishes it, its source witnesses (stating claims and `supports` relations), the arguments that use it, its relations, and its Lean declaration with a link to the source line.
- `/dossiers/<ID>` — one premise dossier: source readings, definitions, competing interpretations, attempts and blockers, and root-route contribution, all derived from the canonical records.
- `/results/<ID>` — one result: verified derivation or transcription, conclusion and premises with their status, the advertised theorem as frozen in the Challenge module, the Comparator configuration (permitted axioms, NanoDa), and the proof projection.
- `/definitions` and `/definitions/<DEF-ID>` — the terms (#204): every disambiguation with its resolution, and each definition with its basis, source claims or stipulation note, Lean declaration and the records that use it. Statement, claim and result pages show the senses they depend on; a result page collects them from the argument, its conclusion and its premises.
- `/claims`, `/sources`, `/candidates` — the source readings, witnesses, and source-range research candidates. Earlier specialist pilots (`/modal`, `/objective-truth`, `/skeleton`) remain reachable under **Reference** rather than primary navigation.

The state, statement and result pages take every status from `python3 scripts/corpus.py frontier --json`, run once at build time (`src/lib/site-state.ts`), so the build needs `python3`. The explorer does not re-implement the closure rules, statuses, floor criteria, stages or dependent walks on any page (#507); it reads them from the report (`docs/corpus-model.md`). A self_evident marking shows its basis, whether the criterion holds and its recorded disagreement on the statement page, the state page's floor section and the graph details. The report's `closed_statements` gives the rule that closes each statement (`proved`, `self_evident`, `alternatives_refuted`, `via_transcription`). Its `established_statements` lists the statements reached from self-evident or defended statements through verified results only. A statement can be closed (off the frontier) without being established: the skeleton proves the root from open premises. Lean declarations are located by a textual scan of `TruthCore/` (`src/lib/lean-source.ts`), including indented declarations and namespace boundaries; snippets retain source indentation and line numbers. This index locates text and does not verify Lean syntax or proof meaning.

## Setup

The Pages build sets `GITHUB_PAGES=true`, which configures the app's `basePath` as `/truth-core` for the project-site URL. The root Turborepo build declares this variable as a hashed task input, so normal and Pages builds cannot restore each other's output. Local and ordinary CI builds keep the root base path.

GitHub requires the repository's Pages publishing source to be set to **GitHub Actions** once in **Settings → Pages**. The normal `GITHUB_TOKEN` cannot enable Pages for a repository that has never had Pages enabled.

The deployment workflow uploads `apps/corpus-explorer/out` with `actions/upload-pages-artifact` and deploys it with `actions/deploy-pages`. When GitHub Actions cannot start (for example because of an Actions budget), nothing deploys and the site stays at its last build; the commit shown on the site makes that visible.

## Epistemic Frontier graph

The homepage and `/graph` default to a compact force-connected global network with a synchronized
research frontier. The graph dominates the workspace, while secondary controls live
under **More views and filters** and the research queue occupies a narrow inspector.
Community colors and structural leaves describe inference connectivity, not confidence.
Round proposition dots and small square inference junctions preserve the AND-premise
structure of arguments. Rings distinguish establishment, conditional closure and
bare or sourced frontier; the visible legend and optional **Frontier highlighted**
emphasis reveal the frontier dots without inventing a geometric boundary. The
default dashed research-link layer adds the corpus's recorded alternatives,
attacks, refutations and claim/argument evidence. For claim and argument relations,
the map projects the original record through its statement or conclusion; selecting
a belief exposes the original record and any research note. Those links affect
visual proximity, not proof, closure or inference-component counts. The overlay can
be hidden with **Recorded research links**, and `relations=0` preserves that choice
in the URL. Hiding the overlay does not move the stable map positions. Readings
with neither an inference nor a recorded research link (singletons) are
omitted from the initial canvas, but stay searchable and can be shown by clearing
**Hide singletons** under the advanced controls. Structural
leaf filters (no supporting inference / no consumer inference) are independent of
frontier obligations. Edges end at the centre of each dot: the network markers
place both React Flow handles on the visible symbol, not on the larger hit box.

The graph data is not embedded in the page. The build writes static JSON buckets
under `/graph-data/` (`src/lib/graph-buckets.ts`, emitted by the route handler
`src/app/graph-data/[file]/route.ts`); the page ships only their manifest. A
bucket is a union of whole layout components (inference steps plus recorded
research links), so no step or link is cut and a root-path, focus or local view
is complete once its node's bucket is loaded. The `root` bucket holds every
component with a statement in `reaching_root_statements` of
`corpus.py frontier --json` (the statements whose upward argument walk reaches
the root, `root_route` aware) and is the default overview. Other linked
components are grouped by their most frequent import area
(`scripts/root_imports.py`), singletons separately, each with its own layout
computed at build time. **Graph data** lists the buckets; any can be loaded, or
every one (`b=all`). `lookup.json` (ID → bucket) loads when the URL addresses a
node, and `search.json` when a text query is typed. Facet filters for lane, area
(the import area of the Lean namespace), closure (established, conditional,
bare or sourced frontier, neither), linked record kind (claim, argument, result,
inference, research link) and root reachability live in the URL (`lane`,
`area`, `closure`, `rec`, `reach`). Each bucket's manifest entry counts these
facets, so with a filter active only the default buckets (kept as dimmed
context) and the buckets with a possible match are fetched.
The **Layered** option retains source clustering and expanded proof cards; selecting
**Focus here** expands complete AND-premises and alternative (OR) applications.
Network positions are deterministic and computed at static-build time, with no
browser force animation.
Select a statement to bring its obligations to the top, or select an obligation to
locate its statement and inspect the exact blocker. From a dot or queue item,
the linked premise dossier exposes previous attempts, missing bridges, source
interpretations and route contribution without changing closure status. Switch to **Selected goal
frontier** to restrict obligations to route-aware dependencies of that proposition;
**Global frontier** restores the full queue. Focus views retain a return link with
the previous viewport, filters, expansions and selection in the URL.

The graph uses the same Python report as the state pages, including the distinction
between closed conditional consequences and established statements. Its research
obligations are a derived projection, keyed by kind and existing corpus IDs. They
are not a new canonical queue: `/candidates` remains the source-range workflow.
Knowledge obligations cover open derivations, bare evidence, alternatives and
objections. Exploration obligations come from recorded competing readings and
source-range candidates; absence of such records never means an area is complete.
Ranking uses manual URL pins, root reachability and argument counts, with selected-node
relevance breaking ties. No expected effort, research value or certainty is invented.

Run `bun run --cwd apps/corpus-explorer test:browser` after a normal explorer build
for the deterministic Chromium journey over the real static export. CI installs
the browser and runs this path before the Pages build. The browser test allocates
its own local port and checks desktop keyboard and mobile touch selection, settled
positions, network/layered comparisons, graph/queue synchronization, goal/global switching,
URL reload, expansion, viewport restoration and mobile overflow. The unit fixtures
call Python's actual frontier computation for grounded and ungrounded reciprocal
cycles, shared dependencies and transcription closure.
