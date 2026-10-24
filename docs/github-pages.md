# GitHub Pages

`apps/corpus-explorer` is a static Next.js export and is deployed by `.github/workflows/pages.yml` on every push to `main`. The site shows the commit it was built from, the commit time and the build time, in the footer and on the state page.

## What the site shows

- `/` — the **state of the case** (#200): the root and the six stages with their status, the open premises that reach the root (bare first, then sourced), the closed statements on the root's paths, the verified derivations on those paths, and the recorded alternatives (refuted or not) and objections.
- `/statements/<ID>` — one statement: where it stands, what establishes it, its source witnesses (stating claims and `supports` relations), the arguments that use it, its relations, and its Lean declaration with a link to the source line.
- `/results/<ID>` — one result: verified derivation or transcription, conclusion and premises with their status, the advertised theorem as frozen in the Challenge module, the Comparator configuration (permitted axioms, NanoDa), and the proof projection.
- `/definitions` and `/definitions/<DEF-ID>` — the terms (#204): every disambiguation with its resolution, and each definition with its basis, source claims or stipulation note, Lean declaration and the records that use it. Statement, claim and result pages show the senses they depend on; a result page collects them from the argument, its conclusion and its premises.
- `/claims`, `/sources`, `/graph`, `/modal`, `/candidates` — the source readings, witnesses, proposition graph, modal-logic MVP and research queue.

The state, statement and result pages take every status from `python3 scripts/corpus.py frontier --json`, run once at build time (`src/lib/site-state.ts`), so the build needs `python3`. The explorer does not re-implement the closure rules for these pages. The report's `closed_statements` gives the rule that closes each statement (`proved`, `self_evident`, `alternatives_refuted`, `via_transcription`). Its `established_statements` lists the statements reached from self-evident or defended statements through verified results only. A statement can be closed (off the frontier) without being established: the skeleton proves the root from open premises. Lean declarations are located by a textual scan of `TruthCore/` (`src/lib/lean-source.ts`).

## Setup

The Pages build sets `GITHUB_PAGES=true`, which configures the app's `basePath` as `/truth-core` for the project-site URL. Local and ordinary CI builds keep the root base path.

GitHub requires the repository's Pages publishing source to be set to **GitHub Actions** once in **Settings → Pages**. The normal `GITHUB_TOKEN` cannot enable Pages for a repository that has never had Pages enabled.

The deployment workflow uploads `apps/corpus-explorer/out` with `actions/upload-pages-artifact` and deploys it with `actions/deploy-pages`. When GitHub Actions cannot start (for example because of an Actions budget), nothing deploys and the site stays at its last build; the commit shown on the site makes that visible.
