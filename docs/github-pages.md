# GitHub Pages

`apps/corpus-explorer` is a static Next.js export and is deployed by `.github/workflows/pages.yml` after pushes to `main`.

The Pages build sets `GITHUB_PAGES=true`, which configures the app's `basePath` as `/truth-core` for the project-site URL. Local and ordinary CI builds keep the root base path.

GitHub requires the repository's Pages publishing source to be set to **GitHub Actions** once in **Settings → Pages**. The normal `GITHUB_TOKEN` cannot enable Pages for a repository that has never had Pages enabled.

The deployment workflow uploads `apps/corpus-explorer/out` with `actions/upload-pages-artifact` and deploys it with `actions/deploy-pages`.
