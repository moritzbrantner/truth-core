This Linux-only CI adapter replaces anonymous Elan installer, Lean distribution,
and Bun release downloads with authenticated GitHub REST asset requests. The
2026-11-09 failures were HTTP 504s during acquisition, before builds/tests; the
cause of the upstream failures is not established.

Lean is selected exclusively from `lean-toolchain`. Elan retains the upstream
installer's latest stable policy. Bun retains latest stable, resolved on each
run; x64 uses the official baseline build so AVX2 is not required. No extra
secret is needed: the job's ephemeral `github.token` authenticates REST calls.
Fork PRs use their read-only Actions token for public assets and never write the
shared main cache. Missing/restricted tokens and HTTP 401/403/404 fail clearly;
there is no anonymous fallback. GHES and non-Linux runners are not supported.

The API's documented octet-stream endpoint can return binary bytes or redirect:
https://docs.github.com/en/rest/releases/assets?apiVersion=2022-11-28#get-a-release-asset
Authorization is sent only to api.github.com. Redirects are restricted to HTTPS
GitHub API and known GitHub asset CDN hosts; CDN requests carry no credential.
Only transport failures and 429/500/502/503/504 retry (four attempts, 2/4/8-second
backoff, 60-second socket timeout, ten-minute transfer deadline per attempt).

Exact caches include OS, architecture, resolved release pins and helper inputs.
Restore precedes binary acquisition; stable metadata resolution still needs the
API on warm caches. Only explicitly enabled main jobs save successful validated
installs. Lake packages, Mathlib cache, and trace-based build restore remain owned
by lean-setup. This does not mitigate unrelated GitHub action, Lake dependency,
Mathlib, npm or Playwright downloads.

Run `python3 .github/actions/release-setup/test_acquire.py` for deterministic
request/redirect/retry/version/cache regressions. CI runs the same tests. New
helper hashes force cold tool caches on the first PR run: successful real
Lean/Elan and Bun acquisition on the final PR head is required before merge;
fixture success alone is not hosted-download evidence.
