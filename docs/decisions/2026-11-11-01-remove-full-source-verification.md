---
date: 2026-11-11
where: "owner direction, 2026-11-11"
---
**Remove full-source verification.** The owner rejected recurring full-source
verification as an impractical standard that causes unrelated failures. Source
metadata, claim bindings and attribution records are checked offline. CI on
PRs, main, schedules and manual dispatch does not refetch source witnesses or
materialize fixed historical samples. Remove the bulk verification command and
its CI-only exceptions rather than keeping the requirement behind retries,
per-host exemptions or a separate scheduled gate.

Source research still reads the cited material. Individual materialization,
raw-witness acquisition and pinning remain explicit research tools with their
existing integrity checks. Missing cached text is reported as not checked in
that run; offline success is not fresh byte verification or source fidelity.
Existing source records, hashes and unavailable/bibliographic markings remain.
Lean, binding, frozen Challenges, Comparator, NanoDa and frontier closure rules
are unchanged. The current contract is in `AGENTS.md` and
`docs/source-evidence.md#validation`.
