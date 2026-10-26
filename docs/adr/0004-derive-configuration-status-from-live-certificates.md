# Derive configuration status from live certificates

Status: accepted for the first executable #477 slice.

Configuration files persist explicit finite assumption selections and their
formal semantics, plus references to ordinary results and finite-model
registrations. They persist no success or closure fields. The existing frontier
remains the sole authority for premise closure and route cost.

A configuration's exact statement applications share one ordered Lean parameter
list. Live execution rebuilds referenced modules, checks each theorem against
those exact applications and runs its existing Comparator/NanoDa gate. Models
are checked by the existing registry verifier and must share the same parameter
assignment across all selected evaluations. This rejects stale certificates and
same-name statements applied to different worlds, frames or predicates. A
vocabulary's registered models cannot be silently omitted from its case.

The default CLI certifies before reporting; an explicit `--registered` mode
supports static dossier/explorer provenance without advertising fresh success.
A later verified explorer build may generate a disposable report during its
existing verification job. It must not introduce a committed proof-status store
or use a previous report as permission to skip invalidated checks.

Core inclusion prunes supersets without powerset search. Actual inclusion
minimality requires certified models for each single-premise removal; absence
of a smaller known theorem licenses only minimality among supplied certificates.
Conditional implication supports are bounded and include exact theorem
provenance; incompatible selections expose no explosive discoveries.
