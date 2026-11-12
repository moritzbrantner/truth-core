---
date: 2026-11-12
where: "owner direction, 2026-11-12"
---
**Strength Registrations Reach The Root.** The owner directed that every
implication from a strong version to a weak version be persisted as a
`strengthens` relation. Until now `frontier` set a registration's backing
argument aside everywhere: for closure, and also for the reaching-root walk and
route expansion, so registering an implication could remove a route to the
root. Workers declined registrations for that reason (`specs/contingent-being-node.toml`).
The backing argument now stays set aside for closure only: it closes nothing by
rules (a) or (d), and `established` changes only through the strength-order
propagation (#1017). For reachability and route expansion it is an ordinary
verified derivation: the strong version is a premise the upward walk follows, so
`reaching_root_statements`, `path_to_root`, the open-premise items,
`premise_dependents`, `support_options`, `thickness`, `orphans`, `dossier` and
`context` include it, and `--routes` may expand an unsourced weak version through
it (a transcription registration expands nothing). The rule change itself left
every closed, established and refuted statement and every closure label
identical on the corpus at the time. A registration still sets its backing
argument aside for closure, so registering a pair can change closure: a weak
version whose only proof was that argument stays open while the strong version
is closed but not established, and a strong version can close because the
registration breaks a support cycle through its weak version. A new optional argument field, `weakening: true`, declares that a
one-premise argument derives a weaker version of its premise; `check` warns
about a verified argument that declares it, or that is the `implication` or `delta_forward`
evidence of a `strength_comparison`, without a `strengthens` relation for the pair. Proof, binding, source and closure rules
are unchanged. An audit of the 209 verified one-premise results without a
registration registered 42 strength orders, including the declined one, recorded
two verified equivalences as `logically_equivalent_to`, and left refutation
arguments, equivalences, countercase steps and consequences with new content
unregistered with reasons (`docs/notes/strength-order-audit.md`). The current
contract is in `docs/corpus-model.md`, "Strength order".
