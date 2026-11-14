---
date: 2026-11-12
where: "owner direction and owner decision, 2026-11-12"
---
**Strength Registrations Compose With Closure.** The owner directed that every
implication from a strong version to a weak version be persisted as a
`strengthens` relation, and decided that formal correctness of the registered
order matters more than incentives. Until now `frontier` set a registration's
backing argument aside everywhere: for closure, for the reaching-root walk and
for route expansion. That under-reported what the proofs show: if the strong
version is closed by derivations from premises P and strong ⇒ weak is a
verified result, the weak version follows from P by composition. Asked whether
a registration should close its weak version whenever the strong version is
closed by a derivation that does not run through the weak version, the owner
answered "Yes, close through it." The backing argument is now an ordinary verified derivation for
closure, by rule (a) or by rule (d) when its result is a transcription
(invariant 16); like any one-premise argument it also closes the weak version
from an open strong leaf, since "closed" means proved from premises that may
be open. It is set aside only when, in a bottom support cycle, its strong
version's support reaches back to its own weak version through a
non-registration step that uses the weak version, because circular support is
not a derivation; other registrations in the same cycle stay. A registration whose argument backs a `refutes` relation still
counts as that refutation. For reachability and route expansion it is an
ordinary verified derivation: `reaching_root_statements`, `path_to_root`, the
open-premise items, `premise_dependents`, `support_options`, `thickness`,
`orphans`, `dossier` and `context` include it, and `--routes` may expand an
unsourced weak version through it (a transcription registration expands
nothing). `established` still changes only through the strength-order
propagation (#1017). A new optional argument field, `weakening: true`,
declares that a one-premise argument derives a weaker version of its premise;
`check` warns about a verified argument that declares it, or that is the
`implication` or `delta_forward` evidence of a `strength_comparison`, without
a `strengthens` relation for the pair. Proof, binding and source rules are
unchanged. An audit of the 209 verified one-premise results without a
registration registered 45 strength orders, including the declined one,
recorded two verified equivalences as `logically_equivalent_to` (removing the
one-way registration of one of them), and left equivalences, countercase steps
and consequences with new content unregistered with reasons
(`docs/notes/strength-order-audit.md`). The current contract is in
`docs/corpus-model.md`, "Strength order".
