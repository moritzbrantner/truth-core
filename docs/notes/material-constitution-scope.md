# Material coincidence and the scope of extensionality

This is an analyst reconstruction for #1075, with attribution deferred. It tests
an inference used in statue/lump discussions, rather than attributing that
inference or an answer to a historical author. No new source claim is made.

The reuse inventory inspected `STMT-PROCESS-TURNOVER-BOUNDARY` and
`STMT-THESEUS-IDENTITY-BOUNDARY`, their dossiers, related arguments, prior attempts
and exact Lean modules. Turnover concerns one carrier with changing constituents;
Theseus concerns competing bearer assignments to a replacement/reassembly
history. Neither supplies the same-history comparison below. The certificate
imports the existing turnover result and applies `TheseusIdentity.chain_identity`
to transport an arbitrary bearer predicate along any identity-preserving finite
chain. Neither proved result is restated as a new open premise.

## One represented history, two interpretations

There are two times and one individually tracked material token. There are two
enduring bearer labels, statue and lump. Both have that token initially; later
the statue is absent while the lump still has it. The ordinary statue example
motivates describing the transition as reshaping, but shape, mechanics, location
and a persistence criterion are **not** encoded. Divergent numerical persistence
is openly stipulated. These finite observations alone do not justify it in
reality. There are no modal worlds or modal possibility claims.

| Representation | Initial token slice | Later token slice |
| --- | --- | --- |
| Enduring statue | {token} | empty (absent) |
| Enduring lump | {token} | {token} |
| Statue temporal whole | {(initial, token)} | initial/later slices as above |
| Lump temporal whole | {(initial, token), (later, token)} | initial/later slices as above |

The last two rows list the **entire** temporal occurrence sets. They are nonempty
Mathlib sets, with subset as global parthood. The existing generic
`UniversalFusionBoundary.Overlap` means having a common part; the singleton
initial occurrence is such a nonempty part here. Its concrete `Body` carrier was
not reused: Bool constituents without time would erase the distinction at issue.
The new `Whole` only changes that carrier to time/token pairs and retains the
same standard subset semantics. It is not a new assertion of universal fusion.

`Correspondence` proves, for every represented time, both existence equivalence
and membership equivalence for every token between the enduring assignment and
its assigned temporal whole. Thus the models agree on all observations in this
small signature, in one fixed history. This does **not** identify their
ontologies, prove that enduring objects have temporal parts, or establish an
adequate physical model. Bool occurs in both argument domains solely as a finite
encoding; separate argument positions distinguish time and bearer labels.

## What the proofs constrain

`Coincident` requires exact token membership equivalence at a single time and
nonemptiness of that slice. `SliceIdentity` adds the bridge from such coincidence
to ordinary bearer equality. The generic incompatibility theorem takes initial
coincidence and later absence of one bearer plus presence of the other. Applying
the bridge equates the bearers and transports existence, contradicting absence.
This conditional step is elementary equality; the substantive closed certificate
also constructs the two representations, their common observations, their
overlap, their distinct extensions and their different extensionality scopes.
It is not just an opaque implication-to-conclusion transcription.

Global extensionality is independently proved for **all** nonempty occurrence
sets: if membership agrees for every represented time and token, the sets and
therefore their subtype objects are equal. Nothing here says membership at one
time suffices. The two temporal wholes therefore consistently have the same
nonempty initial slice and different later existence while global extensionality
holds. Their whole extensions differ at the later occurrence.

Material constituent coincidence is not equality of all mereological parts.
The lump temporal whole is its own part and is not a part of the statue temporal
whole. A separate certificate clause refutes their having all the same global
parts. Omitting self-parts, silently identifying material tokens with all parts,
or applying extensionality to only the initial slice would change the tested
principles. These readings were rejected, not refuted as independently stated
philosophical positions.

## Rivals and open bridges

A one-object view can deny the pair of divergent numerical persistence judgments.
A sortal-relative account can reinterpret the identity/persistence relation;
ordinary Lean equality is not automatically that relation. Neither rival is
refuted by this certificate. A stronger temporal-parts metaphysics needs its own
bridge from the occurrence-set interpretation to actual objects. The enduring
interpretation likewise needs a defended persistence criterion; it is not made
true by two labels. The signature cannot distinguish the interpretations by any
extra spatial, causal, shape or modal observation because it includes none.

Intended root-premise delta: **no change**. No external philosophical premise is
established: the result closes a mathematical certificate of conditional scope
constraints and concrete interpretations. The correspondence, subset parthood
and finite-chain transport do not discharge materialism, persistence, substantial
unity, soul, physical/modal applicability or any Catholicism-root obligation.
The computed frontier comparison is recorded in the PR and CI.

## Verification

The Challenge and vocabulary were frozen at commit `7bc2d1fc` before Solution
work. Reproduce the focused build with
`python3 scripts/worker_env.py -- lake build TruthCore.Results.Mereology.MaterialConstitutionScope.Solution`,
then run `python3 scripts/worker_env.py -- scripts/verify-result.sh MATERIAL-CONSTITUTION-SCOPE`
and `python3 scripts/worker_env.py -- python3 scripts/corpus.py bind-check --result MATERIAL-CONSTITUTION-SCOPE`.
The allowed Mathlib axiom ceiling is exactly `propext`, `Classical.choice`,
`Quot.sound`; the actual exported axiom report and independent NanoDa check are
in the PR's verification evidence. Final CI verifies the delivered revision.
Shared engineering policy resolved at source revision
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.
