# Excluded middle, assertion and the remaining coverage boundary

The existing `ExcludedMiddleWithheld` package concerns stage-indexed proof and
assertion markers: asserting an excluded-middle instance requires a marker
for one side; some instance is unasserted somewhere; every instance is
irrefutable. It is derived by an existing result from explicit intuitionist
proof commitments and a separately open assertion-requires-proof input.
Those statements, source claims and frozen proofs are unchanged.

Object-level `ExcludedMiddle` is `∀ p : Prop, p ∨ ¬ p`. It contains no stage,
assertion or known-proof parameter. Without a bridge, holding and asserting
are different targets. No bridge is invented here.

`AllInstancesAsserted Asserts` says every stage asserts every instance. This
is an independent comparison policy, not an adopted norm or source fact.
`NotAllInstancesAsserted` is its exact logical negative. The checked
`WITHHOLDING-IMPLIES-NOT-UNIVERSAL-ASSERTION` projects the existing full
withholding package's explicit unasserted stage/content witness to that
negative. It is marked an instantiation transcription, not an independent
philosophical defense of its premise. The stronger raw source position stays
an explicit premise; it is not replaced by a weaker attributed reading.

## What the marker controls establish

With object-level excluded middle supplied explicitly, no-assertion/no-proof
markers satisfy the encoded withholding package alongside excluded middle.
The checked constructive irrefutability result is imported rather than
reproved. This demonstrates compatibility of these exact encoded formulas.
It is **not** a classical semantics attributed to intuitionism, a complete
intuitionist model, or a theory of epistemic access.

A mixed two-stage marker structure asserts every content at one stage with
no proof markers and asserts none at the other. Full withholding fails its
proof requirement, while universal assertion fails at the other stage. Thus
refuting the full raw package would not by itself establish the universal
assertion policy either. A logical negative target is needed for that role.

## Why the legacy endpoints are not silently moved

The object-EM graph currently records both the withholding position and
`SomeExcludedMiddleInstanceFails` as alternatives. The latter is exactly
`∃ p, ¬ (p ∨ ¬ p)`, **not** `¬ ∀ p, p ∨ ¬ p`. Its constructive refutation
proves no instance is deniable, not that every instance can be proved.
The existing source/proof record already distinguishes withholding and denial.

The engine's `defended()` criterion currently takes a nonempty finite list of
recorded alternatives as sufficient coverage when all are refuted; it does not
require a separate coverage result. Moving withholding away would leave only
the already-refuted weaker instance-denial and could create an unauthorized
all-alternatives-refuted path to object-level EM. Its legacy floor marking may
mask this path in current root counts, so unchanged counts would not repair
the semantic problem.

Consequently this batch adds the exact assertion-policy endpoint and checked
boundary but preserves both legacy object-EM edges and the existing floor.
Their notes name the unresolved coverage-authority migration. Notes alone do
not constrain closure. The coordinator must resolve that authority before
moving the old endpoints; no generic additional-option flag, source bridge,
floor approval or proof of object-level EM is inferred here.

The serious intuitionist position remains at full strength, including its
separate proof and assertion commitments. An eventual comparison of valid
rules/proof systems must encode its semantic profile and any mapping to the
stage markers explicitly. No complete census of logics or meaning theories
is claimed by this bounded policy consequence.
