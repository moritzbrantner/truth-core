# Sorites: two tolerance principles

This is an analyst investigation prompted by the owner's Sorites request, distinct
from the Ship of Theseus, river persistence, and the parthood theories in #325.
No source-derived claim or historical interpretation is introduced. No primary
source was consulted for attribution in this batch. The names describe explicit
semantic profiles, not an author's whole position.

## Decisive constraint

For a decidable predicate P on a finite natural-number case chain, P(0) and
not-P(n) force some k<n with P(k) and not-P(k+1). The induction tests P at the
penultimate case: if positive, it is the boundary; otherwise recurse on the
shorter chain. Decidability is an explicit scoped hypothesis. The result asserts
existence in this formal model, not that anyone can identify the boundary by
perception, nor that a grain count determines every ordinary use of “heap”.

The incompatible core does not need decidability: positive first, negative last,
and truth-preserving tolerance P(k)→P(k+1) at every step imply contradiction by
induction. Removing any one member admits a model already at n=1: constant
negative, constant positive, and positive-only-at-zero respectively. Thus the
core forces rejection of at least one commitment. It does not choose which.

## Strongest rivals and controls

- A sharp binary extension keeps opposed endpoints and drops universal
  truth-preserving tolerance. The boundary result alone does not establish this
  profile's linguistic or metaphysical adequacy.
- Restricted tolerance may keep binary endpoints while refusing the problematic
  local step. This needs an independently defended restriction, rather than
  selecting it just to save a favored view.
- A stipulated partial classification has positive, borderline, negative cases.
  At length two it keeps opposed endpoints with no immediately opposed pair,
  while losing truth-preserving tolerance already at the first step. Its weak
  non-opposition rule is a different principle, not a solution satisfying every
  original premise. This control is not full supervaluation or fuzzy semantics.
- Dropping endpoint classification is also consistent; the constant models
  witness the formal alternative, without suggesting that every ordinary
  endpoint judgment is dispensable.

Rejected inferences: vagueness is mereology; finite induction refutes every
indeterminacy semantics; local perceptual similarity is already equality or a
transitive equivalence; a formally existing boundary is detectable; a three-status
fixture establishes metaphysical indeterminacy. None follows.

## Verification and premise comparison

`TruthCore.Results.Logic.SoritesBoundary.certificate` binds the complete batch.
Frozen Challenge precedes the solution. Focused diagnostics checked the complete
new vocabulary and solution together on shared prover HEAD
f2db33e8273b214f158d63e2e3a17094ba181735, full-content SHA256
b5844ab4e8fcc6eb81b2a197647679c8f0ec3eb4fa5036fbaefc27f4187a8973,
with no diagnostics. Development concatenation only removes the new local import;
CI owns the delivered module build, binding, Comparator and NanoDa gates.
No Mathlib mathematics is needed beyond Lean's existing Nat and induction.

Actual premise comparison: the incompatible triple retains explicit positive
first, negative last and strong local tolerance inside its scoped theorem;
boundary extraction additionally assumes decidable binary membership. The
partial control replaces strong tolerance by weak non-opposition. No source
reading, ordinary-language adequacy, metaphysical application or current root
premise is established. Root route costs and open premises remain unchanged.
The remaining bridge is a defensible account of which classification and
which tolerance principle applies to the philosophical target.
