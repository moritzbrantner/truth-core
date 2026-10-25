# Hume: conceivability, self-application and collapse

This is the bounded contribution of #248 to Humeanism campaign #247 and the
objective-truth investigation #207. It does not settle either campaign or
show Humeanism false. `HUME-CONCEIVABILITY-TESTS` verifies the conjunction
`TruthCore.Modern.Hume.Conceivability.Checks`, frozen in its Challenge module.
No source commitment is a premise of that theorem.

## Source and fidelity

`HUME-TREATISE-I-3-3` pins Hume Texts Online's original-English I.3.3.
The entire section, including §§1–7 and the concluding §§8–9, was materialized
and read. `HUME-TREATISE-I-3-3-NARROW-A` attributes the §3 conclusion that
reasoning from mere ideas cannot refute the description of a beginning
without a cause. `NarrowWithholding` represents that conclusion with an
explicit description and refutation-relation parameter; it does not implement
a calculus of Hume's ideas or verify the interpretation. It is an open source
commitment, with no result claiming to prove it.

Fidelity critique: §3 does use possibility language about actual separation,
so the narrow reading intentionally records less than the whole passage.
It preserves the explicitly qualified consequence concerning contradiction
and reasoning from ideas; it neither denies a stronger reading nor attributes
an unrestricted bridge over all world-indexed propositions. §§5–7 reject
turning an absence of causes into self-causation or a cause called nothing.
Those arguments do not attest that the bridge is itself conceivable as false,
that it is necessary, or that modal collapse is conceivable. No such
attestation is invented here. A statement about an object beginning without
a productive cause is not a statement about arbitrary higher-order predicates.

The test vocabulary separates a free formal conception relation C, Hume's
passage-specific imaginability, absence of contradiction/refutation from
ideas, metaphysical possibility interpreted by accessibility, epistemic
compatibility with information, and demonstrability. Their definition records
and disambiguation are linked from the statements. Explaining a description
of collapse does not establish that the description meets Hume's relevant
criterion of clear conception. That missing philosophical warrant remains
open; no test assumes its historical endorsement.

## What follows formally

Let H(w) mean ∀P, C(P,w) → ◇P(w), with P ranging over every function
World → Prop. C(¬H,w) and H(w) give ◇¬H(w). This is not ¬H(w).
The universal two-world `selfC` model satisfies H and C(¬H) at false while
H fails at true. Thus those premises do not yield a contradiction or an actual
failure of H. Adding □H conflicts with the obtained accessible failure.
Necessity is a separate commitment. For a fixed P, □¬(C(P)→◇P) has still
another scope and is not an alias for ¬∀P(C(P)→◇P).

Define local collapse MC(w) := ∀P, P(w) → □P(w). With **full function
comprehension**, instantiate P(v) := v = w. MC then forces every world
accessible from w to equal w. This is stronger than a mere truth-value
invariance argument: equality predicates provide point separation explicitly.
For a restricted proposition domain, equal truth values would require an
additional separation/extensionality premise before yielding world identity.
The theorem makes no assertion about such restricted semantics.

On symmetric transitive frames (hence S5 equivalence frames), an accessible
MC-world sees the origin by symmetry and its successors by transitivity.
Separation identifies them, proving ◇MC → MC on that component. Every P and
its negation are therefore invariant there. Every accessible P is actual;
reflexivity additionally makes truth and possibility equivalent. Distinct
isolated components remain possible: identity accessibility on Bool satisfies
MC at false although false ≠ true. No result concludes global uniqueness of
worlds, nor global validity of MC from a component-local premise.

Contingency here means ◇P ∧ ◇¬P. It is constructed independently on universal
Bool accessibility, with P(w) := w = true and explicit witnesses true and
false. On a symmetric transitive component, that contingency conflicts with
◇MC; hence H together with C(MC) conflicts with it too. This is a conditional
impossibility theorem. The finite construction does not establish that any
real-world proposition is metaphysically contingent.

## Models and weakened assumptions

| Fixture | Established property | What it distinguishes |
| --- | --- | --- |
| Universal Bool, indiscriminate C | H fails on the false proposition | C has no built-in metaphysical soundness |
| Universal Bool, selfC | H ∧ C(¬H) at false | Possible failure is not actual failure |
| Universal Bool, P(w) := w = true | ◇P ∧ ◇¬P | Independent semantic contingency |
| Branching Bool | Reflexive/transitive; ◇MC ∧ ¬MC at false | Symmetry cannot simply be dropped |
| Universal Bool, empty C; no ideas-refutations | H and NarrowWithholding | Narrow withholding need not refute H |
| Identity accessibility on Bool | MC at false; false ≠ true | Component collapse is not global uniqueness |

The branching frame is false→false, false→true, true→true. Its true world
collapses, but the origin does not: P(w) := w = false is true at the origin
and false at its accessible successor. Thus even reflexivity and transitivity
alone do not justify the S5 step. The narrow-withholding model is a consistency
test of the bounded interface, not a model of Hume's whole philosophy.

The embedding reuses `Frame`, `MProp`, `Box` and `Dia` from the existing
modal/Scott fixtures. None of Scott's positivity, essence, existence or
theological premises is used, and its axiom-system collapse is not equated
with a Humean view. The proof is constructive and requests no permitted axioms.

## Result and remaining frontier

Accept the result as a conditional modal analysis: the proof follows by
instantiation, singleton separation, accessibility composition and explicit
models. It supplies an attack on strengthening the narrow reading to a
necessary unrestricted bridge **if** the additional conception commitments
are justified. It supplies no `refutes` relation against the sourced Hume
statement, no closure of an objective-truth frontier, and no completion of
#247. The open work is philosophical justification of those stronger
commitments, including the relevance of the chosen proposition domain and
frame, rather than another assumed bridge hidden inside a proof.
