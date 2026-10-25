# Hume’s argument and the scope of self-application

Issue #268 adds five analytical results to the existing #248 result. It does
not refute Hume’s actual causal reasoning, complete campaign #247, or import
Thomistic or Catholic premises. All conception relations and accessibility
frames in the tests are stipulated. Their philosophical adequacy remains a
separate question.

## What the verified source supports

The existing `HUME-TREATISE-I-3-3` witness was materialized and the complete
section (§§1–9, including the notes) read. No new snapshot or source metadata
was needed. The four new source claims cover these substantive steps:

| Passage | Bounded reading | Limit |
| --- | --- | --- |
| §§1–2 | The causal-beginning maxim lacks intuitive certainty under Hume’s comparison-of-ideas account. | An opponent may propose another infallible relation; this does not establish a complete epistemology or deny every entitlement. |
| §3 | Beginning and productive cause are distinct ideas separable in imagination. | The particular imagined beginning is not an arbitrary higher-order world predicate. |
| §4 | Alleged absurdity of uncaused determinate time/place cannot merely prove the absurdity of uncaused existence. | This is Hume’s reply to that argument, not a proved metaphysical homogeneity of times and places. |
| §§5–7 | Excluding all causes excludes self-causation and nothing-as-cause. | This hypothetical exclusion establishes no actual uncaused object. |

The §3 conclusion is **reused**, not given another identity:
`STMT-HUME-NARROW-IDEAS-WITHHOLDING`, supported by
`HUME-TREATISE-I-3-3-NARROW-A`, records the claimed absence of a refutation
from mere ideas. The new imagination claim records its distinct premise.
The source claims are attributed commitments without proofs of their truth;
the five results below take no historical claim as an assumption.

The weakest argument is passage-specific: distinguish beginning and cause;
represent the beginning without conjoining cause; take the resulting
separation to involve no contradiction refutable by reasoning from ideas;
therefore deny a demonstration of the causal maxim from those ideas alone.
Its last transition and the adequacy of its conception criterion remain
Hume’s philosophical commitments, not something Lean has verified about
human imagination.

Fidelity critique: §3 speaks of **actual separation** being “so far possible”
and immediately specifies absence of contradiction and absurdity. The narrow
record preserves that qualification; it does not erase the stronger wording
or settle whether a stronger, particular metaphysical-possibility reading is
ultimately right. Even that particular stronger reading would not itself
supply an unrestricted bridge over all higher-order predicates, its necessity,
or the specific conceptions of denial and modal collapse. Nothing in the
consulted §§1–7 warrants attributing those additional commitments. This is a
verdict about this passage, not a claim that no other Hume text could bear on
the generalization.

## Distinct formulas

Reuse `Conceivability.StrongBridge`:

- `H(w) := ∀P, C(P,w) → ◇P(w)` ranges over all functions `World → Prop`.
- `□H(w)` says every world accessible from `w` satisfies that world-relative bridge.
- `C(¬H,w)` conceives a world-relative failure of the bridge.
- `C(□¬H,w)` conceives necessary denial at a world; it is not `C(¬□H,w)`.
- `C(MC,w)` is another conception commitment. A grammatical label for MC supplies none of these commitments by itself.

No introspection, factivity, scope conversion or conceivability closure is
built into the reused free parameter `C`.

## Checked consequences and countermodels

`HUME-SELF-APPLICATION-HIGHER` composes the already verified #248 ordinary
self-application and necessary-conflict laws. Thus `H` and `C(¬H)` imply
`◇¬H` and conflict with `□H`. Instantiating H at necessary denial instead
gives `◇□¬H`. That **does not** produce an unconditional contradiction with
`□H` on K frames: the two boxes can concern different accessibility steps.
Two sufficient routes to conflict are proved explicitly:

1. reflexivity, so the accessible necessary-denial witness denies H at itself;
2. transitivity and a successor for every root-accessible world, so an
   accessible witness has a further world at which root-necessary H and the
   witness’s necessary denial meet.

These are sufficient routes, not a complete characterization of every frame
validating the implication. `HUME-SELF-APPLICATION-REFLEXIVE` sharpens the
reflexive route: `□H` already supplies H at the root, so no separate actual-H
premise is needed for either conception conflict. Its proof imports and uses
the higher-order result; none of its premises is added as an axiom.

`HUME-SELF-APPLICATION-SCOPES` reuses the #248 universal two-world `selfC`
witness. At `false`, H and `C(¬H)` hold, yielding `◇¬H`, but H is still
actually true and `C(□¬H)` is false. This directly defeats the inference
`◇¬H → ¬H`; it is a consistency countermodel, not a refutation of H.

The second witness has exactly one edge, `false → true`; `true` is a dead end.
At the root, C(P) means P is true at the successor; at the successor nothing
is conceived. H and `□H` hold at the root. So does `C(□¬H)`, because necessary
denial at the dead end is vacuous, whereas `C(¬H)` is false. The conceptions
of denial and necessary denial are therefore not interchangeable even in the
presence of actual H. No singleton cluster or cosmological conclusion is
inferred from the dead end.

`HUME-SELF-APPLICATION-DROPPED` uses three constructors with edges
`root → middle → last` and `last → last`. This frame is serial but not
transitive. Root conception tests truth at middle; middle conceives nothing;
last conceives everything and fails H. The root satisfies H, `□H` and
`C(□¬H)`: seriality cannot replace transitivity in the alternative route.
Changing only root conception to indiscriminate conception gives `C(¬H)`
without `◇¬H`; the root now violates H. Thus conception of denial alone does
not license possible denial without an adequate bridge. The earlier dead-end
model separately shows why transitivity without successor-seriality is also
insufficient. All edge and conception tables are explicit constructor cases.

## Which sense of conception?

`HUME-CONCEPTION-MODES` keeps three analytical alternatives separate from
Hume’s source-specific imagination and mere-ideas criterion:

| Analytical conception | Verified boundary |
| --- | --- |
| Grammatical description with a pointwise denotation | A conjunction of an atom and its negation describes a contradiction. A label also describes MC while an empty formal conception relation denies its conception. Description supplies no consistency or imaginative adequacy. |
| Satisfiability somewhere in the supplied model | The true Bool world satisfies a predicate that is inaccessible from false under identity accessibility. This is neither root-accessible metaphysical possibility nor a complete calculus of logical consistency. |
| Conception defined as root-accessible possibility | H is true by definition; this does not independently vindicate imagination or description. |

Treating contradiction-free description as satisfiability somewhere is one
precise semantic alternative in this experiment. It is not identified with
Hume’s refutation criterion or with a complete proof calculus.

The old bounded `NarrowWithholding` interface can coexist with an empty
conception relation satisfying H or an indiscriminate one violating H. This
is an interface-compatibility check: the unspecified refutation relation does
not secretly impose modal soundness. It is not a model of Hume’s whole mind
or epistemology.

## Verdict and verification boundary

The unrestricted bridge is not valid for every arbitrary conception relation:
indiscriminate or merely grammatical conception has explicit countermodels.
The move from possible failure to actual failure is invalid. A necessary
bridge together with suitable self-application and stated frame conditions
is inconsistent; a merely actual bridge need not be. None of these results
shows that the sourced narrow argument asserts the inconsistent package.
Conceivability of modal collapse, metaphysical contingency and the intended
frame still require independent philosophical warrant. No `refutes` edge
against the sourced narrow statement or Catholic-root closure is claimed.

Each result’s exact bundled proposition is frozen in its Challenge, with a
separate Solution, inference/argument record and empty-axiom Comparator
configuration. The proof accepts the consequences by instantiation,
accessibility composition, existing theorem projection and finite constructor
countermodels. Definitions and the two new disambiguations specify modal
scope and description/consistency senses. The initial axiom audit prints no
axioms for all five results; the final gate also checks Comparator and NanoDa.
