# Existence-PSR scope: two countermodels

This is a small, axiom-free **model-theoretic test**, not an assertion that the
principle of sufficient reason is true. It advances the distinction in #312 and
retains the separate causation and explanation questions in #310 and #311.

## Reuse and formal boundary

`TruthCore.Explanation.ExistencePSR` reuses `Ontic`, `ContingentAt` and
`NecessaryBeing` from `TruthCore.German.Kant.CosmologicalInference`. An
`ExistenceFact.fact x` is a tagged candidate proposition, true at world `w`
just when `ExistsAt w x`. The *explanation* relation has type
`World → Reason Being → ExistenceFact Being → Prop`; the separate causal
relation remains `Ontic.Causes : World → Being → Being → Prop`.

`Sound` prevents explanations for false existence facts. It does **not** impose
a philosophical test of explanatory sufficiency. `ExistencePSR` is universal
over *existence facts*, not over every actual truth. `ContingentPSR` covers
only actual individuals with an accessible world in which they fail to exist.
`EveryExistentExternallyCaused` instead requires a distinct actual causal
predecessor for each individual.

## The models

The advertised theorem `psrScopeBoundary` constructs both cases with two
Boolean worlds, two candidate individuals and universal accessibility:

1. **Existence-PSR without external causation.** Only `false` exists, at both
   worlds. Its existence has a stipulated `intrinsic` reason at each world.
   There are no causal arrows at all. `NecessaryBeing` and `ExistencePSR`
   hold; `EveryExistentExternallyCaused` does not.
2. **Contingent-only PSR without explanation for necessary existence.** The
   individual `false` exists in both worlds, but `true` exists only at world
   `false` and has a stipulated `circumstance` reason there. The necessary
   individual has no assigned explanation anywhere. `ContingentPSR` holds
   non-vacuously and a necessary individual exists, but `ExistencePSR` fails.

Consequences of the model definitions:

- An unrestricted-over-existents PSR does *not by itself* say everything has
  been caused by some **other** individual. A claim that every explanation
  requires such a distinct cause needs an independent bridge.
- A contingent-only PSR does *not by itself* explain necessary existence. An
  opponent applying an explanatory demand to a necessary being must identify
  why that demand applies if their accepted PSR was contingent-only.
- Conversely, someone who grants brute contingent existence yet demands that
  necessary existence have a further explanation has not asserted a formal
  contradiction. They owe an **independent scope-sensitive reason** for this
  asymmetry. The countermodels do not refute that possible reason.

## Premise comparison and frontier

- **Retained:** world-relative existence, modal contingency/necessity and
  distinct causal relations, with universal accessibility for both models.
- **Added as definitions, not metaphysical premises:** tagged existence facts,
  candidate explanation tokens, soundness, the two PSR variants, and the
  separate external-cause predicate.
- **New open philosophical obligations:** whether intrinsic explanations can
  be sufficiently informative and non-circular; whether a fully unrestricted
  PSR applies to necessary existence and to every other kind of fact; whether
  an explanation must be causal or well-founded; and whether a necessary
  existent is actual. Nothing here proves that a God exists.

This result discharges the *formal non-entailment* tests only. It connects
conceptual alternatives around #312; it does not close an argument to the
Truth Core root. The infinite borrowed-power actuality and whole-chain
explanation investigations (#310, #311) remain open.
