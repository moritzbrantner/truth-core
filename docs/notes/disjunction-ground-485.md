# Local truthmakers versus one ground of a necessary existential disjunction (#485)

This note records the first slice of #485. The theorem is `disjunctionGroundMap` in
`TruthCore.Results.Explanation.DisjunctionGround.Solution`. Its vocabulary is in
`TruthCore.Explanation.DisjunctionGround` and reuses the arena of
`TruthCore.Explanation.PSRStrength` (#755). The theorem is zero-axiom. It establishes
conditional consequence and the satisfiability of encoded bundles. It does not establish
any grounding principle, the metaphysical possibility of any model, or any premise on a
root route. No source claim is added. The grounding literature listed on #485 (Merlo,
Trogdon, Leuenberger, Richardson) and the Pruss and van Inwagen material on the Big
Conjunctive Contingent Fact were not read for this work, so nothing below is attributed
to them.

## The question

The alternating model of #445 (`NECESSARY-INDIVIDUAL-ALTERNATING`) has
`□(E a ∨ E b)` with neither `□ E a` nor `□ E b`. #485 asks what, if anything, must
ground that necessity, and whether grounding it requires a necessarily existing
individual.

## The relations kept apart

All four are read at a world `v` of the arena and concern the existential fact `d`
(`ExistentialFact`: `d` is true exactly where some candidate exists).

- **Local ground** (`LocallyGrounded`, `□ ∃ r`). In ordinary language: wherever
  something exists, there is some answer to "why does something exist here?". The
  example is a world-local truthmaker: at world `false` the existence of `false`, at
  world `true` the existence of `true`.
- **Uniform ground** (`UniformGround`, `∃ r □`). One answer that serves at every
  accessible world. The example is a necessary law, or the existence of one necessary
  individual. The counterexample is the truthmakers model, which has local grounds and
  no uniform ground. This is the same quantifier shift that #445 certified for
  existence. Here it is certified for reasons.
- **Instance reading** (`InstanceGrounding`). Every reason for `d` is some individual's
  existence fact. This is the usual truthmaker reading, on which an existential fact is
  grounded by an instance. The counterexample is the `lawGround` model, in which an
  abstract law that is no one's existence fact is the reason.
- **Efficient producer** (`Ontic.Causes`). This is never inferred from `explains`. None
  of the six models has any causation.

`explains` keeps the bare `PSRStrength` reading (DEF-PSR-STRENGTH-REASON), "admitted
as a reason why". No structural property is assumed. Factivity (`Factive`), coherence of
existence facts (`Coherent`) and necessitation (`Necessitating`) are listed hypotheses
or model properties. Transitivity, asymmetry and well-foundedness play no role.
DISAMB-DISJUNCTION-GROUND records the four senses and shows that no result passes from
one to another.

## What is proved

1. `UniformGround → LocallyGrounded`. Under factivity, local grounds make `d` true
   at every accessible world, so `d` is necessary.
2. Under factivity, coherence and the instance reading, local grounds give an existing
   individual at every accessible world. This is necessary population, de dicto.
3. **Bridge theorem.** Factivity, coherence, the instance reading, `Access a a` and a
   uniform ground together give `NecessaryBeing` at `a`. That is an actually existing
   individual that exists at every world accessible from `a`. The proof is not a
   transcription: the uniform reason is shown to be one fixed individual's existence
   fact, and factivity and coherence then carry that individual's existence to every
   accessible world.
4. **Fork**, assuming excluded middle. Under factivity, coherence and `Access a a`, a
   uniform ground is either a reason that is no individual's existence fact (the
   abstract-rule horn) or there is a necessary being. The horns are not claimed to
   exclude each other: a model with both a law and a necessary bearer would satisfy
   both.

## Models (each at world `false`, two worlds, two rigid individuals)

| model | deletes | uniform ground | necessary being | notes |
|---|---|---|---|---|
| `truthmakers` | uniform ground | no | no | local, factive and necessitating instance grounds; `d` is necessary and `E false` is contingent |
| `lawGround` | instance reading | yes (law) | no | the law is necessary and necessitating; no causation |
| `nonfactive` | factivity | yes | no | the reason `E false` is false at world `true` |
| `incoherent` | coherence | yes | no | existence facts are true where their individual is absent |
| `unseenActual` | `Access a a` | yes | no | `true` exists at every world accessible from `false` but not at `false` |
| `fixedBearer` | nothing | yes | yes | the necessary individual grounds `d` and causes nothing; the contingent individual `false` has no cause |

The first five models each keep every other premise of the bridge theorem together
with "no necessary being". They therefore certify that the six-member bundle {factive,
coherent, instance reading, `Access a a`, uniform ground, no necessary being} is an
inclusion-minimal inconsistent core. `fixedBearer` shows that the bridge's premises are
jointly satisfiable, so the theorem is not vacuous.

## Answers to the #485 research cases

1. **Baseline.** The `truthmakers` model reproduces the #445 alternating existence
   extension inside the reason arena. It is a second model with the same existence
   pattern, not a second copy of the #445 semantics, because it adds facts and reasons.
2. **Quantifier and grounding gap.** Local grounds do not give a uniform ground. A
   uniform ground is not an efficient producer: no model has causation.
3. **Scope of necessitation.** Necessitating reasons do not supply a necessarily
   existent ground. Both `truthmakers` and `lawGround` are `Necessitating` and have no
   necessary being. The separate guard, that a necessary reason that necessitates a
   particular contingent disjunct is incoherent, is already certified on main as
   `contingentExcludesNecessaryNecessitatingReason`
   (`TruthCore.Causality.BruteFoundationExplanations`) and in `PSR-COLLAPSE-CORE`. It is
   not reproved here.
4. **Strongest rival.** The `lawGround` model is a coherent stipulative model of a
   necessary abstract rule that guarantees a member of the roster exists, with no
   necessary individual. What a theist argument must add to exclude it is exactly the
   instance reading, or some other premise that turns a uniform ground into a bearer.
   That premise is open.
5. **Minimal contradictory core.** This is the six-member core above.

## Open premises and remaining #485 scope

- **Open.** Whether the necessity of the existential fact needs any uniform ground at
  all. An Oppy-style rival takes local grounds as enough, which is the `truthmakers`
  model. The instance reading as a constraint on grounds is also open, and the
  `lawGround` rival denies it. Neither is defended here.
- **Not done in this slice.** These items come from the investigation comments on #485:
  the finite all-contingent explainer elimination, the `ℕ` prefix countermodel, the
  totality and distribution route, the directedness and Zorn bridges, and the
  well-founded deterministic propagation theorem. The totality route is partly covered
  on main by `PSR-COLLAPSE-CORE`, `BCCF-DERIVATIVE-REPLY` and `STOPPING-POINT-MAP`.
- **Root frontier.** No change. The map has no premises and no root-path statement
  consumes it.
