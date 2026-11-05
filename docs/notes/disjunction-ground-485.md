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

## Truthmaker theory profiles (#941)

### Source read and interpretation boundary

The complete four-page author manuscript of Trenton Merricks, *Précis of Truth
and Ontology* (2011), was pinned twice, materialized and read, including the
surrounding argument summaries. The author-hosted PDF and Wayback capture
20240413232124 have identical bytes and extracted text. The claim locators are
physical manuscript pages; the journal pagination is 184–186. The book itself
was not read. No inference from the précis to a complete historical theory is
claimed.

- Physical p.1 defines Truthmaker as every truth having some entity that makes
  it true. This reports the doctrine, not Merricks's endorsement. A policy over
  every formal world is an analyst modal interpretation, not a quantifier
  literally stated by that sentence.
- Physical p.1 gives a **partial necessary condition**: maker and proposition
  existence jointly guard necessitation of truth. Dropping proposition
  existence would strengthen this. Our rigid fact labels therefore require a
  separate availability interpretation; `MakerNecessitation` is explicitly an
  analyst framework property, not that exact sourced statement.
- Physical p.2 reports the negative-existential argument and its rejection of
  Truthmaker. This is a source commitment; neither its truth nor the book's
  detailed argument is mechanically certified here.
- Physical p.3 retains a demand for truthmakers only for truths about mere
  existence, while refusing to call this a successful curtailed Truthmaker
  doctrine. That class can include general existential truths. Our
  `ExistenceScope`, containing only `A.exist b` labels, is narrower; it is not
  silently identified with Merricks's whole class. The negativeArena's positive
  fact is a mere-existence instance, not an exhaustive analysis of his thesis.

These four source statements are prose-only and retain their own identities.
The conditional configurations below are analyst propositions. Source fidelity,
interpretation and formal verification have different authorities.

### One arena, three scope policies

`TruthmakerTheories.Making W B F` relates a **bearer** to a fact, at a world.
`Arena.explains` instead relates facts. `Ontic.Causes` is efficient causation.
They are distinct. `InstanceMaker` can project a reason through an individual's
existence fact; its soundness is proved only with existing factivity and
coherence. It is not the definition of every truthmaker. `lawGround` has a
uniform fact-reason but no world-immanent uniform bearer maker.

Sound making requires both truth of the made fact and existence of that maker
at the making world. No transitivity, asymmetry or well-foundedness is assumed;
the different argument sorts would first require a typed composition operation.
An individual making a fact of its existence true is an orientation example.
A false fact cannot have a sound maker; an absent candidate fails immanence;
a true negative may lack a maker. Real-world making, aboutness and relevance
need a source-backed analysis or explicit further framework commitments. A
necessary condition is not a sufficient metaphysical analysis.

| Profile | Checked commitment | What it leaves open |
| --- | --- | --- |
| Maximalist | Sound makers for every true fact in the supplied carrier, at every world | Same-maker identity across worlds, production, aboutness |
| Restricted | Sound makers for true facts in a named scope | Makers outside that scope are permitted, not denied |
| Free | Soundness only; no coverage requirement | Both empty and nonempty maker relations are admitted |

The finite `DFact` models are **fragment** models. The stronger
`TRUTHMAKER-TRUTHSET-NONUNIFORMITY` uses **every** `Bool → Prop` truth set as a
truthbearer, ordinary evaluation at each world, and explicit negation and
conjunction closure. On the literal alternating ontology from #938, each true
proposition has a world-immanent maker, and its maker necessitates that truth
wherever that maker exists. Nevertheless, the constant true proposition has
only local makers, with no uniform maker and no necessary individual. This
removes the positive-only fragment loophole within that full propositional
truth-set interpretation. It does not model all essential/aboutness theses of
Armstrong, Merricks or another metaphysical theory, and it does not prove the
ontology metaphysically possible.

### Exact consequences and controls

- Maximalist implies each restricted policy and free semantics. The implication
  is scope inclusion; it is not three mutually exclusive or exhaustive
  worldviews. Free semantics is deliberately permissive.
- Coverage of a necessary fact gives local makers. Maker necessitation does
  not turn these varying bearers into one necessary maker.
- A uniform maker, world immanence and actual self-access give that SAME
  bearer's actual and accessible-world existence. Factivity and existence-fact
  coherence are unnecessary for this direct bearer theorem; the relation
  already has an individual argument. This is conditional, not a defense of
  uniformity or immanence.
- The finite `fixedBearer` interpretation has both maximalist coverage and a
  uniform maker, so the positive branch is satisfiable. It causes nothing.
  `switchingFixedMaking` retains a necessary individual and maximalist coverage
  but switches makers of the existential fact: necessary individual existence
  alone does not ensure it makes that fact true everywhere.
- The restricted relation has a positive, actual existence-fact maker and a
  true unmade existential fact. `TRUTHMAKER-RESTRICTED-SEPARATION` proves
  explicit noncoverage and failure of maximalism. The original frozen
  `TheoryMap` has a weaker existential-negation conjunct at this point;
  rather than edit that target after freezing, the strong intended claim is
  separately frozen and certified in this companion result. No proof of the
  weaker conjunct is advertised as the strong separation.
- Free semantics has both a no-maker interpretation and the nonempty local
  interpretation. It is not a universal denial of making.

### Negative truth and the eligible-maker domain

The #554-style core is now checked under the SAME new making vocabulary:

1. `EmptyFact A e` makes truth of e equivalent to absence of **every eligible
   roster member**.
2. That true negative fact requires some maker there (`NeedsMakerAt`).
3. A maker exists in its making world (`WorldImmanent`).

These are inconsistent; no S5, causation or contingency premise is used. The
coverage instance for this one negative fact suffices; unrestricted maximalism
is stronger than needed. Each omission has a typed control: populated world
without an empty truth; empty world without required coverage; or factive
making by a non-immanent candidate. The third is an omission model, not an
endorsed ontology of nonexistent entities.

`negativeArena` represents an actual positive existence truth and an accessible
true negative, with substantive existence-only coverage. It has no maker for
the negative, and maximalism fails. This comparison is relative to the stated
scope, not a refutation of every restricted theory.

B empties **all eligible makers**, including abstracts if those belong to B.
That B exhausts reality is itself an OPEN domain-completeness bridge. A separate
`abstractArena` is concretely empty according to a supplied false concrete
predicate but has an existing maker. The negative label there means concrete
absence (`ConcreteEmptyFact`), not absolute absence. Maximalism and immanence
survive; only the added `ConcreteMaker` bridge excludes that interpretation.
No independent analysis of concreteness or justification of empty-world
possibility is supplied. This advances #554's formal core but does not close
that whole issue or add a self-reference/diagonal assumption.

### Actual premise comparison

All four certificates are source-free logical/model results, reusing the exact
prior `truthmakers_facts`, `lawGround_facts` and `fixedBearer_facts` theorems.
No truthmaker scope, necessity, empty-world possibility, source commitment or
root premise is independently established. The necessary-being route would
still need uniformity (or a separate principle supplying it) and its semantic
applicability. The PR reports computed `frontier-diff`; no hand-counted premise
reduction is inferred from the new relation's bearer argument.
