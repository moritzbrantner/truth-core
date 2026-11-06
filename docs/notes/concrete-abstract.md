# Concrete and abstract (#1103)

The corpus took `concrete : B → Prop` as a free parameter in dozens of files.
Several models set it to `True`, so the distinction no longer constrained
anything and "abstract things cannot cause" could not even be stated. The
shared vocabulary is `TruthCore/Ontology/ConcreteAbstract.lean`.

## Adopted sense (owner decision, 2026-11-06)

[Decision record](https://github.com/moritzbrantner/truth-core/issues/1103#issuecomment-6683616439).

- **Concrete:** having esse *in re*, its own act of existence in reality
  (`HasEsseInRe InAct esse x := InAct x esse`, reusing `DEF-ESSE`).
- **Abstract:** the contradictory of concrete, having no esse in re
  (`EsseAbstract := ¬ InAct x esse`). At most it has being in the intellect,
  as the number 2 does.
- There are no borderline cases. The owner: "We have these words in order to
  draw a line. The same way we have words like dead and alive, inside or
  outside." ([record](https://github.com/moritzbrantner/truth-core/issues/1103#issuecomment-6683816810))
  Disjointness holds by non-contradiction and exhaustiveness by excluded
  middle (`EsseDichotomy`, result `CONCRETE-ABSTRACT-ESSE-DICHOTOMY`). Both
  are derived, not assumed. The exact dichotomy belongs to the esse criterion
  only; the rival criteria below need not be exhaustive.
- Concreteness is world-independent; `ConcreteAt o c w x` is existence at
  `w` together with concreteness.
- Paradigm anchors (`Anchors`): the reasoner is concrete and the set
  containing 2 is abstract. `Anchors.not_constant` proves that an anchored
  classification cannot be all-True or all-False.

Aquinas does not use the modern word "concrete". The identification is the
owner's stipulation. It draws on three pinned readings, which state only:

| Claim | Locator | Reading |
|---|---|---|
| `AQUINAS-DE-ENTE-C1-ENS-DUPLICITER` | De ente c.1 [69872] | being as divided by the categories (only "quod aliquid in re ponit") versus being as the truth of propositions (privations "are" only so) |
| `AQUINAS-DE-ENTE-C2-NATURE-DUPLEX-ESSE` | De ente c.2 [69873] | a nature has esse "in singularibus" and "in anima"; universality follows the second |
| `AQUINAS-ST-I-Q85-A1-AD2-MATHEMATICALS-ABSTRACTED` | ST I q.85 a.1 ad 1–2 | numbers are abstracted by the intellect, not abstract "secundum rem"; Plato erred in positing otherwise |

## Rival criteria

These are sibling senses under `DISAMB-CONCRETE-ABSTRACT-CRITERIA`. Each is
typed from its own supplied primitive and none defines the adopted sense. The
sections refer to SEP "Abstract Objects" (pinned as
`SEP-ABSTRACT-OBJECTS-2020-CRITERIA`; cited for navigation, no claim).

| Criterion | Declaration | Why not adopted |
|---|---|---|
| causal efficacy (§3.2) | `CausalCriterionConcrete` | it would make the capacity clause ("only concrete things have causal power") true by definition (invariant 9); the activity clause would need an exercise-to-power bridge |
| spatiotemporal occupation (§3.1) | `SpatiotemporalCriterionConcrete` | it makes immaterial agents (God, angels, souls) non-concrete |
| Frege: neither mental nor physical (§3) | `FregeCriterionAbstract` | mind-dependent abstracta; unclear for a divine intellect |
| abstraction (§6) | none: it needs essence vocabulary | silent on causation and location |

The finite capacity model (`DEF-CAUSAL-CAPACITY-CONCRETE`) and the
world-indexed predicate of `NecessaryIndividual.Quantifiers`
(`DEF-NECESSARY-INDIVIDUAL-CONCRETE`) are model-local senses. They do not fix
the corpus sense.

## Migration of existing uses

- **Generic parameters stay generic.** Most library files take `concrete` as a
  parameter of a generic theorem or profile, for example
  `BruteFoundationBoundary.Profile.concrete`, `Scenario.concrete` and
  `CogitoConcrete`. They keep it: each result holds for every instantiation,
  and frozen Challenges cannot change. Their intended instantiation is now
  the adopted sense. The 13 reaching-root statements that use concreteness
  link `DEF-CONCRETE-ESSE-IN-RE` and `DISAMB-CONCRETE-ABSTRACT-CRITERIA`, and
  `DEF-INHABITED-CONCRETE-WORLD` now says so instead of leaving the criterion
  open (#544).
- **Intended interpretation.** `CausalPowerConcreteness.EsseIntendedProfile`
  extends the #1094 `IntendedProfile`. It ties `concrete`/`abstract` to the
  esse sense and requires the anchors, and its
  `EsseIntendedProfile.concrete_not_constant` proves that concreteness is
  not constant. `IntendedProfile` is unchanged. The #1094 adapters have an
  empty abstract extension, so they cannot be esse-intended profiles; they
  show compatibility with the weaker contract only.
- **World-indexed senses.** `NecessaryIndividual.Quantifiers.ConcreteAt` and
  `EmptyTruthmakerReplies.concrete` take world-indexed predicates. Frozen
  Challenges use them, so their Lean names are kept. The disambiguation
  records them as a different, world-varying sense; the adopted sense is
  their world-constant special case.
- **Constant instantiations.** `corpus.py check` warns about a constant
  `concrete`/`abstract` that has no `category-constant: intended (<reason>)`
  declaration (#1107).
