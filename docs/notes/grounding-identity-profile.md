# Local grounding data and transworld identity

Analyst reconstruction for #1078; attribution deferred. The question is whether
coherent counterpart matching and preserved local grounding structure establish
one literally identical necessary concrete individual. The basic singleton
counterpart counterexample is already certified by
`STMT-COUNTERPART-NECESSITY-CONTROLS`; repeating it would add little. This result
compares two profiles of the **same nontrivial source** and common roster.

## Reuse and exact source assumptions

The inventory inspected the related statements, context pack, dossier, attempt
and exact modules for `STMT-WORLD-LOCAL-GROUNDING-DOUBLING`, as well as the existing
counterpart controls. The old doubling theorem already copies any source local
structure while excluding rigid necessary concrete existence. No fixed-tag
rigid companion or generic `Ontic`/`Profile` isomorphism transport was found.

The new conditional retains exactly its four source-side assumptions:

1. Some source individual is concrete and exists.
2. The source grounding relation is well-founded.
3. Each source grounding edge has distinct existing endpoints.
4. The independently supplied noninitial predicate has an existing concrete
   predecessor for every existing concrete noninitial source individual.

No necessary-existence premise, unrestricted PSR, universal contingent dependence
or anti-brute-root law is added. `LocalLaws` packages exactly the old conclusion's
worldwise population, well-foundedness, sound distinct endpoints and noninitial
coverage. The proof uses `doublesPopulation`, `doublesWellFounded`,
`doublesGroundSound` and `doublesNoninitialCoverage` unchanged. The rigid-side
laws are the old laws at world false, copied unchanged to every world.

## Common profile and two assignments

Both profiles use the same ordinary Lean individuals `(tag, source coordinate)`,
two Bool worlds with universal accessibility and the same source concreteness
predicate. Worlds are alternative complete interpretations, not times.

| Assignment | Existing tag at world false | Existing tag at world true |
| --- | --- | --- |
| Exact old `doubled s` | false | true |
| New `rigid s` | false | false |

In each case the source existence predicate still filters the second coordinate.
Grounding and Causes edges copy the source relation between the selected tagged
endpoints. The latter two fields inherit their common interpretation from the
old `doubled` fixture: this is not an independent identification of real efficient
causation with existential grounding. Concreteness does not depend on tag.

At actual world false the existence, Causes and grounds assignments are
**literally equal functions**, and both frames and concrete predicates are
literally equal globally. The complete source structure is copied at every
world. Nevertheless, an existing concrete source coordinate b gives the same
rigid individual `(false,b)` at both worlds in the fixed-tag profile; population
therefore directly yields a necessary concrete witness. No necessary witness is
assumed. The exact imported `doubledHasNoNecessary` excludes one in the disjoint
profile because no tagged individual can have both different required tags.

## Guarded correspondence and exact composition

`SameLocalData` proves unique matching in both directions between each world's
**existing domains**, by equal source coordinate. On matched existing endpoints
it preserves concreteness and both represented edge fields. It is a local-fiber
isomorphism for these specified predicates and relations. It is not a global
bijection on the common candidate roster and not a preservation theorem for
arbitrary modal formulas or identity-sensitive cross-world observations.

The counterpart relation uses the existing four-place relation interface:
`counterparts s w x v y` requires x existing at w, y existing at v, and equal
source coordinates. The proof certifies the existing `Total`, `Unique` and
`Injective` predicates, surjectivity onto every target existing domain and
reflexive links for existing bearers. More decisively, for **every** intermediate
world v, not just one accessible witness:

```text
(there exists y with counterparts w x v y and counterparts v y u z)
  iff counterparts w x u z.
```

The forward direction composes source-coordinate equalities and retains the
endpoint guards. The reverse direction constructs `(v,x.source)` and proves its
existence from the already existing source. Thus this is exact composition,
including identity-world links, rather than unconnected serial correspondences.
Counterpart necessity follows for every initially existing source coordinate.
Still, the relation fails the existing `IdentityBridge`: `(false,b)` and
`(true,b)` correspond but are unequal tagged individuals. Population supplies b,
so the failure is not based on an empty source domain.

The source coordinate names a role in the copied local structure. Its equality
is not by itself equality of the whole tagged individual. Treating it as the
latter would assume precisely the bridge at issue. Conversely, a rival can
reject the fixed-tag assignment as an account of real transworld identity.
Neither interpretation is independently vindicated by this comparison.

## Genuine grounding instance and boundaries

The certificate instantiates the exact old `exampleSourceConditions`. The old
`exampleSourceHasLink`, transported with `copiedEdgeIff`, provides the concrete
actual edge from `(false,(false,false))` to `(false,(false,true))` in **both**
profiles. Soundness ensures existing distinct endpoints; the source is not an
empty graph making universal grounding laws vacuous.

The result is a mathematical common-profile comparison. It neither proves
metaphysical possibility nor establishes real identity, counterpart adequacy,
well-foundedness, grounding interpretation, a PSR or an anti-brute-root principle.
Those remain **OPEN**. It does not say every qualitative predicate of any possible
language is preserved: the certified local data are existence, concreteness,
grounding and Causes, with independently stipulated source structure. The
strongest rigid-identity rival and the structurally coherent disjoint rival are
both represented; the theorem does not select either as true.

Intended and actual root-premise change: **none**. The result has no external
Prop premises because its four source assumptions are explicitly quantified
inside the closed certificate. Conditional comparison is progress on the
configuration space, not a discharge of any root obligation.

## Verification

The Challenge was committed at `49d2c0bc`; syntax-only vocabulary corrections
were committed at `8a057aa9`, before Solution work, replacing an unsupported
namespace alias and expanding unique-existence notation without changing its
meaning. The frozen Challenge itself is unchanged.

Focused Solution build, exact binding, Comparator and independent NanoDa pass.
The result permits no axioms. Reproduce after the focused Solution build with
`python3 scripts/worker_env.py -- scripts/verify-result.sh GROUNDING-IDENTITY-PROFILE`
and `python3 scripts/worker_env.py -- python3 scripts/corpus.py bind-check --result GROUNDING-IDENTITY-PROFILE`.
Final CI covers the delivered revision. Shared engineering policy resolved at
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.
