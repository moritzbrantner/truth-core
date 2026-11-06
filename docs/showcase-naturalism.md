# Showcase: naturalism, spatiotemporality and the caused universe (#1109)

This page applies the defeat-by-consequence method of #1007 to naturalism as a
complete worldview, in the format of `docs/showcase-verificationism.md`.

- **Counted defeats: none.** A defeat counts only if all its premises are
  established (#999). Every consequence-defeat here needs at least one open
  premise.
- **What is proved:** the owner's caused-universe argument refutes each
  ontological variant conditionally: N1, N2, N3 and N3i each entail, with the
  whole-to-part bridge, no self-causation, thesis containment and one
  variant-specific premise (§3 table), that the universe has no existing cause.
- **What survives:** the naturalist escapes (brute universe, infinite regress,
  causal loop) have certified joint models together with every floor item
  listed below.
- **No route effect:** no root-route premise has a naturalist `alternative_to`,
  so route costs do not change (`frontier-diff`, below).

The vocabulary is in `TruthCore/Ontology/Spatiotemporal.lean`,
`TruthCore/Ontology/Naturalism.lean` and
`TruthCore/Ontology/NaturalismConsequences.lean`. The additional mereological
contrasts are in `TruthCore/Ontology/NaturalismContrasts.lean`, with results in
`TruthCore/Results/Ontology/NaturalismContrasts/`; the caused-universe results
remain in `TruthCore/Results/Ontology/Naturalism/`.

- **Axioms:** none. Every result is zero-axiom and constructive.

## 1. Spatiotemporality is its own property

Concrete means having esse in re (#1103). Spatiotemporal is a separate
property with three senses, kept apart in `DISAMB-SPATIOTEMPORAL`:

| Sense | Lean | Meaning |
|---|---|---|
| occupant | `Located F x` | x occupies some region |
| relational | `Related F x` | x stands in a spatiotemporal relation to something |
| part of spacetime | `PartOfSpacetime F x` | x is a part of the spacetime whole, improper parthood allowed |

`SPATIOTEMPORAL-INDEPENDENT-OF-CONCRETE` (premise-free) is a four-candidate
model, anchored with the reasoner concrete and the singleton-set candidate
`{2}` abstract. That anchor is not the number `2` and licenses no universal
claim about all numbers or all pure sets. In the model,
every combination of concrete or abstract with spatiotemporal or not occurs,
in each of the three senses. So no sense follows from concreteness or implies
it.

**Occupation is not presence by power.** Aquinas's God is everywhere "by
power, presence and essence" (ST I q.8 a.3), and an angel is in a place by
applying its power (q.52 a.1). Neither is occupation, so this God is not
`Located`. This is a reading choice recorded in the disambiguation.

### Which combinations each worldview allows

| Worldview | concrete, spatiotemporal | concrete, not spatiotemporal | abstract, not spatiotemporal |
|---|---|---|---|
| Thomist working profile | bodies, composite substances | God, angels, separated souls (`STMT-SOME-CONCRETE-BEING-NOT-SPATIOTEMPORAL`) | numbers/universals with esse only in the intellect on this working reading; historical orientation, attribution deferred, not derived from the `{2}` anchor |
| N1 (Armstrong, as reported) | everything that exists | excluded | excluded from existence |
| N2 | allowed | excluded | allowed |
| N3, spatiotemporal instance (analyst's) | allowed | allowed only if it has no causal power | allowed |
| N3i, spatiotemporal instance (analyst's) | allowed | allowed only if it causes nothing spatiotemporal | allowed |

The last two rows are the analyst's instances of Papineau's schemas with
P = a spatiotemporal sense. They are not Papineau's view. His own theses take
P = physical (`PAPINEAU-RISE-CAUSAL-POWERS-PHYSICAL`,
`PAPINEAU-RISE-INTERACTION-PHYSICAL`) and constrain the physical/nonphysical
divide, not the spatiotemporal one. A causally active being that is physical but
not spatiotemporal is not excluded by them. He also leaves "noncausal realms"
(p.11) open, which matches the third column for P = physical.

The Thomist combination is recorded as `alternative_to` N2.
`Naturalism.concreteNaturalism_excludes` proves that N2 excludes it.

## 2. The worldview at full strength

Each ontological variant is a schema in a **thesis predicate** `P`. This keeps
each proponent's own predicate: a spatiotemporal sense for spatiotemporal
naturalism, "physical" for Papineau.

| Variant | Wording | Record | Typed as |
|---|---|---|---|
| **N1** | Nothing exists apart from spatio-temporal objects. Murphy 2021, pp.53–54, reports that Armstrong held this, citing *Sketch* (2010) p.1. | `MURPHY-2021-ARMSTRONG-NATURALIST` (secondary report) | `ExistenceNaturalism` |
| **N2** | Every existing concrete thing is spatiotemporal. | analyst formulation, attribution deferred | `ConcreteNaturalism` |
| **N3** | "everything with causal powers is physical" (Papineau, *Rise of Physicalism* p.12) | `PAPINEAU-RISE-CAUSAL-POWERS-PHYSICAL` | `CausalPowerNaturalism` |
| **N3i** | "everything that interacts causally with the physical world is physical" (p.11) | `PAPINEAU-RISE-INTERACTION-PHYSICAL` | `InteractionNaturalism` |
| Sellars | "in the dimension of describing and explaining the world, science is the measure of all things" (EPM §41) | `SELLARS-EPM-41-SCIENTIA-MENSURA` | untyped (methodological) |
| Quine | epistemology as "a chapter of psychology" (1969 p.83, via SEP) | `STMT-QUINE-NATURALIZED-EPISTEMOLOGY`, navigation only | untyped (methodological) |

**Fidelity notes.**

- **Armstrong.** *A World of States of Affairs* (1997) and *Sketch* (2010) have
  no pinnable witness. The NDPR review that quotes *Sketch* p.1 refuses
  automated fetches (HTTP 403). N1 is attributed only through Murphy's report.
  Murphy's definition also says that all spatio-temporal objects are
  contingent; the claim drops that conjunct, so it is weaker than the source.
- **Papineau.** He leaves open "noncausal realms" (mathematical objects, value)
  that are not physical, so he is not committed to N1. He also never says that
  physical things are spatiotemporal. The spatiotemporal N3 and N3i (the §1
  table rows and every part-of-spacetime instance below) are the analyst's
  instances of his schemas, not his theses.
- **Sellars.** In the same paragraph Sellars calls the common-sense world of
  objects in Space and Time "unreal". So scientia mensura is not N1: it defers
  ontology to science, whatever science's categories turn out to be.
- **Quine.** He accepted sets as abstract objects, so his naturalism is not N1.

**Strength order (#1017).** `NATURALISM-N1-ENTAILS-N2` backs
`REL-NATURALISM-N1-STRENGTHENS-N2`. The other pairs need bridges:

- N2 gives N3 only with the causal-concreteness floor item.
- N3 and N3i are related only through the exercise-to-power reading.
- Under the owner's #1113 bridge (whatever exists in re is concrete), N1 and N2
  coincide for existents in re.

## 3. Centrepiece: the caused universe (owner argument, 2026-11-06)

> "if we also accept that the universe has a cause, then that cause, which
> causes time to exist, does cause and exist out of time."

The cause is a cause of the **existence** of the spacetime whole (dependence or
conservation, cf. ST I q.104 a.1), not of a temporal beginning. Aquinas holds
that a beginning cannot be demonstrated (q.46 a.2), so nothing here uses the
kalam premise. It is an efficient cause, not a PSR reason
(`DISAMB-PSR-EXPLANATION-CAUSE`).

1. **U** `STMT-UNIVERSE-HAS-EXISTING-CAUSE` (open): the spacetime whole has an
   existing cause c.
2. **C lies outside spacetime.** `UNIVERSE-CAUSE-OUTSIDE-SPACETIME` takes two
   premises:
   - the bridge `STMT-CAUSING-WHOLE-CAUSES-PARTS` (open): causing a whole to
     exist includes causing each of its parts to exist;
   - the sourced `STMT-NOTHING-IS-EFFICIENT-CAUSE-OF-ITSELF` (ST I q.2 a.3).

   If c were a part of spacetime, it would cause itself. U is not even needed
   for this step.
3. **C is concrete**, by the activity clause of the established weak floor
   item `STMT-CAUSAL-POWER-AND-ACTIVITY-REQUIRE-CONCRETENESS` (#1106).
4. **So** something concrete and causal is not part of spacetime. One more
   bridge is needed: the thesis predicate must be contained in spacetime
   (`STMT-THESIS-CONTAINED-IN-SPACETIME`). It is definitional for the
   part-of-spacetime sense and open otherwise. Each variant then fails:

| Result | Extra premise | Refutes |
|---|---|---|
| `CAUSED-UNIVERSE-REFUTES-N1` | none (the cause exists) | N1 |
| `CAUSED-UNIVERSE-REFUTES-N2` | weak causal-concreteness floor item | N2 |
| `CAUSED-UNIVERSE-REFUTES-N3` | exercise-to-power reading `STMT-CAUSING-EXERCISES-POWER` | N3 |
| `CAUSED-UNIVERSE-REFUTES-N3-INTERACTION` | the whole satisfies the thesis `STMT-SPACETIME-WHOLE-SATISFIES-THESIS` | N3i |

Each refutation rests on U, the whole-to-part bridge, no self-causation,
thesis containment and the extra premise in its row. Equivalently, each variant, with the other premises in its refutation
(excluding U), entails that the universe has **no existing cause**: **N ⊢ ¬U**.
This is weaker than `STMT-UNIVERSE-UNCAUSED`, which excludes every causal
edge into the whole. The `Ontic` vocabulary does not require causal endpoints
to exist; even the N2 concreteness floor item supplies concreteness, not
existence. To infer the stronger uncaused-universe position from ¬U would
require an additional causal-endpoint existence premise. The survivor below
separately witnesses that stronger position.

**Status: conditional, not counted.**

- U and the whole-to-part bridge are open.
- `STMT-NOTHING-IS-EFFICIENT-CAUSE-OF-ITSELF` is sourced but not established.
- So the `refutes` relations do not count (#999).

**"Out of time", strong version (#1017).** Read strictly, "C causes time to
exist" yields only that C is not a part of *this* spacetime.
`UNIVERSE-CAUSE-ATEMPORAL` derives the stronger "C is not successively temporal
in any supplied temporal series" with one extra open premise,
`STMT-TEMPORAL-CONTAINED-IN-SPACETIME`: every successive bearer of a supplied
series is a part of this spacetime.

- *Temporal* is `SuccessivelyTemporal` (`DEF-SUCCESSIVELY-TEMPORAL`): present
  at an earlier and a later time of a series, with a change of state. This is
  q.10's successive duration, the negation of Boethian *tota simul*.
- `DISAMB-TEMPORAL-SENSE` settles the cases. A second series with a successive
  bearer outside spacetime falsifies the premise. So does an aevum whose
  adjunct changes are recorded in some supplied series. An aevum with no
  recorded change is not temporal in this sense.
- So the conclusion does not say that C is eternal, and it does not exclude a
  non-successive aeviternal duration.

The strong conclusion is recorded as its own statement,
`STMT-CAUSES-OF-UNIVERSE-ATEMPORAL`.

### The naturalist escapes, at full strength

| Escape | Proponent | Certificate | What it denies |
|---|---|---|---|
| Brute universe | Russell 1948 ("the notion of the world having an explanation is a mistake"; navigation, not pinned here); Oppy, who reports that non-theists deny that the universe has a cause (`REL-OPPY-SUPPORTS-UNIVERSE-UNCAUSED`) | `NATURALIST-UNCAUSED-UNIVERSE-SURVIVOR` | U |
| Infinite regress without an external cause | Hume–Edwards style | same model: an injective chain of proper parts, each caused by the next; every proper part has a cause; the whole has none | U |
| Causal loop | analyst formulation | `CAUSAL-LOOP-REJECTS-BRIDGE`: an existing proper part c causes the whole, and c and a distinct proper part d cause each other | the whole-to-part bridge |

`STMT-UNIVERSE-UNCAUSED` is recorded as `alternative_to` U.

The survivor model jointly satisfies all of the following:

- the anchors (the reasoner exists; the designated singleton-set `{2}`
  candidate does not exist in re);
- the #1113 bridge;
- N1 in all three senses, and N2, N3 and N3i;
- the weak causal-concreteness floor item, the exercise-to-power reading, the
  whole-to-part bridge and no self-causation;
- F3 (something changes), F4 (something is moved) and F6 (some agent has an
  epistemic reason), each borne by a part of spacetime;
- an existing, located spacetime whole that nothing causes;
- an infinite regress: an injective chain of proper parts of spacetime, each
  caused by the next.

So the brute-universe and regress escapes are consistent with every listed
floor item.

The loop model shows the other escape. A naturalist who grants a caused
universe can keep every variant by a causal loop among proper parts: one of
them causes the whole, and the whole-to-part bridge fails. The model does not
show that denying the bridge requires a loop.

**Related records:**

- the Platonic `STMT-COSMOS-HAS-CAUSE` / `STMT-COSMOS-HAS-DISTINCT-CAUSE`
  (a cause of generation, a different sense);
- the PSR records under `DISAMB-PSR-EXPLANATION-CAUSE`;
- Oppy's epistemic objection `STMT-EMPIRICAL-KNOWLEDGE-NO-REASON-UNIVERSE-CAUSED`.

## 4. The other consequences: encoded contrasts and remaining work

The part/simplicity/remoteness contrast and the whole-occupation scope are now
encoded below. Laws, mathematics and the additional logic/epistemic interfaces
remain work of #1109; they are not silently replaced by these narrower tests.

| Consequence | Expected encoding | Expected status |
|---|---|---|
| Laws (Lewis regularity / Armstrong universals / powers) | Still unencoded: separate law-as-description from reified universals/powers and state the exact location criterion. N1 yields instantiation only with a located-universal→instance bridge or definition; an instance→location rule alone does not suffice. | No defeat. Instantiation and Tooley-style uninstantiated-law contrasts need their explicit semantic bridges. |
| Spacetime itself (self-application) | `NATURALISM-WHOLE-OCCUPATION-BOUNDARY`: occupant N1 + "the selected whole occupies no region" ⊢ the selected whole does not exist there. This is a logical transcription/instantiation, not a complete relationalism theorem. The new controls retain both the located existing self-part whole and an unlocated absent whole with another existing located candidate. | No defeat. Located-whole and absent-whole profiles remain distinguished. |
| Logic (F1, excluded middle) | F1 is premise-free in Lean, and excluded middle is about all propositions. Neither constrains the domain, so no consistent variant contradicts them. Murphy 2021 (pinned) offers the naturalist account of necessary truths without truthmakers ("knowledgemaker maximalism"). | No defeat; at most an explanatory burden (D-I). |
| Mathematics (Quine/Putnam vs Field) | Still unencoded: use an actual mathematical set/membership profile and a location→located-member support clause to investigate pure-set unlocation by well-founded induction. A merely positive member→set propagation rule is insufficient. Reification/existence and nominalist representation need separate explicit clauses. The #1113 bridge plus abstract anchor concern the designated `{2}` candidate only, not the number `2`, all numbers or all pure sets. | No defeat or new nominalism certificate in this batch. |
| Epistemic reasons (F6) | Covered by the survivor model: F6 holds with spatiotemporal reasoners. The retorsion bites only if reasons are non-spatiotemporal normative facts, which is open. | No defeat. |
| God contrast | `NATURALISM-PART-REMOTE-SIMPLE-EXCLUSION`: N1 in the part sense + existing proper parts→components + existing proper components→whole composite + two distinct existents ⊢ no existing simple remote-from-all candidate, using the same `Case.RemoteFromAll`/`IsSimple` dictionary. | Conditional necessary-property exclusion, not negation of a naming implication or a counted defeat. No `alternative_to` on the naming leaf and no route change. |


### 4.1 The part-naturalism contrast and its exact bridges

The original expected argument left a dictionary step implicit. The Case API
supplies `ComponentOf` and `Composite` separately. Its existing
`CompositeHasComponentOtherThanItselfReading` says a composite has a component;
it does not license the converse. The new weak, selected-world propositions are:

- `STMT-EXISTING-SPACETIME-PROPER-PARTS-ARE-COMPONENTS`: an **existing** proper
  part of this selected whole is a component of that same whole.
- `STMT-EXISTING-SPACETIME-COMPONENTS-MAKE-WHOLE-COMPOSITE`: an **existing**
  component distinct from this selected whole makes that same whole composite.
- `STMT-TWO-BEINGS-EXIST-AT`: two numerically distinct candidates exist at the
  selected world. This is an explicit premise, not a new floor item.

`NATURALISM-REMOTE-SIMPLE-POPULATION` combines part N1 with the two dictionary
bridges. If a simple remote being exists, there cannot be a distinct pair of
existents. Remoteness excludes the candidate's being a proper part of the
whole. If the whole were composite, candidate simplicity would exclude its
identity with the whole, contradicting that remoteness. A distinct pair then
contradicts the resulting absence of existing proper components. The proof is
constructive: it does not replace double-negated identity by positive equality,
assume excluded middle, or independently assert that the whole exists.

`NATURALISM-PART-REMOTE-SIMPLE-EXCLUSION` composes that checked constraint with
the distinct-pair premise. Its conclusion is exactly
`NoExistingSimpleRemote`: absence of an existing candidate having those two
specified properties under the shared dictionary. The full God-naming premise
runs **from** a fuller description **to** God. Denying conditions in its
antecedent does not refute that implication, nor supply a converse from every
God predicate to the description. Applying the result to an actual God claim
requires the intended same-dictionary characterization and population inputs.
No reverse naming bridge or naturalist rival on the naming leaf is added.
Only the stated N1 instances are tested here. N2 needs its own concreteness
inputs, N3 its causal-power inputs, and N3i its interaction inputs; none is
silently substituted, and physical is not identified with spatiotemporal.

The occupant sibling `NATURALISM-OCCUPANT-REMOTE-SIMPLE-EXCLUSION` reuses
`STMT-THESIS-CONTAINED-IN-SPACETIME` with `P = Located F`. Occupant N1 plus that
explicit containment premise supplies part N1, after which the same checked
exclusion applies. Without containment, occupation and part membership remain
separate; the control below certifies that limit. It is not a physically
faithful counterexample to a location→part criterion that has already been
adopted.

### 4.2 What the populated controls preserve

`NATURALISM-MEREOLOGICAL-CONTRAST-CONTROLS` exports all the properties below;
they are not incidental facts hidden in its implementation:

| Control | Retained properties |
| --- | --- |
| Full background | Part N1, both dictionary bridges and a distinct pair jointly hold; no existing simple remote candidate does. The input bundle is satisfiable. |
| No distinct pair | Both bridges and part N1 hold; an existing, located, self-part whole is simple and remote; occupant N1 also holds. Thus the whole is not declared nonsimple merely by being a whole. |
| No component→composite bridge | Part N1, part→component and the distinct pair hold, with an existing simple remote candidate. The omitted dictionary condition is explicitly false. |
| No part→component bridge | Part N1, component→composite and the distinct pair hold, with an existing simple remote candidate. The omitted condition is explicitly false. |
| No part N1 | Both bridges, the distinct pair and an existing simple remote candidate hold; occupant N1 holds while part N1 is false. Occupation is not silently identified with parthood. |
| Unlocated absent whole | Occupant N1 holds, the whole is unlocated and absent, and a different existing candidate is located. This is a scoped relationalist-style profile, not a complete theory of spacetime. |

The component-without-composition control exposes the **formal API gap**; it is
outside the intended reading of an intrinsic proper composition component, not
a claim that a metaphysically faithful component dictionary has no composition.
The other omissions likewise test exact hypotheses, not complete historical
worldviews. The only-existing-whole profile does not claim compatibility with
all causal, change or epistemic floor commitments; the earlier survivor remains
the authority for its own, different joint floor profile.

The one location region may stand for the whole spacetime region. Locating the
whole there requires no external surrounding space and is distinct from
presence by power. These controls add no source attribution, grounding/causal
principle, geometry, or real-world possibility claim.

## 5. Status summary

| Result | Target | Status |
|---|---|---|
| `SPATIOTEMPORAL-INDEPENDENT-OF-CONCRETE` | separateness of the property | premise-free model |
| `NATURALISM-N1-ENTAILS-N2` | strength order | premise-free; backs `strengthens` |
| `UNIVERSE-CAUSE-OUTSIDE-SPACETIME` | owner step (2) | conditional on the bridge and no self-causation |
| `UNIVERSE-CAUSE-ATEMPORAL` | strong "out of time" | conditional, with one more premise |
| `CAUSED-UNIVERSE-REFUTES-N1/N2/N3/N3-INTERACTION` | N1, N2, N3, N3i | conditional refutations, **not counted** |
| `NATURALIST-UNCAUSED-UNIVERSE-SURVIVOR` | brute and regress escapes | premise-free joint model |
| `CAUSAL-LOOP-REJECTS-BRIDGE` | loop escape | premise-free joint model |
| `NATURALISM-REMOTE-SIMPLE-POPULATION` | part N1 and simple/remoteness dictionary | constructive conditional population constraint |
| `NATURALISM-PART-REMOTE-SIMPLE-EXCLUSION` | existing simple remote candidate | conditional on part N1, both bridges and a distinct pair |
| `NATURALISM-OCCUPANT-REMOTE-SIMPLE-EXCLUSION` | occupant-to-part transport | same exclusion, with explicit existing thesis containment |
| `NATURALISM-WHOLE-OCCUPATION-BOUNDARY` | unlocated whole under occupant N1 | logical transcription/instantiation |
| `NATURALISM-MEREOLOGICAL-CONTRAST-CONTROLS` | populated and omitted-input profiles | explicit scoped model controls |

**What is defeated:** nothing counts.

**What survives:** every variant, through the brute-universe, regress or loop
escape. The cosmological question is thus sharpened to U and the whole-to-part
bridge, but these two are not enough. Each refutation also needs no
self-causation (sourced, not established) and thesis containment (definitional
only for the part-of-spacetime sense). Each variant also needs its own extra
premise:

- N1: none;
- N2: the weak causal-concreteness floor item;
- N3: the exercise-to-power reading;
- N3i: that the whole satisfies the thesis.

Only if all of these were established would all four variants fall.

**Frontier:** no change. Neither U nor the bridge is a root-route premise, and
no route leaf gained a naturalist rival; see the PR's `frontier-diff`.
