# Showcase: naturalism, spatiotemporality and the caused universe (#1109)

This page applies the defeat-by-consequence method of #1007 to naturalism as a
complete worldview, in the format of `docs/showcase-verificationism.md`.

- **Counted defeats: none.** A defeat counts only if all its premises are
  established (#999). Every consequence-defeat here needs at least one open
  premise.
- **What is proved:** the owner's caused-universe argument refutes each
  ontological variant conditionally: N1, N2, N3 and N3i each entail, with two
  bridges, that the universe has no existing cause.
- **What survives:** the naturalist escapes (brute universe, infinite regress,
  causal loop) have certified joint models together with every floor item
  listed below.
- **No route effect:** no root-route premise has a naturalist `alternative_to`,
  so route costs do not change (`frontier-diff`, below).

The vocabulary is in `TruthCore/Ontology/Spatiotemporal.lean`,
`TruthCore/Ontology/Naturalism.lean` and
`TruthCore/Ontology/NaturalismConsequences.lean`. The results are in
`TruthCore/Results/Ontology/Naturalism/`.

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
model, anchored with the reasoner concrete and the set of 2 abstract. In it,
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
| Thomism | bodies, composite substances | God, angels, separated souls (`STMT-SOME-CONCRETE-BEING-NOT-SPATIOTEMPORAL`) | numbers and universals, with esse only in the intellect |
| N1 (Armstrong, as reported) | everything that exists | excluded | excluded from existence |
| N2 | allowed | excluded | allowed |
| N3 / N3i (Papineau) | allowed | allowed only if causally idle | allowed ("noncausal realms", p.11) |

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
  physical things are spatiotemporal. The spatiotemporal N3 is the analyst's
  instance of his schema.
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

Each refutation rests on U and both bridges. Equivalently, each variant with
the bridges commits its holder to an uncaused universe: **N ⊢ ¬U**.

**Status: conditional, not counted.**

- U and the whole-to-part bridge are open.
- `STMT-NOTHING-IS-EFFICIENT-CAUSE-OF-ITSELF` is sourced but not established.
- So the `refutes` relations do not count (#999).

**"Out of time", strong version (#1017).** Read strictly, "C causes time to
exist" yields only that C is not a part of *this* spacetime.
`UNIVERSE-CAUSE-ATEMPORAL` derives the stronger "C is not temporal at all" with
one extra open premise, `STMT-TEMPORAL-CONTAINED-IN-SPACETIME`: no time outside
this spacetime. An aevum or a second temporal series would falsify it. The
strong conclusion is recorded as its own statement,
`STMT-CAUSES-OF-UNIVERSE-ATEMPORAL`.

### The naturalist escapes, at full strength

| Escape | Proponent | Certificate | What it denies |
|---|---|---|---|
| Brute universe | Russell 1948 ("the notion of the world having an explanation is a mistake"; navigation, not pinned here); Oppy, who reports that non-theists deny that the universe has a cause (`REL-OPPY-SUPPORTS-UNIVERSE-UNCAUSED`) | `NATURALIST-UNCAUSED-UNIVERSE-SURVIVOR` | U |
| Infinite regress without an external cause | Hume–Edwards style | same model: every proper part has a cause, the whole has none | U |
| Causal loop | analyst formulation | `CAUSAL-LOOP-REJECTS-BRIDGE` | the whole-to-part bridge |

`STMT-UNIVERSE-UNCAUSED` is recorded as `alternative_to` U.

The survivor model jointly satisfies all of the following:

- the anchors (the reasoner exists; the set of 2 does not);
- the #1113 bridge;
- N1 in all three senses, and N2, N3 and N3i;
- the weak causal-concreteness floor item, the exercise-to-power reading, the
  whole-to-part bridge and no self-causation;
- F3 (something changes), F4 (something is moved) and F6 (some agent has an
  epistemic reason), each borne by a part of spacetime;
- an existing, located spacetime whole that nothing causes.

So the brute-universe escape is consistent with every listed floor item.

The loop model shows the other escape: a naturalist who grants a caused
universe must deny exactly the whole-to-part bridge.

**Related records:**

- the Platonic `STMT-COSMOS-HAS-CAUSE` / `STMT-COSMOS-HAS-DISTINCT-CAUSE`
  (a cause of generation, a different sense);
- the PSR records under `DISAMB-PSR-EXPLANATION-CAUSE`;
- Oppy's epistemic objection `STMT-EMPIRICAL-KNOWLEDGE-NO-REASON-UNIVERSE-CAUSED`.

## 4. The other consequences: status

These are not yet encoded. They are the remaining work of #1109, recorded here
so that nothing is lost.

| Consequence | Expected encoding | Expected status |
|---|---|---|
| Laws (Lewis regularity / Armstrong universals / powers) | A derived-location rule: an immanent universal or power is located where an instance or bearer is. Under N1 (occupant sense) every existing universal, including a law N(F,G), is instantiated (Armstrong's instantiation principle). Lewis laws are not entities, so they are no constraint. | No defeat. Tooley-style uninstantiated laws bite only with an open premise. |
| Spacetime itself (self-application) | N1 + "the whole occupies no region" ⊢ the whole does not exist (relationalism forced). The survivor model already certifies the supersubstantivalist escape: the whole exists, is located and is an improper part of itself. | No defeat. |
| Logic (F1, excluded middle) | F1 is premise-free in Lean, and excluded middle is about all propositions. Neither constrains the domain, so no consistent variant contradicts them. Murphy 2021 (pinned) offers the naturalist account of necessary truths without truthmakers ("knowledgemaker maximalism"). | No defeat; at most an explanatory burden (D-I). |
| Mathematics (Quine/Putnam vs Field) | With location by members, every hereditarily pure set is unlocated (induction on membership), so N1 (occupant sense) ⊢ no pure set exists, against indispensability realism. Field's nominalism is the consistent escape. Under the owner's #1113 bridge and the anchor "{2} is abstract", the number does not exist in re for the Thomist either. | No defeat. Thomism and Field agree that numbers lack esse in re. |
| Epistemic reasons (F6) | Covered by the survivor model: F6 holds with spatiotemporal reasoners. The retorsion bites only if reasons are non-spatiotemporal normative facts, which is open. | No defeat. |
| God | N1 (part sense) + "proper parts of spacetime are components" + a second existent ⊢ no existent is both remote from all (`Case.Catholicism.RemoteFromAll`, the God-naming leaf's clause) and simple. So under N1 the God of the naming leaf does not exist, unless God is the whole, which is not simple. | A rival to the existence of what the leaf describes, not to the naming leaf itself. Hence no `alternative_to` on the leaf and no cost change. |

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

**What is defeated:** nothing counts.

**What survives:** every variant, through the brute-universe, regress or loop
escape. The cosmological question is thus sharpened to two open premises, U
and the whole-to-part bridge. If both were established, all four variants
would fall together.

**Frontier:** no change. Neither U nor the bridge is a root-route premise, and
no route leaf gained a naturalist rival; see the PR's `frontier-diff`.
