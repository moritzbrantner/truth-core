# Modal ontology: 120 propositions for the epistemic frontier

This is the complete 2026-10-26 **research inventory**, organized as twelve groups of ten. The `IMP-01`–`EPI-10` identifiers are stable **intake identifiers**, not replacements for canonical `STMT-…` IDs. The wording is preserved from the original proposal; identifying a proposition does not assert that it is true, source-grounded, metaphysically possible, or Lean-verified.

The original **F** and **H** markers are retained as triage labels: F marks an intended formal/semantic test; H marks a substantive philosophical hypothesis. **Neither means proved.** In particular, F entries that mention models are claims *about stated formal semantics* and still need a matching Lean theorem/countermodel before being treated as established. H entries may contradict each other; retain these as rival hypotheses until investigated. An item whose meaning overlaps an existing `STMT-…` must **reuse or link** that identity after a meaning audit, not create a duplicate statement just to make a new dot. A statement becomes a canonical corpus node only with a meaning-checked registration; a source attribution additionally requires a materialized passage witness.

This inventory gives the workloop an exhaustive **enumeration of the proposed questions**, not an exhaustive disjunction of metaphysical theories. Lean can establish consequences and exhibit countermodels relative to explicit assumptions; no unexamined combination is declared impossible or classified as leading to God. The [configuration elimination and composition loop](configuration-elimination-loop.md) governs the next stage: intake ID → meaning-audited canonical `STMT-…` → explicit semantic profile → proof, model, or recorded unresolved attempt. The research matrix is [#461](https://github.com/moritzbrantner/truth-core/issues/461), linked to existing issues #435–#441 and targeted follow-ups #462–#471. No root-path premise is discharged by recording these items.

## IMP — Impossibility and essence

- **IMP-01 (F)** — An entity whose essential properties jointly entail a contradiction cannot be instantiated under classical logic.
- **IMP-02 (F)** — Adding further propositions to an inconsistent set cannot restore consistency unless an existing proposition or inference rule is revised.
- **IMP-03 (F)** — Describing an impossible entity as *possible* does not eliminate the contradiction constituting its impossibility.
- **IMP-04 (F)** — Resolving a contradiction by altering an essential property changes the original conception being investigated.
- **IMP-05 (F)** — A single conception can contain multiple independent, minimal sets of contradictory properties.
- **IMP-06 (F)** — An inconsistent essence has no classical model satisfying all its essential properties.
- **IMP-07 (F)** — Logical impossibility, physical impossibility, and metaphysical impossibility need not have identical extensions.
- **IMP-08 (F)** — The absence of a discovered contradiction does not logically establish the absence of every contradiction.
- **IMP-09 (F)** — An impossibility proof can depend on substantive necessary truths in addition to purely logical laws.
- **IMP-10 (H)** — Every metaphysical impossibility ultimately derives from an incompatibility among essences or other necessary truths.

## MOD — Modal semantics and possible worlds

- **MOD-01 (F)** — Under standard modal semantics, possibility is equivalent to the negation of necessity of negation: \(\Diamond P\leftrightarrow\neg\Box\neg P\).
- **MOD-02 (F)** — The modal systems K, T, S4, B, and S5 permit different classes of accessibility structures.
- **MOD-03 (F)** — In the standard equivalence-frame interpretation of S5, accessibility is reflexive, symmetric, and transitive.
- **MOD-04 (F)** — Every equivalence class of an S5 accessibility graph forms a strongly connected component.
- **MOD-05 (F)** — An isolated empty world in an S5 frame satisfies the necessity of emptiness relative to its own singleton component.
- **MOD-06 (F)** — A world outside the actual world's accessible component is not a possible alternative relative to the actual world under that accessibility interpretation.
- **MOD-07 (H)** — Absolute metaphysical possibility is appropriately represented by one unrestricted S5 accessibility component.
- **MOD-08 (F)** — Modal accessibility does not, by itself, define temporal succession or a mechanism for moving between worlds.
- **MOD-09 (F)** — The validity of nested modal inferences can change when accessibility assumptions change.
- **MOD-10 (H)** — A complete, consistent collection of propositions is sufficient to represent a genuine metaphysical possibility, rather than merely a syntactically coherent candidate.

## NEC — Necessary individuals

- **NEC-01 (F)** — Necessarily having at least one existent individual does not entail the necessary existence of a particular individual.
- **NEC-02 (F)** — The contingency of every individual does not entail the possibility of a world containing no individuals.
- **NEC-03 (F)** — If a particular concrete entity necessarily exists and necessarily remains concrete, every possible world contains something concrete.
- **NEC-04 (F)** — Necessary existence alone does not entail necessary concreteness.
- **NEC-05 (F)** — A necessarily existing being can possess properties that differ between possible worlds.
- **NEC-06 (F)** — Necessary existence does not logically entail temporal eternity, timelessness, or immutability without additional assumptions.
- **NEC-07 (F)** — Necessary existence alone does not entail causal efficacy.
- **NEC-08 (F)** — Having causal powers does not entail necessary existence.
- **NEC-09 (F)** — A simple formal model can consistently describe an individual that exists concretely in every world and exercises causal powers.
- **NEC-10 (H)** — At least one concrete, causally efficacious being exists necessarily in metaphysical reality.

## EMP — Empty worlds

- **EMP-01 (F)** — A world without concrete entities is not necessarily a world without true propositions.
- **EMP-02 (F)** — A world that is empty throughout its history is distinct from a world containing an empty temporal state.
- **EMP-03 (F)** — A modal model can contain both an empty world and a populated world without contradiction.
- **EMP-04 (F)** — Having no concrete entities is distinct from having no entities whatsoever.
- **EMP-05 (F)** — The necessity of some concrete existence is incompatible with the possibility of a completely concrete-empty world.
- **EMP-06 (F)** — The existence of a necessarily concrete entity excludes a completely concrete-empty possible world.
- **EMP-07 (F)** — The possibility of removing each individual entity separately does not establish the possibility of removing all entities simultaneously.
- **EMP-08 (F)** — Every individual being contingent is consistent with every possible world containing at least one individual.
- **EMP-09 (F)** — A subtraction argument requires assumptions about the preservation of possibility under repeated removals.
- **EMP-10 (H)** — A world entirely devoid of concrete entities is metaphysically possible.

## STA — Empty states and transitions

- **STA-01 (F)** — An empty temporal state contains no concrete entity capable of exercising causal power.
- **STA-02 (F)** — An empty temporal state does not imply an empty world if concrete entities exist at other times.
- **STA-03 (F)** — If the past interval is entirely empty, a first concrete event cannot have a concrete cause located within that interval.
- **STA-04 (F)** — A model allowing uncaused events can represent concrete existence beginning after an empty interval without logical inconsistency.
- **STA-05 (F)** — A first event following an empty past is incompatible with the principle that every concrete event requires an earlier concrete cause.
- **STA-06 (F)** — The possibility of an event in another world does not itself provide a causal mechanism for producing that event in this world.
- **STA-07 (F)** — If the empty state is absorbing under a system's transition laws, no nonempty state is reachable from it.
- **STA-08 (F)** — A dynamical system with an appropriate source term can evolve from an empty state into a nonempty state; the mathematical model alone does not establish metaphysical possibility.
- **STA-09 (H)** — Time cannot exist without change, events, or concrete entities.
- **STA-10 (H)** — The beginning of concrete existence can be explained by an atemporal cause or metaphysical ground.

## TIM — Time and temporal beginnings

- **TIM-01 (F)** — A finite temporal duration does not entail the existence of a first instant.
- **TIM-02 (F)** — The existence of a first instant does not entail the existence of a first concrete event.
- **TIM-03 (F)** — The existence of a first event does not entail that time itself has a beginning.
- **TIM-04 (F)** — Infinitely many temporal instants do not entail infinitely many concrete events.
- **TIM-05 (F)** — Infinitely many distinct events can be assigned to a bounded temporal interval in a mathematical model.
- **TIM-06 (F)** — Temporal precedence and causal precedence are distinct relations; neither is formally identical to the other.
- **TIM-07 (F)** — A finite temporal past does not, by itself, entail finite causal ancestry.
- **TIM-08 (H)** — Temporal passage involves objective becoming, rather than merely relations between events.
- **TIM-09 (H)** — Every temporal event can be understood within an eternalist ontology without objective becoming.
- **TIM-10 (F)** — Branching-time semantics can represent histories sharing a common past while allowing different future continuations.

## CAU — Causal graph structure

- **CAU-01 (F)** — Every nonempty finite directed acyclic graph contains at least one vertex with no incoming edge.
- **CAU-02 (F)** — An infinite directed acyclic graph need not contain any vertex with no incoming edge.
- **CAU-03 (F)** — Weak connectivity of a causal graph does not imply the existence of a first cause.
- **CAU-04 (F)** — Strongly connected components identify causal cycles in a graph but do not, without further interpretation, establish temporal loops.
- **CAU-05 (F)** — A nonempty well-founded causal ordering contains a causally minimal element.
- **CAU-06 (F)** — Acyclicity alone does not entail well-foundedness.
- **CAU-07 (F)** — Having finitely many immediate causes does not entail having finitely many causal ancestors.
- **CAU-08 (F)** — The absence of infinite backward causal chains does not entail that every event has finitely many distinct causal ancestors.
- **CAU-09 (F)** — A causal network may have infinite ancestry even when every event lies within a bounded temporal interval.
- **CAU-10 (H)** — No concrete event can possess an infinite causal ancestry.

## INF — Infinity and supertasks

- **INF-01 (F)** — An infinite series can converge to a finite mathematical value.
- **INF-02 (F)** — A divergent series need not possess a finite sum under ordinary real-series convergence.
- **INF-03 (F)** — An infinite sequence of distinct actions can be scheduled within a finite interval in an idealized mathematical model.
- **INF-04 (F)** — An infinite sequence indexed by \(\omega\) and one with reverse order type \(\omega^*\) have different ordering properties, relevant to beginningless histories and supertasks.
- **INF-05 (F)** — A binary state alternating indefinitely between zero and one does not converge to either state.
- **INF-06 (F)** — Some infinite sequences of states converge to uniquely determined limiting states.
- **INF-07 (F)** — A sequence of actions indexed by the natural numbers has no final action.
- **INF-08 (F)** — The actions of a supertask do not always determine its endpoint state without additional rules governing the limit.
- **INF-09 (F)** — The inconsistency of a particular infinite-action specification does not logically entail the inconsistency of every infinite-action specification.
- **INF-10 (H)** — Every physically or metaphysically realizable supertask must satisfy restrictions stronger than mathematical consistency.

## ACT — Actuality and causal powers

- **ACT-01 (F)** — Modal accessibility in ordinary Kripke semantics does not itself constitute a causal power.
- **ACT-02 (F)** — If every causal power belongs to a concrete entity, an entirely concrete-empty state contains no bearer of causal power.
- **ACT-03 (H)** — Every genuine causal power must have an actually existing bearer or foundation.
- **ACT-04 (H)** — An abstract law, considered independently of any concrete reality, cannot actualize concrete entities.
- **ACT-05 (H)** — Objective metaphysical possibilities are grounded in the potentialities of actual entities.
- **ACT-06 (H)** — Objective metaphysical possibilities can be grounded in essences independently of actual causal powers.
- **ACT-07 (H)** — Modal possibility is metaphysically primitive and need not be grounded in something more fundamental.
- **ACT-08 (H)** — A causal power can exist without being exercised.
- **ACT-09 (F)** — Necessary existence is formally compatible with the contingent exercise of causal powers.
- **ACT-10 (H)** — A metaphysical ground can explain the existence of something without temporally preceding it.

## EXP — Explanation and sufficient reason

- **EXP-01 (H)** — Every contingent concrete fact has a sufficient explanation.
- **EXP-02 (H)** — Every fact about existence, including necessary existence, is eligible for explanation.
- **EXP-03 (H)** — The existence of a necessary being can be explained through its essence without requiring a distinct external cause.
- **EXP-04 (H)** — Metaphysical explanations need not be causal explanations.
- **EXP-05 (F)** — Explaining each member of a collection does not, as a matter of logic alone, establish an explanation of the collection as a whole.
- **EXP-06 (F)** — An infinite dependency structure can provide every dependent element with a predecessor without possessing a foundational element.
- **EXP-07 (H)** — Every chain of metaphysical grounding must ultimately terminate in something ungrounded.
- **EXP-08 (H)** — A totality whose members possess only borrowed causal power cannot have sufficient explanatory power without a nonborrowed foundation.
- **EXP-09 (F)** — The impossibility of observing an observerless world does not establish the impossibility of such a world or explain why concrete reality exists.
- **EXP-10 (H)** — Certain strengthened formulations of the unrestricted PSR, combined with additional necessity principles, entail modal collapse.

## ONT — Ontological arguments and ultimate reality

- **ONT-01 (F)** — If \(G\) is possible and essential existence entails necessary existence, then \(G\) exists necessarily in S5.
- **ONT-02 (F)** — Under the stipulated necessity condition in S5, either \(G\) is necessary or \(G\) is impossible; contingent existence is excluded.
- **ONT-03 (F)** — Under the same conditions, if God's nonexistence is possible, God's nonexistence is necessary.
- **ONT-04 (F)** — Under these conditions, \(\Diamond G\) and \(\Diamond\neg G\) cannot both hold.
- **ONT-05 (F)** — Not having established God's impossibility is epistemically different from establishing God's metaphysical possibility.
- **ONT-06 (F)** — Necessarily existing concrete reality does not logically entail a particular necessarily existing concrete being.
- **ONT-07 (F)** — A necessarily existing concrete being excludes completely concrete-empty possible worlds.
- **ONT-08 (F)** — Necessary existence and concreteness alone do not entail omniscience, omnipotence, perfect goodness, or divine simplicity.
- **ONT-09 (H)** — Independent truths about essence, existence, and dependence can justify one side of the modal ontological argument's possibility dispute over the other.
- **ONT-10 (H)** — There exists exactly one ultimately foundational necessary concrete being from which contingent reality derives its existence.

## EPI — Epistemic and formal proof limits

- **EPI-01 (F)** — Failure to discover a contradiction does not entail metaphysical possibility.
- **EPI-02 (F)** — The existence of a formal model establishes satisfiability relative to its axioms and semantics, not automatically genuine metaphysical possibility.
- **EPI-03 (F)** — An unsuccessful proof attempt does not constitute a disproof.
- **EPI-04 (H)** — Conceivability is a reliable guide to metaphysical possibility under appropriately specified conditions.
- **EPI-05 (H)** — Inconceivability can provide reliable evidence of impossibility under appropriately specified conditions.
- **EPI-06 (F)** — Refuting an argument for a conclusion does not establish the negation of that conclusion.
- **EPI-07 (F)** — A countermodel refutes a proposed logical consequence relative to the formal assumptions under which the countermodel is valid.
- **EPI-08 (F)** — A formal proof's conclusion remains conditional on its definitions, axioms, and inferential rules.
- **EPI-09 (F)** — Mutually implying propositions form equivalence clusters in an implication graph, but their circular derivability does not by itself provide independent justification.
- **EPI-10 (H)** — Multiple genuinely independent explanatory and deductive arguments can establish stronger epistemic support for a metaphysical conclusion than any one argument alone.

## Precision audit before formalization

The original wording above is immutable **intake**, including where it is imprecise. A proof worker must not silently reinterpret it as an already-established theorem:

- **CAU-04** needs a nontrivial SCC or an actual self-loop for the stated cycle intuition: an isolated singleton is a strongly connected component under the usual zero-length-path convention but has no directed cycle.
- **CAU-05** needs the orientation of the well-founded relation fixed before translating 'minimal' into 'no incoming causal edge'.
- **MOD-05** asserts necessity **only relative to** its singleton accessibility component, not in all possible worlds across other components.
- **NEC-09 / ACT-09** must keep potential causal capacity, manifested event and actual exercise separate; a finite model is not evidence of metaphysical instantiation.
- **ONT-01–ONT-04** depend on a precise essential-necessity condition, the S5 frame and what the proposition `G` denotes; the possibility premise is still an independently open metaphysical question.
- **INF-03 / INF-08** separate scheduling an infinite sequence mathematically from establishing that infinitely many physical actions can occur and that an endpoint state is well-defined.

Keep the intake text intact while assigning any corrected reading its own meaning-audited canonical statement, linked as a refinement rather than pretending the original proposition was already proved.

## Research routes and next intake step

| Inventory groups | Existing work to reuse | Focused follow-ups |
| --- | --- | --- |
| IMP, MOD, ONT | #261–#267, #274, #437–#439 | #464, #471 |
| NEC, EMP, STA | #435–#436, merged #445/#456 | #462–#463, #466, #470 |
| TIM, CAU, INF | #318, #336–#339, #367, #440–#441 | #469 |
| ACT, EXP | #310–#312, #319–#320 | #462–#463, #465, #468 |
| EPI | #248, #342, #437–#438, #414 | #467, #471 |

Per entry, first search `corpus/statements/` and Lean for the **same meaning**. Link an existing statement where applicable, otherwise formulate a new canonical statement only after its semantics are fixed; then prove, exhibit a countermodel, or document a clearly open metaphysical premise. Source-derived claims require pinned and materialized witnesses. This preserves all 120 proposals while avoiding 120 potentially duplicate or unjustifiably 'proved' propositions.
