# Alternatives campaign (#387)

Closure rule (c) (`docs/corpus-model.md`) closes an open premise when **every** recorded alternative is refuted, and at least one is recorded. Before this campaign the rule had closed nothing. The campaign records, for every open premise on a root path, the strongest rivals actually held in the literature, classifies how each could be refuted, and refutes in Lean where that is cheap and honest. Owner decisions on #387: no `self_evident` markings; strongest real rivals only, no strawmen; rivals that need copyrighted sources wait for bibliographic citations (#378) as candidates, with the statement and the classification recorded now.

Classes, as in the issue: **self-application** (the rival undermines itself), **countermodel/inconsistency** (the rival is inconsistent with itself or with other results), **derivation** (the premise can be derived instead), **evidential/abductive** (a comparison of explanations), **not yet attackable** (the note says what is missing).

## Policy for `refutes` relations

`corpus.py frontier` counts a `refutes` relation only when its argument has a verified result and is premise-free or all its premises are closed (#391/#411). Conditional refutations resting on open premises do not close a defended premise. This campaign first recorded them only in the `alternative_to` note and here as "refuted given open premises …". Conditional refutations now also carry a `refutes` relation, which `frontier --json` lists with `counted: false` and its unestablished premises until those are established (#999); the relation records which premises the rival must reject and closes nothing.

Two further rules apply to conditional refutations here. The refuting argument must not use the premise it defends. And where the strongest form of a rival denies a premise of the refutation, that form is recorded as its own alternative and counted as unrefuted. Example: Aristotle's retorsion refutes the bare Eleatic thesis given "opinion is a motion"; the McTaggart-style rival grants appearances and denies that an appearance of change is a change, so it is a separate alternative, although it formally entails the Eleatic one.

Self-application rivals in later batches should use the retorsion schema of `TruthCore/Logic/SelfApplication.lean` (merged in PR #403); the Eleatic retorsion here predates it and is a direct proof in the prima via vocabulary.

## Historical batch-1 counts

These counts and route costs are the original campaign baseline, not current
coverage evidence. The dated assessment below uses current main.

After this batch, `frontier --reaching-root` lists 39 open premises
(2 bare, 37 sourced but undefended): 8 have recorded alternatives and
31 have none. No premise closes by refuting all alternatives. The campaign
changes no open-premise ID or route cost relative to current main. The two
classification tables below retain the original 37-premise baseline. Since
bridge batch 1 (#405), four current leaves are outside that baseline and
still need classification: `STMT-POTENCY-IS-UNACTUALIZED-CAPACITY`,
`STMT-BEING-MOVED-IS-ACTUALIZATION-OF-POTENCY`, `STMT-PILOT-JESUS-CLAIMS`
and `STMT-PILOT-ROSE`. Two formerly classified premises are now reached
through those bridges.

Current `frontier --routes` costs count distinct open leaves reached through
verified derivations, rather than only each route's direct hypotheses:

| Route | Distinct open leaves |
|---|---|
| `CATHOLICISM-SKELETON` | 28 |
| `CATHOLICISM-FROM-QUARTA-VIA-WITH-CLASSICAL-ATTRIBUTES` | 29 |
| `CATHOLICISM-FROM-PRIMA-VIA` | 33 |
| `CATHOLICISM-FROM-PRIMA-VIA-VIA-FULL-DESCRIPTION` | 35 |
| `CATHOLICISM-FROM-PRIMA-VIA-VIA-MAXIME-ENS` | 36 |
| `CATHOLICISM-FROM-PRIMA-VIA-WITH-CLASSICAL-ATTRIBUTES` | 36 |
| `CATHOLICISM-FROM-EFFICIENT-REGRESS-WITH-CLASSICAL-ATTRIBUTES` | 37 |
| `CATHOLICISM-FROM-PRIMA-VIA-WITH-Q11-UNIQUENESS` | 38 |

## Batch 1: act/potency and causal regress

Three conditional refutations, each with Challenge/Solution, a Comparator config permitting no axioms, and countermodels showing every premise needed (`TruthCore/Results/Alternatives/`; rival vocabulary in `TruthCore/Alternatives/ActPotencyRegress.lean`):

- `ELEATIC-THESIS-SELF-REFUTING` (self-application): Aristotle, *Physics* VIII.3, 254a24-30. If someone opines that nothing is moved, and opining is a being moved, the thesis is false. Refutes `STMT-ELEATIC-NOTHING-IS-MOVED` given open premises, above all `STMT-OPINION-IS-A-MOTION`, which Aristotle states as a reputable opinion (δοκοῦσιν).
- `MEGARIAN-THESIS-ABOLISHES-MOTION` (inconsistency): *Metaphysics* IX.3, 1046b29-1047a17. Something is moved; what is moved toward r is able to be r (1047a11-14) and not yet r (*Physics* III.2, 201b31-33); so something is able without acting. Refutes `STMT-MEGARIAN-ABILITY-ONLY-WHEN-ACTING` given those open premises, without using the premise it rivals.
- `PER-SE-CAUSAL-LOOP-IMPOSSIBLE` (inconsistency): the Second Way's *sic esset prius seipso*, extended to finite loops by induction on the chain. Refutes `STMT-PER-SE-CAUSAL-LOOP` given open premises, one of which, `STMT-SIMPLE-PRIORITY-IS-TRANSITIVE`, is not yet sourced.

`ELEATIC-THESIS-SELF-REFUTING` and `PER-SE-CAUSAL-LOOP-IMPOSSIBLE` now carry non-counting `refutes` relations (rival refutations round 2); `MEGARIAN-THESIS-ABOLISHES-MOTION` does not, since its rival is recorded by an `attacks` relation, not as an `alternative_to`. Even with them, no premise would close: every premise in the batch keeps at least one rival that is unrefuted even conditionally.

<!-- BEGIN GENERATED: docs/alternatives/premises table "premise=Premise" "rival=Strongest rival(s) recorded" "class=Class" "status=Status" filter:phase=batch-1 -->
| Premise | Strongest rival(s) recorded | Class | Status |
|---|---|---|---|
| `STMT-ACT-SIMPLY-PRIOR-TO-POTENCY` | `STMT-POTENCY-PRIOR-TO-ACT` (*Met.* XII.6, 1071b22-28: the reputable view; theologians from Night); its sourced bundle `STMT-NIGHT-UNPRECEDED-POTENCY-ACTUALIZED` (the unpreceded potency is actualized) | inconsistency, partial: Aristotle's reply covers only potencies being actualized (#352, finding 4) | open; sourced; Night bundle eliminated given open {`STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-BEING-IN-ACT`, `STMT-NOTHING-MOVES-ITSELF-IN-SAME-RESPECT`, `STMT-ACTUAL-MOVER-IS-SIMPLY-PRIOR`} (`GENERATION-FROM-NIGHT-REFUTED`, #497); the bare rival survives as an unpreceded potency never actualized |
| `STMT-ACTUALITY-ONLY-INSOFAR-AS-BEING` | `STMT-ACTUALITY-WITHOUT-BEING` (Meinong, Sosein without Sein) | naive form: inconsistency (Russell); nuclear form: not yet attackable | open; witness waiting (`MEINONG-GEGENSTANDSTHEORIE-3`); elimination failed: the rival is the premise's contradictory, so every refuting core entails it, and among the tested act/potency premises the only minimal core is the premise itself (`ACTUALITY-WITHOUT-BEING-NOT-ELIMINATED`, #497) |
| `STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES` | `STMT-INFINITE-PER-SE-CAUSE-SERIES` (infinitism about ground); `STMT-PER-SE-CAUSAL-LOOP` (coherentism) | infinite series: not yet attackable, consistent by `INFINITE-LOCAL-TRANSMISSION-MODEL` (ACT-GROUND, #310; causal finitism, #367); loop: inconsistency, refuted given open premises | open; both witnesses waiting (#378). *Met.* II.2 (`ARIST-MET-II-2`) is the Aristotelian source still to read for the premise |
| `STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT` | `STMT-ACT-AND-POTENCY-IN-SAME-RESPECT` (Scotus, self-motion by virtual act and formal potency) | not yet attackable: turns on `DISAMB-IN-ACT` | open; Scotus witness waiting (`SCOTUS-QQ-METAPH-IX-Q14`) |
| `STMT-NOTHING-MOVED-EXCEPT-AS-IN-POTENCY` | `STMT-MEGARIAN-ABILITY-ONLY-WHEN-ACTING` (*Met.* IX.3); `STMT-MOVED-WITHOUT-POTENCY` (Ash'arite re-creation) | Megarian: inconsistency, refuted given open premises; Ash'arite: not yet attackable (re-creation as change) | open (Ash'arite unrefuted); al-Ghazali witness waiting |
| `STMT-NOTHING-MOVES-EXCEPT-AS-IN-ACT` | `STMT-CAUSE-MOVES-WITHOUT-BEING-IN-ACT` (emergentism) | not yet attackable: bites only on the formal reading of act | open; witness waiting (Broad 1925, #378) |
| `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER` | `STMT-INERTIAL-UNIFORM-MOTION-WITHOUT-MOVER` (unattributed; motivated by Newton's first law, sourced as the conditional `STMT-NEWTON-LEX-I-CHANGE-OF-STATE-ONLY-BY-IMPRESSED-FORCE`, which asserts no force-free body); `STMT-CHANGE-WITHOUT-ANY-MOVER` (quantum indeterminism) | not yet attackable: uniform motion as state versus reduction; moving versus determining (`DISAMB-MOTION`) | open; rival unattributed (Newton's conditional law sourced, Latin 1687), Born waiting (#378) |
| `STMT-PER-SE-MOVER-LINK-IS-PER-SE-CAUSE-LINK` | `STMT-OCCASIONALIST-MOVER-LINK-WITHOUT-CAUSE` (Malebranche, al-Ghazali) | self-application candidate: SCG III.69 (knowledge of natures from effects) | open; witnesses waiting |
| `STMT-SECOND-MOVERS-MOVE-ONLY-AS-MOVED` | `STMT-MOVED-MOVER-MOVES-NOT-AS-MOVED` (a mover moved in an irrelevant respect) | not yet attackable: it bears on the fidelity of the strong reading; the reply is the weaker sibling reading | open; supported by ST I q.46 a.2 ad 7 reading B |
| `STMT-SOMETHING-IS-MOVED-IN-THIS-WORLD` | `STMT-ELEATIC-NOTHING-IS-MOVED` (*Phys.* VIII.3); `STMT-CHANGE-UNREAL-BUT-APPEARS` (unattributed McTaggart-style rival: McTaggart's sourced thesis `STMT-MCTAGGART-NO-A-SERIES-CHANGE-BUT-APPEARS` denies A-series change and reaches this premise only through the open bridge `STMT-BEING-MOVED-INVOLVES-A-SERIES-CHANGE`, `DISAMB-CHANGE-A-SERIES`) | Eleatic: self-application, refuted given open premises; McTaggart: denies the retorsion's premise | open; Eleatic sourced, McTaggart thesis sourced, bridge open; McTaggart's sourced bundle eliminated given open {`STMT-OPINION-IS-A-MOTION`, `STMT-MOTION-IS-A-CHANGE`} (`MCTAGGART-UNREALITY-OF-TIME-REFUTED`, #497). Diodorus Cronus ("nothing is moving, things have moved"; Sextus, *M.* X) to source |
<!-- END GENERATED -->

Rejected options, with reasons:

- **Megarians as the rival of non-simultaneity.** Stated with the Θ.6 primitive `CanBe`, the Megarian thesis does not contradict `STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT`; it contradicts motion through potency. Stated with `InPotency` it would use "potency" in a sense other than `DEF-POTENCY` (unactualized ability), an equivocation. It is therefore recorded against `STMT-NOTHING-MOVED-EXCEPT-AS-IN-POTENCY`.
- **Refuting non-simultaneity's rivals from non-simultaneity.** Self-motion contradicts the three prima via act/potency premises together; using any of them to refute it would be circular.
- **Hume, *Treatise* I.3.3, as a rival of the mover premise.** On the pinned narrow reading (`HUME-TREATISE-I-3-3-NARROW-A`) Hume denies only that the causal maxim is intuitively or demonstratively certain; that is not inconsistent with the premise, so it is not recorded as an alternative.
- **Hume, *Dialogues* IX, against the per se regress.** Its chain is a temporal succession (per accidens), not a per se series; it belongs with the explanatory track (#311).
- **Lewis 1976 bootstrap loops as the per se loop rival.** They are temporal and per accidens; the per se loop rival is coherentism about ground.

## Remaining root-path premises: first-pass classification

Not yet recorded as relations. Each row names the strongest rival known to the campaign and what refuting it would take; "to source" means no witness is pinned yet.

<!-- BEGIN GENERATED: docs/alternatives/premises table "premise=Premise" "rival=Strongest rival" "class=Class (first pass)" "notes=Notes" filter:phase=remaining -->
| Premise | Strongest rival | Class (first pass) | Notes |
|---|---|---|---|
| `STMT-AS-TO-BEING-SO-TO-TRUTH` | truth belongs only to propositions (deflationism; Frege) | not yet attackable: needs a disambiguation of transcendental and propositional truth | to source |
| `STMT-BRIDGE-CHRISTS-CHURCH-FOUNDED-BY-GOD` | the founded society is human, only the invisible Church is divine (Reformed ecclesiology) | evidential/abductive | bare premise |
| `STMT-BRIDGE-GOD-FOUNDED-AUTHORITY-PROPOSES-ONLY-TRUTH` | a divinely founded authority can err (Westminster Confession 31.4; Luther) | evidential/abductive | to source |
| `STMT-CATHOLIC-CHURCH-DEFINITIVELY-PROPOSES-CREED` | the Latin Church proposes an interpolated creed (Orthodox objection to the Filioque) | evidential | candidate `CREED-C381-FILIOQUE` |
| `STMT-CAUSE-OF-BEING-CAUSES-EVERY-PERFECTION` | existential conservation without primary causal responsibility for each particular actuality | shared-background rival witnessed; metaphysical applicability open | docs/notes/causal-perfection-transfer.md |
| `STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH` | emergence and amplification: causes producing a quality they lack or have less (Broad; natural selection, `DARWIN-ORIGIN`) | countermodel threat | the statement is a recorded strengthening of *Met.* II.1, 993b24-26; Fourth Way order work in #341; to source |
| `STMT-CHRIST-FOUNDED-VISIBLE-CHURCH` | Jesus announced the Kingdom and founded no church (Loisy 1902) | evidential/abductive (#379) | to source (public domain) |
| `STMT-CHRISTS-CHURCH-IS-THE-CATHOLIC-CHURCH` | Orthodox and Protestant ecclesiologies | evidential/abductive (#379) | to source |
| `STMT-CLASSICAL-ATTRIBUTES-SUFFICE` | theistic personalism and open theism: God mutable and temporal | evidential (definitional bridge from *Dei Filius* ch. 1) | to source |
| `STMT-COMPOSITE-HAS-A-UNITING-CAUSE` | brute composition: composition happens without any cause (mereological universalism, Lewis) | not yet attackable | copyrighted, #378 |
| `STMT-EVERY-CREATED-AGENT-ACTS-AS-APPLIED-TO-ACT-BY-GOD` | mere conservationism (Durandus); occasionalism from the other side | not yet attackable | to source |
| `STMT-GOD-IS-MAXIMAL-IN-BEING` | God beyond being (*hyperousios*: Plotinus, Pseudo-Dionysius) | not yet attackable: disambiguation | to source |
| `STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE` | "God" names the personal God of revelation, not a metaphysical principle (Pascal's *Mémorial*); Kant's objection (recorded attack) | evidential/semantic | to source |
| `STMT-GOODNESS-IS-ACTUALITY` | goodness is relative to desire or an idealized attitude (Hume; Railton, `RAILTON-MORAL-REALISM`) | evidential/abductive (rival worldviews); derivation route in #352 (ST I q.5 a.1) | link the existing naturalistic-realism rival |
| `STMT-GRADES-HAVE-A-MAXIMUM` | scales without a maximum (unbounded or open scales) | countermodel: order theory gives scales with no greatest element (#341) | the defence needs a restriction to perfections |
| `STMT-IMMATERIAL-IS-INTELLECTUAL` | immaterial non-intellectual beings: Platonic or Fregean abstract objects (Frege, "Der Gedanke", 1918) | countermodel threat unless "immaterial" is restricted to subsistent beings | to source (public domain) |
| `STMT-IMMUTABLE-IS-ETERNAL` | an immutable thing need not have Boethian eternity (possession of life); abstract objects | derivation (#353) |  |
| `STMT-JESUS-CLAIMED-DIVINE-AUTHORITY-AND-ROSE` | legend (Strauss 1835); hallucination hypotheses | evidential/abductive (#379) | Strauss public domain; later work #378 |
| `STMT-MATTER-FORM-AND-ESSE-ESSENCE-ARE-COMPOSITIONS` | only a distinction of reason between esse and essence (Suárez, *Disp. met.* XXXI) | not yet attackable: real versus rational distinction | to source (Latin, public domain) |
| `STMT-MAXIMUM-IN-BEING-IS-FIRST-BEING` | Neoplatonism: the One is beyond being, so the maximum in being is posterior to it (Plotinus, *Enn.* V.1, V.4) | not yet attackable: needs a disambiguation of "maximal in being" | to source (Greek, public domain) |
| `STMT-MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS` | a maximum is only an upper bound with no causal role | countermodel (order models, #340, #341) | existing objection `STMT-BEING-NOT-A-GENUS` |
| `STMT-NO-COMPONENT-IS-FIRST-BEING` | the first being is a component: David of Dinant (God is prime matter), Stoic God as form in matter | countermodel/inconsistency: Aquinas' own replies in ST I q.3 a.8 | to formalize |
| `STMT-PERFECTIONS-OF-EFFECT-PREEXIST-IN-CAUSE` | emergence | not yet attackable: formal versus eminent pre-existence | to source |
| `STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE` | no testimony suffices to establish a miracle (Hume, *Enquiry* X) | evidential/abductive | Hume witness pinned for other sections only |
| `STMT-SUBSISTENT-BEING-IS-INFINITE` | a subsistent being limited by its own nature | not yet attackable | to source |
| `STMT-THINGS-MORE-AND-LESS-GOOD-TRUE-NOBLE` | value anti-realism: error theory, emotivism, quasi-realism | self-application/inconsistency for naive emotivism (Frege-Geach, `FREGE-GEACH-REFUTES-NAIVE-EMOTIVIST-MEANING`); quasi-realism not yet attackable | link the existing metaethics rivals |
| `STMT-WILL-FOLLOWS-INTELLECT` | intellect without will (Aristotle's self-thinking thought, *Met.* XII.9, with no providence) | not yet attackable | to source |
<!-- END GENERATED -->

## Next batches

Fourth Way (with #341, whose writer owns those files), attributes (with #353–#357), stage 3 (with #379), and the waiting witnesses of batch 1 once #378 lands.


## God-existence coverage cycle: main audit, 2026-11-08

Baseline: `371249351c73d0691247dba947572e26bed2b484`. This extends the existing
alternatives campaign; the current execution handoff remains issue #418.
The public Carneades [PHIL230 outline](https://www.carneades.org/challenge-page/philosophy-of-religion)
names ontological, cosmological and teleological arguments, evil, Euthyphro and
Clifford. Its [PHIL231 outline](https://www.carneades.org/challenge-page/ontological-argument)
names definitional, conceptual, modal, Meinongian, mereological and religious
experience variants. These public outlines are a coverage spine, not full
argument transcripts or evidence of historical author intent. Existing caption
findings in [frontier intake](notes/carneades-frontier-intake.md) and
[wager intake](notes/carneades-decision-wager.md) retain their fidelity limits.
Reconstructions and next investigations below are analyst formulations; new
source attribution is deferred. No new source claim or premise closure is made.

### Targets that must remain distinct

A being's existence at every accessible world does not establish that it is
concrete, causally active, the only such being, intelligent, willing, perfectly
good or revealing. A unique actual grounding source need not be necessarily
unique across worlds. A maximally perfect or first mover needs the explicit
attribute and naming bridges before it is the classical God. Classical theism
still needs separate revelation, resurrection and ecclesial premises to reach
Christianity or Catholicism. The existing checked
`TruthCore.Results.Causality.ClassicalGodRevelationBoundary.checks` supplies a
counterinterpretation to that last shortcut; it does not supply evidence against
actual revelation. `docs/notes/necessary-simple-plurality.md`, the UniqueRoot
batches and the term-sense forks retain the earlier distinctions.

The main route report has 28 root-concluding arguments, with cheapest expanded
open-leaf cost 28. That diagnostic does not rank philosophical warrant or show
that the root is true. Conditional alternative support, semantic clarification
and models matter even when this cost is unchanged. Draft #1181 changes that
presentation and has failed next-work browser assertions; it is not a dependency
of this investigation. Pending #1241 adds an OPEN actual-contingency node;
its conclusions must not be treated as established actual contingency.

### Idle-work audit before selecting investigations

`cargo run --manifest-path truth/Cargo.toml -- orphans --by module` at the
baseline finds large disconnected causal, explanatory and modal families;
Mereology, Hiddenness and Kant also retain disconnected work. The modal triage
already lives in `docs/notes/modal-results-triage.md` and #1241 is its current
connection attempt. For the opposing side, hiddenness has no root-path contact
in this report: its identity bridge is the existing candidate linked below.
That makes an exact bridge test more useful than another isolated hiddenness
core. The report is graph discovery, not evidence of irrelevance: controls and
refutations can remain disconnected by conclusion-to-root accounting. Do not
count a new imported library as a discharged philosophical premise.

### Family assessments and decisive next tests

The current assessment has 21 grouped rows; related variants within a row
retain separate target and follow-up obligations. This is a scope description,
not a research-success metric.

Entries name checked artifacts and the precise limitation they support. A
Solution's existence alone is not current-head certification; unchanged merged
proof evidence is reused, and new proofs retain final CI. A proposed next test is
not a completed result. Where no argument was located, the search bounds are
stated below rather than claiming that nothing has ever been written.

| Family and actual target | Formalized evidence and strongest surviving opposition | Next decisive investigation |
|---|---|---|
| **Motion / act-potency / per-se causes:** a first unmoved mover; classical attributes require later bridges | Batch 1 above, `TruthCore/Alternatives/ActPotencyRegress.lean`, and [motion rivals](notes/opining-motion-rival-coverage.md) distinguish retorsion from changing appearances. Infinitist local transmission and coherentist/occasionalist or same-respect objections are not defeated merely by calling a relation causal. | Use the weakest same-respect and borrowed-exercise premises that imply a source; test the infinitist and self-motion interpretations on the same carrier. Preserve causal applicability as open. |
| **Contingency / PSR / explanatory cosmology:** an actual necessary or underived concrete ground | [PSR strength](notes/psr-strength-755.md), [self-application](notes/psr-self-application-756.md), `AnselmCommonSourceAudit.lean`, and [Kant](kant-cosmological-inference.md) separate local causes, whole-history explanation, common-source and identification. Change alone fails to establish accessible nonexistence. A coherent infinite or brute foundation remains a serious alternative. | Compare weak local explanation with joint/global explanation on the route profile; seek a sufficient bundle without assuming the advertised unique necessary source. Test each globalizing bridge by omission. |
| **Temporal / kalam-style beginning:** a cause of a beginning, not automatically a necessary timeless person | `TruthCore/Causality/CountTemporalNecessity.lean`, `TemporalEventControls.lean` and [temporal rivals](notes/causal-temporal-rival-coverage.md) expose count/history/now and first-time/first-event distinctions. Threshold-production is a declared relation, not ordinary efficient causation by its name. | Test the beginning-to-cause bridge against an unbounded past, empty instants and bounded finite ages; distinguish event causation from a cause of the whole history. No cosmological observation is certified here. |
| **Degrees / perfection / Fourth Way:** maximal being, then a cause of all, then classical God | `QuartaViaDegreeFork`/`QuartaViaDegreeBranchWitnesses`, `TruthCore/Results/Causality/UniqueRootQuarta/Solution.lean`, and [causal perfection transfer](notes/causal-perfection-transfer.md) distinguish maximum, supremum, causal primacy and selected-root perfection. Open scales and a causally idle maximum survive without the relevant bridges. | Minimize the maximal-root perfection bridge; compare an ordered but noncausal maximum with a shared causal background. Do not promote an order-theoretic maximum into an intellect. |
| **Teleology / Fifth Way:** intelligent directors of natural bodies; a single first governor needs additional scope premises | `QuintaViaEachDirected` and `QuintaViaOneGovernor.oneGovernor` retain regularity/chance/intention, the knowing-director principle, reduction, directing-is-moving and uniqueness separately. The latter theorem includes omission countermodels. Natural regularity without cognitive direction challenges the director premise; several directors challenge the quantifier shift. | Compare non-intentional regularity with directed regularity on the existing signature; test whether one-governor scope can be weakened without assuming uniqueness. Evolutionary explanations are not refuted by the arrow analogy. |
| **Fine-tuning / probabilistic design:** evidence favoring a designer, not deductive creation or Catholicism | The audited Fifth Way is not a likelihood calculation. No fine-tuning likelihood/prior argument was located in the bounded search below. Single-universe luck, selection effects, multiverse and alternative designers remain open rival reconstructions, not registered refutations. | Define the evidence and sampling/observer condition before comparing likelihoods; show whether a Bayes-factor direction survives omission of the selection model and designer likelihood. Keep prior odds and theological identification separate. |
| **Definitional / conceptual ontological:** exemplification of a greatest or perfect being | The corpus's naming and GOD sense forks distinguish a nominal definition from an inhabited extension. The Gödel work below does not by itself cover every Anselmian or Meinongian argument. Kant's identification/conversion controls directly warn against this substitution. | Reconstruct the strongest conceptual inference as a typed argument, then test an empty extension and distinct existence senses; reuse the definition/naming forks rather than treating a definition as an existential witness. |
| **Meinongian object/property arguments:** existence from a characterized perfect object, or a challenge to existence-entailing predication | `Causality/MeinongianActuality.lean` and its checked `NoActualityWithoutBeing`/control results examine a golden-mountain interpretation and two explicit act/perfection-to-being premises. This is a conditional objection to actuality without being, not a checked Meinongian proof of God. Rejecting either bridge preserves the recorded rival. | Reconstruct the distinct PHIL231 ontological variant, distinguishing nuclear characterization, exemplification, actuality and existence. Test an uninstantiated or nonexistent characterized object before any inference to an existing perfect being. Do not count the act/perfection refutation as coverage of that whole argument. |
| **Modal ontological / Gödel:** modal God-likeness under a positivity and essence theory | `Results/Isabelle/GoedelGod/GodLikeNecessarilyExists`, `GodLikeUnique`, `NecessaryExistenceIndependence`, and `NotesOnGoedel/{Inconsistency,PossibleGodLikeNecessarilyExists,ActualistPossibilityBoundary}` compare configurations. The possibility input, positivity constraints, actualist domains and accessibility rules remain consequential. The original variant's inconsistency is not a refutation of every modal theism. | Compare the weakest consistent positivity/possibility bundle with its reversal, holding domain and frame fixed. Bridge its God-like predicate to the route's God explicitly before claiming theism or atheism about that target. |
| **Mereological / composition:** an ultimate composer or noncomposite foundation | [Composition scope](notes/composition-causal-scope.md), `Mereology/FusionNoNecessaryParts.lean`, `NecessaryPartFusionDecomposition.lean` and `UniversalFusionBoundary.lean` distinguish fusion, parts, arrangement and individual necessity. Contingent parts do not simply establish a contingent whole, nor a composer by definition. | Compare a brute fusion and a caused arrangement on the same actual-fusion profile; retain the composition-to-cause bridge explicitly and test both its direction and modal strength. |
| **Moral / Euthyphro:** a normative ground, lawgiver or perfectly good being | Existing naturalistic moral realism, `Comparison/MoralLanguage.lean`, `Metaethics/EvilObjection.lean` and [natural goodness/function/authority](notes/natural-goodness-function-and-authority.md) distinguish truth-aptness, value, function and authority. These are not a completed inference from moral realism to God. Naturalistic realism and autonomy of value are serious alternatives; semantic noncognitivism is not their substitute. | Test whether the proposed dependence is on will, nature, reasons or commands; make both directions of the dilemma separate propositions. Derive only what the chosen dependence supports and retain secular realist models. |
| **Logical evil:** incompatibility with specified omnipotence/goodness and a permission norm | `Comparison/ProblemOfEvil.lean` and its Catholic consistency model retain evil, prima-via premises and a disputed stronger good-from-every-evil commitment. Privation does not deny suffering. A finite compatibility model is a defense against a stated contradiction, not an actual theodicy. | Compare capability, permission policy and actual production of good using their existing sibling senses. Test which additional prevention obligation makes the strongest incompatibility follow. |
| **Evidential evil / Rowe:** an omniscient, omnipotent, wholly good being | `RoweDeductiveCore.roweDeductiveCore` uses actual gratuitous suffering plus the permission constraint; `RoweApparentCompatibility.roweApparentCompatibility` shows apparent pointlessness can coexist with theism and hidden blocking costs. [Rowe assessment](rowe-evidential-evil.md) preserves the Moorean shift and the atheist's distribution/induction reply. No likelihood or total-evidence comparison is encoded. | Formalize a bounded recognition/completeness assumption and test its omission; separate an epistemic inference from the already checked deductive core. Possible hidden goods alone neither discharge actual costs nor defeat the inductive evidence. |
| **Divine hiddenness:** a perfectly loving, relationship-capable God with immediate openness | `Hiddenness/NoGod.noGod` derives nonexistence from four explicit premises; `PremisesIndependent` witnesses every omission. Qualified openness, delayed-access and nontheistic-development models survive in `docs/hiddenness.md`. Belief is not acceptance. [Existing bridge candidate](bridges/candidates/02-hiddenness-god-exists.md) records that the route's God is not yet identified with this signature. | First minimize the all-world premises to those at the actual world, then test a typed bridge to the root's classical God. The theist owes a sufficient reason for each actual gap; the critic must justify the unqualified norm and empirical nonresistance. |
| **Religious experience / testimony / epistemic permission (including Clifford):** warranted belief, sometimes an existential claim | The public outline names these topics. The [finite experience reconstruction](notes/religious-experience-recognition.md) now separates an occurring token, source accuracy, defeater absence, theological identification and nonfactive warrant, with finite omission and competing-source controls. Its root-capability connection remains an explicit assembly with open coverage and capability bridges; Clifford remains unformalized. `Alternatives/RevelationRecognition.lean` and existing historical comparisons address nearby testimony questions, not a general proof from experience. Hallucination, cultural dependence and competing revelations remain open alternatives. | Separate experience occurrence, veridicality, defeater absence and reliable identification; compare a fallible witness model with a false-positive model. Epistemic permission must not be reported as truth. |
| **Pragmatic / wager:** choice under a payoff/prior model, not existence | [Wager intake](notes/carneades-decision-wager.md), `Results/Decision/InfiniteWager` and `SignedWager` check mixture ties, signed-infinity boundaries and `practicalNontruth`. Many-gods payoffs and nonvoluntary belief remain serious objections. An undefined signed expectation is not a winning act. | Compare admissible acts and competing reward hypotheses with finite/truncated payoffs; test stability under priors and costs. Keep the practical recommendation distinct from the proposition that God exists. |
| **Attribute incoherence / modal collapse / freedom:** a God satisfying the specific disputed attribute bundle | `Modal/SimplicityCollapse.lean`, `SelectedEffectBridge.lean` and their results test a necessary rigid act, strict efficacy and contingent effects with omission models. Simplicity itself is not defined to entail those bridges. #1241 tests collapse rivals on the route profile under an OPEN contingency node. These results challenge bundles, not every necessary being or every creator. No dedicated foreknowledge-freedom or stone-paradox result was located by the bounded query below. | Test the inference from the relevant simplicity/immutability conception to act necessity and strict efficacy, then compare its denial with the strongest contingent-creation reply. For foreknowledge/omnipotence, first distinguish truth, knowledge, ability and logical impossibility; do not reuse the collapse theorem as their proof. |
| **Consciousness / reason / transcendental:** an adequate account of thought or rational warrant, with a further inference to divine intellect | `Logic/CogitoConcrete.lean` and its results reach an inhabited concrete world or the motion observation only through explicit bearer, actuality and opining bridges. A thought bearer is not automatically an immaterial self, God or divine intellect. `Logic/EpistemicReasons.lean` does not by itself identify a ground of reasoning with God. No dedicated consciousness-to-God or transcendental God argument was located in the bounded search. | Specify the alleged explanatory or normative insufficiency of a naturalistic account, and a rival realization model. Test the explanatory-gap-to-divine-intellect bridge separately from existence of a thinker; preserve physicalist, idealist and neutral alternatives without claiming a full model of each. |
| **Religious disagreement / competing revelations:** exclusivity or warranted identification of a revealed God, usually not bare divine existence | Hiddenness's concept/development models, the wager's competing rewards and the resurrection comparison encode nearby alternatives. They are not a general theorem from disagreement to atheism. No dedicated disagreement argument was located in the bounded search. The strongest challenge concerns reliable discrimination among incompatible claims; a theist can reject equal evidential standing or distinguish disagreement about God from God's existence. | Compare incompatible testimony with shared reliability assumptions and stated defeaters; show which identification or confidence claim fails. Do not infer that all disagreeing parties are false, or that bare necessary existence is disproved. |
| **Naturalism / brute / plural foundations:** surviving alternatives to specified supernatural/unique-cause claims | `Results/Ontology/Naturalism/Survivor` supplies a spatially located whole and an infinite local causal regress; `NaturalismLogicalFloor`, universe-scope controls and [concreteness boundary](notes/causal-concrete-rival-boundary.md) distinguish causal power, location and actuality. Refuting one naturalism definition does not refute every naturalist worldview; formal consistency does not establish reality. | Compare rival models against the same weakest route bundle, identifying the exact premise each rejects. Avoid imposing the theist's causal well-foundedness merely to eliminate the rival. |
| **Revelation / Christianity / Catholicism:** stages beyond classical theism | `History/Resurrection*.lean`, `Comparison/Resurrection.lean` and its legend, stolen-body, swoon and group-hallucination consistency results preserve historical alternatives. `ClassicalGodRevelationBoundary.checks` blocks automatic passage from classical attributes to revelation or Church identity. The stage-3-to-6 explorations retain historical and authority bridges. | Compare the strongest shared evidence constraints before assessing the surviving historical hypotheses, then separately investigate authority and ecclesial identity. Neither a necessary being nor an inconsistent caricature of a rival settles resurrection or Catholicism. |

### Coverage limits and continuation order

This is an initial evidence-backed assessment, not an exhaustive survey of every
Carneades video, every philosophical tradition, or the empirical literature.
For the absence entries, the bounded search was case-insensitive content search
of `corpus/statements/` for fine-tuning, religious experience, Clifford and moral
argument, extended to Meinong, foreknowledge, omnipotence paradox, consciousness,
transcendental argument and religious disagreement, plus filename search of `TruthCore/` for the named families. This can
miss differently named or implicit arguments. Existing `related`, `context` and
`dossier` packs must precede new vocabulary. It is not evidence that an argument
is false or that a family is unimportant. The conceptual, Meinongian and
religious-experience variants need separate reconstructions; modal results must
not be counted as their completion. Historical source authentication is deferred
unless explicitly selected; the existing verified readings remain intact.

### Findings from the first bounded investigations

[PR #1241](https://github.com/moritzbrantner/truth-core/pull/1241) reconciles the
contingency node with current identity and sense rules. It imports closed modal
certificates instead of retaining their broad bundles as assumptions, and keeps
the actual-contingency and frame-schema commitments OPEN. Its computed change
adds one open route-reaching premise; it does not defend actual contingency or
improve the cheapest route. The modal-library contact remains conditional.

[PR #1247](https://github.com/moritzbrantner/truth-core/pull/1247) weakens three
hiddenness norms from all worlds to the actual world. Checked projections and
strictness models distinguish the strengths; the empirical nonbelief witness is
retained. A conditional challenge to the stage-one GOD_4 predicate adds an
explicit one-way identification, with an omission model showing why that bridge
matters. All four carrying-premise omission witnesses are reused. The qualified
reply and nontheistic alternatives remain; no premise truth is established.
See [the substantive assessment](https://github.com/moritzbrantner/truth-core/blob/d2da1c08dfd67601bbdd89ba770d8b4b2b4f4a12/docs/hiddenness.md#actual-world-scope-and-route-identification-2026-11-08).

[PR #1248](https://github.com/moritzbrantner/truth-core/pull/1248) addresses neglected
teleology. The old common-governor result projects to the existing root-route
first-mover node through a labelled assembly. A substantive proof reaches that
same existential node from the original first seven premises without global
uniqueness. Seven omission countermodels and nonvacuity test that particular
bundle; a two-director survivor distinguishes existence from uniqueness. This
is not a seven-premise proof of one common governor. See [the premise and rival
assessment](https://github.com/moritzbrantner/truth-core/blob/8f9a6762f561bca11d7e7620bbc083221de750e0/docs/notes/teleology-first-mover.md).

These are clarification, strength, connection and incompatibility findings.
The focused PRs carry computed deltas and exact-head verification evidence.
Pending PRs are not merged certification; the current handoff #418 records the
live delivery state. No theorem count is used as the completion criterion.

### Prioritized continuation after the initial assessment

Continue alternating a consequential existing gap with a neglected family:

1. **Rowe recognition/completeness:** make a bounded recognition-to-absence
   assumption explicit; test its omission against the existing hidden-cost
   model. Then compare the critic's distribution/induction case with the
   skeptical-theist and Moorean replies. No probability conclusion follows
   merely from the current deductive core.
2. **Fine-tuning:** fix observer-conditioned evidence, rival hypotheses and
   likelihoods before computing evidential direction. Test omission of the
   sampling model and designer likelihood; keep priors and divine identity
   separate. This is not the Fifth Way's regularity argument.
3. **PSR/global explanation:** compare the weakest local sufficient bundle
   with whole-history and joint-explanation commitments, holding semantics
   fixed. Retain coherent infinite and brute foundations as serious survivors.
4. **Conceptual/Meinongian and religious-experience arguments:** reconstruct
   each missing variant independently, with empty-extension and false-positive
   controls. Existing modal and actuality/perfection work must not stand in for
   those arguments. Broaden source coverage only when it discriminates a live fork.
5. **Hiddenness and teleology strength follow-ups:** defend or reject actual
   openness and nonresistance, assess each God-identification conception, and
   localize teleology's universal premises to the witness the existential proof
   needs. Relevant-director uniqueness is a separate one-governor question.
6. **Moral dependence, Clifford and consciousness/reason:** distinguish reasons,
   commands, nature, epistemic permission and divine intellect; compare the
   strongest secular alternatives before selecting a necessary God bridge.
   Foreknowledge-freedom, omnipotence paradoxes and disagreement need their own
   typed reconstructions rather than being counted as modal-collapse coverage.

Progress means weaker sufficient premises, well-typed targets, tested
incompatibilities, genuine rival survivors and resolved bridges. Neither this
assessment nor a checked conditional independently establishes a philosophical
premise. This documentation change has no premise delta. The initial cycle's
completion still requires the selected research and this reconciliation to be
merged with required checks, updated handoff and a final requirement audit; this
table alone is not a completion declaration.
