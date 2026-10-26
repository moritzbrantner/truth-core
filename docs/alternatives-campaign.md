# Alternatives campaign (#387)

Closure rule (c) (`docs/corpus-model.md`) closes an open premise when **every** recorded alternative is refuted, and at least one is recorded. Before this campaign the rule had closed nothing. The campaign records, for every open premise on a root path, the strongest rivals actually held in the literature, classifies how each could be refuted, and refutes in Lean where that is cheap and honest. Owner decisions on #387: no `self_evident` markings; strongest real rivals only, no strawmen; rivals that need copyrighted sources wait for bibliographic citations (#378) as candidates, with the statement and the classification recorded now.

Classes, as in the issue: **self-application** (the rival undermines itself), **countermodel/inconsistency** (the rival is inconsistent with itself or with other results), **derivation** (the premise can be derived instead), **evidential/abductive** (a comparison of explanations), **not yet attackable** (the note says what is missing).

## Policy for `refutes` relations

`corpus.py frontier` counts a `refutes` relation only when its argument has a verified result and is premise-free or all its premises are closed (#391/#411). Conditional refutations resting on open premises do not close a defended premise. This campaign records them in the `alternative_to` note and here as "refuted given open premises …", without a `refutes` relation. All three refutations of this batch have open premises, so this batch records no `refutes` relation.

Two further rules apply to conditional refutations here. The refuting argument must not use the premise it defends. And where the strongest form of a rival denies a premise of the refutation, that form is recorded as its own alternative and counted as unrefuted. Example: Aristotle's retorsion refutes the bare Eleatic thesis given "opinion is a motion"; the McTaggart-style rival grants appearances and denies that an appearance of change is a change, so it is a separate alternative, although it formally entails the Eleatic one.

Self-application rivals in later batches should use the retorsion schema of `TruthCore/Logic/SelfApplication.lean` (merged in PR #403); the Eleatic retorsion here predates it and is a direct proof in the prima via vocabulary.

## Counts

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

No `refutes` relation is recorded for them (#391). Even with them, no premise would close: every premise in the batch keeps at least one rival that is unrefuted even conditionally.

<!-- BEGIN GENERATED: docs/alternatives/premises table "premise=Premise" "rival=Strongest rival(s) recorded" "class=Class" "status=Status" filter:phase=batch-1 -->
| Premise | Strongest rival(s) recorded | Class | Status |
|---|---|---|---|
| `STMT-ACT-SIMPLY-PRIOR-TO-POTENCY` | `STMT-POTENCY-PRIOR-TO-ACT` (*Met.* XII.6, 1071b22-28: the reputable view; theologians from Night) | inconsistency, partial: Aristotle's reply covers only potencies being actualized (#352, finding 4) | open; sourced |
| `STMT-ACTUALITY-ONLY-INSOFAR-AS-BEING` | `STMT-ACTUALITY-WITHOUT-BEING` (Meinong, Sosein without Sein) | naive form: inconsistency (Russell); nuclear form: not yet attackable | open; witness waiting (`MEINONG-GEGENSTANDSTHEORIE-3`); elimination failed: the rival is the premise's contradictory, so its only minimal core is the premise itself (`ACTUALITY-WITHOUT-BEING-NOT-ELIMINATED`, #497) |
| `STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES` | `STMT-INFINITE-PER-SE-CAUSE-SERIES` (infinitism about ground); `STMT-PER-SE-CAUSAL-LOOP` (coherentism) | infinite series: not yet attackable, consistent by `INFINITE-LOCAL-TRANSMISSION-MODEL` (ACT-GROUND, #310; causal finitism, #367); loop: inconsistency, refuted given open premises | open; both witnesses waiting (#378). *Met.* II.2 (`ARIST-MET-II-2`) is the Aristotelian source still to read for the premise |
| `STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT` | `STMT-ACT-AND-POTENCY-IN-SAME-RESPECT` (Scotus, self-motion by virtual act and formal potency) | not yet attackable: turns on `DISAMB-IN-ACT` | open; Scotus witness waiting (`SCOTUS-QQ-METAPH-IX-Q14`) |
| `STMT-NOTHING-MOVED-EXCEPT-AS-IN-POTENCY` | `STMT-MEGARIAN-ABILITY-ONLY-WHEN-ACTING` (*Met.* IX.3); `STMT-MOVED-WITHOUT-POTENCY` (Ash'arite re-creation) | Megarian: inconsistency, refuted given open premises; Ash'arite: not yet attackable (re-creation as change) | open (Ash'arite unrefuted); al-Ghazali witness waiting |
| `STMT-NOTHING-MOVES-EXCEPT-AS-IN-ACT` | `STMT-CAUSE-MOVES-WITHOUT-BEING-IN-ACT` (emergentism) | not yet attackable: bites only on the formal reading of act | open; witness waiting (Broad 1925, #378) |
| `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER` | `STMT-INERTIAL-UNIFORM-MOTION-WITHOUT-MOVER` (unattributed; motivated by Newton's first law, sourced as the conditional `STMT-NEWTON-LEX-I-CHANGE-OF-STATE-ONLY-BY-IMPRESSED-FORCE`, which asserts no force-free body); `STMT-CHANGE-WITHOUT-ANY-MOVER` (quantum indeterminism) | not yet attackable: uniform motion as state versus reduction; moving versus determining (`DISAMB-MOTION`) | open; rival unattributed (Newton's conditional law sourced, Latin 1687), Born waiting (#378) |
| `STMT-PER-SE-MOVER-LINK-IS-PER-SE-CAUSE-LINK` | `STMT-OCCASIONALIST-MOVER-LINK-WITHOUT-CAUSE` (Malebranche, al-Ghazali) | self-application candidate: SCG III.69 (knowledge of natures from effects) | open; witnesses waiting |
| `STMT-SECOND-MOVERS-MOVE-ONLY-AS-MOVED` | `STMT-MOVED-MOVER-MOVES-NOT-AS-MOVED` (a mover moved in an irrelevant respect) | not yet attackable: it bears on the fidelity of the strong reading; the reply is the weaker sibling reading | open; supported by ST I q.46 a.2 ad 7 reading B |
| `STMT-SOMETHING-IS-MOVED-IN-THIS-WORLD` | `STMT-ELEATIC-NOTHING-IS-MOVED` (*Phys.* VIII.3); `STMT-CHANGE-UNREAL-BUT-APPEARS` (unattributed McTaggart-style rival: McTaggart's sourced thesis `STMT-MCTAGGART-NO-A-SERIES-CHANGE-BUT-APPEARS` denies A-series change and reaches this premise only through the open bridge `STMT-BEING-MOVED-INVOLVES-A-SERIES-CHANGE`, `DISAMB-CHANGE-A-SERIES`) | Eleatic: self-application, refuted given open premises; McTaggart: denies the retorsion's premise | open; Eleatic sourced, McTaggart thesis sourced, bridge open. Diodorus Cronus ("nothing is moving, things have moved"; Sextus, *M.* X) to source |
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
| `STMT-CAUSE-OF-BEING-CAUSES-EVERY-PERFECTION` | mere conservationism (Durandus): the cause of being conserves it, secondary causes alone produce further perfections | not yet attackable | to source |
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
