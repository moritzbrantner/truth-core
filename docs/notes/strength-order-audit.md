# Strength-order audit (2026-11-12)

Audit of the verified results whose argument has exactly one premise and no commitments and that no `strengthens` relation registered at main `1587e8313`: 209 results. Argument ids are shown by their first eight characters; `truth context <id>` expands them. The rule change is in [the decision](../decisions/2026-11-12-03-strength-registrations-reach.md); the contract is in [corpus model, Strength order](../corpus-model.md).

## Criterion

A pair is registered when, checked against the Lean types, the conclusion comes from the premise **in the same vocabulary only by weakening steps**: dropping a conjunct (also inside the same existential witness) or one direction of a biconditional; restricting a universal's domain, a relation to a subrelation, or instantiating a universal at the case the argument uses; generalizing an existential (a fixed case to some case, including a named-case disjunction); ∃∀ to ∀∃; ¬∀ over a narrower to ¬∀ over a wider condition; or a weaker relation on the same relata (< to ≤ or ≠). The converse must not be classically provable. Not registered:

- equivalences (proved in both directions, definitional or intuitionistic restatements), recorded as `logically_equivalent_to` where both directions are verified;
- the backing argument of a `refutes` relation: its conclusion denies a recorded rival, and since closure sets a registration's backing argument aside, registering it would drop a counted defeat (`test_no_registration_backs_a_refutation` enforces this);
- a countercase step ∃x ¬P x to ¬∀x P x (or ∃x P x to ¬∀x ¬P x) on the same P, which is classically an equivalence, or a step to the denial of a different proposition;
- instantiations of a logical law (excluded middle, non-contradiction) into new subject matter, and consequences that use further reasoning or add content.

## Registered (42)

20 in the first pass, 22 after review (marked †).

| argument | strong version | weak version |
|---|---|---|
| `0b9fa40e` | Anything that comes to be has some distinct CAUSE_2 | Anything that comes to be has some CAUSE_2 |
| `dbd2edfd` | For an arbitrary supplied type and predicate P, exactly one witness satisfies P | For an arbitrary supplied type and predicate P, at least one witness satisfies P |
| `663b9235` | For an arbitrary supplied type and predicate P, exactly one witness satisfies P | For an arbitrary supplied type and predicate P, any two witnesses satisfying P are equal… |
| `872d82a5` | For the supplied mathematical linear order and x,y, y is strictly greater than x | For the supplied mathematical linear order and x,y, y is at least x |
| `f4da998c` | For the supplied mathematical linear order and x,y, y is strictly greater than x | For the same mathematical x,y, y is not equal to x; this is proposed extra required conten |
| `992770d3` | The cause of a thing's being causes each of its perfections | Universal esse CAUSE_2: causing a distinct effect's esse entails causing its actual perfec |
| `0bb5f653` | The cause of a thing's being causes each of its perfections | Retain the unrestricted transfer for nonuniversal causes and for self-effects |
| `1e6fa15b` | There are natural bodies, and every natural body operates always or for the most part in t | Some natural body operates always or for the most part in the same way so as to attain som |
| `763ce47f` | In ordered efficient causes the first causes the middle and the middle the last: an effici | An efficient cause other than its effect that is itself caused in a respect relevant to it |
| `f4abae1b` | What is maximal in a GENUS_2 is the cause of that perfection in every other thing that has | The genus principle at being only: whatever is maximal in being causes the being of every  |
| `0a8e600a` | At every world each existing contingent individual has a distinct existing cause | Every existing contingent individual has an existing cause at the selected world |
| `fa5cee1f` | Every object has a part that is simple in the standard IsMin sense | Every actually contingent object has a simple actual part |
| `544b257d` | Some concrete individual exists at w and at every world accessible from w: the same rigid… | At least one individual exists at the selected world and at every world accessible from it |
| `a6edde9a` | Some SAME rigid individual satisfies the supplied Scenario concrete predicate, exists at t | At least one individual exists at the selected world and at every world accessible from it |
| `32c7d630` | Some actual CONCRETE_AND_ABSTRACT_6 being is CONTINGENT_1 | Some candidate is CONCRETE_6 and exists at the selected world w₀: ∃ b, CONCRETE_6 b ∧ m.Ex |
| `97c207ee` | Every Johannine commission saying is literarily independent of every Matthean one | John 20.21–23 is independent of Matthew 18.17–18 or Matthew 16.18–19 |
| `ad08fa58` | No nonempty finite path in the supplied causal relation returns to its start | Nothing is both the cause and the effect of another thing: for distinct x and y, x does no |
| `f5b624bf` | Any two bearers of the selected perfection have comparable represented degrees | Each pair of selected-perfection bearers has a bearer at least as high in degree as both |
| `2feb91b4` | Stipulated mathematical configuration component, not an attributed source reading: Some fi | Stipulated mathematical configuration component, not an attributed source reading: Every s |
| `68ab085d` | Stipulated mathematical configuration component, not an attributed source reading: Some su | Stipulated mathematical configuration component, not an attributed source reading: Every m |
| † `08e939d6` | Anything that comes to be has some distinct CAUSE_2 | Every generated thing that causes itself has a CAUSE_2 distinct from itself; that alternat |
| † `f74369e3` | Some bearer of the selected perfection is at its greatest represented degree | Each pair of selected-perfection bearers has a bearer at least as high in degree as both |
| † `9df4ccfb` | There exists an actual concrete root n of the profile selected relation at w, n exists at  | Some concrete individual exists at w and at every world accessible from w: the same rigid… |
| † `6d38a20b` | There are an accessible history v and the SAME concrete individual c with a count-one caus | At least one individual exists at the selected world and at every world accessible from it |
| † `20c5e9de` | What the restricted doctrine concedes: outside its domain it is not the case that whatever | The unrestricted measure doctrine fails: not everything that seems so to someone is true f |
| † `b4eccbb4` | A being is being moved in a respect exactly when it is potentially so and that POTENCY_1,  | Nothing is moved except insofar as it is in POTENCY_1 to that toward which it is moved |
| † `63a8deb7` | A being is in POTENCY_1 in a respect exactly when it is able to be so and is not actually  | Nothing is simultaneously in act and in POTENCY_1 in the same respect, though it may be so |
| † `1bd97b66` | Being different, unequal, or a non-being does not by itself necessitate being in motion | Motion is not identical with difference, inequality, or non-being |
| † `b7ed5289` | Every proposition is the object of some act of thought that affirms or denies it | Every object of thought is affirmed or denied: whatever is the object of some thought is t |
| † `ea3f7bd5` | Every world has no nonempty directed present-support loop on the fixed necessary subtype | No world witnesses every edge of any nonempty union loop on the necessary subtype |
| † `81094ad1` | Global normative reason nihilism | The view supplies no internal reason to adopt it of any represented kind |
| † `53412308` | Reasons of a selected kind are absent | The view supplies no internal reason to adopt it of a selected kind |
| † `56f129f6` | The profile's selected relation at w, restricted to candidates that are CONCRETE_6 and exi | The selected grounds relation restricted to the subtype of all actual CONCRETE_6 ancestors |
| † `92ab7c94` | There exists ONE SAME selected actual concrete necessary root n retaining the PerfectRootA | GOD_4 exists: there is something that is GOD_4, in the sense of the GOD_4 of classical the |
| † `b773170a` | There exists ONE SAME selected actual concrete necessary root n retaining the PerfectRootA | There is one and the same being that is God, is the only being to which the skeleton's IsG |
| † `a9aefdc5` | There is an intelligent first mover moved by none that directs every natural body to an en | There is a first mover moved by none: something that moves another and is itself moved in  |
| † `fccc5a79` | A candidate edge to the selected whole exists but no causer of that whole exists at the se | Exact negation of the existing UniverseHasExistingCause at the SAME Ontic/world/whole |
| † `179378e2` | A relevant supplied mathematical fact lacks esse in re and productively causes its outcome | Disjunction of the explicit set, Form or mathematical selected-world productive/no-esse co |
| † `faa38eda` | A selected-world no-esse capacity/productive countercase exists but none of the named prod | At the selected world one candidate lacks esse in re and either possesses causal power or… |
| † `70a8a65e` | A selected-world productive cause is a supplied Form and lacks esse in re | Disjunction of the explicit set, Form or mathematical selected-world productive/no-esse co |
| † `573a635d` | A selected-world productive cause is a supplied set and lacks esse in re | Disjunction of the explicit set, Form or mathematical selected-world productive/no-esse co |
| † `86d41602` | The separately specified METAPHYSICAL_GROUNDING_2 relation is asymmetric | For the specified bearer, Form and quality, exemplification and participation do not groun |

Effect on closure, computed against the tooling change (#1527) on the corpus at the change: reach, established and refuted sets are unchanged. Fourteen statements whose only closing proof was a backing argument from a closed but not established strong version are open again (they close by `via_strength` once the strong version is established), and three strong versions close because the support cycle through their weak versions no longer forms (distinct-cause principle, unique existence, strict order). The PR body has the computed `frontier-diff`.

## Not registered: equivalences (14)

| argument | premise | conclusion | reason |
|---|---|---|---|
| `b7946610` | Necessary-being node, possibilist K reading: there is an actual root n that is God, the on | Necessary-being node, actualist K reading: there is an actual root n that is God, the one  | proved in both directions (the reverse is registered as strengthens a436e461); now recorded as logically_equivalent_to |
| `47a957e3` | An OPEN framework presentation of union well-foundedness: one world-independent map into a | The union of every admitted world's direct existential-support edges among fixed de re nec | converse of 1fb5fbc1; the pair is recorded as logically_equivalent_to |
| `1fb5fbc1` | The union of every admitted world's direct existential-support edges among fixed de re nec | An OPEN framework presentation of union well-foundedness: one world-independent map into a | converse of 47a957e3; recorded as logically_equivalent_to |
| `c5c9ff49` | Inside Lean logic, ¬. A logical theorem, not a philosophical independence thesis | Inside Lean logic, ∃ P: Prop, P. This asserts only a proof inhabiting some proposition; it | converse of ec000eff: two trivially true Lean-logic pilot statements, proved equivalent |
| `ec000eff` | Inside Lean logic, ∃ P: Prop, P. This asserts only a proof inhabiting some proposition; it | Inside Lean logic, ¬. A logical theorem, not a philosophical independence thesis | converse of c5c9ff49: proved equivalent |
| `57da203d` | Inside Lean logic, ¬. A logical theorem, not a philosophical independence thesis | Inside Lean logic, ∧ ¬. A bounded conjunction of the pilot witness and its logical consequ | P to P ∧ (a consequence of P): equivalent |
| `20920247` | Open premise, the fuller nominal profile under the adopted component-remoteness reading: t | Sense bridge GOD_1 to GOD_4: what meets the full description is the God of classical theis | converse of b7e2768a: proved equivalent |
| `b7e2768a` | Sense bridge GOD_1 to GOD_4: what meets the full description is the God of classical theis | Open premise, the fuller nominal profile under the adopted component-remoteness reading: t | converse of 20920247: proved equivalent |
| `5d8b78ad` | Negation of the Scotist rival act and POTENCY_1 in same respect on the same InAct and InPo | Nothing is simultaneously in act and in POTENCY_1 in the same respect, though it may be so | ¬∃(A ∧ B) to ∀¬(A ∧ B): intuitionistically equivalent |
| `e014720d` | No candidate changes in the SAME general Changes sense used by F3: no characteristic, qual | Exact negation of F3 SomethingChangesReading under the SAME general Changes dictionary | ∀¬P to ¬∃P: intuitionistically equivalent |
| `7f236407` | Ash'arite occasionalist rival: things are moved to new states without being in POTENCY_1 t | Some actual moved tuple is not in POTENCY_1 in the SAME respect under the supplied… | definitionally equal declarations |
| `da9890fc` | GOD_4 exists: there is something that is GOD_4, in the sense of the GOD_4 of classical the | The Catholic pilot affirms the existing skeleton’s GodExists predicate | definitionally equal declarations |
| `f60704c5` | For each effect, any two incoming complete causes coincide | Each graph node has at most one immediate upstream predecessor | definitionally equal (left-uniqueness) |
| `0ff50c59` | Some object is a source of the selected graph relation: it has no incoming cause-edge | The selected graph has at least one graph-relative source | definitionally equal (graph source) |

## Not registered: refutation arguments (3)

Each is a weakening by the steps above, but its argument is a counted or countable refutation.

| argument | premise | conclusion | reason |
|---|---|---|---|
| `61d691f0` | A being is being moved in a respect exactly when it is potentially so and that POTENCY_1,  | Negation of the Ash'arite rival moved without POTENCY_1 on the same MovedIn and InPotency: | backs the refutes relation against the Ash'arite rival (c2307406) |
| `ac0ca8ad` | A being is in POTENCY_1 in a respect exactly when it is able to be so and is not actually  | Negation of the Scotist rival act and POTENCY_1 in same respect on the same InAct and InPo | backs the refutes relation against the Scotist rival (3ea60632) |
| `fe175c53` | There are epistemic reasons: some agent has an epistemic reason to believe some content | Global normative reason denial fails in the given profile | backs the refutes relation against global normative nihilism (2fcbd634); registering it removed that counted refutation |

## Doubtful, left unregistered (6)

| argument | premise | conclusion | reason |
|---|---|---|---|
| `a161fd71` | One actual concrete root at w directly grounds every other actual concretum in the SAME se | Some actual concrete root of the selected grounding relation exists at w, and every actual | common direct grounding to uniqueness of the root: the conclusion adds uniqueness derived from coverage, new content |
| `10d955b0` | Witness-local Fifth Way bundle | There is a first mover moved by none: something that moves another and is itself moved in  | from a composite Fifth Way bundle to the First Way conclusion only through the bundle's internal implications |
| `c1ab1c3b` | Accidental mover coverage supplies a per-se mover | The finite mover fork supplies a per-se mover | from one branch's coverage to the soundness of a three-branch fork: a case-analysis consequence |
| `fbf6b3fe` | The fixed selected conjunction actually holds and fails at some accessible world | Some f belongs to S and satisfies the existing Contingent A w f: it holds actually and fai | joint contingency of a set to contingency of some member: needs reasoning about the set, not a weakening of one claim |
| `0ff5d4a7` | The esse of every CREATURE_1 is received in some principle | The esse of every CREATURE_1 is received in some principle, sense-fixed | different predicates (creature to CREATURE_1-of-universal-cause): a sense bridge, not a weakening |
| `efb88bdf` | Whatever is CREATURE_2 is CREATURE_1, sense-fixed | Whatever is CREATURE_2 (caused in being by another) is CREATURE_1 | different predicates (CREATURE_2 to CREATURE_1, sense-fixed): a sense bridge, not a weakening |

## Not registered: excluded-middle instances into new subject matter (60)

| argument | premise | conclusion |
|---|---|---|
| `65d8afad` | Excluded middle as a general principle: every proposition either holds or does not hold | Positive and discriminating full-eighteen-input control on the EXACT old four-role #732 co |
| `4b889462` | Excluded middle as a general principle: every proposition either holds or does not hold | The weak governing-event institutional link holds, or an actual mandate/body/governing-eve |
| `5b241768` | Excluded middle as a general principle: every proposition either holds or does not hold | On the EXACT unchanged CountTemporalControls.history, import the existing old PositiveCont |
| `bfb93355` | Excluded middle as a general principle: every proposition either holds or does not hold | Five typed boundaries in the original independent-potency dictionary: the weaker relevant- |
| `cdbe2cbe` | Excluded middle as a general principle: every proposition either holds or does not hold | For every supplied graph, each selected node’s full reflexive ancestor cone generated by f |
| `f34268a3` | Excluded middle as a general principle: every proposition either holds or does not hold | On the unchanged original four-being #681 carrier and DirectEsseGenusOmissionControl.profi |
| `a51533bd` | Excluded middle as a general principle: every proposition either holds or does not hold | Reuse the EXACT mixed Ontic and concrete predicate; explicitly add an unused empty-grounds |
| `b35e7cbd` | Excluded middle as a general principle: every proposition either holds or does not hold | Either the admitted situations cover the selected capability-recognition witnesses, or an  |
| `447d83eb` | Excluded middle as a general principle: every proposition either holds or does not hold | The stronger local-plus-invariant profile, or local status with an actual matched religiou |
| `e999ea18` | Excluded middle as a general principle: every proposition either holds or does not hold | For every fixed profile and definition space, semantic named coverage holds or an explicit |
| `cfae2c12` | Excluded middle as a general principle: every proposition either holds or does not hold | Either all natural-knowability moves answer to shared reason, all lack sharedness, or actu |
| `2611caa9` | Excluded middle as a general principle: every proposition either holds or does not hold | The fixed public survivor dictionaries jointly satisfy the three N1 readings, part-based… |
| `3a047eee` | Excluded middle as a general principle: every proposition either holds or does not hold | One fixed Bool-world/Bool-time History with Option candidates jointly satisfies all six or |
| `335968ac` | Excluded middle as a general principle: every proposition either holds or does not hold | Under explicit object-level excluded middle, some stage-indexed marker structure satisfies |
| `5cf9fb65` | Excluded middle as a general principle: every proposition either holds or does not hold | Two source-free Boolean assignments preserve the existing CrossedTops carrier, in-act dict |
| `1ef5435a` | Excluded middle as a general principle: every proposition either holds or does not hold | For every fixed typed form/end profile, goodness exactly coextends with due actuality, or  |
| `4e35adc2` | Excluded middle as a general principle: every proposition either holds or does not hold | Positive joint compatibility control on the EXACT existing CountTemporalControls.history:  |
| `86a473fc` | Excluded middle as a general principle: every proposition either holds or does not hold | Either every proper instance is preserved in practice reference, or a proper instance lost |
| `b0b34755` | Excluded middle as a general principle: every proposition either holds or does not hold | At the selected world the local no-brute and brute-existence alternatives cover and cannot |
| `5dd18965` | Excluded middle as a general principle: every proposition either holds or does not hold | Concrete analyst boundary under supplied excluded middle on the EXACT unchanged… |
| `ad86a700` | Excluded middle as a general principle: every proposition either holds or does not hold | Full-background omission control for the twelve-input fixed-esse necessary… |
| `24b0ed04` | Excluded middle as a general principle: every proposition either holds or does not hold | The partition of the shared question q f7: either a being is in potency in a respect exact |
| `0b47df39` | Excluded middle as a general principle: every proposition either holds or does not hold | Stronger identity-scope fork: named candidate identities cover every admissible proposal o |
| `542c8b60` | Excluded middle as a general principle: every proposition either holds or does not hold | Consume the ORIGINAL NecessarySimplePlurality.jointControl, not the later five-being… |
| `6a7338e3` | Excluded middle as a general principle: every proposition either holds or does not hold | Full25-input positive compatibility and scope control extending the EXACT… |
| `b420c497` | Excluded middle as a general principle: every proposition either holds or does not hold | Positive joint control on the UNCHANGED five-being PartFreePlurality strengthening, explic |
| `b8b176cf` | Excluded middle as a general principle: every proposition either holds or does not hold | Structural omission of ledger L on the unchanged ORIGINAL four-being #681 joint interpreta |
| `834c6ea7` | Excluded middle as a general principle: every proposition either holds or does not hold | Either every defined move is endorsed, every defined move lacks endorsement, or actual opp |
| `f0c4146c` | Excluded middle as a general principle: every proposition either holds or does not hold | In ONE explicit Unit-world/Bool-individual formal fixture, the classifier… |
| `819242eb` | Excluded middle as a general principle: every proposition either holds or does not hold | Either the open named menu holds or all three calibrations fail, on the same admitted scop |
| `3adb1eff` | Excluded middle as a general principle: every proposition either holds or does not hold | For every supplied frame, actual-stable calibration, invariance-only calibration… |
| `6351bf87` | Excluded middle as a general principle: every proposition either holds or does not hold | Every state either has F or lacks it: no state lies between the two sides of the contradic |
| `1cf24420` | Excluded middle as a general principle: every proposition either holds or does not hold | For every supplied presence/possibility profile, the original collective conditional holds |
| `ed68067b` | Excluded middle as a general principle: every proposition either holds or does not hold | For a fixed critic-utterance interpretation and target Rowe frame, at least one holds: the |
| `4516376e` | Excluded middle as a general principle: every proposition either holds or does not hold | Under explicit excluded middle, named domain coverage or the conjunction denying all three |
| `3e15400e` | Excluded middle as a general principle: every proposition either holds or does not hold | For every fixed comparison profile, one of the four named calibration propositions holds o |
| `455f1107` | Excluded middle as a general principle: every proposition either holds or does not hold | The visible, spiritual, joint-aspect or explicit further Church-extension case holds |
| `a4a1c1db` | Excluded middle as a general principle: every proposition either holds or does not hold | Under the esse criterion every candidate is CONCRETE_6 or ABSTRACT_3, and none is both: th |
| `81c8fb8a` | Excluded middle as a general principle: every proposition either holds or does not hold | Either some candidate changes in the supplied general Changes sense or no candidate does |
| `2fd362f4` | Excluded middle as a general principle: every proposition either holds or does not hold | Structural coverage: complete entailing selection, some accepted truthful nonselecting can |
| `2cde635b` | Excluded middle as a general principle: every proposition either holds or does not hold | Any two first movers moved by none are either the same or distinct |
| `7a264b6b` | Excluded middle as a general principle: every proposition either holds or does not hold | For every supplied role/state profile, either the explicit same-act transfer holds or a pr |
| `3348801e` | Excluded middle as a general principle: every proposition either holds or does not hold | For the fixed semantic profile, the direct-only reading holds, or the Jesus-envoy-inclusiv |
| `d9429f72` | Excluded middle as a general principle: every proposition either holds or does not hold | The narrow, teaching-inclusive, or explicit further governing criterion holds |
| `c69cff48` | Excluded middle as a general principle: every proposition either holds or does not hold | Every practice lies in one of three cells: its grammar is fixed by its recognized authorit |
| `4f65460e` | Excluded middle as a general principle: every proposition either holds or does not hold | Either every moved tuple is in POTENCY_1, or some actual moved tuple is not in POTENCY_1,  |
| `530858fb` | Excluded middle as a general principle: every proposition either holds or does not hold | Either capability is realized correctly in an admitted situation and recognition is… |
| `f5e9bf3f` | Excluded middle as a general principle: every proposition either holds or does not hold | Structural trilemma on the SAME generic Ontic/world/whole: an existing cause, no candidate |
| `b7480ef1` | Excluded middle as a general principle: every proposition either holds or does not hold | For every supplied duration profile, either the two named calibrations cover or both fail |
| `d1836945` | Excluded middle as a general principle: every proposition either holds or does not hold | The original every-opiner designated-MOTION_3 norm or an actual opinion/nonmotion countert |
| `806b555d` | Excluded middle as a general principle: every proposition either holds or does not hold | For the SAME supplied per-se link, the old accessibility/WF premise holds or an actual Nat |
| `f867d897` | Excluded middle as a general principle: every proposition either holds or does not hold | For every supplied selected role/state profile, canonical reception holds at the selected  |
| `72b49ae6` | Excluded middle as a general principle: every proposition either holds or does not hold | For each supplied preorder/profile, named superlative calibrations cover or all three fail |
| `faf65c09` | Excluded middle as a general principle: every proposition either holds or does not hold | For every supplied frame, meaning predicate and scope, named coverage or the explicit conj |
| `12f07b36` | Excluded middle as a general principle: every proposition either holds or does not hold | Every NECESSARY_1 being either has the cause of its necessity from another or does not |
| `9cc7d6da` | Excluded middle as a general principle: every proposition either holds or does not hold | Either the explicit named-case coverage hypothesis holds or a precise relevant countercase |
| `cc81f226` | Excluded middle as a general principle: every proposition either holds or does not hold | Structural fork: for every supplied profile, named temporal calibrations cover, or both fa |
| `1052098f` | Excluded middle as a general principle: every proposition either holds or does not hold | For the SAME Before/now profile, every time up to now has a predecessor or some time up to |
| `19d7b5a4` | Excluded middle as a general principle: every proposition either holds or does not hold | Either there is a first mover moved by none or there is none |
| `06cd10d9` | Excluded middle as a general principle: every proposition either holds or does not hold | Logical rule template: for two indexed families of premise propositions and a common concl |

## Not registered: countercase steps (classically equivalent) or denials of a different proposition (34)

| argument | premise | conclusion |
|---|---|---|
| `e1d0d14b` | Some actual CONCRETE_AND_ABSTRACT_6 being is CONTINGENT_1 | Not every actual concrete being is NECESSARY_2 |
| `5758bd1a` | A candidate edge to the selected whole exists but no causer of that whole exists at the se | Exact negation of the selected-whole-causer actuality policy |
| `ba2e49db` | A natural-knowability move answers to shared reason and another natural-knowability move d | Both uniform interpretations fail: not every natural-knowability move is shared, and it is |
| `e91ac9e8` | A selected-world no-esse capacity/productive countercase exists but none of the named prod | Exact negation of the explicit named-case coverage hypothesis, not an unspecified claim th |
| `5c6e8ef2` | A substantive descriptive-role objection: an actual selected religious sentence does not r | Exact failure of the supplied local content/assertion/fact/truth characterization |
| `a0230833` | A supplied method answers opposite truths correctly | Blanket formation insensitivity fails for the supplied states |
| `31be64a6` | An actual defined move is endorsed by the practice own standards and another actual define | Both uniform endorsement profiles fail: not all defined moves are endorsed and it is not t |
| `50c3aee7` | An actual selected religious sentence has the same apparent content assigned in both disco | Exact negation of the stronger analyst local-plus-invariant profile, on the same… |
| `1ed3a9ca` | An actual selected religious sentence has the same apparent content assigned in both disco | Exact negation of matched-content religious truth invariance on the same supplied profile |
| `24c24419` | An actual supplied union/communication/same-act tuple fails canonical reception for the SA | The universal same-act communication-to-canonical-reception transfer fails in this profile |
| `e393076d` | An in-scope cognitively meaningless content has a negation that does not entail some obser | V2 fails to calibrate the supplied cognitive-meaning predicate on the supplied scope |
| `4a87de05` | Each being can not-be, yet common absence is not possible under the SAME supplied semantic | Exact negation of the original AllCanNotBeThenNothingPossibleReading on the SAME profile |
| `ecc4dc17` | Exact failure of the supplied local content/assertion/fact/truth characterization | Exact negation of the two-profile local comparison menu, not of all philosophical… |
| `9dcd13c2` | Jesus gave or promised none of the powers in the unchanged governing table | Exact negation of commission reports go back to jesus on the same Commissioning: not both… |
| `6731cbe4` | Some POTENCY_3 capacity is retained while exercised | Not everything in act in a respect lacks the POTENCY_3 capacity for it |
| `cba6df93` | Some actual moved tuple is not in POTENCY_1 in the SAME respect under the supplied… | Exact negation of the original moved-only-as-in-POTENCY_1 universal in the SAME dictionary |
| `25f9d224` | Some actual opiner of a supplied content is not moved in the SAME asOpinion respect demand | Exact negation of the old OpiningIsBeingMovedReading under the SAME MovedIn, Opines and as |
| `2212f5d4` | Some being before which nothing is in time is in POTENCY_1 in some respect, as in the Nigh | The temporal branch fails: it is not the case that whatever is in POTENCY_1 in a respect h |
| `34cc3a4b` | Some candidate accepted by the supplied judgment is false at the designated arrangement | Exact negation of the old CompleteRequiresSelection on the SAME arrangement and supplied a |
| `de596c5f` | Some candidate accepted by the supplied judgment is false at the designated arrangement | Exact negation of the accepted-candidate truthfulness policy under the SAME arrangement an |
| `7bdd5abb` | Some noncognitive member broadly tends to an end while no knowing intelligent member direc | The existing universal noncognitive-tending-needs-knowing-director principle fails under t |
| `1d2e3da4` | Some single admitted quality has n pairwise numerically distinct Forms for every natural n | Numerical uniqueness of the Form for each admitted quality fails in this interpretation |
| `7107a1f5` | Some subject causes a perfection in itself, as a subject causes its proper accidents from  | The perfection branch fails: it is not the case that nothing causes a perfection in itself |
| `a78824b0` | Some supplied reasoning method clears the finite benchmark | Blanket finite benchmark unreliability fails |
| `0a86321b` | Something changes, in the general sense of CHANGE_2: some thing changes in some characteri | McTaggart's bundle on change does not hold: it is not the case both that no event changes  |
| `6b221edc` | Strong version: for every sentence, if it is meaningful, so is its negation | For any frame and meaningfulness predicate closed under negation, the V3 package fails |
| `4c359d1d` | The interpretation of the designated logical sentence holds under every endorsement profil | The strong global profile-variation thesis fails for the supplied interpretation |
| `8e216377` | There are epistemic reasons: some agent has an epistemic reason to believe some content | Thin global epistemic nihilism fails |
| `32b3030e` | Weak version: for every sentence, if its negation is meaningful, so is its double negation | For any frame and meaningfulness predicate closed under negation, the V1 package fails |
| `13f3a07e` | Über Gewißheit §341: whenever something is doubted, some sentence is exempt from doubt | Universal doubt does not hold: whoever wanted to doubt everything would not get as far as  |
| `d516346b` | At the same designated arrangement a and supplied complete-explanation judgment, some acce | Exact negation of the old CompleteRequiresSelection on the SAME arrangement and supplied a |
| `29a12596` | No meaningful content is about God or the higher under one supplied semantic profile | The exact meaningful-divine-arguability proposition fails under this same semantic/argumen |
| `6a48955d` | The account offers its habit forecast as epistemically entitled | The blanket entitlement-denying reconstruction fails under the explicit premises of the re |
| `26471216` | Half an altering or growing agent may cause no alteration or growth at all: in some case t | No proportional effect of half an altering or growing agent is guaranteed: it is not the c |

## Not registered: consequences with further reasoning or new content (50)

| argument | premise | conclusion |
|---|---|---|
| `ff07829e` | A society counts as founded by GOD_4 as a teaching authority exactly when the supplied… | In the supplied profile, the existing envoy-founding bridge is equivalent to each Jesus-en |
| `c0be361f` | Any two distinct things are comparable in being | A MAXIME_1 (maximal) being is MAXIME_3 (strictly greatest) in being |
| `36a3a382` | At every world modally accessible from actuality, knowledge of the selected Moore conjunct | The selected Moore conjunction cannot be known at any world modally accessible from actual |
| `1fe8fd6f` | Being more in any perfection is asymmetric | A MAXIME_3 (strictly greatest) being is MAXIME_1 (maximal) in being |
| `4271912d` | Each graph node has at most one immediate upstream predecessor | Any two finite upstream paths starting at one node can be extended upstream to a common no |
| `b71e8264` | Every in-scope target has the explicit OBSERVATION_INDISTINGUISHABILITY_BARRIER_6 | No target in the independently supplied scope has a finite satisfiable observation proof |
| `7651bcd6` | Every located set representative has a located representative of an actual strict member… | Every right-summand pure-set representative is unlocated in the supplied frame |
| `857ce9c1` | Every performed doubt whether thought occurs is realized by an occurring thought episode | Every performed doubt that any thought occurs makes its doubted content false |
| `afb096de` | For every x,y in the supplied fixed partial order, when y is not part of x an exact remain | Whenever x is not part of y, some part of x is disjoint from y, in the same supplied Mathl |
| `45f01fbb` | For every x,y in the supplied fixed partial order, when y is not part of x an exact remain | For every nonempty family and every candidate u, Mathlib IsLUB family u iff the existing S |
| `74c5fd65` | For the supplied family of Ontic interpretations, selected standpoint in each and arbitrar | The supplied arbitrary measure assigns equal values to the event that a bare NecessaryBein |
| `3b5b2cc4` | Ground edges strictly increase a natural-number rank | No explanatory Ground edge has its reverse |
| `abdb4f08` | Grounding stability bridge | Grounding candidate entails intervention candidate |
| `820b7701` | If y is SIMPLY_PRIOR_1 to x, then x depends for its being on y and y does not so depend on | Nothing is prior to itself |
| `468b4523` | Inside each world, the existing individuals with that world's Causes edges form an acyclic | Every actual individual in each world has a finite upstream path to an existing source or  |
| `d5dc4a7f` | Inside each world, the existing individuals with that world's Causes edges form an acyclic | In every world with a finite actual carrier, each actual individual has its own finite ups |
| `cea31899` | Joint model for the stated local theory | Joint theory does not entail falsum |
| `16b2cead` | Moral statements have no truth value: they are not the kind of sentence that can be true o | No moral disagreement is a genuine contradiction: no one accepts and another rejects a mor |
| `f9d6b089` | Moral statements have no truth value: they are not the kind of sentence that can be true o | No one is ever in error about a moral matter: no one accepts a moral sentence that has a t |
| `4a020329` | N1, EXISTENCE_NATURALISM_1: at the selected world, everything that exists satisfies the th | Under occupant N1 in the explicitly constructed immanent-location frame, every existing… |
| `1563063f` | No predicate both holds and fails of the same being in the same respect | In the adopted sense POTENCY_1 to a respect is capacity for that respect without actually  |
| `48d5e591` | Part-mediated event has a local patient-lifting bridge | Part-mediated internal motion has a distinct whole mover under lifting |
| `17a1ceab` | Possibly, every contingent concrete thing comes to be in a history whose past has a beginn | Possibly, contingent concrete things are absent at a moment and present at a later one |
| `43543f14` | Possibly, every contingent concrete thing comes to be in a history with a founded past | Possibly, contingent concrete things are absent at a moment and present at a later one |
| `bbbbdfc6` | Some actual CONCRETE_AND_ABSTRACT_6 being is CONTINGENT_1 | No act done at every accessible world strictly yields every actual concrete being |
| `65880bb6` | Some actual CONCRETE_AND_ABSTRACT_6 being is CONTINGENT_1 | The route's world is not modally collapsed (some truth there is not NECESSARY_2) |
| `d9df15d3` | Some occurring intense suffering could be prevented by any omniscient omnipotent being wit | In the supplied Rowe frame, existence of an omniscient, omnipotent, wholly good being woul |
| `9f2b1c6c` | The existing Escape cut principle holds for the recorded actual-CONCRETE_6 existential-gro | The nonempty whole actual CONCRETE_AND_ABSTRACT_6 roster is not a borrowing trap |
| `4387e732` | The existing union of selected world-local existential-support arrows between necessary co | Some rigid grade with no infinite ascent is ascended by support between NECESSARY_2 concre |
| `676f4cc7` | The profile's selected relation at w, restricted to candidates that are CONCRETE_6 and exi | Some rigid grade with no infinite ascent is ascended by actual concrete grounding |
| `beea9a72` | The rigidly necessary subtype is finite and nonempty; no actuality of this background is a | The union restricted to necessary individuals has a source or a nonempty directed TransGen |
| `aeef6604` | The selected governing predicate on the existing nine powers matches the unchanged fixed… | The original fixed narrow institutional bridge holds iff the selected-criterion bridge hol |
| `fb9440bd` | The selected governing predicate on the nine-power carrier includes the power to teach | The selected governing predicate does not coextend with the fixed narrow table |
| `95c5d052` | The selected grounds relation restricted to the subtype of all actual CONCRETE_6 ancestors | Instantiate the existing ExplanatoryAdequacy.Founded predicate on the positive-existence a |
| `8542e377` | Truth tracks being, and greater truth tracks greater being | Whatever is maximally TRUE_1 is maximally a being |
| `92539fa2` | Two interpretations have coextension, extensionally matching independently specified base… | Two interpretations agree on F-exemplification for every common admitted quality, common F |
| `8bbe817d` | Whatever causes a quality in another thing is more such than that thing | Every maximum in being excludes a distinct cause of its being in the existing CausesIn rel |
| `665d4017` | Whatever gives a thing being at a moment is present at that moment | Whatever CAUSE_OF_BEING_2 sustains every other thing is present to each whenever it is |
| `ab3f4165` | Whatever is GOD_4 and has the classical attributes asserts only what he believes and belie | Whatever is GOD_4 and has the classical attributes asserts only what he holds as known |
| `87f32a9c` | Whatever is more a being than m has a higher represented degree of being | A MAXIME_2 (greatest-degree) being is MAXIME_1 (maximal) in being |
| `edd8651b` | Whenever an actual concretum a grounds an actual concretum b at w, a is more in esse than  | For actual concreta a,b at the selected world, if b is maximal in the SAME supplied esse… |
| `93cfbafa` | Whenever x is not part of y, some part of x is disjoint from y, in the same supplied Mathl | For every family and candidate in this fixed partial order, the existing Sum2 Fusion predi |
| `5cc78212` | Disjunction of the explicit set, Form or mathematical selected-world productive/no-esse co | At the selected world one candidate lacks esse in re and either possesses causal power or… |
| `392cb64b` | Intuitionism: excluded middle is not a law of logic. p ∨ ¬p may be asserted only when a pr | The supplied stage-indexed assertion policy does not assert every excluded-middle instance |
| `08dba28f` | What comes to be anew takes its origin from some INNOVATING_CAUSE_4 other than itself, sin | Anything that comes to be has some distinct CAUSE_2 |
| `91a56014` | Any proposed first divisible interval of changing contains a proper subinterval in which c | There is no first extended time in which changing begins |
| `fafc7d2c` | Any proposed first interval of coming to rest is self-defeating: if divisible, cessation a | There is no first extended interval in which coming to rest begins |
| `e6f32278` | Sameness or difference of alteration tracks the affection, while equality or inequality tr | Under the two-factor comparison criterion, the same affection in equal affected amounts yi |
| `03415af9` | An endless populated past would admit a Grim Reaper system of locally ruled stations | In every possible history, each moment with a contingent concrete thing present has a foun |
| `4e8e50bb` | Founded as a teaching authority coextends with direct principal founding or Jesus founding | For any GOD_4 candidate g and society c: if Jesus founded c in the primitive FoundedInMand |
