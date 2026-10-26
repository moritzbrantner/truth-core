# Is being a genus? (issue #340)

The *quarta via* (ST I q.2 a.3) says that what is maximal "in aliquo genere" causes everything in that genus, and it applies this to being. Aristotle (*Metaphysics* III.3, 998b22-27) and Aquinas (ST I q.3 a.5) say that being is not a genus. This note records what the first batch established, which readings were rejected and why, and what remains open.

## Sources pinned and read

| Passage | Locator | Witness |
|---|---|---|
| `ARIST-MET-III-3` | *Metaphysics* III.3 (998a20-999a23) | Perseus `tlg0086.tlg025.perseus-grc2`, existing snapshot |
| `ARIST-MET-IV-2` | *Metaphysics* IV.2 | same snapshot |
| `AQUINAS-ST-I-Q3-A5` | ST I q.3 a.5 | SCTA TAca84, `TAca84-d1e61-Dd1e1139` |
| `AQUINAS-ST-I-Q13-A5` | ST I q.13 a.5 | SCTA TAca84, `TAca84-d1e113-Dd1e1221` |

## What is proved (Lean, no axioms)

- `ARIST-MET-998B-BEING-NOT-A-GENUS`: every genus has a differentia, every differentia is a being, and a genus is not said of its own differentiae. So being is not a genus in the strict sense. The proof is a three-step reductio over typed predication: terms, `IsGenus`, `DifferentiaOf` and essential predication `SaidOf`. Each premise has an omission countermodel.
- `AQUINAS-ST-I-Q3-A5-GOD-IN-NO-GENUS`: imports the Aristotle theorem. Whatever God were properly in would be a genus, and it would be being, so God is properly in no genus. Each Aquinas premise has an omission countermodel.
- `QUARTA-VIA-STRICT-GENUS-READING-FAILS` (countermodel): take "genus" in the genus principle strictly and add Aristotle's premises. The *quarta via* then does not reach a cause of being, even though the model has a real strict genus and the principle holds there.
- `QUARTA-VIA-BROAD-GENUS-COMPATIBLE-WITH-BEING-NOT-A-GENUS` (model): take "genus" broadly, as any perfection. Then the whole *quarta via* (premises and conclusion) and Aristotle's premises hold together.

The objection that being is not a genus is recorded as an `attacks` relation on `STMT-MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS`. It succeeds only against the strict reading. The broad reading, which the corpus formalization already used, survives it. This does not make the premise true: it stays open.

## Readings chosen and rejected

- **"Genus" in the *quarta via* (`DISAMB-GENUS`).** The strict reading is rejected as Aquinas' meaning, for four reasons:
  1. the example, heat, is a quality and not a strict genus of hot things;
  2. the principle is applied to being, which Aquinas says is no genus;
  3. q.3 a.5 ad 2 gives grades of being by approach to God, without a common genus;
  4. Aristotle's 999a6-14 says there is no genus over things ordered as better and worse.

  The strict reading is kept only as a formal contrast (`MaximumInStrictGenusCausesAllInGenusReading`) and has no claim.
- **Predication of the differentia (`DISAMB-PREDICATION-OF-DIFFERENTIA`).** Both premises use essential predication. If "being is said of every differentia" held only as a true but non-essential attribution, the argument would equivocate. Aquinas' "extra essentiam generis" and "extra ens" read the two premises in the same sense.
- **καὶ εἶναι (998b23).** We read it as predicative ("each differentia is a being"), fixed by the conclusion at 998b26-27. The existential reading ("differentiae exist") is not used. The existence of a differentia is taken from Aquinas' "omne genus habet differentias".
- **The status of Book III.** 998b22-27 is one side of an aporia. The claims attribute the argument as stated there. Aquinas takes it as Aristotle's demonstration.
- **God-form of the q.3 a.5 premise.** "If God were in a genus, his genus would be being" is stated for God only. Generalizing it to every being whose esse is its essence would strengthen the sentence, so it was not done.

## Order models of more and less in being (second batch)

`TruthCore/Latin/Aquinas/SummaTheologiae/PrimaPars/Question2/Article3QuartaViaOrder.lean` gives each sense of `DISAMB-BEING-UNIVOCITY` an order model in Mathlib's order theory (`DISAMB-ORDER-OF-BEING`):

- **Univocal: a homogeneous scale** (`HomogeneousScaleReading`, `DEF-HOMOGENEOUS-SCALE`, stipulative). There is one `Preorder` on the beings, and every being has being. `x` is more a being than `y` exactly when `y < x`. A maximum is a maximal element (`IsMax`) of the one scale.
- **Attribution: approach to a primary** (`ApproachToPrimaryReading`, `DEF-ORDER-BY-APPROACH-TO-A-PRIMARY`). The source is q.3 a.5 ad 2, claim `AQUINAS-ST-I-Q3-A5-AD2-APPROACH-ORDER-A`. `x` is more a being than `y` exactly when `x` approaches the primary `p` more nearly (`near y < near x`, with degrees in their own preorder). Nothing more is attributed to the sentence.
- **Strict primacy** (`StrictPrimacyReading`, `DEF-STRICT-PRIMACY`, open premise `STMT-NOTHING-ELSE-REACHES-THE-PRIMARY`). Everything other than `p` falls short of it: nothing ties with the primary. No claim attributes it; q.3 a.5 ad 2 does not say it (see below). Results that need it take it as a separate hypothesis.
- **Causal order to the primary** (`OrderedToPrimaryAsCauseReading`). The source is q.13 a.5 co., *ordo creaturae ad Deum, ut ad principium et causam*, claim `AQUINAS-ST-I-Q13-A5-ORDO-AD-CAUSAM-A`. The primary causes being in every creature (`DEF-CREATURE`). That everything other than the primary is a creature is a further open premise with no claim (`OthersAreCreaturesReading`, `STMT-OTHERS-THAN-PRIMARY-ARE-CREATURES`). Aristotle's *pros hen* (IV.2) does not give this: there the relation to substance may also be affection, way, privation, and so on.

The two models can have the same order shape. When every represented being has the perfection (`∀ x, InAct x r`), an attribution order is a homogeneous scale for the preorder pulled back along `near` (`ApproachToPrimaryReading.homogeneousLift`). This universal possession condition is additional: `ApproachToPrimaryReading` itself requires only the primary to have the perfection. Strict primacy and the causal clause are further separate premises. For #341, this means that order shape alone (Preorder, IsMax, IsGreatest) cannot encode analogy.

### Verdicts

| Frontier premise | Homogeneous scale (univocal) | Attribution order |
|---|---|---|
| `STMT-MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS` | No support from the order, but consistent with it (`QUARTA-VIA-HOMOGENEOUS-SCALE-GIVES-NO-CAUSE-OF-BEING`). It stays open. | **Survives at being, re-read.** Its instance at being is *derived* from the order by approach, strict primacy, the causal order of creatures, the creature premise and excluded middle (`QUARTA-VIA-ATTRIBUTION-GENUS-PRINCIPLE-AT-BEING`). Omission countermodels show that strict primacy, the causal order and the creature premise are each needed. Strict primacy and the creature premise are open and unattributed, so the instance stays open. The principle for other perfections stays open. |
| `STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH` | This is its source sense: Met. II.1 speaks of the *synonymous* quality (τὸ συνώνυμον, 993b25). Consistent with the scale; it stays open. | **Needs re-reading.** It holds with the primary as cause and fails in general (`QUARTA-VIA-ATTRIBUTION-RESTRICTS-CAUSE-MORE-SUCH`). |
| `STMT-MAXIMUM-IN-BEING-IS-FIRST-BEING` | Not yielded. | Not yielded, even with strict primacy, the causal order, the creature premise and `STMT-SIMPLY-PRIOR-IS-CAUSE-OF-BEING` (`QUARTA-VIA-ORDER-READINGS-DO-NOT-YIELD-FIRST-BEING`). With strict primacy the maximum is the primary, so the bridge reduces to: nothing other than the primary is simply prior to it. |

A byproduct for uniqueness (#320): on the attribution order, there is at most one maximum in being. This follows from the order by approach, strict primacy and explicit excluded middle (`QUARTA-VIA-ATTRIBUTION-UNIQUE-MAXIMUM`), without the genus principle or Met. II.1. A countermodel with tied degrees shows that strict primacy is needed. Since strict primacy is an open premise, uniqueness stays open on this route.

### Where an equivocation sits

The existing routes use `STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH` in two ways, and the two fare differently on the attribution order:

- **The primary as cause**, in `AQUINAS-ST-I-Q2-A3-AT-MOST-ONE-MAXIME-ENS`, where a maximum causes another's being. This use holds in the attribution sense, so this route does not equivocate.
- **The primary as effect**, in `AQUINAS-ST-I-Q2-A3-FIRST-MOVER-IS-FIRST-BEING`, where whatever is simply prior to the maximum causes its being and so would be more a being. This use is not derivable on the attribution order. Its synonymous sense is not available at being either: q.13 a.5 (arg. 1 and ad 1) denies that the first agent is a univocal cause, since the sun causes heat without being hot except equivocally. This use equivocates unless it gets its own source.

Candidate `ARIST-MET-993B-PRINCIPLES-UNCAUSED-IN-BEING` records a possible source: Met. II.1, 993b28-30, "nothing is a cause of being to the principles of the eternal beings". The clause was read in the materialized `ARIST-MET-II-1`; no claim has been made on it yet.

### Readings chosen and rejected (second batch)

- **Rejected: strict primacy as a reading of q.3 a.5 ad 2.** An earlier draft of this batch read it from *appropinquat* and *non est mensura proportionata*. The sentence relates degrees of being to approach and denies that God is a proportioned measure; it does not say that nothing other than God reaches God's degree. Since the omission countermodels show that exactly this clause yields uniqueness and the genus principle at being, it cannot be carried by a reading choice. It is now the open premise `STMT-NOTHING-ELSE-REACHES-THE-PRIMARY` with no claim. Places read for a source, orientation only and without passage records yet (candidate `AQUINAS-STRICT-PRIMACY-IN-BEING`): ST I q.4 a.3 ad 1 and ad 3 (creatures fall short of their cause; God is *ens per essentiam, et alia per participationem*), SCG I.28 [2]-[4] (God has being according to its whole power, other things participate it in a particular mode), SCG I.42 [2] (what is said by superabundance is found in only one being). Each speaks of creatures or of what participates, so the identity-sensitive form would also need the creature premise or a participation premise.
- **"Ordo ... ut ad causam" read as `CausesIn p x r`, for creatures.** The sentence grounds the community of the name in an order of the creature to God as to its principle and cause, and the article's example of this mode is medicine as *causa sanitatis quae est in animali*. So the causal relation is stated; the reading choice is only the sense of cause (`DISAMB-CAUSE`). The sentence speaks of creatures, not of everything other than God, so the claim is restricted to creatures and the step to every other being is the separate open premise `STMT-OTHERS-THAN-PRIMARY-ARE-CREATURES` (a source might be ST I q.44 a.1). Only the instance at being is used. The many-to-one mode of analogy (urine and medicine to health) is not formalized; the article assigns God and creatures to the one-to-another mode.
- **Rejected: attribution as order shape alone.** A primary that is merely greatest (`IsGreatest`) is rejected as a model of strict primacy, because then a tie is possible, and neither uniqueness nor the genus principle at being follows. This shows what strict primacy adds; it does not source it, which is why it is an open premise. A preorder alone is rejected as well, because it cannot distinguish the senses at all (`homogeneousLift`).
- **Rejected: Aristotle's *pros hen* as the causal order.** IV.2 lists affections, ways, privations and producers of substance, so the relation to the primary is not only causal. The causal clause is sourced from q.13 a.5, not from IV.2.
- **Not decided: attribution vs proportionality.** Cajetan and Suárez are orientation only. Nothing pinned decides between them, and the order models do not either.

## Remaining obligations

1. **Order models (issue item 3).** Done in the second batch; see above. Still open: making the existing routes use the instance at being (`STMT-MAXIMUM-IN-BEING-CAUSES-ALL-BEINGS`) or the attribution route to uniqueness, and sourcing the primary-as-effect use of Met. II.1. Both are for #341, which can reuse `HomogeneousScaleReading`, `ApproachToPrimaryReading`, `StrictPrimacyReading` and their lemmas (`isMaximumIn_primary`, `eq_of_isMaximumIn`, `StrictPrimacyReading.isGreatest`, `homogeneousLift`, `OrderedToPrimaryAsCauseReading.causesAllInGenus`). Also open: sourcing strict primacy (candidate `AQUINAS-STRICT-PRIMACY-IN-BEING`) and the creature premise.
2. **The rest of ST I q.3 a.5.** Still to formalize: the first proof (a differentia stands to its genus as act to potency), the third proof (things in one genus differ in esse), and not being in a genus *per reductionem* as a principle (God is principle of all esse). The third proof would connect to `STMT-FIRST-UNMOVED-MOVER-IS-SIMPLE`.
3. **Composition onto the root path.** A first-mover version of `STMT-GOD-IN-NO-GENUS` would need the simplicity result plus a generalized and separately sourced esse-essence premise.
4. **Unformalized sourced commitments.** `STMT-NO-GENUS-OVER-PRIOR-AND-POSTERIOR`, `STMT-BEING-SAID-PROS-HEN`, `STMT-DIVINE-NAMES-ANALOGICAL` and `STMT-BEING-FIRST-ANALOGICAL-PREDICATE` are claims without Lean declarations. Whether ST I q.13 a.5 is analogy of attribution or of proportionality (Cajetan or Suárez) is not decided. Those authors are orientation only until pinned.

## Periodic Audit A, round 2 (2026-10-26, #410)

The audit compared main after #392 (`759082ee`) with #422
(`fb944bec39ee1f54adc8051a6fd8c27ae69cd365`). It covered the changed Latin
modules, the root wording, their statements, claims, arguments, results,
definitions and disambiguations, and the root dependencies discussed above.
The shared convention stack resolved at source revision
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`.

Two premise omissions in prose were corrected without changing any Lean type
or proof. First, `homogeneousLift` requires universal possession
`hAll : ∀ x, InAct x r`, while the earlier summaries said an attribution
reading was unconditionally a homogeneous scale. For example, take two
individuals, let only the primary have `r`, and compare them by their degrees:
`ApproachToPrimaryReading` holds but `HomogeneousScaleReading` fails its first
conjunct. The order-shape observation survives with the additional condition.
Second, the uniqueness and genus-at-being summaries now name the explicit
excluded-middle premise used by `eq_of_isMaximumIn`. Their argument and
inference records already listed that premise correctly. The old q.75
non-bodyhood note's next-step paragraph was also advanced to the remaining
per-se-operation and subsistence passage.

### Materialized source-fidelity sample

The following claims were reread in freshly materialized pinned witnesses,
including the surrounding argument. These are source-reading judgments,
not conclusions from Lean or source hashes.

| Claim | Passage and precise locator | Audit reading |
| --- | --- | --- |
| `AQUINAS-ST-I-Q3-A4-ESSE-CAUSE-DICHOTOMY` | `AQUINAS-ST-I-Q3-A4`, co., first proof, *si igitur ipsum esse rei* | Two causal options for distinct esse; not an unrestricted explanatory PSR. |
| `AQUINAS-ST-I-Q3-A4-ESSE-NO-SELF-CAUSE` | Same, *impossibile est autem quod esse sit causatum tantum* | Essential principles alone cannot sufficiently cause their subject's caused esse; contributory or noncausal reasons are not excluded. |
| `AQUINAS-ST-I-Q3-A4-DISTINCT-ESSE-EXTERNAL-CAUSE` | Same, *oportet ergo quod illud cuius esse* | Conditional external-cause conclusion; no converse or conservation thesis. |
| `AQUINAS-ST-I-Q3-A5-AD2-APPROACH-ORDER-A` | `AQUINAS-ST-I-Q3-A5`, ad 2, *tantum habet de esse, quantum ei appropinquat* | Order comparison is an explicit selected reading; strict primacy is kept separate. |
| `AQUINAS-ST-I-Q13-A5-ORDO-AD-CAUSAM-A` | `AQUINAS-ST-I-Q13-A5`, co., *ordo creaturae ad Deum, ut ad principium et causam* | Causal order concerns creatures; all non-primary individuals being creatures remains an additional open premise. |
| `AQUINAS-ST-I-Q75-A2-UNIVERSAL-BODILY-COGNITION` | `AQUINAS-ST-I-Q75-A1-A2`, co., anchor 31460, *cognoscere potest naturas omnium corporum* | Distributive capacity for bodily natures, not simultaneous omniscience. |
| `AQUINAS-ST-I-Q75-A2-BODILY-DETERMINACY` | Same, *omne autem corpus habet aliquam naturam determinatam* | Some constitutive nature for each body; no uniqueness. |
| `AQUINAS-ST-I-Q75-A2-NATURAL-BODILY-INTERFERENCE` | Same, *si igitur principium intellectuale haberet in se naturam* | Open interference conditional; the sensory illustration is not a proof of its universal application. |
| `AQUINAS-ST-I-Q75-A2-INTELLECT-NOT-BODY` | Same, *impossibile est igitur quod principium intellectuale sit corpus* | First subconclusion only, without organ independence or subsistence. |
| `AQUINAS-ST-I-Q75-A2-ORGAN-BODILY-INTERFERENCE` | Same, *natura determinata illius organi corporei prohiberet* | A separately stated organ-level interference commitment. |
| `AQUINAS-ST-I-Q75-A2-INTELLECT-NONORGANIC` | Same, *impossibile est quod intelligat per organum corporeum* | No bodily instrument of exercise; ad 3, anchor 31463, retains object-side bodily dependence. |
| `PASNAU-Q75-COGNITIVE-PLASTICITY-REPLY` | `PASNAU-MIND-HUMAN-NATURE-353-357`, p.355 | The taste/sight examples do not establish either interference premise; pp.356–357 address a distinct universal-concept argument. |
| `VATICAN-I-DEI-FILIUS-CH3-CHURCH-GOD-FOUNDED-TEACHER` | `VATICAN-I-DEI-FILIUS-CH3`, paragraph beginning *Quoniam vero sine fide*, *Deus per Filium suum unigenitum Ecclesiam instituit* | The weak phase-1 existential wording does not add uniqueness. |

The q.75 context also included the full materialized `AQUINAS-ST-I-Q76-A1`,
especially ad 1, anchor 31513, which retains soul-as-form while distinguishing
non-organic intellectual exercise. `AQUINAS-ST-I-Q2-A3` and
`ARIST-MET-II-1` were also materialized and reread: q.2 a.3 retains the broad
perfection reading of genus, while 993b24–26's synonymous-quality condition
keeps the primary-as-effect use an explicitly recorded outstanding gap.

### Proof acceptance, reuse and remaining gaps

- `distinctEsseExternalFromExhaustion` eliminates the essential-cause fork
  using its explicit negation and retains the external fork. This is accepted
  only as the conditional transcription already flagged `assembly`; both
  causal premises remain open. Its finite controls certify schema witnesses,
  not metaphysical possibilities.
- `attributionOrderGenusPrincipleAtBeing` identifies a maximum with the primary
  using approach, strict primacy and excluded middle, then applies the causal
  clause through the creature premise. `attributionOrderUniqueMaximum` uses
  that same identification twice. These consequences are accepted with all
  listed premises; neither strict primacy nor the creature premise is sourced
  by the order lemma. The countermodels and restricted cause-more-such result
  retain the limitations recorded above.
- `intellectIsNotBody` and `intellectUsesNoBodilyOrgan` use the bodily-nature
  witness and the appropriate interference conditional to contradict the
  explicit universal capacity. These are typed reductios rather than opaque
  transcriptions. No inference from non-bodyhood to organ independence is
  advertised. The reused Model and cognitive/determinacy vocabulary coincide;
  the distinct organ relation is necessary. Subsistence, the defense of both
  interference premises and an affirmative rival account remain open.
- The changed root wording matches its existential type and the linked
  phase-1 definition. The skeleton's opaque bridge content remains open and
  is not established by the wording correction.

The reviewed definition/disambiguation links resolve and explain these uses.
No additional missing-link finding was identified in this bounded scope;
#216 remains the broader coverage task. The order models use Mathlib
`Preorder`, `IsMax`, `IsGreatest` and `Preorder.lift`, rather than substitutes.
No duplicate theorem or vocabulary requiring replacement was identified.

Intended and actual premise comparison: **no change**. No theorem, Challenge,
statement identity, argument premise list, transcription flag or root route
is changed. The eight root-route costs remain 28, 29, 33, 35, 36, 36, 37 and
38; the designated route retains 37 open leaves. This audit corrects what the
prose claims, and discharges no philosophical obligation.
