# Load-bearing terms on root paths and their sense forks

Audit of 2026-11-07 (owner direction: "have different theories for a term and
then use this exhaustive enum stuff to say that ONE OF THEM must apply").
Analyst work, attribution deferred.

## Method

1. `python3 scripts/corpus.py frontier --json --reaching-root` gives the
   statements that reach `STMT-CATHOLICISM-TRUE` (353 on the audited head).
   Root-path arguments are the arguments whose conclusion is one of them (201).
2. For each such statement and argument, collect `definition_ids` and
   `disambiguation_ids`; a definition reaches every disambiguation that lists it
   in `sense_definition_ids`. 128 disambiguations are reached.
3. A **fork exists** for a disambiguation when a verified result case-splits
   over its senses, or when `strengthens`/`refutes` relations connect
   statements that use two different senses. Before this PR no root-path
   disambiguation had a case-splitting result; five had one or two relations
   between sense-using statements and none a full fork (DISAMB-GOD, DISAMB-Q14-RECEPTION-SENSES,
   DISAMB-ACTUAL-VS-WHOLE-CARRIER-WF, DISAMB-CONCRETE-ABSTRACT-CRITERIA and
   DISAMB-PER-SE-LINK).
4. **Coverage** and **exclusivity** statements (owner refinement) are the
   statements with suffixes `-SENSES-EXHAUSTIVE` and `-SENSE-UNIQUE` bound to
   a Lean declaration over the term's sense enum.
5. Impact ranks by the number of root-path arguments linking the term
   (directly or through a sense definition), then root-path statements. A
   term's counts include sense definitions shared with other disambiguations,
   so related cause terms overlap.

The reusable script that produced the counts is not committed (temporary
analysis); `truth orphans --senses` (PR #1229) computes the same coverage.

## Ranked table (top 40 of 128)

"Step depends" says whether a root-path step changes validity or premise truth
with the sense; "silo" means every result fixes one predicate and the record
says no step passes between senses (the premise's truth then depends on the
sense, its validity not).

| # | Disambiguation | Term | Senses | Root args | Root stmts | Step depends on sense | Fork | Coverage stmt | Exclusivity stmt |
|---|---|---|---|---|---|---|---|---|---|
| 1 | DISAMB-CAUSE | cause | 4 | 80 | 68 | yes: secunda via self-causation; simple priority → cause of being | **certified (this PR)** | STMT-CAUSE-SENSES-EXHAUSTIVE | STMT-CAUSE-SENSE-UNIQUE |
| 2 | DISAMB-UNITING-CAUSE | uniting / efficient / cause of being | 4 | 65 | 52 | yes: STMT-UNITING-CAUSE-IS-EFFICIENT passes between senses | **certified (batch 2)** | STMT-UNITING-CAUSE-SENSES-EXHAUSTIVE | STMT-UNITING-CAUSE-SENSE-UNIQUE |
| 3 | DISAMB-BECOMING-BEING-CAUSE | causing an effect (becoming vs being) | 3 | 53 | 39 | no root step (counts via shared DEF-CAUSE-OF-PERFECTION) | not forked, see below | no | no |
| 4 | DISAMB-UNITING-CAUSE-ACTUALITY | cause-in-esse vs world-local edge | 3 | 52 | 38 | no root step (counts via shared DEF-CAUSE-OF-PERFECTION); interfaces, not rival readings | not forked, see below | no | no |
| 5 | DISAMB-ARISTOTLE-H6-UNITY-AND-CAUSATION | unity, form, cause | 5 | 52 | 38 | comparison only | no | no | no |
| 6 | DISAMB-IN-ACT | in act (formally / virtually) | 2 | 51 | 31 | yes: two uses in the prima via step must agree | **certified (batch 2)** | STMT-IN-ACT-SENSES-EXHAUSTIVE | STMT-IN-ACT-SENSE-UNIQUE |
| 7 | DISAMB-MAXIME-ENS | maximal in being | 6 | 50 | 24 | weakest sense chosen; strength order natural | **certified (batch 3)** | STMT-MAXIME-SENSES-EXHAUSTIVE | STMT-MAXIME-SENSE-UNIQUE |
| 8 | DISAMB-PER-SE | per se | 4 | 46 | 9 | silo (distinct predicates) | not forked: homonyms (batch 3) | — | — |
| 9 | DISAMB-GOD | God | 6 | 42 | 29 | yes: naming premise | **certified (batch 4)** | STMT-GOD-SENSES-EXHAUSTIVE | STMT-GOD-SENSE-UNIQUE |
| 10 | DISAMB-POTENCY | potency / capacity / power | 5 | 42 | 21 | adopted configurations fix one | **certified (batch 3)** | STMT-POTENCY-SENSES-EXHAUSTIVE | STMT-POTENCY-SENSE-UNIQUE |
| 11 | DISAMB-RECEPTIVE-POTENCY | receptive vs unactualized potency | 2 | 40 | 19 | yes (esse reception) | not forked: distinct Lean types (batch 3) | — | — |
| 12 | DISAMB-PRIORITY-SIMPLE-OR-IN-TIME | prior | 3 | 40 | 16 | yes: act's priority over potency | **certified (this PR)** | STMT-PRIOR-SENSES-EXHAUSTIVE | STMT-PRIOR-SENSE-UNIQUE |
| 13 | DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER | in potency / mutable | 3 | 38 | 17 | yes: immutability | **certified (batch 4)** | STMT-MUTABILITY-SENSES-EXHAUSTIVE | STMT-MUTABILITY-SENSE-UNIQUE |
| 14 | DISAMB-MUTABILITY-CHANNEL | potency and mutability | 2 | 38 | 17 | yes: immutability | duplicate of #13, covered there (batch 4) | — | — |
| 15 | DISAMB-MARK-HIGH-PRIEST-EXCHANGE | reported exaltation / divine authority | 3 | 36 | 28 | yes: report vs claim | no | no | no |
| 16 | DISAMB-MARK-FORGIVENESS-AUTHORITY | forgiveness authority | 2 | 36 | 25 | yes | no | no | no |
| 17 | DISAMB-PHIL-CHRISTOLOGY | Philippians 2 attribution | 2 | 36 | 22 | yes | no | no | no |
| 18 | DISAMB-JOHN-I-AM-CONTEXT-AND-TRUTH | "I am" | 2 | 36 | 22 | yes | no | no | no |
| 19 | DISAMB-MIXED-EXISTENTIAL-PRIORITY | simple vs mixed-token priority | 5 | 36 | 15 | silo | not forked: type-distinct (batch 4) | — | — |
| 20 | DISAMB-Q11-GOD-BEING-PERSON | God as being vs person | 2 | 35 | 26 | silo | no | no | no |
| 21 | DISAMB-KANT-GOD-IDENTIFICATION | God in the comparison | 3 | 35 | 26 | comparison | no | no | no |
| 22 | DISAMB-EXISTENCE-ESSE-SUPPORT | existence / esse / support | 4 | 35 | 24 | yes | not forked: framework interfaces (batch 4) | — | — |
| 23 | DISAMB-MOTION | motion | 2 | 34 | 34 | broad sense chosen; physical change a species | no | no | no |
| 24 | DISAMB-MOVED-BY-SOMETHING | moved by something / another | 3 | 34 | 30 | yes; strength order natural | no | no | no |
| 25 | DISAMB-MODAL-CAUSE-POSSIBILITY-AND-EXERCISE | possible vs exercised causation | 3 | 34 | 24 | yes | no | no | no |
| 26 | DISAMB-PRIOR-DETERMINATION-AND-MOVER | prior determination vs mover | 2 | 33 | 26 | rival discrimination | no | no | no |
| 27 | DISAMB-PERSEVERANCE-SOURCE-AND-MOVER | perseverance vs mover | 2 | 33 | 25 | rival discrimination | no | no | no |
| 28 | DISAMB-CHANGE-A-SERIES | change | 3 | 33 | 25 | rival discrimination | no | no | no |
| 29 | DISAMB-FIRST-PRINCIPLE-WARRANT | first-principle warrant | 5 | 32 | 1 | floor | no | no | no |
| 30 | DISAMB-ORDER-OF-BEING | more and less in being | 3 | 31 | 22 | yes: grades premises | no | no | no |
| 31 | DISAMB-OCCURRENCE-VS-CONCRETE-EXISTENCE | occurrence vs existence | 3 | 30 | 21 | silo | no | no | no |
| 32 | DISAMB-THINKER-LOCAL-VS-GLOBAL-GROUNDING | local vs global grounding | 3 | 28 | 22 | strength order natural | no | no | no |
| 33 | DISAMB-Q14-RECEPTION-SENSES | cognitive reception | 9 | 28 | 17 | yes | partial (1 relation) | no | no |
| 34 | DISAMB-INTELLECT-AND-SENSE-COGNITION | cognition / intellect | 2 | 28 | 13 | yes | no | no | no |
| 35 | DISAMB-INFINITY | infinite | 2 | 27 | 7 | yes | no | no | no |
| 36 | DISAMB-BEING-UNIVOCITY | being univocal / analogical | 2 | 26 | 19 | premise truth | no | no | no |
| 37 | DISAMB-ACTUAL-VS-WHOLE-CARRIER-WF | well-foundedness scope | 2 | 26 | 17 | strength order | partial (2 relations) | no | no |
| 38 | DISAMB-REGION-EXTENT-AND-PERFECTION | infinite extent vs perfection | 2 | 26 | 7 | yes | no | no | no |
| 39 | DISAMB-NECESSARY-INDIVIDUAL-SCOPE | (modal worker's area) | 4 | 25 | 19 | — | out of scope | — | — |
| 40 | DISAMB-COMPLETE-CAUSE-PARTIAL-GROUND | complete cause vs partial ground | 2 | 25 | 15 | yes | no | no | no |

Further terms named in the brief: DISAMB-ETERNITY-AND-TEMPORAL-PERPETUITY
(eternal; 21 root args, 2 statements; `Eternal` is a primitive with no
temporal model, so a fork first needs typed time vocabulary),
DISAMB-IMMUTABLE-AND-CURRENTLY-UNCHANGING (21, 2), DISAMB-TRUE (24, 6),
DISAMB-PERFECTION-SCOPE (22, 1), DISAMB-GOOD-* (20 each), DISAMB-BEING (via
DEF-BEING-AS-ENTITY). None has coverage or exclusivity statements.
DISAMB-NECESSARY and the necessary-being disambiguations belong to the modal
worker and are excluded here.

## Load-bearing terms with no definition or disambiguation

* **Definition gaps.** Of the 353 root-path statements only
  STMT-NOTHING-IS-EFFICIENT-CAUSE-OF-ITSELF had no `definition_ids` (173
  dependent arguments). This PR links DEF-EFFICIENT-CAUSING and DISAMB-CAUSE.
* **"authority" has no disambiguation.** Stage 4 uses claimed divine authority
  (STMT-JESUS-CLAIMED-DIVINE-AUTHORITY-AND-ROSE, under
  DEF-SKELETON-OPEN-PREDICATES; the Mark/John disambiguations separate report
  from claim), and stages 5–6 use teaching authority founded by God
  (STMT-FOUNDER-GUARANTEES-FOUNDED-AUTHORITY,
  STMT-BRIDGE-GOD-FOUNDED-AUTHORITY-PROPOSES-ONLY-TRUTH, DEF-DIVINE-ASSISTANCE,
  DEF-CHURCH-VISIBLE-AUTHORITATIVE-SOCIETY, DEF-TEACHING-INCLUSIVE-GOVERNING-POWER).
  No record says that the root route never passes from Jesus's claimed divine
  authority to the Church's teaching authority. A DISAMB-AUTHORITY needs a
  dedicated definition of "claimed divine authority" (the skeleton predicate
  is generic) and would oblige every route argument that uses both senses to
  link it; that touches lane B records and the bundle audits, so it is left
  for the owner/lane B (needs: vocabulary for the claim predicate).
* **"composite"** is reached through component/fusion definitions
  (DEF-COMPOSITION-COMPONENT, DISAMB-FUSION-CAUSE-EXTERNALITY) but has no
  disambiguation separating matter–form, essence–esse and
  integral-part composition. The matter/form/esse batch
  (`explorations/round4-matter-form-esse-essence-compositions.toml`) is the
  place for it (needs: an owner decision on whether the three compositions
  are senses of one term or three terms).
* "will", "revelation", "church", "found(ed)", "eternal", "immutable",
  "simple", "intellect", "good", "true", "God", "maxime ens", "per se",
  "potency", "act" and "being" all have definition and disambiguation records.

## Fork pattern

`TruthCore.Causality.TermSenseForks` gives each forked term:

* an inductive enum of senses (`PrioritySense`, `CauseSense`);
* a frame of the existing Lean parameters and a sense-relative relation
  (`PriorityFrame.PriorIn`, `CauseFrame.CausesBy`) whose constructors unfold to
  `PriorSimply`/`PriorInTime`/`PriorInSubstance` and to
  `MovesIn`/`EfficientlyCausesIn`/`CausesIn`/`CausesOrigin`;
* COVERAGE (`…SensesExhaustive`, generic `SensesCover`): every use of the term
  on the route is read in some selected sense and equals that sense's
  relation;
* EXCLUSIVITY (`…SenseUnique`, generic `SenseUnique`): the route's reading
  selects at most one constructor. It is a constraint on the reading choice,
  not a disjointness claim: senses may overlap or be strength-ordered in a
  model (DEF-ROUTE-SENSE-SELECTION). Exclusivity with coverage gives
  "uses agree" (no equivocation); the controls show that coverage alone does
  not;
* a joint theorem by cases (disjunctive syllogism over the enum) and
  per-branch results or refutations.

Both coverage and exclusivity are explicit OPEN frontier premises,
attribution deferred. Coverage is attackable by naming a further sense.

### "prior" (DISAMB-PRIORITY-SIMPLE-OR-IN-TIME)

| Branch | Result | Status |
|---|---|---|
| simply | the route premise is STMT-ACT-SIMPLY-PRIOR-TO-POTENCY | yields |
| in substance | ACT-SIMPLY-PRIOR-FROM-SUBSTANCE-PRIORITY via STMT-PRIOR-IN-SUBSTANCE-IS-SIMPLE | yields under open bridge |
| in time | ACT-NOT-PRIOR-IN-TIME-FROM-TEMPORALLY-FIRST-POTENCY, `refutes` STMT-ACT-PRIOR-TO-POTENCY-IN-TIME | refuted under STMT-TEMPORALLY-FIRST-BEING-IN-POTENCY |
| joint | PRIOR-SENSE-FORK-ACT-SIMPLY-PRIOR → STMT-ACT-SIMPLY-PRIOR-TO-POTENCY | coverage + route premise + bridge + temporal premise |
| no equivocation | PRIOR-ROUTE-USES-AGREE-FROM-UNIQUE-SENSE | coverage + exclusivity |

No strength order among the three senses is provable without a bridge; none
is registered. Rejected lead: a bridge from priority in time to simple
priority (Aquinas, ST I q.3 a.1, grants potency prior in time within one
changing thing while act is simply prior). The temporal premise has a serious
rival: Aristotle's priority of act in time in species (Θ.8), which is why the
refutation is conditional.

### "cause" (DISAMB-CAUSE)

| Branch | Result | Status |
|---|---|---|
| efficient | the route premise is the secunda via premise itself | yields |
| moving | NO-SELF-EFFICIENT-CAUSE-FROM-NO-SELF-MOVER (reuses Aristotle's STMT-NO-MOVER-MOVES-ITSELF-IN-ITS-RESPECT) via STMT-SELF-EFFICIENT-CAUSATION-IS-SELF-MOVING | yields under open bridge |
| origin | NO-SELF-EFFICIENT-CAUSE-FROM-NO-SELF-ORIGIN via STMT-SELF-EFFICIENT-CAUSATION-IS-SELF-ORIGINATION | yields under open bridge |
| perfection | SELF-PERFECTING-SUBJECT-REFUTES-NO-SELF-PERFECTION, `refutes` STMT-NOTHING-CAUSES-ITS-OWN-PERFECTION | refuted under STMT-SOME-SUBJECT-CAUSES-ITS-OWN-PERFECTION |
| joint | CAUSE-SENSE-FORK-NO-SELF-EFFICIENT-CAUSE → STMT-NOTHING-IS-EFFICIENT-CAUSE-OF-ITSELF | coverage + route premise + three branch closers |
| no equivocation | CAUSE-ROUTE-USES-AGREE-FROM-UNIQUE-SENSE | coverage + exclusivity |

Strength order: STMT-NO-MOVER-MOVES-ITSELF-IN-ITS-RESPECT `strengthens`
STMT-NOTHING-MOVES-ITSELF-IN-SAME-RESPECT (SAME-RESPECT-NO-SELF-MOTION-FROM-NO-SELF-MOVER).
Outside coverage, and so the named attacks on it: grounding (`Ontic.Causes`,
world-indexed), and Aristotle's formal, material and final causes
(DEF-ARISTOTELIAN-CAUSE-MODES). Rejected lead: closing the perfection branch by
a bridge from efficient causing to causing a perfection; the perfection
premise is refuted under the self-perfecting-subject premise, so the branch
closes by refutation.

## Batch 2: one argument per sense (sense-indexed terms)

Owner direction: senses carry labels TERM_n in the order of the
disambiguation's `sense_definition_ids`; an argument that works under several
senses becomes one argument per sense with ID suffix -TERM-n, and those are the
primary results. The enum, coverage/exclusivity joint theorems are kept as
optional summaries (`TruthCore.Causality.TermSenseForks2`); there, exclusivity
is a premise of a theorem whose conclusion is a root-route node, and the
controls show the step fails when two uses of the term take different senses.

### "uniting cause" (DISAMB-UNITING-CAUSE), to STMT-COMPOSITE-HAS-A-UNITING-CAUSE

| Sense | Per-sense argument | Distinctness premise |
|---|---|---|
| UNITING-CAUSE_1 uniting | COMPOSITE-HAS-UNITING-CAUSE-UNITING-CAUSE-1 | open STMT-NOTHING-UNITES-ITSELF |
| UNITING-CAUSE_2 efficient | existing COMPOSITE-UNITING-CAUSE-FROM-UNION | STMT-NOTHING-IS-EFFICIENT-CAUSE-OF-ITSELF via STMT-UNITING-CAUSE-IS-EFFICIENT |
| UNITING-CAUSE_3 causing being | COMPOSITE-HAS-UNITING-CAUSE-UNITING-CAUSE-3 | open STMT-NOTHING-CAUSES-ITS-OWN-BEING (drops the efficient bridge and the secunda via premise) |
| UNITING-CAUSE_4 temporal composer | existing COMPOSITE-UNITING-CAUSE-FROM-TEMPORAL-PRODUCTION | its own temporal fork |
| summary (1–3) | UNITING-CAUSE-SENSE-FORK-COMPOSITE-HAS-UNITING-CAUSE | coverage + exclusivity |

Strength order: STMT-NOTHING-CAUSES-ITS-OWN-PERFECTION (refuted in batch 1)
`strengthens` STMT-NOTHING-CAUSES-ITS-OWN-BEING, which survives that
refutation.

### "in act" (DISAMB-IN-ACT), to STMT-NOTHING-MOVES-ITSELF-IN-SAME-RESPECT

IN-ACT_3 (DEF-IN-ACT-FORMALLY-OR-VIRTUALLY, ST I q.4 a.2 *univoce vel
eminentius*) is appended to the disambiguation for this fork.

| Sense | Per-sense argument | Status |
|---|---|---|
| IN-ACT_1 formal | NO-SELF-MOTION-SAME-RESPECT-IN-ACT-1 | yields |
| IN-ACT_2 virtual | NO-SELF-MOTION-SAME-RESPECT-IN-ACT-2 | yields |
| IN-ACT_3 formal or virtual | NO-SELF-MOTION-SAME-RESPECT-IN-ACT-3 | yields |
| mixed (IN-ACT_3 mover, IN-ACT_1 non-simultaneity) | control model with self-motion | fails |
| summary | IN-ACT-SENSE-FORK-NO-SELF-MOTION | coverage + exclusivity |

Sense bridges (strength order) run in opposite directions in the two
premises: IN-ACT_1 mover → IN-ACT_3 mover, IN-ACT_3 non-simultaneity →
IN-ACT_1 non-simultaneity. So no uniform reading is weaker in both premises,
which certifies the DISAMB-IN-ACT remark that both premises must be defended
in one sense.

### "cause of becoming or being" (DISAMB-BECOMING-BEING-CAUSE), to STMT-PARTICIPATED-HAS-OTHER-CAUSE

| Sense | Result | Status |
|---|---|---|
| BECOMING-BEING-CAUSE_1 cause of becoming | control model: another cause of coming to be, no cause of being | fails |
| BECOMING-BEING-CAUSE_2 external cause of esse | PARTICIPATED-EXTERNAL-ESSE-CAUSE-BECOMING-BEING-CAUSE-2 (q.3 a.4 + open STMT-PARTICIPATED-HAS-DISTINCT-ESSE), then PARTICIPATED-HAS-OTHER-CAUSE-BECOMING-BEING-CAUSE-2 (explicit sense bridge 2 → 3, `strengthens`) | yields |
| BECOMING-BEING-CAUSE_3 cause of being | the root-path statement itself | — |

### Not forked: DISAMB-UNITING-CAUSE-ACTUALITY

It reaches the root only through DEF-CAUSE-OF-PERFECTION, shared with
DISAMB-CAUSE; no root-path statement or argument links its other senses
(DEF-WORLD-ACTUAL-CAUSAL-GRAPH, DEF-UNITING-CAUSE-ACTUALITY-INTERFACES). Its
senses are interface bridges between `CausesIn c x esse` and the
world-indexed causal graph, not rival readings of one use, so per-sense
arguments to a root conclusion do not exist and a coverage/exclusivity pair
would misdescribe them (needs: a root route that reads one use in the
world-graph sense).

## Next forks

1. Batch 1's "prior" and "cause" forks: restate their exclusivity in a
   two-use joint theorem on a root node, as in batch 2.
2. **DISAMB-MAXIME-ENS** (50): six senses, already strength-ordered in prose
   (weakest chosen); register `strengthens` and a coverage statement.
3. **DISAMB-PER-SE** and **DISAMB-POTENCY**.
4. **DISAMB-ETERNITY-AND-TEMPORAL-PERPETUITY**: needs typed time vocabulary
   for `Eternal` before a fork can fail (invariant 16).

## Batch 3: "maxime ens" and "potency" (#1233 B)

Owner rules: each sense its own Lean declaration, one argument per sense,
coverage and exclusivity first, every per-sense argument concludes a root-route
node or reaches one through a named bridge. Vocabulary
`TruthCore.Causality.TermSenseForks3`, results
`TruthCore.Results.Causality.TermSenseForks3`, spec
`specs/term-sense-forks-3.toml`, maps `explorations/term-sense-forks-3-*.toml`,
attempt ATTEMPT-TERM-SENSE-FORKS-3-20261108.

### maxime ens (DISAMB-MAXIME-ENS) → STMT-MAXIMUM-IN-BEING-CAUSES-ALL-BEINGS

Root-route node: STMT-MAXIMUM-IN-BEING-CAUSES-ALL-BEINGS, the causal principle
at being with a MAXIMAL antecedent, a premise of the direct-esse and
whole-roster root arguments. The source principle "what is maxime in a genus
causes all in it" is read in each sense:

| Sense | Definition | Lean declaration | Per-sense argument (root node) | Outcome |
|---|---|---|---|---|
| MAXIME_1 maximal | DEF-MAXIME-ENS | `IsMaximalIn · · esse` | MAXIMUM-IN-BEING-CAUSES-ALL-AS-MAXIMAL | instantiation at being |
| MAXIME_2 greatest degree | DEF-GREATEST-DEGREE-IN-A-PERFECTION | `GreatestDegreeBearer · esse` | MAXIMAL-BEING-CAUSES-FROM-GREATEST-DEGREE (existing) | through the maximal-to-greatest bridge |
| MAXIME_3 strict | DEF-GREATEST-BEING-STRICT | `StrictlyGreatestIn · · esse` (new) | MAXIMUM-IN-BEING-CAUSES-ALL-AS-STRICTLY-GREATEST | through bridge STMT-MAXIMAL-IN-BEING-IS-STRICTLY-GREATEST (derived from STMT-MORE-IN-BEING-CONNECTED, a total scale of being) |

Existence layer. The quarta via's last step uses the superlative twice
(something is maxime ens; the maxime in being causes being in all others) and
concludes STMT-MAXIME-ENS-CAUSES-BEING-OF-ALL. Coverage
STMT-MAXIME-SENSES-EXHAUSTIVE and exclusivity STMT-MAXIME-SENSE-UNIQUE range
over these two uses. Per sense: MAXIME-ENS-CAUSES-ALL-AS-MAXIMAL, -AS-GREATEST-DEGREE
(bridge STMT-GREATEST-IN-BEING-IS-MAXIMAL, derived from
STMT-MORE-IN-BEING-TRACKS-DEGREE) and -AS-STRICTLY-GREATEST (bridge
STMT-STRICTLY-GREATEST-IN-BEING-IS-MAXIMAL, derived from
STMT-MORE-IN-IS-ASYMMETRIC). Connection plan: no root argument consumes
STMT-MAXIME-ENS-CAUSES-BEING-OF-ALL; the root arguments pair the causal node
above with STMT-GRADES-TO-MAXIMUM-AT-BEING instead, so this layer shows where
exclusivity bites but does not yet reach the root (needs: a root argument that
consumes the quarta via's existential conclusion).

Summary MAXIME-SENSE-FORK-CAUSES-BEING-OF-ALL. Controls: the mixed reading
(existence MAXIMAL, causal GREATEST-degree) fails on incomparable degrees; each
bridge is needed (omission models); tied maxima under asymmetric more-in give a
MAXIMAL being and no STRICTLY greatest one, so MAXIME_3's existence premise is
the strongest. Not forked: DEF-GREATEST-CONCEIVABLE-BEING (Anselm; contrast
only, a rival reading denies coverage), DEF-MAXIMUM-CALIBRATION-PROFILE
(bridge vocabulary, not a reading), DEF-MAXIMUM-IN-A-PERFECTION (MAXIME_1's
declaration at a general respect). No `strengthens` is registered: every
implication between the senses needs an order premise (asymmetry,
connectedness or degree tracking), so none is a single-premise result.

### potency (DISAMB-POTENCY) → STMT-NOTHING-MOVES-ITSELF-IN-SAME-RESPECT

The prima via step uses "in potency" twice: what is moved is in potency, and
nothing is in act and in potency in the same respect. Coverage
STMT-POTENCY-SENSES-EXHAUSTIVE, exclusivity STMT-POTENCY-SENSE-UNIQUE.

| Sense | Definition | Lean declaration | Per-sense argument | Outcome |
|---|---|---|---|---|
| POTENCY_1 adopted | DEF-POTENCY | `AdoptedPotency.InPotency` | NO-SELF-MOTION-FROM-ADOPTED-POTENCY | yields with two premises (no non-simultaneity premise) |
| POTENCY_2 independent | DEF-INDEPENDENT-POTENCY | primitive `InPotency` | AQUINAS-NO-SELF-MOTION-SAME-RESPECT (existing) | yields with three premises |
| POTENCY_3 capacity | DEF-CAPACITY-TO-BE | `CapacityPotency` (new) | NO-SELF-MOTION-FROM-CAPACITY | valid, but its non-simultaneity premise is refuted under STMT-SOME-CAPACITY-EXERCISED (CAPACITY-NON-SIMULTANEITY-FAILS-FROM-EXERCISE; the Megarian thesis also supplies it) |

Summary POTENCY-SENSE-FORK-NO-SELF-MOTION; the mixed reading (moved CAPACITY,
non-simultaneity ADOPTED) allows self-motion. Strength order:
STMT-MOVED-ONLY-AS-IN-ADOPTED-POTENCY `strengthens` STMT-MOVED-ONLY-AS-CAPABLE.
Not senses of this use: DEF-MEGARIAN-ACTUALIST-CAPACITY (a thesis on the
capacity relation) and DEF-RECEPTIVE-POTENCY (a different Lean type).

### Not forked

* **DISAMB-PER-SE**: homonyms. Per se ordered series and necessary per se
  already have distinct Lean declarations of different types; self-evidence
  and per se nota are statuses with no Lean declaration. No root-path use
  admits two senses, so coverage and exclusivity have no use to range over.
* **DISAMB-RECEPTIVE-POTENCY**: receptive potency relates a principle to its
  received act, a different type from InPotency; equivocation is already a
  type error.

### Next forks

DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER and DISAMB-MUTABILITY-CHANNEL (38 root
args; need a typed power-in-another relation for DEF-MUTABLE-THROUGH-ANOTHER),
DISAMB-GOD (42; naming premise), DISAMB-MIXED-EXISTENTIAL-PRIORITY (36),
DISAMB-EXISTENCE-ESSE-SUPPORT (35).

## Batch 4: "mutable", "God" and the quarta via's conclusion (#1233 B)

Vocabulary `TruthCore.Causality.TermSenseForks4`, results
`TruthCore.Results.Causality.TermSenseForks4`, spec
`specs/term-sense-forks-4.toml`, maps `explorations/term-sense-forks-4-*.toml`,
attempt ATTEMPT-TERM-SENSE-FORKS-4-20261108.

### mutable (DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER) → STMT-LIFE-BOUNDARY-REQUIRES-POTENCY

The root argument IMMUTABLE-IS-PRIMITIVE-ETERNAL-FROM-TYPED-BOETHIAN uses "in
potency in some respect" twice: succession requires it, and beginning or
ceasing to live requires it. Q.9 a.2 says a thing is mutable through potency in
itself or through a power in another. DEF-MUTABLE-THROUGH-ANOTHER now has a
declaration over a typed power relation `PowerOver y x r` ("y can change x in
respect r"; not assumed irreflexive, transitive or well-founded). Coverage
STMT-MUTABILITY-SENSES-EXHAUSTIVE, exclusivity STMT-MUTABILITY-SENSE-UNIQUE.

| Sense | Definition | Lean declaration | Per-sense argument (root node) | Outcome |
|---|---|---|---|---|
| MUTABLE_1 in the subject | DEF-POTENCY | `MutableInSubject` (∃ r, InPotency x r) | LIFE-BOUNDARY-POTENCY-FROM-IMMUTABILITY (existing) | yields |
| MUTABLE_2 through another | DEF-MUTABLE-THROUGH-ANOTHER | `MutableThroughAnother` (new) | LIFE-BOUNDARY-POTENCY-THROUGH-ANOTHER | only through the open bridge STMT-SUBJECT-OF-ANOTHERS-POWER-HAS-POTENCY |
| MUTABLE_3 in some way | DEF-MUTABLE-IN-SOME-WAY (appended) | `MutableInSomeWay` (new) | LIFE-BOUNDARY-POTENCY-FROM-SOME-MUTABILITY | the same bridge; the weakest boundary reading, closest to q.10 a.1 |

Strength order: STMT-LIFE-BOUNDARY-REQUIRES-POTENCY and
STMT-LIFE-BOUNDARY-REQUIRES-POWER-IN-ANOTHER each `strengthens`
STMT-LIFE-BOUNDARY-REQUIRES-SOME-MUTABILITY. Controls: a dependent pure act
(no potency in itself, in another's power) that begins to live satisfies the
MUTABLE_2 and MUTABLE_3 boundary statements and falsifies the root node, so the
bridge is needed; the same being breaks the joint summary
MUTABILITY-SENSE-FORK-UNCHANGING-LIFE under the mixed reading (succession
MUTABLE_1, boundary MUTABLE_2). DISAMB-MUTABILITY-CHANNEL lists the same two
senses (DEF-MUTABILITY-IN-ANOTHER duplicates DEF-MUTABLE-THROUGH-ANOTHER and
names the same declaration) and links no root-path statement; it is covered by
this fork.

### God (DISAMB-GOD) → STMT-GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE

The designated root route uses "God" twice: the fully described principle is
God, and whatever is God has the classical attributes. Coverage
STMT-GOD-SENSES-EXHAUSTIVE, exclusivity STMT-GOD-SENSE-UNIQUE.

| Sense | Definition | Lean declaration | Per-sense argument (root node) | Outcome |
|---|---|---|---|---|
| GOD_1 nominal | DEF-GOD-NOMINAL-Q13 | `NominalGod` (new) | NOMINAL-GOD-NAMING-IS-ANALYTIC; GOD-NAMES-DESCRIBED-FROM-NOMINAL | naming and converse analytic; the root premise is **equivalent** to the bridge STMT-NOMINAL-GOD-IS-CLASSICAL-GOD (NOMINAL-BRIDGE-FROM-GOD-NAMES), so the nominal reading adds no warrant (transcriptions, recorded as such) |
| GOD_2 Summa | DEF-GOD-AS-NAMED-IN-THE-SUMMA | free `God` parameter of the older stage-1 routes | GOD-NAMES-DESCRIBED-FROM-SUMMA | through the reduced naming and the open bridge STMT-SUMMA-GOD-IS-CLASSICAL-GOD |
| GOD_3 usage | DEF-GOD-WHAT-ALL-UNDERSTAND | `CalledGod` (new) | GOD-NAMES-DESCRIBED-FROM-USAGE | through the usage premise and the open bridge STMT-CALLED-GOD-IS-CLASSICAL-GOD ("but is it God?") |
| GOD_4 classical | DEF-GOD-OF-CLASSICAL-THEISM | `Signature.IsGod` | the root premise itself | — |

Summary GOD-SENSE-FORK-DESCRIBED-PRINCIPLE-ATTRIBUTES (the described principle
has the classical attributes); the mixed reading (naming GOD_1, attributes
GOD_4) fails. Omission controls: with the GOD_1 (analytic), GOD_2 and GOD_3
namings all true and a described principle present, the GOD_4 root premise
fails when the bridges are omitted.

**Equivocation hazard.** `GodNamesTheFullyDescribedPrinciple` and
`GodIsMaximalInBeing` take the God predicate as a parameter, and bind-check
matches statements by head constant. A theorem proving them at
`God := NominalGod` (analytic) would bind to the GOD_4 root statements. The
GOD_1 readings are therefore separate declarations and statements; the general
fix is #1235's sense check, or classical-specific declarations for the root
premises.

Not readings of this use: GOD_5/GOD_6 (`GodLike`, Scott and Gödel 1970), which
are world-indexed predicates over a positivity constant. They share one
declaration because the formula is the same; their senses differ only in the
positivity constant (DISAMB-POSITIVE).

### The quarta via's conclusion reaches the root

Batch 3's connection plan is closed: CATHOLICISM-FROM-MAXIME-ENS-CAUSING-ALL
(through GOD-EXISTS-FROM-MAXIME-ENS-CAUSING-ALL) is the cheapest route
CATHOLICISM-FROM-FULL-DESCRIPTION-WITHOUT-MOTION with its four quarta via
premises replaced by STMT-MAXIME-ENS-CAUSES-BEING-OF-ALL (MAXIME_1). Uniqueness
of the maximum comes from the witness's causing all being, the
cause-is-more-such principle and excluded middle, without the genus principle.
`frontier-diff`: cheapest route cost 30 → 28. The batch 3 per-sense layer at
that statement now reaches the root.

### Not forked

* **DISAMB-MIXED-EXISTENTIAL-PRIORITY**: type-distinct. Simple priority
  relates beings; the other senses concern a Prior on `Sum B E`, and two of
  them are structural laws. Only simple priority reaches the root, through the
  forked DISAMB-PRIORITY-SIMPLE-OR-IN-TIME.
* **DISAMB-EXISTENCE-ESSE-SUPPORT**: framework interfaces of different Lean
  types (Ontic, ExternallySupportedAt, PresentEsseSupport, UnderivedRootAt).
  The term with two senses on the root route is "existence" (`ExistsAt` at the
  selected world versus `InAct · esse`), and the route already passes between
  them only through explicit bridges (STMT-EXISTING-IN-ACT-AT,
  STMT-ACT-OF-ESSE-SUFFICES-FOR-EXISTENCE-AT).

### Next forks

"existence" (ExistsAt vs esse; needs a disambiguation with DEF-KANT-ONTOLOGICAL-MODEL
and DEF-ESSE as senses), DISAMB-MOTION (34), DISAMB-MOVED-BY-SOMETHING (34),
DISAMB-MODAL-CAUSE-POSSIBILITY-AND-EXERCISE (34), DISAMB-ORDER-OF-BEING (31).

