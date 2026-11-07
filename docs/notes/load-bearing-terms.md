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
| 2 | DISAMB-UNITING-CAUSE | uniting / efficient / cause of being | 4 | 65 | 52 | yes: STMT-UNITING-CAUSE-IS-EFFICIENT passes between senses | no | no | no |
| 3 | DISAMB-BECOMING-BEING-CAUSE | causing an effect (becoming vs being) | 3 | 53 | 39 | yes: conservation read as CausesIn esse | no | no | no |
| 4 | DISAMB-UNITING-CAUSE-ACTUALITY | cause-in-esse vs world-local edge | 3 | 52 | 38 | yes: interface premises | no | no | no |
| 5 | DISAMB-ARISTOTLE-H6-UNITY-AND-CAUSATION | unity, form, cause | 5 | 52 | 38 | comparison only | no | no | no |
| 6 | DISAMB-IN-ACT | in act (formally / virtually) | 2 | 51 | 31 | silo; premise truth depends | no | no | no |
| 7 | DISAMB-MAXIME-ENS | maximal in being | 6 | 50 | 24 | weakest sense chosen; strength order natural | no | no | no |
| 8 | DISAMB-PER-SE | per se | 4 | 46 | 9 | silo (distinct predicates) | no | no | no |
| 9 | DISAMB-GOD | God | 6 | 42 | 29 | yes: naming premise | partial (1 relation) | no | no |
| 10 | DISAMB-POTENCY | potency / capacity / power | 5 | 42 | 21 | adopted configurations fix one | no | no | no |
| 11 | DISAMB-RECEPTIVE-POTENCY | receptive vs unactualized potency | 2 | 40 | 19 | yes (esse reception) | no | no | no |
| 12 | DISAMB-PRIORITY-SIMPLE-OR-IN-TIME | prior | 3 | 40 | 16 | yes: act's priority over potency | **certified (this PR)** | STMT-PRIOR-SENSES-EXHAUSTIVE | STMT-PRIOR-SENSE-UNIQUE |
| 13 | DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER | in potency / mutable | 2 | 38 | 17 | yes: immutability | no | no | no |
| 14 | DISAMB-MUTABILITY-CHANNEL | potency and mutability | 2 | 38 | 17 | yes: immutability | no | no | no |
| 15 | DISAMB-MARK-HIGH-PRIEST-EXCHANGE | reported exaltation / divine authority | 3 | 36 | 28 | yes: report vs claim | no | no | no |
| 16 | DISAMB-MARK-FORGIVENESS-AUTHORITY | forgiveness authority | 2 | 36 | 25 | yes | no | no | no |
| 17 | DISAMB-PHIL-CHRISTOLOGY | Philippians 2 attribution | 2 | 36 | 22 | yes | no | no | no |
| 18 | DISAMB-JOHN-I-AM-CONTEXT-AND-TRUTH | "I am" | 2 | 36 | 22 | yes | no | no | no |
| 19 | DISAMB-MIXED-EXISTENTIAL-PRIORITY | simple vs mixed-token priority | 5 | 36 | 15 | silo | no | no | no |
| 20 | DISAMB-Q11-GOD-BEING-PERSON | God as being vs person | 2 | 35 | 26 | silo | no | no | no |
| 21 | DISAMB-KANT-GOD-IDENTIFICATION | God in the comparison | 3 | 35 | 26 | comparison | no | no | no |
| 22 | DISAMB-EXISTENCE-ESSE-SUPPORT | existence / esse / support | 4 | 35 | 24 | yes | no | no | no |
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

## Next forks

1. **DISAMB-UNITING-CAUSE** (65 root args): uniting cause / efficient cause /
   cause of being; the step STMT-UNITING-CAUSE-IS-EFFICIENT is the sense
   passage to fork, reusing `CauseFrame` with a `uniting` constructor.
2. **DISAMB-BECOMING-BEING-CAUSE** and **DISAMB-UNITING-CAUSE-ACTUALITY**
   (53/52): coming-to-be vs conservation; atemporal CausesIn esse vs
   world-local edges. Both extend the cause enum.
3. **DISAMB-IN-ACT** (51): formal vs virtual act, with a natural strength
   order (formal → formal-or-virtual) on STMT-NOTHING-MOVES-EXCEPT-AS-IN-ACT.
4. **DISAMB-MAXIME-ENS** (50): six senses, already strength-ordered in prose
   (weakest chosen); register `strengthens` and a coverage statement.
5. **DISAMB-ETERNITY-AND-TEMPORAL-PERPETUITY**: needs typed time vocabulary
   for `Eternal` before a fork can fail (invariant 16).
