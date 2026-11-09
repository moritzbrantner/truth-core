# The intellect–will source gap

`STMT-WILL-FOLLOWS-INTELLECT` remains an open input to the classical-attributes
stage. `StageTwo.GodHasWill.godHasWill` already imports
`StageTwo.GodHasIntellect.godHasIntellect`, then uses the universal source reading
`WillFollowsIntellectReading`. There is no missing composition call. This change
preserves source distinctions needed before replacing that input with a
structural derivation; it adds no result or root route and closes no premise.

## Verified readings

The complete articles I q.19 a.1–2 were read from the existing SCTA Leonine 1888
snapshot. The q.19 a.1 witness is reused; a.2 is a new selector in the same
unchanged Git blob. The complete question I q.80 a.1–2, including its prologue,
objections and replies, was materialized from a separately hash-pinned Latin
Corpus Thomisticum page. The page identifies the Leonine text of Rome 1889,
Busa's electronic transcription and Alarcón's revision, and claims rights for
its electronic edition. Its metadata and hashes are committed, not its text.
The selected SCTA revision has only empty placeholders for this part; the web
witness is not represented as an SCTA transcription or a translation.

Q.19 a.1 distinguishes seeking absent good from loving and delighting in good
already possessed. The latter is essential to its divine application; willing
is not inherently a deficiency. Its corpus and ad 3 also identify divine willing
with divine being and qualify its description as motion. Q.19 a.2 adds that
possession of good can issue in communicating it, insofar as possible. It does
not conclude that every possible good must be produced.

Q.80 a.1 distinguishes natural inclination following a thing's own form from a
soul's appetite following apprehension. It speaks of a power by which the animal
*can* appetitively relate to apprehended things. Its ad 2 distinguishes the
formal aspect of an object from the numerical identity of that object: one
thing can be apprehended as sensible/intelligible and appetible as suitable/good.
Q.80 a.2 distinguishes intellectual and sensitive appetite through the
apprehended object and its proportion to a passive power. Intellectual appetite
can concern singular things under a universal account, as well as immaterial
goods; it is not restricted to external objects that are universals.

## What must not be identified

- Natural appetite is not intellectual appetite. Noncognitive directedness in
  the Fifth-Way `TendsTo` API supplies no intellectual-appetite theorem.
- Having intellect or will is not an assertion of a particular current exercise.
  A capacity-to-exercise step must be stated rather than inferred from an opaque
  predicate label. This distinction does not attribute dormant cognition to God.
- Love/rest in possessed good is not deficient seeking. A model requiring an
  absent object would exclude the source's own divine case.
- Q.80's soul-power account describes appetite as passive. That feature must not
  be carried into the universal q.19 conclusion or divine willing, which q.19
  reads as divine being. The analogy of cognition-relative inclination does not
  identify God with a subject acquiring a distinct passive faculty.

These choices are linked from the existing bridge through
`DISAMB-APPETITE-POWER-AND-EXERCISE` and
`DISAMB-CREATURE-PASSIVE-APPETITE-AND-DIVINE-WILL`; natural/cognitive appetite is
separately distinguished by `DISAMB-NATURAL-AND-COGNITIVE-APPETITE`.

## Remaining A–C obligations

The candidate `AQUINAS-INTELLECTUAL-APPETITE-TO-WILL` keeps these obligations open:

A. Represent the form-relative orientation of intellectual nature toward
apprehended good, using q.19's analogy without importing creaturely passivity.

B. Explain an appetitive capacity at the level of nature/power, with seeking or
love/rest appropriately distinguished by possession. Q.80 gives useful
creaturely power structure, but that structure is not yet a universal model of
divine and created willing.

C. State how the resulting intellectual-appetite account is recognized by the
existing primitive `HasWill` predicate. Its intended sourced content is already
recorded by `DEF-HAS-WILL`; the Lean predicate has not been redefined as a
conjunction of newly introduced fields.

A–C are neither proved premises nor a claim of assumptions weaker than the old
bridge. A chain of opaque predicates with these names would only transcribe the
conclusion. A God-specific model would also need a typed account of divine
self-knowledge and known goodness, not merely the old `HasIntellect` label.
No appetite ontology or extra root wrapper is introduced here.

## Omission and discrimination controls

The following are model requirements/research controls, not newly verified Lean
results or refutations of Aquinas:

1. A subject loves its possessed good and never seeks an absent good: an
   absent-good-only definition of will fails the q.19 divine application.
2. A represented intellectual capacity has no represented current exercise:
   this blocks an unargued power-to-current-seeking inference.
3. A noncognitive thing has natural inclination without intellectual appetite:
   this blocks substituting Fifth-Way directedness for will.
4. One object has different cognitive and appetitive formal aspects: numerical
   object identity does not collapse the powers in q.80 a.1 ad 2.
5. A soul's passive appetite is proportioned to an apprehended object; divine
   willing is not thereby made externally moved or passive.
6. A proposed local appetite structure is held fixed while the independent old
   `HasWill` predicate is false: until C is justified, the old bridge does not
   follow from that structure alone. This is an API gap, not a counterexample to
   the full root theory or to the source's intended theology.

The source-only preservation changes no `Challenge`, `Solution`, existing
statement identity, root-route selection, or meanings of `HasIntellect` and
`HasWill`. All six new readings are source claims, not verified derivations.


## Boundary audit for #355 (2026-11-09)

The current bounded inventory was inspected against main at `52d8cb761`.
This is an audit and rejected-lead record, not a new derivation or a claim that
all intellectual-appetite distinctions have been encoded.

* `Results.Causality.IntellectualInclination.willFromIntellectualInclination`
  takes `IntellectHasIntelligibleForm`, `EveryFormHasInclination`, and
  `IntelligibleInclinationIsWill` jointly. Its proof extracts an intelligible
  form, applies the universal inclination premise, then applies recognition.
  The conclusion is the old universal `WillFollowsIntellectReading`; no exercise,
  chosen object or output follows. The companion `controls` already supplies
  the populated one-being/two-form omission interpretations, including cognition
  without inclination and inclination without the independent `HasWill` flag.
  Do not recreate these as an IntellectWillBoundary result. Important evidence
  limit: `results/WILL-FROM-INTELLECTUAL-INCLINATION/comparator.json` lists only
  `willFromIntellectualInclination`, not `controls`; the controls have source
  proofs but are not separately compared under that configuration.
* `Results.Causality.Round5Worklist.willFromIntellectualAppetite` factors
  recognition through `IntelligibleInclinationIsIntellectualAppetite` and
  `IntellectualAppetiteIsWill`. Both are OPEN. The first produces a principle
  bearing `AppetitivePowerOf` and `FollowsIntellect`; these predicates do not
  encode a response to a represented object's goodness or possession. Adding
  another existential intermediary would only relocate recognition.
* Round5's `everyFormInclinedFromFinality` already factors inclination through
  an operation, an end and `EndDirectedOperationIsInclination`. Its
  `DirectedTo o e` does not assert that the subject cognitively represents e as
  good. Identifying these relations would hide the very bridge at issue.
* `Modal.SimplicityCollapse.optionalAct` already has no performance/output at
  world `true`; `inefficaciousAct` has performance there without output. Both
  retain the concrete `noCreation` ontology and its necessary source. Their
  clauses occur in `Results.Modal.SimplicityCollapse.core`, selected by
  `results/SIMPLICITY-COLLAPSE-CORE/comparator.json`. These are output/efficacy
  controls, not models of an intellectual subject without appetitive capacity.
* `Results.Modal.OptimalCreationChoice.checks` already contains the distinct
  tied-optimum candidates, local determinism, failed cross-world stability,
  and the strict-improvement/no-optimum consequence. `OptimalOutputs` separately
  assumes positive-output totality; `uniqueOptimalStable` separately assumes
  uniqueness of the optimal candidate, not just equality of greatest values.
  Reusing these controls does not turn rational appetite into maximizing choice,
  libertarian alternatives or temporal deliberation.

### Actual missing bridge

The unresolved inference is from **representing an end under an apprehended-good
aspect** to **an appetitive capacity responsive to that aspect**, even when the
represented good is already possessed. Neither `Intelligible f` nor
`DirectedTo o e` contains that representation/possession structure. The smallest
next investigation should hold the represented object and its goodness fixed,
vary possession, and distinguish capacity to seek absent good from capacity to
rest in possessed good. It must also admit a cognitive-only subject with the
same representations and no appetitive responses. Then test an explicit local
response-capacity constraint, restricted to the represented goods actually used,
rather than `EveryFormHasInclination` for every natural and intelligible form.
This is a proposed encoding target, not a proved weaker replacement premise.

Recognition by the old primitive `HasWill` remains a separate open bridge; a
response table cannot establish it by renaming its fields. No transfer from
capacity to present exercise or production is licensed. A God-specific use still
needs self-knowledge/known-goodness structure and must allow possessed-good rest
without creaturely passivity. This audit does not reopen the parked immateriality,
life or concrete-scope investigation (#1282).

No new vocabulary, exploration map, Challenge, Solution, source claim or result
was minted: the duplicate distinctions above were rejected, while the proposed
possession-sensitive bridge remains unencoded. The claim/type self-sweep found
no new theorem claim. All three original premises and both appetite-recognition
premises remain open; no will premise is established. Root-premise delta: none.
The unavailable `corpus.py orphans` subcommand was not treated as an idle-library
audit. Shared convention sourceRevision for this audit:
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.
