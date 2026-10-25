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
