# Can independent foundations explain their joint cooperation? (#744)

Result `JOINT-COOPERATION-CERTIFICATE`, module `TruthCore.Explanation.JointCooperation`.
Semantic profile: the #733 `Exercise` records and #734 `Supply`, unchanged. Everything
below is relative to one supplied scenario space and event carrier.

## Thesis tested

The unity argument says two independent foundations could only cooperate by luck, so a
deeper one is needed. Its best source form is ST I q.11 a.3's third proof. The certificate
tests whether that argument separates one source from several.

**Finding.** In this semantics it does not. It forces a choice among the branches below.
Of the exclusions tested, the fit denial is a per-record at-most-one and the total reading
gives at most one source outright, while the brute denial and the pairwise reading hold
with two sources.

## Meaning of the relations

| Term | Ordinary sense | Example | Near miss |
| --- | --- | --- | --- |
| Coexistence | Both are there | Two strangers in one city | Does not involve any shared effect |
| Compatibility | They could both be there | Two tenants who never overlap | Need not be actual |
| Coordination | Both take part in one exercised record | Two people carrying one table | Records membership, not how the work is shared |
| Sufficiency | Given both, the effect follows across the scenarios | Two switches in series with supply held fixed | Has no causal direction (#733) |
| Needed | Removing one leaves an allowed failure | Either series switch, open | Relative to the scenario space |
| No cooperation needed | One can go without an allowed failure | A second key-holder when one key opens the door | |
| Common source | One prior event determines both | A storm behind both the falling barometer and the rain | A shared ancestor that does not determine them is not enough |
| Mutual fit | They never come apart | Two theorems that hold in all models | Says nothing about why they never come apart |
| Brute coincidence | They actually coincide, can come apart, and nothing here determines both | Two friends who turn up in one café unplanned | Relative: a fuller carrier may supply a source |

These are analyst notions. Structural properties are not assumed: ancestry is transitive
by construction (`TransGen`), and no asymmetry or well-foundedness is claimed in general.
Generalizing from ordinary examples to foundations is exactly what is under test, so the
examples only motivate the distinctions. Rival accounts would read the same table
differently: a Humean sees only the regularity, an interventionist treats scenarios as
interventions, a powers theorist wants production, which the table does not state.

## The fork

For a coordinated, jointly sufficient pair (`Coverage`):
`NoCooperationNeeded ∨ (TwoWayVariation ∧ (CommonSource ∨ BruteCoincidence))`.
The four-way form also lists mutual fit. Branches overlap; only the listed incompatibilities
are proved. Mutual fit is not a separate survivor: in one scenario space it makes both
contributors redundant.

| Branch | Witness | What it brings | What excluding it costs |
| --- | --- | --- | --- |
| No cooperation needed, mutual fit | `fit`, `narrow` | Both redundant; effect occurs everywhere; the empty set suffices for it | Requiring both needed refutes occurrence of either at every allowed scenario, so a pair of foundations occurring everywhere is out |
| Common source | `guided` | Each contributor also occurs without it, if both are needed | Dropping it leaves the pair redundant or brute |
| Brute coincidence | `exercisePlural`, `single` | Two-way variation, no common source | With both needed, no exercised source can be a contributor of the pair, at one source or two |

## What each exclusion amounts to

- **Deny fit among contributors occurring everywhere.** Exactly per-record at-most-one
  (`FitExclusionIsAtMostOne`). This agrees with #771's warning: on this background such a
  premise is not independent of uniqueness.
- **Deny brute coincidence.** `IncompatibleCore`: coordination, sufficiency, one exercised
  source contributor and needing both force brute. Each of the five members can be
  dropped with the other four kept (`CoreDeletions`). No source count appears. `guided`
  meets the denial with two sources or one, and `single` violates it with one source.
- **Pairwise reading of q.11 a.3.** Excludes a source as a coordinated contributor, holds with
  two sources and no least event (`guided true`).
- **Total reading of q.11 a.3.** Gives at most one exercised source outright, so it is not an
  independent step. The readings are two claims, `AQUINAS-ST-I-Q11-A3-ONE-ORDER-A` and `-B`.

## Strongest replies

**Pluralist.** Two necessary foundations pose no coincidence problem. A coincidence needs a
space where they could have come apart, and in the modal space they cannot. `FitRival` keeps
this model, with a contingent further event through a non-sufficient exercised record.
Its costs are that neither contributor is needed, the jointly sufficient effect is
necessary in that overlay, and scenario tests say nothing about production there.

**Pluralist, wider space.** Keep indispensability by intervening on necessary beings.
`VariationRival` keeps this model. Its cost: the scenarios are not worlds of either overlay,
and on that space the pair is brute. The same records restricted to the actual scenario
move to the fit branch, so the branch depends on the chosen scenario space.

**Unity.** The sufficiency law linking two independent natures is an extra brute fact. This
is the best remaining line, and the table cannot test it, since the law is simply part of
the occurrence table for one source as well as for two. It needs the per se premise of
q.11 a.3 ("multa non sunt causa unius nisi per accidens"), now candidate
`MANY-CAUSE-ONE-PER-ACCIDENS`, and it must apply the same standard to a single source's law.

## Parity

Uniqueness does not by itself remove the problem. `single` has one least source, occurring
everywhere, with a needed pair that is brute. If an event occurring everywhere suffices for a
contributor, both cannot be needed, so a single determining source occurring everywhere
has the same no-need result.

## Boundaries

- Shared effect and weak connectivity do not give a unique source: `PluralMinima` (#707, #733)
  and `Structural` (#735) are consumed unchanged.
- `Supply` holds in the rivals as the existing proposed standard, not as adequacy.
- Models establish satisfiability of the encoding, not metaphysical possibility.
- Fidelity of the q.11 a.3 readings is uncertain: "deserviunt" and "ordinarentur" are not
  event ancestry, and the source's reason is not encoded.
- `RootMultiplication` (#771) and `CondensationSufficiency` (#768) were unmerged when this
  work started and are not imported.

## Open

Is there an independently defended productive or per se causal notion that separates
producing from idle co-occurrence, applied alike to one source and several? Root delta: none.

## Follow-up (2026-11-03): the law connecting jointly indispensable inputs

**Question.** Even granting #735's two-source group and PR #925's exactly
`{0,1}` intrinsic support for target 2, what explains the *particular productive
law* under which those two contributions jointly yield the target? A complete
group record says **which inputs are required**; it does not say why the record
is admitted as genuinely productive. Nor does a single-source group explain its
own law simply by having only one source.

### Three live arguments, under one explanatory standard

1. **Nature-based law (strongest version).** Let the separately describable
   natures include stable dispositions, manifestation conditions and
   counterfactual constraints. If a substantive independently warranted
   composition principle derives the interaction from those dispositions,
   rather than naming the observed interaction, the combined natures can
   explain the *type of production*. The law need not be a third substance.
   The required premise is that the full essence-and-composition description
   really fixes this relationship, including non-actual cases. It is not
   established by merely renaming `admitted g` as `NatureOf a`.
2. **Law-ground requirement (strongest version).** Let the separately specified
   natures be invariant while two different candidate interaction laws remain
   compatible with them. Those natures alone do not select which law obtains.
   If an ultimate explanation must also account non-circularly for a
   particular productive relation whenever genuinely eligible alternatives
   remain, something else must distinguish the laws. This might be a
   structural principle, a relation, a background law, a further actuality
   fact or an agent's choice; it need not be another **individual being**.
   The contrastive completeness norm and genuine admissibility of both law
   alternatives are independent OPEN philosophical premises.
3. **Plural-source survivor.** Two intrinsic, possibly necessary sources have
   complementary dispositional natures whose combination is restricted by a
   necessary relational structure or co-grounded compatibility principle.
   This can reject law variation with those *full* natures fixed, and it need
   not reify the group index into a third source. It owes a non-circular account
   of its relational principle, or explicitly accepts it as a primitive
   necessary stopping point. It also owes an account of any contingent
   *exercise* or effect not necessitated by that structure. The same burden
   falls on the single-source account's productive powers and exercise.

These are serious alternative **framework commitments**, not a certified
exhaustive metaphysical trilemma. Brute regularity, probabilistic laws,
irreducible relational essences and non-necessitating personal explanation
remain possible replies.

### Exact controlled countermodels using existing #735 inputs

`JointCooperation.lawVariant k on` keeps #735's original group membership,
enablers, effects, intrinsic-seed predicate and bearer candidates. It changes
only admission of the productive record whose effect is target 2. The
`lawExercise` overlay leaves the actual scenario, every event's occurrence
and all local scenario-sufficiency conditionals unchanged; only the admitted
records are exercised. The result is a **law-status intervention**, not a
claim that actual substances with the same complete essences could inhabit
two accessible worlds with distinct laws.

| Original #735 source pattern | Law admitted | Law not admitted | Unchanged controls |
| --- | --- | --- | --- |
| `single`, one ordinary source | target 2 has inductive `Supply` | target 2 lacks `Supply` | Same intrinsic seed 0, contributor record, actual occurrence and scenario sufficiency |
| `plural`, two ordinary sources | target 2 has inductive `Supply` from 0 and 1 | target 2 lacks `Supply` | Same intrinsic seeds 0 and 1, contributor record, actual occurrence and scenario sufficiency |

The supporting Lean results are `law_exercise_controls`,
`target_not_supplied_when_law_off`, and `law_status_parity`. A separate
`single_plural_no_profile_only_verdict` makes a precise information point:
for **any fixed total unary profile** `nature : Nat → N`, a function of that
same profile cannot equal both opposite productive-Supply verdicts. This is
not a ban on relational dispositionalism. If the productive relation is
essential to the full natures, then the two cases do **not** share that full
profile, and the premise of the comparison fails. That is the contested
philosophical fork, made explicit.

The off cases still have the target actually occurring. Thus a failure of
`Supply` cannot be read as the nonexistence of an effect, and a positive
`Supply` remains only the #734 proposed **inductive** productive standard,
not actual efficient causation or ultimate existential adequacy. The cases
are populated, nonvacuous mathematical models and retain their local
conditionals; they do not certify actual-world modal alternatives.

### The non-circularity test for an appeal to *nature*

Ask the proposer to specify a nature **without using the very relation being
explained** and then derive the target relation. Evidence favoring genuine
explanation includes independently intelligible dispositions, their
combination rule, counterfactual predictions in new pairings and background
conditions, and an account of why those dispositions have this manifestation
profile. "A's nature is to produce effect E when B participates" is at most
a useful *description* unless it adds such independent constraints. Calling
the sentence an essence does not create explanatory asymmetry. Conversely,
it is too strong to insist every compositional or constitutive explanation
be reducible to separately instantiated unary properties; a structural or
relational essence may supply irreducible explanatory content.

An ordinary illustration is a circuit with two separately characterized
components. Their individual specifications plus an independently tested
composition rule can predict an output. The mere pair of component labels
cannot. This is an analogy about information and law application, not proof
that metaphysical production is electrical composition.

The same exact test applies to one source: its asserted nature plus its
productive law must have content beyond "whatever makes this outcome". A
necessarily existing source does not automatically necessitate its effects;
source occurrence, actual exercise and actual effect selection remain separate.
If a primitive necessary relation is an admissible self-explanatory stop for
one source, it cannot be prohibited for two just because it is relational
without an additional independent argument.

### Weakest premises and consequences

| Candidate commitment | What follows | What emphatically does not follow |
| --- | --- | --- |
| Fixed full individual profiles across admissible law variants + verdict depends only on those profiles | Incompatible with the two distinct productive verdicts (conditional Lean control) | That such metaphysical law variants exist |
| Independently specified natures plus a non-circular rule that excludes every rival interaction | A nature-and-rule explanation may account for the *type* of cooperation | That the rule explains its own actuality or one being is necessary |
| Ultimate explanation must ground any genuinely variable productive law | The ungrounded law is incomplete if independently relevant alternatives remain | That its ground is an additional person, substance or single cause |
| Every ultimate law must be grounded by exactly one complete individual producer, with the #925 participant-cover policy | Conditional pressure toward object-level uniqueness/compositeness | The truth of that strong policy, God, or divine simplicity |

The first row is an exact formal underdetermination boundary. The remaining
rows contain OPEN interpretive or metaphysical bridges; they are not
machine-certified sufficiency or uniqueness principles. In particular,
"necessary law" is not synonymous with "explained law", but a necessary
impersonal relation may be a positive ultimate stopping proposal on the same
terms as a necessary individual's intrinsic nature.

**Premise/frontier effect:** no registered argument or premise is added or
discharged. The existing named actual underived-source route remains eight
explicit premises, frontier cost nine; PR #925's distinct complete-cover
assembly remains nine premises, cost ten, while still open. Neither the
two-source countermodel nor a nature-label argument closes the bridge from
`Supply` to actual existential or ultimate explanatory adequacy. The missing
independent step is a non-question-begging *law-grounding discriminator*,
followed separately by any bridge from grounding a law to one **necessary
concrete individual**. A theorem about group records does not supply either.
