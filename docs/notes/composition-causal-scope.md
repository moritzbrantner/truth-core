# Which compositions require an actual uniting cause?

This comparison concerns #319 and #325. It reuses the existing q.3 reading,
PowerExistenceBoundary and Vitalism, and inspects the proposed connections in
PRs [655](https://github.com/moritzbrantner/truth-core/pull/655),
[656](https://github.com/moritzbrantner/truth-core/pull/656) and
[657](https://github.com/moritzbrantner/truth-core/pull/657). Those PR references
identify inspected research artifacts, not a new verification certificate or an
assertion that their branches have merged. No new theorem is needed for this
scope finding. No same-profile inconsistent bundle is certified here.

## Source reading and limits

The pinned Latin passage `AQUINAS-ST-I-Q3-A7` was materialized and its entire
article read, including the objections, five proofs and replies. The witness is
SCTA's diplomatic TEI of the Leonine edition, repository `scta-texts/TAca84`,
revision `f9065dc8ce7bc790b8c972e49ee19d661f028be6`, passage XML identity
`TAca84-d1e61-Dd1e1553`. Reproduce the consulted text with
`python3 scripts/source_evidence.py materialize AQUINAS-ST-I-Q3-A7`.
Diplomatic extraction contains printing/OCR artifacts; no missing wording was
silently supplied to create an additional premise.

Precise locators within **I q.3 a.7 co.**:

- **Primo** enumerates quantitative parts, matter/form, nature/suppositum,
  essence/esse, genus/difference, and subject/accident. The argument aims at
  absence of composition in every relevant sense. It is not merely an argument
  that God is not an organism, not an artifact, or not a material aggregate.
- **Secundo** states posteriority to and dependence on components. This is a
  separate source commitment, not a definition of a mathematical fusion.
- **Tertio** argues that things diverse in themselves do not unite into one
  without a uniting cause, then appeals to God's lack of an efficient cause.
  The existing claim `AQUINAS-ST-I-Q3-A7-COMPOSITE-HAS-CAUSE` expressly records
  the interpretive step to a numerically distinct cause of the composite's being
  as one thing. Numerical distinction is in the bound Lean type; nonparthood is
  not. Neither a world index nor actual presence of that cause is in this type.
- **Quinto** discusses heterogeneous and homogeneous wholes, including water
  and air. These examples do not justify quietly replacing every relevant
  composite with an organism or a substantially unified living being.

These observations **do not** show that every arbitrary modern Sum2 fusion is
what Aquinas means by a composite. The source does not state a theorem about
Lean sets, unrestricted second-order fusion, microstate observations, or the
particular Boolean fixtures. Conversely, a modern substantial-unity criterion
cannot be inserted as a restriction of the existing universal q.3 premise just
to avoid a rival counterexample. A narrower reading requires its own statement,
faithful source argument and explicit relation to the present root premise.
The live research candidate is `COMPOSITION-TO-ACTUAL-CAUSE-SCOPE`.

## Exact reused types

`CompositeHasAUnitingCauseReading Composite CausesIn esse` is
`∀ x, Composite x → ∃ c, c ≠ x ∧ CausesIn c x esse`.
The statement is `STMT-COMPOSITE-HAS-A-UNITING-CAUSE`; its composition scope is
linked through `DEF-SIMPLE`, and its causal respect through
`DEF-CAUSE-OF-PERFECTION` and `DEF-ESSE`. `Composite` remains an interpreted
primitive, covering more than the existence of a proper material part.

PR655's `TruthCore.Results.Causality.UnderivedNonComposite.from_union` applies
`TruthCore.Results.Causality.UnderivedCommonSource.causal_from_union` and carries
its **same** named individual into `¬ Composite n`. It retains that result's
eight original inputs and adds the existing q.3 reading plus two separately
open interfaces: `UnitingCausesPresent` and `UnitingCausesAreActual`.
The first makes the alleged distinct cause exist at the selected world; the
second maps cause-in-esse to a world-local `Ontic.Causes` edge with actual
endpoints. Its contradiction uses sourcehood's prohibition of **any** incoming
actual edge, including an edge from a distinct proper component. It does not
need the cause to be spatially outside, a nonpart, or temporally earlier.
The two proposed omission controls separate presence from causal correspondence.
This comparison reuses their stated boundary; it neither reruns their proof
checks nor promotes development diagnostics to final Comparator evidence.

`PowerExistenceBoundary.Composite m x` instead means that the finite model marks
a distinct bearer as a proper component of `x` (`DEF-PROPER-PART-COMPOSITION-MODEL`).
Its `Boundary` already separates exercised underived power, modal necessity,
absence of a represented conserver, and this limited composition. It cannot
replace the broader q.3 parameter without an interpretive bridge.

`Vitalism.SoulUnityIndependence` and its `scenario_same_profile` controls already
show that their fixed turnover/maintenance signature does not determine
substantial unity or soul-as-form. That is a signature-relative independence
result, not a definition of unity or an empirical refutation of an organism.
`DISAMB-MEREO-UNITY` keeps structural and substantial unity apart.

## Required mappings before comparing a rival with the source argument

| Obligation | Exact content to defend | What does not supply it |
| --- | --- | --- |
| Bearer and actuality | A fusion or ordinary system is represented by an actual individual of the common ontic domain at the selected world. | A macro-description type, candidate carrier, or set-theoretic union alone. |
| Relevant composition | That actual individual's structure satisfies the supplied q.3 `Composite` predicate. An embedding from fusion objects would need this preservation property. | Calling a set composite, or restricting the q.3 predicate to organisms without argument. |
| Same witness | The proposed material whole or arrangement bearer is the very individual whose sourcehood was obtained, if sourcehood is to exclude its composition. | Existence of some source alongside some composite; uniqueness of actual sources does not make an arbitrary whole a source. |
| Distinct uniting cause | The selected q.3 reading supplies `c ≠ x` and cause-in-esse at this same target. | No material nonpart outside a universal whole; that is stronger than numerical distinction. |
| Presence | The cause exists at the same selected world as the target. | Atemporal quantification over candidate causes; a cause located only at another world. |
| Causal correspondence | That actual cause-in-esse produces the world-local causal edge excluded by sourcehood. | Strict parthood, a candidate grounding relation, semiconjugacy, or a primitive-to-macro description map. |

These are obligations, not additional axioms of this comparison. In particular,
a material-domain embedding need not exhaust all beings: a possible alleged
nonmaterial cause is not ruled out by coverage of the material whole. A static
fusion algebra also does not establish modal necessity or identity across worlds.

## Strongest replacement accounts and genuine remaining disagreement

| Account | Affirmative replacement in the inspected artifacts | What remains open against the q.3 route |
| --- | --- | --- |
| Universal fusion (PR656) | Nonempty pluralities have a no-extra-parts Sum2 fusion; ordinary organization is further structure. The same fusion facts admit a strict-part candidate-ground relation or an empty relation. | Neither candidate relation is thereby an actual cause-in-esse. The empty relation does not refute q.3 without defended semantic correspondence; the internal distinct-ground variant does not escape sourcehood if it is defended as an actual incoming causal edge. |
| Material nihilism (PR657) | Specified simple bearers and transitions reproduce a nonlinear collective response through every finite history of admitted interventions; a larger intervention family exposes a failed coarse reduction. | A faithful selected macro-description is not an extra material bearer. But having no proper material parts does not eliminate matter/form, essence/esse or other q.3 composition of the primitive bearers. Neither real applicability nor unrestricted causal/explanatory sufficiency is proved. |
| Whole-first grounding (the #331 investigation) | A proposed fundamental material whole, rather than its parts, provides the priority account. | Grounding priority is not automatically world-local efficient causation, and material fundamentality is not metaphysical simplicity. The actual source argument must establish its causal interface and identify the relevant same individual before these positions clash. The source investigation's own locators and qualifications remain authoritative. |
| Thomistic composition route | A composite's being as one requires a numerically distinct uniting cause, with separately defended actual presence and causal correspondence. | Its wide composition scope, actual applicability and sufficiency must be defended rather than inferred from rival explanatory gaps. The current conditional connection does not establish those premises. |

Thus neither "the universe has no material object outside it" nor "organized
responses admit a simple-bearer description" defeats the actual q.3 premise as
currently typed. Conversely, the conditional source-to-noncomposition result does
not refute universalism, nihilism or priority monism until the disputed mappings
are defended in one common interpretation. The substantial next test is a
specific actual case with a defended unity/composition criterion and an account
of why its unity requires a cause-in-esse, compared against the rival's full
replacement explanation on that same case. No arbitrary fusion is assumed to
be a substance, and no explanatory gap establishes the preferred ontology.

## Premise comparison and verification boundary

No philosophical premise is added, removed or discharged. All existing root-route
open premises are retained. There is no new result, source-derived claim,
statement identity, theory bundle or root edge in this batch. The source reading
is persisted here against its existing witness; the candidate records what is
still to be investigated, and the attempt links this scope audit to the existing
dossiers. Source attribution and formal consequence remain separate. Final CI
covers the delivered records; unchanged proof evidence is reused.

## Four composition senses: the genus-to-cause gap

The next bounded cycle asks which **particular composition** supplies which
dependence claim. Its downstream question is whether the same underived witness
can be excluded from that composition, not whether the word *composite* can be
repeated as a new premise. The strong rivals remain affirmative: simple-bearer
arrangements reproduce specified interactions; universalism admits fusions
without making each a substance; priority monism proposes a fundamental material
whole; the Thomistic account offers real constitutive principles and a causal
account of their union. These explanations must meet the same actual case before
their commitments form an incompatible bundle.

| Composition under consideration | Existing exact interface/result | Further commitment needed for dependence |
| --- | --- | --- |
| Material parts | `PowerExistenceBoundary.Composite` means a represented distinct proper component. Its `Boundary` already has an exercised unborrowed, necessary source with such a component and no represented external conserver. `UniversalFusionBoundary.Boundary` distinguishes fusion from candidate grounding. | The component's actual ontological priority, an efficient cause of the whole's esse, or an independently defended grounding relation. A mathematical part/fusion law does not supply all of these at once. |
| Matter–form | `MatterFormAndEsseEssenceAreCompositionsReading` includes it under q3 `Composite`; `FirstMoverSimple.firstMoverSimple` imports that inclusion. Aristotle H.6 offers proximate potential/actual unity with a mover exception. | Why the actual subject has the relevant real constitution, and which material/formal, producing or conserving role supplies the dependence used by the argument. Neither two independently actual substances nor an additional efficient uniter follows merely from a record with two fields. |
| Essence–existence | Article4's `DistinctEsseAt` requires an actual subject and distinct represented principles. `distinctEsseExternalFromExhaustion` derives an actual distinct efficient esse cause from the separate causal dichotomy and no-efficient-self-cause premise. Its existing omission controls are nonvacuous. | Causal exhaustiveness and the exclusion of sufficient efficient self-causation, not just the distinction. Intrinsic noncausal reasons, conservation and modal necessity remain separate. The existing conditional is expressly a transcription, not defense of those premises. |
| Genus–difference | III.3's `IsGenus`, `DifferentiaOf`, `SaidOf`, and q3a5 `InGenus` supply a typed predication interface. Article7 currently has no genus/difference-to-`Composite` inclusion. | A faithful mapping from the classification to the source's real underlying principles, potency/act or essence/esse constitution, then the particular causal/priority premise. Terms, generic commonality and complete individual essence cannot be identified by convenience. |

### Newly read q3a5 arguments

The complete pinned `AQUINAS-ST-I-Q3-A5` Latin article was materialized and read,
with full q3a7 for context. In the same SCTA edition and revision cited above,
the a5 witness is XML identity `TAca84-d1e61-Dd1e1139`, blob
`9204053aec597c5ea95b77543135e641ce4cfdeb`. Its printing artifacts were retained;
no missing philosophical premise was supplied from an unpinned translation.

The **first proof**, after the two senses of being in a genus, says a species is
constituted from genus and differentia. What supplies the constitutive differentia
stands to what supplies the genus as act to potency; sensitive and intellectual
nature provide the example. The relation is between the principles **from which
the predicables are taken**, not between written words or concept tokens as
material pieces. The source uses God's exclusion of potency joined to act to
reject proper genus-membership. The current predicational declarations do not
encode that extra constitution/actuality account.

The **third proof** appeals to generic common quiddity alongside different acts
of being, and argues that things in a genus have esse other than essence. This
is a substantive source argument, recorded as
`STMT-Q3A5-GENUS-ESSE-DISTINCTION`, not an independently defended consequence of
the existing III.3 predication laws. Generic commonality is not by definition
equality of every subject's **complete** essence. The argument's sufficiency and
its mapping into `Article4.Profile.essenceOf` remain to be defended.

Neither reading is the already formalized second proof that being is not a genus.
They retain separate statement identities. These differences matter to the
uniqueness investigation: having one genus-word or shared predicates does not
silently provide q11's same represented nature for the hypothetical individuals.

### A structured joint interpretation test

`GENUS-CAUSE-BOUNDARY` / `GenusCauseBoundary.checks` combines existing results
instead of introducing a fresh opaque simplicity predicate:

1. A four-term taxonomy has a designated genus, species and differentia, and
   classifies both Bool bearers. Genus and differentia are essentially said of
   their represented species; genus is not said of its own differentia. The
   existing `BeingNotAGenus.beingNotAGenus` theorem is applied to these clauses.
2. The existing `EssenceEsseExternalCause.premiseOmissionsAndControl` positive
   witness provides an actual distinct-esse subject, a numerically distinct
   actual efficient cause, causal exhaustiveness and no sufficient efficient
   self-cause. Thus the successful case does not rely on an empty extension or
   an absent differentia. The distinct cause and the subject supply two actual
   Bool bearers.
3. Erasing **only `CausesIn`** preserves the entire actuality, essence, esse and
   essential-principle data, as well as the fixed taxonomy. The subject is still
   actual and distinct-esse; the no-efficient-self-cause premise still holds.
   There is no efficient esse cause, so causal exhaustiveness fails. The proof
   uses `distinctEsseExternalFromExhaustion` to identify that failure.
4. A separate edge-free identity copy keeps the same actuality and taxonomy but
   sets esse equal to essence. Both q3a4 premises hold **vacuously** because their
   distinct-esse antecedent fails. This tests the absence of a genus-to-real-
   distinction bridge; it is not the nonvacuous external-cause case above.

The result is an independence test for the **represented fragment**. It is not a
countermodel to q3a5 after adding its further real-constitution commitments, nor
to the full q3a7 uniting-cause premise. These interpretations establish no
metaphysical possibility, necessary existence, pure actuality, full simplicity,
intrinsic explanatory adequacy or particular actual ontology. In particular,
no equation of represented essence and esse in the identity copy certifies all
the other simplicity exclusions. No world index is in Article4: connecting its
efficient-cause reading to a selected world's causal edge remains another bridge.

The two live additions to test are therefore independently visible: **classification
to real constitution**, and **real distinction to the selected dependence through
causal exhaustiveness/priority**. The source supplies arguments for them; a source
assertion is not their independent defense. The new candidate
`GENUS-DIFFERENTIA-REAL-DEPENDENCE-BRIDGE` preserves this question. The models do
not select the preferred denial, and the first three rows are reused findings,
not new results advertised for this batch.

Intended and actual root-premise change: **none**. All open root leaves are
retained. The two new q3a5 claims are scoped prose readings; the new mathematical
certificate has no ordinary premises and proves the stated joint controls, not
the truth of a composition/dependence thesis. Focused Lean diagnostics reported
zero axioms; final delivered-head CI owns binding, Comparator and NanoDa checks.
