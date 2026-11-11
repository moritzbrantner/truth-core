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

The result is an independence test for the **represented fragment**. The old
clauses require a differentia, not multiple represented species or a full
metaphysical theory of genus-division; the four-term carrier does not claim to
supply the latter. It is not a
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

### Uniting relation locator audit (#1233, 2026-11-09)

The exact root step remains `STMT-UNITING-CAUSE-IS-EFFICIENT` toward
`STMT-COMPOSITE-HAS-A-UNITING-CAUSE`. The definition previously located
`DiverseUnitedOnlyThroughUnitingCauseReading`, whose body says that distinct
components have some uniter. That existential constraint does not define what
uniting means. The corrected locator is the existing primitive field
`TruthCore.Causality.TermSenseForks.UnitingFrame.Unites` in
`TruthCore/Causality/TermSenseForks2.lean`. No proof input changed.

The intended primitive means causal responsibility for bringing components
into one composite: an agent mixing elements is the existing illustration;
co-location and set union alone are excluded. `ComponentOf` remains the q.3
composition parameter, admitting parts, matter/form and essence/esse rather
than merely set membership; diversity here is numerical inequality. These
interpretive examples are not facts proved about arbitrary supplied predicates.
Whether innocent fusion, a self-uniting whole or composition as identity
instantiates this causal gloss remains OPEN. Encoding those judgments needs
an interpreted component/uniter model and explicit applicability commitments.
No temporal order, transitivity, asymmetry, irreflexivity or well-foundedness
is supplied by the field. In particular, the example cannot silently add any
of those properties to the quantified uniter premise.

The existing fork is more than constructor labels: `UnitingFrame.CausesBy`
computes `∃ a b, F.Unites c a b x`, `∃ r, F.EfficientlyCausesIn c x r`, or
`F.CausesIn c x F.esse`. These remain independent primitive relations;
the efficient and esse bridges are open propositions. The disambiguation's
first three sense declarations locate quantified uses of those relations,
not their defining bodies. The temporal frame is the fourth registered
meaning but deliberately not a fourth constructor; its existing calibration
fork must not be advertised as coverage established by the three-case summary.
This is the finite relevant scope, without inventing hypothetical alternatives.
Shared efficient/cause-of-perfection definition records are outside this lane.

Finally `CausesIn c x esse` has no world index or endpoint-existence condition.
`UnitingCausesPresent` supplies source presence for an existing target, and
`UnitingCausesAreActual` supplies the separate `Ontic.Causes` correspondence
when both endpoints exist (`TruthCore/Causality/UnderivedNonComposite.lean`).
Those interfaces are constraints, not definitions of cause-in-esse. Existing
interface omission controls already distinguish them; another countermodel
would duplicate that work. No new bridge, premise closure or metaphysical
possibility claim follows from this locator repair. Premise comparison: none.


## Constitution, passive capacity and a distinct existence ground (2026-11-11)

### Selected question and exact reuse

This continuation of #319/#325 examines the dependency left by the
root-to-pure-act assessment: why should real constitution associated with a
passive capacity require a **distinct actual concrete ground of the bearer's
existence in the same selected relation**? The target remains
`ca07cae9-6102-564e-a7fd-efb013744b3d`
(`STMT-COMPOSITE-HAS-A-UNITING-CAUSE`), with the missing connection to
`STMT-SIMPLY-PRIOR-IS-ACTUAL-CONCRETE-GROUND`. This section is an analyst warrant
assessment, not a new historical attribution or a new definition of composition.
Its inventory baseline is main `6d9b380099158c877373eaf34e2c6a9e4e6d01e4`.

Inspected `context` for result `9fa5708e-e0bc-5fad-bbc1-c32ba9ba8887`, `related`
and `dossier` for the target, and dossiers for all five union premises,
component priority and the simply-prior/ground bridge. Reused exact definitions
and bodies in `Question3/Article7.lean`, `Article7Uniting.lean`,
`Article7UnitingControl.lean`, `Article4.lean`, `TermSenseForks2.lean`, and
`Causality/UnderivedNonComposite.lean`. The existing
`CompositeUnitingCauseFromUnion.compositeHasAUnitingCause` takes **all five**
premises; its omission controls do not establish any premise's truth. The
sense-specific routes and composer/temporal controls in the dossiers remain
separate support options, not independent evidence for their common bridge.

Current computed status must be distinguished from the older account above:
the composite-cause statement, no-efficient-self-cause statement and
simply-prior/ground bridge are conditionally `proved` but **not established**.
The two uniter-to-efficient/esse premises are currently `supported`, not stated;
their older description as bare describes the earlier investigation. Nothing
in this continuation changes those statuses or treats their computed labels
as independent warrant.

The substantive prior findings are retained in
[the H.6 comparison](aristotelian-unity-h6.md),
[the Plotinian need argument](plotinian-composition-unity.md),
[the worldwise whole-first certificate](worldwise-composite-ground.md),
and the sections “Actual prerequisite priority” and q.104 illumination analysis
in [the power/existence boundary](../power-existence-scope-boundary.md).
No duplicate certificate or alternative tracker is introduced.

### Positive argument: what diversity contributes, and what still needs defense

The strongest composition argument is richer than “two things need a third.”
First specify a real bearer and its unity criterion: which constituents and
organization make this very thing exist, rather than merely describe it or
explain an accidental operation? Next distinguish the constituents considered
severally from their obtaining as this constitution. The inventory alone does
not explain the organized whole. Finally ask whether the relevant organizing
principle or productive activity explains that difference. This is a genuine
explanatory demand in generated and organized cases; merely counting distinct
constituents leaves it unanswered.

There are three further levels, each consequential:

1. **Determinate unity.** If constituents admit both the relevant arrangement
   and its absence, their separate natures alone do not determine which
   arrangement obtains. Their actual relation or an organizing activity adds
   explanatory content. This is restricted to those alternative arrangements;
   it does not establish that every composite could have failed to be unified.
2. **Constitutive dependence.** When losing that constitution would destroy
   this bearer, retaining the constitution is necessary for the bearer's
   continuing as this thing. If the constituents/organization constitute it,
   rather than merely accompany it, this supplies a positive restricted
   direction of explanation. Necessary accompaniment alone does not supply
   that direction: whole-first accounts can accept covariance and reverse it.
3. **Existential production.** To conclude that a distinct individual presently
   causes the bearer's esse, one must identify the constitution's explanatory
   role with this efficient/productive role, identify its concrete bearer,
   establish numerical distinction and current presence, and justify inclusion
   in the very relation whose incoming edges the root lacks. None of these
   follows merely from the unity explanandum. A formal principle or an actual
   arrangement is not thereby a second concrete subject.

The strongest external-uniter reply says a composite cannot explain its own
coming to be one, because the whole would already have to exist to exercise
the alleged productive activity. This gives a reason against **sufficient
efficient self-origination**. It does not address an account on which the
present whole is intrinsically constituted without having produced itself.
The alternatives are therefore not exhausted by external production and
self-production. The union proof's efficient/no-self route to `c ≠ x` remains
valid under its premises; the present argument has not independently supplied
its efficient premise for every intrinsic unity.

The part-priority route has a related strength and limitation. The actual
materials are genuine prerequisites of an ordinary material house. Their
indispensability is not merely our epistemic reason for believing in the house.
But a particular house may replace some material; “needs a constitution” must
not become “needs every particular historical part.” More importantly, this
example alone does not prove universal bottom-up priority, nor extend the same
concrete-domain relation to matter/form, essence/esse or subject/accident.
`FirstMoverSimple.firstMoverSimple` already derives noncomposition from
first-being, component priority and a distinct component. It does not prove
that every item called a constitutive principle is an actual concrete being
in the ground relation. `Article7.ComponentOf` quantifies components over
`Being`; `Article4` deliberately represents essence/esse in `Principle`.
A map between these roles needs interpretation, not silent reification.

### Source discrimination: immanent unity, becoming and continued esse

For this selected warrant question, the complete existing materializations
`AQUINAS-ST-I-Q3-A7` (Latin) and `AQUINAS-ST-I-Q104-A1-EN` (Dominican1920
translation) were reread on 2026-11-11. Their existing manifests and precise
witness identities remain authoritative; no new claim or witness was added.
The q3a7 diplomatic text has the already recorded artifacts, including missing
continuation after the second proof's “Deus”; no words are restored as evidence.
Relevant full-article locators are q3a7 co. secundo/tertio/quarto and q104a1
co., from “Every effect depends” through the house and illumination comparisons,
then the creature/God participation paragraph and replies1,2,4.

Q3a7 secundo asserts component dependence; tertio asserts the uniter principle
and invokes God's first efficient causality. Quarto runs **composition to
act/potency**, then invokes God's previously excluded potency. It supplies no
converse from every passive capacity to real composition, and no independent
proof of that exclusion. This preserves the source's positive arguments while
preventing their conclusions from becoming their own warrant.

Q104 offers a stronger answer than a bare illumination analogy: an effect
depends on a cause insofar as that cause produces this effect, and creatures
are said to participate in being whereas God has being essentially. That is
a proposed metaphysical account of continuing dependence. Its concrete house
comparison, however, distinguishes the former builder from materials and their
arrangement, which can preserve the house. The illumination effect concerns
a state of an already existing subject; retained heat supplies the contrasting
case. The examples therefore support role-sensitive dependence, not a general
inference from any unity or passive reception to a present giver of the
subject's bare existence. Reply4 expressly denies that conservation is a
succession of new temporal additions.

To use the participation paragraph in this pre-divine bridge, independently
justify the bearer's received esse and the external concurrent-giving account.
The paragraph's claim that God alone is essentially being cannot itself select
or classify the necessary underived candidate before the simplicity/identity
argument is supplied. Likewise the existing local q3a4 result can be used
conditionally without assuming God: it requires actual distinct esse, causal
exhaustiveness and exclusion of sufficient efficient self-causation. It does
not derive those premises from possession of a passive capacity or from
proper-part composition. No source assertion here discharges that warrant.

### Strong rival accounts on the same explanatory task

| Account | Positive replacement, rather than a bare denial | Specific commitment and remaining price |
| --- | --- | --- |
| Intrinsic potential/actual unity | Proximate matter and form are principles of one actuality, rather than two independently actual objects held by a third tie; a generator can explain its coming to be. | Must defend which bearers have that constitution and why it is explanatory. It need not deny generation or all dependence. H.6 does not itself establish or exclude a concurrent distinct giver of bare esse. |
| Reduction or composition-as-identity | The plural constituents and their actual relations exhaust the whole; there is no additional entity requiring a second production beyond their obtaining. Organization can still explain function and identity conditions. | Must defend the reduction and treatment of whole/parts predication. A model of arrangements alone does not establish reduction, and simple bearers may retain nonmaterial composition. No causal paradox follows just from rejecting an extra uniter. |
| Nonreductive constitution | The whole is real and distinct from its material basis; constitution and organization explain what bearer exists and its powers without being efficient generation of esse by a second subject. | Owes the direction and adequacy of constitution and its identity criterion; cannot rest on covariance or rename the unexplained unity. Accepting real distinction does not by itself turn constitution into efficient self-production. |
| Necessary composite / whole-first natural candidate | The rigid whole exists necessarily; actual proper parts and their properties derive from it, with internal structure explaining its differentiated operations. | Necessity alone is no intrinsic sufficient explanation. Whole-first priority and the account of its structure need defense; the candidate rejects universal reverse part-priority. It is not refuted by the labels composite, natural or necessary. The existing worldwise certificate realizes a specified joint profile, not this candidate's reality or metaphysical possibility. |

These are analyst comparisons; they do not attribute the reduction or
nonreductive accounts to an unread author. The whole-first candidate's price is
its disputed explanatory direction and missing adequate intrinsic reason, not
an independently demonstrated conflict with an accepted floor item. It can
explain internal operations while leaving why this whole exists unresolved;
the external-giver route also retains its own unanswered applicability and
explanatory sufficiency burdens. Neither rival's gap establishes the other.

### Dependency audit and overall provisional judgment

There is **no demonstrated formal cycle** in the inspected union theorem: its
five premises do not include pure act. The danger concerns philosophical
warrant for those inputs. Using q3a7 quarto's already assumed divine absence of
potency to certify the root's absence of potency would be circular warrant.
Using universal component priority to infer simplicity is a separate valid
conditional; defending that priority solely by a simplicity conclusion would
be the same problem. Q104's already identified unique essentially-existing
God cannot independently supply the pre-identification composition bridge.
The local q3a4 route avoids that particular naming cycle when its causal
premises and real distinction receive independent support; those obligations
remain open here.

Even an independently defended constitutional existence ground does not alone
supply the **same-respect actual witness** used by
`FirstBeingNoPotency.firstBeingNoPotency`: from `InPotency x r` that theorem
uses `InAct y r` and `PriorSimply y x`, with non-simultaneity forcing `y ≠ x`.
An actual bodily basis of a dormant capacity need not itself exercise the
performance specified by `r`. Choosing a broader meaning of actuality might
change that assessment, but needs a faithful common respect interpretation.
Calling the basis actual in some other respect supplies no such inference.
No new claim of a countermodel to the full source doctrine is made.

**Provisional judgment:** real constitution gives positive, restricted support
for current constitutive prerequisites of some actual organized bearers.
It does not yet warrant the universal passage to a distinct actual concrete
producer of bare esse in the selected existential relation. The strongest
positive external-giver argument retains independently disputable causal
exhaustiveness, receipt-of-esse and correspondence steps. Intrinsic unity and
whole-first accounts remain live against that passage, with the prices above;
they have not earned unconditional explanatory adequacy. This finding narrows
the root-to-pure-act applicability burden without defeating its valid
conditional proof, establishing a natural necessary being or deciding the
Catholic root.

Revision requires evidence on the precise disputed step: a defended actual
case where this constitution demands a distinct concurrent concrete esse-giver
in the selected relation, together with a justified scope argument reaching the
passive capacities used by the pure-act proof; or a faithful interpretation of
same-respect actuality that supplies the needed witness independently. A
necessary-composite candidate would gain support from an adequate intrinsic
account of its obtaining and structure, and lose support if its own commitments
entailed the reverse dependence in that same relation. Merely assigning edges,
restating generic act-priority or accumulating new unity examples does not
answer these tests.

Attempted approaches in this continuation: the diversity-to-third-uniter
inference, part-indispensability, q3a7's act/potency proof, q104 conservation
and the already certified q3a4 dichotomy. Each has useful conditional force;
none presently supplies the full universal application without the specific
additional warrants identified above. No materially different test inside this
bounded slice is supplied by another omission model. The broader source or
framework investigations just identified are reopening conditions, not new
assignments. Under the owner's instruction to finish current work and stop,
this slice ends with those exact open dependencies recorded for reassessment.

**Actual premise comparison and verification boundary:** no Lean, statement,
claim, definition, inference, result, argument or frontier premise is changed.
The changed files are this existing note and attempt
`356fd6f9-6e1a-548b-a4be-a456f346463f`. Unchanged certificate evidence is reused;
the complete philosophical assessment received qualified acceptance from fresh
reviewer `review_composite_ground` at frozen head
`71af7493628ea4632824a42cc36efc718c158f57`, with no repair required. The review
covered the complete outcome and coordinator synthesis, checked the actual
source/formal guards, and retained the stated open dependencies. Evidence
SHA256 prefixes were note `93bbdc96` and attempt `51aab67b`; this addition records
review metadata only. Offline corpus and attribution checks passed on that
head; final delivered-head CI remains required. Source materialization is
selected research, not a routine verification gate.
