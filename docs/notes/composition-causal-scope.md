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
