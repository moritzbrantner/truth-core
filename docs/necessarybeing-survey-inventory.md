# Necessary Being interactive survey: provisional argument inventory

Reading date: 2026-10-26 · Campaign: [#492](https://github.com/moritzbrantner/truth-core/issues/492) · Source identity: NECESSARYBEING-SURVEY

**Status: source inventory plus first formalized conditional slice.** These pages were traversed in the public interactive quiz, including different answer routes. No survey answers were submitted. Four initial pages (the necessary-being definition, A1c, A1c2 and A7c) now have byte-stable hash-pinned web_snapshot manifests, verified in a local checkout with `source_evidence.py materialize` and inspected there. The definition and A1c also have matching dated Wayback bytes; A1c2 and A7c remain fragile without known matching captures. The first ten source claims cover the definition (three), A1/A1c2 (four), and A7c (three). The A7c steps 1–3 conditional result passed local Lean compilation, Comparator and independent NanoDa checking on 2026-10-31 at baseline `770102e8b399bbc2ab6dcb36dd60ffff93cb4d14`, using `scripts/verify-result.sh NB-SURVEY-FIVE-TO-ONE` with zero permitted axioms. Fresh integration binding on 2026-10-31 at `9f583a004023e7ff6bc0db72dbc057ecca02239c` matches both named premises and the OneCausable conclusion exactly; the global report has 730 bound, 2 existing pins and 0 mismatches. The labels NB-SURV-P01 etc. below are inventory handles, **not STMT IDs**. Other readings await pinned passages and fidelity checks.

The survey has ten numbered arguments, but most share a modal suffix. They should be imported as distinct source arguments sharing the *same* verified modal intermediate result, not ten copies of that proof.

## Pages inspected

| Family | Question pages (observed) | Conclusion and route |
| --- | --- | --- |
| A1 | [a1p0](https://www.necessarybeing.com/a1p0.html), [a1p1](https://www.necessarybeing.com/a1p1.html), [a1p2](https://www.necessarybeing.com/a1p2.html), [a1p3](https://www.necessarybeing.com/a1p3.html), [a1p3b](https://www.necessarybeing.com/a1p3b.html), [a1p4](https://www.necessarybeing.com/a1p4.html) | [a1c](https://www.necessarybeing.com/a1c.html) (self/parts exclusion), [a1c2](https://www.necessarybeing.com/a1c2.html) (explicit external cause) |
| A2 | [a2p1](https://www.necessarybeing.com/a2p1.html), [a2p2](https://www.necessarybeing.com/a2p2.html) | [a2c](https://www.necessarybeing.com/a2c.html) |
| A3 | [a3p1](https://www.necessarybeing.com/a3p1.html), [a3p2](https://www.necessarybeing.com/a3p2.html), [a3p3](https://www.necessarybeing.com/a3p3.html) | [a3c](https://www.necessarybeing.com/a3c.html) |
| A4 | [a4p1](https://www.necessarybeing.com/a4p1.html), [a4p2](https://www.necessarybeing.com/a4p2.html), [a4p3](https://www.necessarybeing.com/a4p3.html), [a4p4](https://www.necessarybeing.com/a4p4.html) | [a4c](https://www.necessarybeing.com/a4c.html) |
| A5 | [a5p1](https://www.necessarybeing.com/a5p1.html), [a5p2](https://www.necessarybeing.com/a5p2.html) | [a5c](https://www.necessarybeing.com/a5c.html) |
| A6 | [a6p1](https://www.necessarybeing.com/a6p1.html), [a6p1b](https://www.necessarybeing.com/a6p1b.html), [a6p2](https://www.necessarybeing.com/a6p2.html) | [a6c](https://www.necessarybeing.com/a6c.html) |
| A7 | [a7p1](https://www.necessarybeing.com/a7p1.html), [a7p2](https://www.necessarybeing.com/a7p2.html), [a7p3](https://www.necessarybeing.com/a7p3.html), [a7p4](https://www.necessarybeing.com/a7p4.html) | [a7c](https://www.necessarybeing.com/a7c.html) |
| A8 | [a8p1](https://www.necessarybeing.com/a8p1.html), [a8p2](https://www.necessarybeing.com/a8p2.html), [a8p3](https://www.necessarybeing.com/a8p3.html), [a8p4](https://www.necessarybeing.com/a8p4.html) | [a8c](https://www.necessarybeing.com/a8c.html) |
| A9 | [a9p1](https://www.necessarybeing.com/a9p1.html), [a9p1b](https://www.necessarybeing.com/a9p1b.html), [a9p2](https://www.necessarybeing.com/a9p2.html), [a9p3](https://www.necessarybeing.com/a9p3.html) | [a9c](https://www.necessarybeing.com/a9c.html) |
| A10 | [a10p1](https://www.necessarybeing.com/a10p1.html), [a10p2](https://www.necessarybeing.com/a10p2.html), [a10p3](https://www.necessarybeing.com/a10p3.html) | [a10c](https://www.necessarybeing.com/a10c.html) |

Shared introduction: [home](https://necessarybeing.com/), [instructions](https://necessarybeing.com/instructions.html), [necessary-being definition](https://necessarybeing.com/definenecessarybeing.html). Different answers may skip families. Routes were independently revisited to inspect conclusions; the table is **not** a claim to enumerate every possible answer history.

## Atomic proposition and definition leads (not yet canonical)

| Handle | Provisional reading | Relevant witness |
| --- | --- | --- |
| NB-SURV-P01 | A necessary being is one that cannot fail to exist and is capable of causing something, at least possibly. | Definition; all conclusion pages |
| NB-SURV-P02 | The author separately stipulates that the existence of some necessary being entails its necessary existence. | Definition; modal suffix |
| NB-SURV-P03 | Possibility is taken as consistency with what is objectively necessary, not mere conceivability. | Instructions; definition |
| NB-SURV-P04 | Contingency means not having to exist by nature. | A1–A10 hover definitions |
| NB-SURV-P05 | In this source, concrete means capable of being a cause. This is not silently identical with spatial, material, actual, or nonabstract. | A8c hover definition |
| NB-SURV-P06 | A cause is an earlier explanatory or partly explanatory condition; for a situation S it exists while S does not yet obtain. | A1c; A7c hover definitions |
| NB-SURV-P07 | Individually possible situations remain possible when a different possible situation becomes actual, even if the two are not jointly possible. | A2p2, A3p3 and other modal questions |
| NB-SURV-P08 | The source identifies this possibility-persistence assumption with necessity of possibility / S5. | A2c–A10c modal suffix |
| NB-SURV-P09 | The modal suffix seeks to infer N from possibility of N, the separate N ⇒ □N axiom, S5 and □N ⇒ N. | A2c–A10c |
| NB-SURV-P10 | The sum/totality C of all contingent things is itself contingent (a nontrivial closure premise). | A1p2 |
| NB-SURV-P11 | Every contingent thing has some cause. | A1p1 |
| NB-SURV-P12 | An object cannot originate itself or be caused entirely by its own parts. | A1p3 |
| NB-SURV-P13 | The alternative A1 route stipulates an external cause and asks again whether every contingent thing has one. | A1p3b, A1p4 |
| NB-SURV-P14 | It need not be necessary that every concrete thing participates in an infinite ungrounded causal chain. | A2p1 |
| NB-SURV-P15 | Under the explicit entire/head definitions, an internally uncaused head of a cause-closed ancestry is uncaused from outside too; a head need not imply cardinal finitude. | A2c |
| NB-SURV-P16 | A possibly uncaused concrete head plus the no-uncaused-contingent premise is used to infer possible noncontingent existence. | A2c |
| NB-SURV-P17 | No individually possible event is necessarily uncausable. | A3p1 |
| NB-SURV-P18 | A first beginning of all contingent existence is possible. | A3p2 |
| NB-SURV-P19 | A first transition from no contingent things to some cannot have an earlier contingent cause. | A3c |
| NB-SURV-P20 | Some caused event involving a property P may cause P to acquire its first instance. | A4p2 |
| NB-SURV-P21 | Being contingent can possibly start to be exemplified. | A4p3; A4c |
| NB-SURV-P22 | General first-exemplification transfer together with causability and the initial transition is used in a reductio to possible necessary existence. | A4c |
| NB-SURV-P23 | It is not necessary that any obtaining set of contingent situations include an uncausable member. | A5p1 |
| NB-SURV-P24 | A possible world can make every obtaining contingent situation causable. | A5c |
| NB-SURV-P25 | Its exact total-history situation C is claimed contingent and causable, although no contingent thing could precede it. | A5c |
| NB-SURV-P26 | It can be possible that every contingent thing is individually causable. | A6p1 |
| NB-SURV-P27 | A stronger/shifted route quantifies over contingent existence situations rather than beings. | A6p1b |
| NB-SURV-P28 | The exact existence situation for a possible world is claimed contingent, causable, and not caused by earlier contingent things. | A6c |
| NB-SURV-P29 | For n ≥ 2, causability of a situation with at least n contingent instances of type T transfers to one with at least n−1 instances. | A7p1 |
| NB-SURV-P30 | It is possible that four contingent things jointly cause a fifth, yielding a causable at-least-five situation. | A7p3 |
| NB-SURV-P31 | Repeated finite transfer yields causability of an at-least-one-contingent situation. | A7c |
| NB-SURV-P32 | An at-least-one-contingent situation cannot be caused by a condition that is itself contingent and prior to that situation. | A7c |
| NB-SURV-P33 | A limiting property entails some deficiency. | A8p1 |
| NB-SURV-P34 | Being a powerful necessary being is proposed as nonlimiting, whereas possible nonexistence is limiting. | A8p2, A8p3 |
| NB-SURV-P35 | If necessarily all causal-concrete beings were contingent, concreteness would inherit limitation, contradicting the nonlimiting candidate. | A8c |
| NB-SURV-P36 | Ordinary entailment over an impossible antecedent can be vacuous; the site stipulates a stronger nontrivial entailment. | A9p1 |
| NB-SURV-P37 | Necessary concreteness is claimed to inherit nontrivially what concreteness entails. | A9p1b |
| NB-SURV-P38 | Necessary concreteness is claimed not to nontrivially entail contingency; the contradiction yields possible necessary concreteness. | A9p2, A9c |
| NB-SURV-P39 | Usually (not without exception), contingent things have causes. | A10p1 |
| NB-SURV-P40 | Infinite, ungrounded causal chains need not include every concrete thing as a metaphysical necessity. | A10p2 |
| NB-SURV-P41 | A possible first contingent member plus the rule of thumb yields only defeasible, prima facie support for a necessary cause. | A10c |

### Alternative readings that must not be collapsed

- **Necessity of a class versus an individual:** □∃x N(x) is not the same as ∃x □E(x) without a fixed domain and transworld identification. The site's separate axiom concerns the existence of some N; preserve this scope.
- **Temporal permanence versus metaphysical necessity:** the introduction says a necessary being cannot fail to exist at any time. Check whether this is intended as cross-world necessity rather than only everlasting existence.
- **Possible causal power versus actual causation:** the nominal definition requires ability; A1 argues from an actual external cause, and A3–A9 from a possible one. Neither makes the bearer necessary *because* it causes.
- **Causation of things, events, and situations:** the source moves between these relata. Do not silently choose one typed relation for all three.
- **Part, whole, and total history:** the sum of contingent things (A1) and the exact situation of all contingent things in a world (A5/A6) are different types of objects, not one unqualified C.
- **The site’s concrete versus other senses of concrete:** its explicit definition is causal-capability-based, not a neutral metaphysical criterion.
- **Possibility of every versus every possibly:** ◇∀x P(x) and ∀x ◇P(x) require distinct proposition IDs until an actual implication is proved.
- **Counterpossible entailment:** A9's nontrivial relation is not classical implication from an impossible antecedent, and cannot be simulated by ordinary material implication without a substantive additional semantics.
- **Probabilistic versus deductive:** A10 explicitly claims defeasible support, not a logical demonstration.

## Argument skeletons and proof obligations

### Registered first slice

- **Definition:** `STMT-NB-SURVEY-DEFINITION`, `STMT-NB-SURVEY-EXISTENCE-NECESSITATION`, and `STMT-NB-SURVEY-OBJECTIVE-POSSIBILITY` preserve the two-part nominal meaning, the extra existential axiom and its account of possibility as distinct claims. None is established by a proof.
- **A1 and external A1c2:** `STMT-NB-A1-CONTINGENT-TOTALITY`, `STMT-NB-A1-CONTINGENTS-CAUSED`, `STMT-NB-A1-SELF-PARTS-EXCLUSION`, and `STMT-NB-A1-CONTINGENTS-EXTERNALLY-CAUSED` record four separate, respondent-reported premises. The first A1 route and its stronger external-cause variant have not been validated as full arguments.
- **A7 finite descent:** `STMT-NB-FIVE-CONTINGENTS-POSSIBLY-CAUSEABLE` and `STMT-NB-COUNT-CAUSABILITY-DESCENT` are **two open reported premises**; `STMT-NB-ONE-CONTINGENT-POSSIBLY-CAUSEABLE` is their conditional intermediate conclusion under `NB-SURVEY-FIVE-TO-ONE`. The Lean solution instantiates the second premise at 5, 4, 3 and 2, so the result is declared a **transcription by instantiation** (`"transcription": "instantiation"`, AGENTS.md invariant 16): it closes no frontier node by itself, and the intermediate conclusion stays open while either premise is open. The `Nat → Prop` causability predicate is deliberately uninterpreted: this result does not reach any cause's metaphysical type, S5, or actual necessary existence. Comparator and independent NanoDa verification passed locally on 2026-10-31; this checks the conditional transcription, not either open premise.

These records link definitions and disambiguations for necessary being, objective possibility, whole/parts, internal/external causation and the abstract possible-causability predicate. No source reading has become an accepted truth or a closed root premise.

| Route | Intended inference | Highest-value unresolved step |
| --- | --- | --- |
| A1 | Contingent whole ⇒ caused; not self/parts ⇒ noncontingent external cause ⇒ actually some N | Is C a contingent causal relatum? Does the universal causal law apply to a sum? |
| A1 external | Contingent whole + universal external-cause premise ⇒ outside contingent totality | Whether the new external-cause premise is warranted independent of a stipulative definition |
| A2 | Not necessary universal headless ungrounded coverage ⇒ proposed possible head/uncaused concrete; contingents caused ⇒ possible N; then S5 | Check the branching-ancestry repair, isolated case and source/domain correspondence using existing graph vocabulary |
| A3 | Possible first beginning + possible causation ⇒ possible earlier noncontingent cause; then S5 | Existence of a causable first event and type of priority |
| A4 | Possible causation and possible first instantiation ⇒ first exemplification of contingency could be caused by noncontingent; then S5 | Whether the generic P transfer survives substituting the property of being contingent |
| A5 | Possible world with causable contingent situations ⇒ causable exact history C ⇒ no prior contingent cause ⇒ possible N; then S5 | C may be empty, or necessity/contingency may not transfer from its members |
| A6 | Possible universal causability of contingent existence situations ⇒ causable exact history C ⇒ possible N; then S5 | Quantifier order and cross-world selection of the exact-history situation |
| A7 | Cause at least five ⇒ repeated cause at least n−1 ⇒ cause at least one ⇒ no contingent predecessor ⇒ possible N; then S5 | Finite transfer must be an explicit premise; typed time and count semantics |
| A8 | No possible N ⇒ all causally concrete beings contingent ⇒ limiting; clashes with a nonlimiting necessary powerful being ⇒ possible N; then S5 | Deficiency/limitation axiom and the relation between intensions and possibility |
| A9 | No possible N ⇒ concreteness entails contingency; nontrivial-inheritance principle contradicts nonentailment ⇒ possible N; then S5 | Give the nontrivial entailment relation its own semantics and countermodels |
| A10 | Possible finite entire chain ⇒ possible first contingent; usual causal propensity ⇒ prima facie necessary cause | Selection effects: a general propensity need not apply to a specially selected first member |

## Lean targets (source materialization done for the first four passages)

1. **A7 finite descent (conditional transcription verified locally):** A schematic predicate `causableAtLeast : Nat → Prop` with explicit transfer for n ≥ 2 yields causability at one from causability at five. Next use a typed possible-world/situation/cause model where warranted, and test the countermodel with the transfer premise absent. This is not an infinite compactness principle. Separately formalize what makes a prior condition noncontingent.
2. **A1 causal totality:** Formalize the union/member relation and an external-cause predicate. Derive the narrow conditional consequence, and show models where each contingent member is caused but the whole is not contingent or not a cause-bearing entity. Do not strengthen a source claim to make its conclusion follow.
3. **Shared S5 suffix:** Reuse existing TruthCore.Modal definitions and exact theorems. Test ◇□N ⇒ N on S5 and its failure in weaker frames, with a separate bridge N ⇒ □N. Do not create ten copied modal theorems.
4. **A5/A6 quantifier discipline:** Provide a finite-world countermodel separating ◇∀x Causable(x) from ∀x◇Causable(x), and another for an empty exact-history situation.
5. **A9 impossible antecedents:** Construct a nonvacuous, independently motivated relation (or keep it explicitly open), and exhibit where classical entailment proves vacuous propositions the survey intends to reject.
6. **A10 evidential boundary:** Model selection of a first member and the conditional probability required; do not register a probabilistic argument as a deduction in the standard Lean result machinery.

## Corpus next steps and verification boundary

1. Keep all materialized witnesses reproducible; find durable archival fallbacks for A1c2 and A7c if possible. The A2 primary question/conclusion cluster is now read below; pin its remaining alternate branches and later A3–A10 pages before source claims.
2. Check site authorship, update date and licensing rather than assigning a philosopher by speculation; inspect each later page's verified text with its context.
3. Critique the first ten source claims against the pinned text. Preserve the A1 stronger external-cause variant, existential versus individual necessity, and the source's respondent-conditional framing.
4. Reuse the verified A7 count transcription and exact premise binding. Extend the typed causal semantics or register a countermodel without transfer; do not treat the count theorem as A7's entire ontic conclusion.
5. Process remaining families in small source-order batches and compare intermediate open premises with the root frontier. No root premise closure has occurred from this first pass.

**Premise comparison for this PR:** A7 introduces two new **open, sourced, respondent-reported premises** and one new conditional intermediate conclusion in a separate argument; neither is on an established root route. The remaining seven statements are separate sourced readings, not accepted truths. No root premise has been discharged, and no route cost is claimed to have decreased. Source and corpus checks pass; the independently checked count result remains a conditional transcription, with exact binding confirmed by the subsequent integration audit below.

## Integration priority after the 2026-10-31 issue review

[Issue #786](https://github.com/moritzbrantner/truth-core/issues/786) now
requests synthesis of the PSR, regress, necessary-foundation and adequacy tracks
before further atomization. Its nine candidate arguments are research steering,
not additional verified results. Read together with
[#750](https://github.com/moritzbrantner/truth-core/issues/750), it separates
contingent-existence PSR (#312), independently defended explanatory adequacy
(#750), and the further bridge to actual concrete existential support (#545).
These are proposed investigation boundaries, not a proved sufficient or minimal
premise set. The survey's A1 causal-totality and A7 prior-cause steps must be
compared with those existing tracks before introducing new vocabulary.

The next synthesis should fix one actual contingent existence explanandum and
trace existing premise, inference, result and rival-model IDs. Compare brute
but locally reliable foundations, underdetermined infinite chains, uniquely
determined source-free structures, and necessary personal/impersonal grounds
under the same adequacy criterion. An unexplained condition is not thereby
inconsistent; a necessary explanatory fact is not thereby a necessary concrete
bearer. The new issue explicitly keeps these bridges open.

Current verified delta: the A7 conditional transcription no longer awaits
Comparator/NanoDa confirmation. No source reading, philosophical premise or
root-path obligation was discharged. Shared policy was resolved at
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`.

The earlier global binding attempt at baseline `770102e8` stopped because an
unrelated module had not been built. This historical setup failure is resolved:
a fresh `python3 scripts/corpus.py bind-check --json` on 2026-10-31 at
`9f583a004023e7ff6bc0db72dbc057ecca02239c` completes with 730 bound results,
2 existing pins and 0 mismatches. Its A7 entry binds `hFive` to
`STMT-NB-FIVE-CONTINGENTS-POSSIBLY-CAUSEABLE`, `hTransfer` to
`STMT-NB-COUNT-CAUSABILITY-DESCENT`, and its conclusion to
`STMT-NB-ONE-CONTINGENT-POSSIBLY-CAUSEABLE`, with no problems. This resolves a
verification task, not either philosophical premise. The candidate no longer
queues that completed check.

## Reuse audit: A1's external cause and the shared modal step

Fresh materialization and reading of `NECESSARYBEING-A1-TOTALITY` (A1c,
steps 1–9) and `NECESSARYBEING-A1-EXTERNAL` (A1c2, steps 1–8) confirms two
different source routes. A1c uses its step 5 self/parts exclusion to seek a
cause or partial cause outside C and its parts. A1c2 assumes externally caused
contingents at step 3. Neither source argument is already formalized by the
A7 count transcription.

Reuse `EXTERNAL-CANDIDATE-NECESSITY`, whose theorem
`TruthCore.Results.Causality.ExternalCandidateNecessity.checks` invokes
`TruthCore.Causality.PossibleCauseOfContingency.externalCandidateIffNecessary`.
In its rigid, world-relative concrete domain, existence of an actual concrete
individual outside every actual contingent concretum is equivalent to existence
of a necessary concrete individual. This is the reusable logical core of A1c
steps 7–8 and A1c2 steps 6–7, after the source-to-model applications are supplied.
No new modal theorem or S5 suffix is needed for this **actual-world** step.
The existing theorem is not a source attribution to the survey and is not yet a
corpus inference from the survey's unbound prose statements.

The exact application obligations are: C must be an admitted causal relatum;
all relevant contingents must lie in C or its parts; a cause outside those parts
must exist actually in the same individual domain; and the modal reading of
contingency must agree. Survey concreteness means causal capability, whereas
the reused theorem takes a stipulated concrete predicate. Their identification
needs an explicit interpretation. An actual partial cause supplies causal
capability only under a compatible causal semantics; modal necessity alone
does not supply that power. The survey conclusion's capacity conjunct cannot
be silently dropped or borrowed from the theorem's concrete label.

For the first route, no-self-production by an act is not the full self/parts
exclusion: `STMT-NO-EXISTENTIAL-SELF-PRODUCTION` does not rule out joint
production by parts or transfer its mixed priority assumptions to a totality.
For the external variant, the stronger universal external-cause premise remains
explicit. Neither a local cause for each member nor the owner's accepted actual
existence alone supplies the required totality-level external cause. Compare
`docs/notes/ultimate-adequacy-integration-735.md` for the separate cumulative
route, which does not require a contingent fusion object. No premise change or
root-frontier closure follows from this reuse audit.

## Typed causal connection: preserve the actual causal witness

`NECESSARY-CAUSE-FROM-CONTINGENT-COVERAGE` formalizes the narrow A1 application
with two explicitly analyst-defined premises: `ContingentsCovered s w whole`
and `ExternalWholeCause s w whole`. The first reuses Mathlib parthood and
`UniversalFusionBoundary.Covers` for actual contingent concreta. The second
reuses `OutsideCause`, guarded by source actuality, concreteness and the
existing `Ontic.Causes` relation. It is not the unqualified A1 source causal law.
The conclusion retains one same source's actual existence, concreteness,
necessity and causal relation to this whole at this world.

The Solution imports the prior `ExternalCandidateNecessity.checks` result.
Its existential conclusion alone could select a different necessary individual;
a first prototype using an arbitrary existential choice failed for exactly
that witness mismatch. The final proof restricts only the auxiliary concrete
predicate to equality with the actual cause, applies the universal result there,
and recovers that very cause. No identity, existence, frame or causal relation
changes. `NECESSARY-BEING-FROM-CONTINGENT-COVERAGE` then projects to the existing
shared necessary-witness statement, giving the typed route an outgoing corpus
connection. Neither Challenge changes after proof search.

**Semantic grounding questions.** The causal relation means the supplied
world-relative `Ontic.Causes`, with actual source guards; a defensible efficient,
partial or sustaining interpretation must still be selected. Ordinary table
construction or device power can illustrate causal relata, but neither is
thereby a verified cause of a totality of all contingents. No undisputed empirical
instance of that latter relation is supplied. Distinctness, temporal precedence,
memberwise causation and mere overlap are excluded as substitutes for the
outside-parts premise. Mathlib parthood's partial-order properties are explicit;
no transitivity, asymmetry, foundation or necessitating sufficiency of Causes is
assumed. No universal member-to-whole causal abstraction is proved. Rival
accounts may deny the totality as a causal relatum, deny its contingency, allow
only internal causes, or use holistic/noncausal reasons. Those replies locate
the application dispute; their logical availability is not a certificate of
explanatory adequacy. The separate selected-ancestry route avoids a contingent
fusion premise, while still owing its existential-grounding interpretation.

**Premise comparison:** two new typed application premises remain OPEN; they
are not replacements asserting the truth of the unbound survey source claims.
No root-reaching premise is discharged. The causal witness retains its source
role, but the theorem does not establish a sufficient intrinsic explanation of
that witness or any divine attribute. Full build and both independent Comparator/NanoDa checks pass with the three
permitted Mathlib axioms. Full binding has 732 bound results, 2 existing pins and
0 mismatches; both new entries match exactly. Root routes and reaching-root
outputs are byte-identical to the pre-change baseline (11 routes,62 open).
The attempt retains the verification and remaining application boundaries.

### A2 bounded primary reading (2026-10-31)

Pinned and materialized the complete requested branch in order: `NECESSARYBEING-A2-QUESTION-ONE` (`a2p1.html`), `NECESSARYBEING-A2-QUESTION-TWO` (`a2p2.html`), and `NECESSARYBEING-A2-CONCLUSION` (`a2c.html`). Two independent GETs returned identical bytes for each page. No license is displayed; manifests commit hashes, locators and short incipits only, with no asserted archive fallback. The source's own title attributes were also inspected in these pinned response bytes; the ordinary text extractor omits those attributes. Alternate links to A2p2b/A2p2c and their conclusions are outside this primary three-page reading; the subsequent complete alternate-cluster reading below now covers them.

**Sequential argument.** A2p1 asks whether every concrete thing must belong to a chain both infinite and ungrounded. A2p2 asks whether individually possible situations remain individually possible when another possible situation is actual, expressly distinguishing this from joint possibility. A2c steps 1–4 define an *entire* chain as closed under its members' causes, hence ungrounded from outside, and assert that any chain-member belongs to such an entire chain. Steps 5–8 combine the reported denial of universal headless ungrounded coverage with that assertion to infer a possible concrete head, then a possible uncaused concrete. Steps 9–11 invoke the earlier reported exclusion of uncaused contingents, obtaining a possible necessary being. A separate twelve-step modal suffix escalates possible N to necessary N using necessity of possibility and the extra N-to-necessary-N reading, then applies reflexivity to obtain N.

**Positive conditional and precise gap.** Closure under all incoming causes plus absence of incoming causes *within* that chain genuinely excludes an outside cause of its head. The difficult earlier step is the coverage/head extraction, not that last observation. Step 3's existence of an entire causal chain is asserted “by definition”; an arbitrary linear chain need not remain linear when all partial causes are added. Moreover step 4 covers things already included in chains, whereas step 5 denies coverage of *every* concrete thing. A possible counterinstance outside every chain must be handled explicitly before step 6 follows. The source defines “head” as a cause or partial cause with no internal cause, so an isolated causally capable individual cannot silently be promoted to that relational head. These are missing representation/coverage obligations, not a certified refutation of every charitable reconstruction. Step 8 cites steps 5 and 6 although the uncaused-head justification is step 7.

**Vocabulary and reuse.** “Infinite” here means lacking a first member, not cardinal infinitude. “Ungrounded” excludes even partial outside causes; “cause” is a prior explanatory or partly explanatory condition, not automatically the existing existential-support relation. A2p1's concrete tooltip permits causing *or being caused*, while A2c requires capability to cause; that change needs a defended domain correspondence. Existing finite-source-path theorems do not supply the missing interpretation or entire-chain coverage merely by naming paths. Existing `TruthCore.Results.Modal.NecessaryIfExistent.positive` already yields `Dia F G w → Box F G w` from Euclidean accessibility and `NecessaryIf F G w`; reflexivity gives actual G. It can therefore reuse the modal suffix once those explicit interfaces are supplied. Neither that theorem nor the propositional suffix by itself establishes a same-individual de re necessity claim: interpreting G as existence of a necessary individual still owes the individual/world semantics and the N-to-necessary-N interface. No new modal proof is needed, and the causal possibility premise remains open.

**A1 stale-task correction.** `NECESSARY-CAUSE-FROM-CONTINGENT-COVERAGE` (`ContingentTotalityCause.necessaryCause`) already composes `STMT-A1-COVERED-CONTINGENTS`, `STMT-A1-EXTERNAL-WHOLE-CAUSE`, and `ExternalCandidateNecessity.checks`, preserving the same causal witness; `NECESSARY-BEING-FROM-CONTINGENT-COVERAGE` projects its necessary-being conclusion. The unbound source claims remain distinct: totality contingency (A1 steps 1–2), contingent causation (step 3), self/parts exclusion (step 5), and external whole cause (A1c2 steps 3,5). Complete contribution and whole-relatum applicability do not follow from exclusion of a single act's self-production or conjunction controls. Formalizing the already delivered external-cause consequence is not the next missing task.

**Premise comparison:** no premise change or discharge. This reading locates the additional entire-chain coverage/head extraction and ontology correspondence needed before any existing modal consequence can consume A2's proposed possibility argument. No source confidence, attribution or definition label establishes those obligations.

A possible-world application of `WholeRosterFoundation.actualRootExists` is a distinct conditional reuse lead, not an identification: its actual population/whole-foundation assumptions must be supplied at that world, its selected existential-ground root must match the source's uncaused causal head, and its whole roster must match the relevant entire causal coverage. Neither nonemptiness nor that correspondence follows from step 5 alone. The survey's consistency-relative tooltip for possibility also requires correspondence to the chosen metaphysical accessibility relation. This reading does not undermine the separate working claim that globally derivative reality needs foundation; it isolates A2's source-to-interface obligations.

**A2 chain refinement (same pinned bytes, 2026-10-31).** None of A2p1, A2p2 or A2c imposes linear comparability or a unique predecessor. A2c steps 1 and 3 appeal to entire-chain closure; step 2's `ungrounded` title attribute explicitly includes partial causes; steps 5–7's `infinite` and `head` attributes respectively refer to absence of a first member and absence of an internal incoming cause. Thus the preceding concern about *linear* chains is conditional, not a source-imposed obstruction. Branching predecessor-closed ancestry is a compatible reconstruction, although the page does not expressly define chain that way.

Under that reconstruction, take the reflexive finite-path ancestors of a possible coverage counterinstance x. This collection exists without well-foundedness, transitivity of the original causal relation, or choosing an infinite path, and is closed under incoming causal edges. If x has no incoming cause, it already supplies the desired uncaused individual; it need not satisfy the source's relational head formulation in step 6. Otherwise the ancestor collection contains a causal edge. If it had no internal source/head, it would be an ungrounded headless ancestry containing x, contrary to the counterinstance. An internal source is externally uncaused by closure. A distinct ancestor has an outgoing finite causal path and hence the source's cause-capability; the seed case inherits its concrete guard. This repairs the *possible uncaused conclusion* without requiring every counterinstance to be a causal head as step 6 asserts.

Consequently there is no demonstrated mathematical coverage obstruction once chain admits such ancestry and “first” means the source's no-incoming-cause head. What remains is an explicit interpretation of chain/first, causal domain and edge guards, plus the modal duality/classical existential extraction and possibility correspondence. A least predecessor comparable with every member would be a stronger reading than an internal source and is not supplied by this repair. This is a proposed structural reuse design, not a new verified result or independent defense of the reported exclusion of universal headless ungrounded coverage.

### Verified branching-ancestry repair

`HEADLESS-CAUSAL-ANCESTRY` now supplies the mathematical construction for the
branching-network reconstruction: reflexive finite-path ancestry is closed
under every incoming edge; universal predecessor availability is equivalent
to every such cone being headless; explicit excluded middle makes the latter
equivalent to absence of graph sources. The helper
`HeadlessCausalAncestry.source_of_not_headless_coverage` extracts a source from
failure of that universal coverage. The source need not cause a further node,
so it avoids the source argument's stronger relational-head claim.

The actual-world helper imports `WorldSourceRegress.actualGraph` and
`actualSource_iff`, preserving the same supplied `Ontic.Causes` and existing-node
subtype. It excludes incoming causes from actual nodes only; it assumes no
endpoint-soundness for absent nodes and identifies no cause with a ground.
Self-loops and cycles are admitted mathematically; headlessness does not assert
infinitely many distinct nodes. No WF, acyclicity, finite branching, linearity,
choice function or population premise is needed for the universal package.
Empty carriers are handled vacuously; the failure-of-coverage hypothesis in the
existence helper supplies the required nonvacuity.

The registered theorem consumes only the explicit classical logical floor;
full build, binding, zero-axiom Comparator and independent NanoDa passed. This
repairs the construction under an explicit ancestry-network interpretation,
not the source's metaphysical possibility, causal-domain or modal-individual
correspondences. God/Catholic/unique-root open unions and route costs remain
unchanged. The A2 alternate branches were unread at construction time; their complete
reading is recorded below.

### A2 alternate branches, complete linked cluster (2026-10-31)

Followed the actual `onclick` redirect targets in pinned A2p2: its negative/unsure answers lead to A2p2b; the latter's affirmative answer leads to A2c2, and negative/unsure answers lead to A2p2c. A2p2c's affirmative answer leads to A2c3; its other answers leave A2 for A3p1, which was not followed. New complete-page witnesses are `NECESSARYBEING-A2-POSSIBLE-IMPOSSIBILITY` (A2p2b), `NECESSARYBEING-A2-REVISED-DEFINITION` (A2p2c), `NECESSARYBEING-A2-CONCLUSION-TWO` (A2c2), and `NECESSARYBEING-A2-CONCLUSION-THREE` (A2c3). All four were materialized and read in full, including the relevant title attributes in hash-checked response bytes. Fresh GETs matched the previously fetched bytes. No license or archive fallback is asserted beyond the manifest's explicit rights limitation. This completes these linked A2 branches, superseding the earlier unread-alternates boundary.

**A2p2b → A2c2.** The new report is that a situation's possible impossibility implies its actual impossibility. The `impossible` title attributes specify contradiction with something necessary. A2c2's first eleven numbered causal steps repeat A2c's argument and retain its causal/chain/domain obligations. Its following modal paragraph takes contraposition of the report: a possible situation cannot become impossible, hence is necessarily possible. In a classical modal representation with impossibility as negated possibility, the report has shape `◇¬◇P → ¬◇P`; contraposition and duality yield `◇P → □◇P`. This is an alternative input for the same necessity-of-possibility principle, not a rejection of that principle or an independently proved frame condition. A2c2 then repeats the twelve-step N suffix, including possible-N to possible-necessary-N and the final reflexivity step. Existing modal results remain the reuse target; there is no new modal theorem to implement merely because the respondent reaches that interface through another question.

**A2p2c → A2c3.** A2p2c expressly stipulates a revised class: a thing must by nature exist when it would automatically exist if its existence were even possible; everything else is called contingent. It then asks the respondent *again* to accept the exclusion of uncaused contingent things under that definition. A2c3 repeats the eleven-step causal possibility argument and replaces the full S5 suffix with a final paragraph invoking precisely that stipulation to infer actual concrete existence. The causal premise therefore has a changed classification; the original no-uncaused-contingents report cannot simply be carried over unchanged. The prose still uses the familiar must-exist and contingent tooltips, so the explicit redefinition and reaffirmation must govern this branch's reading rather than those labels silently restoring the original semantics.

**Premise and witness boundary.** A2c2 retains the causal premises, adds the reported possible-impossibility conditional in place of the original possibility-independence report, and reaches the same explicit modal interface. A2c3 trades that suffix for an automatic-actuality stipulation and a newly reaffirmed causal exclusion for its complementary class. This does not establish a globally weaker bundle. A predicate satisfying a possible-existence-to-actual-existence conditional is not thereby the existing `NecessaryAt` predicate: scope at worlds, accessibility, and persistence of the same individual's class membership must be supplied. In particular, learning at a possible world that some individual satisfies the revised class does not by itself apply that individual's conditional at the actual world. A source-faithful formal design would distinguish this revised class and its transport/actuality reading from de re all-accessible-world existence; merely calling both “necessary” would hide the burden. Both alternate conclusions retain cause-capability, not ordinary physicality, as their concrete meaning. No new source claim, formal result or root-premise discharge follows from this reading.

### Same-individual causal/modal composition

`POSSIBLE-CAUSAL-SOURCE-NECESSITY` imports the verified full-ancestry source
extraction and existing actual-source correspondence. Its `sameSource` helper
keeps the accessible world v and individual c: c exists and has no existing
incoming cause at v; the existing global `LocalCausalPrinciple` makes c
necessary there; Euclidean accessibility transports that SAME c's existence to
every successor of w, while actual reflexivity supplies its existence at w.
The registered result projects this witness to the existing
`STMT-KANT-CONVERSION-NECESSARY-WITNESS`, with nine existing argument consumers.
It does not assert that c is uncaused at w.

The five inputs are explicit excluded middle, the existing global local causal
principle, Euclidean accessibility, reflexivity at w, and accessible failure of
full headless-cone coverage. The latter four remain open commitments; global
causal scope/distinctness is stronger than this proof needs, so no minimality
claim is made. No concreteness or causal capability is inferred for an isolated
source, and the result does not formalize A2c3's revised necessity class. It is
an unattributed conditional reconstruction, not source endorsement or proof of
metaphysical possibility. No de dicto existential necessitation, universal
accessibility, transitivity, WF or cause-to-ground identification is used.

Full build, exact binding, zero-permitted-axiom Comparator and independent
NanoDa passed. The shared necessary-being endpoint gains cost4/direct5 under
the existing classical floor; its old costs2,2,3 remain unchanged. Its reachable
premise union grows13→17 through alternative dependencies, removing none.
God/Catholic/unique-root route costs and unions remain unchanged. No
philosophical premise is discharged.

### A3 complete linked reading and reuse design (2026-10-31)

Pinned/materialized/read in source order A3p1 → A3p2 → A3p3 → A3c, then A3p3b → A3c2 and A3p3c → A3c3. Exact witness IDs are `NECESSARYBEING-A3P1`, `NECESSARYBEING-A3P2`, `NECESSARYBEING-A3P3`, `NECESSARYBEING-A3C`, `NECESSARYBEING-A3P3B`, `NECESSARYBEING-A3C2`, `NECESSARYBEING-A3P3C`, `NECESSARYBEING-A3C3`. Each complete response matched two GETs; relevant title attributes were read in the same hash-checked bytes. Only actual A3 redirect targets were traversed. Negative/unsure A3p1 exits to A4; negative/unsure A3p2 and A3p3c exit to A5. Those exits were not fetched. Rights remain undisplayed; manifests assert no archived fallback.

**Ordered argument.** A3p1 asks whether a possible event can be impossible to cause; its negative answer selects the argument. Its event title fixes a transition's before/after states as essential to event identity, and its uncausable title concerns a prior condition capable of partly explaining that event. A3p2 asks whether all contingent existence could begin, with a Big Bang offered only as illustration. A3p3 supplies the familiar possibility-independence report. A3c steps 1–4 infer the possibility of a transition from no contingent things to some. Step 5 invokes possible causability of every possible event; step 6 infers possible caused occurrence of that transition. Steps 7–8 exclude a contingent cause by requiring the cause to be prior to the first contingent existence. Steps 9–11 obtain a possible noncontingent cause, whose causing supplies concreteness, then a possible Necessary Being. The standard twelve-step modal suffix follows.

**Scope and new obligations.** A3c's note after step 11 expressly denies that “all contingent things” rigidly names a fixed collection. The event is the first occurrence of *some* contingent things, preceded by none; it is not a joint beginning of exactly the actual world's roster, nor a sum inferred contingent from its members. The source's event-identity restriction makes step 6 stronger than possibility of an analogous event with different essential states: possible causation must preserve the transition from no contingents. The cause tooltip in the conclusion is a prior explanatory/partly explanatory condition. Step 7's positive argument works when this priority requires an existing causal bearer on the no-contingents side of the transition. Mere explanatory ordering, simultaneous production, or a nonexistent reason does not yet supply that condition. Conversely, the source's contradiction argument is substantive under the intended temporal-before/existence reading; it need not assume that a cause of each member is a cause of their fusion. Converting this event-cause to the existing concrete individual/existence semantics remains explicit. The causal bearer is capable by its possible exercise; ordinary physicality and the existing intervention-response definition are not automatically identical to that capability.

**Closest existing consequence.** `PossibleCauseOfContingency.possibleExternalCauseYieldsNecessary` already derives `NecessaryConcreteAt s w` from `UniversalFrame s` and `PossiblyExternallyCausedAt s w`; `causalOpportunityAndPossibleBeginning` supplies that latter interface from `PossiblyBeginsAt` and `CausalOpportunityAt`. Its proof preserves the same rigid bearer from the accessible caused history to the actual world and all accessible worlds. The source-informed module explicitly records that its begins predicate is not itself an encoded temporal transition. Hence A3 does not need a duplicate external-candidate or modal suffix proof. To apply it, the fresh source work would be a faithful bridge from the state-preserving causability of the first transition and existing-before-cause condition to an existing concrete cause outside all contingent concrete individuals in that history. Simply assuming `CausalOpportunityAt` packages that substantive bridge rather than proving the source's steps 3–8. `UniversalFrame` is the existing theorem's sufficient modal scope, not something established by the respondent's prose. The propositional NecessaryIfExistent suffix remains separately reusable if chosen instead; neither route licenses exchanging `□∃` for `∃□` without the explicit individual semantics.

**Alternates and premise comparison.** A3p3b/A3c2 replace the original possibility report by possible-impossibility implying actual impossibility, then recover the same necessity-of-possibility principle and modal suffix, as in A2c2. A3p3c instead stipulates automatic existence if possible and re-asks *whether the beginning of all contingent things is possible under the revised class*. Its affirmative path A3c3 repeats the eleven causal steps then appeals directly to the stipulation. Unlike A2p2c, it does not re-ask no-uncaused-contingents; that premise is not used by the A3 argument. Its revised contingent extension and individual/world scope cannot silently be identified with ordinary NecessaryAt. Compared with A2, A3 replaces the exclusion of universal headless ungrounded ancestry and the no-uncaused-contingents report by possible universal contingent beginning and universal possible-event causability, plus its temporal-priority exclusion. It leaves actual contingent beginnings possibly uncaused: possible causal availability is not actual universal PSR. No weaker-overall-bundle or actual-world causal-foundation claim follows. All source premises and representation bridges remain open; this reading makes no premise discharge and adds no formal/source claims.

**A2c2 delivery integrity investigation (2026-10-31, PR821).** CI at 18:06:15 UTC received response hash `4fa48eaea30c51a151ca493514e1c265f12841afa8ac34dbb3d6bc6a0140351d` instead of pinned `4d6e116fa475f73416f9d1c6a36341e7841a000904592f18d5e45d4dec0df949`. The log supplies neither failed bytes nor headers, so the changed content and cause are presently unknown. At 18:12 UTC the exact existing downloader (fixed `truth-core-source-evidence/1`, identity encoding) still returned the pinned 9597 bytes; default urllib and browser user agents, HTTP/HTTPS and www/bare host variants also matched exactly. The local response was nginx, Last-Modified 2017-08-02 02:17:35 GMT; DNS resolved to 198.91.82.219. No local proxy environment was present. These observations exclude a reproduced local user-agent difference but do not exclude runner/network-specific delivery or a transient response. Exact URL and wildcard CDX queries for both host forms returned no capture; no legitimate matching archive fallback was found. No pin or interpretation was changed. A safe repair first requires retaining the failed runner response bytes, headers and resolution, then comparing and reading them; repinning a hash without those bytes or ignoring response differences would not repair source integrity.

**CI delivery follow-up.** The unchanged-head retry of run `41227428523`,
attempt2/job `124617249783`, verified all four original pinned A2 snapshots at
18:18:06 UTC, including the original A2c2 hash `4d6e116fa475`. No source manifest,
verification rule or proof input changed. The first differing response remains
unexplained because its bytes were not retained; this is not evidence that the
source text changed. If reproduced, retain the failing response before any
repin. PR #821 subsequently passed all checks and merged.

### Verified frame-scope reduction for possible external causes

`LOCAL-FRAME-POSSIBLE-EXTERNAL-CAUSE` keeps exactly the old Scenario,
`PossiblyBeginsAt` and `CausalOpportunityAt`, while replacing global
`UniversalFrame` with `Euclidean` and `ActualReflexive` at the selected world.
Its same-cause helper reuses `ExternalCandidateNecessity.checks` with the
already established singleton-concrete selection technique; it retains the
original cause's concrete evidence and preserves its ontic/existence identity.
Only existence/necessity transfer to the actual standpoint; its totality-causing
role is asserted at the accessible history, not automatically here. The old
classical logical basis and permitted Mathlib axioms are unchanged.

`localFrameOfUniversal` proves the old frame premise supplies both replacement
conditions. The existing Boolean identity-frame controls separate these frame
fragments, but cannot witness the whole causal bundle: identity accessibility
has no contingent existents, so possible contingent beginning fails there. No
strictness or minimality certificate for the complete causal-premise bundle is
claimed. A count of four named inputs versus three is not a strength metric.
The beginning and external-opportunity commitments remain open.

`SCENARIO-NECESSARY-CONCRETE-TO-NECESSARY-BEARER` is explicitly an assembly
projection: retain the SAME witness's actual/necessary existence in the SAME
ontic model, dropping only the supplied concrete conjunct. It connects this
Scenario endpoint to the shared necessary-being statement without changing
ontology or independently advancing premise truth. Full build, binding, both
Comparator/NanoDa checks passed. Source temporal/event correspondence, concrete
capability and metaphysical modal applicability remain unproved.

### Conditional A7 temporal-count connection (2026-10-31)

`COUNT-TEMPORAL-NECESSARY-BEING` connects the existing count result to the shared actual necessary-individual conclusion, rather than repeating its opaque decrement proof. `CountTemporalNecessity` reuses the same `TemporalHistory.History`. AtLeastAt means an injective Fin n family of concrete, world-relative contingent bearers present at one time. A guarded caused threshold supplies a concrete cause present earlier, an edge in a separate count-situation causal relation, the target count, and absence of that count at every earlier time. PossibleCount supplies an accessible history with those guards. The new typed five and decrement premises are OPEN configurations, not silent strengthenings of the old sourced count claims.

Six inputs are retained: typed five opportunity, typed decrement, one-way temporal-presence-to-world-existence, explicit EM, Euclidean accessibility and reflexivity at the designated world. The proof imports `NecessaryBeingCountDescent.fiveToOne` instantiated at PossibleCount. At count one, contingency of its SAME earlier cause would give the forbidden earlier singleton threshold. Presence supplies existence in that history; EM yields necessity of that very cause, and the local modal conditions transport its existence/necessity to the designated world. The non-corpus sameCause helper retains its original concrete guard and count-one causal role at the accessible history; no causal role at the designated world is asserted. The corpus endpoint projects to existing `STMT-KANT-CONVERSION-NECESSARY-WITNESS`.

This is genuine conditional derivation/configuration progress under policy #824, with no philosophical truth discharge. No universal frame, now-slice coherence, global PSR, well-foundedness, causal-grounding conversion, uniqueness or God identification is assumed or concluded. Temporal population coverage, causal interpretation, concrete-domain applicability, modal scope and the ever-history existence bridge remain explicit framework commitments. Focused Lean checks pass; both proof helpers/endpoints have zero axioms. Challenge SHA256 remains `e3834ccaaec1c02e679088b415f86e778fe2bcbc62ed957d1114bc64520d77fc`. Corpus and whitespace checks pass; Comparator/NanoDa integration is coordinator-owned and not yet claimed here. The new attempt `ATTEMPT-COUNT-TEMPORAL-NECESSARY-BEING-20261031` retains the exact premise comparison and focused evidence. Source extraction/argument registration for other family commitments remains queued.

Retained strength in the typed count configuration: `CausedThreshold` requires absence at every earlier time, while the witness proof only uses absence at the cause time. This first-threshold guard is not silently attributed to the source. Weakening it to cause-time absence is a separate configuration opportunity; the frozen current Challenge remains unchanged.


### A2 main-branch source extraction (2026-11-01)

Five qualified claims now use the existing public A2 witnesses:

| Claim | Statement and precise locator |
| --- | --- |
| `NB-SURVEY-A2-REPORTED-COVERAGE-DENIAL` | New `STMT-NB-A2-REPORTED-COVERAGE-DENIAL`; `NECESSARYBEING-A2-QUESTION-ONE`, A2P1 question/tooltips and negative-answer continuation. Conditional answer reading only: no actual assent or truth. A2c5's explicit reported denial uses a narrower domain. |
| `NB-SURVEY-A2-ENTIRE-MEMBER-CLOSURE` | New `STMT-NB-A2-ENTIRE-MEMBER-CLOSURE`; `NECESSARYBEING-A2-CONCLUSION`, A2C steps1–4,7 and title attributes. Necessity scope and membership rather than whole-chain extension are retained. |
| `NB-SURVEY-A2-POSSIBLE-HEAD-AND-UNCAUSED` | New `STMT-NB-A2-POSSIBLE-HEAD-AND-UNCAUSED`; same witness, steps5–8. The source's disputed conditional retains its stronger relational head, domain shift and isolated-source gap. |
| `NB-SURVEY-A2-CONTINGENTS-CAUSED` | Reuses `STMT-NB-A1-CONTINGENTS-CAUSED`; same witness, step9. This unqualified reported cause is not the stronger global/distinct/existing-cause LocalCausalPrinciple or a grounding relation. |
| `NB-SURVEY-A2-POSSIBILITY-INVARIANCE` | New `STMT-NB-A2-POSSIBILITY-INVARIANCE`; `NECESSARYBEING-A2-QUESTION-TWO`, A2P2 question/note. Conditional affirmative-answer reading; individual possibility does not require joint possibility. |

All claim witnesses were materialized/read before extraction, including title attributes in their hash-verified bytes. Existing objective-possibility and existential N-to-Box-N source statements remain unchanged. The four new source commitments intentionally have no Lean declaration: no exact formal interpretation or checked source inference is advertised. No new Challenge/Solution, inference or result is introduced. This is extraction/reuse progress with **no premise or root-frontier discharge**.

Source-gloss definitions and `DISAMB-NB-A2-DOMAIN-AND-ANCESTRY` preserve A2P1 cause-OR-effect capability versus A2c cause capability. Entire-chain closure concerns causes of members, not causal production of a collective whole. Infinite means lacking a first member, not cardinal infinity; an isolated graph source need not be a cause/partial-cause head. Existing `HEADLESS-CAUSAL-ANCESTRY` and `POSSIBLE-CAUSAL-SOURCE-NECESSITY` remain unattributed mathematical consequences under their own dictionaries. Applying them still needs chain/head correspondence, capable/actual causal-domain guards, and objective/modal/rigid-individual correspondence. Mere consistency is not explanatory adequacy.

Next coherent extraction is A2P2b/A2c2's alternate modal input, then A2P2c/A2c3's revised classification and reaffirmed report, using their existing public witnesses. Continue afterward with source-ordered A3 extraction and the remaining public campaign queue; no additional later-family witness coverage is delivered here. The candidate and existing first-pass attempt preserve this boundary. Source pins, old claims/types, proof modules and shared generators are unchanged.


### A2 alternate source extraction (2026-11-01)

Four qualified claims use the existing public alternate witnesses:

| Claim / new unbound statement | Precise witness locator |
| --- | --- |
| `NB-SURVEY-A2-ALT-POSSIBLE-IMPOSSIBILITY` / `STMT-NB-A2-ALT-POSSIBLE-IMPOSSIBILITY` | `NECESSARYBEING-A2-CONCLUSION-TWO`, A2C2 modal paragraph after causal step11, with A2P2B question context. Conditional affirmative report and proposed contraposition/duality, not actual assent or a proved modal axiom. |
| `NB-SURVEY-A2-REVISED-MUST-EXIST` / `STMT-NB-A2-REVISED-MUST-EXIST` | `NECESSARYBEING-A2-REVISED-DEFINITION`, A2P2C opening author stipulation and complementary class. A definition does not independently supply an existing bearer. |
| `NB-SURVEY-A2-REVISED-CONTINGENTS-CAUSED` / `STMT-NB-A2-REVISED-CONTINGENTS-CAUSED` | `NECESSARYBEING-A2-CONCLUSION-THREE`, A2C3 steps9–11 under the P2C reaffirmation question. The changed complementary class makes this a distinct premise from ordinary contingent causation. |
| `NB-SURVEY-A2-REVISED-ACTUALITY-CONCLUSION` / `STMT-NB-A2-REVISED-ACTUALITY-CONCLUSION` | Same witness, final actuality paragraph after step11. Attributed conditional conclusion through the revised stipulation, not a certified actual or rigid necessary witness. |

All four witnesses were freshly materialized/read, including hash-verified raw title attributes. Independent read-only fidelity review found no findings; this accepts the source readings, not their truth or formal consequence. Main causal-prefix readings and existing modal results remain reused without duplicate claims/proofs. The four new statements intentionally have no Lean declaration; no new Challenge, inference or result is introduced.

The editorial tag κ distinguishes the revised must-exist class and its complementary contingency. Its would/automatic wording remains unbound: no material-implication classification, ordinary NecessaryAt, counterfactual calculus, existential N-to-Box-N identity or actual-world membership/witness persistence is selected. A2C2 changes a modal report while retaining the ordinary nominal class; A2P2C/A2C3 changes the class and re-asks causal exclusion. Stock tooltips do not erase the explicit stipulation. Source pins, old claims/types and proof modules are unchanged; **no premise truth or root-frontier discharge** is claimed.

A2 main/alternate substantive extraction is complete at these stated boundaries. The candidate remains for source-ordered A3 extraction on its existing public witnesses, then the remaining public A4–A10 witness/reading/extraction queue. This batch delivers no additional later-family witnesses or private reading history and requests no PHP answer endpoint.


### A3 main source extraction and conditional reuse (2026-11-01)

Freshly materialized and read complete `NECESSARYBEING-A3P1`, `NECESSARYBEING-A3P2`, `NECESSARYBEING-A3P3` and `NECESSARYBEING-A3C`, including essential raw HTML title attributes. Five unbound source readings are `NB-SURVEY-A3-POSSIBLE-EVENT-CAUSABILITY` (P1 question/negative continuation), `NB-SURVEY-A3-POSSIBLE-CONTINGENT-BEGINNING` (P2 question/affirmative continuation), `NB-SURVEY-A3-NONRIGID-FIRST-TRANSITION` (C1–4 and note after11), `NB-SURVEY-A3-PRIOR-CAUSE-EXCLUSION` (C5–9) and `NB-SURVEY-A3-POSSIBLE-NECESSARY-CAUSE` (C9–11). Question reports are conditional; the remaining inferences are authorial assertions, not independent truth. The same event retains its essential before/after states; “all” means no contingents before some first appear, not a rigid actual roster. Possible causability does not require every actual event actually to be caused.

The positive exclusion argument is substantive under an earlier-existing causal-condition reading: a contingent cause on the no-contingents side contradicts that side. But the cause tooltip's prior explanatory condition does not alone establish an existing concrete individual, temporal presence, or a totality-cause dictionary. Mere atemporal ordering, simultaneous production or a nonexistent reason cannot supply the reading. These remain unattributed OPEN application bridges; `STMT-SCENARIO-CAUSAL-OPPORTUNITY` is not source-attributed by renaming the assertion. Existing `LOCAL-FRAME-POSSIBLE-EXTERNAL-CAUSE` requires `STMT-EUCLIDEAN-FRAME`, `STMT-ACTUAL-MODAL-REFLEXIVITY`, `STMT-SCENARIO-POSSIBLY-BEGINS` and `STMT-SCENARIO-CAUSAL-OPPORTUNITY`; its same-bearer output can feed `SCENARIO-NECESSARY-CONCRETE-TO-NECESSARY-BEARER`. Those explicit conditional consequences are not a source-to-model bridge or fresh premise defense. The existing A2 possibility-invariance report/modal suffix is reused without a duplicate proof or claim of □∃→∃□.

Two source-only glosses define essential-state events/prior explanatory conditions and the first nonrigid transition; neither introduces a Lean framework. No new source witness, argument/result, Lean file or philosophical discharge. Next extraction is A3P3B/C2 then A3P3C/C3 on existing public witnesses, retaining the revised beginning question under its changed classification. The candidate remains open for that extraction and the remaining public A4–A10 witness/reading/extraction queue; this batch delivers no private later-family witnesses or reading history.

Independent Root and Pages fidelity reviews materialized/read all four main witnesses and verified raw HTML/title hashes without findings. This accepts source fidelity only, not premise truth or Lean consequence.


### A3 alternate extraction and exact semantic reuse (2026-11-01)

Materialized/read the full existing `NECESSARYBEING-A3P3B`, `NECESSARYBEING-A3C2`, `NECESSARYBEING-A3P3C` and `NECESSARYBEING-A3C3` witnesses and verified raw HTML SHA256 before reading title attributes. Exact comparisons of materialized text, not similarity rankings, give the following bounded delta:

| New source claim | Statement and precise witness scope |
| --- | --- |
| `NB-SURVEY-A3-ALT-POSSIBLE-IMPOSSIBILITY` | Reuses `STMT-NB-A2-ALT-POSSIBLE-IMPOSSIBILITY`. A3P3B question/choices match A2P2B; A3C2's modal paragraph after step11 and its note, plus the full suffix, match A2C2. The conditional report and proposed contraposition/duality are not actual assent or a certified S5 principle. |
| `NB-SURVEY-A3-REVISED-MUST-EXIST` | Reuses `STMT-NB-A2-REVISED-MUST-EXIST`. A3P3C opening stipulation/complement exactly matches A2P2C. κ is the same editorial source-class tag, not a new definition, Lean relation or ordinary `NecessaryAt`. |
| `NB-SURVEY-A3-REVISED-POSSIBLE-BEGINNING` | NEW `STMT-NB-A3-REVISED-POSSIBLE-BEGINNING`. A3P3C's question reaffirms possible beginning under the revised contingent complement. This is distinct from the ordinary A3P2 report and from A2P2C's reaffirmed no-uncaused-contingents input. |
| `NB-SURVEY-A3-REVISED-POSSIBLE-NECESSARY-CAUSE` | NEW `STMT-NB-A3-REVISED-POSSIBLE-NECESSARY-CAUSE`. A3C3 steps1–11 and the following nonrigid-all note apply the causal prefix under κ. The words match A3 main, but the class scope changes. One conditional argument reading preserves the transition, possible causation, exclusion and possible κ-cause inference without duplicating intermediate proofs. |
| `NB-SURVEY-A3-REVISED-ACTUALITY-CONCLUSION` | Reuses `STMT-NB-A2-REVISED-ACTUALITY-CONCLUSION`. A3C3's final actuality paragraph after the note and its ending exactly match A2C3; only its preceding possibility argument differs. This is attributed conditional actuality, not a definition supplying an actual rigid bearer. |

The unchanged ordinary-class A3C2 prefix reuses all A3 main readings. General possible-event causability and essential-state event/nonrigid glosses remain reusable in A3C3, but ordinary-class beginning, exclusion and possible-necessary-cause statements are not silently generalized to every classification. A2's revised contingent-cause premise is not imported into A3. The prior explanatory condition still does not alone establish an earlier existing concrete individual; the SAME event, temporal bearer, revised-class persistence and actual-world/rigid-witness correspondence remain OPEN. Stock ordinary tooltips do not erase the explicit revised stipulation. Existing modal and Scenario results retain their own hypotheses; no source soundness, new modal proof or source-to-model identity is credited.

Five qualified claims thus add only two bare statements, no glossary, pin, Lean module, argument or result. The existing alternate/revised disambiguation is extended without changing old meanings. These records cover the materially different A3 main/alternate readings at their stated boundaries, so the existing candidate now advances to the remaining public **A4** witness/reading/extraction range, followed by A5–A10. This is neither campaign completion nor public delivery of private later-family witness/read history, and no philosophical premise or root obligation is discharged. No PHP answer endpoint was requested.

Public A3 main delivery: PR #842 merged as `f669db3d` after exact-head review and required CI passed. Independent A3 alternate fidelity review checked all four materialized witnesses and hash-verified raw titles, directly comparing the three reused A2 meanings; no findings. Source fidelity does not establish soundness, reality correspondence or a new formal consequence. The fuller research A4 queue and public remaining witness/delivery queue retain their separate scopes.

### A4 main property-transfer readings with scoped reductio (2026-11-01)

Materialized/read complete `NECESSARYBEING-A4P1/P2/P3/P4/C`, verifying the pinned raw HTML SHA256 before reading title attributes. Four linked alternate pages informed the independent research review as context; their public witness/reading/extraction delivery remains pending. This main batch adds eight qualified claims, six bare statements, two narrow property/first-exemplification glosses and one scope disambiguation. Ordinary contingent beginning and possibility invariance reuse existing propositions, not new A4 duplicates.

| Claim / statement | Precise main witness scope |
| --- | --- |
| `NB-SURVEY-A4-POSSIBLE-CAUSED-THING` / new `STMT-NB-A4-POSSIBLE-CAUSED-THING` | A4P1 question/affirmative continuation and possible/cause titles; A4C2 recalls the report. Possible caused existence is not actual causation or a guarded concrete bearer. |
| `NB-SURVEY-A4-PROPERTY-FIRST-CAUSE-TRANSFER` / new corresponding statement | A4P2 complete question, redness illustration and property/instance/first-exemplification/cause titles. Separate first-P and caused-P possibilities are not assumed to share worlds or bearers. The antecedent does not require caused acquisition of P. |
| `NB-SURVEY-A4-POSSIBLE-CONTINGENT-BEGINNING` / reused `STMT-NB-A3-POSSIBLE-CONTINGENT-BEGINNING` | A4P3 question/affirmative continuation; C5 and note2 retain the ordinary nonrigid none-to-some meaning. This is not the revised alternate-class question. |
| `NB-SURVEY-A4-POSSIBILITY-INVARIANCE` / reused `STMT-NB-A2-POSSIBILITY-INVARIANCE` | A4P4 complete question/examples/non-joint-possibility note. Its text and the following C modal suffix exactly match A3. No duplicate modal proof or frame characterization. |
| `NB-SURVEY-A4-CAUSED-CONTINGENT-UNDER-NO-POSSIBLE-NECESSARY` / new corresponding statement | A4C1–4 and note1 after17. The author classifies a possible caused thing inside the no-possible-Necessary-Being supposition; the caused-thing/cause-capable-class correspondence is not independently supplied. |
| `NB-SURVEY-A4-POSSIBLE-CAUSED-FIRST-CONTINGENCY` / new corresponding statement | A4C4–9 and notes1–2. Contingency is substituted as P and the transfer is applied, still UNDER that supposition. Its admissibility/intension across histories and first-event correspondence remain open. |
| `NB-SURVEY-A4-PRIOR-CAUSE-EXCLUSION-UNDER-SUPPOSITION` / new corresponding statement | A4C10–14, cause/event/Necessary Being titles and note2. The possible noncontingent cause remains inside the reductio; prior explanatory condition alone does not supply an earlier existing concrete bearer. |
| `NB-SURVEY-A4-REDUCTIO-POSSIBLE-NECESSARY-BEING` / new corresponding statement | A4C14–17 and transition to the reused modal suffix. Only possible Necessary Being is discharged from the supposition, not unconditional caused-first opportunity or its hypothetical causal witness. |

The two property glosses preserve the source's term/concept/abstract-entity account and its permission to use bearer talk. Neither commits to abstract properties as causal objects or a new formal predicate framework. One first-exemplification title includes “first time” and another omits it; the question's first-instance wording and main conclusion's note2 fix the context. The main A4C event title explicitly retains essential states. The revised A4C3 title is shorter and omits that phrase; future alternate extraction must inspect that scope rather than copy every main qualifier automatically.

The source has no explicit restriction against causal or modal properties. Admissibility of contingency, fixed intension with history-dependent extensions, and transfer between separate possibilities remain substantive commitments. Restricting the antecedent to causing acquisition of P or inventing an admissibility exclusion merely to secure the inference would change the source. The existing rooted-causal-property stress outline remains unverified: possible first-P is unestablished, so no source inconsistency or philosophical refutation follows.

Existing `LocalFramePossibleExternalCause` and `ScenarioNecessaryWitness` retain their exact guarded hypotheses. A bridge would have to preserve the accessible history, SAME essential event and existing concrete causal bearer, source classification, externality and the reductio's scope. Neither the general report nor the discharged possibility conclusion alone establishes unconditional `CausalOpportunityAt`; no stronger bridge is source-attributed. Euclidean accessibility, actual reflexivity and rigid-individual transport are not obtained merely from the source's S5 label. Possible cause or de dicto Necessary Being is not an actual rigid necessary causal witness.

No Lean, inference, result, pin or philosophical premise truth changes. This batch explicitly delivers the five A4 main witness manifests, raising the public passage count from394 to399; no other private witness is included. Main attribution is now boundedly recorded; the candidate remains at **A4P4B/C2, then A4P4C/C3**, before later families. Private witness/read history does not complete the public campaign, and no PHP answer endpoint was requested.

Root and independent fidelity reviews read all five main witnesses and raw hash-verified titles without substantive findings; the latter also inspected four alternate contexts. This accepts source fidelity only, not premise truth or a new formal consequence.

### A4 alternate public extraction and exact reuse (2026-11-01)

This batch explicitly delivers only the four existing pinned witness manifests `NECESSARYBEING-A4P4B`, `NECESSARYBEING-A4C2`, `NECESSARYBEING-A4P4C`, and `NECESSARYBEING-A4C3`, raising public passages399→403. Five qualified claims add only one bare statement:

| Claim | Reused meaning or new scoped reading |
| --- | --- |
| `NB-SURVEY-A4-ALT-POSSIBLE-IMPOSSIBILITY` | Reuses `STMT-NB-A2-ALT-POSSIBLE-IMPOSSIBILITY`; C2 modal paragraph after17/notes, with P4B question context. The question and modal suffix match A2 exactly, without actual assent or a verified S5/frame principle. |
| `NB-SURVEY-A4-REVISED-MUST-EXIST` | Reuses `STMT-NB-A2-REVISED-MUST-EXIST`; P4C opening automatic-actuality/complement stipulation. No new class definition or selected material/counterfactual semantics. |
| `NB-SURVEY-A4-REVISED-POSSIBLE-BEGINNING` | Reuses `STMT-NB-A3-REVISED-POSSIBLE-BEGINNING`; P4C reaffirmation/affirmative continuation. Its entire page matches A3P3C. This is not ordinary A4P3 beginning or A2’s causal-exclusion report. |
| `NB-SURVEY-A4-REVISED-PROPERTY-REDUCTIO` | NEW `STMT-NB-A4-REVISED-PROPERTY-REDUCTIO`; C3 steps1–17/notes1–2. Prefix words match main C but κ changes classification. NoPossibleκNB remains hypothetical through3–14; only possibility is discharged17. |
| `NB-SURVEY-A4-REVISED-ACTUALITY-CONCLUSION` | Reuses `STMT-NB-A2-REVISED-ACTUALITY-CONCLUSION`; C3 final paragraph after17/notes matches A2C3. Automatic actuality consumes discharged17, not hypothetical13 cause; actual causal exercise is not inferred. |

The ordinary-class C2 prefix reuses A4 main. Revised C3 uses property transfer and reductio, so it is not aliased to A3’s direct revised possible-cause argument. C3’s shorter event title omits main C’s essential-state qualification: attribute neither that criterion nor its negation. The new reading has no stronger essential-state event definition link; the existing A4 disambiguation distinguishes contexts explicitly. Nonrigid first-exemplification, separate possibilities, property admissibility/intension, earlier existing concrete bearer, class persistence and modal/actual rigid-witness correspondence remain OPEN. No unconditional Scenario opportunity or hypothetical causal witness is exported after the reductio.

All four witnesses were materialized/read with raw SHA/title checks and exact reused-text comparisons. Root and an independent adversary accepted source fidelity without P1 findings; that is neither soundness nor premise truth. No glossary, framework, Lean, argument, result, source kind, dependency, repin or archive fallback is introduced. The other65 private manifests and later private read history are not delivered or copied. Candidate progression to A5 marks only this completed reading range; the remaining public A5–A10 witness/reading/extraction queue remains open, without campaign completion or PHP answer requests.


### Independent A8 source delivery (2026-11-01)

A8 is published as one bounded source dependency for the separate analyst limitation configuration, independently of the still-queued A5–A7 work. The public source cursor remains **A5**; this delivery does not imply that intervening families were processed publicly. It reuses already-public A2 modal/nominal/concrete meanings, with no A5–A7 dependency.

The exact eight unchanged manifests are `NECESSARYBEING-A8P1/P2/P3/P4/C/P2B/P3B/C2`. Seven qualified claims add five bare statements, two source glosses and one disambiguation:

| Reading | Precise witness/locator and scope |
| --- | --- |
| Limiting-property definition | P1 entire introduction/property/entails titles; deficiency-entailing limitation and necessary universal inclusion, not a selected full existential classifier. |
| Powerful Necessary Being nonlimiting | Negative P2 report, C9; conditional evaluative commitment, not actual assent or independently established possibility/quantitative omnipotence. |
| Possible nonexistence limiting | Affirmative P3 report, C3; a separate main-branch commitment, not actual absence or an alternate-branch requirement. |
| Main limitation reductio | C1–11; source2 scoped causal-concrete classification, explicit C4 BACKWARD closure, separate source6 powerful-NB→concrete implication; possibility discharged10–11 only. |
| Main possibility invariance | P4 and C modal paragraph after11; exact P4 match to existing A2 meaning, without a new modal proof or rigid individual. |
| Alternate vacuous limitation reductio | C2steps1–10, explicit vacuity after3 and compressed deficiency/transitivity5–7; no affirmative main-P3 or powerlessness report required. |
| Alternate possibility invariance | P3B entire shorter question/examples/non-joint note and C2 suffix after10; same A2 proposition content despite nonidentical wording, separately located for unambiguous witness binding. |

All eight materialized bodies and raw SHA-verified titles were read. Independent Root fidelity reviews accepted main and alternate: backwards closure and source2/source6 scope are faithful; no full uniform-deficiency semantics or Scott bridge is selected. P2B’s three answer links all lead to P3B, so no affirmative powerlessness answer is invented. No κ branch exists here. Alternate5–7 remains an attributed compressed inference, not an illicit uniform deficiency chosen from varying bearers. Admission of a deficiency property is distinct from an actual deficient bearer. Source assertions, reports, typed conditional consequences and premise truth remain separate.

The two glosses distinguish modal inclusion from stronger relevant/nontrivial consequence and deficiency limitation from root composition/esse/priority horns or Scott positivity. Property/deficiency admission, intension/uniformity, evaluative applicability, causal-concrete/domain and modal/actual rigid-witness correspondence remain OPEN. No empirical powerful Necessary Being, God naming, uniqueness, all-attribute result, source soundness or independently justified possibility follows. A separate analyst proof is not included here, and no bare source statement receives a Lean binding.

This explicit named manifest delta raises public coverage **403→411**. Scoped live verification selects these eight; the other403 public passages receive offline checks only. No other private later witnesses/history or A5–A7/A9–A10 readings are copied. No pin, selector, source kind/dependency, archive fallback, PHP answer/session request, argument/result, truth flag or root-premise closure changes. Public A5 remains queued; A8 coverage is neither campaign completion nor an owner choice of its philosophical premises.


### Independent A9 MAIN source delivery (2026-11-01)

Deliver exactly nine unchanged A9 witnesses `P1/P1B/P2/P3/C/P3B/C2/P3C/C3`, including full alternate context, with five MAIN claims/four bare statements, one NT glossary/disambiguation and a minimal existing ordinary-entailment provenance extension. This compares a genuinely different source argument with the already-public ordinary-property work; it does not copy intervening private history or advance the public **A5** cursor.

| Main reading | Precise source scope |
| --- | --- |
| Nontrivial-entailment criterion | P1 complete contrast/examples/titles. Entailment independent of whether antecedent instances are possible; impossible square-circle **may seem** NT-shape-entailing, octopus entailment **does not seem** nontrivial, with a **plausible** counterpossible remark. |
| Ordinary-to-nontrivial transfer | P1B question/titles and C4: ordinary Concrete→P licenses NT(Concrete-and-Necessary,P), any P, retaining the intermediate NT-to-concrete wording. This is a cross-kind reported commitment, not ordinary conjunction projection. |
| Negative relation-instance report | Negative P2/C6: NOT NT(CNec,Cont), not positive NT(CNec,NOT Cont), actual assent or a possible witness. |
| Main reductio | C1–8: source causal-concrete classification, ordinary inclusion, reported cross-kind lift and contradiction. NoPossibleNB remains1–6; only7–8 discharges possibility. |
| Possibility invariance | P3/C suffix after8: exact P3=A8P4 and existing A2 proposition reuse, not a new S5/frame or rigid-witness proof. |

All nine full materializations and raw SHA/title contexts were read. Root independent main fidelity review accepted these scopes with no findings. The ordinary-entails title is byte-identical to A8P1, so the existing ordinary glossary receives only A9 source provenance; NT stays distinct. No source relation is merged by similar wording.

NT cannot faithfully be equated with Dia antecedent AND boxed implication: the source explicitly considers impossible antecedents in hedged examples. Its basis/derivational/intensional/counterpossible criterion is not a complete chosen calculus. Ordinary conjunction strengthening gives only ordinary inclusion and does not establish that criterion. Changing P1B’s ordinary antecedent to NT would alter the actual report/application. A charitable basis account could be investigated, but no proof, refutation or invented model forces the source bridge true.

Source not-necessarily-existing/by-nature contingency is not automatically actual-presence-guarded ContingentAt. Cause-capable concreteness is not every entity or ordinary physicality. Actualist/domain/class/world/intensional and rigid-witness correspondences remain OPEN. Existing Scott/A8 closure or separation results do not establish NT transfer or independently defend nonlimitation of concrete existence. These are source attributions only: all new statements are unbound, and no Lean/argument/result/model/framework, truth flag, premise discharge or owner choice is added.

Public named passage coverage rises **411→420**. The nine selected witnesses are the scoped live delta; the other 411 receive offline checks only. Alternate witnesses are read/delivered for context but alternate claims remain pending, including the revised generic revisit/keep context; no actual session/assent is inferred. No A5–A7 private progress or later history, new source kind, repin/selector change, archive fallback, PHP request or campaign completion is delivered. The public queue remains A5.


### Public A9 alternate completion with unchanged witnesses (2026-11-01)

Four accepted alternate claims add one bare revised-context NT statement, reusing the nine A9 manifests already delivered in #857. The five semantic files byte-match research30f55352; only public survey notes are adapted. No private A5–A7 progress or canonical later cursor is copied. The public **A5** queue remains next.

| Alternate claim | Precise locator / reuse and scope |
| --- | --- |
| `NB-SURVEY-A9-ALT-POSSIBLE-IMPOSSIBILITY` | C2 modal paragraph after8, P3B context; reuses existing A2 alternate report. Ordinary prefix reuses main A9. |
| `NB-SURVEY-A9-REVISED-MUST-EXIST` | P3C opening must-exist/complement stipulation and generic revisit/keep invitation; reuses A2 meaning without a specific NT-report reaffirmation. |
| `NB-SURVEY-A9-REVISED-NONTRIVIAL-REDUCTIO` | NEW statement; C3steps1–8/titles in revised context. Conditional transfer/negative reports, no uniform κ substitution or selected complete NT semantics. |
| `NB-SURVEY-A9-REVISED-ACTUALITY-CONCLUSION` | C3 final paragraph after8; reuses A2 actuality meaning, consuming discharged8 rather than hypothetical class2/NT consequence5. |

All four full materializations and raw SHA/title contexts were read; independent Root fidelity review accepted the scope with no findings. P3C’s generic keep/revisit invitation is neither a specific reaffirmation nor actual/all-entry-route/session evidence. Prefix wording remains identical to main, but the revised context is recorded separately without silently changing every necessary/modal/NT term. Ordinary-to-NT remains a cross-kind commitment, negative report remains NOT NT(CNec,Cont), and the impossible-antecedent criterion is not Dia antecedent AND boxed inclusion. Outer NoPossibleNB persists1–6; only7–8 discharges possibility. Causal-capability concrete is not actual causal exercise. No new causal opportunity, count/history/limitation consequence or independent NonLimC warrant is supplied.

Public A9 main+alternate **source readings** are complete, not a formal NT framework or source-soundness proof. Intensional/basis/class/actualist/world/rigid-witness correspondence remains OPEN. Total public passages stay **420**; manifests/pins/selectors are unchanged. Cached materializations and offline checks reuse prior live-byte evidence with no live fetch or retry. No new glossary, Lean/argument/result/model/framework, source kind/dependency, truth flag, owner choice, root premise discharge or campaign completion is added. A5 stays queued.


### Independent public A10 MAIN delivery (2026-11-01)

Seven MAIN qualified readings and five unbound statements/default glossary/disambiguation byte-match accepted research0377c9c8. Exactly15 unchanged manifests are the named public delta: `NECESSARYBEING-A10P1/P2/P3/C`, reconsideration `A10P1B/P1C/P1D/P1D2/P1D3/P1E/P1B2`, and modal alternatives `A10P3B/C2/P3C/C3` (all IDs have the `NECESSARYBEING-` prefix). Public passages rise **420→435**. All full bodies and raw SHA/title contexts were read; only MAIN claims are delivered here. Reconsideration/alternate extraction remains pending, and the public **A5** queue stays next. No private A5–A7 history or canonical later cursor is copied.

| MAIN reading | Precise source scope / reuse |
| --- | --- |
| Causal default | P1 question/rule/cause titles; C second paragraph. Conditional defeasible report, not exceptionless causal law or numeric probability. |
| Coverage denial | P2 question/titles; C first paragraph. Exact existing A2 broad cause-OR-effect statement reuse. |
| Possible first contingent | C first paragraph/parenthesis. Complete-chain argument and temporary necessarily-all-concreta-contingent assumption; infinite means no first member. |
| Selected-case application | C second paragraph. Prima-facie cause expectation for selected possible C, conditional noncontingent-cause exclusion. |
| Possibility invariance | P3 question/note and C modal introduction. Exact A2 individual-not-joint possibility report reuse. |
| Modal conditional | C numbered1–12. Consumes possible N/necessitation/modal/actuality interfaces, not evidence for them. |
| Overall evidential conclusion | C opening and closing counter-reasons qualifications. Defeasible prima-facie conclusion, not source truth or undefeated warrant. |

A selected first contingent in a merely possible history is not random sampling or automatically an ordinary encountered case. The reference-class/default-applicability and defeater bridge remains OPEN. Firstness requires same-history/population prior-existing-bearer/absence correspondence; partial explanatory cause alone gives neither it nor actual existential support, complete ground or universal PSR (#545/#311). Whole-ancestry/nonemptiness/head representation remains OPEN; finite is not silently finite cardinality. Coverage P2/C uses cause-OR-effect capability, but nominal Necessary Being is cause-capable: dropping the all-contingent assumption may leave a noncontingent effect-only candidate. That OPEN source-domain bridge is not a refutation of bare necessary-concrete/NE routes under their proper premises.

Existing `HeadlessCausalAncestry.source_of_not_headless_coverage` and `NecessaryIfExistent.positive` supply conditional structural/modal reuse, not the source’s epistemic transfer, actual support or rigid-witness selection. The modal suffix cannot turn prima-facie warrant into `Dia N` or transport numerical probability. Root independently accepted MAIN4 complete bodies/all7 claims/5 statements/gloss/disambiguation and SHA-verified raw P1/P2/C titles; acceptance concerns fidelity, not premise truth or proof.

Context boundaries: size/shape/parts/partless-angel/generalization prompts are conditional route-specific reports, not all-route premises; P1B2 reports only no implication found. P3B’s alternate question is followed by C2 literally recalling original invariance; no silent textual repair. P3C reasks the DEFEASIBLE default under revised classification, unlike A2’s exceptionless revised causation. C3 retains prima-facie/defeater qualifications. All are witnessed/read context; their philosophical claims are not added here.

No Lean/argument/result/model/probability framework, source kind/pin/selector/dependency, truth flag, owner selection, philosophical premise or root closure changes. Fifteen new pages alone receive scoped live verification; other420 are checked offline. This independent cluster publication does not complete the source campaign or move the public A5 cursor.


### A10 P1 reconsideration extraction (2026-11-01)

Six qualified source claims now extract the coherent reconsideration cluster,
using the existing seven pinned pages and unchanged MAIN P1/C context. Six bare
statement identities preserve the different categorical, counterfactual and
default scopes; none is Lean-bound. The existing default/cause gloss is reused,
with one minimal case gloss distinguishing partlessness and hypothetical
beginning from formal simplicity or an actual angel.

| New claim suffix (`NB-SURVEY-A10-…`) | Exact source scope |
| --- | --- |
| `SIZE-CAUSAL-DIFFERENCE-DENIAL` | P1B’s negative report rejects the proposed size-based caused/uncaused contrast; its particle worry is not a physics finding. |
| `SHAPE-CAUSAL-DIFFERENCE-DENIAL` | P1C’s negative report rejects the proposed shape-based contrast, not equality of causal probabilities. |
| `PARTS-CAUSAL-DIFFERENCE-DENIAL` | P1D’s negative report bypasses the angel detour; affirmative/uncertain parts reports do not supply this denial. |
| `PARTLESS-BEGINNING-ANGEL-CAUSED` | P1D2 asks a hypothetical beginning case; no angel existence, possible beginning or actual cause is established. |
| `PARTLESS-CAUSAL-DEFAULT` | P1D3 asks for a further defeasible generalization to OTHER partless things, conditional on the angel case. No contingent-only restriction or exceptionless universal is added. |
| `ARBITRARY-CONTINGENT-CAUSAL-DEFAULT` | P1E reconsiders arbitrary X with explicit more-likely-than-not/default language. Its scope is distinct from MAIN’s generic/encountered default and C’s selected possible first contingent. |

The static continuation evidence fixes the report conditions: initial P1
uncertainty enters reconsideration; size-negative and shape-negative reach
parts. Parts-negative goes directly to P1E, while parts-affirmative OR uncertain
enters the angel question, then its affirmative answer enters the partless-default
question, whose affirmative answer reaches P1E. Initial P1 affirmation bypasses
the entire cluster. P1E affirmation continues to P2. Thus neither an angel
premise nor a negative-parts answer is required by every successful route, and
no uniform answer retention or retraction is invented. The existing fifteen-page
reading/route inventory remains authoritative rather than being counted again.

P1E’s qualified “appears” transition does not establish an exhaustive catalogue
of causal exceptions or resolve the selected-case/reference-class burden.
P1B2 remains contextual authorial no-found-implication, not a refutation or an
activity claim. No actual respondent/session, PHP submission, numerical
probability, default-to-`Dia`, productive concrete support, new source pin,
model, formal argument or philosophical discharge follows. All cause titles
retain the prior partial-explanatory-condition meaning. A10 modal alternate extraction (P3B/C2, then P3C/C3) remains pending; the public A5 queue is unchanged.



Public delivery boundary: thirteen semantic files byte-match research1a704a20. All seven witnesses were already public in #860; no manifests, private A5–A7 history or canonical later cursor are copied.
