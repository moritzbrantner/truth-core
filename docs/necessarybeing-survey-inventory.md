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

### A4 complete property-transfer cluster (2026-10-31)

Complete pinned/materialized reading in link order: `NECESSARYBEING-A4P1`, `NECESSARYBEING-A4P2`, `NECESSARYBEING-A4P3`, `NECESSARYBEING-A4P4`, `NECESSARYBEING-A4C`, then `NECESSARYBEING-A4P4B`, `NECESSARYBEING-A4C2`, `NECESSARYBEING-A4P4C`, `NECESSARYBEING-A4C3`. All nine full-page responses matched duplicate GETs. Source tooltips were inspected in those bytes. A4p1 exits to A8 on negative/unsure; A4p2, A4p3 and A4p4c exit to A5 on those answers; no exits were fetched. No displayed license or matching archive is asserted.

**Exact respondent conditional.** A4p1 affirms possibility of something having a cause. A4p2 quantifies over any property P which can first be exemplified and can have caused instances, asking whether P can have a caused first instance. Schematically its two *separate* possibilities are `◇First(P)` and `◇∃x(Px ∧ Caused x)`; the consequent is `◇CausedFirst(P)`. It does not assert every possible event is causable, every instance is caused, or that the two antecedent witnesses coincide. Its redness example illustrates first-instantiation production; it does not establish unrestricted substitution. The property tooltip permits terms, concepts or abstract entities characterizing their instances; instance means a bearer of the property. First-exemplification tooltips mention first occurrence explicitly in one position and omit “first” in another; the question's first-instance wording supplies that intended restriction. A4p3 supplies possible first contingent existence, and A4p4 supplies the familiar modal report.

**Source-order inference.** A4c steps 1–4 assume no possible Necessary Being and infer from possible caused existence a possible caused contingent instance. Steps 5–9 combine that with a possible first contingent occurrence and substitute contingency into the property-transfer conditional. Steps 10–13 exclude a contingent source prior to the first contingent occurrence, yielding a possible noncontingent cause; steps 14–17 contradict the opening supposition and conclude possible Necessary Being. Note 1 explicitly permits translating property talk into bearer talk, so abstract property entities need not be additional causal relata. Note 2 explicitly makes “all contingents” nonrigid, as in A3. The standard modal suffix follows. The reductio needs classification of the possible caused thing as contingent when no Necessary Being is possible; that is not automatic if the caused-thing domain includes causally inert/nonconcrete bearers outside the source's necessity/contingency dichotomy. A4p1's cause tooltip describes a prior condition capable of explaining an event; A4c's cause tooltip says a prior partly explanatory condition. A defended source/domain correspondence must retain actual bearer existence and adequate temporal-before priority, rather than inferring those from an abstract explanatory condition alone.

**New substantive burden versus A3.** A4 replaces universal possible-event causability by universal property-transfer, possible caused existence, and reductio. It retains possible universal contingent beginning and prior-existing-source exclusion. To apply its transfer to modal contingency, one must treat that world/individual-dependent classification as an admissible property with the same extension across the relevant first-instantiation and caused-instance possibilities. Those possibilities cannot be combined merely by intersecting their worlds; the transfer report itself is the substantive permission to obtain a new caused-first world. The event tooltip in A4c retains state-essential event identity; first-P causation must preserve the relevant absence-to-presence change, not just produce another P instance after earlier ones. No global PSR is inferred.

The unrestricted-property wording has no explicit admissibility restriction against causal or modal properties. A useful conditional stress test is P = existence itself: *if* its first exemplification were possible, and a caused existent were possible, the report would demand a caused first existence. Under a prior-existing-bearer reading of cause this is incompatible with the absence of every existent before that first occurrence. This is not a demonstrated source inconsistency: the source does not affirm possible first existence of everything, and an admissibility/domain restriction might distinguish it from the affirmed first contingent existence. It does show why a redness illustration cannot independently license all property substitutions, and why restrictions must be explicit rather than invented to secure the conclusion.

**Rooted-causal-property scope test (unverified).** A4p2's question and redness illustration (`NECESSARYBEING-A4P2`), read with A4c steps 7–9 (`NECESSARYBEING-A4C`), concern a property with a *bearer caused to exist*. They do not require that the bearer be caused specifically to acquire P. Narrowing that antecedent to causal acquisition of P would strengthen the source's premise rather than merely clarify it. Test the stated scope with `P(x) := ∃ r, Source(R,r) ∧ ReflTransGen R r x`, where `Source(R,r)` means no incoming R-cause. This is a nonrecursive formula defining a causally relational property, not a circular definition of P.

Conditionally, let the SAME R represent causing its target to exist, let source and target individuals share the relevant domain, and require each nonempty causal path to put its source's existence before its target's first existence. A caused P-bearer then has a distinct uncaused root ancestor: the root cannot be that caused bearer itself. That root is already a prior P-instance, obstructing a *caused first* P-instance in this profile. This is a proof outline, not a Lean certificate. An ordinary root→effect pattern suggests separate first-P and later-caused-P witnesses, but does NOT establish metaphysical possibility of a first P-instance. If an uncaused divine root is eternally present, P may never first begin. Nor may a graph omit external birth-causes while claiming its root is uncaused under the source's causal meaning. No A4 inconsistency or refutation of theism follows.

The test isolates an admissibility/recombination burden: unrestricted modal possibility alone does not combine separate first-instance and caused-bearer possibilities into a caused-first possibility. An independently defended restriction excluding causal relational properties might avoid this test, but must still justify admitting modal contingency. Keeping the property intension fixed across histories does not require keeping the same bearers or extensions; the root formula must be re-evaluated under each history's SAME interpreted causation. No new model, new framework, unrestricted transfer principle or formal/source claim is introduced by this test.

**Alternates and reuse.** A4p4b/A4c2 use possible-impossibility implying actual impossibility to reach the same modal suffix. A4p4c redefines must-exist as automatic existence if possible, then re-asks whether first contingent existence is possible under its complementary class; A4c3 retains the seventeen-step property argument and replaces the suffix by the stipulation. Neither branch silently restores ordinary de re NecessaryAt. Once the possible caused-first-contingency world is faithfully connected to `PossiblyExternallyCausedAt`, existing `PossibleCauseOfContingency` consequences and `LocalFramePossibleExternalCause` supply the necessary-concrete route; the latter's explicit local modal assumptions avoid assuming universal accessibility merely for convenience. No new modal proof is proposed. The source's N proposition alone does not select the same rigid individual; that stronger endpoint belongs to the existing typed composition under its interfaces. No source claim or proof was added here, no premise was discharged, and no weaker-overall-bundle claim follows.

The bounded structural reuse audit sharpens that bridge: at a fixed history v, firstness concerns a time t0 before which no bearer classified as contingent at v is present; a concrete cause bearer must be present at some tc<t0. Its contingency would then contradict firstness. The event's clock alone does not supply bearer presence. Existing `TemporalHistory.CoherentAtNow` links only the designated now slice to world actuality, and cannot supply history-ever actuality of that earlier cause. World, individual, time and event sorts must therefore remain distinct; a temporal `StrictForward` condition is insufficient. No existing generic property-transfer theorem or source-event-to-Scenario opportunity bridge was located. This is the remaining constructive representation step, not a reason to duplicate the already proved modal consequence.

### A5 exact-history situation cluster (2026-10-31)

Pinned, materialized and fully read `NECESSARYBEING-A5P1`, `NECESSARYBEING-A5P2`, `NECESSARYBEING-A5C`, `NECESSARYBEING-A5P2B`, `NECESSARYBEING-A5C2`, `NECESSARYBEING-A5P2C`, `NECESSARYBEING-A5C3`. All seven full responses matched duplicate GETs. Followed actual A5 redirects only; negative/unsure A5p1 and revised-definition A5p2c exit to A6, not fetched. Tooltips inspected in pinned bytes; no license or archived fallback asserted.

**Quantifiers and order.** A5p1 asks whether necessarily, *if* contingent situations obtain, at least one is impossible to cause. The selected negative report denies necessity of that whole conditional. A5c steps 2–6 use modal duality to obtain a possible W where the conditional is false. Classical falsity of the implication supplies both a nonempty extension of obtaining contingent situations and absence of uncausable members. Each obtaining contingent situation is individually possibly caused; it does not follow that all are caused, jointly causable in one history, or actually caused in W. Step 5 mentions only absence of uncausable members, but the omitted nonemptiness remains available from step 4 and must not be discarded or silently replaced by nonemptiness of contingent *individuals*.

Steps 7–10 specify C as all and only the particular contingent things existing or ever having existed in W. The note after step 20 explicitly fixes those particular bearers (illustrated by four), unlike A3's nonrigid first-contingent transition. The `includes` title attribute says that Y would obtain/exist were X actual; thus W includes C gives possible C, while C's positive member commitments support necessity-to-member-necessity. Step 11 argues C is nonnecessary under the initial assumption of no possible Necessary Being; steps 12–13 classify it as an obtaining contingent situation in W and apply that world's causability coverage. Steps 14–17 exclude any contingent prior cause of this exact-history situation and infer a possible noncontingent cause. Steps 18–20 discharge the initial reductio; the common modal suffix then follows.

**Positive logical reuse and empty case.** `TruthCore.Results.Explanation.JointCondition.contingent` already proves that an actual fixed conjunction with a contingent member is contingent, and `necessityEquivalence` exchanges necessity of that conjunction with necessity of each fixed member. The same elementary reasoning applies to any defined world predicate C entailing a fixed contingent member's occurrence. It supplies neither a causal whole/token in the fact domain, nor the source's all-and-only negative commitment. Here “ever existed” also needs an explicit temporal extension: necessity of ever-occurrence does not automatically imply necessity of existence at a designated now. The source's step 11 empty-bearer branch says necessary C with no included contingents implies necessarily no contingents; it then invokes the prior reported possibility of something caused to obtain a noncontingent cause. A5 does not re-ask that prior premise, and a respondent route must actually retain it. This branch is not resolved just by step 4's nonempty *situation* domain. One can have a contingent proposition about absence of individual contingents without an individual contingent bearer, depending on the semantics. A precise representation must distinguish situations, individuals and their occurrence/existence rather than treating the guards interchangeably.

**Positive empty-bearer repair (unverified).** The empty roster can define an obtaining negative situation C, not an absent situation: no contingent concrete individual exists or has ever existed in that history. A5c steps 7 and 11 (`NECESSARYBEING-A5C`) explicitly discuss the empty-bearer branch. Under the reductio of no possible Necessary Being, the retained earlier possibility of a caused thing may supply a reachable history with a contingent concrete bearer; C is then false there, and true at the selected empty-roster W. On this interpretation C is contingent at W, so W's individual contingent-situation causability coverage applies to C itself. If that SAME C obtains in a possible history with an actual concrete causal bearer, that bearer cannot be contingent: its existence anywhere in that history would violate C's ever-absence content. This branch needs neither joint causal sufficiency nor member-to-whole causal distribution. It does not certify that the required histories or causal interpretation are metaphysically possible.

Six application obligations remain explicit:

1. Admit the empty-roster negative whole-history C in the situation/fact domain; nonempty contingent *situation* coverage does not imply a contingent *individual* bearer.
2. Preserve the identity and all-and-only content of C at its possible caused occurrence, rather than substituting an analogous situation with a new roster.
3. Supply an actual concrete causal bearer in that SAME complete history; an abstract fact-reason or mere possible capacity is not this witness.
4. Relate “ever existed” to the individual-existence semantics so that an earlier contingent cause counts against C. A designated now-slice alone is insufficient.
5. Preserve modal reach between W, the positive alternative and the possible caused-C history, including the scope of the no-possible-necessary-being reductio. The source's possibility-independence/S5 report is a sufficient proposed interpretation, not an established frame fact.
6. Actually retain the prior possible-caused-thing report invoked at step 11, with the causal-bearer/capability domain interpretation needed to obtain the positive alternative. A5 does not independently re-ask or prove it.

Existing `PSRStrength.Arena`, `Contingent` and `WeakPSR` keep fact identity and individual existence separate and provide the shape of possible coverage of the SAME obtaining contingent fact. But `Explained` is fact→fact explanation, not concrete individual causation. Conversely, `Scenario.PossiblyExternallyCausedAt` requires `ContingencyBeginsAt` and thus a POSITIVE contingent concrete individual; it cannot represent the empty-C case. Future composition can reuse pointwise `LocalFramePossibleExternalCause.necessaryOfExternalCandidate` and the existing Euclidean/reflexive same-individual transport after actual-concrete externality is independently supplied, without duplicating the modal result or asserting a new causal ontology. The empty-case argument is presently a charitable semantic/proof outline, not a Lean certificate, source claim, model, premise discharge or completion of A5.

**Causal boundary for nonempty C.** The A5c cause-of-a-situation tooltip requires a prior condition capable of partly explaining why that same situation obtains. It is an opportunity claim, not complete explanatory sufficiency or actual PSR. An exact-history description does not alone define a temporal onset or show that any earlier contingent condition is external to its complete causal production. A contingent predecessor already among the specified ever-bearers is compatible with the description's *truth*; whether it can cause that whole description's obtaining is the substantive issue. Thus step 14's appeal to “prior” and “exactly” needs a defended whole-history causal interpretation; it does not follow from the fixed-conjunction theorem, nor from excluding a single act's self-production. If instead C is only an end-time summary state, an earlier included cause need not be prior to its own existence, so that interpretation cannot inherit whole-history externality without a bridge. Possible causation must preserve the fixed C, not replace it by an analogous history with a different roster. A source-faithful external-candidate/Scenario application therefore still needs existing concrete bearer guards and this causal exclusion; the already proved same-witness local-frame consequence can then be reused. No new modal or conjunction proof is proposed.

**Alternates and comparison.** A5p2/A5c use possibility-independence; A5p2b/A5c2 recover the same modal principle from possible-impossibility implying actual impossibility. A5p2c revises must-exist to automatic existence if possible and re-asks the plausibility of the earlier uncausability denial; its wording abbreviates the original conditional, so a formal extraction must preserve which conditional the respondent actually reaffirms. A5c3 repeats the same twenty-step causal argument and ends by stipulation, retaining the earlier individual/world class-correspondence burden. Compared with A4, A5 replaces property-transfer and possible first contingent beginning by possible nonempty contingent-situation coverage and the exact-history C construction/externality argument. It does not derive collective causal sufficiency from individual opportunity. All these source/application premises remain open; no source confidence, definition label or logical packaging discharges them.

### A6 restricted existence-situation cluster (2026-10-31)

Read the actual linked range in order: `NECESSARYBEING-A6P1` → `NECESSARYBEING-A6P1B` → `NECESSARYBEING-A6P2` → `NECESSARYBEING-A6C`, then `NECESSARYBEING-A6P2B` → `NECESSARYBEING-A6C2` and `NECESSARYBEING-A6P2C` → `NECESSARYBEING-A6C3`. All eight complete pages were pinned from duplicate matching GETs, materialized and read with title attributes inspected in those bytes. Negative/unsure answers to A6p1, A6p1b and A6p2c leave for A7; those exits were not fetched in this reading. No rights or archived fallback beyond the manifests' limitations is asserted.

**Two distinct respondent reports.** A6p1 asks whether possibly every contingent individual that happens to exist possibly has a cause. Its affirmative answer leads to a separate question A6p1b, asking the analogous claim for contingent *existence situations*. The source does not infer the second report from the first. A6p1b's `existence situation` title includes facts concerning what exists and its exact cardinality, illustrated by exactly 45 emeralds and no more; it therefore reaches beyond single-individual existence facts and includes negative exclusion content. Its cause tooltip is a prior condition capable of partly explaining why a situation obtains. Neither the individual question nor that explanation-language licenses identification with a concrete efficient/sustaining cause without an adapter.

**Scope/order and argument.** A6c step 2 repeats the existence-situation report; step 3 explicitly construes it as a possible W where each obtaining contingent existence situation is individually possibly caused. Its faithful local shape is outer possibility of a coverage profile, then universal quantification over the relevant obtaining contingent facts, then individual possibility of their causation. It is not necessary coverage, not actual causation, and not a single possible history jointly causing all facts. Compared with A5 it restricts the fact class from all contingent situations to existence situations and states possible coverage directly; it does not negate a conditional and therefore does not itself supply A5's nonempty contingent-situation guard. An empty extension can satisfy the coverage report; the later C construction and contingency argument must supply an applicable fact rather than receiving one for free.

Steps 4–7 construct the same rigid all-and-only ever-contingent roster situation C used by A5. Step 8 repeats the nonnecessity proof under no possible Necessary Being, including the empty-roster branch and its retained prior possible-caused-thing report. Step 9 explicitly classifies C as an existence situation because it pertains to what exists; steps 10–11 classify it contingent and apply coverage. Steps 12–15 repeat whole-history prior-cause exclusion and the possible noncontingent source conclusion; steps 16–18 discharge the reductio. The fixed-roster note again includes ever-existence, not merely current simultaneity. The ordinary modal suffix follows. These are genuine source assertions, not independent defenses of fact admission, temporal identity, or externality.

**Reuse and remaining bridge.** The existing fixed-conjunction consequences cover only positive commitment/necessity reasoning with the appropriate historical occurrence predicate. Existing `EmptyHistoryCausalAvailability` is the relevant empty-roster causal consequence once C is admitted, its content is preserved in the caused history, and the cause is an actual concrete bearer whose existence counts in that history. Empty individuals do not mean no situation: negative C may itself obtain contingently. Its externality can follow from absence of contingent individuals ever in a history preserving C, without collective causal sufficiency. This does not settle nonempty C's whole-history priority argument. The exact cardinality tooltip supports admitting negative existential content as a *kind* of situation; it does not prove an unrestricted comprehension principle yielding every required fact token or its causal availability.

`PSRStrength.Arena` already separates facts from individuals and an individual's existence fact from arbitrary facts. `WeakPSR` supplies individual possible fact-*reasons* for contingent truths at a selected world; it neither includes the outer possible-coverage profile automatically nor turns reasons into concrete causes. Reusing its types can expose the restriction and modal scopes, but applying a fact-reason theorem under a causal label would change meaning. Once an actual concrete cause external to contingent individuals is obtained in an accessible caused-C history, existing pointwise necessity and local-frame same-bearer transport supply the downstream consequence. No duplicate modal proof or new framework is needed merely to record A6.

**Alternates/premise comparison.** A6p2/A6c use possibility-independence; A6p2b/A6c2 use the already read possible-impossibility report and same modal suffix. A6p2c redefines must-exist as automatic actuality if possible and explicitly reaffirms the existence-situation coverage report; A6c3 repeats the eighteen-step argument and concludes by stipulation. That changes the contingency classification and retains world/individual-scope correspondence obligations; it does not prove ordinary `NecessaryAt` by renaming. No premise change or discharge from attribution: A6 supplies a narrower, explicitly reaffirmed respondent commitment and inherits the exact-history application burdens. No source claims, Lean declarations or verification claims were added by this reading.

### A7 remaining complete question/alternate context (2026-10-31)

New complete-page witnesses: `NECESSARYBEING-A7P1`, `NECESSARYBEING-A7P2`, `NECESSARYBEING-A7P3`, `NECESSARYBEING-A7P4`, `NECESSARYBEING-A7P4B`, `NECESSARYBEING-A7C2`, `NECESSARYBEING-A7P4C`, `NECESSARYBEING-A7C3`. Duplicate GETs matched; each was materialized/read fully with title attributes inspected in the pinned bytes. Existing `NECESSARYBEING-A7-DESCENT` was materialized for context; its manifest and proved count files were preserved. Actual A7 links alone were followed. Negative/unsure A7p1 and A7p3 leave for A8, not fetched. Rights remain undisplayed and no fallback is invented.

**Ordered reports and causal meaning.** A7p1 asks the n-to-(n−1) possible-causal-situation transfer for any type T and n≥2; a factory producing a hundred cubed blocks illustrates the report. It does not require the same possible world, same factory, or same objects in successive witnesses. A7p2's cats/rats question routes *all three* answers to A7p3, and contributes no premise to A7c's argument; no mathematical ability or response is evidence for a causal claim. A7p3 proposes just four contingent things jointly producing a fifth, and characterizes that as causing an at-least-five situation. It is explicitly a respondent's possibility report, not member-to-whole causation established from arithmetic. A7p4 supplies the familiar modal question.

A7p1 and A7p3's cause-of-situation title attributes are unusually precise: the condition exists prior to S obtaining, expressly glossed as *while S does not yet obtain*, and can partly explain S's obtaining. A7c2's corresponding tooltip preserves this; its `prior` tooltip gives the same iff. This is stronger and more useful than merely explanatory ordering. At count one, a contingent cause existing while no contingent thing yet exists is directly contradictory if cause presence is included in the same temporal contingent population. It need not be barred by a separate all-history description argument. The source thereby supplies a positive intended exclusion for steps 4–5, conditional on consistent temporal presence and contingency classification. Existing now-slice versus whole-history actuality distinctions remain relevant: a condition present before the target must count as an actual causal bearer in that same possible history, and a time-varying/reclassified predicate cannot silently replace the source's contingent class.

**Exact proof boundary and next connection.** Reuse `STMT-NB-FIVE-CONTINGENTS-POSSIBLY-CAUSEABLE`, `STMT-NB-COUNT-CAUSABILITY-DESCENT`, `STMT-NB-ONE-CONTINGENT-POSSIBLY-CAUSEABLE` through result `NB-SURVEY-FIVE-TO-ONE`, theorem `TruthCore.Results.Causality.NecessaryBeingCountDescent.fiveToOne`. As its result record explicitly states, this is an instantiation transcription over an uninterpreted Nat→Prop predicate, with two open hypotheses. It preserves no worlds, concrete cause bearer, clock, or target facts; it is not yet the source's full seven-step necessary-being argument. No count proof needs repeating. A genuine next connection would interpret its count predicate as existence of a possible caused threshold situation with an existing concrete bearer, and use the just-read pre-target-absence condition at count one to show that same bearer noncontingent. Existing pointwise necessity and local-frame same-bearer transport can then supply the de re endpoint once domain, modal contingency, and history-to-world actuality correspond. The source's propositional N suffix alone does not encode that identity.

This transfer is not mere downward logical monotonicity of cardinality. A factory can precede a hundred-block threshold while already coexisting with some contingent blocks, so producing the former does not automatically precede absence of all contingent things. The universal transfer report is precisely what allows a *different* causal scenario at the lower threshold, and at one it has substantive foundational content. Neither the example nor the verified four instantiations independently defends that possibility/recombination principle. Likewise the four-contributor report must retain the target's full contingent domain, not count five selected objects while ignoring other existing contingents.

**Alternates and premise comparison.** A7p4b/A7c2 replace the original modal input by possible-impossibility implying actual impossibility, then use the same suffix. A7p4c stipulates automatic actuality if possible and asks whether to revisit prior answers: “Sure” loops to A7p1; keeping answers leads to A7c3, which repeats the seven causal steps and concludes by stipulation. This is a keep-answers condition under redefinition, not the separate explicit coverage or beginning reaffirmation seen in A3–A6. Its revised contingent extension still needs semantic accounting. No source claim, proof, axiom or premise discharge was added; the new source context sharpens the temporal causal interface without establishing its truth or applicability.

### A8 limiting-property cluster (2026-10-31)

Complete linked reading: `NECESSARYBEING-A8P1`, `NECESSARYBEING-A8P2`, `NECESSARYBEING-A8P3`, `NECESSARYBEING-A8P4`, `NECESSARYBEING-A8C`; alternate `NECESSARYBEING-A8P2B`, `NECESSARYBEING-A8P3B`, `NECESSARYBEING-A8C2`. All eight full pages matched duplicate GETs, were materialized/read, and relevant title attributes were inspected in those pinned bytes. A8-only links were followed; exits to A9 were not fetched. Rights remain undisplayed, with no invented archive fallback.

**Definitions, response conditions, main argument.** A8p1 defines a limiting property as one entailing a deficiency, with lack of power as example. Its `entails` tooltip explicitly means necessarily every bearer of X bears Y: unrestricted modal inclusion, not relevant, causal, explanatory or nonvacuous entailment. A8p2 asks whether being a *powerful* Necessary Being is limiting; the selected answer is negative. A8p3 asks whether possibly not existing is limiting; affirmative selects A8p4's modal report and A8c. A8c steps 1–5 suppose no possible Necessary Being, infer that concrete existence entails possible nonexistence, then infer concrete existence limiting. Steps 6–9 use powerful Necessary Being's entailing concreteness to make it limiting, contradicting the report; steps 10–11 conclude possible Necessary Being. The standard N suffix follows. The concrete tooltip is causal capability, not ordinary physicality; “powerful” adds a property to the source's necessary/concrete class without a quantitative power definition here. The classification step still needs individual existence/contingency semantics at accessible worlds; impossibility of necessary *concreta* does not classify every arbitrary entity.

**Alternative explicitly embraces vacuity.** Negative/unsure answers to A8p3 route to A8p2b, which asks whether powerlessness is limiting; *all three answers* continue to A8p3b's modal report. Its answer therefore is not a required affirmative premise of A8c2. A8c2 steps 1–4 expressly infer that an impossible powerful-Necessary-Being antecedent entails having a limiting property because its conditional is vacuously necessary. Steps 5–7 use limiting-as-entailing-deficiency and transitivity to infer that the target property entails a deficiency, contradicting its nonlimiting report. Steps 8–10 conclude possibility. This alternate does not require the main branch's report that possible nonexistence is limiting. Neither branch uses the automatic-actuality redefinition alternatives from A2–A7: the only actual A8 alternatives lead to the same modal-report suffix. No unseen branch is presumed.

**Positive inference and burden location.** Given unrestricted modal inclusion and any admitted deficiency property, an impossible property entails that deficiency vacuously. Consequently its being nonlimiting already excludes its impossibility, classically. This is a substantive way to locate what the respondent's negative answer commits to *under the stated semantics*, rather than a separate independent vindication of the intended object's possibility. It does not require any actually deficient being: admission of a deficiency *property* is different from its exemplification. If limiting is formalized by existential quantification over deficiency properties, that property's admission and the step from entailing “has some limiting property” to a suitable deficiency must be explicit. A8c2's compressed quantification cannot silently choose one uniform deficiency from varying bearers. A fixed admitted deficiency property gives the direct vacuity reconstruction; this is a proposed logical reading, not a newly certified theorem or source truth claim. Restricting entailment to relevant/nonvacuous entailment would evade vacuity but change the source's explicit tooltip and its alternate argument. Treating “nonlimiting” merely as an ordinary evaluative judgment while retaining all these formal consequences would likewise leave its semantic adequacy unargued.

**Reuse/premise comparison.** This is a new evaluative-property/entailment family, not a count reduction, contingent-totality external cause, or fact-to-concrete-cause argument. The root route's `RootMultiplication.HasLimitingPrinciple` means three stipulated structural horns and is not this deficiency-entailing property classification. No identification with it, unreceived esse, infinity, omnipotence or God is licensed by the shared word “limiting.” Existing `STMT-NB-SURVEY-EXISTENCE-NECESSITATION` remains the explicitly open de dicto interface for the shared suffix; `NecessaryIfExistent.positive` can reuse that suffix under its existing modal hypotheses. It does not by itself select the same individual across worlds. No new causal or modal proof is proposed, and no premise is discharged by the source's or respondent's judgment. The main branch retains both classification reports; the alternate replaces the contingency-limitation report with vacuous entailment reasoning and property-admission scope. Neither is an independently established possibility premise.

**Closest positivity reuse, without identification.** Dossier/type audit finds `STMT-SCOTT-POSITIVE-POSSIBLY-EXEMPLIFIED`, with existing theorem `TruthCore.Results.Isabelle.GoedelGod.GodLikeNecessarilyExists.positivePossiblyExemplified` in the Solution for `SCOTT-GOD-LIKE-NECESSARILY-EXISTS`. It uses `NegationPositiveExcludesPositive`, `PositiveClosedUnderNecessaryImplication` and explicit excluded middle to rule out an impossible positive property's necessary implication of its negation. This is the closest certified logical pattern: exclusion plus closure under necessary implication forces possible exemplification. It does not identify Scott positivity with A8 nonlimitation, nor discharge either's evaluative commitments. A8's fixed-deficiency vacuity argument should therefore be compared to that existing helper before any new formalization, with the classifier correspondence kept explicit rather than adding a second positivity framework.

### A9 nontrivial-entailment cluster (2026-10-31)

Pinned/materialized/read complete pages `NECESSARYBEING-A9P1`, `NECESSARYBEING-A9P1B`, `NECESSARYBEING-A9P2`, `NECESSARYBEING-A9P3`, `NECESSARYBEING-A9C`, `NECESSARYBEING-A9P3B`, `NECESSARYBEING-A9C2`, `NECESSARYBEING-A9P3C`, `NECESSARYBEING-A9C3`. Duplicate GETs matched; title attributes were inspected in those same bytes. Actual A9 redirects alone were followed, stopping before A10. No displayed license or archive fallback is asserted.

**Explicit change from A8.** A9p1 distinguishes ordinary entailment (necessary universal property inclusion) from nontrivial entailment, which holds independently of whether its antecedent can have instances, rather than solely because it cannot. The source expressly allows an impossible antecedent to nontrivially entail something: square-circle to shape illustrates this, whereas square-circle to octopus is rejected. The tooltip and prose therefore do not define nontrivial entailment as ordinary entailment plus possible exemplification. Nor do they identify it with actual causal/explanatory grounding. Its independence condition concerns the basis of the implication and needs an intensional or consequence-sensitive interpretation beyond mere extension over possible worlds; the page supplies examples and a gloss, not a complete logic for that relation.

**Reported bridge and eight-step argument.** A9p1b asks, for a property P ordinarily entailed by concreteness, whether concrete-and-necessary nontrivially entails concrete and thereby P. Its affirmative report is extracted as the universal bridge in A9c step 4: for any P, ordinary entailment from Concrete to P licenses nontrivial entailment from Concrete∧Necessary to P. A9p2's selected negative answer denies nontrivial entailment of contingency from concrete-and-necessary. Its tooltip uses “not necessarily existing” for contingent and “necessarily existing” for necessary, with concreteness as cause-capability. A9c steps 1–3 suppose no possible Necessary Being and infer ordinary concrete-to-contingent entailment. Steps 4–6 apply the reported bridge at P=contingency, contradict the negative report, and steps 7–8 conclude possible Necessary Being. The common modal suffix follows.

The inference is a valid conditional reductio once those two relation-specific reports and the ontic classification step are explicit. Its substantive burden is the lift from an *arbitrary ordinary* necessary implication to a *nontrivial* implication after strengthening the antecedent. Ordinary conjunction weakening supplies only ordinary necessary implication; it does not certify independence from impossibility as a basis. Conversely, replacing the bridge's ordinary antecedent by nontrivial Concrete-to-P would weaken/change the respondent's actual question and remove the source's advertised application unless that stronger antecedent were established. It is possible to investigate whether an independent derivation through concreteness satisfies the source's intended independence criterion even under the reductio, but no such criterion or derivation is already proved here. Calling either report intuitively plausible is not a truth discharge. No independent new causal availability, count, totality or source witness is supplied by this family.

**Closest reuse and alternate scopes.** Existing `PositiveClosedUnderNecessaryImplication` and Scott's `positivePossiblyExemplified` concern unrestricted necessary inclusion and a separate positivity classifier. They do not express A9's nontrivial relation or prove its lift; A8's vacuous argument cannot silently substitute for a family expressly distinguishing vacuity. The existing necessary-individual vocabulary can express the ordinary classification step only with its actual-existence and concrete-domain guards. `NecessaryIfExistent.positive` remains the shared downstream modal consequence under explicit premises, not a same-individual witness-selection theorem. No exact existing nontrivial-entailment declaration or lift was located in the bounded reuse search; no new relation framework is introduced merely to restate it.

A9p3/A9c use possibility-independence; A9p3b/A9c2 use possible-impossibility implying actual impossibility and repeat the same eight-step argument and modal suffix. A9p3c redefines must-exist as automatic actuality if possible, then offers revisiting prior answers (loop to A9p1b) or keeping them (A9c3). A9c3 retains the eight-step relation argument and concludes by stipulation. The ordinary revised-class/world-identity obligations remain; no unlisted explicit reaffirmation or relevance logic is inferred. Premise comparison: A9 replaces A8's limiting/deficiency classification with nontrivial-entailment lifting and a specific exclusion report. It does not discharge the possibility obligation independently of those open reports, and does not establish a weaker overall bundle. No source claim, Lean proof or model was added.

### A10 complete defeasible family (2026-10-31)

New pinned/materialized/read complete-page IDs, all prefixed `NECESSARYBEING-`: `A10P1`, `A10P2`, `A10P3`, `A10C`; alternative context `A10P1B`, `A10P1C`, `A10P1D`, `A10P1D2`, `A10P1D3`, `A10P1E`, `A10P1B2`; modal alternatives `A10P3B`, `A10C2`, `A10P3C`, `A10C3`. All fifteen response bodies matched duplicate GETs and were read with relevant title attributes. Actual family redirects alone were followed; `escape.html` exits were not fetched. No undisplayed license or archived fallback is asserted.

**Ordered reports and branches.** A10p1 asks whether contingent things generally have causes as a rule of thumb. Affirmative proceeds to A10p2's denial of necessary universal headless/ungrounded chain coverage, then A10p3's familiar modal question. An unsure answer to A10p1 opens A10p1b's size question; negative answers there lead through A10p1c's shape question and A10p1d's parts question. Denying a parts difference leads directly to A10p1e, which renews the default for an arbitrarily chosen contingent thing. Affirmative/unsure on the parts question instead asks in A10p1d2 about a beginning partless angel, then A10p1d3 about generalizing from that angel to other partless things; affirmative answers converge on A10p1e. Various negative/unsure replies end at escape or the pinned A10p1b2 terminal, which states no implication has been found. Thus neither a partless angel's possible beginning nor causal uniformity across size/shape/parts is universally assumed by every successful route. The terminal's modest statement about the author's inference search is not a nonexistence proof.

**Defeasible inference, not probability theorem.** A10c first repeats the complete-chain reasoning resembling A2, under a temporary assumption that every concrete thing is contingent. Its concrete tooltip permits causing *or being caused*. It obtains a possible first contingent C and applies the reported causal rule of thumb to C. A cause of such a first contingent would be noncontingent; the source concludes only a prima facie reason for possible Necessary Being, followed by the modal suffix. Both the opening and final paragraphs qualify the conclusion and expressly allow defeating counter-reasons. The rule-of-thumb tooltip defines defeasible entitlement for a particular encountered member of a class; it supplies no probability space, distribution, sampling rule or numeric confidence. The phrase more-likely-than-not is therefore not a verified probability bound. Applying the general default to this specially selected first member in a merely possible history needs a defended reference-class/epistemic applicability bridge and defeater treatment. It is not actual universal PSR, nor a deductive possible-cause premise just because earlier families use one.

“Infinite” again means no first member, so its contrast with finite cannot silently mean finite cardinality; branching closed ancestry and headlessness remain the A2 interpretation issue. A10's repeated complete-chain paragraph does not independently justify source nonemptiness, complete ancestry coverage or the representation of firstness. Existing `HeadlessCausalAncestry` is the structural reuse lead under explicit graph correspondences, not a truth discharge. If a first-contingent witness is supplied, the source's causal-priority reading can exclude a contingent cause only when it precedes all contingent presence in the same relevant population/history; explanatory priority alone does not prove that guard. A cause-capable concrete bearer and modal/individual semantics still need alignment. The same-witness local-frame consequence and `NecessaryIfExistent.positive` remain conditional downstream reuse; neither transports defeasible entitlement or numerical probability through that consequence automatically.

**Modal alternates and textual discrepancy.** A10p3b asks the possible-impossibility question. Its affirmative target A10c2 nevertheless repeats A10c's *original* possibility-independence report and derivation, rather than explicitly recalling the question just answered. The source's actual prose must not be silently repaired. A charitable reconstruction could use the previously identified contraposition/duality connection from that alternate report to the same modal principle, but this is a reconstruction and an additional fidelity note, not the page's literal recalled premise. A10p3c stipulates automatic actuality if possible and re-asks the causal default under the revised contingent class; A10c3 substitutes that stipulation for the modal suffix while retaining prima facie qualifications. No alternate turns defeasible evidence into certainty.

**Premise comparison and remaining source scope.** A10 weakens the earlier no-uncaused-contingents report to a defeasible causal default, while retaining denial of universal headless ungrounded coverage and adding its selected-case epistemic application. This is a change in inference strength, not a deductive proof from fewer premises. No exact existing corpus theorem transporting this source's defeasible default to its selected modal foundation was located in the bounded reuse search; no new probability or defeasible-logic framework is added to manufacture one. No source/report-to-truth discharge, claim, Lean proof or model is added.

The numbered A2–A10 linked families now have reading coverage, but this does **not** establish campaign completeness. Existing manifests leave known A1 question/context leads `a1p0`, `a1p1`, `a1p2`, `a1p3`, `a1p3b`, `a1p4` without witnesses, as listed in the earlier route inventory; additional A1 branches require actual-link closure review rather than guessed URLs. Shared home and instructions also lack manifests. `NECESSARYBEING-DEFINITION` already pins a selected definition range, so full-page context/link coverage should be audited rather than assumed from that selected witness. A1c/A1c2 conclusions are already pinned. These are a bounded next source-audit lead list, not newly fetched evidence or a claim to exhaust every possible answer history; no earlier-page fetching was performed in this batch.

### Conditional A7 temporal-count connection (2026-10-31)

`COUNT-TEMPORAL-NECESSARY-BEING` connects the existing count result to the shared actual necessary-individual conclusion, rather than repeating its opaque decrement proof. `CountTemporalNecessity` reuses the same `TemporalHistory.History`. AtLeastAt means an injective Fin n family of concrete, world-relative contingent bearers present at one time. A guarded caused threshold supplies a concrete cause present earlier, an edge in a separate count-situation causal relation, the target count, and absence of that count at every earlier time. PossibleCount supplies an accessible history with those guards. The new typed five and decrement premises are OPEN configurations, not silent strengthenings of the old sourced count claims.

Six inputs are retained: typed five opportunity, typed decrement, one-way temporal-presence-to-world-existence, explicit EM, Euclidean accessibility and reflexivity at the designated world. The proof imports `NecessaryBeingCountDescent.fiveToOne` instantiated at PossibleCount. At count one, contingency of its SAME earlier cause would give the forbidden earlier singleton threshold. Presence supplies existence in that history; EM yields necessity of that very cause, and the local modal conditions transport its existence/necessity to the designated world. The non-corpus sameCause helper retains its original concrete guard and count-one causal role at the accessible history; no causal role at the designated world is asserted. The corpus endpoint projects to existing `STMT-KANT-CONVERSION-NECESSARY-WITNESS`.

This is genuine conditional derivation/configuration progress under policy #824, with no philosophical truth discharge. No universal frame, now-slice coherence, global PSR, well-foundedness, causal-grounding conversion, uniqueness or God identification is assumed or concluded. Temporal population coverage, causal interpretation, concrete-domain applicability, modal scope and the ever-history existence bridge remain explicit framework commitments. Focused Lean checks pass; both proof helpers/endpoints have zero axioms. Challenge SHA256 remains `e3834ccaaec1c02e679088b415f86e778fe2bcbc62ed957d1114bc64520d77fc`. Corpus and whitespace checks pass; Comparator/NanoDa integration is coordinator-owned and not yet claimed here. The new attempt `ATTEMPT-COUNT-TEMPORAL-NECESSARY-BEING-20261031` retains the exact premise comparison and focused evidence. Source extraction/argument registration for other family commitments remains queued.

Retained strength in the typed count configuration: `CausedThreshold` requires absence at every earlier time, while the witness proof only uses absence at the cause time. This first-threshold guard is not silently attributed to the source. Weakening it to cause-time absence is a separate configuration opportunity; the frozen current Challenge remains unchanged.


### A1 question chain and shared context closure audit (2026-10-31)

Ten previously absent page witnesses are now pinned, materialized and read in
full: `NECESSARYBEING-HOME`, `NECESSARYBEING-INSTRUCTIONS`,
`NECESSARYBEING-NECESSITY-CONTEXT`, `NECESSARYBEING-Q1`, and
`NECESSARYBEING-A1P0`, `A1P1`, `A1P2`, `A1P3`, `A1P3B`, `A1P4` (the latter IDs
all retain the `NECESSARYBEING-` prefix). Each complete response matched two
GETs before manifest creation; title definitions and actual redirect targets
were read in those pinned bytes. No new archive fallback or displayed license
is asserted. No survey response was submitted.

**Shared context and selection scope.** Home frames the exercise as testing
what follows from the respondent's reports, not establishing those reports as
truths. Instructions equate can/possible with consistency with objective
necessities, explain hover definitions, and state that some answers are
tracked. The separate necessity explanation leaves the term familiar rather
than reducing it to knowledge; it requires truth across every possible actual
situation to count as necessary. The existing `NECESSARYBEING-DEFINITION`
witness was re-materialized and its selected text compared with its complete
hash-checked page: it includes the entire visible body, not a truncated argument.
It preserves possible causal capability, impossibility of nonexistence, and the
SEPARATELY stipulated existential necessitation axiom. It does not identify
that axiom with de re candidate identity or prove the real-world modal frame.
Existing A1c/A1c2 selected ranges were also re-materialized; they omit the
congratulatory introduction but retain the full numbered arguments and closing
questions. None of those existing manifests was changed.

**Static A1 route closure.** The parsed choices have the following actual
HTML destinations; no guessed alternate pages were fetched.

| Page | Actual successor choices |
| --- | --- |
| A1p0 | Every answer goes to A1p1. Its inside-itself question adds no discriminating premise to these routes. |
| A1p1 | Denying possible uncaused contingent existence goes to A1p2; affirmative/unsure exits to A3p1. |
| A1p2 | Affirming totality contingency goes to A1p3; negative/unsure exits to A2p1. |
| A1p3 | Answering no to the disjunction (self-origination or production solely by own parts) goes to A1c; affirmative/unsure goes to A1p3b. |
| A1p3b | Explicit external-cause stipulation, then A1p4. |
| A1p4 | Denying existence without at least partial external origination goes to A1c2; affirmative/unsure exits to A3p1. |

A1p3's collective own-parts exclusion is not merely a prohibition of one act's
self-production. The fallback does not infer externality from the earlier
unqualified report: A1p3b changes the causal vocabulary, and A1p4 RE-ASKS the
causal question under it. The stipulation excludes the effect itself or its part, retaining an explicit
“(alone)” qualifier; A1p4's tooltip excludes a mere part as the relevant cause. Preserve those
wordings and the partial-cause scope rather than silently deciding a full joint
contribution theory. Its past-origination wording does not itself supply the
present esse-sustaining correspondence used by direct-esse results. Existing
A1 totality-relatum/actuality and complete self/parts-exclusion obligations and
already checked external-whole-cause consequences remain unchanged.

**Entry boundary.** Home links to instructions; instructions link to the full
being definition, separate necessity explanation and Q1. Q1 asks the
respondent's initial stance and directs its three answers to `a1.php`, `a2.php`
and `a3.php`. Those answer endpoints were NOT requested or interpreted: reading
their targets could submit a stance in a survey that announces answer tracking.
The six A1 question pages were read directly. This closes the known static A1
HTML/question/context witness gaps, not every server-side entry path, answer
history or executable implementation. No extra A1 HTML branch was discovered
from the inspected question chain; its A2/A3 exits already belong to the read
numbered families.

**Next source-ordered extraction cluster.** Reuse the existing four A1
statements/claims and the checked external-whole consequence. First align
A1p1→A1p2→A1p3→A1c as one respondent-conditional totality/self-parts cluster;
then compare A1p3b→A1p4→A1c2 as the explicit stronger causal variant. New question
witnesses do not by themselves merit duplicate claims or independent premise
truth markings. The collective complete-contribution and whole-relatum roles
may remain declared framework inputs while their conditional consequences are
explored, under policy #824. This source batch adds no Lean, claim, model,
causal principle, philosophical discharge or root-route change.

Validation for this bounded source batch: all ten new witnesses passed live
source verification after materialization; the other458 manifests received the
offline check only. Offline source bindings, JSON parsing and whitespace checks
pass. No Lean inputs changed.


### A1 source-ordered extraction audit: reuse, no duplicate readings

The newly witnessed A1p1→A1p2→A1p3→A1c cluster and its A1p3b→A1p4→A1c2
variant were compared with the four existing statement/claim records, their
definitions/disambiguation and existing typed consequences. All four already
record respondent-supplied commitments rather than unconditional author
endorsement. No genuinely missing A1 premise reading or demonstrated
claim/type mismatch was found that requires a new statement, source claim or
Lean declaration in this bounded cluster.

| Existing statement and claim reused | Exact question/conclusion correspondence |
| --- | --- |
| `STMT-NB-A1-CONTINGENT-TOTALITY` / `NB-SURVEY-A1-TOTALITY-CONTINGENT` | A1P2 asks for the sum's contingency; A1c steps 1–2 introduce C and explicitly credit contingency to the report. This is not a proved individual-to-totality closure law. |
| `STMT-NB-A1-CONTINGENTS-CAUSED` / `NB-SURVEY-A1-CONTINGENTS-CAUSED` | A1P1's negative report supplies A1c step 3's exclusion of a possible causeless contingent thing. Externality is not part of that initial question. |
| `STMT-NB-A1-SELF-PARTS-EXCLUSION` / `NB-SURVEY-A1-SELF-PARTS-EXCLUSION` | A1P3 asks one disjunctive question; its negative answer excludes both self-origination and production solely by own parts, as A1c step 5 records. It cannot be replaced by exclusion of a single act's self-production or merely distinct individual causes. |
| `STMT-NB-A1-CONTINGENTS-EXTERNALLY-CAUSED` / `NB-SURVEY-A1-EXTERNAL-CAUSE` | A1P3B stipulates the altered cause vocabulary and A1P4 re-asks the originating-cause question; A1c2 steps 3,5 explicitly use that stronger report. It is not inferred from the unqualified answer. |

The four premise statements remain unbound prose readings: there is no new
Lean type to approve merely from these question witnesses. Future formal
extraction must preserve the source's impossibility wording (A1c step 3 and
A1c2 step 3), or explicitly identify a weaker selected-world use; it must not
silently equate those scopes. A1P1's cause hover admits a prior condition
capable of explaining or partly explaining an event/change, whereas the
conclusion hover describes a prior condition explaining or partly explaining
something else. This lexical detail does not independently impose present
existential support, cause actuality, a time order or full explanatory
sufficiency on a typed relation. The existing uninterpreted A1 cause sense
remains appropriately distinct from Aquinas's origin-cause predicate and from
present esse support. The `(alone)` qualifier in A1P3B is not silently turned
into a complete joint-contribution axiom.

`NECESSARY-CAUSE-FROM-CONTINGENT-COVERAGE` and
`NECESSARY-BEING-FROM-CONTINGENT-COVERAGE` remain the existing typed analyst
connections, with their SAME witness and explicit coverage/actual external
cause inputs. They are not newly verified consequences of the four unbound
source statements. The self/parts route's collective complete-contribution
role may be a declared conditional framework input; this audit neither derives
it from single-act exclusion nor starts a recursive defense campaign.

Actual extraction delta: four statement/claim pairs reused; zero new or changed
claims, statements, definitions, disambiguations, Lean types or source pins;
no philosophical truth discharge or new root route. Audit findings are
persisted here and in the existing first-pass attempt rather than manufactured
as activity propositions. The next unprocessed source-ordered atomic extraction
cluster is A2P1→A2P2→A2c's respondent causal/ancestry conditions, using its already
read alternate pages only where their meanings differ. That extraction is NOT
started here: owner issue #826 now prioritizes the cross-attribute matrix and a
bounded conditional vertical slice.

### A2 bounded source extraction: main branch (2026-11-01)

Five source claims now preserve the main A2 cluster without inventing a second mathematical model or registering a new proof:

| Claim | Statement / precise witness locator |
| --- | --- |
| `NB-SURVEY-A2-REPORTED-COVERAGE-DENIAL` | New `STMT-NB-A2-REPORTED-COVERAGE-DENIAL`; `NECESSARYBEING-A2-QUESTION-ONE`, A2P1 question/tooltips and negative-answer continuation. This is **conditional on choosing that answer**, not an assertion in the bare question, actual respondent assent, or premise truth. A2C step5 is explicit immediate context, with its narrower domain preserved separately. |
| `NB-SURVEY-A2-ENTIRE-MEMBER-CLOSURE` | New `STMT-NB-A2-ENTIRE-MEMBER-CLOSURE`; `NECESSARYBEING-A2-CONCLUSION`, A2C steps1–4,7 and title attributes. Necessity scope is retained. Membership in an entire chain, not containment of the original chain as a whole, is asserted. |
| `NB-SURVEY-A2-POSSIBLE-HEAD-AND-UNCAUSED` | New `STMT-NB-A2-POSSIBLE-HEAD-AND-UNCAUSED`; same witness, steps5–8. Records the source's disputed conditional and stronger relational head, with isolated-source and broad-to-narrow-domain gaps explicit. It is not a new certified implication. |
| `NB-SURVEY-A2-CONTINGENTS-CAUSED` | Reuses **`STMT-NB-A1-CONTINGENTS-CAUSED`**; same witness, step9. Unqualified reported causation, not the stronger global/distinct/existing-cause `LocalCausalPrinciple` or selected existential grounding. |
| `NB-SURVEY-A2-POSSIBILITY-INVARIANCE` | New `STMT-NB-A2-POSSIBILITY-INVARIANCE`; `NECESSARYBEING-A2-QUESTION-TWO`, A2P2 question and individual-versus-joint-possibility note. The report is conditional on the affirmative branch. Main A2c's modal interpretation is context, not a new proof of S5 or rigid-individual necessity. |

All selected witnesses and the four alternates were freshly materialized and read before extraction; A1P1 and the definition page supplied immediate context. The existing objective-possibility and existential N-to-Box-N source statements/claims remain unchanged. The four new statements intentionally have **no Lean declaration**: they preserve disputed source commitments before an exact formal interpretation is selected. No new Challenge/Solution, inference or result advertises the unverified source argument as a mechanically checked consequence. This is extraction/reuse progress, not a new proof or truth discharge.

The new source-gloss definitions and `DISAMB-NB-A2-DOMAIN-AND-ANCESTRY` preserve the A2P1 cause-OR-effect capability domain, A2c cause-capability domain, and entire/member/head meanings. Formal actual-graph correspondence remains an explicit unattributed application question. `HEADLESS-CAUSAL-ANCESTRY` and `POSSIBLE-CAUSAL-SOURCE-NECESSITY` already provide the conditional mathematical consequences under their own dictionaries; neither is newly attributed to A2. There is no member-to-whole causal production inference in the source's member-closure argument. Infinite remains no-first-member rather than cardinal infinity; no separate objection to the working inadequacy of wholly borrowed reality is introduced.

Three application seams remain distinct: source chains/heads versus actual full ancestor cones; capable-domain and actual-cause guards versus the typed global causal principle; and objective/de dicto modal reports versus the frame and rigid-witness interfaces. Mere model consistency is not explanatory adequacy. A2P2b/A2c2's alternate modal report and A2P2c/A2c3's changed necessity/contingency classification remain the next coherent **extraction** batch, though their witnesses were already read. The candidate is retained for those readings and source-ordered A3–A10; campaign completion is not claimed. Corpus consistency, offline source binding and whitespace checks pass. No source pin, old claim/type, shared generator or proof module changed.

Public A2 delivery: #837 publishes the five qualified claims above from the existing public witnesses, without the seventy-four later private pages. Its public candidate preserves the pending A4–A10 witness/reading queue; this fuller private inventory already records those witnesses and retains the same next A2 alternate extraction. Local source-search success and the public remaining-delivery boundary are different scopes, not philosophical closure.

### A2 alternate extraction: modal input and revised classification (2026-11-01)

Four qualified source claims complete the materially different A2 alternate readings, using the four existing pinned witnesses freshly materialized/reread with hash-verified title attributes:

| Claim / new unbound statement | Precise witness locator |
| --- | --- |
| `NB-SURVEY-A2-ALT-POSSIBLE-IMPOSSIBILITY` / `STMT-NB-A2-ALT-POSSIBLE-IMPOSSIBILITY` | `NECESSARYBEING-A2-CONCLUSION-TWO`, A2C2 modal paragraph after causal step11; immediate question context `NECESSARYBEING-A2-POSSIBLE-IMPOSSIBILITY` (A2P2B). The author recalls the affirmative input and proposes contraposition/duality to necessity of possibility. The question is not actual assent, and no S5/frame proof is claimed. |
| `NB-SURVEY-A2-REVISED-MUST-EXIST` / `STMT-NB-A2-REVISED-MUST-EXIST` | `NECESSARYBEING-A2-REVISED-DEFINITION`, A2P2C opening stipulation and complementary class. This is the author's explicit definition, not a respondent's assertion that a bearer exists. |
| `NB-SURVEY-A2-REVISED-CONTINGENTS-CAUSED` / `STMT-NB-A2-REVISED-CONTINGENTS-CAUSED` | `NECESSARYBEING-A2-CONCLUSION-THREE`, A2C3 steps9–11 under the A2P2C reaffirmation question. The report remains conditional on an affirmative answer under the changed class. It is not an alias of the main `STMT-NB-A1-CONTINGENTS-CAUSED`. |
| `NB-SURVEY-A2-REVISED-ACTUALITY-CONCLUSION` / `STMT-NB-A2-REVISED-ACTUALITY-CONCLUSION` | Same witness, final actuality paragraph after step11. The source concludes actuality through its revised stipulation instead of the twelve-step modal suffix; this is an attributed conditional conclusion, not a certified actual or rigid necessary witness. |

The two source-gloss definitions and `DISAMB-NB-A2-ALT-REVISED-NECESSITY` preserve two separate changes. A2C2 changes the modal report while retaining the ordinary nominal class; A2P2C/A2C3 changes the class itself. The editorial tag κ denotes only the latter source stipulation and its complementary contingency, not a source symbol or new Lean relation. Its would/automatically wording is left unbound: no counterfactual calculus, vacuous material-implication classification, ordinary `NecessaryAt`, or source N-to-Box-N identity is selected. A possible classified individual does not by itself carry the required classification/condition to the actual world; this semantic/witness step remains open. Stock tooltips retained by A2C3 do not erase its explicit revised stipulation.

The existing main causal-prefix readings, unqualified causal relation gloss, objective-possibility reading and ancestry/modal consequence proofs are reused only where their meanings match. No repeated prefix/suffix claims, new Lean proof, semantic framework or source-to-actual-graph identity is introduced. New source commitments are deliberately unbound and no premise or root obligation is discharged. All four claim locators pass existing source-evidence bindings, corpus consistency and whitespace checks; the original five-claim main batch also passed independent source-fidelity review, which establishes neither premise truth nor Lean consequence.

A2's substantive main/alternate readings are now extracted at these stated boundaries; the existing candidate remains for source-ordered **A3** extraction, then the later families. The private research checkout has later witnesses/readings which are not automatically delivered public evidence. A future public batch must preserve the public baseline and include only its named source/reading delta; this extraction adds no source manifest. No PHP answer endpoint was requested and no source pin, old claim/type, script or generated import changed.

Public A2 alternate delivery: PR #839 merged at `7cd1a3df` after required CI and exact-head review without findings. Its four claim/statement readings match this fuller research record. The public A4–A10 remaining witness/delivery queue and this private static linked-page coverage are separate scopes; neither constitutes campaign completion or premise discharge. Independent materialized/raw-tooltip acceptance concerns source fidelity only.


### A3 main source extraction and conditional reuse (2026-11-01)

Freshly materialized and read complete `NECESSARYBEING-A3P1`, `NECESSARYBEING-A3P2`, `NECESSARYBEING-A3P3` and `NECESSARYBEING-A3C`, including essential raw HTML title attributes. Five unbound source readings are `NB-SURVEY-A3-POSSIBLE-EVENT-CAUSABILITY` (P1 question/negative continuation), `NB-SURVEY-A3-POSSIBLE-CONTINGENT-BEGINNING` (P2 question/affirmative continuation), `NB-SURVEY-A3-NONRIGID-FIRST-TRANSITION` (C1–4 and note after11), `NB-SURVEY-A3-PRIOR-CAUSE-EXCLUSION` (C5–9) and `NB-SURVEY-A3-POSSIBLE-NECESSARY-CAUSE` (C9–11). Question reports are conditional; the remaining inferences are authorial assertions, not independent truth. The same event retains its essential before/after states; “all” means no contingents before some first appear, not a rigid actual roster. Possible causability does not require every actual event actually to be caused.

The positive exclusion argument is substantive under an earlier-existing causal-condition reading: a contingent cause on the no-contingents side contradicts that side. But the cause tooltip's prior explanatory condition does not alone establish an existing concrete individual, temporal presence, or a totality-cause dictionary. Mere atemporal ordering, simultaneous production or a nonexistent reason cannot supply the reading. These remain unattributed OPEN application bridges; `STMT-SCENARIO-CAUSAL-OPPORTUNITY` is not source-attributed by renaming the assertion. Existing `LOCAL-FRAME-POSSIBLE-EXTERNAL-CAUSE` requires `STMT-EUCLIDEAN-FRAME`, `STMT-ACTUAL-MODAL-REFLEXIVITY`, `STMT-SCENARIO-POSSIBLY-BEGINS` and `STMT-SCENARIO-CAUSAL-OPPORTUNITY`; its same-bearer output can feed `SCENARIO-NECESSARY-CONCRETE-TO-NECESSARY-BEARER`. Those explicit conditional consequences are not a source-to-model bridge or fresh premise defense. The existing A2 possibility-invariance report/modal suffix is reused without a duplicate proof or claim of □∃→∃□.

Two source-only glosses define essential-state events/prior explanatory conditions and the first nonrigid transition; neither introduces a Lean framework. No new source witness, argument/result, Lean file or philosophical discharge. Next extraction is already read A3P3B/C2 then A3P3C/C3, retaining the revised beginning question under its changed classification. The candidate remains open; the private later-family witness inventory is not public delivery.

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

Five qualified claims thus add only two bare statements, no glossary, pin, Lean module, argument or result. The existing alternate/revised disambiguation is extended without changing old meanings. These records cover the materially different A3 main/alternate readings at their stated boundaries, so the existing candidate now advances to source-ordered **A4**, followed by the remaining campaign. This is neither campaign completion nor public delivery of private later-family witness/read history, and no philosophical premise or root obligation is discharged. No PHP answer endpoint was requested.

Public A3 main delivery: PR #842 merged as `f669db3d` after exact-head review and required CI passed. Independent A3 alternate fidelity review checked all four materialized witnesses and hash-verified raw titles, directly comparing the three reused A2 meanings; no findings. Source fidelity does not establish soundness, reality correspondence or a new formal consequence. The fuller research A4 queue and public remaining witness/delivery queue retain their separate scopes.
