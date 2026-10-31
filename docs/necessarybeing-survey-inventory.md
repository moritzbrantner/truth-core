# Necessary Being interactive survey: provisional argument inventory

Reading date: 2026-10-26 · Campaign: [#492](https://github.com/moritzbrantner/truth-core/issues/492) · Source identity: NECESSARYBEING-SURVEY

**Status: source inventory plus first formalized conditional slice.** These pages were traversed in the public interactive quiz, including different answer routes. No survey answers were submitted. Four initial pages (the necessary-being definition, A1c, A1c2 and A7c) now have byte-stable hash-pinned web_snapshot manifests, verified in a local checkout with `source_evidence.py materialize` and inspected there. The definition and A1c also have matching dated Wayback bytes; A1c2 and A7c remain fragile without known matching captures. The first ten source claims cover the definition (three), A1/A1c2 (four), and A7c (three). The A7c steps 1–3 conditional result passed local Lean compilation, Comparator and independent NanoDa checking on 2026-10-31 at baseline `770102e8b399bbc2ab6dcb36dd60ffff93cb4d14`, using `scripts/verify-result.sh NB-SURVEY-FIVE-TO-ONE` with zero permitted axioms. Corpus binding is a separate integration check. The labels NB-SURV-P01 etc. below are inventory handles, **not STMT IDs**. Other readings await pinned passages and fidelity checks.

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
| NB-SURV-P15 | Under explicit chain/entire/head definitions, a finite entire chain admits an uncaused head. | A2c |
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
| A2 | Not necessary universal infinite ungrounded regress ⇒ possible finite head; head uncaused; contingents caused ⇒ possible N; then S5 | Show the chain-to-head step with empty/singleton and non-well-founded graph models |
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

1. Keep the four materialized page witnesses reproducible; find durable archival fallbacks for A1c2 and A7c if possible. Pin subsequent A2–A10 source pages before source claims.
2. Check site authorship, update date and licensing rather than assigning a philosopher by speculation; inspect each later page's verified text with its context.
3. Critique the first ten source claims against the pinned text. Preserve the A1 stronger external-cause variant, existential versus individual necessity, and the source's respondent-conditional framing.
4. Verify the written A7 Lean result with `lake build`, `corpus.py bind-check` and Comparator. Then extend the typed causal semantics or register a countermodel without transfer; do not treat the count theorem as A7's entire ontic conclusion.
5. Process remaining families in small source-order batches and compare intermediate open premises with the root frontier. No root premise closure has occurred from this first pass.

**Premise comparison for this PR:** A7 introduces two new **open, sourced, respondent-reported premises** and one new conditional intermediate conclusion in a separate argument; neither is on an established root route. The remaining seven statements are separate sourced readings, not accepted truths. No root premise has been discharged, and no route cost is claimed to have decreased. Source and corpus checks pass locally; the new Lean result's independent Comparator verification must be reported from CI before it is called proven.

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

The subsequent global `corpus.py bind-check` could not run to completion:
`ActualityWithoutBeingNotEliminated/Solution.olean` was absent from the local
build. That attempt was on old baseline `770102e8`; it was an unbuilt integration
prerequisite, not a rejected A7 binding or failed philosophical inference. The
checkout was subsequently fast-forwarded to `7b7174f2`; the old build was stopped
and is not verification evidence for the new revision. Reuse applicable
delivered-head CI evidence before scheduling another full integration build.
