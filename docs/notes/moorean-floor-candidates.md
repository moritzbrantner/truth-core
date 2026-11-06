# First Moorean candidate batch

This is a reviewable **proposal batch**, requested in [#1119](https://github.com/moritzbrantner/truth-core/issues/1119), not a floor register or an approval. The authoritative register is the corpus's `self_evident` markings, projected by `corpus.py frontier --json` and the explorer. No marking, source claim, relation, definition or Lean theorem changes in this batch.

The batch reuses checked conditional consequences. Ranking reflects potential root reach and how much of the remaining obligation is understood; it does **not** certify that a commitment is obvious, true, or common ground. The first three items form one package about the *selected Catholic practice*. They must not be read as universal claims about every `Practice`, nor as three independent reductions in root cost.

Owner decisions are **not prerequisites to conditional investigation**. Continue treating the competing readings as explicit inputs, type currently untyped rivals as sibling propositions where their content differs, and test consequences, contradictions, triviality and which objections retain force. Establishment is needed for a counted root-frontier settlement, not for exploring a framework. The proposals below are available if a particular floor settlement is selected; they are not a request to choose definitions before that work can proceed.

## Ranking and present impact

At main `0367eebc5b98263ba16d87a2ddd0e9388d10056e`, there are 12 reported verified root routes, cheapest cost 31. The single recorded rival of `STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE` is `STMT-WF-RELIGION-CUT-OFF-FROM-SHARED-REASON`; revelation is one open leaf on all 12 routes.

| Priority | Proposed commitment | Proposed basis for owner consideration | Cost change from settling this item alone in the current registered graph |
| --- | --- | --- | --- |
| 1 | The Catholic practice has the recorded conciliar natural-knowability definition | Descriptive observation about the practice's canon, **not** assent to its theological truth | 0 on every route |
| 2 | Its conciliar definitions belong to its own authoritative standards | Explicit institutional/framework commitment; contested, not a met common-ground criterion | 0 on every route |
| 3 | Its natural-knowability affirmation answers to reason shared with outsiders | Explicit reading/framework commitment; contested, not a met common-ground criterion | 0 on every route |
| 4 | The spacetime whole has an existing cause of its existence | Contested causal framework commitment; not an ordinary observation | 0 on every route |

For items 1–3, the *potential downstream target* is the one revelation leaf shared by all 12 routes: its eventual settlement would remove that one leaf per route. That is conditional on repairing and checking the missing single-rival refutation described below; it is **not** the computed effect of approving these proposals. Their effects must not be added as −3 per route. Item 4 currently has no registered naturalist alternative on a root-route leaf and therefore has no advertised root-cost benefit.

## 1. A descriptive canon premise

**Existing statement:** `STMT-DEI-FILIUS-DEFINES-NATURAL-KNOWABILITY-OF-GOD`.

**Candidate in ordinary language:** the selected Catholic practice includes a conciliar definition affirming that God can be known with certainty from created things by natural human reason. Accepting this descriptive premise says what the practice defines; it does not assert that the defined proposition is true or that anyone actually knows God that way.

**Exact scope/type:** `CouncilDefinesNaturalKnowabilityReading P := ∃ m, P.AffirmsNaturalKnowability m ∧ P.Defined m`, in `TruthCore/Alternatives/Fideism.lean`. `P` must be the selected Catholic practice. The statement is recorded as *stated*, but is not established; textual assertion is not floor acceptance. No claim that every possible practice contains this move is proposed.

**Why this belongs in the batch:** the checked `needsCouncil` control in `WF-FAILS-AS-DESCRIPTION-OF-CATHOLIC-PRACTICE` witnesses that both interpretation bridges can hold while the sharp fideist pair survives when the council premise is removed. This is an indispensable third input, easily hidden if the problem is described as requiring only two bridge decisions.

**Rivals and burdens:** no `alternative_to` is recorded for this descriptive statement. The framework still needs an interpretation that identifies the selected practice and its `Defined` moves with the recorded Catholic practice; the generic theorem does not supply that identification. An owner may consider the descriptive observation, but no new source certification or approval is claimed here. Approving it alone settles neither bridge, refutes no recorded revelation rival and changes no route cost.

## 2. Conciliar definitions as the practice's own standards

**Existing statement:** `STMT-CONCILIAR-DEFINITION-IS-PRACTICE-OWN-STANDARD`.

**Candidate:** in that selected practice, what an ecumenical council defines is endorsed by the practice's own authoritative standards.

**Exact scope/type:** `DefinitionIsOwnStandardReading P := ∀ m, P.Defined m → P.OwnStandard m`. This is one direction only. It neither says that every correct religious move is a conciliar definition nor identifies theological truth with institutional authority.

**Recorded rival:** `STMT-COUNCIL-TEACHING-THEOLOGY-NOT-GRAMMAR`: conciliar formulations may be theology *about* the practice rather than its grammar, and may distort first-order religious life. This rival has no bound Lean declaration, so the note does not claim to have formally refuted it or to have proved it is simply the logical negation of this bridge.

**Checked consequence:** with the canon premise and item 3, `TruthCore.Results.Alternatives.FideismCatholicPractice.fideismFailsAsDescription` rejects the sharp pair `InternalGrammarReading P ∧ CutOffReading P`. Its `needsDefinitionIsOwnStandard` model proves this bridge cannot be dropped. With the canon's separate confession of a referent, `FIDEIST-REFERENCE-BUNDLE-FAILS-FOR-CATHOLIC-PRACTICE` also rejects the stronger reference bundle; it does not refute every nonreferential account.

**Decision versus proof:** this is a proposed framework input about an institution's standards, not a definition silently imposed on all practices or a consequence of the canon's wording. The existing source-search attempt preserves arguments on both sides. Owner acceptance would settle this input in the selected interpretation, but the other inputs and the single-rival gap remain. Current route impact: zero.

## 3. Natural reason as shared reason

**Existing statement:** `STMT-NATURAL-REASON-IS-SHARED-REASON`.

**Candidate:** when the selected practice affirms natural knowability of God, that move answers to standards of reason shared with outsiders to the practice.

**Exact scope/type:** `NaturalReasonIsSharedReading P := ∀ m, P.AffirmsNaturalKnowability m → P.AnswersToSharedReason m`. This is about which standards a move answers to, not a claim that everyone actually knows God, agrees on every inference, or occupies a view from no conceptual framework.

**Recorded rival:** `STMT-NATURAL-REASON-WITHIN-THEOLOGICAL-HORIZON`: the tradition's natural reason is exercised within a theological horizon and may be internal to a theistic form of life. This rival is untyped. Non-Christian knowers are not thereby shown to stand outside every theological horizon; that rejected inference remains recorded in `ATTEMPT-LUMEN-NATURALE-WITNESSES-1010`. Choosing this candidate must not quietly replace “shared with outsiders to this practice” by the stronger “neutral to every form of life.”

**Checked consequence:** the same `fideismFailsAsDescription` theorem derives the sharp pair's failure from the canon plus both bridges. `needsNaturalReasonIsShared` witnesses that a correct defined move can answer to no shared standard if this reading is dropped. It is a conditional incompatibility, not a retorsion proving this candidate independently.

**Decision versus proof:** owner acceptance would choose an openly declared reading/framework input; no sourced attribution or independent defeat of the rival reading is inferred from acceptance. Items 1–2 and the single-rival gap still matter. Current route impact: zero.

## The fideism closure gap that three approvals still do not repair

The exact frozen Challenge is:

```lean
(P : Practice)
(hCouncil : CouncilDefinesNaturalKnowabilityReading P)
(hDefinition : DefinitionIsOwnStandardReading P)
(hShared : NaturalReasonIsSharedReading P) :
FideismFailsAsDescription P
```

Here `FideismFailsAsDescription P := ¬ (InternalGrammarReading P ∧ CutOffReading P)`. The relation `REL-WF-CUT-OFF-ALTERNATIVE-TO-REVELATION-RECOGNIZABLE` instead records **CutOffReading alone** as the revelation rival. Rejection of a conjunction does not reject a particular conjunct. There is no recorded `refutes` relation targeting that rival.

Consequently, even hypothetical settlement of all three inputs establishes only the bundle-failure result in today's graph. To count a refutation of the existing single rival requires a checked specialization with `InternalGrammarReading P` established in the same interpretation, or a justified change to the recorded rival's scope together with the appropriate checked result. Do not silently add internality as an established premise merely because it is part of the sharp fideist position. The current relation also uses an external-signs/shared-reason reading in its note without a separately bound premise; any consequential reliance on that reading needs an explicit interpretation/bridge.

`FIDEISM-GRAMMAR-CASES-PARTITION` supplies an exhaustive grammar-fixer partition, but its “neither authorities nor ordinary use fixes the grammar” cell survives the recorded premises (`neitherCellSurvives` in `FIDEISM-FAILS-IN-AUTHORITY-AND-USE-CASES`). Thus switching to the newer case argument does not remove the burden by itself. Its two canon premises, shared-reason bridge, authority/use case bridges and ordinary-use premises must all retain their individual status.

**Computed counterfactuals:** using the existing `corpus.frontier_report` fixpoint in memory at the main revision above, settling item 1, 2, 3 or 4 separately changes no route cost. Settling both bridges also changes none. Settling items 1–3 jointly establishes `STMT-WF-FAILS-AS-DESCRIPTION-OF-CATHOLIC-PRACTICE`, while the cut-off rival remains unrefuted, revelation remains unestablished, and every route cost remains unchanged. These are hypothetical settlements, not actual floor markings. No corpus file was changed for the probes.

## 4. An existing cause of the spacetime whole

**Existing statement:** `STMT-UNIVERSE-HAS-EXISTING-CAUSE` (U).

**Candidate:** at the selected world, the spacetime whole has an existing cause of its existence. This is efficient dependence/conservation, not a claim that time began or that an explanation in a PSR sense is a cause.

**Exact type:** `UniverseHasExistingCause o F w := ∃ c, o.ExistsAt w c ∧ o.Causes w c F.whole` in `TruthCore/Ontology/NaturalismConsequences.lean`.

**Recorded rival:** `STMT-UNIVERSE-UNCAUSED`, which excludes **every** incoming causal edge. It is stronger than ¬U: the supplied `Ontic` need not make causal endpoints exist. `ATTEMPT-NATURALISM-NO-EXISTING-CAUSE-1117` preserves the counterexample to identifying these two denials. U does contradict the stronger uncaused-whole position, but ¬U must not be described as that position.

**Checked rival consequence:** `CAUSED-UNIVERSE-REFUTES-N1` has four premises: U, `STMT-CAUSING-WHOLE-CAUSES-PARTS`, `STMT-NOTHING-IS-EFFICIENT-CAUSE-OF-ITSELF`, and `STMT-THESIS-CONTAINED-IN-SPACETIME`. Its logical contrapositive says that N1 with the *other three inputs* implies **no existing cause**. This is not a consequence of bare N1 alone. A spatial part-of-the-whole thesis makes containment definitional; occupant, relational and physical readings need their own bridge. N2 additionally uses the approved weak causal-concreteness floor item; N3 needs exercise-to-power and N3i needs the whole to satisfy the thesis. No premises may be dropped by grouping all variants as naturalism.

**Why low priority:** `NATURALIST-UNCAUSED-UNIVERSE-SURVIVOR` already witnesses all four variants jointly with a genuinely uncaused whole, an injective infinite regress of proper parts and the listed floor items. U is a contested new commitment, not forced by that floor. Accepting U alone would leave the other three N1 premises unestablished, so the registered naturalist refutations still would not count. Their targets are not registered alternatives to any root leaf; even a counted N1 refutation therefore has no automatic root-cost benefit. No joint root settlement is certified by this proposal.

## Candidates deliberately not duplicated or promoted

- **Meaningfulness of universal laws / negation closure:** `STRONG-VERIFICATIONISM-WITH-LAWS-FAILS` already derives its defeat from the approved weak negation-closure floor item. A new “laws are meaningful” approval is unnecessary for that existing defeat. This does not settle Carnap's V4 proposal reading: `VERIFICATIONISM-PROPOSAL-JOINT-SURVIVOR` and `ATTEMPT-CARNAP-V4-BRIDGE-1008` preserve its distinct pragmatic/analytic escapes.
- **Something changes against McTaggart:** `MCTAGGART-BUNDLE-DEFEATED-BY-CHANGE` already uses approved F3. Its typed scope is the 1908 pair of theses, not every McTaggart-inspired restriction about opiners. No new floor item is requested.
- **N1 excludes existing pure sets:** the naturalism showcase lists the required law/mathematics consequences as not yet encoded. The adopted abstract anchor is not itself a proof that an existing pure set is non-spatiotemporal in the selected sense. No floor proposal here claims that consequence has already been certified.
- **Brute universe has no explanation of contingent existence:** `UniverseUncaused` excludes efficient causes of a selected whole, not all PSR reasons for contingent facts. A causal/explanatory bridge would be needed. No new “everything has an explanation” floor item is inferred from its name.
- **Potency and cogito changes:** the owner already selected the potency definition and existing-in-re/concrete profile work. Those are being audited in their own argument batches, not repackaged here as fresh Moorean approvals.

## Premise comparison and next action

Actual delta: **no premise change**, no new bare premise, no floor proposal enacted. The target closure rule is a future counted defense of `STMT-REVELATION-POSSIBLE-AND-RECOGNIZABLE`; the immediate research action is to encode the conjunction/single-rival scopes and interpretation variants explicitly, then test their conditional consequences before claiming that a bridge decision can settle the recorded rival. An argument may cease to support a particular objection without its entire worldview being globally refuted. The coordinator may present items 1–3 as a precisely scoped package for discussion, with item 4 explicitly lower priority. No item should be submitted as a guaranteed route reduction or as already independently warranted.
