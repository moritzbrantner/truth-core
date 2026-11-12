# Transcendental foundation routes: practice, correctness and normative authority

**Investigation status (2026-11-02):** analytic, source-free candidate comparison; two new Lean
boundary experiments proposed for Comparator certification. No additional
historical interpretation is attributed to a thinker or to the positions below.
Formal home: `TruthCore/Logic/TranscendentalPractice.lean` and the two
`TruthCore/Results/Logic/TranscendentalPractice/` certificates. The starting
revision was `c0f23be` (after PR #924 and the explorer improvements).

**Method clarification (2026-11-12):** An actual, suitably interpreted
practice can provide prima facie or constitutive warrant for its genuine
necessary preconditions. Do not demand an indefinitely prior, independent
argument for each such condition. Test whether the alleged precondition is
really necessary in that same practice and whether a stronger ontic or
categorical conclusion needs a distinct bridge. This clarification does not
upgrade the conditional results below into claims about actual performance.

## The thesis and the decisive fork

Transcendental arguments have the form: **activity/commitment A occurs or is
undertaken; condition C is necessary for A; therefore C**. The disputed step
is usually the second, especially where C moves from a semantic rule of a
practice to an independently existing epistemic/moral standard or a necessary
metaphysical ground. A semantic truth or a formal proof can be a necessary
*description of successful* activity without being a necessary precondition
for an agent's *attempt* at that activity.

Test each proposed condition in three distinct strengths:

1. **Constitutive:** the activity, in the specified sense, counts as successful
   only if C holds. A denial while advertising the very same successful act
   may be contradictory, but the truth of the practice's actual success and
   the interpretation of C still require justification.
2. **Instrumental/dialectical:** C makes the activity reliable, correctable,
   defensible or consistent with an agent's declared aims. Denial can create
   a pragmatic or self-application burden, without a contradiction by logic.
3. **Ontic or categorical:** C is a mind-independent obligation, objective
   truthmaker, necessary source or divine attribute. This requires a further
   bridge and independent defense; do not build it into the meaning of A.

Only a **same-sense** assertion plus actual scope/standard and a certified
contradiction earns the label *performative contradiction*. Someone making a
mistake, using a convention, or accepting only a local reason-demand need not
contradict their stated commitments. An internally false assertion is possible
without making all assertions inconsistent.

**Independent-warrant audit.** The new proofs justify *logical relations*
inside specified formal meanings: an exact criterion implies fiber invariance,
and realization through a unique effective means entails its performance.
Neither result independently justifies the existence of an actual epistemic
norm, a true moral duty, a warranted observer, or an actual successful practice.
Worlds, efficacy, deontic predicates and selection policies in the finite
controls are stipulated. Source-backed discussions already exist in the
linked Wittgenstein, Sellars, Hume, Aristotle, Gibbard and metaethics dossiers;
their source interpretations are not re-proved or automatically imported as
new foundational premises here. Immediate first-person awareness or public
observation could supply a separate warrant for **an activity's occurrence**,
but it does not supply the proposed ontic conclusion by definition.

## Ten starting points, grouped into three vertical slices

| Activity or commitment A | Candidate necessary precondition C, and its status | Denial test and most important open bridge |
| --- | --- | --- |
| **Rational inquiry:** asking questions answerable to something beyond preference | A target distinction and some correction standard for *successful* truth-directed inquiry. The exact-classifier fiber condition is formally derived only under a supplied truth interpretation and data projection (`STMT-CORRECTION-CRITERION-EXACT-FACTORIZATION`). Actual inquiry and method reliability are not proved. | A method may inquire, produce mistakes and revise them without perfectly discriminating all states. Denial of an *exact* criterion is not a performative contradiction unless exact success is claimed. An objective, universally binding inquiry norm remains open. |
| **Truth-directed belief:** selecting what to believe because it is true | A distinction between actual truth and acceptance; PR #924's `TruthDirected` is a *stipulated normative policy*, not derived from merely having beliefs. | Two-world controls preserve consistent but false acceptance. Error or selective belief alone is not a contradiction. The truth-directed ought and epistemic entitlement need independent warrant. |
| **Avoiding wishful thinking:** refusing to treat desire as evidence | Separability of desire from evidential support, plus a policy disfavoring desire-led belief. Separability is a conceptual/operational proposal; **the obligatory policy is not proved** by the mere possibility of self-deception. | Someone can choose a comforting belief and remain logically consistent. Calling the choice an epistemic vice requires an epistemic norm and its applicability. A speaker explicitly endorsing the norm while exempting themself may face *same-rule* self-application, a different charge from proving objective duty. |
| **Logical inference:** moving from premises to conclusions | Under one fixed semantics, valid inference preserves truth if its premises are true. This is a conditional meaning of soundness, not a proof that any asserted premises are true. Truth Core already has `TruthPilot`, `TruthNontriviality`, self-application and the classical/intuitionist competitors. | Using one local inference rule while doubting some global logical principle can be coherent. Contradiction requires accepting both a rule and its denial in the *same scope and sense*. A uniform metaphysical foundation of every logic is not entailed. |
| **Meaningful assertion:** presenting a content as true in a sense | A content and an identifiable truth-sense (`SelfApplication.AssertionCommitment`); an **accurate** assertion also needs truth. Assertion need not be accurate. `PerformedDenial` already handles universal denial of performed episodes. | A false assertion is possible. A *performed and accurate* universal denial of its own kind of episodes is impossible when its denial covers that episode. Withholding, irony, fiction or asserting a false denial does not produce that contradiction. |
| **Knowledge:** claiming to know a proposition | Factivity for the specified meaning of knowledge (`KnowledgeRetorsion`); having an actual knower or justified belief is separately open. | Factive knowledge of *no one knows anything* is refuted, but asserting that sentence or withholding knowledge is not. An externalist naturalist or skeptic can accept local factivity without a necessary knower. |
| **Error correction:** distinguishing mistake from correction | For an **exact evidence-only** classifier, correctness is invariant under indistinguishable reports (`CorrectionCriterion`). This is a mathematical characterization, not a justified or computable method. | Two Boolean worlds with identical reports and different truths defeat exact classification, even with a truth-directed ideal policy. Denying exact access is not denying truth or all practical self-correction. |
| **Practical reasoning:** selecting means for an end | For an end *actually achieved* through a uniquely effective action, that action must have been performed (`STMT-TRANSCENDENTAL-AGENCY-DUTY-BOUNDARY`). This is a verified-form conditional target, not a claim that mere intention compels action. | An agent may desire an end and fail to act or judge falsely about its means. A constitutive instrumental norm must be stated separately from causal success; no categorical duty follows from the conditional. |
| **Moral obligation:** saying that an action ought to be done independently of one's preferences | A normative authority or defended deontic bridge, not simply factual descriptions or success. `DescriptivePlanBoundary` already certifies descriptive/factual freedom under its planning language. | Opposite duty assignments are jointly satisfiable with the same successful means-end behavior. Expressivist planning, constructivist obligation and non-theistic realism are still available. An objective duty and its unique necessary source are not deduced. |
| **Responsible agency:** evaluating an actor as answerable for an act | Candidates: reasons-responsiveness, control, ownership, competence, alternatives, or fair information; none is *the* precondition without selecting a theory of responsibility. | An action can occur without any duty to assign praise/blame, and constraint does not automatically eliminate all responsibility. A real-world bridge from agency to deserved obligation, moral realism or a free personal necessary ground is open. |

## Two new certified targets and their controls

### A. Epistemic truth versus epistemic access

`LOGIC-TRANSCENDENTAL-INQUIRY-ACCESS-BOUNDARY` composes the existing
`CORRECTION-CRITERION-EXACT-FACTORIZATION` with PR #924's fixed
two-world semantics. It specializes exact criterion factorization to the truth
of a content and constructs **two joint models**:

- `TruthDirected` selects the empty actually true worldview. Both worlds report
  `(true, true)` but disagree about truth of the content `true`. Consequently no
  classifier on those reports can be exact. This is a model of an *ideal
  selection policy without data-relative access*, not of a successful human
  inquirer or an actual method.
- Identity reports distinguish the worlds and admit an exact classifier for
  the very same content. The selection policy `onlyDenier` still chooses the
  wrong worldview at actual world `true`. This is *access without a
  truth-directed policy*. It is not a defense of choosing wrongly.

Thus neither ideal normativity nor exact criterion availability is sufficient
for the other; the evidence-to-norm bridge cannot be omitted. The first clause
of the theorem obtains `FiberInvariant` from the imported characterization,
not a second implementation. No normative truth, temporal revision or actual
epistemic warrant is certified.

### B. Instrumental success versus categorical duty

`LOGIC-TRANSCENDENTAL-AGENCY-DUTY-BOUNDARY` proves: a valued goal *realized*
via an action which is the only effective one entails that that action was
performed. Its **two inhabited two-action controls** have the same desired
end, the same actual performance and the same efficacy relation. The duty
predicate is true for the effective action in one and false in the other.
This shows the descriptive/functional state of this small practice does not
determine categorical oughts. It does not prove that one should always follow
valued ends, or that objective duties are fictional. The one-step efficacy
relation (working action versus irrelevant action) has no assumed causal
mechanism, time, transitivity, asymmetry or well-foundedness; generalizing it
to a metaphysical dependence relation would require another explicit bridge.

`DEF-TRANSCENDENTAL-GOAL-REALIZATION` distinguishes actual production from
mere planning; `DEF-TRANSCENDENTAL-CATEGORICAL-DUTY` is deliberately
uninterpreted. Importing an ethical realist's bridge may exclude one of these
models, but its premises must be published and challenged, not added silently.

## Rival completions, not straw positions

- **Naturalistic/reliabilist:** real error-correction, successful reasoning and
  local reason-giving can be grounded in natural processes, testable norms and
  socially maintained inquiry, while ultimate explanation or categorical
  morality remains unsettled. Existing #737 and #756 controls show that a
  local epistemic demand is not automatically an ontic PSR. Burden: actual
  reliability, calibration, and a credible account of normative authority.
- **Constructivist:** the categorical-sounding authority of reason may arise
  from commitments constitutive of agency or the practice of giving reasons.
  It must specify who is bound, why the norm survives changed preferences,
  and whether the scope is universal. A constitutive rule is not automatically
  a necessary concrete being.
- **Expressivist/quasi-realist:** an ought can play an inferential and planning
  role without being a representational report about an objective property.
  Truth Core's `PlanStateEmbedding` and `DescriptivePlanBoundary` leave this
  serious branch open. Burden: embedding, disagreement, and distinguishing
  robust obligation from chosen plans under real hard cases.
- **Skeptical/quietist:** one may perform inquiry, assertion and conditional
  reasoning while withholding an all-encompassing theory of their ultimate
  grounds. This is not self-refuting unless the position makes an explicit
  same-sense universal claim that its own act or assertion contradicts. Burden:
  articulate honest local standards and how to address persistent error.
- **Objective realist / classical theist:** genuinely binding epistemic and
  moral norms may be non-optional and ultimately grounded in a necessary
  intellect or Good. The strongest case is not merely an inconsistency charge
  but a discriminating bridge from such a norm's authority to the nature of
  its necessary ground. The existence and uniqueness of that ground and its
  intellectual/willing attributes require arguments against serious
  non-theistic normative realism, not just against inconsistency.

These are analytic competitor templates. No historical school or individual
is said to endorse the exact Boolean models; documentary source claims must
be grounded independently in pinned primary witnesses.

## Connections and exact frontier consequences

| Existing corpus route | What this investigation connects | Why it does not close a premise |
| --- | --- | --- |
| `STMT-TRUTH-DIRECTED-REFLECTIVE-DUTY` (PR #924) | Its truth-directed `OughtAdopt` policy is reused in the epistemic access countermodel. | The policy's normative authority and duty-content truth remain open. |
| `STMT-CORRECTION-CRITERION-EXACT-FACTORIZATION` | Its exact equivalence theorem is imported and specialized to truth; the finite controls separate norm and access. | No evidence provides warranted actual-world correction. |
| `STMT-NO-FACTIVE-KNOWER-OF-UNIVERSAL-NO-KNOWLEDGE` and `PerformedDenial` | Their retorsion and assertability limits provide the assertion/knowledge family without duplicate propositions. | No actual knower, thinking substance or universal epistemic authority follows. |
| `STMT-PSR-SELF-APPLICATION-STANCE-MAP` / `STMT-PSR-EPISTEMIC-ONTIC-BRIDGE-LADDER` (#756) | Reasons for believing are kept separate from reasons why facts obtain. | No epistemic-to-ontic PSR bridge follows from practice. |
| `DESCRIPTIVE-PLAN-BOUNDARY` and #370 | The agency control tests an additional actual-success/categorical-ought separation. | Normative realism and the identity of the Good with God remain open. |
| `STMT-WILL-FOLLOWS-INTELLECT`, `STMT-IMMATERIAL-IS-INTELLECTUAL` (#143 root) | Potential downstream route, if an independent objective normative ground and necessary intellect could be established. | Our action profile models no intellect, divine substance, immateriality or modal necessity; these root premises cannot be inferred. |

No new `root_route` or `refutes` relation is warranted. There is **no
inference edge** to a necessary being, divine intellect or the Catholicism
root: that would conceal an unproved metaphysical bridge. The graphs gain two
formal result candidates with source-free, individually typed
statements, inferences, arguments, attempts and definition links. They add no
root-reaching philosophical premise or new root route. At the inspected
`c0f23be` baseline there were 12 root routes, cheapest cost **31** open leaves;
rerun `python3 scripts/corpus.py frontier --routes` and
`--reaching-root` on the delivered revision before claiming any delta.

## Next decisive investigations

1. **Normative bridge:** articulate the strongest non-circular argument that
   rational inquiry or avoidance of wishful thinking actually obligates an
   agent rather than simply constituting a preferred practice. Contrast an
   objective epistemic duty with a constitutive or prudential rule and test
   finite rival models *before* positing a source for the duty.
2. **Truth-access bridge:** demand a realistically applicable correction method
   or warranted fallibilist substitute under imperfect evidence; `AdmitsCriterion`
   alone is extensional and not computable or epistemically accessible. Compare
   reliable and systematically misleading but locally coherent agents.
3. **Moral-ground bridge:** if an objective categorical norm survives rivals,
   test why its authority needs an individual, why that individual is necessary,
   and why an impersonal normative fact or constructive practice fails. Only
   then attempt a typed connection to necessary concrete being or divine
   intellect. Trace premises one bridge at a time; the root remains open.

**Self-sweep:** These are universal conditionals and *existence of finite
models*, not universal facts about real agents. The positive premises of the
goal theorem are `Realizes` and `OnlyEffective`; the first entails actual
performance already for some action, and the second forces it to be the named
action. The models each have `Unit` goals and `Bool` actions/worlds; no carrier
is empty. Epistemic selection may be extensionally ideal but is not an actual
time-indexed belief formation, and the agency model is actual-success-only,
not intention. No new source claim or self-evident marking is introduced.
