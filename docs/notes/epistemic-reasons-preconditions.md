# What must obtain if there are epistemic reasons?

Analyst investigation for [#930](https://github.com/moritzbrantner/truth-core/issues/930),
2026-11-05. F6 is accepted common ground; this note does not reopen its defense.
Attribution is deferred. These are arguments offered for assessment, not claims
about a historical author's view or new mechanically certified results.

**Conclusion:** accepting epistemic reasons commits us to actual epistemic
favoring: some consideration makes a belief or other relevant attitude better
supported in an epistemic respect. Under the ordinary factual-belief reading,
that respect concerns answering the question correctly or being warranted in
one's answer. A mere propensity to produce belief, or the desirability of
having it, cannot by itself fill that role. This is a constraint on adequate
accounts of reasons, including reductive accounts. It does not establish an
irreducible normative substance, a personal ground, or a reason to seek truth
that overrides every other consideration.

## Three starting points that must stay distinct

1. **Thin encoding.** `STMT-THERE-ARE-EPISTEMIC-REASONS` is
   `TruthCore.Logic.EpistemicReasons.ThereAreEpistemicReasons Reason`, defined as
   `∃ a p, Reason a p`. `Reason a p` means that agent `a` has an epistemic reason
   to believe content `p`. The declaration does not encode a particular
   consideration, truth conditions, support, desire, causation or authority.
   An arbitrary nonempty relation satisfies the formula. Logic alone cannot
   recover the missing interpretation from its name.
2. **Ordinary epistemic-role interpretation.** The accepted existential is
   understood as about considerations counting in favor of attitudes *as
   answers to a question*, rather than merely making those attitudes pleasant
   or producing them. The argument below explains and defends this reading.
   It is semantic and philosophical work additional to the bare Lean formula.
3. **Preference-independent reasons.** Whether at least some epistemic
   support retains pro tanto force for a person who does not want an accurate
   answer is a stronger question. Objective here means this limited
   independence from the subject's desire for the supported answer or for
   accuracy; it does not mean agent-neutral, infallible, overriding,
   irreducible, or independent of every mental/social fact. This independence
   is argued separately in #930; F6's encoding does not specify it.

A genuine goal-relative epistemic reason can meet interpretation 2: its
favoring holds relative to a truth-directed project. Someone who denies even
such favoring denies F6 in this reading. Someone who accepts it but denies 3
is a surviving rival. No change of terminology settles that disagreement.

The transcendental inference is: **there is an epistemic reason; an epistemic
reason cannot obtain without C; therefore C obtains.** It requires a warranted
second premise. Believing the first gives a rational commitment to established
prerequisites; it does not show that one already explicitly believes every
prerequisite or accepts a theory called transcendentalism. Nor does `P → C`
establish that C exists necessarily, at every possible world.

The ordinary-role existential is registered separately as
`STMT-THERE-ARE-ORDINARY-ROLE-EPISTEMIC-REASONS`; the stronger authority
existential as `STMT-THERE-ARE-PREFERENCE-INDEPENDENT-EPISTEMIC-REASONS`.
Both remain **OPEN**, with neither a self-evidence marking nor a certified
result. `DISAMB-EPISTEMIC-REASON-EXISTENCE-ROLE-AUTHORITY` links their three
precise sense definitions and identifies their relationship to unchanged F6.
These reusable analyst propositions have no Lean declaration: a theorem
encoding their role premises would not establish their instantiation or
philosophical warrant. `interpretation_of` is a source-claim relation, so no
such attribution record is fabricated for this analyst fork.

## A complete argument: support cannot be replaced by production

Consider the factual question whether a jar contains an even number of tiles.
An intelligible, competently obtained count can favor the answer “even.” A
pleasant picture, selected without examining the jar and offered solely to
make that answer attractive, does not thereby support that answer. Both can
influence belief. The contrast concerns their epistemic bearing, not how
strongly they influence someone. A count can fail to convince; an attractive
picture can convince very effectively.

The argument has three premises:

- **A.** Some consideration really is an epistemic reason for some attitude
  (accepted F6, interpreted as above).
- **B.** A consideration is an epistemic reason only if it counts in favor of
  its target in a respect relevant to answering the question correctly or
  being warranted in the answer. Warrant allows uncertainty, defeaters and
  justified error; it is not defined as guaranteed truth.
- **C.** Merely causing an attitude or making its possession rewarding does
  not, by those features alone, supply that favorable bearing.

Therefore **some actual epistemic favoring obtains, and any adequate account
must accommodate the favorable bearing rather than substitute sheer causal
influence or reward for it.** The conclusion concerns at least one reason and
its role. It does not assert that all subjects have reasons for every question.

**Why accept B?** A factual belief presents an answer as how things stand.
Enjoying an imagined answer is a different attitude even if the sentence and
pleasure are the same. An assessment of a consideration *as a reason for the
factual answer* must therefore bear on the answer's epistemic merits. If an
account says only that the consideration makes the answer desirable or
psychologically inevitable, it has changed which success it explains. This
is a reason to retain B rather than a stipulation that every truth-directed
practice already generates categorical duties. B concerns what qualifies an
already accepted epistemic reason, not why anyone must enter the practice.

**Why accept C?** The count can favor “even” for someone who remains
unconvinced, while reassurance can produce that belief without supplying
information about the tiles. Favoring and production thus answer different
questions. Similarly, a reward for believing “even” tells us what would pay,
not whether the jar contains an even number. Rewards can become evidence:
for instance, a trusted observer's offering the reward only after counting.
Then their epistemic bearing comes from the informative connection, not from
the reward's desirability alone. This argument excludes a *bare* production
or reward account. It does not exclude an account that explains favorable
bearing through natural causal relations that reliably track the answer.

A and B supply the positive conclusion; C identifies the explanatory
constraint on accounts of it. This is conceptual and case-based warrant,
not a Lean derivation of normativity from descriptive facts. B is defended
here but remains open to philosophical challenge, not newly classified as
self-evident. No new root premise or closure is registered.

## Why these are prerequisites, and what they exclude

The necessity claim is stronger than saying that support would be useful.
Remove the assessable target altogether and there is no answer or attitude
for the alleged reason to favor. Remove every favorable bearing and the
consideration no longer counts in favor of that target in any epistemic
respect; only producing, liking or describing the attitude remains. Remove
applicability to every subject/target and there is no instance left to satisfy
F6 in this reading. Thus denying each *thin role condition entirely* removes
the accepted kind of reason, rather than just making reasoning harder.
This does not require that all targets have only one permissible attitude,
that favoring is comparative in a total ordering, or that all reasons are
evidence in the narrow sensory sense.

A more discriminating consequence is available with one further premise:
**in an ordinary undefeated counting case, relevant contrary observations can
change which answer is supported while the person's desires stay fixed.**
This is evidence-responsiveness. Compare a person who wants an even total and
carefully counts an even total with a person with the same desires who
carefully counts an odd total, with competence, background and defeaters held
fixed. The latter observation does not become support for “even” merely
because the person still wants it. Observation is relevant because it bears
on the total; bare wishing supplies no such bearing. This is an independently
motivated contrast, not a claim of demonstrated metaphysical duplicates.

If reason direction were a function of desires *alone*, equal desires would
always give the same direction. Evidence-responsiveness supplies equal-desire
cases with different support; the two conditions cannot both hold. Hence
**desires alone cannot determine epistemic support in those cases.** This is
a conceptual application of the existing equal-data fiber condition in
`CorrectionCriterion`, not a new mathematical theorem or registered finite
model. The additional responsiveness premise does the philosophical work.
F6 by itself does not ensure such contrasting cases exist.

The result leaves the strongest instrumental rival intact: desires can
select the goal, while evidence determines which answer serves that goal.
It excludes only a desire-only explanation of support, not every goal-relative
account and not reliable causal/naturalistic constitutions that include the
relevant evidence relations. If the rival denies that factual endorsement
has any epistemic merits apart from desire satisfaction, it rejects B; if it
accepts those merits but restricts their force to chosen projects, the
remaining dispute is preference-independent authority.

## Strong objections and what they change

**“You have defined normativity into reasons.”** F6 already accepts some
reasons, rather than merely some beliefs. Extracting their favoring role is
legitimate if that is what was accepted. It would be circular to use B to
convince a global nihilist that reasons exist, or to derive categorical
reasons from merely participating in inquiry. This argument does neither.
Its substantive test is whether an account preserves the distinction between
a consideration supporting an answer and one merely producing it. An owner
who meant only a causal disposition by F6 would need to select that different
starting meaning; ordinary epistemic favoring would then remain unestablished.

**“Reliability is natural and causal.”** Agreed: perceptual and testimonial
mechanisms may make considerations epistemically relevant by connecting them
to the subject matter. A naturalist can propose that reliable, appropriately
functioning belief formation constitutes the relevant support. C does not
require causal duplicates with different reasons, or show that no natural
property realizes the normative role. The open burden is to explain why the
specified reliability/function counts as epistemic support, including
accidental reliability and misleading-environment cases. Those challenges
are not a refutation of every possible naturalist explanation.

**“A false belief can be justified; truth connection is too strong.”** B
requires bearing on correctness or warrant, not actual truth of the favored
answer, known evidence, increased numerical probability in every case,
knowledge, or a perfect method. A misleading but competently used count can
justify an incorrect answer. Logical or mathematical reasons need not supply
new statistical information. Particular accounts of justification may place
different restrictions on cases; nothing here settles internalism,
externalism or whether reasons themselves must be facts.

**“The standard applies only if I want the truth.”** This is the strongest
surviving authority objection. B and C do not defeat it. One may accept
truth-relative epistemic support yet deny any reason for the indifferent
agent to follow it. The positive response in #930 is that factual endorsement
continues to answer a question even when a comforting error is useful. That
supports correction as an epistemic merit; the additional conclusion that
this merit retains normative force without the agent's project remains a
separate argued bridge. Accuracy mathematics alone cannot settle that bridge.

**“A reason must be accessible or motivational.”** Reasons one has,
justification available to one, rational belief based on a reason, and actual
motivation are different. F6 does not quantify over reasoning performances.
This investigation establishes no universal access condition. It also does
not deny that an adequate particular account might require some availability.

## Ranked necessary conditions

“Entailed” below means entailed under the indicated interpretation, not a
new kernel-verified result or a globally accepted philosophical necessity.

| Candidate | Status and precise scope |
| --- | --- |
| A subject, a target content/attitude, and an applicable instance of favoring | Entailed by accepted reason existence in its intended reading. Formal existential witnesses alone do not prove physical agents actually exist; an actual-world interpretation would have to say what the domain represents. The subject need not already believe the content. |
| Epistemic assessability of the target | Entailed under interpretation 2: there must be something for the answer or attitude to get right, or a warrant standard relevant to it. This does not require a complete theory of truth or an accessible exact test. |
| Favorable epistemic bearing rather than mere production or payoff | Entailed under B; B and C have the independent semantic/case argument above. No irreducibility is inferred. |
| Relevant applicability to that subject/target/circumstance | Entailed in the ordinary reading of a reason *for* someone. Not every reason applies to everyone; more information or different circumstances can alter what is supported. No universal impartiality follows. |
| Some favoring independent of the subject's desire for accuracy | Independently argued but open; supplied only if interpretation 3 is selected and defended. It is not guaranteed by the thin F6 formula or B. |
| Preference-independent favoring for the selected objective reason | Entailed once interpretation 3 is accepted. Cross-agent invariance needs relevant circumstances fixed and a further argument. |
| Belief-independent truth conditions for every possible content | Not established. Factual truth can concern mental or socially constituted facts; there is no inference to a comprehensive correspondence metaphysics. |
| Actual possibility of epistemic error, disagreement, correction or a second agent | Not necessary on the present premises. A reason can favor a true answer even if its subject never errs; the examples diagnose meaning without establishing that all reason-bearing settings admit error. |
| Factivity of every reason or truth of every supported belief; logical omniscience; infallible access | Not established. These strengthen F6 and B. |
| A normative role with no possible natural/functional realization | Not established. Role indispensability does not imply ontological irreducibility. |
| A truthmaker, universal PSR, necessary individual, personal author, overriding duty or moral realism | Not established. Each needs a distinct defended bridge; none is a prerequisite demonstrated here. |

## Which explanatory options remain?

A reliable natural/functional account can explain the epistemic bearing through
world-tracking and cognitive function; it still owes an account of its
normative significance. An irreducible impersonal account can take favoring
facts as basic; irreducibility itself is not established. A constitutive or
practice account can explain how correctness organizes factual endorsement;
it still owes the bridge from the role to authority for an indifferent agent.
A goal-relative account can retain reasons within a chosen epistemic project
while denying that last bridge. These are serious explanatory options, not
Lean models establishing metaphysical possibility, and not equally complete
merely because listed. A personal-ground account is another option requiring
its own explanatory case. Global error theory conflicts with accepted F6;
self-undermining alone has not refuted it.

The result is positive but limited: **an account which eliminates every
instance of epistemic favoring fails to accommodate the accepted starting
point; an account which explains favoring by natural facts need not eliminate
it.** “Real” here means that the favoring claim is actually correct in the
selected sense. It does not prejudge substance, reduction, truthmakers or
mind-independence. A theory must preserve this role or explain openly why it
rejects F6; no ontology is selected simply by naming the role normative.

## Exact reuse, rejected proof and remaining question

Read F6's related search and dossier, the existing nihilism result, and the
#929 access/agency boundaries. The exact existing retorsion is
`TruthCore.Results.Logic.EpistemicNihilismRetorsion.nihilismSelfUndermining`:
nihilism entails no reason to believe nihilism, not its falsity.
`TruthCore.Results.Logic.CorrectionCriterion.characterization` concerns an
exact extensional classifier iff correctness is invariant on equal-data
fibers. It does not give human access or bind an agent to a norm.
`TruthCore.Results.Logic.TranscendentalPractice.InquiryAccess.boundary` and
`TruthCore.Results.Logic.TranscendentalPractice.AgencyDuty.boundary` preserve
those access/authority distinctions. #756's epistemic/ontic boundary, #932's
discursive-authority investigation and #933's grounding question remain
separate; no undelivered bridge from them is used.

The merged PR #1045 argument is linked in
[the correction note](epistemic-reasons-930.md). It was inspected read-only at `ffe53ec53150bacad511a1a5ff1b8b2fcb926993`,
contains the earlier #930 argument and mathematical accuracy controls. Its
proofs are not imported or restated here. No accuracy cost has been used as a
normative premise in this investigation.

A new Lean theorem `∃ a p, Reason a p → ...` deriving nonempty domains would
add no philosophical content. Adding a new predicate “epistemic favoring” and
assuming `Reason → Favoring` would merely transcribe B. Both were rejected;
there is no new theorem, frozen Challenge, source claim or formal
model. The two consequential analyst readings are separate open statements,
with linked definitions and disambiguation rather than a decorative proof. This note and the linked attempt preserve the argument rather than
advertise a manufactured proof count.

Premise comparison: F6 retained as accepted common ground. B adds the openly
defended ordinary-role interpretation; C defends a distinction used to assess
explanations. Neither is classified as a newly closed premise. Preference
independence is not added as an undisputed input. No philosophical or root
premise is discharged; the two open sibling statements and their sense records
add reusable interpretation metadata, without a formal inference, root route
or closure change.

The next consequential question in #930 is whether being an epistemic merit
of factual endorsement itself supplies a pro tanto reason for a person wholly
indifferent to accuracy. The goal-relative reply must be answered on its own
terms. Ontological grounding is downstream of fixing that authority claim.
