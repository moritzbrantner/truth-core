# Evidence gives a reason against wishful distortion (#930)

Analyst argument, 2026-11-05. Attribution deferred. This note investigates a
positive reason to believe the principle, rather than claiming that the previous
truth-policy/access countermodels establish it. The selected conclusion is:

> When a consideration is independently warranted as bearing on whether p is
> true, it gives a defeasible epistemic reason to adjust one's confidence in p
> accordingly. Merely wanting p to be true supplies no competing epistemic
> reason unless the desire is itself warranted evidence about p.

This is a positive, preference-independent claim **within epistemic evaluation**.
It is not a universal obligation to investigate, acquire every truth, maximize
accuracy at any cost, or believe a precisely known probability. It does not say
that every actual desire is evidentially irrelevant: wanting water can be evidence
of thirst; wanting an election result need not be evidence of its occurrence.
The qualification “independently warranted” excludes assuming that a comforting
answer has a higher probability simply because it is comforting.

## What counts as a reason here

Here “pro tanto” means a reason that can be outweighed. A pro tanto epistemic
reason is a consideration counting in favor of holding,
withholding or revising a representation **with respect to getting its subject
matter right**. It can remain a reason when it loses an all-things-considered
choice. This fixes the domain and the weight distinction; it does not establish
that there are any such reasons. That existence/authority claim is defended
below, not built into the mathematical definitions. “Genuine” does not mean
“categorical and overriding by definition.”

Truth-indication is a relation between an item of evidence and a proposition's
being true under a warranted interpretation. Accuracy is success in representing
that subject matter. Epistemic reasons concern how the representation is supported;
practical reasons concern what to do, including whether to investigate at all.
An instrumental goal is an independently chosen end. A categorical,
all-things-considered ought would bind regardless of competing ends or reasons.
These notions cannot be substituted for one another. None supplies an ontic
reason why the represented fact exists (#756).

## The positive argument and why accept its premises

1. **Believing and merely enjoying a representation are different attitudes.**
   To believe that the bridge is safe is to take its safety to describe the
   bridge. To enjoy imagining it safe need not do that. The difference explains
   why discovering a crack can correct the first attitude while leaving the
   pleasure of the second intact. It also explains disagreement: one person's
   contrary belief conflicts with the first representation, while contrary
   fantasies can coexist. These are reasons to accept truth as a correctness
   standard of factual belief; they are not a definition making every belief
   justified or every believer a conscious truth-maximizer.
2. **A warranted indication of error supplies a defeasible reason for correcting
   an endorsed representation, considered as a representation.** This is the
   normative bridge. The grounds for accepting it are the discriminating roles
   of evidence in correction, disagreement and justification: a crack is a
   reason to reduce confidence in safety because it bears on safety, whereas a
   comforting paint color does not thereby answer the safety question. The
   same distinction survives reversing our wishes: when we wish the bridge
   unsafe, the crack's epistemic direction does not reverse. An explanation
   that makes correction answer solely to comfort fails to account for this
   difference. The bridge therefore has explanatory and comparative support;
   it is not derived from the meaning of “representation,” nor from algebra.
   A harmless control is a sealed photograph containing seven counted blue tiles.
   Wishing there were eight does not change the count; recounting can correct
   the belief even when nobody will act on it and nothing dangerous follows.
   The proposed reason concerns what the photograph shows, not a precaution
   against harm. Bridge safety illustrates the same distinction with practical
   stakes added, not its normative source.
3. **Desire alone need not change the indicated subject matter.** Hold the
   evidence fixed while reversing which answer is comforting. In ordinary
   cases like an already counted election or a structural inspection, that
   reversal need not alter the result or its evidence. Then desire supplies a
   reason to enjoy, imagine or perhaps promote an answer, but no additional
   indication that the answer describes the world. This is a restricted
   independence claim, not a ban on psychological or self-fulfilling evidence.
4. It follows, given bridge 2, that wishful distortion has an epistemic reason
   against it even if the agent does not enjoy accuracy. That reason comes
   from the assessment's bearing on what the person represents as actual, not
   from a chosen numerical reward or the observer's disapproval. A comforting
   false representation may nevertheless be practically preferable. Its
   practical benefit does not make it better supported as a factual answer.

The key advance over “if you want truth, follow evidence” is premise 2: the
indication is offered as a reason whether or not accuracy is desired. This is a
substantive, defeasible normative judgment with articulated support. We have
not given a premise-free demonstration that forces assent to that judgment.
Calling the bridge open records this limit; it does not mean that no reasons
have been offered to accept it.

## Constitutive standards are not automatic obligations

Good knives cut and legal chess moves obey rules. Neither fact obliges anyone
to cut or play. Likewise, factual representation does not obligate anyone to
investigate every question. One can suspend belief, avoid a topic, or enjoy an
acknowledged fantasy. The argument concerns how an already endorsed factual
answer is supported; it supplies no obligation to enter that activity.

Even this restricted claim requires bridge 2: merely having a correctness
standard could yield only a classification of success/failure. We defend the
further, evaluative claim that warranted error-indications count against an
endorsed representation. The knife/chess objection correctly defeats the
inference “has a standard, therefore categorically ought.” It does not by itself
defeat the more modest reason against representing a cracked bridge as safe,
considered as a factual answer. A good knife may be a bad murder weapon to use;
a comforting belief may be bad as an answer yet good for morale. Recognizing
one dimension's assessment does not settle the whole choice. There remains a
serious rival who denies that even this dimension supplies actual reasons.

## Checked mathematical support, including uncertain assessment

`TruthCore.Logic.EpistemicAccuracy.error q r` is the expected binary squared
error of credence r under assessment q:

    q(1-r)^2 + (1-q)r^2.

For substantive probability use, q and r lie in [0,1]. The identities happen to
hold for all real inputs; negative probabilities are not thereby admitted.
The certificate establishes the exact regret identity

    error(q,r) - error(q,q) = (r-q)^2,

nonnegative regret, and equality exactly when r=q. A distortion therefore has
an independently calculable cost under the stated accuracy criterion. No
Ought/Reason predicate appears in the theorem. It does not merely pass an
opaque bridge premise straight through a proof.

We need not pretend to know the correct q. If all independently admitted values
of q lie within ε of c, ε≥0, and r lies more than 2ε above or below c, then r has
strictly worse expected error than c **for every admitted q**. The proof factors
the difference as `(r-c)(r+c-2q)`. For example, c=0.5, ε=0.1 and r=0.8 give a
strict cost for every q in [0.4,0.6]. This does not say that c is the unique best
response to imprecise evidence, or that every small departure is a distortion.
If the credible range is broad enough, this guarantee can fail. Neither the
range nor its warrant is established by the theorem.

Why use squared error? It treats truth and falsity symmetrically, increases
with distance from the actual binary outcome, and grades confidence rather
than only categorical correctness. Its expectation strictly favors reporting
the probability used in the assessment instead of shifting it toward a wished
outcome. These are reasons to use it as one transparent accuracy measure.
They do not prove that every admissible epistemology must use Brier loss or
that all possible accuracy measures deliver this exact cost. We add no scoring
framework. Desire-independence and correction in the preceding argument do
not stand or fall with squared error's unique numerical weighting.

The concrete certificate also shows: at q=1/2, moving from r=1/2 to r=1 costs
1/4 expected squared error; granting the latter a practical comfort reward of
1 makes its combined cost smaller. This is a satisfiable, nonempty numerical
rival to **overriding** accuracy, not a disproof of epistemic reasons. The
positive epistemic reading and the practical preference use exactly the same
error function and inputs. No normative answer is hidden in the choice of
actual outcome or an empty domain.

## A probability-free positive foothold

There is a stronger, deliberately restricted accuracy result. Suppose a person
assigns confidence r to p and s to not-p, with each in [0,1]. If r+s differs
from one, the projected pair

    r'=(1+r-s)/2, s'=(1-r+s)/2

remains in [0,1], sums to one, and reduces the **summed** squared error of the
two representations by `(r+s-1)^2/2` in BOTH possible truth states. The separate
`Statewise.dominance` theorem proves the bounds, coherence, exact reduction and
strict dominance. For r=s=0.8, the correction is r'=s'=0.5 and the reduction is
0.18 whichever proposition is true. No known q, calibrated prior or probability
range is needed. No knowledge of which state obtains is needed either.

This supplies a particularly strong application of bridge 2: the original pair
incurs an avoidable representational defect under every possible answer to the
factual question, with no tradeoff in the companion representation's summed
score. The improvement is mathematical, not an alleged punishment or lost
money. A comfort-seeker can still reject accuracy's normative relevance, so
this is not a deductive refutation of the strongest rival. But uncertainty
about which answer is true cannot defeat this particular reason for correction.
We do not claim that all wishful beliefs are incoherent: a coherent but biased
pair generally has no such statewise-dominating correction. There the expected
accuracy argument still depends on warrant for an assessment or range.

These comparisons evaluate credence assignments; they do not assume that people
can directly choose their beliefs. Optimizing a reported probability is not
automatically changing genuine belief. The comfort-reward control compares
modeled evaluations, not an available voluntary act of wishful believing.
Evidence-responsive revision, managing attention or seeking further information
may occur over time; no instantaneous control or duty-from-ability inference
is supplied here.

## The strongest surviving rival

The strongest rival accepts every mathematical identity and descriptive
correctness distinction, yet denies bridge 2. It says: “Evidence marks an
answer accurate; that is an actual reason only if accuracy is one of my goals.
I prefer comforting factual belief even knowing it is less supported. I can
still follow conditional inference rules without accepting categorical reasons.”
This position is coherent. It is not refuted merely because its speaker uses
reasoning or because belief has a truth condition. Our #929 boundaries remain.

The cost of this rival is substantive: it withholds preference-independent
reason-giving force from the very distinction between correction and comforting
rationalization. It can classify an erroneous assessment but cannot criticize
it epistemically independently of the agent's ends. The positive view better
preserves the ordinary intelligibility of “I have evidence against this, even
though I would be happier believing it.” That is an abductive and reflective
case for bridge 2, not a proof that all coherent accounts must accept it. A
revisionary anti-normativist can accept that cost. The argument offers support for the modest reason-giving principle without
settling whether its ultimate account is realist, constitutive or constructive,
or establishing a complete metaphysics or an anti-skeptical victory.

An internalist demands accessible warrant for the estimate or evidence range;
a reliabilist may instead emphasize a genuinely reliable process even when
its rate is unknown to the agent. Both have a place for truth-responsive
correction, but disagree about what licenses using a particular q. Our result
assumes neither that subjective coherence calibrates q nor that external
reliability automatically gives accessible justification. A social-practice
account can explain agreement about standards; it still owes an account of
why error counts against an answer when local approval rewards it. A theist
or non-theistic normative realist may accept the positive principle; neither
the source nor the necessity of a normative ground follows from it.

## Reuse, premises and present handoff

The existing STMT-THERE-ARE-EPISTEMIC-REASONS is already an owner-approved
common-ground floor (F6, #1007). Its existential Reason predicate does not
identify which considerations are reasons. Its existing nihilism retorsion
expressly distinguishes self-undermining from falsity and retains the global
nihilist rival. We reuse that distinction, introduce no replacement Reason
predicate, and do not present #930 as first establishing the existential floor.
This argument tries to identify and defend a concrete kind of reason.

Inspected `related` and dossiers for the #924 truth-directed duty and #929
inquiry/access and agency/duty boundaries; inspected #930/#932 briefs, existing
transcendental attempts, the #756 epistemic/ontic distinction, and existing
contrastive-worldview results. No existing Brier/regret theorem was found.
The old results are retained as boundaries, not copied or renamed as positive
normative achievements. This slice needs no new source, passage or claim.

Formal assumptions added: a particular squared-error interpretation; for the
robust comparison, ε≥0, the admitted interval and separation by more than 2ε.
These are explicitly quantified conditional inputs, not established facts about
an agent. No q/calibration fact, moral realism, God or ontic PSR is retained as
a premise of the mathematical theorem. Philosophical assumptions defended but
not mechanically established: factual belief's truth standard, the restricted
desire/evidence independence, and especially bridge 2. Removed/discharged:
none of the previous authority/access or root premises. Positive warrant has
advanced by giving reasons for a restricted reason-giving principle and an
explicit strongest rejection, separately from the new accuracy consequence.
There is no universally categorical or all-things-considered duty result.

Next decisive question: whether the explanatory advantage of preference-
independent correction justifies bridge 2 against the goal-relative rival;
then, separately, how much warrant a concrete evidence range has. Investigating
God's existence or acquiring historical source witnesses is not the missing
step of this argument. The exact root-frontier comparison and delivered-head
verification belong to the linked PR/issue handoff.

Issue #930 remains open: this delivers a positive defeasible argument and
accuracy theorems, while the general authority challenge survives at bridge 2.
