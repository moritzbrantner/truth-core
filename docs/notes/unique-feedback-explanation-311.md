# Unique feedback and whole-chain explanation (#311)

The state equations `a = !b`, `b = a && b` have one satisfying
Boolean pair, `(true,false)`. Their gates are nonconstant: negation
changes across its two inputs; conjunction changes when either input varies
with the other held true. These are logical constraints. They are not
world-local causal edges, temporal evolution, pure copying of plans, or
borrowed instrumental powers. Sensitivity is a truth-table property, not
an assertion that each single-bit perturbation at the solution changes
both outputs.

| a | b | First equation | Second equation |
|---|---|---|---|
| false | false | fails | holds |
| false | true | holds | fails |
| true | false | holds | holds |
| true | true | fails | holds |

`UniqueFeedback.Controls` certifies sensitivity, the satisfying witness,
and equality of every consistent state with it. The proof does not select
an observed boundary value or assume uniqueness. It eliminates the other
three states. This is a nonvacuous satisfiability/uniqueness control; no
explanation predicate is present.

## Reuse and nonduplication

- Merged #299's `EssentialPowerUnderdetermined.essentialPowerUnderdetermined`
  gives all-on/off solutions and cut responses. Its local rule is preserved.
- `LocalObservationSelectsSolution.localObservationSelectsSolution` supplies
  determinacy only after fixing an observation. This control needs none.
- `RegressDomains.CycleAndConverseBoundary` admits equal least/greatest fixed
  points on an intrinsic self-loop. That supplied intrinsic predicate is not
  used here; neither fixed-point selection convention is used.
- Pending #619 owns complete-presence-history contrasts and differing reason
  assignments on the same memberwise structure. It is comparison evidence,
  with no dependency on its unmerged declarations. Those assignments are not
  repeated here.

No existing philosophical conclusion is imported as a fresh premise.
The previous theorems are comparison evidence; the new result proves only
its own distinct finite control.

## Surviving explanation question

Mathematical solution multiplicity cannot be the entire objection to logical
feedback: the constraints here are satisfied and have no second solution.
This does not prove an adequate ontological explanation or prove its absence.
The strongest rival says that the intrinsic global structural fact explains
the satisfying state. A brute global fact and a non-well-founded grounding
account are distinct further answers. None is eliminated by this table.

To reject the structural answer, one must specify which obtaining fact needs
explanation, what counts as sufficient explanation of it, and why satisfying
these global constraints does not meet that norm. A whole-series PSR or a
contrastive requirement must enter explicitly; neither automatically implies
externality or rules out explanatory circularity. No notion of explanation
is defined to prohibit loops. Conversely, uniqueness alone supplies no
independent defense of those norms or of the global structural answer.

The issue's original plans bootstrap still requires a richer interpretation:
these gates are not an inventor-free copying history. No inference from lack
of an inventor to impossibility, from consistency to metaphysical possibility,
or from explanatory dissatisfaction to an original causal source is made.
EXP-SCOPE, EXP-LOCAL-TO-GLOBAL, EXP-NONCIRCULAR and EXP-ULTIMATE remain open.
Source attribution remains paused; no historical claim is added.

## Premises, verification and service evidence

Intended and actual root-path open-premise delta: zero. The closed certificate
has no ordinary premises and no new root connection. All root philosophical
premises are retained; none is discharged.

The Challenge was frozen before proof work, SHA256
`80249ef71f3aa529bc97d4343b15e5af74788f8de1b0b631226a2b897a91325d`.
The shared persistent service accepted repeated full-content edits without
mutating its checkout/imports, at workspace
`/home/brantner/privat/truth-core-sprint-proof`, head
`75192b1c3efdf19f25601e52a06116e706420f11`, session `causal-harvest`,
path `Scratch/issue311.lean`. HTTP 200, final content SHA256
`d9a641f7007215a7884b0ec70d00651952546916e250d2df5e99cb870ae8c949`;
no errors and `#print axioms` reports no axioms. Initial implicit unfolding
failed; explicit unfolding and direct Boolean contradiction proofs fixed it.
Lease wait was 0.000010s, first request 0.836s, corrected warm request 0.230s.
Retain the warm serialized service for small edits; no second session or
benchmark rerun was needed. These are interactive diagnostics, not final
Comparator verification.

Canonical final CI owns build, binding, Comparator and NanoDa. After build,
reproduce the result gate with
`python3 scripts/worker_env.py -- scripts/verify-result.sh UNIQUE-FEEDBACK-CONTROL`.
The attempt record retains rejected interpretations and precise evidence.

## Explanatory-adequacy audit: what an endless series is asked to explain

The renewed Agrippa/Münchhausen question is about whether a regress supplies
what an inquiry requires, not whether an infinite set is contradictory. The
explanatory version in #311 has a specific primary-source argument. The pinned
Latta translation of *Monadology* §§31–45 was materialized and read in full
(`LEIBNIZ-MONADOLOGY-31-45`, text SHA256
`48c8019d588af3c5d262323ea365382be7021bf4f4ee23f7f0b68eb6650b6d04`).
This is an explanatory argument, not a historical attribution of Agrippa's
modes to Leibniz and not an inference from skeptical suspension to causal
impossibility.

### The source's demand and proposed answer

1. **Scope, §32:** a real/existing fact or true statement calls for a sufficient
   reason why it is so rather than otherwise. A reason may be unknown to us;
   lack of discovery is not absence of explanation. This is the stated PSR,
   not something the existing mathematical controls establish.
2. **Necessary truths, §§33–35:** their reasons are sought by analysis into
   simpler truths, terminating in primary identity principles whose opposites
   contradict. This is a proposed nonarbitrary analytical terminus, not a
   license to stop at any favored assertion. Its legitimacy still needs
   defense against rival epistemologies.
3. **The explanandum, §36:** contingent truths include the sequence or
   connection of created things. The example of the present act of writing
   allows infinitely detailed efficient and final causes. Thus the argument
   does not simply demand finitely many prior events or deny infinite detail.
4. **The insufficiency step, §37:** those further contingent details again
   require analysis for their reasons. Leibniz takes that renewal to leave
   the final question unsettled and concludes that the sufficient final
   reason lies outside the contingent series, however infinite it is.
5. **Proposed ground, §§38,45:** the conclusion is a necessary substance;
   §45 describes this proposed necessary being as having the reason for its
   existence in itself. This is not efficient self-production. Necessary-truth
   analysis in step 2, a de re modal existence predicate, and a sufficient
   intrinsic existence reason are not interchangeable.

These are sourced argument steps and open commitments, not a newly certified
inference application. The existing
`STMT-LEIBNIZ-SERIES-SUFFICIENT-REASON` already records the final
outside-the-series conclusion. The new readings expose what drives it rather
than registering the desired conclusion as another bridge assumption.

The distinctive criticism is **explanatory deferment**: an account of why
this contingent reason obtains merely introduces a further contingent reason
whose obtaining remains owed an account under the same norm. An endless
sequence of these local answers does not, *on Leibniz's stated view*, finish
the original why-question. Its length alone is not the defect; the alleged
unresolved explanatory dependence is. The burden is therefore to defend the
whole-sequence demand and why no admissible global or non-well-founded account
can satisfy it, rather than to point at infinity or assume that all adequate
explanation has a finite proof tree.

### What is already checked, and what remains a philosophical premise

| Existing certificate | What it settles | What it leaves open |
| --- | --- | --- |
| `TruthCore.Results.Causality.UniqueFeedback.controls` | Nonconstant global equations can have a unique consistent solution without observed boundary data. | Why these equations obtain; whether their structural fact is an intrinsic sufficient explanation. |
| `TruthCore.Results.Modal.HistoryContrastive.controls` | The same infinite memberwise causal/explanatory labels admit a necessary nondiscriminator or a contingent internal discriminator. | Whether discrimination is required or sufficient; whether the internal marker explains its own obtaining. |
| `TruthCore.Causality.BruteFoundationExplanations.necessaryReasonAndNecessitation` | A necessary reason plus explicit necessitation makes the specified individual's existence necessary. | Whether adequate explanation necessitates; why the full reason is necessary; independent sufficiency of a proposed necessary ground. |
| `TruthCore.Logic.Regress.Graph.grounded_eq_lfp` and `TruthCore.Results.Logic.RegressSchema.regressSchemaPackage` | Inductive finite grounding is the least fixed point, distinct from a source-free all-on successor assignment in the greatest fixed point. | Why actual power, epistemic warrant or complete explanation must meet that inductive norm. |

None needs to be reproved here. In particular, the Boolean uniqueness control
is not a counterexample to the *source's whole-series PSR*: it contains no
adequacy interpretation. Conversely it prevents dismissing a global-structure
reply merely because local copying equations can have multiple solutions.
The history discriminator is a separate minimal test, not the answer to the
stronger question of why its own contingent premises obtain.

### Strongest replacement accounts face the same question

These are explicit rival answer profiles, not new historical attributions or
certificates of metaphysical possibility.

| Account | Positive answer offered | Commitment it rejects or must defend |
| --- | --- | --- |
| Leibnizian final reason | The contingent order has a sufficient reason outside that order, in a proposed necessary being with an intrinsic reason. | Defend unrestricted/whole-series scope, the deferment-to-externality step, actual instantiation and intrinsic sufficiency. Necessity alone does not discharge these. |
| Memberwise sufficiency | An account of each member and its relations accounts for the series; there is no additional obtaining fact left over just by collecting the members. | Defend that sufficiency and the treatment of totality. The reply challenges the independent whole-series explanandum, not simply the existence of a first event. |
| Intrinsic global structure | The actual laws/whole constraints explain their jointly determined state, rather than one member originating it. | Explain or justify primitiveness of the constraints' obtaining, or defend an intrinsic account of that obtaining. A unique solution relative to supplied constraints establishes neither adequacy nor its absence. |
| Non-well-founded explanation | A whole pattern of explanatory dependence can be adequate without an inductive terminus. | Give a non-question-begging adequacy criterion and address vicious circularity/deferral. An infinite graph or local label assignment alone does not establish this reply. |
| Brute global fact | The complete obtaining contingent structure is a primitive fact, not an unexplained gap within a claimed total PSR account. | Reject or restrict the PSR openly. This leaves the why-question unanswered on the PSR standard; it does not become logically inconsistent merely for declining that demand. |

The first account is held to the same standard: calling a ground necessary,
self-existent or divine does not by itself show why its nature is instantiated
or why its intrinsic reason is sufficient. §45 proposes such an answer; it is
not established by the notation `NecessaryAt` or by the source's assertion.
Likewise, an epistemic foundationalist may defend noninferential warrant, an
infinitist available reasons, or a coherentist a holistic criterion. Their
justificatory standards must not be imported into ontic causation without an
independently defended cross-domain bridge.

### Exact open obligations and premise comparison

- **EXP-SCOPE:** defend why the contingent sequence's obtaining is a live
  explanandum beyond the supplied local facts, and which PSR applies to it.
- **EXP-LOCAL-TO-GLOBAL:** decide whether memberwise explanation, together with
  explicit totality/closure principles, answers that question. Neither a
  predecessor count nor a copied value is a sufficient argument.
- **EXP-NONCIRCULAR / EXP-ULTIMATE:** defend the exclusion of a global intrinsic
  or non-well-founded final reason rather than build externality into the word
  explanation. §37 takes the outside-the-series step; the rival can contest it.
- **Intrinsic adequacy and actuality:** establish the proposed necessary
  ground and its reason, without turning necessary status into an existence
  proof or an exception to the universal demand.
- **ACT-GROUND and temporal scope:** remain separate. Explanatory
  insufficiency does not itself show that a source-free causal system cannot
  act, and neither result would by itself forbid an unbounded temporal past.

Intended and actual root-path change: none. All 63 counted open premises and
the eight route costs are retained; no argument/result or root connection is
added. The five source readings are prose-only and do not certify the norms
they report. The dossier-linked attempt and the
`CONTINGENT-SERIES-EXPLANATION-ADEQUACY` candidate preserve the unresolved
burden. The next decisive task is an argument for or against that norm on a
shared global-structure case, rather than another solution-counting example.

## Positive infinitist account: common explanation and its exact limit

### Witness and reading boundary

The positive rival is now supported by an accessible primary argument:
Evan Welchance, *Metaphysical Infinitism and Theoretical Virtue*,
*Erkenntnis* (2026), DOI [10.1007/s10670-026-01084-1](https://doi.org/10.1007/s10670-026-01084-1).
`WELCHANCE-INFINITISM-1-3` pins the official CC BY 4.0 publisher PDF,
selected physical pp.1–18 (§§1–2.4 through p.18). The complete
21-page PDF was read for conclusion and context; the selected argument
range was materialized and read. The source's argument is defeasible philosophical
reasoning; no Lean theorem or new root commitment is advertised.

The Bohn candidate's title was inaccurate. Publisher metadata identifies
*Indefinitely Descending Ground*, pp.167–181, DOI
[10.1093/oso/9780198755630.003.0009](https://doi.org/10.1093/oso/9780198755630.003.0009).
PhilArchive identifies an author manuscript at `https://philarchive.org/archive/BOHIDG`,
but direct and versioned fetches returned HTTP 403. The author's University
of Agder page links the institutional record `https://hdl.handle.net/11250/4022949`,
whose NVA landing page was inaccessible to the browsing tool. These are
promising witness locators, not a reading. No Bohn view is attributed from
its abstract, another author's quotation, or a paywall. The source ID is
retained; the chapter remains unread and has no pinned passage here.

### The positive argument actually read

Welchance's §1.1 means facts obtaining in virtue of other facts, illustrated
by Socrates and his singleton. §§1.2–1.3 impose a shared question about
existence, including fundamentalia. A brute or unexplained foundation does
not lose every explanatory use; by parity, neither must an unexplained
chain. This defends local explanatory value without claiming to explain
the whole chain. §2.1 grants foundationalism's virtue of a relatively small
common explanatory base. §§2.2–2.3 offer a rival virtue: one underlying
explanatory theory applies throughout concrete existence. The motivation is
a defeasible preference for explaining instances of one phenomenon alike,
illustrated through vagueness. §2.4 considers uniform identity-based and
different-kinds-of-existence replies, arguing that each has costs. The
conclusion is parity on these considerations, expressly not infinitism's
truth or overall superiority. §1.3 n.15 mentions explaining explanatory
links through further prior facts but leaves that strategy undeveloped.

### Five-question audit and independent appraisal

The following is repository analysis of that proposal, not an attribution of
additional theses to Welchance.

1. **Ordinary meaning.** An in-virtue-of answer specifies what makes a fact
   obtain, rather than who first produced a thing or what a person must know.
   That is a plausible target of ontological explanation, but it covers more
   than efficient causation. Its relata here are obtaining facts, including
   basic existence facts about particular objects. An interpretation in terms
   of beings themselves needs a defended translation, not a silent change of
   the variable type.
2. **Examples and granularity.** Socrates's existence and his singleton make
   the proposed direction intelligible; they do not establish an actual
   endless concrete chain. Wood/atom/chair examples suggest constitution,
   but the existence of atoms alone plainly omits arrangement and relevant
   composition conditions. The source's §2.4 explicitly distinguishes an
   existential claim from basic existence claims and instance facts. An
   adequate reconstruction therefore preserves plural/full explanatory
   grounds. A binary edge from one contributing fact need not itself be a
   sufficient explanation. One must not replace joint sufficiency with the
   assertion that every fact has one predecessor.
3. **Exclusions.** Temporal ancestry, persistence after production, efficient
   action, logical entailment, covariance, beliefs supported by further
   beliefs, and a consistent graph are not automatically instances of the
   proposed relation. Ordinary constitution cases do not identify it with
   direct present-esse conservation `R`. No epistemic infinitism is doing
   ontological work here.
4. **Why structural properties?** Constitutive priority and the singleton
   example motivate direction in those cases. They do not by themselves
   establish universal asymmetry, transitivity, or well-foundedness. The
   positive infinitist motivation is continuity of explanatory practice:
   changing level need not change what it is to explain an existence fact.
   If that motivation is sound, indefinitely many adequate local explanations
   need no special originating explanation merely to count as local answers.
   This is a reason to resist an automatic termination requirement, not a
   demonstration that every local chain is adequate. The foundationalist can
   answer that a genuine distinction between derivative and intrinsic
   existence justifies differing explanations. That reply must defend the
   distinction and the intrinsic answer; the infinitist must defend treating
   the relevant existence facts as one explanatory kind. Neither side earns
   its preferred relation property through notation.
5. **Abstraction.** A formal comparison would need explicit existence facts,
   plural full grounds and any conditions under which explaining members
   explains a totality. It must distinguish immediate explanation from its
   ancestral closure, and fact grounding from efficient conservation. No
   finite inductive generator is proposed as the definition of actual
   explanation. The already certified PLG non-well-foundedness example
   settles a logical-rule boundary only; its uninterpreted atoms do not
   supply this missing interpretation.

### Strongest objection and the consequential fork

The ground-floor objection deserves its strongest form: each local explanation
may depend on obtaining facts whose explanatory efficacy is itself borrowed.
If every explanation merely passes on that same unpaid obligation, why does
the chain explain any actual existence rather than characterize a possible
pattern of dependence? Supplying infinitely many labels, or unique solutions
to given constraints, would not answer that objection.

The rival's positive answer has two parts. Local explanation may be
constitutive determination rather than transmission of an explanatory
quantity that must first be deposited somewhere. Uniformity then supports
continuing the same explanatory practice without a privileged level.
Furthermore, an unexplained explanation-base is not generally inert: a
foundationalist who permits a brute basic entity to explain derivatives
must give a relevant reason why a brute globally structured chain cannot
explain its members. These are substantial reasons, conditional on genuine
local sufficiency and the proposed symmetry of explanatory burdens. They
are not merely an assertion that infinity is consistent.

The strongest foundationalist response rejects that symmetry: the required
intrinsic sufficient reason is independently defended, whereas the chain's
whole obtaining remains unanswered. A demonstrated intrinsic answer would
therefore defeat this parity argument; simply naming a necessary object
would not. Conversely, even a successful parity argument would show that
neither *bare* foundation nor *bare* chain finishes the total inquiry. Equal
unanswered questions do not become answered questions.

This gives a discriminating fork rather than a new mathematical fixture:

- With a memberwise explanatory aim, genuine full local grounds plus the
  uniformity reason provide a positive infinitist account. Its actuality,
  local adequacy and relation interpretation remain to be defended.
- With a whole-series/existence PSR, the present infinitist proposal leaves
  the totality question open or admits a brute totality. It does not discharge
  `EXP-SCOPE`, `EXP-LOCAL-TO-GLOBAL`, `EXP-NONCIRCULAR` or `EXP-ULTIMATE`.
  Extending upward explanation of grounding links is a further proposal,
  not an already supplied totality explanation.
- With direct existential conservation as the target, neither memberwise
  fact explanation nor explanatory uniformity establishes an `R` instance,
  an independent sustainer, or its absence. The relation bridge remains OPEN;
  see the five-question audit in `docs/power-existence-scope-boundary.md`.

The positive account therefore challenges the claim that foundationalism
wins merely by possessing a base, and supplies a concrete reason for
preferring explanatory continuity. It does not refute independently
supported causal-finitism/patchwork premises; their joint-realizability
argument must be assessed on its own relation and background assumptions
(`docs/notes/causal-finitism-367.md`). Nor does it show that all-branch
well-foundedness is the weakest needed condition: an adequate intrinsic
full explanation could matter more than the shape of every ancillary
partial-ground path. No implication between those requirements is added.

Intended and actual root-premise delta: zero. No premise is added, removed
or discharged, and no graph/result/type changes. Rejected interpretations:
Bohn's abstract as a read chapter; uniform explanation as total PSR success;
parity as proof of actual infinitism; a binary partial edge as a full ground;
fact explanation as efficient present-esse support. The next decisive
comparison is an independently defended intrinsic existence explanation
against this explicit uniformity/parity case, holding the explanandum fixed.
The companion intrinsic-nature analysis in `docs/psr-scope-countermodels.md`
now assesses that positive reply and its individual-actuality burden; it
does not declare the intrinsic account or this rival discharged.

### Finite access, the reason for the order, and comparative economy

The owner's further objections sharpen three separate demands. These are
argument candidates and appraisal, not new source attributions or established
premises. The existing [epistemic infinitism analysis](infinitist-justification-adequacy.md),
especially its Klein–Turri §§4a–b reading, already distinguishes available
reasons from an actually completed infinite performance. That reply is reused,
not counted as a new finding.

**Can a finite thinker ever progress?** If justification of the first claim
requires first completing verification of every later reason, an endless
chain cannot meet that condition through successive finite inquiry. That is
a strong objection to that particular completion requirement. The infinitist
must defend a different adequate epistemic status: finite inquiry can answer
particular challenges or improve support without finishing the whole chain.
Calling those steps progress still requires a truth-conducive reasonhood norm,
not mere accumulation of further assertions. A finite schema can make further
steps intelligible, but neither a schema nor arbitrarily many individually
possible responses establishes one actually suitable available chain.

Ontic determination is a different target. The facts that constitute a chair
are not required to await a thinker's inspection in order to obtain. Finite
cognitive limitations therefore do not by themselves exclude infinite ontic
dependence. Conversely, calling dependence ontic does not entitle a finite
thinker to claim knowledge that it adequately explains the chair. The rival
owes accessible warrant for the proposed dependence account and its scope,
while a totality explanation remains owed if that is the common demand.
There is no inference from human inability to traverse a chain to the chain's
nonexistence, or from the chain's obtaining to human access to its explanation.

**Any rule can be questioned; why this order?** A request for justification
is not itself a refutation. If every answer were rejected solely because a
further question is grammatically possible, the same veto would apply to a
finite foundation and to the vetoing rule. The substantive challenge is whether
the rule and its application are independently warranted or merely borrow
all their force from the very order they purport to vindicate. A general
rule must discriminate correct from incorrect applications; repeating it
at another level does not supply that discrimination. This burden applies
also to an asserted noninferential warrant or intrinsic existence reason.

For ontic explanation, an order is not merely the order of enumeration,
a causal chronology, or an arbitrary chosen relation. Even necessary
co-obtaining or mutual entailment does not select a direction of explanation.
The account must say which facts make which others obtain, why those full
grounds are sufficient, and why reversal changes the relevant constitutive
or essential dependence. If a contribution is only a partial ground, the
rest of the joint ground and its arrangement cannot be hidden inside a
binary arrow. The source's §1.3 n.15 proposes further explanation of the
explanatory links but does not develop a vindication of this whole order.
So the new open demand is precise: defend the obtaining and direction of
these constitutive links and their governing rule, not just explain each
member given that rule. Merely redescribing an unexplained order with a
short recursive clause would relocate this demand.

A constitutive or essence-based reason for the direction could answer a
local order question without tracing an infinite history. That is a possible
shape of answer, not an independently established reason in this batch.
For present-esse support, it would additionally need the conservation
interpretation defended above; a fact-grounding answer cannot substitute
for it. For epistemic rules, the corresponding obligation concerns warrant
and truth-conduciveness, not ontic constitution. The two demands must not
be merged because both use the word “because.”

**Is an infinite regress infinitely less economical?** The strongest
parsimony argument is conditional: for the *same* explanandum and adequacy
standard, if a finite account explains at least as much with fewer gratuitous
independent commitments, prefer it other things equal. A regress that adds
independent unexplained entities or merely relocates an unexplained ordering
rule has a real cost. Infinitism does not answer that criticism by announcing
that all its members depend on something else.

The comparison nevertheless needs an explicit inventory. Number of entities,
number of kinds or laws, number of independently unexplained commitments,
and length of a generating specification measure different things. A finite
base may explain infinitely many dependent entities; a uniform infinite
chain need not introduce an independent assumption for every member.
Equally, a short specification may describe infinitely many things without
explaining why any of them or that ordering rule obtains. Compression alone
establishes neither explanatory adequacy nor an infinitist advantage.

Welchance's already-read §2 comparison concerns precisely competing kinds
of unity: a relatively small common base and a common explanatory theory.
Our appraisal does not convert their alleged parity into a general result
about economy. A finite proposal must supply its base, the relevant
production/constitution principles and the reason they obtain; an infinite
proposal must supply its local full grounds, their direction/order and the
status of the totality. Count any independent brute commitments on both
sides, retain differences in what each explains, and only then apply the
conditional preference. Neither “infinitely many members” nor “one source”
alone settles that comparison.

The material delta is thus a sharper open ordering/rule obligation and an
explicit conditional parsimony test. The finite-mind availability answer
was already covered in #669; it is not repackaged as new support. No new
independent defense of infinitism, causal conservation or an intrinsic
foundation is supplied here. Root-premise change remains zero.

### Witness extraction repair

The initial full pp.1–21 selection passed locally but failed CI40782499547
on its extracted-text hash, with the full-PDF bytes unchanged
(`1f98353914c8e4650660d0bdd84549912ed4b0ec76a318877be72dbd7f6c8f9f`).
A bounded comparison used local Poppler26.01.0 and Ubuntu:noble
Poppler24.02.0, matching CI's extraction. The sole normalized difference
was the arrangement of zero-width characters in the CC-license URL on
physical p.19; no philosophical text differed. Restricting the materialized
selection to pp.1–18 avoids that extractor-sensitive footer while retaining
the positive and critical arguments at issue. The full-PDF raw hash remains
pinned, and its conclusion, license and references remain consulted context,
not an additional selected passage. The historical passage ID is retained.
No extraction normalization, integrity gate or repository dependency changed.
The publisher HTML was considered but rejected because repeated fetches
changed raw bytes; it was not substituted as a stable witness.
