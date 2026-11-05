# Carneades: retained duty and the future-ability repair

Owner direction (2026-11-05, #1035): the following is a working logical
reconstruction. Attribution remains deferred; no source acquisition or historical
intention work is required for conditional investigation. Earlier caption notes
below remain provisional research history, not certified attribution.

Read the complete English `en-orig` auto-caption recording of Carneades.org,
[The Paradox of Kant's Law (Ought Implies Can)](https://www.youtube.com/watch?v=qjNs4t4GQ2A),
5:50, on 2026-10-28. Channel metadata identifies Carneades.org, not a verified
individual speaker. This is a provisional reading: audio/slides were not checked.
No attributed corpus claim or passage manifest is created. Before attribution,
obtain a producer-pinned `media_span` export, materialize it and check decisive
wording against audio. The downloaded VTT SHA256
`9aa5616c1d78e6db0007e08032e2482d240b0c5cd33634af329d4a24b1bf4ada`
identifies consulted bytes only; it is not a verified source-span hash. Reproduce:

```sh
yt-dlp --skip-download --write-auto-subs --sub-langs en-orig \
  --sub-format vtt --write-info-json --socket-timeout 15 --retries 0 \
  --output '/tmp/carneades-deontology.%(id)s.%(ext)s' \
  'https://www.youtube.com/watch?v=qjNs4t4GQ2A'
```

## Argument read and strongest rival

- **00:18–00:41:** presents “ought implies can.” The historical label “Kant's
  law” is the narrator's; no historical Kant attribution is authenticated here.
- **00:42–01:54:** borrowed-car return is owed, yet after a crash cannot be
  performed; debt without funds is a parallel. Retaining duty plus present
  inability conflicts with the present-ability reading. The narrator favors
  retaining the duty. This is a substantive moral commitment, not established
  by the scenario's description.
- **01:54–03:32:** proposes broad logical possibility, then objects that ability
  in a richer or more powerful world does not establish this agent's ability.
  The objection limits this repair's practical meaning, not logical consistency.
- **03:38–04:24:** fulfillment in the actual future is also too strong: the
  debtor may never earn sufficient funds, while the narrator retains the duty.
- **04:27–05:26:** proposes some possible future based on the agent's decisions;
  actual choice may lead elsewhere. Acknowledges that the weakening objection
  may persist, while preferring it to unrestricted alternative-world possibility.
- **05:26–05:50:** closing series announcement; no further premise supplied.

The exact candidate is a compatibility requirement between the ideal
continuations used to interpret obligation and the choice-accessible
continuations used to interpret ability. The strongest rival retains an
obligation even when every choice-accessible fulfilling future has closed.
Against that rival, merely naming a branching-future operator supplies no
argument. Another rival rejects ideal-world semantics of actual duties entirely.
Neither rival is eliminated by a frame correspondence theorem.

## Formal result, reuse, and rejected readings

`TruthCore.Modal.DeonticFutureBoundary` reuses canonical `Modal.Frame`; no
additional modal engine or dependency is introduced. Existing
`TemporalHistory.History` separates world, being and time and is intentionally
not reused as an agency vocabulary: it models presence-at-times, not choice.
`Modal.Holds` provides the same universal/existential shape for box/diamond;
small named predicates on continuation profiles avoid inventing a second syntax.
The new `compatibility` theorem is constructive and axiom-free: for all goal
predicates, ideal-universal obligation implies available-existential fulfillment
iff some successor is both ideal and available. Forward: instantiate the goal
with ideal accessibility itself. Backward: use a common successor for any goal.
Serial ideal accessibility alone does not establish that overlap.

The certificate adds two finite controls. First, true is the only ideal
successor, false is the only feasible successor, and both are broadly possible:
obligation and broad possibility hold, but feasible fulfillment fails. Second,
when both Boolean successors are treated as available alternative continuations,
the correspondence holds, while selecting only false as the actual continuation
still fails fulfillment. These are separate relation interpretations over complete
continuation profiles, not time instants; no temporal order, transition law,
empirical agency or metaphysical realizability is inferred. The same relation
shape can serve different controls without equating their intended meanings.

Rejected: deriving actual moral duty from an ideal frame; treating broad
possibility as ability; treating some feasible fulfilling future as actual
fulfillment; treating permission as ability; inferring present ability from
future ability; attributing the analyst's semantics to Kant; identifying return
of a destroyed original object with replacement, compensation or debt repayment.
The video's move from car-return to replacement requires a distinct action
specification. Retained responsibility for causing inability is also distinct
from an unperformable present duty. No theorem decides these moral questions.

All moral axioms and their ideal-world/agency interpretation remain open. The
certificate proves a semantic constraint and controls, not the narrator's moral
premises. It connects no Catholic-case root path and discharges no existing open
premise: intended and actual root delta zero. The attempt and dossier target
`STMT-DEONTIC-FUTURE-BOUNDARY`; no new philosophical claim is used merely to log
research activity.


## Lost ability and retained duty: #1035

The question is which commitments may jointly survive when an agent loses the
ability to return a borrowed original object. `RetainedDuty.Case` keeps one fixed
agent, three dates (`before`, `after`, `later`) and three different actions
(`originalReturn`, `compensation`, `debtRepayment`). Its duty, practical ability,
actual fulfillment and retrospective responsibility fields are independent.
This is a finite analyst interpretation, not an agency theory authenticated by a
source. No axiom deriving a duty from borrowing, crashing, owing money or culpable
conduct is supplied.

The full graph is explicit. `InitialDuty s` and `Retention s` imply
`PresentDuty s` (`retentionTransfer`); `PresentDuty s`,
`PresentInability s` and `PresentOIC s` imply logical falsity (`directCore`).
`retainedCore` composes the latter proof after the former transfer. Initial duty
and retention are separate open commitments: a description of the crash does not
establish either. Present OIC is universal over the three actions at `after`,
while the duty and inability instances concern the identical original-return
action and fixed agent. The transfer itself is a single-application transcription of its explicit
policy; the incompatible cores and closed witnesses supply the constraint.
These are conditional contradictions; none
assumes the advertised falsity as a bridge premise.

The closed `controls` theorem and five registered finite interpretations witness
every single deletion. For the direct core: `noDuty` omits duty, `ableReturn`
omits inability and `crash` omits OIC. For the full core: `neverOwed` omits initial
duty, `lapse` omits retention, `ableReturn` omits inability and `crash` omits OIC.
The omitted member is also false in each interpretation. Thus both cores are
inclusion-minimal under this same interpretation; no smallest-cardinality or
exhaustive philosophical classification is claimed. `neverOwed` has no duty, so
its retention conditional and present OIC hold vacuously; this is a valid deletion
control, not a nonvacuous moral account of debt. `lapse` has an initial duty and
retrospective responsibility despite no present return duty. The finite date
and action carriers are nonempty and completely enumerated. No possible-world
population, concrete existence relation or empty individual domain is involved.

The strongest present-OIC rival cancels the now-impossible original-return duty
while retaining retrospective responsibility (`lapse`). The strongest retention
rival retains that same duty despite present and future inability (`crash`) and
therefore rejects present OIC and this future repair. These replies are not
silently equated with allowing compensation: the crash interpretation makes
compensation feasible later but supplies no compensation duty. A duty to repair
would require an explicit additional moral policy and a new action specification.
It is not recovery of ability to return a destroyed original.

The debt control retains a stipulated debt-repayment duty and lacks present
funds, yet has practical ability at `later`; actual repayment is false at every
date. Future ability therefore coexists with never fulfilling, and does not
restore present ability. The crash control has no possible later original return;
merely moving OIC into the future does not rescue every retained duty.
`futureRepair` **uses** the exact existing
`TruthCore.Modal.DeonticFutureBoundary.compatibility` theorem, requiring an
explicit duty-to-ideal interpretation together with ideal/future overlap. Its
frame carrier is dates, its goal is practical ability for the fixed action and
its available relation is the stipulated strict future. No identification of
dates with the old complete-continuation interpretation is inferred. Ideal-world
semantics itself and the claim that a date is genuinely practically feasible
remain open interpretations. `controls` also consumes the exact old
`TruthCore.Results.Modal.DeonticFutureBoundary.certificate`; the overlap
correspondence is reused, not presented as a new discovery.

The proof is constructive and zero-axiom. The moral and practical policies remain
open inputs, and no root-route premise is discharged. Intended root delta: zero;
actual root delta is supplied by the PR's computed frontier diff. This adds
conditional incompatibilities, omission witnesses and a repaired-policy boundary,
not an unconditional moral verdict or a Catholic-case conclusion.

Local-service experiment: the supplied preview at
`a2d97ecf1429e86b3e12f15b91b735f85e27822e`, session `workloop-20261105`,
returned a correctly bound response for full module content SHA256
`34fc78594b07c8b438c9e2a3c2fcb423268114744308ab38bed052f2592a5aa5`.
Its old cached `DeonticFutureBoundary.Solution` was not marked as a Lean module,
so the service rejected the import despite the latest-main source having the
module header. The canonical CLI build passed. Lease wait was 0.000047 s and
request time 1.144 s; no comparative performance claim follows from a rejected
request. Continue with the CLI for this slice; retain the service for compatible
imports and revise preview preparation before using it on module-converted
imports. No service restart, dependency change or preview rebuild was performed.


The separate frozen `BranchControls` target supplies the full possible-future
reading. `Plan` has complete `Branch.missed`/`Branch.recovery` futures; each branch
has its own dated ability and performance. Feasible and ideal sets and the actual
branch are explicit, separate inputs. `BranchAbility` existentially quantifies
later dates within one branch; `FeasibleAbility` then quantifies feasible branches.
`branchRepair` uses the imported compatibility theorem on precisely that carrier.
In `debtPlan`, recovery is ideal and feasible, actual non-recovery is also feasible,
and the repayment duty is stipulated. No actual-date repayment ability or
performance occurs, although a feasible recovery has later ability. Actual-branch
abilities agree with `current.able`; this is one joint control, not a combination
of unrelated models. No feasible branch can return the original object in that
debt-specific interpretation. The earlier date-only `FutureCan` control is
narrower and must not be presented as quantification over alternative histories.
This distinguishes actual recovery from a choice-accessible recovery without
claiming that the supplied alternatives are empirically or morally justified.


## Review repair: action-local operational cores

The review of PR #1041 correctly identified that the initial universal-OIC
formulation was stronger than the contradiction needs. Set-deletion minimality
of those cores did not minimize the strength of their OIC policy. The frozen
original Challenge and all five original theorem types remain unchanged;
`RetainedDutyLocal` supplies separately frozen weaker companions.

`LocalOIC s` means only `PresentDuty s → s.able after originalReturn`.
The new direct core consumes present duty, present inability and this local
policy. The temporal core consumes initial duty, the same retention policy,
present inability and LocalOIC, composing the existing retention transfer.
These are the operational elimination results; neither needs OIC for
compensation or debt repayment. The original universal results are preserved
as frozen predecessors, with no claim that the stronger policy is necessary.

`universalToLocal` binds the universal statement to its local sibling, and the
registered `strengthens` relation records that exact entailment. The comparison
is an instantiation transcription, not independent moral warrant. Strictness is
witnessed twice in `LocalControls`: an original-return duty and ability hold in
both controls, so local OIC is nonvacuous. One additionally owes compensation
without compensation ability; the other owes debt repayment without repayment
ability. Universal OIC fails independently in each. These are distinct action
policies, not a redefinition of original return.

The old five omission interpretations gain local-policy evaluations. They
certify every single deletion for each weaker core: noDuty/ableReturn/crash for
the direct core; neverOwed/lapse/ableReturn/crash for the temporal core. The
remaining original premise facts are imported, not reproved. No-duty vacuity
remains explicit. This establishes inclusion-minimality of the new premise sets
and a strict weakening relative to the old universal policy, not absolute
logical weakestness. The same frozen future and branching repairs are unchanged.

Premise delta: replace universal present OIC by original-return-only LocalOIC in
both operational arguments; retain all their other premises. No moral policy is
proved true, and no Catholicism root premise changes. Attribution stays deferred.
