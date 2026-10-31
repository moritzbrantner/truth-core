# Testing standards of ultimate explanatory adequacy (#750)

Outcome: a **failed discriminator with a certified incompatible core**, not a defended
standard. The theorems are `core` and `comparison` in
`TruthCore.Results.Explanation.ExplanatoryAdequacy.Solution`, over
`TruthCore.Explanation.ExplanatoryAdequacy` and the #755 `Arena`. `core` is zero-axiom;
`comparison` permits the Mathlib three because it consumes #735's `plural_no_least`.
They establish conditional consequence and model verdicts. They establish no standard
and no model's metaphysical possibility. No new source claim is added.

## Findings

1. **A truth-discriminating contrast demand excludes well-founded accounts of contingent
   facts.** Reason closure, a contingent explanandum, a well-founded contingent reason
   relation and contrast relevance are jointly inconsistent. A true reason false at a
   rival world is contingent, so it renews the demand. This is not an argument for a
   necessary ground: contrast relevance has no account of the target in `ground`, `plural`
   or `law`, and it holds on `chain`.
2. **A weaker closure standard cannot tell a ground from a token.** Reason closure
   admits a necessary being's nonnecessitating reason, and it admits the same reasons
   with no necessary being at all (`law`). Those two arenas have one projection without
   beings. A fact true everywhere, added as sole reason, gives any truth of any arena a
   reason-closed account (`tokenExpand`), including the brute model.
3. **Excluding the brute terminus is stipulated, not derived.** Reason closure rejects
   `brute` because its clause `covered` says contingent members have reasons. That is
   the disputed point restated, so it cannot serve as an argument against that rival.
4. **The necessary-being stop is circular, and says so.** `BeingStop` names its expected
   satisfier. With closure, foundedness and a contingent explanandum it excludes that no
   being is necessary, because it stated that. Without foundedness `chain` meets it
   vacuously, and `law` fails it while having the same reasons as `ground`.

The non-theistic witnesses are `law`, `chain` and `necessitarian`. The first two have no
necessary being at all. So reason closure does not presuppose a necessary being, and
`idle` shows a necessary being does not suffice for it.

**An open premise.** A standard that keeps a nonnecessitating ground and excludes a
token must read something beyond truth, admitted reasons and accessibility, because
`ground` and `law` agree on all of these. What is missing is an independently defended
account of how a reason true at both a world and its rival is relevant to which outcome
obtains. Nothing here supplies it, for a divine, impersonal or lawlike ground alike.

## The incompatible core

Fix an arena, a world and an account `S` of `x`. `core` refutes the bundle below, and also
its variants replacing the last member by all reasons necessitating, or by
`ContrastRelevant`. Deletion models are certified for the first bundle only, so the first
bundle is inclusion-minimal. That is not minimum cardinality. The core forces rejection
of at least one member and does not choose one.

| Deleted member | Model | Surviving position |
| --- | --- | --- |
| `ReasonClosed` | `brute` | A contingent terminus with no reason |
| `Founded` | `chain` | A source-free infinite chain of contingent facts |
| `AllReasonsVary` | `ground` | A necessary reason for a contingent target |
| `Contingent` target | `necessitarian` | The target has no rival |

This is a contradiction among commitments, not a proof that these four positions exhaust
reality, and rejecting `ReasonClosed` is available as in `brute`.

## Verdicts on one target

All rivals share worlds `Nat`, actual world `0`, universal accessibility, the fact
signature `Fact` and `Fact.target`. "None" means no account containing the target meets
the standard in that model, except in the `ReasonClosed` column, whose clause already
requires the target.

| Rival | `ReasonClosed` | `ContrastRelevant` | `TwoWay` | `BeingStop` |
| --- | --- | --- | --- | --- |
| `ground`: one necessary being | met | none | met | met |
| `plural`: two necessary beings | met | none | met | met |
| `law`: necessary fact, no necessary being | met | none | met | fails for every closed account |
| `chain`: infinite contingent history | met | met | none | met vacuously, without the whole |
| `necessitarian`: no rival to the target | met | met vacuously | met vacuously | not tested |
| `brute`: contingent terminus | none | none | none | not tested |
| `idle`: necessary being, no reasons | none | none | none | not tested |

`UniformContrast`, one reason excluding all rivals of a member, holds on `chain` without
the whole. With the whole, `ContrastRelevant` holds, each rival being excluded by some
member, and `UniformContrast` fails. So per-rival contrast does not reach the whole as one
answer, while it is met member by member. Whether the whole needs one answer is not
settled by either standard.

`law` may be read as a necessary law or as a bare token. Formally there is one arena. The
signature has no personal-agency predicate, so `ground` covers a necessary personal ground
and a necessary impersonal ground alike, and no theorem separates them.

On the #735 overlays the same graph changes verdict with the modal table. Under the
all-necessary overlay target2 has a reason-closed account in all four graphs, including
`chain`, which has no joint Supply of target2. Under the other overlay `single` and
`plural` have one, and `branch` and `chain` have none. That last failure comes from
`nonCopy`: that overlay has two worlds, so the contingent contributors are coextensive with
target2. The `chain` rival above shows infinite descent itself does not fail reason
closure, so this is a limit of the two-world overlay and no verdict on infinite branches.
Plural keeps #735's Supply with no least node.

## The candidates of #750

**Contrast relevance.** Ordinary meaning: an answer to "why this rather than otherwise?"
bears on that alternative. Example: an overload explains why the fuse blew rather than
held, and the overload is absent in the rival case. Near misses: a stochastic setup or a
free agent's motive can be the same in both cases, and on many accounts still explains.
`ContrastRelevant` takes the strict reading, so it refuses those cases where the same
reason holds at the rival. That is why it cannot serve as a general norm without a defense
of that refusal. `TwoWay` takes the weaker reading and is met by tokens given a rival outcome.
Probabilistic favoring has no formal test here.

**Nonvacuity.** `nonCopy` excludes a reason coextensive with its target, the #712 copy and
the #755 `ReasonIndependent` limit. It is cheap: a true-everywhere token passes. Compare
#677, whose token expansion is on #312 models; `tokenExpand` is a separate construction on
arenas and is not derived from it.

**Indispensable-condition closure.** `closed` makes every admitted reason part of the
account, so an account cannot invoke an unaddressed condition. This is bookkeeping for the
word "complete". It over-counts when an arena admits a redundant reason, and it assumes the
arena lists the account's own reasons. Ordinary scientific explanation is not held to
this closure: the demand is confined to accounts offered as ultimate.

**Symmetry and stopping.** The standards `ReasonClosed`, `ContrastRelevant` and `TwoWay`
are equivalent on an arena and its `bare` projection, so they cannot read which being is
offered. Their verdicts still vary with the modal table, and necessity of a fact carries
the stopping force in `ReasonClosed`. That is a preference for noncontingent stops stated
in `covered`, not a result.

## The relation and structural properties

`explains` is #755's parameter, with its meaning, examples and rival accounts in
`docs/notes/psr-strength-755.md`. No transitivity or asymmetry is assumed. `Founded` is the
only structural condition added, as a member of the core and never as a standing law.
Well-foundedness of explanation is what `chain` denies and is not defended here. Causes is
empty in the shared rivals, so no causal claim is made; in `overlay` reasons are #735's
actual graph edges, read as admitted reasons by stipulation.

The theorems generalize nothing from ordinary explanation to metaphysics. The fuse example
motivates the form of a contrast question and does not show ultimate facts have answers.

## Sources read

Materialized and read for this work, with no new claim. Each reading is context, not a
premise.

- `LEIBNIZ-MONADOLOGY-31-45`, Latta translation. §32 asks a reason "why it should be so and
  not otherwise". §§36–37 hold that further contingent detail renews the demand, and §38
  places the final reason in a necessary substance; existing claims
  `LEIBNIZ-32-FACT-REASON-DEMAND` and `LEIBNIZ-36-37-CONTINGENT-DETAIL-DEFERMENT` record
  these. The core sharpens the tension for the strict formal reading only. It does not
  show Leibniz's own "reason" is truth-discriminating, and his §45 intrinsic reason is not
  formalized here.
- `OPPY-UNIVERSE-NO-CAUSE-13-22`. In §VI's regress case with some necessity, histories
  diverge "only because chances play out differently", a nonnecessitating natural rival.
  At §VII, p.21, ontological necessities are "theoretical rock bottom", primitives on either side.
  `OPPY-2020-NECESSITY-COMPARATIVE-COST` records the restricted comparison.

Both directions remain disputed: Leibniz's renewal argument motivates `covered`, and Oppy's
primitive stopping point resists any claim that a necessary stop explains more. Neither
source defends a formal standard above.

## Rejected and open

Rejected: defining adequacy by a necessary-being stop, as circular; treating `nonCopy` as
relevance, since tokens pass; treating contrast relevance as the general norm, since it
refuses a reason that holds at the rival and, with closure and a contingent explanandum,
every well-founded account; treating `TwoWay` as
sufficient, since tokens pass given a rival outcome.

Open: the relevance premise above; whether `covered` is defensible against a brute stop;
whether explanation is well-founded; a difference-making reading (a reason whose absence
removes the target) has no certified model here; probabilistic favoring; whether the whole
requires one answer. #735 retains integration authority.

## Premise effects

Intended and actual root delta: none. Both results have no premises and neither lies on a
root route. No configuration changes status.

## Positive fact extraction and the concrete-being boundary (#786/#545)

The bounded composition `NECESSARY-FACT-BOUNDARY` has the following brief:

- **Target:** make the fact-level output of reason closure and foundedness
  positive, while retaining the distinction from necessary concrete existence.
- **Reuse:** `ExplanatoryAdequacy.forced`, `core_necessitate`, `law_closed`,
  `ground_founded` and the exact existing `law` interpretation. No new reason,
  world, fact, bearer or ground relation is introduced.
- **Missing step:** explicit excluded-middle witness extraction and a joint
  certificate showing all explanatory backgrounds with no necessary bearer.
- **Premise comparison:** no root premise change or discharge. All internal
  philosophical backgrounds remain conditional; no new claim about an author.

For a fixed arena `A`, standpoint `a`, account `S` and target `x`, the new
conditional is:

```
ExcludedMiddle → ReasonClosed A a S x → Contingent A a x → Founded A a S →
  NecessaryReasonForMember A a S ∧ ¬ AllReasonsNecessitate A a S
```

The positive conclusion is exactly:

```
∃ r, S r ∧ A.holds a r ∧ (∀ v, Access A a v → A.holds v r) ∧
  ∃ c, S c ∧ Contingent A a c ∧ A.explains a r c
```

This is stronger than merely reporting an incompatible bundle with all reasons
contingent: it extracts an actual member and preserves that member's role as an
admitted reason. It does **not** say that `r` directly explains `x`, that `r`
is autonomous or ungrounded, that it is one individual's existence fact, or
that it produces anything. No ancestry path back to `x` is advertised.
Necessity is relative to the same accessibility relation; actual truth is
stated separately, so reflexivity is not smuggled in.

The proof uses the already proved `forced` descent lemma. At a contingent
member with no contingent predecessor, coverage gives an admitted reason,
closure puts it in the account, and truthfulness supplies its actual truth.
Under explicit excluded middle, its noncontingency gives truth at every
accessible world. A second excluded-middle split selects the positive
existential. The modal cost is the imported `core_necessitate`; a necessary
reason cannot necessitate a contingent member. No argument here shows excluded
middle to be logically minimal. The full `ReasonClosed` record is reused,
although this extraction does not use its `nonCopy` field; no weakest-premise
or independently defended adequacy claim is made.

`lawControl` uses the literal #750 `law`, with the same `OneSource` account,
world `0`, fact `.target`, truth assignments, reason assignments and `Unit`
bearer carrier. It jointly satisfies reason closure, target contingency,
contingent-reason foundedness and the positive necessary-fact conclusion.
The witness is `.source true`, not an extra bearer. At accessible world `1`
the only bearer is absent, so **no** bearer is necessary at `0`. The inherited
cause relation is empty. This is a countermodel to a bare promotion from the
fact-level conclusion to a necessary individual, not a metaphysical possibility
claim, an adequate real law explanation, or an abstract cause of concrete
existence. No concrete predicate appears in this arena: in particular the
certificate does not supply concrete existential support.

The existing `brute` and `chain` deletion controls continue to guard the
coverage and foundedness assumptions. No new independent omission certificate
or exhaustive metaphysical partition is claimed. Nor is this a formalization of
Pearce's entire argument: autonomous facts, circumstances and sufficient
concrete support would require their own sourced interpretation and interfaces.
The new statement packages a universal conditional and its matched control;
its empty outer argument-premise list does not establish its internal premises.

Development uses the existing pinned Lean toolchain and CLI fallback: no local
service/preview was running when inspected. A focused build of the imported
ExplanatoryAdequacy solution is in progress; the new Challenge was frozen before
its Solution. No verification claim is made before the new result passes its
build, binding and Comparator/NanoDa gates. No original Challenge is edited.
