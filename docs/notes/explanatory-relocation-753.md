# Explanatory relocation: temporal paths still leave a question about the whole (#753)

This note reads "moving from world to world" as a **temporal path of states**
inside one history, not causal travel among complete worlds. It asks whether
explaining each transition explains why the complete actual path obtains. The
outcome is a precise failed lift with a surviving rival. It does not refute an
infinite regress, prove a first step or discharge a root premise.

## The result in one paragraph

On bi-infinite time, three properties of a condition on complete paths cannot
hold together: it is preserved by re-dating, it has a unique solution, and that
solution changes. This covers global constraints, not only recurrences. So a
beginningless history that changes is not uniquely fixed, as a dated path, by
any date-blind condition. To select it you need a date-sensitive input or you
must give up the dated contrast. Dropping the dated contrast is a real option:
the flip law selects a changing beginningless path up to dating. But then the
contrast has moved to which law holds, because every never-repeating path has
its own undated law. No formal step here says why any law applies.

## Semantic profile

- **Profile.** `TemporalHistory.History` over `pathHistory C`: worlds are the
  solutions of `C`, all mutually accessible; one state present per time; `now=0`;
  `Causes` empty. `SameEvidence`, `Determines`, `EvidenceOnly` and `Selects` are
  reused unchanged from #736.
- **Model population.** The general clauses range over all state and reason
  types. Fixtures use Bool states and Int time (or a `Fin` window).
- **Omitted.** No chance law, intrinsic nature, plural enabling structure,
  adequate-explanation predicate, causal or grounding relation, or real modality
  is encoded. No first time is assumed or denied in general.

## What is certified

`PATH-RELOCATION-CERTIFICATE` and `PATH-RELOCATION-CONTROLS`, bound to
`TruthCore.Results.Explanation.PathRelocation.certificate` and `.controls`.

| Test from #753 | Checked finding | Exact limit |
| --- | --- | --- |
| Local to whole, law held fixed | World-invariant reason truth determines the history iff the condition has no other solution. | A lift criterion for this vector only. |
| Bi-infinite with autonomous law | A unique solution cannot change. A periodic law passes each period to its unique solution. | About uniqueness of a condition, not about whether histories change. |
| Strongest global rival (#738) | `GlobalLaw` is shift-invariant, so `fixedSignal`'s stationarity is forced by the theorem. | Applicability of the constraint stays OPEN. |
| Whole vector, any size (#736) | A changing solution is undetermined by any vector agreeing with its re-dating; determination forces a reason that varies under re-dating. | Entailing standard only; covers reasons that are necessary, since those are world-invariant. |
| Local token reasons | Tokens agree exactly when histories do; every evidence-only selector is coextensive with the target. | Success here is re-encoding of the informational content. It does not rule out explanatory direction. |
| Replacing a chain by a law | Copy laws and graph laws are exact in the theorem's scope: laws equal iff paths equal (dated), or iff agree up to dating (injective paths). | The family is unrestricted. A restricted family can exclude: functional undated laws exclude `revisit`. |
| Finite path and boundary | Functional law: solutions biject with start states. A one-edge relation on a two-point window uniquely selects a changing path, which the bi-infinite theorem forbids. | The contrast moves to the start state, or to which relation holds. |
| Branching | Solutions sharing a state splice. Under `rise`, tokens before time 0 do not determine. All tokens do. | No claim that reality branches. |
| Temporal, modal, state relations | `flip` has a state 2-cycle and mutually accessible worlds; dated occurrences have no cycle and every one has a predecessor. | A state-type cycle is not an actual-occurrence cycle. No bridge between the relations is supplied. |

**Incompatible core with deletions.** {`ShiftInvariant C`, `UniqueSolution C f`,
`Changes f`} is inconsistent. Deleting each member is witnessed: uniqueness by
`flip`, invariance by `pinned`, change by `allTrue`. This is inclusion-minimal
for this bundle, in this semantics, at the level of those three properties. It
forces rejecting at least one member; it does not say which.

## Surviving branches for a changing beginningless history

Nothing below is excluded by the theorems. The list is not a certified
partition of all metaphysical positions.

1. **Decline the dated contrast.** Leibniz III §6 argues that instants without
   things are nothing and a supposed anticipation would not differ from the
   actual state (`LEIBNIZ-III-6-TEMPORAL-REASON`). On that profile the shift rival
   is no rival, and `flip` selects its path up to dating. Remaining burden: why
   this law, given that graph laws make the choice of undated law track the choice
   of never-repeating path.
2. **Keep the dated contrast and supply a date-sensitive input.** A pin, a dated
   law or a token vector. Clarke III §4 objects that the order view would make a
   world created sooner not sooner at all, and says at §6 that the same reasoning
   applies as for space (`CLARKE-III-4-6-TEMPORAL-REPLY`); his volitional reply on
   indifferent alternatives is the existing `CLARKE-III-2-5-8-VOLITIONAL-REASON`.
   A date-sensitive will is not modelled here. Remaining burden: the input's own
   status, including whether it is more than a copy.
3. **Accept stationarity.** Unique and date-blind, but no change in the state
   vocabulary. The burden moves to reconciling this with observed change, or to
   locating change outside the encoded states.
4. **Decline entailing selection.** A chance or causal account may leave a rival
   standing (#736's positive weights, the `rise` branching control). The theorem
   does not refute this. Whether it answers why this path obtains is open.
5. **Brute whole.** Accept the path with no selector. Consistent, at the price of
   limiting total explanatory ambition.

**Necessary-being route.** A necessary ground with a date-blind law gets no
exemption: it falls under the same core. Under the entailing standard it selects
a dated changing path only with a date-sensitive input, or an undated one up to
dating with the law's burden remaining. This is a constraint on that route, not
evidence for or against it. An intrinsically sufficient infinite whole faces the
same three branches, and its intrinsic property is date-blind or it is not.

## Where the burden moves

Same explanandum: why this complete path rather than a rival?

| Account | Burden moves to |
| --- | --- |
| Finite boundary condition | The start state (bijection theorem), or the relation with its ends. |
| Brute actual condition | Nowhere. It stops, and the limit on explanation is explicit. |
| Plural enabling causes | Not modelled here. #747 and #754 show joint supply and least foundations come apart; unity and applicability stay open. |
| Infinite derivative dependence | The law or the token vector. See branches 1 and 2. #754's rooted branch still lacks target supply. |
| Global structure | The class of admitted structures, and why one applies. |

## Semantic grounding

**Relocation** is the only relation-like notion introduced. It means replacing a
contrast between paths by a contrast between carriers (start states, tokens, laws)
that correspond exactly to them. Example: a dated schedule that lists each state
relocates "why this sequence?" to "why this schedule?". Counterexample: a restriction
to functional laws, which excludes paths and so isn't mere relocation. Differs
from grounding: exact correspondence has no direction, so it neither shows that the
carrier explains the path nor that it doesn't. Exact correspondence bears on
**informational** content only. A rival can say a law adds explanatory direction
even so; that is what the note leaves open, and it isn't established by a bijection.

**TemporalEdge** is adjacency between dated occurrences. Its asymmetry and
acyclicity come from Int order, not from an argument about causation, and it has no
well-foundedness (every occurrence has a predecessor). No generalization from
ordinary experience is used in a proof. Ordinary switch and schedule examples
motivate readings only. Serious rivals are the branches above, and the theorems
leave each standing.

## Vacuity audit

- **Unreachable worlds:** `pathHistory` access is universal among solutions.
- **Empty extension:** every world has one state at every time; `now=0` is populated.
- **Empty carrier:** a general solution type may be empty, but the failure clauses
  take a supplied `a`, and `flip` witnesses a changing solution.
- **Inconsistent background:** the failure clause's hypotheses are jointly witnessed
  by `flip` with constant truth (`Controls`), so it isn't vacuous.
- **Seriality:** universal access is reflexive, so successors exist.

## Sources and reuse

Materialized and read in full: `LEIBNIZ-CLARKE-LEIBNIZ-III-1-8` and
`LEIBNIZ-CLARKE-CLARKE-III-1-8`. Two new prose claims record III §6 and Clarke III
§§4,6. Neither is attributed the formal theorems, and neither author discusses
paths, laws or solution spaces in these passages.

Imported: `HistorySelection.no_selection`, `UniqueFeedback.controls`, `GlobalLaw`,
`fixedSignal`, `SameEvidence`, `Determines`, `EvidenceOnly`, `Selects`, `History`,
`SameHistory`. Compared but not imported: #748 `LawActuality` (time-dependent laws
that the periodicity clause does not constrain), #754 `UltimateAdequacy`,
`SPACE-TRANSLATION-BOUNDARY` (the spatial analogue with a covariance norm). #757 is
not consumed.

## Premise delta and open gaps

Root and route delta: **none**. The new records sit on no root route.

Open: whether a dated contrast is genuine; which restricted law family, if any, is
independently warranted; why any condition applies to anything; whether adequacy
may decline entailment; chance, plural enabling and intrinsic-sufficiency accounts,
which are compared here and not formalized. Next test: state a restricted law family
with an independent motivation and check which changing beginningless paths it keeps.
