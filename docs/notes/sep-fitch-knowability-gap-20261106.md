# SEP knowability: bounded implementation intake

Inventory base: public main `92ccf46217c8e4aa65c5235938e5411a0c8adeda`.
Analyst reconstruction; attribution deferred. No new historical/source claim,
Lean theorem, verification evidence or root-premise discharge is supplied here.

Navigation read: [SEP, Fitch’s Paradox of Knowability](https://plato.stanford.edu/entries/fitch-paradox/),
§2 proof, §§3.2–3.4 constructive limits, all of §4 semantic restrictions, and
all of §5 syntactic restrictions, including §5.3 objections. These are navigation
locators, not pinned witnesses or claims about original authors’ intentions.

## Existing work and rejected duplicates

`corpus.py related STMT-CC100-124-TRUTH-KNOWABILITY --limit 10` and dossiers for
that seed, `STMT-CC100-124-CONTEXTUAL-TRUTH-KNOWLEDGE`, and
`STMT-CC100-124-CONTEXTUAL-COMMON-KNOWER-BRIDGE` find the October31 intake but
no Lean declaration, argument, result or countermodel for these propositions.
Literal/contextual siblings are scope alternatives, not proved Fitch steps.
Exact text/declaration searches across TruthCore, attempts, results, arguments
and inferences found no Moore-conjunction knowability proof. The existing
ultimate-adequacy-integration-735 note, bounded intake table at line1904,
already rejects the common-knower quantifier exchange. Do not repackage that
warning as a new result.

Exact vocabulary/reuse:

- `TruthCore.Modal.Frame`, `Holds`, `Reflexive`, `Symmetric`, `Transitive` in
  `TruthCore/Modal/Kripke.lean`. `Formula` has one modal box, no epistemic
  operator; its derived conjunction is classical, so do not use it to advertise
  a constructive conjunction theorem.
- `TruthCore.Logic.JustificationIntrospection.Knows F p w` is exactly universal
  truth of the predicate p over epistemic alternatives. Reuse for the survivor
  and frame specialization; `TruthCore.Modal.axiomT_valid` supplies factivity
  from reflexivity. The existing
  `TruthCore.Results.Logic.JustificationIntrospection.introspectionTransfer`
  uses `axiom4_valid` but proves a different justification-norm consequence.
- `TruthCore.Results.Logic.KnowledgeRetorsion.noFactiveKnowerOfUniversalNoKnowledge`
  proves that universal ignorance cannot itself be known under factivity. It
  has neither modal knowability nor a Moore-conjunction schema: no duplicate.
- `TruthCore.Modal.DesignatedValidity` already supplies `ContentTransport`,
  `Agreement`, designated validity and successor-closure criteria. Do not
  reimplement their local/global distinction. The present theorem can avoid
  necessitation altogether by requiring laws at each accessed witness world.

The seed’s someone/sometime operator and a fixed subject’s epistemic box are
not identical. Use a generic world-indexed K for the principal consequence;
interpret it explicitly as fixed-agent knowledge for the concrete frame model.
Distributed `∃ agent/time` satisfies conjunct extraction if each witness does,
but does not identify one subject/time for different truths. A formal bridge
from a temporal language to world-indexed contents remains separate. F6’s
existence of epistemic reasons supplies none of the knowability premises.

## Selected gap: Moore-instance closure versus restricted discoverability

Let `P : W → Prop`, `K : (W → Prop) → W → Prop`, modal frame R, and actual a.
Write `M(P)(w) := P(w) ∧ ¬K(P)(w)` and
`PossibleKnown(P,a) := ∃v, R(a,v) ∧ K(P)(v)`.

The weakest useful local core needs only, for every v accessible from a:

1. `K(M(P))(v) → K(P)(v)` (left-conjunct extraction for this instance).
2. `K(M(P))(v) → M(P)(v)` (factivity for this instance).

From these, constructively `¬PossibleKnown(M(P),a)`. General factivity and
full conjunction distribution are sufficient stronger profiles, not minimal
premises. Neither reflexivity of modal R, S4/S5, modal necessitation, knowledge
of the laws, nor actual-world factivity alone is needed. Actual-only laws are
insufficient unless separately transported to the possible knower.

If the one schema instance `M(P)(a) → PossibleKnown(M(P),a)` is also assumed,
then constructively `¬M(P)(a)` and `P(a) → ¬¬K(P)(a)`. Upgrade to `P(a) → K(P)(a)`
requires only explicit stability `¬¬K(P)(a) → K(P)(a)`, rather than unrestricted
DNE. A general excluded-middle assumption is a stronger sufficient alternative.
Keep the constructive proof free of `classical` and `Classical.byContradiction`.
The direct positive existential result is also useful: an unknown truth P gives
a true but unpossibly-known content M(P), with no DNE or knowability premise.

For a family C, local restricted knowability is
`∀Q, C(Q) → Q(a) → PossibleKnown(Q,a)`. The decisive bridge is `C(M(P))` for
the target P. Closure of C under *all* Moore conjunctions is stronger than
necessary. Prove strong-to-weak schema specialization separately if recorded
as sibling strengths. P itself need not belong to C for the Moore-instance
argument; keep target class and knowability class distinct. Unrestricted C is
one specialization, not the baseline statement.

### Strong survivor under the same epistemic background

Use four worlds 0,1,2,3, actual0. Epistemic equivalence classes are `{0,1}`,
`{2}`, `{3}`. Define K using the existing `Knows`. Modal R relates worlds with the same atomic truth value: `{0,2}`, `{1,3}`.
Let atom p be true at0,2 and false at1,3. Both frames satisfy S5; all predicates
have factive K and full conjunction extraction, and K has positive/negative
introspection. Yet p is actually true and not actually known, because0
admits1 as an epistemic alternative.

Take C to be all contents constant on equal atomic valuations: if p(u) and
p(v) have the same truth value then Q(u) iff Q(v). This contains every Boolean
combination of the one nonconstant atom (and is closed under ordinary Boolean
operations); it is not merely an arbitrary justification flag or a singleton
chosen to fit the desired truth. For **every world w** and every Q in C, if
Q(w) then Q is known at2 when p(w), and at3 otherwise; the selected endpoint is modally accessible from w. Finite case analysis
provides those witnesses without classical choice. Thus restricted knowability
holds globally, with both true and false atomic valuations represented by fully
informed alternatives, while actual ignorance survives. The reverse `PossibleKnown(Q,w) → Q(w)` also holds for C: factivity at
the modal witness gives Q there, and modal accessibility preserves the atom’s
valuation, so C transports Q back to w. Thus even the **biconditional**
restricted knowability schema holds globally. Universal R gives a second,
weaker survivor of the forward schema, but loses this reverse implication.

M(p) is true at0 but false at2 although their atomic valuations agree, so C
excludes it. Full knowability fails at the very Moore instance the theorem
requires. The survivor preserves the same factivity/conjunction background;
it removes the Moore-admissibility premise, not the epistemic laws. Its
philosophical burden remains whether restricting knowability to contents
independent of epistemic status captures the intended thesis. An extensional
family is a semantic surrogate for an epistemic-free fragment, not a proved
adequate syntax or account of human discovery.

## Other genuine gaps, deferred

1. Actuality-indexed knowability: distinguish the world of learning from the
   world described, and test whether knowledge of actual ignorance implies
   ignorance at the learning world. This is a content/index bridge, not another
   designated-necessitation theorem. It needs a two-index epistemic account;
   defer until the first cluster lands.
2. Strengthened restricted knowability plus KK: §5.3’s argument uses both
   `p → ◇Kp` and `◇KKp → Kp`, together with possible transport of `Kp → KKp`.
   This is stronger than forward knowability, and requires admitting both p
   and Kp. It is a later test of the survivor, not a refutation of every basic
   restriction. Do not silently add the reverse schema or epistemic closure.

## Four-line implementation brief

1. **Target:** typed Moore-conjunction unknowability, constructive knowability
   collapse, explicit stability upgrade, and the four-world restricted-family
   survivor in one lane C Logic cluster; no God/common-knower conclusion.
2. **Reuse:** the three CC100-124 statement IDs above as discovery anchors;
   `Frame`, `Holds`, `axiomT_valid`, and
   `JustificationIntrospection.Knows` as exact semantic vocabulary. Existing
   retorsion/introspection results are neighboring boundaries, not proof
   premises. Preserve their interpretation rather than adding another Knows.
3. **Missing step:** frozen Challenges and solutions for the weak local core,
   strong-profile specialization and same-background survivor; new analyst
   statements/argument/result/configuration records with no new source claims.
   Prove the survivor’s C membership/Boolean closure, global knowability,
   actual ignorance and failure of Moore closure explicitly.
4. **Premise comparison:** no current frontier premise changes. Conditional
   consequences retain accessed-world factivity/extraction, add exactly the
   relevant Moore knowability instance, and add K-stability only for the
   classical-strength conclusion. The survivor retains factivity, full
   extraction and even S5, retains restricted global knowability, and rejects
   Moore admissibility. No primitive premise or root obligation is discharged.

The intake above preceded implementation. Issue #1053 selected this cluster;
the implemented declarations and exact proof boundaries are recorded below.
Convention resolution sourceRevision:
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.


## Selected implementation (#1053)

The vocabulary is `TruthCore.Logic.FitchKnowability`; all six checked results
are in `TruthCore.Results.Logic.FitchKnowability.Solution`. The weak core is
`RelevantLaws`, not `GlobalLaws`; `relevantFromGlobal` explicitly records the
strong-to-weak implication. `mooreUnknowable` applies factivity and extraction
at the possible knower. `doubleNegatedKnowledge` composes that obstruction
with `MooreInstance`. `stabilityUpgrade` separately consumes
`KnowledgeStable`; it does not use ambient classical DNE. `restrictedInstance`
requires both `RestrictedKnowability` and `MooreAdmissible`. No inclusion-
minimality, intuitionistic countermodel or proof of either open premise is
advertised. The constructive theorem can be read as exclusion of the selected
actual unknown truth; it does not replace double-negated knowledge by knowledge.

`restrictedSurvivor` certifies the exact named `survivorEpistemic`,
`survivorModal`, `survivorContext` and `survivorAtom`. Both frames are reflexive,
symmetric and transitive. The result includes full global factivity and
conjunct extraction, Boolean closure of `AtomInvariant survivorAtom`, inclusion
of the atom itself, global biconditional restricted knowability, actual
ignorance, failure of Moore admissibility, and failure of E-subset-R. Thus the
rival keeps the epistemic laws, scope and selected content fixed while excluding
the Moore content from the knowability domain. In particular, this witness does
not answer what happens if epistemic alternatives are additionally required to
be modally possible: that is an OPEN compatibility extension, not an omitted
property that can be silently ascribed to the model.

All formulations are analyst statements with attribution deferred. Existing
CC100-124 source readings are unchanged. The generic K result extends to a
some-agent/sometime interpretation only if factivity and conjunct extraction
are supplied at each relevant world for that same content. The concrete
survivor is fixed-agent relational knowledge. No common witness across contents,
God, actual epistemic authority or root truth follows. F6 epistemic-reason
existence is unchanged. A transcendental commitment to conditions of inquiry or
denial is distinct from the claim that every truth is knowable, and still more
from knowledge of every truth. No further normativity premise is introduced. The independent questions of adequate admissibility,
humanly possible inquiry, actuality/time indexing and applicability to reality
remain OPEN; their blockers are semantic/formalization choices rather than
missing source acquisition.

## Compatibility extension (#1059)

The previously OPEN E-subset-R comparison is now a separate analyst cluster,
`TruthCore.Logic.KnowabilityCompatibility`, preserving the earlier Challenge,
source claims and exact meanings. The adapter `relationalContext E R actual`
constructs the existing Context using the existing fixed-agent `Knows E`.
`Included E R` explicitly says that an epistemic alternative at w is a modal
alternative at that same w. It does not identify the two relations or impose
commutation, temporal change or an actuality-indexed content interpretation.

Three results in `TruthCore.Results.Logic.KnowabilityCompatibility.Solution`
separate the bridges:

- `admittedKnown`: under Euclidean R, E ⊆ R, and the **global biconditional**
  for C, every true admitted content is known. Given p(w), forward knowability
  provides R(w,v) and Kp(v). For any E(w,u), inclusion gives R(w,u), and the
  Euclidean sibling property gives R(u,v). Reverse knowability at u gives
  p(u), establishing Kp(w). Factivity, modal reflexivity, epistemic S5, C's
  Boolean closure, Moore admissibility and classical stability are unnecessary
  for this consequence. C is still restricted: this is not knowledge of all
  predicates without an additional unrestricted-domain premise.
- `forwardSurvivor`: retain the exact earlier four worlds, epistemic blocks,
  atom and invariant-content family, but make R universal. All old forward
  witnesses remain accessible. E ⊆ R and both frames satisfy S5; actual
  ignorance and failure of Moore admissibility remain. The biconditional
  fails, proved by composing `admittedKnown` with actual ignorance. Thus
  epistemic/modal compatibility is not an obstacle to ordinary **forward**
  restricted knowability. The reverse implication is a real strengthening.
- `lineSurvivor`: take R to be the union of the previous E and R. This is the
  reflexive symmetric line 2–0–1–3. Old modal edges retain the old equivalence;
  on newly admitted epistemic edges, symmetry lets knowledge at the endpoint
  yield truth at the start. E ⊆ R, the global biconditional and ignorance
  coexist, but Euclideanness fails at successors 1 and2 of0. This is a genuine
  weaker-frame rival, not a claim that metaphysical modality is non-Euclidean.

Both model proofs import the earlier complete restricted-survivor certificate,
reusing its factivity, conjunction extraction, Boolean closure, atom membership,
actual ignorance and inadmissible Moore content. The earlier certificate itself
already supplies the compatibility-omission control under S5. The three
witnessed omissions do not establish a complete frame correspondence or global
inclusion-minimality. In particular, the collapse theorem's proof uses the
reverse schema at epistemic alternatives, not merely at actuality.

Claim/type self-sweep: all knowledge operators remain fixed-agent relational
boxes over the SAME content predicate, with no someone/sometime or common-knower
quantifier exchange. No temporal interpretation, source attribution, F6-to-
knowability bridge, actual cognitive competence, normative authority or root
truth is added. Admitted contents are a semantic surrogate for an epistemic-free
fragment, not a proved syntax or an independently warranted philosophical
restriction. The strongest rival retains forward knowability, S5 and E ⊆ R
while rejecting reverse knowability; a second retains the biconditional but
rejects Euclidean R. Actual applicability of all three relations/schemas remains
OPEN. The necessary-condition inference from accepting epistemic reasons still
does not establish either knowability schema.

The new Challenge compiled before Solution and is frozen at SHA256
`aa93f7e522c1aae0406e69890a2ca53d8a25b93755a11b9778720af206bca0c8`.
The direct proof terms depend on no axioms. Remaining verification/publication
state is recorded by the result records and current issue handoff rather than
asserted by this mathematical discussion.

`positiveSurvivor` additionally supplies a joint nonvacuity control for the
collapse assumptions: both E and R are the earlier `survivorModal`, on the same
four worlds and C. The admitted atom has both true and false valuations.
Atom invariance proves global biconditional knowability, and `admittedKnown`
then yields admitted knowledge. This is neither an inconsistent background nor
an empty family. Its separately frozen `Positive/Challenge.lean` has SHA256
`61df2cc207280ea7b1896343521b737cad4a4d9a520ed0df3109e78e548b7a39`;
the original Challenge is unchanged. The computed #143 frontier remains90
open premises (30bare/18supported/42stated), cheapest route31, with no additions,
removals or discharges.


## Proper intuitionistic forcing model (#1065)

This is a deliberately different logical semantic profile, not a counterexample
to the earlier Lean-`Prop` result or to the owner's established excluded-middle
floor. The model admits **all** persistent contents on information order
`0 ≤ 1 ≤ 2`. The information order is not automatically physical time,
epistemic accessibility, or metaphysical necessity. Actuality is stipulated at1.

`TruthCore.Logic.IntuitionisticKnowability.Content` is
`(UpperSet (Fin 3))ᵒᵈ`: Mathlib orders UpperSet by reverse inclusion, so its dual
has truth ordered by inclusion. The actual Mathlib Heyting implication and
pseudocomplement are used. The checked `forcingBridge` shows
`w ∈ (P ⇨ Q)` iff every information extension `v ≥ w` that forces P forces Q;
negation specializes this to no future P. This bridge prevents replacing
intuitionistic negation with Boolean complement or a stand-in truth table.

The epistemic frame is the first-three-world restriction of the earlier
`survivorEpistemic`: blocks{0,1},{2}. Modal R is the matching restriction of the
existing universal frame, hence E⊆R. Existing Frame, Knows and PossibleKnown
meanings are reused exactly on the underlying extensions. Typed content
constructors use Mathlib upperClosure, and `OperatorsExact` proves it adds no
world on this selected model: raw relational knowledge and possibility already
preserve persistent contents. Old epistemic frame properties are imported from
the checked restricted-survivor certificate, not restated as new premises.

The four persistent contents are `∅`, `{2}`, `{1,2}`, and `univ`. Knowledge maps
them to `∅`, `{2}`, `{2}`, and `univ`. The joint certificate proves factivity,
top/conjunction preservation, normal distribution, positive introspection and
the specifically stated Heyting negative-introspection inequality. Ordinary
E/R equivalence is also checked, but none of this is a soundness/completeness
claim for an entire IK/IS5 calculus or a claim that every additional constructive
modal interaction law holds.

Every persistent content satisfies forward knowability: if true anywhere it
is true at2, and the fixed agent knows it at the singleton endpoint2. Moore
contents use **Heyting** `P ⊓ (KP)ᶜ`; all are still contents, and they are bottom
in this model and cannot be known. Thus no arbitrary epistemic-free syntactic
restriction excludes them. The certificate also proves `P ≤ (KP)ᶜᶜ` for every
content.

For the same model choose `P={1,2}`. At1, P and double-negated KP are forced,
while KP **and its intuitionistic negation** are both unforced. The relevant
object-language DNE formula `¬¬KP ⇨ KP` and EM formula `KP ∨ ¬KP` are unforced.
Metalevel non-forcing is not object-level negation. In particular, the old
pointwise `FitchKnowability.Moore` would give a different, nonpersistent
extension and is NOT identified with this Moore operation. The old
`doubleNegatedKnowledge` and `stabilityUpgrade` theorems are comparison anchors,
not falsely instantiated as future-world-negation theorems. Factivity and the
matching relational operators are reused only where semantics genuinely match.

Claim/type self-sweep: the counterprofile has one fixed agent/operator and one
actual information index; no distributed/common-knower, actual human knowledge,
F6-to-knowability, necessary being, God or root truth is inferred. The strong
classical/stable rival excludes the omitted-stability profile; this model does
not refute or silently reopen the established EM floor. Classical Mathlib
reasoning about a finite mathematical model is separate from the model's
object-language validity. Applicability of these information stages and
accessibility relations to actual inquiry remains **OPEN**.

The ordinary-import Challenge was compiled with only its two intended sorry
warnings and frozen before Solution work: SHA256
`d89a0bd265e18e8245b0ff4a3d247be3b082cae81e945ccea1dedeb1407a9c77`.
The selected Solution compiles warning-free; both exact bindings pass. Actual
axiom probes are exactly the approved Mathlib trio for both results. Initial
missing Fin order/Fintype imports and explicit-set-membership rewrites were
repaired without changing the frozen targets. A metadata-only disambiguation
scope correction avoids retroactively assigning new senses to old arguments.
Both exact Comparator and independent NanoDa checks passed with the approved
Mathlib trio. Computed root-frontier90→90 (30bare18supported42stated), cheapest
route31→31; no added, removed or discharged root premises. Final delivered-head
CI and current-head review remain required.
