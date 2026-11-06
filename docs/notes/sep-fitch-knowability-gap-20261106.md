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
existence is unchanged. The independent questions of adequate admissibility,
humanly possible inquiry, actuality/time indexing and applicability to reality
remain OPEN; their blockers are semantic/formalization choices rather than
missing source acquisition.
