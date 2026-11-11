# Divine love of all existing things: bounded q.20 bridge

## Target and source reading

This is an analyst reconstruction of Thomas Aquinas, *Summa theologiae* I q.20
a.2, connected to `STMT-GOD-IS-SUPREMELY-GOOD`
(`e0dae79f-c042-5a08-a148-725d0468df91`) and `STMT-GOD-HAS-WILL`
(`66aecdd7-ea4e-55c6-9377-10db08893854`). Both are existing
root-reaching case nodes, but the new conclusion is **not** itself a premise of
the current `STMT-CATHOLICISM-TRUE` route. This is a **candidate supporting
bridge**, not a root-premise discharge: the named next consumers are
`STMT-HIDDENNESS-GOD-LOVES` (a stronger perfectly-loving, relationship-capable
God) and `STMT-CLASSICAL-ATTRIBUTES-INCLUDE-PERFECT-INTELLECT-AND-GOOD-WILL`
(an actual good will without deceptive assertion). Universal willing of some
good does not entail either perfect interpersonal accessibility or veracity;
those are additional disputed normative/cognitive bridges. This checkpoint
is therefore lower-priority exploratory support until such a bridge is built.

Sources consulted for orientation and semantic review, without creating new
source claims or pinned passage records:

- [ST I q.20 a.2 co. and ad 3–4](https://www.newadvent.org/summa/1020.htm):
  every existing thing has existence and perfections as goods; God's will
  causes their existence/good (by q.19 a.4); so God wills some good to each
  thing; to love something is to will good to it. Love of irrational creatures
  is not friendship; sinners are loved under their existing nature and opposed
  under the aspect of sin. Ad 2 explicitly separates the eternal divine love
  from the temporal existence of creatures.
- [ST I q.20 a.1 co., ad 1, ad 3](https://www.newadvent.org/summa/1020.htm):
  love as first act of will, unlike a bodily passion; willing good for someone
  is distinct from merely willing a good.
- [ST I q.19 a.1 co., ad 2](https://www.newadvent.org/summa/1019.htm):
  will follows intellect and includes possessing, loving and delighting in
  good, not only seeking an absent object. `GodHasWill` is nevertheless an
  opaque one-place predicate in the existing Lean case.
- [ST I q.19 a.4 co., ad 3–4](https://www.newadvent.org/summa/1019.htm):
  divine will is the cause of things; divine goodness is a reason for willing
  other things, and natural or essential causation is not freely interchangeable
  with an act of will.

The argument **does not** say that God loves irrational creatures with
friendship, loves all recipients in the same degree, approves of moral
wrongdoing, needs creatures, experiences affective changes, or necessarily
wills any particular finite creature. Q.19 a.3 distinguishes absolute and
suppositional necessity. Neither `Loves` nor `WillsGoodFor` has a time index:
the formalization does not prove the eternality/temporal-creation distinction
in q.20 a.2 ad 2. The conclusion is quantified over the actual things in
`InAct x esse`; it is not over all merely possible entities. It is vacuous if
`IsGod` is empty; the finite controls supply an actual God and an actual
distinct other for diagnostic purposes.

## Formal route and explicit OPEN inputs

In `TruthCore.Case.Catholicism.DivineLoveBridge`:

1. `GodIsSupremelyGood IsGod InAct GoodIn CausesIn esse` is precisely
   `∀ g, IsGod g → GoodIn g esse ∧ ∀ x r, x ≠ g → InAct x r → CausesIn g x r`.
   Its goodness is metaphysical participation/causal-perfection goodness,
   **not** a predicate of moral benevolence. In particular, it does not
   quantify over intentional acts and excludes self-effects.
2. `GodHasWill IsGod HasWill` is just `∀ g, IsGod g → HasWill g`. It does not
   say what God wills, what an act of will causes, or that any exercise occurs.
3. `GoodnessIsActualityReading GoodIn InAct` is the already recorded
   `STMT-GOODNESS-IS-ACTUALITY`: `∀ x r, GoodIn x r ↔ InAct x r`.
4. **OPEN `CausalExistenceWilling`:** For a distinct actual `x`, if God has
   will and effectively causes `x` in `esse`, then God wills the existence-good
   *for that x*. This intentional step is **not** in `CausesIn` and is not
   obtained merely from causal maximality or supreme-goodness.
5. **OPEN `DivineOwnGoodWilling`:** A God who has will and is good in `esse`
   wills that good for Himself. Needed because the existing causal goodness
   predicate explicitly excludes self-causation. It expresses a q.19 a.1 /
   q.20 a.1 theme, not an inference from the opaque `HasWill` flag alone.
6. **OPEN `WillingGoodEntailsLove`:** If God wills an actual good *to its
   recipient*, then God loves that recipient in the non-passional sense of
   willing some good to it in q.20 a.2. Aquinas restricts benevolence properly
   speaking to rational creatures (ad 3), while irrational creatures are loved
   in a different, ordered way. This one-way sufficient rule adds neither
   universal friendship nor affection, equal degree or unqualified desire.

`divineWillsGoodForAllExisting` proves that for each God and each actual `x`,
there is a good of `x` which God wills for `x`. The witness is `esse`: for
`x ≠ g` the universal causal-perfection predicate supplies causation of
existence and the open causal-to-intentional bridge supplies willing; for
`x = g` the independent self-good bridge applies. The theorem then uses
coextension of actual being and good. `godLovesAllExisting` adds the final
love-meaning bridge to obtain
`∀ g, IsGod g → ∀ x, InAct x esse → Loves g x`.

These are Lean-checked **conditional** conclusions (not registered or
Comparator-verified corpus results), not a derivation
from supreme goodness plus bare will alone and not independent confirmation
of the Catholicism root. The `GoodIn`/`InAct` dictionaries and the causal
`CausesIn` relation are the ones supplied to the existing case statements;
no new identification with moral goodness, divine intention, or mental
activity is smuggled into their definitions. Nor does the theorem prove the
stronger q.19 a.4 thesis that willing itself efficiently *causes* the
creature's good; `CausesIn` and `WillsGoodFor` are separately typed and merely
connected by an explicit bridge. `WillsGoodFor` is a primitive
recipient-directed volition, not a relation defined in terms of `Loves`;
`Loves` is another primitive, not an alias for `WillsGoodFor`.

## q.19 a.4's positive support options, and rival

Q.19 a.4 offers three distinguishable reasons to take the causal bridge
seriously, **not** generic proof rules for `CausesIn`:

1. **Priority of intellect/volition over natural teleology.** A natural
   agent's end and means are directed by an antecedent intellectual agent;
   God as first agent acts intellectually and voluntarily. This needs a
   defended hierarchy of intentional determination and first agency; a bare
   causing relation has neither.
2. **Determinate effects vs. necessary uniform natural emission.** A natural
   agent has a fixed effect unless impeded, whereas the indeterminate fullness
   of the first divine source produces determinate finite effects through
   intellectual-volitional specification. This requires the relevant
   metaphysical indeterminacy, an account of the effects' diversity, and
   an objection-resistant distinction between nature and choice.
3. **Intellectual preexistence of effects.** Effects are conceived in the
   intellectual cause and are actualized through the cause's will. This
   gives a particularly direct intentional explanation but needs
   preexistence-as-conceived and willing-as-actualizing, neither of which
   follows from the extant `CausesIn` relation.

The strongest rival *to this specific causal-to-willing step* grants that the
first source has will and wills its own good, but says its effects flow from
its nature without an additional recipient-directed act of willing. This
natural-diffusion account preserves the existing `HasWill` and `CausesIn`
predicates and is directly instantiated by the `omitCausalWill` control. Its
philosophical price relative to Aquinas is a denial that q.19 a.4's account
of divine essence as intellect/will, its reasons for determination of effects,
or its goodness-as-reason-for-willing explanation suffices for volition toward
each effect. This remains open, not a demonstrated incoherence.

The broader, historically motivated rival is a **first intellect acting by
necessary emanation without will**:
`corpus/statements/2537adb1-fca8-4a76-93a7-18a688cb4507.json` and
`TruthCore/Causality/SpineRivalsAttributes.lean`. It disputes even the earlier
move from cognition/first causation to divine will itself and must reject at
least one of q.19 a.4's three philosophical routes or their applicability.
Neither rival violates the existing generic `CausesIn` semantics merely by
disagreeing with its intentional interpretation.

For `CausalExistenceWilling`, a mundane positive illustration is a builder
causing a shelter to exist because she chooses that shelter for its
occupants; a contrast is an unintended byproduct of a machine with an
operator who also happens to have will. These are conceptual examples of
distinct causation and intending, not evidence that divine creation is
exactly like either. Efficient causation, mere enabling, natural emanation,
formal/exemplar preexistence and choosing an outcome are different roles.
No transitivity, well-foundedness, asymmetry, or causal uniqueness is assumed
of `WillsGoodFor`; nor is any such property supplied for generic `CausesIn`
by this module. **OPEN applicability** is precisely the step from those
ordinary volitional examples or Thomistic metaphysical arguments to every
existing creature's intentional dependence on the first cause.

## Nonvacuity, omissions, and revision conditions

`LoveControls` uses `Being = Bool` (false = God, true = distinct creature),
`Respect = Unit`, `esse = ()`, both beings in act and good, and exactly the
God-to-creature `CausesIn` assignment. `GodIsSupremelyGood`, `GodHasWill` and
the existing goodness/actuality coextension hold in **every** profile.

| Profile | OPEN bridge omitted | Actual failure |
| --- | --- | --- |
| `complete` | none | Both God and creature are loved |
| `omitCausalWill` | causal existence → willing good for creature | Creature is unloved; own-good willing and love entailment survive |
| `omitOwnWill` | God's self-good → self-directed willing | God Himself is unloved; creature is loved |
| `omitLoveMeaning` | willing good for recipient → loving | Both are willed good but neither is loved |

These are proposed populated finite **structural surrogates**, not metaphysical
possibility proofs. The q.19 a.4 intellectual and teleological positive
commitments are not encoded in the surrogate. Restoring those richer
commitments could eliminate the omissions. The comparison establishes the
specific insufficiency of the existing stage-2 predicate types (the Lean
control `loveControls` is kernel-checked by `decide` after unfolding), not a
global non-entailment under all Thomist interpretations.

Axiom footprint (`#print axioms`, this module imports no Mathlib):
`divineWillsGoodForAllExisting` and `godLovesAllExisting` use `propext`,
`Classical.choice` and `Quot.sound`, because the proof splits classically on
whether the loved `x` is God Himself; `loveControls` uses `propext`. None is a
registered corpus result. Registering the theorems would require either an
explicit decidable-identity input on `Being` or a bridge reformulated to avoid
the self/other case split, under the zero-axiom policy for non-Mathlib results
(`docs/axiom-policy.md`).

The current provisional assessment is therefore that Aquinas supplies a
coherent conditional argument *under an intentional-creative causality
reading*, but the existing corpus's generic causality/goodness and opaque
will premises do not yet warrant it. A useful next test would formally
instantiate one of q.19 a.4's three positive subroutes with independent
claims about an intellect's practical determination of effects, then check
it against the necessary-emanation rival and the surviving `HasWill`-without-
recipient-directed-volition model. A new source claim should wait for a
pinned witness and exact attribution review; this note is a navigation and
interpretation record only.
