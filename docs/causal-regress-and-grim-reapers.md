# Can Grim Reapers prove the *per se* causal-regress premise?

**Target:** `STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES`, the still-open
Second Way claim interpreted as well-foundedness of `CausesAsCaused`. The current
corpus has a sourced reading but no independent proof of this claim. The result
`AQUINAS-ST-I-Q2-A3-SECUNDA-VIA` uses it as a premise; it does **not** establish
it. Likewise, an infinite chain of temporal causes *per accidens* is not the
same claim as an essentially ordered chain exercising power *per se*.

## 1. The no-first-deadline Grim Reaper test

Consider Reapers with deadlines indexed by `Nat`; a higher index signifies an
earlier deadline. There is no earliest deadline. Give each Reaper the rule:

> Reaper `n` acts **if and only if** no Reaper with a higher index acts.

Formally, `acts n ↔ ∀ m > n, ¬ acts m`.

The axiom-free Lean result
`GRIM-REAPER-NO-FIRST-SCHEDULE-IMPOSSIBLE` derives a contradiction:

1. If some Reaper `n` acts, no higher-index Reaper acts.
2. In particular, none higher than `n + 1` acts. The rule then **requires**
   `n + 1` to act, contradicting (1).
3. So no Reaper acts. The rule for index `0` then requires Reaper `0` to act,
   again contradicting the supposition.

This is an inconsistency of **that combined schedule and rule**, not of an
infinite ordered set alone. The companion model
`FINITE-GRIM-REAPER-SCHEDULE-CONSISTENT` verifies that three Reapers with the
same rule are consistent: the maximum-index (earliest-deadline) Reaper acts.

The law already captures the strong assumption that there is an action at a
deadline exactly when none has occurred earlier. A physical story adds more
assumptions: a victim initially alive, each Reaper capable of acting, no
unrelated death or resurrection invalidating that equivalence, and the
specified deadlines and counterfactuals being jointly realizable. Dropping or
weakening these assumptions may dissolve the contradiction.

## 2. Why this does not yet establish the target

The per se premise in Aquinas, *Summa theologiae* I q.2 a.3, concerns the
simultaneous dependence of an intermediate efficient cause on another. A
Grim Reaper sequence, by contrast, is a supertask-style arrangement of
events ordered **in time**, with a specialized inhibition rule. Neither the
temporal order nor its action rule follows from the definition of `CausesAsCaused`.

`INFINITE-LOCAL-TRANSMISSION-MODEL` makes the underdetermination explicit:

- There is a predecessor relation `R (n + 1) n` with no first member.
- All nodes are currently active, so each satisfies the **local** condition
  `active n ↔ active (n + 1)`.
- Nevertheless `R` is not well-founded (`¬ Acc R 0`).

This is a consistent mathematical model. It is **not** a demonstrated possible
world containing genuinely derivative efficient causes. In particular, a
defender may insist that "causing only as caused" imposes more than matching
activity: a power must actually be *grounded*, not just locally correlated.
But that stronger meaning must be specified and independently defended.

The exact missing step is a **transfer principle** of roughly this form:

> If a genuinely *per se* cause-chain had no first, its powers and dependencies
> could be arranged into a jointly possible Reaper-type configuration with the
> stated action rule.

This is related to a causal-network *patchwork* or recombination principle.
It is not pure logic. Merely assuming "no first entails no effect" as the
transfer principle would restate the desired conclusion and beg the question.
Formalizing a conditional proof from an explicitly assumed transfer principle
is straightforward, but would close no frontier premise until that principle
itself is justified. No such axiom is included in these verified results.

## 3. The deeper issue: which notion of grounding?

An equation at every link, `power(n) = power(n + 1)`, for binary power has two
uniform solutions (every link powerless or every link powered). These are
**genuine, explicitly defined mathematical objects**, but the *equations*
alone do not specify which one is intended.

The stronger theorem `ESSENTIAL-POWER-UNDERDETERMINED` tests whether making the
link's *essential* nature more precise fixes the problem. Its rule says a node
is active **exactly when an immediately upstream cause is active**. It
establishes all of the following without axioms:

1. The whole infinite chain can be active, while a different assignment
   satisfying the same equations has no active members.
2. For **any** chosen link, we can cut it and give a consistent assignment
   that preserves activity above the cut but leaves the cut node and **every
   downstream node inactive**. This models the counterfactual indispensability
   of its immediate cause to the downstream effects.
3. The uncut chain is still not well-founded.

This answers an objection to the earlier `LocalTransmission` countermodel:
even explicitly modeling the removal of instrumental support does not *by
itself* select a unique global source of power. The intervention result is an
**existence of an admissible response**, not proof that real causal powers
must obey exactly these equations or that every intervention has that response.

The contrasting theorem `FINITE-GROUNDING-HAS-SOURCE` takes a different, more
explanatory reading. A node's power is **inductively grounded** when either it
has intrinsic power, or it receives power along one actual link from another
node whose power is already inductively grounded. Lean constructs a finite
path from every such active node to an intrinsic source. If no source exists,
no act in this *inductive* semantics can be established.

Both mathematical approaches are internally coherent. The choice of
inductive (rather than coinductive, greatest-fixed-point or global) grounding
semantics is **a philosophical premise**, not a theorem about natural numbers
or about the Reapers. It cannot simply be hidden inside the meaning of
`CausesAsCaused` to close the Second Way frontier.

This addresses the worry about endlessly deferred *mathematical definitions*:
mathematicians do insist on unambiguous semantics, but infinity by itself is
not a flaw. Implicit or recursive definitions may work through existence and
uniqueness, or through an explicitly chosen least or greatest fixed point.
Tarski's original [lattice-theoretical fixed-point
theorem](https://people.csail.mit.edu/carroll/probSem/Documents/Tarski.pdf)
shows why a monotone self-reference can have a collection of fixed points
with least and greatest members. Existence need not imply uniqueness. What
our successor-chain equations lack is **a justified selection of the intended
solution**. What a metaphysical causal explanation might additionally lack
is an *independent actualizer*, but that claim requires separate argument.

The result `LOCAL-OBSERVATION-SELECTS-SOLUTION` sharpens this qualification:
**once activity or inactivity at node zero is supplied as a fact**, induction
on the index uniquely fixes the activity of every other link in the local
successor chain. So *non-uniqueness without a boundary condition* is not an
argument that the chain is mathematically impossible; one observed effect can
select a solution. **What explains that effect** is a different question.

This suggests a sharper proof task than "all infinities are impossible":

1. Define a *per se* instrumental cause by its **essentially borrowed** power,
   not merely its temporal ancestry or observed activity.
2. Establish, without merely defining the desired conclusion, **why real
   instrumental causation must follow the inductive/finite-source semantics**.
   The finite-grounding theorem then entails that an all-borrowed source-free
   chain cannot ground a present act.
3. Challenge this bridge with the stronger cut-edge and global fixed-point
   models. Explain why their power should not count as genuinely derivative
   efficient power, or concede the limit of the proof.
4. Only then, if helpful, defend a bridge from a hypothetical chain to a
   *possible* Grim Reaper configuration. Distinguish logically consistent
   instructions, physically possible operations, and metaphysically possible
   causal networks; a paradox in the instructions by itself does not settle
   these modalities.

## 4. Primary-source boundary and further objections

- **Pinned:** Aquinas, *Summa theologiae* I q.2 a.3, via
  `AQUINAS-ST-I-Q2-A3`, argues that removing the first cause removes the
  middle and the last; this is the very inference under challenge.
- **New pinned witness:** Aristotle, *Metaphysics* II.2 (994a),
  `ARIST-MET-II-2`, from the existing immutable Perseus Greek snapshot. Aristotle
  says that all terms of an infinite series of this kind would be intermediate
  and without a first there is no cause. The chapter treats several kinds of
  cause, so applying that statement specifically to the typed relation
  `CausesAsCaused` requires an interpretive step. The passage is **not** counted
  as a mathematical proof of well-foundedness.
- **Research leads, not yet pinned claims:** Robert Koons, *A New Kalam
  Argument: Revenge of the Grim Reaper* (the causal-network patchwork route);
  Nicholas Shackel, *The Form of the Benardete Dichotomy* (the unsatisfiable-pair
  diagnosis); Alexander Pruss, *Infinity, Causation, and Paradox* (super-tasks
  and causal finitism), and his 2025 essay *Grim Reapers and Logical
  Impossibility* (the effects of additional rules such as resurrection);
  Schmid and Malpass, *Benardete Paradoxes, Causal Finitism, and the
  Unsatisfiable Pair Diagnosis* (objections and replies).

**Frontier verdict:** the impossible Reaper schedule, finite schedule, infinite
local-transmission countermodel, cut-edge dependence countermodel, observation
selection lemma and finite inductive-source theorem are constructively proved
in their respective models.
`STMT-NO-INFINITE-PER-SE-EFFICIENT-CAUSE-SERIES` remains **open**. The next
research slice is an independent defense of why *per se* efficient power has
the inductive source-grounding semantics, not a Lean `sorry` removed by
restating the target as an axiom.

For the separate question whether an **endless temporal task can finish**, see
[supertasks and divergent series](supertasks.md). Its limit-endpoint model,
oscillating-output counterexample and fixed-cost divergence result do not
transfer automatically to simultaneous *per se* causal dependence.
