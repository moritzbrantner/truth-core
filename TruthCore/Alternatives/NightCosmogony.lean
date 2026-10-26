import TruthCore.Alternatives.ActPotencyRegress

/-!
The "potency prior" cosmogony that Aristotle reports in *Metaphysics* XII.6,
1071b22-28 (the theologians who generate all from Night, the physicists who say
"all things were together"), and the open bridge its elimination needs (#497).

No new vocabulary: the commitment and the bridge are stated over the shared
act/potency predicates `InAct`, `InPotency`, `MovedIn`, `MovesIn` and
`PriorSimply` (`TruthCore.Latin.Aquinas.SummaTheologiae`).

Source witness: Ross/Perseus Greek edition, passage `ARIST-MET-XII-6`.
-/

namespace TruthCore.Alternatives.NightCosmogony

universe u v

/-- The theologians' and physicists' commitment as Aristotle presents it: some
being is in potency in a respect, no being in act in that respect is simply
prior to it, and it is nonetheless being reduced to act in that respect.

"If, as the theologians say who generate from Night, or as the physicists say
that all things were together, the same impossibility [follows]. For how will
it be moved, if there is not some cause in actuality?" (καίτοι εἰ ὡς λέγουσιν
οἱ θεολόγοι οἱ ἐκ νυκτὸς γεννῶντες, ἢ ὡς οἱ φυσικοὶ ὁμοῦ πάντα χρήματά φασι,
τὸ αὐτὸ ἀδύνατον. πῶς γὰρ κινηθήσεται, εἰ μὴ ἔσται ἐνεργείᾳ τι αἴτιον;).

Reading steps: "the same" is the aporia's "potency is prior" (claim
`ARIST-MET-1071B-POTENCY-PRIOR-A`), read as simple priority
(`DISAMB-PRIORITY-SIMPLE-OR-IN-TIME`); "generate from Night" is read as one
such potency being reduced to act, motion in the broad sense (`DISAMB-MOTION`),
which Aristotle's question "how will it be moved?" presupposes. Weakest
reading: one potency and one respect, not every potency; nothing about the
time of the generation or whether Night existed for an infinite time
(1072a7-8). It entails the bare rival
`TruthCore.Alternatives.ActPotencyRegress.PotencyPriorToActReading`.

Source: Aristotle, *Metaphysics* XII.6, 1071b26-29.
-/
def UnprecededPotencyActualizedReading {Being : Sort u} {Respect : Sort v}
    (InAct InPotency MovedIn : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∃ x r, (InPotency x r ∧ ∀ y, InAct y r → ¬ PriorSimply y x) ∧ MovedIn x r

/-- Open bridge, unattributed: a being in act in a respect that moves another
being, which is in potency in that respect, is simply prior to it.

Aristotle's conclusion "that act is prior" (ὅτι δʼ ἐνέργεια πρότερον,
1072a4) after "how will it be moved, if there is not some cause in actuality?"
(1071b28-29) motivates it, and Aquinas' "an efficient cause is prior to its
effect" (`EfficientCauseIsPriorToEffectReading`) is a sourced cousin for
efficient causes, but no source sentence says it of every actual mover of a
potency, so no claim attributes it. It does not say that moving is simple
priority (`DEF-SIMPLE-PRIORITY`), only that this kind of moving brings it;
it says nothing of self-movers or of movers not in act. -/
def ActualMoverIsSimplyPriorReading {Being : Sort u} {Respect : Sort v}
    (InAct InPotency : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ y x r, InPotency x r → MovesIn y x r → InAct y r → y ≠ x → PriorSimply y x

end TruthCore.Alternatives.NightCosmogony
