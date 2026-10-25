import TruthCore.Logic.ExcludedMiddle

/-!
Aristotle, *Metaphysics* IV.7, 1011b29-1012a17: the remaining arguments for
excluded middle after the statement of the law (1011b23-24, #167).

Every argument here is aimed at someone who *posits an intermediate*
(μεταξὺ ἀντιφάσεως): a third state, act of thought or answer besides
affirmation and denial. None is aimed at someone who merely *withholds* assent
from `p ∨ ¬p` (the intuitionist, `STMT-EXCLUDED-MIDDLE-WITHHELD-INTUITIONISM`).
The formal results built on these readings make that difference exact:

* the change argument (1011b29-1012a1) derives `F a ∨ ¬F a` for every state
  from a change premise that is itself a disjunction about every change, so the
  withholder withholds that premise too;
* the thought argument read conditionally (1012a2-5) shows only that a thought
  that is true or false settles its object, which the withholder grants;
* read universally, its premise "every object of thought is judged truly or
  falsely" is *equivalent* to excluded middle, so it begs the question against
  the withholder.

Source: Aristotle, *Metaphysics* IV.7 (Bekker pagination), passage
`ARIST-MET-IV-7`. CTS work: `urn:cts:greekLit:tlg0086.tlg025`.
-/

namespace TruthCore.Greek.Aristotle.Metaphysics

universe u

/-! ## The change argument, 1011b29-1012a1 -/

/-- Change between contradictories, *Metaphysics* IV.7, 1011b29-1012a1: in
respect of a contradictory pair (good / not good, white / not white), every
change goes from the one side to the other: "from not good to good, or from
this to not good" (ἐκ μὴ ἀγαθοῦ γὰρ εἰς ἀγαθὸν μεταβάλλει ἢ ἐκ τούτου εἰς μὴ
ἀγαθόν). The second horn makes the same point for a grey-like intermediate:
otherwise there would be a generation to white not from not-white, "but this is
not seen".

`State` is the states a subject passes through, `F` one side of the pair and
`Changes a b` a change from `a` to `b` in respect of it. Only the direction
"change → it went from one side to the other" is taken. The wider parenthesis,
that change is only into opposites and intermediates, concerns contraries and is
not used. -/
def ChangeOnlyBetweenContradictoriesReading {State : Type u}
    (F : State → Prop) (Changes : State → State → Prop) : Prop :=
  ∀ a b, Changes a b → (¬ F a ∧ F b) ∨ (F a ∧ ¬ F b)

/-- Change is seen, *Metaphysics* IV.7, 1011b29-1012a1: the posited
intermediate "would not change ... but now it is always seen to" (νῦν δʼ ἀεὶ
φαίνεται). Read as what the observation states: change in respect of the
contradictory pair is seen, i.e. some state is the start of such a change. This
is the sourced reading (claim `ARIST-MET-1011B-WHAT-IS-ALWAYS-CHANGES-A`). -/
def ChangeIsSeenReading {State : Type u}
    (Changes : State → State → Prop) : Prop :=
  ∃ a b, Changes a b

/-- What is always changes, universally: every state in the domain of the
contradictory pair is the start of some change in respect of it. This is **not**
attributed to Aristotle: it generalizes the observation `ChangeIsSeenReading` to
every state of the domain, which is what the formal argument needs. It is the
formalization's own open premise (`STMT-WHAT-IS-ALWAYS-CHANGES`, no claim; Codex
P1 on #174). -/
def WhatIsAlwaysChangesReading {State : Type u}
    (Changes : State → State → Prop) : Prop :=
  ∀ a, ∃ b, Changes a b

/-- Conclusion of the change argument: every state either has `F` or lacks it,
so no state lies between the contradictories. Excluded middle for one
predicate over one domain of states, derived rather than assumed. -/
def ContradictoryPairDecidedOnStates {State : Type u} (F : State → Prop) : Prop :=
  ∀ a, F a ∨ ¬ F a

/-! ## The thought argument, 1012a2-5 -/

/-- Thought that is true or false affirms or denies, *Metaphysics* IV.7, 1012a2-4, reading
A (conditional): "every object of discursive and intuitive thought, thought
either affirms or denies (this is clear from the definition) whenever it is
true or false" (ὅταν ἀληθεύῃ ἢ ψεύδηται). The clause "whenever it is true or
false" is read as a condition: every thought that is true or false is an
affirmation or a denial. There is no third act of thought that is true or false.

`Thought` is acts of thought; `Affirms t` and `Denies t` say that `t` affirms or
denies its object; `TrueT` and `FalseT` that `t` is true or false. -/
def TruthAptThoughtAffirmsOrDeniesReading {Thought : Type u}
    (Affirms Denies TrueT FalseT : Thought → Prop) : Prop :=
  ∀ t, TrueT t ∨ FalseT t → Affirms t ∨ Denies t

/-- Truth by composition, *Metaphysics* IV.7, 1012a4-5, read with the definition
of truth at 1011b26-27: "when it combines in this way, affirming or denying, it
is true; when in that way, false". An affirmation is true when its object holds
and false when it does not; a denial is true when its object does not hold and
false when it does. Stated as biconditionals, as a definition is. -/
def ThoughtTrueOrFalseByCompositionReading {Thought : Type u}
    (object : Thought → Prop) (Affirms Denies TrueT FalseT : Thought → Prop) : Prop :=
  ∀ t,
    (Affirms t → (TrueT t ↔ object t) ∧ (FalseT t ↔ ¬ object t)) ∧
      (Denies t → (TrueT t ↔ ¬ object t) ∧ (FalseT t ↔ object t))

/-- Every object of thought is affirmed or denied, *Metaphysics* IV.7, 1012a2-3,
reading B (universal), first half, as the sentence states it: "every object of
thought (πᾶν τὸ διανοητὸν καὶ νοητὸν), thought either affirms or denies". Whatever
is the object of some thought is the object of a thought that affirms or denies
it. This is the sourced reading (claim `ARIST-MET-1012A-THOUGHT-AFFIRMS-OR-DENIES-B`). -/
def ObjectOfThoughtAffirmedOrDeniedReading {Thought : Type u}
    (object : Thought → Prop) (Affirms Denies : Thought → Prop) : Prop :=
  ∀ t, ∃ t', (object t' ↔ object t) ∧ (Affirms t' ∨ Denies t')

/-- Thought affirms or denies every proposition: reading B's first half extended
from "every object of thought" to every proposition, each taken as a possible
object of thought. That extension is **not** attributed to Aristotle: it is the
formalization's own open premise (`STMT-THOUGHT-AFFIRMS-OR-DENIES-EVERY-PROPOSITION`,
no claim), which the bivalence analysis needs. It says that each proposition is
the object of an affirmation or denial, not yet that this is true or false. -/
def ThoughtAffirmsOrDeniesEveryPropositionReading {Thought : Type u}
    (object : Thought → Prop) (Affirms Denies : Thought → Prop) : Prop :=
  ∀ p : Prop, ∃ t, (object t ↔ p) ∧ (Affirms t ∨ Denies t)

/-- Affirming or denying thought is true or false, *Metaphysics* IV.7, 1012a2-4,
reading B (universal), second half, as the sentence states it: "whenever it is
true or false" read not as a condition but as saying that thought, in affirming
or denying, is thereby true or false. This is the sourced reading (claim
`ARIST-MET-1012A-EVERY-OBJECT-JUDGED-B`). -/
def AffirmingOrDenyingThoughtIsTrueOrFalseReading {Thought : Type u}
    (Affirms Denies TrueT FalseT : Thought → Prop) : Prop :=
  ∀ t, Affirms t ∨ Denies t → TrueT t ∨ FalseT t

/-- Every object of thought is judged truly or falsely, for every proposition:
bivalence for thought. It combines reading B's second half with the extension of
"every object of thought" to every proposition, and that extension is **not**
attributed to Aristotle: this is the formalization's own open premise
(`STMT-EVERY-OBJECT-OF-THOUGHT-JUDGED-TRULY-OR-FALSELY`, no claim). The result
`ARIST-MET-1012A-THOUGHT-BIVALENCE-IFF-EXCLUDED-MIDDLE` shows it is equivalent
to excluded middle given the other readings. -/
def EveryObjectOfThoughtJudgedTrulyOrFalselyReading {Thought : Type u}
    (object : Thought → Prop) (TrueT FalseT : Thought → Prop) : Prop :=
  ∀ p : Prop, ∃ t, (object t ↔ p) ∧ (TrueT t ∨ FalseT t)

/-- Conclusion of the thought argument on reading A: a thought that is true or
false settles its object, `object t ∨ ¬ object t`. No intermediate is left for a
thought that is true or false; nothing is said about objects no thought has settled. -/
def TruthAptThoughtDecidesItsObject {Thought : Type u}
    (object : Thought → Prop) (TrueT FalseT : Thought → Prop) : Prop :=
  ∀ t, TrueT t ∨ FalseT t → object t ∨ ¬ object t

/-- Reading B's bivalence of thought holds exactly when excluded middle does. -/
def ThoughtBivalenceIffExcludedMiddle {Thought : Type u}
    (object : Thought → Prop) (TrueT FalseT : Thought → Prop) : Prop :=
  EveryObjectOfThoughtJudgedTrulyOrFalselyReading object TrueT FalseT ↔
    TruthCore.Logic.ExcludedMiddle

end TruthCore.Greek.Aristotle.Metaphysics
