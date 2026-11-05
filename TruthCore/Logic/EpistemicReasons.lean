module

@[expose] public section

/-!
Floor item F6 (#1007): there are epistemic reasons. Its rival is global
epistemic nihilism, held at full strength by Bart Streumer, *Unbelievable
Errors* (OUP 2017), as part of his global normative error theory: there are no
normative reasons of any kind, epistemic reasons included. Streumer grants that
we cannot believe this theory, and denies that this makes it false. Terence
Cuneo, *The Normative Web* (OUP 2007), argues from the parity of moral and
epistemic normativity. Neither text is pinned yet; the owner approved F6 on
the common-ground basis without a stating text (2026-11-05).

`Reason a p`: agent `a` has an epistemic reason to believe content `p`.
`Holds p`: content `p` is so. `nihilism` is a content whose holding is global
epistemic nihilism for this `Reason`.
-/

namespace TruthCore.Logic.EpistemicReasons

universe u v

/-- F6: some agent has an epistemic reason to believe some content. -/
def ThereAreEpistemicReasons {Agent : Sort u} {Content : Sort v}
    (Reason : Agent → Content → Prop) : Prop :=
  ∃ a p, Reason a p

/-- Global epistemic nihilism: no agent has an epistemic reason to believe
anything (Streumer's error theory, restricted to epistemic reasons). -/
def EpistemicNihilism {Agent : Sort u} {Content : Sort v}
    (Reason : Agent → Content → Prop) : Prop :=
  ∀ a p, ¬ Reason a p

/-- `nihilism` expresses global epistemic nihilism: it holds exactly when there
are no epistemic reasons. -/
def ExpressesNihilism {Agent : Sort u} {Content : Sort v}
    (Reason : Agent → Content → Prop) (Holds : Content → Prop) (nihilism : Content) : Prop :=
  Holds nihilism ↔ EpistemicNihilism Reason

/-- The owner's retorsion (#1007): if there are no epistemic reasons, then no
one has an epistemic reason to believe that there are none. -/
def NihilismSelfUndermining {Agent : Sort u} {Content : Sort v}
    (Reason : Agent → Content → Prop) (nihilism : Content) : Prop :=
  EpistemicNihilism Reason → ∀ a, ¬ Reason a nihilism

/-- The gap: self-undermining is not falsity. Some interpretation has a
content expressing nihilism that holds, while no one has a reason to believe
it. Streumer's position: true, but not believable with reason. -/
def NihilismConsistentAndUnbelievable : Prop :=
  ∃ (Agent Content : Type) (Reason : Agent → Content → Prop) (Holds : Content → Prop)
    (nihilism : Content),
    ExpressesNihilism Reason Holds nihilism ∧ Holds nihilism ∧ (∀ a, ¬ Reason a nihilism) ∧
      Nonempty Agent

end TruthCore.Logic.EpistemicReasons
