import TruthCore.Greek.Aristotle.Physics.Typed.Motion
namespace TruthCore.Results.Aristotle.Physics.Typed.LocalRegressFromPerSeRegress
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- No infinite descending chain under a well-founded relation: if every being is
accessible under `R`, no sequence steps down `R` forever. -/
theorem noDescendingChain {Being : Type} (R : Being → Being → Prop)
    (hAcc : ∀ x, Acc R x) : ¬ ∃ c : Nat → Being, ∀ n, R (c (n + 1)) (c n) := by
  rintro ⟨c, hc⟩
  have key : ∀ x, Acc R x → ∀ n, c n = x → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro n hn
      exact ih (c (n + 1)) (hn ▸ hc n) (n + 1) rfl
  exact key (c 0) (hAcc (c 0)) 0 rfl

/-- *Physics* VII.1's restricted regress follows from the *prima via*'s regress
premise. A link of VII.1's chain is a mover other than the moved thing that moves
it and is itself being moved; by the *prima via*'s second-movers premise it is a
per se link, and the per se series has no infinite descent. -/
theorem localRegressFromPerSeRegress {Being : Type} {Respect : Type}
    (IsLocal : Respect → Prop)
    (MovedIn : Being → Respect → Prop)
    (MovesIn : Being → Being → Respect → Prop)
    (MovesPrimarily : Being → Being → Prop)
    (MovesAsMoved : Being → Being → Prop)
    (hPerSe : SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved)
    (hRegress : NoInfinitePerSeMoverSeriesReading MovesAsMoved) :
    NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily := by
  -- INF-ARIST-PHYS-VII-1-LOCAL-REGRESS-FROM-PER-SE-REGRESS
  rintro ⟨c, hChain⟩
  apply noDescendingChain MovesAsMoved hRegress
  refine ⟨c, fun n => ?_⟩
  obtain ⟨hNe, _, ⟨r, _, hMoves⟩, ⟨r', _, hMoved⟩⟩ := hChain n
  exact hPerSe (c (n + 1)) (c n) r hNe hMoves ⟨r', hMoved⟩

/-- Both premises are needed. Every model is the successor chain on `Nat`, each
number moving its predecessor locally and primarily and being moved: without the
second-movers premise no link is per se; without the regress premise the per se
series is the successor relation itself. -/
theorem premisesNeeded :
    (¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesPrimarily MovesAsMoved : Being → Being → Prop),
      NoInfinitePerSeMoverSeriesReading MovesAsMoved →
      NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily) ∧
    (¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesPrimarily MovesAsMoved : Being → Being → Prop),
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily) := by
  have succChain : ∀ n, LocalMovedMoverLink (fun _ : Unit => True) (fun (_ : Nat) _ => True)
      (fun y x (_ : Unit) => y = x + 1) (fun y x => y = x + 1) (n + 1) n :=
    fun n => ⟨Nat.succ_ne_self n, rfl, ⟨(), trivial, rfl⟩, ⟨(), trivial, trivial⟩⟩
  refine ⟨?_, ?_⟩
  · intro h
    exact h Nat Unit (fun _ => True) (fun _ _ => True) (fun y x _ => y = x + 1)
      (fun y x => y = x + 1) (fun _ _ => False)
      (fun x => Acc.intro x (fun _ hf => hf.elim)) ⟨fun n => n, succChain⟩
  · intro h
    exact h Nat Unit (fun _ => True) (fun _ _ => True) (fun y x _ => y = x + 1)
      (fun y x => y = x + 1) (fun y x => y = x + 1)
      (fun _ _ _ _ hMoves _ => hMoves) ⟨fun n => n, succChain⟩

/-- The restricted regress is strictly weaker than the per se regress, even
granted the second-movers premise: when no respect is local, there is no local
chain at all, while the per se series is the infinite successor relation. So
VII.1's conclusion cannot stand in for the *prima via*'s regress premise. -/
theorem restrictedRegressIsWeaker :
    ¬ ∀ (Being Respect : Type) (IsLocal : Respect → Prop) (MovedIn : Being → Respect → Prop)
        (MovesIn : Being → Being → Respect → Prop) (MovesPrimarily MovesAsMoved : Being → Being → Prop),
      SecondMoversMoveOnlyAsMovedReading MovedIn MovesIn MovesAsMoved →
      NoInfiniteLocalMovedMoverChainReading IsLocal MovedIn MovesIn MovesPrimarily →
      NoInfinitePerSeMoverSeriesReading MovesAsMoved := by
  intro h
  have hAcc := h Nat Unit (fun _ => False) (fun _ _ => True) (fun y x _ => y = x + 1)
    (fun y x => y = x + 1) (fun y x => y = x + 1)
    (fun _ _ _ _ hMoves _ => hMoves)
    (fun ⟨c, hc⟩ => by obtain ⟨_, _, ⟨_, hl, _⟩, _⟩ := hc 0; exact hl)
  exact noDescendingChain (fun y x : Nat => y = x + 1) hAcc ⟨fun n => n, fun _ => rfl⟩

end TruthCore.Results.Aristotle.Physics.Typed.LocalRegressFromPerSeRegress
