import Mathlib.Data.Fintype.Card
import Mathlib.Order.WellFounded
import TruthCore.Results.Modern.Fine.PlgDerivedRules.Solution

namespace TruthCore.Results.Modern.Fine.StrictGroundAcyclic
open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Results.Modern.Fine.PlgDerivedRules

/-- In a consistent `S`, no atom derivably strictly grounds itself:
Non-Circularity would derive every sequent. -/
theorem strictIrrefl {Atom : Type} {S : Set (Sequent Atom)} (hCons : Consistent S)
    (A : Atom) : ¬ StrictlyGrounds S A A := by
  intro hAA
  obtain ⟨s, hs⟩ := hCons
  exact hs (Derivable.nonCircularity s hAA)

/-- A finite chain of derivable strict partial grounds collapses, by the derived
Transitivity `(≺/≺)` (`PLG-DERIVED-RULES`), to one derivable strict partial
ground. -/
theorem transGen_strict {Atom : Type} {S : Set (Sequent Atom)} {A C : Atom}
    (h : Relation.TransGen (StrictlyGrounds S) A C) : StrictlyGrounds S A C := by
  induction h with
  | single hAB => exact hAB
  | tail _ hBC ih => exact strictTrans ih hBC

/-- From a PLG-consistent set of sequents, derivable strict partial ground has
no cycles, is not reversed by weak partial ground, and is well-founded when
there are finitely many atoms. The finite case is Mathlib's
`Finite.wellFounded_of_trans_of_irrefl`, whose proof is classical. -/
theorem consistentStrictGroundAcyclic : ConsistentStrictGroundAcyclic := by
  intro Atom S hCons
  refine ⟨fun A hCycle => strictIrrefl hCons A (transGen_strict hCycle), ?_, ?_⟩
  · intro A B hAB hBA
    exact strictIrrefl hCons A (Derivable.transStrictWeak hAB hBA)
  · intro hFin
    have : IsTrans Atom (StrictlyGrounds S) := ⟨fun _ _ _ => strictTrans⟩
    have : Std.Irrefl (StrictlyGrounds S) := ⟨strictIrrefl hCons⟩
    exact Finite.wellFounded_of_trans_of_irrefl _

end TruthCore.Results.Modern.Fine.StrictGroundAcyclic
