import TruthCore.Modern.Fine.PureLogicOfGround

namespace TruthCore.Results.Modern.Fine.PlgDerivedRules
open TruthCore.Modern.Fine.PureLogicOfGround
open Sequent

/-- Transitivity `(≺/≺)`, as Fine derives it (p. 6): weaken the first premise
by Subsumption `(≺/≼)`, then apply Transitivity `(≼/≺)`. -/
theorem strictTrans {Atom : Type} {S : Set (Sequent Atom)} {A B C : Atom}
    (hAB : StrictlyGrounds S A B) (hBC : StrictlyGrounds S B C) :
    StrictlyGrounds S A C :=
  Derivable.transWeakStrict (Derivable.subsumptionStrictPartial hAB) hBC

/-- Amalgamation `(≤)`, as Fine derives it (p. 7): cut the premises against
the identity `C ≤ C`, listed once per premise. -/
theorem amalgamateWeak {Atom : Type} {S : Set (Sequent Atom)} {ι : Type}
    [Nonempty ι] (Δ : ι → Set Atom) (C : Atom)
    (h : ∀ i, Derivable S (weakFull (Δ i) C)) :
    Derivable S (weakFull (⋃ i, Δ i) C) := by
  have hId : Derivable S (weakFull (Set.range fun _ : ι => C) C) := by
    rw [Set.range_const]
    exact Derivable.identity C
  exact Derivable.cut (fun _ => C) Δ h hId

/-- Amalgamation `(<)`, as Fine derives it (p. 7): each antecedent is a strict
partial ground by Subsumption `(</≺)`, the weakened premises amalgamate, and
Reverse Subsumption makes the amalgam strict. -/
theorem amalgamateStrict {Atom : Type} {S : Set (Sequent Atom)} {ι : Type}
    [Nonempty ι] (Δ : ι → Set Atom) (C : Atom)
    (h : ∀ i, Derivable S (strictFull (Δ i) C)) :
    Derivable S (strictFull (⋃ i, Δ i) C) := by
  refine Derivable.reverseSubsumption
    (amalgamateWeak Δ C fun i => Derivable.subsumptionStrictFull (h i)) ?_
  intro A hA
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hA
  exact Derivable.subsumptionStrictFullPartial (h i) hi

/-- Fine's Transitivity `(≺/≺)` and both Amalgamation rules (nonempty families)
are derivable in PLG. -/
theorem plgDerivedRules : PlgDerivedRules := by
  intro Atom S
  refine ⟨fun _ _ _ => strictTrans, ?_, ?_⟩
  · intro ι _ Δ C h
    exact amalgamateWeak Δ C h
  · intro ι _ Δ C h
    exact amalgamateStrict Δ C h

end TruthCore.Results.Modern.Fine.PlgDerivedRules
