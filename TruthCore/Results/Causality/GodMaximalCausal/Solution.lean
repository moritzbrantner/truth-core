module

public import TruthCore.Causality.GodMaximalCausal

@[expose] public section

namespace TruthCore.Results.Causality.GodMaximalCausal
open TruthCore.Causality.GodMaximalCausal
open TruthCore.Case.Catholicism (GodIsMaximalInBeing)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Latin.Aquinas.SummaTheologiae (MoreSuchHasThePerfectionReading)
open TruthCore.Logic (ExcludedMiddle)

/-- God causes another's being, so is more in being than it and so has being;
anything more in being than God would be distinct from it and so exceeded by God,
against asymmetry. Conditional on six OPEN premises. -/
theorem godMaximalFromCausing {B R : Type} (IsGod : B → Prop) (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (hEM : ExcludedMiddle)
    (hCauses : GodCausesBeingOfAllOthers IsGod CausesIn esse)
    (hMore : CauseOfQualityInAnotherIsMoreSuchReading CausesIn MoreIn)
    (hHas : MoreSuchHasThePerfectionReading InAct MoreIn)
    (hAsym : MoreInIsAsymmetric MoreIn)
    (hOther : SomethingOtherThanGodExists IsGod) :
    GodIsMaximalInBeing IsGod InAct MoreIn esse := by
  intro g hg
  obtain ⟨y, hy⟩ := hOther g hg
  refine ⟨hHas esse g y (hMore g y esse (fun h => hy h.symm) (hCauses g y hg hy)), ?_⟩
  intro z hz
  rcases hEM (z = g) with hEq | hNe
  · subst hEq
    exact hAsym esse z z hz hz
  · exact hAsym esse g z (hMore g z esse (fun h => hNe h.symm) (hCauses g z hg hNe)) hz

theorem controls : TruthCore.Causality.GodMaximalCausal.Control.Certificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro g y hg hy
    exact ⟨hg, Bool.rec (motive := fun y => y ≠ g → y = false) (fun _ => rfl)
      (fun h => (h hg.symm).elim) y hy⟩
  · intro _ _ _ hxy hyx
    exact Bool.noConfusion (hxy.2.symm.trans hyx.1)
  · intro g hg
    exact ⟨false, fun h => Bool.noConfusion (h.trans hg)⟩
  · intro _ _ _ _ h
    exact h
  · intro _ _ _ _
    trivial
  · intro g hg
    exact ⟨trivial, fun _ h => Bool.noConfusion (h.2.symm.trans hg)⟩

end TruthCore.Results.Causality.GodMaximalCausal
