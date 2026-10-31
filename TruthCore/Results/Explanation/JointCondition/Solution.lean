import TruthCore.Explanation.JointCondition

namespace TruthCore.Results.Explanation.JointCondition
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.JointCondition

theorem contingent {W B F : Type} (A : Arena W B F) (S : Set F) (w : W)
    (hActual : JointTrue A S w) (hMember : ContingentMember A S w) :
    JointContingent A S w := by
  rcases hMember with ⟨f, hf, _, v, hv, hAbsent⟩
  exact ⟨hActual, v, hv, fun hJoint => hAbsent (hJoint f hf)⟩

theorem necessityEquivalence : NecessityEquivalence := by
  intro W B F A S w
  constructor
  · intro h f hf v hv
    exact h v hv f hf
  · intro h v hv f hf
    exact h f hf v hv

theorem mixedCertificate : MixedCertificate := by
  have hc : Contingent (ground false) false GroundFact.choice := by
    refine ⟨rfl, true, trivial, ?_⟩
    intro h
    cases h
  have ha : JointTrue (ground false) {GroundFact.ground, GroundFact.choice} false := by
    intro f hf
    have hCases : f = GroundFact.ground ∨ f = GroundFact.choice := hf
    rcases hCases with rfl | rfl
    · trivial
    · rfl
  exact ⟨fun _ => trivial, hc,
    contingent (ground false) {GroundFact.ground, GroundFact.choice} false ha
      ⟨GroundFact.choice, Or.inr rfl, hc⟩,
    GroundFact.ground, trivial, fun _ _ => trivial⟩

end TruthCore.Results.Explanation.JointCondition
