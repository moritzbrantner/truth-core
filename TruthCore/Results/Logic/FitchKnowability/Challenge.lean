import TruthCore.Logic.FitchKnowability

namespace TruthCore.Results.Logic.FitchKnowability
open TruthCore.Logic.FitchKnowability

theorem mooreUnknowable {W : Type} (c : Context W) (p : W → Prop)
    (laws : RelevantLaws c p) : MooreUnknowable c p := by sorry

theorem doubleNegatedKnowledge {W : Type} (c : Context W) (p : W → Prop)
    (laws : RelevantLaws c p) (hInstance : MooreInstance c p) :
    DoubleNegatedKnowledge c p := by sorry

theorem stabilityUpgrade {W : Type} (c : Context W) (p : W → Prop)
    (double : DoubleNegatedKnowledge c p) (stable : KnowledgeStable c p) :
    TruthKnown c p := by sorry

theorem restrictedInstance {W : Type} (c : Context W) (C : (W → Prop) → Prop)
    (p : W → Prop) (knowable : RestrictedKnowability c C)
    (admissible : MooreAdmissible c C p) : MooreInstance c p := by sorry

theorem relevantFromGlobal {W : Type} (c : Context W) (p : W → Prop)
    (laws : GlobalLaws c) : RelevantLaws c p := by sorry

theorem restrictedSurvivor : RestrictedSurvivor := by sorry

end TruthCore.Results.Logic.FitchKnowability
