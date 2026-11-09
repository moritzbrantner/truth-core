module

public import TruthCore.Explanation.AutonomousGroundConcrete
public import TruthCore.Results.Explanation.AutonomousGroundNecessity.Solution

@[expose] public section

namespace TruthCore.Results.Explanation.AutonomousGroundConcrete
open TruthCore.Explanation.AutonomousGroundConcrete
open TruthCore.Explanation.AutonomousGroundNecessity
open TruthCore.Explanation.ExistenceIngredient
open TruthCore.Explanation.PSRStrength (Arena)
open TruthCore.Causality.JointGroups
open TruthCore.Causality.BruteFoundationBoundary

/-- Assembly only: reuse sameTarget on the supplied Profile's exact ontology
and concrete predicate; the witness is the original target, never a replacement. -/
theorem necessaryConcrete {W B O G : Type} (m : Profile W B)
    (holds : W → Fact B O → Prop) (explains : W → Fact B O → Fact B O → Prop)
    (conjunct : Fact B O → Fact B O → Prop) (exist : B → Fact B O)
    (h : Groups (Fact B O) G) (autonomous : Fact B O → Prop) (w : W) (b : B)
    (hActual : ActualConcreteTargetAt ⟨m.ontic, holds, exist, explains, conjunct⟩ m.concrete w b)
    (hGround : AutonomousFullGround h autonomous b)
    (hAutonomous : AutonomousFactsNecessaryAt ⟨m.ontic, holds, exist, explains, conjunct⟩ autonomous w)
    (hNecessitates : WholeGroundNecessitatesTargetAt ⟨m.ontic, holds, exist, explains, conjunct⟩ h w b)
    (hCoherent : PositiveTargetCoherent ⟨m.ontic, holds, exist, explains, conjunct⟩ b) :
    NecessaryConcreteAt m w := by
  exact ⟨b, TruthCore.Results.Explanation.AutonomousGroundNecessity.sameTarget
    ⟨m.ontic, holds, exist, explains, conjunct⟩ h autonomous m.concrete w b
    hActual hGround hAutonomous hNecessitates hCoherent⟩

/-- Populated same-model compatibility certificate, not metaphysical possibility. -/
theorem certificate : TruthCore.Explanation.AutonomousGroundConcrete.Certificate := by
  have hActual : ActualConcreteTargetAt arena model.concrete false false :=
    ⟨True.intro, Or.inl rfl⟩
  have hGround : AutonomousFullGround ground autonomous false := by
    refine ⟨(), True.intro, rfl, ?_⟩
    intro f hf
    exact hf.elim (fun he => he) False.elim
  have hAutonomous : AutonomousFactsNecessaryAt arena autonomous false := by
    intro f hf v _
    change f = other () at hf
    subst f
    exact True.intro
  have hNecessitates : WholeGroundNecessitatesTargetAt arena ground false false := by
    intro _ _ _ _ _ _
    exact Or.inl rfl
  have hCoherent : PositiveTargetCoherent arena false := ⟨rfl, fun _ => Iff.rfl⟩
  refine ⟨hActual, hGround, hAutonomous, hNecessitates, hCoherent, ?_, ?_, ?_, ?_, ?_⟩
  · exact necessaryConcrete model arena.holds arena.explains arena.conjunct arena.exist
      ground autonomous false false hActual hGround hAutonomous hNecessitates hCoherent
  · intro hi
    obtain ⟨f, hf, he⟩ := hi () True.intro rfl
    have hf' : f = other () := hf.elim (fun he => he) False.elim
    subst f
    exact he
  · exact ⟨other (), Or.inl rfl⟩
  · refine ⟨True.intro, Or.inr rfl, true, True.intro, ?_⟩
    intro ht
    rcases ht with ht | ht <;> cases ht
  · intro w
    exact ⟨false, True.intro, Or.inl rfl⟩

end TruthCore.Results.Explanation.AutonomousGroundConcrete
