module

public import TruthCore.Teleonomy.DirectorRivalBoundary

@[expose] public section
namespace TruthCore.Results.Comparison.Teleonomy.DirectorRivalBoundary.ExactRival
open TruthCore.Teleonomy
open TruthCore.Teleonomy.DirectorRivalBoundary
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels
theorem exactRival {Being End : Type} (HasCognition Intelligent : Being → Prop)
    (TendsTo : Being → End → Prop) (Directs : Being → Being → End → Prop)
    (hWitness : UndirectedTendingWitness HasCognition Intelligent TendsTo Directs) :
    NotDirectorPrinciple HasCognition Intelligent TendsTo Directs := by
  intro hPrinciple
  obtain ⟨x, e, hNoCognition, hTends, hNoDirector⟩ := hWitness
  exact hNoDirector (hPrinciple x e hNoCognition hTends)
end TruthCore.Results.Comparison.Teleonomy.DirectorRivalBoundary.ExactRival
