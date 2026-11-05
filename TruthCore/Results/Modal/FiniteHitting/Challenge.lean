import TruthCore.Modal.FiniteHitting.Vocabulary

namespace TruthCore.Results.Modal.FiniteHitting
open TruthCore.Modal.FiniteHitting

theorem checks : Package := by sorry

theorem laws : TruthCore.Modal.FiniteHitting.Laws := by sorry

theorem compactLaws : CompactLaws := by sorry

theorem weakening : Weakening := by sorry

theorem tailBoundary : TailBoundary := by sorry

theorem omissionControls : OmissionControls := by sorry

theorem strictAmalgamation : TruthCore.Models.PopulationClosureSeparation.Separation := by sorry

theorem cores : Cores := by sorry

theorem tailProfiles : TailProfiles := by sorry

open TruthCore.Modal
open TruthCore.Modal.S5Research (Universal)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)

theorem hittingCore (W I : Type) (F : Frame W) (p : ExistsAt W I) (w : W)
    (hu : Universal F) (hh : Hitting p) (ha : AbsenceAmalgamation F p w)
    (hn : NoNecessary F p w) : TruthCore.Logic.ConfigurationFalse := by sorry

theorem finiteWorldCore (W I : Type) (F : Frame W) (p : ExistsAt W I) (w : W)
    (hu : Universal F) (hp : DeDicto F p w) (ha : AbsenceAmalgamation F p w)
    (ho : OneFinite p) (hn : NoNecessary F p w) : TruthCore.Logic.ConfigurationFalse := by sorry
end TruthCore.Results.Modal.FiniteHitting
