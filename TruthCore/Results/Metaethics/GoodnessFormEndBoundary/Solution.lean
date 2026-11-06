module

public import TruthCore.Metaethics.GoodnessFormEnd
public import TruthCore.Results.Logic.CorrectionCriterion.Solution

@[expose] public section
namespace TruthCore.Results.Metaethics.GoodnessFormEndBoundary
open TruthCore.Metaethics.GoodnessFormEnd
open TruthCore.Logic.CorrectionCriterion
open TruthCore.Latin.Aquinas.SummaTheologiae

private theorem artifactThesis : DueActualityThesis artifact := by
  intro x p
  exact Iff.rfl

theorem routeBridge : ∀ f : Frame, DueActualityThesis f →
    (GoodnessIsActualityReading f.GoodIn f.Has ↔ AllActualitiesDue f) := by
  intro f hThesis
  constructor
  · intro hCoext x p hActual
    exact ((hThesis x p).mp ((hCoext x p).mpr hActual)).1
  · intro hDue x p
    constructor
    · intro hGood
      exact ((hThesis x p).mp hGood).2
    · intro hActual
      exact (hThesis x p).mpr ⟨hDue x p hActual, hActual⟩

private theorem rejectsCells : ∀ f : Frame, DueActualityThesis f →
    ¬ SurplusGood f ∧ ¬ OmittedDueGood f := by
  intro f h
  constructor
  · rintro ⟨x, p, hGood, hNot⟩
    exact hNot ((h x p).mp hGood)
  · rintro ⟨x, p, hDue, hNot⟩
    exact hNot ((h x p).mpr hDue)

private theorem surplusWitness : SurplusGood surplusArtifact := by
  exact ⟨.knife, .mass, trivial, fun h => h.1⟩

private theorem noOmissionSurplus : ¬ OmittedDueGood surplusArtifact := by
  rintro ⟨x, p, hDue, hNot⟩
  exact hNot hDue.2

private theorem omissionWitness : OmittedDueGood omissionArtifact := by
  refine ⟨.knife, .existence, ⟨trivial, trivial⟩, ?_⟩
  intro h
  cases h.1

private theorem noSurplusOmission : ¬ SurplusGood omissionArtifact := by
  rintro ⟨x, p, hGood, hNot⟩
  exact hNot hGood.2

private theorem mixedSurplus : SurplusGood mixedArtifact := by
  exact ⟨.knife, .mass, ⟨rfl, rfl⟩, fun h => h.1⟩

private theorem mixedOmission : OmittedDueGood mixedArtifact := by
  refine ⟨.knife, .existence, ⟨trivial, trivial⟩, ?_⟩
  intro h
  cases h.2

private theorem artifactNotCoext :
    ¬ GoodnessIsActualityReading artifact.GoodIn artifact.Has := by
  intro h
  exact ((h .knife .mass).mpr trivial).1

private theorem missingUltimate :
    UltimateDuePerfectionRequiredReading artifact.GoodSimply
      (fun x => artifact.Has x (artifact.ultimate x)) := by
  intro x hMissing hGood
  cases x with
  | knife => cases hGood
  | counterweight => exact hMissing trivial

private theorem coarseFails :
    ¬ AdmitsCriterion coarse (fun a => artifact.GoodIn a.1 a.2) := by
  intro h
  have inv := (TruthCore.Results.Logic.CorrectionCriterion.characterization.1
    (Bearer × Perfection) (Unit × Perfection) coarse
    (fun a => artifact.GoodIn a.1 a.2)).mp h
  have impossible := (inv (.knife, .mass) (.counterweight, .mass) rfl).mpr
    (show artifact.GoodIn .counterweight .mass from ⟨trivial, trivial⟩)
  exact impossible.1

private theorem enrichedSucceeds :
    AdmitsCriterion formSensitive (fun a => artifact.GoodIn a.1 a.2) := by
  refine ⟨(fun data => artifactDue data.1 data.2.1 data.2.2 ∧
    artifactHas .knife data.2.2), ?_⟩
  intro a
  exact Iff.rfl

private theorem featureBoundary : FeatureCriterionBoundary := by
  intro f observe
  exact TruthCore.Results.Logic.CorrectionCriterion.characterization.1 _ _ observe _

private theorem identityNotForced :
    ∃ p : PropertyPresentation artifact,
      DueActualityThesis artifact ∧ ¬ PropertyIdentity p := by
  let presentation : PropertyPresentation artifact :=
    { Property := Bool
      denotes := fun _ => artifact.GoodIn
      good := false
      dueActual := true
      goodMeaning := fun _ _ => Iff.rfl
      dueMeaning := fun _ _ => Iff.rfl }
  refine ⟨presentation, artifactThesis, ?_⟩
  intro h
  change false = true at h
  cases h

private theorem rivalOccupancy : RivalOccupancy := by
  refine ⟨?_, ?_, ?_, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_, ?_⟩
  · rintro ⟨x, p⟩ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨trivial, trivial⟩
  · rintro ⟨x, p⟩ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> trivial
  · rintro ⟨x, p⟩ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨rfl, trivial, trivial⟩
  · intro _ a
    exact Iff.rfl
  · intro _ a
    exact Iff.rfl

theorem namedControls : NamedSpaceControls := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro d hd
      cases d with
      | due => exact Or.inl rfl
      | feature => exact Or.inr (Or.inl rfl)
      | approval => exact Or.inr (Or.inr rfl)
      | other => exact False.elim (hd rfl)
    · refine ⟨.due, ?_, ?_⟩
      · intro h
        cases h
      · intro x p
        exact Iff.rfl
    · intro h
      exact ((h .knife .mass).mpr trivial).1
    · intro h
      have bad := (h .knife .existence).mp (show artifact.GoodIn .knife .existence from ⟨trivial, trivial⟩)
      cases bad.1
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨.other, trivial, ?_⟩
      rintro (h | h | h) <;> cases h
    · exact ⟨.other, trivial, fun _ _ => Iff.rfl⟩
    · intro h
      have bad := (h .counterweight .mass).mpr trivial
      cases bad.1
    · intro h
      have bad := (h .counterweight .mass).mpr ⟨rfl, trivial, trivial⟩
      cases bad.1
    · intro h
      exact ((h .knife .mass).mp ⟨rfl, rfl⟩).1

/-- Named finite witnesses preserve every advertised property in the type. -/
theorem boundaries : BoundaryCertificate := by
  refine ⟨routeBridge, rejectsCells, artifactThesis, surplusWitness,
    noOmissionSurplus, omissionWitness, noSurplusOmission, mixedSurplus,
    mixedOmission, artifactNotCoext, ?_, ?_, missingUltimate, coarseFails,
    enrichedSucceeds, featureBoundary, identityNotForced, rivalOccupancy, namedControls⟩
  · intro x p
    exact Iff.rfl
  · exact ⟨⟨trivial, trivial⟩, trivial, id, by intro h; cases h⟩

end TruthCore.Results.Metaethics.GoodnessFormEndBoundary
