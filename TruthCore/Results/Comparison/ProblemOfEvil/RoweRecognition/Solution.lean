module
public import TruthCore.English.Rowe.Recognition
public import TruthCore.Results.Comparison.ProblemOfEvil.RoweDeductiveCore.Solution
public import TruthCore.Results.Comparison.ProblemOfEvil.RoweApparentCompatibility.Solution

@[expose] public section
namespace TruthCore.Results.Comparison.ProblemOfEvil.RoweRecognition
open TruthCore.English.Rowe TruthCore.English.Rowe.Recognition

theorem recognitionToActual (s : Sig) (survey : Survey s)
    (hCoverage : Covered s survey) (hComplete : Complete s survey)
    (hApparent : ApparentlyPointlessSuffering s) : GratuitousSufferingReading s := by
  obtain ⟨e, hOccurs, hIntense, h⟩ := hApparent
  refine ⟨e, hOccurs, hIntense, ?_⟩
  intro b hKnows hPower
  obtain ⟨hPrevent, hNone⟩ := h b hKnows hPower
  refine ⟨hPrevent, ?_⟩
  rintro ⟨o, hCost, hBlocking⟩
  exact hNone ⟨o, hCost,
    hComplete b e o hKnows hPower hOccurs hIntense
      (hCoverage b e o hKnows hPower hOccurs hIntense hCost hBlocking) hCost hBlocking,
    hBlocking⟩

theorem recognitionExcludesTheism (s : Sig) (survey : Survey s)
    (hCoverage : Covered s survey) (hComplete : Complete s survey)
    (hApparent : ApparentlyPointlessSuffering s)
    (hPermission : PermissionConstraintReading s) : NoTheisticBeing s := by
  exact RoweDeductiveCore.roweDeductiveCore s
    (recognitionToActual s survey hCoverage hComplete hApparent) hPermission

/-- Actual suffering and a hypothetical omniscient omnipotent preventer, with
no actual costs. WhollyGood is empty; permission is intentionally not assumed. -/
def clearModel : Sig where
  Being := Unit
  Event := Unit
  Outcome := Unit
  Omniscient _ := True
  Omnipotent _ := True
  WhollyGood _ := False
  Occurs _ := True
  IntenseSuffering _ := True
  CanPrevent _ _ := True
  Cost _ _ _ := False
  GreaterGood _ _ := True
  EqualOrWorseEvil _ _ := False
  RecognizesCost _ _ _ := False

theorem nonvacuity : Nonvacuity := by
  refine ⟨clearModel, fun _ _ => [], ?_, ?_, ?_, ?_, ⟨(), trivial, trivial⟩⟩
  · intro b e o _ _ _ _ hCost
    exact False.elim hCost
  · intro b e o _ _ _ _ _ hCost
    exact False.elim hCost
  · refine ⟨(), trivial, trivial, ?_⟩
    intro b _ _
    exact ⟨trivial, fun ⟨_, hCost, _⟩ => hCost⟩
  · refine ⟨(), trivial, trivial, ?_⟩
    intro b _ _
    exact ⟨trivial, fun ⟨_, hCost, _⟩ => hCost⟩

theorem omissionControls : OmissionControls := by
  -- Use the concrete model, rather than the existential certificate's witness.
  have hp' : PermissionConstraintReading RoweApparentCompatibility.model := by
    intro b e hk _ ho _ _
    exact ⟨true, ⟨hk, ho, rfl⟩, Or.inl ⟨rfl, ho⟩⟩
  have ha' : ApparentlyPointlessSuffering RoweApparentCompatibility.model := by
    refine ⟨false, rfl, rfl, ?_⟩
    intro b hk _
    refine ⟨⟨hk, rfl⟩, ?_⟩
    rintro ⟨o, hc, hr, _⟩
    exact Bool.noConfusion (hc.1.symm.trans hr.1)
  have ht' : TheisticBeingExists RoweApparentCompatibility.model := ⟨true, rfl, rfl, rfl⟩
  constructor
  · refine ⟨RoweApparentCompatibility.model, fun _ _ => [], ?_, ?_, hp', ha', ht'⟩
    · intro b e o _ _ _ _ hm
      exact False.elim (List.not_mem_nil hm)
    · intro hc
      have hm := hc true false true rfl rfl rfl rfl ⟨rfl, rfl, rfl⟩ (Or.inl ⟨rfl, rfl⟩)
      exact List.not_mem_nil hm
  · refine ⟨RoweApparentCompatibility.model, fun _ _ => [true], ?_, ?_, hp', ha', ht'⟩
    · intro b e o _ _ _ _ hc _
      exact hc.2.2 ▸ List.Mem.head []
    · intro hc
      have hr := hc true false true rfl rfl rfl rfl (List.Mem.head []) ⟨rfl, rfl, rfl⟩ (Or.inl ⟨rfl, rfl⟩)
      exact Bool.noConfusion hr.1
end TruthCore.Results.Comparison.ProblemOfEvil.RoweRecognition
