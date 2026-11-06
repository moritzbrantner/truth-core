module

public import TruthCore.Case.Catholicism.StageThree.ChurchDefinitions
public import TruthCore.Case.Catholicism.StageThree.DivineFounding

@[expose] public section

namespace TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Models

open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.ChurchDefinitions
open TruthCore.Case.Catholicism.StageThree.DivineFounding

/-- Four society objects permit a nonempty intersection with both extra
aspects; no actual society or jurisdiction is represented by these labels. -/
def societySig (visible : Bool × Bool → Prop) : Signature :=
  { modelSig True with
    Society := Bool × Bool
    catholicChurch := (true, true)
    Founded := fun _ _ => True
    VisibleWithAuthority := visible
    FoundedAsTeachingAuthority := fun _ _ => True
    DefinitivelyProposesAsRevealed := fun _ _ => True }

/-- Six exact extension controls, no Church identity or historical claim. -/
theorem criterionModels : ChurchCriterionModels := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨modelSig True, (fun _ => True), (fun _ => True),
      ⟨(), trivial, trivial⟩, (fun _ => Iff.rfl), (fun _ => Iff.rfl), ?_,
      ⟨(), trivial, trivial⟩⟩
    intro _
    constructor
    · intro _; exact ⟨trivial, trivial⟩
    · intro _; trivial
  · let σ : Signature := { modelSig True with VisibleWithAuthority := fun _ => False }
    refine ⟨σ, (fun _ => True), (fun _ => True),
      ⟨(), trivial, trivial⟩, (fun _ => Iff.rfl), ?_, ?_, ?_⟩
    · intro hVisible; exact (hVisible ()).1 trivial
    · intro hJoint; exact ((hJoint ()).1 trivial).1
    · intro hFounded; obtain ⟨_, _, hVisible⟩ := hFounded; exact hVisible
  · refine ⟨modelSig True, (fun _ => True), (fun _ => False),
      ⟨(), trivial, trivial⟩, (fun _ => Iff.rfl), ?_, ?_, ⟨(), trivial, trivial⟩⟩
    · intro hSpiritual; exact (hSpiritual ()).1 trivial
    · intro hJoint; exact ((hJoint ()).1 trivial).2
  · refine ⟨societySig (fun c => c.1 = true),
      (fun c => c.1 = true ∧ c.2 = true), (fun c => c.2 = true),
      ⟨(true, true), trivial, rfl, rfl⟩, (fun _ => Iff.rfl), ?_, ?_,
      ⟨(true, true), trivial, rfl⟩⟩
    · intro hVisible
      have h : false = true := ((hVisible (true, false)).2 rfl).2
      cases h
    · intro hSpiritual
      have h : false = true := ((hSpiritual (false, true)).2 rfl).1
      cases h
  · refine ⟨societySig (fun _ => True), (fun c => c.1 = true), (fun _ => False),
      ⟨(true, true), trivial, rfl⟩, ⟨?_, ?_, ?_⟩,
      ⟨(true, true), trivial, trivial⟩⟩
    · intro hVisible
      have h : false = true := (hVisible (false, false)).2 trivial
      cases h
    · intro hSpiritual; exact (hSpiritual (true, true)).1 rfl
    · intro hJoint; exact ((hJoint (true, true)).1 rfl).2
  · refine ⟨societySig (fun _ => False), (fun c => c.1 = true), (fun _ => True),
      ⟨(true, true), trivial, rfl⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro hVisible; exact (hVisible (true, true)).1 rfl
    · intro hSpiritual
      have h : false = true := (hSpiritual (false, false)).2 trivial
      cases h
    · intro hJoint; exact ((hJoint (true, true)).1 rfl).1
    · intro hFounded; obtain ⟨_, _, hVisible⟩ := hFounded; exact hVisible

end TruthCore.Results.Case.Catholicism.StageThree.ChurchDefinitions.Models
