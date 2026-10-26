import TruthCore.Causality.PowerExistenceBoundary

namespace TruthCore.Results.Causality.PowerExistenceBoundary
open TruthCore.Causality
open TruthCore.Causality.PowerExistenceBoundary

/-- A narrowly sufficient bridge, made explicit rather than hidden in the
meaning of "unborrowed": if every actual conserver of this bearer's esse
necessarily transmits *this very power in this respect*, an unborrowed
source has no external conserver in the model. The countermodel below shows
that the transmission premise is not entailed by finite power grounding.
Its metaphysical acceptability remains open. -/
theorem originalPowerBlocksEsseSupportIfItTransmits
    (m : Profile W B) (w : W) (x : B)
    (hConservationTransmits : ∀ y,
      m.supportsEsse w y x → m.transmitsPower w y x)
    (hOriginal : UnborrowedPowerAt m w x) :
    ¬ExternallySupportedAt m w x := by
  rintro ⟨y, _, _, hSupport⟩
  exact hOriginal.2.2 y (hConservationTransmits y hSupport)

theorem powerExistenceBoundary : Boundary := by
  constructor
  · let m : Profile Bool Role := {
      ontic := {
        frame := { access := fun _ _ => True }
        ExistsAt := fun w x => match x with
          | .source | .effect => w = false
          | .conserver => True
        Causes := fun w y x =>
          (w = false ∧ y = .source ∧ x = .effect) ∨
          (w = false ∧ y = .conserver ∧ x = .source) }
      transmitsPower := fun w y x => w = false ∧ y = .source ∧ x = .effect
      supportsEsse := fun w y x => w = false ∧ y = .conserver ∧ x = .source
      intrinsicPower := fun w x => w = false ∧ x = .source
      properPartOf := fun _ _ => False }
    refine ⟨m, (fun _ _ => True.intro), ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro w y x h
        rcases h with ⟨hw, hy, hx⟩
        subst w
        subst y
        subst x
        exact ⟨rfl, rfl⟩
      constructor
      · intro w y x h
        rcases h with ⟨hw, hy, hx⟩
        subst w
        subst y
        subst x
        exact ⟨True.intro, rfl⟩
      constructor
      · intro w y x h
        exact h.elim
      constructor
      · intro w y x h
        exact Or.inl h
      · intro w y x h
        exact Or.inr h
    · refine ⟨rfl, ⟨rfl, rfl⟩, ?_⟩
      intro y h
      exact Role.noConfusion h.2.2
    · apply FinitelyGroundedPower.borrowed
      · exact ⟨rfl, rfl, rfl⟩
      · apply FinitelyGroundedPower.intrinsic
        exact ⟨rfl, rfl⟩
    · exact ⟨.conserver, True.intro, by decide, ⟨rfl, rfl, rfl⟩⟩
    · refine ⟨rfl, true, True.intro, ?_⟩
      exact Bool.noConfusion
  · let m : Profile Bool Role := {
      ontic := {
        frame := { access := fun _ _ => True }
        ExistsAt := fun _ _ => True
        Causes := fun _ y x => y = .source ∧ x = .effect }
      transmitsPower := fun _ y x => y = .source ∧ x = .effect
      supportsEsse := fun _ _ _ => False
      intrinsicPower := fun _ x => x = .source
      properPartOf := fun y x => y = .conserver ∧ x = .source }
    refine ⟨m, (fun _ _ => True.intro), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro w y x _
        exact ⟨True.intro, True.intro⟩
      constructor
      · intro w y x h
        exact h.elim
      constructor
      · intro w y x _
        exact ⟨True.intro, True.intro⟩
      constructor
      · intro w y x h
        exact h
      · intro w y x h
        exact h.elim
    · refine ⟨True.intro, rfl, ?_⟩
      intro y h
      exact Role.noConfusion h.2
    · apply FinitelyGroundedPower.borrowed
      · exact ⟨rfl, rfl⟩
      · apply FinitelyGroundedPower.intrinsic
        rfl
    · rintro ⟨y, _, _, h⟩
      exact h.elim
    · intro _ _
      exact True.intro
    · exact ⟨.conserver, by decide, ⟨rfl, rfl⟩⟩

end TruthCore.Results.Causality.PowerExistenceBoundary
