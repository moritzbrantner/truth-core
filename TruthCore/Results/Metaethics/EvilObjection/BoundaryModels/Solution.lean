module

public import TruthCore.Metaethics.EvilObjection
public import TruthCore.Results.Metaethics.EvilObjection.InternalChallenge.Solution
public import TruthCore.Results.Comparison.ProblemOfEvil.RoweApparentCompatibility.Solution

@[expose] public section

namespace TruthCore.Results.Metaethics.EvilObjection.BoundaryModels

open TruthCore.Metaethics.EvilObjection TruthCore.English.OConnor TruthCore.English.Rowe

inductive Utterance | moralEvil | suffering | internal

/-- A moral utterance, a descriptive suffering report and a report of a target
conditional have distinct roles. Positive disapproval and the internal report's
truth are independent inputs, not silently built into truthlessness. -/
def critic (internalTrue protests : Prop) : Critic where
  Sentence := Utterance
  SaysBad φ := match φ with | .moralEvil => True | .suffering => False | .internal => False
  Moral φ := match φ with | .moralEvil => True | .suffering => False | .internal => False
  TruthApt φ := match φ with | .moralEvil => False | .suffering => True | .internal => True
  Holds φ := match φ with | .moralEvil => False | .suffering => True | .internal => internalTrue
  ExpressesDisapproval φ := match φ with | .moralEvil => protests | .suffering => False | .internal => False
  evilUtterance := .moralEvil
  sufferingReport := .suffering
  internalReport := .internal

/-- The positive affective analysis is compatible with truth-aptness and truth.
This is an analyst semantic witness, not an attribution to every expressivist. -/
def truthAffectiveCritic : Critic :=
  { critic False True with
    TruthApt := fun _ => True
    Holds := fun φ => match φ with | .moralEvil => True | .suffering => True | .internal => False }

theorem criticStrict (internalTrue protests : Prop) : StrictTruthlessPolicy (critic internalTrue protests) := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · intro φ hMoral
    cases φ with
    | moralEvil => exact id
    | suffering => exact False.elim hMoral
    | internal => exact False.elim hMoral
  · intro φ hNotApt
    cases φ with
    | moralEvil => exact id
    | suffering => exact False.elim (hNotApt trivial)
    | internal => exact False.elim (hNotApt trivial)
  · intro φ hBad
    exact hBad

theorem criticAffective (internalTrue : Prop) : BadnessAsDisapproval (critic internalTrue True) := by
  intro φ
  cases φ <;> exact Iff.rfl

theorem noCostGratuitous (s : Sig) (hApparent : ApparentlyPointlessSuffering s) :
    GratuitousSufferingReading (WithoutBlockingCosts s) := by
  obtain ⟨e, hOccurs, hIntense, hPrevent⟩ := hApparent
  refine ⟨e, hOccurs, hIntense, ?_⟩
  intro b hKnows hPower
  refine ⟨(hPrevent b hKnows hPower).1, ?_⟩
  rintro ⟨o, hCost, _⟩
  exact hCost

theorem criticDescriptive (s : Sig) (internalTrue protests : Prop)
    (hSuffering : ∃ e, s.Occurs e ∧ s.IntenseSuffering e) :
    DescriptiveReport (critic internalTrue protests) s := by
  refine ⟨id, ⟨fun _ => hSuffering, fun _ => trivial⟩⟩

theorem boundaryModels : BoundaryModels := by
  obtain ⟨s, hPermission, hApparent, hTheism, _⟩ :=
    TruthCore.Results.Comparison.ProblemOfEvil.RoweApparentCompatibility.roweApparentCompatibility
  have hSuffering : ∃ e, s.Occurs e ∧ s.IntenseSuffering e := by
    obtain ⟨e, hOccurs, hIntense, _⟩ := hApparent
    exact ⟨e, hOccurs, hIntense⟩
  have hGratuitous := noCostGratuitous s hApparent
  have hInternal := InternalChallenge.internalPermissionChallenge (WithoutBlockingCosts s) hGratuitous
  have hNotInternal : ¬ InternalPermissionChallenge s := fun h => h hTheism hPermission
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨critic True True, s, criticStrict True True, criticAffective True,
      criticDescriptive s True True hSuffering,
      criticDescriptive (WithoutBlockingCosts s) True True hSuffering,
      ?_, hTheism, hPermission, hTheism, hGratuitous, hInternal⟩
    exact ⟨id, trivial, ⟨fun _ => hInternal, fun _ => trivial⟩⟩
  · refine ⟨truthAffectiveCritic, ?_, trivial, trivial⟩
    intro φ
    cases φ <;> exact Iff.rfl
  · have hRemaining : RemainingUse (critic False False) s := ⟨id, hNotInternal, id⟩
    refine ⟨critic False False, s, criticStrict False False,
      criticDescriptive s False False hSuffering, hTheism, hPermission, hRemaining, ?_⟩
    intro hCoverage
    cases hCoverage with
    | inl h => exact hRemaining.1 h
    | inr h =>
      cases h with
      | inl h => exact hRemaining.2.1 h
      | inr h => exact hRemaining.2.2 h

end TruthCore.Results.Metaethics.EvilObjection.BoundaryModels
