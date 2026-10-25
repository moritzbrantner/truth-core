import TruthCore.Results.Modal.S4.ScopeBoundary.Solution
namespace TruthCore.Results.Modal.S4.Extensionality
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite
open TruthCore.Modal.S4Research
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

theorem left_agreement (w : World) (h : Agree (language false) .left w) :
    w = .left := by
  have hp := (h (fun w => Holds (pockets false).frame (pockets false).valuation w
    (.atom false)) ⟨.atom false, rfl⟩).mp rfl
  cases w <;> first | rfl | cases hp

theorem twin_agreement (w : World) (h : Agree (language false) .twin w) :
    w = .twin := by
  have hp := (h (fun w => Holds (pockets false).frame (pockets false).valuation w
    (.atom true)) ⟨.atom true, rfl⟩).mp rfl
  cases w <;> first | rfl | cases hp

theorem root_not_right (h : Agree (language false) .root .right) : False := by
  have hp := (h (fun w => Holds (pockets false).frame (pockets false).valuation w
    (.diamond (.atom false))) ⟨.diamond (.atom false), rfl⟩).mp ⟨.left, rfl, rfl⟩
  obtain ⟨v, hv, ht⟩ := hp
  cases v <;> first | exact Bool.noConfusion hv | exact Bool.noConfusion ht

theorem language_extensional : PropositionalExtensionality (language false) := by
  intro w v h
  have hs : Agree (language false) v w := fun P hp => (h P hp).symm
  cases w with
  | left => exact (left_agreement v h).symm
  | twin => exact (twin_agreement v h).symm
  | root =>
    cases v with
    | root => rfl
    | left => cases left_agreement .root hs
    | twin => cases twin_agreement .root hs
    | right => exact (root_not_right h).elim
  | right =>
    cases v with
    | root => exact (root_not_right hs).elim
    | left => cases left_agreement .right hs
    | twin => cases twin_agreement .right hs
    | right => rfl

theorem unpaired_full (w : World) (hw : w ≠ .root) :
    MC (pockets false).frame allPredicates w := by
  apply (K.Laws.full_iff_successors _ _).mpr
  intro v hv
  cases w <;> cases v <;> first | rfl | exact (hw rfl).elim | cases hv

theorem checks : Extensionality := by
  refine ⟨language_extensional, ?_, unpaired_full .right ?_, unpaired_full .twin ?_, ?_⟩
  · intro W w v h
    exact ((h (fun x => x = w) trivial).mp rfl).symm
  · intro h; cases h
  · intro h; cases h
  · intro v _
    cases v with
    | root => exact ⟨.left, rfl, Countermodels.left_collapse false allPredicates⟩
    | left => exact ⟨.left, rfl, Countermodels.left_collapse false allPredicates⟩
    | right => exact ⟨.right, rfl, unpaired_full .right (by intro h; cases h)⟩
    | twin => exact ⟨.twin, rfl, unpaired_full .twin (by intro h; cases h)⟩
end TruthCore.Results.Modal.S4.Extensionality
