import TruthCore.Modal.DResearch.Witnesses
namespace TruthCore.Results.Modal.DResearch.Witnesses
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.DResearch

private theorem fullOfSingleton {W : Type} (F : Frame W) (w : W)
    (h : ∀ v, F.access w v → v = w) : MC F allPredicates w := by
  intro P _ hp v hv
  exact h v hv ▸ hp

theorem pocketOne : MC pocket.frame allPredicates 1 :=
  fullOfSingleton _ _ (by
    intro v; cases v <;> intro hv
    all_goals first | rfl | exact Bool.noConfusion hv)
private theorem pocketFour : MC pocket.frame allPredicates 4 :=
  fullOfSingleton _ _ (by
    intro v; cases v <;> intro hv
    all_goals first | rfl | exact Bool.noConfusion hv)
theorem forkOne : MC fork.frame allPredicates 1 :=
  fullOfSingleton _ _ (by
    intro v; cases v <;> intro hv
    all_goals first | rfl | exact Bool.noConfusion hv)
theorem forkTwo : MC fork.frame allPredicates 2 :=
  fullOfSingleton _ _ (by
    intro v; cases v <;> intro hv
    all_goals first | rfl | exact Bool.noConfusion hv)

private theorem pocketRoot : ¬ MC pocket.frame allPredicates 0 := by
  intro h
  have he := identity_separates pocket.frame allPredicates 0 trivial h 1 rfl
  exact PocketWorld.noConfusion he
private theorem pocketTwo : ¬ MC pocket.frame allPredicates 2 := by
  intro h
  have he := identity_separates pocket.frame allPredicates 2 trivial h 3 rfl
  exact PocketWorld.noConfusion he
private theorem forkRoot : ¬ MC fork.frame allPredicates 0 := by
  intro h
  have he := identity_separates fork.frame allPredicates 0 trivial h 1 rfl
  exact ForkWorld.noConfusion he

private theorem pocketSerial : Serial pocket.frame := by
  intro w
  cases w with
  | root => exact ⟨1, rfl⟩
  | collapse => exact ⟨1, rfl⟩
  | left => exact ⟨3, rfl⟩
  | right => exact ⟨2, rfl⟩
  | away => exact ⟨4, rfl⟩
private theorem forkSerial : Serial fork.frame := by
  intro w
  cases w with
  | root => exact ⟨1, rfl⟩
  | left => exact ⟨1, rfl⟩
  | right => exact ⟨2, rfl⟩

theorem checks : WitnessChecks := by
  constructor
  · refine ⟨pocketSerial, ?_, ?_, ?_, pocketOne, pocketFour, pocketRoot,
      ⟨1, rfl, pocketOne⟩, ?_, ⟨⟨1, rfl, rfl⟩, ⟨2, rfl, ?_⟩⟩,
      ⟨1, rfl, rfl⟩, ?_, ⟨rfl, rfl⟩, ?_, ?_, ⟨?_, ?_⟩, ?_, rfl, rfl⟩
    · intro h; exact Bool.noConfusion (h 0)
    · intro h; exact Bool.noConfusion (h 0 1 rfl)
    · intro h; exact Bool.noConfusion (h 0 2 3 rfl rfl)
    · intro hBox; exact pocketTwo (hBox 2 rfl)
    · exact PocketWorld.noConfusion
    · exact PocketWorld.noConfusion
    · intro v; cases v <;> intro hv
      all_goals first | rfl | exact Bool.noConfusion hv
    · intro v; cases v <;> intro hv
      all_goals first | rfl | exact Bool.noConfusion hv
    · exact Bool.noConfusion
    · exact Bool.noConfusion
    · intro v; cases v
      all_goals constructor <;> intro h
      all_goals first | rfl | exact Bool.noConfusion h | exact PocketWorld.noConfusion h
  · refine ⟨forkSerial, ?_, ?_, forkOne, forkTwo, forkRoot,
      ⟨1, rfl, forkOne⟩, ?_, ⟨⟨1, rfl, rfl⟩, ⟨2, rfl, ?_⟩⟩,
      ⟨1, rfl, rfl⟩, ?_, rfl, rfl⟩
    · intro h; exact Bool.noConfusion (h 0)
    · intro h; exact Bool.noConfusion (h 0 1 rfl)
    · intro v hv
      cases v with
      | root => exact Bool.noConfusion hv
      | left => exact forkOne
      | right => exact forkTwo
    · exact ForkWorld.noConfusion
    · exact ForkWorld.noConfusion
end TruthCore.Results.Modal.DResearch.Witnesses
