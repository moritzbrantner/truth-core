import TruthCore.Results.Modern.Russell.Description.Solution
namespace TruthCore.Results.Modern.Russell.Cardinality
open TruthCore.Modern.Russell.Existence
private theorem nonemptyA : ExistsPred (Inst singleA) := ⟨.a, rfl⟩
private theorem nonemptyB : ExistsPred (Inst singleB) := ⟨.b, rfl⟩
private theorem nonemptyBoth : ExistsPred (Inst both) := ⟨.a, rfl⟩
private theorem emptyNone : ¬ ExistsPred (Inst none) := by
  rintro ⟨x, hx⟩
  exact Bool.noConfusion hx
private theorem uniqueA : AtMostOne (Inst singleA) := by
  intro x y hx hy
  cases x with
  | a =>
    cases y with
    | a => rfl
    | b => exact Bool.noConfusion hy
  | b => exact Bool.noConfusion hx
private theorem manyNotUnique : ¬ AtMostOne (Inst both) := by
  intro h
  exact Entity.noConfusion (h .a .b rfl rfl)
theorem checks : CardinalityBoundary := by
  refine ⟨emptyNone, ?_, nonemptyA, nonemptyBoth, rfl, rfl, rfl, ?_,
    ⟨fun _ => nonemptyB, fun _ => nonemptyA⟩, rfl,
    (fun h => Bool.noConfusion h), ?_, ?_⟩
  · intro x y hx
    exact Bool.noConfusion hx
  · intro h
    change 1 = 2 at h
    exact Nat.noConfusion (Nat.succ.inj h)
  · exact (TruthCore.Results.Modern.Russell.Description.checks Entity _).mpr
      ⟨nonemptyA, uniqueA⟩
  · intro h
    exact manyNotUnique
      ((TruthCore.Results.Modern.Russell.Description.checks Entity _).mp h).2
end TruthCore.Results.Modern.Russell.Cardinality
