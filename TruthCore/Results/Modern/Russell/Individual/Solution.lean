import TruthCore.Modern.Russell.Existence
namespace TruthCore.Results.Modern.Russell.Individual
open TruthCore.Modern.Russell.Existence
private theorem inhabitedAt : ∀ w, ExistsPred (actual w) := by
  intro w
  cases w with
  | false => exact ⟨.a, trivial⟩
  | true => exact ⟨.b, trivial⟩
private theorem noDenotation : ¬ DenotesAt actual true (token true) := by
  rintro ⟨x, hx, ha⟩
  cases x with
  | a => exact ha
  | b => exact Entity.noConfusion (Option.some.inj hx)
theorem checks : IndividualBoundary := by
  refine ⟨inhabitedAt, trivial, (fun h => h), ⟨.a, rfl, trivial⟩,
    noDenotation, ⟨⟨.a, trivial⟩, rfl⟩, (fun _ n => n.denotes), ?_, ?_⟩
  · intro h
    exact h true rfl
  · exact ⟨true, rfl, trivial⟩
end TruthCore.Results.Modern.Russell.Individual
