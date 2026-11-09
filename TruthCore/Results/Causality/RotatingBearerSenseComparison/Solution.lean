module
public import TruthCore.Causality.RotatingBearerSenseComparison
public import TruthCore.Results.Causality.NecessarySenseFork.Solution
@[expose] public section
namespace TruthCore.Results.Causality.RotatingBearerSenseComparison
open TruthCore.Causality.RotatingBearerSenseComparison
open TruthCore.Causality.NecessarySenseFork

theorem classification : Classification := by
  intro W B m w CN em h s x
  have noBox : ¬ BoxExistsAt m.ontic w x := fun hx => h.2 ⟨x, hx⟩
  have noTertia : ¬ NecessaryIn .tertiaVia m w CN x := by
    intro hn
    apply noBox
    intro v hv
    rcases em (m.ontic.ExistsAt v x) with present | absent
    · exact present
    · exact False.elim (hn ⟨v, hv, absent⟩)
  cases s with
  | deDictoK => exact ⟨fun _ => rfl, fun _ => h.1⟩
  | boxK => exact ⟨fun hx => False.elim (noBox hx), fun h => by cases h⟩
  | actualistK => exact ⟨fun hx => False.elim (noBox hx.2), fun h => by cases h⟩
  | boxT => exact ⟨fun hx => False.elim (noBox hx.2), fun h => by cases h⟩
  | boxS4 => exact ⟨fun hx => False.elim (noBox hx.2), fun h => by cases h⟩
  | boxB => exact ⟨fun hx => False.elim (noBox hx.2), fun h => by cases h⟩
  | boxS5 => exact ⟨fun hx => False.elim (noBox hx.2), fun h => by cases h⟩
  | tertiaVia => exact ⟨fun hx => False.elim (noTertia hx), fun h => by cases h⟩
  | perSe => exact ⟨fun hx => False.elim (noTertia hx.1), fun h => by cases h⟩

theorem rootClassification : RootClassification := by
  intro W σ m w CN em h s
  constructor
  · rintro ⟨n, hn, hf⟩
    exact ⟨(classification W σ.Being m w CN em h s n).mp hn, n, hf⟩
  · rintro ⟨hs, n, hf⟩
    exact ⟨n, (classification W σ.Being m w CN em h s n).mpr hs, hf⟩

theorem controls : Controls := by
  have cert := NecessarySenseFork.certificate
  refine ⟨cert.2.2, ?_, ?_, ⟨false, rfl⟩, ?_⟩
  · exact ⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩
  · intro x v hv
    exact ⟨v, rfl⟩
  · intro h
    exact h.2 ⟨(), fun _ _ => trivial⟩
end TruthCore.Results.Causality.RotatingBearerSenseComparison
