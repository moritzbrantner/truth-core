import TruthCore.Modern.Hume.SelfApplication
namespace TruthCore.Results.Modern.Hume.SelfApplication.HigherOrder
open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability
open TruthCore.Modern.Hume.SelfApplication

theorem checks : HigherOrderLaws := by
  have old := TruthCore.Results.Modern.Hume.Conceivability.checks
  refine ⟨old.1, old.2.1, ?_, ?_, ?_⟩
  · intro W F C w hH hC
    exact hH _ hC
  · intro W F C w hr hH hn hC
    obtain ⟨v, hwv, hneg⟩ := hH _ hC
    exact hneg v (hr v) (hn v hwv)
  · intro W F C w ht hs hH hn hC
    obtain ⟨v, hwv, hneg⟩ := hH _ hC
    obtain ⟨z, hvz⟩ := hs v hwv
    exact hneg z hvz (hn z (ht w v z hwv hvz))
end TruthCore.Results.Modern.Hume.SelfApplication.HigherOrder
