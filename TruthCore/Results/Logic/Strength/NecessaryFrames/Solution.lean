module

public import TruthCore.Logic.Strength.NecessaryFrames

/-!
Certificates for `TruthCore.Logic.Strength.NecessaryFrames` (#1598). Each
equivalence proves STRONG ⇔ WEAK ∧ DELTA for one registered strength pair;
the implication direction reuses the pair's registered backing theorem.
-/

@[expose] public section

namespace TruthCore.Results.Logic.Strength.NecessaryFrames

open TruthCore.Modal
open TruthCore.Logic.Strength.NecessaryFrames
open TruthCore.Causality.NecessarySenseFork

/-- S5 ⇔ S4 ∧ symmetric frame: a reflexive Euclidean frame is symmetric, and a
reflexive transitive symmetric frame is Euclidean. -/
theorem s5OverS4Exact : S5OverS4Exact := by
  intro W σ m w CN
  constructor
  · rintro ⟨n, ⟨⟨hRefl, hEucl⟩, hBox⟩, hFacts⟩
    exact ⟨⟨n, ⟨⟨hRefl, fun x y z hxy hyz => hEucl y x z (hEucl x y x hxy (hRefl x)) hyz⟩, hBox⟩,
      hFacts⟩, fun x y hxy => hEucl x y x hxy (hRefl x)⟩
  · rintro ⟨⟨n, ⟨⟨hRefl, hTrans⟩, hBox⟩, hFacts⟩, hSym⟩
    exact ⟨n, ⟨⟨hRefl, fun x l r hl hr => hTrans l x r (hSym x l hl) hr⟩, hBox⟩, hFacts⟩

/-- KTB ⇔ T ∧ symmetric frame: KTB frames are exactly the symmetric T frames. -/
theorem bOverTExact : BOverTExact := by
  intro W σ m w CN
  constructor
  · rintro ⟨n, ⟨⟨hRefl, hSym⟩, hBox⟩, hFacts⟩
    exact ⟨⟨n, ⟨hRefl, hBox⟩, hFacts⟩, hSym⟩
  · rintro ⟨⟨n, ⟨hRefl, hBox⟩, hFacts⟩, hSym⟩
    exact ⟨n, ⟨⟨hRefl, hSym⟩, hBox⟩, hFacts⟩

end TruthCore.Results.Logic.Strength.NecessaryFrames
