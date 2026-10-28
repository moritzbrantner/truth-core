import TruthCore.Causality.ParityUnionRegress
namespace TruthCore.Results.Causality.ParityUnionRegress
open TruthCore.Causality.ParityUnionRegress
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference

theorem noTwoSteps (w : Bool) (a b c : Nat)
    (h : support w a b) (k : support w b c) : False := by
  cases w <;> simp only [support, Bool.false_eq_true, ↓reduceIte] at h k <;> omega

theorem localWF (w : Bool) : WellFoundedPresentEsseSupport model support w := by
  refine ⟨fun n => Acc.intro n (fun g h => ?_)⟩
  exact Acc.intro g (fun a k => False.elim (noTwoSteps w a g n k.2 h.2))

theorem unionIff (g n : Nat) :
    UnionNecessarySupport model support false g n ↔ g = n + 1 := by
  constructor
  · rintro ⟨_, _, w, _, h⟩
    exact h.1
  · intro h
    refine ⟨(fun _ _ => True.intro), (fun _ _ => True.intro), ?_⟩
    by_cases he : n % 2 = 0
    · exact ⟨false, True.intro, h, he⟩
    · refine ⟨true, True.intro, h, ?_⟩
      dsimp
      omega

theorem unionNotWF : ¬ WellFoundedUnionNecessarySupport model support false := by
  intro h
  exact h.not_rightTotal (fun n => ⟨n+1, (unionIff _ _).2 rfl⟩)

theorem unionAcyclic (n : Nat) :
    ¬ Relation.TransGen (UnionNecessarySupport model support false) n n := by
  have decreasing : ∀ {a b}, Relation.TransGen
      (UnionNecessarySupport model support false) a b → b < a := by
    intro a b h
    induction h with
    | single h => have := (unionIff _ _).1 h; omega
    | tail h k ih => have := (unionIff _ _).1 k; omega
  intro h
  have := decreasing h
  omega

/-- Every target has a supporter in one parity world; no common underived
individual exists, although each local support relation terminates. -/
theorem checks : Certificate := by
  refine ⟨(fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩),
    ⟨0, True.intro, fun _ _ => True.intro⟩, True.intro,
    (fun _ _ _ _ _ _ _ _ => True.intro), noTwoSteps, localWF,
    unionIff, unionAcyclic, unionNotWF, ?_⟩
  rintro ⟨n, _, _, h⟩
  obtain ⟨w, hp, he⟩ := ((unionIff (n+1) n).2 rfl).2.2
  exact h w (n+1) hp he
end TruthCore.Results.Causality.ParityUnionRegress
