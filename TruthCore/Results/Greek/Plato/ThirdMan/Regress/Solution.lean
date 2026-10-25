import TruthCore.Greek.Plato.ThirdMan
namespace TruthCore.Results.Greek.Plato.ThirdMan.Regress
open TruthCore.Greek.Plato.Forms TruthCore.Greek.Plato.ThirdMan
universe u v
variable {E : Type u} {Q : Type v}
/-- Conditional Third Man: finite induction constructs unbounded distinct Forms. -/
theorem regress (s : Vocabulary E Q) (eligible : List E → Prop)
    (hSeed : PropertyInstances s) (hScope : InitialScope s eligible)
    (hFormation : Formation s eligible) (hSelf : UniformSelfPredication s)
    (hNonid : ParticipantNonidentity s) (hIteration : Iteration s eligible) :
    UnboundedForms s := by
  obtain ⟨a,b,q,hab,ha,hb,hq,hFa,hFb⟩ := hSeed
  refine ⟨q,hq,?_⟩
  have aux : ∀ n : Nat, ∃ fs : List E, fs.length = n ∧
      fs.Pairwise (· ≠ ·) ∧ (∀ f ∈ fs, s.FormOf f q) ∧
      eligible (fs ++ [a,b]) ∧ (∀ x ∈ fs ++ [a,b], s.Exemplifies x q) := by
    intro n
    induction n with
    | zero =>
      refine ⟨[],rfl, List.Pairwise.nil, ?_, hScope a b ha hb, ?_⟩
      · intro x hx; cases hx
      · intro x hx
        rcases pairCases hx with rfl | rfl
        · exact hFa
        · exact hFb
    | succ n ih =>
      obtain ⟨fs,hlen,hpair,hforms,helig,hF⟩ := ih
      have hplural : Plural (fs ++ [a,b]) :=
        ⟨a, List.mem_append_right fs (List.Mem.head _) , b,
          List.mem_append_right fs (List.Mem.tail a (List.Mem.head _)), hab⟩
      obtain ⟨f,hform,hparts⟩ := hFormation q hq _ helig hplural hF
      refine ⟨f::fs, congrArg Nat.succ hlen, ?_, ?_, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨fun x hx =>
          hNonid q hq f x hform (hparts x (List.mem_append_left _ hx)), hpair⟩
      · intro x hx
        rcases consCases hx with rfl | hx
        · exact hform
        · exact hforms x hx
      · exact hIteration q hq _ f helig hform
      · intro x hx
        rcases consCases hx with rfl | hx
        · exact hSelf q hq x hform
        · exact hF x hx
  intro n
  obtain ⟨fs,hlen,hpair,hforms,_⟩ := aux n
  exact ⟨fs,hlen,hpair,hforms⟩
end TruthCore.Results.Greek.Plato.ThirdMan.Regress
