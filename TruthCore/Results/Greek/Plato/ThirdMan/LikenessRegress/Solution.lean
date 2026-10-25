import TruthCore.Greek.Plato.ThirdMan
namespace TruthCore.Results.Greek.Plato.ThirdMan.LikenessRegress
open TruthCore.Greek.Plato.Forms TruthCore.Greek.Plato.ThirdMan
universe u v
variable {E : Type u} {Q : Type v}
/-- Conditional likeness regress, without ordinary self-predication. -/
theorem likenessRegress (s : Vocabulary E Q) (eligible : List E → Prop) (q : Q)
    (hSeed : LikenessSeed s eligible q)
    (hFormation : LikenessFormation s eligible q)
    (hSymmetry : LikenessSymmetry s) (hBridge : ParticipationLikeness s)
    (hNonid : ParticipantNonidentity s) (hIteration : Iteration s eligible) :
    UnboundedForms s := by
  obtain ⟨hq,a,b,hab,helig,habLike,hbaLike⟩ := hSeed
  refine ⟨q,hq,?_⟩
  have aux : ∀ n : Nat, ∃ fs : List E, fs.length = n ∧
      fs.Pairwise (· ≠ ·) ∧ (∀ f ∈ fs, s.FormOf f q) ∧
      eligible (fs ++ [a,b]) ∧ MutuallyLike s (fs ++ [a,b]) := by
    intro n
    induction n with
    | zero =>
      refine ⟨[],rfl,List.Pairwise.nil,(by intro x hx; cases hx),helig,?_⟩
      intro x hx y hy hxy
      rcases pairCases hx with rfl | rfl <;> rcases pairCases hy with rfl | rfl
      · exact False.elim (hxy rfl)
      · exact habLike
      · exact hbaLike
      · exact False.elim (hxy rfl)
    | succ n ih =>
      obtain ⟨fs,hlen,hpair,hforms,helig,hLike⟩ := ih
      have hplural : Plural (fs ++ [a,b]) :=
        ⟨a,List.mem_append_right fs (List.Mem.head _) ,b,
          List.mem_append_right fs (List.Mem.tail a (List.Mem.head _)),hab⟩
      obtain ⟨f,hform,hparts⟩ := hFormation _ helig hplural hLike
      refine ⟨f::fs, congrArg Nat.succ hlen, ?_, ?_, ?_, ?_⟩
      · exact List.pairwise_cons.mpr ⟨fun x hx =>
          hNonid q hq f x hform (hparts x (List.mem_append_left _ hx)),hpair⟩
      · intro x hx
        rcases consCases hx with rfl | hx
        · exact hform
        · exact hforms x hx
      · exact hIteration q hq _ f helig hform
      · intro x hx y hy hxy
        rcases consCases hx with hxf | hxo
        · rcases consCases hy with hyf | hyo
          · exact False.elim (hxy (hxf.trans hyf.symm))
          · rw [hxf]
            exact hSymmetry y f (hBridge y f (hparts y hyo))
        · rcases consCases hy with hyf | hyo
          · rw [hyf]
            exact hBridge x f (hparts x hxo)
          · exact hLike x hxo y hyo hxy
  intro n
  obtain ⟨fs,hlen,hpair,hforms,_⟩ := aux n
  exact ⟨fs,hlen,hpair,hforms⟩
end TruthCore.Results.Greek.Plato.ThirdMan.LikenessRegress
