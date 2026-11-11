module

public import TruthCore.Logic.FormSelection

@[expose] public section
namespace TruthCore.Results.Logic.FormSelection
open TruthCore.Logic.FormSelection
open TruthCore.Latin.Aquinas.SummaTheologiae.FormReception

theorem selection {C S F : Type} (p : Presentation C S F)
    (ha : Accurate p) (hi : IntrinsicDecoder p) (c d : C)
    (hs : p.state c = p.state d) : p.target c = p.target d := by
  exact (ha c).symm.trans ((congrArg (p.decode c) hs).trans ((hi c d (p.state d)).trans (ha d)))

theorem controls :
    ForeignFormCapacity recipient () ∧
    (∀ f, recipient.ForeignForm () f ∧ recipient.CanHaveForm () f .withoutMatter) ∧
    ¬ recipient.Intellectual () ∧
    Accurate contextual ∧ contextual.state false = contextual.state true ∧
    contextual.target false ≠ contextual.target true ∧
    (∀ b, sensor b b = replay b b) ∧
    sensor true false ≠ replay true false := by
  exact ⟨⟨false, True.intro, .withoutMatter, rfl⟩,
    (fun _ => ⟨True.intro, rfl⟩), (fun h => h), (fun _ => rfl), rfl,
    Bool.noConfusion, (fun _ => rfl), Bool.noConfusion⟩

theorem referenceControls :
    faulty.referent () = true ∧ ¬ Correct faulty () ∧
    Correct (ground true) () ∧ Correct (ground false) () ∧
    (ground true).referent () ≠ (ground false).referent () := by
  exact ⟨rfl, Bool.noConfusion, rfl, rfl, Bool.noConfusion⟩

end TruthCore.Results.Logic.FormSelection
