import TruthCore.Modal.Kripke

/-!
An analyst's epistemic interpretation of the existing Kripke frame. This is
not a source attribution or an account of all knowledge. In particular, absence
of knowledge of justification is not definitionally absence of justification.
-/
namespace TruthCore.Logic.JustificationIntrospection
open TruthCore.Modal

/-- At w, p holds throughout the epistemic alternatives admitted by the frame.
Reflexivity makes this factive; no completeness or actual knowledge is assumed. -/
def Knows {W : Type} (F : Frame W) (p : W → Prop) (w : W) : Prop :=
  Holds F (fun v (_ : Unit) => p v) w (.box (.atom ()))

/-- For this one proposition, knowledge requires justification at every world.
`justified` is independently supplied, not defined by paths, truth or knowledge. -/
def KnowledgeRequiresJustification {W : Type} (F : Frame W)
    (p justified : W → Prop) : Prop :=
  ∀ w, Knows F p w → justified w

/-- Transitive epistemic alternatives plus the global knowledge/justification
norm suffice for higher-order knowledge of justification. Contraposition then
excludes knowing p when knowing its justification fails. Neither the frame
condition nor the norm is claimed to hold for actual subjects. -/
def IntrospectionTransfer : Prop :=
  ∀ (W : Type) (F : Frame W) (p justified : W → Prop),
    Transitive F → KnowledgeRequiresJustification F p justified →
    ∀ w, (Knows F p w → Knows F justified w) ∧
      (¬ Knows F justified w → ¬ Knows F p w)

/-- Factivity and a global knowledge-requires-justification norm alone permit
knowledge and justification without knowledge of justification. The same model
violates transitivity; it does not model lack of certainty or universal ignorance. -/
def HigherOrderIgnoranceBoundary : Prop :=
  ∃ (F : Frame (Fin 3)) (p justified : Fin 3 → Prop) (actual : Fin 3),
    Reflexive F ∧ ¬ Transitive F ∧
    KnowledgeRequiresJustification F p justified ∧
    Knows F p actual ∧ justified actual ∧ ¬ Knows F justified actual

/-- The conditional transfer together with its factive omission model. This
establishes no foundationalist, coherentist or infinitist epistemic standard. -/
def IntrospectionBoundary : Prop :=
  IntrospectionTransfer ∧ HigherOrderIgnoranceBoundary

end TruthCore.Logic.JustificationIntrospection
