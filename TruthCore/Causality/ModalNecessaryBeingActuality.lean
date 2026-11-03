import TruthCore.Causality.NecessaryConcreteRouteBridge

/-! Configured instances have independent statement identities. These aliases
retain exactly the old propositions at modalPossible/modalIsAt, without claiming
the generic temporal schemas or introducing an ontology or new data. -/
namespace TruthCore.Causality.ModalNecessaryBeingActuality
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryConcreteRouteBridge (modalPossible modalIsAt)
open TruthCore.Case.Catholicism

/-- Necessary-to-act bridge ONLY for the supplied accessible-world dictionary. -/
def ConfiguredHasBeing {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (esse : R) : Prop :=
  NecessaryBeingHasBeing (modalPossible m w) (modalIsAt m) InAct esse

/-- Universal identity with each maximum IF ANY, ONLY at the supplied modal
instance. This gives no maximum or necessary candidate existence. -/
def ConfiguredConvergence {W B R : Type} (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  NecessaryPerSeIsMaximeEns (modalPossible m w) (modalIsAt m)
    CausesNecessityOf InAct MoreIn esse

end TruthCore.Causality.ModalNecessaryBeingActuality
