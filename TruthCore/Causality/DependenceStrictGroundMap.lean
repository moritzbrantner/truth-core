module

public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Modern.Fine.PureLogicOfGround

@[expose] public section

namespace TruthCore.Causality.DependenceStrictGroundMap

open TruthCore.Modern.Fine.PureLogicOfGround

/-- OPEN interpretation premise. For distinct beings, counterfactual dependence
`D x y` must *actually be represented* as a derivable strict partial ground of
the existence fact of `x` by the existence fact of `y`. `existenceFact` keeps
the things distinct from the facts about their existence; neither injectivity
nor this map is definitional. Self-dependence is deliberately excluded. -/
def DependenceMapsToStrictExistenceGround {B Atom : Type}
    (D : B → B → Prop) (existenceFact : B → Atom)
    (S : Set (Sequent Atom)) : Prop :=
  ∀ x y, x ≠ y → D x y → StrictlyGrounds S (existenceFact y) (existenceFact x)

namespace Control

/-- Omitting PLG consistency permits a symmetric `D` even with the entire
strict-grounding map, because an inconsistent theory derives every sequent. -/
def NoConsistency : Prop :=
  ∃ S : Set (Sequent Bool),
    DependenceMapsToStrictExistenceGround (fun _ _ : Bool => True) id S ∧
    ¬ TruthCore.Causality.Round2PerfectionPrimacy.DistinctBeingsNotMutuallyDependent
      (fun _ _ : Bool => True)

/-- Omitting the interpretation map permits mutual existential dependence
even while an unrelated PLG theory remains consistent. -/
def NoMap : Prop :=
  ∃ S : Set (Sequent Nat), Consistent S ∧
    ¬ TruthCore.Causality.Round2PerfectionPrimacy.DistinctBeingsNotMutuallyDependent
      (fun _ _ : Bool => True)

def Certificate : Prop := NoConsistency ∧ NoMap

end Control

end TruthCore.Causality.DependenceStrictGroundMap
