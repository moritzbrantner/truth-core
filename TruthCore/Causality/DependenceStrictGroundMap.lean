module

public import TruthCore.Causality.Round2PerfectionPrimacy
public import TruthCore.Modern.Fine.PureLogicOfGround

@[expose] public section

namespace TruthCore.Causality.DependenceStrictGroundMap

open TruthCore.Modern.Fine.PureLogicOfGround

/-- OPEN interpretive premise, encoded as a structural surrogate. Formally it
says only this: each `D`-edge `x → y` between distinct beings lands, under the
labelling `existenceFact`, on a sequent `existenceFact y ≺ existenceFact x`
that is derivable from the PLG theory `S`. `S` and `existenceFact` are
arbitrary parameters and the atoms are uninterpreted
(`DEF-FINE-PLG-STRICT-PARTIAL-GROUND`). The type therefore does not say that
the atoms are existence facts, that the edges are actual or faithful grounding,
or which kind of ground (constitutive or natural/causal) is meant. Reading the
labels as existence facts and the sequents as real grounds is a further OPEN
interpretation outside the type (`docs/notes/distinct-dependence-strict-ground-route.md`).
Together with `Consistent S`, the map already forces `D` to have no finite
cycle of distinct steps (`mapForcesDistinctDependenceAcyclic`), which is more
than nonmutuality. Neither injectivity of the labelling nor this map is
definitional; self-dependence is deliberately excluded. -/
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
