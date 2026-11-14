module

public import TruthCore.Causality.DependenceStrictGroundMap
public import TruthCore.Results.Modern.Fine.StrictGroundAcyclic.Solution
public import TruthCore.Results.Modern.Fine.InfiniteDescent.Solution

@[expose] public section

namespace TruthCore.Results.Causality.DependenceStrictGroundMap

open TruthCore.Causality.DependenceStrictGroundMap
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Results.Modern.Fine.PlgDerivedRules
open TruthCore.Results.Modern.Fine.StrictGroundAcyclic
open TruthCore.Results.Modern.Fine.InfiniteDescent

/-- Structural-surrogate support for the existing nonmutual-existential-
dependence premise. A reversible pair of distinct dependence edges would map
to a two-edge cycle of derivable strict partial grounds between the beings'
labelling atoms, contradicting PLG consistency. The atoms are uninterpreted:
reading them as existence facts, and the sequents as real grounds, is an OPEN
interpretation that the type does not encode. The interpretation map and
consistency are OPEN inputs. (The frozen Challenge's doc comment says
"existence facts"; read it as these labelling atoms.) -/
theorem nonmutualDependenceFromStrictGround {B Atom : Type}
    (D : B → B → Prop) (existenceFact : B → Atom)
    (S : Set (Sequent Atom))
    (hCons : Consistent S)
    (hMap : DependenceMapsToStrictExistenceGround D existenceFact S) :
    DistinctBeingsNotMutuallyDependent D := by
  intro x y hne hxy hyx
  have hyxGround : StrictlyGrounds S (existenceFact y) (existenceFact x) :=
    hMap x y hne hxy
  have hxyGround : StrictlyGrounds S (existenceFact x) (existenceFact y) :=
    hMap y x (Ne.symm hne) hyx
  have hSelf : StrictlyGrounds S (existenceFact x) (existenceFact x) :=
    strictTrans hxyGround hyxGround
  exact strictIrrefl hCons (existenceFact x) hSelf

/-- Both interpretation and consistency are necessary to draw the conditional
conclusion: each omitted input has a populated counterinterpretation. -/
theorem controls : TruthCore.Causality.DependenceStrictGroundMap.Control.Certificate := by
  constructor
  · refine ⟨Set.univ, ?_, ?_⟩
    · intro x y _ _
      exact Derivable.assumption (Set.mem_univ _)
    · intro hAsym
      exact hAsym true false (by decide) trivial trivial
  · obtain ⟨S, hCons, _, _⟩ := nonCircularityAllowsInfiniteDescent
    refine ⟨S, hCons, ?_⟩
    intro hAsym
    exact hAsym true false (by decide) trivial trivial

end TruthCore.Results.Causality.DependenceStrictGroundMap
