import TruthCore.Causality.DependenceStrictGroundMap
import TruthCore.Results.Modern.Fine.StrictGroundAcyclic.Solution
import TruthCore.Results.Modern.Fine.InfiniteDescent.Solution

namespace TruthCore.Results.Causality.DependenceStrictGroundMap

open TruthCore.Causality.DependenceStrictGroundMap
open TruthCore.Causality.Round2PerfectionPrimacy
open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Results.Modern.Fine.PlgDerivedRules
open TruthCore.Results.Modern.Fine.StrictGroundAcyclic
open TruthCore.Results.Modern.Fine.InfiniteDescent

/-- Conditional support for the existing nonmutual-existential-dependence
premise. A reversible dependence pair would become a two-edge cycle of
derivable *strict* grounds of existence facts, contradicting PLG consistency.
The interpretation map and consistency are independent OPEN inputs. -/
theorem nonmutualDependenceFromStrictGround {B Atom : Type}
    (D : B → B → Prop) (existenceFact : B → Atom)
    (S : Set (Sequent Atom))
    (hCons : Consistent S)
    (hMap : DependenceMapsToStrictExistenceGround D existenceFact S) :
    DistinctBeingsNotMutuallyDependent D := by
  sorry

/-- Both interpretation and consistency are necessary to draw the conditional
conclusion: each omitted input has a populated counterinterpretation. -/
theorem controls : TruthCore.Causality.DependenceStrictGroundMap.Control.Certificate := by
  sorry

end TruthCore.Results.Causality.DependenceStrictGroundMap
