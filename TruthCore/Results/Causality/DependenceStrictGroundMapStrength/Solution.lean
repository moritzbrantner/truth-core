module

public import TruthCore.Causality.DependenceStrictGroundMapStrength
public import TruthCore.Results.Modern.Fine.StrictGroundAcyclic.Solution
public import TruthCore.Results.Modern.Fine.InfiniteDescent.Solution

@[expose] public section

namespace TruthCore.Results.Causality.DependenceStrictGroundMapStrength

open TruthCore.Causality.DependenceStrictGroundMap
open TruthCore.Causality.DependenceStrictGroundMapStrength
open TruthCore.Modern.Fine.PureLogicOfGround
open TruthCore.Results.Modern.Fine.StrictGroundAcyclic
open TruthCore.Results.Modern.Fine.InfiniteDescent

/-- Structural strength of the strict-ground support bundle: consistency and
the dependence-to-strict-ground map already force distinct-step dependence to
have no finite cycle, which is more than nonmutuality. Each distinct edge
`x → y` maps to `existenceFact y ≺ existenceFact x`, so a cycle of edges maps
to a chain of strict grounds from a label to itself; the existing
`transGen_strict` and `strictIrrefl` close it. -/
theorem mapForcesDistinctDependenceAcyclic {B Atom : Type}
    (D : B → B → Prop) (existenceFact : B → Atom)
    (S : Set (Sequent Atom))
    (hCons : Consistent S)
    (hMap : DependenceMapsToStrictExistenceGround D existenceFact S) :
    DistinctDependenceAcyclic D := by
  have hChain : ∀ {a b : B}, Relation.TransGen (DistinctEdge D) a b →
      Relation.TransGen (StrictlyGrounds S) (existenceFact b) (existenceFact a) := by
    intro a b h
    induction h with
    | single hab => exact Relation.TransGen.single (hMap _ _ hab.1 hab.2)
    | tail _ hbc ih => exact Relation.TransGen.head (hMap _ _ hbc.1 hbc.2) ih
  intro x hCycle
  exact strictIrrefl hCons (existenceFact x) (transGen_strict (hChain hCycle))

/-- The support bundle has a populated model with a distinct dependence
edge, so it is not satisfied only by an empty dependence relation. The model
reuses the consistent infinite-descent theory, in which `n + 1 ≺ n` is
derivable, with `D x y` iff `y = x + 1`. -/
theorem nonvacuity :
    TruthCore.Causality.DependenceStrictGroundMapStrength.Control.Nonvacuous := by
  obtain ⟨S, hCons, hStep, _⟩ := nonCircularityAllowsInfiniteDescent
  refine ⟨S, fun x y => y = x + 1, hCons, ?_, 0, 1, by decide, rfl⟩
  intro x y _ hxy
  subst hxy
  exact hStep x

end TruthCore.Results.Causality.DependenceStrictGroundMapStrength
