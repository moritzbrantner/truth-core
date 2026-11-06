module

public import TruthCore.Causality.DirectEsseRootUniquenessAtBeing

/-! Same-dictionary scope weakening of actual grounding asymmetry. The current
maximum/root proof only excludes reverse edges at maximal-in-esse targets.
This says nothing about whether selected grounds is direct production or partial
support in reality. Actuality/concreteness, the degree dictionary and all causal
bridges remain separate inputs. Reciprocal nonmaximal dependents are not excluded
by this weaker policy; their explanatory adequacy is not certified. -/
@[expose] public section
namespace TruthCore.Causality.MaximalGroundingAsymmetry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic
open TruthCore.Logic.CogitoConcrete

/-- Actual grounding has no reverse edge when its target is maximal in the SAME
supplied esse respect. Other pairs of actual concreta remain unconstrained. -/
def AtMaximalTarget {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  ∀ a b, ActualConcrete m w a → ActualConcrete m w b →
    IsMaximumIn InAct MoreIn esse b → m.grounds w a b → ¬ m.grounds w b a

namespace Control
inductive Node where | root | left | right deriving DecidableEq
open Node
def grounds (a b : Node) : Prop :=
  (a = root ∧ b ≠ root) ∨ (a = left ∧ b = right) ∨ (a = right ∧ b = left)
def model : Profile Unit Node where
  ontic :=
    { frame := { access := fun _ _ => True }
      ExistsAt := fun _ _ => True
      Causes := fun _ => grounds }
  concrete := fun _ => True  -- category-constant: intended (three stipulated actual concreta test grounding scope; no reality or concrete/abstract adequacy follows)
  grounds := fun _ => grounds
def act (_ : Node) (_ : Unit) : Prop := True
def more (_ : Unit) (a b : Node) : Prop := a = root ∧ b ≠ root
def cause (a b : Node) (_ : Unit) : Prop := a = root ∧ b ≠ root
end Control

/-- Every nonlogical input of the seven-premise whole-roster route is exported,
with weak asymmetry in place of global asymmetry. EM remains an explicit input.
The distinct dependent pair is actual, nonmaximal and reciprocally grounded;
the same interpretation has an actual maximal root. It is not a full25-input
attribute model or a metaphysical possibility certificate. -/
def PopulatedStrictness : Prop :=
  let m := Control.model
  InhabitedConcreteAt m.ontic m.concrete () ∧
  ExistingInActAt m.ontic Control.act () () ∧
  EsseCauseIsActualConcreteGround m () Control.cause () ∧
  MaximumInBeingCausesAllBeingsReading Control.act Control.more Control.cause () ∧
  GradesToMaximumAtBeing Control.act Control.more () ∧
  AtMaximalTarget m () Control.act Control.more () ∧
  ActualRoot m () .root ∧ IsMaximumIn Control.act Control.more () .root ∧
  ActualConcrete m () .left ∧ ActualConcrete m () .right ∧
  Control.Node.left ≠ Control.Node.right ∧
  (¬ IsMaximumIn Control.act Control.more () .left) ∧
  (¬ IsMaximumIn Control.act Control.more () .right) ∧
  m.grounds () .left .right ∧ m.grounds () .right .left ∧
  ¬ ActualGroundingAsymmetric m ()
end TruthCore.Causality.MaximalGroundingAsymmetry
