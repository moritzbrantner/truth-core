module

public import TruthCore.Causality.PureActRoot
public import TruthCore.Causality.RootWithoutLimitingPrinciple

/-! Strict pure actuality at the actual roots, derived from no limitation (#320)

Analyst formulation, attribution deferred.

`ROOT-WITHOUT-LIMITING-PRINCIPLE` shows that ONE witnessed necessary root has
none of the three represented limiting principles (`HasLimitingPrinciple`):
composition, esse other than essence, a distinct simply-prior being. Its
essence/esse step (`identityOfActualRoot`) and its firstness step hold for EVERY
actual root, so the universal version `ActualRootsWithoutLimitingPrinciple`
follows from the same premises without population, whole-roster or dependence.

The open bridge `UnlimitedDeterminationsArePure` says that a being without any of
these three limiting principles has only pure real determinations: every non-pure
determination comes from composition, received esse or dependence on something
prior. It ranges over all beings, not only roots. Its restriction to actual roots
would, given the derived no-limitation fact, simply restate strict pure actuality
at the roots, so the bridge supports that conclusion only in its general form.

The same bridge also yields strict pure actuality for first unmoved movers from
the existing simplicity reading (no composition, esse not other than essence)
and the first-mover-is-first-being bridge, so one premise feeds both the
first-mover and the necessary-root uniqueness routes. -/

@[expose] public section

namespace TruthCore.Causality.RootPurity
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.RootMultiplication (HasLimitingPrinciple)

variable {W B P D : Type}

/-- Every actual root of the selected grounding relation at `w` has none of the
three represented limiting principles. -/
def ActualRootsWithoutLimitingPrinciple (m : Profile W B) (w : W)
    (Composite : B → Prop) (Prior : B → B → Prop) (essence esse : B → P) : Prop :=
  ∀ r, ActualRoot m w r → ¬ HasLimitingPrinciple Composite Prior essence esse r

/-- OPEN bridge, over all beings: a being with no represented limiting principle
has only pure real determinations. -/
def UnlimitedDeterminationsArePure
    (Composite : B → Prop) (Prior : B → B → Prop) (essence esse : B → P)
    (Has : B → D → Prop) (Pure : D → Prop) : Prop :=
  ∀ x, ¬ HasLimitingPrinciple Composite Prior essence esse x → ∀ d, Has x d → Pure d

namespace Control
open TruthCore.Causality.NecessaryConcreteRouteBridge
  (oneWorld EsseCauseIsActualConcreteGround SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.PureActRoot (ActualRootDeterminationsArePure)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
  (DistinctEsseCauseDichotomyReading EssentialPrinciplesCannotCauseDistinctEsseReading)

/-- Every being is in act in the one esse respect, nothing causes anything, and
represented esse equals represented essence for every being. -/
def flat : TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.Profile
    Bool Unit Unit where
  InAct := fun _ _ => True
  CausesIn := fun _ _ _ => False
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  essentialPrinciplesAloneSufficeForEsse := fun _ => False
  esse := ()

def none2 (_ _ : Bool) : Prop := False
def none1 (_ : Bool) : Prop := False

/-- The seven non-logical premises of the no-limitation step for a profile. -/
def Inputs (m : Profile Unit Bool) : Prop :=
  ExistingInActAt m.ontic flat.InAct flat.esse () ∧
  EsseCauseIsActualConcreteGround m () flat.CausesIn flat.esse ∧
  DistinctEsseCauseDichotomyReading flat ∧
  EssentialPrinciplesCannotCauseDistinctEsseReading flat ∧
  SimplyPriorIsActualConcreteGround m () none2 ∧
  CompositePosteriorToComponentsReading none2 none2 ∧
  CompositeHasComponentOtherThanItselfReading none1 none2

/-- Two ungrounded candidates. -/
abbrev twoRoots := TruthCore.Causality.PureActRoot.Control.twoRoots
/-- `true` grounds `false`. -/
abbrev oneRoot := TruthCore.Causality.PureActRoot.Control.oneRoot

/-- Only `false` has the one determination. -/
def onlyFalse (x : Bool) (_ : Unit) : Prop := x = false

/-- Single first mover `true`: it moves, nothing is moved. -/
def fmMoved (_ : Bool) (_ : Unit) : Prop := False
def fmMoves (f _ : Bool) (_ : Unit) : Prop := f = true

/-- Finite one-world interpretations; excluded middle is not asserted.
* Bridge omitted: the seven inputs hold, both roots are unlimited, each has a
  non-pure determination, and strict pure actuality at the roots fails.
* Positive witness: the seven inputs and the bridge hold, and so does strict
  pure actuality at the roots.
* The bridge exceeds what the roots need: with one root, strict pure actuality
  at the roots holds while the bridge fails at the unlimited non-root `false`.
* First-mover bridge omission: a single simple first mover that is first in
  being has a non-pure determination; the bridge and strict pure actuality for
  first movers fail. -/
def Certificate : Prop :=
  (Inputs twoRoots ∧
    ActualRootsWithoutLimitingPrinciple twoRoots () none1 none2 flat.essenceOf flat.esseOf ∧
    ¬ UnlimitedDeterminationsArePure none1 none2 flat.essenceOf flat.esseOf
      (fun _ (_ : Unit) => True) (fun _ => False) ∧
    ¬ ActualRootDeterminationsArePure twoRoots () (fun _ (_ : Unit) => True) (fun _ => False)) ∧
  (Inputs twoRoots ∧
    UnlimitedDeterminationsArePure none1 none2 flat.essenceOf flat.esseOf
      (fun _ (_ : Unit) => True) (fun _ => True) ∧
    ActualRootDeterminationsArePure twoRoots () (fun _ (_ : Unit) => True) (fun _ => True) ∧
    ActualRoot twoRoots () true) ∧
  (Inputs oneRoot ∧
    ActualRootDeterminationsArePure oneRoot () onlyFalse (fun _ => False) ∧
    ¬ UnlimitedDeterminationsArePure none1 none2 flat.essenceOf flat.esseOf
      onlyFalse (fun _ => False) ∧
    ActualRoot oneRoot () true ∧ ¬ ActualRoot oneRoot () false) ∧
  (FirstUnmovedMoverIsSimpleReading fmMoved fmMoves none1 none1 none1 flat.essenceOf flat.esseOf ∧
    TruthCore.Case.Catholicism.FirstUnmovedMoverIsFirstBeing fmMoved fmMoves none2 ∧
    TruthCore.Case.Catholicism.IsFirstUnmovedMover fmMoved fmMoves true ∧
    ¬ UnlimitedDeterminationsArePure none1 none2 flat.essenceOf flat.esseOf
      (fun _ (_ : Unit) => True) (fun _ => False) ∧
    ¬ TruthCore.Causality.PureActThisness.FirstMoverDeterminationsArePure fmMoved fmMoves
      (fun _ (_ : Unit) => True) (fun _ => False))

end Control
end TruthCore.Causality.RootPurity
