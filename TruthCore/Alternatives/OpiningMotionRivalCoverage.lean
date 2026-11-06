module

public import TruthCore.Alternatives.ActPotencyRegress
public import TruthCore.Logic.ExcludedMiddle

/-!
# An unmoved opiner versus the stronger global-no-motion account

The old norm demands motion of each opiner in its supplied asOpinion respect.
The existing raw rival denies ALL motion and grants an opinion. It genuinely
opposes that norm but is stronger than an actual local countertuple: another
being can move while this opiner misses its designated motion. No source
identification or metaphysical possibility is established by the finite table.
-/
@[expose] public section
namespace TruthCore.Alternatives.OpiningMotionRivalCoverage
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Latin.Aquinas.SummaTheologiae

def Countertuple {B R : Type} (MovedIn : B → R → Prop) (Opines : B → Prop → Prop)
    (asOpinion : Prop → R) : Prop :=
  ∃ x p, Opines x p ∧ ¬ MovedIn x (asOpinion p)

def NormFails {B R : Type} (MovedIn : B → R → Prop) (Opines : B → Prop → Prop)
    (asOpinion : Prop → R) : Prop :=
  ¬ OpiningIsBeingMovedReading MovedIn Opines asOpinion

def OpinionMotionFork {B R : Type} (MovedIn : B → R → Prop) (Opines : B → Prop → Prop)
    (asOpinion : Prop → R) : Prop :=
  OpiningIsBeingMovedReading MovedIn Opines asOpinion ∨ Countertuple MovedIn Opines asOpinion

def mixedMoved : Bool → Unit → Prop := fun x _ => x = true
def mixedOpinions : Bool → Prop → Prop := fun x _ => x = false
def mixedRespect : Prop → Unit := fun _ => ()

/-- The target countertuple, actual opinion, and other being's motion are all
exported; this is a populated formal scope control, not a thinking subject in reality. -/
def Controls : Prop :=
  (∃ x y p, x ≠ y ∧ mixedOpinions x p ∧ (∀ r, ¬ mixedMoved x r) ∧ mixedMoved y ()) ∧
  SomethingIsMovedReading mixedMoved ∧
  Countertuple mixedMoved mixedOpinions mixedRespect ∧
  ¬ ChangeUnrealButAppearsReading mixedMoved mixedOpinions ∧
  NormFails mixedMoved mixedOpinions mixedRespect
end TruthCore.Alternatives.OpiningMotionRivalCoverage
