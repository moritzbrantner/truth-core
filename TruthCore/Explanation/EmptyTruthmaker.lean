module

public import TruthCore.Explanation.TruthmakerTheories
public import TruthCore.Logic.Configuration

/-! #554: one negative proposition over an unchanged eligible individual roster.
The negative proposition means absolute eligible-domain absence. It is not a
new truthbearer ontology: `arena` embeds that one proposition into the existing
Arena solely to consume its checked pointwise contradiction. No coherence of
existence labels, modal axiom, domain completeness or metaphysical possibility
is asserted. Making is primitive; factivity is independently testable. -/
@[expose] public section
namespace TruthCore.Explanation.EmptyTruthmaker
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.TruthmakerTheories
variable {W B : Type}

def Empty (present : W → B → Prop) (w : W) : Prop := ∀ b, ¬ present w b

/-- E: an accessible world has no eligible existent, including abstracts if
those belong to the roster. An inhabited outer roster is not an existent. -/
def EmptyPossible (F : TruthCore.Modal.Frame W) (present : W → B → Prop) (a : W) : Prop :=
  ∃ w, F.access a w ∧ Empty present w

/-- T: the single true negative requires a maker at each accessible world.
This is weaker than coverage of every represented truth. -/
def NegativeCoverage (F : TruthCore.Modal.Frame W) (present makes : W → B → Prop)
    (a : W) : Prop := ∀ w, F.access a w → Empty present w → ∃ b, makes w b

/-- I: makers of this negative exist at their making world in the component.
Neither factivity nor existence elsewhere substitutes for this condition. -/
def Immanence (F : TruthCore.Modal.Frame W) (present makes : W → B → Prop)
    (a : W) : Prop := ∀ w, F.access a w → ∀ b, makes w b → present w b

def NegativeFactivity (F : TruthCore.Modal.Frame W) (present makes : W → B → Prop)
    (a : W) : Prop := ∀ w, F.access a w → ∀ b, makes w b → Empty present w

/-- A one-fact adapter, not a coherent ontology of all existence facts. -/
def arena (F : TruthCore.Modal.Frame W) (present : W → B → Prop) : Arena W B Unit where
  ontic := { frame := F, ExistsAt := present, Causes := fun _ _ _ => False }
  holds := fun w _ => Empty present w
  exist := fun _ => ()
  explains := fun _ _ _ => False
  conjunct := fun _ _ => True

/-- Restriction preserves the exact accessible scope of T and I. -/
def scopedMaking (F : TruthCore.Modal.Frame W) (makes : W → B → Prop)
    (a : W) : Making W B Unit := fun w b _ => F.access a w ∧ makes w b

/-- Single-world pullbacks of the already certified negativeArena controls.
No new ontology is introduced by changing the finite world representation. -/
def oneFrame : TruthCore.Modal.Frame Unit := ⟨fun _ _ => True⟩
def presentControl (inhabited : Bool) : Unit → Unit → Prop :=
  fun _ b => negativeArena.ontic.ExistsAt inhabited b
def populatedControl : Unit → Unit → Prop := presentControl false
def emptyControl : Unit → Unit → Prop := presentControl true
def absentMaking : Unit → Unit → Prop := fun _ b => outsideMaking true b .empty
def noMaker : Unit → Unit → Prop := fun _ b => noMaking true b NFact.empty

/-- Concrete emptiness keeps the existing supplied concrete extension separate
from existence. Its truth and interpretation are both explicit in this premise. -/
def ConcreteEmptyAt {W B K : Type} (A : Arena W B K)
    (C : W → B → Prop) (w : W) (f : K) : Prop :=
  ConcreteEmptyFact A C f ∧ A.holds w f

end TruthCore.Explanation.EmptyTruthmaker
