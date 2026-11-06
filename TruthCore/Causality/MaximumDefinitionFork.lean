module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaGreatestDegree
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
public import TruthCore.Logic.ExcludedMiddle

/-! Analyst interfaces between maximality and greatestness. Existing source
 greatest-degree and old weak maximal predicates remain unchanged. Represented
 degrees are supplied, not a theorem that analogical being is homogeneous.
 Directedness below ranges over the selected perfection's actual bearers only;
 neither totality, injective values nor uniqueness is hidden in the frame.
 Causal responsibility is the existing CausesIn, separate from order.
-/

@[expose] public section
namespace TruthCore.Causality.MaximumDefinitionFork
open TruthCore.Latin.Aquinas.SummaTheologiae

structure Frame (Degree : Type) where
  Being : Type
  Respect : Type
  InAct : Being → Respect → Prop
  MoreIn : Respect → Being → Being → Prop
  CausesIn : Being → Being → Respect → Prop
  selected : Respect
  value : Being → Degree
  Maxime : Being → Prop

variable {Degree : Type} [Preorder Degree]

def StrictDegreeCalibration (f : Frame Degree) : Prop :=
  ∀ x y, f.InAct x f.selected → f.InAct y f.selected →
    (f.MoreIn f.selected x y ↔ f.value y < f.value x)

def DirectedBearers (f : Frame Degree) : Prop :=
  ∀ x y, f.InAct x f.selected → f.InAct y f.selected →
    ∃ z, f.InAct z f.selected ∧ f.value x ≤ f.value z ∧ f.value y ≤ f.value z

/-- Weak interface sufficient for transporting the greatest-degree causal
principle to the old merely-maximal antecedent at the selected respect. -/
def MaximalToGreatest (f : Frame Degree) : Prop :=
  ∀ m, IsMaximumIn f.InAct f.MoreIn f.selected m →
    GreatestDegreeBearer f.InAct f.selected f.value m

def StrictGreatest (f : Frame Degree) (m : f.Being) : Prop :=
  f.InAct m f.selected ∧ ∀ x, f.InAct x f.selected → x ≠ m → f.value x < f.value m

def MaximalDefinition (f : Frame Degree) : Prop :=
  ∀ m, f.Maxime m ↔ IsMaximumIn f.InAct f.MoreIn f.selected m

def GreatestDefinition (f : Frame Degree) : Prop :=
  ∀ m, f.Maxime m ↔ GreatestDegreeBearer f.InAct f.selected f.value m

def StrictDefinition (f : Frame Degree) : Prop :=
  ∀ m, f.Maxime m ↔ StrictGreatest f m

def MaximalDefinitionFails (f : Frame Degree) : Prop := ¬ MaximalDefinition f
def StrictDefinitionFails (f : Frame Degree) : Prop := ¬ StrictDefinition f

def NamedCoverage (f : Frame Degree) : Prop :=
  MaximalDefinition f ∨ GreatestDefinition f ∨ StrictDefinition f

def Other (f : Frame Degree) : Prop :=
  ¬ MaximalDefinition f ∧ ¬ GreatestDefinition f ∧ ¬ StrictDefinition f

def DefinitionFork : Prop := ∀ f : Frame Degree, NamedCoverage f ∨ Other f

/-- Fixed two incomparable represented degrees in the standard product order.
No new order is defined. This is a formal profile, not analogical being. -/
def incomparable : Frame (Bool × Bool) where
  Being := Bool
  Respect := Unit
  InAct := fun _ _ => True
  MoreIn := fun _ _ _ => False
  CausesIn := fun _ _ _ => False
  selected := ()
  value := fun x => if x then (true, false) else (false, true)
  Maxime := fun _ => True

/-- Distinct actual bearers tied at one represented degree; maximal and greatest
can agree without strict supremacy or uniqueness. -/
def tied : Frame Unit where
  Being := Bool
  Respect := Unit
  InAct := fun _ _ => True
  MoreIn := fun _ _ _ => False
  CausesIn := fun _ _ _ => True
  selected := ()
  value := fun _ => ()
  Maxime := fun _ => True

/-- A selective primitive superlative agrees with neither all tied maxima nor
strict supremacy (which has no instance here). -/
def remainder : Frame Unit := { tied with Maxime := fun x => x = true }

def Controls : Prop :=
  (StrictDegreeCalibration incomparable ∧ MaximalDefinition incomparable ∧
    ¬ GreatestDefinition incomparable ∧ ¬ MaximalToGreatest incomparable ∧
    GreatestDegreeCausesAllInGenusReading incomparable.InAct incomparable.CausesIn
      incomparable.selected incomparable.value ∧
    ¬ MaximumInBeingCausesAllBeingsReading incomparable.InAct incomparable.MoreIn
      incomparable.CausesIn incomparable.selected) ∧
  (DirectedBearers tied ∧ StrictDegreeCalibration tied ∧ MaximalDefinition tied ∧
    GreatestDefinition tied ∧ ¬ StrictDefinition tied ∧
    (∃ m n, m ≠ n ∧ GreatestDegreeBearer tied.InAct tied.selected tied.value m ∧
      GreatestDegreeBearer tied.InAct tied.selected tied.value n)) ∧ Other remainder

end TruthCore.Causality.MaximumDefinitionFork
