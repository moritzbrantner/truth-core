import TruthCore.Causality.PartFreePlurality

/-! #697: a proposed constitutive-content route to the existing Q11 theorem.
These are openly stipulated interfaces, not historical claims, a second ontology,
or a definition of God. Equality of represented natures remains distinct from
numerical identity of beings and from equality of labels or eminent perfections. -/
namespace TruthCore.Causality.ConstitutiveNatureUniqueness
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The proposed content is complete for identity of the represented nature.
This is an independently disputed extensionality principle, not mere agreement
on a list of names and not a consequence of the word `essence`. -/
def ConstitutiveContentComplete {P R : Type} (content : P → R → Prop) : Prop :=
  ∀ p q, (∀ r, content p r ↔ content q r) → p = q

/-- The contents of each first mover's represented nature agree with the SAME
act/perfection predicate used by every-perfection. In a virtual/eminent reading
this is substantially stronger than a difference in formal character. -/
def FirstMoverContentAgreesWithAct {B P R : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (InAct : B → R → Prop) (essence : B → P) (content : P → R → Prop) : Prop :=
  ∀ f, IsFirstUnmovedMover Moved Moves f → ∀ r,
    content (essence f) r ↔ InAct f r

/-- Explicit OPEN applicability adapter: the Q11 suppositum/nature identity is
required of the first-mover candidates. Q3a3's attributed claim about God is not
silently broadened to every necessary or underived actual individual. -/
def FirstMoverSuppositumIsNature {B P R : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (suppositum essence : B → P) : Prop :=
  GodSuppositumIsNatureReading (IsFirstUnmovedMover Moved Moves) suppositum essence

namespace Control
open TruthCore.Causality.PartFreePlurality

/-- Copy the original represented act profile. This agrees on the roots but
forgets their distinct primitive essence values. It is not complete content. -/
def actContent (p : Being) (r : Respect) : Prop := inAct p r

/-- An injective five-row constitutive code on the SAME principle carrier.
Only the code differs between controls; no ontic, causal, power, composition,
identity, essence, suppositum or original act assignment is changed.
These three tests are assignment data, not attributed real perfections. -/
def separatingContent : Being → Respect → Prop :=
  Being.rec (motive := fun _ => Respect → Prop)
    (fun _ => True)
    (TruthCore.Causality.NecessarySimplePlurality.Respect.rec (motive := fun _ => Prop) True True False)
    (TruthCore.Causality.NecessarySimplePlurality.Respect.rec (motive := fun _ => Prop) True False True)
    (TruthCore.Causality.NecessarySimplePlurality.Respect.rec (motive := fun _ => Prop) False True True)
    (TruthCore.Causality.NecessarySimplePlurality.Respect.rec (motive := fun _ => Prop) False False True)

/-- The original full joint model survives either individual proposed
strengthening, but not both. This is a SAME-interpretation omission test, not
metaphysical possibility or an adequate account of primitive individuation. -/
def Certificate : Prop :=
  JointControl ∧
  FirstMoverSuppositumIsNature moved moves suppositum essence ∧
  FirstMoverContentAgreesWithAct moved moves inAct essence actContent ∧
  ¬ ConstitutiveContentComplete actContent ∧
  ConstitutiveContentComplete separatingContent ∧
  ¬ FirstMoverContentAgreesWithAct moved moves inAct essence separatingContent
/-- The existing positive witness's constitutive table, named so the finite
model registry can bind the exact data without choosing from an existential
proof. This is definitionally the former local table, not a new interpretation. -/
def positiveContent : TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.B →
    TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.R → Prop :=
  TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.B.rec
    (motive := fun _ => TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.R → Prop)
    (fun _ => True)
    (TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.R.rec (motive := fun _ => Prop) True False)
    (fun _ => False)
    (TruthCore.Results.Aquinas.SummaTheologiae.OneFirstMover.Joint.R.rec (motive := fun _ => Prop) False True)

end Control
end TruthCore.Causality.ConstitutiveNatureUniqueness
