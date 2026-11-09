module

@[expose] public section
namespace TruthCore.Causality.ExistsSenseMeaning

/-- EXISTS_1: a witness from the candidate domain satisfying P. No actuality guard. -/
inductive DomainExists {E : Type} (P : E → Prop) : Prop where
  | intro (witness : E) (satisfies : P witness)

/-- EXISTS_2: a candidate satisfying P and the supplied existence extension at w.
The primitive ex predicate is not defined as act in esse. -/
inductive ActualExists {W E : Type} (ex : W → E → Prop) (w : W)
    (P : E → Prop) : Prop where
  | intro (witness : E) (existsAt : ex w witness) (satisfies : P witness)

/-- The same inhabited candidate type admits an empty actual extension;
a full actual extension gives a positive witness. No modal frame is involved. -/
def Controls : Prop :=
  DomainExists (fun _ : Unit => True) ∧
  ¬ ActualExists (fun (_ : Unit) (_ : Unit) => False) () (fun _ => True) ∧
  ActualExists (fun (_ : Unit) (_ : Unit) => True) () (fun _ => True)
end TruthCore.Causality.ExistsSenseMeaning
