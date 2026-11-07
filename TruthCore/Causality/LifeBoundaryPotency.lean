module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.BoethianEternity
public import TruthCore.Logic.ExcludedMiddle

/-! Life boundary requires potency, as the contrapositive of q.10 a.1

`STMT-LIFE-BOUNDARY-REQUIRES-POTENCY` (whatever begins or ceases to live is in
potency in some respect) reaches the root without a derivation. ST I q.10 a.1
says that what is altogether immutable can have neither beginning nor end
(`STMT-ALTOGETHER-IMMUTABLE-HAS-NO-BEGINNING-OR-END`, previously without a Lean
binding or consumer). Reading "altogether immutable" as "in potency in no
respect" (`ImmutableHasNoLifeBoundary`), the target is its contrapositive under
excluded middle. This is a logical rearrangement, not new content: the gap the
open premise carried (q.9's mutability through a power in another versus
potency in the subject, `DISAMB-POTENCY-IN-SUBJECT-VS-IN-ANOTHER`) now sits in
the reading of *omnino immutabile*. -/

@[expose] public section

namespace TruthCore.Causality.LifeBoundaryPotency
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct LifeBeginsOrEnds)

/-- q.10 a.1, with "altogether immutable" read as "in potency in no respect":
such a being's life neither begins nor ends. -/
def ImmutableHasNoLifeBoundary {B R T : Type} [LT T] (InPotency : B → R → Prop)
    (LivesAt : B → T → Prop) : Prop :=
  ∀ x, PureAct InPotency x → ¬ LifeBeginsOrEnds LivesAt x

namespace Control
open TruthCore.Latin.Aquinas.SummaTheologiae (LifeBoundaryRequiresPotencyReading)

/-- One being with no potency that lives at `true` only: its life begins. -/
def livesLater (_ : Unit) (t : Bool) : Prop := t = true
def noPotency (_ _ : Unit) : Prop := False

/-- Without the q.10 a.1 premise, a pure act's life begins and the conclusion
fails; with no life boundary anywhere, both hold. -/
def Certificate : Prop :=
  (¬ ImmutableHasNoLifeBoundary noPotency livesLater ∧
    ¬ LifeBoundaryRequiresPotencyReading noPotency livesLater) ∧
  (ImmutableHasNoLifeBoundary noPotency (fun (_ : Unit) (_ : Bool) => True) ∧
    LifeBoundaryRequiresPotencyReading noPotency (fun (_ : Unit) (_ : Bool) => True))

end Control
end TruthCore.Causality.LifeBoundaryPotency
