module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.BoethianEternity
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3

/-! Pure act lives, from life as self-operation (ST I q.18 a.3)

`STMT-PURE-ACT-LIVES` (an open premise of the eternity route) reaches the root
without a derivation. Q.18 a.3 co. says that things are said to live insofar as
they operate from themselves and not as moved by others (*vivere dicuntur aliqua
secundum quod operantur ex seipsis, et non quasi ab aliis mota*), and ad 2 that
God is his own understanding and his own living. Typed:
* `SelfOperatingUnmovedLives`: whatever operates from itself and is moved in no
  respect lives at some time of the frame;
* `PureActOperates`: whatever is in potency in no respect operates from itself;
* the route premise `MovedOnlyAsInPotencyReading`: whatever is moved in a respect
  is in potency in it, so a pure act is moved in no respect.
`Operates` is a primitive predicate (immanent operation, *actio quae manet in
agente*, ad 1), not motion. -/

@[expose] public section

namespace TruthCore.Causality.SelfOperationLife
open TruthCore.Latin.Aquinas.SummaTheologiae (PureAct)

variable {B R T : Type}

/-- q.18 a.3 co.: whatever operates from itself and is moved in no respect lives
at some time of the duration frame. -/
def SelfOperatingUnmovedLives (Operates : B → Prop) (MovedIn : B → R → Prop)
    (LivesAt : B → T → Prop) : Prop :=
  ∀ x, Operates x → (∀ r, ¬ MovedIn x r) → ∃ t, LivesAt x t

/-- Bridge supported by q.18 a.3 ad 2 (said there of God): whatever is in potency
in no respect operates from itself. -/
def PureActOperates (InPotency : B → R → Prop) (Operates : B → Prop) : Prop :=
  ∀ x, PureAct InPotency x → Operates x

namespace Control
open TruthCore.Latin.Aquinas.SummaTheologiae (PureActLivesReading MovedOnlyAsInPotencyReading)

def none1 (_ : Unit) : Prop := False
def all1 (_ : Unit) : Prop := True
def none2 (_ _ : Unit) : Prop := False
def all2 (_ _ : Unit) : Prop := True

/-- One being in potency in no respect. Omitting the operation bridge, the life
premise, or the potency premise (it is moved without potency) leaves it without
life; with all three it lives. -/
def Certificate : Prop :=
  (¬ PureActOperates none2 none1 ∧
    SelfOperatingUnmovedLives none1 none2 none2 ∧
    MovedOnlyAsInPotencyReading none2 none2 ∧
    ¬ PureActLivesReading none2 none2) ∧
  (PureActOperates none2 all1 ∧
    ¬ SelfOperatingUnmovedLives all1 none2 none2 ∧
    MovedOnlyAsInPotencyReading none2 none2 ∧
    ¬ PureActLivesReading none2 none2) ∧
  (PureActOperates none2 all1 ∧
    SelfOperatingUnmovedLives all1 all2 none2 ∧
    ¬ MovedOnlyAsInPotencyReading all2 none2 ∧
    ¬ PureActLivesReading none2 none2) ∧
  (PureActOperates none2 all1 ∧
    SelfOperatingUnmovedLives all1 none2 all2 ∧
    MovedOnlyAsInPotencyReading none2 none2 ∧
    PureActLivesReading none2 all2)

end Control
end TruthCore.Causality.SelfOperationLife
