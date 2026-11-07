module

public import TruthCore.Case.Catholicism.StageOneQuartaVia
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Greek.Aristotle.Metaphysics
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaAscent
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article2

/-! Preexistence of perfections from causal transfer and "more such" (#320)

`STMT-PERFECTIONS-OF-EFFECT-PREEXIST-IN-CAUSE` (ST I q.4 a.2, first proof) is an
open leaf of every route to `STMT-CATHOLICISM-TRUE` with no derivation. It follows
from:
* `CauseOfBeingCausesEveryPerfection`, a premise of the same routes;
* `CauseOfQualityInAnotherIsMoreSuchReading`, a premise of the same routes;
* `MoreSuchHasThePerfectionReading`, the Quarta Via premise that what is more such
  has the perfection;
* excluded middle on whether the cause is the effect itself.

For a distinct cause, it causes the perfection, so it is more such, so it has the
perfection. If cause and effect coincide, the effect's perfection is the cause's.
So the route premise set is not independent modulo the Quarta Via "more such"
premise. Analyst composition; attribution deferred. -/

@[expose] public section

namespace TruthCore.Causality.PerfectionPreexistence
open TruthCore.Case.Catholicism (CauseOfBeingCausesEveryPerfection)
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Latin.Aquinas.SummaTheologiae
  (MoreSuchHasThePerfectionReading PerfectionsOfEffectPreexistInCauseReading)

namespace Control

/-- Respect `false` is esse, `true` a further perfection. Everything is in act in
esse; only `false` is in act in the further perfection. -/
def inAct (x r : Bool) : Prop := r = false ∨ x = false

/-- `true` causes the being of `false` only. -/
def causesBeing (c x r : Bool) : Prop := c = true ∧ x = false ∧ r = false
/-- `true` causes `false` in every respect. -/
def causesAll (c x _ : Bool) : Prop := c = true ∧ x = false
/-- `true` exceeds `false` in esse only. -/
def moreBeing (r y x : Bool) : Prop := y = true ∧ x = false ∧ r = false
/-- `true` exceeds `false` in every respect. -/
def moreAll (_ y x : Bool) : Prop := y = true ∧ x = false
def noMore (_ _ _ : Bool) : Prop := False

/-- Finite interpretations; excluded middle is not asserted. Each of the three
non-logical premises is omitted in turn with the other two holding, and
preexistence fails; all three and preexistence hold together. -/
def Certificate : Prop :=
  (¬ CauseOfBeingCausesEveryPerfection inAct causesBeing false ∧
    CauseOfQualityInAnotherIsMoreSuchReading causesBeing moreBeing ∧
    MoreSuchHasThePerfectionReading inAct moreBeing ∧
    ¬ PerfectionsOfEffectPreexistInCauseReading inAct causesBeing false) ∧
  (CauseOfBeingCausesEveryPerfection inAct causesAll false ∧
    ¬ CauseOfQualityInAnotherIsMoreSuchReading causesAll noMore ∧
    MoreSuchHasThePerfectionReading inAct noMore ∧
    ¬ PerfectionsOfEffectPreexistInCauseReading inAct causesAll false) ∧
  (CauseOfBeingCausesEveryPerfection inAct causesAll false ∧
    CauseOfQualityInAnotherIsMoreSuchReading causesAll moreAll ∧
    ¬ MoreSuchHasThePerfectionReading inAct moreAll ∧
    ¬ PerfectionsOfEffectPreexistInCauseReading inAct causesAll false) ∧
  (CauseOfBeingCausesEveryPerfection (fun _ _ => True) causesAll false ∧
    CauseOfQualityInAnotherIsMoreSuchReading causesAll moreAll ∧
    MoreSuchHasThePerfectionReading (fun _ _ => True) moreAll ∧
    PerfectionsOfEffectPreexistInCauseReading (fun _ _ => True) causesAll false ∧
    causesAll true false true)

end Control
end TruthCore.Causality.PerfectionPreexistence
