module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1

/-! Actuality only insofar as being, from "perfect insofar as having being"
(ST I q.4 a.2 with q.5 a.1)

`STMT-ACTUALITY-ONLY-INSOFAR-AS-BEING` (q.4 a.1 ad 3) is an underived leaf of
every root route. ST I q.4 a.2 gives a reason close to it: *secundum hoc enim
aliqua perfecta sunt, quod aliquo modo esse habent*, things are perfect insofar
as they have being in some way (`PerfectOnlyInsofarAsBeing`). With q.5 a.1's
"each thing is perfect insofar as it is in act" (`PerfectInsofarAsInActReading`),
whatever is in act in a respect is perfect in it, and so has being. The q.4 a.2
clause is the definition-linked statement
`STMT-ALL-PERFECTIONS-PERTAIN-TO-PERFECTION-OF-BEING`, encoded here as a
supported sibling. -/

@[expose] public section

namespace TruthCore.Causality.PerfectionOfBeing

/-- q.4 a.2: whatever is perfect in some respect has being. -/
def PerfectOnlyInsofarAsBeing {B R : Type} (PerfectIn InAct : B → R → Prop) (esse : R) : Prop :=
  ∀ x r, PerfectIn x r → InAct x esse

namespace Control
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Respect `false` is esse, `true` another perfection; the one being is in act
in `true` only. -/
def actTrue (_ : Unit) (r : Bool) : Prop := r = true
def perfectTrue (_ : Unit) (r : Bool) : Prop := r = true
def perfectNone (_ : Unit) (_ : Bool) : Prop := False
def actAll (_ : Unit) (_ : Bool) : Prop := True

/-- Without q.5 a.1 the being is in act in a respect without being perfect in it;
without q.4 a.2 it is perfect without having being; in both cases it lacks being.
With everything in act, both premises and the conclusion hold. -/
def Certificate : Prop :=
  (¬ PerfectInsofarAsInActReading perfectNone actTrue ∧
    PerfectOnlyInsofarAsBeing perfectNone actTrue false ∧
    ¬ ActualityOnlyInsofarAsBeingReading actTrue false) ∧
  (PerfectInsofarAsInActReading perfectTrue actTrue ∧
    ¬ PerfectOnlyInsofarAsBeing perfectTrue actTrue false ∧
    ¬ ActualityOnlyInsofarAsBeingReading actTrue false) ∧
  (PerfectInsofarAsInActReading actAll actAll ∧
    PerfectOnlyInsofarAsBeing actAll actAll false ∧
    ActualityOnlyInsofarAsBeingReading actAll false)

end Control
end TruthCore.Causality.PerfectionOfBeing
