import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question5.Article1
namespace TruthCore.Results.Aquinas.SummaTheologiae.GoodnessFromDesirability
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- ST I q.5 a.1 co.: a thing is good in a perfection exactly when it actually
has that perfection, derived from the article's own three steps: the notion of
good is the desirable (`GoodIsDesirableReading`), each thing is desirable
insofar as it is perfect (`DesirableInsofarAsPerfectReading`), and each thing
is perfect insofar as it is in act (`PerfectInsofarAsInActReading`).

`GoodIn`, `DesirableIn`, `PerfectIn` and `Has` are independent parameters; no
premise is a definition and none has the conclusion as its consequent, so the
proof composes three distinct relations and could fail: `premisesNeeded` gives,
for each premise, a model of the other two in which the conclusion is false.
The conclusion is exactly the existing reading `GoodnessIsActualityReading`
(statement `STMT-GOODNESS-IS-ACTUALITY`). The article's last clause
(*esse enim est actualitas omnis rei*), which carries the conclusion from act
to being, is not used: the existing reading stops at act. -/
theorem goodnessIsActualityFromDesirability {Being Perfection : Type}
    (GoodIn DesirableIn PerfectIn Has : Being → Perfection → Prop)
    (hGood : GoodIsDesirableReading GoodIn DesirableIn)
    (hDesirable : DesirableInsofarAsPerfectReading DesirableIn PerfectIn)
    (hPerfect : PerfectInsofarAsInActReading PerfectIn Has) :
    GoodnessIsActualityReading GoodIn Has := by
  -- INF-AQUINAS-ST-I-Q5-A1-GOODNESS-FROM-DESIRABILITY
  intro x p
  -- good as desirable, desirable as perfect
  have hGoodPerfect : GoodIn x p ↔ PerfectIn x p := (hGood x p).trans (hDesirable x p)
  -- perfect as in act
  exact hGoodPerfect.trans (hPerfect x p)

/-- Each premise is needed, and the premises are jointly satisfiable with
something good (models over `Unit`). -/
theorem premisesNeeded : GoodnessFromDesirabilityPremisesNeeded := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- without "good is the desirable": nothing is good, everything else holds
    intro hAll
    have h := hAll Unit Unit (fun _ _ => False) (fun _ _ => True) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    exact (h () ()).mpr trivial
  · -- without "desirable insofar as perfect": nothing good or desirable; all perfect, all actual
    intro hAll
    have h := hAll Unit Unit (fun _ _ => False) (fun _ _ => False) (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    exact (h () ()).mpr trivial
  · -- without "perfect insofar as in act": nothing good, desirable or perfect; all actual
    intro hAll
    have h := hAll Unit Unit (fun _ _ => False) (fun _ _ => False) (fun _ _ => False)
      (fun _ _ => True) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    exact (h () ()).mpr trivial
  · -- all four predicates true
    exact ⟨fun _ _ => True, fun _ _ => True, fun _ _ => True, fun _ _ => True,
      fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, trivial⟩

end TruthCore.Results.Aquinas.SummaTheologiae.GoodnessFromDesirability
