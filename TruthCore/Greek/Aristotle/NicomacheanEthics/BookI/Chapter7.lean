/-!
Bounded readings of Aristotle, Nicomachean Ethics I.7, 1097b22–1098a20.
The pinned Greek witness ARIST-EN-I-7 was materialized and read, including the
whole chapter. These are source commitments, not proofs of the function
argument or an inference from biological function to categorical obligation.
-/
namespace TruthCore.Greek.Aristotle.NicomacheanEthics

/-- 1097b25–28 and 1098a7–15: for an exercise of a role with a characteristic
function, goodness of the exercise qua that role requires excellent performance.
Only the necessary-condition direction of the analogy is recorded. Role,
function assignment and excellent exercise are independent parameters; the
reading neither proves a human function exists nor identifies its standard
with current approval. `GoodQuaRole` evaluates the exercise, not a practitioner
as a persisting bearer of skill: no claim that a good practitioner always acts
well is made. It is not all-things-considered moral worth.
-/
def FunctionExcellenceReading {Exercise Role Function : Type}
    (ExerciseOfRole : Exercise → Role → Prop) (HasFunction : Role → Function → Prop)
    (GoodQuaRole : Exercise → Role → Prop)
    (ExcellentExercise : Exercise → Function → Prop) : Prop :=
  ∀ x r f, ExerciseOfRole x r → HasFunction r f →
    GoodQuaRole x r → ExcellentExercise x f

/-- 1098a7–20: the human good is actual rational activity of soul according to
virtue, over a complete life. Only necessary conditions are recorded. Here
`VirtuousActivity` means activity according to the appropriate excellence
(and, where several virtues are at issue, the best and most complete), not
mere success at an arbitrary assigned task. No internal account or ordering of
virtues is supplied by these parameters. `RationalActivity` is exercise, not
mere capacity; `CompleteLife` is not a numerical duration threshold. The
reading asserts no happy-life witness or categorical obligation to pursue it.
-/
def HumanGoodActivityReading {Life : Type}
    (HumanGood RationalActivity VirtuousActivity CompleteLife : Life → Prop) : Prop :=
  ∀ life, HumanGood life →
    RationalActivity life ∧ VirtuousActivity life ∧ CompleteLife life

end TruthCore.Greek.Aristotle.NicomacheanEthics
