import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question75.Article2

/-!
ST I q.75 a.2 co., the organ step after the first non-bodyhood inference.
The pinned Latin witness is `AQUINAS-ST-I-Q75-A1-A2`, anchor 31460;
reply 3 (31463) distinguishes an organ of exercise from bodily dependence
on the side of the object. Q.76 a.1 ad 1 (31513) repeats that distinction.

The existing `Model`, cognitive capacity and bodily determinacy are reused.
The extra relation `through i b` means that i's intellectual operation can
be exercised through b as an instrument. It does not mean that b supplies
phantasms, that cognition has no bodily conditions, or that a modern physical
realization is already excluded. Its organ-level interference constraint
is an explicit premise, not a consequence of non-bodyhood.
-/
namespace TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect

/-- Q.75 a.2 co., `natura determinata illius organi corporei prohiberet ...`:
if intellectual exercise uses a bodily organ with a naturally constitutive
bodily nature, that nature would prevent the universal bodily cognitive
capacity. This is the source's disputed organ-interference premise, not a
proved generalization from the colored-vessel illustration. -/
def OrganBodilyInterference {Principle Nature : Type}
    (m : Model Principle Nature) (through : Principle → Principle → Prop)
    (intellect : Principle) : Prop :=
  ∀ organ n, through intellect organ → m.IsBody organ →
    m.BodilyNature n → m.HasNaturally organ n →
    ¬ UniversalBodilyCognition m intellect

/-- No body can be an instrument through which the designated intellectual
operation is exercised (q.75 a.2 co.). `through` concerns capacity for such
exercise; it is not an individual episode of thinking. This does not deny
object-side bodily dependence (q.75 a.2 ad 3), establish subsistence, or
refute all physical realizations or every form of physicalism. -/
def IntellectUsesNoBodilyOrgan {Principle Nature : Type}
    (m : Model Principle Nature) (through : Principle → Principle → Prop)
    (intellect : Principle) : Prop :=
  ¬ ∃ organ, m.IsBody organ ∧ through intellect organ

end TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect
