/-!
ST I q.75 a.2 co., first subconclusion (not a body), read from the pinned Latin
`AQUINAS-ST-I-Q75-A1-A2`. This module does not formalize the subsequent organ,
per-se-operation or subsistence steps. In particular, not being a body is not
identified with the rejection of every physical realization of cognition.

The existing `IntellectWill.ImmaterialIsIntellectualReading` concerns the
opposite implication and the highest immateriality of God. Its primitive
`HasIntellect` predicate does not supply a cognitive scope or a theory of
representation. This local typed vocabulary is therefore distinct, without
changing or restating that earlier conclusion as a premise.
-/
namespace TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect

/-- Typed vocabulary for the first q.75 a.2 inference. `BodilyNature` selects
natures of bodies; `HasNaturally` is constitutive possession, not representing
that nature as an object. `CanUnderstand` is a capacity, not a current act or
omniscience. The designated intellectual principle is a theorem parameter. -/
structure Model (Principle Nature : Type) where
  IsBody : Principle → Prop
  BodilyNature : Nature → Prop
  HasNaturally : Principle → Nature → Prop
  CanUnderstand : Principle → Nature → Prop

/-- A human being through intellect can know the natures of all bodies
(q.75 a.2 co., `homo per intellectum ... naturas omnium corporum`). Read
 distributively as unrestricted capacity across bodily natures, not a single
simultaneous act or knowledge of every fact about every body. -/
def UniversalBodilyCognition {Principle Nature : Type}
    (m : Model Principle Nature) (intellect : Principle) : Prop :=
  ∀ n, m.BodilyNature n → m.CanUnderstand intellect n

/-- Every body has some determinate nature (q.75 a.2 co.). This existential
witness is constitutively present in the body; no uniqueness is asserted. -/
def BodilyDeterminacy {Principle Nature : Type} (m : Model Principle Nature) : Prop :=
  ∀ b, m.IsBody b → ∃ n, m.BodilyNature n ∧ m.HasNaturally b n

/-- If the intellectual principle had in itself the nature of a body, it
could not know all bodies (q.75 a.2 co., `Si igitur ...`). This is an open,
source-attributed interference principle, not part of the meaning of body,
nature or representation. The taste example does not prove its universal
application to intellect. No particular unknowable nature is selected from
this negated universal, so excluded middle is not introduced. -/
def NaturalBodilyInterference {Principle Nature : Type}
    (m : Model Principle Nature) (intellect : Principle) : Prop :=
  ∀ n, m.BodilyNature n → m.HasNaturally intellect n →
    ¬ UniversalBodilyCognition m intellect

/-- First subconclusion of q.75 a.2 co.: the intellectual principle is not a
body. This does not assert that it is no part/form of a body, is altogether
immaterial in the q.14 divine sense, or is the complete human being. It does
not establish non-organic operation, subsistence or immortality. -/
def IntellectIsNotBody {Principle Nature : Type}
    (m : Model Principle Nature) (intellect : Principle) : Prop :=
  ¬ m.IsBody intellect

end TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect
