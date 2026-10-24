import TruthCore.English.VanRoojen.MoralCognitivism

/-!
Conclusion propositions of the Frege–Geach refutation of naive emotivism
(#182). They live outside `TruthCore.Comparison` because they are not
theories: `bind-check` binds them to their statements by head constant,
without unfolding.
-/

namespace TruthCore.Refutations.Emotivism

open TruthCore.English.VanRoojen

universe u v w x

/-- Geach's moral modus ponens is not valid. -/
def GeachModusPonensInvalid {Sentence : Sort u}
    (ValidMP : Sentence → Sentence → Prop) (p q : Sentence) : Prop :=
  ¬ ValidMP p q

/-- The occasion reading of emotivism is false: it is not the case that the
meaning of a moral sentence in an occurrence is accounted for by the attitude it
expresses there. -/
def EmotivistMeaningFails {Sentence : Sort u} {Ctx : Sort v}
    {Meaning : Sort w} {Attitude : Sort x}
    (Moral : Sentence → Prop) (meaning : Sentence → Ctx → Meaning)
    (Expresses : Sentence → Ctx → Attitude → Prop) : Prop :=
  ¬ EmotivistMeaningIsExpressedAttitudeReading Moral meaning Expresses

end TruthCore.Refutations.Emotivism
