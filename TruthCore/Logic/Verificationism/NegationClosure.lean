module

public import TruthCore.Logic.Verificationism

/-!
Closure of meaningfulness under negation as a floor item, and the two
verificationist packages it defeats (#1008, owner decision 2026-11-05).

`MeaningClosedUnderNegation L meaningful` (strong): if a sentence is
meaningful, so is its negation. `MeaningClosedUnderNegationOfNegations`
(weak): the same, only for negated sentences. `meaningful` is the pre-theoretic predicate a criterion is
offered as an account of (sense (2) of `DISAMB-VERIFICATIONIST-MEANINGFUL`),
not a criterion's verdict.

Each rival package identifies `meaningful` with a criterion and includes what
its proponent holds of the empirical language:

* `StrongVerificationismWithLaws` (V1): analytic sentences are true at every
  world, a sentence is meaningful iff analytic or conclusively verifiable, and
  the language has a universal law over infinitely many individuals with an
  observable possible counterinstance.
* `Ayer1946ExcludesANegation` (V3): a sentence is meaningful iff literally
  meaningful by the 1946 criterion, the language has Church's observation
  statements, and some negated sentence (such as "there is no god") is not
  meaningful.

The refutations are in `TruthCore.Results.Logic.Verificationism.*Closure`.
-/
@[expose] public section

namespace TruthCore.Logic.Verificationism

variable {L : Language}

/-- Strong version (`STMT-MEANINGFULNESS-CLOSED-UNDER-NEGATION-STRONG`): for
every sentence, if it is meaningful, so is its negation. -/
def MeaningClosedUnderNegation (L : Language) (meaningful : L.Sentence → Prop) : Prop :=
  ∀ s, meaningful s → meaningful (L.neg s)

/-- Weak version (`STMT-MEANINGFULNESS-CLOSED-UNDER-NEGATION-WEAK`): closure only
for negated sentences: if `¬s` is meaningful, so is `¬¬s`. This is the only
instance the defeat of V1 uses. -/
def MeaningClosedUnderNegationOfNegations (L : Language) (meaningful : L.Sentence → Prop) :
    Prop :=
  ∀ s, meaningful (L.neg s) → meaningful (L.neg (L.neg s))

/-- The rival of the strong version (`STMT-SOME-MEANINGFUL-NEGATION-NOT-MEANINGFUL`):
some meaningful sentence has a negation that is not meaningful. -/
def SomeMeaningfulNegationNotMeaningful (L : Language) (meaningful : L.Sentence → Prop) :
    Prop :=
  ∃ s, meaningful s ∧ ¬ meaningful (L.neg s)

/-- The rival of the weak version
(`STMT-SOME-MEANINGFUL-NEGATION-DOUBLE-NEGATION-NOT-MEANINGFUL`): some
meaningful negated sentence has a double negation that is not meaningful. -/
def SomeMeaningfulNegationDoubleNegationNotMeaningful (L : Language)
    (meaningful : L.Sentence → Prop) : Prop :=
  ∃ s, meaningful (L.neg s) ∧ ¬ meaningful (L.neg (L.neg s))

/-- Analytic sentences are true at every world. -/
def AnalyticValid (F : Frame L) : Prop :=
  ∀ s, F.analytic s → ∀ w, L.holds w s

/-- The language has a universal law with an observable possible
counterinstance: a law setting, an individual `a`, and observation statements
`R a` and `notB` (true exactly where `B a` is false) that hold together
somewhere. -/
def HasTestableLaw (F : Frame L) : Prop :=
  ∃ U : UniversalLaw L, Nonempty (LawSetting F U) ∧
    ∃ (a : U.Individual) (notB : L.Sentence),
      F.observation (U.R a) ∧ F.observation notB ∧
      (∀ w, L.holds w notB ↔ ¬ L.holds w (U.B a)) ∧ L.Satisfiable [U.R a, notB]

/-- The V1 package (`STMT-STRONG-VERIFICATIONISM-WITH-LAWS`): analytic sentences
are valid, meaningfulness is analyticity or conclusive verifiability, and the
language has a testable universal law. -/
def StrongVerificationismWithLaws (F : Frame L) (meaningful : L.Sentence → Prop) : Prop :=
  AnalyticValid F ∧ (∀ s, meaningful s ↔ F.analytic s ∨ ConclusivelyVerifiable F s) ∧
    HasTestableLaw F

/-- The V1 package fails for this frame and meaningfulness predicate
(`STMT-STRONG-VERIFICATIONISM-WITH-LAWS-FAILS`). -/
def StrongVerificationismWithLawsFails (F : Frame L) (meaningful : L.Sentence → Prop) : Prop :=
  ¬ StrongVerificationismWithLaws F meaningful

/-- The V3 package (`STMT-AYER-1946-EXCLUDES-A-NEGATION`): meaningfulness is
literal meaningfulness by the 1946 criterion, the language has Church's
observation statements, and some negated sentence is not meaningful. -/
def Ayer1946ExcludesANegation (F : Frame L) (meaningful : L.Sentence → Prop) : Prop :=
  (∀ s, meaningful s ↔ LiterallyMeaningful1946 F s) ∧
    (∃ o₁ o₂ o₃, ChurchObservations F o₁ o₂ o₃) ∧ ∃ y, ¬ meaningful (L.neg y)

/-- The V3 package fails for this frame and meaningfulness predicate
(`STMT-AYER-1946-EXCLUDES-A-NEGATION-FAILS`). -/
def Ayer1946ExcludesANegationFails (F : Frame L) (meaningful : L.Sentence → Prop) : Prop :=
  ¬ Ayer1946ExcludesANegation F meaningful

end TruthCore.Logic.Verificationism
