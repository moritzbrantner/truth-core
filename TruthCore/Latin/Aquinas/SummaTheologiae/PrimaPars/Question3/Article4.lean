/-!
ST I q.3 a.4 co., first proof, verified against pinned Latin passage
`AQUINAS-ST-I-Q3-A4`.

Aquinas reasons that esse distinct from essence must be caused either by
essential principles or by another agent; the former cannot sufficiently
cause the very being of a thing with caused esse. We separate the *two
substantive premises* from their external-cause conclusion. Nothing in these
definitions asserts the premises as true or gives a metaphysical argument
for their exhaustiveness.

The `InAct` / `CausesIn` fields retain the shared Aquinas vocabulary for
actual being and an efficient cause in the `esse` respect. Unlike the
analytic `supportsEsse` relation in `PowerExistenceBoundary`, the external
cause here is explicitly interpreted as an efficient cause of being, not
ordinary production or a merely sufficient noncausal reason.
-/
namespace TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-- Typed interface for the first proof of q.3 a.4. Comparing `essenceOf`
and `esseOf` uses the common `Principle` sort also used in the existing
simplicity results. `essentialPrinciplesAloneSufficeForEsse` means
*sufficiently efficiently caused by those principles alone*, not merely intrinsically intelligible. -/
structure Profile (Being Principle Respect : Type) where
  InAct : Being → Respect → Prop
  CausesIn : Being → Being → Respect → Prop
  essenceOf : Being → Principle
  esseOf : Being → Principle
  essentialPrinciplesAloneSufficeForEsse : Being → Prop
  esse : Respect

/-- An actually existing subject whose esse and essence differ in the
represented `Principle` identity relation. No modality is built in. -/
def DistinctEsseAt (p : Profile B P R) (x : B) : Prop :=
  p.InAct x p.esse ∧ p.esseOf x ≠ p.essenceOf x

/-- Another actually existing bearer directly efficiently causes x's esse.
This is a *selected interpretation* of "causatum ab alio", not the claim
that every external explanation must be efficient causation. -/
def HasExternalEsseCause (p : Profile B P R) (x : B) : Prop :=
  ∃ y, y ≠ x ∧ p.InAct y p.esse ∧ p.CausesIn y x p.esse

/-- ST I q.3 a.4 co., first proof, "vel ... a principiis essentialibus ...
vel ... ab aliquo exteriori" as applied to esse distinct from essence.
The dichotomy is an open, source-attributed metaphysical commitment; brute
being or a noncausal intrinsic/global reason would reject its exhaustiveness. -/
def DistinctEsseCauseDichotomyReading (p : Profile B P R) : Prop :=
  ∀ x, DistinctEsseAt p x →
    p.essentialPrinciplesAloneSufficeForEsse x ∨ HasExternalEsseCause p x

/-- ST I q.3 a.4 co., first proof, "nulla res sufficit quod sit sibi causa
essendi, si habeat esse causatum", restricted to the distinct-esse case.
This excludes sufficient efficient self-origination from essential principles
alone; it does not exclude every noncausal intrinsic sufficient reason. -/
def EssentialPrinciplesCannotCauseDistinctEsseReading
    (p : Profile B P R) : Prop :=
  ∀ x, DistinctEsseAt p x → ¬p.essentialPrinciplesAloneSufficeForEsse x

/-- ST I q.3 a.4 co., first proof, "illud cuius esse est aliud ab essentia
sua, habeat esse causatum ab alio". Neither its converse nor a modal
necessity or divine simplicity conclusion is part of this reading. -/
def DistinctEsseRequiresExternalCauseReading (p : Profile B P R) : Prop :=
  ∀ x, DistinctEsseAt p x → HasExternalEsseCause p x

/-- All recorded efficient causes of esse actually exist, as do their
effects. This is a coherence condition for the finite semantic controls,
not a new source premise. -/
def Coherent (p : Profile B P R) : Prop :=
  ∀ y x, p.CausesIn y x p.esse →
    p.InAct y p.esse ∧ p.InAct x p.esse

/-- Two countermodels and a nonvacuous successful control over two beings:
(1) a brute existent with distinct esse and no cause, satisfying the
no-self-cause principle but not causal exhaustiveness;
(2) an existent whose essential principles alone suffice to cause its esse,
with no external agent,
satisfying the disjunction but not the exclusion;
(3) a separate existing efficient cause of the subject's distinct esse,
satisfying both premises and their conclusion.

These are consistent typed interpretations, **not** demonstrations that
each interpretation is metaphysically possible. -/
def PremiseOmissionsAndControl : Prop :=
  (∃ p : Profile Bool Bool Unit,
    Coherent p ∧ DistinctEsseAt p false ∧
    (∀ y x r, ¬p.CausesIn y x r) ∧
    ¬p.essentialPrinciplesAloneSufficeForEsse false ∧
    ¬HasExternalEsseCause p false ∧
    EssentialPrinciplesCannotCauseDistinctEsseReading p ∧
    ¬DistinctEsseCauseDichotomyReading p ∧
    ¬DistinctEsseRequiresExternalCauseReading p) ∧
  (∃ p : Profile Bool Bool Unit,
    Coherent p ∧ DistinctEsseAt p false ∧
    p.essentialPrinciplesAloneSufficeForEsse false ∧
    ¬HasExternalEsseCause p false ∧
    DistinctEsseCauseDichotomyReading p ∧
    ¬EssentialPrinciplesCannotCauseDistinctEsseReading p ∧
    ¬DistinctEsseRequiresExternalCauseReading p) ∧
  (∃ p : Profile Bool Bool Unit,
    Coherent p ∧ DistinctEsseAt p false ∧
    HasExternalEsseCause p false ∧
    DistinctEsseCauseDichotomyReading p ∧
    EssentialPrinciplesCannotCauseDistinctEsseReading p ∧
    DistinctEsseRequiresExternalCauseReading p)

end TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4
