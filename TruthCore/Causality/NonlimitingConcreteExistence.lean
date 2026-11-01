import TruthCore.Modal.LimitationSeparation
import TruthCore.Causality.BruteFoundationBoundary
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Causality.PossibleCauseOfContingency

/-! Analyst specialization, not an identification with source A8's powerful
Necessary Being property. Phi contains only concreteness and actual existence;
Q is accessible absence. Neither defines necessity into Phi. The Profile's
selected grounds field is unused; no causal, PSR or foundation law is added. -/
namespace TruthCore.Causality.NonlimitingConcreteExistence
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Modal.LimitationPossibility
open TruthCore.Modal (Euclidean)
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Isabelle.AFP.GoedelGod (Property Dia)
open TruthCore.Logic (ExcludedMiddle)

/-- Concrete existence, with no necessity, power or causal role in the target. -/
def ConcreteExistence {W B : Type} (m : Profile W B) : Property W B :=
  fun c v => m.concrete c ∧ m.ontic.ExistsAt v c

/-- Possible absence, without an actual-existence guard. This is not the
ContingentAt predicate, which additionally demands actual presence. -/
def PossibleAbsence {W B : Type} (m : Profile W B) : Property W B :=
  fun c v => Dia m.ontic.frame (fun u => ¬ m.ontic.ExistsAt u c) v

/-- OPEN specialized classifier commitment on THIS Ontic's possible absence.
It is not a new binding of the source's modal/evaluative sentence. -/
def KnownAbsenceLimitingAt {W B : Type} (m : Profile W B)
    (L : Property W B → W → Prop) (w : W) : Prop :=
  KnownLimitingAt L (PossibleAbsence m) w

/-- OPEN nonlimitation of concrete existence. Distinct from source P2's
nonlimitation of the powerful-Necessary-Being property. -/
def ConcreteExistenceNonlimitingAt {W B : Type} (m : Profile W B)
    (L : Property W B → W → Prop) (w : W) : Prop :=
  NonlimitingAt L (ConcreteExistence m) w

/-- SAME Ontic-level transport algorithm as EmptyHistoryCausalAvailability's
necessaryAtOrigin; no irrelevant Arena/fact fields are introduced to use it. -/
theorem necessaryAtOrigin {W B : Type} (m : Ontic W B) (w v : W) (c : B)
    (hEuclidean : Euclidean m.frame) (hReflexive : ActualReflexive m w)
    (hwv : m.frame.access w v) (hn : NecessaryAt m v c) :
    m.ExistsAt w c ∧ NecessaryAt m w c :=
  ⟨hn w (hEuclidean w v w hwv hReflexive),
    fun z hwz => hn z (hEuclidean w v z hwv hwz)⟩

/-- NEW view only: preserve the old mixed Ontic/concreteness literally.
The arbitrary empty grounds field is unused by every new inference and is
not proposed as a real existential-support interpretation. -/
def controlProfile : Profile Bool (Option Bool) where
  ontic := TruthCore.Causality.PossibleCauseOfContingency.mixed.ontic
  concrete := TruthCore.Causality.PossibleCauseOfContingency.mixed.concrete
  grounds := fun _ _ _ => False

/-- NEW analyst dictionary, not sourced: a property is classified limiting
when the selected none candidate lacks it at the standpoint. This tests joint
compatibility, not the truth of an evaluative standard. -/
def controlClassifier (P : Property Bool (Option Bool)) (v : Bool) : Prop :=
  ¬ P none v

/-- All six inputs jointly hold on the unchanged mixed ontology. The known
limiting absence property has a real exemplar in this fixture; an actual
contingent individual remains beside the necessary none candidate. -/
def JointControl : Prop :=
  KnownAbsenceLimitingAt controlProfile controlClassifier false ∧
  ConcreteExistenceNonlimitingAt controlProfile controlClassifier false ∧
  BackwardClosedAt controlProfile.ontic.frame controlClassifier false ∧
  ExcludedMiddle ∧ Euclidean controlProfile.ontic.frame ∧
  ActualReflexive controlProfile.ontic false ∧
  NecessaryConcreteAt controlProfile false ∧
  (controlProfile.ontic = TruthCore.Causality.PossibleCauseOfContingency.mixed.ontic ∧
    controlProfile.concrete = TruthCore.Causality.PossibleCauseOfContingency.mixed.concrete) ∧
  (controlProfile.concrete (some false) ∧ controlProfile.ontic.ExistsAt false (some false) ∧
    ContingentAt controlProfile.ontic false (some false)) ∧
  PossibleAbsence controlProfile (some false) false ∧
  NecessaryAt controlProfile.ontic false none

end TruthCore.Causality.NonlimitingConcreteExistence
