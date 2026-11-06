module

public import TruthCore.Logic.Verificationism.NegationClosure
public import TruthCore.Logic.ExcludedMiddle
public import TruthCore.Results.Logic.Verificationism.VerdictSilent.Solution

/-!
Analyst calibrations for the independent cognitive-significance predicate in
Verificationism. Criterion verdicts are not silently identified with it.
Calibrations compare extensions only on the supplied scope. No historical
attribution, property identity, or universal survey of meaning theories follows.
The all-admitted option is a comparison proposal for this truth-conditional
language, not the claim that every utterance has cognitive significance.
-/
@[expose] public section
namespace TruthCore.Logic.MeaningDefinitionFork
open TruthCore.Logic.Verificationism

variable {L : Language}

/-- The offered criterion is both necessary and sufficient for the independent
meaning predicate, within exactly the supplied comparison scope. -/
def Calibration (F : Frame L) (meaningful scope verifiable : L.Sentence → Prop) : Prop :=
  ∀ s, scope s → (meaningful s ↔ F.analytic s ∨ verifiable s)

def V1Definition (F : Frame L) (meaningful scope : L.Sentence → Prop) : Prop :=
  Calibration F meaningful scope (ConclusivelyVerifiable F)

def V2Definition (F : Frame L) (meaningful scope : L.Sentence → Prop) : Prop :=
  Calibration F meaningful scope (WeaklyVerifiable1936 F)

def V3Definition (F : Frame L) (meaningful scope : L.Sentence → Prop) : Prop :=
  Calibration F meaningful scope (EmpiricallyVerifiable F)

/-- Every sentence in the supplied scope has the independent meaning property. -/
def AllInScopeMeaningful (meaningful scope : L.Sentence → Prop) : Prop :=
  ∀ s, scope s → meaningful s

def NamedCoverage (F : Frame L) (meaningful scope : L.Sentence → Prop) : Prop :=
  V1Definition F meaningful scope ∨ V2Definition F meaningful scope ∨
    V3Definition F meaningful scope ∨ AllInScopeMeaningful meaningful scope

/-- No named extension calibrates this predicate on this scope. This opposes
NamedCoverage, not every conclusion about meaningfulness. Further philosophical
admissibility of the supplied predicate remains open. -/
def RemainingDefinition (F : Frame L) (meaningful scope : L.Sentence → Prop) : Prop :=
  ¬ V1Definition F meaningful scope ∧ ¬ V2Definition F meaningful scope ∧
    ¬ V3Definition F meaningful scope ∧ ¬ AllInScopeMeaningful meaningful scope

def DefinitionFork : Prop :=
  ∀ (L : Language) (F : Frame L) (meaningful scope : L.Sentence → Prop),
    NamedCoverage F meaningful scope ∨ RemainingDefinition F meaningful scope

/-- Explicit target-relative demarcation demand, independent of the criterion.
Admitting all sentences is inadequate for this demand, not thereby false in
languages where every scoped sentence is cognitively meaningful. -/
def ExcludedContent (meaningful scope : L.Sentence → Prop) : Prop :=
  ∃ s, scope s ∧ ¬ meaningful s

/-- V2's proposed exclusion target supplies exactly the observational
independence that the existing unrestricted-auxiliary construction exploits. -/
def V2ExcludedTarget (F : Frame L) (meaningful scope : L.Sentence → Prop) : Prop :=
  ∃ m o, scope m ∧ ¬ meaningful m ∧ F.observation o ∧ ¬ L.Entails [L.neg m] o

/-- Global comparison scope. -/
def GlobalScope : L.Sentence → Prop := fun _ => True

/-- The exact V3 exclusion input retained by the existing calibrated package. -/
def ExcludedNegation (meaningful : L.Sentence → Prop) : Prop :=
  ∃ s, ¬ meaningful (L.neg s)

/-- A family-level consequence: supplied constraints reject the named accounts,
leaving the explicit remainder. This does not exhaust admissible meaning theories. -/
def NamedDemarcationFailure (F : Frame L) (meaningful : L.Sentence → Prop) : Prop :=
  RemainingDefinition F meaningful GlobalScope

def NotV1GlobalDefinition (F : Frame L) (meaningful : L.Sentence → Prop) : Prop :=
  ¬ V1Definition F meaningful GlobalScope

def NotV2Definition (F : Frame L) (meaningful scope : L.Sentence → Prop) : Prop :=
  ¬ V2Definition F meaningful scope

def NotV3GlobalDefinition (F : Frame L) (meaningful : L.Sentence → Prop) : Prop :=
  ¬ V3Definition F meaningful GlobalScope

def ChurchObservationSetting (F : Frame L) : Prop :=
  ∃ o₁ o₂ o₃, ChurchObservations F o₁ o₂ o₃

namespace Control
open TruthCore.Results.Logic.Verificationism.VerdictSilent

def observed : twoCoordinate.Sentence := fun w => w.1
def tautology : twoCoordinate.Sentence := fun _ => true
def analyticOnly : twoCoordinate.Sentence → Prop := observableFrame.analytic

def Properties : Prop :=
  VerificationPrinciple observableFrame analyticOnly GlobalScope
    (EmpiricallyVerifiable observableFrame) ∧
  RemainingDefinition observableFrame analyticOnly GlobalScope ∧
  analyticOnly tautology ∧ ¬ analyticOnly observed ∧
  ConclusivelyVerifiable observableFrame observed ∧
  WeaklyVerifiable1936 observableFrame observed ∧
  LiterallyMeaningful1946 observableFrame observed

end Control
end TruthCore.Logic.MeaningDefinitionFork
