module

public import TruthCore.Logic.Verificationism
public import TruthCore.Results.Logic.Verificationism.VerdictSilent.Solution

/-!
Analyst semantic-profile siblings of the two UNCHANGED untyped natural-theology
statements. No profile/source identity, complete argument-domain interpretation
or epistemic warrant is assumed. World-premise admissibility, logical consequence,
a supplied warrant criterion and finite observation verification stay separate.
-/
@[expose] public section
namespace TruthCore.Logic.NaturalTheologySemanticScope
open TruthCore.Logic.Verificationism

inductive Standard where
  | consequence | warrant | finiteObservation
  deriving DecidableEq

structure Profile (L : Language) where
  Argument : Type
  target : Argument → L.Sentence
  premises : Argument → List L.Sentence
  admitted : Argument → Prop
  worldPremise : L.Sentence → Prop
  warranted : Argument → Prop
  meaningful : L.Sentence → Prop
  aboutGod : L.Sentence → Prop
  aboutHigher : L.Sentence → Prop
  standard : Standard

/-- These criteria are not silently equated. In particular, the independent
warrant predicate is an OPEN supplied interpretation, not verified warrant. -/
def Meets {L : Language} (F : Frame L) (p : Profile L) : Standard → p.Argument → Prop
  | .consequence, a => L.Entails (p.premises a) (p.target a)
  | .warrant, a => p.warranted a
  | .finiteObservation, a =>
      (∀ s, s ∈ p.premises a → F.observation s) ∧ L.Satisfiable (p.premises a) ∧
        L.Entails (p.premises a) (p.target a)

def WorldArgument {L : Language} (F : Frame L) (p : Profile L) (s : L.Sentence) : Prop :=
  ∃ a, p.admitted a ∧ (∀ premise, premise ∈ p.premises a → p.worldPremise premise) ∧
    Meets F p p.standard a ∧ p.target a = s

/-- Full meaningfulness denial includes God and the higher. It remains a
profile proposal, not a new historical attribution or an identity with the book. -/
def NoMeaningfulDivine {L : Language} (p : Profile L) : Prop :=
  ∀ s, p.meaningful s → ¬ p.aboutGod s ∧ ¬ p.aboutHigher s

def NaturalTheologyArguable {L : Language} (F : Frame L) (p : Profile L) : Prop :=
  ∃ s, p.meaningful s ∧ p.aboutGod s ∧ WorldArgument F p s

def NotNaturalTheologyArguable {L : Language} (F : Frame L) (p : Profile L) : Prop :=
  ¬ NaturalTheologyArguable F p

/-- Independent OPEN bridge: formal consequence does not supply warrant. -/
def ConsequenceWarrantBridge {L : Language} (F : Frame L) (p : Profile L) : Prop :=
  ∀ a, p.admitted a → Meets F p .consequence a → p.warranted a

/-- Reuse the exact old empirical standard when THIS criterion is selected.
This is not a warrant bridge, nor a claim every actual argument is in the roster. -/
theorem empiricalArgumentConclusive {L : Language} (F : Frame L) (p : Profile L)
    (s : L.Sentence) (hStandard : p.standard = .finiteObservation)
    (h : WorldArgument F p s) : ConclusivelyVerifiable F s := by
  obtain ⟨a, _, _, hMeets, hTarget⟩ := h
  rw [hStandard] at hMeets
  obtain ⟨hObs, hSat, hEnt⟩ := hMeets
  exact ⟨p.premises a, hObs, hSat, hTarget ▸ hEnt⟩

namespace Control
open TruthCore.Results.Logic.Verificationism.VerdictSilent

def divine : twoCoordinate.Sentence := fun w => w.2

/-- A populated candidate argument whose conclusion follows from itself.
Its premise has not been supplied as world-grounded, and the independent
warrant condition fails. Completeness/adequacy for actual arguments is OPEN. -/
def profile : Profile twoCoordinate where
  Argument := Unit
  target _ := divine
  premises _ := [divine]
  admitted _ := True
  worldPremise _ := False
  warranted _ := False
  meaningful _ := True
  aboutGod _ := True
  aboutHigher _ := False
  standard := .consequence

def Properties : Prop :=
  profile.meaningful divine ∧ profile.aboutGod divine ∧
  ¬ NoMeaningfulDivine profile ∧
  profile.admitted () ∧ profile.premises () = [divine] ∧
  Meets observableFrame profile .consequence () ∧
  ¬ Meets observableFrame profile .warrant () ∧
  ¬ profile.worldPremise divine ∧
  NotNaturalTheologyArguable observableFrame profile ∧
  ¬ ConsequenceWarrantBridge observableFrame profile

end Control
end TruthCore.Logic.NaturalTheologySemanticScope
