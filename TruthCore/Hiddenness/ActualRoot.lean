module

public import TruthCore.Hiddenness.Models
public import TruthCore.Case.Catholicism.Root

/-! Analyst scope fork, attribution deferred. The actual-world norms are weaker
siblings of the global hiddenness norms. No claim is made that their empirical
or love premises hold. The route identification is a separately stipulated
one-way bridge; the spelling of God supplies no identification. -/
@[expose] public section
namespace TruthCore.Hiddenness.ActualRoot
open TruthCore.Hiddenness

def ActualGodLoves (s : Sig) : Prop := s.God s.actual → s.PerfectLove s.actual

def ActualAlwaysOpen (s : Sig) : Prop :=
  s.PerfectLove s.actual → ∀ p t, s.Capable s.actual p t →
    ¬ s.Resists s.actual p t → s.Available s.actual p t

def ActualAccessNeedsBelief (s : Sig) : Prop :=
  ∀ p t, ¬ s.Believes s.actual p t → ¬ s.Available s.actual p t

/-- OPEN identification: each bearer of the route's selected God predicate
entails the personal-ultimate existence proposition at this actual world.
It does not identify all necessary beings, or infer existence in either signature. -/
def RouteIdentification {B : Type} (IsGod : B → Prop) (s : Sig) : Prop :=
  ∀ g, IsGod g → s.God s.actual

def NoRouteGod {B : Type} (IsGod : B → Prop) : Prop :=
  ¬ TruthCore.Case.Catholicism.GodExists IsGod

/-- Explicit finite interpretation for strictness tests. Actual-world norms
are vacuous or hold because access is absent; remote commitments vary. This
is a logical interpretation, not an account of actual divine love or persons. -/
def remoteModel (god love access belief : Bool) : Sig where
  World := Bool
  Person := Unit
  Time := Bool
  actual := false
  God w := w = true ∧ god = true
  PerfectLove w := w = true ∧ love = true
  Capable _ _ _ := True
  Resists _ _ _ := False
  Believes w _ t := if w then belief = true else t = true
  Available w _ _ := w = true ∧ access = true
  HasConcept _ _ _ := True
  ReflectiveDoubt _ _ _ := False
  Accepts _ _ _ := False
  GoodReason _ _ _ := False

def Controls : Prop :=
  (∃ s, ActualGodLoves s ∧ ActualAlwaysOpen s ∧ ActualAccessNeedsBelief s ∧
    NonresistantNonbelief s ∧ RouteIdentification (fun _ : Unit => False) s ∧ NoGod s) ∧
  (∃ s, ActualGodLoves s ∧ ¬ GodLoves s) ∧
  (∃ s, ActualAlwaysOpen s ∧ ¬ AlwaysOpen s) ∧
  (∃ s, ActualAccessNeedsBelief s ∧ ¬ AccessNeedsBelief s) ∧
  (∃ s, ActualAlwaysOpen s ∧ ActualAccessNeedsBelief s ∧ NonresistantNonbelief s ∧ GodExists s) ∧
  (∃ s, ActualGodLoves s ∧ ActualAccessNeedsBelief s ∧ NonresistantNonbelief s ∧ GodExists s) ∧
  (∃ s, ActualGodLoves s ∧ ActualAlwaysOpen s ∧ NonresistantNonbelief s ∧ GodExists s) ∧
  (∃ s, ActualGodLoves s ∧ ActualAlwaysOpen s ∧ ActualAccessNeedsBelief s ∧ GodExists s) ∧
  (∃ s, ActualGodLoves s ∧ ActualAlwaysOpen s ∧ ActualAccessNeedsBelief s ∧
    NonresistantNonbelief s ∧ TruthCore.Case.Catholicism.GodExists (fun _ : Unit => True) ∧
    ¬ RouteIdentification (fun _ : Unit => True) s)
end TruthCore.Hiddenness.ActualRoot
