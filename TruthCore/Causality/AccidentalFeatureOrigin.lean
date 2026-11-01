/-! Analyst partial case of SCG I.42[9], not a binding of its whole argument.
Feature denotes a repeatable characteristic kind, not a numerical accident token.
Roles are standpoint-local; no Ontic, modal frame or God predicate is supplied.
Formal character and its production differ from eminent InAct and CausesIn. -/
namespace TruthCore.Causality.AccidentalFeatureOrigin

/-- Independently interpreted OPEN roles. An externalFeatureCause witness is
only in this role; no actuality, numerical distinction or existential grounding
is built into the carrier or fields. Essence and ordinary bearer roles differ. -/
structure RoleSchema (Being Principle Feature : Type) where
  occurs : Being → Feature → Prop
  accidental : Being → Feature → Prop
  essenceProduces : Principle → Feature → Prop
  externalFeatureCause : Being → Being → Feature → Prop

variable {B P F : Type}

/-- Selected accidental classification; not an essential/accidental coverage law. -/
def Accidental (s : RoleSchema B P F) (x : B) (f : F) : Prop := s.accidental x f

/-- One repeatable characteristic occurs in x but not y at this standpoint. -/
def Distinguishes (s : RoleSchema B P F) (x y : B) (f : F) : Prop :=
  s.occurs x f ∧ ¬ s.occurs y f

/-- Selected cause-origin fork, conditional on actual role occurrence and its
accidental classification. Exhaustiveness and causal interpretation remain OPEN. -/
def OriginFork (s : RoleSchema B P F) (essenceOf : B → P) (x : B) (f : F) : Prop :=
  s.accidental x f → s.occurs x f →
    s.essenceProduces (essenceOf x) f ∨ ∃ c, s.externalFeatureCause c x f

/-- Explicit production-sharing policy for this pair and feature. Agreement in
necessity alone is not silently made a proof of this premise. -/
def SharedProduction (s : RoleSchema B P F) (essenceOf : B → P)
    (x y : B) (f : F) : Prop :=
  s.essenceProduces (essenceOf x) f → s.essenceProduces (essenceOf y) f

/-- Selected realization only at y,f; no universal realization is required. -/
def Realization (s : RoleSchema B P F) (essenceOf : B → P) (y : B) (f : F) : Prop :=
  s.essenceProduces (essenceOf y) f → s.occurs y f

/-- Existence in the supplied classified-origin role, not ExistsAt or c ≠ x. -/
def ExternalOriginExists (s : RoleSchema B P F) (x : B) (f : F) : Prop :=
  ∃ c, s.externalFeatureCause c x f

end TruthCore.Causality.AccidentalFeatureOrigin
