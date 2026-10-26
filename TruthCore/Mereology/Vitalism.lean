/-!
An analyst's finite stress test for the mereological-vitalism proposal (#329).

The data include complete replacement of two material cohorts, continued
self-maintenance, coordinated activity, and an operational continuation relation.
Three interpretations agree on *all* these facts but differ on substantial
unity and on an irreducible soul-as-form. The latter two are metaphysical
predicates, deliberately not defined by the observed behavior.

This is a logical independence test, **not** an empirical model of an organism,
a proof of metaphysical possibility, or a sourced account of Aristotle's soul.
In particular, a material-process rival must still defend the adequacy of its
explanation, and the vitalist must independently defend the soul/whole bridge.
-/

namespace TruthCore.Mereology.Vitalism

inductive Phase where
  | early
  | late
  deriving DecidableEq

inductive Component where
  | original
  | replacement
  deriving DecidableEq

/-- The common observational/structural vocabulary and two independently
interpreted metaphysical predicates. `Continuity` denotes an observable
process-level successor, **not** the numerical identity of a substance. -/
structure Scenario where
  MemberAt : Phase → Component → Prop
  Alive : Phase → Prop
  Integrated : Phase → Prop
  SelfMaintaining : Phase → Prop
  Continuity : Phase → Phase → Prop
  SubstantialUnity : Phase → Prop
  SoulAsForm : Phase → Prop

/-- Both phases are alive, integrated and self-maintaining, the observed
process continues, and none of the earlier cohort is in the later phase. -/
def TurnoverProfile (s : Scenario) : Prop :=
  s.MemberAt .early .original ∧
    ¬ s.MemberAt .early .replacement ∧
    s.MemberAt .late .replacement ∧
    ¬ s.MemberAt .late .original ∧
    s.Alive .early ∧ s.Alive .late ∧
    s.Integrated .early ∧ s.Integrated .late ∧
    s.SelfMaintaining .early ∧ s.SelfMaintaining .late ∧
    s.Continuity .early .late

/-- Indistinguishable with respect to *every* material/behavioral relation
in this deliberately restricted language. Soul and substantial unity are
excluded because the issue is whether that language determines them. -/
def SameProfile (s t : Scenario) : Prop :=
  (∀ p c, s.MemberAt p c ↔ t.MemberAt p c) ∧
    (∀ p, s.Alive p ↔ t.Alive p) ∧
    (∀ p, s.Integrated p ↔ t.Integrated p) ∧
    (∀ p, s.SelfMaintaining p ↔ t.SelfMaintaining p) ∧
    (∀ p q, s.Continuity p q ↔ t.Continuity p q)

/-- A minimal causal-history surrogate: the old cohort is replaced, while
life and coordinated maintenance continue. The metaphysical interpretation
of that activity is an independent parameter, rather than a hidden premise. -/
def scenario (unity soul : Prop) : Scenario where
  MemberAt := fun p c =>
    match p, c with
    | .early, .original => True
    | .late, .replacement => True
    | _, _ => False
  Alive := fun _ => True
  Integrated := fun _ => True
  SelfMaintaining := fun _ => True
  Continuity := fun p q => (p = .early ∧ q = .late) ∨ p = q
  SubstantialUnity := fun _ => unity
  SoulAsForm := fun _ => soul

theorem scenario_has_turnover (unity soul : Prop) :
    TurnoverProfile (scenario unity soul) := by
  simp [TurnoverProfile, scenario]

theorem scenario_same_profile (u₁ s₁ u₂ s₂ : Prop) :
    SameProfile (scenario u₁ s₁) (scenario u₂ s₂) := by
  simp [SameProfile, scenario]

/-- MEREO-005: the same rich but finite material/behavioral history has
1. a soul-and-substance reading and a process-only reading; and
2. a soul-and-substance reading and a soul-free substantial-unity reading.

Thus neither full material turnover nor operational life/integration alone
settles substantial unity, and even granting substantial unity does not
logically settle whether its principle is an irreducible soul-as-form.
This conclusion is only about this explicit signature and these models.
-/
def SoulUnityIndependence : Prop :=
  (∃ v f : Scenario,
    TurnoverProfile v ∧ TurnoverProfile f ∧ SameProfile v f ∧
      v.SubstantialUnity .early ∧ v.SoulAsForm .early ∧
      ¬ f.SubstantialUnity .early ∧ ¬ f.SoulAsForm .early) ∧
  (∃ v h : Scenario,
    TurnoverProfile v ∧ TurnoverProfile h ∧ SameProfile v h ∧
      v.SubstantialUnity .early ∧ v.SoulAsForm .early ∧
      h.SubstantialUnity .early ∧ ¬ h.SoulAsForm .early)

end TruthCore.Mereology.Vitalism
