module

/-! Bounded analyst candidates for the q104 preservation fork.
These are action records, not completed meanings of PRESERVATION_1/2. In
particular `givingEsse` is an uninterpreted productive role. `intercepting` names
an intervention on an identified threat; it does not analyze successful
prevention. Neither constructor is an interpretation of `CausesIn` at esse.
No time order, fresh production, withdrawal counterfactual, modal power,
transitivity, or well-foundedness is assumed. -/

@[expose] public section
namespace TruthCore.Causality.PreservationCandidates

/-- A corruption threat has a particular bearer and an originating agent.
Whether this is a genuine corruption process remains an interpretation burden. -/
structure Threat (Being : Type) where
  source : Being
  target : Being

/-- Positive contribution roles. Interception carries the threat being addressed;
its target is checked by the action record rather than inferred from a label.
Giving esse has no completed productive semantics and is deliberately not bound
to either original preservation sense. -/
inductive Contribution (Being : Type) where
  | givingEsse
  | intercepting (threat : Threat Being)

/-- One continuing action episode, with agent, bearer, and contribution role.
`ongoing` is primitive episode occurrence, not a new event at each instant. -/
structure Action (Being : Type) where
  agent : Being
  bearer : Being
  contribution : Contribution Being
  ongoing : Prop

/-- The candidate requires an ongoing action directed to this very bearer and
its present existence. Mere continued existence supplies no such action. -/
structure ProductiveCandidate {Being : Type} (existsNow : Being → Prop)
    (a : Action Being) : Prop where
  present : existsNow a.bearer
  ongoing : a.ongoing
  productiveRole : a.contribution = .givingEsse

/-- Threat-relative candidate: an ongoing intervention addresses a threat to
this bearer. This does not entail that the intervention succeeds or that it is
necessary; those are the precise missing prevention semantics. -/
def InterceptionCandidate {Being : Type} (a : Action Being) : Prop :=
  ∃ threat : Threat Being, a.contribution = .intercepting threat ∧
    threat.target = a.bearer ∧ a.ongoing

/-- The two *episodes* cannot have both roles. This does not say that one agent
cannot both give esse and protect a bearer by different actions. -/
theorem roles_disjoint {Being : Type} {E : Being → Prop} {a : Action Being}
    (p : ProductiveCandidate E a) (i : InterceptionCandidate a) : False := by
  obtain ⟨_, role, _, _⟩ := i
  rw [p.productiveRole] at role
  cases role

def giving : Action Bool := ⟨false, true, .givingEsse, True⟩
def guarding : Action Bool :=
  ⟨false, true, .intercepting ⟨false, true⟩, True⟩
def misdirected : Action Bool :=
  ⟨false, true, .intercepting ⟨false, false⟩, True⟩
def ceased : Action Bool := ⟨false, true, .givingEsse, False⟩

/-- Populated productive candidate with no interception: no real esse-giving
instance is claimed by this finite role assignment. -/
theorem productive_control : ProductiveCandidate (fun _ => True) giving ∧
    ¬ InterceptionCandidate giving := by
  have p : ProductiveCandidate (fun _ => True) giving := ⟨True.intro, True.intro, rfl⟩
  exact ⟨p, fun i => roles_disjoint p i⟩

/-- Populated interception candidate with an existing bearer, but no productive
role. Protecting a bearer is not made a cause of esse. -/
theorem interception_control : InterceptionCandidate guarding ∧
    ¬ ProductiveCandidate (fun _ => True) guarding := by
  have i : InterceptionCandidate guarding := ⟨⟨false, true⟩, rfl, rfl, True.intro⟩
  exact ⟨i, fun p => roles_disjoint p i⟩

/-- Continued existence does not recover a ceased productive episode. -/
theorem occurrence_omission : ¬ ProductiveCandidate (fun _ => True) ceased := by
  intro p
  exact p.ongoing

/-- An action role without the present bearer is insufficient. -/
theorem presence_omission : ¬ ProductiveCandidate (fun _ => False) giving := by
  intro p
  exact p.present

/-- Addressing a threat to another bearer does not meet the candidate. -/
theorem target_omission : ¬ InterceptionCandidate misdirected := by
  intro i
  obtain ⟨threat, role, bad, _⟩ := i
  have h : (⟨false, false⟩ : Threat Bool) = threat := by
    exact Contribution.intercepting.inj role
  rw [← h] at bad
  cases bad

/-- Concrete candidate for removing one represented corruption threat. This is
set subtraction, not yet causal prevention: deleting a record alone need not
stop the process represented by it. Unlike a free prevention flag its effect
on every represented threat is fixed by the body. -/
def removeThreat {Being : Type} (t : Threat Being)
    (exposed : Threat Being → Prop) : Threat Being → Prop :=
  fun other => exposed other ∧ other ≠ t

theorem removed_threat_absent {Being : Type} (t : Threat Being)
    (exposed : Threat Being → Prop) : ¬ removeThreat t exposed t := by
  intro h
  exact h.2 rfl

theorem other_threat_retained {Being : Type} (t other : Threat Being)
    (exposed : Threat Being → Prop) (h : exposed other) (hne : other ≠ t) :
    removeThreat t exposed other := ⟨h, hne⟩

/-- Even removing a populated threat leaves another threat to the same bearer.
No unqualified continued-existence or complete-protection conclusion follows. -/
theorem incomplete_protection_control :
    removeThreat (⟨false, true⟩ : Threat Bool) (fun _ => True) ⟨true, true⟩ := by
  constructor
  · trivial
  · intro h
    have bad := congrArg Threat.source h
    cases bad

end TruthCore.Causality.PreservationCandidates
