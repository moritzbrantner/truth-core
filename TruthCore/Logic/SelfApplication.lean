/-!
Self-application (retorsion) as a reusable schema (#397).

Three typed layers, all data with no built-in philosophical premise:

* **Norms.** A `Norm` on claims has a `scope` (which claims it governs) and a
  `standard` (what a governed claim must meet). Relative to an acceptance
  predicate (`Acceptable`: established, warranted, absolutely true, opined, …)
  the norm *holds* when every acceptable claim in its scope meets its standard.
  `Norm.selfApplication` is the dilemma: if a claim (typically the norm's own
  formulation) lies in the scope and fails the standard, then either the norm
  holds and that claim is not acceptable, or the claim is acceptable and is a
  counterexample to the norm. The scope premise is an explicit hypothesis;
  `scopePremiseNeeded` is a model where it is dropped and nothing follows.
* **Assertion.** Asserting a content presents it as true in a stated
  `TruthSense`: absolutely, or relative to an agent. `AssertionCommitment`
  is the proposition the assertion commits its speaker to. No bridge between
  absolute and relative truth is built in.
* **Demarcation.** A weak thesis is the strong norm restricted to a domain
  fixed by a demarcation criterion (`Norm.restrict`). `Norm.demarcationTest`
  is the second-order self-application test: if the weak thesis (or its
  criterion's own statement) falls inside the domain, the restricted norm
  inherits the strong dilemma; if it falls outside and is acceptable, it is a
  concession (`Norm.Concedes`): an acceptable claim in the strong scope that
  fails the standard, so the strong norm fails.

Instances: `TruthCore.Logic.Relativism`, `TruthCore.Greek.Plato.Theaetetus`,
`TruthCore.Logic.Scientism`. Everything is constructive; no axiom is used.
-/

namespace TruthCore.Logic.SelfApplication

/-- A norm on claims: which claims it governs and what a governed claim must
meet. Data only; whether the norm holds depends on an acceptance predicate. -/
structure Norm (Claim : Type) where
  scope : Claim → Prop
  standard : Claim → Prop

namespace Norm

variable {Claim : Type}

/-- The norm holds for the acceptance predicate `Acceptable`: every acceptable
claim in its scope meets its standard. -/
def Holds (N : Norm Claim) (Acceptable : Claim → Prop) : Prop :=
  ∀ c, N.scope c → Acceptable c → N.standard c

/-- `c` is a counterexample to the norm: in scope, acceptable, and failing the
standard. -/
def Counterexample (N : Norm Claim) (Acceptable : Claim → Prop) (c : Claim) : Prop :=
  N.scope c ∧ Acceptable c ∧ ¬ N.standard c

theorem not_holds_of_counterexample {N : Norm Claim} {Acceptable : Claim → Prop} {c : Claim}
    (h : N.Counterexample Acceptable c) : ¬ N.Holds Acceptable :=
  fun hHolds => h.2.2 (hHolds c h.1 h.2.1)

/-- The self-application dilemma. If `self` lies in the norm's scope and fails
its standard: horn 1, if the norm holds then `self` is not acceptable by the
norm's own lights; horn 2, if `self` is acceptable it is a counterexample. -/
theorem selfApplication {N : Norm Claim} {Acceptable : Claim → Prop} {self : Claim}
    (hScope : N.scope self) (hFail : ¬ N.standard self) :
    (N.Holds Acceptable → ¬ Acceptable self) ∧
      (Acceptable self → N.Counterexample Acceptable self) :=
  ⟨fun hHolds hAcc => hFail (hHolds self hScope hAcc),
    fun hAcc => ⟨hScope, hAcc, hFail⟩⟩

/-- The two horns together: such a norm is not both holding and acceptable. -/
theorem not_holds_and_acceptable {N : Norm Claim} {Acceptable : Claim → Prop} {self : Claim}
    (hScope : N.scope self) (hFail : ¬ N.standard self) :
    ¬ (N.Holds Acceptable ∧ Acceptable self) :=
  fun ⟨hHolds, hAcc⟩ => (selfApplication hScope hFail).1 hHolds hAcc

/-- A demarcation criterion: which claims belong to the restricted domain. -/
structure Demarcation (Claim : Type) where
  inDomain : Claim → Prop

/-- The weak thesis: the norm restricted to the demarcated domain. -/
def restrict (N : Norm Claim) (D : Demarcation Claim) : Norm Claim :=
  ⟨fun c => N.scope c ∧ D.inDomain c, N.standard⟩

/-- What the restriction concedes: an acceptable claim in the strong scope,
outside the demarcated domain, that fails the standard. -/
def Concedes (N : Norm Claim) (D : Demarcation Claim) (Acceptable : Claim → Prop)
    (c : Claim) : Prop :=
  N.scope c ∧ ¬ D.inDomain c ∧ Acceptable c ∧ ¬ N.standard c

/-- The restriction is weaker: whatever satisfies the strong norm satisfies it. -/
theorem holds_restrict {N : Norm Claim} {D : Demarcation Claim} {Acceptable : Claim → Prop}
    (h : N.Holds Acceptable) : (N.restrict D).Holds Acceptable :=
  fun c hScope hAcc => h c hScope.1 hAcc

/-- Every concession is a counterexample to the strong norm. -/
theorem counterexample_of_concedes {N : Norm Claim} {D : Demarcation Claim}
    {Acceptable : Claim → Prop} {c : Claim} (h : N.Concedes D Acceptable c) :
    N.Counterexample Acceptable c :=
  ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- Second-order self-application test for a weak thesis `w` (or the statement
of its demarcation criterion) that lies in the strong scope and fails the
standard. Inside the domain, the restricted norm inherits the strong dilemma.
Outside it, an acceptable `w` is a concession and the strong norm fails. -/
theorem demarcationTest {N : Norm Claim} {D : Demarcation Claim} {Acceptable : Claim → Prop}
    {w : Claim} (hScope : N.scope w) (hFail : ¬ N.standard w) :
    (D.inDomain w →
        ((N.restrict D).Holds Acceptable → ¬ Acceptable w) ∧
          (Acceptable w → (N.restrict D).Counterexample Acceptable w)) ∧
      (¬ D.inDomain w → Acceptable w → N.Concedes D Acceptable w ∧ ¬ N.Holds Acceptable) := by
  constructor
  · intro hIn
    exact selfApplication (N := N.restrict D) ⟨hScope, hIn⟩ hFail
  · intro hOut hAcc
    have hConc : N.Concedes D Acceptable w := ⟨hScope, hOut, hAcc, hFail⟩
    exact ⟨hConc, not_holds_of_counterexample (counterexample_of_concedes hConc)⟩

end Norm

/-- Advertised form of the schema (`STMT-SELF-APPLICATION-DILEMMA`), quantified
over every claim type, norm, acceptance predicate and claim. -/
def SelfApplicationDilemma : Prop :=
  ∀ (Claim : Type) (N : Norm Claim) (Acceptable : Claim → Prop) (self : Claim),
    N.scope self → ¬ N.standard self →
      (N.Holds Acceptable → ¬ Acceptable self) ∧
        (Acceptable self → N.Counterexample Acceptable self)

/-- Without the scope premise nothing follows: a norm can hold while an
acceptable claim outside its scope fails its standard
(`STMT-SELF-APPLICATION-SCOPE-NEEDED`). -/
def ScopePremiseNeeded : Prop :=
  ∃ (N : Norm Bool) (Acceptable : Bool → Prop) (self : Bool),
    ¬ N.scope self ∧ ¬ N.standard self ∧ N.Holds Acceptable ∧ Acceptable self

/-- Advertised form of the second-order demarcation test
(`STMT-DEMARCATION-TEST`). -/
def DemarcationTest : Prop :=
  ∀ (Claim : Type) (N : Norm Claim) (D : Norm.Demarcation Claim) (Acceptable : Claim → Prop)
    (w : Claim),
    N.scope w → ¬ N.standard w →
      (D.inDomain w →
          ((N.restrict D).Holds Acceptable → ¬ Acceptable w) ∧
            (Acceptable w → (N.restrict D).Counterexample Acceptable w)) ∧
        (¬ D.inDomain w → Acceptable w → N.Concedes D Acceptable w ∧ ¬ N.Holds Acceptable)

/-- A weak thesis outside its own domain is consistent: the restricted norm
holds, the weak thesis is acceptable and fails the standard
(`STMT-DEMARCATION-OUTSIDE-CONSISTENT`). Consistency, not a defense. -/
def DemarcationOutsideConsistent : Prop :=
  ∃ (N : Norm Bool) (D : Norm.Demarcation Bool) (Acceptable : Bool → Prop) (w : Bool),
    N.scope w ∧ ¬ N.standard w ∧ ¬ D.inDomain w ∧ Acceptable w ∧ (N.restrict D).Holds Acceptable

/-! ### Assertion -/

/-- The sense in which an assertion presents its content as true. -/
inductive TruthSense (Agent : Type) where
  | absolute
  | relativeTo (a : Agent)

/-- Truth data for contents: an unindexed (absolute) predicate and an
agent-relative one. No relation between them is assumed. -/
structure TruthSemantics (Agent Content : Type) where
  trueAbs : Content → Prop
  trueFor : Agent → Content → Prop

/-- Truth in a stated sense. -/
def TruthSemantics.trueIn {Agent Content : Type} (T : TruthSemantics Agent Content) :
    TruthSense Agent → Content → Prop
  | .absolute, p => T.trueAbs p
  | .relativeTo a, p => T.trueFor a p

/-- What asserting `p` in sense `s` commits the speaker to: that `p` is true in
that sense. A commitment, not a claim that the assertion is correct. -/
def AssertionCommitment {Agent Content : Type} (T : TruthSemantics Agent Content)
    (s : TruthSense Agent) (p : Content) : Prop :=
  T.trueIn s p

/-- A content disquotes into a proposition under a truth predicate: if the
content is true, what it says holds. Only this direction is assumed. -/
def Disquotes {Content : Type} (truth : Content → Prop) (p : Content) (says : Prop) : Prop :=
  truth p → says

end TruthCore.Logic.SelfApplication
