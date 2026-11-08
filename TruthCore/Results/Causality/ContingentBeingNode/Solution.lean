module

public import TruthCore.Causality.ContingentBeingNode
public import TruthCore.Results.Modal.StandardCorrespondenceCertificate.Solution
public import TruthCore.Results.Modal.ConvergenceCertificate.Solution
public import TruthCore.Results.Modal.K.Laws.Solution
public import TruthCore.Results.Modal.T.Laws.Solution
public import TruthCore.Results.Modal.B.Laws.Solution
public import TruthCore.Results.Modal.S5.Laws.Solution
public import TruthCore.Results.Modal.SimplicityCollapse.Solution
public import TruthCore.Results.Causality.ModalSenseSupport.Solution

/-!
# The contingency node: connection to the route and refutations of collapse

`inhabits` derives the Cogito population node from the contingency node (sole
premise, a strength order). Each refutation takes a verified modal-library
conclusion as a premise and applies it: the K collapse laws (collapse iff every
accessible world is the actual one), the T laws (necessary collapse gives
actual collapse on reflexive frames), the B laws (possible collapse gives actual
collapse on symmetric frames), the S5 laws (possible collapse leaves no
contingent proposition), and the simplicity-collapse core (an act performed at
every accessible world yields no contingent effect strictly). Frame conditions
come from the route's modal principles (T, B, 5 schemas) through the
correspondence certificates, one argument per frame-class sense of NECESSARY_2.
-/

@[expose] public section

namespace TruthCore.Results.Causality.ContingentBeingNode

open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Causality.ContingentBeingNode
open TruthCore.Causality.ModalSenseSupport
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- The contingency node strengthens the Cogito population node. -/
theorem inhabits {W B : Type} (m : Profile W B) (w : W)
    (h : SomeActualContingentAt m w) : InhabitedConcreteAt m.ontic m.concrete w := by
  obtain ⟨x, hc, hx, _⟩ := h
  exact ⟨x, hc, hx⟩

/-- Not every actual concrete being is NECESSARY_2: the node's witness is not. -/
theorem notEveryNecessary {W B : Type} (m : Profile W B) (w : W)
    (h : SomeActualContingentAt m w) : NotEveryActualConcreteNecessaryAt m w := by
  obtain ⟨x, hc, hx, v, hv, hn⟩ := h
  exact fun hAll => hn (hAll x hc hx v hv)

/-- K sense (any frame): by the K collapse law, full collapse at `w` means that
`w` accesses only itself; the node's accessible world lacking its witness then
is `w`, where the witness exists. -/
theorem notCollapsedK {W B : Type} (m : Profile W B) (w : W)
    (hK : TruthCore.Modal.KResearch.Laws) (h : SomeActualContingentAt m w) :
    RouteNotCollapsedAt m.ontic w := by
  obtain ⟨x, _, hx, v, hv, hn⟩ := h
  intro hc
  have hvw : v = w := (hK.1 W m.ontic.frame w).mp hc v hv
  subst hvw
  exact hn hx

/-- KT sense: the T schema gives reflexivity (T correspondence); by the T law,
necessary collapse then gives actual collapse, excluded by `notCollapsedK`. -/
theorem notNecessarilyCollapsedT {W B : Type} (m : Profile W B) (w : W)
    (hCorr : StandardCorrespondenceCertificate.{0})
    (hK : TruthCore.Modal.KResearch.Laws) (hTL : TruthCore.Modal.TResearch.Laws)
    (hT : OnticTSchemaValid m.ontic) (h : SomeActualContingentAt m w) :
    RouteNotNecessarilyCollapsedAt m.ontic w := by
  have hRefl : Reflexive m.ontic.frame := (hCorr.1 W m.ontic.frame).mp hT
  intro hBox
  exact notCollapsedK m w hK h ((hTL.2 W m.ontic.frame allPredicates hRefl w).1 hBox)

/-- KTB sense: the B schema gives symmetry (B correspondence); by the B law,
possible collapse then gives actual collapse, excluded by `notCollapsedK`. -/
theorem notPossiblyCollapsedKTB {W B : Type} (m : Profile W B) (w : W)
    (hConv : ConvergenceCertificate.{0, 0})
    (hK : TruthCore.Modal.KResearch.Laws) (hBL : TruthCore.Modal.BResearch.Laws)
    (hB : OnticBSchemaValid m.ontic) (h : SomeActualContingentAt m w) :
    RouteNotPossiblyCollapsedAt m.ontic w := by
  have hSym : Symmetric m.ontic.frame := (hConv.2.2.2.2.2.2.2.1 W m.ontic.frame).mpr hB
  intro hPoss
  exact notCollapsedK m w hK h (hBL.2.1 W m.ontic.frame w hSym hPoss)

/-- S5 sense: the T and 5 schemas give an S5 frame (T and 5 correspondences); by
the S5 law, possible collapse leaves no contingent proposition at `w`, but the
existence of the node's witness is one (true at `w` by reflexivity, false at the
accessible world lacking it). -/
theorem notPossiblyCollapsedS5 {W B : Type} (m : Profile W B) (w : W)
    (hCorr : StandardCorrespondenceCertificate.{0}) (hConv : ConvergenceCertificate.{0, 0})
    (hS5L : TruthCore.Modal.S5Research.Laws)
    (hT : OnticTSchemaValid m.ontic) (h5 : Ontic5SchemaValid m.ontic)
    (h : SomeActualContingentAt m w) : RouteNotPossiblyCollapsedAt m.ontic w := by
  have hRefl : Reflexive m.ontic.frame := (hCorr.1 W m.ontic.frame).mp hT
  have hEucl : Euclidean m.ontic.frame := (hConv.2.2.2.2.2.2.2.2 W m.ontic.frame).mpr h5
  obtain ⟨x, _, hx, v, hv, hn⟩ := h
  intro hPoss
  exact (hS5L.2.2.1 W m.ontic.frame w ⟨hRefl, hEucl⟩ hPoss).2.2
    (fun u => m.ontic.ExistsAt u x) ⟨⟨w, hRefl w, hx⟩, ⟨v, hv, hn⟩⟩

/-- No act token performed at every accessible world strictly yields every
actual concrete being: by the simplicity-collapse core it would yield the node's
witness strictly, so the witness would not be contingent. -/
theorem noNecessaryActYieldsAll {W B : Type} (m : Profile W B) (w : W)
    (hCore : TruthCore.Modal.SimplicityCollapse.Core) (h : SomeActualContingentAt m w) :
    NoNecessaryActStrictlyYieldsAllAt m w := by
  rintro ⟨A, p, a, hpo, hSame, hStrict⟩
  obtain ⟨x, hc, hx⟩ := h
  apply hCore.1 W B A p w a x hSame (hStrict x hc hx.1)
  rw [hpo]
  exact hx

namespace Control
open TruthCore.Causality.ContingentBeingNode.Control
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)

private abbrev corr := TruthCore.Results.Modal.StandardCorrespondenceCertificate.certificate.{0}
private abbrev conv := TruthCore.Results.Modal.ConvergenceCertificate.certificate.{0, 0}
private abbrev kLaws := TruthCore.Results.Modal.K.Laws.checks
private abbrev tLaws := TruthCore.Results.Modal.T.Laws.checks
private abbrev bLaws := TruthCore.Results.Modal.B.Laws.checks
private abbrev s5Laws := TruthCore.Results.Modal.S5.Laws.checks
private abbrev core := TruthCore.Results.Modal.SimplicityCollapse.core

theorem twoNode : SomeActualContingentAt twoWorlds false :=
  ⟨false, trivial, Or.inr rfl, true, trivial, by simp [twoWorlds]⟩

theorem stepNode : SomeActualContingentAt step false :=
  ⟨false, trivial, Or.inr rfl, true, rfl, by simp [step]⟩

/-- Full collapse at a world that accesses only itself. -/
theorem collapsedOfSelfOnly {W B : Type} (o : TruthCore.German.Kant.CosmologicalInference.Ontic W B)
    (u : W) (h : ∀ v, o.frame.access u v → v = u) : RouteCollapsedAt o u :=
  (kLaws.1 W o.frame u).mpr h

theorem nonvacuity : Nonvacuity := by
  obtain ⟨hT, _, hB, h5⟩ :=
    TruthCore.Results.Causality.ModalSenseSupport.Control.universalSchemas
      twoWorlds.ontic.frame (fun _ _ => trivial)
  refine ⟨twoNode, hT, hB, h5, inhabits _ _ twoNode, ?_, notEveryNecessary _ _ twoNode,
    notCollapsedK _ _ kLaws twoNode, notNecessarilyCollapsedT _ _ corr kLaws tLaws hT twoNode,
    notPossiblyCollapsedKTB _ _ conv kLaws bLaws hB twoNode, noNecessaryActYieldsAll _ _ core twoNode⟩
  intro x _ _ hCont
  cases x
  · exact ⟨true, trivial, Or.inl rfl, rfl⟩
  · obtain ⟨_, _, _, hn⟩ := hCont
    exact (hn (Or.inl rfl)).elim

theorem omissions : Omissions := by
  refine ⟨?_, ⟨stepNode, ?_, ?_⟩, ⟨stepNode, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨hT, _, hB, h5⟩ :=
      TruthCore.Results.Causality.ModalSenseSupport.Control.universalSchemas
        oneWorld.ontic.frame (fun _ _ => trivial)
    have hC : RouteCollapsedAt oneWorld.ontic () := collapsedOfSelfOnly _ _ (fun _ _ => rfl)
    refine ⟨hT, hB, h5, ?_, fun _ _ _ _ _ => trivial, hC, fun _ _ => hC, ⟨(), trivial, hC⟩, ?_⟩
    · rintro ⟨_, _, _, _, _, hn⟩
      exact hn trivial
    · exact ⟨Unit, ⟨oneWorld.ontic, (), fun _ _ => True, fun _ _ _ => True⟩, (), rfl,
        fun _ _ => trivial, fun _ _ _ _ _ _ => trivial⟩
  · intro h
    have := (corr.1 Bool step.ontic.frame).mp h false
    simp [step] at this
  · intro v hv
    exact collapsedOfSelfOnly _ _ (fun u hu => by
      have h1 : u = true := hu
      have h2 : v = true := hv
      rw [h1, h2])
  · intro h
    have := (conv.2.2.2.2.2.2.2.1 Bool step.ontic.frame).mpr h false true rfl
    simp [step] at this
  · exact ⟨true, rfl, collapsedOfSelfOnly _ _ (fun u hu => hu)⟩
  · exact ⟨false, trivial, Or.inr rfl, true, Or.inl rfl, by simp [le]⟩
  · exact TruthCore.Results.Causality.ModalSenseSupport.Control.tValid _
      TruthCore.Results.Causality.ModalSenseSupport.Control.leReflexive
  · intro h
    have := (conv.2.2.2.2.2.2.2.1 Bool le.ontic.frame).mpr h false true (Or.inl rfl)
    simp [le, TruthCore.Causality.ModalSenseSupport.Control.leFrame] at this
  · intro h
    have := (conv.2.2.2.2.2.2.2.2 Bool le.ontic.frame).mpr h false true false
      (Or.inl rfl) (Or.inl rfl)
    simp [le, TruthCore.Causality.ModalSenseSupport.Control.leFrame] at this
  · refine ⟨true, Or.inr rfl, collapsedOfSelfOnly _ _ (fun u hu => ?_)⟩
    cases u
    · simp [le, TruthCore.Causality.ModalSenseSupport.Control.leFrame] at hu
    · rfl

theorem scope : Scope := by
  intro W B m w hAll x hc hx hCont
  obtain ⟨_, v, hv, hn⟩ := hCont
  exact (hn (hAll x hc hx v hv)).elim

end Control

/-- The batch controls: nonvacuity, omission models and the vacuity scope of the
grounding premise under concrete necessitarianism. -/
theorem controls : TruthCore.Causality.ContingentBeingNode.Control.Controls :=
  ⟨Control.nonvacuity, Control.omissions, Control.scope⟩

end TruthCore.Results.Causality.ContingentBeingNode
