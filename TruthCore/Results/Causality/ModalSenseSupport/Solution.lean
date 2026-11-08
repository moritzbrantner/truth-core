module

public import TruthCore.Causality.ModalSenseSupport
public import TruthCore.Results.Modal.StandardCorrespondenceCertificate.Solution
public import TruthCore.Results.Modal.ConvergenceCertificate.Solution

/-! Frame-class branches of the "necessary" sense fork from modal principles.
Each fork theorem takes the modal library's correspondence certificates
(`StandardCorrespondenceCertificate`: T schema iff reflexive;
`ConvergenceCertificate`: 4 iff transitive, B iff symmetric, 5 iff Euclidean)
as premises and APPLIES them to the route's frame: the schema premises are
modal principles about the route's necessity, and the frame condition of the
selected sense is derived, not assumed. The K node is the existing
`NecessaryRootBoxK` (25 route inputs, NECESSARY-ROOT-BOX-K). The controls
instantiate the certificates with their existing proofs. -/

@[expose] public section

namespace TruthCore.Results.Causality.ModalSenseSupport
open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.ModalSenseSupport
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Case.Catholicism (Signature)

/-- A reading premise fixing one sense, and the node in that sense, give the fork node. -/
theorem forkOfSense {W : Type} {σ : Signature} {m : Profile W σ.Being} {w : W}
    {CN : σ.Being → σ.Being → Prop} {Intended : Sense → Prop} (s : Sense)
    (hSel : ∀ t, Intended t ↔ t = s) (h : NecessaryRootInSense s σ m w CN) :
    NecessaryRootOnIntendedReading Intended σ m w CN :=
  ⟨s, ⟨(hSel s).2 rfl, fun t ht => (hSel t).1 ht⟩, h⟩

/-- T branch (NECESSARY_2 in KT): the K node, the T schema on the route's frame
and the T reading give the fork node; reflexivity comes from the T
correspondence of the modal library. -/
theorem forkT {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Intended : Sense → Prop)
    (hCorr : StandardCorrespondenceCertificate.{0})
    (hK : NecessaryRootBoxK σ m w CN) (hT : OnticTSchemaValid m.ontic)
    (hSel : IntendedIsBoxT Intended) :
    NecessaryRootOnIntendedReading Intended σ m w CN := by
  obtain ⟨n, hBox, hFacts⟩ := hK
  have hRefl : Reflexive m.ontic.frame := (hCorr.1 W m.ontic.frame).mp hT
  exact forkOfSense .boxT hSel ⟨n, ⟨hRefl, hBox⟩, hFacts⟩

/-- S4 branch (NECESSARY_2 in S4): reflexivity from the T correspondence,
transitivity from the 4 correspondence. -/
theorem forkS4 {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Intended : Sense → Prop)
    (hCorr : StandardCorrespondenceCertificate.{0})
    (hConv : ConvergenceCertificate.{0, 0})
    (hK : NecessaryRootBoxK σ m w CN) (hT : OnticTSchemaValid m.ontic)
    (h4 : Ontic4SchemaValid m.ontic) (hSel : IntendedIsBoxS4 Intended) :
    NecessaryRootOnIntendedReading Intended σ m w CN := by
  obtain ⟨n, hBox, hFacts⟩ := hK
  have hRefl : Reflexive m.ontic.frame := (hCorr.1 W m.ontic.frame).mp hT
  have hTrans : Transitive m.ontic.frame := (hConv.2.2.2.2.2.2.1 W m.ontic.frame).mpr h4
  exact forkOfSense .boxS4 hSel ⟨n, ⟨⟨hRefl, hTrans⟩, hBox⟩, hFacts⟩

/-- KTB branch (NECESSARY_2 in KTB): reflexivity from the T correspondence,
symmetry from the B correspondence. -/
theorem forkKTB {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Intended : Sense → Prop)
    (hCorr : StandardCorrespondenceCertificate.{0})
    (hConv : ConvergenceCertificate.{0, 0})
    (hK : NecessaryRootBoxK σ m w CN) (hT : OnticTSchemaValid m.ontic)
    (hB : OnticBSchemaValid m.ontic) (hSel : IntendedIsBoxB Intended) :
    NecessaryRootOnIntendedReading Intended σ m w CN := by
  obtain ⟨n, hBox, hFacts⟩ := hK
  have hRefl : Reflexive m.ontic.frame := (hCorr.1 W m.ontic.frame).mp hT
  have hSymm : Symmetric m.ontic.frame := (hConv.2.2.2.2.2.2.2.1 W m.ontic.frame).mpr hB
  exact forkOfSense .boxB hSel ⟨n, ⟨⟨hRefl, hSymm⟩, hBox⟩, hFacts⟩

/-- S5 branch (NECESSARY_2 in S5): reflexivity from the T correspondence,
Euclideanness from the 5 correspondence. -/
theorem forkS5 {W : Type} (σ : Signature) (m : Profile W σ.Being) (w : W)
    (CN : σ.Being → σ.Being → Prop) (Intended : Sense → Prop)
    (hCorr : StandardCorrespondenceCertificate.{0})
    (hConv : ConvergenceCertificate.{0, 0})
    (hK : NecessaryRootBoxK σ m w CN) (hT : OnticTSchemaValid m.ontic)
    (h5 : Ontic5SchemaValid m.ontic) (hSel : IntendedIsBoxS5 Intended) :
    NecessaryRootOnIntendedReading Intended σ m w CN := by
  obtain ⟨n, hBox, hFacts⟩ := hK
  have hRefl : Reflexive m.ontic.frame := (hCorr.1 W m.ontic.frame).mp hT
  have hEucl : Euclidean m.ontic.frame := (hConv.2.2.2.2.2.2.2.2 W m.ontic.frame).mpr h5
  exact forkOfSense .boxS5 hSel ⟨n, ⟨⟨hRefl, hEucl⟩, hBox⟩, hFacts⟩

namespace Control
open TruthCore.Causality.ModalSenseSupport.Control
open TruthCore.Causality.NecessarySenseFork.Control (unitSignature unitProfile chainFrame)

private abbrev corr := TruthCore.Results.Modal.StandardCorrespondenceCertificate.certificate.{0}
private abbrev conv := TruthCore.Results.Modal.ConvergenceCertificate.certificate.{0, 0}

theorem tValid {W : Type} (F : Frame W) (h : Reflexive F) :
    Valid F (.imp (.box (.atom ())) (.atom ()) : Formula Unit) := (corr.1 W F).mpr h
theorem fourValid {W : Type} (F : Frame W) (h : Transitive F) :
    Valid F (convergenceFormula 0 1 2 0) := (conv.2.2.2.2.2.2.1 W F).mp h
theorem bValid {W : Type} (F : Frame W) (h : Symmetric F) :
    Valid F (convergenceFormula 0 0 1 1) := (conv.2.2.2.2.2.2.2.1 W F).mp h
theorem fiveValid {W : Type} (F : Frame W) (h : Euclidean F) :
    Valid F (convergenceFormula 1 0 1 1) := (conv.2.2.2.2.2.2.2.2 W F).mp h

theorem universalSchemas {W : Type} (F : Frame W) (hU : ∀ a b, F.access a b) :
    Valid F (.imp (.box (.atom ())) (.atom ()) : Formula Unit) ∧
    Valid F (convergenceFormula 0 1 2 0) ∧ Valid F (convergenceFormula 0 0 1 1) ∧
    Valid F (convergenceFormula 1 0 1 1) :=
  ⟨tValid F (fun a => hU a a), fourValid F (fun a _ c _ _ => hU a c),
    bValid F (fun a b _ => hU b a), fiveValid F (fun _ l r _ _ => hU l r)⟩

theorem unitK : NecessaryRootBoxK unitSignature unitProfile () noCN :=
  ⟨(), fun _ _ => trivial, ⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩, trivial,
    fun _ _ => rfl, trivial⟩

theorem everywhereK {W : Type} (F : Frame W) (w : W) :
    NecessaryRootBoxK unitSignature (everywhere F) w noCN :=
  ⟨(), fun _ _ => trivial, ⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩, trivial,
    fun _ _ => rfl, trivial⟩

/-- The fork node on reading `· = s` forces the side condition of `s`. -/
theorem forkForces {W : Type} {m : Profile W unitSignature.Being} {w : W} (s : Sense)
    (h : NecessaryRootOnIntendedReading (· = s) unitSignature m w noCN) :
    ∃ n, NecessaryIn s m w noCN n := by
  obtain ⟨t, ⟨hts, _⟩, n, hn, _⟩ := h
  subst hts
  exact ⟨n, hn⟩

theorem nonvacuity : Nonvacuity := by
  obtain ⟨hT, h4, hB, h5⟩ := universalSchemas unitProfile.ontic.frame (fun _ _ => trivial)
  have hR : Reflexive unitProfile.ontic.frame := fun _ => trivial
  refine ⟨hT, h4, hB, h5, unitK, ?_, ?_, ?_, ?_⟩
  · exact forkT _ _ _ _ _ corr unitK hT (fun _ => Iff.rfl)
  · exact forkS4 _ _ _ _ _ corr conv unitK hT h4 (fun _ => Iff.rfl)
  · exact forkKTB _ _ _ _ _ corr conv unitK hT hB (fun _ => Iff.rfl)
  · exact forkS5 _ _ _ _ _ corr conv unitK hT h5 (fun _ => Iff.rfl)

theorem leReflexive : Reflexive leFrame := fun a => by cases a <;> simp [leFrame]

theorem omissions : Omissions := by
  refine ⟨⟨everywhereK _ _, ?_, fun _ => Iff.rfl, ?_⟩, ⟨everywhereK _ _, ?_, ?_, fun _ => Iff.rfl, ?_⟩,
    ⟨everywhereK _ _, tValid _ leReflexive, ?_, fun _ => Iff.rfl, ?_⟩,
    ⟨everywhereK _ _, tValid _ leReflexive, ?_, fun _ => Iff.rfl, ?_⟩, ?_, ?_⟩
  · intro h
    have := (corr.1 Bool stepFrame).mp h false
    simp [stepFrame] at this
  · intro h
    obtain ⟨_, hn⟩ := forkForces .boxT h
    have := hn.1 false
    simp [everywhere, stepFrame] at this
  · exact tValid _ (fun a => Or.inl rfl)
  · intro h
    have := (conv.2.2.2.2.2.2.1 Nat chainFrame).mpr h 0 1 2 (Or.inr rfl) (Or.inr rfl)
    simp [chainFrame] at this
  · intro h
    obtain ⟨_, hn⟩ := forkForces .boxS4 h
    have := hn.1.2 0 1 2 (Or.inr rfl) (Or.inr rfl)
    simp [everywhere, chainFrame] at this
  · intro h
    have := (conv.2.2.2.2.2.2.2.1 Bool leFrame).mpr h false true (Or.inl rfl)
    simp [leFrame] at this
  · intro h
    obtain ⟨_, hn⟩ := forkForces .boxB h
    have := hn.1.2 false true (Or.inl rfl)
    simp [everywhere, leFrame] at this
  · intro h
    have := (conv.2.2.2.2.2.2.2.2 Bool leFrame).mpr h false true false (Or.inl rfl) (Or.inl rfl)
    simp [leFrame] at this
  · intro h
    obtain ⟨_, hn⟩ := forkForces .boxS5 h
    have := hn.1.2 false true false (Or.inl rfl) (Or.inl rfl)
    simp [everywhere, leFrame] at this
  · obtain ⟨hT, h4, hB, h5⟩ := universalSchemas unitProfile.ontic.frame (fun _ _ => trivial)
    refine ⟨unitK, hT, h4, hB, h5, ?_⟩
    rintro ⟨s, ⟨_, hAll⟩, _⟩
    have h1 := hAll .boxK trivial
    have h2 := hAll .boxT trivial
    exact absurd (h1.trans h2.symm) (by decide)
  · obtain ⟨hT, h4, hB, h5⟩ := universalSchemas nowhere.ontic.frame (fun _ _ => trivial)
    refine ⟨hT, h4, hB, h5, fun _ => Iff.rfl, ?_⟩
    rintro ⟨_, _, _, _, hRoot, _⟩
    exact hRoot.1.2

theorem rivalNegations : RivalNegations := by
  refine ⟨fun W B o w => ⟨?_, ?_⟩, ?_⟩
  · rintro h ⟨a, b, hab, ha, hpa, hb, hpb⟩
    exact h a b ha hpa hb hpb hab
  · intro h a b ha hpa hb hpb hab
    exact h ⟨a, b, hab, ha, hpa, hb, hpb⟩
  · rintro hCore ⟨W, B, A, p, w, a, x, hSame, hStrict, hCont⟩
    exact hCore.1 W B A p w a x hSame hStrict hCont

end Control

/-- The batch controls: nonvacuity, one omission model per load-bearing premise,
and the exact negations of the two recorded rivals. -/
theorem controls : TruthCore.Causality.ModalSenseSupport.Control.Controls :=
  ⟨Control.nonvacuity, Control.omissions, Control.rivalNegations⟩

end TruthCore.Results.Causality.ModalSenseSupport
