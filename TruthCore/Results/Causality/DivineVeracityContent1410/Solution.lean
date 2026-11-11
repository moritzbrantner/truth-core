module
public import Mathlib.Logic.Function.Defs
public import TruthCore.Causality.DivineVeracityContent1410

@[expose] public section
namespace TruthCore.Results.Causality.DivineVeracityContent1410
open TruthCore.Case.Catholicism
open TruthCore.Causality.NamingVeracityBatch1
open TruthCore.Causality.DivineVeracity1410
open TruthCore.Causality.DivineVeracityContent1410
open TruthCore.Logic.ReflectiveCoherence (Semantics)

theorem contentRouteA {World Content : Type} (σ : Signature) (S : Semantics World Content) (w : World)
    (V : Attitudes σ Content) (D : Content → Prop)
    (h0 : ContentSincere σ V) (h1 : ScopedAccuracy σ S w V D)
    (h2 : AssertionsInDomain σ V D) : ContentAssertionTruth σ S w V :=
  fun g hg hc c ha => h1 g hg hc c (h2 g hg hc c ha) (h0 g hg hc c ha)

theorem contentRouteB {World Content : Type} (σ : Signature) (S : Semantics World Content) (w : World)
    (V : Attitudes σ Content) (h0 : CounterComplete σ S w V)
    (h1 : NoContraryAssertion σ S V) : ContentAssertionTruth σ S w V := by
  intro g hg hc c ha
  exact Classical.byContradiction (fun hn =>
    h1 g hg hc c ha (h0 g hg hc c ha ((S.neg_true_iff w c).mpr hn)))

theorem counterCompleteFromDomain {World Content : Type} (σ : Signature) (S : Semantics World Content) (w : World)
    (V : Attitudes σ Content) (D : Content → Prop)
    (h0 : DomainComplete σ S w V D) (h1 : AssertionsInDomain σ V D)
    (h2 : NegationClosed S D) : CounterComplete σ S w V :=
  fun g hg hc c ha hn => h0 g hg hc (S.neg c) (h2 c (h1 g hg hc c ha)) hn

theorem legacyAssertionFromContent {World Content : Type} (σ : Signature) (S : Semantics World Content) (w : World)
    (C : Attitudes σ Content) (V : Veracity σ)
    (h0 : ContentAssertionTruth σ S w C)
    (h1 : AssertionRepresentation σ S w C V) : GodAssertsOnlyTruth σ V := by
  intro g hg hc p ha
  obtain ⟨c, hca, hd⟩ := h1 g hg hc p ha
  exact hd (h0 g hg hc c hca)

theorem erasureRepresented {World Content : Type} (σ : Signature) (S : Semantics World Content) (w : World)
    (C : Attitudes σ Content) : ErasureRepresentation σ S w C := by
  intro g _ _ p ha
  obtain ⟨c, hca, heq⟩ := ha
  exact ⟨c, hca, heq.mp⟩

open TruthCore.Causality.DivineVeracityContent1410.Control

theorem controls : TruthCore.Causality.DivineVeracityContent1410.Control.Certificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [JointSelective, ContentAssertionTruth, ContentSincere, ScopedAccuracy,
      AssertionsInDomain, NegationClosed, DomainComplete, CounterComplete,
      NoContraryAssertion, semantics, domain, selective, a, b, σ,
      TruthCore.Causality.NamingVeracityBatch1.Control.sig, Bool.forall_bool, Prod.forall]
  · intro V h
    have heq : semantics.trueAt false a = semantics.trueAt false b :=
      propext ⟨fun _ => rfl, fun _ => rfl⟩
    have ha := (h a).mpr rfl
    have hb := (h b).mp (heq ▸ ha)
    exact Bool.noConfusion (congrArg (fun c : Bool × Bool × Bool => c.2.2) hb)
  · simp [RouteBSuspension, CounterComplete, NoContraryAssertion,
      ContentAssertionTruth, ContentSincere, suspended, semantics, a, σ,
      TruthCore.Causality.NamingVeracityBatch1.Control.sig, Bool.forall_bool ]
  · simp [CognitiveRival, DomainComplete, ScopedAccuracy, ConsistentAssent,
      ContentAssertionTruth, deceiving, semantics, a, σ,
      TruthCore.Causality.NamingVeracityBatch1.Control.sig, Bool.forall_bool ]
  · simp [DomainGaps, DomainComplete, AssertionsInDomain, NegationClosed,
      CounterComplete, NoContraryAssertion, ContentAssertionTruth, suspendedFalse,
      semantics, a, σ, TruthCore.Causality.NamingVeracityBatch1.Control.sig,
      Bool.forall_bool]

end TruthCore.Results.Causality.DivineVeracityContent1410
