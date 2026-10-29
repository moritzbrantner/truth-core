import TruthCore.Causality.OccurrenceUnderivedEssence
import TruthCore.Results.Causality.CogitoNecessaryConcrete.Solution
import TruthCore.Results.Causality.UnderivedEssenceEsse.Solution
namespace TruthCore.Results.Causality.OccurrenceUnderivedEssence
open TruthCore.Causality.CogitoNecessaryConcrete
open TruthCore.Causality.OccurrenceUnderivedEssence
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.UnderivedNonComposite
open TruthCore.Logic.CogitoSubject
open TruthCore.Logic.CogitoConcrete
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4

/-- Refine the existing #564 descent without dropping its root property;
transport actual support into that SAME grounding relation, and apply the
existing #680 q3 theorem to that SAME individual. No necessity→underived step. -/
theorem checks {W B Episode P A : Type}
    (m : TruthCore.Causality.BruteFoundationBoundary.Profile W B)
    (Occurs : Episode → Prop) (Bears : B → Episode → Prop)
    (R : W → B → B → Prop) (w : W) (p : Profile B P A)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hConcrete : EveryBearerIsConcrete Occurs Bears m.concrete)
    (hExists : EveryBearerExistsAt m.ontic Occurs Bears w)
    (hAcc : ThinkerGroundingAccessible m Occurs Bears w)
    (hGrounded : ThinkerAncestryGrounded m Occurs Bears w)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hSupport : ActualSupportIsConcreteGround m R w)
    (hInAct : ExistingInActAt m.ontic p.InAct p.esse w)
    (hPresent : UnitingCausesPresent m.ontic p.CausesIn p.esse w)
    (hTyped : ActualEsseCausesSupportAt m.ontic R p.CausesIn p.esse w)
    (hExhaustive : DistinctEsseCauseDichotomyReading p)
    (hNoSelfCause : EssentialPrinciplesCannotCauseDistinctEsseReading p) :
    SameWitnessEssenceIdentity m Occurs Bears R w p := by
  obtain ⟨b, e, n, he, hb, ha, hc, hn, hNec, hRoot⟩ :=
    TruthCore.Results.Causality.CogitoNecessaryConcrete.necessaryConcreteRootAncestor
      m Occurs Bears w hOccurs hBearer hConcrete hExists hAcc hGrounded hEM
  have hNo : ∀ c, m.ontic.ExistsAt w c → ¬ R w c n := by
    intro c hce hR
    exact hRoot c (hSupport c n hce hc hn hR)
  refine ⟨b, e, n, he, hb, ha, hc, hn, hNec, hRoot, hNo, ?_⟩
  have hNN := TruthCore.Results.Causality.UnderivedEssenceEsse.actual_not_not_identity_direct
    m.ontic R w p n hn hNo hInAct hPresent hTyped hExhaustive hNoSelfCause
  cases hEM (p.esseOf n = p.essenceOf n) with
  | inl h => exact h
  | inr h => exact False.elim (hNN h)
/-- A necessary bearer need not itself be the minimal ancestor. The root
selection retained by the new helper, rather than necessity alone, matters. -/
theorem recipient_control : NecessaryRecipientControl := by
  have hAcc : ∀ b, Acc (ActualConcreteGround recipientGrounding true) b := by
    have hWF : WellFounded (ActualConcreteGround recipientGrounding true) := by
      apply Subrelation.wf (r := fun c n : Bool =>
        TruthCore.Models.NecessarilyUnderived.varyingRank c <
        TruthCore.Models.NecessarilyUnderived.varyingRank n)
      · intro c n h
        rcases h.2.2 with ⟨_, rfl, rfl⟩
        decide
      · exact InvImage.wf TruthCore.Models.NecessarilyUnderived.varyingRank Nat.lt_wfRel.wf
    exact hWF.apply
  refine ⟨⟨(), trivial⟩, (fun _ _ => ⟨true, rfl⟩), (fun _ _ _ _ => trivial),
    (fun _ _ _ _ => trivial), (fun b _ _ _ => hAcc b), ?_, ?_,
    (fun _ _ => trivial), ?_, (by decide), ?_, rfl⟩
  · intro _ _ _ _ _ _ _ _ hcont
    obtain ⟨_, v, _, hv⟩ := hcont
    exact (hv trivial).elim
  · exact ⟨true, (), true, trivial, rfl, Relation.ReflTransGen.refl,
      trivial, trivial, fun _ _ => trivial⟩
  · intro h
    exact h false trivial ⟨rfl, rfl, rfl⟩
  · intro c _ h
    exact Bool.noConfusion h.2.2
end TruthCore.Results.Causality.OccurrenceUnderivedEssence
