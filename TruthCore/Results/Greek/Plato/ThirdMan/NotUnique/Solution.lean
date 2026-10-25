import TruthCore.Greek.Plato.ThirdMan.Sensitivity
namespace TruthCore.Results.Greek.Plato.ThirdMan.NotUnique
open TruthCore.Greek.Plato.Forms TruthCore.Greek.Plato.ThirdMan
universe u v
/-- The derived plurality is incompatible with numerical uniqueness. -/
theorem notUnique {E : Type u} {Q : Type v} (s : Vocabulary E Q)
    (h : UnboundedForms s) : NotUniqueForms s := by
  intro hu
  obtain ⟨q,hq,hunbounded⟩ := h
  obtain ⟨fs,hlen,hpair,hforms⟩ := hunbounded 2
  cases fs with
  | nil => exact Nat.noConfusion hlen
  | cons f fs =>
    cases fs with
    | nil => exact Nat.noConfusion (Nat.succ.inj hlen)
    | cons g gs =>
      exact (List.pairwise_cons.mp hpair).1 g (List.Mem.head _)
        (hu q hq f g (hforms f (List.Mem.head _)) (hforms g (List.Mem.tail f (List.Mem.head _))))
end TruthCore.Results.Greek.Plato.ThirdMan.NotUnique
