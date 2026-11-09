import TruthCore.Case.Catholicism.StageTwo

open TruthCore.Case.Catholicism
namespace TruthCore.GodSenseBindingFixture

theorem classical (σ : Signature) (g : σ.Being) (InAct : σ.Being → Unit → Prop)
    (MoreIn : Unit → σ.Being → σ.Being → Prop) (hGod : σ.IsGod g)
    (h : GodIsMaximalInBeing σ.IsGod InAct MoreIn ()) :
    GodIsMaximalInBeing σ.IsGod InAct MoreIn () := h

-- The same head constant, but a trivial predicate instead of Signature.IsGod.
-- hGod deliberately keeps the classical sense elsewhere in the theorem type.
theorem nominal (σ : Signature) (g : σ.Being) (InAct : σ.Being → Unit → Prop)
    (MoreIn : Unit → σ.Being → σ.Being → Prop) (hGod : σ.IsGod g)
    (h : GodIsMaximalInBeing (fun _ => True) InAct MoreIn ()) :
    GodIsMaximalInBeing (fun _ => True) InAct MoreIn () := h

end TruthCore.GodSenseBindingFixture
