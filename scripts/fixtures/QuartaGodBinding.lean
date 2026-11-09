import TruthCore.Results.Case.Catholicism.FromQuartaViaWithClassicalAttributes.Solution

namespace TruthCore.QuartaGodBindingFixture
open TruthCore.Case.Catholicism

-- Keep the classical predicate elsewhere: a global occurrence must not
-- excuse instantiating the naming premise with an unrestricted predicate.
theorem wrongNaming (σ : Signature) {Respect : Type}
    (InAct : σ.Being → Respect → Prop)
    (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop)
    (esse : Respect) (ComponentOf : σ.Being → σ.Being → Prop)
    (hClassical : GodExists σ.IsGod)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf
      (fun _ => True)) : GodExists σ.IsGod := hClassical
end TruthCore.QuartaGodBindingFixture
