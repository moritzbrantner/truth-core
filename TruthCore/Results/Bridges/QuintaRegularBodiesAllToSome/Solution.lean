import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuintaVia
namespace TruthCore.Results.Bridges.QuintaRegularBodiesAllToSome
open TruthCore.Latin.Aquinas.SummaTheologiae
/-- Bridge (#401): the quinta via's first premise on its universal reading
(`STMT-NATURAL-BODIES-ACT-REGULARLY-FOR-THE-BEST`: there are natural bodies, and
each regularly attains some end that is best for it) entails its existential
reading (`STMT-SOME-NATURAL-BODIES-ACT-REGULARLY-FOR-THE-BEST`: some natural body
does). Existential instantiation from the existence conjunct, then the universal
conjunct. The converse fails; this bridge does not choose between the readings. -/
theorem someNaturalBodiesActRegularlyForTheBestOfAll {Being : Type} {End : Type}
    (NaturalBody : Being → Prop) (RegularlyAttains Best : Being → End → Prop)
    (hAll : NaturalBodiesActRegularlyForTheBestReading NaturalBody RegularlyAttains Best) :
    SomeNaturalBodiesActRegularlyForTheBestReading NaturalBody RegularlyAttains Best := by
  obtain ⟨⟨x, hx⟩, hEach⟩ := hAll
  -- The body that exists is a natural body that regularly attains a best end.
  refine ⟨x, hx, ?_⟩
  exact hEach x hx
end TruthCore.Results.Bridges.QuintaRegularBodiesAllToSome
