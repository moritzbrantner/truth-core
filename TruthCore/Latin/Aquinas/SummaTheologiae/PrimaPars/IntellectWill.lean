/-!
Source-derived readings from Thomas Aquinas, *Summa theologiae* I q.14 a.1 co.
(*utrum in Deo sit scientia*) and I q.19 a.1 co. (*utrum in Deo sit voluntas*),
used for stage 2, group 3 (#143).

Vocabulary: `ComposedOfMatterAndForm x` as in q.3 a.2 and a.7; `HasIntellect x`
and `HasWill x` are primitive predicates whose content these readings constrain.

Source witnesses: SCTA diplomatic TEI of the Leonine edition, vol. 4 (Rome 1888),
`scta-texts/TAca84`, passages `AQUINAS-ST-I-Q14-A1` and `AQUINAS-ST-I-Q19-A1`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u

/-- Immateriality is the reason why a thing knows (*immaterialitas alicuius rei
est ratio quod sit cognoscitiva*), and the mode of knowledge follows the mode of
immateriality: the intellect knows more than sense because it is more separate
from matter. Since God is in the highest degree immaterial, he is in the highest
degree of knowledge.

Read as: what is in no way composed of matter and form has intellect. This is
the interpretive step: the article grades knowledge by immateriality, and the
reading takes its highest grade, altogether immaterial, as intellectual.

Source: Thomas Aquinas, *Summa theologiae* I q.14 a.1 co.
-/
def ImmaterialIsIntellectualReading {Being : Sort u}
    (ComposedOfMatterAndForm HasIntellect : Being → Prop) : Prop :=
  ∀ x, ¬ ComposedOfMatterAndForm x → HasIntellect x

/-- Will follows intellect: "in whatever has intellect there is will, as in
whatever has sense there is animal appetite" (*in quolibet habente intellectum,
est voluntas*).

Source: Thomas Aquinas, *Summa theologiae* I q.19 a.1 co.
-/
def WillFollowsIntellectReading {Being : Sort u} (HasIntellect HasWill : Being → Prop) :
    Prop :=
  ∀ x, HasIntellect x → HasWill x

end TruthCore.Latin.Aquinas.SummaTheologiae
