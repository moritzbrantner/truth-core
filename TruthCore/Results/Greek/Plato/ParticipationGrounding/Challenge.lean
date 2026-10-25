import TruthCore.Greek.Plato.ParticipationGrounding
namespace TruthCore.Results.Greek.Plato.ParticipationGrounding
open TruthCore.Greek.Plato.Forms TruthCore.Greek.Plato.ParticipationGrounding
universe u v w
variable {Entity : Type u} {Quality : Type v} {Feature : Type w}
theorem assignmentUnderdetermined : AssignmentUnderdetermined := by sorry
theorem groundingIndependent : GroundingIndependent := by sorry
theorem noCircularExplanation (e : Explanation Entity Quality Feature)
    (h : AsymmetricGround e) (x f : Entity) (q : Quality) :
    NoCircularExplanation e x f q := by sorry
theorem selectorAgreement (s t : Vocabulary Entity Quality)
    (e d : Explanation Entity Quality Feature) (feature : Feature)
    (h : SharedSelector s t e d feature) : ClassificationAgreement s t := by sorry
end TruthCore.Results.Greek.Plato.ParticipationGrounding
