import TruthCore.Case.Catholicism.StageTwo

/-!
ST I q.11 a.3 co., first proof, with q.3 a.3 co. The `Principle` images
represent the individuating suppositum and nature of a being. Equality of these
images is not equality between the Lean types Being and Principle. Their
connection to individual identity is an explicit premise, not a definition.
The domain is divine beings, not the divine persons of Trinitarian theology.
-/
namespace TruthCore.Latin.Aquinas.SummaTheologiae

universe u v

/-- Q.11 a.3 first proof: that by which a singular is this singular cannot be
shared by numerically different individuals. `suppositumOf` represents that
individuating basis; injectivity remains a substantive sourced assumption. -/
def IndividuatingBasisIsIncommunicableReading {Being : Sort u} {Principle : Sort v}
    (suppositumOf : Being → Principle) : Prop :=
  ∀ x y, suppositumOf x = suppositumOf y → x = y

/-- Q.3 a.3 co., reused by q.11 a.3: in God the suppositum does not differ from
nature. Read universally over proper instances of the original `IsGod`; no
absence-of-composition premise is silently strengthened to this identity. -/
def GodSuppositumIsNatureReading {Being : Sort u} {Principle : Sort v}
    (IsGod : Being → Prop) (suppositumOf essenceOf : Being → Principle) : Prop :=
  ∀ g, IsGod g → suppositumOf g = essenceOf g

/-- Q.11 a.3's contrast between being God and being this God presupposes one
nature signified by the proper divine name. This universal shared-nature
reading is explicit and open; `IsGod` is not defined by this equality. The
parameter is not a genus, a universal received in matter, or a divine person. -/
def ProperGodInstancesHaveCommonNatureReading {Being : Sort u} {Principle : Sort v}
    (IsGod : Being → Prop) (essenceOf : Being → Principle) (deity : Principle) : Prop :=
  ∀ g, IsGod g → essenceOf g = deity

/-- Local non-entailment when individuation is omitted: two distinct proper-God
instances may have equal suppositum/nature images. This is a finite logical
sensitivity test, not a source-faithful alternative theology. -/
def UniquenessFailsWithoutIndividuation : Prop :=
  ∃ suppositumOf essenceOf : Bool → Bool, ∃ deity : Bool,
    GodSuppositumIsNatureReading (fun _ => True) suppositumOf essenceOf ∧
    ProperGodInstancesHaveCommonNatureReading (fun _ => True) essenceOf deity ∧
    ¬ TruthCore.Case.Catholicism.GodIsOne (fun _ : Bool => True)

/-- Local sensitivity test omitting only the suppositum/nature identity. -/
def UniquenessFailsWithoutNatureIdentity : Prop :=
  ∃ suppositumOf essenceOf : Bool → Bool, ∃ deity : Bool,
    IndividuatingBasisIsIncommunicableReading suppositumOf ∧
    ProperGodInstancesHaveCommonNatureReading (fun _ => True) essenceOf deity ∧
    ¬ TruthCore.Case.Catholicism.GodIsOne (fun _ : Bool => True)

/-- Local sensitivity test omitting only the common divine-nature reading. -/
def UniquenessFailsWithoutCommonNature : Prop :=
  ∃ suppositumOf essenceOf : Bool → Bool,
    IndividuatingBasisIsIncommunicableReading suppositumOf ∧
    GodSuppositumIsNatureReading (fun _ => True) suppositumOf essenceOf ∧
    ¬ TruthCore.Case.Catholicism.GodIsOne (fun _ : Bool => True)

end TruthCore.Latin.Aquinas.SummaTheologiae
