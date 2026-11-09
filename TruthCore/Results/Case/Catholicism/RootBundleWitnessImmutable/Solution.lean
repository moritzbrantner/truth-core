module

public import TruthCore.Case.Catholicism.RootBundleWitnessImmutable

@[expose] public section
namespace TruthCore.Results.Case.Catholicism.RootBundleWitnessImmutable
open TruthCore.Case.Catholicism.RootBundleWitnessImmutable

theorem certificate : Certificate := by
  dsimp only [Certificate, PositiveCertificate, OmissionCertificate, Joint,
    Maximal, First, Priority, Nonoverlap, Conclusion,
    TruthCore.Case.Catholicism.GodIsMaximalInBeing,
    TruthCore.Case.Catholicism.MaximumInBeingIsFirstBeing,
    TruthCore.Case.Catholicism.GodIsImmutable,
    TruthCore.Case.Catholicism.IsImmutable,
    TruthCore.Latin.Aquinas.SummaTheologiae.PureAct,
    TruthCore.Latin.Aquinas.SummaTheologiae.IsMaximumIn,
    TruthCore.Latin.Aquinas.SummaTheologiae.IsFirstBeing,
    TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading,
    TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading,
    positive, withoutMaximal, withoutFirst, withoutPriority, withoutNonoverlap]
  repeat' constructor!
  all_goals decide


theorem evaluation0 : Maximal positive := certificate.1.1.1

theorem evaluation1 : First positive := certificate.1.1.2.1

theorem evaluation2 : Priority positive := certificate.1.1.2.2.1

theorem evaluation3 : Nonoverlap positive := certificate.1.1.2.2.2

theorem evaluation4 : Conclusion positive := certificate.1.2.1

theorem enumerateBool : ∀ x : Bool, x = false ∨ x = true := by decide
end TruthCore.Results.Case.Catholicism.RootBundleWitnessImmutable
