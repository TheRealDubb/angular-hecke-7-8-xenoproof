import AngularPhysicalOrderPairedAmplitude

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.ExceptionalSourceShell
open PlainRows DetectorAmplitude ExceptionalAmplitudePair ExceptionalShell
open CenteredMomentExceptionalAmplitudePair (Tests)
local notation "O" => ActualEisensteinCubic.O
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]
def profileMass {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Tests)(J:ℕ):ℝ:=
  p.heightWeight s.t^J*q.heightWeight v.t^J*slotControl s*slotControl v*
    Real.sqrt (volume s)*Real.sqrt (volume v)

lemma profileMass_nonneg {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Data α)(v:Data κ)(p q:Tests)(J:ℕ):0≤profileMass s v p q J:=by
  unfold profileMass
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by dsimp [Tests.heightWeight]; positivity)
    (slotControl_nonneg s)) (slotControl_nonneg v)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end OAI.SevenEighths.Angular.ExceptionalSourceShell

#print axioms OAI.SevenEighths.Angular.ExceptionalSourceShell.profileMass_nonneg
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ExceptionalSourceShell.profileMass_nonneg
