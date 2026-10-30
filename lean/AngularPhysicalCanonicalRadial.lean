import AngularPhysicalEnergyState
import AngularPhysicalFixedRowMask
import OAI.NumberTheory.DirichletL.Energy.ChildState

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.ChildState
open EnergyState CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open CenteredMomentRadialEligibleEnergy (Radial)
open CenteredMomentSecondOriginalChildren (sourceRadial)
open CenteredMomentFirstAmplificationChoice (ballProfile ballProfile_nonneg)
open CenteredMomentSectorLocalization (dyadicScale dyadicScale_pos)
local notation "O" => ActualEisensteinCubic.O
def canonicalRadial (τ:AngularCharacter)(Q:Ideal O)(n:Fin 4→ℤ):Radial:=
  sourceRadial (fun z=>z≠0 ∧ ¬ExceptionalRows.FixedInducingRow τ Q fixedBadMask 1 z)
    ballProfile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _z=>ballProfile_nonneg _)

lemma canonical_mask_nonexceptional (τ:AngularCharacter)(Q R:Ideal O)(hR:R≠0)
    (n:Fin 4→ℤ)(z:O)(hz:(canonicalRadial τ Q n).keep z):
    ¬ExceptionalRows.FixedInducingRow τ Q
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z:=by
  intro hh
  exact hz.2 ((ExceptionalRows.fixedInducingRow_mul_mask_iff τ Q
    fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
    (ConcretePrimeRowBridge.idealGenerator_ne_zero R hR) one_ne_zero hz.1
    (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh)


end OAI.SevenEighths.Angular.ChildState

#print axioms OAI.SevenEighths.Angular.ChildState.canonical_mask_nonexceptional
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ChildState.canonical_mask_nonexceptional
