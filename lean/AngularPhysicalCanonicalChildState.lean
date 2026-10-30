import AngularPhysicalCanonicalRadial

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
open CenteredMomentEnergyChildState (ball_support)
def canonicalState {angularOrder:ℕ} (Z Bmask:ℝ)(hZ:1<Z)(τ:AngularCharacter)(horder:τ.k.natAbs=angularOrder)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)
    (hn:1≤dyadicScale (n 1)):NaturalState angularOrder Z Bmask 2 where
  character:=τ
  angular_order:=horder
  fixedModulus:=Q
  puncture:=R
  radial:=canonicalRadial τ Q n
  rowWidth:=Real.logb Z (dyadicScale (n 1))
  characterWidth:=Real.logb Z (τ.modulus.absNorm:ℝ)
  base_ge_one:=hZ.le
  row_nonneg:=Real.logb_nonneg hZ hn
  character_nonneg:=Real.logb_nonneg hZ (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))
  scale_eq:=(Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _)).symm
  modulus_bound:=by
    rw [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  puncture_ne_zero:=hR
  puncture_bound:=hRN
  radial_support:=ball_support
  row_ne_zero:=fun _ hz=>hz.1
  nonexceptional:=canonical_mask_nonexceptional τ Q R hR n

lemma canonicalState_width {angularOrder:ℕ} (Z Bmask:ℝ)(hZ:1<Z)(τ:AngularCharacter)(horder:τ.k.natAbs=angularOrder)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    (canonicalState Z Bmask hZ τ horder Q R hR hRN n hn).width=
      Real.logb Z (dyadicScale (n 1))+Real.logb Z (τ.modulus.absNorm:ℝ):=rfl

lemma canonicalState_power {angularOrder:ℕ} (Z Bmask:ℝ)(hZ:1<Z)(τ:AngularCharacter)(horder:τ.k.natAbs=angularOrder)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)(hn:1≤dyadicScale (n 1)):
    Z^(canonicalState Z Bmask hZ τ horder Q R hR hRN n hn).width=
      (τ.modulus.absNorm:ℝ)*dyadicScale (n 1):=by
  rw [canonicalState_width,Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (dyadicScale_pos _),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (show 0<(τ.modulus.absNorm:ℝ) by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot))]
  ring


theorem canonicalState_order {angularOrder:ℕ} (Z Bmask:ℝ)(hZ:1<Z)
    (τ:AngularCharacter)(horder:τ.k.natAbs=angularOrder)(Q R:Ideal O)
    (hR:R≠0)(hRN:(R.absNorm:ℝ)≤Z^Bmask)(n:Fin 4→ℤ)
    (hn:1≤dyadicScale (n 1)) :
    (canonicalState Z Bmask hZ τ horder Q R hR hRN n hn).character.k.natAbs=angularOrder :=
  horder

end OAI.SevenEighths.Angular.ChildState

#print axioms OAI.SevenEighths.Angular.ChildState.canonicalState_power
#print axioms OAI.SevenEighths.Angular.ChildState.canonicalState_order
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ChildState.canonicalState_order
