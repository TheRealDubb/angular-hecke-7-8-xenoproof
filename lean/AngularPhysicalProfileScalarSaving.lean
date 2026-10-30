import AngularPhysicalProfilePhysicalBudget

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical
open PlainRows DetectorAmplitude ExceptionalAmplitudePair FiniteProfileExceptional
open FiniteProfileExceptionalCommon CommonExceptionalSource
open PlainRows.CommonRows (Input withHeight)
open CenteredMomentFiniteProfileExceptional CenteredMomentHeckeWindowEnergy
open CanonicalQuadraticSieve ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
universe u

open MeasureTheory
open FiniteProfileExceptionalPhysical ChildRows RayFourExpansion
open CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondHeightFamily (fixedBadMask)
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentRowNorm CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentForcing
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentLogDyadic
open CenteredMomentSmooth CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentHeckeColumnWindow
local instance {κ:Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι:Type u} [Fintype ι] [DecidableEq ι]
open CenteredMomentSecondPhysicalLedger CenteredMomentRankinRadical

lemma forcingNorm_ge_one (C D:Ideal O)(hC:Supported C)(U:Finset (CommonIndex C D)) :
    1≤forcingNorm C D U := by
  have hf:0<forcingNorm C D U:=common_product_pos C D hC _
  unfold forcingNorm at hf ⊢
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast ne_of_gt hf)

lemma column_cap_ledger (c d r:ℝ)(hc:0≤c)(hd:0≤d) :
    2*max r 0/3≤(c+d)/3+max (r-min c d) 0 := by
  have hmin:0≤min c d:=le_min hc hd
  have hc':min c d≤c:=min_le_left _ _
  have hd':min c d≤d:=min_le_right _ _
  by_cases hr:0≤r
  · rw [max_eq_left hr]
    by_cases hm:r≤min c d
    · rw [max_eq_right (by linarith : r-min c d≤0)]
      linarith
    · rw [max_eq_left (by linarith : 0≤r-min c d)]
      linarith
  · rw [max_eq_right (le_of_not_ge hr)]
    have hm:0≤max (r-min c d) 0:=le_max_right _ _
    linarith

lemma common_weight_bound (Z c d θ B ε δ r:ℝ)(hZ:1<Z)(hc:1≤c)(hd:1≤d)
    (hθ:0≤θ)(hC:c≤Z^B)(hD:d≤Z^B):
    Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*(c*d)^θ*
      Z^(-(Real.logb Z c+Real.logb Z d)/3)≤
        Z^(2*ε+δ+2*B*θ-2*max r 0/3):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hcd:0≤c*d:=mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans hd)
  have hpow:(c*d)^θ≤Z^(2*B*θ):=by
    calc
      _≤(Z^B*Z^B)^θ:=Real.rpow_le_rpow hcd
        (mul_le_mul hC hD (zero_le_one.trans hd) (Real.rpow_nonneg hz.le _)) hθ
      _=Z^(2*B*θ):=by
        rw [←Real.rpow_add hz,←Real.rpow_mul hz.le]
        congr 1;ring
  have hl:=column_cap_ledger (Real.logb Z c) (Real.logb Z d) r
    (Real.logb_nonneg hZ hc) (Real.logb_nonneg hZ hd)
  calc
    _≤Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*Z^(2*B*θ)*
      Z^(-(Real.logb Z c+Real.logb Z d)/3):=by gcongr
    _=Z^((2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)+2*B*θ-
      (Real.logb Z c+Real.logb Z d)/3):=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1;ring
    _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem common_ideal_product (I J : Ideal O) :
    (∏ P : CommonIndex I J, P.val) = commonRadical I J := by
  exact Finset.prod_coe_sort (s := CenteredMomentCompleteCommon.commonSupport I J) (f := fun P : Ideal O => P)

end OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical

#print axioms OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical.forcingNorm_ge_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical.forcingNorm_ge_one

#print axioms OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical.column_cap_ledger
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical.column_cap_ledger

#print axioms OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical.common_weight_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical.common_weight_bound

#print axioms OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical.common_ideal_product
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FiniteProfileExceptionalPhysical.common_ideal_product
