import AngularPhysicalCommonExceptionalCost

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.CommonExceptionalSource
open PlainRows ExceptionalMaskedSource ExceptionalAmplitudePair DetectorAmplitude ExceptionalSourceShell
open PlainRows.CommonRows (Input alloc_ne alloc_norm_pos commonData)
open ExceptionalRows CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentAllocationCost
open CenteredMomentCommonProfile CenteredMomentSourceMass CenteredMomentAddedZeroUniform
open CenteredMomentExceptionalAmplitudePair (Tests)
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]
theorem coordinate_dvd (s:Input ι)(C:Ideal O)(B:actualAllocations s.pools C)(j:ι⊕Fin 2):
    B.val j∣C:=by
  exact (Finset.dvd_prod_of_mem B.val (Finset.mem_univ j)).trans
    (dvd_of_eq (Finset.mem_filter.mp B.property).2)

theorem coordinate_norm_le (s:Input ι)(C:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(j:ι⊕Fin 2):
    (Ideal.absNorm (B.val j):ℝ)≤Ideal.absNorm C:=by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC))
    (map_dvd Ideal.absNorm (coordinate_dvd s C B j))

theorem extracted_lower (s:Input ι)(C:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C)
    (j:ι⊕Fin 2)(Z r X:ℝ)(hZ:1<Z)(hX:Z^r≤X):
    Z^(r-Real.logb Z (Ideal.absNorm C:ℝ))≤X/Ideal.absNorm (B.val j):=by
  have hz:=zero_lt_one.trans hZ
  have hN:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hN]
  exact div_le_div₀ ((Real.rpow_nonneg hz.le r).trans hX) hX (alloc_norm_pos s C B j)
    (coordinate_norm_le s C hC B j)

end OAI.SevenEighths.Angular.CommonExceptionalSource

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.coordinate_dvd
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.coordinate_dvd

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.coordinate_norm_le
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.coordinate_norm_le

#print axioms OAI.SevenEighths.Angular.CommonExceptionalSource.extracted_lower
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.CommonExceptionalSource.extracted_lower
