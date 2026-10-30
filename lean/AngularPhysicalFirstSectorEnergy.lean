import AngularPhysicalFirstZeroDictionary
import OAI.NumberTheory.DirichletL.Moments.FirstSectorLocalization

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows
open CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentRowNorm
open CenteredMomentSourceRow (supportedColumns sourceGenerator sourceGenerator_supported primary_span_supported)
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentFirstSectorLocalization (retainedPair discardedPair reducedFirstSum_sector_split)

def retainedEnergy (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      retainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

def discardedEnergy (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      discardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

theorem finiteHeckeEnergy_sector_localized (η : AngularCharacter) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K X Z ξ : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K X Z ξ+
        discardedEnergy η m A t S c W K X Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_sector_split _ _ _ _ W K X Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.finiteHeckeEnergy_sector_localized
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.finiteHeckeEnergy_sector_localized
