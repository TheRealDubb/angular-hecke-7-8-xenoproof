import AngularPhysicalFirstReducedEnergy
import OAI.NumberTheory.DirichletL.Moments.SupportedZeroEnergy
import OAI.NumberTheory.DirichletL.Moments.SourceZeroEnergy

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows
open CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentRowNorm
open CenteredMomentSourceRow (supportedColumns sourceGenerator sourceGenerator_supported primary_span_supported)
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentFirstLocalization (canonicalZeroPair)
open CenteredMomentZeroMeanBridge (canonical_ideal_zero_sum)
open CenteredMomentZeroMode (idealZeroEnergy)
open CenteredMomentSupportedZeroEnergy (activeColumns activeColumns_supported idealZeroEnergy_filter)
open CenteredMomentAddedZeroUniform (Tuple finiteTupleProduct)
open CenteredMomentSourceMass (finiteColumns finiteColumnCoefficient)

def zeroEnergy (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalZeroPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K

theorem zeroEnergy_eq_original (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      CenteredMomentZeroMode.idealZeroEnergy (CenteredMomentSourceRow.supportedColumns S)
        (fun _ h => (Finset.mem_filter.mp h).2)
        (fun I => c I * rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  unfold zeroEnergy
  exact canonical_ideal_zero_sum (CenteredMomentSourceRow.supportedColumns S)
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun I => c I * rowWeight η m A 1 t I) W K

theorem zeroEnergy_eq_active_original (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K =
      idealZeroEnergy (activeColumns S c) (activeColumns_supported S c)
        (fun I => c I*rowWeight η m A 1 t I) K * paperRadialFourier W 0 := by
  rw [zeroEnergy_eq_original]
  congr 1
  exact idealZeroEnergy_filter (supportedColumns S) (fun I h => (Finset.mem_filter.mp h).2)
    (fun I => c I*rowWeight η m A 1 t I) K (fun I => c I≠0)
    (fun I _ h => by simp only [not_not] at h; rw [h,zero_mul])

theorem zeroEnergy_eq_active (η : AngularCharacter) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    zeroEnergy η m A t S c W K = zeroEnergy η m A t (activeColumns S c) c W K := by
  rw [zeroEnergy_eq_active_original,zeroEnergy_eq_original]
  have he : supportedColumns (activeColumns S c)=activeColumns S c :=
    Finset.filter_eq_self.mpr (activeColumns_supported S c)
  simp only [he]

theorem zeroEnergy_eq_zero_of_subunit {ι : Type*} [Fintype ι]
    (η : AngularCharacter) (m A : O) (t : ℝ) (S : Finset (Tuple ι)) (β : Tuple ι → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K Y : ℝ) (hY : Y<1)
    (hN : ∀ v∈S,β v≠0 → finiteTupleProduct v≠0 ∧
      (Ideal.absNorm (finiteTupleProduct v):ℝ)≤Y) :
    zeroEnergy η m A t (finiteColumns S) (finiteColumnCoefficient S β) W K=0 := by
  have hb (v : Tuple ι) (hv : v∈S) : β v=0 := by
    by_contra hn
    have hh := hN v hv hn
    have hnorm : (1:ℝ)≤Ideal.absNorm (finiteTupleProduct v) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hh.1)
    linarith
  have hc (I : Ideal O) : finiteColumnCoefficient S β I=0 := by
    unfold finiteColumnCoefficient
    exact Finset.sum_eq_zero (fun v hv => hb v (Finset.mem_filter.mp hv).1)
  simp only [zeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.zeroEnergy_eq_original
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.zeroEnergy_eq_original

#print axioms OAI.SevenEighths.Angular.PlainRows.zeroEnergy_eq_active_original
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.zeroEnergy_eq_active_original

#print axioms OAI.SevenEighths.Angular.PlainRows.zeroEnergy_eq_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.zeroEnergy_eq_active

#print axioms OAI.SevenEighths.Angular.PlainRows.zeroEnergy_eq_zero_of_subunit
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.zeroEnergy_eq_zero_of_subunit
