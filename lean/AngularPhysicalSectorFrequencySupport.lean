import AngularPhysicalSectorCorrelationChildren
import OAI.NumberTheory.DirichletL.Moments.SecondSectorFrequency

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PhysicalBlock
open CanonicalQuadraticSieve
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondSectorColumns  CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLedger CenteredMomentCanonicalFirst
local notation "O" => ActualEisensteinCubic.O

open PlainRows (heightCoeff)
def sectorFrequency (η : AngularCharacter) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O) : ℂ :=
  ∑ I : sectorPool C hC.1 S,∑ J : sectorPool D hD.1 S,
    (if IsCoprime (I:Ideal O) (J:Ideal O) then
      idealCorrelation (C*I) (D*J)
        ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
        ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) j
      else 0)*((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F j I J

theorem sectorFrequency_zero_of_common (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O) (hj : idealCorrelation C D hC hD j=0) :
    sectorFrequency η t S β C D hC hD F j=0 := by
  have he := sector_correlation_children η t S β C D hC hD hCD 1 {j} (fun _=>1) F
  simpa only [Finset.sum_singleton,one_mul,hj,zero_mul,mul_zero,Finset.sum_const_zero,
    sectorFrequency] using he

theorem sectorFrequency_common_support (η : AngularCharacter) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (F : O→Ideal O→Ideal O→ℂ) (j : O)
    (hj : sectorFrequency η t S β C D hC hD F j≠0) : commonFrequencyGenerator C D∣j := by
  by_contra hn
  exact hj (sectorFrequency_zero_of_common η t S β C D hC hD hCD F j
    (idealCorrelation_zero_outside_common C D hC hD hCD j hn))

end OAI.SevenEighths.Angular.PhysicalBlock

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.sectorFrequency_common_support
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.sectorFrequency_common_support
