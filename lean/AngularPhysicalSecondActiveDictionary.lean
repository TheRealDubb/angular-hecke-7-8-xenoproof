import AngularPhysicalSectorFrequencySupport
import AngularPhysicalSecondBlock
import OAI.NumberTheory.DirichletL.Moments.SecondActivePhysicalDictionary

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PhysicalBlock
open PlainRows CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentActiveSource
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentSupport
open CenteredMomentHeckeColumnWindow CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSectorLocalization
open CenteredMomentSecondWholeKernel CenteredMomentLogDyadic
open CenteredMomentSecondSectorRetained CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem sectorFrequency_active (η:AngularCharacter)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(F:O→Ideal O→Ideal O→ℂ)(z:O):
    sectorFrequency η t S β C D hC hD F z=
      sectorFrequency η t (activeSource S β) β C D hC hD F z:=by
  let f:Ideal O→Ideal O→ℂ:=fun I J=>
    if hI:Supported (C*I) then if hJ:Supported (D*J) then
      (if IsCoprime I J then idealCorrelation (C*I) (D*J) hI hJ z else 0)*
        ((β (C*I)*heightCoeff η t I)*star (β (D*J)*heightCoeff η t J))*F z I J
      else 0 else 0
  have he (T:Finset (Ideal O)):
      sectorFrequency η t T β C D hC hD F z=
        ∑I∈sectorPool C hC.1 T,∑J∈sectorPool D hD.1 T,f I J:=by
    calc
      _=∑I:sectorPool C hC.1 T,∑J:sectorPool D hD.1 T,f I J:=by
        unfold sectorFrequency
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro J hJ
        have hc:Supported (C*I):=(supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 T I⟩
        have hd:Supported (D*J):=(supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 T J⟩
        simp only [f,dite_eq_left hc,dite_eq_left hd]
      _=_:=by
        simp_rw [Finset.sum_coe_sort]
        exact Finset.sum_coe_sort (sectorPool C hC.1 T)
          (fun I=>∑J∈sectorPool D hD.1 T,f I J)
  rw [he S,he (activeSource S β)]
  symm
  apply CenteredMomentSecondActivePhysicalDictionary.sector_pair_sum_active C D hC.1 hD.1 S β f
  · intro I J h
    simp only [f,h,zero_mul,mul_zero]
    split_ifs <;> rfl
  · intro I J h
    simp only [f,h,zero_mul,star_zero,mul_zero]
    split_ifs <;> rfl

 theorem physicalBlock_active (η:AngularCharacter)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ):
    physicalBlock η t S β C D hC hD U R rows W K n=
      physicalBlock η t (activeSource S β) β C D hC hD U R rows W K n:=by
  unfold physicalBlock
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  exact sectorFrequency_active η t S β C D hC hD
    (fun j I J=>physicalKernel C D W K R j I J*
      ((dyadicWeight (n 0) (secondEffectiveScale C D
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K)*
        dyadicWeight (n 1) (normValue z)*dyadicWeight (n 2) (I.absNorm:ℝ)*
        dyadicWeight (n 3) (J.absNorm:ℝ):ℝ):ℂ)) _

end OAI.SevenEighths.Angular.PhysicalBlock

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.sectorFrequency_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.sectorFrequency_active

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.physicalBlock_active
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.physicalBlock_active
