import AngularPhysicalSectorFrequencySupport
import AngularPhysicalSecondBlock
import OAI.NumberTheory.DirichletL.Moments.SecondBlockSupport

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PhysicalBlock
open CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O

open PlainRows (heightCoeff)
theorem normalizedBlock_zero_of_common (η : AngularCharacter) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hz:∀z∈rows,idealCorrelation C D hC hD
      ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z)=0) :
    normalizedBlock η t S β C D hC hD U R rows W K n=0 := by
  unfold normalizedBlock
  apply Finset.sum_eq_zero
  intro z hzr
  let F:O→Ideal O→Ideal O→ℂ:=fun _ I J=>
    wholeKernel W (fun _=>logAnnulus)
      (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
      (Real.log (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K/
        dyadicScale (n 0))) (Real.log (normValue z/dyadicScale (n 1)))
      (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
      (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))
  have he:=sectorFrequency_zero_of_common η t S β C D hC hD hCD F
    ((commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)*z) (hz z hzr)
  simpa only [sectorFrequency,F,mul_zero] using congrArg (fun x:ℂ=>retainedScalar C D U R z*x) he

theorem normalizedBlock_nonzero_common (η : AngularCharacter) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (W:𝓢(ℝ,ℂ)) (K:ℝ) (n:Fin 4→ℤ)
    (hne:normalizedBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  by_contra hn
  push Not at hn
  apply hne
  exact normalizedBlock_zero_of_common η t S β C D hC hD hCD U R rows W K n
    (fun z hz=>by simpa only [mul_assoc] using hn z hz)

theorem physicalBlock_nonzero_common (η : AngularCharacter) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (C D : Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D))
    (R:ℝ) (rows:Finset O) (hrows:∀z∈rows,z≠0)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z∈rows,idealCorrelation C D hC hD
      (commonFrequencyGenerator C D*(nonunitFrequencyGenerator C D U*z))≠0 := by
  rw [physicalBlock_eq η t S β C D hC hD U R rows hrows W K hK n] at hne
  exact normalizedBlock_nonzero_common η t S β C D hC hD hCD U R rows W K n
    (right_ne_zero_of_mul hne)

end OAI.SevenEighths.Angular.PhysicalBlock

#print axioms OAI.SevenEighths.Angular.PhysicalBlock.physicalBlock_nonzero_common
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalBlock.physicalBlock_nonzero_common
