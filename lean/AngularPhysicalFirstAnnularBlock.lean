import AngularPhysicalFirstLiveSupport
import AngularPhysicalFirstCommonBound
import OAI.NumberTheory.DirichletL.Moments.FirstDivisorSupport
import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalAnnularCommonBound

noncomputable section
set_option maxHeartbeats 1000000
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
universe u
namespace OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion CompletedGauss RayFourExpansion
open PlainRows PlainRows.CommonRows PlainRows.ChildInputs PlainRows.FirstPhysical
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentGaussEnergy CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentActiveSource CenteredMomentRowNorm CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalDyadicAssembly (Blocks effectiveScale)
open CenteredMomentFirstPhysicalSource (columns column_supported element element_span scalar
  inactiveWeight fixedPresentationCost fixedPresentationCost_pos)
open CenteredMomentFirstWholeKernel (windows)
open CenteredMomentFirstDiscardedEnergy (inactiveSubsets)
open CenteredMomentSecondRetainedRows CenteredMomentSecondHeightFamily
open CenteredMomentSecondWindowBudget CenteredMomentSecondHarmonicBudget
open CenteredMomentFirstMixedAllowance CenteredMomentRankinRadical
open CenteredMomentFirstInactiveRadicalMass (actual_inactive_radical_mass inactiveWeight_nonneg)
local notation "O" => ActualEisensteinCubic.O
open CenteredMomentSecondDivisorSupport
open CenteredMomentFirstPhysicalDyadicRows (activeRows activeRows_norm activeRows_nonzero)
open FirstPhysicalAdmission (block_activeRows)
variable {ι : Type*} [Fintype ι]

lemma common_coefficient_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : AngularCharacter) (t : ℝ) (I : supportedColumns (residualPool D hD.1 s.columns)) :
    (if IsCoprime D (I:Ideal O) ∧ L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff τ t I=0 := by
  split_ifs with hi
  · have hz : s.beta (D*I)=0 := by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (Finset.mem_filter.mp I.property).2.1 s.beta H hβ hn hi.2)
    rw [hz,zero_mul]
  · rw [zero_mul]

theorem commonEnergy_zero (s : OriginalData ι) (D : Ideal O) (hD : Supported D)
    (H : ℝ) (hβ : ∀I,s.beta I≠0→(I.absNorm:ℝ)≤H)
    (L : Ideal O) (hL : H/(D.absNorm:ℝ)<L.absNorm)
    (τ : AngularCharacter) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    commonEnergy s D hD τ t L W K=0 := by
  unfold commonEnergy gaussEnergy gaussPolynomial
  simp only [common_coefficient_zero s D hD H hβ L hL τ t,zero_mul,
    Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0),Complex.ofReal_zero,tsum_zero]

theorem actual_annular_block_from_common_energy (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : AngularCharacter) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ E₁ E₂ : Ideal O→ℝ,
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), 0≤E₁ L) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), 0≤E₂ L) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ E₁ L*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ E₂ L*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        ∑ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)) := by
  obtain ⟨Cb,hCb,hbound⟩:=fixed_log_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n E₁ E₂ hE₁ hE₂ hleft hright
  rw [block_activeRows η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta
    C D hC hD E rows W K n]
  exact hbound η s t C D hC hD hCD E (activeRows rows n)
    (activeRows_nonzero rows n) K (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 2)) (dyadicScale (n 3)) hK
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _=>CenteredMomentFirstAnnularMajorant.profile_nonneg _)
    (fun h hh=>by
      have hn:=activeRows_norm rows n h hh
      have hm:=CenteredMomentFirstAnnularMajorant.scaled_majorant
        (dyadicScale (n 1)) (normValue h) (dyadicScale_pos _) hn.2.1.le hn.2.2.le
      simpa only [normValue_eq_embedding] using hm.ge)
    E₁ E₂ hE₁ hE₂ hleft hright


end OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.common_coefficient_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.common_coefficient_zero

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.commonEnergy_zero
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.commonEnergy_zero

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.actual_annular_block_from_common_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.actual_annular_block_from_common_energy
