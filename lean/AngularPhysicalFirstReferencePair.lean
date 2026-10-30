import AngularPhysicalFirstFixedConductorBound
import AngularPhysicalFirstSourceSupport
import OAI.NumberTheory.DirichletL.Moments.FirstMixedWindow
import OAI.NumberTheory.DirichletL.Moments.FirstCanonicalFamily
import OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget

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
open CenteredMomentSecondWindowBudget CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedAllowance CenteredMomentRankinRadical
open CenteredMomentFirstInactiveRadicalMass (actual_inactive_radical_mass inactiveWeight_nonneg)
local notation "O" => ActualEisensteinCubic.O
open PlainRows.FirstPhysical.Support
open CenteredMomentFirstMixedRoot (allowance_root allowance_pair paired_reference_root)
open CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentSupportedCorrelation
theorem actual_fixed_reference_pair (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(η:AngularCharacter)(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair η C D hC E ξ₁ ξ₂)
    (K A₀ B₀ a T M Z EL ER:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)
    (ha:0<a)(hT:0<T)(hZ:1<Z)(hEL:0≤EL)(hER:0≤ER)
    (hl:a*T≤(C.absNorm:ℝ)*Real.exp M*A₀)
    (hr:a*T≤(D.absNorm:ℝ)*Real.exp M*B₀):
    ‖scalar C D hC E K A₀ B₀‖/T*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(T/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(T/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)/
        (commonRadical C D).absNorm*Real.sqrt (EL*ER):=by
  have hF:0<fixedPresentationCost:=fixedPresentationCost_pos
  have hNC:0<(C.absNorm:ℝ):=norm_pos C hC.1
  have hND:0<(D.absNorm:ℝ):=norm_pos D hD.1
  have hNR:0<((Ideal.span {activeConductor C D}).absNorm:ℝ):=active_norm_pos C D
  have hP:0<((commonRadical C D).absNorm:ℝ):=norm_pos _ (commonRadical_ne_zero C D)
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hrpos:0<‖eisEmbedding (activeConductor C D)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero _ (activeConductor_supported C D hC)))
  have hs:=scalar_conductor_algebra _ _ K T _ _ _ (Real.exp M/a) fixedPresentationCost
    (η.modulus.absNorm:ℝ) (F.left.modulus.absNorm:ℝ) (F.right.modulus.absNorm:ℝ)
    (norm_nonneg _) (norm_nonneg _) hK.le hT (mul_pos hNC hND)
    (sq_pos_of_pos he) hrpos (by positivity) fixedPresentationCost_pos.le (Nat.cast_nonneg _)
    hqL.le hqR.le (weighted_scalar_volume C D hC E K A₀ B₀ a T M hK hA hB ha hT hl hr)
    F.conductor_caps.1 F.conductor_caps.2
  have haR:=allowance_root Z (C.absNorm:ℝ) (D.absNorm:ℝ)
    ((commonRadical C D).absNorm:ℝ) ((Ideal.span {activeConductor C D}).absNorm:ℝ)
    (allowance C D Z+allowance D C Z) hZ hNC hND hP hNR
    (allowance_pair C D hC hD hCD Z hZ)
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,Real.sqrt_sq (norm_nonneg _)] at haR
  rw [paired_reference_root _ _ T _ _ Z _ _ EL ER hqL hqR hT hNC hND
    (zero_lt_one.trans hZ) hEL hER]
  calc
    _=(‖scalar C D hC E K A₀ B₀‖*T/((C.absNorm:ℝ)*D.absNorm)*
        Real.sqrt ((F.left.modulus.absNorm:ℝ)*F.right.modulus.absNorm))*
        (Z^((allowance C D Z+allowance D C Z)/2)*Real.sqrt (EL*ER)):=by
      field_simp
    _≤(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ)*
        (‖eisEmbedding (activeConductor C D)‖/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)))*
        (Z^((allowance C D Z+allowance D C Z)/2)*Real.sqrt (EL*ER)):=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _=(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ))*
        ((‖eisEmbedding (activeConductor C D)‖/Real.sqrt ((C.absNorm:ℝ)*D.absNorm))*
          Z^((allowance C D Z+allowance D C Z)/2))*Real.sqrt (EL*ER):=by ring
    _≤(‖inactiveWeight C D E‖*(Real.exp M/a)*fixedPresentationCost*K*(η.modulus.absNorm:ℝ))*
        (1/(commonRadical C D).absNorm)*Real.sqrt (EL*ER):=by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haR (by positivity))
        (Real.sqrt_nonneg _)
    _=_:=by ring





theorem original_fixed_reference_pair {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z EL ER:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hEL:0≤EL)(hER:0≤ER)(hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (PlainRows.CommonRows.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=PlainRows.CommonRows.volume s;
    ‖scalar C D hC E K A₀ B₀‖/V*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*Real.sqrt (EL*ER):=by
  have ha:0<(∏i,s.lo i)*a₁*a₂:=
    mul_pos (mul_pos (Finset.prod_pos (fun i _=>s.lo_pos i)) ha₁) ha₂
  obtain ⟨hl,hr⟩:=block_reference_lower s.η m A t S
    (PlainRows.CommonRows.coefficient s R seed) C D hC hD E rows W U
    K K₀ H₀ A₀ B₀ ((∏i,s.lo i)*a₁*a₂) (PlainRows.CommonRows.volume s) M hA hB
    (fun I hi=>original_column_lower s R seed I a₁ a₂ ha₁.le ha₂.le hs₁ hs₂ hi) hwin hn
  exact actual_fixed_reference_pair C D hC hD hCD E s.η ξ₁ ξ₂ F
    K A₀ B₀ _ _ M Z EL ER hK hA hB ha (PlainRows.CommonRows.volume_pos s) hZ hEL hER hl hr


theorem original_four_budget_reference {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z:ℝ)(EL ER:Fin 4→ℝ)(JL JR:ℕ)(height:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hEL:∀i,0≤EL i)(hER:∀i,0≤ER i)(hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (PlainRows.CommonRows.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=PlainRows.CommonRows.volume s;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (∑i:Fin 4,∑j:Fin 4,
        windowBudget JL height ((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i)*
        windowBudget JR height ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER j))≤
      (‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
        (∑i:Fin 4,∑j:Fin 4,windowBudget JL height (EL i)*windowBudget JR height (ER j)) :=by
  dsimp only
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hh:=original_fixed_reference_pair s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
    m A t S C D hC hD hCD E ξ₁ ξ₂ F rows W U K K₀ H₀ A₀ B₀ M Z
    (EL i) (ER j) hK hA hB hZ (hEL i) (hER j) hwin hn
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have hCpos:=norm_pos C hC.1
  have hDpos:=norm_pos D hD.1
  have hV:=PlainRows.CommonRows.volume_pos s
  have hz:0<Z:=zero_lt_one.trans hZ
  have hei:=hEL i
  have herj:=hER j
  have hh':=mul_le_mul_of_nonneg_right hh
    (mul_nonneg (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JL)
      (profileMoment_nonneg JL)) (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JR)
      (profileMoment_nonneg JR)))
  simp only [Real.sqrt_mul (by positivity : 0≤
    (F.left.modulus.absNorm:ℝ)*(PlainRows.CommonRows.volume s/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i),
    Real.sqrt_mul (hEL i)] at hh'
  unfold windowBudget
  nlinarith only [hh']


end OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.actual_fixed_reference_pair
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.actual_fixed_reference_pair

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_fixed_reference_pair
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_fixed_reference_pair

#print axioms OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_four_budget_reference
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstPhysicalSourceAssembly.original_four_budget_reference
