import AngularPhysicalSecondSourcePoisson

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.PlainRows.SecondSource
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentFirstSectors CenteredMomentCommonSectors
open IdealMobiusDivisorSum ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFourier CenteredMomentPoisson CenteredMomentSupportedCorrelation
open CenteredMomentRowNorm CenteredMomentSecondDiagonal
open CenteredMomentSecondSourceEnergy (secondSourceKernel)
open CenteredMomentSecondSourcePoisson (secondSourceKernel_poisson)
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceZeroEnergy CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceSecondZeroEnergy
  (secondZeroEnergy_filter sourceGenerator_span sourceGenerator_primary sourceGenerator_injective
   profileCoefficient_dvd)
local notation "O" => ActualEisensteinCubic.O
def sourceSecondZero (S : Finset (Ideal O)) (β : Ideal O→ℂ) (η : AngularCharacter) (t : ℝ) : ℂ :=
  secondZeroEnergy Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
    (fun I => β I*heightCoeff η t I)

lemma heightCoeff_norm_le_one (η : AngularCharacter) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoeff η t I‖≤1 := by
  have hn : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp : ‖(Ideal.absNorm I:ℂ)^(Complex.I*t)‖=1 := by
    rw [show (Ideal.absNorm I:ℂ)=((Ideal.absNorm I:ℝ):ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn]
    simp
  rw [heightCoeff,norm_mul,hp,mul_one]
  exact η.norm_idealHom_le_one I

theorem sourceSecondZero_divisor_bound (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : AngularCharacter) (t B Y : ℝ) (hB : 0≤B) (hY : 0≤Y)
    (s : Ideal O) (hs : s≠0)
    (hc : ∀ I∈supportedColumns S,β I≠0→‖β I‖≤B)
    (hdiv : ∀ I∈supportedColumns S,β I≠0→s∣I)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤Y) :
    ‖sourceSecondZero S β η t‖≤128*B^2*Y/(Ideal.absNorm s:ℝ) := by
  let Q : Finset (supportedColumns S) := Finset.univ.filter (fun I => β I≠0)
  rw [sourceSecondZero,secondZeroEnergy_filter Finset.univ (sourceGenerator S)
    (sourceGenerator_supported S) (fun I => β I*heightCoeff η t I) (fun I => β I≠0)
      (by intro I _ h; simp only [not_not] at h; rw [h,zero_mul])]
  refine secondZeroEnergy_divisor_bound Q (sourceGenerator S) (sourceGenerator_supported S)
    (sourceGenerator_primary S) (sourceGenerator_injective S).injOn _ B hB ?_ s hs ?_ Y hY ?_
  · intro I hI
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (heightCoeff_norm_le_one η t I
      (Finset.mem_filter.mp I.property).2.1) (norm_nonneg _)).trans
      (by simpa only [mul_one] using hc I I.property (Finset.mem_filter.mp hI).2)
  · intro I hI
    rw [sourceGenerator_span]
    exact hdiv I I.property (Finset.mem_filter.mp hI).2
  · intro I hI
    rw [sourceGenerator_span]
    exact hN I I.property (Finset.mem_filter.mp hI).2

theorem sourceSecondZero_eq_zero_of_subunit (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (η : AngularCharacter) (t Y : ℝ) (hY : Y<1)
    (hN : ∀ I∈supportedColumns S,β I≠0→(Ideal.absNorm I:ℝ)≤Y) :
    sourceSecondZero S β η t=0 := by
  have hc (I : supportedColumns S) : β I=0 := by
    by_contra hn
    have hi : (1:ℝ)≤Ideal.absNorm (I:Ideal O) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.mem_filter.mp I.property).2.1)
    linarith [hN I I.property hn]
  simp only [sourceSecondZero,secondZeroEnergy,hc,zero_mul,star_zero,mul_zero,Finset.sum_const_zero]

end OAI.SevenEighths.Angular.PlainRows.SecondSource

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.heightCoeff_norm_le_one
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.heightCoeff_norm_le_one

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.sourceSecondZero_divisor_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.sourceSecondZero_divisor_bound

#print axioms OAI.SevenEighths.Angular.PlainRows.SecondSource.sourceSecondZero_eq_zero_of_subunit
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.SecondSource.sourceSecondZero_eq_zero_of_subunit
