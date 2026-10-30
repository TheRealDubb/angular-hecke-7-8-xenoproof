import AngularPhysicalFirstWindow

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.PlainRows.FirstPhysical
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum
open FourierBridge
open CenteredMomentFirstPhysicalSource (allocatedData columns element element_supported element_span
  column_supported columns_gauss_polynomial_filter generator_span element_norm)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

local instance angularFirstWindowColumnsDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem column_window_common (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:AngularCharacter)(t θ X:ℝ)(V:ℝ→ℂ)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) z=
        commonWindow s C hC τ t θ X V L z:=by
  simp only [ha,element_norm]
  rw [columns_gauss_polynomial_filter Q C hC s.columns
    (fun I=>(if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I*
      columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ) z]
  unfold commonWindow
  congr 1
  funext I
  rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]

theorem column_window_original_integral (s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:s.s∣C)(τ:AngularCharacter)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) z=
      ∫w:ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        allocatedPolynomial s C L τ (t+2*Real.pi*(w-θ)) T z:=by
  rw [column_window_common s Q C hQ hC hQC τ t θ X V L a ha z]
  exact common_window_original_integral s hS hp C hC hseed τ t T θ X hX V hVc hVs L z

theorem column_star_window_original_integral (s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:s.s∣C)(τ:AngularCharacter)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=>a I*star (columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ)) (-z)=
      ∫w:ℝ,columnDensity (fun x=>star (V x)) (conjugate_compact V hVc)
        (conjugate_smooth V hVs) w*logPhase (-θ-w) (Real.log X)*
        allocatedPolynomial s C L τ (t+2*Real.pi*(w-(-θ))) T (-z):=by
  simp only [star_columnPhase]
  exact column_window_original_integral s hS hp Q C hQ hC hQC hseed τ t T (-θ) X hX
    (fun x=>star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) L a ha (-z)

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.column_window_common
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.column_window_common

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.column_window_original_integral
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.column_window_original_integral

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.column_star_window_original_integral
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.column_star_window_original_integral
