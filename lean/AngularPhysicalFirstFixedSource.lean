import AngularPhysicalFirstFixedDivisor
import AngularPhysicalFirstWindowCanonical

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
open CenteredMomentLogDyadic CenteredMomentSecondWindowSource CenteredMomentSecondWindowBudget
open FourierBridge CompletedGauss WindowEnergy
open CenteredMomentHeckeWindowEnergy (heightCost)
open CenteredMomentFirstPhysicalSource (allocatedData columns element element_supported element_span
  column_supported columns_gauss_polynomial_filter generator_span element_norm)
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

local instance angularFirstFixedSourceDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {η:AngularCharacter}{C D:Ideal O}{hC:Supported C}
  {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}

theorem FixedPair.left_column (F:FixedPair η C D hC E ξ₁ ξ₂)(s:OriginalData ι)(t:ℝ)(L:Ideal O)
    (I:columns C C hC.1 s.columns):
    divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta C a*
        leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C C hC.1 s.columns a)) ξ₁ I=
      (if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff F.left t I:=
  fixed_divisor_column s η F.left C _ ξ₁ F.left_height L I
    (column_supported C C hC.1 s.columns I) t

theorem FixedPair.right_column (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (s:OriginalData ι)(t:ℝ)(L:Ideal O)(I:columns C D hD.1 s.columns):
    divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η (fixedBadMask*idealGenerator s.R) 1 t s.beta D a*
        rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
            (activeExponent C D)) (element C D hD.1 s.columns a)) ξ₂ I=
      (if L∣(I:Ideal O) then s.beta (D*I) else 0)*heightCoeff F.right t I:=
  fixed_divisor_column s η F.right D _ ξ₂ F.right_height L I
    (column_supported C D hD.1 s.columns I) t

theorem FixedPair.original_data (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)(hsC:s.s∣C)(hsD:s.s∣D)
    (t T:ℝ)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*leftChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L z=
      allocatedPolynomial s C L F.left t T z ∧
    (Real.sqrt T:ℂ)⁻¹*rightChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L (-z)=
      allocatedPolynomial s D L F.right t T (-z):=by
  constructor
  · exact first_column_original_data s hS hp C hC hsC F.left t T L _ (F.left_column s t L) z
  · exact first_column_original_data_filter s hS hp C D hC.1 hD hCD hsD F.right t T L _
      (F.right_column hD s t L) (-z)

theorem FixedPair.window_integrals (F:FixedPair η C D hC E ξ₁ ξ₂)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)(hsC:s.s∣C)(hsD:s.s∣D)
    (t T θ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁:ℝ→ℂ)(hV₁c:HasCompactSupport V₁)(hV₁s:ContDiff ℝ ∞ V₁)
    (V₂:ℝ→ℂ)(hV₂c:HasCompactSupport V₂)(hV₂s:ContDiff ℝ ∞ V₂)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*leftWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC E ξ₁ L θ X V₁ z=
      (∫w:ℝ,columnDensity V₁ hV₁c hV₁s w*logPhase (θ-w) (Real.log X)*
        allocatedPolynomial s C L F.left (t+2*Real.pi*(w-θ)) T z) ∧
    (Real.sqrt T:ℂ)⁻¹*rightWindowChild s η (fixedBadMask*idealGenerator s.R) t C D hC hD E ξ₂ L θ Y V₂ (-z)=
      (∫w:ℝ,columnDensity (fun x=>star (V₂ x)) (conjugate_compact V₂ hV₂c)
        (conjugate_smooth V₂ hV₂s) w*logPhase (-θ-w) (Real.log Y)*
        allocatedPolynomial s D L F.right (t+2*Real.pi*(w-(-θ))) T (-z)):=by
  constructor
  · exact column_window_original_integral s hS hp C C hC.1 hC rfl hsC F.left t T θ X hX
      V₁ hV₁c hV₁s L _ (F.left_column s t L) z
  · exact column_star_window_original_integral s hS hp C D hC.1 hD hCD hsD F.right t T θ Y hY
      V₂ hV₂c hV₂s L _ (F.right_column hD s t L) z

end OAI.SevenEighths.Angular.PlainRows.FirstPhysical

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.left_column
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.left_column

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.right_column
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.right_column

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.original_data
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.original_data

#print axioms OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.window_integrals
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.FirstPhysical.FixedPair.window_integrals
