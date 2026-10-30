import AngularPhysicalExceptionalRowsPair

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace OAI.SevenEighths.Angular.SecondExceptionalKernel
open PlainRows ChildRows ExceptionalRows
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSupport CenteredMomentRestrictedEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentSmooth CenteredMomentSupportedCorrelation CenteredMomentMobiusRegroup
open CenteredMomentSecondExceptionalKernel (whole_kernel_actual_second_pair)
local notation "O" => ActualEisensteinCubic.O
theorem actual_exceptional_block_bound (W:𝓢(ℝ,ℂ))(decay J:ℕ):
    ∃B:ℝ,0≤B ∧ ∀r:ℝ,0<r →
      ∀(η:AngularCharacter)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
        (C D:Ideal O)(hC:Supported C)(hD:Supported D),
      primeSupport C=primeSupport D →
      ∀(U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)
        (ρ x:O→ℝ)(u:sectorPool C hC.1 S→ℝ)(v:sectorPool D hD.1 S→ℝ)
        (Q:Ideal O)(m:O)(χ₀:RayCharacter),
      Q≤Ideal.span {(72:O)} → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let c:=fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I
      let d:=fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I
      (∀z∈rows,FixedInducingRow (childCharacter η χ₀) Q m A z) →
      ∀E:ℝ,0≤E →
      (∀χ ξ:RayCharacter,
        (∀z∈rows,FixedInducingRow (childCharacter η χ) Q m A z) →
        (∀z∈rows,FixedInducingRow (childCharacter η (ξ⁻¹)) Q m A (-z)) →
        ∀w:ℝ,
        (∑L∈divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O)),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
          ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
            (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
              (movingCoefficient A (sectorElement C hC.1 S) c) χ I*columnPhase logAnnulus (u I) w) z‖*
          ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
            (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
              (movingCoefficient A (sectorElement D hD.1 S) d) (ξ⁻¹) I*star (columnPhase logAnnulus (v I) w)) (-z)‖)
          ≤E*(1+‖w‖)^J) →
      (1+r)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            (c I*star (d J))*wholeKernel W (fun _=>logAnnulus) r (ρ z) (x z) (u I) (v J)‖≤B*E:=by
  obtain ⟨B,hB,hbound⟩:=whole_kernel_actual_second_pair W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num))
    (fun _ x hx=>CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure x hx) decay J
  refine ⟨B,hB,?_⟩
  intro r hr η t S β C D hC hD hCD U R rows ρ x u v Q m χ₀ hQ hmLam hm2
  dsimp only
  intro hrows E hE hpair
  have hcopD (I:sectorPool D hD.1 S):
      IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement D hD.1 S I):=by
    simpa only [mul_comm] using sectorElement_coprime D C hD hC hCD.symm S I
  have he:=hbound r hr rows Finset.univ Finset.univ (primaryGenerator C) (primaryGenerator D)
    (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
    (sectorElement C hC.1 S) (sectorElement D hD.1 S)
    ((supported_span_primaryGenerator_iff C).mpr hC) ((supported_span_primaryGenerator_iff D).mpr hD)
    (sectorElement_supported C hC.1 S) (sectorElement_supported D hD.1 S)
    (primaryGenerator_spec C (supported_primaryGenerator_ne_zero C hC)).2
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).2
    (sectorElement_primary C hC.1 S) (sectorElement_primary D hD.1 S)
    (sectorElement_coprime C D hC hD hCD S) hcopD
    (retainedScalar C D U R) (fun I=>β (C*I)*heightCoeff η t I)
    (fun I=>β (D*I)*heightCoeff η t I) u v ρ x
    (fun z _=>actual_retained_scalar_norm C D hC hD hCD U R z)
    (fun z _=>logAnnulus_norm _) (fun z _=>logAnnulus_norm _) E hE
  have hh:∀χ ξ:RayCharacter,∀w:ℝ,
      (∑L∈divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O)),
        ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*∑z∈rows,
        ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
          (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
            (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
              (sectorElement C hC.1 S) (fun I=>β (C*I)*heightCoeff η t I)) χ I*columnPhase logAnnulus (u I) w) z‖*
        ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
          (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
            (movingCoefficient (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)
              (sectorElement D hD.1 S) (fun I=>β (D*I)*heightCoeff η t I)) (ξ⁻¹) I*
              star (columnPhase logAnnulus (v I) w)) (-z)‖)≤E*(1+‖w‖)^J:=by
    intro χ ξ w
    have hg:=exceptional_rows_pair η χ₀ χ ξ Q hQ m _ hmLam hm2 rows hrows
    exact hpair χ ξ hg.1 hg.2 w
  have he':=he (by simpa only [sectorElement_span] using hh)
  have hcop (I:sectorPool C hC.1 S)(J:sectorPool D hD.1 S):
      IsCoprime (sectorElement C hC.1 S I) (sectorElement D hD.1 S J) ↔
        IsCoprime (I:Ideal O) (J:Ideal O):=by
    rw [←Ideal.isCoprime_span_singleton_iff,sectorElement_span,sectorElement_span]
  have hcop' (I:sectorPool C hC.1 S)(J:sectorPool D hD.1 S):
      IsCoprime (primaryGenerator (I:Ideal O)) (primaryGenerator (J:Ideal O)) ↔
        IsCoprime (I:Ideal O) (J:Ideal O):=hcop I J
  simpa only [sectorElement_span,idealCorrelation,primaryGenerator_mul,sectorElement,hcop'] using he'

end OAI.SevenEighths.Angular.SecondExceptionalKernel

#print axioms OAI.SevenEighths.Angular.SecondExceptionalKernel.actual_exceptional_block_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondExceptionalKernel.actual_exceptional_block_bound
