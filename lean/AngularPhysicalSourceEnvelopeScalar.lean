import AngularPhysicalSecondEnvelope

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.SourceCapacity
open PlainRows PhysicalBlock SecondFamily
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization CenteredMomentSecondRadicalBudget
open CenteredMomentSourceDyadicShell CenteredMomentHeckeColumnWindow
open CenteredMomentSecondPhysicalCost CenteredMomentSupport ConcretePrimeRowBridge CenteredMomentSourceRow
open CenteredMomentSecondSectorColumns (sectorPool)
open CenteredMomentSecondNonexceptionalScalar (scalar_cancel)
open CenteredMomentSecondPhysicalLedger (common_product_pos)
open CenteredMomentSecondCapacitySourceShift (scalar_capacity_shift adjustedEnvelopeRef)
local notation "O" => ActualEisensteinCubic.O
open CenteredMomentSecondPhysicalBlock (outerScalar)
theorem actual_envelope_scalar (η:AngularCharacter)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(_hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    (fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) := by
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hu:0<((∏P∈U,P.val).absNorm:ℝ):=by
    rw [map_prod,Nat.cast_prod]
    apply Finset.prod_pos
    intro P hP
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (by rw [←commonPrime_span C D hC P]; exact (commonPrime_supported C D hC P).1))
  have hn (i:Fin 4):0<dyadicScale (n i):=dyadicScale_pos _
  let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
  have hr:0<r:=div_pos (mul_pos (hn 0) (hn 1)) (mul_pos (hn 2) (hn 3))
  have hscale := (physical_effective_scale η t S β C D hC hD U R rows W K n hne).le
  have he : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K=
      K*(Ideal.span {commonFrequencyGenerator C D}).absNorm*
        (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm/((C.absNorm:ℝ)*D.absNorm) := by
    rw [secondEffectiveScale,←normValue_eq_embedding,normValue_mul]
    dsimp only [normValue]
    ring
  have hrat : secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))≤r := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hscale (dyadicScale_pos _).le) (mul_pos (hn 2) (hn 3)).le
  have hfrac : (secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
      dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)≤1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  rw [outerScalar,normalizer,actual_partitionNormalizer C D hC]
  change _≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))
  rw [childEnvelope,scalar_cancel _ _ _ _ _ _ _ _ _ r _ hc hd
    (dyadicScale_pos _) (dyadicScale_pos _) hu hr.le]
  rw [←he]
  calc
    _=((fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)))*
      ((secondEffectiveScale C D (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) K*
        dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))/(1+r)):=by ring
    _≤_:=by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfrac
        (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm*Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3)) by positivity)

theorem actual_residual_sqrt_cap (η:AngularCharacter)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    Real.sqrt (dyadicScale (n 2)*dyadicScale (n 3))≤
      4*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm) := by
  obtain ⟨I,J,hI,hJ,hwi,hwj⟩:=physicalBlock_column_witnesses η t S β C D hC hD U R rows W K n hne
  have hH:0≤Hsource:=(Nat.cast_nonneg ((C*(I:Ideal O)).absNorm)).trans (hsource _ hI)
  have hc:0<(C.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)
  have hd:0<(D.absNorm:ℝ):=by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)
  have hx:dyadicScale (n 2)≤4*Hsource/(C.absNorm:ℝ):=
    (residual_window_bounds C I hC.1 0 Hsource (n 2) (Nat.cast_nonneg _) (hsource _ hI) hwi).2
  have hy:dyadicScale (n 3)≤4*Hsource/(D.absNorm:ℝ):=
    (residual_window_bounds D J hD.1 0 Hsource (n 3) (Nat.cast_nonneg _) (hsource _ hJ) hwj).2
  have hh:=Real.sqrt_le_sqrt (mul_le_mul hx hy (dyadicScale_pos _).le (by positivity))
  have he:(4*Hsource/(C.absNorm:ℝ))*(4*Hsource/(D.absNorm:ℝ))=
      (4*Hsource)^2/((C.absNorm:ℝ)*D.absNorm):=by ring
  rw [he,Real.sqrt_div (sq_nonneg _),Real.sqrt_sq (by positivity)] at hh
  exact hh

theorem actual_source_envelope_scalar (η:AngularCharacter)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    (outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))≤
    4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm) := by
  apply (actual_envelope_scalar η t S β C D hC hD U R rows W K hK n hne).trans
  have hh:=mul_le_mul_of_nonneg_left
    (actual_residual_sqrt_cap η t S β C D hC hD U R rows W K n Hsource hsource hne)
    (show 0≤(fixedFactor:ℝ)*η.modulus.absNorm by positivity)
  convert hh using 1 ; ring

theorem actual_source_envelope_scalar_extra (η:AngularCharacter)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(U:Finset (CommonIndex C D))
    (R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (Hsource:ℝ)(hsource:∀I,β I≠0→(I.absNorm:ℝ)≤Hsource)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)
    (Eextra:ℝ)(hEextra:0≤Eextra) :
    ((outerScalar C D K n*normalizer C D U)/Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*
      childEnvelope η C D U n/
      (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))))*Eextra≤
    (4*(fixedFactor:ℝ)*η.modulus.absNorm*Hsource/Real.sqrt ((C.absNorm:ℝ)*D.absNorm))*Eextra :=
  mul_le_mul_of_nonneg_right
    (actual_source_envelope_scalar η t S β C D hC hD U R rows W K hK n Hsource hsource hne) hEextra
end OAI.SevenEighths.Angular.SourceCapacity

#print axioms OAI.SevenEighths.Angular.SourceCapacity.actual_envelope_scalar
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SourceCapacity.actual_envelope_scalar

#print axioms OAI.SevenEighths.Angular.SourceCapacity.actual_residual_sqrt_cap
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SourceCapacity.actual_residual_sqrt_cap

#print axioms OAI.SevenEighths.Angular.SourceCapacity.actual_source_envelope_scalar
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SourceCapacity.actual_source_envelope_scalar

#print axioms OAI.SevenEighths.Angular.SourceCapacity.actual_source_envelope_scalar_extra
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SourceCapacity.actual_source_envelope_scalar_extra
