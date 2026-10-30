import AngularPhysicalSecondChildFamily
import AngularPhysicalSecondChildWitness

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.SecondFamily
open PlainRows ChildRows ExceptionalRows PhysicalBlock
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalLedger
open CenteredMomentSecondMovingSupport CenteredMomentSecondSixthSource
open CenteredMomentCanonicalFirst CenteredMomentPartitionNorm CenteredMomentSupport
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open CenteredMomentSecondSixthReduction (reducedNumerator sixthFactor fixed_sixth_factorization
  sixthFactor_ne_zero reducedNumerator_ne_zero)
open CenteredMomentSecondRadicalBudget (fixedFactor fixedFactor_pos)
open CenteredMomentSecondRadicalColumns (residual_sixth_coefficient_right)
open CenteredMomentSecondLiveBlock (liveRows liveRows_geometry liveRows_weight)
open CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O
open CenteredMomentSecondDyadicRowSupport
section Family
variable {η:AngularCharacter}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→AngularCharacter}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)

include h hK hne

theorem dyadic_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*(fixedFactor:ℝ)) := by
  obtain ⟨z,hzl,_,hz0,hscale⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  have hw:=(h.physical_budget t S β R rows W K hK n hne χ).2 Z hZ z hzl
  have hh:=Real.logb_le_logb_of_le hZ (dyadicScale_pos (n 1)) hscale.le
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) (normValue_pos z hz0).ne'] at hh
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*(fixedFactor:ℝ))=
      Real.logb Z (4:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul (by norm_num : (4:ℝ)≠0) (by positivity : 4*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

omit h hK hne in

theorem radial_support_bound (Φ:ℝ→ℂ)(b:ℝ)
    (hs:Function.support Φ⊆Set.Iic b)(y:O)
    (hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y≤b*dyadicScale (n 1) :=
  (div_le_iff₀ (dyadicScale_pos (n 1))).mp (hs hy)

theorem radial_radius_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hh:=dyadic_log_budget h t S β R rows W K hK n hne Z hZ χ
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*(fixedFactor:ℝ))=
      Real.logb Z b+Real.logb Z (16*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hb.ne' (by positivity : 16*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [Real.logb_mul hb.ne' (dyadicScale_pos (n 1)).ne',hf]
  linarith

theorem radial_point_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (normValue y)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hl:=Real.logb_le_logb_of_le hZ (normValue_pos y hy0)
    (radial_support_bound n Φ b hs y hy)
  have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb
  linarith

theorem declared_radial_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  exact radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb

theorem whole_radial_norm_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ))) := by
  have hτ:(0:ℝ)<(τ χ).modulus.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (τ χ).modulus_ne_bot)
  have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb
  rw [←Real.logb_mul (mul_pos hb (dyadicScale_pos (n 1))).ne' hτ.ne'] at hh
  exact (mul_le_mul_of_nonneg_right (radial_support_bound n Φ b hs y hy) hτ.le).trans
    ((Real.logb_le_iff_le_rpow hZ (mul_pos (mul_pos hb (dyadicScale_pos (n 1))) hτ)).mp hh)

end Family

end OAI.SevenEighths.Angular.SecondFamily

#print axioms OAI.SevenEighths.Angular.SecondFamily.dyadic_log_budget
#print axioms OAI.SevenEighths.Angular.SecondFamily.whole_radial_norm_budget
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.SecondFamily.whole_radial_norm_budget
