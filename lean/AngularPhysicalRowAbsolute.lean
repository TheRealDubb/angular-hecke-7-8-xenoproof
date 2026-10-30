import AngularPhysicalPlainSlots

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.DetectorSource
open PlainRows ExceptionalRows AngularRowClosure ConcretePrimeRowBridge
open CenteredMomentCounting CenteredMomentTwist CenteredMomentLattice
open CenteredMomentHeckeSlots (whole_product_normalization)
local notation "O" => ActualEisensteinCubic.O
theorem rowTwistedSum_absolute (η : AngularCharacter) (m A z : O) (W : ℝ→ℂ)
    (b M t X : ℝ) (hb : 0≤b) (hM : 0≤M) (hX : 0<X)
    (hs : Function.support W⊆Set.Iic b) (hW : ∀x,‖W x‖≤M) :
    ‖rowTwistedSum η m A z W t X‖≤(128*b*M)*X := by
  have hh := norm_tsum_ideal_ball
    (fun I : Ideal O => (η.idealHom I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)) (b*X) M
    (mul_nonneg hb hX.le) hM (by
      change (η.idealHom (0:Ideal O)*_)*_*_=0
      rw [map_zero,zero_mul,zero_mul,zero_mul]) (by
      intro I
      by_cases hI : I=0
      · subst I; simpa only [map_zero,zero_mul,mul_zero,norm_zero] using hM
      · rw [norm_mul]
        exact (mul_le_mul (row_twisted_coefficient_norm η m A z t I hI) (hW _)
          (norm_nonneg _) zero_le_one).trans_eq (one_mul M)) (by
      intro I hI
      exact (div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hI)))
  exact hh.trans_eq (by ring)

theorem normalized_rectangle_absolute (η : AngularCharacter) (m A z : O)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ M₁ M₂ : ℝ)
    (hb₁ : 0≤b₁) (hb₂ : 0≤b₂) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hW₁ : ∀x,‖W₁ x‖≤M₁) (hW₂ : ∀x,‖W₂ x‖≤M₂)
    (t X₁ X₂ Y₁ Y₂ T : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hpX : X₁*X₂=T) (hpY : Y₁*Y₂=T) :
    ‖(Real.sqrt T:ℂ)⁻¹ *
      (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
       rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)‖≤
      (2*(128*b₁*M₁)*(128*b₂*M₂))*Real.sqrt T := by
  have hT : 0<T := hpX ▸ mul_pos hX₁ hX₂
  have hsq : 0<Real.sqrt T := Real.sqrt_pos.2 hT
  have hprod (U V : ℝ) (hU : 0<U) (hV : 0<V) :
      ‖rowTwistedSum η m A z W₁ t U*rowTwistedSum η m A z W₂ t V‖≤
        ((128*b₁*M₁)*(128*b₂*M₂))*(U*V) := by
    rw [norm_mul]
    apply (mul_le_mul (rowTwistedSum_absolute η m A z W₁ b₁ M₁ t U hb₁ hM₁ hU hs₁ hW₁)
      (rowTwistedSum_absolute η m A z W₂ b₂ M₂ t V hb₂ hM₂ hV hs₂ hW₂)
      (norm_nonneg _) (by positivity)).trans_eq
    ring
  have hraw := (norm_sub_le
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)
    (rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)).trans
      (add_le_add (hprod X₁ X₂ hX₁ hX₂) (hprod Y₁ Y₂ hY₁ hY₂))
  rw [hpX,hpY] at hraw
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hsq.le]
  apply (mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hsq.le)).trans_eq
  have he := Real.sq_sqrt hT.le
  field_simp
  rw [he]
  ring

end OAI.SevenEighths.Angular.DetectorSource

#print axioms OAI.SevenEighths.Angular.DetectorSource.rowTwistedSum_absolute
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.DetectorSource.rowTwistedSum_absolute

#print axioms OAI.SevenEighths.Angular.DetectorSource.normalized_rectangle_absolute
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.DetectorSource.normalized_rectangle_absolute
