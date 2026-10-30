import AngularPhysicalExcludedPair
import AngularPhysicalNaturalRow
import AngularPhysicalPlainZeroEnergy
import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalControl

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.NaturalRows
open OAI.SevenEighths.Angular.Dyadic PlainZeroEnergy
open InverseAmplification (polynomial_twistProfile)
open HeckeInverseAmplification (twistProfile)
open CenteredMomentNaturalRowSource (fixedConductorFactor)
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero)
open ExceptionalRows (FixedInducingRow)
open CenteredMomentLattice CenteredMomentTwist QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentOriginalRadialComparison (radialEnergy)
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => ActualEisensteinCubic.O

lemma twist_polynomial (χ : AngularCharacter) (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support (W:ℝ→ℂ)⊆Set.Icc a b) (t X : ℝ) :
    polynomial χ false (normPowerProfile W a b ha hs (W.smooth ⊤) t) X 0 0 =
      polynomial χ false W X 0 t := by
  have hp : (normPowerProfile W a b ha hs (W.smooth ⊤) t:ℝ→ℂ)=twistProfile W 0 t := by
    funext x
    rw [normPowerProfile_apply]
    unfold twistProfile HeckeDyadic.shift
    simp only [Complex.ofReal_zero,zero_sub,neg_neg]
    rw [mul_comm Complex.I (t:ℂ)]
    ring
  rw [hp,polynomial_twistProfile]

theorem natural_masked_floor (angularOrder:ℕ) (a b ε : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃ n : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0<C ∧
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀ (η : AngularCharacter) (Q R : Ideal O) (r : Radial) (bΦ : ℝ), η.k.natAbs=angularOrder → R≠0 → 0≤bΦ →
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η Q (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
    ∀ (Z m q ρ t X₁ X₂ : ℝ), 1≤Z → 0≤m → 0≤q → r.scale=Z^m →
      m+q≤ρ → 0<X₁ → 0<X₂ → (η.modulus.absNorm:ℝ)≤Z^q →
    zeroEnergy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂ X₁ X₂ r ≤
      C*(R.radical.absNorm:ℝ)^ε*bΦ^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(1+‖t‖)^n*Z^(m+q+4*ρ) := by
  obtain ⟨S,C,hC,hpair⟩ := CommonMask.excluded_pair angularOrder a b ε ha hb hε
  obtain ⟨n,T,Ct,hCt,ht⟩ :=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a b ha S
  let F : ℝ := fixedConductorFactor
  have hF : 0<F := by
    unfold F fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨4*n,T,C*Ct^4*F^4,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ η Q R r bΦ horder hR hbΦ hsΦ hz hex Z m q ρ t X₁ X₂ hZ hm hq hscale hρ hX₁ hX₂ hη
  let r' : Radial := {r with keep := fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  let χ : O→AngularCharacter := fun z=>if hz:z≠0 then (naturalRow η z hz).character else η
  have hχ (z:O) (h:r'.keep z) : (χ z).k≠0 ∨ (χ z).residue≠1 := by
    have hn := hz z h.1
    have hc : χ z=(naturalRow η z hn).character := by simp [χ,hn]
    exact (congrArg (fun ψ : AngularCharacter=>ψ.k≠0 ∨ ψ.residue≠1) hc).mpr
      ((naturalRow η z hn).nonprincipal hn Q R hR (hex z h.1))
  have hχorder (z:O) (h:r'.keep z) : (χ z).k.natAbs=angularOrder := by
    have hn := hz z h.1
    simpa only [χ,dite_eq_left hn,(naturalRow η z hn).angular_type] using horder
  have hmod (z:O) (h:r'.keep z) : ((χ z).modulus.absNorm:ℝ)≤F*bΦ*Z^(m+q) := by
    have hn := hz z h.1
    have hh : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m := by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←hscale]
      exact (div_le_iff₀ r.scale_pos).mp (hsΦ h.2)
    simpa only [χ,dite_eq_left hn,add_comm q m] using
      (naturalRow η z hn).modulus_power_bound Z q m bΦ (zero_lt_one.trans_le hZ) hbΦ hη hh
  let V₁ := normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t
  let V₂ := normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t
  have hv₁ : Function.support (V₁:ℝ→ℂ)⊆Set.Icc a b := (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t).trans hs₁
  have hv₂ : Function.support (V₂:ℝ→ℂ)⊆Set.Icc a b := (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t).trans hs₂
  have he := hpair V₁ V₂ hv₁ hv₂ χ r' R (F*bΦ*Z^(m+q)) X₁ X₂ hR
    (by positivity) hX₁ hX₂ hχorder hχ hmod
  have hid : zeroEnergy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂ X₁ X₂ r =
      radialEnergy (fun z=>polynomial (excluded (χ z) R) false V₁ X₁ 0 0 *
        polynomial (excluded (χ z) R) false V₂ X₂ 0 0) r'.keep r'.profile r'.scale := by
    unfold zeroEnergy radialEnergy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · by_cases hp : r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · have hn := hz z hk
        simp only [r',hk,true_and,ite_true]
        rw [zero_row_norm η (excluded (χ z) R) _ 1 z
          (by simpa only [χ,dite_eq_left hn,one_mul] using (naturalRow η z hn).masked_element R hR)
          W₁ W₂ a b ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤) t X₁ X₂ hX₁ hX₂]
        rw [norm_mul,twist_polynomial,twist_polynomial]
        split_ifs with h
        · rfl
        · exact False.elim (h hp)
    · simp [r',hk]
  rw [←hid] at he
  have hB₁ := ht W₁ hs₁ t
  have hB₂ := ht W₂ hs₂ t
  have hprod : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₁ * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₂)^2 ≤
      (Ct^4*(T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n) := by
    have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_le_mul hB₁ hB₂ (apply_nonneg _ _) (by positivity)) 2
    exact hh.trans_eq (by dsimp [V₁,V₂]; rw [Nat.mul_comm 4 n,pow_mul]; ring)
  have hp : Z^m*(Z^(m+q))^4≤Z^(m+q+4*ρ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hZ),←Real.rpow_add (zero_lt_one.trans_le hZ)]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  have hd := diagonalControl_nonneg r.profile
  dsimp only [r'] at he
  rw [hscale,max_eq_right (Real.one_le_rpow hZ hm)] at he
  apply he.trans
  calc
    _ ≤ C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*Z^m*
      ((Ct^4*(T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n))*(F*bΦ*Z^(m+q))^4 := by
        gcongr
    _ = (C*Ct^4*F^4*(R.radical.absNorm:ℝ)^ε*bΦ^4*diagonalControl r.profile*
      (T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*T.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2*(1+‖t‖)^(4*n))*(Z^m*(Z^(m+q))^4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)


end OAI.SevenEighths.Angular.NaturalRows

#print axioms OAI.SevenEighths.Angular.NaturalRows.natural_masked_floor
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalRows.natural_masked_floor
