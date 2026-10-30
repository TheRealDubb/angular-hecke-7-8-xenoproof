import AngularPhysicalNaturalReferenceLowReflection
import AngularPhysicalRelativeSlotCoefficients
import OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneousError
noncomputable section
set_option maxHeartbeats 400000
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.NaturalReference
open Dyadic ConcreteTraceCRT QuadraticInitialBound EnergyState ReferenceState EnergyBands
open ConcretePrimeRowBridge
open NaturalRows CommonMask InductionEnergy RelativePrime
open EnergyAllocatedChildren
open CenteredMomentCommonMaskEnergy (heightCoefficient)
open CenteredMomentEnergyReferenceState (effectiveRadial)
open CenteredMomentOriginalRadialComparison (radialEnergy)
open CenteredMomentEnergyBands (length length_nonneg)
open CenteredMomentEnergyReferenceChild (independentProfiles)
open CenteredMomentEnergyReferenceChildProfiles (reflectionProfiles)
open CenteredMomentEnergyProfiles CenteredMomentFiniteProfileExceptional
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentLattice CenteredMomentRetainedProfile CenteredMomentTwist
open CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot (primePool)
local notation "O" => ActualEisensteinCubic.O
variable {angularOrder:ℕ}
open Filter
open CenteredMomentNaturalRowSource (fixedConductorFactor)
open CenteredMomentOriginalReflectionErrorMass
  (annularWeight_zero_norm normalized_linear_bound errorConstant errorConstant_pos)
open CenteredMomentCounting CenteredMomentAbsoluteEnergy
open CenteredMomentOriginalRadialComparison
open CenteredMomentCommonMaskEnergy (heightCoefficient_norm)
open HeckePrimeAnnular
open CenteredMomentComparisonReflection (inverse_half_power)
open CenteredMomentNaturalFixedRaySource (radialEnergy_le_absolute_mass)
lemma actual_coefficient_norm (χ : AngularCharacter) (W : ℝ→ℂ) (D freq B : ℝ)
    (hD : 0<D) (hB : 0≤B) (hW : ∀x,‖W x‖≤B) (I : Ideal O) :
    ‖χ.idealHom I*annularWeight W D 0 freq I‖≤B := by
  by_cases hI:I=0
  · subst I
    simpa only [map_zero,zero_mul,norm_zero] using hB
  rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
  exact (mul_le_mul (χ.norm_idealHom_le_one I) (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)

lemma actual_coefficient_support (χ : AngularCharacter) (W : ℝ→ℂ) (b D freq : ℝ)
    (hD : 0<D) (hs : Function.support W⊆Set.Iic b) (I : Ideal O)
    (hne : χ.idealHom I*annularWeight W D 0 freq I≠0) :
    (I.absNorm:ℝ)≤max 1 b*D := by
  have hw : W ((I.absNorm:ℝ)/D)≠0:=by
    intro hz
    exact hne (by simp only [annularWeight,hz,zero_mul,mul_zero])
  exact ((div_le_iff₀ hD).mp (hs hw)).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le)

lemma polynomial_all_ideals (χ : AngularCharacter) (W : ℝ→ℂ) (D freq : ℝ) :
    polynomial χ false W D 0 freq=
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal O,χ.idealHom I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he:(∑'I:NonzeroIdeal,χ.idealHom I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal O,χ.idealHom I*annularWeight W D 0 freq I:=by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal O|I≠0})
      (f:=fun I:Ideal O=>χ.idealHom I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [map_zero,zero_mul])
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,Dyadic.norm,
    annularWeight,Dyadic.shift,HeckeDyadic.shift,mul_assoc] using he

theorem plain_polynomial_bound (χ : AngularCharacter) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ false W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>χ.idealHom I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      change χ.idealHom (0:Ideal O)*_ = 0
      rw [map_zero,zero_mul])
    (actual_coefficient_norm χ W D freq B hD hB hW)
    (actual_coefficient_support χ W b D freq hD hs)
  convert hh using 1; ring

theorem naturalSlot_ideal_bound (χ : AngularCharacter) (pool : Finset (Ideal O))
    (β : Ideal O→ℂ) (b M P : ℝ) (hM : 0≤M) (hP : 0<P)
    (hβ : ∀I∈pool,‖β I‖≤M)
    (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    ‖naturalSlot χ pool β P‖≤(128*max 1 b*M)*Real.sqrt P := by
  let f : Ideal O→ℂ:=fun I=>if I∈pool then χ.idealHom I*β I else 0
  have hf0 : f 0=0:=by simp only [f,map_zero,zero_mul,ite_self]
  have hf : ∀I,‖f I‖≤M := by
    intro I
    by_cases hi : I∈pool
    · simp only [f,ite_eq_left hi,norm_mul]
      exact (mul_le_mul (χ.norm_idealHom_le_one I) (hβ I hi) (norm_nonneg _) zero_le_one).trans_eq (one_mul M)
    · simpa only [f,ite_eq_right hi,norm_zero] using hM
  have hsup : ∀I,f I≠0 → (I.absNorm:ℝ)≤max 1 b*P := by
    intro I hi
    have hm : I∈pool:=by by_contra hn;exact hi (by simp only [f,ite_eq_right hn])
    have hb : β I≠0:=by intro hz;exact hi (by simp only [f,ite_eq_left hm,hz,mul_zero])
    exact (hs I hm hb).trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hP.le)
  have he : (∑'I:Ideal O,f I)=∑I∈pool,χ.idealHom I*β I := by
    rw [tsum_eq_sum (s:=pool) (fun I hi=>by simp only [f,ite_eq_right hi])]
    exact Finset.sum_congr rfl (fun I hi=>by simp only [f,ite_eq_left hi])
  have hh:=norm_tsum_ideal_ball f (max 1 b*P) M (by positivity) hM hf0 hf hsup
  rw [he] at hh
  unfold naturalSlot
  rw [←inverse_half_power P hP.le]
  apply normalized_linear_bound P _ hP
  convert hh using 1 ; ring

theorem natural_remaining_homogeneous_bound {α : Type*} (F T : Finset α) (hT : T⊆F)
    (W : ℝ→ℂ) (bshort Bshort : ℝ) (b M : α→ℝ)
    (hBshort : 0≤Bshort) (hM : ∀j∈F,0≤M j)
    (hW : ∀x,‖W x‖≤Bshort) (hsW : Function.support W⊆Set.Iic bshort)
    (χ : AngularCharacter) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ)
    (P : α→ℝ) (X omega : ℝ) (hX : 0<X) (hP : ∀j∈T,0<P j)
    (hβ : ∀j∈T,∀I∈pool j,‖β j I‖≤M j)
    (hs : ∀j∈T,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) :
    ‖polynomial χ false W X 0 omega*∏j∈T,naturalSlot χ (pool j) (β j) (P j)‖^2≤
      errorConstant F bshort 1 b M*Bshort^2*X*∏j∈T,P j := by
  have hshort:=pow_le_pow_left₀ (norm_nonneg _)
    (plain_polynomial_bound χ W bshort Bshort X omega hBshort hX hW hsW) 2
  rw [mul_pow,Real.sq_sqrt hX.le] at hshort
  have hj (j:α) (hj:j∈T):
      ‖naturalSlot χ (pool j) (β j) (P j)‖^2≤(128*max 1 (b j)*M j)^2*P j := by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (naturalSlot_ideal_bound χ (pool j) (β j) (b j) (M j) (P j)
        (hM j (hT hj)) (hP j hj) (hβ j hj) (hs j hj)) 2
    simpa only [mul_pow,Real.sq_sqrt (hP j hj).le] using hh
  have hc₀ : (128*max 1 bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort 1 b M := by
    have hp : (∏j∈T,(128*max 1 (b j)*M j)^2)≤∏j∈F,max 1 ((128*max 1 (b j)*M j)^2) :=
      (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) (fun j _=>le_max_right 1 _)).trans
        (Finset.prod_le_prod_of_subset_of_one_le₀ hT (fun j _=>by positivity)
          (fun j _ _=>le_max_left 1 _))
    unfold errorConstant
    simp only [mul_one]
    exact mul_le_mul (by linarith [sq_nonneg (128*max 1 bshort)]) hp
      (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
  have hc : (128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2)≤
      errorConstant F bshort 1 b M*Bshort^2 := by
    calc
      _=((128*max 1 bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*Bshort^2:=by ring
      _≤_:=mul_le_mul_of_nonneg_right hc₀ (sq_nonneg Bshort)
  calc
    _ = ‖polynomial χ false W X 0 omega‖^2*∏j∈T,‖naturalSlot χ (pool j) (β j) (P j)‖^2 := by
      simp only [norm_mul,mul_pow,norm_prod,Finset.prod_pow]
    _ ≤ ((128*max 1 bshort*Bshort)^2*X)*∏j∈T,(128*max 1 (b j)*M j)^2*P j :=
      mul_le_mul hshort (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) hj)
        (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
    _ = ((128*max 1 bshort*Bshort)^2*(∏j∈T,(128*max 1 (b j)*M j)^2))*(X*∏j∈T,P j) := by
      rw [Finset.prod_mul_distrib];ring
    _ ≤ (errorConstant F bshort 1 b M*Bshort^2)*(X*∏j∈T,P j) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hX.le (Finset.prod_nonneg (fun j hj=>(hP j hj).le)))
    _ = _ := by ring

theorem natural_reference_error_homogeneous {α:Type*}(F:Finset α)(bshort:ℝ)(b M:α→ℝ)
    (hM:∀i∈F,0≤M i):
    ∃C:ℝ,0<C ∧ ∀(T:Finset α),T⊆F → ∀W:𝓢(ℝ,ℂ),
      Function.support (W:ℝ→ℂ)⊆Set.Iic bshort →
      ∀(χ:O→AngularCharacter)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
        (t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),
      0<X → 0<K → (∀i∈T,0<P i) →
      (∀i∈T,∀I∈pool i,Prime I) →
      (∀i∈T,∀I∈pool i,‖β i I‖≤M i) →
      (∀i∈T,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) →
      (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t *
        ∏i∈T,naturalSlot (χ z) (pool i) (heightCoefficient (β i) t) (P i)) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl Φ*max 1 K*X*∏i∈T,P i:=by
  refine ⟨errorConstant F bshort 1 b M,errorConstant_pos _ _ _ _ _,?_⟩
  intro T hT W hsW χ pool β P t X K Φ keep hX hK hP hp hβ hs hΦ
  let A:=(schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W
  have hA:0≤A:=apply_nonneg _ _
  have hWA:∀x,‖W x‖≤A:=SchwartzMap.norm_le_seminorm ℝ W
  let R:=fun z:O=>polynomial (χ z) false W X 0 t *
    ∏i∈T,naturalSlot (χ z) (pool i) (heightCoefficient (β i) t) (P i)
  let V:=errorConstant F bshort 1 b M*A^2*X*∏i∈T,P i
  have hV:0≤V:=by
    dsimp only [V]
    exact mul_nonneg (mul_nonneg (mul_nonneg (errorConstant_pos F bshort 1 b M).le
      (sq_nonneg A)) hX.le) (Finset.prod_nonneg (fun i hi=>(hP i hi).le))
  have hr(z:O):‖R z‖^2≤V:=by
    have hh:=natural_remaining_homogeneous_bound F T hT W bshort A b M hA hM hWA hsW
      (χ z) pool (fun i=>heightCoefficient (β i) t) P X t hX hP
      (fun i hi I hI=>by rw [heightCoefficient_norm _ _ _ (hp i hi I hI).ne_zero];exact hβ i hi I hI)
      (fun i hi I hI hn=>hs i hi I hI (left_ne_zero_of_mul hn))
    exact hh
  have hsum:Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖R z‖^2):=
    Summable.of_nonneg_of_le (fun z=>mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right V)
  apply (radialEnergy_le_absolute_mass R keep Φ K hΦ hsum).trans
  calc
    _≤∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*V:=hsum.tsum_le_tsum
      (fun z=>mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right V)
    _=(∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*V:=tsum_mul_right
    _≤(diagonalControl Φ*max 1 K)*V:=mul_le_mul_of_nonneg_right
      (radial_weight_lattice_bound_all Φ K hK) hV
    _=_:=by dsimp [V,A];ring

theorem relative_slot_error {α:Type*}(F:Finset α)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi bshort:ℝ)(ha:0<aslot)
    (hs:Function.support Wslot⊆Set.Icc aslot bslot)(hc:Continuous Wslot):
    ∃C:ℝ,0<C ∧ ∀T:Finset α,T⊆F → ∀W:𝓢(ℝ,ℂ),
      Function.support (W:ℝ→ℂ)⊆Set.Iic bshort →
      ∀(χ:O→AngularCharacter)(ν:α→AngularCharacter)(pool:α→Finset (Ideal O))
        (P σ freq:α→ℝ)(t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),
      0<X → 0<K → (∀i∈T,0<P i) → (∀i∈T,lo≤σ i) → (∀i∈T,σ i≤hi) →
      (∀i∈T,∀I∈pool i,Prime I) → (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t *
        ∏i∈T,naturalSlot (χ z) (pool i)
          (heightCoefficient (fun I=>(ν i).idealHom I*
            HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I) t) (P i)) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl Φ*max 1 K*X*∏i∈T,P i:=by
  obtain ⟨B,hB,hslot⟩:=RelativeFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi ha hs hc
  obtain ⟨C,hC,he⟩:=natural_reference_error_homogeneous F bshort
    (fun _=>bslot) (fun _=>B) (fun _ _=>hB.le)
  refine ⟨C,hC,?_⟩
  intro T hT W hW χ ν pool P σ freq t X K Φ keep hX hK hP hlo hhi hp hΦ
  apply he T hT W hW χ pool
    (fun i I=>(ν i).idealHom I*HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I)
    P t X K Φ keep hX hK hP hp
  · intro i hi I hI
    have hb:=(hslot (ν i) (P i) (σ i) (freq i) 0 (hP i hi) (hlo i hi) (hhi i hi)
      I (hp i hi I hI).ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hb
  · intro i hi I hI hn
    have hb:=(hslot (ν i) (P i) (σ i) (freq i) 0 (hP i hi) (hlo i hi) (hhi i hi)
      I (hp i hi I hI).ne_zero).2
    apply hb
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hΦ


end OAI.SevenEighths.Angular.NaturalReference

#print axioms OAI.SevenEighths.Angular.NaturalReference.actual_coefficient_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.actual_coefficient_norm

#print axioms OAI.SevenEighths.Angular.NaturalReference.actual_coefficient_support
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.actual_coefficient_support

#print axioms OAI.SevenEighths.Angular.NaturalReference.polynomial_all_ideals
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.polynomial_all_ideals

#print axioms OAI.SevenEighths.Angular.NaturalReference.plain_polynomial_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.plain_polynomial_bound

#print axioms OAI.SevenEighths.Angular.NaturalReference.naturalSlot_ideal_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.naturalSlot_ideal_bound

#print axioms OAI.SevenEighths.Angular.NaturalReference.natural_remaining_homogeneous_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.natural_remaining_homogeneous_bound

#print axioms OAI.SevenEighths.Angular.NaturalReference.natural_reference_error_homogeneous
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.natural_reference_error_homogeneous

#print axioms OAI.SevenEighths.Angular.NaturalReference.relative_slot_error
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.relative_slot_error
