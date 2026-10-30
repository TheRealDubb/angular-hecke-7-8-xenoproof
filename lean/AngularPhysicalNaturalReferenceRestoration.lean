import AngularPhysicalNaturalReferenceLowReflection
import AngularPhysicalPositiveNormalized
import OAI.NumberTheory.DirichletL.Energy.ReferenceWeightedEnergy
import OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionBudget
noncomputable section
set_option maxHeartbeats 400000
open scoped Classical BigOperators SchwartzMap ContDiff
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
open PlainRows AllocatedNatural
open CenteredMomentNaturalRowSource (fixedConductorFactor support_prime)
open CenteredMomentCommonMaskEnergy (heightCoefficient_norm positive_height_phase_norm triple_sum)
open CenteredMomentCommonMaskExpansion (uniformMajorant uniformMajorant_nonneg)
open CenteredMomentEnergyReferenceState (radialEnergy_effective)
open CenteredMomentEnergyReferenceWeightedEnergy (radial_weighted_energy)
open RadialSummability
theorem original_positive_deletion {α : Type*} [Fintype α] [DecidableEq α]
    (η : AngularCharacter) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (hp : ∀i,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    let χ:=(naturalRow η z hz).character
    let S:=CompletedGauss.primeSupport R
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        ∑D₁∈S.powerset,∑D₂∈S.powerset,∑J∈(Finset.univ : Finset α).powerset,
          signedCoefficient χ S D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
          (Dyadic.polynomial χ false (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
            (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
           Dyadic.polynomial χ false (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
            (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
           ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)) := by
  dsimp only
  rw [original_positive_normalized (naturalRow η z hz) R hR W₁ W₂ a₁ b₁ a₂ b₂
    ha₁ ha₂ hs₁ hs₂ hW₁ hW₂ pool β P hP t X₁ X₂ hX₁ hX₂]
  congr 1
  exact simultaneous_deletion (naturalRow η z hz).character (CompletedGauss.primeSupport R)
    (support_prime R) (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
    (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₁ X₂ hX₁ hX₂ Finset.univ pool
    (fun i _=>hp i) (fun i=>heightCoefficient (β i) t) P


variable {α:Type*}[Fintype α][DecidableEq α]
def signedCommonSource {Z Bmask bΦ:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(z:O):ℂ:=
  let χ:=naturalCharacter s.character z
  let R:=CompletedGauss.primeSupport s.puncture
  ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈(Finset.univ:Finset α).powerset,
    signedCoefficient χ R D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
      (polynomial χ false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
       polynomial χ false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
       ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i))

lemma original_row_eq_signed {Z Bmask bΦ a b:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)
    (W₁ W₂:𝓢(ℝ,ℂ))(ha:0<a)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool:α→Finset (Ideal O))(hp:∀i,∀I∈pool i,Prime I)
    (β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(z:O)(hz:z≠0):
    positiveSlotRow s.character s.mask 1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        signedCommonSource s W₁ W₂ pool β P t X₁ X₂ z:=by
  have hh:=original_positive_deletion s.character z hz s.puncture s.puncture_ne_zero
    W₁ W₂ a b a b ha ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
    pool hp β P hP t X₁ X₂ hX₁ hX₂
  dsimp only at hh
  simp only [NaturalRows.twist_polynomial _ W₁ a b ha hs₁ t,
    NaturalRows.twist_polynomial _ W₂ a b ha hs₂ t] at hh
  simpa only [NaturalState.mask,signedCommonSource,naturalCharacter_eq s.character z hz] using hh

theorem original_energy_eq_signed {Z Bmask bΦ a b:ℝ}(s:NaturalState angularOrder Z Bmask bΦ)
    (W₁ W₂:𝓢(ℝ,ℂ))(ha:0<a)
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (pool:α→Finset (Ideal O))(hp:∀i,∀I∈pool i,Prime I)
    (β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
      s.radial.keep s.radial.profile s.radial.scale=
    radialEnergy (signedCommonSource s W₁ W₂ pool β P t X₁ X₂)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale:=by
  change _=radialEnergy _ (effectiveRadial s.radial).keep _ _
  rw [radialEnergy_effective]
  unfold energy radialEnergy
  apply tsum_congr
  intro z
  by_cases hz:s.radial.keep z
  · simp only [ite_eq_left hz]
    rw [original_row_eq_signed s W₁ W₂ ha hs₁ hs₂ pool hp β P hP t X₁ X₂ hX₁ hX₂
      z (s.row_ne_zero z hz),norm_mul,norm_mul,
      positive_height_phase_norm X₁ t hX₁,positive_height_phase_norm X₂ t hX₂,one_mul,one_mul]
  · simp only [ite_eq_right hz]

theorem original_energy_weighted_deletion (bslot M:α→ℝ)(hM:∀i,0≤M i)
    (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(Z Bmask bΦ a b:ℝ)(s:NaturalState angularOrder Z Bmask bΦ)
      (W₁ W₂:𝓢(ℝ,ℂ)),0<a → 0≤b →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
        (t X₁ X₂ E p:ℝ),
      (∀i,∀I∈pool i,Prime I) → (∀i,0<P i) →
      (∀i,∀I∈pool i,‖β i I‖≤M i) →
      (∀i,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤bslot i*P i) →
      0<X₁ → 0<X₂ → 0≤E → p≤1 →
      (∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
       ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
       ∀J∈(Finset.univ:Finset α).powerset,
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
          polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
          ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i)
            (heightCoefficient (β i) t) (P i))
          (effectiveState s).radial.keep s.radial.profile s.radial.scale
            ≤E*((∏I∈D₂,I).absNorm:ℝ)^p) →
      energy s.character s.mask 1 t W₁ W₂ pool β P X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤C*(s.puncture.radical.absNorm:ℝ)^ε*E:=by
  obtain ⟨C,hC,hmass⟩:=CenteredMomentEnergyReferenceDeletionBudget.weighted_uniform_mass_subpower
    (Finset.univ:Finset α) bslot M (fun i _=>hM i) (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro Z Bmask bΦ a b s W₁ W₂ ha hb hs₁ hs₂ pool β P t X₁ X₂ E p hp hP hβ hs hX₁ hX₂ hE hple hchildren
  let R:=CompletedGauss.primeSupport s.puncture
  have hR:∀I∈R,Prime I:=support_prime s.puncture
  let κ:={D:Finset (Ideal O)//D∈R.powerset}×
    {D:Finset (Ideal O)//D∈R.powerset}×{J:Finset α//J∈(Finset.univ:Finset α).powerset}
  let cf(z:O)(j:κ):=signedCoefficient (naturalCharacter s.character z) R j.1.val j.2.1.val j.2.2.val
    pool (fun i=>heightCoefficient (β i) t) P
  let f(z:O)(j:κ):=polynomial (naturalCharacter s.character z) false W₁
    (X₁/((∏I∈j.1.val,I).absNorm:ℝ)) 0 t *
    polynomial (naturalCharacter s.character z) false W₂
    (X₂/((∏I∈j.2.1.val,I).absNorm:ℝ)) 0 t *
    ∏i∈Finset.univ\j.2.2.val,naturalSlot (naturalCharacter s.character z) (pool i)
      (heightCoefficient (β i) t) (P i)
  let ρ(j:κ):=uniformMajorant R j.1.val j.2.1.val j.2.2.val bslot M
  let q(j:κ):=((∏I∈j.2.1.val,I).absNorm:ℝ)^(p/2)
  have hρ(j:κ):0≤ρ j:=uniformMajorant_nonneg _ _ _ _ _ _ (fun i _=>hM i)
  have hq(j:κ):0≤q j:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hn(D:Finset (Ideal O))(hD:D∈R.powerset):0<((∏I∈D,I).absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun I hi=>(hR I (Finset.mem_powerset.mp hD hi)).ne_zero)))
  have hcf(z:O)(j:κ):‖cf z j‖≤ρ j:=by
    apply signedCoefficient_uniform _ R hR _ _ (Finset.mem_powerset.mp j.1.property)
      (Finset.mem_powerset.mp j.2.1.property) _ pool (fun i=>heightCoefficient (β i) t) P bslot M
      (fun i _=>hp i) (fun i _=>hP i) (fun i _=>hM i)
    · intro i _ I hI
      rw [heightCoefficient_norm _ _ _ (hp i I hI).ne_zero]
      exact hβ i I hI
    · intro i _ I hI hnz
      exact hs i I hI (left_ne_zero_of_mul hnz)
  have hsum(j:κ):Summable (fun z:O=>if (effectiveState s).radial.keep z then
      ‖f z j‖^2*(s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale)).re else 0):=by
    obtain ⟨B,hB,hbound⟩:=slots_bounded (Finset.univ\j.2.2.val) pool (fun i=>heightCoefficient (β i) t) P
    exact RadialSummability.pair_radial_summable (naturalCharacter s.character)
      (fun z=>∏i∈Finset.univ\j.2.2.val,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (β i) t) (P i)) (fun _=>t) (fun _=>t) W₁ W₂ a b a b
      (X₁/((∏I∈j.1.val,I).absNorm:ℝ)) (X₂/((∏I∈j.2.1.val,I).absNorm:ℝ)) B hb hb
      (div_pos hX₁ (hn _ j.1.property)) (div_pos hX₂ (hn _ j.2.1.property)) hs₁ hs₂
      (fun z=>hbound _) (effectiveState s).radial.keep s.radial.profile s.radial.scale s.radial.scale_pos
  have hchild(j:κ):radialEnergy (fun z=>f z j) (effectiveState s).radial.keep
      s.radial.profile s.radial.scale≤E*(q j)^2:=by
    have hh:=hchildren j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property
    have hpow:(q j)^2=((∏I∈j.2.1.val,I).absNorm:ℝ)^p:=by
      dsimp only [q]
      rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      norm_num
    rw [hpow]
    exact hh
  have he:=radial_weighted_energy cf f ρ q hρ hq (effectiveState s).radial.keep s.radial.profile
    s.radial.scale E s.radial.nonneg (fun z _=>hcf z) hE hsum hchild
  have hid(z:O):(∑j:κ,cf z j*f z j)=signedCommonSource s W₁ W₂ pool β P t X₁ X₂ z:=
    triple_sum R.powerset R.powerset (Finset.univ:Finset α).powerset
      (fun D₁ D₂ J=>signedCoefficient (naturalCharacter s.character z) R D₁ D₂ J
        pool (fun i=>heightCoefficient (β i) t) P *
        (polynomial (naturalCharacter s.character z) false W₁ (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
         polynomial (naturalCharacter s.character z) false W₂ (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
         ∏i∈Finset.univ\J,naturalSlot (naturalCharacter s.character z) (pool i) (heightCoefficient (β i) t) (P i)))
  simp_rw [hid] at he
  rw [←original_energy_eq_signed s W₁ W₂ ha hs₁ hs₂ pool hp β P hP t X₁ X₂ hX₁ hX₂] at he
  have hm:(∑j:κ,ρ j*q j)≤C*((∏I∈R,I).absNorm:ℝ)^(ε/2):=by
    exact (triple_sum R.powerset R.powerset (Finset.univ:Finset α).powerset
      (fun D₁ D₂ J=>uniformMajorant R D₁ D₂ J bslot M*((∏I∈D₂,I).absNorm:ℝ)^(p/2))).trans_le
      (hmass R hR (p/2) (by linarith))
  have hr:(((∏I∈R,I).absNorm:ℝ)^(ε/2))^2=(s.puncture.radical.absNorm:ℝ)^ε:=by
    rw [CenteredMomentAllocatedNaturalSource.primeSupport_product_radical s.puncture s.puncture_ne_zero]
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  exact he.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _=>mul_nonneg (hρ j) (hq j))) hm 2) hE).trans_eq
    (by rw [mul_pow,hr]))


end OAI.SevenEighths.Angular.NaturalReference

#print axioms OAI.SevenEighths.Angular.NaturalReference.original_positive_deletion
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.original_positive_deletion

#print axioms OAI.SevenEighths.Angular.NaturalReference.original_row_eq_signed
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.original_row_eq_signed

#print axioms OAI.SevenEighths.Angular.NaturalReference.original_energy_eq_signed
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.original_energy_eq_signed

#print axioms OAI.SevenEighths.Angular.NaturalReference.original_energy_weighted_deletion
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.NaturalReference.original_energy_weighted_deletion
