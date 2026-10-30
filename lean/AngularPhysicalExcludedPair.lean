import AngularPhysicalCommonMaskRadial
import AngularPhysicalPlainPositiveEnergy
import AngularPhysicalNaturalMask
import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.CommonMask
open OAI.SevenEighths.Angular.Dyadic ConcreteTraceCRT
open CenteredMomentPositiveSummability (bounded_radial_summable)
open CenteredMomentOriginalRadialComparison (radialEnergy finite_weighted)
local notation "O" => ActualEisensteinCubic.O

open NaturalRows (excluded)
open CenteredMomentNaturalRowSource (support_prime)
open CenteredMomentAllocatedNaturalSource (primeSupport_product_radical)
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound

theorem excluded_pair (angularOrder:ℕ) (a b ε : ℝ) (ha : 0<a) (hb : 0≤b) (hε : 0<ε) :
    ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0<C ∧
    ∀ (W₁ W₂ : 𝓢(ℝ,ℂ)), Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
    ∀ (χ : O→AngularCharacter) (r : Radial) (R : Ideal O) (Q X₁ X₂ : ℝ), R≠0 →
      0≤Q → 0<X₁ → 0<X₂ →
      (∀z,r.keep z→(χ z).k.natAbs=angularOrder) →
      (∀z,r.keep z→(χ z).k≠0 ∨ (χ z).residue≠1) →
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤Q) →
    radialEnergy (fun z=>polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Q^4 := by
  obtain ⟨S,C,hC,hpair⟩ := PlainPositiveEnergy.actual_radial_pair_bound angularOrder a b ha
  obtain ⟨Cd,hCd,hdel⟩ := actual_radial_shared_energy (∅ : Finset (Fin 0))
    (fun _=>0) (fun _=>0) (by simp) ε hε
  refine ⟨S,Cd*C*3^8,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R Q X₁ X₂ hR hQ hX₁ hX₂ horder hχ hmod
  let E := C*diagonalControl r.profile*max 1 r.scale*
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Q^4*3^8
  have hdiag := diagonalControl_nonneg r.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hh := hdel (CompletedGauss.primeSupport R) (support_prime R) χ W₁ W₂
    X₁ X₂ a b a b (fun _=>∅) (fun _ _=>0) (fun _=>1) r.keep r.profile r.scale E
    hX₁ hX₂ hb hb hs₁ hs₂ (by simp) (by simp) (by simp) (by simp)
    r.scale_pos r.nonneg hE ?_
  · simp only [Finset.prod_empty,mul_one] at hh
    rw [primeSupport_product_radical R hR] at hh
    change radialEnergy (fun z=>polynomial (excluded (χ z) R) false W₁ X₁ 0 0 *
      polynomial (excluded (χ z) R) false W₂ X₂ 0 0) r.keep r.profile r.scale ≤ _ at hh
    exact hh.trans_eq (by dsimp [E]; ring)
  · intro D₁ hD₁ D₂ hD₂ J hJ
    have hn (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport R).powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime R I (Finset.mem_powerset.mp hD hi)).ne_zero)))
    have he := hpair W₁ W₂ hs₁ hs₂ χ r Q
      (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0
      hQ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂)) horder hχ hmod
    norm_num only [abs_zero,add_zero,show (3:ℝ)^4=81 by norm_num] at he
    simpa only [Finset.empty_sdiff,Finset.prod_empty,mul_one] using he.trans_eq (by dsimp [E]; ring)


end OAI.SevenEighths.Angular.CommonMask

#print axioms OAI.SevenEighths.Angular.CommonMask.excluded_pair
