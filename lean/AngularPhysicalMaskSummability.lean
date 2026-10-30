import AngularPhysicalCommonMaskEnergy
import AngularPhysicalPlainAbsolute
import OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.CommonMask
open OAI.SevenEighths.Angular.Dyadic ConcreteTraceCRT
open CenteredMomentPositiveSummability (bounded_radial_summable)
open CenteredMomentOriginalRadialComparison (radialEnergy finite_weighted)
local notation "O" => ActualEisensteinCubic.O

theorem polynomial_bounded (W : 𝓢(ℝ,ℂ)) (a b X : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support (W:ℝ→ℂ)⊆Set.Icc a b) :
    ∃B : ℝ,0≤B ∧ ∀χ : AngularCharacter,∀t : ℝ,‖polynomial χ false W X 0 t‖≤B := by
  refine ⟨(128*b*SchwartzMap.seminorm ℝ 0 0 W)*Real.sqrt X,by positivity,?_⟩
  intro χ t
  exact PlainAbsolute.polynomial_absolute χ W b (SchwartzMap.seminorm ℝ 0 0 W) X t
    hb (apply_nonneg _ _) hX (fun x=>SchwartzMap.norm_le_seminorm ℝ W x)
    (fun x hx=>(hs hx).2)

lemma pair_radial_summable (χ : O→AngularCharacter) (P : O→ℂ) (t omega : O→ℝ)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b c d X Y Pbound : ℝ)
    (hb : 0≤b) (hd : 0≤d) (hX : 0<X) (hY : 0<Y)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b) (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc c d)
    (hP : ∀z,‖P z‖≤Pbound) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z:O=>if keep z then
      ‖polynomial (χ z) false W₁ X 0 (t z)*polynomial (χ z) false W₂ Y 0 (omega z)*P z‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B₁,hB₁,h₁⟩:=polynomial_bounded W₁ a b X hb hX hs₁
  obtain ⟨B₂,hB₂,h₂⟩:=polynomial_bounded W₂ c d Y hd hY hs₂
  apply bounded_radial_summable _ (B₁*B₂*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul (h₁ _ _) (h₂ _ _) (norm_nonneg _) hB₁)
    (hP z) (norm_nonneg _) (mul_nonneg hB₁ hB₂)

lemma polynomial_const_mul (χ : AngularCharacter) (W : ℝ→ℂ) (X σ omega : ℝ) (c : ℂ) :
    Dyadic.polynomial χ false (fun x=>c*W x) X σ omega=
      c*Dyadic.polynomial χ false W X σ omega := by
  unfold Dyadic.polynomial
  have he : (fun I : Dyadic.NonzeroIdeal=>
      Dyadic.summand χ false (fun x=>c*W x) X σ omega I)=
      (fun I=>c*Dyadic.summand χ false W X σ omega I) := by
    funext I
    unfold Dyadic.summand
    ring
  rw [he,tsum_mul_left]
  ring


end OAI.SevenEighths.Angular.CommonMask

#print axioms OAI.SevenEighths.Angular.CommonMask.pair_radial_summable
