import AngularPhysicalPlainSecondFamily
import OAI.NumberTheory.DirichletL.Moments.SourceRectangle

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentRowNorm CenteredMomentRectangle
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRectangle
open CenteredMomentExtraction
open CenteredMomentSecondHeightFamily (fixedBadMask fixedBadMask_ne_zero fixedBadMask_coprime)
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [instι : Fintype ι] [decι : DecidableEq ι]

def maskedRectangle (η : AngularCharacter) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J

def fullMaskedRectangle (η : AngularCharacter) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) : ℂ :=
  ∑ v : (∀ i,slots i),(∏ i,ν i (v i)*Wslot i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      (if IsCoprime ((∏ i,(v i:Ideal O))*I*J) R then (1:ℂ) else 0)*
      (if L∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
      idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)

theorem source_polynomial_eq_full_masked_rectangle (η : AngularCharacter) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (tuplePool slots S₁ S₂),
      finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      fullMaskedRectangle η m A z t slots ν (fun i I=>Wslot i ((Ideal.absNorm I:ℝ)/P i))
        R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [finite_column_regroup,sum_tuplePool]
  unfold fullMaskedRectangle
  apply Finset.sum_congr (by ext; simp)
  intro v hv
  rw [← finite_plain_rectangle S₁ S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ h₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [profileCoefficient,pack_product,pack_slot,pack_left,pack_right]
  ring

theorem fullMaskedRectangle_pullback (η : AngularCharacter) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ =
      fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) 1 1 := by
  unfold fullMaskedRectangle
  simp only [one_mul,idealRectangle_extract]


end OAI.SevenEighths.Angular.PlainRows

#print axioms OAI.SevenEighths.Angular.PlainRows.source_polynomial_eq_full_masked_rectangle
