import AngularPhysicalAllocatedNormalized
import AngularPhysicalNaturalCharacter
import AngularPhysicalCommonHeightEnvelope
import OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalRadial

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.AllocatedRadial
open AllocatedNatural PlainRows PlainRows.CommonRows PlainRows.RadialEnergy
open NaturalRows CommonMask Dyadic ChildRows ExceptionalRows ConcreteTraceCRT MeasureTheory
open CenteredMomentRetainedProfile CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentOriginalRadialComparison (radialEnergy)
open CenteredMomentAllocatedNaturalRadial (profile_support)
open CenteredMomentAllocatedNaturalSource (Plain rawScale rawScale_pos raw_same_product primeSupport_product_radical)
open CenteredMomentCommonMaskEnergy (heightCoefficient heightCoefficient_norm positive_height_phase_norm)
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => ActualEisensteinCubic.O
variable {α:Type*} [Fintype α] [DecidableEq α]
def Shared (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)
      (χ : O→AngularCharacter)(W₁ W₂ : 𝓢(ℝ,ℂ))(X₁ X₂ a₁ b₁ a₂ b₂ : ℝ)
      (pool : α→Finset (Ideal O))(β : α→Ideal O→ℂ)(P : α→ℝ)
      (keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K E : ℝ),
      0<X₁ → 0<X₂ → 0≤b₁ → 0≤b₂ →
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      (∀j∈F,∀I∈pool j,Prime I) → (∀j∈F,0<P j) →
      (∀j∈F,∀I∈pool j,‖β j I‖≤M j) →
      (∀j∈F,∀I∈pool j,β j I≠0 → (I.absNorm:ℝ)≤b j*P j) →
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → 0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        radialEnergy (fun z=>polynomial (χ z) false W₁
          (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          polynomial (χ z) false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ z) (pool j) (β j) (P j)) keep Φ K≤E) →
      radialEnergy (fun z=>polynomial ((χ z).excludePrimes R hR) false W₁ X₁ 0 0 *
        polynomial ((χ z).excludePrimes R hR) false W₂ X₂ 0 0 *
        ∏j∈F,naturalSlot ((χ z).excludePrimes R hR) (pool j) (β j) (P j)) keep Φ K≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

theorem uniform_shared (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,∀F : Finset T,
      Shared F (fun i=>b i) (fun i=>M i) C ε := by
  have he (T : Finset α) (F : Finset T) : ∃C : ℝ,0<C ∧ Shared F (fun i=>b i) (fun i=>M i) C ε :=
    actual_radial_shared_energy F (fun i=>b i) (fun i=>M i) (fun i _=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑T : Finset α,∑F : Finset T,C T F
  have hp (T : Finset α) : 0≤∑F : Finset T,C T F:=Finset.sum_nonneg (fun F _=>(hC T F).le)
  refine ⟨B,by have hh : 0≤∑T : Finset α,∑F : Finset T,C T F:=Finset.sum_nonneg (fun T _=>hp T);dsimp [B];linarith,?_⟩
  intro T F R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hprime hP hβ hs hK hΦ hE hchild
  have hCB : C T F≤B := by
    have h₁:=Finset.single_le_sum (fun G _=>(hC T G).le) (Finset.mem_univ F)
    have h₂:=Finset.single_le_sum (fun T _=>hp T) (Finset.mem_univ T)
    dsimp [B];linarith
  exact (hb T F R hR χ W₁ W₂ X₁ X₂ a₁ b₁ a₂ b₂ pool β P keep Φ K E
    hX₁ hX₂ hb₁ hb₂ hs₁ hs₂ hprime hP hβ hs hK hΦ hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

end OAI.SevenEighths.Angular.AllocatedRadial

#print axioms OAI.SevenEighths.Angular.AllocatedRadial.uniform_shared
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.AllocatedRadial.uniform_shared
