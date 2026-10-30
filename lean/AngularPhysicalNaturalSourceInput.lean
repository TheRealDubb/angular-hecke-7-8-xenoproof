import AngularPhysicalOriginalSourceComparison
import AngularPhysicalEnergyState

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.PlainRows.CommonRows
open CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRectangle CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceRow CenteredMomentRetainedProfile
open CenteredMomentSecondHeightFamily (fixedBadMask)
open CenteredMomentPositiveSummability (bounded_radial_summable)
open CenteredMomentPlainEnergy CenteredMomentRowNorm
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [instι:Fintype ι] [decι:DecidableEq ι]
local instance angularNaturalSourceInputDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

section Natural
open EnergyState CenteredMomentFiniteProfileExceptional
variable {angularOrder:ℕ} {Z Bmask bΦ a b : ℝ}
variable (state : NaturalState angularOrder Z Bmask bΦ) (p : Profiles a b) (ha : 0<a)
variable (S : ι→Finset (Ideal O)) (hp : ∀i,∀I∈S i,Prime I)
variable (ν : ι→AngularCharacter) (Wslot : ι→ℝ→ℂ) (P M : ι→ℝ)
variable (hP : ∀i,0<P i) (hM : ∀i,1≤M i)
variable (aslot bslot : ℝ) (haslot : 0<aslot)
variable (hsSlot : ∀i,Function.support (Wslot i)⊆Set.Icc aslot bslot)
variable (hWslot : ∀i x,‖Wslot i x‖≤M i)
variable (t X₁ X₂ Y₁ Y₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
variable (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (hsame : Y₁*Y₂=X₁*X₂)

def naturalData : Data ι where
  η := state.character
  m := state.mask
  A := 1
  t := t
  slots := S
  prime := hp
  ν := fun i=>(ν i).idealHom
  W := Wslot
  lo := fun _=>aslot
  hi := fun _=>bslot
  P := P
  lo_pos := fun _=>haslot
  P_pos := hP
  support := hsSlot
  W₁ := p.profile 0
  W₂ := p.profile 1
  X₁ := X₁
  X₂ := X₂
  Y₁ := Y₁
  Y₂ := Y₂
  M := M
  M_ge_one := hM
  coefficient_bound := fun i I _=>by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ((ν i).norm_idealHom_le_one I) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hWslot i ((Ideal.absNorm I:ℝ)/P i))
  b₁ := b
  b₂ := b
  support₁ := fun x hx=>(p.support 0 hx).2
  support₂ := fun x hx=>(p.support 1 hx).2
  X₁_pos := hX₁
  X₂_pos := hX₂
  Y₁_pos := hY₁
  Y₂_pos := hY₂
  same_product := hsame
  rows := ∅
  weight := fun _=>0
  weight_nonneg := fun _ _=>le_refl _

def naturalInput : Input ι :=
  completeInput (naturalData state p S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
    t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame)
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 0) a b ha (p.support 0))
    (CenteredMomentDetectorPlainSource.support_zero (p.profile 1) a b ha (p.support 1))
    (fun i I=>(ν i).norm_idealHom_le_one I) hWslot aslot bslot haslot
    (fun _=>le_refl _) (fun _=>le_refl _)

theorem natural_energy_comparison :
    let inp := naturalInput state p ha S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame
    OAI.SevenEighths.Angular.InductionEnergy.energy state.character state.mask 1 t
      (p.profile 0) (p.profile 1) S
      (fun i I=>(ν i).idealHom I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P X₁ X₂
      state.radial.keep state.radial.profile state.radial.scale ≤
    2*‖finiteHeckeEnergy state.character fixedBadMask 1 t
      (finiteColumns (Fintype.piFinset inp.pools)) (coefficient inp state.puncture 1)
      state.radial.profile state.radial.scale‖/(X₁*X₂*∏i,P i)+
    2*OAI.SevenEighths.Angular.InductionEnergy.energy state.character state.mask 1 t
      (p.profile 0) (p.profile 1) S
      (fun i I=>(ν i).idealHom I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) P Y₁ Y₂
      state.radial.keep state.radial.profile state.radial.scale :=
  positive_energy_comparison
    (naturalInput state p ha S hp ν Wslot P M hP hM aslot bslot haslot hsSlot hWslot
      t X₁ X₂ Y₁ Y₂ hX₁ hX₂ hY₁ hY₂ hsame) state.puncture state.radial

end Natural

end OAI.SevenEighths.Angular.PlainRows.CommonRows

#print axioms OAI.SevenEighths.Angular.PlainRows.CommonRows.natural_energy_comparison
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PlainRows.CommonRows.natural_energy_comparison
