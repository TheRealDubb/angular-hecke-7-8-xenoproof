import AngularPhysicalDetectorMesh
import AngularPhysicalNaturalUnitMask
import OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorInitial
open EnergyState EnergyBands RelativePrime PlainRows NaturalRows InductionEnergy
open QuadraticInitialBound CenteredMomentFiniteProfileExceptional ConcretePrimeRowBridge
open CenteredMomentSecondHeightFamily (fixedBadMask)
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentEnergyBands (length)
open ConcreteTraceCRT
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

def initialKeep (η:AngularCharacter) (Q:Ideal O) (z:O):Prop :=
  z≠0 ∧ ¬ExceptionalRows.FixedInducingRow η Q (fixedBadMask*idealGenerator 1) 1 z

def initialState (n:ℕ) (η:AngularCharacter) (hn:η.k.natAbs=n) (Q:Ideal O)
    (Φ:𝓢(ℝ,ℂ)) (bΦ U δ:ℝ) (hU:1≤U) (hδ:0≤δ)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ) (hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤U^δ):NaturalState n U 0 bΦ where
  character:=η
  angular_order:=hn
  fixedModulus:=Q
  puncture:=1
  radial:={
    keep:=initialKeep η Q
    profile:=Φ
    scale:=U
    scale_pos:=zero_lt_one.trans_le hU
    nonneg:=fun z=>hp _ }
  rowWidth:=1
  characterWidth:=δ
  base_ge_one:=hU
  row_nonneg:=by norm_num
  character_nonneg:=hδ
  scale_eq:=by simp
  modulus_bound:=hη
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=hs
  row_ne_zero:=fun _ h=>h.1
  nonexceptional:=fun _ h=>h.2

/-- This is the literal finite physical sum, including the same angular parent,
prime columns, common height, and all natural support holes. -/
theorem finite_physical_le_energy {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:AngularCharacter) (Q:Ideal O) (Φ:𝓢(ℝ,ℂ)) (U:ℝ) (hU:0<U)
    (hp:∀x,0≤(Φ x).re) (hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ) (t:ℝ)
    (rows:Finset O) (hkeep:∀z∈rows,initialKeep η Q z)
    (hrows:∀z∈rows,((Ideal.span {z}).absNorm:ℝ)≤U):
    (∑z∈rows,‖positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂‖^2)≤
      energy η (fixedBadMask*idealGenerator 1) 1 t W₁ W₂ S β P X₁ X₂
        (initialKeep η Q) Φ U := by
  let m:O:=fixedBadMask*idealGenerator 1
  obtain ⟨B,hB⟩:=product_bounded η m 1 t
    (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹ W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  have hsum:=CenteredMomentPositiveSummability.bounded_radial_summable
    (fun z:O=>positiveSlotRow η m 1 z W₁ W₂ S β P t X₁ X₂) B hB
    (initialKeep η Q) Φ U hU
  have he (z:O) (hz:z∈rows):
      ‖positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂‖^2=
        if initialKeep η Q z then
          ‖positiveSlotRow η m 1 z W₁ W₂ S β P t X₁ X₂‖^2*
            (Φ (‖eisEmbedding z‖^2/U)).re else 0 := by
    rw [if_pos (hkeep z hz)]
    have hx:‖eisEmbedding z‖^2/U∈Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows z hz
    rw [hone _ hx,Complex.one_re,mul_one]
    exact congrArg (fun q:ℂ=>‖q‖^2)
      (natural_unit_mask_positive (naturalRow η z (hkeep z hz).1) W₁ W₂ S β P t X₁ X₂).symm
  calc
    _=∑z∈rows,if initialKeep η Q z then
        ‖positiveSlotRow η m 1 z W₁ W₂ S β P t X₁ X₂‖^2*
          (Φ (‖eisEmbedding z‖^2/U)).re else 0 := Finset.sum_congr rfl he
    _≤_:=hsum.sum_le_tsum _ (fun z _=>by
      split_ifs
      · exact mul_nonneg (sq_nonneg _) (hp _)
      · exact le_rfl)


end OAI.SevenEighths.Angular.PhysicalDetectorInitial

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorInitial.finite_physical_le_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorInitial.finite_physical_le_energy
