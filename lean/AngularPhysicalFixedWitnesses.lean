import OAI.NumberTheory.DirichletL.ParametersFixedSource
import OAI.NumberTheory.DirichletL.Dictionary.InverseRawRealRadial
import AngularPhysicalDetectorActualBandParameters

/- Fixed geometric data. None of these choices depends on the target
character or its conductor. The angular order is fixed by the caller. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set
namespace OAI.SevenEighths.Angular.PhysicalFixedWitnesses
local notation "O" => ActualEisensteinCubic.O

def rayModulus : Ideal O :=
  Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} ⊓ Ideal.span {(72:O)}

theorem rayModulus_ne_zero : rayModulus≠0 :=
  Ideal.inf_ne_bot_of_ne_bot
    (Ideal.span_singleton_eq_bot.not.mpr CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

instance : NeZero rayModulus := ⟨rayModulus_ne_zero⟩
instance : Finite (O⧸rayModulus) := Ring.HasFiniteQuotients.finiteQuotient rayModulus_ne_zero

theorem rayModulus_le_mask : rayModulus≤Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} := inf_le_left

theorem rayModulus_le_72 : rayModulus≤Ideal.span {(72:O)} := inf_le_right

theorem rayModulus_ne_top : rayModulus≠⊤ := by
  have hmask : Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}≤Ideal.span {(2:O)} :=
    Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _)
  have hle := rayModulus_le_mask.trans hmask
  intro h
  exact CanonicalQuadraticSieve.twoIdeal_maximal.isPrime.ne_top (top_le_iff.mp (h ▸ hle))

theorem exists_radial_majorant :
    ∃(Phi : 𝓢(ℝ,ℂ))(bPhi : ℝ),2≤bPhi ∧
      Function.support (Phi:ℝ→ℂ)⊆Iic bPhi ∧
      (∀x,0≤(Phi x).re) ∧ ∀x∈Icc (0:ℝ) 1,Phi x=1 := by
  obtain ⟨Phi,hcompact,hpos,_hreal,hone⟩ :=
    DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant
  obtain ⟨b,hb⟩ := hcompact.isCompact.bddAbove
  refine ⟨Phi,max 2 b,le_max_left _ _,?_,hpos,hone⟩
  intro x hx
  exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)

end OAI.SevenEighths.Angular.PhysicalFixedWitnesses
#print axioms OAI.SevenEighths.Angular.PhysicalFixedWitnesses.rayModulus_ne_zero
#print axioms OAI.SevenEighths.Angular.PhysicalFixedWitnesses.rayModulus_ne_top
#print axioms OAI.SevenEighths.Angular.PhysicalFixedWitnesses.exists_radial_majorant
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalFixedWitnesses.exists_radial_majorant
