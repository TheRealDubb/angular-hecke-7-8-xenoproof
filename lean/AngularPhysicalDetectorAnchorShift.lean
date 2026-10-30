import AngularPhysicalFixedRayAnchor
import AngularPhysicalCommonMaskSlots

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PhysicalDetectorJoint
open NaturalRows CommonMask RelativePrime
local notation "O" => ActualEisensteinCubic.O

theorem norm_ideal_unit (χ : AngularCharacter) (I : Ideal O)
    (hI : I≠0) (hc : IsCoprime I χ.modulus) : ‖χ.idealHom I‖=1 := by
  let : Finite (O⧸χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (O⧸χ.modulus)ˣ := Fintype.ofFinite _
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
  have hu : IsUnit (Ideal.Quotient.mk χ.modulus (ConcretePrimeRowBridge.idealGenerator I)) := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr
    simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hc
  rw [←ConcretePrimeRowBridge.span_idealGenerator I,AngularCharacter.idealHom_span,
    AngularCharacter.norm_elementCoeff χ hg]
  obtain ⟨u,he⟩ := hu
  rw [←he]
  simpa only [MulChar.coe_equivToUnitHom] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.residue.apply_mem_rootsOfUnity u)

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Shift an arbitrary angular dictionary twist to the anchor, retaining
exactly its conductor zeros. No finite-order assumption is made. -/
theorem shifted_anchor_coefficient (η Ω ν : AngularCharacter) (u : O)
    (F : NaturalRow η u) (G : NaturalRow (η.product ν) u)
    (θ : RayQuotient.Characters M H) (I : Ideal O) :
    G.character.idealHom I*(rayRelativeCharacter M H hH (Ω.product ν) θ).idealHom I=
      (excluded F.character ν.modulus).idealHom I*
        (rayRelativeCharacter M H hH Ω θ).idealHom I := by
  rw [G.ideal,excluded_ideal _ _ ν.modulus_ne_bot,F.ideal]
  by_cases hI : I=0
  · subst I
    simp only [map_zero,zero_mul,ite_self]
  by_cases hc : IsCoprime I ν.modulus
  · rw [if_pos hc]
    have hn := norm_ideal_unit ν I hI hc
    have hcancel : ν.idealHom I*star (ν.idealHom I)=1 := by
      simpa only [Complex.star_def,hn,one_pow,Complex.ofReal_one] using
        Complex.mul_conj' (ν.idealHom I)
    simp only [rayRelativeCharacter_coeff,AngularCharacter.product_idealHom,star_mul']
    calc
      _=(η.idealHom I*CanonicalRowCompletion.idealRowHom
          (CenteredMomentSecondHeightFamily.fixedBadMask^6*u) I)*
          (star (Ω.idealHom I)*RayQuotient.idealCharacter M H hH θ I)*
          (ν.idealHom I*star (ν.idealHom I)) := by ring
      _=_ := by rw [hcancel,mul_one]
  · rw [if_neg hc,zero_mul]
    have hn : ν.idealHom I=0 := (ν.idealHom_zero_iff I).mpr (Or.inr hc)
    simp only [AngularCharacter.product_idealHom,hn,mul_zero,zero_mul]

/-- The same identity for the literal normalized slot, for every pool,
weight and frequency encoded in that weight. -/
theorem shifted_anchor_slot (η Ω ν : AngularCharacter) (u : O)
    (F : NaturalRow η u) (G : NaturalRow (η.product ν) u)
    (θ : RayQuotient.Characters M H) (pool : Finset (Ideal O))
    (weight : Ideal O→ℂ) (P : ℝ) :
    naturalSlot G.character pool
      (fun I=>(rayRelativeCharacter M H hH (Ω.product ν) θ).idealHom I*weight I) P=
    naturalSlot (excluded F.character ν.modulus) pool
      (fun I=>(rayRelativeCharacter M H hH Ω θ).idealHom I*weight I) P := by
  unfold naturalSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simpa only [←mul_assoc] using congrArg (fun c : ℂ=>c*weight I)
    (shifted_anchor_coefficient M H hH η Ω ν u F G θ I)

end OAI.SevenEighths.Angular.PhysicalDetectorJoint

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.norm_ideal_unit
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.norm_ideal_unit

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.shifted_anchor_coefficient
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.shifted_anchor_coefficient

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.shifted_anchor_slot
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.shifted_anchor_slot
