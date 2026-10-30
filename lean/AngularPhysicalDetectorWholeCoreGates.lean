import AngularPhysicalDetectorFreeExceptional
import AngularPhysicalFixedRayAnchor

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorJoint
open NaturalRows RelativePrime PhysicalDetectorInitial
open HeckeInverseAmplification (FreeRow)
open CenteredMomentNaturalFixedRaySource hiding fixed_inducing_free_support internalQ
local notation "O" => ActualEisensteinCubic.O

/-- The free sixth-power-reduced rows removed by `initialKeep` lie in a
fixed finite set. In particular they need not be discarded by imposing a
scale-dependent lower bound on every row. -/
theorem fixed_exceptional_free_finite (η : AngularCharacter) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQtop : Q ≠ ⊤)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus) :
    {u : FreeRow | ¬initialKeep η Q u.val}.Finite := by
  have hfinite := HeckeExceptionalRows.rows_finite
    (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
    (fun P hP => UniqueFactorizationMonoid.prime_of_normalized_factor P
      (Multiset.mem_toFinset.mp hP))
  have hpre : {u : FreeRow | u.val ∈ HeckeExceptionalRows.rows
      (UniqueFactorizationMonoid.normalizedFactors Q).toFinset}.Finite :=
    hfinite.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro u hu
  have hex : ExceptionalRows.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator 1) 1 u.val := by
    by_contra hn
    exact hu ⟨u.property.1, hn⟩
  exact fixed_inducing_free_support η Q hQ0 hQtop hQ72 hQη
    (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator 1)
    (mul_ne_zero CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero
      (ConcretePrimeRowBridge.idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hex

/-- The fixed exception set is finite even when the amplitude anchor
modulus differs from the detector base modulus. Intersecting the two
moduli enlarges the exception set and recovers the supported-core theorem. -/
theorem fixed_initial_exceptions_finite (η : AngularCharacter) (Q : Ideal O)
    (hQ0 : Q≠0) (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) :
    {u : FreeRow | ¬initialKeep η Q u.val}.Finite := by
  have hh := fixed_exceptional_free_finite η (internalQ Q η)
    (Ideal.inf_ne_bot_of_ne_bot hQ0 η.modulus_ne_bot) (ne_top_of_le_ne_top hQt inf_le_left)
    (inf_le_left.trans hQ72) inf_le_right
  apply hh.subset
  intro u hu hkeep
  have hex : ExceptionalRows.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1)
      1 u.val := by
    by_contra hn
    exact hu ⟨u.property.1,hn⟩
  apply hkeep.2
  obtain ⟨χ,ψ,hkχ,hkψ,hprim,hind,hmod,hcoeff⟩ := hex
  exact ⟨χ,ψ,hkχ,hkψ,hprim,hind,inf_le_left.trans hmod,hcoeff⟩

/-- A single fixed finite set removes every bad initial row in the entire
finite detector dictionary, including independent amplitude anchors. -/
theorem fixed_initial_exception_union {Label : Type*} [Fintype Label]
    (η : Label→AngularCharacter) (Q : Label→Ideal O)
    (hQ0 : ∀j,Q j≠0) (hQt : ∀j,Q j≠⊤) (hQ72 : ∀j,Q j≤Ideal.span {(72:O)}) :
    ∃E : Finset FreeRow,∀u : FreeRow,u∉E ↔ ∀j,initialKeep (η j) (Q j) u.val := by
  let E : Label→Finset FreeRow := fun j=>
    (fixed_initial_exceptions_finite (η j) (Q j) (hQ0 j) (hQt j) (hQ72 j)).toFinset
  refine ⟨Finset.univ.biUnion E,?_⟩
  intro u
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,not_exists]
  have he (j : Label) : u∈E j ↔ ¬initialKeep (η j) (Q j) u.val :=
    Set.Finite.mem_toFinset _
  simp only [he,not_not]


end OAI.SevenEighths.Angular.PhysicalDetectorJoint

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.fixed_exceptional_free_finite
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.fixed_exceptional_free_finite

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.fixed_initial_exceptions_finite
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.fixed_initial_exceptions_finite

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorJoint.fixed_initial_exception_union
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorJoint.fixed_initial_exception_union
