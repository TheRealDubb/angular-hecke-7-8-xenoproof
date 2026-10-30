import AngularPhysicalDetectorLiteralSource
import AngularPhysicalDetectorCoefficientPresentation
import AngularPhysicalDetectorWholeCoreGates
import OAI.NumberTheory.DirichletL.PrimeRows.DetectorReady

/- Actual final-probe source gates, with its original orientations.
The fixed exceptional set is kept explicit. Every sufficiently large
nonfloor row avoids it, uniformly over the entire finite dictionary.
No angular 7/8 premise, zero-free conclusion, or moment/count bound is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open Filter Set
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows RelativePrime PhysicalDetectorInitial
open HeckeInverseAmplification (FreeRow)
open ProbeHighRowFamily (rowNorm rowNorm_ge_one rawRow conductorConstant
  rawRow_conductor rowCharacter_conductor momentElement)
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceNaturalFamily (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) : AngularCharacter :=
  let F := naturalRow (SourceRows.sourceMomentData M H hH S hS η j).η u.val u.property.1
  if ProbeHighRowFamily.sourceMomentReverse M H j then F.character.conjugate else F.character

theorem literal_source_ideal_coefficients (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter)
    (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) (I : Ideal O) :
    (SourceRows.sourceDetectorFamily M H hH S hS η u j).idealHom I=
      (sourceNaturalFamily M H hH S hS η u j).idealHom I := by
  rw [SourceRows.source_family_moment_coeff M H hH S hS hbad]
  have he : ((SourceRows.sourceMomentData M H hH S hS η j).character (momentElement u)).idealHom I=
      (naturalCharacter (SourceRows.sourceMomentData M H hH S hS η j).η u.val).idealHom I := by
    rcases j with b|theta
    · cases b <;> exact source_moment_natural_coeff _ _ _
    · exact source_moment_natural_coeff _ _ _
  rw [he,naturalCharacter_eq _ u.val u.property.1]
  unfold sourceNaturalFamily
  cases ProbeHighRowFamily.sourceMomentReverse M H j <;>
    simp only [Bool.false_eq_true,ite_false,Bool.true_eq,ite_true,
      AngularCharacter.conjugate_idealHom,Complex.star_def]

theorem literal_source_type (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) :
    (SourceRows.sourceDetectorFamily M H hH S hS η u j).k=
      (sourceNaturalFamily M H hH S hS η u j).k := by
  have he : (sourceNaturalFamily M H hH S hS η u j).k=
      if ProbeHighRowFamily.sourceMomentReverse M H j then
        -(SourceRows.sourceMomentData M H hH S hS η j).η.k
      else (SourceRows.sourceMomentData M H hH S hS η j).η.k := by
    unfold sourceNaturalFamily
    split_ifs <;> simp only [AngularCharacter.conjugate_k,NaturalRow.angular_type]
  rw [he]
  rcases j with b|theta
  · cases b <;> simp [SourceRows.sourceDetectorFamily,SourceRows.sourceMomentData,
      ProbeHighRowFamily.sourceMomentReverse,SourceRows.momentData,SourceRows.targetRow_k,
      AngularCharacter.excludePrimes_k]
  · simp [SourceRows.sourceDetectorFamily,SourceRows.sourceMomentData,
      ProbeHighRowFamily.sourceMomentReverse,SourceRows.momentData]

theorem literal_source_order (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) :
    (SourceRows.sourceDetectorFamily M H hH S hS η u j).k.natAbs≤η.k.natAbs := by
  rcases j with b|theta
  · cases b <;> simp [SourceRows.sourceDetectorFamily,SourceRows.targetRow_k,
      AngularCharacter.excludePrimes_k]
  · simp [SourceRows.sourceDetectorFamily]

theorem literal_source_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter)
    (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) (Q : Ideal O)
    (hkeep : initialKeep (SourceRows.sourceMomentData M H hH S hS η j).η Q u.val) :
    (SourceRows.sourceDetectorFamily M H hH S hS η u j).k≠0 ∨
      (SourceRows.sourceDetectorFamily M H hH S hS η u j).residue≠1 := by
  have hn := (naturalRow (SourceRows.sourceMomentData M H hH S hS η j).η u.val u.property.1).nonprincipal
    u.property.1 Q 1 one_ne_zero hkeep.2
  have ho : (sourceNaturalFamily M H hH S hS η u j).k≠0 ∨
      (sourceNaturalFamily M H hH S hS η u j).residue≠1 := by
    by_cases he : ProbeHighRowFamily.sourceMomentReverse M H j=true
    · have hf : sourceNaturalFamily M H hH S hS η u j =
          (naturalRow (SourceRows.sourceMomentData M H hH S hS η j).η u.val u.property.1).character.conjugate := by
        simp [sourceNaturalFamily,he]
      rw [hf]
      rcases hn with hk|hr
      · left; simpa only [AngularCharacter.conjugate_k,neg_ne_zero] using hk
      · right
        change star _≠1
        intro hh
        exact hr (star_injective (hh.trans (star_one _).symm))
    · have hf : sourceNaturalFamily M H hH S hS η u j =
          (naturalRow (SourceRows.sourceMomentData M H hH S hS η j).η u.val u.property.1).character := by
        simp [sourceNaturalFamily,he]
      rw [hf]
      exact hn
  exact PhysicalDetectorJoint.nonprincipal_of_coefficients _ _
    (literal_source_type M H hH S hS η u j).symm
    (fun I=>(literal_source_ideal_coefficients M H hH S hS hbad η u j I).symm) ho

theorem literal_fixed_exceptions (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter)
    (hMt : M≠⊤) (hM72 : M≤Ideal.span {(72:O)}) :
    ∃E : Finset FreeRow,∀u : FreeRow,u∉E →
      (∀j,initialKeep (SourceRows.sourceMomentData M H hH S hS η j).η
        (internalQ M (SourceRows.sourceMomentData M H hH S hS η j).η) u.val) ∧
      (∀j,(SourceRows.sourceDetectorFamily M H hH S hS η u j).k≠0 ∨
        (SourceRows.sourceDetectorFamily M H hH S hS η u j).residue≠1) := by
  let base := fun j=>(SourceRows.sourceMomentData M H hH S hS η j).η
  obtain ⟨E,hE⟩ := PhysicalDetectorJoint.fixed_initial_exception_union base (fun j=>internalQ M (base j))
    (fun j=>Ideal.inf_ne_bot_of_ne_bot (NeZero.ne M) (base j).modulus_ne_bot)
    (fun _=>ne_top_of_le_ne_top hMt inf_le_left) (fun _=>inf_le_left.trans hM72)
  refine ⟨E,?_⟩
  intro u hu
  have hk := (hE u).mp hu
  exact ⟨hk,fun j=>literal_source_nonprincipal M H hH S hS hbad η u j _ (hk j)⟩

/-- All nonfloor source rows eventually have both the required retained
moment representation and an entire detector family. The threshold is
chosen before the moving row and every label. -/
theorem eventually_literal_source_retained (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : AngularCharacter)
    (hMt : M≠⊤) (hM72 : M≤Ideal.span {(72:O)}) (lower : ℝ) (hlower : 0<lower) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀u : FreeRow,Z^lower≤rowNorm u →
      (∀j,initialKeep (SourceRows.sourceMomentData M H hH S hS η j).η
        (internalQ M (SourceRows.sourceMomentData M H hH S hS η j).η) u.val) ∧
      (∀j,(SourceRows.sourceDetectorFamily M H hH S hS η u j).k≠0 ∨
        (SourceRows.sourceDetectorFamily M H hH S hS η u j).residue≠1) := by
  obtain ⟨E,hE⟩ := literal_fixed_exceptions M H hH S hS hbad η hMt hM72
  filter_upwards [(tendsto_rpow_atTop hlower).eventually (eventually_gt_atTop (∑u∈E,rowNorm u)),
    eventually_gt_atTop (1:ℝ)] with Z hlarge hZ
  refine ⟨hZ,?_⟩
  intro u hu
  apply hE u
  intro hmem
  have hc := Finset.single_le_sum (fun v (_ : v∈E)=>(zero_le_one.trans (rowNorm_ge_one v))) hmem
  linarith

theorem angular_target_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : FreeRow) :
    ((SourceRows.targetRow η u).excludePrimes S hS).modulus.absNorm≤
      η.modulus.absNorm*conductorConstant*(Ideal.span {u.val}:Ideal O).absNorm*(∏P∈S,P).absNorm := by
  let : Finite (O⧸η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Finite (O⧸(rawRow u).modulus) := Ring.HasFiniteQuotients.finiteQuotient (rawRow u).modulus_ne_bot
  change ((η.modulus⊓(rawRow u).modulus)*(∏P∈S,P)).absNorm≤_
  rw [map_mul]
  apply Nat.mul_le_mul_right _
  calc
    _≤η.modulus.absNorm*(rawRow u).modulus.absNorm := FiniteConductor.absNorm_inf_le_mul _ _
    _≤_ := by simpa only [mul_assoc] using Nat.mul_le_mul_left η.modulus.absNorm (rawRow_conductor u)

def literalConductorConstant (S : Finset (Ideal O)) (η : AngularCharacter) : ℕ :=
  conductorConstant*(∏P∈S,P).absNorm*(η.modulus.absNorm+1)+conductorConstant*M.absNorm

theorem literal_source_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) :
    (SourceRows.sourceDetectorFamily M H hH S hS η u j).modulus.absNorm≤
      literalConductorConstant M S η*(Ideal.span {u.val}:Ideal O).absNorm := by
  cases j with
  | inl b=>
    cases b with
    | false=>
      apply (angular_target_conductor S hS η u).trans
      unfold literalConductorConstant
      ring_nf
      omega
    | true=>
      apply (rowCharacter_conductor S hS u).trans
      unfold literalConductorConstant
      ring_nf
      omega
  | inr theta=>
    apply (ProbeRayCharacterFamily.raw_twisted_conductor M H hH u theta).trans
    unfold literalConductorConstant
    ring_nf
    omega

theorem eventually_literal_source_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : AngularCharacter) (pad : ℝ) (hpad : 0<pad) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(u : FreeRow)(d : ℝ),rowNorm u≤Z^(d-pad) →
      ∀j,((SourceRows.sourceDetectorFamily M H hH S hS η u j).modulus.absNorm:ℝ)≤Z^d := by
  filter_upwards [(tendsto_rpow_atTop hpad).eventually
    (eventually_ge_atTop (literalConductorConstant M S η:ℝ)),eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro u d hu j
  have hq : ((SourceRows.sourceDetectorFamily M H hH S hS η u j).modulus.absNorm:ℝ)≤
      (literalConductorConstant M S η:ℝ)*rowNorm u := by
    dsimp only [rowNorm]
    exact_mod_cast literal_source_conductor M H hH S hS η u j
  apply hq.trans
  calc
    _≤Z^pad*Z^(d-pad) := mul_le_mul hc hu
      (zero_le_one.trans (rowNorm_ge_one u)) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
    _=Z^d := by rw [←Real.rpow_add (zero_lt_one.trans hZ)];congr 1;ring

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_ideal_coefficients
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_ideal_coefficients

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_type
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_type

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_order
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_order

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_nonprincipal
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_nonprincipal

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_fixed_exceptions
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_fixed_exceptions

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.eventually_literal_source_retained
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.eventually_literal_source_retained

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.angular_target_conductor
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.angular_target_conductor

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_conductor
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_conductor

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.eventually_literal_source_conductor
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.eventually_literal_source_conductor
