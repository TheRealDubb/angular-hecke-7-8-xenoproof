import AngularPhysicalDetectorCentralProduct
import AngularPhysicalDetectorReciprocalRectangle
import AngularPhysicalDetectorLiteralSourceGates

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Angular.PhysicalDetectorHigh
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions
  FirstTail rowNorm rowNorm_ge_one)
open PhysicalReciprocal (presentationComplexity)
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def centralRemainingScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS.prime) x*
    continuedCorrection S hS η u x w z

lemma centralRowScalar_split (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : AngularCharacter) (u : FreeRow) (x w z : ℂ) :
    centralRowScalar S hS hmax η u x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      centralRemainingScalar S hS η u x w z := by
  unfold centralRowScalar centralRemainingScalar
  ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M ≤ Hray)
variable (angularOrder : ℕ)

theorem centralRemainingScalar_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : SourceExclusions S),FirstTail (4*e) S →
      ∀(η : AngularCharacter) (u : FreeRow) (horder : η.k.natAbs≤angularOrder)
      (hnp : ∀j,(SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).k≠0 ∨
        (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).residue≠1)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u) hnp (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖≤C*
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*
        (presentationComplexity ((SourceRows.targetRow η u).excludePrimes S hS.prime) H)^eps := by
  obtain ⟨Ch,hCh,hh⟩ := continuedCorrection_first_subpower eps heps
  obtain ⟨Cr,hCr,hr⟩ := PhysicalDetectorControl.buffered_rectangle_reciprocal_bound angularOrder e eps he he' heps
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨(L+1)*Cr*Ch,by positivity,?_⟩
  intro S hS hfirst η u horder hnp B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L+1 :=
    (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ)<2)
      (by simp only [Complex.mul_re];rw [hz];norm_num)).trans (by linarith)
  have hc := hh (4*e) S hS hfirst η u x w z
    (by rw [hx];linarith) (by rw [hw];linarith) (by rw [hz]) (by rw [hx,hw];linarith)
  have hrec := hr (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u)
    (fun j=>(PhysicalDetectorLiteralSource.literal_source_order M Hray hHray S hS.prime η u j).trans horder)
    hnp B a H i hB ha ha1 hH hbin
    (Sum.inl false) x (by rw [hx]) (by rw [hx];linarith) hxi
  change ‖PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS.prime) x‖ ≤ Cr * presentationComplexity ((SourceRows.targetRow η u).excludePrimes S hS.prime) H ^ eps at hrec
  unfold centralRemainingScalar
  rw [norm_mul,norm_mul]
  apply (mul_le_mul (mul_le_mul hl hrec (norm_nonneg _) (by linarith)) hc (norm_nonneg _)
    (mul_nonneg (by linarith) (mul_nonneg hCr.le (Real.rpow_nonneg (by
      unfold presentationComplexity PhysicalLogarithmic.complexity;positivity) _)))).trans
  exact le_of_eq (by ring)

end SevenEighths.Angular.PhysicalDetectorHigh

end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.centralRowScalar_split

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.centralRemainingScalar_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.centralRemainingScalar_bound
