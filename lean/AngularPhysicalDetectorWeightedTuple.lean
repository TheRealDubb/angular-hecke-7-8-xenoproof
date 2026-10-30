import AngularPhysicalDetectorTupleFactor

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Angular.PhysicalDetectorHigh
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail)
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem tupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→ProbePhysical.PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i

def calibratedTupleValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : AngularCharacter) (u : FreeRow)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℂ :=
  star ((calibrationForSet S hmax).residueMonoid u.val)*
  (∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1))*
  physicalCompensatedRow S hS (Finset.univ.image P) (tupleOutside S P hPS) η u x w z

theorem calibratedTupleValue_factor {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : AngularCharacter) (u : FreeRow)
    (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS.prime) x))*
      (continuedCorrection (markExclusions S (Finset.univ.image P))
        (markedSourceExclusions S hS (Finset.univ.image P)) η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          continuedCompensatedLocal η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z
            (star (η.idealHom (P i).val)*((P i).val.absNorm:ℂ)^x)
            (((P i).val.absNorm:ℂ)^(-w))) := by
  unfold calibratedTupleValue
  rw [physicalCompensatedRow_indexed S hS P hP hPS]
  simp only [Finset.prod_mul_distrib]
  ring

end SevenEighths.Angular.PhysicalDetectorHigh
end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.tupleOutside

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibratedTupleValue_factor
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibratedTupleValue_factor
