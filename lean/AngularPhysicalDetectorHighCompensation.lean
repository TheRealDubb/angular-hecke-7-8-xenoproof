import AngularPhysicalDetectorHighMarkedSubset

/- Actual angular adaptation of pinned OAI-003 proof bodies.
Original OpenAI and predecessor Apache-2.0 notices retained in source pin. -/
set_option Elab.async false
set_option maxHeartbeats 600000
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open ActualEisensteinCubic HeckeInverseAmplification ProbePhysical ProbeEuler ProbeEulerFinsupp
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
open ProbeHighRowFamily (rowCharacter rowCharacter_hasProd markExclusions markExclusions_prime
  mem_markExclusions lift_outside_hasProd)
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
attribute [local irreducible] FamilyContinuation.LFunction AngularCharacter.excludePrimes SourceRows.targetRow

def compensatedLocalCorrection (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (x w z B q : ℂ) : ℂ :=
  B*markedLocalCorrection η u P x w z-q*localCorrection η u P x w z

theorem compensatedLocalCorrection_eq_raw (η : AngularCharacter) (u : FreeRow) (P : PrimeIdeal)
    (x w z B q : ℂ) :
    compensatedLocalCorrection η u P x w z B q=
      (B*idealRowMarkedLocalFactor η u.val P x w z-q*idealRowHighLocalFactor η u.val P.val x w z)*
        localNormalization η u P x w z := by
  rw [compensatedLocalCorrection,markedLocalCorrection,localCorrection_eq_normalization]
  ring

theorem spectralCompensatedRow_original_L_factorization
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter) (u : FreeRow)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedRow S T η u.val x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS) (6*z)*HeckeFamily.LFunction (rowCharacter S hS u) w/
        FamilyContinuation.LFunction ((SourceRows.targetRow η u).excludePrimes S hS) x)*
      (globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,compensatedLocalCorrection η u P x w z (B P) (q P)) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hZ := HeckeFamily.LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := HeckeFamily.LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := FamilyContinuation.LFunction_ne_zero ((SourceRows.targetRow η u).excludePrimes S hS) x hx1
  have hn := finite_replacement_normalized S hS hbad T hT η u x w z
    (fun P=>B P*idealRowMarkedLocalFactor η u.val P x w z-q P*idealRowHighLocalFactor η u.val P.val x w z)
    hx hw hz
  simp_rw [←compensatedLocalCorrection_eq_raw] at hn
  rw [←spectralCompensatedRow_eq_product S hS T hT η u.val x w z B q hx hw hz] at hn
  rw [←hn,globalNormalization]
  field_simp [hZ,hW,hD]

theorem indexedCompensatedHigh_original_L_factorization {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : AngularCharacter) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    indexedCompensatedHigh η S (fun i=>CompletedGauss.primaryGenerator (P i).val) u.val x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*HeckeFamily.LFunction (rowCharacter S hS.prime u) w/
        FamilyContinuation.LFunction ((SourceRows.targetRow η u).excludePrimes S hS.prime) x)*
      (globalCorrection (markExclusions S (Finset.univ.image P)) η u x w z*
        ∏i,compensatedLocalCorrection η u (P i) x w z
          (star (η.idealHom (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  have hs (i : Fin K) := outside_prime_supported S hS.bad (P i) (hPS i)
  rw [indexedCompensatedHigh_eq_spectral η S P hP hs u.val x w z]
  have ht : ∀Q∈Finset.univ.image P,Q.val∉S := by
    intro Q hQ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
    exact hPS i
  rw [spectralCompensatedRow_original_L_factorization S hS.prime hS.bad
    (Finset.univ.image P) ht η u x w z _ _ hx hw hz,Finset.prod_image hP.injOn]


end
end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.spectralCompensatedRow_original_L_factorization

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.indexedCompensatedHigh_original_L_factorization
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.indexedCompensatedHigh_original_L_factorization
