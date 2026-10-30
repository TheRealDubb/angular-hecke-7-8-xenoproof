import AngularPhysicalPrincipalLocalBridge
import AngularPhysicalDetectorHighPrincipal

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ProbePhysical ProbeEuler ProbeLocal
open ProbeHighRowFamily (markExclusions)
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem spectral_principal_ratio_product (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedRow S T η 1 x w z B q=
      markedIdealHighSeries S 1 η 1 x w z*
        ∏P∈T,(B P*idealRowMarkedLocalFactor η 1 P x w z-
          q P*idealRowHighLocalFactor η 1 P.val x w z)/
            idealRowHighLocalFactor η 1 P.val x w z := by
  have hb := markedRowSeries_subset_replacement S hS.prime T T (fun _ h=>h) hT
    η 1 x w z hx hw hz
  simp only [Finset.sdiff_self,Finset.prod_empty,mul_one] at hb
  have hn : (∏P∈T,idealRowHighLocalFactor η 1 P.val x w z)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro P hP
    exact PhysicalPrincipalProducts.principal_high_local_ne_zero S hS η P (hT P hP) x w z hx hw hz
  rw [spectralCompensatedRow_eq_product S hS.prime T hT η 1 x w z B q hx hw hz,
    hb,Finset.prod_div_distrib]
  field_simp [hn]

theorem spectral_principal_continued (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : AngularCharacter)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedRow S T η 1 x w z B q=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        FamilyContinuation.LFunction (η.excludePrimes S hS.prime) x*globalClosedCorrection η S x w z)*
      ∏P∈T,compensatedReplacement (coordV P.val.absNorm z) (coordW P.val.absNorm 1 w)
        (coordD P.val.absNorm (η.idealHom P.val) 1 x)
        (PhysicalPrincipalProducts.idealMarkedClosed η P x w z) (B P) (q P)/
          idealClosedCorrection η P x w z := by
  rw [spectral_principal_ratio_product S hS T hT η x w z B q hx hw hz,
    principalHigh_L_factorization S hS.prime (outside_prime_supported S hS.bad) hS.tail η x w z hx hw hz]
  congr 1
  apply Finset.prod_congr rfl
  intro P hP
  exact PhysicalPrincipalProducts.principal_compensated_ratio S hS η P (hT P hP) x w z (B P) (q P) hx hw hz

theorem indexedCompensatedHigh_principal_continued {K : ℕ} (η : AngularCharacter)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        FamilyContinuation.LFunction (η.excludePrimes S hS.prime) x*globalClosedCorrection η S x w z)*
      ∏i,compensatedReplacement (coordV (Ideal.absNorm (P i).val) z)
        (coordW (Ideal.absNorm (P i).val) 1 w)
        (coordD (Ideal.absNorm (P i).val) (η.idealHom (P i).val) 1 x)
        (PhysicalPrincipalProducts.idealMarkedClosed η (P i) x w z)
        (star (η.idealHom (P i).val)*(Ideal.absNorm (P i).val:ℂ)^x)
        ((Ideal.absNorm (P i).val:ℂ)^(-w))/idealClosedCorrection η (P i) x w z := by
  have hs (i : Fin K) : Supported (P i).val := outside_prime_supported S hS.bad (P i) (hPS i)
  rw [indexedCompensatedHigh_eq_spectral η S P hP hs 1 x w z]
  have ht : ∀Q∈Finset.univ.image P,Q.val∉S := by
    intro Q hQ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
    exact hPS i
  rw [spectral_principal_continued S hS (Finset.univ.image P) ht η x w z _ _ hx hw hz,
    Finset.prod_image hP.injOn]


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.spectral_principal_ratio_product

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.spectral_principal_continued

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.indexedCompensatedHigh_principal_continued
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.indexedCompensatedHigh_principal_continued
