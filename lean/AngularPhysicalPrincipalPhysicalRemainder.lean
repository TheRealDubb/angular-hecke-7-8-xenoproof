import AngularPhysicalPrincipalPool
import AngularPhysicalPrincipalRemainderSaving
import AngularPhysicalPrincipalResidueNormalization

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalPrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss PhysicalPrincipalProducts
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem physical_principal_residue_remainder {K : ℕ}
    (angularCap : ℕ) (η : AngularCharacter) (horder : η.k.natAbs≤angularCap) (hk : η.k≠0) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : 7/8<(PhysicalZeroSupremum.beta angularCap)+e) (ha2 : (PhysicalZeroSupremum.beta angularCap)+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ell : Fin K→ℝ,(∑j,ell j)=1/6 → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0≤W j x ∧ W j x≤B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1≤Z → (∀j,480≤c*Z^(ell j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        PhysicalDetectorHigh.principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)-
      PhysicalPrincipalResidue.sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        ((PhysicalZeroSupremum.beta angularCap)+e) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
        (PhysicalDetectorHigh.globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)))‖≤
      C/e*Z^((PhysicalZeroSupremum.beta angularCap)-11/16-17/48000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := PhysicalPrincipalRemainderBounds.source_remainders_strict_saving angularCap η horder hk S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0<Z := by linarith
  have hb := hbound ell hell W (fun j _=>hW j) (fun j _=>hsupp j) T (fun j _ p hp=>hT j p hp)
    Z hZ (fun j _=>hthreshold j) (fun j _=>hmod j)
  dsimp only at hb
  have heq := principal_physical_pool_ordered angularCap η horder hk S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(ell j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z ((PhysicalZeroSupremum.beta angularCap)+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral ((PhysicalZeroSupremum.beta angularCap)+e) F=
      verticalIntegral ((PhysicalZeroSupremum.beta angularCap)+e) (fun s=>fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold PhysicalPrincipalResidue.sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _≤(2*C)/e*Z^((PhysicalZeroSupremum.beta angularCap)-11/16-17/48000)
  apply hn.trans
  have hCe : C≤C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0≤Z^((PhysicalZeroSupremum.beta angularCap)-11/16-17/48000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith

end OAI.SevenEighths.Angular.PhysicalPrincipalPhysical

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalPhysical.physical_principal_residue_remainder
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalPrincipalPhysical.physical_principal_residue_remainder
