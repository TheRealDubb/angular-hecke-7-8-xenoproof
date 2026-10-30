import AngularPhysicalAmplifiedRadicalFamily
import OAI.NumberTheory.DirichletL.Energy.FirstLowHomogeneousPowers
noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace OAI.SevenEighths.Angular.FirstColumnScalar
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentSecondHeightFamily CenteredMomentCompleteCommon
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentFirstMixedNormalization CenteredMomentFirstMixedNormalizationActual CenteredMomentFirstMixedAllowance
open CenteredMomentFirstAmplifiedFourCoefficients CenteredMomentFirstCommonReferencePower
open CenteredMomentEnergyFirstGaussianCoefficients CenteredMomentSecondChildPowerBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFiniteProfileExceptional
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O
local notation "Ray"=>RayFourExpansion.RayCharacter

open CenteredMomentEnergyFirstHighGaussianUniformPowers


/-- Used only in statements whose character arguments occur through `.modulus`. -/
def modulusCarrier (χ:AngularCharacter):HeckeFamily.Character:=
  HeckeFamily.Character.ofResidue χ.modulus χ.modulus_ne_bot 1
    (fun u=>MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk χ.modulus)))
@[simp] lemma modulusCarrier_modulus (χ:AngularCharacter):
    (modulusCarrier χ).modulus=χ.modulus:=rfl

theorem actual_low_homogeneous_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:AngularCharacter)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mdecl)
    (hlow:Real.logb Z V≤5*Mdecl/6)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:1≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)
    (F seed Bcommon:ℝ)(srcLoss:Fin 4→ℝ)(hF:0≤F)(hseed:0<seed)(heps1:eps≤1)
    (hncap:(C.absNorm:ℝ)≤Z^Bcommon)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed)
    (rmain:ℝ)
    (rerror:elementPool (primePool M Hray Sbad (1/2) 1 (Z^(sigma/3)))→Fin 3→Ray→ℝ):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (rerror p i χ) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (upper^N*(56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ)))*F/seed)*
        Z^(Mdecl-M0+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+lossVector sigma delta reserve paid eps Mcap saving j)  :=by
  exact CenteredMomentEnergyFirstLowHomogeneousPowers.actual_low_homogeneous_four_powers
    M Hray Sbad hbad (modulusCarrier η) (modulusCarrier τ) C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hlow hloss hMamp hcard hmod
    upper N hupper H hH F seed Bcommon srcLoss hF hseed heps1 hncap hbound rmain rerror

theorem actual_high_homogeneous_four_powers
    (M:Ideal O)[NeZero M](Hray:Subgroup (O⧸M)ˣ)(Sbad:Finset (Ideal O))
    (hbad:fixedBadPrimes⊆Sbad)
    (η τ:AngularCharacter)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:primeSupport C=primeSupport D)(E:Finset (CommonIndex C D))
    (K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss:ℝ)
    (hK:0<K)(hV:0<V)(hZ:1<Z)(hs:0<sigma)(heps:0≤eps)(hM:0≤Mdecl)
    (hcap:Mdecl≤Mcap)(hactual:Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)≤Mwidth)(hwidth:Mwidth≤Mdecl)
    (hlow:Real.logb Z V≤Mdecl)(hloss:0≤primeLoss)(hMamp:0≤Mamp)
    (hcard:Z^(sigma/3-primeLoss)≤(primePool M Hray Sbad (1/2) 1 (Z^(sigma/3))).card)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (upper:ℝ)(N:ℕ)(hupper:1≤upper)
    (H:Fin 4→ℝ)(hH:∀j,0≤H j)
    (F seed Bcommon:ℝ)(srcLoss:Fin 4→ℝ)(hF:0≤F)(hseed:0<seed)(heps1:eps≤1)
    (hncap:(C.absNorm:ℝ)≤Z^Bcommon)
    (hbound:∀j,H j≤F*Z^(srcLoss j)/seed):
    let P:=primePool M Hray Sbad (1/2) 1 (Z^(sigma/3));
    let M0:=Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ);
    let K0:=nominalLog C D (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K V Z;
    let Kmain:=mainCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve;
    let Kerror:=fun (p:elementPool P)(i:Fin 3)(_:Ray)=>
      errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ)) K0
        (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve p (errorIndex i+1);
    let alpha:=CenteredMomentSecondChildPowerBudget.powers eps;
    let amain:=fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain (sigma/3)
      (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)) j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z (Kerror p i χ)
        (Mdecl-M0) paid saving (Mwidth/4-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z (errorIndex i+1)) j;
    (∑j:Fin 4,normalizedPower upper V (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ) Z
      (allowance C D Z) eps
      (sourceCoefficients P ((Mamp+2*sigma)/(sigma/6)) amain aerror alpha j) N (alpha j))≤
      (upper^N*(56*((Mamp+2*sigma)/(sigma/6)+1872*(Fintype.card Ray:ℝ)))*F/seed)*
        Z^(Mdecl-M0+eps*Bcommon+primeLoss)*
        ∑j:Fin 4,Z^(srcLoss j+lossVector sigma delta reserve paid eps Mcap saving j)  :=by
  exact CenteredMomentEnergyFirstHighGaussianUniformPowers.actual_high_homogeneous_four_powers
    M Hray Sbad hbad (modulusCarrier η) (modulusCarrier τ) C D hC hD hCD E
    K V Z sigma delta reserve paid eps saving Mdecl Mwidth Mcap Mamp primeLoss
    hK hV hZ hs heps hM hcap hactual hwidth hlow hloss hMamp hcard hmod
    upper N hupper H hH F seed Bcommon srcLoss hF hseed heps1 hncap hbound

end OAI.SevenEighths.Angular.FirstColumnScalar

#print axioms OAI.SevenEighths.Angular.FirstColumnScalar.actual_low_homogeneous_four_powers
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstColumnScalar.actual_low_homogeneous_four_powers

#print axioms OAI.SevenEighths.Angular.FirstColumnScalar.actual_high_homogeneous_four_powers
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.FirstColumnScalar.actual_high_homogeneous_four_powers
