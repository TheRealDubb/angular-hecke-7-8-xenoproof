import AngularPhysicalDetectorLiteralPrime
import AngularPhysicalDetectorFreePlain

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff SchwartzMap
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows PlainRows CommonMask RelativePrime PhysicalDetectorInitial
open OAI.SevenEighths.Angular.Dyadic
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentEnergyBands (length)
open HeckeDetectorRowwisePolynomial (logProfile)
open HeckeDetectorDyadicProfiles (positiveAnnular)
open HeckeInverseAmplification (FreeRow)
local notation "O" => ActualEisensteinCubic.O
attribute [local irreducible] AngularCharacter.idealHom naturalRow

variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- An actual ordinary marked moment for the literal final-probe dictionary
and canonical physical prime amplitudes. The degree precedes the target,
source exclusions, selected dictionary label and its conductor. No angular
7/8 premise or abstract moment/count estimate is assumed. Conductor avoidance
is an explicit coefficient gate, to be supplied at sufficiently large scale. -/
theorem literal_source_plain_moment
    (n : ℕ) (W : ℝ→ℂ) (lo hi bPhi delta eps : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbPhi : 2≤bPhi) (hdelta : 0<delta) (hdelta1 : delta≤1) (heps : 0<eps)
    (Phi : 𝓢(ℝ,ℂ)) (hsPhi : Function.support (Phi:ℝ→ℂ)⊆Iic bPhi)
    (hpPhi : ∀x,0≤(Phi x).re) (hone : ∀x∈Icc (0:ℝ) 1,Phi x=1) :
    ∃J : ℕ,∀eta : AngularCharacter,∀S : Finset (Ideal O),∀hS : ∀P∈S,Prime P,
      CanonicalQuadraticSieve.fixedBadPrimes⊆S →
      M≤Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} →
      ∀label : Sum Bool (RayQuotient.Characters M H),
      let base := (SourceRows.sourceMomentData M H hH S hS eta label).η
      base.k.natAbs=n →
      ∀Q : Ideal O,Q≤M → internalQ Q base≠0 → internalQ Q base≠⊤ →
        internalQ Q base≤Ideal.span {(72:O)} →
      ∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,1<U ∧
      ∀T : Finset Slot,∀(w : T→ℝ)(z : T→ℂ)(height : ℝ),
        (∀i,0≤w i) → (∀i,w i≤PhysicalDetectorUniform.commonMesh 2 0 1 eps) →
        (∀i,lo≤1-(z i).re) → (∀i,1-(z i).re≤hi) →
        0≤height → (∀i,|(z i).im|≤height) →
        (∀i,∀P∈primePool M H 2 (U^(w i)),
          W ((P.absNorm:ℝ)/(U^(w i)))≠0 → IsCoprime P base.modulus) →
      ∀j k : ℕ,j+k≤2 → ∀sigma∈Icc (0:ℝ) 1,∀freq∈Icc (-height) height,
      ∀X : ℝ,0<X → X≤U → 2*length U X+6*(3/4:ℝ)*(∑i,w i)≤1+delta →
      ∀rows : Finset FreeRow,(∀u∈rows,initialKeep base (internalQ Q base) u.val) →
        (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U) →
      (∑u∈rows,‖polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
          false ((logProfile^[j]) positiveAnnular) X sigma freq *
        polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
          false ((logProfile^[k]) positiveAnnular) X sigma freq *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i)‖^2) ≤
        C*(1+height)^J*U^(1+delta+eps) := by
  have hsW : Function.support (fun x=>conj (W x))⊆Icc (1:ℝ) 2 := by
    intro x hx
    apply hWs
    intro hz
    exact hx (by simp only [hz,map_zero])
  obtain ⟨J,hm⟩ := PhysicalDetectorJoint.actual_free_plain_energy (α:=Slot) M H hH n
    (fun x=>conj (W x)) 1 2 lo hi bPhi delta eps (by norm_num) hsW
    (Complex.conjCLE.contDiff.comp hW) (by norm_num) hbPhi hdelta hdelta1 heps
    Phi hsPhi hpPhi hone
  refine ⟨J,?_⟩
  intro eta S hS hbad hMmask label base hk Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hm base hk Q hQM hQ0 hQt hQ72 base rfl
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with U hU
  refine ⟨hU.1,?_⟩
  intro T w z height hw hwm hlo hhi hh hv hcop j k hjk sigma hsigma freq hfreq
    X hX hXU hcap rows hkeep hrows
  have he := hU.2 T (fun _=>1) w (fun i=>1-(z i).re) (fun i=>-(z i).im)
    height hw hwm hlo hhi hh (fun i=>by simpa only [abs_neg] using hv i)
    (ProbeHighRowFamily.sourceMomentReverse M H label) j k hjk sigma hsigma freq hfreq
    X hX hXU hcap rows hkeep hrows (fun _=>0) (fun _ _=>by simpa using hh)
  have hnorm (u : FreeRow) :
      ‖polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
          false ((logProfile^[j]) positiveAnnular) X sigma freq *
        polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
          false ((logProfile^[k]) positiveAnnular) X sigma freq *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i)‖ =
      ‖polynomial (if ProbeHighRowFamily.sourceMomentReverse M H label then
          (naturalCharacter base u.val).conjugate else naturalCharacter base u.val)
          false ((logProfile^[j]) positiveAnnular) X sigma freq *
        polynomial (if ProbeHighRowFamily.sourceMomentReverse M H label then
          (naturalCharacter base u.val).conjugate else naturalCharacter base u.val)
          false ((logProfile^[k]) positiveAnnular) X sigma freq *
        ∏i,naturalSlot (naturalCharacter base u.val) (primePool M H 2 (U^(w i)))
          (fun I=>(rayRelativeCharacter M H hH base 1).idealHom I *
            HeckePrimeAnnular.annularWeight (fun y=>conj (W y)) (U^(w i))
              (1-(z i).re) (-(z i).im) I) (U^(w i))‖ := by
    rw [literal_source_polynomial M H hH S hS hbad,
      literal_source_polynomial M H hH S hS hbad]
    simp only [norm_mul,norm_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [canonical_amplitude_relative_slot M H hH base u hMmask W 2
      (U^(w i)) (z i) (Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) _) (hcop i),
      RCLike.norm_conj]
  simp only [zero_add] at he
  rw [Finset.sum_congr rfl (fun u _=>congrArg (fun r:ℝ=>r^2) (hnorm u))]
  exact he

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_plain_moment
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_plain_moment
