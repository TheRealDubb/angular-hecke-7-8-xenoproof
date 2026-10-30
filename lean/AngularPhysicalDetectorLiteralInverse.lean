import AngularPhysicalDetectorLiteralPrime
import AngularPhysicalDetectorPrimeCoprime
import AngularPhysicalDetectorAnnularPool
import AngularPhysicalDetectorRowHeightInverse
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySupport
import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryProfiles
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows CommonMask RelativePrime InverseRows CubicEisenstein.AngularRawCoefficientGates
open OAI.SevenEighths.Angular.Dyadic
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentDetectorDictionary (annular_prime_coprime oriented_logTest logTest_eq_iterate)
open HeckeDetectorRowwisePolynomial (logProfile)
open HeckeDetectorInverseFiberCount (inverseTest)
open HeckeDetectorCoefficientTransfer (orientedProfile orientedFrequency orientedFrequency_abs)
open HeckeInverseAmplification (FreeRow)
open ProbeHighRowFamily (momentElement)
open PhysicalDetectorJoint (annularPool annularPool_subset annularPool_ratio naturalSlot_annular_filter)
local notation "O" => ActualEisensteinCubic.O
attribute [local irreducible] AngularCharacter.idealHom naturalRow

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Actual marked inverse energy for the literal final-detector family and
its canonical physical prime amplitudes. The conductor gates are supplied
internally at every width >= wmin. The degree precedes the target conductor;
there is no angular zero-free hypothesis or retained-row assumption. -/
theorem literal_source_inverse_moment
    (n : ℕ) (W : ℝ→ℂ) (lo hi eps wmin : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (heps : 0<eps) (hwmin : 0<wmin) (K : ℕ) :
    ∃J : ℕ,∀eta : AngularCharacter,∀S : Finset (Ideal O),∀hS : ∀P∈S,Prime P,
      CanonicalQuadraticSieve.fixedBadPrimes⊆S →
      M≤Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} →
      ∀label : Sum Bool (RayQuotient.Characters M H),
      (SourceRows.sourceMomentData M H hH S hS eta label).η.k=(n:ℤ) →
      ∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,1<U ∧
      ∀{Slot : Type} [Fintype Slot] [DecidableEq Slot],Fintype.card Slot≤K →
      ∀(w : Slot→ℝ)(z : Slot→ℂ),
        (∀i,wmin≤w i) → (∀i,lo≤1-(z i).re) → (∀i,1-(z i).re≤hi) →
      ∀r : ℝ,0≤r → r+2*(∑i,w i)<1 → 2*r+8*(∑i,w i)<3 →
      ∀rows : Finset FreeRow,(∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U) →
      ∀tstar : ℝ,∀k : ℕ,k≤2 → ∀sigma∈Icc (0:ℝ) 1,
      ∀height freq : ℝ,0≤height → freq∈Icc (-height) height →
      (∑u∈rows,‖polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
          true ((logProfile^[k]) (inverseTest U tstar r)) (U^r) sigma freq *
        ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i)‖^2) ≤
        (C*(1+height)^J)*U^(1+eps) := by
  have hsW : Function.support (fun x=>conj (W x))⊆Icc (1:ℝ) 2 := by
    intro x hx
    apply hWs
    intro hz
    exact hx (by simp only [hz,map_zero])
  obtain ⟨J,hm⟩ := PhysicalDetectorDirectInverse.annular_rowwise_inverse_marked_energy n
    (fun x=>conj (W x)) lo hi eps hsW (Complex.conjCLE.contDiff.comp hW) heps K
  refine ⟨J,?_⟩
  intro eta S hS hbad hMmask label hk
  let data := SourceRows.sourceMomentData M H hH S hS eta label
  let base := data.η
  obtain ⟨C,U0,hC,hU0,hbound⟩ := hm data hk
  have hlarge : ∀ᶠU : ℝ in atTop,
      (base.modulus.absNorm:ℝ)+((deletedBase data).modulus.absNorm:ℝ)<U^wmin :=
    (tendsto_rpow_atTop hwmin).eventually (eventually_gt_atTop _)
  refine ⟨C,hC,?_⟩
  filter_upwards [hlarge,eventually_ge_atTop U0] with U hlarge hU0le
  have hU : 1<U := hU0.trans_le hU0le
  have hUp : 0<U := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro Slot inst dec hK w z hw hlo hhi r hr hcap1 hcap2 rows hrows
    tstar k hk2 sigma hsigma height freq hh hfreq
  have hP (i : Slot) : 0<U^(w i) := Real.rpow_pos_of_pos hUp _
  have hlarge' (i : Slot) :
      (base.modulus.absNorm:ℝ)<U^(w i) ∧ ((deletedBase data).modulus.absNorm:ℝ)<U^(w i) := by
    have he := hlarge.trans_le (Real.rpow_le_rpow_of_exponent_le hU.le (hw i))
    have hb : (0:ℝ)≤base.modulus.absNorm := by positivity
    have hd : (0:ℝ)≤(deletedBase data).modulus.absNorm := by positivity
    constructor <;> linarith
  have hcop (i : Slot) (P : Ideal O) (hp : P∈primePool M H 2 (U^(w i)))
      (hval : W ((P.absNorm:ℝ)/(U^(w i)))≠0) : IsCoprime P base.modulus :=
    angular_annular_prime_coprime base _ (hP i) (hlarge' i).1 W hWs P
      (Finset.mem_filter.mp hp).2.1 hval
  let L := fun i=>annularPool (primePool M H 2 (U^(w i))) (U^(w i))
  have hnorm (v : NonzeroElement) (hv : v∈rows.image momentElement) :
      ‖ConcreteTraceCRT.eisEmbedding v.val‖^2≤U := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    simpa only [momentElement,ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] using hrows u hu
  have hfreq' : orientedFrequency (ProbeHighRowFamily.sourceMomentReverse M H label) freq∈
      Icc (-height) height := by
    apply abs_le.mp
    rw [orientedFrequency_abs]
    exact abs_le.mpr hfreq
  have he := hbound U hU0le hK L w (fun i=>hwmin.le.trans (hw i))
    (fun i P hp=>(Finset.mem_filter.mp (annularPool_subset _ _ hp)).2.1)
    (fun i P hp=>annularPool_ratio _ _ P hp) (fun i=>(hlarge' i).2)
    base (fun _=>rayRelativeCharacter M H hH base 1)
    (fun i=>1-(z i).re) (fun i=>-(z i).im) (fun _=>0) hlo hhi
    r hr hcap1 hcap2 (rows.image momentElement) hnorm tstar
    (ProbeHighRowFamily.sourceMomentReverse M H label) k hk2 sigma hsigma
    height (orientedFrequency (ProbeHighRowFamily.sourceMomentReverse M H label) freq)
    hh hfreq' (fun _ _=>by simpa using hh)
  have hinj : Function.Injective (momentElement : FreeRow → NonzeroElement) := by
    intro u v huv
    apply Subtype.ext
    exact congrArg (fun x : NonzeroElement => x.val) huv
  rw [Finset.sum_image hinj.injOn] at he
  simp only [zero_add,PhysicalDetectorDirectInverse.idealCoeff] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  rw [norm_mul,norm_mul,SourceRows.source_family_moment_norm M H hH S hS hbad eta u label
    true ((logProfile^[k]) (inverseTest U tstar r)) (U^r) sigma freq
    (Real.rpow_pos_of_pos hUp _),oriented_logTest,logTest_eq_iterate]
  congr 1
  simp only [norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  change ‖HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i)‖ =
    ‖naturalSlot (naturalRow base u.val u.property.1).character (L i)
      (fun I=>(rayRelativeCharacter M H hH base 1).idealHom I*
        HeckePrimeAnnular.annularWeight (fun x=>conj (W x)) (U^(w i))
          (1-(z i).re) (-(z i).im) I) (U^(w i))‖
  rw [naturalSlot_annular_filter _ _ _ _ hsW,
    ←naturalCharacter_eq base u.val u.property.1,
    canonical_amplitude_relative_slot M H hH base u hMmask W 2 (U^(w i)) (z i) (hP i) (hcop i),
    RCLike.norm_conj]

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_inverse_moment
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_inverse_moment
