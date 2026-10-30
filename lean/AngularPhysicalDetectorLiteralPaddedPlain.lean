import AngularPhysicalDetectorLiteralMoment
import AngularPhysicalDetectorPrimeCoprime
import AngularPhysicalDetectorPlainRowwise
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount

/- Actual canonical-prime marked counting with explicit plain-length
padding. This pays the supported witness's possible m>1/2. Empty slots
give the required unmarked estimate; nonempty slots retain the physical
amplitude gain. Retention is supplied by the actual nonfloor source gates.
No angular zero-free hypothesis or energy/count premise is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff SchwartzMap
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows RelativePrime PhysicalDetectorInitial
open OAI.SevenEighths.Angular.Dyadic
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentEnergyBands (length)
open HeckeDetectorRowwisePolynomial (logProfile)
open HeckeDetectorDyadicProfiles (positiveAnnular positiveAnnular_support)
open CenteredMomentSourceMass (idealBall mem_idealBall)
open HeckeInverseAmplification (FreeRow)
local notation "O" => ActualEisensteinCubic.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem literal_source_padded_plain_count
    (n : ℕ) (W : ℝ→ℂ) (lo hi bPhi pad eps wmin : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbPhi : 2≤bPhi) (hpad : 0<pad) (hpad1 : pad≤1)
    (heps : 0<eps) (hwmin : 0<wmin)
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
      ∀(w : Slot→ℝ)(z : Slot→ℂ)(height : ℝ),
        (∀i,wmin≤w i) → (∀i,w i≤PhysicalDetectorUniform.commonMesh 2 0 1 eps) →
        (∀i,lo≤1-(z i).re) → (∀i,1-(z i).re≤hi) →
        0≤height → (∀i,|(z i).im|≤height) →
      ∀m : ℝ,0≤m → m≤1 → 2*m+6*(3/4:ℝ)*(∑i,w i)≤1+pad →
      ∀rows : Finset FreeRow,
        (∀u∈rows,initialKeep base (internalQ Q base) u.val) →
        (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U) →
      ∀sigma freq : FreeRow→ℝ,(∀u∈rows,sigma u∈Icc (0:ℝ) 1) →
        (∀u∈rows,freq u∈Icc (-height) height) →
      ∀delta witnessLoss primeMass : ℝ,
        (∀u∈rows,U^(delta*m-witnessLoss)≤
          ‖polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
            false positiveAnnular (U^m) (sigma u) (freq u)‖^2) →
        (∀u∈rows,U^primeMass≤
          ‖∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i)‖^2) →
        (rows.card:ℝ)≤(C*(1+height)^J)*U^(1+pad+eps-2*delta*m-primeMass+2*witnessLoss) := by
  obtain ⟨J,hm⟩ := literal_source_plain_moment (Slot:=Slot) M H hH n W lo hi bPhi
    pad eps hWs hW hbPhi hpad hpad1 heps Phi hsPhi hpPhi hone
  refine ⟨J+1,?_⟩
  intro eta S hS hbad hMmask label base hk Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,hbound⟩ := hm eta S hS hbad hMmask label hk Q hQM hQ0 hQt hQ72
  have hlarge : ∀ᶠU : ℝ in atTop,(base.modulus.absNorm:ℝ)<U^wmin :=
    (tendsto_rpow_atTop hwmin).eventually (eventually_gt_atTop _)
  refine ⟨192*C,by positivity,?_⟩
  filter_upwards [hbound,hlarge] with U hU hlarge
  refine ⟨hU.1,?_⟩
  intro w z height hw hwm hlo hhi hh hz m hm0 hm1 hcap rows hkeep hrows
    sigma freq hsigma hfreq delta witnessLoss primeMass hspike hprime
  have hUp : 0<U := zero_lt_one.trans hU.1
  have hX : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hXU : U^m≤U := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU.1.le hm1
  have hlen : length U (U^m)=m := by
    rw [length,max_eq_right (Real.one_le_rpow hU.1.le hm0),Real.logb_rpow hUp hU.1.ne']
  have hcop (i : Slot) (P : Ideal O) (hp : P∈primePool M H 2 (U^(w i)))
      (hval : W ((P.absNorm:ℝ)/(U^(w i)))≠0) : IsCoprime P base.modulus :=
    angular_annular_prime_coprime base _ (Real.rpow_pos_of_pos hUp _)
      (hlarge.trans_le (Real.rpow_le_rpow_of_exponent_le hU.1.le (hw i))) W hWs P
      (Finset.mem_filter.mp hp).2.1 hval
  let family := fun u=>SourceRows.sourceDetectorFamily M H hH S hS eta u label
  let P : FreeRow→ℂ := fun u=>∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i)
  let energy : ℝ := (C*(1+height)^J)*U^(1+pad+eps)
  have henergy0 : 0≤energy := by dsimp [energy];positivity
  have hemom : ∀j k : ℕ,j+k≤2 → ∀s∈Icc (0:ℝ) 1,∀t∈Icc (-height) height,
      (∑u∈rows,‖polynomial (family u) false ((logProfile^[j]) positiveAnnular) (U^m) s t *
        polynomial (family u) false ((logProfile^[k]) positiveAnnular) (U^m) s t * P u‖^2)≤energy := by
    intro j k hjk s hs t ht
    have he := hU.2 Finset.univ (fun i=>w i.val) (fun i=>z i.val) height
      (fun i=>hwmin.le.trans (hw i.val)) (fun i=>hwm i.val)
      (fun i=>hlo i.val) (fun i=>hhi i.val) hh (fun i=>hz i.val)
      (fun i=>hcop i.val) j k hjk s hs t ht (U^m) hX hXU
      (by rw [hlen,Finset.sum_coe_sort];exact hcap) rows hkeep hrows
    have hprod (u : FreeRow) :
        (∏i : (Finset.univ : Finset Slot),
          HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i.val)) (z i.val))=P u :=
      Finset.prod_coe_sort Finset.univ (fun i : Slot=>
        HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i))
    simpa only [hprod,family,energy] using he
  have hcover : ∀I:Ideal O,I≠0 → positiveAnnular ((I.absNorm:ℝ)/(U^m))≠0 →
      I∈idealBall ((9/4)*(U^m)) := by
    intro I hI hi
    exact (mem_idealBall _ _).mpr ⟨hI,(div_le_iff₀ hX).mp (positiveAnnular_support hi).2⟩
  have hb := PhysicalDetectorPlain.plain_squared_rowwise rows family positiveAnnular (U^m) hX
    (idealBall ((9/4)*(U^m))) hcover P 0 1 (-height) height energy (by norm_num)
    (by linarith) henergy0 sigma freq hsigma hfreq hemom
  let A : ℝ := (192*C)*(1+height)^(J+1)
  have he : (∑u∈rows,‖polynomial (family u) false positiveAnnular (U^m) (sigma u) (freq u)*
      polynomial (family u) false positiveAnnular (U^m) (sigma u) (freq u)*P u‖^2)≤A*U^(1+pad+eps) := by
    apply hb.trans
    calc
      _≤192*(1+height)*energy := by nlinarith
      _=_ := by dsimp [A,energy];rw [pow_succ];ring
  have hsp : ∀u∈rows,U^(2*(delta*m-witnessLoss)+primeMass)≤
      ‖polynomial (family u) false positiveAnnular (U^m) (sigma u) (freq u)*
        polynomial (family u) false positiveAnnular (U^m) (sigma u) (freq u)*P u‖^2 := by
    intro u hu
    rw [show 2*(delta*m-witnessLoss)+primeMass=
      ((delta*m-witnessLoss)+(delta*m-witnessLoss))+primeMass by ring,
      Real.rpow_add hUp,Real.rpow_add hUp,norm_mul,norm_mul,mul_pow,mul_pow]
    exact mul_le_mul
      (mul_le_mul (hspike u hu) (hspike u hu) (Real.rpow_nonneg hUp.le _) (sq_nonneg _))
      (hprime u hu) (Real.rpow_nonneg hUp.le _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hc := HeckeDetectorRowCount.card_of_energy rows _ U
    (2*(delta*m-witnessLoss)+primeMass) (1+pad+eps) A hUp hsp he
  convert hc using 1 <;> dsimp only [A] <;> congr 2 <;> ring

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_padded_plain_count
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_padded_plain_count
