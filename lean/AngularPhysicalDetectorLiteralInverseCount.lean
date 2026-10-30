import AngularPhysicalDetectorLiteralInverse
import AngularRowwiseMarked

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open OAI.SevenEighths.Angular.Dyadic
open HeckeInverseAmplification (FreeRow)
open HeckeDetectorRowwisePolynomial (logProfile)
open HeckeDetectorInverseFiberCount (inverseTest)
open CenteredMomentSourceMass (idealBall mem_idealBall)
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The inverse branch of the actual source count, with sigma and height
chosen separately for each row. Only the literal detector/prime spikes are
premises; the energy and conductor-avoidance estimates are supplied inside.
This is the ordinary inverse branch, not the missing joint affine bound. -/
theorem literal_source_inverse_count
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
      ∀tstar height : ℝ,0≤height → ∀sigma freq : FreeRow→ℝ,
        (∀u∈rows,sigma u∈Icc (0:ℝ) 1) → (∀u∈rows,freq u∈Icc (-height) height) →
      ∀delta witnessLoss primeMass : ℝ,
        (∀u∈rows,U^(delta*r-witnessLoss)≤
          ‖polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
            true (inverseTest U tstar r) (U^r) (sigma u) (freq u)‖^2) →
        (∀u∈rows,U^primeMass≤
          ‖∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i)‖^2) →
        (rows.card:ℝ)≤(C*(1+height)^J)*U^(1+eps-delta*r-primeMass+witnessLoss) := by
  obtain ⟨J,hm⟩ := literal_source_inverse_moment M H hH n W lo hi eps wmin
    hWs hW heps hwmin K
  refine ⟨J+1,?_⟩
  intro eta S hS hbad hMmask label hk
  obtain ⟨C,hC,hbound⟩ := hm eta S hS hbad hMmask label hk
  refine ⟨12*C,by positivity,?_⟩
  filter_upwards [hbound] with U hU
  refine ⟨hU.1,?_⟩
  intro Slot inst dec hK w z hw hlo hhi r hr hcap1 hcap2 rows hrows
    tstar height hh sigma freq hsigma hfreq delta witnessLoss primeMass hspike hprime
  have hUp : 0<U := zero_lt_one.trans hU.1
  have hD : 0<U^r := Real.rpow_pos_of_pos hUp _
  let family := fun u=>SourceRows.sourceDetectorFamily M H hH S hS eta u label
  let P : FreeRow→ℂ := fun u=>∏i,HeckePrimeRow.canonicalPrimeAmplitude
    M H u.val W 2 (U^(w i)) (z i)
  let E : ℝ := (C*(1+height)^J)*U^(1+eps)
  have hE : 0≤E := by dsimp [E];positivity
  have hs : Function.support (inverseTest U tstar r)⊆Icc (1/4:ℝ) (9/4) :=
    HeckeDetectorDyadicActual.inverse_profile_support (U^tstar) (U^r)
  have hcover : ∀I:Ideal O,I≠0 → inverseTest U tstar r ((I.absNorm:ℝ)/(U^r))≠0 →
      I∈idealBall ((9/4)*(U^r)) := by
    intro I hI hi
    exact (mem_idealBall _ _).mpr ⟨hI,(div_le_iff₀ hD).mp (hs hi).2⟩
  have he := hU.2 hK w z hw hlo hhi r hr hcap1 hcap2 rows hrows tstar
  have hb := RowwiseMarked.marked_rowwise rows family true (inverseTest U tstar r)
    (U^r) hD (idealBall ((9/4)*(U^r))) hcover P 0 1 (-height) height E
    (by norm_num) (by linarith) sigma freq hsigma hfreq
    (by simpa only [Function.iterate_zero,id_eq] using fun s hs t ht=>he 0 (by norm_num) s hs height t hh ht)
    (by simpa only [Function.iterate_succ_apply,Function.iterate_zero,id_eq] using
      fun s hs t ht=>he 1 (by norm_num) s hs height t hh ht)
    (by simpa only [Function.iterate_succ_apply,Function.iterate_zero,id_eq] using
      fun s hs t ht=>he 2 (by norm_num) s hs height t hh ht)
  have henergy : (∑u∈rows,‖polynomial (family u) true (inverseTest U tstar r)
      (U^r) (sigma u) (freq u)*P u‖^2)≤((12*C)*(1+height)^(J+1))*U^(1+eps) := by
    apply hb.trans
    calc
      _≤12*(1+height)*E := by nlinarith
      _=_ := by dsimp [E];rw [pow_succ];ring
  have hsp : ∀u∈rows,U^((delta*r-witnessLoss)+primeMass)≤
      ‖polynomial (family u) true (inverseTest U tstar r) (U^r) (sigma u) (freq u)*P u‖^2 := by
    intro u hu
    rw [Real.rpow_add hUp,norm_mul,mul_pow]
    exact mul_le_mul (hspike u hu) (hprime u hu) (Real.rpow_nonneg hUp.le _) (sq_nonneg _)
  have hc := HeckeDetectorRowCount.card_of_energy rows _ U
    ((delta*r-witnessLoss)+primeMass) (1+eps) ((12*C)*(1+height)^(J+1)) hUp hsp henergy
  convert hc using 1 <;> congr 2 <;> ring

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_inverse_count
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_inverse_count
