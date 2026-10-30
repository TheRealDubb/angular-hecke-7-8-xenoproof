import AngularPhysicalDetectorLiteralInverseCount
import AngularPhysicalDetectorLiteralPaddedPlain

/- Common constants for the literal inverse/plain source counts. The height
degree is chosen before the angular character and its finite conductor;
the constant and threshold are chosen before the source label, selected
prime slots, rows and rowwise zero/frequency. Both branches use exactly
the same physical canonical-prime product. No energy or count hypothesis
and no angular 7/8 ceiling is imported into this statement. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff SchwartzMap
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows RelativePrime PhysicalDetectorInitial
open OAI.SevenEighths.Angular.Dyadic
open HeckeInverseAmplification (FreeRow)
open HeckeDetectorInverseFiberCount (inverseTest)
open HeckeDetectorDyadicProfiles (positiveAnnular)
local notation "O" => ActualEisensteinCubic.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local notation "Label" => Sum Bool (RayQuotient.Characters M H)

theorem literal_source_paired_counts
    (n : ℕ) (W : ℝ→ℂ) (lo hi bPhi epsm wmin : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbPhi : 2≤bPhi) (hepsm : 0<epsm) (hepsm1 : epsm≤1) (hwmin : 0<wmin)
    (Phi : 𝓢(ℝ,ℂ)) (hsPhi : Function.support (Phi:ℝ→ℂ)⊆Iic bPhi)
    (hpPhi : ∀x,0≤(Phi x).re) (hone : ∀x∈Icc (0:ℝ) 1,Phi x=1) :
    ∃J : ℕ,∀eta : AngularCharacter,eta.k= -(n:ℤ) →
      ∀S : Finset (Ideal O),∀hS : ∀P∈S,Prime P,
      CanonicalQuadraticSieve.fixedBadPrimes⊆S →
      M≤Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} →
      M≠⊤ → M≤Ideal.span {(72:O)} →
      ∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,1<U ∧
      ∀(selected : Finset Slot)(label : Label),
      ∀(w : selected→ℝ)(z : selected→ℂ)(height : ℝ),
        (∀i,wmin≤w i) → (∀i,w i≤PhysicalDetectorUniform.commonMesh 2 0 1 (epsm/2)) →
        (∀i,lo≤1-(z i).re) → (∀i,1-(z i).re≤hi) →
        0≤height → (∀i,|(z i).im|≤height) →
      ∀rows : Finset FreeRow,
        (∀u∈rows,initialKeep (SourceRows.sourceMomentData M H hH S hS eta label).η
          (internalQ M (SourceRows.sourceMomentData M H hH S hS eta label).η) u.val) →
        (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U) →
      ∀sigma freq : FreeRow→ℝ,(∀u∈rows,sigma u∈Icc (0:ℝ) 1) →
        (∀u∈rows,freq u∈Icc (-height) height) →
      ∀delta witnessLoss primeMass : ℝ,
        (∀u∈rows,U^primeMass≤
          ‖∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i)‖^2) →
      (∀r tstar : ℝ,0≤r → r+2*(∑i,w i)<1 → 2*r+8*(∑i,w i)<3 →
        (∀u∈rows,U^(delta*r-witnessLoss)≤
          ‖polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
            true (inverseTest U tstar r) (U^r) (sigma u) (freq u)‖^2) →
        (rows.card:ℝ)≤(C*(1+height)^J)*U^(1+epsm-delta*r-primeMass+witnessLoss)) ∧
      (∀m : ℝ,0≤m → m≤1 → 2*m+6*(3/4:ℝ)*(∑i,w i)≤1+epsm/2 →
        (∀u∈rows,U^(delta*m-witnessLoss)≤
          ‖polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
            false positiveAnnular (U^m) (sigma u) (freq u)‖^2) →
        (rows.card:ℝ)≤(C*(1+height)^J)*U^(1+epsm-2*delta*m-primeMass+2*witnessLoss)) := by
  have hinv (tag : Bool) := literal_source_inverse_count M H hH
    (if tag then n else 0) W lo hi epsm wmin hWs hW hepsm hwmin (Fintype.card Slot)
  have hplain (idx : Finset Slot×Bool) := literal_source_padded_plain_count
    (Slot:=idx.1) M H hH (if idx.2 then n else 0) W lo hi bPhi (epsm/2) (epsm/2) wmin
    hWs hW hbPhi (by linarith) (by linarith) (by linarith) hwmin Phi hsPhi hpPhi hone
  choose Ji hi using hinv
  choose Jp hp using hplain
  let J := (∑tag : Bool,Ji tag)+(∑idx : Finset Slot×Bool,Jp idx)
  refine ⟨J,?_⟩
  intro eta hk S hS hbad hMmask hMt hM72
  let data := SourceRows.sourceMomentData M H hH S hS eta
  let tag (label : Label) : Bool := if (data label).η.k=0 then false else true
  have ht (label : Label) : (data label).η.k=((if tag label then n else 0:ℕ):ℤ) := by
    have hh := SourceRows.sourceMomentData_nonnegative_types M H hH n S hS eta hk label
    by_cases hz : (data label).η.k=0
    · simp [tag,hz]
    · simpa only [tag,hz,ite_false,Bool.true_eq,ite_true] using hh.resolve_left hz
  have hta (label : Label) : (data label).η.k.natAbs=(if tag label then n else 0) := by
    rw [ht];exact Int.natAbs_natCast _
  choose Ci hCi hI using fun label=>hi (tag label) eta S hS hbad hMmask label (ht label)
  have hp' (idx : Finset Slot×Label) := hp (idx.1,tag idx.2) eta S hS hbad hMmask
    idx.2 (hta idx.2) M le_rfl
    (Ideal.inf_ne_bot_of_ne_bot (NeZero.ne M) (data idx.2).η.modulus_ne_bot)
    (ne_top_of_le_ne_top hMt inf_le_left) (inf_le_left.trans hM72)
  choose Cp hCp hP using hp'
  let C := 1+(∑label,Ci label)+(∑idx,Cp idx)
  have hi0 : 0≤∑label,Ci label := Finset.sum_nonneg (fun label _=>(hCi label).le)
  have hp0 : 0≤∑idx,Cp idx := Finset.sum_nonneg (fun idx _=>(hCp idx).le)
  have hC : 0<C := by dsimp [C];linarith
  have hCiC (label : Label) : Ci label≤C := by
    have hh := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset Label))=>(hCi k).le)
      (Finset.mem_univ label)
    dsimp [C];linarith
  have hCpC (idx : Finset Slot×Label) : Cp idx≤C := by
    have hh := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset (Finset Slot×Label)))=>(hCp k).le)
      (Finset.mem_univ idx)
    dsimp [C];linarith
  have hJi (label : Label) : Ji (tag label)≤J :=
    (Finset.single_le_sum (fun k _=>Nat.zero_le (Ji k)) (Finset.mem_univ (tag label))).trans
      (Nat.le_add_right _ _)
  have hJp (idx : Finset Slot×Label) : Jp (idx.1,tag idx.2)≤J :=
    (Finset.single_le_sum (fun k _=>Nat.zero_le (Jp k)) (Finset.mem_univ (idx.1,tag idx.2))).trans
      (Nat.le_add_left _ _)
  refine ⟨C,hC,?_⟩
  filter_upwards [Filter.eventually_all.2 hI,Filter.eventually_all.2 hP] with U hIU hPU
  refine ⟨(hIU (Sum.inl false)).1,?_⟩
  intro selected label w z height hw hwm hlo hhi hh hz rows hkeep hrows
    sigma freq hsigma hfreq delta witnessLoss primeMass hprime
  have hUp : 0<U := zero_lt_one.trans (hIU label).1
  have hscaleI : Ci label*(1+height)^(Ji (tag label))≤C*(1+height)^J :=
    mul_le_mul (hCiC label) (pow_le_pow_right₀ (by linarith) (hJi label)) (by positivity) hC.le
  have hscaleP : Cp (selected,label)*(1+height)^(Jp (selected,tag label))≤C*(1+height)^J :=
    mul_le_mul (hCpC (selected,label)) (pow_le_pow_right₀ (by linarith) (hJp (selected,label)))
      (by positivity) hC.le
  constructor
  · intro r tstar hr hcap1 hcap2 hspike
    have hK : Fintype.card selected≤Fintype.card Slot := Fintype.card_le_of_injective
      (Subtype.val : selected→Slot) Subtype.val_injective
    exact ((hIU label).2 hK w z hw hlo hhi r hr hcap1 hcap2 rows hrows
      tstar height hh sigma freq hsigma hfreq delta witnessLoss primeMass hspike hprime).trans
      (mul_le_mul_of_nonneg_right hscaleI (Real.rpow_nonneg hUp.le _))
  · intro m hm0 hm1 hcap hspike
    have hc := (hPU (selected,label)).2 w z height hw hwm hlo hhi hh hz
      m hm0 hm1 hcap rows hkeep hrows sigma freq hsigma hfreq
      delta witnessLoss primeMass hspike hprime
    have he : 1+epsm/2+epsm/2-2*delta*m-primeMass+2*witnessLoss=
        1+epsm-2*delta*m-primeMass+2*witnessLoss := by ring
    rw [he] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right hscaleP (Real.rpow_nonneg hUp.le _))

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_paired_counts
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_source_paired_counts
