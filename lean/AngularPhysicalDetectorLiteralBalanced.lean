import AngularPhysicalDetectorLiteralPairedCounts
import AngularPhysicalDetectorPhysicalCount
import OAI.NumberTheory.DirichletL.Hecke.DetectorBranchBudget
import OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection

/- The pinned ordinary balanced count, now for the actual angular source
dictionary. All four analytic count branches are supplied internally.
The remaining premises are the literal same-row spikes, their joint length
geometry, retention and the physical prime-amplitude bins. In particular
there is no prior angular 7/8 bound or moment/count premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff SchwartzMap
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows RelativePrime PhysicalDetectorInitial
open OAI.SevenEighths.Angular.Dyadic
open HeckeInverseAmplification (FreeRow)
open HeckeDetectorInverseFiberCount (inverseTest)
open HeckeDetectorDyadicProfiles (positiveAnnular)
open HeckeDetectorPhysicalSelection HeckeDetectorRowCount HeckeDetectorBranchBudget
local notation "O" => ActualEisensteinCubic.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local notation "Label" => Sum Bool (RayQuotient.Characters M H)

theorem literal_balanced_spike_count
    (n : ℕ) (W : ℝ→ℂ) (lo hi bPhi epsm wmin : ℝ)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbPhi : 2≤bPhi) (hepsm : 0<epsm) (hepsm1 : epsm≤1) (hwmin : 0<wmin)
    (Phi : 𝓢(ℝ,ℂ)) (hsPhi : Function.support (Phi:ℝ→ℂ)⊆Iic bPhi)
    (hpPhi : ∀x,0≤(Phi x).re) (hone : ∀x∈Icc (0:ℝ) 1,Phi x=1)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (alo bhi B : ℝ) (halo : 0<alo) (hab : alo≤bhi) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo alo bhi) (hφB : ∀y,φ y≤B) :
    ∃J : ℕ,∀eta : AngularCharacter,eta.k= -(n:ℤ) →
      ∀S : Finset (Ideal O),∀hS : ∀P∈S,Prime P,
      CanonicalQuadraticSieve.fixedBadPrimes⊆S →
      M≤Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask} →
      M≠⊤ → M≤Ideal.span {(72:O)} →
      ∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,1<U ∧
      ∀(slots : Finset Slot)(label : Label)(w g : Slot→ℝ)(z : Slot→ℂ),
      ∀height mesh binWidth delta eps nu tstar r m : ℝ,
        (∀i∈slots,wmin≤w i) → (∀i∈slots,w i≤mesh) →
        mesh≤PhysicalDetectorUniform.commonMesh 2 0 1 (epsm/2) → 0≤mesh →
        (∀i∈slots,lo≤1-(z i).re) → (∀i∈slots,1-(z i).re≤hi) →
        0≤height → (∀i∈slots,|(z i).im|≤height) →
        0<binWidth → 7/37≤∑i∈slots,w i →
        0<delta → delta≤5/6 → 0≤eps → eps≤1/1000 → eps≤epsm/300 →
        0<nu → 1≤tstar → tstar≤3/2 → 0≤r → r≤2 → 0≤m → m≤1/2+75*eps →
        tstar-r-eps≤m → r≤tstar+eps →
      ∀rows : Finset FreeRow,rows.Nonempty →
        (∀u∈rows,initialKeep (SourceRows.sourceMomentData M H hH S hS eta label).η
          (internalQ M (SourceRows.sourceMomentData M H hH S hS eta label).η) u.val) →
        (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤U) →
      ∀sigma freq : FreeRow→ℝ,(∀u∈rows,sigma u∈Icc (0:ℝ) 1) →
        (∀u∈rows,freq u∈Icc (-height) height) →
        (∀u∈rows,U^(delta*r-2*eps)≤
          ‖polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
            true (inverseTest U tstar r) (U^r) (sigma u) (freq u)‖^2) →
        (∀u∈rows,U^(delta*m-2*eps)≤
          ‖polynomial (SourceRows.sourceDetectorFamily M H hH S hS eta u label)
            false positiveAnnular (U^m) (sigma u) (freq u)‖^2) →
        (∀u∈rows,∀i∈slots,HeckePrimeAmplitudeBins.amplitude (U^(w i)) (delta/2) binWidth
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i))=g i) →
        (rows.card:ℝ)≤(C*(1+height)^J)*U^(
          max (shortExponent delta (weightedMean slots w g/delta) tstar) (longExponent delta tstar)
            +159*eps+epsm+mesh+7*nu) := by
  obtain ⟨Jp,hp⟩ := literal_source_paired_counts (Slot:=Slot) M H hH n W lo hi bPhi epsm wmin
    hWs hW hbPhi hepsm hepsm1 hwmin Phi hsPhi hpPhi hone
  have hiraw (tag : Bool) := PhysicalDetectorCount.physical_inverse_count
    (if tag then n else 0) M H hH ∅ φ hφ hφc hφp hφ0 hφne
    alo bhi B halo hab hB hφs hφB 2 epsm (by norm_num) hepsm
  choose Ji Ui hUi hi using hiraw
  let J := Jp+∑tag : Bool,Ji tag
  refine ⟨J,?_⟩
  intro eta hk S hS hbad hMmask hMt hM72
  obtain ⟨Cp,hCp,hP⟩ := hp eta hk S hS hbad hMmask hMt hM72
  let data := SourceRows.sourceMomentData M H hH S hS eta
  let tag (label : Label) : Bool := if (data label).η.k=0 then false else true
  have ht (label : Label) : (data label).η.k=((if tag label then n else 0:ℕ):ℤ) := by
    have hh := SourceRows.sourceMomentData_nonnegative_types M H hH n S hS eta hk label
    by_cases hz : (data label).η.k=0
    · simp [tag,hz]
    · simpa only [tag,hz,ite_false,Bool.true_eq,ite_true] using hh.resolve_left hz
  choose Ci hCi hI using fun label=>hi (tag label) (data label) (ht label)
  let C := Cp+∑label,Ci label
  have hsum : 0≤∑label,Ci label := Finset.sum_nonneg (fun label _=>(hCi label).le)
  have hC : 0<C := by dsimp [C];linarith
  have hCiC (label : Label) : Ci label≤C := by
    have hh := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset Label))=>(hCi k).le)
      (Finset.mem_univ label)
    dsimp [C];linarith
  have hJi (label : Label) : Ji (tag label)≤J :=
    (Finset.single_le_sum (fun k _=>Nat.zero_le (Ji k)) (Finset.mem_univ (tag label))).trans
      (Nat.le_add_left _ _)
  refine ⟨C,hC,?_⟩
  filter_upwards [hP,eventually_ge_atTop (max (Ui false) (Ui true))] with U hPU hUraw
  refine ⟨hPU.1,?_⟩
  intro slots label w g z height mesh binWidth delta eps nu tstar r m
    hw hwm hmesh hmesh0 hlo hhi hh hz hbin hsupply hd hd1 he he1 hepad
    hnu hts hts1 hr hr2 hm hmmax hleft hright rows hne hkeep hrows
    sigma freq hsigma hfreq hspikeI hspikeP hbins
  have hUp : 0<U := zero_lt_one.trans hPU.1
  let A := C*(1+height)^J
  let loss := commonLoss eps epsm mesh nu
  let q := weightedMean slots w g
  let x := q/delta
  have hA : 0<A := by dsimp [A];positivity
  have hL : 0<∑i∈slots,w i := by linarith
  have hwpos (i : Slot)(hi : i∈slots) : 0<w i := hwmin.trans_le (hw i hi)
  obtain ⟨u0,hu0⟩ := hne
  have hg (i : Slot)(hi : i∈slots) : 0≤g i ∧ g i≤delta/2 := by
    rw [←hbins u0 hu0 i hi]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)
  obtain ⟨hq0,hq1⟩ := weightedMean_bounds slots w g delta (fun i hi=>(hwpos i hi).le) hL hg
  have hx : 0≤x := div_nonneg hq0 hd.le
  have hx1 : x≤1/2 := (div_le_iff₀ hd).mpr (by dsimp [q];linarith)
  have hqx : delta*x=q := by dsimp [x];field_simp
  have hdle : delta≤1 := by linarith
  have hscaleP : Cp*(1+height)^Jp≤A :=
    mul_le_mul (by dsimp [C];linarith)
      (pow_le_pow_right₀ (by linarith) (Nat.le_add_right _ _)) (by positivity) hC.le
  have hscaleI : Ci label*(1+height)^(Ji (tag label))≤A :=
    mul_le_mul (hCiC label) (pow_le_pow_right₀ (by linarith) (hJi label)) (by positivity) hC.le
  have promote (p e : ℝ) (hb : (rows.card:ℝ)≤Cp*(1+height)^Jp*U^p) (he : p≤e) :
      (rows.card:ℝ)≤A*U^e := hb.trans (mul_le_mul hscaleP
        (Real.rpow_le_rpow_of_exponent_le hPU.1.le he) (Real.rpow_nonneg hUp.le _) hA.le)
  have hUi' : Ui (tag label)≤U := by
    cases tag label
    · exact (le_max_left _ _).trans hUraw
    · exact (le_max_right _ _).trans hUraw
  have hi0 := (hI label U r delta eps rows
    (fun u=>SourceRows.sourceDetectorFamily M H hH S hS eta u label)
    (ProbeHighRowFamily.sourceMomentReverse M H label) tstar height sigma freq
    hUi' hr hr2 hh hrows hsigma hfreq
    (fun u _ I=>SourceRows.source_family_moment_coeff M H hH S hS hbad eta u label I) hspikeI).1
  have hI0 : (rows.card:ℝ)≤A*U^(max 1 ((1+5*r)/6)-delta*r+loss) := by
    apply hi0.trans
    apply mul_le_mul hscaleI (Real.rpow_le_rpow_of_exponent_le hPU.1.le ?_)
      (Real.rpow_nonneg hUp.le _) hA.le
    exact no_slot_inverse_loss r delta eps epsm mesh nu he hmesh0 hnu.le
  have hm1 : m≤1 := by linarith
  have hmcap : 2*m≤1+epsm/2 := by linarith
  have hp0 := (hPU.2 (∅:Finset Slot) label (fun i=>w i.val) (fun i=>z i.val) height
    (by simp) (by simp) (by simp) (by simp) hh (by simp) rows hkeep hrows sigma freq hsigma hfreq
    delta (2*eps) 0 (by intro u hu;simp)).2 m hm hm1 (by simpa using hmcap) hspikeP
  have hP0 : (rows.card:ℝ)≤A*U^(1-2*delta*m+loss) := by
    apply promote _ _ hp0
    dsimp [loss,commonLoss];linarith
  have select (v : ℝ) (hv : 0≤v) (hv1 : v≤7/37) :
      ∃selected : Finset Slot,selected⊆slots ∧ (∑i∈selected,w i)≤v ∧
      ∀u∈rows,U^(2*q*v-delta*mesh)≤
        ‖∏i∈selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i)‖^2 := by
    obtain ⟨selected,hsub,hpos,hlen,hsp⟩ := select_physical_product M H rows ⟨u0,hu0⟩ slots
      (fun u : FreeRow=>u.val) (fun _=>W) (fun _=>2) w g z U delta mesh binWidth v
      hPU.1 hd.le hmesh0 hbin hwpos hwm hL hv (hv1.trans hsupply) hbins
    exact ⟨selected,hsub,hlen,hsp⟩
  have paired (selected : Finset Slot) (hsub : selected⊆slots) (mass : ℝ)
      (hprime : ∀u∈rows,U^mass≤
        ‖∏i∈selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i)‖^2) :=
    hPU.2 selected label (fun i=>w i.val) (fun i=>z i.val) height
      (fun i=>hw i.val (hsub i.property)) (fun i=>(hwm i.val (hsub i.property)).trans hmesh)
      (fun i=>hlo i.val (hsub i.property)) (fun i=>hhi i.val (hsub i.property)) hh
      (fun i=>hz i.val (hsub i.property)) rows hkeep hrows sigma freq hsigma hfreq
      delta (2*eps) mass (by
        intro u hu
        have hprod : (∏i : selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2
            (U^(w i.val)) (z i.val))=
            ∏i∈selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i) :=
          Finset.prod_coe_sort selected (fun i : Slot=>
            HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w i)) (z i))
        rw [hprod]
        exact hprime u hu)
  have hI : 23/37≤r → r<1 → nu<(1-r)/2 →
      (rows.card:ℝ)≤A*U^(inverseExponent delta x r+loss) := by
    intro hrlo hr1 hv
    obtain ⟨hv0,hv1,hcap1,hcap2⟩ := inverse_requested_capacity r nu hrlo hr1 hnu hv
    obtain ⟨selected,hsub,hlen,hprime⟩ := select ((1-r)/2-nu) hv0 hv1
    have hc := (paired selected hsub _ hprime).1 r tstar hr
      (by rw [Finset.sum_coe_sort];linarith) (by rw [Finset.sum_coe_sort];linarith) hspikeI
    apply promote _ _ hc
    have hl := inverse_marked_loss r delta x eps epsm mesh nu hd.le hdle hx hx1 he hmesh0 hnu.le
    rw [hqx] at hl
    dsimp only [loss] at *
    linarith only [hl]
  have hP : r≤crossing x tstar → m<1/2 → nu<(1-2*m)/(9/2+12*(0:ℝ)) →
      (rows.card:ℝ)≤A*U^(1-2*delta*m-2*(delta*x)*(1-2*m)/(9/2+12*(0:ℝ))+loss) := by
    intro hrc hmhalf hv
    obtain ⟨hv0,hv1,hcap⟩ := plain_requested_capacity 0 x tstar r m eps nu (by norm_num)
      hx hx1 hts hts1 hrc hleft (by linarith) hnu.le hv
    obtain ⟨selected,hsub,hlen,hprime⟩ := select ((1-2*m)/(9/2+12*(0:ℝ))-nu) hv0 hv1
    have hc := (paired selected hsub _ hprime).2 m hm hm1
      (by rw [Finset.sum_coe_sort];nlinarith) hspikeP
    apply promote _ _ hc
    have hl := plain_marked_loss m delta x 0 eps epsm mesh nu hd.le hdle hx hx1 he hmesh0 hnu.le
    rw [hqx] at hl
    rw [hqx]
    dsimp only [loss] at *
    nlinarith only [hl]
  have hc := count_bound_of_source_branches (rows.card:ℝ) A U delta x 0 tstar r m
    loss nu eps hA.le hPU.1.le hd.le hd1 hx hx1 (by norm_num) (by norm_num)
    hts hts1 hnu.le he hleft hright hI0 hP0 hI hP
  convert hc using 1 <;> dsimp only [A,x,q,loss,commonLoss] <;> congr 2 <;> ring

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_balanced_spike_count
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_balanced_spike_count
