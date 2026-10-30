import AngularPhysicalDetectorLiteralBalanced
import AngularPhysicalDetectorAdaptiveWitness

/- Ordinary balanced counting for actual supported zero witnesses in a
common physical amplitude bin. The zero, inverse spike, plain spike and
joint length relation belong to the same witness. All four moment/count
branches and the dictionary/dyadic partition are supplied internally. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff SchwartzMap
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open NaturalRows RelativePrime PhysicalDetectorInitial PhysicalDetectorJoint
open OAI.SevenEighths.Angular.Dyadic
open HeckeInverseAmplification (FreeRow)
open HeckeDetectorWitnessRows (dyadicLength)
open HeckeDetectorPhysicalSelection HeckeDetectorRowCount
local notation "O" => ActualEisensteinCubic.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local notation "Label" => Sum Bool (RayQuotient.Characters M H)

theorem literal_balanced_witness_rows
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
      ∀(slots : Finset Slot)(w g : Slot→ℝ)(z : Slot→ℂ),
      ∀height mesh binWidth a eps nu T allowance : ℝ,∀i : ℕ,
        (∀j∈slots,wmin≤w j) → (∀j∈slots,w j≤mesh) →
        mesh≤PhysicalDetectorUniform.commonMesh 2 0 1 (epsm/2) → 0≤mesh →
        (∀j∈slots,lo≤1-(z j).re) → (∀j∈slots,1-(z j).re≤hi) →
        0≤height → (∀j∈slots,|(z j).im|≤height) →
        0<binWidth → 7/37≤∑j∈slots,w j →
        51/100<a → 2*a-1≤5/6 → 0≤eps → eps≤1/1000 → eps≤epsm/300 →
        0<nu → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀allRows : Finset FreeRow,
        (∀u∈allRows,∀label : Label,initialKeep (SourceRows.sourceMomentData M H hH S hS eta label).η
          (internalQ M (SourceRows.sourceMomentData M H hH S hS eta label).η) u.val) →
        (∀u∈allRows,((Ideal.span {u.val}).absNorm:ℝ)≤U) →
        (∀u∈allRows,∀j∈slots,HeckePrimeAmplitudeBins.amplitude (U^(w j)) ((2*a-1)/2) binWidth
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val W 2 (U^(w j)) (z j))=g j) →
        (∀u : allRows,SupportedWitness (SourceRows.sourceDetectorFamily M H hH S hS eta u.val)
          U a eps (Endpoint.balancedCutoff (2*a-1) (1/2-weightedMean slots w g/(2*a-1))) T allowance i) →
        (allRows.card:ℝ)≤((Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2)*
          (C*(1+height)^J)*U^(Endpoint.balancedRowCount (2*a-1)
            (1/2-weightedMean slots w g/(2*a-1))+159*eps+epsm+mesh+7*nu) := by
  obtain ⟨J,hcount⟩ := literal_balanced_spike_count (Slot:=Slot) M H hH n W lo hi bPhi epsm wmin
    hWs hW hbPhi hepsm hepsm1 hwmin Phi hsPhi hpPhi hone
    φ hφ hφc hφp hφ0 hφne alo bhi B halo hab hB hφs hφB
  refine ⟨J,?_⟩
  intro eta hk S hS hbad hMmask hMt hM72
  obtain ⟨C,hC,hbound⟩ := hcount eta hk S hS hbad hMmask hMt hM72
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with U hU
  refine ⟨hU.1,?_⟩
  intro slots w g z height mesh binWidth a eps nu T allowance i
    hw hwm hmesh hmesh0 hlo hhi hh hz hbin hsupply ha had he he1 hepad hnu hfreq
    allRows hkeep hnorm hbins witness
  let delta := 2*a-1
  let x := weightedMean slots w g/delta
  let tstar := Endpoint.balancedCutoff delta (1/2-x)
  let A := C*(1+height)^J
  let E := Endpoint.balancedRowCount delta (1/2-x)+159*eps+epsm+mesh+7*nu
  have hUp : 0<U := zero_lt_one.trans hU.1
  have hA : 0<A := by dsimp [A];positivity
  by_cases hneAll : allRows.Nonempty
  · obtain ⟨u0,hu0⟩ := hneAll
    have hd : 0<delta := by dsimp [delta];linarith
    have hL : 0<∑j∈slots,w j := by linarith
    have hg (j : Slot)(hj : j∈slots) : 0≤g j ∧ g j≤delta/2 := by
      rw [←hbins u0 hu0 j hj]
      exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)
    obtain ⟨hq0,hq1⟩ := weightedMean_bounds slots w g delta
      (fun j hj=>hwmin.le.trans (hw j hj)) hL hg
    have hx : 0≤x := div_nonneg hq0 hd.le
    have hx1 : x≤1/2 := (div_le_iff₀ hd).mpr (by linarith)
    have hts := balanced_cutoff_bounds hd.le had hx hx1
    let chi : allRows→Label→AngularCharacter := fun u=>SourceRows.sourceDetectorFamily M H hH S hS eta u.val
    let key : allRows→Label×Fin (dyadicLength U)×Fin (dyadicLength U) :=
      fun u=>((witness u).label,(witness u).left,(witness u).right)
    let fiber (label : Label)(left right : Fin (dyadicLength U)) : Finset allRows :=
      Finset.univ.filter (fun u=>key u=(label,left,right))
    have hinj : Function.Injective (Subtype.val : allRows→FreeRow) := Subtype.val_injective
    have hf (label : Label)(left right : Fin (dyadicLength U)) :
        ((fiber label left right).card:ℝ)≤A*U^E := by
      let f := fiber label left right
      by_cases hne : f.Nonempty
      · let rows : Finset FreeRow := f.image Subtype.val
        have hrows : rows⊆allRows := by
          intro u hu
          obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
          exact v.property
        have fields (u : allRows)(hu : u∈f) :
            (witness u).label=label ∧ (witness u).left=left ∧ (witness u).right=right := by
          simpa only [key,Prod.mk.injEq] using (Finset.mem_filter.mp hu).2
        let r := Real.logb U ((2:ℝ)^left.val)
        let m := Real.logb U ((2:ℝ)^right.val)
        have hr (u : allRows)(hu : u∈f) : (witness u).r=r := by
          rw [(witness u).toWitness.left_exponent hU.1,(fields u hu).2.1]
        have hm (u : allRows)(hu : u∈f) : (witness u).m=m := by
          rw [(witness u).toWitness.right_exponent hU.1,(fields u hu).2.2]
        have hgeom := fiber_lengths f hne chi U a eps tstar T allowance i hU.1 witness left right
          (fun u hu=>(fields u hu).2.1) (fun u hu=>(fields u hu).2.2)
        change tstar-r-eps≤m ∧ r≤tstar+eps ∧ m≤1/2+75*eps ∧ tstar-1/2-76*eps≤r ∧ 0≤m at hgeom
        have hr0 : 0≤r := by linarith [hgeom.2.2.2.1,hts.1]
        have hr2 : r≤2 := by linarith [hgeom.2.1,hts.2]
        let sigma : FreeRow→ℝ := Function.extend Subtype.val (fun u : allRows=>(witness u).zero.re) (fun _=>0)
        let freq : FreeRow→ℝ := Function.extend Subtype.val (fun u : allRows=>(witness u).toWitness.frequency) (fun _=>0)
        have hsval (u : allRows) : sigma u.val=(witness u).zero.re := hinj.extend_apply _ _ u
        have hfval (u : allRows) : freq u.val=(witness u).toWitness.frequency := hinj.extend_apply _ _ u
        have hsigma : ∀u∈rows,sigma u∈Icc (0:ℝ) 1 := by
          intro u hu
          obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
          rw [hsval]
          exact ⟨by linarith [(witness v).zero_lower],(witness v).toWitness.real_part_upper⟩
        have hfreq' : ∀u∈rows,freq u∈Icc (-height) height := by
          intro u hu
          obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
          rw [hfval]
          exact abs_le.mp ((witness v).toWitness.frequency_bound.trans hfreq)
        have hc := hU.2 slots label w g z height mesh binWidth delta eps nu tstar r m
          hw hwm hmesh hmesh0 hlo hhi hh hz hbin hsupply hd had he he1 hepad hnu hts.1 hts.2
          hr0 hr2 hgeom.2.2.2.2 hgeom.2.2.1 hgeom.1 hgeom.2.1 rows
          (hne.image Subtype.val) (fun u hu=>hkeep u (hrows hu) label) (fun u hu=>hnorm u (hrows hu))
          sigma freq hsigma hfreq'
          (by
            intro u hu
            obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
            rw [hsval,hfval]
            have h := (witness v).inverse_spike
            rw [hr v hv,(fields v hv).1] at h
            exact h)
          (by
            intro u hu
            obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
            rw [hsval,hfval]
            have h := (witness v).plain_spike
            rw [hm v hv,(fields v hv).1] at h
            exact h)
          (fun u hu=>hbins u (hrows hu))
        have he := balanced_count_identity hd.le had hx hx1
        change max (shortExponent delta x tstar) (longExponent delta tstar)=
          Endpoint.balancedRowCount delta (1/2-x) at he
        rw [he] at hc
        have hcard : rows.card=f.card := Finset.card_image_of_injective _ hinj
        rw [hcard] at hc
        exact hc
      · have he : f=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        change (f.card:ℝ)≤A*U^E
        rw [he,Finset.card_empty,Nat.cast_zero]
        positivity
    have hpart : (allRows.card:ℝ)=∑label,∑left,∑right,((fiber label left right).card:ℝ) := by
      have hp := Finset.sum_fiberwise_of_maps_to (s:=(Finset.univ:Finset allRows))
        (t:=(Finset.univ:Finset (Label×Fin (dyadicLength U)×Fin (dyadicLength U))))
        (g:=key) (f:=fun _=>(1:ℝ)) (by intro u hu;exact Finset.mem_univ _)
      simpa only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
        nsmul_eq_mul,mul_one,fiber] using hp.symm
    calc
      _=∑label,∑left,∑right,((fiber label left right).card:ℝ) := hpart
      _≤∑(_label:Label),∑(_left:Fin (dyadicLength U)),∑(_right:Fin (dyadicLength U)),A*U^E :=
        Finset.sum_le_sum (fun label _=>Finset.sum_le_sum (fun left _=>
          Finset.sum_le_sum (fun right _=>hf label left right)))
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring
  · have he : allRows=∅ := Finset.not_nonempty_iff_eq_empty.mp hneAll
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_balanced_witness_rows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_balanced_witness_rows
