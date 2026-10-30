import AngularPhysicalDetectorLiteralSource
import AngularPhysicalDetectorPhysicalCount
import AngularPhysicalDetectorAdaptiveWitness

/- Sharp ordinary HIGH counting with exponent 1-delta for the actual final source dictionary, including
its reversed denominator and ray presentations. The inverse energy is proved
internally. No PhysicalBatch coefficient/orientation premise, angular 7/8
ceiling, feedback hypothesis, or assumed row count is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource
open PhysicalDetectorJoint
open OAI.SevenEighths.Angular.Dyadic
open HeckeInverseAmplification (FreeRow)
open HeckeDetectorWitnessRows (dyadicLength)
open HeckeDetectorInverseFiberCount (inverseTest)
local notation "O" => ActualEisensteinCubic.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
local notation "Label" => Sum Bool (RayQuotient.Characters M H)

theorem literal_sharp_high_witness_rows (n : ℕ)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (alo bhi B : ℝ) (halo : 0<alo) (hab : alo≤bhi) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo alo bhi) (hφB : ∀y,φ y≤B)
    (εm : ℝ) (hεm : 0<εm) :
    ∃J : ℕ,∀η : AngularCharacter,η.k= -(n:ℤ) →
    ∀S : Finset (Ideal O),∀hS : ∀P∈S,Prime P,
      CanonicalQuadraticSieve.fixedBadPrimes⊆S →
    ∃C : ℝ,0<C ∧ ∀ᶠU : ℝ in atTop,1<U ∧
      ∀allRows : Finset FreeRow,(∀u∈allRows,((Ideal.span {u.val}).absNorm:ℝ)≤U) →
      ∀a eps T allowance height : ℝ,∀i : ℕ,
      5/6≤2*a-1 → 2*a-1≤1 → 0≤eps → eps≤1/1000 →
      0≤height → 2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      (∀u : allRows,SupportedWitness (SourceRows.sourceDetectorFamily M H hH S hS η u.val)
        U a eps (3/2) T allowance i) →
      (allRows.card:ℝ)≤((Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2)*
        (C*(1+height)^J)*U^((1-(2*a-1))+εm+78*eps) := by
  have hinv (tag : Bool) := PhysicalDetectorCount.physical_inverse_count
    (if tag then n else 0) M H hH ∅ φ hφ hφc hφp hφ0 hφne
    alo bhi B halo hab hB hφs hφB 2 εm (by norm_num) hεm
  choose Ji Ui hUi hi using hinv
  let J := ∑tag : Bool,Ji tag
  refine ⟨J,?_⟩
  intro η hk S hS hbad
  let data := SourceRows.sourceMomentData M H hH S hS η
  let tag (j : Label) : Bool := if (data j).η.k=0 then false else true
  have ht (j : Label) : (data j).η.k=((if tag j then n else 0:ℕ):ℤ) := by
    have hh := SourceRows.sourceMomentData_nonnegative_types M H hH n S hS η hk j
    by_cases hz : (data j).η.k=0
    · simp [tag,hz]
    · simpa only [tag,hz,ite_false,Bool.true_eq,ite_true] using hh.resolve_left hz
  choose Ci hCi hI using fun j=>hi (tag j) (data j) (ht j)
  let C := 1+∑j,Ci j
  have hC : 0<C := by
    have hh := Finset.sum_nonneg (fun j (_ : j∈(Finset.univ : Finset Label))=>(hCi j).le)
    dsimp [C];linarith
  have hCij (j : Label) : Ci j≤C := by
    have hh := Finset.single_le_sum (fun k (_ : k∈(Finset.univ : Finset Label))=>(hCi k).le)
      (Finset.mem_univ j)
    dsimp [C];linarith
  have hJi (j : Label) : Ji (tag j)≤J :=
    Finset.single_le_sum (fun k _=>Nat.zero_le (Ji k)) (Finset.mem_univ (tag j))
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (max (Ui false) (Ui true)),eventually_gt_atTop (1:ℝ)]
    with U hU₀ hU
  refine ⟨hU,?_⟩
  intro allRows hnorm a eps T allowance height i ha0 ha1 heps heps1 hh hfreq witness
  have hUi' (j : Label) : Ui (tag j)≤U := by
    cases tag j
    · exact (le_max_left _ _).trans hU₀
    · exact (le_max_right _ _).trans hU₀
  have hscaleC (j : Label) : Ci j*(1+height)^(Ji (tag j))≤C*(1+height)^J :=
    mul_le_mul (hCij j) (pow_le_pow_right₀ (by linarith) (hJi j)) (by positivity) hC.le
  let δ := 2*a-1
  let tstar : ℝ := 3/2
  let A := C*(1+height)^J
  let E := (1-δ)+εm+78*eps
  let χ : allRows→Label→AngularCharacter := fun u=>SourceRows.sourceDetectorFamily M H hH S hS η u.val
  let key : allRows→Label×Fin (dyadicLength U)×Fin (dyadicLength U) :=
    fun u=>((witness u).label,(witness u).left,(witness u).right)
  let fiber (label : Label) (left right : Fin (dyadicLength U)) : Finset allRows :=
    Finset.univ.filter (fun u=>key u=(label,left,right))
  have hUp : 0<U := zero_lt_one.trans hU
  have hA : 0<A := by dsimp [A];positivity
  have hts : 1≤tstar ∧ tstar≤3/2 := by norm_num [tstar]
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
      have fields (u:allRows)(hu:u∈f) :
          (witness u).label=label ∧ (witness u).left=left ∧ (witness u).right=right := by
        simpa only [key,Prod.mk.injEq] using (Finset.mem_filter.mp hu).2
      let r := Real.logb U ((2:ℝ)^left.val)
      let m := Real.logb U ((2:ℝ)^right.val)
      have hr (u:allRows)(hu:u∈f) : (witness u).r=r := by
        rw [(witness u).toWitness.left_exponent hU,(fields u hu).2.1]
      have hgeom := fiber_lengths f hne χ U a eps tstar T allowance i hU witness left right
        (fun u hu=>(fields u hu).2.1) (fun u hu=>(fields u hu).2.2)
      change tstar-r-eps≤m ∧ r≤tstar+eps ∧ m≤1/2+75*eps ∧ tstar-1/2-76*eps≤r ∧ 0≤m at hgeom
      have hr0 : 0≤r := by linarith [hgeom.2.2.2.1,hts.1]
      have hr2 : r≤2 := by
        have hrupper := hgeom.2.1
        dsimp only [tstar] at hrupper
        linarith only [hrupper,heps1]
      let σ : FreeRow→ℝ := Function.extend Subtype.val (fun u:allRows=>(witness u).zero.re) (fun _=>0)
      let freq : FreeRow→ℝ := Function.extend Subtype.val (fun u:allRows=>(witness u).toWitness.frequency) (fun _=>0)
      have hσval (u:allRows) : σ u.val=(witness u).zero.re := hinj.extend_apply _ _ u
      have hfval (u:allRows) : freq u.val=(witness u).toWitness.frequency := hinj.extend_apply _ _ u
      have hσ : ∀u∈rows,σ u∈Icc (0:ℝ) 1 := by
        intro u hu
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
        rw [hσval]
        exact ⟨by linarith [(witness v).zero_lower],(witness v).toWitness.real_part_upper⟩
      have hfq : ∀u∈rows,freq u∈Icc (-height) height := by
        intro u hu
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
        rw [hfval]
        exact abs_le.mp ((witness v).toWitness.frequency_bound.trans hfreq)
      have hi := (hI label U r δ eps rows
        (fun u=>SourceRows.sourceDetectorFamily M H hH S hS η u label)
        (ProbeHighRowFamily.sourceMomentReverse M H label) tstar height σ freq
        (hUi' label) hr0 hr2 hh (fun u hu=>hnorm u (hrows hu)) hσ hfq
        (fun u _ I=>SourceRows.source_family_moment_coeff M H hH S hS hbad η u label I)
        (by
          intro u hu
          obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
          rw [hσval,hfval]
          have h := (witness v).inverse_spike
          rw [hr v hv,(fields v hv).1] at h
          exact h)).2 (76*eps) (by positivity) ha0 ha1
        (by dsimp only [tstar] at hgeom;linarith [hgeom.2.2.2.1])
      have hh : (rows.card:ℝ)≤A*U^E := by
        apply hi.trans
        convert mul_le_mul_of_nonneg_right (hscaleC label)
          (Real.rpow_nonneg hUp.le (1-δ+2*eps+εm+76*eps)) using 1 <;>
          dsimp only [A,E] <;> congr 2 <;> ring
      have hcard : rows.card=f.card := Finset.card_image_of_injective _ hinj
      rw [hcard] at hh
      exact hh
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

end OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_sharp_high_witness_rows
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorLiteralSource.literal_sharp_high_witness_rows
