import AngularPhysicalDetectorActualCubeFubini

namespace OAI

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) : Finset FreeRow :=
  R.filter (fun u=>idx u=i ∧ grid u=k)

@[simp] lemma mem_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) (u : FreeRow) :
    u∈cubeBinRows R idx grid i k ↔ u∈R ∧ idx u=i ∧ grid u=k := by simp [cubeBinRows]

lemma sum_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤m) (f : FreeRow→ℂ) :
    (∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),∑u∈cubeBinRows R idx grid i k,f u)=∑u∈R,f u := by
  have hm : ∀u∈R,(idx u,grid u)∈(Finset.range (n+1)).product (Finset.range (m+1)) := by
    intro u hu
    simpa only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] using
      And.intro (Nat.lt_succ_of_le (hlabel u hu).1) (Nat.lt_succ_of_le (hlabel u hu).2)
  have hs := Finset.sum_fiberwise_of_maps_to hm f
  simpa only [Finset.product_eq_sprod,Finset.sum_product,Prod.mk.injEq,cubeBinRows] using hs

theorem finiteCentralCubeRows_bin_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤m) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)=
    ∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),
      finiteCentralCubeRows S hS hmax η (cubeBinRows R idx grid i k) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*B) := by
  unfold finiteCentralCubeRows
  rw [←sum_cubeBinRows R idx grid n m hlabel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro u hu
  rcases (mem_cubeBinRows R idx grid i k u).mp hu with ⟨hu,hi,hk⟩
  simp only [hi,hk]


/-- Extend a label off the finite physical row set only to express a finite
partition. Values off the row set are absent from every resulting sum. -/
def extendRowLabel (R : Finset FreeRow) (label : R→ℕ) (u : FreeRow) : ℕ :=
  if h : u∈R then label ⟨u,h⟩ else 0

@[simp] lemma extendRowLabel_coe (R : Finset FreeRow) (label : R→ℕ) (u : R) :
    extendRowLabel R label u.val=label u := by
  simp [extendRowLabel,u.property]

def actualWindowCell (R : Finset FreeRow) (idx grid : R→ℕ) (i k : ℕ) : Finset R :=
  Finset.univ.filter (fun u=>idx u=i ∧ grid u=k)

lemma actualWindowCell_image (R : Finset FreeRow) (idx grid : R→ℕ) (i k : ℕ) :
    (actualWindowCell R idx grid i k).image Subtype.val=
      cubeBinRows R (extendRowLabel R idx) (extendRowLabel R grid) i k := by
  ext u
  constructor
  · intro hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    exact (mem_cubeBinRows _ _ _ _ _ _).mpr
      ⟨v.property,by simpa [actualWindowCell] using hv⟩
  · intro hu
    obtain ⟨hR,hi,hk⟩ := (mem_cubeBinRows _ _ _ _ _ _).mp hu
    refine Finset.mem_image.mpr ⟨⟨u,hR⟩,?_,rfl⟩
    simpa [actualWindowCell,extendRowLabel,hR] using And.intro hi hk

/-- Counted windows on the row subtype partition the original finite row
integral exactly. No projection multiplicity is inserted or discarded. -/
theorem finiteCentralCubeRows_subtype_bin_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : R→ℕ) (n m : ℕ)
    (hlabel : ∀u : R,idx u≤n ∧ grid u≤m) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*extendRowLabel R grid u)
      (fun u=>(3*extendRowLabel R idx u+1:ℕ)*B)=
    ∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),
      finiteCentralCubeRows S hS hmax η
        ((actualWindowCell R idx grid i k).image Subtype.val) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*B) := by
  have hfull : ∀u∈R,extendRowLabel R idx u≤n ∧ extendRowLabel R grid u≤m := by
    intro u hu
    simpa only [extendRowLabel,dif_pos hu] using hlabel ⟨u,hu⟩
  simpa only [actualWindowCell_image] using
    finiteCentralCubeRows_bin_partition S hS hmax η R T hT W Yp W0 W1 X Y Z e B
      (extendRowLabel R idx) (extendRowLabel R grid) n m hfull

/-- Finite window losses are counted once. Analytic bounds for the nonempty
cells remain explicit premises, including the floor cell k=0. -/
theorem finiteCentralCubeRows_subtype_bin_norm {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (T : Fin K→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : R→ℕ) (n m : ℕ)
    (hlabel : ∀u : R,idx u≤n ∧ grid u≤m) (normer : ℂ) (A : ℝ) (hA : 0≤A)
    (hcell : ∀i≤n,∀k≤m,(actualWindowCell R idx grid i k).Nonempty →
      ‖finiteCentralCubeRows S hS hmax η
        ((actualWindowCell R idx grid i k).image Subtype.val) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*B)/normer‖≤A) :
    ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*extendRowLabel R grid u)
      (fun u=>(3*extendRowLabel R idx u+1:ℕ)*B)/normer‖≤
      (n+1:ℕ)*(m+1:ℕ)*A := by
  rw [finiteCentralCubeRows_subtype_bin_partition S hS hmax η R T hT W Yp W0 W1
    X Y Z e B idx grid n m hlabel]
  simp_rw [Finset.sum_div]
  calc
    _ ≤ ∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),
        ‖finiteCentralCubeRows S hS hmax η
          ((actualWindowCell R idx grid i k).image Subtype.val) T hT W Yp W0 W1 X Y Z e
          (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*B)/normer‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>norm_sum_le _ _))
    _ ≤ ∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),A := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      by_cases hne : (actualWindowCell R idx grid i k).Nonempty
      · exact hcell i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hne
      · have hz : actualWindowCell R idx grid i k=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simpa [hz,finiteCentralCubeRows] using hA
    _ = _ := by simp; ring

end SevenEighths.Angular.PhysicalDetectorHigh

end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.sum_cubeBinRows

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.finiteCentralCubeRows_bin_partition

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actualWindowCell_image

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.finiteCentralCubeRows_subtype_bin_partition

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.finiteCentralCubeRows_subtype_bin_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.finiteCentralCubeRows_subtype_bin_norm
