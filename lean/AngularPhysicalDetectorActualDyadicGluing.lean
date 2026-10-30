import AngularPhysicalDetectorActualBinPartition
import OAI.NumberTheory.DirichletL.PrimeRows.RowPartition

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily (rowNorm rowNorm_ge_one dyadicRows mem_dyadicRows
  exists_dyadicRows dyadicRows_disjoint)
local notation "O" => ActualEisensteinCubic.O

def actualDyadIndex (u : FreeRow) : ℕ :=
  if h : u.val≠1 then Nat.find (exists_dyadicRows 1 zero_lt_one u h (rowNorm_ge_one u)) else 0

lemma actualDyadIndex_mem (u : FreeRow) (hu : u.val≠1) :
    u∈dyadicRows 1 (actualDyadIndex u) := by
  rw [actualDyadIndex,dif_pos hu]
  exact Nat.find_spec (exists_dyadicRows 1 zero_lt_one u hu (rowNorm_ge_one u))

lemma actualDyadIndex_eq_of_mem {u : FreeRow} {k : ℕ} (hk : u∈dyadicRows 1 k) :
    actualDyadIndex u=k := by
  have hm := actualDyadIndex_mem u (mem_dyadicRows.mp hk).1
  by_contra he
  exact (Finset.disjoint_left.mp (dyadicRows_disjoint 1 zero_lt_one he)) hm hk

lemma actualDyad_filter (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1) (k : ℕ) :
    R.filter (fun u=>actualDyadIndex u=k)=R∩dyadicRows 1 k := by
  ext u
  constructor
  · intro hu
    obtain ⟨hmem,hk⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_inter.mpr ⟨hmem,?_⟩
    simpa only [hk] using actualDyadIndex_mem u (hR u hmem)
  · intro hu
    obtain ⟨hmem,hk⟩ := Finset.mem_inter.mp hu
    exact Finset.mem_filter.mpr ⟨hmem,actualDyadIndex_eq_of_mem hk⟩

lemma sum_actualDyads (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (F : Finset ℕ) (hF : ∀u∈R,actualDyadIndex u∈F) (f : FreeRow→ℂ) :
    (∑k∈F,∑u∈R∩dyadicRows 1 k,f u)=∑u∈R,f u := by
  have hs := Finset.sum_fiberwise_of_maps_to hF f
  simpa only [actualDyad_filter R hR] using hs

def spliceDyadicLabel (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (label : ∀k : ℕ,↥(R∩dyadicRows 1 k)→ℕ) (u : R) : ℕ :=
  label (actualDyadIndex u.val) ⟨u.val,Finset.mem_inter.mpr
    ⟨u.property,actualDyadIndex_mem u.val (hR u.val u.property)⟩⟩

lemma spliceDyadicLabel_at (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (label : ∀k : ℕ,↥(R∩dyadicRows 1 k)→ℕ) (u : R) (k : ℕ)
    (hk : u.val∈dyadicRows 1 k) :
    spliceDyadicLabel R hR label u=label k ⟨u.val,Finset.mem_inter.mpr ⟨u.property,hk⟩⟩ := by
  have he := actualDyadIndex_eq_of_mem hk
  subst k
  rfl

/-- The global row labels are exactly the per-dyad labels at every summed
row. All row and selected-prime multiplicities remain unchanged. -/
theorem finiteCentralCubeRows_dyadic_gluing {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (F : Finset ℕ) (hF : ∀u∈R,actualDyadIndex u∈F)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z e B : ℝ) (idx grid : ∀k : ℕ,↥(R∩dyadicRows 1 k)→ℕ) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*extendRowLabel R (spliceDyadicLabel R hR grid) u)
      (fun u=>(3*extendRowLabel R (spliceDyadicLabel R hR idx) u+1:ℕ)*B)=
    ∑k∈F,finiteCentralCubeRows S hS hmax η (R∩dyadicRows 1 k) T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*extendRowLabel (R∩dyadicRows 1 k) (grid k) u)
      (fun u=>(3*extendRowLabel (R∩dyadicRows 1 k) (idx k) u+1:ℕ)*B) := by
  unfold finiteCentralCubeRows
  rw [←sum_actualDyads R hR F hF]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro u hu
  have huR := (Finset.mem_inter.mp hu).1
  have hud := (Finset.mem_inter.mp hu).2
  have hi := spliceDyadicLabel_at R hR idx ⟨u,huR⟩ k hud
  have hg := spliceDyadicLabel_at R hR grid ⟨u,huR⟩ k hud
  simp only [extendRowLabel,dif_pos huR,dif_pos hu,hi,hg]

/-- The per-dyad bounds will be discharged by actual_counted_dyadic_cube.
This finite identity pays the number of dyads exactly once. -/
theorem finiteCentralCubeRows_dyadic_gluing_norm {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : AngularCharacter) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (F : Finset ℕ) (hF : ∀u∈R,actualDyadIndex u∈F)
    (T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z e B : ℝ) (idx grid : ∀k : ℕ,↥(R∩dyadicRows 1 k)→ℕ)
    (normer : ℂ) (A : ℝ)
    (hbound : ∀k∈F,‖finiteCentralCubeRows S hS hmax η (R∩dyadicRows 1 k) T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*extendRowLabel (R∩dyadicRows 1 k) (grid k) u)
      (fun u=>(3*extendRowLabel (R∩dyadicRows 1 k) (idx k) u+1:ℕ)*B)/normer‖≤A) :
    ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*extendRowLabel R (spliceDyadicLabel R hR grid) u)
      (fun u=>(3*extendRowLabel R (spliceDyadicLabel R hR idx) u+1:ℕ)*B)/normer‖≤F.card*A := by
  rw [finiteCentralCubeRows_dyadic_gluing S hS hmax η R hR F hF T hT W Yp W0 W1 X Y Z e B idx grid,
    Finset.sum_div]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hbound).trans_eq (by simp))

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actualDyadIndex_mem

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actualDyadIndex_eq_of_mem

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actualDyad_filter

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.sum_actualDyads

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.spliceDyadicLabel_at

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.finiteCentralCubeRows_dyadic_gluing

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.finiteCentralCubeRows_dyadic_gluing_norm
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.finiteCentralCubeRows_dyadic_gluing_norm
