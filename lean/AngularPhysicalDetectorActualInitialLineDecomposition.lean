import AngularPhysicalDetectorActualSlabFubini
import AngularPhysicalDetectorActualUniformJoins
import AngularPhysicalDetectorActualBufferedBin
import AngularPhysicalDetectorActualBufferedIntegral

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail
  selectedFirstBound selectedFirstBound_nonneg 
   rowNorm)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)
variable (angularOrder : ℕ)

theorem initialLineIntegral_central_decomposition {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH0 : 0≤H) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : AngularCharacter) (u : FreeRow) (hu : u.val≠1) (horder : η.k.natAbs≤angularOrder)
      (hnp : ∀j,(SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).k≠0 ∨
        (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).residue≠1)
    (hbin : PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u) hnp (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
    let E : Set HeightSpace := {t | |t.1.1|≤H}
    IntegrableOn (k (a+16*e)) E heightMeasure ∧
    initialLineIntegral S hS hmax P hPS η u W0 W1 X Y Z a e=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ((∫p : HeightSpace in E,k (a+16*e) p ∂heightMeasure)+
          I*((∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2)) ∂volume.prod volume)-
            (∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)) ∂volume.prod volume))+
          ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure) := by
  dsimp only
  let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hi := actual_first_line_integrable S hS hmax (hfirst.mono_parameter (by linarith)) P hP hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (1-a-6*e) (17/50)
    ⟨by linarith,by linarith⟩ le_rfl (by norm_num) X Y Z hX hY hZ
  have hleft := continuedPhysicalRowKernel_buffered_integrable M Hray hHray angularOrder e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu horder hnp hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  obtain ⟨C,hC,hjoins0⟩ := uniform_buffered_horizontal_join_decay M Hray hHray angularOrder K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 0 (17/50) le_rfl (by norm_num)
  have hjoins := hjoins0 η u hu P hP hPS horder hnp
  have hJ (tx : ℝ) (htx : |tx|=H) :
      Integrable (fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) (volume.prod volume) :=
    (hjoins X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx).1
  have hm := hJ (-H) (by rw [abs_neg,abs_of_nonneg hH0])
  have hp := hJ H (abs_of_nonneg hH0)
  have hc := height_slab_partial_integrable _ H hH0 hleft
  refine ⟨hleft,?_⟩
  rw [initialLineIntegral,←integral_add_compl hE hi]
  congr 2
  rw [height_slab_integral_pair _ H hH0 hi.integrableOn,
    height_slab_integral_pair _ H hH0 hleft]
  have heq : (fun q : ℝ×ℝ=>∫tx : ℝ in -H..H,k 2 ((tx,q.1),q.2))=
      (fun q : ℝ×ℝ=>(∫tx : ℝ in -H..H,k (a+16*e) ((tx,q.1),q.2))+
        I*((∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2))-(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)))) := by
    funext q
    have hHT : H≤3*(i+1:ℕ)*B := by
      apply hH.trans
      have hn : (3*i+2:ℕ)≤3*(i+1) := by omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
    simpa only [k,continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using
      source_buffered_x_rectangle M Hray hHray S hS hmax P hPS η u hnp B a e i he he' ha haTop hfirst hbin W0 W1 X Y Z hZ
        ((((1-a-6*e):ℝ):ℂ)+q.2*I) ((17/50:ℂ)+q.1*I) (by simp) (by norm_num) 2 H (by linarith) hH0 hHT
  rw [heq]
  dsimp only [k] at hm hp ⊢
  have hsplit := integral_add hc ((hm.sub hp).const_mul I)
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit,integral_const_mul]
  congr 1
  exact congrArg (fun z : ℂ=>I*z) (integral_sub hm hp)


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.initialLineIntegral_central_decomposition
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.initialLineIntegral_central_decomposition
