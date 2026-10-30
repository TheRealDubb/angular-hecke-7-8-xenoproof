import AngularPhysicalDetectorActualInitialCubeSaving
import AngularPhysicalDetectorActualOriginalLineBridge

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

theorem original_row_cube_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : AngularCharacter) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀(horder : η.k.natAbs≤angularOrder)
      (hnp : ∀j,(SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).k≠0 ∨
        (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).residue≠1),∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u) hnp (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hbound⟩ := initial_line_cube_arbitrary_saving M Hray hHray angularOrder
    K τ saving b ζ hτ hb hζ e he he' S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η u hu P hP hPS horder hnp Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [rowIntegral_eq_initialLineIntegral a e ha haTop he he' S hS hmax hfirst P hP hPS
    η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0]
  exact hbound η u hu P hP hPS horder hnp Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.original_row_cube_arbitrary_saving
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.original_row_cube_arbitrary_saving
