import AngularPhysicalDetectorActualInitialLineDecomposition
import AngularPhysicalDetectorActualCentralRectangleCutoff

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

lemma scaleBound_eq_rpow_of_one_le {q lo hi : ℝ} (hq : 1≤q) (hl : lo≤hi) :
    scaleBound q lo hi=q^hi := by
  unfold scaleBound
  rw [max_eq_right (mul_le_mul_of_nonneg_left hl (Real.log_nonneg hq)),
    Real.rpow_def_of_pos (by linarith)]

theorem uniform_initial_line_central_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : AngularCharacter) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀(horder : η.k.natAbs≤angularOrder)
      (hnp : ∀j,(SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).k≠0 ∨
        (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).residue≠1),∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u) hnp (3*(i+1:ℕ)*B)<a+2*e →
      ‖initialLineIntegral S hS hmax P hPS η u W0 W1 X Y Z a e-
        centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨Cj,hCj,hjoin0⟩ := uniform_buffered_horizontal_join_decay M Hray hHray angularOrder K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  obtain ⟨Ct,hCt,htail0⟩ := uniform_original_x_height_tail K S hS hmax (hfirst.mono_parameter (by linarith))
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*(2*Cj+Ct),by positivity,?_⟩
  intro η u hu P hP hPS horder hnp X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hjoin := hjoin0 η u hu P hP hPS horder hnp
  have htail := htail0 η u hu P hP hPS
  have hcost := contourArithmeticCost_nonneg η u P
  have hZ0 : 0<Z := by linarith
  let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  let J := fun tx : ℝ=>∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) ∂volume.prod volume
  let tail := ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure
  let A : ℝ := contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤A := by dsimp [A];exact div_nonneg (by positivity) (pow_nonneg (height_pos _).le _)
  have hj (tx : ℝ) (htx : |tx|=H) : ‖J tx‖≤Cj*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := (hjoin X Y Z hX hY hZ0 a B H i ha haTop hB hH hbin tx htx).2
    rw [scaleBound_eq_rpow_of_one_le hZ (by norm_num)] at hb
    convert hb using 1 ; dsimp [J,k,A] ; ring
  have ht : ‖tail‖≤Ct*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := htail (1-a-6*e) ⟨by linarith,by linarith⟩ X Y Z hX hY hZ0 H hH0
    convert hb using 1 ; dsimp [tail,k,E,A,height] ; rw [abs_of_nonneg hH0] ; ring
  have hdec := (initialLineIntegral_central_decomposition M Hray hHray angularOrder e a B H i he he' ha haTop hB hH0 hH S hS hmax hfirst
    P hP hPS η u hu horder hnp hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ0).2
  have heq : initialLineIntegral S hS hmax P hPS η u W0 W1 X Y Z a e-
      centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=n*(I*(J (-H)-J H)+tail) := by
    rw [hdec]
    dsimp [centralRowIntegral,n,J,tail,k,E]
    ring
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(‖J (-H)‖+‖J H‖+‖tail‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg n)
      apply (norm_add_le (I*(J (-H)-J H)) tail).trans
      rw [norm_mul,norm_I,one_mul]
      exact add_le_add (norm_sub_le (J (-H)) (J H)) (le_refl ‖tail‖)
    _ ≤ ‖n‖*(Cj*A+Cj*A+Ct*A) := by
      gcongr
      · exact hj (-H) (by rw [abs_neg,abs_of_nonneg hH0])
      · exact hj H (abs_of_nonneg hH0)
    _ = _ := by dsimp [A];ring


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.scaleBound_eq_rpow_of_one_le

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.uniform_initial_line_central_error
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.uniform_initial_line_central_error
