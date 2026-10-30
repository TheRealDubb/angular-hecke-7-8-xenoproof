import AngularPhysicalDetectorActualUniformDenominator
import AngularPhysicalDetectorHighPhysicalSelectedBounds
import OAI.NumberTheory.DirichletL.Hecke.StripActual

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail
  selectedFirstBound selectedFirstBound_nonneg selectedFirstBound_polynomial
  calibrated_numerator_first_uniform_growth rowNorm)
open ProbeRowRadicalConductor (fixedConductorConstant)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O ⧸ M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)
variable (angularOrder : ℕ)

def coarsePrimeCost (T : Finset ProbePhysical.PrimeIdeal) : ℝ := ∏P∈T,(8192:ℝ)*(P.val.absNorm:ℝ)^3

lemma coarsePrimeCost_nonneg (T : Finset ProbePhysical.PrimeIdeal) : 0≤coarsePrimeCost T := by
  unfold coarsePrimeCost
  positivity

theorem calibrated_physicalRow_buffered_polynomial_growth
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : AngularCharacter) (u : FreeRow),u.val≠1 →
      ∀(T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (horder : η.k.natAbs≤angularOrder)
      (hnp : ∀j,(SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).k≠0 ∨
        (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u j).residue≠1),
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      PhysicalDetectorZeros.zeroMaximum (SourceRows.sourceDetectorFamily M Hray hHray S hS.prime η u) hnp (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z‖≤
        C*(η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6*
          coarsePrimeCost T*(3+|H|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_uniform_growth S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_denominator_polynomial_growth M Hray hHray angularOrder e he he' S hS.prime
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨L*Cr*Cn*Ch,by positivity,?_⟩
  intro η u hu T hT horder hnp a B H i ha ha1 hB hH hbin x w z hxl hxr hxi hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hwlow : -(1/100:ℝ)≤w.re := by rw [hw];linarith
  have hn' := hn u hu w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec := hreciprocal η u horder hnp a B H i ha ha1 hB hH hbin x hxl hxr hxi
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (η.idealHom P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤coarsePrimeCost T := by
    rw [norm_prod]
    unfold coarsePrimeCost
    conv_rhs => rw [←Finset.prod_attach]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    have hQ : (4:ℝ)≤P.val.val.absNorm := by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)
    exact (continuedCompensatedLocal_first_bound η u P.val _ hQ 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)).trans (selectedFirstBound_polynomial (by linarith))
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (η.idealHom P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*(Cr*(η.modulus.absNorm:ℝ)^2*N^2*(3+|H|)^2))*(Cn*N^3*(3+|w.im|)^2)*(Ch*N)*coarsePrimeCost T := by
      apply mul_le_mul _ hg (norm_nonneg _) (by have hc:=coarsePrimeCost_nonneg T;dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (by positivity)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by dsimp [N];ring

theorem calibrated_physicalRow_first_joint_polynomial_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : AngularCharacter) (u : FreeRow),u.val≠1 →
      ∀(T : Finset ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S),∀x w z : ℂ,x.re=2 → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4*coarsePrimeCost T*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_uniform_growth S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨L*L*Cn*Ch,by positivity,?_⟩
  intro η u hu T hT x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hn' := hn u hu w hw
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (1/4) S hS hfirst T η u x w z (by rw [hx];norm_num) hw hz
      (by rw [hx];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS.prime) x‖≤L :=
    PhysicalReciprocal.reciprocal_norm_le _ (by norm_num) (by rw [hx])
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (η.idealHom P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤coarsePrimeCost T := by
    rw [norm_prod]
    unfold coarsePrimeCost
    conv_rhs => rw [←Finset.prod_attach]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    apply (continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by rw [hx];norm_num) hx.le hw hz (by rw [hx];linarith)).trans
    exact selectedFirstBound_polynomial (by have hn:=hS.tail.norm_four P.val (hT P.val P.property);exact_mod_cast (by omega : 1≤P.val.val.absNorm))
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (η.idealHom P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*L)*(Cn*N^3*(3+|w.im|)^2)*(Ch*N)*coarsePrimeCost T := by
      apply mul_le_mul _ hg (norm_nonneg _) (by have hc:=coarsePrimeCost_nonneg T;dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hL)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by dsimp [N];ring


end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.coarsePrimeCost_nonneg

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibrated_physicalRow_buffered_polynomial_growth

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibrated_physicalRow_first_joint_polynomial_growth
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibrated_physicalRow_first_joint_polynomial_growth
