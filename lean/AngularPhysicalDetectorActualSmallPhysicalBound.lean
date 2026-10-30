import AngularPhysicalDetectorWeightedTuple
import AngularPhysicalDetectorActualSmallTupleCorrection
import AngularPhysicalDetectorActualGlobalScalar

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Angular.PhysicalDetectorHigh
open HeckeFamily HeckeInverseAmplification ProbePhysical
open ProbeHighRowFamily (rowCharacter markExclusions markedSourceExclusions FirstTail)
local notation "O" => ActualEisensteinCubic.O

theorem calibrated_physical_tuple_sum (angularCap K : ℕ) (e δ a b r B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) :
    ∃C : ℝ,0<C ∧ ∀η : AngularCharacter,η.k.natAbs≤angularCap → η.k≠0 → ∀u : FreeRow,u.val≠1 →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → (PhysicalZeroSupremum.beta angularCap)+8*e≤x.re →
      (1/2:ℝ)≤w.re → z.re=r →
      (∑P:(∀i,T i),‖calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
        (fun i=>hT i (P i).val (P i).property) W Y x w z‖)≤
      C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*
        (∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨CL,hCL,hL⟩ := calibrated_scalar_growth angularCap e (δ/2) he he' (by linarith) (by linarith) S hS hmax
  obtain ⟨CG,hCG,hG⟩ := continued_selected_tuple_with_correction K (δ/2) a b r B (by linarith) ha hb hr hB
  refine ⟨CL*CG,mul_pos hCL hCG,?_⟩
  intro η horder hk u hu T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have ht : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val ∧ (4:ℝ)≤P.val.absNorm := by
    intro i P hP
    exact ⟨outside_prime_supported S hS.bad P (hT i P hP),by exact_mod_cast hS.tail.norm_four P (hT i P hP)⟩
  let L : ℂ := star ((calibrationForSet S hmax).residueMonoid u.val)*
    (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      PhysicalReciprocal.reciprocal ((SourceRows.targetRow η u).excludePrimes S hS.prime) x)
  let G : (∀i,T i)→ℂ := fun P=>continuedCorrection
    (markExclusions S (Finset.univ.image (fun i=>(P i).val)))
    (markedSourceExclusions S hS (Finset.univ.image (fun i=>(P i).val))) η u x w z*
    ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u (P i).val (ht i (P i).val (P i).property).1 x w z
        (star (η.idealHom (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
        (((P i).val.val.absNorm:ℂ)^(-w))
  have heq (P:∀i,T i) : calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i (P i).val (P i).property) W Y x w z=L*G P :=
    calibratedTupleValue_factor S hS hmax η u _ (hdis P) _ W Y x w z
  have hLb : ‖L‖≤CL*(η.modulus.absNorm:ℝ)^(δ/2)*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2 :=
    hL η horder hk u hu x w z hxβ hw (by rw [hz];exact hr)
  have hGb : (∑P:(∀i,T i),‖G P‖)≤CG*N^(δ/2)*∏i,(Y i)^r :=
    hG (1/4) S hS hfirst η u T ht Y hY W hWS hWB x w z hx hw hz (by linarith)
  have hη : (η.modulus.absNorm:ℝ)^(δ/2)≤(η.modulus.absNorm:ℝ)^δ :=
    Real.rpow_le_rpow_of_exponent_le (PhysicalLogarithmic.modulus_norm_ge_one η) (by linarith)
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _
  simp_rw [heq,norm_mul]
  rw [←Finset.mul_sum]
  calc
    _ ≤ (CL*(η.modulus.absNorm:ℝ)^(δ/2)*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2)*
        (CG*N^(δ/2)*∏i,(Y i)^r) :=
      mul_le_mul hLb hGb (Finset.sum_nonneg fun _ _=>norm_nonneg _) (by positivity)
    _ ≤ (CL*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2)*
        (CG*N^(δ/2)*∏i,(Y i)^r) := by gcongr
    _ = (CL*CG)*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ)*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
      have hp : N^(3/5+δ/2)*N^(δ/2)=N^(3/5+δ) := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (CL*CG)*(η.modulus.absNorm:ℝ)^δ*(N^(3/5+δ/2)*N^(δ/2))*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by ring
        _ = _ := by rw [hp]

end SevenEighths.Angular.PhysicalDetectorHigh
end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibrated_physical_tuple_sum
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.calibrated_physical_tuple_sum
