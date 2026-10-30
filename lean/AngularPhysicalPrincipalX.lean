import AngularPhysicalPrincipalProducts
import AngularPhysicalPrincipalMellin
import AngularPhysicalZeroSupremum
import AngularPrimeDeletion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace OAI.SevenEighths.Angular.PhysicalPrincipalX
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PhysicalPrincipalMellin PhysicalPrincipalProducts
local notation "Id" => Ideal ActualEisensteinCubic.O

private theorem angular_global_analytic_x (η : AngularCharacter) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>PhysicalDetectorHigh.globalClosedCorrection η S x w z)
      {x : ℂ|7/8<x.re} := by
  apply (PhysicalDetectorHigh.remainder_globalClosedCorrection_analytic_x η S hS w z hw hz).mono
  intro x hx
  exact PhysicalDetectorHigh.theta_bounds.2.trans hx

lemma marked_differentiableAt_x (η : AngularCharacter) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 7/8 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => PhysicalPrincipalProducts.idealMarkedClosed η P x w z) x := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) 1 x z hQ
    (PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (AngularCharacter.norm_idealHom_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (η.idealHom P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (η.idealHom P.val) w
  unfold PhysicalPrincipalProducts.idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem local_analytic_x (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | 7/8 < x.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) 1 w z hQ
    (PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (AngularCharacter.norm_idealHom_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (PhysicalDetectorHigh.actualAPhase η (primaryGenerator P.val)) (η.idealHom P.val) 1 x z hQ
    (PhysicalDetectorHigh.actualAPhase_norm_le_one η _) (AngularCharacter.norm_idealHom_le_one η _) (by simp) hx.le hz
  have hm := marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => PhysicalDetectorHigh.idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (η.idealHom P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem selected_analytic_x (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => selectedMultiplier η T x w z) {x : ℂ | 7/8 < x.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_x η S hS P (hT P hp) w z hw hz)

theorem slot_analytic_x {ι : Type*} (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | 7/8 < x.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem window_analytic_x {ι : Type*} (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (W : ι → ℝ → ℂ) (scale : ι → ℝ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => windowMultiplier η J T W scale x w z) {x : ℂ | 7/8 < x.re} :=
  slot_analytic_x η S hS J T _ hT w z hw hz

theorem combined_selected_analytic_x (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => PhysicalDetectorHigh.globalClosedCorrection η S x w z * selectedMultiplier η T x w z)
      {x : ℂ | 7/8 < x.re} :=
  (angular_global_analytic_x η S hS w z hw hz).mul
    (selected_analytic_x η S hS T hT w z hw hz)

theorem combined_slot_analytic_x {ι : Type*} (η : AngularCharacter) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => PhysicalDetectorHigh.globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {x : ℂ | 7/8 < x.re} :=
  (angular_global_analytic_x η S hS w z hw hz).mul
    (slot_analytic_x η S hS J T b hT w z hw hz)

def continuedSourceMultiplier {ι : Type*} (η : AngularCharacter) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z) * (Z:ℂ)^(x+z-1) * (Y:ℂ)^(w-1) *
    Complex.exp ((x+z-1)^2) *
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z * mellin W1 w *
      PhysicalReciprocal.reciprocal (η.excludePrimes S hS) x *
      PhysicalDetectorHigh.globalClosedCorrection η S x w z * slotMultiplier η J T b x w z

theorem continued_source_analytic_x {ι : Type*} (angularCap : ℕ) (η : AngularCharacter) (horder : η.k.natAbs≤angularCap) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (7/8 : ℝ) (PhysicalZeroSupremum.beta angularCap) < x.re} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (7/8 : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : (PhysicalZeroSupremum.beta angularCap)<x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (angular_global_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := PhysicalZeroSupremum.reciprocal_differentiableAt_of_beta_lt angularCap
    (η.excludePrimes S hS.prime) (by simpa only [AngularCharacter.excludePrimes_k] using horder) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_eq_raw {ι : Type*} (η : AngularCharacter) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : 0<x.re) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      PhysicalPrincipalMellin.sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (PhysicalDetectorHigh.globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  simp only [continuedSourceMultiplier,PhysicalPrincipalMellin.sourceMultiplier,
    PhysicalReciprocal.reciprocal_eq_inv _ x hx0 (fun _ _=>hx1),div_eq_mul_inv]

theorem continued_source_ae_raw {ι : Type*} (η : AngularCharacter) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a : ℝ) (ha : 0<a) (w z : ℂ) :
    (fun t : ℝ => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z ((a:ℂ)+t*I) w z)
      =ᵐ[volume] (fun t : ℝ => PhysicalPrincipalMellin.sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
        ((a:ℂ)+t*I) (PhysicalDetectorHigh.globalClosedCorrection η S ((a:ℂ)+t*I))
          (slotMultiplier η J T b ((a:ℂ)+t*I)) w z) := by
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply continued_source_eq_raw
  · simpa using ha
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem source_analytic_x_off_one {ι : Type*} (angularCap : ℕ) (η : AngularCharacter) (horder : η.k.natAbs≤angularCap) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => PhysicalPrincipalMellin.sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (PhysicalDetectorHigh.globalClosedCorrection η S x) (slotMultiplier η J T b x) w z)
      {x : ℂ | max (7/8 : ℝ) (PhysicalZeroSupremum.beta angularCap) < x.re ∧ x≠1} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _
    ((Complex.isOpen_re_gt _).inter (isClosed_singleton.isOpen_compl))
  intro x hx
  have hx' : (7/8 : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx.1
  have hβ : (PhysicalZeroSupremum.beta angularCap)<x.re := lt_of_le_of_lt (le_max_right _ _) hx.1
  have hx0 : x≠0 := by intro h; simp only [h,zero_re] at hx'; norm_num at hx'
  have hL := FamilyContinuation.LFunction_differentiableAt (η.excludePrimes S hS.prime) x (by linarith) hx.2
  have hLn := PhysicalZeroSupremum.LFunction_ne_zero_of_beta_lt angularCap (η.excludePrimes S hS.prime)
    (by simpa only [AngularCharacter.excludePrimes_k] using horder) hβ (fun _ _=>hx.2)
  have hH := (angular_global_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  unfold PhysicalPrincipalMellin.sourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_differentiable_strip {ι : Type*} (angularCap : ℕ) (η : AngularCharacter) (horder : η.k.natAbs≤angularCap) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : 7/8<a) (hβ : (PhysicalZeroSupremum.beta angularCap)<a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤x.re ∧ x.re≤c} := by
  apply (continued_source_analytic_x angularCap η horder S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1


end OAI.SevenEighths.Angular.PhysicalPrincipalX

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.marked_differentiableAt_x

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.local_analytic_x

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.selected_analytic_x

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.slot_analytic_x

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.window_analytic_x

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.combined_selected_analytic_x

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.combined_slot_analytic_x

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.continued_source_analytic_x

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.continued_source_eq_raw

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.continued_source_ae_raw

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.source_analytic_x_off_one

#print axioms OAI.SevenEighths.Angular.PhysicalPrincipalX.continued_source_differentiable_strip
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalPrincipalX.continued_source_differentiable_strip
