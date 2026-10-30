import AngularRawCoefficient
import OAI.NumberTheory.DirichletL.Reflection.FullRaw

/-! Exact conversion of the reflected angular series to its unrestricted
raw ideal index, preserving natural zeros and the entire scalar. Absolute
summability is proved for this actual kernel and coefficient, not assumed. -/
namespace OAI.CubicEisenstein.AngularFullRaw
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CompletedGauss CompletedDyadic SevenEighths.Angular
open SevenEighths.InverseMoment SevenEighths.InverseReflectedPhase
open AngularRawTail AngularRawCoefficient AngularControlledScalar AngularMixedReflection
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] {N a c : Eis} {mode : Bool}

theorem angularRawDualKernelTerm_summable_norm (order : ℕ)
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (scale ρ q B : ℝ) (hscale : 0<scale) (hρ : 0<ρ) (hq : 1<q)
    (hB : 0≤B) (β : ℕ→Ideal Eis→Ideal Eis→ℂ)
    (hβ : ∀m,∀I J : NonzeroDualIdeal,‖β m I.val J.val‖≤B) :
    Summable (fun x : ℕ×NonzeroDualIdeal×NonzeroDualIdeal =>
      ‖angularRawDualKernelTerm order V scale ρ q β x‖) := by
  obtain ⟨C,hC,hdec⟩:=AngularReflectionKernel.paperKernel_euler_power_decay order
    V a b ha hsupp hV 2 0
  have hq6 : 1<q^6 := one_lt_pow₀ hq (by norm_num)
  have hg : Summable (fun m : ℕ => ((q^6)⁻¹)^m) :=
    summable_geometric_of_lt_one (by positivity) ((inv_lt_one₀ (by positivity)).mpr hq6)
  have hi := nonzeroDualIdeal_inv_pow_summable 2 (by norm_num)
  have hj := nonzeroDualIdeal_inv_pow_summable 6 (by norm_num)
  have hij := hi.mul_of_nonneg hj (fun I=>by positivity) (fun J=>by positivity)
  have hs := hg.mul_of_nonneg hij (fun m=>by positivity) (fun IJ=>by positivity)
  have hmajor := hs.mul_left (B*C*(scale^2*ρ^6)⁻¹)
  apply hmajor.of_nonneg_of_le (fun _=>norm_nonneg _)
  intro x
  have hn:=nonzeroDualIdeal_norm_pos x.2.1
  have hb:=nonzeroDualIdeal_norm_pos x.2.2
  have hx : 0<scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3 := by positivity
  have hk := (hdec _ hx).2
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
  norm_num only [Nat.cast_ofNat] at hk
  have hr : (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^(-(2:ℝ))=
      ((scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*
      (Ideal.absNorm x.2.2.val:ℝ)^3)^2)⁻¹ := by
    rw [Real.rpow_neg hx.le,Real.rpow_two]
  rw [hr,rawDualKernel_inverse_square] at hk
  calc
    _ = ‖β x.1 x.2.1.val x.2.2.val‖*
        ‖AngularReflectionKernel.paperKernel order V
          (scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3)‖ := by
        rw [angularRawDualKernelTerm,norm_mul]
    _ ≤ B*(C*((scale^2*ρ^6)⁻¹*((q^6)⁻¹)^x.1 *
        (((Ideal.absNorm x.2.1.val:ℝ)^2)⁻¹*((Ideal.absNorm x.2.2.val:ℝ)^6)⁻¹))) :=
      mul_le_mul (hβ x.1 x.2.1 x.2.2) hk (norm_nonneg _) hB
    _ = _ := by ring

def angularLiteralRawSeries (order : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) (t : Eisˣ×RawTailIndex) : ℂ :=
  angularRawDualKernelTerm order (Vstar W) (literalRawScale G s X) 1 completedRamifiedStep
    (angularLiteralRawCoefficient order G D s hc j S t.1) t.2

lemma angularLiteralRawSeries_support (order : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    Function.support (angularLiteralRawSeries order G D s hc j S W X)⊆Set.range thetaRawIndex := by
  intro t ht
  have hp : Squarefree t.2.2.1.val ∧ primaryGenerator t.2.2.1.val≠0 ∧ primaryGenerator t.2.2.2.val≠0 := by
    by_contra hn
    exact ht (by simp only [angularLiteralRawSeries,angularRawDualKernelTerm,angularLiteralRawCoefficient,literalRawCoefficient,ite_eq_right hn,zero_mul])
  exact ⟨(t.1,t.2.1,⟨t.2.2.1.val,hp.1,hp.2.1⟩,⟨t.2.2.2.val,hp.2.2⟩),rfl⟩


theorem angularMixedReflected_eq_fullRaw (order : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (j : ι → ℕ) (S : Finset ι) (W : ℝ → ℂ) (X : ℝ) :
    angularMixedReflected order D s G.generator_ne_zero hc G.generator_good j S W X =
      (fixedRadialCoefficientScalar / thetaDerivativeScalar *
        s.stratumShapeFactor (c * ∏ i, G.generator i) *
        shapeOrderPhase s (c * ∏ i, G.generator i) ^ order) *
        ∑' t : Eisˣ × RawTailIndex, angularLiteralRawSeries order G D s hc j S W X t := by
  unfold angularMixedReflected
  rw [← thetaRawIndex_injective.tsum_eq (angularLiteralRawSeries_support order G D s hc j S W X)]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro t
  have hx : sourceCuspPhaseNumerator s.index (s.upper 0 0) (thetaFullFrequency t) =
      s.modelDualNumerator t.1 t.2.1 t.2.2.1.val t.2.2.2.val := by
    rw [thetaFullFrequency_eq_fixedCuspArrayIndex]
    rfl
  unfold fixedSeriesTerm
  rw [physical_full_index_kernel_argument, hx, thetaFullFrequency_eq_fixedCuspArrayIndex]
  unfold angularLiteralRawSeries angularRawDualKernelTerm angularLiteralRawCoefficient
    literalRawCoefficient thetaRawIndex literalRawScale fullIndexDenominator
  rw [ite_eq_left ⟨t.2.2.1.property.1,t.2.2.1.property.2,t.2.2.2.property⟩]
  dsimp only
  simp only [ramifiedScale, one_mul]
  ring

theorem angularLiteralRawSeries_summable_norm (order : ℕ) (G : PrimeFamily ι)
    (D : ControlledStratumArithmetic G.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N) (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ i, ringChar (Eis⧸G.ideal i)≠2) (j : ι→ℕ) (hj : ∀ i, j i<6)
    (S : Finset ι) (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    Summable (fun t : Eisˣ×RawTailIndex => ‖angularLiteralRawSeries order G D s hc j S W X t‖) := by
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨?_,(hasSum_fintype _).summable⟩
  intro u
  exact angularRawDualKernelTerm_summable_norm order (Vstar W) lo hi hlo (Vstar_support W lo hi hWs)
    (Vstar_contDiff W lo hi hlo hWs hW) (literalRawScale G s X) 1 completedRamifiedStep
    (Ideal.absNorm (∏ i,G.ideal i):ℝ) (literalRawScale_pos G s hc X hX) (by norm_num)
    completedRamifiedStep_gt_one (Nat.cast_nonneg _) (angularLiteralRawCoefficient order G D s hc j S u)
    (angularLiteralRawCoefficient_norm order G D s hc hN hbase hchar j hj S u)

#print axioms angularMixedReflected_eq_fullRaw
#print axioms angularLiteralRawSeries_summable_norm
end
end OAI.CubicEisenstein.AngularFullRaw
