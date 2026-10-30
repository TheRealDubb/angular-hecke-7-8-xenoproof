import AngularHybridCoefficient
import OAI.NumberTheory.DirichletL.Reflection.RawCoefficient

/-! Fixed-order tail bound for the actual angular reflection kernel.
The finite set of source seminorms and the constant are chosen before all
source profiles, moving rows, scales and coefficient arrays. They may depend
on the fixed angular order. The cube index remains unrestricted. -/

namespace OAI.CubicEisenstein.AngularRawTail
open scoped Classical BigOperators ContDiff SchwartzMap
open ActualEisensteinCubic CompletedGauss SevenEighths.InverseReflectedPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def angularRawDualKernelTerm (order : ℕ) (V : ℝ → ℂ) (scale ρ q : ℝ)
    (β : ℕ → Ideal Eis → Ideal Eis → ℂ) (x : RawTailIndex) : ℂ :=
  β x.1 x.2.1.val x.2.2.val * AngularReflectionKernel.paperKernel order V
    (scale * (ρ * q ^ x.1) ^ 3 * (Ideal.absNorm x.2.1.val : ℝ) *
      (Ideal.absNorm x.2.2.val : ℝ) ^ 3)

theorem angular_raw_kernel_tail (order : ℕ) (a b q : ℝ) (ha : 0<a) (hq : 1<q) (A : ℕ) :
    ∃ (S : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ (V : SchwartzMap ℝ ℂ), Function.support (V : ℝ→ℂ)⊆Set.Icc a b →
    ∀ (scale ρ B T : ℝ), 0<scale → 0<ρ → 0≤B → 0<T →
    ∀ (β : ℕ→Ideal Eis→Ideal Eis→ℂ),
      (∀ m, ∀ I J : NonzeroDualIdeal, ‖β m I.val J.val‖≤B) →
    ∀ cut : RawTailIndex→Prop,
      (∀ x, cut x → T≤scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3) →
    Summable (fun x => ‖if cut x then angularRawDualKernelTerm order V scale ρ q β x else 0‖) ∧
      ‖∑' x, if cut x then angularRawDualKernelTerm order V scale ρ q β x else 0‖≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*B*T^(-(A:ℝ))*(scale^2*ρ^6)⁻¹ := by
  obtain ⟨S,C,hC,hkernel⟩ := AngularReflectionKernel.paperKernel_euler_source_power_decay order a b ha (A+2) 0
  let D : ℝ := (∑' x,rawTailWeight q x)+1
  have hsum := rawTailWeight_summable q hq
  have hD : 0<D := by
    have h : 0≤∑' x,rawTailWeight q x := tsum_nonneg (rawTailWeight_nonneg q)
    dsimp only [D]
    linarith
  refine ⟨S,C*D,mul_pos hC hD,?_⟩
  intro V hV scale ρ B T hs hρ hB hT β hβ cut hcut
  let M : ℝ := C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V*B*T^(-(A:ℝ))*(scale^2*ρ^6)⁻¹
  have hM : 0≤M := by dsimp only [M]; positivity
  have hmajor : ∀ x : RawTailIndex,
      ‖if cut x then angularRawDualKernelTerm order V scale ρ q β x else 0‖≤M*rawTailWeight q x := by
    intro x
    by_cases hx : cut x
    · rw [ite_eq_left hx,angularRawDualKernelTerm,norm_mul]
      let arg := scale*(ρ*q^x.1)^3*(Ideal.absNorm x.2.1.val:ℝ)*(Ideal.absNorm x.2.2.val:ℝ)^3
      have harg : 0<arg := lt_of_lt_of_le hT (hcut x hx)
      have hk := (hkernel V hV arg harg).2
      simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hk
      have hp := tail_power_gain A T arg hT (hcut x hx)
      have hk' := hk.trans (mul_le_mul_of_nonneg_left hp (by positivity :
        0≤C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V))
      apply (mul_le_mul (hβ x.1 x.2.1 x.2.2) hk' (norm_nonneg _) hB).trans_eq
      dsimp only [M,arg]
      rw [rawDualKernel_inverse_square]
      unfold rawTailWeight
      ring
    · rw [ite_eq_right hx,norm_zero]
      exact mul_nonneg hM (rawTailWeight_nonneg q x)
  have hn := (hsum.mul_left M).of_nonneg_of_le (fun x => norm_nonneg _) hmajor
  refine ⟨hn,?_⟩
  calc
    _ ≤ ∑' x, ‖if cut x then angularRawDualKernelTerm order V scale ρ q β x else 0‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' x, M*rawTailWeight q x := hn.tsum_le_tsum hmajor (hsum.mul_left M)
    _ = M*(∑' x,rawTailWeight q x) := tsum_mul_left
    _ ≤ M*D := mul_le_mul_of_nonneg_left (by dsimp only [D]; linarith) hM
    _ = _ := by dsimp only [M]; ring

#print axioms angular_raw_kernel_tail
end
end OAI.CubicEisenstein.AngularRawTail
