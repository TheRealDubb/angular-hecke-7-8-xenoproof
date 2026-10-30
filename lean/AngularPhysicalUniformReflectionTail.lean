import AngularPhysicalDeletedReflectedTail
import AngularPhysicalAnnularFourierAbsoluteOrder
import OAI.NumberTheory.DirichletL.Moments.UniformReflectionApproximation
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.UniformReflectionTail
open AnnularFourier ReflectionTails ReflectionMass
open CenteredMomentReflectionDeletion (SmoothIdeal norm)
open CenteredMomentReflectionTailMass (dual_scale_bounds)
open CenteredMomentComparisonReflection (discarded_rapid_control normalized_power_eq)
open CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O
theorem discarded_bound (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (A B : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀(G : 𝓢(ℝ,ℂ))(χ : AngularCharacter)(Y R : ℝ),
      0<Y → 0<R →
      ‖Dyadic.polynomial χ false
        (fun x=>(discardedWeight R x:ℂ)*profile k a b ha G x) Y 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Y^B/Real.sqrt Y)/R^A := by
  obtain ⟨H,D,hD,hDb⟩ := absolute_order_euler_bound angularOrder a b ha (B+A) 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨H,K*D,mul_pos hK hD,?_⟩
  intro k hk G χ Y R hY hR
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hf : ∀x : ℝ,0<x → x^(B+A)*‖profile k a b ha G x‖≤
      D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := by
    intro x hx
    have hh := hDb k hk G 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) (B+A))
      (norm_nonneg _)).trans hh
  have hm := discarded_rapid_control _ A B (D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G)
    R (by positivity) hR hf
  exact (hKb χ _ ((D*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G)/R^A)
    Y (by positivity) hY hm).trans_eq (by ring)

theorem discarded_negligible (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (xi saving L Cscale : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀(G : 𝓢(ℝ,ℂ))(χ : AngularCharacter)(Y Z : ℝ),
      1≤Z → 0<Y → Y≤Cscale*Z^L →
      ‖Dyadic.polynomial χ false
        (fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*profile k a b ha G x) Y 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((saving+L*(3/2))/(xi/2))
  have hsav : saving+L*(3/2)≤xi/2*(A:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : 0<xi/2)).mp hA.le
    nlinarith
  obtain ⟨H,C,hC,hbound⟩ := discarded_bound angularOrder a b ha A 2 (by omega)
  refine ⟨H,C*Cscale^(3/2:ℝ),by positivity,?_⟩
  intro k hk G χ Y Z hZ hY hYZ
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hR : 0<Z^(xi/2) := Real.rpow_pos_of_pos hz _
  have hp : Y^2/Real.sqrt Y≤Cscale^(3/2:ℝ)*Z^(L*(3/2)) := by
    rw [normalized_power_eq Y hY 2]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
    calc
      _≤(Cscale*Z^L)^(3/2:ℝ) := Real.rpow_le_rpow hY.le hYZ (by norm_num)
      _=_ := by rw [Real.mul_rpow hscale.le (by positivity),←Real.rpow_mul hz.le]
  have hd : (Z^(xi/2))^A=Z^((xi/2)*(A:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  calc
    _≤C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Y^2/Real.sqrt Y)/(Z^(xi/2))^A :=
      hbound k hk G χ Y _ hY hR
    _≤C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        (Cscale^(3/2:ℝ)*Z^(L*(3/2)))/(Z^(xi/2))^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=(C*Cscale^(3/2:ℝ))*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        Z^(L*(3/2)-(xi/2)*(A:ℝ)) := by
      rw [hd,Real.rpow_sub hz]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

theorem deleted_discarded_negligible (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (xi saving L Cscale epsilon : ℝ)
    (hxi : 0<xi) (hscale : 0<Cscale) (hepsilon : 0<epsilon) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀(G : 𝓢(ℝ,ℂ))
      (S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)(η ηi χ : AngularCharacter)(Q X Z : ℝ),
      1≤Z → 0<Q → 0<X → Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X →
      let F := fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*profile k a b ha G x
      (∀D∈S.powerset,Summable (fun I : SmoothIdeal S=>coefficient η ηi S D I*
        Dyadic.polynomial χ false F
          (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0)) ∧
      ‖∑D∈S.powerset,∑'I : SmoothIdeal S,coefficient η ηi S D I*
        Dyadic.polynomial χ false F
          (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)) 0 0‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
          (Ideal.absNorm (∏P∈S,P):ℝ)^epsilon*Z^(-saving) := by
  obtain ⟨H,C,hC,hCb⟩ := discarded_negligible angularOrder a b ha xi saving L Cscale hxi hscale
  obtain ⟨D,hD,hDb⟩ := coefficient_column_bound epsilon hepsilon
  refine ⟨H,D*C,mul_pos hD hC,?_⟩
  intro k hk G S hS η ηi χ Q X Z hZ hQ hX hcap
  dsimp only
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hh := hDb S hS η ηi
    (fun E I=>Dyadic.polynomial χ false
      (fun x=>(discardedWeight (Z^(xi/2)) x:ℂ)*profile k a b ha G x)
      (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm I.val)) 0 0)
    (C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*Z^(-saving)) (by positivity) (by
      intro E hE I
      have hy := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) I Q X (Cscale*Z^L) hQ hX hcap
      exact hCb k hk G χ _ Z hZ hy.1 hy.2)
  exact ⟨hh.1,hh.2.trans_eq (by ring)⟩


end OAI.SevenEighths.Angular.UniformReflectionTail

#print axioms OAI.SevenEighths.Angular.UniformReflectionTail.discarded_bound
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.UniformReflectionTail.discarded_bound

#print axioms OAI.SevenEighths.Angular.UniformReflectionTail.discarded_negligible
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.UniformReflectionTail.discarded_negligible

#print axioms OAI.SevenEighths.Angular.UniformReflectionTail.deleted_discarded_negligible
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.UniformReflectionTail.deleted_discarded_negligible
