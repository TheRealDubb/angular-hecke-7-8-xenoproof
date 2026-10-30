import AngularPhysicalReflectedTailControl

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.ReflectionTails
open AnnularFourier
open PlainDeletion (polynomial_plain)
open CenteredMomentComparisonReflection (ideal_norm_rpow_summable discarded_rapid_control normalized_power_eq)
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

theorem actual_reflected_small_negligible (angularOrder:ℕ) (a b xi saving : ℝ) (ha : 0<a) (hxi : 0<xi) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀(η : AngularCharacter)(t Y Z : ℝ),
      1≤Z → 0<Y → Y≤Z^(-xi) →
      ‖Dyadic.polynomial η false
        (profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t)) Y 0 0‖≤
        C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨B,hB⟩ := exists_nat_gt (max (2:ℝ) (saving/xi+1/2))
  have hB2 : 2≤B := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hB))
  have hBp : 0≤(B:ℝ)-1/2 := by have := (le_max_left _ _).trans_lt hB;linarith
  have hsav : saving≤xi*((B:ℝ)-1/2) := by
    have hh := (le_max_right _ _).trans_lt hB
    have hh' : saving/xi≤(B:ℝ)-1/2 := by linarith
    exact (div_le_iff₀ hxi).mp hh' |>.trans_eq (mul_comm _ _)
  obtain ⟨n,hn⟩ := actual_reflected_absolute_bound angularOrder a b ha B hB2
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hbound⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro k hk η t Y Z hZ hY hYZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  apply (hbound k hk η t Y hY).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [normalized_power_eq Y hY B]
  calc
    _≤(Z^(-xi))^((B:ℝ)-1/2) := Real.rpow_le_rpow hY.le hYZ hBp
    _=Z^((-xi)*((B:ℝ)-1/2)) := (Real.rpow_mul hz.le _ _).symm
    _≤Z^(-saving) := Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem actual_reflected_upper_negligible (angularOrder:ℕ) (a b xi saving L Cscale : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hCscale : 0<Cscale) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀k:ℤ,k.natAbs=angularOrder → ∀(η : AngularCharacter)(t Y Z : ℝ),
      1≤Z → 0<Y → Y≤Cscale*Z^L →
      ‖Dyadic.polynomial η false
        (fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
          profile k a b ha (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) x) Y 0 0‖≤
        C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((saving+L*(3/2))/(xi/2))
  have hsav : saving+L*(3/2)≤xi/2*(A:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : 0<xi/2)).mp hA.le
    nlinarith
  obtain ⟨n,hn⟩ := actual_reflected_discarded_bound angularOrder a b ha A 2 (by omega)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hbound⟩ := hn W hs hW
  refine ⟨C*Cscale^(3/2:ℝ),by positivity,?_⟩
  intro k hk η t Y Z hZ hY hYZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hR : 0<Z^(xi/2) := Real.rpow_pos_of_pos hz _
  have hp : Y^2/Real.sqrt Y≤Cscale^(3/2:ℝ)*Z^(L*(3/2)) := by
    rw [normalized_power_eq Y hY 2]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
    calc
      _≤(Cscale*Z^L)^(3/2:ℝ) := Real.rpow_le_rpow hY.le hYZ (by norm_num)
      _=_ := by rw [Real.mul_rpow hCscale.le (by positivity),←Real.rpow_mul hz.le]
  have hd : (Z^(xi/2))^A=Z^((xi/2)*(A:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  calc
    _≤C*(1+‖t‖)^n*(Y^2/Real.sqrt Y)/(Z^(xi/2))^A := hbound k hk η t Y _ hY hR
    _≤C*(1+‖t‖)^n*(Cscale^(3/2:ℝ)*Z^(L*(3/2)))/(Z^(xi/2))^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=(C*Cscale^(3/2:ℝ))*(1+‖t‖)^n*Z^(L*(3/2)-(xi/2)*(A:ℝ)) := by
      rw [hd,Real.rpow_sub hz]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)


end OAI.SevenEighths.Angular.ReflectionTails

#print axioms OAI.SevenEighths.Angular.ReflectionTails.actual_reflected_small_negligible
#print axioms OAI.SevenEighths.Angular.ReflectionTails.actual_reflected_upper_negligible
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionTails.actual_reflected_upper_negligible
