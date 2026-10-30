import AngularPhysicalFrequencyScale
import AngularPhysicalAnnularConjugateEnergy
import OAI.NumberTheory.DirichletL.Moments.UniformReflectionScale
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace OAI.SevenEighths.Angular.ReflectionChoices
open Dyadic AnnularFourier
open CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentOneReflectionScaleEnergy (annulus_complex_support annulus_complex_smooth)
open CenteredMomentReflectedNormalization (actual_log_window)
theorem actual_rowwise_scales (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (A J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(orders:ι→ℤ),(∀i,(orders i).natAbs=angularOrder) → ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→AngularCharacter)(P : ι→ℂ)
      (s lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,lx i∈Set.Icc lo hi) → (∀i,ly i∈Set.Icc low high) →
      (∀i,0<s i) → 0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).conjugate false
        (fun x=>(annulus x:ℂ)*((1+s i)^A:ℂ)*profile (orders i) a b ha (G i) (s i*x))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  have hreal : ∀y,conj (CenteredMomentReflectedAnnuli.logWindow y)=
      CenteredMomentReflectedAnnuli.logWindow y := by
    intro y
    exact Complex.conj_ofReal _
  obtain ⟨H,C,hC,hbound⟩:=AnnularEnergy.actual_inverse_uniform angularOrder a b ha
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) hlog hwindow hreal A J
  refine ⟨H,C,hC,?_⟩
  intro ι _ orders horders G χ P s lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly hspos hD hE hGD henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i) false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        (polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := FrequencyScale.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=>hlx i) (fun i _=>hly i) (henergy v)
    rw [actual_log_window]
    simp only [←mul_assoc]
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by rw [←pow_mul,Nat.mul_comm J 2]
    apply hh.trans_eq
    rw [hp]
    ring
  have hh:=hbound orders horders G χ (fun i=>polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i)
    s (fun i=>Real.exp (lx i)) hspos (fun i=>Real.exp_pos _) D
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) hD (mul_nonneg hdx (mul_nonneg hdy hE)) hGD hfixed
  simp only [actual_log_window,←mul_assoc] at hh
  convert hh using 1

theorem actual_independent_choices (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (B J : ℕ) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀{α : ι→Type},
      ∀(orders:ι→ℤ),(∀i,(orders i).natAbs=angularOrder) → ∀(G : ι→𝓢(ℝ,ℂ))(χ : ι→AngularCharacter)(P : ι→ℂ)(s X : ∀i,α i→ℝ)(keep : ∀i,α i→Prop)
        (ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high D E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i u,0<s i u) → (∀i u,keep i u → 0<X i u ∧ Real.log (X i u)∈Set.Icc lo hi) → 0<D → 0≤E →
      (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      ∀u : ∀i,α i,
      (∑i,‖if keep i (u i) then polynomial (χ i).conjugate false
        (fun x=>(annulus x:ℂ)*((1+s i (u i))^B:ℂ)*profile (orders i) a b ha (G i) (s i (u i)*x))
        (X i (u i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i else 0‖^2)≤
        C*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_rowwise_scales angularOrder a b ha B J
  refine ⟨H,C,hC,?_⟩
  intro ι _ α orders horders G χ P s X keep ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hly hspos hgeom hD hE hGD henergy u
  let lx (i : ι) := if keep i (u i) then Real.log (X i (u i)) else lo
  let P' (i : ι) := if keep i (u i) then P i else 0
  have hlx (i : ι) : lx i∈Set.Icc lo hi := by
    dsimp [lx]
    split_ifs with hk
    · exact (hgeom i (u i) hk).2
    · exact ⟨le_rfl,hlh⟩
  have he (v : ℝ) (j k : Fin 2) (x : ℝ) (hx : x∈Set.Icc lo hi)
      (y : ℝ) (hy : y∈Set.Icc low high) :
      (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (-2*Real.pi*v)*
        polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P' i‖^2)
        ≤E*(1+‖v‖)^(2*J) := by
    apply (Finset.sum_le_sum (fun i _=>?_)).trans (henergy v j k x hx y hy)
    dsimp only [P']
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
      exact sq_nonneg _
  have hh := hb orders horders G χ P' (fun i=>s i (u i)) lx ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hlx hly (fun i=>hspos i (u i)) hD hE hGD he
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [lx,P']
  split_ifs with hk
  · rw [Real.exp_log (hgeom i (u i) hk).1]
  · simp


end OAI.SevenEighths.Angular.ReflectionChoices

#print axioms OAI.SevenEighths.Angular.ReflectionChoices.actual_rowwise_scales
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionChoices.actual_rowwise_scales

#print axioms OAI.SevenEighths.Angular.ReflectionChoices.actual_independent_choices
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.ReflectionChoices.actual_independent_choices
