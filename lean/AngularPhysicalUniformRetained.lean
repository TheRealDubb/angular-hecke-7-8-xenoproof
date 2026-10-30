import AngularPhysicalRetainedWeighted
import AngularPhysicalReflectionChoices
import OAI.NumberTheory.DirichletL.Moments.ReflectedChoiceEnergy
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace OAI.SevenEighths.Angular.UniformRetained
open Dyadic AnnularFourier CenteredMomentSectorLocalization CenteredMomentScaleSupremum
open CenteredMomentReflectionWeightedEnergy (Index)
open CenteredMomentReflectedTruncation (retainedAnnuli)
open RetainedWeighted UniformReflectionApproximation ReflectionChoices
open OriginalReflectionApproximation (radical_le_original)
open CenteredMomentNaturalPrimitive
theorem actual_retained_uniform_energy (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (epsilon : ℝ)
    (hepsilon : 0<epsilon) (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(G : ι→𝓢(ℝ,ℂ))(χ ψ : ι→AngularCharacter)(P : ι→ℂ)(X R ly omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d lo hi low high D E Rcap : ℝ),
      (∀i,(ψ i).k.natAbs=angularOrder) → (∀i,0<X i) → 0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0<dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2∈retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2)∈Set.Icc lo hi) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedSource (χ i) (ψ i) a b ha (G i) (X i) (R i)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨H,Cp,hCp,hp⟩ := actual_independent_choices angularOrder a b ha B J
  obtain ⟨Cw,hCw,hw⟩ := actual_retained_weighted_energy epsilon hepsilon
  refine ⟨H,Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ G χ ψ P X R ly omega Wshort c d lo hi low high D E Rcap
    horders hX hd hshort hshortsmooth hlh hlw hly hgeom hD hE hGD hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let s (i : ι) (u : α i) := dyadicScale u.2
  let Y (i : ι) (u : α i) := s i u*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2
  let keep (i : ι) (u : α i) := u.2∈retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  have hchoice := hp (fun i=>(ψ i).k) horders G χ P s Y keep ly omega Wshort c d lo hi low high D E
    hd hshort hshortsmooth hlh hlw hly
    (fun i u=>dyadicScale_pos u.2)
    (fun i u hu=>⟨mul_pos (dyadicScale_pos u.2) (dualScale_pos _ _ _ (hX i) _ _),
      hgeom i u _ hu⟩) hD hE hGD henergy
  let P' (i : ι) := polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i
  have hselected (u : ∀i,α i) :
      (∑i,‖retainedColumn (χ i) (ψ i) (profile (ψ i).k a b ha (G i)) (X i) (R i) (hX i) B (P' i) (u i)‖^2)≤
        Cp*D^2*(1+2*(hi-lo))*(1+2*(high-low))*E := by
    change (∑i,‖if keep i (u i) then
      polynomial (χ i).conjugate false
        (fun x=>(annulus x:ℂ)*((1+s i (u i))^B:ℂ)*profile (ψ i).k a b ha (G i) (s i (u i)*x))
        (Y i (u i)) 0 0 * P' i else 0‖^2) ≤ _
    simpa only [P',mul_assoc] using hchoice u
  have hh:=hw χ ψ a b ha G X R hX (fun _=>B) P' (fun _=>hB)
    Rcap _ hRcap hcap hselected
  simp only [P',←mul_assoc] at hh
  convert hh using 1 <;> ring

open Filter CenteredMomentReflectionRetainedLength CenteredMomentReflectionTailMass
open CenteredMomentReflectionDeletion (subset_product_norm_pos)
theorem eventually_natural_choice_geometry (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : AngularCharacter)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      let S := redundantSet χ.modulus ψ.modulus
      ∀u : Index S,
      let Y := (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈u.1.1.val,P):ℝ)/(Z^a*CenteredMomentReflectionDeletion.norm u.1.2.val)
      ∀hY : 0<Y,u.2∈retainedAnnuli (Z^(xi/4)) Y hY →
      1≤dyadicScale u.2*Y ∧
      0≤Real.log (dyadicScale u.2*Y) ∧
      Real.log (dyadicScale u.2*Y)≤(M-a+xi)*Real.log Z := by
  filter_upwards [eventually_actual_retained_length C 1 xi hC le_rfl hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod
  dsimp only
  intro u hY hu
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hD := subset_product_norm_pos u.1.1.val
    (fun P hP=>hS P ((Finset.mem_powerset.mp u.1.1.property) hP))
  have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤C*Z^M := by
    have hh : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by exact_mod_cast hcap
    exact hh.trans hmod
  have hh := hZ.2 M a _ _ _ _ hQ hD hc
    (subset_norm_le _ _ hS (Finset.mem_powerset.mp u.1.1.property))
    (restoration_norm_one _ u.1.2) u.2 hY hu
  simp only [one_mul] at hh
  refine ⟨hh.1,Real.log_nonneg hh.1,?_⟩
  have hz : 0<Real.log Z := Real.log_pos hZ.1
  have hlog := hh.2.2
  rw [Real.logb] at hlog
  exact (div_le_iff₀ hz).mp hlog

theorem actual_natural_retained_energy (angularOrder:ℕ) (a b:ℝ) (ha:0<a) (epsilon Cscale xi : ℝ)
     (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(G : ι→𝓢(ℝ,ℂ))(χ ψ : ι→AngularCharacter)(P : ι→ℂ)(omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort D E Rcap : ℝ),
      (∀i,(ψ i).k.natAbs=angularOrder) → 0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      (∀i,(ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0<D → 0≤E → (∀i,H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i)≤D) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedSource (χ i) (ψ i) a b ha (G i) (Z^along) (Z^(xi/4))*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*D^2*(1+2*(max 0 (M-along+xi)*Real.log Z))*E := by
  obtain ⟨H,C,hC,hb⟩ := actual_retained_uniform_energy angularOrder a b ha epsilon hepsilon B J hB
  refine ⟨H,C,hC,?_⟩
  filter_upwards [eventually_natural_choice_geometry Cscale xi hscale hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ G χ ψ P omega Wshort c d M along bshort D E Rcap horders hd hshort hshortsmooth
    hnatural hmod hD hE hGD hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  have hlog : 0≤Real.log Z := (Real.log_pos hZ.1).le
  have hexp : Real.exp (bshort*Real.log Z)=Z^bshort := by
    rw [Real.rpow_def_of_pos hz,mul_comm]
  have hgeom (i : ι) (u : Index (sourcePrimes (χ i) (ψ i)))
      (hY : 0<dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)
      (hu : u.2∈CenteredMomentReflectedTruncation.retainedAnnuli (Z^(xi/4))
        (dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2) hY) :
      Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)∈
        Set.Icc 0 (max 0 (M-along+xi)*Real.log Z) := by
    have hh := hZ.2 (χ i) (ψ i) M along (hnatural i) (hmod i) u hY hu
    exact ⟨hh.2.1,hh.2.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)⟩
  have hrad (i : ι) : (Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap :=
    (radical_le_original (χ i) (ψ i) (hnatural i)).trans (hcap i)
  have hh := hb G χ ψ P (fun _=>Z^along) (fun _=>Z^(xi/4)) (fun _=>bshort*Real.log Z) omega
    Wshort c d 0 (max 0 (M-along+xi)*Real.log Z) (bshort*Real.log Z) (bshort*Real.log Z)
    D E Rcap horders (fun _=>Real.rpow_pos_of_pos hz _) hd hshort hshortsmooth
    (mul_nonneg (le_max_left _ _) hlog) le_rfl (fun _=>⟨le_rfl,le_rfl⟩) hgeom
    hD hE hGD hRcap hrad (by
      intro v j k x hx y hy
      have hey : y=bshort*Real.log Z := le_antisymm hy.2 hy.1
      simpa only [hey,hexp] using henergy v j k x hx)
  simpa only [hexp,sub_zero,sub_self,mul_zero,add_zero,mul_one] using hh


end OAI.SevenEighths.Angular.UniformRetained

#print axioms OAI.SevenEighths.Angular.UniformRetained.actual_retained_uniform_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.UniformRetained.actual_retained_uniform_energy

#print axioms OAI.SevenEighths.Angular.UniformRetained.eventually_natural_choice_geometry
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.UniformRetained.eventually_natural_choice_geometry

#print axioms OAI.SevenEighths.Angular.UniformRetained.actual_natural_retained_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.UniformRetained.actual_natural_retained_energy
