import AngularPhysicalReflectionWeighted
import AngularPhysicalUniformReflectionApproximation
import AngularPhysicalReflectedNormalization
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace OAI.SevenEighths.Angular.RetainedWeighted
open CenteredMomentNaturalPrimitive CenteredMomentSectorLocalization
open CenteredMomentReflectionDeletion (SmoothIdeal norm)
open CenteredMomentReflectionWeightedEnergy (Index)
open CenteredMomentReflectedAnnuli (annularProfile annularMass)
open CenteredMomentReflectedTruncation (retainedAnnuli)
open ReflectionMass ReflectionWeighted AnnularFourier
open OriginalReflectionApproximation (finiteAnnularColumn)
open UniformReflectionApproximation (retainedSource)
local notation "O" => ActualEisensteinCubic.O
abbrev sourcePrimes (χ ψ : AngularCharacter) := redundantSet χ.modulus ψ.modulus

def dualScale (χ ψ : AngularCharacter) (X : ℝ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D.val,P):ℝ)/(X*norm H.val)

lemma dualScale_pos (χ ψ : AngularCharacter) (X : ℝ) (hX : 0<X)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    0<dualScale χ ψ X D H := by
  have hD : (∏P∈D.val,P : Ideal O)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>
    (redundantSet_prime χ.modulus ψ.modulus P ((Finset.mem_powerset.mp D.property) hP)).ne_zero)
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hd : 0<(Ideal.absNorm (∏P∈D.val,P):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  exact div_pos (mul_pos hQ hd) (mul_pos hX (CenteredMomentReflectionDeletion.norm_pos H.val))


def normalizedSource (F:ℝ→ℂ) (B:ℕ) (s:ℝ) (x:ℝ):ℂ :=
  (annulus x:ℂ)*((1+s)^B:ℂ)*F (s*x)

lemma annular_normalization (χ:AngularCharacter) (F:ℝ→ℂ) (B:ℕ) (k:ℤ) (Y:ℝ):
    (Real.sqrt (dyadicScale k):ℂ)*Dyadic.polynomial χ false
      (annularProfile F (dyadicScale k)) (dyadicScale k*Y) 0 0 =
    (annularMass B k:ℂ)*Dyadic.polynomial χ false
      (normalizedSource F B (dyadicScale k)) (dyadicScale k*Y) 0 0 := by
  have hf:normalizedSource F B (dyadicScale k)=
      (fun x=>((1+dyadicScale k)^B:ℂ)*annularProfile F (dyadicScale k) x):=by
    funext x
    dsimp [normalizedSource,annularProfile]
    ring
  rw [hf,NormalizedReflectionEnergy.polynomial_const,←mul_assoc]
  have hp:(1+dyadicScale k)^B≠0:=ne_of_gt (by have := dyadicScale_pos k;positivity)
  have hc:(annularMass B k:ℂ)*((1+dyadicScale k)^B:ℂ)=(Real.sqrt (dyadicScale k):ℂ):=by
    have hr:annularMass B k*(1+dyadicScale k)^B=Real.sqrt (dyadicScale k):=
      div_mul_cancel₀ _ hp
    exact_mod_cast hr
  rw [hc]

def retainedColumn (χ ψ:AngularCharacter) (F:ℝ→ℂ) (X R:ℝ) (hX:0<X)
    (B:ℕ) (P:ℂ) (u:Index (sourcePrimes χ ψ)):ℂ :=
  if u.2∈retainedAnnuli R (dualScale χ ψ X u.1.1 u.1.2)
      (dualScale_pos χ ψ X hX u.1.1 u.1.2) then
    Dyadic.polynomial χ.conjugate false (normalizedSource F B (dyadicScale u.2))
      (dyadicScale u.2*dualScale χ ψ X u.1.1 u.1.2) 0 0 *P
  else 0

theorem finiteAnnularColumn_normalized (χ ψ:AngularCharacter) (F:ℝ→ℂ)
    (X R:ℝ) (hX:0<X) (B:ℕ) (P:ℂ)
    (D:(sourcePrimes χ ψ).powerset) (I:SmoothIdeal (sourcePrimes χ ψ)):
    finiteAnnularColumn χ.conjugate F R (dualScale χ ψ X D I)*P =
      ∑'k:ℤ,(annularMass B k:ℂ)*retainedColumn χ ψ F X R hX B P ((D,I),k) := by
  rw [finiteAnnularColumn,dite_eq_left (dualScale_pos χ ψ X hX D I),
    tsum_eq_sum (s:=retainedAnnuli R (dualScale χ ψ X D I) (dualScale_pos χ ψ X hX D I))
      (fun k hk=>by simp only [retainedColumn,ite_eq_right hk,mul_zero]),Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [retainedColumn,ite_eq_left hk,annular_normalization]
  ring

theorem retainedSource_eq_weighted (χ ψ:AngularCharacter) (a b:ℝ) (ha:0<a)
    (G:𝓢(ℝ,ℂ)) (X R:ℝ) (hX:0<X) (B:ℕ) (P:ℂ)
    (hs:Summable (fun u:Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.conjugate (sourcePrimes χ ψ) B u*
        retainedColumn χ ψ (profile ψ.k a b ha G) X R hX B P u‖)):
    retainedSource χ ψ a b ha G X R*P =
      ∑'u:Index (sourcePrimes χ ψ),signedWeight ψ ψ.conjugate (sourcePrimes χ ψ) B u*
        retainedColumn χ ψ (profile ψ.k a b ha G) X R hX B P u := by
  rw [signed_series_reindex ψ ψ.conjugate (sourcePrimes χ ψ) B _ hs]
  change (∑D∈(sourcePrimes χ ψ).powerset,∑'I:SmoothIdeal (sourcePrimes χ ψ),
    coefficient ψ ψ.conjugate (sourcePrimes χ ψ) D I*
      finiteAnnularColumn χ.conjugate (profile ψ.k a b ha G) R
        ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm I.val)))*P = _
  rw [←Finset.sum_coe_sort (sourcePrimes χ ψ).powerset,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D _
  rw [←tsum_mul_right]
  apply tsum_congr
  intro I
  change (coefficient ψ ψ.conjugate (sourcePrimes χ ψ) D.val I*
    finiteAnnularColumn χ.conjugate (profile ψ.k a b ha G) R (dualScale χ ψ X D I))*P = _
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ _ X R hX B P D I]
  simp only [mul_assoc,tsum_mul_left]

theorem actual_retained_weighted_energy (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι:Type*} [Fintype ι],
      ∀(χ ψ:ι→AngularCharacter)(a b:ℝ)(ha:0<a)(G:ι→𝓢(ℝ,ℂ))(X R:ι→ℝ)
        (hX:∀i,0<X i)(B:ι→ℕ)(P:ι→ℂ),
      (∀i,2≤B i) → ∀(Rcap E:ℝ),1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀u:∀i,Index (sourcePrimes (χ i) (ψ i)),
        (∑i,‖retainedColumn (χ i) (ψ i) (profile (ψ i).k a b ha (G i))
          (X i) (R i) (hX i) (B i) (P i) (u i)‖^2)≤E) →
      (∑i,‖retainedSource (χ i) (ψ i) a b ha (G i) (X i) (R i)*P i‖^2)≤C*Rcap^ε*E := by
  obtain ⟨C,hC,hb⟩:=actual_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ ψ a b ha G X R hX B P hB Rcap E hRcap hcap hselection
  let f (i:ι):=retainedColumn (χ i) (ψ i) (profile (ψ i).k a b ha (G i))
    (X i) (R i) (hX i) (B i) (P i)
  have he:=hb (fun i=>sourcePrimes (χ i) (ψ i))
    (fun i=>redundantSet_prime (χ i).modulus (ψ i).modulus) ψ (fun i=>(ψ i).conjugate)
    B hB Rcap E hRcap hcap f hselection
  have hid (i:ι):=retainedSource_eq_weighted (χ i) (ψ i) a b ha (G i)
    (X i) (R i) (hX i) (B i) (P i) (he.1 i)
  simpa only [hid] using he.2
end OAI.SevenEighths.Angular.RetainedWeighted

#print axioms OAI.SevenEighths.Angular.RetainedWeighted.dualScale_pos
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RetainedWeighted.dualScale_pos

#print axioms OAI.SevenEighths.Angular.RetainedWeighted.annular_normalization
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RetainedWeighted.annular_normalization

#print axioms OAI.SevenEighths.Angular.RetainedWeighted.finiteAnnularColumn_normalized
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RetainedWeighted.finiteAnnularColumn_normalized

#print axioms OAI.SevenEighths.Angular.RetainedWeighted.retainedSource_eq_weighted
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RetainedWeighted.retainedSource_eq_weighted

#print axioms OAI.SevenEighths.Angular.RetainedWeighted.actual_retained_weighted_energy
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.RetainedWeighted.actual_retained_weighted_energy
