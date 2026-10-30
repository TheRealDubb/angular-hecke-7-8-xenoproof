import AngularPhysicalSource
import OAI.NumberTheory.DirichletL.Inversion.InitialDetectorSource

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.Angular.MarkedDictionary
open OAI.SevenEighths.Angular.Dyadic RawDictionary InverseInitialConjugateEnergy
open InverseInitialPoissonBridge UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

theorem indexed_mark_initial {ι : Type*} (T : Finset ι) (P : ι→Ideal O) (A : ι→ℂ)
    (η : Ideal O →* ℂ) (χ : AngularCharacter) (u : O)
    (hrow : ∀I,χ.idealHom I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ→ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hc : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑i∈T,A i*χ.idealHom (P i))=
      ∑i∈T,A i*originalTotalPolynomial S (P i) η (fun _=>1)
        (twistedProfile W σ freq) Z r z u := by
  rw [inverse_eq_initial_source η χ u hrow W Z r σ freq hZ S hc]
  have hn : ((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ)=((Z^(-(r+z)/2):ℝ):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.rpow_add hZ]
    congr 2
    ring
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrow]
  simp only [heckeIdealCharacter_apply]
  calc
    _ = (((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ))*
      (A i*((moebius I:ℂ)*(η I*CanonicalRowCompletion.idealRowHom u I)*
      (η (P i)*CanonicalRowCompletion.idealRowHom u (P i))*
      twistedProfile W σ freq ((I.absNorm:ℝ)/Z^r))) := by ring
    _ = _ := by rw [hn];ring

theorem indexed_conjugate_mark_norm {ι : Type*} (T : Finset ι) (P : ι→Ideal O) (A : ι→ℂ)
    (η : Ideal O →* ℂ) (χ : AngularCharacter) (u : O)
    (hrow : ∀I,χ.idealHom I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ→ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hc : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S)
    (hη : ∀i∈T,A i≠0 → η (P i)≠0) :
    ‖polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑i∈T,A i*star (CanonicalRowCompletion.idealRowHom u (P i)))‖=
      ‖∑i∈T,(star (A i)/η (P i))*originalTotalPolynomial S (P i) η (fun _=>1)
        (twistedProfile W σ freq) Z r z u‖ := by
  have hm : (∑i∈T,(star (A i)/η (P i))*χ.idealHom (P i))=
      star (∑i∈T,A i*star (CanonicalRowCompletion.idealRowHom u (P i))) := by
    simp only [star_sum,star_mul,star_star]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : A i=0
    · simp [ha]
    · rw [hrow]
      field_simp [hη i hi ha]
  rw [←indexed_mark_initial T P (fun i=>star (A i)/η (P i)) η χ u hrow W Z r z σ freq hZ S hc,hm]
  simp only [norm_mul,norm_star]

#print axioms indexed_mark_initial
#print axioms indexed_conjugate_mark_norm
end SevenEighths.Angular.MarkedDictionary
end
end OAI
