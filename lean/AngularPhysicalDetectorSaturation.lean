import AngularPhysicalDetectorActualUpper
import OAI.NumberTheory.DirichletL.Hecke.DetectorSaturation

noncomputable section
open scoped Classical Topology ContDiff ComplexConjugate
open Set Metric Complex MeasureTheory Filter
namespace OAI.SevenEighths.Angular.PhysicalDetectorDyadic
open OAI.SevenEighths.Angular.Dyadic FamilyContinuation PhysicalLogarithmic
open PhysicalReciprocal (presentationComplexity)
open HeckeDeletionBounds
open HeckeDetectorDyadicProfiles HeckeDetectorProfiles HeckeDetectorFrequency
open HeckeDetectorSaturation (logarithmic_cost_eventually normalized_product_lower)
open HeckeDyadic (constant_absorbed_eventually)
theorem actual_saturation (angularOrder : ℕ) (R dmax τ ε e κ η Clower : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε/2) (hClower : 0≤Clower) :
    ∃ U₀ : ℝ, ∀ Z d : ℝ, 1≤Z → 0≤d → d≤dmax → 2<Z^τ →
      U₀≤Z^d → 1<Z^d →
      ∀ {ι : Type*} [Fintype ι] (χ : ι→AngularCharacter) (horder : ∀ j, (χ j).k.natAbs≤angularOrder)
        (hχ : ∀ j, ((χ j).k≠0 ∨ (χ j).residue≠1)) (a : ℝ) (i : ℕ),
        51/100≤a → a≤1 →
        PhysicalDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))<a+2*e →
        ∀ j : ι, ∀ Dstar r m σ freq : ℝ,
        (χ j).modulus.absNorm≤Z^d → 0<Dstar →
        0≤r → r≤R → 0≤m → m≤R → (Z^d)^r≤4*Dstar →
        a≤σ → σ≤1 → |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
        (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
        let M := polynomial (χ j) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar ((Z^d)^r))
          ((Z^d)^r) σ freq
        let S := polynomial (χ j) false positiveAnnular ((Z^d)^m) σ freq
        1≤Clower*(Real.logb 2 (Z^d))^2*((Z^d)^r)^(1/2-σ)*((Z^d)^m)^(1/2-σ)*(‖M‖*‖S‖) →
        m≤1/2+75*ε ∧ (Z^d)^((2*a-1)*r-2*ε)≤‖M‖^2 ∧
          (Z^d)^((2*a-1)*m-2*ε)≤‖S‖^2 := by
  obtain ⟨Cu,hCu,hupper⟩ := simultaneous_upper angularOrder R dmax τ (ε/2) e κ η
    hR hdmax hτ (by linarith) he he' hκ hκ' hη hbudget
  have hev := (logarithmic_cost_eventually Clower ε hε).and
    (constant_absorbed_eventually Cu (ε/2) (by linarith))
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨U₀,?_⟩
  intro Z d hZ hd hd' hT hlarge hU ι _ χ horder hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσ hσ' hfreq hheight M S hprod
  have hσlo : 51/100≤σ := ha.trans hσ
  obtain ⟨hcost,hconst⟩ := hU₀ (Z^d) hlarge
  obtain ⟨hMu,hSu⟩ := hupper Z d hZ hd hd' hT χ horder hχ a i ha ha' hmax j Dstar r m σ freq
    hQ hDs hr hrR hm hmR hratio hσlo hσ' hfreq hheight
  have hp := normalized_product_lower (Z^d) r m σ a ε
    (Clower*(Real.logb 2 (Z^d))^2) ‖M‖ ‖S‖ hU hr hm hσ
    (mul_nonneg hClower (sq_nonneg _)) (norm_nonneg _) (norm_nonneg _) hcost hprod
  have hbound (x : ℝ) : Cu*(Z^d)^(x+ε/2)≤(Z^d)^(x+ε) := by
    calc
      _ ≤ (Z^d)^(ε/2)*(Z^d)^(x+ε/2) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg (by linarith) _)
      _ = _ := by rw [←Real.rpow_add (by linarith : 0<Z^d)]; congr 1; ring
  exact Detector.simultaneous_saturation hU (by linarith) hε.le (sq_nonneg _) (sq_nonneg _)
    hp (hMu.trans (hbound _)) (hSu.trans (hbound _))

end OAI.SevenEighths.Angular.PhysicalDetectorDyadic


#print axioms OAI.SevenEighths.Angular.PhysicalDetectorDyadic.actual_saturation
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorDyadic.actual_saturation
