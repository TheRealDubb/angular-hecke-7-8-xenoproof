import AngularInverseProfileEndpoint
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint

set_option maxHeartbeats 1200000

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter Complex
namespace OAI.SevenEighths.Angular.PhysicalDetectorCount
open OAI.SevenEighths.Angular.Dyadic InverseRows
open HeckeInverseAmplification (FreeRow sourceExponent)
open HeckeDetectorCoefficientTransfer (orientedProfile orientedFrequency orientedFrequency_abs)
open HeckeDetectorInverseFiberCount (inverseTest)

/-- The unmarked inverse count is supplied by actual angular raw moments.
The premise is the literal detector spike, not an assumed moment estimate.
Constants depend on the fixed parent data, before all moving rows, conductors,
scales and chosen frequencies. The reversed presentation is retained. -/
theorem physical_inverse_count (angularOrder : ℕ)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a b B : ℝ) (ha : 0<a) (hab : a≤b) (hB : 0<B)
    (hφs : Function.support φ⊆Ioo a b) (hφB : ∀ y,φ y≤B)
    (R εm : ℝ) (hR : 0≤R) (hεm : 0<εm) :
    ∃ J : ℕ, ∃ U₀ : ℝ, 1<U₀ ∧
      ∀ data : RowData, data.η.k=(angularOrder:ℤ) → ∃ C : ℝ, 0<C ∧
      ∀ (U r δ ε : ℝ) (rows : Finset FreeRow)
        (χ : FreeRow→AngularCharacter) (reverse : Bool)
        (tstar height : ℝ) (σ freq : FreeRow→ℝ),
      U₀≤U → 0≤r → r≤R → 0≤height →
      (∀ u∈rows, ((Ideal.span {u.val}).absNorm:ℝ)≤U) →
      (∀ u∈rows, σ u∈Icc (0:ℝ) 1) →
      (∀ u∈rows, freq u∈Icc (-height) height) →
      (∀ u∈rows, ∀ I : Ideal O, (χ u).idealHom I =
        if reverse then conj ((data.character ⟨u.val,u.property.1⟩).idealHom I)
        else (data.character ⟨u.val,u.property.1⟩).idealHom I) →
      (∀ u∈rows, U^(δ*r-2*ε) ≤
        ‖polynomial (χ u) true (inverseTest U tstar r) (U^r) (σ u) (freq u)‖^2) →
      (rows.card:ℝ) ≤ C*(1+height)^J*U^(sourceExponent r-δ*r+2*ε+εm) ∧
      (∀ γ : ℝ, 0≤γ → 5/6≤δ → δ≤1 → 1-γ≤r →
        (rows.card:ℝ) ≤ C*(1+height)^J*U^(1-δ+2*ε+εm+γ)) := by
  obtain ⟨J,U₀,hU₀,hbound⟩ := InverseAmplification.fixed_profile_rowwise_endpoint angularOrder
    M H hH S φ hφ hφc hφp hφ0 hφne a b B ha hab hB hφs hφB R εm hR hεm
  refine ⟨J,U₀,hU₀,?_⟩
  intro data hk
  obtain ⟨C,hC,henergy⟩ := hbound data hk
  refine ⟨C,hC,?_⟩
  intro U r δ ε rows χ reverse tstar height σ freq hU hr hrR hheight hrows hσ hf hc hspike
  have hU1 : 1<U := hU₀.trans_le hU
  have hUp : 0<U := zero_lt_one.trans hU1
  have hf' : ∀ u∈rows, orientedFrequency reverse (freq u)∈Icc (-height) height := by
    intro u hu
    apply abs_le.mp
    rw [orientedFrequency_abs]
    exact abs_le.mpr (hf u hu)
  have he := henergy U hU r rows reverse tstar height σ
    (fun u => orientedFrequency reverse (freq u)) hr hrR hheight hrows hσ hf'
  have hsp : ∀ u∈rows, U^(δ*r-2*ε) ≤
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true
        (orientedProfile reverse (inverseTest U tstar r)) (U^r)
        (σ u) (orientedFrequency reverse (freq u))‖^2 := by
    intro u hu
    have hh := hspike u hu
    rw [CoefficientTransfer.norm_of_oriented_coefficients (χ u)
      (data.character ⟨u.val,u.property.1⟩) reverse (hc u hu) true _ _ _ _
      (Real.rpow_pos_of_pos hUp _)] at hh
    exact hh
  have hb := HeckeDetectorRowCount.card_of_energy rows _ U (δ*r-2*ε)
    (sourceExponent r+εm) (C*(1+height)^J) hUp hsp he
  have hcount : (rows.card:ℝ) ≤ C*(1+height)^J*U^(sourceExponent r-δ*r+2*ε+εm) := by
    convert hb using 1 <;> congr 2 <;> ring
  refine ⟨hcount,?_⟩
  intro γ hγ hδ hδhi hgeom
  have hsource : sourceExponent r=max 1 ((1+5*r)/6) := rfl
  rw [hsource] at hcount
  have hh := HeckeDetectorRowCount.high_bin_count (ε := 2*ε+εm)
    (by positivity : 0≤C*(1+height)^J) hU1.le hδ hδhi hγ hgeom
    (by simpa only [add_assoc] using hcount)
  simpa only [add_assoc] using hh

end OAI.SevenEighths.Angular.PhysicalDetectorCount


#print axioms OAI.SevenEighths.Angular.PhysicalDetectorCount.physical_inverse_count
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorCount.physical_inverse_count
