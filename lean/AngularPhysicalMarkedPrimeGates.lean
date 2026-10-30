import AngularPhysicalMarkedDeletedSource
import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeleted
import OAI.NumberTheory.DirichletL.Detector.DetectorMomentPrimeGeometry

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.Angular.MarkedReference
open InverseRows
open InverseInitialDetectorSource (primeProfile)
open RawDictionary InverseInitialPhysicalSlots
open CubicEisenstein.AngularRawCoefficientGates InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap Filter CanonicalQuadraticSieve CanonicalRowCompletion
open DetectorDictionaryInverseMarkedReference
local notation "O"=>HeckeFamily.O

theorem deleted_large_eventually {Label Slot:Type*}[Fintype Label][Fintype Slot]
    (data:Label→RowData)(ell:Slot→ℝ)(hell:∀s,0<ell s) :
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<(Z^d)^(ell s/d) := by
  have ht:∀ᶠZ:ℝ in atTop,∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤Z),mul_div_cancel₀ _ hd.ne']
  exact ht j s

theorem deletedBase_supported (data:RowData)(I:Ideal O)
    (hI:(deletedBase data).idealHom I≠0) : CanonicalQuadraticSieve.Supported I := by
  by_contra hn
  exact hI (deletedBase_zero_unsupported data I hn)

theorem deleted_source_live_prime {Δ:ℝ}{D:Parameters.HighData Δ}
    (F:ProbeFinalAssembly.SourceData D)(data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
    (X:ℝ)(hX:0<X)(ζ:ℂ)(hζ:ζ.re≤1)
    (hlarge:((deletedBase data).modulus.absNorm:ℝ)<X)
    (P:Ideal O)(hP:P∈livePrimes M H F.W 2 X) :
    Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      (deletedBase data).idealHom P≠0 ∧ ‖(deletedBase data).idealHom P‖=1 ∧
      ‖star (primeProfile F.W X ζ P)/(deletedBase data).idealHom P‖≤1 := by
  have hd:=livePrime_data M H F.W 1 2 X hX F.complex_support P hP
  have hcop:=(deletedBase data).prime_coprime_of_norm_gt P hd.1
    (hlarge.trans_le (by simpa only [one_mul] using hd.2.2.1))
  have hn:=(deletedBase data).norm_idealHom_one_of_coprime P hd.1.ne_zero hcop
  have hne:=(deletedBase data).idealHom_ne_zero_of_coprime P hd.1.ne_zero hcop
  have hout:outside (excluded data) P := by
    by_contra hh
    exact hne (InverseDeletion.deleted_zero_outside (baseCharacter data) (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data)) P hh)
  refine ⟨hd.1,hout,hne,hn,?_⟩
  rw [norm_div,norm_star,hn,div_one]
  exact ProbeHighRowFamily.sourceMoment_primeProfile_norm F X ζ hζ P

#print axioms deleted_large_eventually
#print axioms deleted_source_live_prime
end SevenEighths.Angular.MarkedReference

end

end OAI
