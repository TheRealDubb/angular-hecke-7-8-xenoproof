import AngularRawReferenceBound
import AngularPhysicalUniform
import OAI.NumberTheory.DirichletL.Detector.DetectorMomentData

noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Angular.RawProfiles
open InverseRows RawCompact InverseMoment
open HeckeInverseAmplification (scaleProfile twistProfile logTest)
open HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount
open DetectorDictionaryInverseClippedUniform
theorem fixed_raw_profiles (angularOrder : ℕ) (c κ:ℝ)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,data.η.k=(angularOrder:ℤ)→∃C:ℝ,0<C ∧
      ∀reverse:Bool,∀n:ℕ,n≤2→∀U:ℝ,0<U→∀tstar r:ℝ,
      ∀s∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤height→t∈Set.Icc (-height) height→
      let W:=twistProfile (logTest (orientedProfile reverse (inverseTest U tstar r)) n) s t;
      RawMoment data W c κ (C*(1+height)^J) ∧
      RawMoment data (scaleProfile W) c κ (C*(1+height)^J):=by
  obtain ⟨J,hreference⟩:=CubicEisenstein.AngularRawReferenceBound.raw_reference_moment angularOrder
    referenceWindow (1/18) (13/4) c κ (by norm_num) (by norm_num)
    (fun x hx=>referenceWindow_support (subset_tsupport _ hx)) hc hκ
  obtain ⟨K,C,hC,hfamily⟩:=RawUniform.raw_pair_height_uniform J
  refine ⟨K,?_⟩
  intro data hk
  obtain ⟨A,hA,href⟩:=hreference data hk
  exact ⟨A*C,mul_pos hA hC,hfamily data c κ A hA.le href⟩


set_option pp.deepTerms true in
#check @fixed_raw_profiles
#print axioms fixed_raw_profiles
end OAI.SevenEighths.Angular.RawProfiles
