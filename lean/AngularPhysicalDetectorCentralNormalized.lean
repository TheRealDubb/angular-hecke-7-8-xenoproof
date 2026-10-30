import AngularPhysicalDetectorCentralSlots
import OAI.NumberTheory.DirichletL.Detector.HighRowsCentralQuotient

namespace OAI

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
noncomputable section
namespace SevenEighths.Angular.PhysicalDetectorHigh
open ProbeHighRowFamily (unitPart unitPart_coprime multiplicity_lt_six row_phase_ramified
  markExclusions mem_markExclusions markedSourceExclusions marked_firstTail FirstTail)
open HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

theorem actual_central_unramified_normalized (η : AngularCharacter) (u : FreeRow) (P : ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (480:ℝ)≤P.val.absNorm)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖idealUnramifiedCorrection η u P x w z‖ ∧
    ‖continuedCompensatedLocal η u P hs x w z
        (star (η.idealHom P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
      idealUnramifiedCorrection η u P x w z+star (idealRowHom u.val P.val)‖≤
        1440*(P.val.absNorm:ℝ)^(-(51/100:ℝ)) := by
  have heta := η.norm_idealHom_one_of_coprime P.val P.property.ne_zero hη
  have hv := row_phase_norm_one_of_not_dvd u P hs hn
  have hA := actualAPhase_norm_le_one η (primaryGenerator P.val)
  constructor
  · exact unramifiedClosed_central_lower _ a e _ _ _ x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  · have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
    have hV : ‖coordV P.val.absNorm z‖<1 := by
      rw [coordV_norm _ hQ0]
      exact (rpow_le_half _ _ (by linarith) (by rw [hz];norm_num)).trans_lt (by norm_num)
    have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 :=
      (coordR_norm_le _ hQ0 _ x z hA).trans_lt
        ((rpow_le_half _ _ (by linarith) (by rw [hx,hz];linarith)).trans_lt (by norm_num))
    rw [continuedCompensatedLocal_unramified η u P hs hn x w z hV hR]
    exact unramifiedSelected_central_quotient _ a e _ _ _ x w z hQ ha ha1 he he1 hA heta hv hx hw hz
end SevenEighths.Angular.PhysicalDetectorHigh
end

end OAI

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_central_unramified_normalized
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_central_unramified_normalized
