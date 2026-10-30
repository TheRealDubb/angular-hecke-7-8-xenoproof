import AngularPhysicalDetectorActualPhysicalJoinBudget

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace OAI.SevenEighths.Angular.PhysicalDetectorHigh

def principalSignalE (p : ActualRetainedParameters) : ℝ :=
  min (((5/6)*p.rmin)/8) (1/2000)

def actualSignalSaving (p : ActualRetainedParameters) : ℝ :=
  min p.saving (((5/6)*p.rmin)/4)

/-- The principal comparison has a separate contour displacement. Its choice
does not alter the retained windows, slot lengths, or detector parameters. -/
lemma actual_principal_signal_budget (p : ActualRetainedParameters) :
    0<principalSignalE p ∧ principalSignalE p≤1/1000 ∧
    0<actualSignalSaving p ∧ actualSignalSaving p≤p.saving ∧
    p.normalizerLoss+actualSignalSaving p≤17/48000 ∧
    principalSignalE p+actualSignalSaving p≤(7/8)*((5/6)*p.rmin) := by
  rcases p.early_conditions with ⟨hew,hew1,hewM,hewr,he,he1,her,hrest⟩
  rcases p.mesh_conditions with ⟨hem,hem1,hR,hmesh,hnu,hcc,hcommon⟩
  rcases p.loss_conditions with ⟨hz,hm,hpad,hn,hd,hs,hl,hphase⟩
  have hr := p.slot_conditions.2.2.1
  rcases p.epsilon_conditions with ⟨heps,hepsr⟩
  have hN : (0:ℝ)≤p.N := Nat.cast_nonneg _
  have hNeps : 0≤(p.N+8)*p.eps := by positivity
  have hcount : 0≤159*p.epsw+p.epsm+p.R+7*p.nu+p.countCost := by positivity
  have hbudget := p.central_budget
  have hsave : actualSignalSaving p≤p.saving := min_le_left _ _
  have hsave2 : actualSignalSaving p≤((5/6)*p.rmin)/4 := min_le_right _ _
  have helo : principalSignalE p≤((5/6)*p.rmin)/8 := min_le_left _ _
  have hehi : principalSignalE p≤1/2000 := min_le_right _ _
  refine ⟨?_,by linarith,?_,hsave,?_,?_⟩
  · exact lt_min (by positivity) (by norm_num)
  · exact lt_min hs (by positivity)
  · linarith
  · linarith

/-- Join the same physical principal pool in both premises. Constants may
depend on the fixed target here; the positive exponent saving does not. -/
lemma actual_normalized_signal_join (p : ActualRetainedParameters)
    (beta Z Cdet Cprincipal : ℝ) (hZ : 1≤Z) (hdet0 : 0≤Cdet) (hpr0 : 0≤Cprincipal)
    (probe principal signal normalizer : ℂ)
    (hdet : ‖(probe-principal)/normalizer‖≤Cdet*Z^(beta-11/16-p.saving))
    (hpr : ‖principal/normalizer-signal‖≤Cprincipal*
      (Z^(beta-11/16-17/48000+p.normalizerLoss)+
       Z^(beta-11/16+principalSignalE p-(7/8)*((5/6)*p.rmin)))) :
    ‖probe/normalizer-signal‖≤(Cdet+2*Cprincipal)*Z^(beta-11/16-actualSignalSaving p) := by
  rcases actual_principal_signal_budget p with ⟨_,_,_,hs,hrem,hslot⟩
  have hd := Real.rpow_le_rpow_of_exponent_le hZ
    (show beta-11/16-p.saving≤beta-11/16-actualSignalSaving p by linarith)
  have hr := Real.rpow_le_rpow_of_exponent_le hZ
    (show beta-11/16-17/48000+p.normalizerLoss≤beta-11/16-actualSignalSaving p by linarith)
  have hp := Real.rpow_le_rpow_of_exponent_le hZ
    (show beta-11/16+principalSignalE p-(7/8)*((5/6)*p.rmin)≤beta-11/16-actualSignalSaving p by linarith)
  calc
    _=‖(probe-principal)/normalizer+(principal/normalizer-signal)‖ := by congr 1;ring
    _≤‖(probe-principal)/normalizer‖+‖principal/normalizer-signal‖ := norm_add_le _ _
    _≤Cdet*Z^(beta-11/16-p.saving)+Cprincipal*
        (Z^(beta-11/16-17/48000+p.normalizerLoss)+
         Z^(beta-11/16+principalSignalE p-(7/8)*((5/6)*p.rmin))) := add_le_add hdet hpr
    _≤Cdet*Z^(beta-11/16-actualSignalSaving p)+Cprincipal*
        (Z^(beta-11/16-actualSignalSaving p)+Z^(beta-11/16-actualSignalSaving p)) :=
      add_le_add (mul_le_mul_of_nonneg_left hd hdet0)
        (mul_le_mul_of_nonneg_left (add_le_add hr hp) hpr0)
    _=_ := by ring

end OAI.SevenEighths.Angular.PhysicalDetectorHigh

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_principal_signal_budget

#print axioms OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_normalized_signal_join
set_option pp.deepTerms true in
#check OAI.SevenEighths.Angular.PhysicalDetectorHigh.actual_normalized_signal_join
