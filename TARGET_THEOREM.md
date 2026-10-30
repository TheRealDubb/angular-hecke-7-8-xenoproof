# Exact review target

## Family and normalization

Let K=Q(sqrt(-3)) and O=Z[omega], where omega is a primitive cube root of unity. For nonzero a, let alpha(a)=a/|a| under the fixed complex embedding. An `AngularCharacter` contains:

- an integer k;
- a nonzero ideal modulus m;
- a finite multiplicative residue character nu on O/m, with its prescribed zero extension;
- the compatibility equation alpha(u)^k nu(u)=1 for every global unit u.

Its coefficient on a principal ideal (a) is nu(a) alpha(a)^k for nonzero a, with the actual modulus-prime zeros retained. This equation makes the coefficient independent of the generator. The zero ideal has coefficient zero. The finite residue character and integer k are subject to compatibility; they are not independent arbitrary parameters.

See [AngularCharacter.lean](lean/AngularCharacter.lean) and [AngularSeries.lean](lean/AngularSeries.lean). The continued function is defined in [AngularFamilyContinuation.lean](lean/AngularFamilyContinuation.lean) from primitive theta continuation and exact finite Euler factors. For Re(s)>1 it agrees with the absolutely convergent ideal series sum_I chi(I)/N(I)^s. The exact identification is checked in [AngularPhysicalPublicStatementCheck.lean](lean/AngularPhysicalPublicStatementCheck.lean).

## Untwisted statement

For every such chi and every complex s with Re(s)>7/8, L(s,chi) is nonzero, with s=1 excluded when k=0 and the finite residue character is principal. Both angular signs, k=0, all nonzero finite ideal moduli, and primitive and imprimitive presentations are included. The boundary line Re(s)=7/8 is not claimed.

Namespace: `OAI.SevenEighths.Angular.PhysicalFinalAssembly`.

```lean
theorem LFunction_ne_zero_of_seven_eighths_lt_re
    (χ : AngularCharacter) (s : ℂ) (hs : (7/8:ℝ)<s.re)
    (hpole : χ.k=0 → χ.residue=1 → s≠1) :
    FamilyContinuation.LFunction χ s≠0
```

Exact source: [AngularPhysicalFinalAssembly.lean](lean/AngularPhysicalFinalAssembly.lean).

## Unitary norm twists

For every real tau, the released convention has coefficient chi(I) N(I)^(+i tau) and continuation L_chi(s-i tau). Its principal pole is 1+i tau. The research brief's convention has coefficient chi(I) N(I)^(-i tau), continuation L_chi(s+i tau), and principal pole 1-i tau. Both statements have the same strict boundary Re(s)>7/8, with a pole exclusion only for k=0 and principal residue character.

Exact sources: [AngularNormTwist.lean](lean/AngularNormTwist.lean), [AngularNormTwistContinuation.lean](lean/AngularNormTwistContinuation.lean), and [AngularPhysicalNormTwistNonvanishing.lean](lean/AngularPhysicalNormTwistNonvanishing.lean).

The public declarations are `norm_twist_nonzero` and `brief_norm_twist_nonzero` in the namespace above. The latter file includes the coefficient sign, series identification, shifted-function identity, and a separately written expected statement.

## Quantifiers and exclusions

Uniform estimates fix a finite angular cap before choosing constants and smooth-profile bounds. The family statement follows by finite-cap induction; no uniform estimates over unbounded angular orders are asserted. Conductors may vary within a fixed cap. Magnitude constants or eventual thresholds may follow the target where the corresponding theorem explicitly permits this; the positive improvement margin used in the supremum argument must be chosen before the target.

The review target is this Eisenstein family and these unitary twists. It does not assert a Gaussian-family theorem, a bound below 7/8, a result on the boundary, or the Riemann hypothesis. Relative to 15/16, the stated boundary is smaller by 1/16; the reviewer should separately assess whether the formal scope supports that comparison.
