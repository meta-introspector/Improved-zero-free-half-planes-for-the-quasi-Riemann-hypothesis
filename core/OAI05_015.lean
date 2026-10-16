lemma outerQuotient_mk (s H : O) :
    outerQuotient s (Ideal.Quotient.mk _ H)=idealRowHom H (Ideal.span {s}) := by
  unfold outerQuotient
  apply idealRowHom_congr_mod
  exact Ideal.Quotient.eq.mp (representative_spec _ _)

theorem bareCongruenceCoefficient_all_prime_powers (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p}) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) =
      sourceScalar p hp hg t k j := by
  cases t with
  | zero =>
    simp only [pow_zero]
    rw [bareCongruenceCoefficient_inner_one _ (pow_ne_zero _ hp.ne_zero), outerQuotient_mk]
    unfold sourceScalar
    rw [ite_eq_left rfl]
    by_cases hk : k=0
    · subst k
      simp only [pow_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, ite_true]
    · rw [ite_eq_right hk, ← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg,
        MulChar.pow_apply' _ hk]
  | succ n =>
    rw [bareCongruenceCoefficient_prime_power p hp hg n k j]
    simp only [sourceScalar, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel]

def physicalPrincipalSeries (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (eta a x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
      (actualSextic (Ideal.span {p}) hg (-1)) x w z
      (bareCongruenceCoefficient (p^(e.val+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)))
      e.val l k m

theorem physicalPrincipalSeries_eq (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (eta a x w z : ℂ) :
    physicalPrincipalSeries p hp hg eta a x w z = sourcePrincipalSeries p hp hg eta a x w z := by
  simp only [physicalPrincipalSeries, sourcePrincipalSeries, sourcePrincipalTerm,
    bareCongruenceCoefficient_all_prime_powers p hp hg]

theorem physicalPrincipalSeries_euler_identity (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    physicalPrincipalSeries p hp hg eta a x w z =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  rw [physicalPrincipalSeries_eq]
  exact sourcePrincipalSeries_euler_identity p hp hg hc eta a x w z hV hR hW hD

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1357

/-! Original module: OAI.NumberTheory.DirichletL.Detector.ReciprocityCRT
Source SHA256: 1c4a531823120481ddc6a92d8310fab6b9942461f31e48831480278ebb2e8d56
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1358



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase
local notation "O" => ActualEisensteinCubic.O

def reciprocityCoefficient (A s : O) (hA : A≠0) (H : O) : ℂ :=
  reciprocitySign A s * bareCongruenceCoefficient A s hA H

theorem reciprocityCoefficient_product (A B s r : O)
    (hA : Supported (Ideal.span {A})) (hB : Supported (Ideal.span {B}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpA : goodLambda^2∣A-1) (hpB : goodLambda^2∣B-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    reciprocityCoefficient (A*B) (s*r)
      (mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero B hB)) H =
      (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        reciprocityCoefficient A s (supportedElement_ne_zero A hA) H *
        reciprocityCoefficient B r (supportedElement_ne_zero B hB) H := by
  have hsB := idealRowHom_ne_zero_of_coprime s B hs hcop.of_mul_left_right.of_mul_right_left
  have hrA := idealRowHom_ne_zero_of_coprime r A hr hcop.of_mul_left_left.of_mul_right_right.symm
  have hAr : idealRowHom r (Ideal.span {A}) = reciprocitySign A r * idealRowHom A (Ideal.span {r}) :=
    idealRowHom_primary_reciprocity A r hpA hpr hA hr
  have hBs : idealRowHom s (Ideal.span {B}) = reciprocitySign B s * idealRowHom B (Ideal.span {s}) :=
    idealRowHom_primary_reciprocity B s hpB hps hB hs
  have hratio :
      (idealRowHom B (Ideal.span {A}) * idealRowHom r (Ideal.span {A}) *
       idealRowHom A (Ideal.span {B}) * idealRowHom s (Ideal.span {B})) /
      (idealRowHom B (Ideal.span {s}) * idealRowHom A (Ideal.span {r})) =
      (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        reciprocitySign A r * reciprocitySign B s := by
    rw [hAr, hBs]
    field_simp
  have hsign : reciprocitySign (A*B) (s*r) * reciprocitySign A r * reciprocitySign B s =
      reciprocitySign A s * reciprocitySign B r := by
    calc
      _ = reciprocitySign A s * reciprocitySign B r *
          reciprocitySign A r ^ 2 * reciprocitySign B s ^ 2 := by
        simp only [reciprocitySign_mul_left, reciprocitySign_mul_right]
        ring
      _ = _ := by
        rw [reciprocitySign_sq A r (supported_residue_odd A hA) (supported_residue_odd r hr),
          reciprocitySign_sq B s (supported_residue_odd B hB) (supported_residue_odd s hs),
          mul_one, mul_one]
  unfold reciprocityCoefficient
  rw [bareCongruenceCoefficient_product_reduced A B s r (supportedElement_ne_zero A hA)
    (supportedElement_ne_zero B hB) hs hr hcop H, hratio]
  calc
    _ = (reciprocitySign (A*B) (s*r) * reciprocitySign A r * reciprocitySign B s) *
        (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H *
        bareCongruenceCoefficient B r (supportedElement_ne_zero B hB) H := by ring
    _ = _ := by rw [hsign]; ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1358

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CompletedCoefficient
Source SHA256: 73c24a04fa469f891a63a491a6d8afaa52249cf0b4ab2cf3eb0c4b99a9585648
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1359




namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase
local notation "O" => ActualEisensteinCubic.O

lemma supported_completed (c n : O) (hc : Supported (Ideal.span {c}))
    (hn : Supported (Ideal.span {n})) : Supported (Ideal.span {c*n^3}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow]
  apply (supported_mul_iff _ _).mpr
  refine ⟨hc,?_⟩
  have hn2 := (supported_mul_iff _ _).mpr ⟨hn,hn⟩
  have hn3 := (supported_mul_iff _ _).mpr ⟨hn2,hn⟩
  simpa only [pow_succ, pow_zero, one_mul] using hn3

lemma primary_completed (c n : O) (hc : goodLambda^2∣c-1)
    (hn : goodLambda^2∣n-1) : goodLambda^2∣c*n^3-1 := by
  have h := dvd_add (dvd_mul_of_dvd_left hc (n^3))
    (dvd_mul_of_dvd_left hn (n^2+n+1))
  convert h using 1 ; ring

def correctedFiniteCoefficient (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : A≠0) (H : O) : ℂ :=
  gaussTwo I hI * star (G A) * reciprocityCoefficient A s hA H

theorem correctedFiniteCoefficient_product (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (H : O) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    correctedFiniteCoefficient (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) H =
      correctedFiniteCoefficient I hI.2 A s hA H * correctedFiniteCoefficient J hJ.2 B r hB H := by
  dsimp only
  let c := primaryGenerator I
  let d := primaryGenerator J
  let A := c*n^3
  let B := d*m^3
  have hAs := supported_completed c n hc hn
  have hBs := supported_completed d m hd hm
  have hAB : IsCoprime A B := hcop.of_mul_left_left.of_mul_right_left
  have hnA : n∣A := by refine ⟨c*n^2,?_⟩; dsimp only [A]; ring
  have hmB : m∣B := by refine ⟨d*m^2,?_⟩; dsimp only [B]; ring
  have hcA : c∣A := dvd_mul_right c (n^3)
  have hdB : d∣B := dvd_mul_right d (m^3)
  have hcd : IsCoprime c d := (hAB.of_isCoprime_of_dvd_left hcA).of_isCoprime_of_dvd_right hdB
  have hcm : IsCoprime c m := (hAB.of_isCoprime_of_dvd_left hcA).of_isCoprime_of_dvd_right hmB
  have hnd : IsCoprime n d := (hAB.of_isCoprime_of_dvd_left hnA).of_isCoprime_of_dvd_right hdB
  have hnm : IsCoprime n m := (hAB.of_isCoprime_of_dvd_left hnA).of_isCoprime_of_dvd_right hmB
  have hphase := completed_cubic_cross_cancel c n d m hc hn hd hm hpc hpn hpd hpm hcd hcm hnd hnm
  change sexticPair A B * sexticPair c d^2 * star (reciprocitySign A B)=1 at hphase
  change gaussTwo (I*J) hIJ.2 * star (G (A*B)) *
      reciprocityCoefficient (A*B) (s*r) _ H =
    (gaussTwo I hI.2 * star (G A) * reciprocityCoefficient A s _ H) *
    (gaussTwo J hJ.2 * star (G B) * reciprocityCoefficient B r _ H)
  rw [gaussTwo_coprime_product_sextic I J hI hJ hIJ hIJcop,
    G_mul A B (supported_residue_odd A hAs) (supported_residue_odd B hBs),
    reciprocityCoefficient_product A B s r hAs hBs hs hr
      (primary_completed c n hpc hpn) (primary_completed d m hpd hpm) hps hpr hcop H]
  simp only [star_mul]
  change (sexticPair c d^2 * gaussTwo I hI.2 * gaussTwo J hJ.2) *
    (star (reciprocitySign A B)*(star (G B)*star (G A))) *
    (sexticPair A B * reciprocityCoefficient A s _ H * reciprocityCoefficient B r _ H) = _
  calc
    _ = (sexticPair A B * sexticPair c d^2 * star (reciprocitySign A B)) *
      ((gaussTwo I hI.2 * star (G A) * reciprocityCoefficient A s _ H) *
       (gaussTwo J hJ.2 * star (G B) * reciprocityCoefficient B r _ H)) := by ring
    _ = _ := by rw [hphase,one_mul]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1359

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SourceCoefficient
Source SHA256: 374110c8227301a3be4ce6269f22ededcb0484583fc28a76c39e6b898fef70a4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1360



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbePhase ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def sourceHighCoefficient (C : CalibrationData) (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (u a : O) : ℂ :=
  actualCongruenceCoefficient C A s hA (u*a^6) * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid u)) *
    gaussTwo I hI * star (FiniteGaussPhase.angularFactor A * G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

def bareSourceCoefficient (η : HeckeFamily.Character) (I : Ideal O)
    (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  targetMonoid η A * star (FiniteGaussPhase.angularFactor A) *
    correctedFiniteCoefficient I hI A s hA H

theorem sourceHighCoefficient_eq_bare (S : Finset (Ideal O)) (hS : ∀ P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (u a : O)
    (hH : IsCoprime (calibrationForSet S hS).generator (u*a^6)) :
    sourceHighCoefficient (calibrationForSet S hS) η I hI A s (supportedElement_ne_zero A hA) u a =
      bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (u*a^6) := by
  let C := calibrationForSet S hS
  have ha : IsCoprime C.generator a :=
    hH.of_isCoprime_of_dvd_right (by refine ⟨u*a^5,?_⟩; ring)
  have hval : C.residueMonoid (u*a^6)=C.residueMonoid u := by
    rw [map_mul,map_pow,calibrationForSet_residue_sixth S hS a ha,mul_one]
  have he := calibration_coefficient_cancel S hS A s hA hs hcop (u*a^6) hH
  dsimp only at he
  dsimp only [C] at hval
  rw [hval] at he
  unfold sourceHighCoefficient bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  simp only [star_mul]
  calc
    _ = (actualCongruenceCoefficient (calibrationForSet S hS) A s (supportedElement_ne_zero A hA) (u*a^6) *
      idealRowHom (calibrationForSet S hS).generator (Ideal.span {s}) /
      ((Real.sqrt (elementNorm (calibrationForSet S hS).generator):ℂ)*(calibrationForSet S hS).tau*
       (calibrationForSet S hS).residueMonoid s*star ((calibrationForSet S hS).residueMonoid u)) *
      ((calibrationForSet S hS).Xi A)⁻¹) *
      (gaussTwo I hI * star (G A) * star (FiniteGaussPhase.angularFactor A) *
        targetMonoid η A * reciprocitySign A s) := by ring
    _ = _ := by rw [he]; ring

theorem bareSourceCoefficient_product (η : HeckeFamily.Character) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (H : O) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) H =
      bareSourceCoefficient η I hI.2 A s hA H * bareSourceCoefficient η J hJ.2 B r hB H := by
  have he := correctedFiniteCoefficient_product I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop H
  dsimp only at he ⊢
  unfold bareSourceCoefficient
  rw [he,map_mul,angularFactor_mul,star_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1360

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CoefficientDirect
Source SHA256: 1a7fb5daa29cb08f55ba17e630678ebf1b23a9162e5b10d833ecab6301932152
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1361



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow ProbePhase
local notation "O" => ActualEisensteinCubic.O

def calibratedHighCoefficient (C : CalibrationData) (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  actualCongruenceCoefficient C A s hA H * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s) *
    gaussTwo I hI * star (FiniteGaussPhase.angularFactor A * ProbePhase.G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

lemma div_mul_frequency_cancel (a b c m : ℂ) (hc : c≠0) :
    c*(a/(b*c)*m)=a/b*m := by
  simp only [div_eq_mul_inv,mul_inv_rev]
  calc
    _ = (c*c⁻¹)*(a*b⁻¹*m) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hc,one_mul]

theorem calibratedHighCoefficient_eq_bare (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (I : Ideal O) (hI : primaryGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : O) :
    calibratedHighCoefficient (calibrationForSet S hS) η I hI A s (supportedElement_ne_zero A hA) H=
      star ((calibrationForSet S hS).residueMonoid H)*
        bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  let C := calibrationForSet S hS
  by_cases hH : IsCoprime C.generator H
  · have hn : star (C.residueMonoid H)≠0 := by
      apply star_ne_zero.mpr
      exact C.residue.apply_ne_zero_iff.mpr ((CubicEisenstein.isUnit_quotient_span_iff C.generator H).mpr hH)
    have he := sourceHighCoefficient_eq_bare S hS η I hI A s hA hs hcop H 1 (by simpa using hH)
    simp only [one_pow,mul_one] at he
    rw [←he]
    unfold sourceHighCoefficient calibratedHighCoefficient
    simp only [one_pow,mul_one]
    symm
    convert div_mul_frequency_cancel
      (actualCongruenceCoefficient C A s (supportedElement_ne_zero A hA) H * idealRowHom C.generator (Ideal.span {s}))
      ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s)
      (star (C.residueMonoid H))
      (gaussTwo I hI*star (FiniteGaussPhase.angularFactor A*ProbePhase.G A)*targetMonoid η A*(C.Xi A)⁻¹*reciprocitySign A s)
      hn using 1 <;> dsimp only [C] <;> ring
  · have hz := actualCongruenceCoefficient_zero_off_calibration S hS A s
      (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) hcop H hH
    have hξ : C.residueMonoid H=0 := by
      change C.residue (Ideal.Quotient.mk _ H)=0
      apply MulChar.map_nonunit
      exact fun h=>hH ((CubicEisenstein.isUnit_quotient_span_iff _ _).mp h)
    dsimp only [C] at hξ
    simp only [calibratedHighCoefficient,hz,zero_mul,zero_div,hξ,star_zero]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1361

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SixthFrequency
Source SHA256: aeeff56575517a387397660c9131a32b786dfe64a5d09d5994a3e1cb6133477c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1362


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
open CompletedGauss ConcreteTraceCRT GaussianShiftedPartition CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma finite_fourier_invariant_unit {R : Type*} [CommRing R] [Fintype R]
    (F : R→ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (hF : ∀ x,F ((u:R)*x)=F x) (H : R) :
    (∑ x,F x*ψ (((u:R)*H)*x)) = ∑ x,F x*ψ (H*x) := by
  symm
  rw [← Equiv.sum_comp u.mulLeft (fun x=>F x*ψ (H*x))]
  simp only [Units.mulLeft_apply,hF]
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  congr 1
  ring

lemma supported_sixth_value (A v : O) (hA : Supported (Ideal.span {A}))
    (hcop : IsCoprime A v) : idealRowHom (v^6) (Ideal.span {A})=1 := by
  rw [idealRowHom_sixth_mask _ _ hA, ite_eq_left ((Ideal.isCoprime_span_singleton_iff A v).mpr hcop)]

theorem barePhysicalFourier_sixth_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    barePhysicalFourier A s (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) (v^6*H) =
      barePhysicalFourier A s (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs) H := by
  have hAs := mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs)
  let := finite_quotient_span hAs
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let u := residueUnit (A*s) (v^6) hcop.pow_left.symm
  have hF (x : Residue (A*s)) :
      movingQuotient A s (supportedElement_ne_zero s hs) ((u:Residue (A*s))*x) =
        movingQuotient A s (supportedElement_ne_zero s hs) x := by
    rw [show (u:Residue (A*s))=Ideal.Quotient.mk _ (v^6) by rfl,
      movingQuotient_unit_scale A s hs (v^6) hcop.of_mul_right_right.pow_left,
      supported_sixth_value A v hA hcop.of_mul_right_left.symm,
      supported_sixth_value s v hs hcop.of_mul_right_right.symm,inv_one,one_mul,one_mul]
  have he := finite_fourier_invariant_unit (movingQuotient A s (supportedElement_ne_zero s hs))
    (quotientTrace (A*s) hAs) u hF (Ideal.Quotient.mk _ H)
  unfold barePhysicalFourier elementFourier
  simp only [tsum_fintype]
  change (∑ x,movingQuotient A s (supportedElement_ne_zero s hs) x *
    quotientTrace (A*s) hAs (Ideal.Quotient.mk _ (v^6*H)*x)) =
    ∑ x,movingQuotient A s (supportedElement_ne_zero s hs) x *
      quotientTrace (A*s) hAs (Ideal.Quotient.mk _ H*x)
  simpa only [u,residueUnit_coe,map_mul] using he

theorem bareCongruenceCoefficient_sixth_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (v^6*H) =
      bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  have he := barePhysicalFourier_sixth_frequency A s hA hs v H hcop
  simp only [barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  exact mul_left_cancel₀ hn he

theorem bareSourceCoefficient_sixth_frequency (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (v H : O) (hcop : IsCoprime v (A*s)) :
    bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (v^6*H) =
      bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [bareCongruenceCoefficient_sixth_frequency A s hA hs v H hcop]

theorem bareSourceCoefficient_product_frequency (η : HeckeFamily.Character) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (a b : O)
    (hba : IsCoprime b ((primaryGenerator I*n^3)*s))
    (hab : IsCoprime a ((primaryGenerator J*m^3)*r)) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) ((a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (a^6) * bareSourceCoefficient η J hJ.2 B r hB (b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop ((a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (b^6) hab
  rw [show b^6*a^6=(a*b)^6 by ring] at hi
  rw [show a^6*b^6=(a*b)^6 by ring] at hj
  rw [hi,hj] at he
  exact he

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1362

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LocalUnitFrequency
Source SHA256: e9ff5a6c85d1f956dd9f53409637e72f229be1d6fc3c7b97f2cb2ff931b4a387
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1363



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
open CompletedGauss ConcreteTraceCRT GaussianShiftedPartition CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation ConcretePrimeRowBridge ProbePrimePower ProbeLocal ProbeEuler
local notation "O" => ActualEisensteinCubic.O

lemma finite_fourier_unit_scale {R : Type*} [CommRing R] [Fintype R]
    (F : R → ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (c : ℂ) (hc : c ≠ 0)
    (hF : ∀ x, F ((u : R) * x) = c * F x) (H : R) :
    (∑ x, F x * ψ (((u : R) * H) * x)) = c⁻¹ * ∑ x, F x * ψ (H*x) := by
  have he : (∑ x, F x * ψ (H*x)) = c * ∑ x, F x * ψ (((u : R)*H)*x) := by
    rw [← Equiv.sum_comp u.mulLeft (fun x => F x * ψ (H*x))]
    simp only [Units.mulLeft_apply, hF, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show H*((u : R)*x) = ((u : R)*H)*x by ring]
    ring
  rw [he, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem barePhysicalFourier_unit_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    barePhysicalFourier A s (supportedElement_ne_zero A hA)
        (supportedElement_ne_zero s hs) (b*H) =
      ((idealRowHom b (Ideal.span {A}))⁻¹ * idealRowHom b (Ideal.span {s})) *
        barePhysicalFourier A s (supportedElement_ne_zero A hA)
          (supportedElement_ne_zero s hs) H := by
  have hAs := mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs)
  let := finite_quotient_span hAs
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let u := residueUnit (A*s) b hcop.symm
  have hcA := idealRowHom_ne_zero_of_coprime A b hA hcop.of_mul_right_left.symm
  have hcs := idealRowHom_ne_zero_of_coprime s b hs hcop.of_mul_right_right.symm
  have hF (x : Residue (A*s)) :
      movingQuotient A s (supportedElement_ne_zero s hs) ((u : Residue (A*s))*x) =
        (idealRowHom b (Ideal.span {A}) * (idealRowHom b (Ideal.span {s}))⁻¹) *
          movingQuotient A s (supportedElement_ne_zero s hs) x := by
    exact movingQuotient_unit_scale A s hs b hcop.of_mul_right_right x
  have he := finite_fourier_unit_scale (movingQuotient A s (supportedElement_ne_zero s hs))
    (quotientTrace (A*s) hAs) u _ (mul_ne_zero hcA (inv_ne_zero hcs)) hF
    (Ideal.Quotient.mk _ H)
  unfold barePhysicalFourier elementFourier
  simp only [tsum_fintype]
  change (∑ x, movingQuotient A s (supportedElement_ne_zero s hs) x *
    quotientTrace (A*s) hAs (Ideal.Quotient.mk _ (b*H)*x)) =
      _ * ∑ x, movingQuotient A s (supportedElement_ne_zero s hs) x *
        quotientTrace (A*s) hAs (Ideal.Quotient.mk _ H*x)
  simpa only [u, residueUnit_coe, map_mul, mul_inv_rev, inv_inv, mul_comm] using he

theorem bareCongruenceCoefficient_unit_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H) =
      ((idealRowHom b (Ideal.span {A}))⁻¹ * idealRowHom b (Ideal.span {s})) *
        bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  have he := barePhysicalFourier_unit_frequency A s hA hs b H hcop
  simp only [barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  apply mul_left_cancel₀ hn
  rw [he]
  ring

lemma idealRowHom_norm_one_of_coprime (s b : O)
    (hs : Supported (Ideal.span {s})) (hcop : IsCoprime b s) :
    ‖idealRowHom b (Ideal.span {s})‖ = 1 := by
  have h6 := idealRowHom_sixth_mask b (Ideal.span {s}) hs
  rw [idealRowHom_argument_pow _ _ _ hs,
    ite_eq_left ((Ideal.isCoprime_span_singleton_iff s b).mpr hcop.symm)] at h6
  exact Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0)

theorem bareCongruenceCoefficient_unit_frequency_norm (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H)‖ =
      ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ := by
  rw [bareCongruenceCoefficient_unit_frequency A s hA hs b H hcop,
    norm_mul, norm_mul, norm_inv,
    idealRowHom_norm_one_of_coprime A b hA hcop.of_mul_right_left,
    idealRowHom_norm_one_of_coprime s b hs hcop.of_mul_right_right,
    inv_one, one_mul, one_mul]

theorem bareCongruenceCoefficient_unit_frequency_eq_zero_iff (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H) = 0 ↔
      bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H = 0 := by
  rw [← norm_eq_zero, bareCongruenceCoefficient_unit_frequency_norm A s hA hs b H hcop,
    norm_eq_zero]

lemma supported_element_power (p : O) (hs : Supported (Ideal.span {p})) (n : ℕ) :
    Supported (Ideal.span {p^n}) := by
  rw [← Ideal.span_singleton_pow]
  exact supported_pow hs n

lemma idealRowHom_prime_power_value (p b : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (n : ℕ) :
    idealRowHom b (Ideal.span {p^n}) =
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^n := by
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg]

lemma actualSextic_unit_power_ne_zero (p b : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hcop : IsCoprime b p) (t : ℕ) :
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t ≠ 0 := by
  apply pow_ne_zero
  exact (actualSextic (Ideal.span {p}) hg).apply_ne_zero_iff.mpr
    ((isUnit_quotient_span_iff p b).mpr hcop.symm)

theorem bareCongruenceCoefficient_prime_power_unit_frequency (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
          bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) := by
  have he := bareCongruenceCoefficient_unit_frequency (p^t) (p^k)
    (supported_element_power p hs t) (supported_element_power p hs k) b (p^j)
    (hcop.pow_right.mul_right hcop.pow_right)
  simpa only [idealRowHom_prime_power_value p b hg, div_eq_mul_inv, mul_comm] using he

theorem bareCongruenceCoefficient_all_prime_powers_unit (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
          sourceScalar p hp hg t k j := by
  rw [bareCongruenceCoefficient_prime_power_unit_frequency p hp hs hg b hcop t k j,
    bareCongruenceCoefficient_all_prime_powers p hp hg t k j]

theorem barePhysicalFourier_all_prime_powers_unit (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    barePhysicalFourier (p^t) (p^k) (pow_ne_zero _ hp.ne_zero)
        (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      (Ideal.absNorm (Ideal.span {p^k}) : ℂ) *
        (((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
          (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
            sourceScalar p hp hg t k j) := by
  rw [barePhysicalFourier_eq,
    bareCongruenceCoefficient_all_prime_powers_unit p hp hs hg b hcop t k j]

theorem bareCongruenceCoefficient_all_prime_powers_unit_norm (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    ‖bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j)‖ =
      ‖sourceScalar p hp hg t k j‖ := by
  have he := bareCongruenceCoefficient_unit_frequency_norm (p^t) (p^k)
    (supported_element_power p hs t) (supported_element_power p hs k) b (p^j)
    (hcop.pow_right.mul_right hcop.pow_right)
  rw [bareCongruenceCoefficient_all_prime_powers p hp hg t k j] at he
  exact he

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1363

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SourceBounds
Source SHA256: 86184dc0cca58d1494ee7cdb68149db84b16182995d0007d29b9ca6b7759428c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1364



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbePhase ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareCongruenceCoefficient_norm_le (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    ‖bareCongruenceCoefficient A s hA H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  apply congruenceCoefficient_norm_le A s hA hs
  · intro m
    exact idealRowHom_norm _ _
  · intro m
    exact idealRowHom_norm _ _

theorem bareSourceCoefficient_norm_le (η : HeckeFamily.Character)
    (I : Ideal O) (hI : CubicSieve.Admissible I) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s})) (H : O) :
    ‖bareSourceCoefficient η I hI.2 A s (supportedElement_ne_zero A hA) H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  have hR : ‖reciprocitySign A s‖≤1 := sexticReciprocityPhase_norm A s
  have ht := targetMonoid_norm_le_one η A
  have hfac : ‖targetMonoid η A‖*‖reciprocitySign A s‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) ht).trans hR
  calc
    _ = (‖targetMonoid η A‖*‖reciprocitySign A s‖)*
        ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ := by
      simp only [bareSourceCoefficient, correctedFiniteCoefficient, reciprocityCoefficient,
        norm_mul,norm_star,CubicSieve.gaussTwo_norm_one I hI,
        FiniteGaussPhase.norm_angularFactor A (supportedElement_ne_zero A hA),
        G_norm_one_of_odd A (supported_residue_odd A hA),one_mul,mul_one]
      ring
    _ ≤ ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hfac
    _ ≤ _ := bareCongruenceCoefficient_norm_le A s (supportedElement_ne_zero A hA)
      (supportedElement_ne_zero s hs) H

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1364

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighSeries
Source SHA256: eac7cc6bd848ea9b64e6f3b3022ca408f3dee5bf213f7df3ef12fc3f07fe022c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1365


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def bareIdealHighCoefficient (η : HeckeFamily.Character) (u : O) (I J K L : Id) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L then
    bareSourceCoefficient η I (supported_primaryGenerator_ne_zero I h.2.1)
      (primaryGenerator I * primaryGenerator J^3) (primaryGenerator K)
      (mul_ne_zero (supported_primaryGenerator_ne_zero I h.2.1)
        (pow_ne_zero _ (supported_primaryGenerator_ne_zero J h.2.2.1)))
      (u*primaryGenerator L^6)
  else 0

theorem bareIdealHighCoefficient_norm_le (η : HeckeFamily.Character) (u : O) (I J K L : Id) :
    ‖bareIdealHighCoefficient η u I J K L‖ ≤ (K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3 := by
  unfold bareIdealHighCoefficient
  split_ifs with h
  · have hi := (supported_span_primaryGenerator_iff I).mpr h.2.1
    have hj := (supported_span_primaryGenerator_iff J).mpr h.2.2.1
    have hk := (supported_span_primaryGenerator_iff K).mpr h.2.2.2.1
    have hb := bareSourceCoefficient_norm_le η I ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      (primaryGenerator I*primaryGenerator J^3) (primaryGenerator K)
      (supported_completed _ _ hi hj) hk (u*primaryGenerator L^6)
    rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).1,
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).1,
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).1,
      map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] at hb
    convert hb using 1 ; ring
  · simp only [norm_zero]
    positivity

def bareIdealHighSummand (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  bareIdealHighCoefficient η u I J K L * fullIdealWeight (x+1/2) I *
    fullIdealWeight (1+3*x) J * fullIdealWeight w K * fullIdealWeight (6*z) L

lemma fullIdealWeight_nat_scale (s : ℂ) (I : Id) (hI : I≠0) (k : ℕ) :
    (I.absNorm:ℝ)^k * ‖fullIdealWeight s I‖ = ‖fullIdealWeight (s-k) I‖ := by
  have hN : 0<(I.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [fullIdealWeight,ite_eq_right hI]
  simp only [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [Complex.neg_re,Complex.sub_re,Complex.ofReal_re]
  rw [← Real.rpow_natCast,← Real.rpow_add hN]
  congr 1
  ring

theorem bareIdealHighSummand_norm_le (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖bareIdealHighSummand η u x w z I J K L‖ ≤
      ‖fullIdealWeight (x-1/2) I‖ * ‖fullIdealWeight (3*x-2) J‖ *
      ‖fullIdealWeight (w-1) K‖ * ‖fullIdealWeight (6*z) L‖ := by
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L
  · have hb := bareIdealHighCoefficient_norm_le η u I J K L
    calc
      _ ≤ ((K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3) *
          ‖fullIdealWeight (x+1/2) I‖ * ‖fullIdealWeight (1+3*x) J‖ *
          ‖fullIdealWeight w K‖ * ‖fullIdealWeight (6*z) L‖ := by
        simp only [bareIdealHighSummand,norm_mul]
        gcongr
      _ = ((I.absNorm:ℝ)^1*‖fullIdealWeight (x+1/2) I‖) *
          ((J.absNorm:ℝ)^3*‖fullIdealWeight (1+3*x) J‖) *
          ((K.absNorm:ℝ)^1*‖fullIdealWeight w K‖) * ‖fullIdealWeight (6*z) L‖ := by ring
      _ = _ := by
        rw [fullIdealWeight_nat_scale _ I h.2.1.1 1,
          fullIdealWeight_nat_scale _ J h.2.2.1.1 3,
          fullIdealWeight_nat_scale _ K h.2.2.2.1.1 1]
        norm_num only [Nat.cast_one, Nat.cast_ofNat]
        rw [show x+(1/2:ℂ)-1=x-1/2 by ring,show (1:ℂ)+3*x-3=3*x-2 by ring]
  · simp only [bareIdealHighSummand,bareIdealHighCoefficient,dite_eq_right h,zero_mul,norm_zero]
    positivity

theorem bareIdealHighSummand_summable (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      bareIdealHighSummand η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  have h1 := fullIdealWeight_summable_norm (x-1/2) (by
    simp only [Complex.sub_re,Complex.div_re,Complex.one_re,Complex.one_im,
      show (2:ℂ).re=2 by rfl,show (2:ℂ).im=0 by rfl]
    norm_num
    linarith)
  have h2 := fullIdealWeight_summable_norm (3*x-2) (by
    norm_num [Complex.sub_re,Complex.mul_re]
    linarith)
  have h3 := fullIdealWeight_summable_norm (w-1) (by
    simp only [Complex.sub_re,Complex.one_re]
    linarith)
  have h4 := fullIdealWeight_summable_norm (6*z) (by
    norm_num [Complex.mul_re]
    linarith)
  have h12 := h1.mul_of_nonneg h2 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have h34 := h3.mul_of_nonneg h4 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have hall := h12.mul_of_nonneg h34
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hall
  intro p
  simpa only [mul_assoc] using bareIdealHighSummand_norm_le η u x w z p.1.1 p.1.2 p.2.1 p.2.2

def bareIdealHighSeries (η : HeckeFamily.Character) (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), bareIdealHighSummand η u x w z p.1.1 p.1.2 p.2.1 p.2.2

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1365

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighDeletion
Source SHA256: 220edd1faefc835cef352ad47ffadc47f48c96e7bcac54ad662e97ca7396db1c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1366


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highIdealMask (S : Finset Id) (D I J K L : Id) : ℂ :=
  completedMask S D I J *
    (if ∀ P∈S,¬P∣K then 1 else 0) * (if ∀ P∈S,¬P∣L then 1 else 0)

lemma highIdealMask_norm_le_one (S : Finset Id) (D I J K L : Id) :
    ‖highIdealMask S D I J K L‖≤1 := by
  unfold highIdealMask
  split_ifs <;> simp only [mul_one,mul_zero,norm_zero]
  · exact completedMask_norm_le_one S D I J
  all_goals norm_num

def markedIdealHighSummand (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  highIdealMask S D I J K L * bareIdealHighSummand η u x w z I J K L

lemma markedIdealHighSummand_norm_le (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖markedIdealHighSummand S D η u x w z I J K L‖≤‖bareIdealHighSummand η u x w z I J K L‖ := by
  rw [markedIdealHighSummand,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (highIdealMask_norm_le_one S D I J K L)

theorem markedIdealHighSummand_summable (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (fun p=>markedIdealHighSummand_norm_le S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2)
    (bareIdealHighSummand_summable η u x w z hx hw hz).norm

def markedIdealHighSeries (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1366

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighAbsolute
Source SHA256: 51b80c27d59a001fef43bce1f68de88fee6b7ee0ee46a55422691f3948da9943
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1367


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
abbrev NonzeroFrequency := {u : O // u≠0}

def frequencyWeight (z : ℂ) (u : NonzeroFrequency) : ℂ := (elementNorm u.val:ℂ)^(-z)

lemma frequencyWeight_norm (z : ℂ) (u : NonzeroFrequency) :
    ‖frequencyWeight z u‖=‖eisEmbedding u.val‖^(-2*z.re) := by
  have hn : 0<‖eisEmbedding u.val‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero u.property)
  unfold frequencyWeight elementNorm
  have hN : (Ideal.absNorm (Ideal.span {u.val}):ℝ)=‖eisEmbedding u.val‖^2 :=
    (eisEmbedding_norm_sq_eq_absNorm_span u.val).symm
  rw [hN,
    Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn), Complex.neg_re,
    ← Real.rpow_natCast_mul hn.le 2]
  congr 1
  ring

theorem frequencyWeight_summable_norm (z : ℂ) (hz : 1<z.re) :
    Summable (fun u : NonzeroFrequency => ‖frequencyWeight z u‖) := by
  simp only [frequencyWeight_norm]
  exact (summable_embedding_rpow (-2*z.re) (by linarith)).subtype _

def highAbsoluteMajorant (x w z : ℂ) (p : (Id×Id)×(Id×Id)) : ℝ :=
  ‖fullIdealWeight (x-1/2) p.1.1‖ * ‖fullIdealWeight (3*x-2) p.1.2‖ *
  ‖fullIdealWeight (w-1) p.2.1‖ * ‖fullIdealWeight (6*z) p.2.2‖

lemma highAbsoluteMajorant_nonneg (x w z : ℂ) (p : (Id×Id)×(Id×Id)) :
    0≤highAbsoluteMajorant x w z p := by unfold highAbsoluteMajorant; positivity

lemma highAbsoluteMajorant_summable (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) : Summable (highAbsoluteMajorant x w z) := by
  have h1 := fullIdealWeight_summable_norm (x-1/2) (by norm_num [Complex.sub_re,Complex.div_re]; linarith)
  have h2 := fullIdealWeight_summable_norm (3*x-2) (by norm_num [Complex.sub_re,Complex.mul_re]; linarith)
  have h3 := fullIdealWeight_summable_norm (w-1) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have h4 := fullIdealWeight_summable_norm (6*z) (by norm_num [Complex.mul_re]; linarith)
  have h12 := h1.mul_of_nonneg h2 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have h34 := h3.mul_of_nonneg h4 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
  have hall := h12.mul_of_nonneg h34
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _=>mul_nonneg (norm_nonneg _) (norm_nonneg _))
  unfold highAbsoluteMajorant
  simpa only [mul_assoc] using hall

theorem fullHighSummand_summable (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re)
    (mask : NonzeroFrequency→ℂ) (hmask : ∀u,‖mask u‖≤1) :
    Summable (fun p : NonzeroFrequency×((Id×Id)×(Id×Id)) =>
      mask p.1 * frequencyWeight z p.1 *
        markedIdealHighSummand S D η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) := by
  have hm := (frequencyWeight_summable_norm z hz).mul_of_nonneg
    (highAbsoluteMajorant_summable x w z hx hw (by linarith))
    (fun _=>norm_nonneg _) (highAbsoluteMajorant_nonneg x w z)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hm
  intro p
  rw [norm_mul,norm_mul]
  have hcoeff := (markedIdealHighSummand_norm_le S D η p.1.val x w z
    p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2).trans
    (bareIdealHighSummand_norm_le η p.1.val x w z p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2)
  change _≤‖frequencyWeight z p.1‖*highAbsoluteMajorant x w z p.2
  calc
    _ ≤ (1*‖frequencyWeight z p.1‖)*highAbsoluteMajorant x w z p.2 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hmask p.1) (norm_nonneg _)
      · exact hcoeff
      · exact norm_nonneg _
      · positivity
    _ = _ := by rw [one_mul]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1367

/-! Original module: OAI.NumberTheory.DirichletL.Detector.IdealMultiplicative
Source SHA256: 177bb0614d6fb87cc0cafaf0bf49c7521dfb334306636e7c4f292e57b16f908c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1368




namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highSupport (I J K L : Id) : Prop :=
  Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L

lemma highSupport_mul (I J K L I' J' K' L' : Id) (hcop : IsCoprime I I') :
    highSupport (I*I') (J*J') (K*K') (L*L') ↔
      highSupport I J K L ∧ highSupport I' J' K' L' := by
  simp only [highSupport, squarefree_mul_iff, supported_mul_iff]
  have hc := hcop.isRelPrime
  tauto

lemma span_primaryGenerator_of_supported (I : Id) (hI : Supported I) :
    Ideal.span {primaryGenerator I}=I :=
  (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I hI)).1

lemma primaryGenerator_coprime (I J : Id) (hI : Supported I) (hJ : Supported J)
    (hcop : IsCoprime I J) : IsCoprime (primaryGenerator I) (primaryGenerator J) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rwa [span_primaryGenerator_of_supported I hI,span_primaryGenerator_of_supported J hJ]

lemma completed_block_dvd_cube (I J K L : Id) : I*J^3*K ∣ (I*J*K*L)^3 := by
  refine ⟨I^2*K^2*L^3,?_⟩
  ring

lemma first_block_dvd (I J K L : Id) : I ∣ I*J*K*L := by
  refine ⟨J*K*L,?_⟩
  ring

lemma last_block_dvd (I J K L : Id) : L ∣ I*J*K*L := by
  refine ⟨I*J*K,?_⟩
  ring

theorem bareIdealHighCoefficient_mul (η : HeckeFamily.Character)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η 1 (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η 1 I J K L * bareIdealHighCoefficient η 1 I' J' K' L' := by
  have hII := hcop.mono (first_block_dvd I J K L) (first_block_dvd I' J' K' L')
  by_cases h : highSupport I J K L ∧ highSupport I' J' K' L'
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    rcases h with ⟨h,h'⟩
    have hsA := (supported_mul_iff (I*J^3) K).mpr
      ⟨(supported_mul_iff I (J^3)).mpr ⟨h.2.1,supported_pow h.2.2.1 3⟩,h.2.2.2.1⟩
    have hsB := (supported_mul_iff (I'*J'^3) K').mpr
      ⟨(supported_mul_iff I' (J'^3)).mpr ⟨h'.2.1,supported_pow h'.2.2.1 3⟩,h'.2.2.2.1⟩
    have hc3 : IsCoprime ((I*J*K*L)^3) ((I'*J'*K'*L')^3) := hcop.pow_left.pow_right
    have hab := primaryGenerator_coprime _ _ hsA hsB
      (hc3.mono (completed_block_dvd_cube I J K L) (completed_block_dvd_cube I' J' K' L'))
    have hba := primaryGenerator_coprime _ _ h'.2.2.2.2 hsA
      (hcop.symm.pow_right.mono (last_block_dvd I' J' K' L') (completed_block_dvd_cube I J K L))
    have hab' := primaryGenerator_coprime _ _ h.2.2.2.2 hsB
      (hcop.pow_right.mono (last_block_dvd I J K L) (completed_block_dvd_cube I' J' K' L'))
    simp only [primaryGenerator_mul,primaryGenerator_pow] at hab hba hab'
    have he := bareSourceCoefficient_product_frequency η I I'
      ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryGenerator J) (primaryGenerator J') (primaryGenerator K) (primaryGenerator K')
      ((supported_span_primaryGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryGenerator_iff K').mpr h'.2.2.2.1)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).2
      (primaryGenerator_spec I' (supported_primaryGenerator_ne_zero I' h'.2.1)).2
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).2
      (primaryGenerator_spec J' (supported_primaryGenerator_ne_zero J' h'.2.2.1)).2
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).2
      (primaryGenerator_spec K' (supported_primaryGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryGenerator L) (primaryGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dite_eq_left hprod,dite_eq_left h,dite_eq_left h']
    simp only [primaryGenerator_mul,one_mul]
    dsimp only at he
    convert he using 1 ; ring_nf
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    rw [dite_eq_right hprod]
    by_cases hi : highSupport I J K L
    · have hj : ¬highSupport I' J' K' L' := fun hj=>h ⟨hi,hj⟩
      unfold highSupport at hj
      rw [dite_eq_right hj,mul_zero]
    · unfold highSupport at hi
      rw [dite_eq_right hi,zero_mul]

lemma fullIdealWeight_mul (s : ℂ) (I J : Id) :
    fullIdealWeight s (I*J)=fullIdealWeight s I*fullIdealWeight s J :=
  (IdealEuler.normWeight s).map_mul I J

theorem bareIdealHighSummand_mul (η : HeckeFamily.Character) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η 1 x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η 1 x w z I J K L * bareIdealHighSummand η 1 x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_mul η I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1368
