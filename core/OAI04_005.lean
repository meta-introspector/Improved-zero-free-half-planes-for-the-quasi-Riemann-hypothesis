  intro p hp
  exact fun hz => hp (by simp only [correctedSummand, markedSummand, hz, mul_zero])

theorem correctedCompletedT_ray_expansion (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    correctedCompletedT S D Ψ W X =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedCompletedT S D (rayMonoid χ * Ψ) W X := by
  unfold correctedCompletedT
  simp_rw [correctedSummand_ray_expansion]
  rw [Summable.tsum_finsetSum (fun χ _ =>
    (markedSummand_summable S D (rayMonoid χ * Ψ) W hW X hX).mul_left (correctionCoeff χ))]
  simp only [tsum_mul_left, markedCompletedT]

theorem correctedCompletedT_norm_le (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ χ : RayCharacter, ‖markedCompletedT S D (rayMonoid χ * Ψ) W X‖ ≤ B) :
    ‖correctedCompletedT S D Ψ W X‖ ≤ 32 * B := by
  rw [correctedCompletedT_ray_expansion S D Ψ W hW X hX]
  calc
    _ ≤ ∑ χ : RayCharacter, ‖correctionCoeff χ *
        markedCompletedT S D (rayMonoid χ * Ψ) W X‖ := norm_sum_le _ _
    _ ≤ ∑ χ : RayCharacter, ‖correctionCoeff χ‖ * B := by
      apply Finset.sum_le_sum
      intro χ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound χ) (norm_nonneg _)
    _ = (∑ χ : RayCharacter, ‖correctionCoeff χ‖) * B := (Finset.sum_mul ..).symm
    _ ≤ 32 * B := mul_le_mul_of_nonneg_right correctionCoeff_sum_norm_le hB

end SevenEighths.ProbeCompleted
end

end OAI
end OAIOriginalModule0487

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhaseCancellation
Source SHA256: ee63346ce2709592091877618f6a15e913bddae5c7c5666720c965491b3be79f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0488


namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem quadraticRayValue_norm_one (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : ‖quadraticRayValue r‖ = 1 := by
  rw [quadraticRayValue_eq_fourthRoot r hr]
  simp [fourthRoot]

theorem G_norm_one (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : ‖G a‖ = 1 := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  have hn := Complex.norm_eq_one_of_pow_eq_one hc (by decide : (3 : ℕ) ≠ 0)
  change ‖fixedGValue (residue a)‖ = 1
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift, norm_mul, norm_inv,
    hn, inv_one, one_mul]
  exact quadraticRayValue_norm_one _ ha

theorem cubicTwo_isUnit_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) :
    IsUnit (Ideal.Quotient.mk cubicTwoIdeal a) := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field _
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
  have hd : (2 : O) ∣ a := by
    simpa only [cubicTwoIdeal, Ideal.mem_span_singleton, neg_dvd] using hm
  exact ((odd_residue_iff_not_two_dvd a).mp ha) hd

theorem G_norm_one_of_odd (a : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a)) : ‖G a‖ = 1 :=
  G_norm_one a ha (cubicTwo_isUnit_of_odd a ha)

theorem G_conjugate_cancel (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) : star (G a) * G a = 1 := by
  have hn := G_norm_one a ha hu
  have hs : star (G a) = (G a)⁻¹ := (Complex.inv_eq_conj hn).symm
  rw [hs]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hn]; norm_num))

theorem completed_phase_cancel (c n : O)
    (hc : EisensteinEPrimaryPhase.odd (residue c))
    (hn : EisensteinEPrimaryPhase.odd (residue n))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal (c * n ^ 3))) :
    star (G (c * n ^ 3)) * (G c * reciprocitySign c n * G (n ^ 3)) = 1 := by
  rw [← G_completed_index c n hc hn]
  apply G_conjugate_cancel _ _ hu
  rw [show c * n ^ 3 = c * ((n * n) * n) by ring]
  simp only [residue_mul]
  exact odd_mul _ _ hc (odd_mul _ _ (odd_mul _ _ hn hn) hn)

end SevenEighths.ProbePhase
end

end OAI
end OAIOriginalModule0488

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrimePower
Source SHA256: 2a1f1361af78658be0076053f8169e6900093b25ddc014ff88a2179aec0f1bdb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0489



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein

local notation "O" => ActualEisensteinCubic.O

def primeGauss (p : O) (hp : p ≠ 0) (χ : MulChar (O ⧸ Ideal.span {p}) ℂ)
    (h : O) : ℂ :=
  ∑' x : O ⧸ Ideal.span {p}, χ x * quotientTrace p hp (Ideal.Quotient.mk _ h * x)

def primePowerGauss (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  conductorFourier p (p ^ n) hp (pow_ne_zero _ hp) χ h

theorem primePowerGauss_support (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O)
    (hG : primePowerGauss p hp χ n h ≠ 0) : p ^ n ∣ h :=
  conductorFourier_support p (p ^ n) hp (pow_ne_zero _ hp) χ h hG

theorem primePowerGauss_zero_off_support (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O)
    (hdiv : ¬p ^ n ∣ h) : primePowerGauss p hp χ n h = 0 := by
  by_contra hG
  exact hdiv (primePowerGauss_support p hp χ n h hG)

theorem primePowerGauss_lift (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    primePowerGauss p hp χ n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp χ h := by
  unfold primePowerGauss primeGauss
  rw [conductorFourier_lift]
  have hn : Ideal.absNorm (Ideal.span {p ^ n}) = Ideal.absNorm (Ideal.span {p}) ^ n := by
    rw [← Ideal.span_singleton_pow, map_pow]
  rw [hn, Nat.cast_pow]

theorem primePowerGauss_nonprincipal_extra_divisibility (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n : ℕ) (h : O)
    (hph : p ∣ h) : primePowerGauss p hp χ n (p ^ n * h) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  have hz : Ideal.Quotient.mk (Ideal.span {p}) h = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  have hzero : primeGauss p hp χ h = 0 := by
    rw [primeGauss, tsum_fintype]
    simp only [hz, zero_mul, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  rw [hzero, mul_zero]

theorem primePowerGauss_principal (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hψ : quotientTrace p hp ≠ 1) (n : ℕ) (h : O) :
    primePowerGauss p hp 1 n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        (if p ∣ h then (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ) else -1) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  congr 1
  have hdiv : Ideal.Quotient.mk (Ideal.span {p}) h = 0 ↔ p ∣ h := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  simpa only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss, hdiv] using
    ProbeGauss.frequencyGauss_principal (quotientTrace p hp) hψ
      (Ideal.Quotient.mk (Ideal.span {p}) h)

theorem higher_outer_lift_annihilated (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) {n : ℕ} (hn : 0 < n) (m : O) :
    ξ (Ideal.Quotient.mk (Ideal.span {p}) m) * primePowerGauss p hp χ n (-m) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  by_cases hG : primePowerGauss p hp χ n (-m) = 0
  · rw [hG, mul_zero]
  · have hdneg := primePowerGauss_support p hp χ n (-m) hG
    have hdpow : p ∣ p ^ n := dvd_pow_self p (Nat.ne_of_gt hn)
    have hdm : p ∣ m := dvd_neg.mp (hdpow.trans hdneg)
    have hz : Ideal.Quotient.mk (Ideal.span {p}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdm)
    rw [hz, MulChar.map_zero, zero_mul]

def scalarKOne (p : O) (hp : p ≠ 0)
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {p}, χ d * primePowerGauss p hp ξ n
    (h - p ^ n * GaussianShiftedPartition.representative p d)

theorem scalarKOne_eq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    scalarKOne p hp χ ξ n h =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (ξ * χ⁻¹) n h := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  by_cases hdiv : p ^ n ∣ h
  · obtain ⟨k, rfl⟩ := hdiv
    have hmk (d : O ⧸ Ideal.span {p}) :
        Ideal.Quotient.mk (Ideal.span {p})
          (k - GaussianShiftedPartition.representative p d) =
          Ideal.Quotient.mk (Ideal.span {p}) k - d := by
      rw [map_sub, GaussianShiftedPartition.representative_spec]
    have hscalar : scalarKOne p hp χ ξ n (p ^ n * k) =
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
          ∑ d : O ⧸ Ideal.span {p}, χ d * ProbeGauss.frequencyGauss ξ
            (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
      unfold scalarKOne
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← mul_sub, primePowerGauss_lift]
      have he : primeGauss p hp ξ (k - GaussianShiftedPartition.representative p d) =
          ProbeGauss.frequencyGauss ξ (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
        rw [primeGauss, tsum_fintype]
        simp only [hmk, ProbeGauss.frequencyGauss]
      rw [he]
      ring
    rw [hscalar, ProbeGauss.finite_gauss_convolution, primePowerGauss_lift]
    have hG : primeGauss p hp χ 1 = gaussSum χ (quotientTrace p hp) := by
      simp [primeGauss, tsum_fintype, gaussSum]
    have hF : primeGauss p hp (ξ * χ⁻¹) k =
        ProbeGauss.frequencyGauss (ξ * χ⁻¹) (quotientTrace p hp) (Ideal.Quotient.mk _ k) := by
      simp only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss]
    rw [hG, hF]
    ring
  · rw [primePowerGauss_zero_off_support p hp (ξ * χ⁻¹) n h hdiv, mul_zero]
    unfold scalarKOne
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro d _
    have hndiv : ¬p ^ n ∣ h - p ^ n * GaussianShiftedPartition.representative p d := by
      intro hd
      apply hdiv
      have ha := dvd_add hd (dvd_mul_right (p ^ n)
        (GaussianShiftedPartition.representative p d))
      simpa only [sub_add_cancel] using ha
    rw [primePowerGauss_zero_off_support p hp ξ n _ hndiv, mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI
end OAIOriginalModule0489

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussValuation
Source SHA256: d3a89fbcbfc27d896d16326057e3825d3814a547b99547be22b1a73c27a02a45
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0490


namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem primePowerGauss_at_pow_nonprincipal (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n j : ℕ) :
    primePowerGauss p hp.ne_zero χ n (p ^ j) =
      if j = n then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp.ne_zero χ 1
      else 0 := by
  by_cases he : j = n
  · subst j
    rw [ite_eq_left rfl]
    simpa only [mul_one] using primePowerGauss_lift p hp.ne_zero χ n 1
  rw [ite_eq_right he]
  rcases lt_or_gt_of_ne he with hjn | hnj
  · apply primePowerGauss_zero_off_support
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    omega
  · have hle : n ≤ j := Nat.le_of_lt hnj
    have heq : p ^ j = p ^ n * p ^ (j - n) := by rw [← pow_add, Nat.add_sub_of_le hle]
    rw [heq]
    apply primePowerGauss_nonprincipal_extra_divisibility p hp.ne_zero χ hχ
    exact dvd_pow_self p (by omega)

theorem primePowerGauss_at_pow_principal (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hψ : quotientTrace p hp.ne_zero ≠ 1) (n j : ℕ) :
    primePowerGauss p hp.ne_zero 1 n (p ^ j) =
      (if n + 1 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (n + 1) else 0) -
      (if n ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n else 0) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp.ne_zero
  have hcard : (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1 := by
    rw [Nat.card_units, Nat.cast_sub (Nat.card_pos : 0 < Nat.card (O ⧸ Ideal.span {p})),
      Nat.cast_one]
    rfl
  rcases lt_trichotomy j n with hjn | he | hnj
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), sub_self]
    apply primePowerGauss_zero_off_support
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    omega
  · subst j
    have hnot : ¬p ∣ (1 : O) := by simpa only [isUnit_iff_dvd_one] using hp.not_isUnit
    simpa only [mul_one, ite_eq_right hnot, ite_eq_right (Nat.not_succ_le_self n),
      ite_eq_left (le_refl n), zero_sub, mul_neg_one] using
      primePowerGauss_principal p hp.ne_zero hψ n 1
  · have hle : n ≤ j := by omega
    have heq : p ^ j = p ^ n * p ^ (j - n) := by rw [← pow_add, Nat.add_sub_of_le hle]
    have hd : p ∣ p ^ (j - n) := dvd_pow_self p (by omega)
    rw [heq, primePowerGauss_principal, ite_eq_left hd, ite_eq_left (by omega : n + 1 ≤ j),
      ite_eq_left hle, hcard, pow_succ]
    ring
    exact hψ

end SevenEighths.ProbePrimePower
end

end OAI
end OAIOriginalModule0490

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RadialMellin
Source SHA256: fafd663de5bd857c564980129c02711e08e934740930b38c941d0458c4056f5c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0491



namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped FourierTransform RealInnerProductSpace Topology
namespace SevenEighths.ProbeRadialMellin

def laplace (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ r : ℝ in Ioi 0, f r * Complex.exp (-(t*r : ℝ))

lemma mellin_real (f : ℝ → ℂ) (s : ℝ) :
    mellin f (s : ℂ) = ∫ r : ℝ in Ioi 0, (r^(s-1) : ℝ) • f r := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

lemma mellinConvergent_real (f : ℝ → ℂ) (s : ℝ) :
    MellinConvergent f (s : ℂ) ↔
      IntegrableOn (fun r : ℝ => (r^(s-1) : ℝ) • f r) (Ioi 0) := by
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change (r:ℂ)^((s:ℂ)-1)*f r = (r^(s-1):ℝ)*f r
  rw [show (s:ℂ)-1=((s-1:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow (le_of_lt hr)]

lemma gamma_scaled_integrable {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    IntegrableOn (fun t : ℝ => t^(s-1)*Real.exp (-(r*t))) (Ioi 0) := by
  have hg : MellinConvergent (fun t : ℝ => (Real.exp (-t) : ℂ)) (s : ℂ) := by
    rw [mellinConvergent_real]
    simpa only [Complex.real_smul, RCLike.ofReal_eq_complex_ofReal,
      Complex.ofReal_mul, mul_comm] using!
      (Real.GammaIntegral_convergent hs).ofReal (𝕜 := ℂ)
  have hh := (MellinConvergent.comp_mul_left (f := fun t : ℝ => (Real.exp (-t) : ℂ))
    (s := (s : ℂ)) hr).mpr hg
  rw [mellinConvergent_real] at hh
  simpa only [RCLike.smul_re, RCLike.ofReal_re] using! hh.re

lemma gamma_scaled_integral {s r : ℝ} (hs : 0<s) (hr : 0<r) :
    (∫ t : ℝ in Ioi 0, t^(s-1)*Real.exp (-(r*t))) =
      r^(-s)*Real.Gamma s := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr, one_div, Real.inv_rpow hr.le,
    Real.rpow_neg hr.le]

lemma laplace_mellin_integrable (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    Integrable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ×ℝ => f p.1 *
      ((p.2:ℂ)^(s-1)*Complex.exp (-(p.1*p.2:ℝ))))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    exact hf.comp_fst.mul (by fun_prop)
  have hn (r t : ℝ) (ht : 0<t) :
      ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖ =
        ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t))) := by
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_exp]
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.ofReal_re]
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    apply ((gamma_scaled_integrable hs hr).const_mul ‖f r‖).mono'
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hn r t ht).le
  · have hw : IntegrableOn (fun r : ℝ => r^(-s.re)*‖f r‖) (Ioi 0) := by
      apply hconv.norm.congr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
        Complex.sub_re, Complex.one_re]
      congr 2
      ring
    apply (hw.const_mul (Real.Gamma s.re)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hi : (fun t : ℝ => ‖f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ)))‖) =ᵐ[
      volume.restrict (Ioi 0)] (fun t => ‖f r‖*(t^(s.re-1)*Real.exp (-(r*t)))) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hn r t ht
    rw [integral_congr_ae hi]
    rw [integral_const_mul, gamma_scaled_integral hs hr]
    ring

lemma mellin_laplace (f : ℝ → ℂ) (s : ℂ) (hs : 0<s.re)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hconv : MellinConvergent f (1-s)) :
    mellin (laplace f) s = Complex.Gamma s * mellin f (1-s) := by
  have hi := laplace_mellin_integrable f s hs hf hconv
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ r : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) := by
      unfold mellin laplace
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [smul_eq_mul, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [mul_comm r t]
      ring
    _ = ∫ r : ℝ in Ioi 0, ∫ t : ℝ in Ioi 0,
        f r*((t:ℂ)^(s-1)*Complex.exp (-(r*t:ℝ))) :=
      integral_integral_swap hi.swap
    _ = ∫ r : ℝ in Ioi 0, f r*((r:ℂ)^(-s)*Complex.Gamma s) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [integral_const_mul]
      have hh := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr
      simp only [Complex.ofReal_mul] at *
      rw [hh, one_div, Complex.inv_cpow_ofReal_nonneg hr.le, Complex.cpow_neg]
    _ = _ := by
      rw [mellin, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [show 1-s-1 = -s by ring, smul_eq_mul]
      ring

open EisensteinSchwartzPoisson

def paperConstant : ℝ := 2*Real.pi/Real.sqrt 3

lemma paperConstant_pos : 0<paperConstant := by
  unfold paperConstant
  positivity

lemma paperConstant_sq : paperConstant^2 = 4*Real.pi^2/3 := by
  unfold paperConstant
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  norm_num

lemma paperE_norm (z : ℂ) : ‖paperE z‖=1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp

lemma paper_fourier_pairing (f g : ℂ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ u : ℂ, paperFourier f u * g u) = ∫ z : ℂ, f z * paperFourier g z := by
  have hi : Integrable (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))*f p.2*g p.1) := by
    apply (hg.norm.mul_prod hf.norm).mono'
    · have hp : Continuous (fun p : (ℂ × ℂ) => paperE (-(p.2*p.1))) := by
        simp_rw [paperE_eq_exp]
        fun_prop
      exact (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
        hg.aestronglyMeasurable.comp_fst
    · exact Eventually.of_forall fun p => by
        simp only [norm_mul, paperE_norm, one_mul]
        exact le_of_eq (mul_comm _ _)
  simp only [paperFourier, Complex.real_smul]
  simp_rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]
  rw [integral_integral_swap (hi.const_mul ((2/Real.sqrt 3:ℝ):ℂ))]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by dsimp only; rw [mul_comm z u]; ring

lemma paper_gaussian_fourier (t : ℝ) (ht : 0<t) (u : ℂ) :
    paperFourier (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) u =
      (paperConstant/t:ℝ)*Complex.exp (-(paperConstant^2*‖u‖^2/t:ℝ)) := by
  rw [paperFourier_eq_standard,
    fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat,
    div_self (by norm_num : (2:ℂ)≠0), Complex.cpow_one]
  simp only [Complex.real_smul, ← Complex.ofReal_pow, paperFrequency_norm_sq, paperConstant_sq]
  push_cast
  have he : -(Real.pi:ℂ)^2*((4/3:ℝ)*‖u‖^2:ℝ)/(t:ℂ) =
      -((4*Real.pi^2/3*‖u‖^2/t:ℝ):ℂ) := by push_cast; ring
  push_cast at he
  rw [he]
  unfold paperConstant
  push_cast
  ring

lemma radial_continuous (W : SchwartzMap ℝ ℂ) : Continuous (paperRadialFourier W) := by
  rw [paperRadialFourier_eq_ray]
  exact (paperFourierRayCLM W).continuous.comp Real.continuous_sqrt

lemma radial_isBigO_top (W : SchwartzMap ℝ ℂ) (A : ℕ) :
    paperRadialFourier W =O[atTop] (fun r : ℝ => r^(-(A:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W A 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
  have hh := hb 0 (by omega) r hr
  simp only [LocalLogFourier.eulerDeriv, iteratedDeriv_zero, Real.exp_zero, mul_one] at hh
  have hp : r^A * ‖paperRadialFourier W r‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le (by linarith : r≤1+r) A)
      (norm_nonneg _)).trans hh
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hr _),
    Real.rpow_neg hr.le, Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hr A)).mpr (by simpa [mul_comm] using hp)

lemma radial_isBigO_zero (W : SchwartzMap ℝ ℂ) :
    paperRadialFourier W =O[𝓝[>] 0] (fun r : ℝ => r^(-(0:ℝ))) := by
  obtain ⟨C, hC, hb⟩ := paperRadialFourier_euler_bound W 0 0
  apply isBigO_iff.mpr
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  simpa [LocalLogFourier.eulerDeriv] using hb 0 (by omega) r hr

theorem radial_mellin_convergent (W : SchwartzMap ℝ ℂ) (z : ℂ) (hz : 0<z.re) :
    MellinConvergent (paperRadialFourier W) z := by
  obtain ⟨A, hA⟩ := exists_nat_gt z.re
  exact mellinConvergent_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz

theorem radial_mellin_differentiable (W : SchwartzMap ℝ ℂ) :
    DifferentiableOn ℂ (mellin (paperRadialFourier W)) {z | 0<z.re} := by
  intro z hz
  obtain ⟨A,hA⟩ := exists_nat_gt z.re
  exact (mellin_differentiableAt_of_isBigO_rpow
    ((radial_continuous W).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (radial_isBigO_top W A) hA (radial_isBigO_zero W) hz).differentiableWithinAt

lemma radial_laplace_duality (W : SchwartzMap ℝ ℂ) (t : ℝ) (ht : 0<t) :
    laplace (paperRadialFourier W) t =
      (paperConstant/t:ℝ)*laplace W (paperConstant^2/t) := by
  have hf : Integrable (fun z : ℂ => W (‖z‖^2)) := (radialTestCLM W).integrable
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t:ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using ht) 0 (0:ℂ)
  have h := paper_fourier_pairing _ _ hf hg
  have hleft : (∫ u : ℂ, paperFourier (fun z : ℂ => W (‖z‖^2)) u *
      Complex.exp (-(t:ℂ)*‖u‖^2)) = (Real.pi:ℂ)*laplace (paperRadialFourier W) t := by
    simp_rw [paperFourier_radial]
    rw [laplace, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by simp [Complex.ofReal_mul]
  have hright : (∫ z : ℂ, W (‖z‖^2)*paperFourier
      (fun u : ℂ => Complex.exp (-(t:ℂ)*‖u‖^2)) z) =
      (Real.pi:ℂ)*((paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) := by
    simp_rw [paper_gaussian_fourier t ht]
    rw [laplace, ← integral_const_mul, ← CubicEisenstein.integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      have he : paperConstant^2*‖u‖^2/t = paperConstant^2/t*‖u‖^2 := by ring
      rw [he]
      ring
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h

lemma mellin_reciprocal_laplace (W : ℝ → ℂ) (z : ℂ) :
    mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) =
      (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*mellin (laplace W) z := by
  have hfun : (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) =
      (fun t : ℝ => (paperConstant:ℂ) • ((t:ℂ)^(-1:ℂ) •
        laplace W (paperConstant^2*t⁻¹))) := by
    funext t
    simp [Complex.cpow_neg_one, div_eq_mul_inv, smul_eq_mul, mul_assoc]
  rw [hfun, mellin_const_smul, mellin_cpow_smul]
  rw [show 1-z+(-1) = -z by ring]
  have hh := mellin_comp_inv (fun t : ℝ => laplace W (paperConstant^2*t)) (-z)
  rw [neg_neg] at hh
  rw [hh, mellin_comp_mul_left _ _ (sq_pos_of_pos paperConstant_pos)]
  simp only [smul_eq_mul]
  ring

theorem radial_mellin_gamma (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z)*Complex.Gamma z /
        Complex.Gamma (1-z))*mellin W (1-z) := by
  have hc := CubicReflectionKernel.compact_source_mellin_convergent W a b ha hW
    (W.smooth ⊤) (1-z)
  have hL := mellin_laplace (paperRadialFourier W) (1-z)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    ((radial_continuous W).aestronglyMeasurable)
    (by simpa only [sub_sub_cancel] using radial_mellin_convergent W z hz)
  have hR := mellin_laplace W z hz W.continuous.aestronglyMeasurable hc
  have he : mellin (laplace (paperRadialFourier W)) (1-z) =
      mellin (fun t : ℝ => (paperConstant/t:ℝ)*laplace W (paperConstant^2/t)) (1-z) := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [radial_laplace_duality W t ht]
  rw [hL, sub_sub_cancel, mellin_reciprocal_laplace, hR] at he
  have hg : Complex.Gamma (1-z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
    simp only [Complex.sub_re, Complex.one_re]; linarith)
  apply (mul_left_cancel₀ hg)
  rw [he]
  field_simp

lemma paper_prefactor (z : ℂ) :
    (paperConstant:ℂ)*((paperConstant^2:ℝ):ℂ)^(-z) =
      (paperConstant:ℂ)^(1-2*z) := by
  have hn : (paperConstant:ℂ)≠0 := Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'
  have hh := Complex.cpow_nat_mul' (x := (paperConstant:ℂ)) (n := 2)
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_pos])
    (by simp [Complex.arg_ofReal_of_nonneg paperConstant_pos.le, Real.pi_nonneg]) (-z)
  push_cast
  rw [← hh, show 1-2*z = 1+2*(-z) by ring, Complex.cpow_add _ _ hn,
    Complex.cpow_one]
  norm_num

theorem radial_mellin_identity (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) (hz1 : z.re<1) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  rw [radial_mellin_gamma W a b ha hW z hz hz1, paper_prefactor]

lemma positive_source_mellin (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0)
    (s : ℝ) : 0<(mellin W (s:ℂ)).re ∧ (mellin W (s:ℂ)).im=0 := by
  have hc := CubicReflectionKernel.compact_source_mellin_convergent W a b ha hW
    (W.smooth ⊤) (s:ℂ)
  have hr : ∀r, W r = ((W r).re:ℂ) := by
    intro r
    apply Complex.ext <;> simp [hreal]
  have he : mellin W (s:ℂ) =
      (((∫ r : ℝ in Ioi 0, r^(s-1)*(W r).re):ℝ):ℂ) := by
    rw [mellin_real, ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _
    dsimp only
    rw [hr r, Complex.real_smul, Complex.ofReal_mul]
    simp
  rw [he]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  have hi : IntegrableOn (fun r : ℝ => r^(s-1)*(W r).re) (Ioi 0) := by
    have hh := ((mellinConvergent_real W s).mp hc).re
    simpa only [RCLike.smul_re] using! hh
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hi).mpr
  · have hset : Function.support (fun r : ℝ => r^(s-1)*(W r).re) ∩ Ioi 0 =
        Function.support (fun r : ℝ => (W r).re) := by
      ext r
      simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
      constructor
      · intro hh
        exact fun h => hh.1 (by rw [h, mul_zero])
      · intro hh
        have hw : W r≠0 := fun h => hh (by rw [h]; rfl)
        have hp := ha.trans_le (hW hw).1
        exact ⟨mul_ne_zero (Real.rpow_pos_of_pos hp _).ne' hh, hp⟩
    rw [hset]
    apply ((Complex.continuous_re.comp W.continuous).isOpen_support).measure_pos volume
    by_contra h
    apply hne
    ext r
    have hh : (W r).re=0 := by
      by_contra hn
      exact h ⟨r,hn⟩
    change W r = 0
    rw [hr r, hh, Complex.ofReal_zero]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (hnonneg r)

theorem radial_mellin_positive (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0)
    (s : ℝ) (hs : 0<s) (hs1 : s<1) :
    0<(mellin (paperRadialFourier W) (s:ℂ)).re ∧
      (mellin (paperRadialFourier W) (s:ℂ)).im=0 := by
  obtain ⟨hp, hz⟩ := positive_source_mellin W a b ha hW hreal hnonneg hne (1-s)
  have hh : mellin W (1-(s:ℂ)) = ((mellin W ((1-s:ℝ):ℂ)).re:ℂ) := by
    rw [show 1-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl]
    exact Complex.ext (by simp) (by simpa using hz)
  rw [radial_mellin_identity W a b ha hW (s:ℂ) hs hs1, hh]
  have hpow : (paperConstant:ℂ)^(1-2*(s:ℂ)) = ((paperConstant^(1-2*s):ℝ):ℂ) := by
    rw [show 1-2*(s:ℂ)=((1-2*s:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow paperConstant_pos.le]
  rw [hpow, show 1-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re,
    Complex.ofReal_im, and_true]
  exact mul_pos (div_pos (mul_pos (Real.rpow_pos_of_pos paperConstant_pos _)
    (Real.Gamma_pos_of_pos hs)) (Real.Gamma_pos_of_pos (by linarith))) hp

theorem radial_mellin_one_sixth_pos (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0) :
    0<(mellin (paperRadialFourier W) (1/6)).re ∧
      (mellin (paperRadialFourier W) (1/6)).im=0 := by
  simpa using radial_mellin_positive W a b ha hW hreal hnonneg hne (1/6)
    (by norm_num) (by norm_num)

theorem radial_mellin_identity_right (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (z : ℂ) (hz : 0<z.re) :
    mellin (paperRadialFourier W) z =
      ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
        mellin W (1-z) := by
  let D : Set ℂ := {z | 0<z.re}
  let G : ℂ → ℂ := fun z =>
    ((paperConstant:ℂ)^(1-2*z)*Complex.Gamma z / Complex.Gamma (1-z))*
      mellin W (1-z)
  have hop : IsOpen D := isOpen_lt continuous_const Complex.continuous_re
  have hcv : Convex ℝ D := (convex_Ioi (0:ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have hf : AnalyticOnNhd ℂ (mellin (paperRadialFourier W)) D :=
    (radial_mellin_differentiable W).analyticOnNhd hop
  have hG : DifferentiableOn ℂ G D := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (paperConstant:ℂ)^(1-2*z)) w :=
      (differentiableAt_const _ |>.sub (differentiableAt_id.const_mul 2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr paperConstant_pos.ne'))
    have h2 := CubicReflectionKernel.Gamma_differentiableAt_of_re_pos w hw
    have h3 := (Complex.differentiable_one_div_Gamma (1-w)).comp w
      (differentiableAt_const _ |>.sub differentiableAt_id)
    have h4 := (CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hW
      (W.smooth ⊤) (1-w)).comp w (differentiableAt_const _ |>.sub differentiableAt_id)
    simpa only [G, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply] using! (((h1.mul h2).mul h3).mul h4).differentiableWithinAt
  have hev : mellin (paperRadialFourier W) =ᶠ[𝓝 (1/2:ℂ)] G := by
    have hstrip : IsOpen {w:ℂ | 0<w.re ∧ w.re<1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hstrip.mem_nhds (by norm_num)] with w hw
    exact radial_mellin_identity W a b ha hW w hw.1 hw.2
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hop)
    hcv.isPreconnected (by norm_num [D]) hev hz

lemma gamma_quotient_strip (lo hi : ℝ) (hlo : 0<lo) :
    ∃ (n : ℕ) (C : ℝ), 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      ‖Complex.Gamma ((σ:ℂ)+t*Complex.I) / Complex.Gamma (1-((σ:ℂ)+t*Complex.I))‖ ≤
        C*(1+|t|)^n := by
  obtain ⟨A,hA⟩ := exists_nat_gt hi
  obtain ⟨C,hC,hb⟩ := CubicReflectionKernel.Gamma_pair_strip_bound 1 (by norm_num) A
  refine ⟨2*A+2,C/lo,div_pos hC hlo,?_⟩
  intro σ hσ t
  have hσ0 : 0<σ := hlo.trans_le hσ.1
  have hz : (σ:ℂ)+t*Complex.I≠0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at this
    linarith
  have hh := hb σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ t
  norm_num only [Complex.ofReal_one] at hh
  rw [add_comm (1:ℂ), Complex.Gamma_add_one _ hz, mul_div_assoc, norm_mul] at hh
  have hnorm : lo≤‖(σ:ℂ)+t*Complex.I‖ := by
    apply hσ.1.trans
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero] using
      Complex.re_le_norm ((σ:ℂ)+t*Complex.I)
  have hh' := (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans hh
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlo).mpr
  simpa [div_mul_eq_mul_div, mul_comm] using hh'

theorem radial_mellin_strip_decay (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0<lo) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      (1+|t|)^N * ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ ≤ C := by
  obtain ⟨n,Cg,hCg,hg⟩ := gamma_quotient_strip lo hi hlo
  obtain ⟨Cw,hCw,hw⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W a b ha hW
    (W.smooth ⊤) (1-hi) (1-lo) (n+N)
  have hc : Continuous (fun σ : ℝ => paperConstant^(1-2*σ)) :=
    (Real.continuous_const_rpow paperConstant_pos.ne').comp
      (continuous_const.sub (continuous_const.mul continuous_id))
  obtain ⟨B,hB⟩ := isCompact_Icc.bddAbove_image (hc.continuousOn (s := Icc lo hi))
  let Cp := |B|+1
  have hCp : 0<Cp := by dsimp [Cp]; positivity
  refine ⟨Cp*Cg*Cw,by positivity,?_⟩
  intro σ hσ t
  have hp : ‖(paperConstant:ℂ)^(1-2*((σ:ℂ)+t*Complex.I))‖≤Cp := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos paperConstant_pos]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      show (2:ℂ).re=2 by rfl, show (2:ℂ).im=0 by rfl, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact (hB (mem_image_of_mem _ hσ)).trans (by change B≤|B|+1; linarith [le_abs_self B])
  have hwb := hw (1-σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩ (-t)
  rw [abs_neg, show ((1-σ:ℝ):ℂ)+(-t:ℝ)*Complex.I = 1-((σ:ℂ)+t*Complex.I) by
    push_cast; ring] at hwb
  rw [radial_mellin_identity_right W a b ha hW _ (by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact hlo.trans_le hσ.1), mul_div_assoc, norm_mul, norm_mul]
  calc
    _ ≤ (1+|t|)^N*(Cp*(Cg*(1+|t|)^n)*
        ‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      gcongr
      exact hg σ hσ t
    _ = (Cp*Cg)*((1+|t|)^(n+N)*‖mellin W (1-((σ:ℂ)+t*Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwb (by positivity)

theorem radial_mellin_analytic (W : SchwartzMap ℝ ℂ) :
    AnalyticOnNhd ℂ (mellin (paperRadialFourier W)) {z | 0<z.re} :=
  (radial_mellin_differentiable W).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

theorem radial_mellin_strip_rapid (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (lo hi : ℝ) (hlo : 0<lo) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ σ∈Icc lo hi, ∀t : ℝ,
      ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ ≤ C/(1+|t|)^N := by
  obtain ⟨C,hC,hb⟩ := radial_mellin_strip_decay W a b ha hW lo hi hlo N
  refine ⟨C,hC,fun σ hσ t => (le_div_iff₀ (by positivity)).mpr ?_⟩
  simpa only [mul_comm] using hb σ hσ t

theorem radial_mellin_vertical_integrable (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (σ : ℝ) (hσ : 0<σ) :
    Complex.VerticalIntegrable (mellin (paperRadialFourier W)) σ := by
  obtain ⟨C,hC,hb⟩ := radial_mellin_strip_decay W a b ha hW σ σ hσ 2
  have hc : Continuous (fun t : ℝ => mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (radial_mellin_analytic W _ (by simpa using hσ)).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    simpa only [div_eq_mul_inv] using CubicReflectionKernel.weighted_two_to_cauchy
      (norm_nonneg _) t (hb σ ⟨le_rfl,le_rfl⟩ t)

theorem radial_mellin_inverse_integrable (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ) (hσ : 0<σ) (hx : 0<x) :
    Integrable (fun t : ℝ => (x:ℂ)^(-((σ:ℂ)+t*Complex.I))*
      mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)) := by
  have hi := radial_mellin_vertical_integrable W a b ha hW σ hσ
  apply (hi.norm.const_mul (x^(-σ))).mono'
  · have hm := hi.aestronglyMeasurable
    have hc : Continuous (fun t : ℝ => (x:ℂ)^(-((σ:ℂ)+t*Complex.I))) :=
      (by fun_prop : Continuous (fun t : ℝ => -((σ:ℂ)+t*Complex.I))).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
    exact hc.aestronglyMeasurable.mul hm
  · exact Eventually.of_forall fun t => by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp

theorem radial_mellin_inversion (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ) (hσ : 0<σ) (hx : 0<x) :
    mellinInv σ (mellin (paperRadialFourier W)) x = paperRadialFourier W x :=
  mellinInv_mellin_eq σ (paperRadialFourier W) hx
    (radial_mellin_convergent W σ hσ)
    (radial_mellin_vertical_integrable W a b ha hW σ hσ)
    (radial_continuous W).continuousAt

theorem radial_mellin_one_sixth_ne_zero (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W ⊆ Icc a b)
    (hreal : ∀r, (W r).im=0) (hnonneg : ∀r, 0≤(W r).re) (hne : W≠0) :
    mellin (paperRadialFourier W) (1/6) ≠ 0 := by
  intro h
  have hp := (radial_mellin_one_sixth_pos W a b ha hW hreal hnonneg hne).1
  rw [h] at hp
  exact (lt_irrefl 0) hp

end SevenEighths.ProbeRadialMellin

end

end OAI
end OAIOriginalModule0491

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorProfiles
Source SHA256: d19cb167702eb17958b3eafc3240e81d28d4013382e3197c624f33a7a866bf44
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0492


namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def expNeg (x : ℝ) : ℂ := Complex.exp (-(x : ℂ))

lemma expNeg_smooth : ContDiff ℝ ∞ expNeg := by
  exact Complex.ofRealCLM.contDiff.neg.cexp

lemma expNeg_hasDerivAt (x : ℝ) : HasDerivAt expNeg (-expNeg x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).neg).cexp
  convert! h using 1; simp [expNeg]

lemma iteratedDeriv_expNeg (n : ℕ) :
    iteratedDeriv n expNeg = fun x => (-1 : ℂ)^n*expNeg x := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, (expNeg_hasDerivAt x).deriv, pow_succ]
    ring

lemma expNeg_derivative_norm (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n expNeg x‖ = Real.exp (-x) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expNeg]
  simp [expNeg, norm_pow, Complex.norm_exp]

lemma expNeg_derivative_decay (n i : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1+x)^n*‖iteratedFDeriv ℝ i expNeg x‖ ≤ (n.factorial : ℝ)*Real.exp 1 := by
  rw [expNeg_derivative_norm]
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (1+x) (by linarith : 0 ≤ 1+x) n)
  calc
    _ ≤ (Real.exp (1+x)*(n.factorial : ℝ))*Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_right_comm, ← Real.exp_add, show (1+x)+(-x) = 1 by ring]
      ring

def productProfile (Ω V T : ℝ → ℂ) (A B C s : ℝ) : ℂ :=
  Ω s*(1-V (A*s))*expNeg (B*s)*T (C*s)

def inverseProfile (W V : ℝ → ℂ) (R x : ℝ) : ℂ := W x*V (R*x)

def logSourceFun (Ω V T : ℝ → ℂ) (A B C y : ℝ) : ℂ :=
  Ω y*(1-V (A*Real.exp y))*expNeg (B*Real.exp y)*T (C*Real.exp y)

lemma logSource_smooth (Ω V T : ℝ → ℂ) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T) (A B C : ℝ) :
    ContDiff ℝ ∞ (logSourceFun Ω V T A B C) := by
  unfold logSourceFun
  have hE := expNeg_smooth
  fun_prop

lemma logSource_compact (Ω V T : ℝ → ℂ) (hΩ : HasCompactSupport Ω) (A B C : ℝ) :
    HasCompactSupport (logSourceFun Ω V T A B C) :=
  ((hΩ.mul_right).mul_right).mul_right

def logSource (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C : ℝ) : SchwartzMap ℝ ℂ :=
  (logSource_compact Ω V T hΩc A B C).toSchwartzMap (logSource_smooth Ω V T hΩ hV hT A B C)

@[simp] lemma logSource_apply (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C y : ℝ) :
    logSource Ω V T hΩc hΩ hV hT A B C y =
      Ω y*(1-V (A*Real.exp y))*expNeg (B*Real.exp y)*T (C*Real.exp y) := rfl

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end OAIOriginalModule0492

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesBounds
Source SHA256: ae320323b2353a2580fdfd37f735a006b80cd7a0c9a929eb0f683c02a09ddf74
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0493


namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

theorem scaled_derivatives_of_decay (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hdecay : ∀ i ≤ K, ∀ u : ℝ, 0 ≤ u →
      (1+u)^K*‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  let m := Real.exp (-L)
  let H := Real.exp L
  let S : ℝ := ∑ j ∈ Finset.range (K+1), (j.factorial : ℝ)*CF*(H^2)^j
  have hm : 0 < m := Real.exp_pos _
  have hH : 1 ≤ H := Real.one_le_exp_iff.mpr hL
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨S/m^K,by positivity,?_⟩
  intro R hR j hj y hy
  have hh := FourierBridge.coupled_factor_uniform_derivative F R 1 y m H CF 0 K j hF
    hR hm (Real.exp_le_one_iff.mpr (by linarith)) hH (by simpa using hH)
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).1))
    (Real.exp_le_exp.mpr (by simpa using (abs_le.mp hy).2))
    hj hCF (by simpa using hdecay)
  simp only [zero_add, pow_zero, mul_one, one_mul] at hh
  have hs : (j.factorial : ℝ)*CF*(H^2)^j ≤ S := by
    dsimp only [S]
    apply Finset.single_le_sum (s := Finset.range (K+1))
      (f := fun i => (i.factorial : ℝ)*CF*(H^2)^i) (a := j)
    · intro i hi; positivity
    · exact Finset.mem_range.mpr (by omega)
  exact (le_div_iff₀ (pow_pos hm K)).mpr (by simpa [mul_comm] using hh.trans hs)

theorem scaled_schwartz_derivatives (F : SchwartzMap ℝ ℂ)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => F (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay F (F.smooth ⊤) L hL K
    (FourierBridge.schwartzDerivativeDecayConstant F K K)
    (FourierBridge.schwartzDerivativeDecayConstant_nonneg F K K)
  intro i hi u hu
  simpa using FourierBridge.schwartz_derivative_decay_finite F 0 K K i u le_rfl hi hu

theorem scaled_expNeg_derivatives (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (fun z => expNeg (R*Real.exp z)) y‖ ≤ C := by
  apply scaled_derivatives_of_decay expNeg expNeg_smooth L hL K
    ((K.factorial : ℝ)*Real.exp 1) (by positivity)
  intro i hi u hu
  exact expNeg_derivative_decay K i u hu

lemma const_one_derivative_norm (j : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const]
  split_ifs <;> simp

lemma complement_derivative_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (C : ℝ) (j : ℕ) (y : ℝ) (hbound : ‖iteratedFDeriv ℝ j F y‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun z => 1-F z) y‖ ≤ 1+C := by
  change ‖iteratedFDeriv ℝ j ((fun _ : ℝ => (1 : ℂ)) - F) y‖ ≤ _
  rw [iteratedFDeriv_sub contDiff_const (hF.of_le (by simp))]
  change ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y - iteratedFDeriv ℝ j F y‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add (const_one_derivative_norm j y) hbound)

lemma product_derivative_bound (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (K j : ℕ) (hj : j ≤ K) (y : ℝ)
    (hFb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i F y‖ ≤ CF)
    (hGb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i G y‖ ≤ CG) :
    ‖iteratedFDeriv ℝ j (fun z => F z*G z) y‖ ≤ (2 : ℝ)^K*CF*CG := by
  apply (norm_iteratedFDeriv_mul_le hF hG y (n := j) (by simp)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ)*CF*CG := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFb i (hi'.trans hj)) (by positivity))
        (hGb (j-i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ)^j*CF*CG := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hCF) hCG

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end OAIOriginalModule0493

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesUniform
Source SHA256: 7a386ddfd33ff9c8f8cd2dcbfb2b7c2b825d50591a59076a4f8892bab7540636
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0494


namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma logSource_support (Ω V T : ℝ → ℂ) (A B C : ℝ) :
    tsupport (logSourceFun Ω V T A B C) ⊆ tsupport Ω :=
  tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans tsupport_mul_subset_left)

theorem logSource_window_derivatives (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ j ≤ K, ∀ y : ℝ, |y| ≤ L →
      ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ ≤ C := by
  obtain ⟨CΩ,hCΩ,hbΩ⟩ := hΩc.exists_bound_iteratedFDeriv hΩ K
  obtain ⟨CV,hCV,hbV⟩ := scaled_schwartz_derivatives V L hL K
  obtain ⟨CT,hCT,hbT⟩ := scaled_schwartz_derivatives T L hL K
  obtain ⟨CE,hCE,hbE⟩ := scaled_expNeg_derivatives L hL K
  let P := (2 : ℝ)^K
  refine ⟨P*(P*(P*CΩ*(1+CV))*CE)*CT,by dsimp [P]; positivity,?_⟩
  intro A B D hA hB hD j hj y hy
  let v : ℝ → ℂ := fun z => V (A*Real.exp z)
  let e : ℝ → ℂ := fun z => expNeg (B*Real.exp z)
  let t : ℝ → ℂ := fun z => T (D*Real.exp z)
  have hv : ContDiff ℝ ∞ v := (V.smooth ⊤).comp (by fun_prop)
  have he : ContDiff ℝ ∞ e := expNeg_smooth.comp (by fun_prop)
  have ht : ContDiff ℝ ∞ t := (T.smooth ⊤).comp (by fun_prop)
  have hcv : ContDiff ℝ ∞ (fun z => 1-v z) := contDiff_const.sub hv
  have hcomp (i : ℕ) (hi : i ≤ K) : ‖iteratedFDeriv ℝ i (fun z => 1-v z) y‖ ≤ 1+CV :=
    complement_derivative_bound v hv CV i y (hbV A hA i hi y hy)
  have hfirst (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)) y‖ ≤ P*CΩ*(1+CV) :=
    product_derivative_bound Ω _ hΩ hcv CΩ (1+CV) hCΩ (by positivity) K i hi y
      (fun q hq => hbΩ q hq y) hcomp
  have hsecond (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z*(1-v z)*e z) y‖ ≤ P*(P*CΩ*(1+CV))*CE :=
    product_derivative_bound _ e (hΩ.mul hcv) he _ CE (by dsimp [P]; positivity) hCE
      K i hi y hfirst (fun q hq => hbE B hB q hq y hy)
  exact product_derivative_bound _ t ((hΩ.mul hcv).mul he) ht _ CT
    (by dsimp [P]; positivity) hCT K j hj y hsecond (fun q hq => hbT D hD q hq y hy)

theorem logSource_uniform_seminorm (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ k j : ℕ, j ≤ K →
      SchwartzMap.seminorm ℝ k j (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)
        ≤ L^k*C := by
  obtain ⟨C,hC,hb⟩ := logSource_window_derivatives Ω V T hΩc hΩ L hL K
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD k j hj
  apply SchwartzMap.seminorm_le_bound' ℝ k j _ (by positivity)
  intro y
  change ‖y‖^k*‖iteratedDeriv j (logSourceFun Ω V T A B D) y‖ ≤ L^k*C
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hz : ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ = 0
  · rw [hz, mul_zero]; positivity
  have hys : y ∈ tsupport Ω := logSource_support Ω V T A B D
    ((support_iteratedFDeriv_subset j) (by simpa [Function.mem_support] using hz))
  have hy : |y| ≤ L := abs_le.mpr (hwindow hys)
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy k)
    (hb A B D hA hB hD j hj y hy) (norm_nonneg _) (pow_nonneg hL k)

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end OAIOriginalModule0494

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFourier
Source SHA256: 3cfebeba1b243d97e149968ea3aabefc62996c0751c1275580a2875dda9a7867
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0495


namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeDetectorProfiles
noncomputable section

theorem uniform_fourier_moment (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      (∫ t : ℝ, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  obtain ⟨C,hC,hb⟩ := logSource_uniform_seminorm Ω V T hΩc hΩ L hL hwindow (J+p)
  let C' := (1+L^p)*C
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  refine ⟨(2 : ℝ)^J*(FourierBridge.coefficientMomentBound 0 C'+
    FourierBridge.coefficientMomentBound J C'),?_,?_⟩
  · exact mul_nonneg (by positivity) (add_nonneg
      (FourierBridge.coefficientMomentBound_nonneg 0 C' hC')
      (FourierBridge.coefficientMomentBound_nonneg J C' hC'))
  intro A B D hA hB hD
  have hh := FourierBridge.uniform_fourier_one_plus_moment
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J 1 C'
    (by norm_num) hC' (by
      intro i hi
      have h0 := hb A B D hA hB hD 0 i hi
      have hp := hb A B D hA hB hD p i hi
      simp only [pow_zero, one_mul] at h0 ⊢
      dsimp only [C']
      linarith)
  simpa only [one_mul] using hh

theorem schwartz_weighted_tail (g : SchwartzMap ℝ ℂ) (J N : ℕ)
    (R : ℝ) (hR : 0 < R) :
    R^N*(∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J*‖(𝓕 g) t‖) ≤
      ∫ t : ℝ, (1+‖t‖)^(J+N)*‖(𝓕 g) t‖ := by
  have hiJ := AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hiN := AnalyticBridge.schwartz_fourier_one_plus_integrable g (J+N)
  have hs : MeasurableSet {t : ℝ | R < ‖t‖} := measurableSet_lt measurable_const continuous_norm.measurable
  rw [← integral_const_mul]
  apply (setIntegral_mono_on (hiJ.const_mul _).integrableOn hiN.integrableOn hs ?_).trans
    (setIntegral_le_integral hiN (Filter.Eventually.of_forall (by intro t; positivity)))
  intro t ht
  have hp : R^N ≤ (1+‖t‖)^N := pow_le_pow_left₀ hR.le (by change R < ‖t‖ at ht; linarith) N
  calc
    _ ≤ (1+‖t‖)^N*((1+‖t‖)^J*‖(𝓕 g) t‖) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem uniform_fourier_tail (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (J N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ R : ℝ, 0 < R →
      (∫ t : ℝ in {t | R < ‖t‖}, (1+‖t‖)^J *
        ‖(𝓕 (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D)) t‖) ≤ C/R^N := by
  obtain ⟨C,hC,hb⟩ := uniform_fourier_moment Ω V T hΩc hΩ L hL hwindow (J+N)
  refine ⟨C,hC,?_⟩
  intro A B D hA hB hD R hR
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa [mul_comm] using (schwartz_weighted_tail
    (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) J N R hR).trans
    (hb A B D hA hB hD)

theorem logSource_product_inversion (Ω V T : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B D x y : ℝ) :
    logSourceFun Ω V T A B D (x+y) =
      ∫ t : ℝ, FourierBridge.logPhase t x * FourierBridge.logPhase t y *
        (𝓕 (logSource Ω V T hΩc hΩ hV hT A B D)) t := by
  have hh := FourierBridge.schwartz_log_inversion
    (logSource Ω V T hΩc hΩ hV hT A B D) (x+y)
  change logSourceFun Ω V T A B D (x+y) = _ at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← FourierBridge.logPhase_add]
  congr 1
  simp only [FourierBridge.logPhase, RCLike.inner_apply, conj_trivial]
  congr 2
  ring_nf

end
end SevenEighths.HeckeDetectorFourier

end OAI
end OAIOriginalModule0495

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFourierSeparation
Source SHA256: 3be7de3dea3a5f4318df2ccbfb87492ac0b0baa2929b33613507133e92e6cd69
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0496


namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

def phasePolynomial {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, a i*FourierBridge.logPhase t (x i)

lemma phasePolynomial_continuous {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) :
    Continuous (phasePolynomial S a x) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul (FourierBridge.logPhase_continuous_left _)

lemma phasePolynomial_norm {α : Type*} (S : Finset α) (a : α → ℂ) (x : α → ℝ) (t : ℝ) :
    ‖phasePolynomial S a x t‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  calc
    _ ≤ ∑ i ∈ S, ‖a i*FourierBridge.logPhase t (x i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, FourierBridge.logPhase_norm, mul_one]

lemma separated_pair_integrable {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    Integrable (fun t => (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t) := by
  have hmeas : AEStronglyMeasurable (fun t => phasePolynomial S a x t*phasePolynomial T b y t) volume :=
    ((phasePolynomial_continuous S a x).mul
    (phasePolynomial_continuous T b y)).aestronglyMeasurable
  have hh := (𝓕 g).integrable.mul_bdd hmeas (Filter.Eventually.of_forall (fun t =>
    (norm_mul _ _).le.trans (mul_le_mul (phasePolynomial_norm S a x t)
      (phasePolynomial_norm T b y t) (norm_nonneg _) (Finset.sum_nonneg (fun i hi => norm_nonneg _)))))
  simpa only [mul_assoc] using hh

lemma schwartz_product_inversion (g : SchwartzMap ℝ ℂ) (x y : ℝ) :
    g (x+y) = ∫ t : ℝ,
      (𝓕 g) t*FourierBridge.logPhase t x*FourierBridge.logPhase t y := by
  rw [FourierBridge.schwartz_log_inversion g (x+y)]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp : Complex.exp (↑(2*Real.pi*inner ℝ t (x+y))*Complex.I) =
      FourierBridge.logPhase t x*FourierBridge.logPhase t y := by
    rw [← FourierBridge.logPhase_add]
    simp only [FourierBridge.logPhase, RCLike.inner_apply, conj_trivial]
    congr 2
    ring_nf
  rw [hp]
  ring

theorem finite_pair_separation {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (g : SchwartzMap ℝ ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)) =
      ∫ t : ℝ, (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t := by
  have hterm (i : α) (j : β) : Integrable (fun t : ℝ =>
      (𝓕 g) t*(a i*FourierBridge.logPhase t (x i))*(b j*FourierBridge.logPhase t (y j))) := by
    simpa only [phasePolynomial, Finset.sum_singleton] using
      separated_pair_integrable {i} {j} a b x y g
  have hsum (t : ℝ) : (𝓕 g) t*phasePolynomial S a x t*phasePolynomial T b y t =
      ∑ i ∈ S, ∑ j ∈ T,
        (𝓕 g) t*(a i*FourierBridge.logPhase t (x i))*(b j*FourierBridge.logPhase t (y j)) := by
    simp only [phasePolynomial, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  simp_rw [hsum]
  rw [integral_finsetSum S (fun i hi => integrable_finsetSum T (fun j hj => hterm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum T (fun j hj => hterm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [schwartz_product_inversion g (x i) (y j), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

end
end SevenEighths.HeckeDetectorFourier

end OAI
end OAIOriginalModule0496

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFourierWitness
Source SHA256: 0626b78ba8177f8bb6750821c9ee33f403d3e7b62d08ea7b1e26a83783e246a7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0497


namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

lemma frequency_interval_compl (R : ℝ) :
    (Set.Icc (-R) R)ᶜ = {t : ℝ | R < ‖t‖} := by
  ext t
  simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_ofPred_eq, Real.norm_eq_abs,
    ← abs_le, not_le]

private lemma exists_interval_norm_product (f h : ℝ → ℂ) (hf : Continuous f)
    (hh : Integrable h) (hprod : Integrable (fun u => h u * f u))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∫ u : ℝ in Set.Icc (-R) R, h u * f u‖ ≤ (∫ u : ℝ, ‖h u‖) * ‖f t‖ := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (-R) R).Nonempty from ⟨0, by constructor <;> linarith⟩)
    hf.norm.continuousOn
  refine ⟨t, by simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using ht, ?_⟩
  have hb : Integrable (fun u => ‖h u‖ * ‖f t‖) := hh.norm.mul_const _
  calc
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R, ‖h u * f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Set.Icc (-R) R, ‖h u‖ * ‖f t‖ := by
      apply setIntegral_mono_on hprod.norm.integrableOn hb.integrableOn measurableSet_Icc
      intro u hu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hmax hu) (norm_nonneg _)
    _ ≤ ∫ u : ℝ, ‖h u‖ * ‖f t‖ :=
      setIntegral_le_integral hb (Filter.Eventually.of_forall (by intro u; positivity))
    _ = _ := integral_mul_const _ _

theorem exists_interval_frequency {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∫ u : ℝ in Set.Icc (-R) R,
        (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u‖ ≤
        (∫ u : ℝ, ‖(𝓕 g) u‖)*
          ‖phasePolynomial S a x t*phasePolynomial T b y t‖ := by
  have hf : Continuous (fun u => phasePolynomial S a x u * phasePolynomial T b y u) :=
    (phasePolynomial_continuous S a x).mul (phasePolynomial_continuous T b y)
  have hi : Integrable (fun u => (𝓕 g) u *
      (phasePolynomial S a x u * phasePolynomial T b y u)) := by
    simpa only [mul_assoc] using separated_pair_integrable S T a b x y g
  obtain ⟨t, ht, hb⟩ := exists_interval_norm_product
    (fun u => phasePolynomial S a x u * phasePolynomial T b y u)
    (fun u => (𝓕 g) u) hf (𝓕 g).integrable hi R hR
  exact ⟨t, ht, by simpa only [mul_assoc] using hb⟩

private theorem integral_sub_interval_norm_le (f w : ℝ → ℂ) (E R : ℝ)
    (hf : Integrable f) (hw : Integrable w)
    (hbound : ∀ u, ‖f u‖ ≤ E * ‖w u‖) :
    ‖(∫ u : ℝ, f u) - (∫ u : ℝ in Set.Icc (-R) R, f u)‖ ≤
      E * (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) := by
  have hsplit := integral_add_compl (s := Set.Icc (-R) R) measurableSet_Icc hf
  have heq : (∫ u : ℝ, f u) - (∫ u : ℝ in Set.Icc (-R) R, f u) =
      ∫ u : ℝ in {u | R < ‖u‖}, f u := by
    rw [← hsplit, frequency_interval_compl]
    abel
  rw [heq]
  have hm : MeasurableSet {u : ℝ | R < ‖u‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  calc
    _ ≤ ∫ u : ℝ in {u | R < ‖u‖}, ‖f u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in {u | R < ‖u‖}, E * ‖w u‖ :=
      setIntegral_mono_on hf.norm.integrableOn (hw.norm.const_mul E).integrableOn hm
        (fun u _ => hbound u)
    _ = _ := integral_const_mul _ _

private theorem separated_pair_norm_le {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ) (z : ℂ) (u : ℝ) :
    ‖z * phasePolynomial S a x u * phasePolynomial T b y u‖ ≤
      ((∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)) * ‖z‖ := by
  rw [mul_assoc, norm_mul, norm_mul, mul_comm ‖z‖]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  exact mul_le_mul (phasePolynomial_norm S a x u) (phasePolynomial_norm T b y u)
    (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

private theorem schwartz_tail_le (g : SchwartzMap ℝ ℂ) (R : ℝ)
    (hR : 0 < R) (N : ℕ) :
    (∫ u : ℝ in {u | R < ‖u‖}, ‖(𝓕 g) u‖) ≤
      (∫ u : ℝ, (1+‖u‖)^N * ‖(𝓕 g) u‖) / R^N := by
  apply (le_div_iff₀ (pow_pos hR N)).mpr
  simpa only [pow_zero, one_mul, Nat.zero_add, mul_comm] using
    schwartz_weighted_tail g 0 N R hR

private theorem separated_pair_tail_of_bound {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (w : ℝ → ℂ) (R M : ℝ) (N : ℕ)
    (hi : Integrable (fun u => w u * phasePolynomial S a x u * phasePolynomial T b y u))
    (hw : Integrable w) (hbound : (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) ≤ M / R^N) :
    ‖(∫ u : ℝ, w u * phasePolynomial S a x u * phasePolynomial T b y u) -
      (∫ u : ℝ in Set.Icc (-R) R,
        w u * phasePolynomial S a x u * phasePolynomial T b y u)‖ ≤
      ((∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)) / R^N * M := by
  let E := (∑ i ∈ S, ‖a i‖) * (∑ j ∈ T, ‖b j‖)
  have hE : 0 ≤ E := mul_nonneg
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have htail := integral_sub_interval_norm_le
    (fun u => w u * phasePolynomial S a x u * phasePolynomial T b y u)
    w E R hi hw (fun u => separated_pair_norm_le S T a b x y (w u) u)
  calc
    _ ≤ E * (∫ u : ℝ in {u | R < ‖u‖}, ‖w u‖) := htail
    _ ≤ E * (M / R^N) := mul_le_mul_of_nonneg_left hbound hE
    _ = _ := by rw [div_mul_eq_mul_div, mul_div_assoc]

theorem separated_pair_tail {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ‖(∫ u : ℝ, (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u) -
      (∫ u : ℝ in Set.Icc (-R) R,
        (𝓕 g) u*phasePolynomial S a x u*phasePolynomial T b y u)‖ ≤
      ((∑ i ∈ S, ‖a i‖)*(∑ j ∈ T, ‖b j‖))/R^N *
        (∫ u : ℝ, (1+‖u‖)^N*‖(𝓕 g) u‖) := by
  exact separated_pair_tail_of_bound S T a b x y (fun u : ℝ => (𝓕 g : SchwartzMap ℝ ℂ) u)
    R (∫ u : ℝ, (1+‖u‖)^N * ‖(𝓕 g) u‖) N
    (separated_pair_integrable S T a b x y g) (𝓕 g).integrable
    (schwartz_tail_le g R hR N)

theorem exists_bounded_frequency {α β : Type*} (S : Finset α) (T : Finset β)
    (a : α → ℂ) (b : β → ℂ) (x : α → ℝ) (y : β → ℝ)
    (g : SchwartzMap ℝ ℂ) (R : ℝ) (hR : 0 < R) (N : ℕ) :
    ∃ t : ℝ, ‖t‖ ≤ R ∧
      ‖∑ i ∈ S, ∑ j ∈ T, a i*b j*g (x i+y j)‖ ≤
      ((∑ i ∈ S, ‖a i‖)*(∑ j ∈ T, ‖b j‖))/R^N *
        (∫ u : ℝ, (1+‖u‖)^N*‖(𝓕 g) u‖) +
      (∫ u : ℝ, ‖(𝓕 g) u‖)*
        ‖phasePolynomial S a x t*phasePolynomial T b y t‖ := by
  obtain ⟨t,ht,hb⟩ := exists_interval_frequency S T a b x y g R hR.le
  refine ⟨t,ht,?_⟩
  rw [finite_pair_separation]
  have htail := separated_pair_tail S T a b x y g R hR N
  exact (norm_le_norm_sub_add _ _).trans (add_le_add htail hb)

end
end SevenEighths.HeckeDetectorFourier

end OAI
end OAIOriginalModule0497

/-! Original module: OAI.NumberTheory.DirichletL.IdealEuler
Source SHA256: 6d266b5758b5e34be713d67cdaccbfdb9686899f20f22e75ad1fe574eb785825
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0498



namespace OAI

namespace SevenEighths.IdealEuler

open ActualEisensteinCubic UniqueFactorizationMonoid
open CompletedGauss (MulFiber mulFiber_moebius_sum)
open SmoothMobiusCorrection (PrimeIdeal)
open scoped BigOperators Classical

noncomputable section

def normWeight (s : ℂ) : Ideal O →*₀ ℂ where
  toFun := CubicEisenstein.fullIdealWeight s
  map_zero' := by simp [CubicEisenstein.fullIdealWeight]
  map_one' := by simp [CubicEisenstein.fullIdealWeight]
  map_mul' I J := by
    by_cases hI : I = 0
    · simp [CubicEisenstein.fullIdealWeight, hI]
    by_cases hJ : J = 0
    · simp [CubicEisenstein.fullIdealWeight, hJ]
    simp only [CubicEisenstein.fullIdealWeight, hI, hJ, mul_ne_zero hI hJ,
      ite_false, map_mul, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

def weighted (a : Ideal O →*₀ ℂ) (s : ℂ) : Ideal O →*₀ ℂ where
  toFun I := a I * normWeight s I
  map_zero' := by rw [map_zero, map_zero, zero_mul]
  map_one' := by rw [map_one, map_one, one_mul]
  map_mul' I J := by simp only [map_mul]; ring

def series (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := ∑' I : Ideal O, weighted a s I

def inverseSeries (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' I : Ideal O, (moebius I : ℂ) * weighted a s I

theorem weighted_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I : Ideal O => ‖weighted a s I‖) := by
  apply (CubicEisenstein.fullIdealWeight_summable_norm s hs).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem weighted_summable (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun I : Ideal O => weighted a s I) :=
  (weighted_summable_norm a ha s hs).of_norm

theorem inverse_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun I : Ideal O => ‖(moebius I : ℂ) * weighted a s I‖) := by
  apply (weighted_summable_norm a ha s hs).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one I)

theorem series_eq_LSeries (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = LSeries (ShortDraftHeckeBridge.normFiberCoeff a) s :=
  SmoothMobiusCorrection.idealDirichlet_eq_LSeries a ha s hs

theorem inverseSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s * series a s = 1 := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (moebius p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (inverse_summable_norm a ha s hs).mul_norm (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : MulFiber B, F p.1) = if B = 1 then 1 else 0 := by
    by_cases hB : B = 0
    · subst B
      have hz (p : MulFiber 0) : F p.1 = 0 := by simp only [F, p.2, map_zero, mul_zero]
      simp only [hz, tsum_zero, zero_ne_one, ite_false]
    · calc
        _ = (∑' p : MulFiber B, (moebius p.1.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.2])
        _ = _ := by
          rw [mulFiber_moebius_sum B hB]
          split_ifs with hB1
          · subst B
            simp only [map_one, one_mul]
          · exact zero_mul _
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : MulFiber B, F p.1) (∑' p, F p) at hsum
  simp_rw [hfiber] at hsum
  have hFone : (∑' p, F p) = 1 := by simpa using hsum.tsum_eq.symm
  calc
    _ = ∑' p : Ideal O × Ideal O, ((moebius p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (inverse_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = 1 := hFone

theorem series_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : series a s ≠ 0 := by
  intro hz
  have h := inverseSeries_mul_series a ha s hs
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem inverseSeries_eq_inv (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : inverseSeries a s = (series a s)⁻¹ := by
  calc
    _ = (inverseSeries a s * series a s) * (series a s)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ (series_ne_zero a ha s hs), mul_one]
    _ = _ := by rw [inverseSeries_mul_series a ha s hs, one_mul]

theorem primeValueHom_eq (f : Ideal O →*₀ ℂ) : CanonicalRowCompletion.primeValueHom f = f := by
  ext I
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
  · change (if I = 0 then 0 else ((normalizedFactors I).map f).prod) = f I
    simp only [hI, ite_false]
    rw [← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]

theorem prime_summable_norm (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Summable (fun P : PrimeIdeal => ‖weighted a s P.val‖) :=
  (weighted_summable_norm a ha s hs).comp_injective Subtype.val_injective

theorem prime_norm_lt_one (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : ‖weighted a s P.val‖ < 1 := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ < 1
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ < 1
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (ha P.val)).trans_lt
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by have h := SmoothMobiusCorrection.prime_norm_two_le P
        exact_mod_cast (by omega : 1 < Ideal.absNorm P.val)) (by simpa using neg_neg_of_pos hs)

theorem local_factor_ne_zero (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 0 < s.re) (P : PrimeIdeal) : 1 - weighted a s P.val ≠ 0 :=
  SmoothMobiusCorrection.one_sub_ne_zero (prime_norm_lt_one a ha s hs P)

theorem inverseSeries_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    inverseSeries a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val) := by
  have h := SmoothMobiusCorrection.mobiusPrimeCoeff_euler (weighted a s)
    (prime_summable_norm a ha s hs)
  simpa only [SmoothMobiusCorrection.mobiusPrimeCoeff, primeValueHom_eq, inverseSeries] using h

theorem euler_hasProd (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹) (series a s) := by
  have hm : Multipliable (fun P : PrimeIdeal => 1 - weighted a s P.val) := by
    simpa only [sub_eq_add_neg] using multipliable_one_add_of_summable
      (show Summable (fun P : PrimeIdeal => ‖-weighted a s P.val‖) by
        simpa only [norm_neg] using prime_summable_norm a ha s hs)
  have heq : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) = (series a s)⁻¹ :=
    (inverseSeries_euler a ha s hs).symm.trans (inverseSeries_eq_inv a ha s hs)
  have hne : (∏' P : PrimeIdeal, (1 - weighted a s P.val)) ≠ 0 := by
    rw [heq]
    exact inv_ne_zero (series_ne_zero a ha s hs)
  simpa only [heq, inv_inv] using hm.hasProd.inv₀ hne

theorem series_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = ∏' P : PrimeIdeal, (1 - weighted a s P.val)⁻¹ :=
  (euler_hasProd a ha s hs).tprod_eq.symm

def deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) : Ideal O →*₀ ℂ :=
  CanonicalRowCompletion.primeValueHom
    (fun I => if I ∈ S.image Subtype.val then 0 else a I)

theorem deletePrimes_prime (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    deletePrimes S a P.val = if P ∈ S then 0 else a P.val := by
  have hmem : P.val ∈ S.image Subtype.val ↔ P ∈ S := by
    constructor
    · intro hP
      obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP
      exact (Subtype.ext hQP : Q = P) ▸ hQ
    · intro hP
      exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
  change CanonicalRowCompletion.primeValueHom _ P.val = _
  rw [CanonicalRowCompletion.primeValueHom_prime _ _ P.property]
  simp only [hmem]

theorem deletePrimes_norm_le_one (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) : ∀ I, ‖deletePrimes S a I‖ ≤ 1 := by
  apply CanonicalRowCompletion.primeValueHom_norm_le_one
  intro I
  split_ifs
  · simp only [norm_zero, zero_le_one]
  · exact ha I

theorem deletePrimes_apply (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes S a I = if ∀ P ∈ S, ¬P.val ∣ I then a I else 0 := by
  by_cases ho : ∀ P ∈ S, ¬P.val ∣ I
  · rw [ite_eq_left ho]
    by_cases hI : I = 0
    · subst I
      rw [map_zero, map_zero]
    · change (if I = 0 then 0 else
        ((normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J)).prod) = a I
      simp only [hI, ite_false]
      have hmap : (normalizedFactors I).map (fun J => if J ∈ S.image Subtype.val then 0 else a J) =
          (normalizedFactors I).map a := by
        apply Multiset.map_congr rfl
        intro J hJ
        have hnot : J ∉ S.image Subtype.val := by
          intro hmem
          obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hmem
          exact ho P hP (dvd_of_mem_normalizedFactors hJ)
        simp only [hnot, ite_false]
      rw [hmap, ← map_multiset_prod, prod_normalizedFactors_eq hI, normalize_eq]
  · simp only [ho, ite_false]
    push Not at ho
    obtain ⟨P, hPS, J, hJ⟩ := ho
    rw [hJ, map_mul, deletePrimes_prime]
    simp only [hPS, ite_true, zero_mul]

theorem deletePrimes_primeSet_apply (M : Ideal O) (hM : M ≠ 0)
    (a : Ideal O →*₀ ℂ) (I : Ideal O) :
    deletePrimes (SmoothMobiusCorrection.primeSet M) a I =
      if IsCoprime I M then a I else 0 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
    exact (ite_self _).symm
  have heq : (∀ P ∈ SmoothMobiusCorrection.primeSet M, ¬P.val ∣ I) ↔ IsCoprime I M := by
    rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff hI hM]
    constructor
    · intro h
      apply Finset.disjoint_left.mpr
      intro P hPI hPM
      have hp : Prime P := IdealMobiusDivisorSum.support_prime hPM
      exact h ⟨P, hp⟩ (SmoothMobiusCorrection.mem_primeSet M ⟨P, hp⟩ |>.mpr hPM)
        (dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPI))
    · intro h P hPM hPI
      exact Finset.disjoint_left.mp h
        (Multiset.mem_toFinset.mpr ((mem_normalizedFactors_iff hI).mpr ⟨P.property, hPI⟩))
        ((SmoothMobiusCorrection.mem_primeSet M P).mp hPM)
  simpa only [heq] using deletePrimes_apply (SmoothMobiusCorrection.primeSet M) a I

theorem series_deletePrimes (S : Finset PrimeIdeal) (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    series (deletePrimes S a) s =
      series a s * ∏ P ∈ S, (1 - weighted a s P.val) := by
  have hlocal (P : PrimeIdeal) :
      (1 - weighted (deletePrimes S a) s P.val)⁻¹ =
        (1 - weighted a s P.val)⁻¹ * (if P ∈ S then 1 - weighted a s P.val else 1) := by
    change (1 - deletePrimes S a P.val * normWeight s P.val)⁻¹ = _
    rw [deletePrimes_prime]
    by_cases hP : P ∈ S
    · simp only [hP, ite_true, zero_mul, sub_zero, inv_one]
      exact (inv_mul_cancel₀ (local_factor_ne_zero a ha s (by linarith) P)).symm
    · simp only [hP, ite_false, mul_one]
      rfl
  have hfinite : Multipliable (fun P : PrimeIdeal => if P ∈ S then 1 - weighted a s P.val else 1) := by
    apply multipliable_of_hasFiniteMulSupport
    apply S.finite_toSet.subset
    intro P hP
    by_contra hPS
    change P ∉ S at hPS
    exact hP (by simp only [hPS, ite_false])
  rw [series_euler _ (deletePrimes_norm_le_one S a ha) s hs,
    series_euler a ha s hs]
  simp_rw [hlocal]
  rw [(euler_hasProd a ha s hs).multipliable.tprod_mul hfinite]
  congr 1
  rw [tprod_eq_prod (s := S) (fun P hP => by simp only [hP, ite_false])]
  exact Finset.prod_congr rfl (fun P hP => by simp only [hP, ite_true])

theorem series_of_coprime_mask (M : Ideal O) (hM : M ≠ 0)
    (a b : Ideal O →*₀ ℂ) (hb : ∀ I, ‖b I‖ ≤ 1)
    (hmask : ∀ I, a I = if IsCoprime I M then b I else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series a s = series b s *
      ∏ P ∈ SmoothMobiusCorrection.primeSet M, (1 - weighted b s P.val) := by
  have heq : a = deletePrimes (SmoothMobiusCorrection.primeSet M) b := by
    ext I
    rw [deletePrimes_primeSet_apply M hM, hmask]
  rw [heq]
  exact series_deletePrimes _ b hb s hs

theorem series_ofResidue_source_mask (M K : Ideal O) (hM : M ≠ 0)
    [Finite (O ⧸ K)] (χ : MulChar (O ⧸ M) ℂ) (φ : MulChar (O ⧸ K) ℂ)
    (hχ : IdealCharacter.UnitInvariant M χ) (hφ : IdealCharacter.UnitInvariant K φ)
    (hmask : ∀ x : O, χ (Ideal.Quotient.mk M x) =
      if IsUnit (Ideal.Quotient.mk M x) then φ (Ideal.Quotient.mk K x) else 0)
    (s : ℂ) (hs : 1 < s.re) :
    series (IdealCharacter.ofResidue M χ hχ) s =
      series (IdealCharacter.ofResidue K φ hφ) s *
        ∏ P ∈ SmoothMobiusCorrection.primeSet M,
          (1 - weighted (IdealCharacter.ofResidue K φ hφ) s P.val) :=
  series_of_coprime_mask M hM _ _ (IdealCharacter.norm_ofResidue_le_one K φ hφ)
    (IdealCharacter.ofResidue_source_mask M K χ φ hχ hφ hmask) s hs

theorem exists_primitive_series_associate (M : Ideal O) (hM : M ≠ 0)
    [Finite (O ⧸ M)] (χ : MulChar (O ⧸ M) ℂ) (hχ : IdealCharacter.UnitInvariant M χ) :
    ∃ (K : Ideal O) (φ : MulChar (O ⧸ K) ℂ) (hφ : IdealCharacter.UnitInvariant K φ),
      M ≤ K ∧ K ≠ ⊥ ∧ FiniteFourier.IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ (s : ℂ), 1 < s.re →
        series (IdealCharacter.ofResidue M χ hχ) s =
          series (IdealCharacter.ofResidue K φ hφ) s *
            ∏ P ∈ SmoothMobiusCorrection.primeSet M,
              (1 - weighted (IdealCharacter.ofResidue K φ hφ) s P.val) := by
  obtain ⟨K, φ, hφ, hMK, hK, hp, hn, hmask, _⟩ :=
    IdealCharacter.exists_primitive_associate M χ hχ
  let : Finite (O ⧸ K) := Finite.of_surjective _ (Ideal.Quotient.factor_surjective hMK)
  refine ⟨K, φ, hφ, hMK, hK, hp, hn, ?_⟩
  intro s hs
  exact series_of_coprime_mask M hM _ _
    (IdealCharacter.norm_ofResidue_le_one K φ hφ) hmask s hs

end

end SevenEighths.IdealEuler

end OAI
end OAIOriginalModule0498

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Boundary
Source SHA256: 10cf42c76993a667b631241e70e3105681331d83a466beb9cdb069392d623fc6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0499



namespace OAI

namespace SevenEighths.HeckeBoundary

open ActualEisensteinCubic Complex
open SevenEighths.IdealEuler SevenEighths.IdealCharacter
open SmoothMobiusCorrection (PrimeIdeal)
open Asymptotics Filter
open scoped BigOperators Classical Topology

noncomputable section

theorem re_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

theorem re_log_cpow_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x)
    (y : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - (n : ℂ) ^ (-x : ℂ))).re +
      4 * (-log (1 - z * (n : ℂ) ^ (-(x + I * y)))).re +
      (-log (1 - z ^ 2 * (n : ℂ) ^ (-(x + 2 * I * y)))).re := by
  have hn' : (n : ℝ) ^ (-x) < 1 := by
    rw [Real.rpow_neg (Nat.cast_nonneg n), inv_lt_one_iff₀]
    exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
  have hz' : ‖z * (n : ℂ) ^ (-(I * y))‖ = 1 := by
    rw [norm_mul, hz, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (by omega : (0 : ℕ) < n))]
    simp
  convert! re_log_comb_nonneg (by positivity) hn' hz' using 6
  · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
  · congr 2
    rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, mul_left_comm]
  · rw [neg_add, cpow_add _ _ <| mod_cast by omega, ← ofReal_neg,
      ofReal_cpow n.cast_nonneg (-x), ofReal_natCast,
      show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow,
      mul_left_comm]

theorem summable_neg_log_euler (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun P : PrimeIdeal => -log (1 - weighted a s P.val)) :=
  (prime_summable_norm a ha s hs).of_norm.clog_one_sub.neg

theorem exp_log_euler_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val)) = series a s := by
  have hp : HasProd (fun P : PrimeIdeal => (1 - weighted a s P.val)⁻¹)
      (exp (∑' P : PrimeIdeal, -log (1 - weighted a s P.val))) :=
    (summable_neg_log_euler a ha s hs).hasSum.cexp.congr
      (fun S => Finset.prod_congr rfl (fun P _ => by
        simp only [Function.comp_apply]
        rw [exp_neg, exp_log (local_factor_ne_zero a ha s (by linarith) P)]))
  exact hp.unique (euler_hasProd a ha s hs)

def PrimeTriple (a₀ a₁ a₂ : Ideal O →*₀ ℂ) : Prop :=
  ∀ P : PrimeIdeal,
    (a₀ P.val = 0 ∧ a₁ P.val = 0 ∧ a₂ P.val = 0) ∨
    (a₀ P.val = 1 ∧ ‖a₁ P.val‖ = 1 ∧ a₂ P.val = a₁ P.val ^ 2)

theorem re_log_weighted_comb_nonneg (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) (P : PrimeIdeal) :
    0 ≤ 3 * (-log (1 - weighted a₀ (x : ℂ) P.val)).re +
      4 * (-log (1 - weighted a₁ (x + I * y) P.val)).re +
      (-log (1 - weighted a₂ (x + 2 * I * y) P.val)).re := by
  change 0 ≤ 3 * (-log (1 - a₀ P.val * normWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * normWeight (x + I * y) P.val)).re +
      (-log (1 - a₂ P.val * normWeight (x + 2 * I * y) P.val)).re
  rcases h P with ⟨h₀, h₁, h₂⟩ | ⟨h₀, h₁, h₂⟩
  · simp only [h₀, h₁, h₂, zero_mul, sub_zero, log_one, neg_zero, zero_re,
      mul_zero, add_zero, le_refl]
  · simp only [h₀, h₂, one_mul]
    change 0 ≤ 3 * (-log (1 - CubicEisenstein.fullIdealWeight (x : ℂ) P.val)).re +
      4 * (-log (1 - a₁ P.val * CubicEisenstein.fullIdealWeight (x + I * y) P.val)).re +
      (-log (1 - a₁ P.val ^ 2 * CubicEisenstein.fullIdealWeight (x + 2 * I * y) P.val)).re
    simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false]
    exact re_log_cpow_comb_nonneg (SmoothMobiusCorrection.prime_norm_two_le P) hx y h₁

theorem norm_series_product_ge_one (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series a₀ (x : ℂ) ^ 3 * series a₁ (x + I * y) ^ 4 *
      series a₂ (x + 2 * I * y)‖ := by
  have hs₀ : 1 < (x : ℂ).re := hx
  have hs₁ : 1 < (x + I * y : ℂ).re := by simpa using hx
  have hs₂ : 1 < (x + 2 * I * y : ℂ).re := by simpa using hx
  have H₀ := summable_neg_log_euler a₀ ha₀ _ hs₀
  have H₁ := summable_neg_log_euler a₁ ha₁ _ hs₁
  have H₂ := summable_neg_log_euler a₂ ha₂ _ hs₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← exp_log_euler_eq_series a₀ ha₀ _ hs₀,
    ← exp_log_euler_eq_series a₁ ha₁ _ hs₁, ← exp_log_euler_eq_series a₂ ha₂ _ hs₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  exact tsum_nonneg fun P => re_log_weighted_comb_nonneg a₀ a₁ a₂ h hx y P

theorem square_unitInvariant (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) : UnitInvariant M (χ ^ 2) := by
  intro u
  rw [χ.pow_apply' two_ne_zero, hχ u, one_pow]

theorem ofResidue_primeTriple (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) :
    PrimeTriple (ofResidue M 1 (one_unitInvariant M))
      (ofResidue M χ hχ) (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) := by
  intro P
  let q := Ideal.Quotient.mk M (Submodule.IsPrincipal.generator P.val)
  have hv (ψ : MulChar (O ⧸ M) ℂ) (hψ : UnitInvariant M ψ) :
      ofResidue M ψ hψ P.val = ψ q := by
    change value M ψ P.val = _
    have hP : P.val ≠ ⊥ := P.property.ne_zero
    simp only [value, hP, ite_false, q]
  rw [hv, hv, hv]
  by_cases hq : IsUnit q
  · right
    refine ⟨MulChar.one_apply hq, ?_, χ.pow_apply' two_ne_zero q⟩
    let : Fintype (O ⧸ M)ˣ := Fintype.ofFinite _
    obtain ⟨u, hu⟩ := hq
    rw [← hu]
    have hn := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    simpa only [MulChar.coe_equivToUnitHom] using hn
  · left
    exact ⟨MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq, MulChar.map_nonunit _ hq⟩

theorem norm_residue_series_product_ge_one (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖series (ofResidue M 1 (one_unitInvariant M)) (x : ℂ) ^ 3 *
      series (ofResidue M χ hχ) (x + I * y) ^ 4 *
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) (x + 2 * I * y)‖ :=
  norm_series_product_ge_one _ _ _
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ) hx y

theorem horizontal_isBigO_of_zero (F : ℂ → ℂ) (t : ℝ)
    (hF : DifferentiableAt ℂ F (1 + I * t)) (hz : F (1 + I * t) = 0) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun x : ℝ => (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have h := hF.hasDerivAt
  rw [← zero_add (1 + _)] at h
  simpa only [zero_add, hz, sub_zero]
    using (Complex.isBigO_comp_ofReal_nhds
      (h.comp_add_const 0 _).differentiableAt.isBigO_sub) |>.mono nhdsWithin_le_nhds

theorem horizontal_isBigO_one (F : ℂ → ℂ) (t : ℝ)
    (hF : ContinuousAt F (1 + I * t)) :
    (fun x : ℝ => F (1 + x + I * t)) =O[𝓝[>] 0] fun _ => (1 : ℂ) := by
  refine IsBigO.mono ?_ nhdsWithin_le_nhds
  simp_rw [add_comm (1 : ℂ), add_assoc]
  rw [← zero_add (1 + _)] at hF
  exact hF.comp (f := fun x : ℝ => x + (1 + I * t)) (x := 0) (by fun_prop)
    |>.tendsto.isBigO_one ℂ

theorem boundary_ne_zero_of_series_eq (a₀ a₁ a₂ : Ideal O →*₀ ℂ)
    (ha₀ : ∀ I, ‖a₀ I‖ ≤ 1) (ha₁ : ∀ I, ‖a₁ I‖ ≤ 1) (ha₂ : ∀ I, ‖a₂ I‖ ≤ 1)
    (h : PrimeTriple a₀ a₁ a₂) (F₀ F₁ F₂ : ℂ → ℂ)
    (hEq₀ : ∀ s : ℂ, 1 < s.re → F₀ s = series a₀ s)
    (hEq₁ : ∀ s : ℂ, 1 < s.re → F₁ s = series a₁ s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → F₂ s = series a₂ s)
    (t : ℝ)
    (hPole : (fun x : ℝ => F₀ (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x)
    (hReg₁ : DifferentiableAt ℂ F₁ (1 + I * t))
    (hReg₂ : ContinuousAt F₂ (1 + 2 * I * t)) : F₁ (1 + I * t) ≠ 0 := by
  intro hz
  have hLower (x : ℝ) (hx : 0 < x) :
      1 ≤ ‖F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t)‖ := by
    have hs₀ : 1 < (1 + x : ℂ).re := by simp; exact hx
    have hs₁ : 1 < (1 + x + I * t : ℂ).re := by simpa using hs₀
    have hs₂ : 1 < (1 + x + 2 * I * t : ℂ).re := by simpa using hs₀
    rw [hEq₀ _ hs₀, hEq₁ _ hs₁, hEq₂ _ hs₂]
    simpa only [ofReal_add, ofReal_one] using
      norm_series_product_ge_one a₀ a₁ a₂ ha₀ ha₁ ha₂ h (by linarith : 1 < 1 + x) t
  have hReg₂' : ContinuousAt F₂ (1 + I * ((2 * t : ℝ) : ℂ)) := by
    convert hReg₂ using 1
    push_cast
    ring
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [ofReal_zero, zero_pow (by decide), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr hx), one_mul, mul_one]
  have H₀ : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0]
      fun x => F₀ (1 + x) ^ 3 * F₁ (1 + x + I * t) ^ 4 * F₂ (1 + x + 2 * I * t) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun x hx => (norm_one (α := ℝ)).symm ▸ (hLower x hx)
  have H := (hPole.pow 3).mul ((horizontal_isBigO_of_zero F₁ t hReg₁ hz).pow 4)
    |>.mul (horizontal_isBigO_one F₂ (2 * t) hReg₂')
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

section Quadratic

open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open UniqueFactorizationMonoid
open scoped ComplexOrder

def zetaConvolutionCoeff (a : Ideal O →*₀ ℂ) (B : Ideal O) : ℂ :=
  if B = 0 then 0 else ∑ D ∈ idealDivisors B, a D

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

@[simp] theorem zetaConvolutionCoeff_one (a : Ideal O →*₀ ℂ) :
    zetaConvolutionCoeff a 1 = 1 := by
  rw [zetaConvolutionCoeff, ite_eq_right one_ne_zero, idealDivisors_one, Finset.sum_singleton]
  exact map_one a

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem zetaConvolutionCoeff_prime_pow (a : Ideal O →*₀ ℂ) (P : Ideal O)
    (hP : Prime P) (k : ℕ) :
    zetaConvolutionCoeff a (P ^ k) = ∑ j ∈ Finset.range (k + 1), a P ^ j := by
  rw [zetaConvolutionCoeff, ite_eq_right (pow_ne_zero k hP.ne_zero), idealDivisors_prime_pow P hP k,
    Finset.sum_image]
  · simp only [map_pow]
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_isUnit hP.ne_zero hij

theorem zetaConvolutionCoeff_mul (a : Ideal O →*₀ ℂ) (B C : Ideal O)
    (hB : B ≠ 0) (hC : C ≠ 0) (hBC : IsRelPrime B C) :
    zetaConvolutionCoeff a (B * C) = zetaConvolutionCoeff a B * zetaConvolutionCoeff a C := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  simp only [zetaConvolutionCoeff, hB, hC, mul_ne_zero hB hC, ite_false]
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  simp only [map_mul, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem zetaConvolutionCoeff_nonneg (a : Ideal O →*₀ ℂ)
    (ha : ∀ P : Ideal O, Prime P → a P = 0 ∨ a P = 1 ∨ a P = -1)
    (B : Ideal O) : 0 ≤ zetaConvolutionCoeff a B := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => simp [zetaConvolutionCoeff]
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, zetaConvolutionCoeff_one]
    exact zero_le_one
  | hpr k hP =>
    rw [zetaConvolutionCoeff_prime_pow a _ hP k]
    rcases ha _ hP with hz | ho | hm
    · exact Finset.sum_nonneg (fun j _ => by rw [hz]; exact pow_nonneg (le_refl 0) j)
    · exact Finset.sum_nonneg (fun j _ => by rw [ho, one_pow]; exact zero_le_one)
    · rw [hm, neg_one_geom_sum]
      split_ifs <;> first | exact le_refl 0 | exact zero_le_one
  | @hcp B C hBC hB hC =>
    by_cases hB0 : B = 0
    · simp [hB0, zetaConvolutionCoeff]
    by_cases hC0 : C = 0
    · simp [hC0, zetaConvolutionCoeff]
    rw [zetaConvolutionCoeff_mul a B C hB0 hC0 hBC]
    exact mul_nonneg hB hC

theorem quadratic_normFiber_nonneg (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ)
    (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ ShortDraftHeckeBridge.normFiberCoeff
      (zetaConvolutionCoeff (ofResidue M χ hχ)) n := by
  apply Finset.sum_nonneg
  intro B _
  apply zetaConvolutionCoeff_nonneg
  intro P hP
  change value M χ P = 0 ∨ value M χ P = 1 ∨ value M χ P = -1
  have hP0 : P ≠ ⊥ := hP.ne_zero
  simp only [value, hP0, ite_false]
  exact MulChar.isQuadratic_iff_sq_eq_one.mpr hquad _

theorem mulFiber_character_sum (a : Ideal O →*₀ ℂ) (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : CompletedGauss.MulFiber B, a p.val.1) = zetaConvolutionCoeff a B := by
  let e := CompletedGauss.mulFiberDivisorEquiv B hB
  rw [zetaConvolutionCoeff, ite_eq_right hB]
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, a D.val :=
      e.tsum_eq (fun D => a D.val)
    _ = _ := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl) a).symm

theorem zetaConvolution_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => zetaConvolutionCoeff a B * normWeight s B)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  let F : Ideal O × Ideal O → ℂ := fun p => a p.1 * normWeight s (p.1 * p.2)
  have hprod := (weighted_summable_norm a ha s hs).mul_norm
    (CubicEisenstein.fullIdealWeight_summable_norm s hs)
  have heq (p : Ideal O × Ideal O) :
      weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 = F p := by
    change (a p.1 * normWeight s p.1) * normWeight s p.2 = _
    simp only [F, map_mul, mul_assoc]
  have hF : Summable F := hprod.of_norm.congr heq
  have hfiber (B : Ideal O) : (∑' p : CompletedGauss.MulFiber B, F p.val) =
      zetaConvolutionCoeff a B * normWeight s B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : CompletedGauss.MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : CompletedGauss.MulFiber B, a p.val.1) * normWeight s B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_character_sum a B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : CompletedGauss.MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  convert hsum using 1
  calc
    _ = ∑' p : Ideal O × Ideal O,
        weighted a s p.1 * CubicEisenstein.fullIdealWeight s p.2 :=
      tsum_mul_tsum_of_summable_norm (weighted_summable_norm a ha s hs)
        (CubicEisenstein.fullIdealWeight_summable_norm s hs)
    _ = _ := tsum_congr heq

theorem zetaConvolution_normFiber_one (a : Ideal O →*₀ ℂ) :
    ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a) 1 = 1 := by
  have hsingle : (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {1} := by
    ext I
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_singleton]
    exact Ideal.absNorm_eq_one_iff.trans (by rw [Ideal.one_eq_top])
  unfold ShortDraftHeckeBridge.normFiberCoeff
  rw [hsingle, Finset.sum_singleton, zetaConvolutionCoeff_one]

theorem zetaConvolution_LSeries_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (LSeries.term (ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a)) s)
      (series a s * CubicEisenstein.fullIdealZeta s) := by
  have h := (zetaConvolution_hasSum a ha s hs).tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' I : {I : Ideal O // Ideal.absNorm I = n},
    zetaConvolutionCoeff a I.val * CubicEisenstein.fullIdealWeight s I.val) _ at h
  simpa only [SmoothMobiusCorrection.idealDirichlet_fiber] using h

theorem zetaConvolution_LSeries_eq (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (ShortDraftHeckeBridge.normFiberCoeff (zetaConvolutionCoeff a)) s =
      series a s * CubicEisenstein.fullIdealZeta s :=
  (zetaConvolution_LSeries_hasSum a ha s hs).tsum_eq

theorem quadratic_product_positive (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hEq : ∀ s : ℂ, 1 < s.re →
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s) (y : ℝ) :
    0 < F y := by
  refine LSeries.positive_of_differentiable_of_eqOn
    (quadratic_normFiber_nonneg M χ hχ hquad)
    (zetaConvolution_normFiber_one (ofResidue M χ hχ) ▸ zero_lt_one) hF
    (x := 1) ?_ ?_ y
  · exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun s hs => (zetaConvolution_LSeries_hasSum (ofResidue M χ hχ)
        (norm_ofResidue_le_one M χ hχ) s hs).summable)
  · intro s hs
    rw [hEq s hs, zetaConvolution_LSeries_eq (ofResidue M χ hχ)
      (norm_ofResidue_le_one M χ hχ) s hs]

theorem fullIdealZeta_eq_dirichlet_product (s : ℂ) (hs : 1 < s.re) :
    CubicEisenstein.fullIdealZeta s = riemannZeta s *
      (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s := by
  let a := normWeight 0
  have ha (I : Ideal O) : ‖a I‖ ≤ 1 := by
    by_cases hI : I = ⊥ <;> simp [a, normWeight, CubicEisenstein.fullIdealWeight, hI]
  have hchar (n : ℕ) : (1 : DirichletCharacter ℂ 1) n = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  have hseries : series a s = CubicEisenstein.fullIdealZeta s := by
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;>
      simp [weighted, a, normWeight, CubicEisenstein.fullIdealWeight, hI]
  have hinverse : inverseSeries a s =
      LSeries (ShortDraftHeckeBridge.pairInverseCoeff (1 : DirichletCharacter ℂ 1)
        (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1))) s := by
    rw [← ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse
      (1 : DirichletCharacter ℂ 1) (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1))
      (ShortDraftHeckeBridge.baseChangeWeight (1 : DirichletCharacter ℂ 1))
      (ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff (1 : DirichletCharacter ℂ 1)) s]
    rw [← SmoothMobiusCorrection.idealDirichlet_eq_LSeries
      (ShortDraftHeckeBridge.baseChangeWeight (1 : DirichletCharacter ℂ 1))
      (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one (1 : DirichletCharacter ℂ 1)) s hs]
    apply tsum_congr
    intro I
    by_cases hI : I = ⊥ <;>
      simp [weighted, a, normWeight, CubicEisenstein.fullIdealWeight,
        ShortDraftHeckeBridge.baseChangeWeight, hI, hchar]
  have hi := inverseSeries_mul_series a ha s hs
  have hp := ShortDraftHeckeBridge.pair_inverse_euler_identity
    (1 : DirichletCharacter ℂ 1) (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)) s hs
  rw [← hinverse, DirichletCharacter.LFunction_modOne_eq] at hp
  rw [← hseries]
  calc
    series a s = 1 * series a s := (one_mul _).symm
    _ = ((riemannZeta s *
        (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s) *
          inverseSeries a s) * series a s := by rw [hp]
    _ = _ := by rw [mul_assoc, hi, mul_one]

def regularizedIdealZeta (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ 1 s *
    (ShortDraftHeckeBridge.baseChangeChar (1 : DirichletCharacter ℂ 1)).LFunction s

theorem regularizedIdealZeta_differentiable : Differentiable ℂ regularizedIdealZeta :=
  (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).mul
    (DirichletCharacter.differentiable_LFunction
      (ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one
        (1 : DirichletCharacter ℂ 1) rfl))

theorem regularizedIdealZeta_eq (s : ℂ) (hs : 1 < s.re) :
    regularizedIdealZeta s = (s - 1) * CubicEisenstein.fullIdealZeta s := by
  have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
  rw [regularizedIdealZeta, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne hs1, DirichletCharacter.LFunctionTrivChar,
    DirichletCharacter.LFunction_modOne_eq, fullIdealZeta_eq_dirichlet_product s hs,
    mul_assoc]

theorem regularizedIdealZeta_neg_two : regularizedIdealZeta (-2 : ℝ) = 0 := by
  have hz := riemannZeta_neg_two_mul_nat_add_one 0
  rw [Nat.cast_zero, zero_add, mul_one] at hz
  rw [regularizedIdealZeta, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne (by norm_num : (-2 : ℝ) ≠ (1 : ℂ)),
    DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq]
  simp only [ofReal_neg, ofReal_ofNat, hz, mul_zero, zero_mul]

theorem differentiable_dslope_of_entire (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) :
    Differentiable ℂ (dslope F c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 c)).mpr
    hF.differentiableOn

theorem quadratic_one_ne_zero_of_regularized_zeta (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L R : ℂ → ℂ) (hL : Differentiable ℂ L) (hR : Differentiable ℂ R)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hReq : ∀ s : ℂ, 1 < s.re → R s = (s - 1) * CubicEisenstein.fullIdealZeta s)
    (y : ℝ) (hRy : R y = 0) : L 1 ≠ 0 := by
  intro hz
  let F : ℂ → ℂ := fun s => R s * dslope L 1 s
  have hF : Differentiable ℂ F := hR.mul (differentiable_dslope_of_entire L hL 1)
  have hEq (s : ℂ) (hs : 1 < s.re) :
      F s = series (ofResidue M χ hχ) s * CubicEisenstein.fullIdealZeta s := by
    have hs1 : s ≠ 1 := by intro he; simp only [he, one_re, lt_self_iff_false] at hs
    dsimp only [F]
    rw [hReq s hs, dslope_of_ne L hs1, slope, smul_eq_mul, vsub_eq_sub, hz, sub_zero,
      hLeq s hs]
    field_simp
  have hpos := quadratic_product_positive M χ hχ hquad F hF hEq y
  have hzero : F y = 0 := by simp only [F, hRy, zero_mul]
  exact hzero.not_gt hpos

theorem quadratic_one_ne_zero_of_entire (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (hquad : χ ^ 2 = 1)
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLeq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) : L 1 ≠ 0 :=
  quadratic_one_ne_zero_of_regularized_zeta M χ hχ hquad L regularizedIdealZeta hL
    regularizedIdealZeta_differentiable hLeq regularizedIdealZeta_eq (-2)
    regularizedIdealZeta_neg_two

theorem normWeight_real_nonneg (x : ℝ) (B : Ideal O) : 0 ≤ normWeight (x : ℂ) B := by
  change 0 ≤ CubicEisenstein.fullIdealWeight (x : ℂ) B
  unfold CubicEisenstein.fullIdealWeight
  split_ifs
  · exact le_rfl
  · rw [← ofReal_natCast, ← ofReal_neg, ← ofReal_cpow (Nat.cast_nonneg _)]
    exact_mod_cast Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm B)) (-x)

theorem norm_series_le_norm_fullIdealZeta (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (x : ℝ) (hx : 1 < x) : ‖series a (x : ℂ)‖ ≤ ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ := by
  have hs : 1 < (x : ℂ).re := hx
  have hweight (I : Ideal O) :
      CubicEisenstein.fullIdealWeight (x : ℂ) I = (‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ : ℂ) :=
    eq_coe_norm_of_nonneg (normWeight_real_nonneg x I)
  have hnorm : ‖CubicEisenstein.fullIdealZeta (x : ℂ)‖ =
      ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight (x : ℂ) I‖ := by
    unfold CubicEisenstein.fullIdealZeta
    rw [tsum_congr hweight, ← ofReal_tsum,
      Complex.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
  rw [hnorm]
  refine (norm_tsum_le_tsum_norm (weighted_summable_norm a ha _ hs)).trans ?_
  apply Summable.tsum_le_tsum _ (weighted_summable_norm a ha _ hs)
    (CubicEisenstein.fullIdealWeight_summable_norm _ hs)
  intro I
  change ‖a I * CubicEisenstein.fullIdealWeight (x : ℂ) I‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha I)

theorem fullIdealZeta_isBigO_near_one_horizontal :
    (fun x : ℝ => CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun x => (1 : ℂ) / x := by
  have hR : (fun x : ℝ => regularizedIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := by
    simpa only [ofReal_zero, mul_zero, add_zero] using horizontal_isBigO_one
      regularizedIdealZeta 0 (by simpa using (regularizedIdealZeta_differentiable 1).continuousAt)
  have hB : (fun x : ℝ => (x : ℂ) * CubicEisenstein.fullIdealZeta (1 + x)) =O[𝓝[>] 0]
      fun _ => (1 : ℂ) := hR.congr'
    (eventually_nhdsWithin_of_forall (fun x hx => by
      dsimp only
      rw [regularizedIdealZeta_eq _ (by simpa using hx), add_sub_cancel_left]))
    (Filter.EventuallyEq.refl _ _)
  exact (isBigO_mul_iff_isBigO_div (eventually_nhdsWithin_of_forall
    (fun x hx => ofReal_ne_zero.mpr (ne_of_gt hx)))).mp hB

theorem series_isBigO_near_one_horizontal (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x := by
  have h : (fun x : ℝ => series a (1 + x)) =O[𝓝[>] 0]
      fun x => CubicEisenstein.fullIdealZeta (1 + x) := by
    apply IsBigO.of_bound'
    apply eventually_nhdsWithin_of_forall
    intro x hx
    change 0 < x at hx
    simpa only [ofReal_add, ofReal_one] using
      norm_series_le_norm_fullIdealZeta a ha (1 + x) (by linarith)
  exact h.trans fullIdealZeta_isBigO_near_one_horizontal

theorem residue_boundary_ne_zero_of_series_eq (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L L₂ : ℂ → ℂ)
    (hEq : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s)
    (hEq₂ : ∀ s : ℂ, 1 < s.re → L₂ s =
      series (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ)) s)
    (t : ℝ) (hL : DifferentiableAt ℂ L (1 + I * t))
    (hL₂ : ContinuousAt L₂ (1 + 2 * I * t)) : L (1 + I * t) ≠ 0 :=
  boundary_ne_zero_of_series_eq
    (ofResidue M 1 (one_unitInvariant M)) (ofResidue M χ hχ)
    (ofResidue M (χ ^ 2) (square_unitInvariant M χ hχ))
    (norm_ofResidue_le_one M 1 (one_unitInvariant M))
    (norm_ofResidue_le_one M χ hχ)
    (norm_ofResidue_le_one M (χ ^ 2) (square_unitInvariant M χ hχ))
    (ofResidue_primeTriple M χ hχ)
    (series (ofResidue M 1 (one_unitInvariant M))) L L₂ (fun _ _ => rfl)
    hEq hEq₂ t
    (series_isBigO_near_one_horizontal _ (norm_ofResidue_le_one M 1 (one_unitInvariant M)))
    hL hL₂

end Quadratic

end

end SevenEighths.HeckeBoundary

end OAI
end OAIOriginalModule0499

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.EulerLog
Source SHA256: d113d222250a1a98c35416261b399b80577a20e2f2ca8ae1ce5897806e6371d9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0500





namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set Metric Filter Complex ActualEisensteinCubic
open SevenEighths.IdealEuler SevenEighths.IdealCharacter
open SmoothMobiusCorrection (PrimeIdeal)

namespace SevenEighths.HeckeEulerLog

def eulerLog (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ :=
  ∑' P : PrimeIdeal, -Complex.log (1 - weighted a s P.val)

def majorant (σ : ℝ) (P : PrimeIdeal) : ℝ :=
  (3 / 2) * (Ideal.absNorm P.val : ℝ) ^ (-σ)

theorem majorant_summable {σ : ℝ} (hσ : 1 < σ) : Summable (majorant σ) := by
  have h := (SmoothMobiusCorrection.prime_norm_series_summable (σ - 1)
    (by linarith)).mul_left (3 / 2)
  convert h using 1
  ext P
  unfold majorant
  congr 2
  ring

theorem weighted_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} {σ : ℝ} (hs : σ ≤ s.re) :
    ‖weighted a s P.val‖ ≤ (Ideal.absNorm P.val : ℝ) ^ (-σ) := by
  change ‖a P.val * CubicEisenstein.fullIdealWeight s P.val‖ ≤ _
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false, norm_mul]
  change ‖a P.val‖ * ‖SmoothMobiusCorrection.primeNormPower P s‖ ≤ _
  rw [SmoothMobiusCorrection.norm_primeNormPower]
  have hn : (1 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast (show 1 ≤ Ideal.absNorm P.val from
      (by have := SmoothMobiusCorrection.prime_norm_two_le P; omega))
  exact (mul_le_of_le_one_left (by positivity) (ha _)).trans
    (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))

theorem weighted_norm_le_half (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} (hs : 1 ≤ s.re) : ‖weighted a s P.val‖ ≤ 1 / 2 := by
  refine (weighted_norm_le a ha P hs).trans ?_
  rw [Real.rpow_neg_one]
  have hn : (2 : ℝ) ≤ Ideal.absNorm P.val := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  exact inv_le_of_inv_le₀ (by norm_num) (by norm_num at *; exact hn)

theorem log_factor_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) {s : ℂ} {σ : ℝ} (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖-Complex.log (1 - weighted a s P.val)‖ ≤ majorant σ P := by
  have hhalf := weighted_norm_le_half a ha P (hσ.trans hs)
  have h := Complex.norm_log_one_add_half_le_self
    (z := -weighted a s P.val) (by simpa using hhalf)
  simp only [norm_neg, ← sub_eq_add_neg] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_left (weighted_norm_le a ha P hs) (by norm_num))

theorem weighted_differentiable (a : Ideal O →*₀ ℂ) (P : PrimeIdeal) :
    Differentiable ℂ (fun s ↦ weighted a s P.val) := by
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_pos P).ne'
  change Differentiable ℂ (fun s ↦ a P.val * CubicEisenstein.fullIdealWeight s P.val)
  simp only [CubicEisenstein.fullIdealWeight, P.property.ne_zero, ite_false]
  exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem log_factor_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (P : PrimeIdeal) :
    DifferentiableOn ℂ (fun s ↦ -Complex.log (1 - weighted a s P.val)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hn := prime_norm_lt_one a ha s (by linarith : 0 < s.re) P
  have hslit : 1 - weighted a s P.val ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -weighted a s P.val) (by simpa using hn)
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub (weighted_differentiable a P s))).neg.differentiableWithinAt

theorem eulerLog_differentiableOn_halfplane (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < σ) : DifferentiableOn ℂ (eulerLog a) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (majorant_summable hσ)
  · intro P
    exact (log_factor_differentiableOn a ha P).mono (fun s hs ↦ hσ.trans hs)
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro P s hs
    exact log_factor_norm_le a ha P hσ.le hs.le

theorem eulerLog_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (eulerLog a) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hσ : 1 < (1 + s.re) / 2 := by linarith
  have hmem : s ∈ {w : ℂ | (1 + s.re) / 2 < w.re} := by dsimp; linarith
  exact ((eulerLog_differentiableOn_halfplane a ha hσ s hmem).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

theorem exp_eulerLog_eq_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : Complex.exp (eulerLog a s) = series a s :=
  SevenEighths.HeckeBoundary.exp_log_euler_eq_series a ha s hs

def eulerLogBound : ℝ := 1 + ∑' P : PrimeIdeal, majorant (3 / 2) P

theorem eulerLogBound_ge_one : 1 ≤ eulerLogBound := by
  unfold eulerLogBound
  have h : 0 ≤ ∑' P : PrimeIdeal, majorant (3 / 2) P :=
    tsum_nonneg (fun P ↦ by unfold majorant; positivity)
  linarith

theorem eulerLog_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖eulerLog a s‖ ≤ eulerLogBound := by
  have hb : ∀ P : PrimeIdeal, ‖-Complex.log (1 - weighted a s P.val)‖ ≤ majorant (3 / 2) P :=
    fun P ↦ log_factor_norm_le a ha P (by norm_num) hs
  have hsum := majorant_summable (by norm_num : (1 : ℝ) < 3 / 2)
  have hnorm : Summable (fun P : PrimeIdeal ↦ ‖-Complex.log (1 - weighted a s P.val)‖) :=
    hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hb
  calc
    ‖eulerLog a s‖ ≤ ∑' P : PrimeIdeal, ‖-Complex.log (1 - weighted a s P.val)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' P : PrimeIdeal, majorant (3 / 2) P := hnorm.tsum_le_tsum hb hsum
    _ ≤ eulerLogBound := by unfold eulerLogBound; linarith

theorem inner_disk_re {t : ℝ} {s : ℂ}
    (hs : s ∈ closedBall (2 + (t : ℂ) * Complex.I) (1 / 2)) : 3 / 2 ≤ s.re := by
  have hn : ‖(2 + (t : ℂ) * Complex.I) - s‖ ≤ 1 / 2 := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hs
  have hr := Complex.re_le_norm ((2 + (t : ℂ) * Complex.I) - s)
  norm_num at hr
  linarith

theorem eulerLog_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog a) (series a)
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog a s‖ ≤ eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(eulerLog_differentiableOn a ha).mono hsub, ?_, ?_⟩
  · intro s hs
    exact exp_eulerLog_eq_series a ha s (hsub hs)
  · intro s hs
    exact eulerLog_norm_le a ha (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

theorem continued_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (L : ℂ → ℂ) (hL : ∀ s : ℂ, 1 < s.re → L s = series a s) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog a) L (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog a s‖ ≤ eulerLogBound := by
  obtain ⟨hd, he, hb⟩ := eulerLog_inner_disk a ha t
  refine ⟨hd, ?_, hb⟩
  intro s hs
  have hr := inner_disk_re (ball_subset_closedBall hs)
  exact (he hs).trans (hL s (by linarith)).symm

def principalLog (s : ℂ) : ℂ := Complex.log (1 - 2 / (s + 1))

theorem norm_two_div_add_one_lt_one {s : ℂ} (hs : 1 < s.re) :
    ‖(2 : ℂ) / (s + 1)‖ < 1 := by
  have hr := Complex.re_le_norm (s + 1)
  norm_num at hr
  have hn : 0 < ‖s + 1‖ := by linarith
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_lt_one hn).mpr (by linarith)

theorem norm_two_div_add_one_le {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖(2 : ℂ) / (s + 1)‖ ≤ 4 / 5 := by
  have hr := Complex.re_le_norm (s + 1)
  norm_num at hr
  have hn : 0 < ‖s + 1‖ := by linarith
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_iff₀ hn).mpr (by linarith)

theorem principalLog_differentiableOn :
    DifferentiableOn ℂ principalLog {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hnorm := norm_two_div_add_one_lt_one hs
  have hslit : 1 - (2 : ℂ) / (s + 1) ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg, neg_div] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -(2 : ℂ) / (s + 1)) (by simpa using hnorm)
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub ((differentiableAt_const (2 : ℂ)).div
      (differentiableAt_id.add_const 1) hs1))).differentiableWithinAt

theorem exp_principalLog {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalLog s) = (s - 1) / (s + 1) := by
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [principalLog, Complex.exp_log (SmoothMobiusCorrection.one_sub_ne_zero
    (norm_two_div_add_one_lt_one hs))]
  field_simp
  ring

theorem principalLog_norm_le {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖principalLog s‖ ≤ 3 := by
  have hb := norm_two_div_add_one_le hs
  have hlt : ‖-(2 : ℂ) / (s + 1)‖ < 1 := by simpa using hb.trans_lt (by norm_num : (4 : ℝ) / 5 < 1)
  have h := Complex.norm_log_one_add_le hlt
  have hn : ‖-(2 : ℂ) / (s + 1)‖ = ‖(2 : ℂ) / (s + 1)‖ := by simp
  rw [hn] at h
  have heq : 1 + -(2 : ℂ) / (s + 1) = 1 - 2 / (s + 1) := by ring
  rw [heq] at h
  change ‖principalLog s‖ ≤ _ at h
  have hden : 0 < 1 - ‖(2 : ℂ) / (s + 1)‖ := by linarith
  have hinv : (1 - ‖(2 : ℂ) / (s + 1)‖)⁻¹ ≤ 5 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  have hnorm := norm_nonneg ((2 : ℂ) / (s + 1))
  have hsq : ‖(2 : ℂ) / (s + 1)‖ ^ 2 ≤ 16 / 25 := by nlinarith
  have hmul := mul_le_mul hsq hinv (inv_nonneg.mpr hden.le) (by norm_num : (0 : ℝ) ≤ 16 / 25)
  nlinarith

def principalEulerLog (a : Ideal O →*₀ ℂ) (s : ℂ) : ℂ := principalLog s + eulerLog a s

theorem principalEulerLog_differentiableOn (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) :
    DifferentiableOn ℂ (principalEulerLog a) {s : ℂ | 1 < s.re} :=
  principalLog_differentiableOn.add (eulerLog_differentiableOn a ha)

theorem exp_principalEulerLog (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (principalEulerLog a s) = ((s - 1) / (s + 1)) * series a s := by
  rw [principalEulerLog, Complex.exp_add, exp_principalLog hs, exp_eulerLog_eq_series a ha s hs]

theorem principalEulerLog_norm_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖principalEulerLog a s‖ ≤ 3 + eulerLogBound :=
  (norm_add_le _ _).trans (add_le_add (principalLog_norm_le hs) (eulerLog_norm_le a ha hs))

theorem principal_continued_inner_disk (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = ((s - 1) / (s + 1)) * series a s) (t : ℝ) :
    DifferentiableOn ℂ (principalEulerLog a) (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ principalEulerLog a) L
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖principalEulerLog a s‖ ≤ 3 + eulerLogBound := by
  have hsub : ball (2 + (t : ℂ) * Complex.I) (1 / 2) ⊆ {s : ℂ | 1 < s.re} := by
    intro s hs
    have := inner_disk_re (ball_subset_closedBall hs)
    change 1 < s.re
    linarith
  refine ⟨(principalEulerLog_differentiableOn a ha).mono hsub, ?_, ?_⟩
  · intro s hs
    exact (exp_principalEulerLog a ha (hsub hs)).trans (hL s (hsub hs)).symm
  · intro s hs
    exact principalEulerLog_norm_le a ha
      (inner_disk_re (closedBall_subset_closedBall (by norm_num) hs))

theorem residue_continued_inner_disk (M : Ideal O) [Finite (O ⧸ M)]
    (χ : MulChar (O ⧸ M) ℂ) (hχ : UnitInvariant M χ) (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = series (ofResidue M χ hχ) s) (t : ℝ) :
    DifferentiableOn ℂ (eulerLog (ofResidue M χ hχ))
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      EqOn (Complex.exp ∘ eulerLog (ofResidue M χ hχ)) L
        (ball (2 + (t : ℂ) * Complex.I) (1 / 2)) ∧
      ∀ s ∈ closedBall (2 + (t : ℂ) * Complex.I) (49 / 100),
        ‖eulerLog (ofResidue M χ hχ) s‖ ≤ eulerLogBound :=
  continued_inner_disk _ (norm_ofResidue_le_one M χ hχ) L hL t

theorem continued_logarithmic_control {e M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b C t : ℝ) (a : Ideal O →*₀ ℂ),
      (∀ I, ‖a I‖ ≤ 1) → ∀ L : ℂ → ℂ,
      1 / 2 ≤ b → b ≤ 1 → Real.exp 1 ≤ C →
      (∀ s : ℂ, 1 < s.re → L s = series a s) →
      DifferentiableOn ℂ L (ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e)) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 3 * e), ‖L z‖ ≤ C ^ M) →
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 6 * e),
        ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 8 * e),
        ‖deriv L z / L z‖ ≤
          (LogarithmicControl.outerConstant e eulerLogBound M / (2 * e)) * Real.log C) := by
  obtain ⟨D, hD, hbound⟩ := LogarithmicControl.logarithmic_control he he'
    eulerLogBound_ge_one hM hε
  refine ⟨D, hD, ?_⟩
  intro b C t a ha L hb hb' hC hEq hL h0 hp
  obtain ⟨hE, heq, hEb⟩ := continued_inner_disk a ha L hEq t
  exact hbound b C L (eulerLog a) (2 + (t : ℂ) * Complex.I)
    hb hb' hC hL h0 hp hE heq hEb

theorem principal_continued_logarithmic_control {e M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (b C t : ℝ) (a : Ideal O →*₀ ℂ),
      (∀ I, ‖a I‖ ≤ 1) → ∀ L : ℂ → ℂ,
      1 / 2 ≤ b → b ≤ 1 → Real.exp 1 ≤ C →
      (∀ s : ℂ, 1 < s.re → L s = ((s - 1) / (s + 1)) * series a s) →
      DifferentiableOn ℂ L (ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e)) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - b - 3 * e), ‖L z‖ ≤ C ^ M) →
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 6 * e),
        ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall (2 + (t : ℂ) * Complex.I) (2 - b - 8 * e),
        ‖deriv L z / L z‖ ≤
          (LogarithmicControl.outerConstant e (3 + eulerLogBound) M / (2 * e)) * Real.log C) := by
  have hA : 1 ≤ 3 + eulerLogBound := by linarith [eulerLogBound_ge_one]
  obtain ⟨D, hD, hbound⟩ := LogarithmicControl.logarithmic_control he he' hA hM hε
  refine ⟨D, hD, ?_⟩
  intro b C t a ha L hb hb' hC hEq hL h0 hp
  obtain ⟨hE, heq, hEb⟩ := principal_continued_inner_disk a ha L hEq t
  exact hbound b C L (principalEulerLog a) (2 + (t : ℂ) * Complex.I)
    hb hb' hC hL h0 hp hE heq hEb

end SevenEighths.HeckeEulerLog

end

end OAI
end OAIOriginalModule0500

/-! Original module: OAI.NumberTheory.DirichletL.IdealMangoldt
Source SHA256: c705c91104e26af00cc38fba2cd83c91f8587c68e4ae886979e14a441007446f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0501



namespace OAI

namespace SevenEighths.IdealMangoldt

open ActualEisensteinCubic UniqueFactorizationMonoid ArithmeticFunction
open scoped BigOperators Classical

noncomputable section

def primeBase (I : Ideal O) : Ideal O := if h : IsPrimePow I then h.choose else 1

theorem primeBase_spec {I : Ideal O} (hI : IsPrimePow I) :
    Prime (primeBase I) ∧ ∃ k : ℕ, 0 < k ∧ primeBase I ^ k = I := by
  obtain ⟨k, hp, hk, heq⟩ := hI.choose_spec
  simp only [primeBase, hI, dite_true]
  exact ⟨hp, k, hk, heq⟩

theorem primeBase_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    primeBase (P ^ k) = P := by
  have hpow : IsPrimePow (P ^ k) := ⟨P, k, hP, hk, rfl⟩
  obtain ⟨hQ, l, hl, heq⟩ := primeBase_spec hpow
  apply associated_iff_eq.mp
  apply hQ.associated_of_dvd hP
  exact hQ.dvd_of_dvd_pow (heq ▸ dvd_pow_self (primeBase (P ^ k)) hl.ne')

def value (I : Ideal O) : ℝ :=
  if IsPrimePow I then Real.log (Ideal.absNorm (primeBase I)) else 0

@[simp] theorem value_zero : value (0 : Ideal O) = 0 := by
  simp only [value, not_isPrimePow_zero, ite_false]

@[simp] theorem value_one : value (1 : Ideal O) = 0 := by
  simp only [value, not_isPrimePow_one, ite_false]

theorem value_pow {P : Ideal O} (hP : Prime P) {k : ℕ} (hk : 0 < k) :
    value (P ^ k) = Real.log (Ideal.absNorm P) := by
  rw [value, ite_eq_left (show IsPrimePow (P ^ k) from ⟨P, k, hP, hk, rfl⟩),
    primeBase_pow hP hk]

theorem value_nonneg (I : Ideal O) : 0 ≤ value I := by
  by_cases hI : IsPrimePow I
  · rw [value, ite_eq_left hI]
    apply Real.log_nonneg
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨_, (primeBase_spec hI).1⟩).trans' (by decide : 1 ≤ 2)
  · simp only [value, hI, ite_false, le_refl]

theorem isPrimePow_absNorm {I : Ideal O} (hI : IsPrimePow I) :
    IsPrimePow (Ideal.absNorm I) := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨p, n, hn, _, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  rw [map_pow, hnorm, ← pow_mul]
  exact (isPrimePow_nat_iff _).mpr ⟨p, n * k, hp, mul_pos hn hk, rfl⟩

theorem value_eq_zero_of_norm_not_primePow {I : Ideal O}
    (hI : ¬IsPrimePow (Ideal.absNorm I)) : value I = 0 := by
  exact ite_eq_right (fun h => hI (isPrimePow_absNorm h))

theorem prime_mem_primesOver_of_dvd_norm {P : Ideal O} (hP : Prime P)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Ideal.absNorm P) :
    P ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨Q, hQ, hQu, hQP⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp P hd
  have heq : P = Q := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero |>.eq_of_le
    hQ.ne_top (Ideal.dvd_iff_le.mp hQP)
  subst Q
  exact ⟨Ideal.isPrime_of_prime hP, ⟨hQu.symm⟩⟩

theorem primeBase_mem_primesOver {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {I : Ideal O} (hI : IsPrimePow I) (hn : Ideal.absNorm I = p ^ k) :
    primeBase I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  obtain ⟨hP, l, hl, heq⟩ := primeBase_spec hI
  apply prime_mem_primesOver_of_dvd_norm hP hp
  apply hp.dvd_of_dvd_pow
  have hnorm := congrArg Ideal.absNorm heq
  rw [map_pow, hn] at hnorm
  rw [hnorm]
  exact dvd_pow_self _ hk.ne'

theorem primeBase_injective_on_norm {I J : Ideal O} (hI : IsPrimePow I)
    (hJ : IsPrimePow J) (hn : Ideal.absNorm I = Ideal.absNorm J)
    (hbase : primeBase I = primeBase J) : I = J := by
  obtain ⟨hP, k, hk, hPk⟩ := primeBase_spec hI
  obtain ⟨_, l, hl, hPl⟩ := primeBase_spec hJ
  rw [← hbase] at hPl
  have hkl : k = l := by
    apply Nat.pow_right_injective (SmoothMobiusCorrection.prime_norm_two_le ⟨_, hP⟩)
    have hnI : Ideal.absNorm (primeBase I) ^ k = Ideal.absNorm I := by
      simpa only [map_pow] using congrArg Ideal.absNorm hPk
    have hnJ : Ideal.absNorm (primeBase I) ^ l = Ideal.absNorm J := by
      simpa only [map_pow] using congrArg Ideal.absNorm hPl
    exact hnI.trans (hn.trans hnJ.symm)
  exact hPk.symm.trans ((congrArg (primeBase I ^ ·) hkl).trans hPl)

def normFiber (n : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset

@[simp] theorem mem_normFiber (n : ℕ) (I : Ideal O) : I ∈ normFiber n ↔ Ideal.absNorm I = n :=
  Set.Finite.mem_toFinset _

def coeff (w : Ideal O → ℝ) (n : ℕ) : ℝ := ∑ I ∈ normFiber n, w I * value I

theorem coeff_nonneg (w : Ideal O → ℝ) (hw : ∀ I, 0 ≤ w I) (n : ℕ) :
    0 ≤ coeff w n :=
  Finset.sum_nonneg (fun I _ => mul_nonneg (hw I) (value_nonneg I))

theorem coeff_le_unweighted (w : Ideal O → ℝ) (hw : ∀ I, w I ≤ 1) (n : ℕ) :
    coeff w n ≤ coeff (fun _ => 1) n := by
  apply Finset.sum_le_sum
  intro I hI
  exact mul_le_mul_of_nonneg_right (hw I) (value_nonneg I)

theorem coeff_eq_sum_primePowers (n : ℕ) :
    coeff (fun _ => 1) n =
      ∑ I ∈ (normFiber n).filter IsPrimePow, Real.log (Ideal.absNorm (primeBase I)) := by
  simp only [coeff, one_mul, value, Finset.sum_filter]

theorem coeff_eq_zero_of_not_primePow {n : ℕ} (hn : ¬IsPrimePow n)
    (w : Ideal O → ℝ) : coeff w n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  rw [value_eq_zero_of_norm_not_primePow (by simpa only [(mem_normFiber n I).mp hI] using hn),
    mul_zero]

def primesOver (p : ℕ) [Fact p.Prime] : Finset (Ideal O) :=
  (IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) O).toFinset

@[simp] theorem mem_primesOver (p : ℕ) [Fact p.Prime] (P : Ideal O) :
    P ∈ primesOver p ↔ P ∈ (Ideal.span {(p : ℤ)}).primesOver O :=
  Set.Finite.mem_toFinset _

theorem primesOver_card (p : ℕ) [Fact p.Prime] :
    (primesOver p).card = ((Ideal.span {(p : ℤ)}).primesOver O).ncard := by
  exact (Set.ncard_eq_toFinset_card _).symm

theorem primesOver_log_sum_le (p : ℕ) [hp : Fact p.Prime] :
    ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) ≤ 2 * Real.log p := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.out.one_lt.le)
  by_cases h1 : p % 3 = 1
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [ShortDraftHeckeBridge.absNorm_split hp.out h1 P]
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      ShortDraftHeckeBridge.split_count_of_mod_one hp.out h1]
    norm_num
  by_cases h2 : p % 3 = 2
  · have hv (P : Ideal O) (hP : P ∈ primesOver p) :
        Real.log (Ideal.absNorm P) = 2 * Real.log p := by
      have hPP := (mem_primesOver p P).mp hP
      let : P.IsPrime := hPP.1
      let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPP.2
      rw [ShortDraftHeckeBridge.absNorm_inert hp.out h2 P, Nat.cast_pow, Real.log_pow]
      norm_num
    rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card,
      ShortDraftHeckeBridge.inert_count_of_mod_two hp.out h2]
    norm_num
  have h3 : p = 3 := by
    have h0 : p % 3 = 0 := by have := Nat.mod_lt p (by decide : 0 < 3); omega
    have h := (Nat.dvd_prime hp.out).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  subst p
  have hv (P : Ideal O) (hP : P ∈ primesOver 3) :
      Real.log (Ideal.absNorm P) = Real.log 3 := by
    have hPP := (mem_primesOver 3 P).mp hP
    let : P.IsPrime := hPP.1
    let : P.LiesOver (Ideal.span {(3 : ℤ)}) := hPP.2
    rw [ShortDraftHeckeBridge.absNorm_ramified P]
    norm_num
  rw [Finset.sum_congr rfl hv, Finset.sum_const, nsmul_eq_mul, primesOver_card]
  norm_num only [Nat.cast_ofNat]
  rw [ShortDraftHeckeBridge.ramified_count]
  norm_num only [Nat.cast_one, one_mul, Nat.cast_ofNat]
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem coeff_prime_pow_le (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    coeff (fun _ => 1) (p ^ k) ≤ 2 * Real.log p := by
  rw [coeff_eq_sum_primePowers]
  let S := (normFiber (p ^ k)).filter IsPrimePow
  have hS (I : Ideal O) (hI : I ∈ S) : IsPrimePow I ∧ Ideal.absNorm I = p ^ k :=
    ⟨(Finset.mem_filter.mp hI).2, (mem_normFiber _ I).mp (Finset.mem_filter.mp hI).1⟩
  have hinj : Set.InjOn primeBase (↑S : Set (Ideal O)) := by
    intro I hI J hJ heq
    exact primeBase_injective_on_norm (hS I hI).1 (hS J hJ).1
      ((hS I hI).2.trans (hS J hJ).2.symm) heq
  have hsub : S.image primeBase ⊆ primesOver p := by
    intro P hP
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hP
    exact (mem_primesOver p _).mpr (primeBase_mem_primesOver hp.out hk (hS I hI).1 (hS I hI).2)
  calc
    _ = ∑ P ∈ S.image primeBase, Real.log (Ideal.absNorm P) := (Finset.sum_image hinj).symm
    _ ≤ ∑ P ∈ primesOver p, Real.log (Ideal.absNorm P) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro P hP _
      have hPP := (mem_primesOver p P).mp hP
      have hprime : Prime P := Ideal.prime_of_mem_primesOver
        (by simpa using (show (p : ℤ) ≠ 0 by exact_mod_cast hp.out.ne_zero)) hPP
      exact Real.log_nonneg (by exact_mod_cast
        (SmoothMobiusCorrection.prime_norm_two_le ⟨P, hprime⟩).trans' (by decide : 1 ≤ 2))
    _ ≤ _ := primesOver_log_sum_le p

theorem coeff_le_two_vonMangoldt (w : Ideal O → ℝ) (hw : ∀ I, w I ≤ 1) (n : ℕ) :
    coeff w n ≤ 2 * vonMangoldt n := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    let : Fact p.Prime := ⟨hp⟩
    rw [vonMangoldt_apply_pow hk.ne', vonMangoldt_apply_prime hp]
    exact (coeff_le_unweighted w hw _).trans (coeff_prime_pow_le p hk)
  · rw [coeff_eq_zero_of_not_primePow hn, vonMangoldt_eq_zero_iff.mpr hn, mul_zero]

theorem coeff_chebyshev (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) :
    ∃ C : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(coeff w n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨2 * C, fun N => ?_⟩
  calc
    _ ≤ 2 * cumsum (fun n => ‖(vonMangoldt n : ℂ)‖) N := by
      unfold cumsum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coeff_nonneg w hw0 n), abs_of_nonneg vonMangoldt_nonneg]
        using coeff_le_two_vonMangoldt w hw1 n
    _ ≤ 2 * (C * N) := mul_le_mul_of_nonneg_left (hC N) (by norm_num)
    _ = _ := by ring

theorem coeff_summable_nterm (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (coeff w n : ℂ)) σ) := by
  have hs : Summable (nterm (fun n => (vonMangoldt n : ℂ)) σ) := by
    simpa only [← nterm_eq_norm_term] using
      (@ArithmeticFunction.LSeriesSummable_vonMangoldt (σ : ℂ) (by simpa using hσ)).norm
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro n
    exact ite_nonneg (by positivity) (div_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _))
  · intro n
    by_cases hn : n = 0
    · simp only [nterm, hn, ite_true, mul_zero, le_refl]
    · simp only [nterm, hn, ite_false, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (coeff_nonneg w hw0 n), abs_of_nonneg vonMangoldt_nonneg]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (coeff_le_two_vonMangoldt w hw1 n)
        (Real.rpow_nonneg (by positivity) _)

theorem coeff_LSeriesSummable (w : Ideal O → ℝ) (hw0 : ∀ I, 0 ≤ w I)
    (hw1 : ∀ I, w I ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coeff w n : ℂ)) s := by
  apply Summable.of_norm
  simpa only [norm_term_eq_nterm_re] using coeff_summable_nterm w hw0 hw1 hs

def classCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  coeff (fun I => if I ∈ C then 1 else 0) n

theorem classCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ classCoeff C n :=
  coeff_nonneg _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_le_two_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n ≤ 2 * vonMangoldt n :=
  coeff_le_two_vonMangoldt _ (fun _ => by split_ifs <;> norm_num) n

theorem classCoeff_chebyshev (C : Set (Ideal O)) :
    ∃ B : ℝ, ∀ N : ℕ, cumsum (fun n => ‖(classCoeff C n : ℂ)‖) N ≤ B * N :=
  coeff_chebyshev _ (fun _ => by split_ifs <;> norm_num)
    (fun _ => by split_ifs <;> norm_num)

theorem classCoeff_summable_nterm (C : Set (Ideal O)) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (classCoeff C n : ℂ)) σ) :=
  coeff_summable_nterm _ (fun _ => by split_ifs <;> norm_num)
    (fun _ => by split_ifs <;> norm_num) hσ

end

end SevenEighths.IdealMangoldt

end OAI
end OAIOriginalModule0501

/-! Original module: OAI.NumberTheory.DirichletL.IdealLogDerivative
Source SHA256: aee9630303da5159e33828238d7ee8b76c4ebfa2b997ce1f762c182b314c0310
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0502


namespace OAI

namespace SevenEighths.IdealLogDerivative

open ActualEisensteinCubic UniqueFactorizationMonoid IdealEuler
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical Topology

noncomputable section

def coeff (a : Ideal O →*₀ ℂ) (n : ℕ) : ℂ :=
  ShortDraftHeckeBridge.normFiberCoeff (fun I => (IdealMangoldt.value I : ℂ) * a I) n

theorem norm_coeff_le (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1) (n : ℕ) :
    ‖coeff a n‖ ≤ IdealMangoldt.coeff (fun _ => 1) n := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg I), one_mul]
  exact mul_le_of_le_one_right (IdealMangoldt.value_nonneg I) (ha I)

theorem norm_coeff_le_two_vonMangoldt (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (n : ℕ) :
    ‖coeff a n‖ ≤ 2 * ArithmeticFunction.vonMangoldt n :=
  (norm_coeff_le a ha n).trans
    (IdealMangoldt.coeff_le_two_vonMangoldt (fun _ => 1) (fun _ => le_refl _) n)

theorem coeff_summable (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) : LSeriesSummable (coeff a) s := by
  apply Summable.of_norm
  have h := (IdealMangoldt.coeff_LSeriesSummable (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_refl _) hs).norm
  apply h.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.coeff_nonneg (fun _ => 1) (fun _ => zero_le_one) n)]
    using norm_coeff_le a ha n

theorem primePow_coprime_factor {B C : Ideal O} (h : IsPrimePow (B * C))
    (hBC : IsRelPrime B C) : B = 1 ∨ C = 1 := by
  obtain ⟨P, k, hP, hk, heq⟩ := h
  obtain ⟨i, hi, hBi⟩ := (dvd_prime_pow hP k).mp
    (heq.symm ▸ dvd_mul_right B C)
  obtain ⟨j, hj, hCj⟩ := (dvd_prime_pow hP k).mp
    (heq.symm ▸ dvd_mul_left C B)
  have hB := associated_iff_eq.mp hBi
  have hC := associated_iff_eq.mp hCj
  by_cases hi0 : i = 0
  · left; simpa only [hi0, pow_zero] using hB
  by_cases hj0 : j = 0
  · right; simpa only [hj0, pow_zero] using hC
  exact (hP.not_isUnit (hBC (hB ▸ dvd_pow_self P hi0) (hC ▸ dvd_pow_self P hj0))).elim

theorem value_mul_coprime {B C : Ideal O} (hBC : IsRelPrime B C) :
    IdealMangoldt.value (B * C) =
      (if C = 1 then IdealMangoldt.value B else 0) +
      (if B = 1 then IdealMangoldt.value C else 0) := by
  by_cases hB : B = 1
  · subst B
    simp only [one_mul, IdealMangoldt.value_one, ite_self, ite_true, zero_add]
  by_cases hC : C = 1
  · subst C
    simp only [mul_one, IdealMangoldt.value_one, ite_self, ite_true, add_zero]
  have hnot : ¬IsPrimePow (B * C) := by
    intro h
    exact (primePow_coprime_factor h hBC).elim hB hC
  simp only [IdealMangoldt.value, hnot, hB, hC, ite_false, zero_add]

theorem idealDivisors_one : idealDivisors (1 : Ideal O) = {1} := by
  ext D
  rw [mem_idealDivisors (show (1 : Ideal O) ≠ ⊥ from one_ne_zero), Finset.mem_singleton]
  exact isUnit_iff_dvd_one.symm.trans isUnit_iff_eq_one

theorem idealDivisors_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    idealDivisors (P ^ k) = (Finset.range (k + 1)).image (fun j => P ^ j) := by
  ext D
  rw [mem_idealDivisors (show P ^ k ≠ ⊥ from pow_ne_zero k hP.ne_zero), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨j, hj, hDj⟩ := (dvd_prime_pow hP k).mp hD
    exact ⟨j, Finset.mem_range.mpr (by omega), (associated_iff_eq.mp hDj).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact pow_dvd_pow P (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)

theorem sum_value_prime_pow (P : Ideal O) (hP : Prime P) (k : ℕ) :
    (∑ D ∈ idealDivisors (P ^ k), (IdealMangoldt.value D : ℂ)) =
      k * (Real.log (Ideal.absNorm P) : ℂ) := by
  rw [idealDivisors_prime_pow P hP k, Finset.sum_image]
  · induction k with
    | zero => simp only [Nat.zero_add, Finset.sum_range_one, pow_zero,
        IdealMangoldt.value_one, Complex.ofReal_zero, Nat.cast_zero, zero_mul]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, IdealMangoldt.value_pow hP (Nat.succ_pos k)]
      push_cast
      ring
  · exact fun i _ j _ hij => pow_injective_of_not_isUnit hP.not_isUnit hP.ne_zero hij

theorem sum_value_mul (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsRelPrime B C) :
    (∑ D ∈ idealDivisors (B * C), (IdealMangoldt.value D : ℂ)) =
      (∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ)) +
      ∑ D ∈ idealDivisors C, (IdealMangoldt.value D : ℂ) := by
  have hcop : IsCoprime B C := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply Ideal.isUnit_iff.mp
    exact hBC (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)
  have h1B : (1 : Ideal O) ∈ idealDivisors B := (mem_idealDivisors hB).mpr (one_dvd _)
  have h1C : (1 : Ideal O) ∈ idealDivisors C := (mem_idealDivisors hC).mpr (one_dvd _)
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hcop]
  calc
    _ = ∑ D ∈ idealDivisors B, ∑ E ∈ idealDivisors C,
        ((if E = 1 then (IdealMangoldt.value D : ℂ) else 0) +
        (if D = 1 then (IdealMangoldt.value E : ℂ) else 0)) := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      rw [value_mul_coprime ((hBC.of_dvd_left ((mem_idealDivisors hB).mp hD)).of_dvd_right
        ((mem_idealDivisors hC).mp hE)), Complex.ofReal_add]
      split_ifs <;> rfl
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_irrel,
        Finset.sum_ite_eq', ite_eq_left h1C, ite_eq_left h1B, Finset.sum_const_zero]

theorem sum_value_divisors (B : Ideal O) (hB : B ≠ 0) :
    (∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ)) =
      (Real.log (Ideal.absNorm B) : ℂ) := by
  induction B using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact (hB rfl).elim
  | h1 hunit =>
    rw [isUnit_iff_eq_one.mp hunit, idealDivisors_one, Finset.sum_singleton]
    simp only [IdealMangoldt.value_one, map_one, Nat.cast_one, Real.log_one]
  | hpr k hP =>
    rw [sum_value_prime_pow _ hP k, map_pow, Nat.cast_pow, Real.log_pow]
    push_cast
    rfl
  | @hcp B C hBC ihB ihC =>
    have hB0 : B ≠ 0 := left_ne_zero_of_mul hB
    have hC0 : C ≠ 0 := right_ne_zero_of_mul hB
    rw [sum_value_mul B C hB0 hC0 hBC, ihB hB0, ihC hC0, map_mul, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hB0))
        (by exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hC0)), Complex.ofReal_add]

theorem value_le_log_norm (B : Ideal O) :
    IdealMangoldt.value B ≤ Real.log (Ideal.absNorm B) := by
  by_cases h : IsPrimePow B
  · obtain ⟨P, k, hP, hk, rfl⟩ := h
    rw [IdealMangoldt.value_pow hP hk, map_pow, Nat.cast_pow, Real.log_pow]
    apply le_mul_of_one_le_left
    · exact Real.log_natCast_nonneg _
    · exact_mod_cast hk
  · rw [IdealMangoldt.value, ite_eq_right h]
    exact Real.log_natCast_nonneg _

theorem weighted_eq_term (a : Ideal O →*₀ ℂ) (s : ℂ) (B : Ideal O) :
    weighted a s B = LSeries.term (fun _ => a B) s (Ideal.absNorm B) := by
  by_cases hB : B = 0
  · subst B
    simp only [map_zero, LSeries.term_zero]
  · have hn : Ideal.absNorm B ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hB
    change a B * CubicEisenstein.fullIdealWeight s B = _
    simp only [CubicEisenstein.fullIdealWeight, hB, ite_false,
      LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

theorem weighted_hasDerivAt (a : Ideal O →*₀ ℂ) (s : ℂ) (B : Ideal O) :
    HasDerivAt (fun z => weighted a z B)
      (-((Real.log (Ideal.absNorm B) : ℂ) * weighted a s B)) s := by
  simp_rw [weighted_eq_term]
  convert LSeries.hasDerivAt_term (fun _ => a B) (Ideal.absNorm B) s using 1
  by_cases hn : Ideal.absNorm B = 0
  · simp only [hn, LSeries.term_zero, mul_zero]
  · simp only [LSeries.term_of_ne_zero hn, LSeries.logMul, Complex.natCast_log,
      mul_div_assoc]

theorem log_weighted_hasSum (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun B : Ideal O => (Real.log (Ideal.absNorm B) : ℂ) * weighted a s B)
      (-deriv (series a) s) := by
  obtain ⟨x, hx, hxs⟩ := exists_between hs
  have hu := weighted_summable_norm a ha (x : ℂ) (by simpa using hx)
  have hd (B : Ideal O) : DifferentiableOn ℂ (fun z => weighted a z B) {z : ℂ | x < z.re} :=
    fun z _ => (weighted_hasDerivAt a z B).differentiableAt.differentiableWithinAt
  have hU : IsOpen {z : ℂ | x < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hbound (B : Ideal O) (z : ℂ) (hz : z ∈ {z : ℂ | x < z.re}) :
      ‖weighted a z B‖ ≤ ‖weighted a (x : ℂ) B‖ := by
    simp only [weighted_eq_term]
    exact LSeries.norm_term_le_of_re_le_re _ (by simpa using hz.le) _
  have H := Complex.hasSum_deriv_of_summable_norm hu hd hU hbound hxs
  simp_rw [(weighted_hasDerivAt a s _).deriv] at H
  unfold IdealEuler.series
  simpa only [neg_neg] using H.neg

theorem mangoldt_weighted_summable_norm (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun B : Ideal O => ‖(IdealMangoldt.value B : ℂ) * weighted a s B‖) := by
  apply (log_weighted_hasSum a ha s hs).summable.norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro B
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg B), abs_of_nonneg (Real.log_natCast_nonneg _)]
  exact mul_le_mul_of_nonneg_right (value_le_log_norm B) (norm_nonneg _)

theorem mangoldt_series_eq_LSeries (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    (∑' B : Ideal O, (IdealMangoldt.value B : ℂ) * weighted a s B) = LSeries (coeff a) s := by
  have H := (mangoldt_weighted_summable_norm a ha s hs).of_norm.hasSum.tsum_fiberwise Ideal.absNorm
  change HasSum (fun n : ℕ => ∑' B : {B : Ideal O // Ideal.absNorm B = n},
    (IdealMangoldt.value B.val : ℂ) * weighted a s B.val) _ at H
  have hf (n : ℕ) : (∑' B : {B : Ideal O // Ideal.absNorm B = n},
      (IdealMangoldt.value B.val : ℂ) * weighted a s B.val) = LSeries.term (coeff a) s n := by
    unfold coeff
    simpa only [weighted, normWeight,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, mul_assoc]
      using SmoothMobiusCorrection.idealDirichlet_fiber
        (fun B => (IdealMangoldt.value B : ℂ) * a B) s n
  simp_rw [hf] at H
  exact H.tsum_eq.symm

theorem mulFiber_value_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : CompletedGauss.MulFiber B, (IdealMangoldt.value p.val.1 : ℂ)) =
      (Real.log (Ideal.absNorm B) : ℂ) := by
  let e := CompletedGauss.mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B}, (IdealMangoldt.value D.val : ℂ) :=
      e.tsum_eq (fun D => (IdealMangoldt.value D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (IdealMangoldt.value D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun _ => Iff.rfl)
        (fun D => (IdealMangoldt.value D : ℂ))).symm
    _ = _ := sum_value_divisors B hB

theorem coeff_LSeries_mul_series (a : Ideal O →*₀ ℂ) (ha : ∀ I, ‖a I‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s * series a s = -deriv (series a) s := by
  let f := weighted a s
  let F : Ideal O × Ideal O → ℂ := fun p => (IdealMangoldt.value p.1 : ℂ) * f (p.1 * p.2)
  have hprod := (mangoldt_weighted_summable_norm a ha s hs).mul_norm
    (weighted_summable_norm a ha s hs)
  have hF : Summable F := by
    apply hprod.of_norm.congr
    intro p
    dsimp only [F, f]
    rw [map_mul]
    ring
  have hfiber (B : Ideal O) : (∑' p : CompletedGauss.MulFiber B, F p.val) =
      (Real.log (Ideal.absNorm B) : ℂ) * f B := by
    by_cases hB : B = 0
    · subst B
      have hz (p : CompletedGauss.MulFiber 0) : F p.val = 0 := by
        simp only [F, p.property, map_zero, mul_zero]
      simp only [hz, tsum_zero, map_zero, mul_zero]
    · calc
        _ = (∑' p : CompletedGauss.MulFiber B, (IdealMangoldt.value p.val.1 : ℂ)) * f B := by
          rw [← tsum_mul_right]
          exact tsum_congr (fun p => by simp only [F, p.property])
        _ = _ := by rw [mulFiber_value_sum B hB]
  have hsum := hF.hasSum.tsum_fiberwise (fun p : Ideal O × Ideal O => p.1 * p.2)
  change HasSum (fun B : Ideal O => ∑' p : CompletedGauss.MulFiber B, F p.val) _ at hsum
  simp_rw [hfiber] at hsum
  calc
    _ = (∑' B : Ideal O, (IdealMangoldt.value B : ℂ) * f B) * ∑' B : Ideal O, f B := by
      rw [mangoldt_series_eq_LSeries a ha s hs]
      rfl
    _ = ∑' p : Ideal O × Ideal O, ((IdealMangoldt.value p.1 : ℂ) * f p.1) * f p.2 :=
      tsum_mul_tsum_of_summable_norm (mangoldt_weighted_summable_norm a ha s hs)
        (weighted_summable_norm a ha s hs)
    _ = ∑' p, F p := by
      apply tsum_congr
      intro p
      simp only [F, map_mul]
      ring
    _ = -deriv (series a) s := hsum.unique (log_weighted_hasSum a ha s hs)

theorem coeff_LSeries_eq_neg_logDeriv (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s = -deriv (series a) s / series a s := by
  apply (eq_div_iff (series_ne_zero a ha s hs)).mpr
  exact coeff_LSeries_mul_series a ha s hs

theorem coeff_LSeries_eq_neg_logDeriv_of_eq (a : Ideal O →*₀ ℂ)
    (ha : ∀ I, ‖a I‖ ≤ 1) (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 1 < z.re → F z = series a z)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (coeff a) s = -deriv F s / F s := by
  have hd : deriv F s = deriv (series a) s := by
    apply Filter.EventuallyEq.deriv_eq
    have hU : {z : ℂ | 1 < z.re} ∈ nhds s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hU] with z hz
    exact hF z hz
  rw [hd, hF s hs]
  exact coeff_LSeries_eq_neg_logDeriv a ha s hs

end
end SevenEighths.IdealLogDerivative

end OAI
end OAIOriginalModule0502

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.CanonicalReferenceThreshold
Source SHA256: 013aa771f4f84decba163ede69d9626e4dc953cef4aa865099b4e6b21bf6dc93
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0503


namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap ContDiff

namespace SevenEighths.InverseMoment

theorem exists_canonical_reference_cutoff (lo hi : ℝ) :
    ∃ Vlog : SchwartzMap ℝ ℂ, ∃ Alog : ℝ, 0 < Alog ∧
      Alog = CanonicalCubeSeparation.columnWindowRadius lo hi + 1 ∧
      HasCompactSupport Vlog ∧
      tsupport Vlog ⊆ Set.Icc (-Alog) Alog ∧
      (∀ x, Vlog x ≠ 0 → |x| ≤ Alog) ∧
      (∀ x, |x| ≤ CanonicalCubeSeparation.columnWindowRadius lo hi → Vlog x = 1) ∧
      Vlog 0 = 1 := by
  obtain ⟨v, hvc, hvs, hvone, hvbox, hvzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff
      (CanonicalCubeSeparation.columnWindowRadius lo hi)
      (CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi)
  let Vlog : SchwartzMap ℝ ℂ := hvc.toSchwartzMap hvs
  refine ⟨Vlog, CanonicalCubeSeparation.columnWindowRadius lo hi + 1,
    by linarith [CanonicalCubeSeparation.columnWindowRadius_nonneg lo hi],
    rfl, hvc, hvbox, ?_, hvone, hvzero⟩
  intro x hx
  exact abs_le.mpr (hvbox (subset_tsupport v hx))

theorem eventually_canonical_reference_gates (hi Alog window eta : ℝ)
    (heta : 0 < eta) :
    ∃ Z0 : ℝ, 1 < Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
      1 ≤ eta * Real.log Z ∧ hi ≤ Z ^ eta ∧
      Real.exp Alog ≤ Z ^ eta ∧ Real.exp window ≤ Z ^ eta := by
  let R : ℝ := 2 + |hi| + |Alog| + |window|
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [abs_nonneg hi, abs_nonneg Alog, abs_nonneg window]
  refine ⟨2 + Real.exp (R / eta), by linarith [Real.exp_pos (R / eta)], ?_⟩
  intro Z hZ
  have hZtwo : 2 ≤ Z := by linarith [Real.exp_pos (R / eta)]
  have hZpos : 0 < Z := by linarith
  have hZexp : Real.exp (R / eta) ≤ Z := by linarith
  have hlog := Real.log_le_log (Real.exp_pos (R / eta)) hZexp
  rw [Real.log_exp] at hlog
  have hRlog : R ≤ Real.log Z * eta := (div_le_iff₀ heta).mp hlog
  have hpow : Real.exp R ≤ Z ^ eta := by
    rw [Real.rpow_def_of_pos hZpos]
    exact Real.exp_le_exp.mpr hRlog
  have hexp : Real.exp 1 ≤ Z ^ eta :=
    (Real.exp_le_exp.mpr hR).trans hpow
  refine ⟨hZtwo, (by linarith [Real.add_one_le_exp (1 : ℝ)] : 2 ≤ Real.exp 1).trans
    hexp, hexp, by nlinarith, ?_, ?_, ?_⟩
  · have hhi : hi ≤ R := by
      dsimp [R]
      linarith [le_abs_self hi, abs_nonneg Alog, abs_nonneg window]
    exact hhi.trans ((by linarith [Real.add_one_le_exp R] : R ≤ Real.exp R).trans hpow)
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    dsimp [R]
    linarith [le_abs_self Alog, abs_nonneg hi, abs_nonneg window]
  · apply (Real.exp_le_exp.mpr ?_).trans hpow
    dsimp [R]
    linarith [le_abs_self window, abs_nonneg hi, abs_nonneg Alog]

theorem canonical_reference_pool_coverage (hi B Z N L D : ℝ)
    (hB : 0 ≤ B) (hhi : hi ≤ B) (hZ : 1 ≤ Z) (hNL : N ≤ L)
    (hD : B * Z ^ L ≤ D) : hi * Z ^ N ≤ D := by
  calc
    hi * Z ^ N ≤ B * Z ^ N :=
      mul_le_mul_of_nonneg_right hhi (Real.rpow_nonneg (by linarith) _)
    _ ≤ B * Z ^ L :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hNL) hB
    _ ≤ D := hD

theorem exists_canonical_reference_family_gates {ι : Type*} (s : Finset ι)
    (hi Alog window : ι → ℝ) (eta : ℝ) (heta : 0 < eta) :
    ∃ B : ℝ, 0 < B ∧ ∃ Z0 : ℝ, 1 < Z0 ∧
      (∀ i ∈ s, hi i ≤ B ∧ Real.exp (Alog i) ≤ B ∧ Real.exp (window i) ≤ B) ∧
      ∀ Z : ℝ, Z0 ≤ Z →
        2 ≤ Z ∧ 2 ≤ Z ^ eta ∧ Real.exp 1 ≤ Z ^ eta ∧
        1 ≤ eta * Real.log Z ∧ B ≤ Z ^ eta ∧
        (∀ i ∈ s, hi i ≤ Z ^ eta ∧ Real.exp (Alog i) ≤ Z ^ eta ∧
          Real.exp (window i) ≤ Z ^ eta) ∧
        (∀ i ∈ s, ∀ N L D : ℝ, N ≤ L → B * Z ^ L ≤ D → hi i * Z ^ N ≤ D) := by
  let mass : ι → ℝ := fun i => |hi i| + Real.exp (Alog i) + Real.exp (window i)
  have hm : ∀ i, 0 ≤ mass i := by intro i; dsimp [mass]; positivity
  let B : ℝ := 1 + ∑ i ∈ s, mass i
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound : ∀ i ∈ s, hi i ≤ B ∧ Real.exp (Alog i) ≤ B ∧
      Real.exp (window i) ≤ B := by
    intro i hiS
    have hsum : mass i ≤ ∑ j ∈ s, mass j := Finset.single_le_sum (fun j _ => hm j) hiS
    dsimp [mass, B] at *
    constructor
    · linarith [le_abs_self (hi i), Real.exp_pos (Alog i), Real.exp_pos (window i)]
    constructor
    · linarith [abs_nonneg (hi i), Real.exp_pos (window i)]
    · linarith [abs_nonneg (hi i), Real.exp_pos (Alog i)]
  obtain ⟨Z0, hZ0, hgate⟩ := eventually_canonical_reference_gates B 0 0 eta heta
  refine ⟨B, hB, Z0, hZ0, hbound, ?_⟩
  intro Z hZ
  obtain ⟨hZtwo, htwo, hexp, hlog, hBpow, _, _⟩ := hgate Z hZ
  refine ⟨hZtwo, htwo, hexp, hlog, hBpow, ?_, ?_⟩
  · intro i hiS
    obtain ⟨hhi, hA, hw⟩ := hbound i hiS
    exact ⟨hhi.trans hBpow, hA.trans hBpow, hw.trans hBpow⟩
  · intro i hiS N L D hNL hD
    exact canonical_reference_pool_coverage (hi i) B Z N L D hB.le
      (hbound i hiS).1 (by linarith) hNL hD

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0503

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialFibers
Source SHA256: ebb7bf227fcc807358d15ebe182f24a32ea662ce3986aa7a944bdb3029b5a5d6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0504


namespace OAI

namespace SevenEighths.InverseInitialFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical
noncomputable section

@[ext] structure InitialTuple (J : ℕ) where
  common : Ideal O
  divisor : Ideal O
  residual : Ideal O
  frequency : O
  assigned : Fin J → SmoothMobiusCorrection.PrimeIdeal

structure Valid {J : ℕ} (x : InitialTuple J) (t f : Ideal O) (k : O) : Prop where
  common_eq : t * x.divisor = x.common
  label_eq : x.divisor * x.residual = f
  divisor_good : primaryGenerator x.divisor ≠ 0
  row_eq : primaryGenerator x.divisor * x.frequency = k
  assigned_dvd : ∀ i, (x.assigned i).val ∣ t * f

theorem Valid.of_reconstruction {J : ℕ} (x : InitialTuple J) (t f : Ideal O) (k : O)
    (hf : primaryGenerator f ≠ 0) (hC : t*x.divisor = x.common)
    (hlabel : x.divisor*x.residual = f)
    (hrow : primaryGenerator x.divisor*x.frequency = k)
    (hslots : ∀ i, (x.assigned i).val ∣ t*f) : Valid x t f k := by
  refine ⟨hC, hlabel, ?_, hrow, hslots⟩
  intro hz
  apply hf
  rw [← hlabel, primaryGenerator_mul, hz, zero_mul]

lemma divisor_dvd {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) : x.divisor ∣ f := ⟨x.residual, hx.label_eq.symm⟩

lemma divisor_ne_zero {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hf : f ≠ 0) : x.divisor ≠ 0 := by
  intro hz
  have he := hx.label_eq
  rw [hz, zero_mul] at he
  exact hf he.symm

theorem valid_key_injective {J : ℕ} (t f : Ideal O) (k : O) (hf : f ≠ 0)
    {x y : InitialTuple J} (hx : Valid x t f k) (hy : Valid y t f k)
    (hd : x.divisor = y.divisor) (ha : x.assigned = y.assigned) : x = y := by
  have hd0 := divisor_ne_zero hx hf
  have hc : x.common = y.common := by rw [← hx.common_eq, ← hy.common_eq, hd]
  have hs : x.residual = y.residual := by
    apply mul_left_cancel₀ hd0
    exact hx.label_eq.trans (by simpa only [hd] using hy.label_eq.symm)
  have hg : primaryGenerator x.divisor ≠ 0 := hx.divisor_good
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ hg
    exact hx.row_eq.trans (by simpa only [hd] using hy.row_eq.symm)
  exact InitialTuple.ext hc hd hs hr ha

lemma divisors_mul_image (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealDivisors (I*J) =
      ((idealDivisors I) ×ˢ (idealDivisors J)).image (fun p => p.1*p.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hI hJ), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨A, B, hA, hB, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hD
    exact ⟨(A,B), Finset.mem_product.mpr
      ⟨(mem_idealDivisors hI).mpr hA, (mem_idealDivisors hJ).mpr hB⟩, hab.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hI).mp (Finset.mem_product.mp hp).1)
      ((mem_idealDivisors hJ).mp (Finset.mem_product.mp hp).2)

lemma divisor_card_mul_le (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (idealDivisors (I*J)).card ≤ (idealDivisors I).card * (idealDivisors J).card := by
  rw [divisors_mul_image I J hI hJ, ← Finset.card_product]
  exact Finset.card_image_le

theorem valid_tuple_card_le {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card * (idealDivisors (t*f)).card^J := by
  let D := idealDivisors f
  let E := idealDivisors (t*f)
  let encode (x : T) : D × (Fin J → E) :=
    (⟨x.val.divisor, (mem_idealDivisors hf).mpr (divisor_dvd (hT x.val x.property))⟩,
      fun i => ⟨(x.val.assigned i).val,
        (mem_idealDivisors (mul_ne_zero ht hf)).mpr ((hT x.val x.property).assigned_dvd i)⟩)
  have hi : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply valid_key_injective t f k hf (hT x.val x.property) (hT y.val y.property)
    · exact congrArg Subtype.val (congrArg Prod.fst hxy)
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : E => z.val) (congrFun (congrArg Prod.snd hxy) i)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, D, E] using Fintype.card_le_of_injective encode hi

theorem valid_tuple_card_le_separated {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card^(J+1) * (idealDivisors t).card^J := by
  apply (valid_tuple_card_le T t f k ht hf hT).trans
  calc
    _ ≤ (idealDivisors f).card *
        ((idealDivisors t).card * (idealDivisors f).card)^J :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (divisor_card_mul_le t f ht hf) J)
    _ = _ := by rw [mul_pow, pow_succ]; ring

lemma valid_label_squarefree {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hC : Squarefree x.common) (hs : Squarefree x.residual)
    (hmask : IsCoprime x.residual x.common) : Squarefree f := by
  have hdC : x.divisor ∣ x.common := by rw [← hx.common_eq]; exact dvd_mul_left _ _
  have hds : IsCoprime x.divisor x.residual := (hmask.of_isCoprime_of_dvd_right hdC).symm
  rw [← hx.label_eq]
  exact squarefree_mul_iff.mpr ⟨hds.isRelPrime, hC.squarefree_of_dvd hdC, hs⟩

lemma divisor_card_pos (I : Ideal O) (hI : I ≠ 0) : 1 ≤ (idealDivisors I).card := by
  apply Finset.one_le_card.mpr
  exact ⟨1, (mem_idealDivisors hI).mpr (one_dvd I)⟩

theorem valid_tuple_card_le_slot_cap {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) (K : ℕ) (hJ : J ≤ 2*K) :
    T.card ≤ (idealDivisors f).card^(1+2*K) * (idealDivisors t).card^(2*K) := by
  apply (valid_tuple_card_le_separated T t f k ht hf hT).trans
  exact Nat.mul_le_mul
    (pow_le_pow_right₀ (divisor_card_pos f hf) (by omega))
    (pow_le_pow_right₀ (divisor_card_pos t ht) hJ)

theorem valid_tuple_small_power (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : Finset (InitialTuple J)) (t f : Ideal O) (k : O),
      t ≠ 0 → f ≠ 0 → (∀ x ∈ T, Valid x t f k) →
      (T.card : ℝ) ≤ C * ((Ideal.absNorm t : ℝ) * Ideal.absNorm f)^ε := by
  have hJr : 0 < (J+1 : ℝ) := by positivity
  obtain ⟨C, hC, hb⟩ := IdealDivisorBound.ideal_divisor_small_power
    (ε/(J+1)) (div_pos hε hJr)
  refine ⟨C^(J+1), by positivity, ?_⟩
  intro T t f k ht hf hT
  have htf : t*f ≠ 0 := mul_ne_zero ht hf
  have hsub : idealDivisors f ⊆ idealDivisors (t*f) := by
    intro D hD
    exact (mem_idealDivisors htf).mpr
      (((mem_idealDivisors hf).mp hD).trans (dvd_mul_left _ _))
  have hcard : T.card ≤ (idealDivisors (t*f)).card^(J+1) := by
    apply (valid_tuple_card_le T t f k ht hf hT).trans
    calc
      _ ≤ (idealDivisors (t*f)).card * (idealDivisors (t*f)).card^J :=
        Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ = _ := by rw [pow_succ]; ring
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ((idealDivisors (t*f)).card : ℝ))
    (hb (t*f) htf) (J+1)
  apply (show (T.card : ℝ) ≤ ((idealDivisors (t*f)).card : ℝ)^(J+1) by
    exact_mod_cast hcard).trans (hh.trans_eq ?_)
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), map_mul, Nat.cast_mul]
  congr 1
  push_cast
  field_simp

def initialFiber {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O) : Finset (InitialTuple J) :=
  source.filter (fun x => Valid x t f k ∧ (∀ i, x.assigned i ∈ lists i) ∧ keep x)

theorem initialFiber_card_le {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) :
    (initialFiber source lists keep t f k).card ≤
      (idealDivisors f).card^(J+1) * (idealDivisors t).card^J :=
  valid_tuple_card_le_separated _ t f k ht hf
    (fun _x hx => (Finset.mem_filter.mp hx).2.1)

theorem initialFiber_card_le_slot_cap {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) (K : ℕ) (hJ : J ≤ 2*K) :
    (initialFiber source lists keep t f k).card ≤
      (idealDivisors f).card^(1+2*K) * (idealDivisors t).card^(2*K) :=
  valid_tuple_card_le_slot_cap _ t f k ht hf
    (fun _x hx => (Finset.mem_filter.mp hx).2.1) K hJ

theorem initialFiber_small_power (J : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (source : Finset (InitialTuple J))
      (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
      (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O),
      t ≠ 0 → f ≠ 0 →
      ((initialFiber source lists keep t f k).card : ℝ) ≤
        C * ((Ideal.absNorm t : ℝ) * Ideal.absNorm f)^ε := by
  obtain ⟨C, hC, hbound⟩ := valid_tuple_small_power J ε hε
  refine ⟨C, hC, ?_⟩
  intro source lists keep t f k ht hf
  exact hbound _ t f k ht hf (fun _x hx => (Finset.mem_filter.mp hx).2.1)

theorem initialFiber_weight_bound {J : ℕ} (source : Finset (InitialTuple J))
    (lists : Fin J → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : InitialTuple J → Prop) (t f : Ideal O) (k : O)
    (ht : t ≠ 0) (hf : f ≠ 0) (w : InitialTuple J → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ x ∈ initialFiber source lists keep t f k, ‖w x‖ ≤ C) :
    (∑ x ∈ initialFiber source lists keep t f k, ‖w x‖) ≤
      C * ((idealDivisors f).card : ℝ)^(J+1) * ((idealDivisors t).card : ℝ)^J := by
  calc
    _ ≤ ∑ _x ∈ initialFiber source lists keep t f k, C :=
      Finset.sum_le_sum hw
    _ = ((initialFiber source lists keep t f k).card : ℝ) * C := by simp
    _ ≤ ((idealDivisors f).card^(J+1) * (idealDivisors t).card^J : ℕ) * C :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast initialFiber_card_le source lists keep t f k ht hf) hC
    _ = _ := by push_cast; ring

end
end SevenEighths.InverseInitialFibers

end OAI
end OAIOriginalModule0504

/-! Original module: OAI.NumberTheory.DirichletL.Descent.InitializationEnergy
Source SHA256: f23bcb4510dad637646bf914c2b77bccce5ea9b7535e89f8f87e51ec29e3359a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0505




namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss CanonicalQuadraticSieve SevenEighths.InverseInitialFibers
open IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

abbrev InitialChild := Ideal Eis × Ideal Eis × Eis

def initialChild {J : ℕ} (x : InitialTuple J) : InitialChild :=
  (idealQuotient x.divisor x.common, x.divisor * x.residual,
    primaryGenerator x.divisor * x.frequency)

structure InitialSourceValid {J : ℕ} (x : InitialTuple J) : Prop where
  common_ne_zero : x.common ≠ 0
  residual_ne_zero : x.residual ≠ 0
  divisor_good : primaryGenerator x.divisor ≠ 0
  divisor_dvd : x.divisor ∣ x.common
  assigned_dvd : ∀ i, (x.assigned i).val ∣ x.common * x.residual

theorem initialChild_valid {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    Valid x (initialChild x).1 (initialChild x).2.1 (initialChild x).2.2 := by
  have ht : idealQuotient x.divisor x.common * x.divisor = x.common := by
    rw [mul_comm, idealQuotient_mul hx.divisor_dvd]
  refine ⟨ht, rfl, hx.divisor_good, rfl, ?_⟩
  intro i
  change (x.assigned i).val ∣ idealQuotient x.divisor x.common * (x.divisor * x.residual)
  rw [← mul_assoc, ht]
  exact hx.assigned_dvd i

theorem initialChild_nonzero {J : ℕ} (x : InitialTuple J) (hx : InitialSourceValid x) :
    (initialChild x).1 ≠ 0 ∧ (initialChild x).2.1 ≠ 0 := by
  have hD : x.divisor ≠ 0 := by intro he; exact hx.divisor_good (by simp [he])
  constructor
  · intro ht
    have he := (initialChild_valid x hx).common_eq
    rw [ht, zero_mul] at he
    exact hx.common_ne_zero he.symm
  · exact mul_ne_zero hD hx.residual_ne_zero

def initialQuotientSet {J : ℕ} (source : Finset (InitialTuple J)) : Finset (Ideal Eis) :=
  source.image (fun x => (initialChild x).1)

def initialDivisorWeight (J : ℕ) (c : InitialChild) : ℝ :=
  ((idealDivisors c.2.1).card : ℝ) ^ (J + 1) * ((idealDivisors c.1).card : ℝ) ^ J

theorem initialChild_fiber_weight {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x) (c : InitialChild)
    (ht : c.1 ≠ 0) (hf : c.2.1 ≠ 0) (w : InitialTuple J → ℝ)
    (hw : ∀ x ∈ source, w x ≤ 1) :
    (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
  have hvalid : ∀ x ∈ source.filter (fun x => initialChild x = c), Valid x c.1 c.2.1 c.2.2 := by
    intro x hx
    obtain ⟨hxs, he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using initialChild_valid x (hsource x hxs)
  calc
    _ ≤ ∑ _x ∈ source.filter (fun x => initialChild x = c), (1 : ℝ) :=
      Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    _ = ((source.filter (fun x => initialChild x = c)).card : ℝ) := by simp
    _ ≤ initialDivisorWeight J c := by
      have hh := valid_tuple_card_le_separated _ c.1 c.2.1 c.2.2 ht hf hvalid
      dsimp only [initialDivisorWeight]
      exact_mod_cast hh

theorem initial_energy_projection {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) (F : InitialChild → ℂ) :
    (∑ x ∈ source, w x * ‖F (initialChild x)‖ ^ 2) ≤
      ∑ t ∈ initialQuotientSet source, ((idealDivisors t).card : ℝ) ^ J *
        ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (J + 1) *
          ∑ k ∈ rows, ‖F (t, f, k)‖ ^ 2 := by
  have hmaps : ∀ x ∈ source, initialChild x ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      Finset.mem_product.mpr (hchild x hx)⟩
  have hfiber : ∀ c ∈ initialQuotientSet source ×ˢ (labels ×ˢ rows),
      (∑ x ∈ source with initialChild x = c, w x) ≤ initialDivisorWeight J c := by
    intro c hc
    obtain ⟨ht, hfk⟩ := Finset.mem_product.mp hc
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ht
    have ht0 : c.1 ≠ 0 := he ▸ (initialChild_nonzero x (hsource x hx)).1
    exact initialChild_fiber_weight source hsource c ht0
      (hlabels c.2.1 (Finset.mem_product.mp hfk).1) w hw
  have he := fiber_energy_bound source (initialQuotientSet source ×ˢ (labels ×ˢ rows))
    initialChild w (initialDivisorWeight J) (fun c => ‖F c‖ ^ 2) hmaps
    (fun _ _ => sq_nonneg _) hfiber
  apply he.trans_eq
  simp only [Finset.sum_product, initialDivisorWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

def initialPositiveEnergy {J : ℕ} (source : Finset (InitialTuple J))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (F : InitialChild → ℂ) : ℝ :=
  ∑ t ∈ initialQuotientSet source, ((idealDivisors t).card : ℝ) ^ J *
    ∑ f ∈ labels, ((idealDivisors f).card : ℝ) ^ (J + 1) *
      ∑ k ∈ rows, ‖F (t, f, k)‖ ^ 2

theorem initialPositiveEnergy_nonneg {J : ℕ} (source : Finset (InitialTuple J))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (F : InitialChild → ℂ) :
    0 ≤ initialPositiveEnergy source labels rows F := by
  unfold initialPositiveEnergy
  positivity

theorem initial_weighted_count {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw0 : ∀ x ∈ source, 0 ≤ w x) (hw1 : ∀ x ∈ source, w x ≤ 1)
    (F G : InitialChild → ℂ) :
    ‖∑ x ∈ source, (w x : ℂ) * F (initialChild x) * star (G (initialChild x))‖ ≤
      Real.sqrt (initialPositiveEnergy source labels rows F) *
        Real.sqrt (initialPositiveEnergy source labels rows G) := by
  have hF := initial_energy_projection source hsource labels rows hlabels hchild w hw1 F
  have hG := initial_energy_projection source hsource labels rows hlabels hchild w hw1 G
  apply (weighted_cauchy source w (F ∘ initialChild) (G ∘ initialChild) hw0).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem initial_weighted_count_normalized {J : ℕ} (source : Finset (InitialTuple J))
    (hsource : ∀ x ∈ source, InitialSourceValid x)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hlabels : ∀ f ∈ labels, f ≠ 0)
    (hchild : ∀ x ∈ source, (initialChild x).2.1 ∈ labels ∧ (initialChild x).2.2 ∈ rows)
    (w : InitialTuple J → ℝ) (hw0 : ∀ x ∈ source, 0 ≤ w x) (hw1 : ∀ x ∈ source, w x ≤ 1)
    (F G : InitialChild → ℂ) (H : ℝ) (hH : 0 < H) :
    ‖∑ x ∈ source, (w x : ℂ) * F (initialChild x) * star (G (initialChild x))‖ ≤
      H * (Real.sqrt (H⁻¹ * initialPositiveEnergy source labels rows F) *
        Real.sqrt (H⁻¹ * initialPositiveEnergy source labels rows G)) := by
  apply (initial_weighted_count source hsource labels rows hlabels hchild w hw0 hw1 F G).trans_eq
  rw [Real.sqrt_mul (inv_nonneg.mpr hH.le), Real.sqrt_mul (inv_nonneg.mpr hH.le)]
  have hc : H * (Real.sqrt H⁻¹) ^ 2 = 1 := by
    rw [Real.sq_sqrt (inv_nonneg.mpr hH.le), mul_inv_cancel₀ hH.ne']
  calc
    _ = (H * (Real.sqrt H⁻¹) ^ 2) *
        (Real.sqrt (initialPositiveEnergy source labels rows F) *
          Real.sqrt (initialPositiveEnergy source labels rows G)) := by rw [hc, one_mul]
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0505

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic
Source SHA256: c146a25cbcc2429c7b1cf9c70c8fcb0953d84bddb5f043d6fbefb25c5b17ce63
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0506



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open MixedCrossSeparation (columnCoefficient)
open SevenEighths.InverseMoment SevenEighths.InverseInitialFibers
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀∉Ideal.span {p i})

def initialColumn (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏ i∈S,p i) *
    rowCoprimeMask (fun i=>Ideal.span {p i}) S (j*C) *
    star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S d) *
    finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S h * H S

theorem initialColumn_eq_secondPre (Ψ : O →* ℂ) (j C d h : O)
    (H : Finset ι→ℂ) (S : Finset ι) :
    initialColumn p hp hcop hg Ψ j C d h H S =
      secondPreColumn p hp hcop hg Ψ (j*C) 1 1 d h H S := by
  have hone := ActualEisensteinCubic.finiteSquarefreeRow_one (fun i=>Ideal.span {p i}) hg S
  simp only [initialColumn,secondPreColumn,hone,one_pow,mul_one]

theorem initial_common_extraction (hpr : ∀ i,λ₀^2∣p i-1)
    (Ψ : O →* ℂ) (j t d h : O) (H : Finset ι→ℂ)
    (V N : Finset ι) (hVN : Disjoint V N) :
    initialColumn p hp hcop hg Ψ j (d*t) d h H (V∪N) =
      initialColumn p hp hcop hg Ψ j (d*t) d h (fun _=>1) V *
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>H (V∪U)) N := by
  simp only [initialColumn_eq_secondPre]
  simpa only [one_mul] using secondPreColumn_union p hp hcop hg hpr Ψ j t 1 1 d h H V N hVN

theorem initial_marked_child (F V A : Finset ι) (Ψ : O →* ℂ) (j t d h : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X : ℝ) :
    (∑ N∈(F\V).powerset,
      secondChildColumn p hp hcop hg Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (fun U=>primeMark slots lists a (A∪V∪U)*
          W (primeProductNorm p (V∪U)/X)) N) =
    ∑ J∈slots.powerset,primeMark J lists a (A∪V)*
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (j*t) (d*∏ i∈V,p i) (d*h)
        (slots\J) (fun i=>lists i\A) a W (X/primeProductNorm p V) := by
  simpa only [secondChildSum,one_mul,←Finset.union_assoc] using
    secondChildSum_marked_fixed_pool p hp hcop hg F V A Ψ j t 1 1 d h slots lists a W X

theorem initial_input_row (F : Finset ι) (Ψ : O →* ℂ) (j : O)
    (H : Finset ι→ℂ) (z : O) :
    inputConjugateRow p hg F Ψ j 1 1 H z =
      FirstCauchyArithmetic.supportConjugateSum (fun i=>Ideal.span {p i}) hg F
        (fun S=>Ψ (∏ i∈S,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) S j*H S) z := by
  unfold inputConjugateRow
  congr 1
  funext S
  have hone := ActualEisensteinCubic.finiteSquarefreeRow_one (fun i=>Ideal.span {p i}) hg S
  simp only [secondInputCoefficient,hone,one_pow,mul_one]

def sourceIdeal (S : Finset ι) : Ideal O := Ideal.span {∏ i∈S,p i}

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_ne_zero (S : Finset ι) : sourceIdeal p S≠0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_union (S T : Finset ι) (hst : Disjoint S T) :
    sourceIdeal p (S∪T)=sourceIdeal p S*sourceIdeal p T := by
  simp only [sourceIdeal,Finset.prod_union hst,Ideal.span_singleton_mul_span_singleton]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_gen (hpr : ∀ i,λ₀^2∣p i-1) (S : Finset ι) :
    primaryGenerator (sourceIdeal p S)=∏ i∈S,p i := by
  apply primaryGenerator_span _ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have he : p i*(∏ j∈S,p j)-1=(p i-1)*(∏ j∈S,p j)+((∏ j∈S,p j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left (hpr i) _) ih

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_dvd (E G : Finset ι) (hEG : E⊆G) : sourceIdeal p E∣sourceIdeal p G := by
  refine ⟨sourceIdeal p (G\E),?_⟩
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]

def sourcePrime (i : ι) : SmoothMobiusCorrection.PrimeIdeal :=
  ⟨Ideal.span {p i},Ideal.prime_of_isPrime (NeZero.ne _) inferInstance⟩

def sourceTuple {J : ℕ} (G E V : Finset ι) (h : O) (assigned : Fin J→ι) : InitialTuple J :=
  ⟨sourceIdeal p G,sourceIdeal p E,sourceIdeal p V,h,fun i=>sourcePrime p (assigned i)⟩

omit [DecidableEq ι] in
theorem source_prime_dvd (S : Finset ι) (i : ι) (hi : i∈S) :
    (sourcePrime p i).val∣sourceIdeal p S := by
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact Finset.dvd_prod_of_mem p hi

include hp in

theorem sourceTuple_valid (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (G E V : Finset ι) (h : O) (assigned : Fin J→ι)
    (hEG : E⊆G) (ha : ∀ i,assigned i∈G∪V) :
    InitialSourceValid (sourceTuple p G E V h assigned) := by
  refine ⟨sourceIdeal_ne_zero p hp G,sourceIdeal_ne_zero p hp V,?_,
    sourceIdeal_dvd p E G hEG,?_⟩
  · change primaryGenerator (sourceIdeal p E)≠0
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  · intro i
    change (sourcePrime p (assigned i)).val∣sourceIdeal p G*sourceIdeal p V
    rcases Finset.mem_union.mp (ha i) with hi|hi
    · exact dvd_mul_of_dvd_left (source_prime_dvd p G (assigned i) hi) _
    · exact dvd_mul_of_dvd_right (source_prime_dvd p V (assigned i) hi) _

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem source_quotient (G E : Finset ι) (hEG : E⊆G) :
    CanonicalQuadraticSieve.idealQuotient (sourceIdeal p E) (sourceIdeal p G)=
      sourceIdeal p (G\E) := by
  apply mul_left_cancel₀ (sourceIdeal_ne_zero p hp E)
  rw [CanonicalQuadraticSieve.idealQuotient_mul (sourceIdeal_dvd p E G hEG)]
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]

include hp in

theorem source_child (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (G E V : Finset ι) (h : O) (assigned : Fin J→ι) (hEG : E⊆G) :
    initialChild (sourceTuple p G E V h assigned)=
      (sourceIdeal p (G\E),sourceIdeal p E*sourceIdeal p V,(∏ i∈E,p i)*h) := by
  simp only [initialChild,sourceTuple,source_quotient p hp G E hEG,sourceIdeal_gen p hp hpr E]

theorem initial_pair_children
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (j t d h₁ h₂ : O) (H₁ H₂ : Finset ι→ℂ) :
    (∑ S∈F.powerset,∑ T∈F.powerset,if Disjoint S T then
      star (initialColumn p hp hcop hg Ψ₁ j (d*t) d h₁ H₁ S)*
        initialColumn p hp hcop hg Ψ₂ j (d*t) d h₂ H₂ T else 0) =
    ∑ V∈F.powerset,
      (FirstCauchyArithmetic.supportMobius (fun i=>Ideal.span {p i}) V *
        star (initialColumn p hp hcop hg Ψ₁ j (d*t) d h₁ (fun _=>1) V)*
          initialColumn p hp hcop hg Ψ₂ j (d*t) d h₂ (fun _=>1) V) *
        star (∑ N∈(F\V).powerset,secondChildColumn p hp hcop hg Ψ₁
          (j*t) (d*∏ i∈V,p i) (d*h₁) (fun U=>H₁ (V∪U)) N) *
        (∑ N∈(F\V).powerset,secondChildColumn p hp hcop hg Ψ₂
          (j*t) (d*∏ i∈V,p i) (d*h₂) (fun U=>H₂ (V∪U)) N) := by
  simp only [initialColumn_eq_secondPre]
  simpa only [secondSeparatedPair,secondCommonWeight,secondChildSum,one_mul] using
    secondSeparatedPair_eq_children p hp hcop hg hinj hpr F Ψ₁ Ψ₂ j t 1 1 d h₁ h₂ H₁ H₂

theorem initial_scalar_self_pair
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i})≠2)
    (Ψ : O →* ℂ) (j C d h : O) (V : Finset ι)
    (hΨ : ‖Ψ (∏ i∈V,p i)‖=1) :
    star (initialColumn p hp hcop hg Ψ j C d h (fun _=>1) V)*
      initialColumn p hp hcop hg Ψ j C d h (fun _=>1) V =
      rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C)*
        rowCoprimeMask (fun i=>Ideal.span {p i}) V d *
        rowCoprimeMask (fun i=>Ideal.span {p i}) V h := by
  have hcol := columnCoefficient_mul_star p hp hcop hg hc V
  have hphase : Ψ (∏ i∈V,p i)*star (Ψ (∏ i∈V,p i))=1 := by
