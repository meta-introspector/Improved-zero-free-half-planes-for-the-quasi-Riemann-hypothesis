    ((elementNorm r.2/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
      lowAdditiveCoefficient C W1 Y r.1 r.2 v

lemma calibration_elementNorm_pos (C : CalibrationData) : 0<elementNorm C.generator := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))

lemma lowPhysicalScale_pos (C : CalibrationData) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    0<lowPhysicalScale C X Y := mul_pos (mul_pos (calibration_elementNorm_pos C) hX) hY

lemma lowAdditiveCoefficient_outer_zero (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) (h : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0) :
    lowAdditiveCoefficient C W1 Y s m v=0 := by
  unfold lowAdditiveCoefficient
  split_ifs <;> simp [h]

lemma lowRowMellinIntegrand_nonzero_form (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (hY : 0<Y) (r : PhysicalRowIndex) (v : ℝ)
    (hc : ∀P∈C.excluded,¬P∣r.1.val) :
    lowRowMellinIntegrand C W0 W1 Ω X Y r v=
      ((Y:ℂ)⁻¹*W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*idealRowHom C.generator r.1.val/
        (C.tau*C.residueMonoid (primaryGenerator r.1.val))*
          (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ))*
          (Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
          sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2)*
          Ω (elementNorm r.2/lowPhysicalScale C X Y)*C.residueMonoid r.2)*
        (((elementNorm r.2/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W0 ((v:ℂ)*Complex.I)) := by
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  have hqc : (((Ideal.absNorm r.1.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (div_pos hq hY).ne'
  unfold lowRowMellinIntegrand lowAdditiveCoefficient
  rw [ite_eq_left hc]
  dsimp only
  rw [Complex.cpow_add _ _ hqc]
  ring

lemma lowRowMellinIntegrand_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hΩ : Ω 0=0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (r : PhysicalRowIndex) : Integrable (lowRowMellinIntegrand C W0 W1 Ω X Y r) := by
  by_cases hm : r.2=0
  · have he : lowRowMellinIntegrand C W0 W1 Ω X Y r=0 := by
      funext v
      simp [lowRowMellinIntegrand,hm,elementNorm,hΩ]
    rw [he]
    exact integrable_zero _ _ _
  by_cases hc : ∀P∈C.excluded,¬P∣r.1.val
  · have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
    have hmpos : 0<elementNorm r.2 := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
    change Integrable (fun v : ℝ=>lowRowMellinIntegrand C W0 W1 Ω X Y r v)
    simp_rw [lowRowMellinIntegrand_nonzero_form C W0 W1 Ω X Y hY r _ hc]
    exact (low_mellin_ratio_integrable W0 a0 b0 ha0 hW0 hWs _ _
      (div_pos hmpos (lowPhysicalScale_pos C X Y hX hY)) (div_pos hq hY)).const_mul _
  · have he : lowRowMellinIntegrand C W0 W1 Ω X Y r=0 := by
      funext v
      simp [lowRowMellinIntegrand,lowAdditiveCoefficient,hc]
    rw [he]
    exact integrable_zero _ _ _

theorem physicalRowWeight_low_mellin (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowRowMellinIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y r v := by
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  have hΩ : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  by_cases hm : r.2=0
  · have hw : W0 0=0 := by
      by_contra hh
      have hx := (hW0 hh).1
      linarith
    simp [physicalRowWeight,lowRowMellinIntegrand,hm,elementNorm,hw,hΩ,Ω]
  by_cases hc : ∀P∈C.excluded,¬P∣r.1.val
  · have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
    have hmpos : 0<elementNorm r.2 := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
    rw [physicalRowWeight_insert_cutoff C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y hY r]
    unfold physicalRowWeight lowRowMellinIntegrand lowAdditiveCoefficient lowPhysicalScale
    dsimp only
    simp only [ite_eq_left hc]
    have hh := physical_radial_low_mellin W0 a0 b0 ha0 hW0 hWs
      (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2)
      (calibration_elementNorm_pos C) hq hX hY hmpos

    calc
      _ = (Ω (elementNorm r.2/(elementNorm C.generator*X*Y))*(Y:ℂ)⁻¹*
        W1 ((Ideal.absNorm r.1.val:ℝ)/Y)*idealRowHom C.generator r.1.val*
        (C.tau*C.residueMonoid (primaryGenerator r.1.val))⁻¹*C.residueMonoid r.2*
        (Real.sqrt (Ideal.absNorm r.1.val):ℂ)⁻¹*
        sexticGauss (primaryGenerator r.1.val) (supported_primaryGenerator_ne_zero r.1.val r.1.property) (-r.2))*
        ((Real.sqrt (elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X):ℂ)⁻¹*
          W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))) := by dsimp only [Ω]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
      _ = _ := by
        rw [hh]
        repeat rw [←integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun v=>by dsimp only [Ω]; ring)
  · simp [physicalRowWeight,lowRowMellinIntegrand,lowAdditiveCoefficient,hc]

lemma lowAdditiveCoefficient_height (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    lowAdditiveCoefficient C W1 Y s m v=
      (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*lowAdditiveCoefficient C W1 Y s m 0 := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  have hqc : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (div_pos hq hY).ne'
  unfold lowAdditiveCoefficient
  split_ifs
  · dsimp only
    rw [Complex.cpow_add _ _ hqc]
    simp only [Complex.ofReal_zero,zero_mul,add_zero]
    ring
  · simp

lemma lowAdditiveCoefficient_height_norm (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    ‖lowAdditiveCoefficient C W1 Y s m v‖=‖lowAdditiveCoefficient C W1 Y s m 0‖ := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  rw [lowAdditiveCoefficient_height C W1 Y hY s m v,norm_mul,
    low_mellin_phase_norm _ v (div_pos hq hY),one_mul]

def lowArithmeticCoefficient (C : CalibrationData) (s : {I : Id // Supported I}) : ℂ :=
  if ∀P∈C.excluded,¬P∣s.val then
    idealRowHom C.generator s.val/(C.tau*C.residueMonoid (primaryGenerator s.val))
  else 0

lemma calibration_residue_inverse_norm (C : CalibrationData) (a : O) : ‖(C.residueMonoid a)⁻¹‖≤1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  change ‖(C.residue (Ideal.Quotient.mk (Ideal.span {C.generator}) a))⁻¹‖≤1
  simpa only [MulChar.inv_apply_eq_inv'] using
    FiniteRayExpansion.norm_char_le_one C.residue⁻¹ (Ideal.Quotient.mk (Ideal.span {C.generator}) a)

lemma lowArithmeticCoefficient_norm (C : CalibrationData) (s : {I : Id // Supported I}) :
    ‖lowArithmeticCoefficient C s‖≤‖C.tau‖⁻¹ := by
  unfold lowArithmeticCoefficient
  split_ifs
  · simp only [div_eq_mul_inv,mul_inv_rev,norm_mul,norm_inv]
    have hi := calibration_residue_inverse_norm C (primaryGenerator s.val)
    rw [norm_inv] at hi
    have hh := (mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg _)) (idealRowHom_norm C.generator s.val)).trans hi
    simpa only [mul_assoc] using mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg C.tau)) hh
  · simp

lemma lowArithmeticCoefficient_source_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (s : {I : Id // Supported I}) : ‖lowArithmeticCoefficient (calibrationForSet S hS) s‖≤1 := by
  simpa only [calibrationForSet_tau_norm,inv_one] using lowArithmeticCoefficient_norm (calibrationForSet S hS) s

lemma lowAdditiveCoefficient_eq (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) :
    lowAdditiveCoefficient C W1 Y s m v=
      (Y:ℂ)⁻¹*W1 ((Ideal.absNorm s.val:ℝ)/Y)*lowArithmeticCoefficient C s*
        (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
          (Real.sqrt (Ideal.absNorm s.val):ℂ)⁻¹*
            sexticGauss (primaryGenerator s.val) (supported_primaryGenerator_ne_zero s.val s.property) (-m) := by
  unfold lowAdditiveCoefficient lowArithmeticCoefficient
  split_ifs <;> simp only [mul_zero,zero_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1255

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowMellinFubini
Source SHA256: 4035f4dc914b859f298ed9cdc73428b17eac3e8da7229e24357ada789f837ee0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1256


namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowRowMellinIntegrand_common_support (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset PhysicalRowIndex,∀v : ℝ,∀r∉R,
      lowRowMellinIntegrand C W0 W1 Ω X Y r v=0 := by
  have hs := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  have hm := elementWindow_finite_support Ω hΩ _ (lowPhysicalScale_pos C X Y hX hY)
  refine ⟨hs.toFinset×ˢhm.toFinset,?_⟩
  intro v r hr
  simp only [Finset.mem_product,Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support] at hr
  by_cases h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0
  · unfold lowRowMellinIntegrand
    rw [lowAdditiveCoefficient_outer_zero C W1 Y r.1 r.2 v h,mul_zero]
  · have ho : Ω (elementNorm r.2/lowPhysicalScale C X Y)=0 := by
      by_contra ho
      exact hr ⟨h,ho⟩
    simp [lowRowMellinIntegrand,ho]

lemma lowRowMellinIntegrand_mul_summable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (v : ℝ) (B : PhysicalRowIndex→ℂ) :
    Summable (fun r=>lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r) := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  apply summable_of_ne_finset_zero (s:=R)
  intro r hr
  rw [hR v r hr,zero_mul]

lemma lowRowMellinIntegrand_sum_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    Integrable (fun v : ℝ=>∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r) := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  have he (v : ℝ) : (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∑r∈R,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
    apply tsum_eq_sum
    intro r hr
    rw [hR v r hr,zero_mul]
  simp_rw [he]
  exact integrable_finsetSum R (fun r _=>(lowRowMellinIntegrand_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hΩ0 X Y hX hY r).mul_const _)

lemma lowRowMellinIntegrand_tsum_integral (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    (∑'r : PhysicalRowIndex,∫v : ℝ,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∫v : ℝ,∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
  obtain ⟨R,hR⟩ := lowRowMellinIntegrand_common_support C W0 W1 Ω hW1 hΩ X Y hX hY
  have he (v : ℝ) : (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r)=
      ∑r∈R,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B r := by
    apply tsum_eq_sum
    intro r hr
    rw [hR v r hr,zero_mul]
  rw [tsum_eq_sum (s:=R) (fun r hr=>by simp only [hR _ r hr,zero_mul,integral_zero])]
  simp_rw [he]
  exact (integral_finsetSum R (fun r _=>(lowRowMellinIntegrand_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hΩ0 X Y hX hY r).mul_const _)).symm

theorem physicalRowWeight_tsum_low_mellin (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : PhysicalRowIndex→ℂ) :
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*B r)=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,∑'r : PhysicalRowIndex,
          lowRowMellinIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y r v*B r := by
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  have hΩ : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  simp_rw [physicalRowWeight_low_mellin C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY]
  simp_rw [mul_assoc,←integral_mul_const]
  repeat rw [tsum_mul_left]
  congr 2
  exact lowRowMellinIntegrand_tsum_integral C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩ hΩ0 X Y hX hY B

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1256

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowRayAmplitude
Source SHA256: 7c2aedb44bc9cf4048d6a788d992168443a27b58e73e16160d5f50db0c1547d4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1257


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowRayAmplitude (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (m : O) (v : ℝ) : ℂ :=
  ∑'s : {I : Id // Supported I},if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0

lemma lowAdditiveCoefficient_common_support (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀m : O,∀v : ℝ,∀s∉F,
      lowAdditiveCoefficient C W1 Y s m v=0 := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  refine ⟨ho.toFinset,?_⟩
  intro m v s hs
  apply lowAdditiveCoefficient_outer_zero
  simpa only [Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support,not_not] using hs

lemma lowAdditiveCoefficient_mul_summable (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (m : O) (v : ℝ)
    (F : {I : Id // Supported I}→ℂ) :
    Summable (fun s=>lowAdditiveCoefficient C W1 Y s m v*F s) := by
  obtain ⟨R,hR⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  apply summable_of_ne_finset_zero (s:=R)
  intro s hs
  rw [hR m v s hs,zero_mul]

lemma lowRayAmplitude_eq_finite (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀σ : RayRing,∀m : O,∀v : ℝ,
      lowRayAmplitude C W1 Y σ m v=
        ∑s∈F,if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0 := by
  obtain ⟨F,hF⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  refine ⟨F,?_⟩
  intro σ m v
  apply tsum_eq_sum
  intro s hs
  simp only [hF m v s hs,ite_self]

lemma lowRayAmplitude_group (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (m : O) (v : ℝ)
    (B : RayRing→ℂ) :
    (∑'s : {I : Id // Supported I},lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s))=
      ∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ := by
  obtain ⟨F,hF⟩ := lowAdditiveCoefficient_common_support C W1 hW1 Y hY
  have hleft : (∑'s : {I : Id // Supported I},lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s))=
      ∑s∈F,lowAdditiveCoefficient C W1 Y s m v*B (physicalIdealRay s) := by
    apply tsum_eq_sum
    intro s hs
    rw [hF m v s hs,zero_mul]
  have hr (σ : RayRing) : lowRayAmplitude C W1 Y σ m v=
      ∑s∈F,if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0 := by
    apply tsum_eq_sum
    intro s hs
    simp only [hF m v s hs,ite_self]
  rw [hleft]
  simp_rw [hr,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [ite_mul,zero_mul]
  simp

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1257

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowSeparated
Source SHA256: 0cd344ff44c0b4db181ba658a3589a4368cfdae6d4205a439b7204e60dda18b2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1258



namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowSeparatedIntegrand (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (B : RayRing→O→ℂ) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I)*
    ∑'m : O,Ω (elementNorm m/lowPhysicalScale C X Y)*C.residueMonoid m*
      ((elementNorm m/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
        ∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m

lemma lowSeparatedIntegrand_eq (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) (v : ℝ) :
    (∑'r : PhysicalRowIndex,lowRowMellinIntegrand C W0 W1 Ω X Y r v*B (physicalIdealRay r.1) r.2)=
      lowSeparatedIntegrand C W0 W1 Ω X Y B v := by
  have hs := lowRowMellinIntegrand_mul_summable C W0 W1 Ω hW1 hΩ X Y hX hY v
    (fun r=>B (physicalIdealRay r.1) r.2)
  rw [hs.tsum_prod,←hs.tsum_comm]
  unfold lowSeparatedIntegrand
  rw [←tsum_mul_left]
  apply tsum_congr
  intro m
  rw [←lowRayAmplitude_group C W1 hW1 Y hY m v (fun σ=>B σ m)]
  repeat rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  unfold lowRowMellinIntegrand
  ring

lemma lowSeparatedIntegrand_integrable (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    Integrable (lowSeparatedIntegrand C W0 W1 Ω X Y B) := by
  have hh := lowRowMellinIntegrand_sum_integrable C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1 hΩ hΩ0 X Y hX hY
    (fun r=>B (physicalIdealRay r.1) r.2)
  simpa only [lowSeparatedIntegrand_eq C W0 W1 Ω hW1 hΩ X Y hX hY B] using hh

theorem physicalRowWeight_low_separated (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*B (physicalIdealRay r.1) r.2)=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y B v := by
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩ := lowOuterCutoff_compact (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  rw [physicalRowWeight_tsum_low_mellin C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY]
  simp_rw [lowSeparatedIntegrand_eq C W0 W1 _ hW1c hΩ X Y hX hY B]

theorem markedPhysicalProbe_low_separated (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      (Real.sqrt (lowPhysicalScale C X Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand C W0 W1 (lowOuterCutoff (a0*a1) (max 1 (b0*b1))) X Y
          (fun σ m=>correctedCompletedT C.excluded D (physicalRayRowMonoid η C σ m) gaussianCompletedProfile Z) v := by
  have hW0c : HasCompactSupport W0 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  rw [markedPhysicalProbe_eq_gaussian_rows η C D W0 W1 hW0c hW1c X Y Z hX hY hZ]
  simp_rw [physicalRowMonoid_eq_ray]
  exact physicalRowWeight_low_separated C W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs X Y hX hY
    (fun σ m=>correctedCompletedT C.excluded D (physicalRayRowMonoid η C σ m) gaussianCompletedProfile Z)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1258

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowCompensation
Source SHA256: 72434463a783cf5d62f4d1014cb3df31431ce0a87522cc6c887caf78fc084c8a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1259



namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted CanonicalRowCompletion RayFourExpansion ProbeRow CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowMarkedInverseRow (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (D : Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑χ : RayCharacter,correctionCoeff χ*
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
      (fun A=>if D∣A then (1:ℂ) else 0)

lemma lowMarkedInverseRow_eq (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (D : Id) (T t : ℝ) (hT : 0<T)
    (σ : RayRing) (m : O) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
        lowMarkedInverseRow η S hS D T t σ m :=
  physicalRayRow_eq_periodic_inverse η S hS hbad σ m D _ (gaussianFixedWindow_twist_compact t) T hT

theorem compensationRowTest_low_separated {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    compensationRowTest η (calibrationForSet S hS) W0 W1 p J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
          (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t) v := by
  unfold compensationRowTest
  simp_rw [physicalRowMonoid_eq_ray]
  have hC : (calibrationForSet S hS).excluded=S := calibrationForSet_excluded S hS
  rw [hC]
  simp_rw [lowMarkedInverseRow_eq η S hS hbad _ T t hT]
  exact physicalRowWeight_low_separated (calibrationForSet S hS) W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hWs _ _ (div_pos hX (slotProduct_norm_pos p hp J))
      (div_pos hY (slotProduct_norm_pos p hp J))
      (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)

lemma compensationRowTest_low_integrable {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) :
    Integrable (lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
      (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (lowMarkedInverseRow η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)) := by
  exact lowSeparatedIntegrand_integrable (calibrationForSet S hS) W0 W1 _ a0 b0 ha0 hW0 hWs
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    (lowOuterCutoff_compact _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
    (lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)) _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J)) _

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1259

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowSelectedSum
Source SHA256: 8992273342b3dc16026d48068d2f7e0f148a5214e0327b9f9d36405aa33e543e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1260


namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowSeparatedIntegrand_finite_sum {α : Type*} (F : Finset α) (c : α→ℂ)
    (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ) (hW1 : HasCompactSupport W1) (hΩ : HasCompactSupport Ω)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : α→RayRing→O→ℂ) (v : ℝ) :
    (∑k∈F,c k*lowSeparatedIntegrand C W0 W1 Ω X Y (B k) v)=
      lowSeparatedIntegrand C W0 W1 Ω X Y (fun σ m=>∑k∈F,c k*B k σ m) v := by
  simp_rw [←lowSeparatedIntegrand_eq C W0 W1 Ω hW1 hΩ X Y hX hY]
  simp_rw [←tsum_mul_left]
  rw [←Summable.tsum_finsetSum (fun k _=>
    (lowRowMellinIntegrand_mul_summable C W0 W1 Ω hW1 hΩ X Y hX hY v
      (fun r=>B k (physicalIdealRay r.1) r.2)).mul_left (c k))]
  apply tsum_congr
  intro r
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma lowSeparatedIntegral_finite_sum {α : Type*} (F : Finset α) (c : α→ℂ)
    (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (a0 b0 : ℝ) (ha0 : 0<a0) (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hWs : ContDiff ℝ ∞ W0) (hW1 : HasCompactSupport W1)
    (hΩ : HasCompactSupport Ω) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : α→RayRing→O→ℂ) :
    (∑k∈F,c k*∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω X Y (B k) v)=
      ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω X Y (fun σ m=>∑k∈F,c k*B k σ m) v := by
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum F (fun k _=>(lowSeparatedIntegrand_integrable C W0 W1 Ω
    a0 b0 ha0 hW0 hWs hW1 hΩ hΩ0 X Y hX hY (B k)).const_mul (c k))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun v=>lowSeparatedIntegrand_finite_sum F c C W0 W1 Ω hW1 hΩ X Y hX hY B v)

def lowSelectedInverseRow {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑k∈F,c k*lowMarkedInverseRow η S hS (D k) T t σ m

lemma lowSelectedInverseRow_correction {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→Id) (T t : ℝ) (σ : RayRing) (m : O) :
    lowSelectedInverseRow F c η S hS D T t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        ∑k∈F,c k*InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
          (fun A=>if D k∣A then (1:ℂ) else 0) := by
  unfold lowSelectedInverseRow lowMarkedInverseRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro k hk
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1260

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowSlotSplit
Source SHA256: 6d38232a49b27e4de08952f55405cafbf331921e753c200f1735464d38e7566f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1261


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

abbrev LowUnselectedTuple {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :=
  ∀i : J,↥(slots i.val)
abbrev LowSelectedTuple {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :=
  ∀i : SelectedSlot J,↥(slots i.val)

def lowSlotTupleEquiv {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K)) :
    (∀i,↥(slots i)) ≃ LowUnselectedTuple slots J×LowSelectedTuple slots J where
  toFun p := (fun i=>p i.val,fun i=>p i.val)
  invFun p i := if hi : i∈J then p.1 ⟨i,hi⟩ else p.2 ⟨i,by simp [hi]⟩
  left_inv p := by
    funext i
    dsimp only
    split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [dite_eq_left i.property]
    · funext i
      have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
      simp only [dite_eq_right hi]

def lowSlotJoin {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) : Fin K→O :=
  fun i=>((lowSlotTupleEquiv slots J).symm (a,b) i).val

lemma lowSlotJoin_nonzero {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : Fin K) :
    lowSlotJoin slots J a b i≠0 := hslots i _ ((lowSlotTupleEquiv slots J).symm (a,b) i).property

lemma lowSlotJoin_unselected {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : J) :
    lowSlotJoin slots J a b i.val=(a i).val := by
  simp only [lowSlotJoin,lowSlotTupleEquiv,Equiv.coe_fn_symm_mk,dite_eq_left i.property]

lemma lowSlotJoin_selected {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) (i : SelectedSlot J) :
    lowSlotJoin slots J a b i.val=(b i).val := by
  have hi : i.val∉J := (Finset.mem_sdiff.mp i.property).2
  simp only [lowSlotJoin,lowSlotTupleEquiv,Equiv.coe_fn_symm_mk,dite_eq_right hi]

lemma lowSlotJoin_unselectedProduct {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    slotProduct (lowSlotJoin slots J a b) J=∏i : J,(a i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort J]
  simp only [lowSlotJoin_unselected]

lemma lowSlotJoin_selectedProduct {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    slotProduct (lowSlotJoin slots J a b) (Finset.univ\J)=∏i : SelectedSlot J,(b i).val := by
  unfold slotProduct
  rw [←Finset.prod_coe_sort (Finset.univ\J)]
  simp only [lowSlotJoin_selected]

lemma lowSlotJoin_selectedFactor {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ) :
    selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
      ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
        FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val)) := by
  unfold selectedSlotFactor
  simp only [lowSlotJoin_selected]

theorem sum_lowSlotJoin {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(slots i)),F (fun i=>(p i).val))=
      ∑a : LowUnselectedTuple slots J,∑b : LowSelectedTuple slots J,F (lowSlotJoin slots J a b) := by
  calc
    _ = ∑p : LowUnselectedTuple slots J×LowSelectedTuple slots J,F (lowSlotJoin slots J p.1 p.2) :=
      (Equiv.sum_comp (lowSlotTupleEquiv slots J).symm (fun p=>F (fun i=>(p i).val))).symm
    _ = _ := Fintype.sum_prod_type _

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1261

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowSlotPolynomial
Source SHA256: 9ae3f903bfe58745d2bd4664b34fafd1dd4bb92eb32993dcc9d89b2ce120246e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1262


namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowUnselectedWeight {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (a : LowUnselectedTuple slots J) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (∏i : J,(a i).val)^(-(3/2:ℝ)):ℝ):ℂ)*
    ∏i : J,W i.val (elementNorm (a i).val/P i.val)

def lowSelectedWeight {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) : ℂ :=
  star (HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(b i).val))*
    ∏i : SelectedSlot J,W i.val (elementNorm (b i).val/P i.val)*
      FourierBridge.logPhase (-t) (Real.log (elementNorm (b i).val/P i.val))

def lowSelectedIdeal {K : ℕ} (slots : Fin K→Finset O) (J : Finset (Fin K))
    (b : LowSelectedTuple slots J) : Id := Ideal.span {∏i : SelectedSlot J,(b i).val}

lemma lowSlotJoin_weight {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    compensationSubsetWeight η W P (lowSlotJoin slots J a b) J*
      selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
        lowUnselectedWeight slots J W P a*lowSelectedWeight η slots J W P t b := by
  unfold compensationSubsetWeight compensationSubsetCoefficient
  rw [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct,lowSlotJoin_selectedFactor]
  rw [←Finset.prod_coe_sort J (fun i=>W i (elementNorm (lowSlotJoin slots J a b i)/P i))]
  simp only [lowSlotJoin_unselected]
  unfold lowUnselectedWeight lowSelectedWeight
  ring

lemma lowUnselectedProduct_norm_pos {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    0<elementNorm (∏i : J,(a i).val) := by
  apply physicalElementNorm_pos
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>hslots i.val _ (a i).property)

lemma compensationRowTest_join_low {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    compensationRowTest η (calibrationForSet S hS) W0 W1 (lowSlotJoin slots J a b) J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v := by
  simpa only [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct,lowSelectedIdeal] using
    compensationRowTest_low_separated η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
      (lowSlotJoin slots J a b) (lowSlotJoin_nonzero slots hslots J a b) J X Y T t hX hY hT

theorem compensation_tuple_low_polynomial {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→Finset O) (hslots : ∀i x,x∈slots i→x≠0)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (X Y T t : ℝ) (hX : 0<X) (hY : 0<Y) (hT : 0<T) :
    (∑p : (∀i,↥(slots i)),compensationSubsetWeight η W P (fun i=>(p i).val) J*
      compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y T t*
        selectedSlotFactor W P (fun i=>(p i).val) J t)=
      ∑a : LowUnselectedTuple slots J,lowUnselectedWeight slots J W P a*
        ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
          ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
            (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
            (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
            (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
              η S hS (lowSelectedIdeal slots J) T t) v := by
  rw [sum_lowSlotJoin slots J (fun p=>compensationSubsetWeight η W P p J*
    compensationRowTest η (calibrationForSet S hS) W0 W1 p J X Y T t*selectedSlotFactor W P p J t)]
  apply Finset.sum_congr rfl
  intro a ha
  let L := elementNorm (∏i : J,(a i).val)
  have hL : 0<L := lowUnselectedProduct_norm_pos slots hslots J a
  let C := calibrationForSet S hS
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  let N : ℂ := (Real.sqrt (lowPhysicalScale C (X/L) (Y/L)):ℂ)⁻¹*(1/(2*Real.pi):ℂ)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩc : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  calc
    _ = lowUnselectedWeight slots J W P a*N*
        ∑b : LowSelectedTuple slots J,lowSelectedWeight η slots J W P t b*
          ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω (X/L) (Y/L)
            (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [compensationRowTest_join_low η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
        slots hslots J a b X Y T t hX hY hT]
      have hw := lowSlotJoin_weight η slots J W P t a b
      dsimp only [C,Ω,L,N]
      linear_combination (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*
        (1/(2*Real.pi):ℂ)*(∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (lowMarkedInverseRow η S hS (lowSelectedIdeal slots J b) T t) v)*hw
    _ = _ := by
      rw [lowSeparatedIntegral_finite_sum Finset.univ (lowSelectedWeight η slots J W P t)
        C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩc hΩ0 (X/L) (Y/L)
        (div_pos hX hL) (div_pos hY hL)]
      rfl

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1262

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowSlotWeights
Source SHA256: ea0501da5e20d644336933979785e1adb5ae43591bc10287d08c720b81ee17d3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1263


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow FourierBridge
local notation "O" => ActualEisensteinCubic.O

def lowSingleSlotWeight (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) : ℂ :=
  star (HeckeFamily.elementCoeff η a)*W (elementNorm a/P)*logPhase (-t) (Real.log (elementNorm a/P))

lemma lowSelectedWeight_eq_product {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    lowSelectedWeight η slots J W P t b=
      ∏i : SelectedSlot J,lowSingleSlotWeight η (W i.val) (P i.val) t (b i).val := by
  have he : HeckeFamily.elementCoeff η (∏i : SelectedSlot J,(b i).val)=
      ∏i : SelectedSlot J,HeckeFamily.elementCoeff η (b i).val := map_prod (targetMonoid η) _ _
  unfold lowSelectedWeight lowSingleSlotWeight
  rw [he,star_prod]
  simp only [Finset.prod_mul_distrib,mul_assoc]

lemma lowSingleSlotWeight_norm (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖≤‖W (elementNorm a/P)‖ := by
  rw [lowSingleSlotWeight,norm_mul,norm_mul,norm_star,logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (targetMonoid_norm_le_one η a)

lemma lowSingleSlotWeight_height_norm (η : HeckeFamily.Character) (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖lowSingleSlotWeight η W P t a‖=‖lowSingleSlotWeight η W P 0 a‖ := by
  simp only [lowSingleSlotWeight,norm_mul,logPhase_norm,mul_one]

lemma lowSelectedWeight_norm {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖≤∏i : SelectedSlot J,‖W i.val (elementNorm (b i).val/P i.val)‖ := by
  rw [lowSelectedWeight_eq_product,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>lowSingleSlotWeight_norm η (W i.val) (P i.val) t (b i).val)

lemma lowSelectedWeight_height_norm {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (t : ℝ)
    (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖=‖lowSelectedWeight η slots J W P 0 b‖ := by
  rw [lowSelectedWeight_eq_product,lowSelectedWeight_eq_product,norm_prod,norm_prod]
  exact Finset.prod_congr rfl (fun i _=>lowSingleSlotWeight_height_norm η (W i.val) (P i.val) t (b i).val)

lemma lowSelectedWeight_norm_le_one {K : ℕ} (η : HeckeFamily.Character) (slots : Fin K→Finset O)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (hW : ∀i x,‖W i x‖≤1) (t : ℝ) (b : LowSelectedTuple slots J) :
    ‖lowSelectedWeight η slots J W P t b‖≤1 :=
  (lowSelectedWeight_norm η slots J W P t b).trans
    (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hW i.val _))

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1263

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SpectralPoisson
Source SHA256: 51cade1ad1cece39d3e1eb3bdbe0c7624bf27195d3a07529a9a3fab333147404
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1264



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def transformedSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (K : ℝ) (t : ℂ) (I J : Ideal O) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
        ∑' H : O, actualCongruenceCoefficient C (completedIndex I J) s hA H *
          paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*completedIndex I J)*s))
  else 0

theorem physical_spectral_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K : ℝ) (hK : 0<K) (t : ℂ) (ht : 1<t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C S D s hs W K t p.1 p.2 := by
  rw [physical_spectral_reopen η C S D s hs W hWc K hK t ht]
  apply tsum_congr
  intro p
  unfold transformedSpectralTerm
  by_cases hA : completedIndex p.1 p.2≠0
  · rw [dite_eq_left hA, physical_row_poisson C (completedIndex p.1 p.2) s hA
      (supportedElement_ne_zero s hs) W hWc hWs K hK]
    ring
  · rw [dite_eq_right hA, spectralSummand_zero_completedIndex S D p.1 p.2 _ t (not_ne_iff.mp hA), zero_mul]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1264

/-! Original module: OAI.NumberTheory.DirichletL.Detector.MellinPoisson
Source SHA256: 547898e89145c23c58df9dfbbcb1401c8264fc177ec874a9c63a1c77bb75e408
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1265


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma finiteSupport_verticalIntegral {α : Type*} (c : α → ℂ)
    (hc : (Function.support c).Finite) (F : α → ℂ → ℂ) (σ : ℝ)
    (hF : ∀ a, Integrable (fun y : ℝ => F a ((σ:ℂ)+y*Complex.I))) :
    verticalIntegral σ (fun t => ∑' a, c a * F a t) =
      ∑' a, c a * verticalIntegral σ (F a) := by
  have hz (a : α) (ha : a∉hc.toFinset) : c a=0 := by
    simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using ha
  have he (t : ℂ) : (∑' a, c a*F a t) = ∑ a∈hc.toFinset, c a*F a t :=
    tsum_eq_sum (fun a ha => by rw [hz a ha, zero_mul])
  rw [tsum_eq_sum (s := hc.toFinset) (fun a ha => by rw [hz a ha, zero_mul])]
  unfold verticalIntegral
  simp_rw [he]
  rw [integral_finsetSum _ (fun a ha => (hF a).const_mul (c a)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_const_mul]
  ring

theorem inner_mellin_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s}))
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (K Z : ℝ) (hK : 0<K) (hZ : 0<Z) :
    (∑' m : O, C.residueMonoid m * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) *
      verticalIntegral 4 (fun t => (Z:ℂ)^t * Complex.exp (t^2) *
        spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) t)) =
    verticalIntegral 4 (fun t => (Real.sqrt (elementNorm s):ℂ)⁻¹ *
      ((Z:ℂ)^t * Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D s hs W K t p.1 p.2) := by
  let c (m : O) := C.residueMonoid m * (Real.sqrt (elementNorm s):ℂ)⁻¹ *
    sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K)
  have hc : (Function.support c).Finite := by
    apply (elementWindow_finite_support W hWc K hK).subset
    intro m hm hz
    exact hm (by simp only [c, hz, mul_zero])
  rw [← finiteSupport_verticalIntegral c hc
    (fun m t => (Z:ℂ)^t * Complex.exp (t^2) *
      spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) t) 4
    (fun m => physicalRow_integrable η C D s hs m Z hZ)]
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  norm_num only [Complex.ofReal_ofNat]
  have ht : 1 < ((4:ℂ)+(y:ℂ)*Complex.I).re := by simp
  rw [← physical_spectral_poisson η C C.excluded D s hs W hWc hWs K hK _ ht,
    ← tsum_mul_left]
  apply tsum_congr
  intro m
  dsimp only [c]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1265

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Transformed
Source SHA256: 60df1fb14e7056098016561e34189118d99f8710309d74cc746091147888dfaa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1266


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def poissonPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  (Y:ℂ)⁻¹ * ∑' s : {I : Ideal O // Supported I},
    if ∀ p∈C.excluded, ¬p∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let q_s : ℝ := Ideal.absNorm s.val
      W₁ (q_s/Y) * CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q_s*X):ℂ)) *
      verticalIntegral 4 (fun t => (Real.sqrt q_s:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2)) *
        ∑' p : Ideal O × Ideal O, transformedSpectralTerm η C C.excluded D a has W₀
          (elementNorm C.generator*q_s*X) t p.1 p.2)
    else 0

theorem markedPhysicalProbe_eq_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W₀ W₁ : ℝ → ℂ) (hWc : HasCompactSupport W₀)
    (hWs : ContDiff ℝ ∞ W₀) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) :
    markedPhysicalProbe η C D W₀ W₁ X Y Z = poissonPhysicalProbe η C D W₀ W₁ X Y Z := by
  unfold markedPhysicalProbe poissonPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with h
  · dsimp only
    congr 1
    have ha := supported_primaryGenerator_ne_zero s.val s.property
    have has := (supported_span_primaryGenerator_iff s.val).mpr s.property
    have hn : elementNorm (primaryGenerator s.val) = (Ideal.absNorm s.val:ℝ) := by
      unfold elementNorm
      rw [(primaryGenerator_spec s.val ha).1]
    have hb : 0<elementNorm C.generator := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
    have hs : 0<(Ideal.absNorm s.val:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
    have hK : 0<elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := mul_pos (mul_pos hb hs) hX
    simpa only [hn] using inner_mellin_poisson η C D (primaryGenerator s.val) has
      W₀ hWc hWs (elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X) Z hK hZ
  · rfl

theorem physicalProbe_eq_poisson (η : HeckeFamily.Character) (C : CalibrationData)
    (W₀ W₁ : ℝ → ℂ) (hWc : HasCompactSupport W₀) (hWs : ContDiff ℝ ∞ W₀)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) :
    physicalProbe η C W₀ W₁ X Y Z = poissonPhysicalProbe η C 1 W₀ W₁ X Y Z :=
  markedPhysicalProbe_eq_poisson η C 1 W₀ W₁ hWc hWs X Y Z hX hZ

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1266

/-! Original module: OAI.NumberTheory.DirichletL.Detector.ZeroIndex
Source SHA256: 49f1b9219781ee95156776336245092a7486c916e4cad1cffdaebceac1530c70
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1267


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]

def zeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(6*m)))) * W^k * V^m

omit [(Ideal.span {p}).IsMaximal] in
lemma zeroIndex_inner_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hV : ‖V‖<1) :
    HasSum (fun m => zeroIndexTerm p χ W V 0 m) (1/(1-V)) := by
  simpa [zeroIndexTerm, one_div] using hasSum_geometric_of_norm_lt_one hV

include hp in
lemma zeroIndex_inner_pos (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (k : ℕ) (hk : k≠0) :
    HasSum (fun m => zeroIndexTerm p χ W V k m) (W^k) := by
  apply (hasSum_ite_eq 0 (W^k)).congr
  intro s
  apply Finset.sum_congr rfl
  intro m hm
  dsimp only
  unfold zeroIndexTerm
  rw [ite_eq_right hk, zero_index_scalar p hp χ k (6*m) hk]
  by_cases h : m=0
  · subst m; simp
  · have h6 : 6*m≠0 := by omega
    simp [h, h6]

def zeroIndexSeries (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) : ℂ :=
  ∑' k, ∑' m, zeroIndexTerm p χ W V k m

include hp in
lemma zeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (hW : ‖W‖<1) (hV : ‖V‖<1) :
    zeroIndexSeries p χ W V = 1/(1-V)+W/(1-W) := by
  have htail : HasSum (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) (W/(1-W)) := by
    have he : (fun k => ∑' m, zeroIndexTerm p χ W V (k+1) m) =
        (fun k => W * W^k) := by
      funext k
      rw [(zeroIndex_inner_pos p hp χ W V (k+1) (by omega)).tsum_eq, pow_succ]
      ring
    rw [he]
    simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hW).mul_left W
  have hall := HasSum.sum_range_add (f := fun k => ∑' m, zeroIndexTerm p χ W V k m) (k := 1) htail
  simpa only [zeroIndexSeries, Finset.sum_range_one,
    (zeroIndex_inner_zero p χ W V hV).tsum_eq] using hall.tsum_eq

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1267

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SourceLocal
Source SHA256: db29a85fc6d3e1c38ce9e8dce9e0f795baa68aa85b9a228c70df9991e0ec54c2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1268



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def sourceScalar (t k j : ℕ) : ℂ :=
  if t=0 then
    if k=0 then 1 else (actualSextic (Ideal.span {p}) hg ^ k) (Ideal.Quotient.mk _ (p^j))
  else positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k j

def sourcePrincipalTerm (eta a x w z : ℂ) (e l k m : ℕ) : ℂ :=
  sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
    (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) x w z
    (sourceScalar p hp hg (e+3*l) k (6*m)) e l k m

lemma sourcePrincipalTerm_pos (eta a x w z : ℂ) (e l k m : ℕ) (ht : e+3*l≠0) :
    sourcePrincipalTerm p hp hg eta a x w z e l k m =
      principalMarkedTerm p hp hg eta a
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) e l k m := by
  unfold sourcePrincipalTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [sourceScalar, ht, ite_false, principalMarkedTerm, coordV, Complex.ofReal_natCast]

lemma sourcePrincipalTerm_zero (eta a x w z : ℂ) (k m : ℕ) :
    sourcePrincipalTerm p hp hg eta a x w z 0 0 k m =
      zeroIndexTerm p (actualSextic (Ideal.span {p}) hg)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) k m := by
  unfold sourcePrincipalTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [weightedScalar, localCubePhase, sourceScalar, zeroIndexTerm, coordV,
    mul_zero, add_zero, pow_zero,  one_mul, zero_mul, Nat.choose_zero_succ,
    ite_true, Complex.ofReal_natCast]

def sourcePrincipalSeries (eta a x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z e.val l k m

include hc in
lemma sourcePrincipalSeries_eq (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourcePrincipalSeries p hp hg eta a x w z =
      principalFullSeries p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) := by
  dsimp only
  simp only [Complex.ofReal_natCast]
  let X : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)
  let W : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)
  let V : ℂ := coordV (Ideal.absNorm (Ideal.span {p})) z
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hr : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1 := by
    have he := evenRatio_eq_coordR _ hQ a x z
    simp only [Complex.ofReal_natCast] at he
    change ‖evenRatio _ a _ _‖<1
    rw [he]
    exact hR
  have hW' : ‖W‖<1 := by simpa only [W, coordW, one_mul, Complex.ofReal_natCast] using hW
  have he : Summable (fun l => principalInner p hp hg eta a X W V 0 l) :=
    (principalInner_even_hasSum p hp hg hc eta a X W V hV hr).summable
  have h0 : (fun l => ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z 0 l k m) =
      (fun l => principalInner p hp hg eta a X W V 0 l +
        if l=0 then zeroIndexSeries p (actualSextic (Ideal.span {p}) hg) W V else 0) := by
    funext l
    by_cases hl : l=0
    · subst l
      simp only [sourcePrincipalTerm_zero, principalInner_zero p hp hg,  ite_true,
        zero_add, zeroIndexSeries, W, V]
    · rw [ite_eq_right hl, add_zero]
      apply tsum_congr
      intro k
      apply tsum_congr
      intro m
      exact sourcePrincipalTerm_pos p hp hg eta a x w z 0 l k m (by omega)
  have h1 : (fun l => ∑' k, ∑' m, sourcePrincipalTerm p hp hg eta a x w z 1 l k m) =
      (fun l => principalInner p hp hg eta a X W V 1 l) := by
    funext l
    apply tsum_congr
    intro k
    apply tsum_congr
    intro m
    exact sourcePrincipalTerm_pos p hp hg eta a x w z 1 l k m (by omega)
  unfold sourcePrincipalSeries principalFullSeries principalMarkedSeries
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  rw [h0, h1, he.tsum_add (hasSum_ite_eq 0 _).summable, tsum_ite_eq]
  rw [zeroIndexSeries_eq p hp _ W V hW' hV]
  change _ = 1/(1-V)+W/(1-W)+((∑' l, principalInner p hp hg eta a X W V 0 l)+
    ∑' l, principalInner p hp hg eta a X W V 1 l)
  ring

include hc in

theorem sourcePrincipalSeries_euler_identity (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x ≠ 0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourcePrincipalSeries p hp hg eta a x w z =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  rw [sourcePrincipalSeries_eq p hp hg hc eta a x w z hV hR hW]
  exact principalFullSeries_euler_identity p hp hg hc eta a x w z hV hR hW hD

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1268

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Coordinates
Source SHA256: 0bd4412f7f9599222632de140616fc1cb0105d9c47e3d730a12857c47b0918ab
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1269



namespace OAI

noncomputable section
namespace SevenEighths.HeckeCoordinates
open HeckeFamily

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 := IsCyclotomicExtension.zeta_spec 3 ℚ K
private def pb : PowerBasis ℤ O := hζ.integralPowerBasis

private theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

private theorem pb_gen : pb.gen = HeckeFamily.omega := hζ.integralPowerBasis_gen

theorem coordinateElement_surjective :
    Function.Surjective (fun n : ℤ × ℤ => coordinateElement n.1 n.2) := by
  intro x
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨(a,b), ?_⟩
  have hsum := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    have hi : i.val < 2 := by simpa only [pb_dim] using i.isLt
    have hv : i.val = 0 ∨ i.val = 1 := by omega
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases hv with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  rw [huniv] at hsum
  have hne : i0 ≠ i1 := by decide
  have hnot : i0 ∉ ({i1} : Finset (Fin pb.dim)) := by
    simpa only [Finset.mem_singleton] using hne
  rw [Finset.sum_insert hnot, Finset.sum_singleton] at hsum
  simp only [pb.basis_eq_pow] at hsum
  simpa [a, b, i0, i1, pb_gen, coordinateElement, smul_eq_mul, mul_comm] using hsum

def intQuotientHom (χ : Character) : ℤ →+ (O ⧸ χ.modulus) :=
  (Ideal.Quotient.mk χ.modulus).toAddMonoidHom.comp (Int.castAddHom O)

def zmodQuotientHom (χ : Character) : ZMod χ.period →+ (O ⧸ χ.modulus) :=
  ZMod.lift χ.period ⟨intQuotientHom χ, by
    change Ideal.Quotient.mk χ.modulus ((χ.period : ℤ) : O) = 0
    simpa only [Int.cast_natCast] using quotient_period χ⟩

@[simp] theorem zmodQuotientHom_intCast (χ : Character) (a : ℤ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) :=
  ZMod.lift_coe _ _ _

@[simp] theorem zmodQuotientHom_natCast (χ : Character) (a : ℕ) :
    zmodQuotientHom χ (a : ZMod χ.period) = Ideal.Quotient.mk χ.modulus (a : O) := by
  simpa only [Int.cast_natCast] using zmodQuotientHom_intCast χ (a : ℤ)

def coordinateQuotientHom (χ : Character) :
    (ZMod χ.period × ZMod χ.period) →+ (O ⧸ χ.modulus) where
  toFun p := zmodQuotientHom χ p.1 +
    zmodQuotientHom χ p.2 * Ideal.Quotient.mk χ.modulus HeckeFamily.omega
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add]; ring

@[simp] theorem coordinateQuotientHom_intCast (χ : Character) (a b : ℤ) :
    coordinateQuotientHom χ (a, b) =
      Ideal.Quotient.mk χ.modulus (coordinateElement a b) := by
  simp only [coordinateQuotientHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    zmodQuotientHom_intCast, coordinateElement, map_add, map_mul]

theorem coordinateQuotientHom_surjective (χ : Character) :
    Function.Surjective (coordinateQuotientHom χ) := by
  intro x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a,b⟩, hab⟩ := coordinateElement_surjective z
  change coordinateElement a b = z at hab
  exact ⟨(a,b), by rw [coordinateQuotientHom_intCast, hab]⟩

theorem coefficients_eq_quotient_character (χ : Character)
    (a : Fin χ.period × Fin χ.period) :
    coefficients χ a = χ.residue (coordinateQuotientHom χ (a.1, a.2)) := by
  simp [HeckeFamily.coefficients, HeckeFamily.elementCoeff, coordinateQuotientHom,
    coordinateElement]

end SevenEighths.HeckeCoordinates

end

end OAI
end OAIOriginalModule1269

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.CharacterAnalytic
Source SHA256: e426e0a61e9e7caaa8bf95071dd6a2b86464fee067bcb43c0ac7b58ca989ea28
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1270


namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeCharacterAnalytic

def additiveFiberEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (π : A →+ B) (hπ : Function.Surjective π) : A ≃ B × π.ker := by
  classical
  let r : B → A := fun b => (hπ b).choose
  have hr : ∀ b, π (r b) = b := fun b => (hπ b).choose_spec
  exact {
    toFun := fun a => (π a, ⟨a - r (π a), by simp [AddMonoidHom.mem_ker, hr]⟩)
    invFun := fun p => p.2 + r p.1
    left_inv := by intro a; simp
    right_inv := by
      rintro ⟨b, k⟩
      have hk : π k = 0 := k.property
      apply Prod.ext
      · simp [hr, hk]
      · apply Subtype.ext
        simp [hr, hk] }

theorem sum_comp_additiveHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] (π : A →+ B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ a, f (π a)) = (Nat.card π.ker : ℂ) * ∑ b, f b := by
  classical
  let : Fintype π.ker := Fintype.ofFinite _
  have hid (a : A) : f (π a) = (fun p : B × π.ker => f p.1) (additiveFiberEquiv π hπ a) := rfl
  simp_rw [hid]
  rw [(additiveFiberEquiv π hπ).bijective.sum_comp (fun p : B × π.ker => f p.1)]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, Nat.card_eq_fintype_card]

theorem sum_residue_pullback_eq_zero {A R : Type*} [AddCommGroup A] [Fintype A]
    [CommRing R] [Fintype R] (π : A →+ R) (hπ : Function.Surjective π)
    (χ : MulChar R ℂ) (hχ : χ ≠ 1) : (∑ a, χ (π a)) = 0 := by
  rw [sum_comp_additiveHom π hπ, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

def finCastEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun a := (a : ℕ)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv a := Fin.ext (ZMod.val_natCast_of_lt a.isLt)
  right_inv z := ZMod.natCast_zmod_val z

theorem coefficients_sum_eq_zero (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    (∑ a, HeckeFamily.coefficients χ a) = 0 := by
  classical
  let : Finite (HeckeFamily.O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  calc
    (∑ a, HeckeFamily.coefficients χ a) =
        ∑ a, χ.residue (HeckeCoordinates.coordinateQuotientHom χ (e a)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact HeckeCoordinates.coefficients_eq_quotient_character χ a
    _ = ∑ a : ZMod χ.period × ZMod χ.period,
        χ.residue (HeckeCoordinates.coordinateQuotientHom χ a) :=
      e.bijective.sum_comp (fun a => χ.residue (HeckeCoordinates.coordinateQuotientHom χ a))
    _ = 0 := sum_residue_pullback_eq_zero
      (HeckeCoordinates.coordinateQuotientHom χ)
      (HeckeCoordinates.coordinateQuotientHom_surjective χ) χ.residue hχ

theorem continuedLattice_differentiableAt_nonprincipal (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs₀ : s ≠ 0) :
    DifferentiableAt ℂ (HeckeFamily.continuedLattice χ) s :=
  HeckeFamily.continuedLattice_differentiableAt χ hs₀
    (Or.inr (coefficients_sum_eq_zero χ hχ))

theorem residue_zero_of_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    χ.residue 0 = 0 := by
  rcases subsingleton_or_nontrivial (HeckeFamily.O ⧸ χ.modulus) with h | h
  · let := h
    exfalso
    apply hχ
    apply MulChar.ext'
    intro a
    have ha : a = 1 := Subsingleton.elim _ _
    simp [ha]
  · let := h
    exact χ.residue.map_zero

theorem coefficients_zero_of_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    HeckeFamily.coefficients χ (0, 0) = 0 := by
  simpa only [HeckeFamily.coefficients, HeckeFamily.elementCoeff,
    HeckeFamily.coordinateElement, Fin.val_zero, Int.natCast_zero, Int.cast_zero,
    zero_mul, zero_add, map_zero] using residue_zero_of_nonprincipal χ hχ

theorem completed_entire_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    Differentiable ℂ (HeckeTheta.completed (HeckeFamily.coefficients χ)) := by
  intro s
  exact (HeckeTheta.pair (HeckeFamily.coefficients χ)).differentiableAt_Λ
    (Or.inr (by rw [HeckeTheta.pair_f₀, coefficients_zero_of_nonprincipal χ hχ]))
    (Or.inr (HeckeTheta.pair_g₀_eq_zero _ (coefficients_sum_eq_zero χ hχ)))

theorem continuedLattice_entire_nonprincipal (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) : Differentiable ℂ (HeckeFamily.continuedLattice χ) := by
  exact ((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
      Complex.differentiable_one_div_Gamma).mul (completed_entire_nonprincipal χ hχ)

theorem continuedLattice_neg_succ (χ : HeckeFamily.Character) (n : ℕ) :
    HeckeFamily.continuedLattice χ (-((n + 1 : ℕ) : ℂ)) = 0 := by
  unfold HeckeFamily.continuedLattice HeckeTheta.latticeL
  rw [Complex.Gamma_neg_nat_eq_zero (n + 1)]
  simp

end SevenEighths.HeckeCharacterAnalytic

end

end OAI
end OAIOriginalModule1270

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Operations
Source SHA256: 489c63376991b67a57b09714e80de6f990a18943d498601984c9bcbef71b00fa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1271



namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

def Character.product (χ ψ : Character) : Character :=
  Character.ofResidue (χ.modulus ⊓ ψ.modulus)
    (Ideal.inf_ne_bot_of_ne_bot χ.modulus_ne_bot ψ.modulus_ne_bot)
    (ResidueCharacter.product χ.modulus ψ.modulus χ.residue ψ.residue)
    (ResidueCharacter.product_global_units _ _ _ _ χ.unit_trivial ψ.unit_trivial)

theorem elementCoeff_product (χ ψ : Character) (z : O) :
    elementCoeff (χ.product ψ) z = elementCoeff χ z * elementCoeff ψ z :=
  ResidueCharacter.product_mk _ _ _ _ z

def Character.inverse (χ : Character) : Character where
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue⁻¹
  unit_trivial u := by simp [MulChar.inv_apply_eq_inv', χ.unit_trivial]
  period := χ.period
  period_pos := χ.period_pos
  period_mem := χ.period_mem

theorem elementCoeff_inverse (χ : Character) (z : O) :
    elementCoeff χ.inverse z = (elementCoeff χ z)⁻¹ := by
  exact MulChar.inv_apply_eq_inv' _ _

def Character.power (χ : Character) (n : ℕ) : Character where
  modulus := χ.modulus
  modulus_ne_bot := χ.modulus_ne_bot
  residue := χ.residue ^ n
  unit_trivial u := by
    let v := Units.map (Ideal.Quotient.mk χ.modulus).toMonoidHom u
    change (χ.residue ^ n) (v : O ⧸ χ.modulus) = 1
    rw [MulChar.pow_apply_coe]
    change χ.residue (Ideal.Quotient.mk χ.modulus u) ^ n = 1
    simp [χ.unit_trivial]
  period := χ.period
  period_pos := χ.period_pos
  period_mem := χ.period_mem

theorem elementCoeff_power_of_unit (χ : Character) (n : ℕ) (z : O)
    (hz : IsUnit (Ideal.Quotient.mk χ.modulus z)) :
    elementCoeff (χ.power n) z = elementCoeff χ z ^ n := by
  change (χ.residue ^ n) (Ideal.Quotient.mk χ.modulus z) = _
  obtain ⟨u, hu⟩ := hz
  rw [← hu, MulChar.pow_apply_coe, hu]
  rfl

end SevenEighths.HeckeFamily

end

end OAI
end OAIOriginalModule1271

/-! Original module: OAI.NumberTheory.DirichletL.LatticeSummability
Source SHA256: c8c238c1504428039efdfde34bf6c56958038ef60913490d3b5e0bd5d87801d3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1272



namespace OAI

noncomputable section
namespace SevenEighths.LatticeSummability
open EisensteinTheta

theorem normForm_nonneg (x y : ℝ) : 0 ≤ normForm x y := by
  unfold normForm
  nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]

theorem normForm_eq_zero_iff (x y : ℝ) : normForm x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    unfold normForm at h
    have hx : x ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
    have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]
    exact ⟨sq_eq_zero_iff.mp hx, sq_eq_zero_iff.mp hy⟩
  · rintro ⟨rfl, rfl⟩
    simp [normForm]

theorem normForm_ge_half_norm_sq (n : ℤ × ℤ) :
    (1 / 2 : ℝ) * ‖n‖ ^ 2 ≤ normForm n.1 n.2 := by
  rw [Prod.norm_def, ← Int.norm_cast_real, ← Int.norm_cast_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  unfold normForm
  rcases le_total |(n.1 : ℝ)| |(n.2 : ℝ)| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg ((n.1 : ℝ) - n.2), sq_nonneg (n.1 : ℝ)]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg ((n.1 : ℝ) - n.2), sq_nonneg (n.2 : ℝ)]

theorem summable_pair_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable (fun n : ℤ × ℤ => ‖n‖ ^ (-k)) := by
  have h := (finTwoArrowEquiv ℤ).symm.summable_iff.mpr
    (EisensteinSeries.summable_one_div_norm_rpow hk)
  have hn (n : ℤ) : (n.natAbs : ℝ) = ‖n‖ := by
    exact congrArg (fun x : NNReal => (x : ℝ)) (NNReal.natCast_natAbs n)
  simpa only [finTwoArrowEquiv_symm_apply, Function.comp_def,
    EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero,
    Matrix.cons_val_one, Prod.norm_def, Nat.cast_max, hn] using h

theorem summable_normForm_neg_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => normForm n.1 n.2 ^ (-σ)) := by
  have hmajor := (summable_pair_norm_rpow (k := 2 * σ) (by linarith)).mul_left
    ((1 / 2 : ℝ) ^ (-σ))
  apply Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (normForm_nonneg _ _) _) _ hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    simp [normForm, Real.zero_rpow (by linarith : -σ ≠ 0),
      Real.zero_rpow (by linarith : -(2 * σ) ≠ 0)]
  · have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
    calc
      normForm n.1 n.2 ^ (-σ) ≤ ((1 / 2 : ℝ) * ‖n‖ ^ 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (normForm_ge_half_norm_sq n)
          (by linarith)
      _ = (1 / 2 : ℝ) ^ (-σ) * ‖n‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg _)]
        congr 1
        rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring

theorem summable_one_div_normForm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => 1 / normForm n.1 n.2 ^ σ) := by
  simpa only [Real.rpow_neg (normForm_nonneg _ _), one_div] using
    summable_normForm_neg_rpow hσ

theorem summable_weighted_normForm {w : ℤ × ℤ → ℂ} {C σ : ℝ}
    (hw : ∀ n, ‖w n‖ ≤ C) (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => ‖w n‖ / normForm n.1 n.2 ^ σ) := by
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (normForm_nonneg _ _) _)) _
    ((summable_one_div_normForm_rpow hσ).mul_left C)
  intro n
  simpa only [mul_one_div] using
    div_le_div_of_nonneg_right (hw n) (Real.rpow_nonneg (normForm_nonneg _ _) _)

end SevenEighths.LatticeSummability

end

end OAI
end OAIOriginalModule1272

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.ThetaSeries
Source SHA256: 25d74f312961971c15115137887094db35e9ee466127444694a4da29a007a2d1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1273



namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability

@[simp] theorem periodicCoeff_zero {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) :
    periodicCoeff w (0, 0) = w (0, 0) := by
  simp [periodicCoeff, residueEquiv, regroup, Int.divModEquiv, Int.natMod]

theorem norm_periodicCoeff_le {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (n : ℤ × ℤ) : ‖periodicCoeff w n‖ ≤ ∑ a, ‖w a‖ := by
  unfold periodicCoeff
  exact Finset.single_le_sum (fun a _ => norm_nonneg (w a)) (Finset.mem_univ _)

private theorem normForm_coordinates_eq_zero (n : ℤ × ℤ) :
    normForm n.1 n.2 = 0 ↔ n = (0, 0) := by
  rw [normForm_eq_zero_iff]
  simp only [Int.cast_eq_zero, Prod.ext_iff]

theorem theta_sub_zero_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => if normForm n.1 n.2 = 0 then 0 else
      periodicCoeff w n * (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ))
      ((pair w).f t - (pair w).f₀) := by
  have h := (theta_hasSum w ht).sub (hasSum_ite_eq (0, 0) (w (0, 0)))
  rw [pair_f₀]
  convert h using 1
  funext n
  simp only [normForm_coordinates_eq_zero]
  by_cases hn : n = (0, 0)
  · subst n
    simp [normForm]
  · simp [hn]

theorem completed_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => (Real.pi : ℂ) ^ (-s) * Complex.Gamma s *
      periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s) (completed w s) := by
  have hsum : Summable (fun n : ℤ × ℤ => ‖periodicCoeff w n‖ /
      normForm n.1 n.2 ^ s.re) :=
    summable_weighted_normForm (norm_periodicCoeff_le w) hs
  have h := hasSum_mellin_pi_mul₀
    (a := periodicCoeff w) (p := fun n : ℤ × ℤ => normForm n.1 n.2)
    (F := fun t => (pair w).f t - (pair w).f₀)
    (fun _ => normForm_nonneg _ _) (by linarith : 0 < s.re)
    (fun _ ht => theta_sub_zero_hasSum w ht) hsum
  rwa [(pair_hasMellin w hs).2] at h

theorem latticeL_hasSum {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n / (normForm n.1 n.2 : ℂ) ^ s)
      (latticeL w s) := by
  have hΓ := Complex.Gamma_ne_zero_of_re_pos (by linarith : 0 < s.re)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (Real.pi : ℂ) ^ s ≠ 0 := fun h => hπ ((Complex.cpow_eq_zero_iff _ _).mp h).1
  have h := (completed_hasSum w hs).mul_left ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹)
  change HasSum _ ((Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ * completed w s)
  convert h using 1
  funext n
  rw [Complex.cpow_neg]
  field_simp

end SevenEighths.HeckeTheta

end

end OAI
end OAIOriginalModule1273

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.FamilySeries
Source SHA256: e1f13693e9b19dcdca6ff4da5e2bba935790506dd253228372fdc23356ce946a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1274




namespace OAI

noncomputable section
namespace SevenEighths.HeckeTheta
open EisensteinTheta

theorem latticeL_eq_of_coefficients_right {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (hcoeff : ∀ n, periodicCoeff w n = periodicCoeff v n)
    {s : ℂ} (hs : 1 < s.re) : latticeL w s = latticeL v s := by
  have hw := latticeL_hasSum w hs
  simp_rw [hcoeff] at hw
  exact hw.unique (latticeL_hasSum v hs)

theorem latticeL_eq_of_coefficients {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (hcoeff : ∀ n, periodicCoeff w n = periodicCoeff v n)
    {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) : latticeL w s = latticeL v s := by
  have hwa : AnalyticOnNhd ℂ (regularizedLatticeL w) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (regularizedLatticeL_differentiableAt w
      (by intro h; simp [h] at hz)).differentiableWithinAt
  have hva : AnalyticOnNhd ℂ (regularizedLatticeL v) {z : ℂ | 0 < z.re} := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 0)).2
    intro z hz
    exact (regularizedLatticeL_differentiableAt v
      (by intro h; simp [h] at hz)).differentiableWithinAt
  have hident := Continuation.product_identity_on_halfPlane 0 1
    (regularizedLatticeL w) (fun _ => 1) (regularizedLatticeL v)
    hwa analyticOnNhd_const hva (by
      intro z hz
      have hz' : 1 < z.re := by simpa using hz
      have hz₀ : z ≠ 0 := by intro h; norm_num [h] at hz'
      have hz₁ : z ≠ 1 := by intro h; norm_num [h] at hz'
      simp only [mul_one, regularizedLatticeL_eq w hz₀ hz₁,
        regularizedLatticeL_eq v hz₀ hz₁,
        latticeL_eq_of_coefficients_right w v hcoeff hz']) hs
  have hs₀ : s ≠ 0 := by intro h; simp [h] at hs
  simp only [mul_one, regularizedLatticeL_eq w hs₀ hs₁,
    regularizedLatticeL_eq v hs₀ hs₁] at hident
  exact mul_left_cancel₀ (sub_ne_zero.mpr hs₁) hident
end SevenEighths.HeckeTheta

namespace SevenEighths.HeckeFamily
open EisensteinTheta

theorem continuedLattice_hasSum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℤ × ℤ => elementCoeff χ (coordinateElement n.1 n.2) /
      (normForm n.1 n.2 : ℂ) ^ s) (continuedLattice χ s) := by
  simpa only [periodicCoeff_eq_elementCoeff, continuedLattice] using HeckeTheta.latticeL_hasSum (coefficients χ) hs

theorem continuedLattice_eq_of_elementCoeff_eq (χ ψ : Character)
    (hχψ : ∀ z, elementCoeff χ z = elementCoeff ψ z)
    {s : ℂ} (hs : 0 < s.re) (hs₁ : s ≠ 1) :
    continuedLattice χ s = continuedLattice ψ s := by
  apply HeckeTheta.latticeL_eq_of_coefficients (coefficients χ) (coefficients ψ) _ hs hs₁
  intro n
  simp only [periodicCoeff_eq_elementCoeff, hχψ]

end SevenEighths.HeckeFamily

end

end OAI
end OAIOriginalModule1274

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.IdealBridge
Source SHA256: 6c1fc33b7372108323bf3af3d4ab6f6e454ea9896b89e78964463a8e35df735f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1275





namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def idealCoeff (χ : Character) : Ideal O →*₀ ℂ :=
  IdealCharacter.ofResidue χ.modulus χ.residue χ.unit_trivial

@[simp] theorem idealCoeff_zero (χ : Character) : idealCoeff χ 0 = 0 := map_zero _

theorem idealCoeff_span (χ : Character) {z : O} (hz : z ≠ 0) :
    idealCoeff χ (Ideal.span {z}) = elementCoeff χ z :=
  IdealCharacter.ofResidue_span χ.modulus χ.residue χ.unit_trivial hz

theorem coordinateElement_eq_baseline (a b : ℤ) :
    coordinateElement a b = ActualEisensteinCoordinates.eval a b := rfl

def coordinateEquiv : (ℤ × ℤ) ≃ O :=
  Equiv.ofBijective (fun n => coordinateElement n.1 n.2)
    ⟨fun _ _ h => Prod.ext
      (ActualEisensteinCoordinates.unique_coordinates h).1
      (ActualEisensteinCoordinates.unique_coordinates h).2,
      HeckeCoordinates.coordinateElement_surjective⟩

theorem normForm_eq_absNorm_span (n : ℤ × ℤ) :
    EisensteinTheta.normForm n.1 n.2 =
      (Ideal.absNorm (Ideal.span {coordinateElement n.1 n.2}) : ℝ) := by
  rw [coordinateElement_eq_baseline,
    ← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    ActualEisensteinCubic.eisEmbedding_eval_norm_sq]
  simp only [EisensteinTheta.normForm, Int.cast_add, Int.cast_sub, Int.cast_mul, pow_two]

def elementTerm (χ : Character) (s : ℂ) (z : O) : ℂ :=
  elementCoeff χ z / (Ideal.absNorm (Ideal.span {z}) : ℂ) ^ s

def idealTerm (χ : Character) (s : ℂ) (I : Ideal O) : ℂ :=
  idealCoeff χ I / (Ideal.absNorm I : ℂ) ^ s

theorem elementTerm_coordinate (χ : Character) (s : ℂ) (n : ℤ × ℤ) :
    elementTerm χ s (coordinateEquiv n) =
      elementCoeff χ (coordinateElement n.1 n.2) /
        (EisensteinTheta.normForm n.1 n.2 : ℂ) ^ s := by
  change elementCoeff χ (coordinateElement n.1 n.2) /
    (Ideal.absNorm (Ideal.span {coordinateElement n.1 n.2}) : ℂ) ^ s = _
  rw [normForm_eq_absNorm_span]
  rw [Complex.ofReal_natCast]

theorem elementTerm_hasSum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    HasSum (elementTerm χ s) (continuedLattice χ s) := by
  apply coordinateEquiv.hasSum_iff.mp
  change HasSum (fun n => elementTerm χ s (coordinateEquiv n)) _
  simpa only [elementTerm_coordinate] using continuedLattice_hasSum χ hs

theorem elementTerm_zero (χ : Character) {s : ℂ} (hs : s ≠ 0) :
    elementTerm χ s 0 = 0 := by
  simp [elementTerm, Complex.zero_cpow hs]

theorem elementTerm_unit_mul (χ : Character) (s : ℂ) (u : Oˣ) (z : O) :
    elementTerm χ s ((u : O) * z) = elementTerm χ s z := by
  unfold elementTerm
  rw [elementCoeff_unit_mul, Ideal.span_singleton_mul_left_unit u.isUnit]

theorem elementTerm_idealGenerator (χ : Character) (s : ℂ)
    (I : UnrestrictedIdealReindex.NonzeroIdeal) :
    elementTerm χ s (ConcretePrimeRowBridge.idealGenerator I.val) = idealTerm χ s I.val := by
  unfold elementTerm idealTerm
  rw [ConcretePrimeRowBridge.span_idealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator χ.modulus χ.residue χ.unit_trivial
    I.property (ConcretePrimeRowBridge.span_idealGenerator I.val)).symm

theorem continuedLattice_eq_six_ideal_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    continuedLattice χ s = 6 * ∑' I : Ideal O, idealTerm χ s I := by
  have hs₀ : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero (elementTerm χ s)
    (elementTerm_hasSum χ hs).summable (elementTerm_zero χ hs₀)
    (elementTerm_unit_mul χ s)
  rw [(elementTerm_hasSum χ hs).tsum_eq] at h
  simp_rw [elementTerm_idealGenerator] at h
  have hsum : (∑' I : UnrestrictedIdealReindex.NonzeroIdeal, idealTerm χ s I.val) =
      ∑' I : Ideal O, idealTerm χ s I := by
    apply tsum_subtype_eq_of_support_subset
    intro I hI hzero
    exact hI (by rw [hzero]; unfold idealTerm; rw [map_zero]; exact zero_div _)
  rwa [hsum] at h

def LFunction (χ : Character) (s : ℂ) : ℂ := continuedLattice χ s / 6

theorem LFunction_eq_ideal_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = ∑' I : Ideal O, idealTerm χ s I := by
  rw [LFunction, continuedLattice_eq_six_ideal_tsum χ hs]
  ring

theorem LFunction_differentiableAt (χ : Character) {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1 ∨ χ.residue ≠ 1) :
    DifferentiableAt ℂ (LFunction χ) s := by
  apply DifferentiableAt.div_const
  rcases hs₁ with hs₁ | hχ
  · exact continuedLattice_differentiableAt χ hs₀ (Or.inl hs₁)
  · exact HeckeCharacterAnalytic.continuedLattice_differentiableAt_nonprincipal χ hχ hs₀

theorem LFunction_entire_nonprincipal (χ : Character) (hχ : χ.residue ≠ 1) :
    Differentiable ℂ (LFunction χ) :=
  (HeckeCharacterAnalytic.continuedLattice_entire_nonprincipal χ hχ).div_const 6

end SevenEighths.HeckeFamily

end

end OAI
end OAIOriginalModule1275

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Euler
Source SHA256: 3c2d31189b4eb5efa3417c73fa7390c7add3350143df5e98fd951a375631558d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1276



namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem idealCoeff_norm_le_one (χ : Character) (I : Ideal O) : ‖idealCoeff χ I‖ ≤ 1 := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact IdealCharacter.norm_ofResidue_le_one χ.modulus χ.residue χ.unit_trivial I

theorem idealTerm_eq_weighted (χ : Character) (s : ℂ) (I : Ideal O) :
    idealTerm χ s I = IdealEuler.weighted (idealCoeff χ) s I := by
  change idealCoeff χ I / (Ideal.absNorm I : ℂ)^s =
    idealCoeff χ I * CubicEisenstein.fullIdealWeight s I
  by_cases hI : I = 0
  · rw [hI, map_zero]
    simp
  · simp only [CubicEisenstein.fullIdealWeight, hI, ite_false,
      Complex.cpow_neg, div_eq_mul_inv]

theorem LFunction_eq_series (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = IdealEuler.series (idealCoeff χ) s := by
  rw [LFunction_eq_ideal_tsum χ hs]
  exact tsum_congr (idealTerm_eq_weighted χ s)

theorem LFunction_ne_zero_of_one_lt_re (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s ≠ 0 := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.series_ne_zero (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

theorem inverseSeries_mul_LFunction (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    IdealEuler.inverseSeries (idealCoeff χ) s * LFunction χ s = 1 := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.inverseSeries_mul_series (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

theorem LFunction_eq_normFiber_LSeries (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LSeries (ShortDraftHeckeBridge.normFiberCoeff (idealCoeff χ)) s := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.series_eq_LSeries (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

end SevenEighths.HeckeFamily

end

end OAI
end OAIOriginalModule1276

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.BoundaryIntegration
Source SHA256: 404bb346650e5a84f6e839eaee1c4598b45296af0dcaeacd2bc6a5a0470a5045
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1277




namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

theorem LFunction_one_ne_zero_quadratic (χ : Character)
    (hχ : χ.residue ≠ 1) (hquad : χ.residue ^ 2 = 1) : LFunction χ 1 ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact HeckeBoundary.quadratic_one_ne_zero_of_entire χ.modulus χ.residue
    χ.unit_trivial hquad (LFunction χ) (LFunction_entire_nonprincipal χ hχ)
      (fun s hs => LFunction_eq_series χ hs)

theorem LFunction_boundary_ne_zero (χ : Character) (t : ℝ)
    (hpole : t ≠ 0 ∨ χ.residue ≠ 1)
    (hsquare : t ≠ 0 ∨ χ.residue ^ 2 ≠ 1) :
    LFunction χ (1 + Complex.I * t) ≠ 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  have h1 (t : ℝ) (ht : t ≠ 0) : (1 + Complex.I * t : ℂ) ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_add] at hi
    exact ht hi
  have h0 (t : ℝ) : (1 + Complex.I * t : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  apply HeckeBoundary.residue_boundary_ne_zero_of_series_eq χ.modulus χ.residue
    χ.unit_trivial (LFunction χ) (LFunction (χ.power 2))
    (fun s hs => LFunction_eq_series χ hs)
    (fun s hs => LFunction_eq_series (χ.power 2) hs) t
  · apply LFunction_differentiableAt χ (h0 t)
    exact hpole.imp (h1 t) id
  · have heq : (1 + 2 * Complex.I * t : ℂ) = 1 + Complex.I * (2 * t : ℝ) := by
      push_cast
      ring
    rw [heq]
    apply DifferentiableAt.continuousAt (𝕜 := ℂ)
    apply LFunction_differentiableAt (χ.power 2) (h0 (2*t))
    rcases hsquare with ht | hsq
    · exact Or.inl (h1 (2*t) (mul_ne_zero (by norm_num) ht))
    · exact Or.inr hsq

theorem LFunction_one_ne_zero_nonprincipal (χ : Character) (hχ : χ.residue ≠ 1) :
    LFunction χ 1 ≠ 0 := by
  by_cases hquad : χ.residue ^ 2 = 1
  · exact LFunction_one_ne_zero_quadratic χ hχ hquad
  · simpa only [Complex.ofReal_zero, mul_zero, add_zero] using
      LFunction_boundary_ne_zero χ 0 (Or.inr hχ) (Or.inr hquad)

theorem LFunction_ne_zero_of_re_eq_one (χ : Character) {s : ℂ}
    (hs : s.re = 1) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  have heq : s = 1 + Complex.I * s.im := by
    apply Complex.ext <;> simp [hs]
  by_cases ht : s.im = 0
  · have hs1 : s = 1 := by rw [heq, ht]; simp
    subst s
    exact LFunction_one_ne_zero_nonprincipal χ (hpole.resolve_left (not_not.mpr rfl))
  · rw [heq]
    exact LFunction_boundary_ne_zero χ s.im (Or.inl ht) (Or.inl ht)

theorem LFunction_ne_zero_of_one_le_re (χ : Character) {s : ℂ}
    (hs : 1 ≤ s.re) (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 := by
  rcases eq_or_lt_of_le hs with h | h
  · exact LFunction_ne_zero_of_re_eq_one χ h.symm hpole
  · exact LFunction_ne_zero_of_one_lt_re χ h

end SevenEighths.HeckeFamily

end

end OAI
end OAIOriginalModule1277

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessArithmetic
Source SHA256: b63baaac3d06b4e8d37fe2dc5b25ba228025d1b90111429ecc68c747b42d6559
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1278


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessArithmetic
open HeckeFamily UniqueFactorizationMonoid CompletedGauss
local notation "O" => HeckeFamily.O

def cutoffCoefficient (V : ℝ → ℂ) (D : ℝ) (I : Ideal O) : ℂ :=
  if I = 0 then 0 else
    ∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)

theorem fiber_norm_le {I : Ideal O} (hI : I ≠ 0) (p : MulFiber I) :
    Ideal.absNorm p.val.1 ≤ Ideal.absNorm I := by
  apply Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  exact map_dvd Ideal.absNorm ⟨p.val.2, p.property.symm⟩

theorem cutoffCoefficient_small (V : ℝ → ℂ) (D : ℝ) (hD : 0 < D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (I : Ideal O) (hI : (Ideal.absNorm I : ℝ) ≤ D) :
    cutoffCoefficient V D I = if I = 1 then 1 else 0 := by
  by_cases hI0 : I = 0
  · simp [cutoffCoefficient, hI0]
  · rw [cutoffCoefficient, ite_eq_right hI0]
    have heq : (fun p : MulFiber I => (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)) =
        (fun p : MulFiber I => (moebius p.val.1 : ℂ)) := by
      funext p
      rw [hV _ (div_nonneg (by positivity) hD.le) ((div_le_one hD).mpr ?_), mul_one]
      exact (by exact_mod_cast fiber_norm_le hI0 p : (Ideal.absNorm p.val.1 : ℝ) ≤ Ideal.absNorm I).trans hI
    rw [heq]
    exact mulFiber_moebius_sum I hI0

theorem cutoffCoefficient_tail (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (I : Ideal O) :
    cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      cutoffCoefficient V D I - if I = 1 then 1 else 0 := by
  have hD0 : 0 < D := by linarith
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ D
  · rw [cutoffCoefficient_small V D hD0 hV I hI]
    by_cases hI1 : I = 1
    · subst I
      simp only [map_one, Nat.cast_one, mul_one, ite_true, one_mul, sub_self]
      rw [hV _ (by positivity) ((div_le_one hD0).mpr hD), sub_self]
    · simp only [hI1, ite_false, zero_mul, sub_zero]
  · have hv : V (2 * (Ideal.absNorm I : ℝ) / D) = 0 := by
      apply hVzero
      apply (le_div_iff₀ hD0).mpr
      linarith [lt_of_not_ge hI]
    have hI1 : I ≠ 1 := by
      intro hh
      subst I
      simp only [map_one, Nat.cast_one] at hI
      linarith
    rw [hv, sub_zero, mul_one, ite_eq_right hI1, sub_zero]

theorem weighted_fiber (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D) *
      IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2)) =
      cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I := by
  by_cases hI : I = 0
  · subst I
    have hz (p : MulFiber 0) : IdealEuler.weighted (idealCoeff χ) s (p.val.1 * p.val.2) = 0 := by
      rw [p.property, map_zero]
    simp [hz, cutoffCoefficient]
  · rw [cutoffCoefficient, ite_eq_right hI, ← tsum_mul_right]
    apply tsum_congr
    intro p
    rw [p.property]

def exponentialTerm (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (Y : ℝ) (I : Ideal O) : ℂ :=
  cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I *
    Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ))

theorem exponentialTerm_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ) (I : Ideal O) :
    exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D)) =
      exponentialTerm χ V D s Y I - if I = 1 then Complex.exp (-1 / (Y : ℂ)) else 0 := by
  have h := cutoffCoefficient_tail V D hD hV hVzero I
  unfold exponentialTerm
  calc
    _ = (cutoffCoefficient V D I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) *
        IdealEuler.weighted (idealCoeff χ) s I * Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ)) := by ring
    _ = _ := by
      rw [h]
      by_cases hI : I = 1
      · subst I
        simp only [ite_true, map_one, Nat.cast_one, Complex.ofReal_one, mul_one]
        ring
      · simp only [hI, ite_false, sub_zero]

theorem exponential_sum_tail (χ : Character) (V : ℝ → ℂ) (D : ℝ) (hD : 2 ≤ D)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (Y : ℝ)
    (hsum : Summable (exponentialTerm χ V D s Y)) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1 - V (2 * (Ideal.absNorm I : ℝ) / D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1 / (Y : ℂ)) := by
  simp_rw [exponentialTerm_tail χ V D hD hV hVzero s Y]
  rw [hsum.tsum_sub ((hasSum_ite_eq (1 : Ideal O) (Complex.exp (-1 / (Y : ℂ)))).summable)]
  simp only [tsum_ite_eq]

end SevenEighths.HeckeDetectorWitnessArithmetic

end

end OAI
end OAIOriginalModule1278

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorPartition
Source SHA256: 32ac0a12ece8c986c2630603dee97493f864a42b0c4922eee5e14d8a13d2f4a2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1279


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorPartition
open DyadicTransfer

theorem partition (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (n J : ℕ) (hn : 1 ≤ n) (hJ : (n : ℝ) ≤ (2 : ℝ)^J) :
    (∑ j ∈ Finset.range (J+1), annularCutoff V ((n : ℝ)/(2 : ℝ)^j)) = 1 := by
  rw [partial_partition]
  rw [hsmall _ (by positivity) ((div_le_one (by positivity)).mpr hJ)]
  rw [hlarge _ (by exact_mod_cast (show 2 ≤ 2*n by omega))]
  ring

theorem finite_pair_reassembly {A : Type*} (S : Finset A) (a : A → ℂ)
    (n m : A → ℕ) (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (J K : ℕ)
    (hn : ∀ p ∈ S, 1 ≤ n p ∧ (n p : ℝ) ≤ (2 : ℝ)^J)
    (hm : ∀ p ∈ S, 1 ≤ m p ∧ (m p : ℝ) ≤ (2 : ℝ)^K) :
    (∑ p ∈ S, a p) =
      ∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1), ∑ p ∈ S,
        a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
  symm
  calc
    _ = ∑ p ∈ S, ∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1),
        a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
      calc
        _ = ∑ j ∈ Finset.range (J+1), ∑ p ∈ S, ∑ k ∈ Finset.range (K+1),
            a p * annularCutoff V ((n p : ℝ)/(2 : ℝ)^j) *
              annularCutoff V ((m p : ℝ)/(2 : ℝ)^k) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      simp_rw [← Finset.mul_sum]
      rw [partition V hsmall hlarge (m p) K (hm p hp).1 (hm p hp).2]
      simp only [mul_one]
      rw [← Finset.mul_sum, partition V hsmall hlarge (n p) J (hn p hp).1 (hn p hp).2,
        mul_one]

theorem annular_support (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (x : ℝ) (hx : 0 ≤ x) (j : ℕ)
    (hne : annularCutoff V (x/(2 : ℝ)^j) ≠ 0) :
    (2 : ℝ)^j / 2 < x ∧ x < 2*(2 : ℝ)^j := by
  have hp : 0 < (2 : ℝ)^j := by positivity
  have hy : 0 ≤ x/(2 : ℝ)^j := div_nonneg hx hp.le
  have hlo : 1/2 < x/(2 : ℝ)^j := by
    by_contra h
    have hh := le_of_not_gt h
    apply hne
    rw [annularCutoff, hsmall _ hy (by linarith), hsmall _ (by positivity) (by linarith)]
    ring
  have hhi : x/(2 : ℝ)^j < 2 := by
    by_contra h
    apply hne
    exact annularCutoff_eq_zero_of_two_le V hlarge (le_of_not_gt h)
  constructor
  · have := (lt_div_iff₀ hp).mp hlo
    linarith
  · exact (div_lt_iff₀ hp).mp hhi

def length (X : ℝ) : ℕ := ⌈Real.logb 2 X⌉₊

theorem norm_le_last_scale (X : ℝ) (hX : 0 < X) : X ≤ (2 : ℝ)^(length X) := by
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hX).mp
    (Nat.le_ceil (Real.logb 2 X))
  simpa only [Real.rpow_natCast, length] using h

theorem length_bound (X : ℝ) (hX : 1 ≤ X) :
    (length X : ℝ) + 1 < Real.logb 2 X + 2 := by
  have hlog : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX
  have h := Nat.ceil_lt_add_one hlog
  change (⌈Real.logb 2 X⌉₊ : ℝ) + 1 < _
  linarith

theorem pair_scale_bounds (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (hterm : ∀ y : ℝ, 2 ≤ y → T y = 0)
    (x y D U : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hD : 0 < D) (hU : 0 < U)
    (j k : ℕ)
    (hj : annularCutoff V (x/(2 : ℝ)^j) ≠ 0)
    (hk : annularCutoff V (y/(2 : ℝ)^k) ≠ 0)
    (hfirst : V (x/D) ≠ 0)
    (hproduct : 1 - V (2*(x*y)/D) ≠ 0)
    (hterminal : T (x*y/U) ≠ 0) :
    (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
      (2 : ℝ)^j*(2 : ℝ)^k < 8*U := by
  obtain ⟨hjlo,hjhi⟩ := annular_support V hsmall hlarge x hx j hj
  obtain ⟨hklo,hkhi⟩ := annular_support V hsmall hlarge y hy k hk
  have hJ : 0 < (2 : ℝ)^j := by positivity
  have hK : 0 < (2 : ℝ)^k := by positivity
  have hxd : x < 2*D := by
    by_contra h
    apply hfirst
    apply hlarge
    exact (le_div_iff₀ hD).mpr (le_of_not_gt h)
  have hprod : D < 2*(x*y) := by
    by_contra h
    apply hproduct
    rw [hsmall _ (by positivity) ((div_le_one hD).mpr (le_of_not_gt h))]
    ring
  have hxyU : x*y < 2*U := by
    by_contra h
    apply hterminal
    apply hterm
    exact (le_div_iff₀ hU).mpr (le_of_not_gt h)
  have hlo : (2 : ℝ)^j*(2 : ℝ)^k/4 < x*y := by
    have h1 := mul_lt_mul_of_pos_right hjlo (show 0 < y by linarith)
    have h2 := mul_lt_mul_of_pos_left hklo (show 0 < (2 : ℝ)^j/2 by positivity)
    nlinarith
  have hhi : x*y < 4*((2 : ℝ)^j*(2 : ℝ)^k) := by
    have h1 := mul_lt_mul_of_pos_right hjhi (show 0 < y by linarith)
    have h2 := mul_lt_mul_of_pos_left hkhi (show 0 < 2*(2 : ℝ)^j by positivity)
    nlinarith
  constructor
  · linarith
  constructor <;> linarith

def pairCoefficient (χ : HeckeFamily.Character) (V T : ℝ → ℂ)
    (D Y U : ℝ) (s : ℂ) (p : Ideal HeckeFamily.O × Ideal HeckeFamily.O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((Ideal.absNorm p.1 : ℝ)/D) *
    IdealEuler.weighted (HeckeFamily.idealCoeff χ) s (p.1*p.2) *
    Complex.exp (-((Ideal.absNorm (p.1*p.2) : ℝ) : ℂ)/(Y : ℂ)) *
    (1-V (2*(Ideal.absNorm (p.1*p.2) : ℝ)/D)) * T ((Ideal.absNorm (p.1*p.2) : ℝ)/U)

theorem actual_pair_reassembly (χ : HeckeFamily.Character) (V T : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (D Y U X Z : ℝ) (hX : 0 < X) (hZ : 0 < Z) (s : ℂ)
    (S : Finset (Ideal HeckeFamily.O × Ideal HeckeFamily.O))
    (hS : ∀ p ∈ S, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧
      (Ideal.absNorm p.1 : ℝ) ≤ X ∧ (Ideal.absNorm p.2 : ℝ) ≤ Z) :
    (∑ p ∈ S, pairCoefficient χ V T D Y U s p) =
      ∑ j ∈ Finset.range (length X+1), ∑ k ∈ Finset.range (length Z+1), ∑ p ∈ S,
        pairCoefficient χ V T D Y U s p *
          annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
          annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k) := by
  apply finite_pair_reassembly S _ _ _ V hsmall hlarge
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).1),
      (hS p hp).2.2.1.trans (norm_le_last_scale X hX)⟩
  · intro p hp
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS p hp).2.1),
      (hS p hp).2.2.2.trans (norm_le_last_scale Z hZ)⟩

theorem exists_large_pair (J K : ℕ) (F : ℕ → ℕ → ℂ) :
    ∃ j ∈ Finset.range (J+1), ∃ k ∈ Finset.range (K+1),
      ‖∑ j ∈ Finset.range (J+1), ∑ k ∈ Finset.range (K+1), F j k‖ ≤
        ((J+1 : ℕ) : ℝ)*((K+1 : ℕ) : ℝ)*‖F j k‖ := by
  let S := (Finset.range (J+1)) ×ˢ (Finset.range (K+1))
  have hS : S.Nonempty := ⟨(0,0), by simp [S]⟩
  obtain ⟨p,hp,hmax⟩ := S.exists_max_image (fun p => ‖F p.1 p.2‖) hS
  obtain ⟨hj,hk⟩ := Finset.mem_product.mp hp
  refine ⟨p.1,hj,p.2,hk,?_⟩
  calc
    _ = ‖∑ q ∈ S, F q.1 q.2‖ := by rw [Finset.sum_product]
    _ ≤ ∑ q ∈ S, ‖F q.1 q.2‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ S, ‖F p.1 p.2‖ := Finset.sum_le_sum (fun q hq => hmax q hq)
    _ = _ := by simp [S, Finset.card_product, mul_assoc]

end SevenEighths.HeckeDetectorPartition

end

end OAI
end OAIOriginalModule1279

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFourierActual
Source SHA256: 651411ebbda4d602cdf7ca86a7bde2f5e99aadbc9edb5453341c2b833e3c9f7d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1280



namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeFamily HeckeDetectorProfiles
noncomputable section

def inverseCoefficient (χ : Character) (V W : ℝ → ℂ) (Dstar D : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ)*IdealEuler.weighted (idealCoeff χ) s I*
    V ((Ideal.absNorm I : ℝ)/Dstar)*W ((Ideal.absNorm I : ℝ)/D)

def plainCoefficient (χ : Character) (W : ℝ → ℂ) (N : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  IdealEuler.weighted (idealCoeff χ) s I*W ((Ideal.absNorm I : ℝ)/N)

lemma scaled_exp_log_product (x y D N R : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hD : 0 < D) (hN : 0 < N) :
    (D*N/R)*Real.exp (Real.log (x/D)+Real.log (y/N)) = x*y/R := by
  rw [Real.exp_add, Real.exp_log (div_pos hx hD), Real.exp_log (div_pos hy hN)]
  field_simp

theorem actual_pair_profile (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hΩ : W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N) =
      inverseCoefficient χ V W₁ Dstar D s I*plainCoefficient χ W₂ N s J*
        logSourceFun Ω V T (2*D*N/Dstar) (D*N/Y) (D*N/U)
          (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) := by
  by_cases hW₁ : W₁ ((Ideal.absNorm I : ℝ)/D) = 0
  · simp [hW₁, inverseCoefficient]
  by_cases hW₂ : W₂ ((Ideal.absNorm J : ℝ)/N) = 0
  · simp [hW₂, plainCoefficient]
  have hx : 0 < (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hy : 0 < (Ideal.absNorm J : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hscale (R : ℝ) := scaled_exp_log_product (Ideal.absNorm I) (Ideal.absNorm J) D N R hx hy hD hN
  have htwo : (2*D*N/Dstar)*Real.exp
      (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) =
        2*((Ideal.absNorm I : ℝ)*(Ideal.absNorm J : ℝ))/Dstar := by
    calc
      _ = 2*((D*N/Dstar)*Real.exp
        (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N))) := by ring
      _ = _ := by rw [hscale]; ring
  unfold HeckeDetectorPartition.pairCoefficient inverseCoefficient plainCoefficient logSourceFun
  rw [hΩ hW₁ hW₂, one_mul, htwo, hscale Y, hscale U, map_mul]
  simp only [map_mul, Nat.cast_mul, expNeg]
  push_cast
  ring_nf

theorem actual_finite_pair_separation (χ : Character) (Ω V T W₁ W₂ : ℝ → ℂ)
    (hΩc : HasCompactSupport Ω) (hΩs : ContDiff ℝ ∞ Ω)
    (hVs : ContDiff ℝ ∞ V) (hTs : ContDiff ℝ ∞ T)
    (Dstar D N Y U : ℝ) (hD : 0 < D) (hN : 0 < N) (s : ℂ)
    (S R : Finset (Ideal O)) (hS : ∀ I ∈ S, I ≠ 0) (hR : ∀ J ∈ R, J ≠ 0)
    (hΩ : ∀ I ∈ S, ∀ J ∈ R,
      W₁ ((Ideal.absNorm I : ℝ)/D) ≠ 0 → W₂ ((Ideal.absNorm J : ℝ)/N) ≠ 0 →
      Ω (Real.log ((Ideal.absNorm I : ℝ)/D)+Real.log ((Ideal.absNorm J : ℝ)/N)) = 1) :
    (∑ I ∈ S, ∑ J ∈ R, HeckeDetectorPartition.pairCoefficient χ V T Dstar Y U s (I,J)*
      W₁ ((Ideal.absNorm I : ℝ)/D)*W₂ ((Ideal.absNorm J : ℝ)/N)) =
      ∫ t : ℝ,
        (𝓕 (logSource Ω V T hΩc hΩs hVs hTs (2*D*N/Dstar) (D*N/Y) (D*N/U))) t*
        phasePolynomial S (inverseCoefficient χ V W₁ Dstar D s)
          (fun I => Real.log ((Ideal.absNorm I : ℝ)/D)) t*
        phasePolynomial R (plainCoefficient χ W₂ N s)
          (fun J => Real.log ((Ideal.absNorm J : ℝ)/N)) t := by
  rw [← finite_pair_separation]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  exact actual_pair_profile χ Ω V T W₁ W₂ Dstar D N Y U hD hN s I J
    (hS I hI) (hR J hJ) (hΩ I hI J hJ)

end
end SevenEighths.HeckeDetectorFourier

end OAI
end OAIOriginalModule1280

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorProfilesCutoffs
Source SHA256: 56f14a849cd2803d601da72ace45e533aa9f608c3ab8d5f16030eef0e32093a8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1281


namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

abbrev cutoff : SchwartzMap ℝ ℂ := QuadraticInitialBound.sieveCutoff

lemma cutoff_one (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : cutoff x = 1 := by
  simp only [cutoff, QuadraticInitialBound.sieveCutoff_apply,
    QuadraticInitialBound.sieveBump_eq_one hx hx1, Complex.ofReal_one]

lemma cutoff_zero (x : ℝ) (hx : 2 ≤ x) : cutoff x = 0 := by
  rw [QuadraticInitialBound.sieveCutoff_apply]
  have hh := QuadraticInitialBound.sieveBump.zero_of_le_dist (x := x)
    (show QuadraticInitialBound.sieveBump.rOut ≤ dist x 0 by
      change 2 ≤ dist x 0
      simpa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)] using hx)
  rw [hh, Complex.ofReal_zero]

lemma cutoff_norm_le (x : ℝ) : ‖cutoff x‖ ≤ 1 := by
  rw [QuadraticInitialBound.sieveCutoff_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg QuadraticInitialBound.sieveBump.nonneg]
  exact QuadraticInitialBound.sieveBump.le_one

lemma annular_log_bound (x : ℝ) (hx : 0 ≤ x)
    (hactive : DyadicTransfer.annularCutoff cutoff x ≠ 0) : |Real.log x| ≤ Real.log 2 := by
  have hh := HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx 0
    (by simpa using hactive)
  norm_num at hh
  have hx0 : 0 < x := by linarith
  have hlo := Real.log_le_log (by norm_num : 0 < (2 : ℝ)⁻¹)
    (show (2 : ℝ)⁻¹ ≤ x by linarith)
  rw [Real.log_inv] at hlo
  exact abs_le.mpr ⟨hlo,Real.log_le_log hx0 hh.2.le⟩

theorem exists_product_log_cutoff :
    ∃ Ω : ℝ → ℂ, HasCompactSupport Ω ∧ ContDiff ℝ ∞ Ω ∧
      tsupport Ω ⊆ Set.Icc (-(2*Real.log 2+1)) (2*Real.log 2+1) ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        DyadicTransfer.annularCutoff cutoff x ≠ 0 → DyadicTransfer.annularCutoff cutoff y ≠ 0 →
        Ω (Real.log x+Real.log y) = 1 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨Ω,hc,hs,hone,hsupp,hzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff (2*Real.log 2) (by positivity)
  refine ⟨Ω,hc,hs,hsupp,?_⟩
  intro x y hx hy hax hay
  apply hone
  have hb1 := annular_log_bound x hx hax
  have hb2 := annular_log_bound y hy hay
  exact (abs_add_le _ _).trans (by linarith)

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end OAIOriginalModule1281

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorTail
Source SHA256: ebf5f37d2824454f7434c661aa8f0ee2f05e6a2bbdcd5103f4c5ee32c3619c9d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1282


namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorTail
open HeckeFamily HeckeDetectorWitnessArithmetic CompletedGauss
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

lemma exponential_cubic_bound (x Y : ℝ) (hx : 0 < x) (hY : 0 < Y) :
    x * Real.exp (-x/Y) ≤ 6*Y^3/x^2 := by
  have he := Real.pow_div_factorial_le_exp (x/Y) (show 0 ≤ x/Y by positivity) 3
  norm_num only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] at he
  have hh := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(x/Y))).le
  have hex : Real.exp (x/Y)*Real.exp (-(x/Y))=1 := by rw [←Real.exp_add]; simp
  rw [hex] at hh
  have hb : (x/Y)^3*Real.exp (-(x/Y)) ≤ 6 := by nlinarith
  calc
    _ = (Y^3/x^2)*((x/Y)^3*Real.exp (-(x/Y))) := by
      rw [neg_div]
      field_simp
    _ ≤ (Y^3/x^2)*6 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

lemma divisor_count (I : Ideal O) (hI : I ≠ 0) :
    ((idealDivisors I).card : ℝ) ≤ 128*(Ideal.absNorm I : ℝ) := by
  apply DescentFiberCost.finite_ideal_count_real
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  · intro J hJ
    exact ne_zero_of_dvd_ne_zero hI ((mem_idealDivisors hI).mp hJ)
  · intro J hJ
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
      (map_dvd Ideal.absNorm ((mem_idealDivisors hI).mp hJ))

theorem cutoffCoefficient_bound (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D : ℝ) (I : Ideal O) :
    ‖cutoffCoefficient V D I‖ ≤ 128*B*(Ideal.absNorm I : ℝ) := by
  by_cases hI : I = 0
  · simp [cutoffCoefficient,hI]
  rw [cutoffCoefficient,ite_eq_right hI]
  let e := mulFiberDivisorEquiv I hI
  have he : (∑' p : MulFiber I, (moebius p.val.1 : ℂ)*V ((Ideal.absNorm p.val.1 : ℝ)/D)) =
      ∑' J : {J : Ideal O // J ∈ idealDivisors I},
        (moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D) :=
    e.tsum_eq (fun J => (moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D))
  rw [he,tsum_fintype]
  calc
    _ ≤ ∑ J : {J : Ideal O // J ∈ idealDivisors I},
        ‖(moebius J.val : ℂ)*V ((Ideal.absNorm J.val : ℝ)/D)‖ := norm_sum_le _ _
    _ ≤ ∑ J : {J : Ideal O // J ∈ idealDivisors I}, B := by
      apply Finset.sum_le_sum
      intro J hJ
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (CubicEisenstein.norm_ideal_moebius_le_one _)).trans (hV _)
    _ = ((idealDivisors I).card : ℝ)*B := by simp
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right (divisor_count I hI) hB]

lemma norm_weight_two (I : Ideal O) (hI : I ≠ 0) :
    ‖CubicEisenstein.fullIdealWeight 2 I‖ = 1/(Ideal.absNorm I : ℝ)^2 := by
  rw [CubicEisenstein.fullIdealWeight,ite_eq_right hI,Complex.cpow_neg,Complex.cpow_ofNat,
    norm_inv,norm_pow,Complex.norm_natCast]
  simp [one_div]

lemma weighted_norm_le_one (χ : Character) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖IdealEuler.weighted (idealCoeff χ) s I‖ ≤ 1 := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, norm_zero]
    norm_num
  have hN : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  change ‖idealCoeff χ I*CubicEisenstein.fullIdealWeight s I‖ ≤ 1
  rw [norm_mul,CubicEisenstein.fullIdealWeight,ite_eq_right hI]
  have hc : (Ideal.absNorm I : ℂ) = ((Ideal.absNorm I : ℝ) : ℂ) := by norm_cast
  rw [hc,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ)<Ideal.absNorm I)]
  calc
    _ ≤ (1 : ℝ)*(Ideal.absNorm I : ℝ)^(-s.re) := by
      exact mul_le_mul_of_nonneg_right (idealCoeff_norm_le_one χ I) (by positivity)
    _ ≤ 1 := by
      simpa using Real.rpow_le_one_of_one_le_of_nonpos hN (neg_nonpos.mpr hs)

theorem exponentialTerm_bound (χ : Character) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖exponentialTerm χ V D s Y I‖ ≤
      (768*B*Y^3)*‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  by_cases hI : I = 0
  · simp [hI,exponentialTerm,cutoffCoefficient,CubicEisenstein.fullIdealWeight]
  have hN : (0 : ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(Y : ℂ))‖ =
      Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [exponentialTerm,norm_mul,norm_mul,he,norm_weight_two I hI]
  calc
    _ ≤ (128*B*(Ideal.absNorm I : ℝ))*Real.exp (-(Ideal.absNorm I : ℝ)/Y) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (mul_le_mul (cutoffCoefficient_bound V B hB hV D I)
        (weighted_norm_le_one χ s hs I) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ ≤ (128*B)*(6*Y^3/(Ideal.absNorm I : ℝ)^2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (exponential_cubic_bound _ Y hN hY) (by positivity)
    _ = _ := by ring

theorem exponentialTerm_summable (χ : Character) (V : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (D Y : ℝ) (hY : 0 < Y)
    (s : ℂ) (hs : 0 ≤ s.re) : Summable (exponentialTerm χ V D s Y) :=
  ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (768*B*Y^3)).of_norm_bounded (exponentialTerm_bound χ V B hB hV D Y hY s hs)

lemma cutoff_defect_bound (V : ℝ → ℂ) (B : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (x : ℝ) : ‖1-V x‖ ≤ 1+B :=
  (norm_sub_le _ _).trans (by simpa using add_le_add_left (hV x) 1)

def terminalRemainder (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    (1-T ((Ideal.absNorm I : ℝ)/U))

lemma exponentialTerm_half (χ : Character) (V : ℝ → ℂ) (D Y : ℝ)
    (_hY : 0 < Y) (s : ℂ) (I : Ideal O) :
    exponentialTerm χ V D s Y I = exponentialTerm χ V D s (2*Y) I *
      Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))) := by
  unfold exponentialTerm
  rw [mul_assoc (cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I),
    ←Complex.exp_add]
  congr 2
  push_cast
  ring

theorem terminalRemainder_bound (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re)
    (I : Ideal O) :
    ‖terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  by_cases hI : (Ideal.absNorm I : ℝ) ≤ U
  · rw [terminalRemainder,hTone _ (by positivity) ((div_le_one hU).mpr hI)]
    simp only [sub_self,mul_zero,norm_zero]
    positivity
  have he : ‖Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ)))‖ ≤
      Real.exp (-U/(2*Y)) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hc : (-((Ideal.absNorm I : ℝ) : ℂ)/(2*(Y : ℂ))).re =
        -(Ideal.absNorm I : ℝ)/(2*Y) := by
      rw [show (2 : ℂ)*(Y : ℂ) = ((2*Y : ℝ) : ℂ) by push_cast; rfl,
        ←Complex.ofReal_neg,←Complex.ofReal_div,Complex.ofReal_re]
    rw [hc]
    exact div_le_div_of_nonneg_right (by linarith [lt_of_not_ge hI]) (by positivity)
  rw [terminalRemainder,exponentialTerm_half χ V D Y hY s I]
  simp only [norm_mul]
  have h1 := mul_le_mul
    (exponentialTerm_bound χ V B hB hV D (2*Y) (by positivity) s hs I) he
    (norm_nonneg _) (by positivity)
  have h2 := mul_le_mul h1 (cutoff_defect_bound V B hV (2*(Ideal.absNorm I : ℝ)/D))
    (norm_nonneg _) (by positivity)
  have h3 := mul_le_mul h2 (cutoff_defect_bound T BT hT ((Ideal.absNorm I : ℝ)/U))
    (norm_nonneg _) (by positivity)
  apply h3.trans_eq
  ring

theorem terminalRemainder_summable (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    Summable (terminalRemainder χ V T D Y U s) :=
  ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left
    (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))).of_norm_bounded
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)

theorem terminalRemainder_tsum_bound (χ : Character) (V T : ℝ → ℂ) (B BT : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ B) (hT : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hTone : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1)
    (D Y U : ℝ) (hY : 0 < Y) (hU : 0 < U) (s : ℂ) (hs : 0 ≤ s.re) :
    ‖∑' I, terminalRemainder χ V T D Y U s I‖ ≤
      (6144*B*Y^3*(1+B)*(1+BT)*Real.exp (-U/(2*Y)))*
        ∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖ := by
  have hsum := terminalRemainder_summable χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs
  apply (norm_tsum_le_tsum_norm hsum.norm).trans
  rw [←tsum_mul_left]
  exact hsum.norm.tsum_le_tsum
    (terminalRemainder_bound χ V T B BT hB hBT hV hT hTone D Y U hY hU s hs)
    ((CubicEisenstein.fullIdealWeight_summable_norm 2 (by norm_num)).mul_left _)

theorem terminalRemainder_uniform_small (B BT ε : ℝ)
    (hB : 0 ≤ B) (hBT : 0 ≤ BT) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : Character) (V T : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ B) → (∀ x : ℝ, ‖T x‖ ≤ BT) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      ∀ (D : ℝ) (s : ℂ), 0 ≤ s.re →
      ‖∑' I, terminalRemainder χ V T D (U^20) (U^21) s I‖ < ε := by
  let C : ℝ := 6144*B*(1+B)*(1+BT)*(∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖)
  have ht : Tendsto (fun U : ℝ => C*(U^60*Real.exp (-U/2))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 60 (1/2) (by norm_num)).const_mul C
    convert h using 1
    · ext U
      rw [show (60 : ℝ) = ((60 : ℕ) : ℝ) by norm_num,Real.rpow_natCast]
      congr 2
      ring_nf
    · ring_nf
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ V T hV hT hTone D s hs
  have hUpos : 0 < U := by linarith
  have hb := terminalRemainder_tsum_bound χ V T B BT hB hBT hV hT hTone
    D (U^20) (U^21) (by positivity) (by positivity) s hs
  have he : -(U^21)/(2*U^20) = -U/2 := by
    rw [show U^21 = U^20*U by ring]
    field_simp
  have hp : (U^20)^3 = U^60 := by ring
  rw [he,hp] at hb
  have hC : (6144*B*U^60*(1+B)*(1+BT)*Real.exp (-U/2))*
      (∑' I : Ideal O, ‖CubicEisenstein.fullIdealWeight 2 I‖) = C*(U^60*Real.exp (-U/2)) := by
    dsimp [C]
    ring
  rw [hC] at hb
  exact hb.trans_lt (hU₀ U hU₀')

theorem exponential_sum_tail_unconditional (χ : Character) (V : ℝ → ℂ)
    (B D Y : ℝ) (hB : 0 ≤ B) (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) :=
  exponential_sum_tail χ V D hD hV hVzero s Y
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs)

def terminalTerm (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    T ((Ideal.absNorm I : ℝ)/U)

private lemma summable_mul_bounded {A : Type*} (f g : A → ℂ)
    (hf : Summable f) (B : ℝ) (hg : ∀ a, ‖g a‖ ≤ B) :
    Summable (fun a => f a*g a) :=
  (hf.norm.mul_right B).of_norm_bounded (fun a => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hg a) (norm_nonneg _))

theorem terminal_sum_identity (χ : Character) (V T : ℝ → ℂ)
    (B BT D Y U : ℝ) (hB : 0 ≤ B)
    (hVbound : ∀ x : ℝ, ‖V x‖ ≤ B) (hTbound : ∀ x : ℝ, ‖T x‖ ≤ BT)
    (hD : 2 ≤ D) (hY : 0 < Y)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (hs : 0 ≤ s.re) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      (∑' I : Ideal O, exponentialTerm χ V D s Y I) - Complex.exp (-1/(Y : ℂ)) -
        ∑' I : Ideal O, terminalRemainder χ V T D Y U s I := by
  let f := fun I : Ideal O => exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D))
  have hf : Summable f := summable_mul_bounded _ _
    (exponentialTerm_summable χ V B hB hVbound D Y hY s hs) (1+B)
    (fun I => cutoff_defect_bound V B hVbound _)
  have hr : Summable (terminalRemainder χ V T D Y U s) :=
    summable_mul_bounded f _ hf (1+BT) (fun I => cutoff_defect_bound T BT hTbound _)
  have hi : terminalTerm χ V T D Y U s = fun I => f I-terminalRemainder χ V T D Y U s I := by
    funext I
    dsimp [f,terminalTerm,terminalRemainder]
    ring
  rw [hi,hf.tsum_sub hr]
  rw [show (∑' I, f I) = (∑' I, exponentialTerm χ V D s Y I)-Complex.exp (-1/(Y : ℂ)) from
    exponential_sum_tail_unconditional χ V B D Y hB hVbound hD hY hV hVzero s hs]

theorem terminal_sum_finite (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hTzero : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ I ∈ ConcretePrimeRowBridge.idealsUpTo ⌈2*U⌉₊, terminalTerm χ V T D Y U s I := by
  apply tsum_eq_sum
  intro I hI
  by_cases hI0 : I = 0
  · simp [terminalTerm,exponentialTerm,cutoffCoefficient,hI0]
  have hN : (⌈2*U⌉₊ : ℝ) < Ideal.absNorm I := by
    have hn : ¬Ideal.absNorm I ≤ ⌈2*U⌉₊ := by
      intro hh
      apply hI
      exact ConcretePrimeRowBridge.mem_idealsUpTo.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0),hh⟩
    exact_mod_cast lt_of_not_ge hn
  have ht : T ((Ideal.absNorm I : ℝ)/U)=0 := by
    apply hTzero
    apply (le_div_iff₀ hU).mpr
    linarith [Nat.le_ceil (2*U)]
  simp only [terminalTerm,ht,mul_zero]

end SevenEighths.HeckeDetectorTail

end

end OAI
end OAIOriginalModule1282

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientBounds
Source SHA256: 6c782794201b4449e84a7c8be2b71baab283954a0b5a448bd0676f9011d3f4e3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1283



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorCoefficientBounds
open HeckeFamily HeckeDetectorFourier HeckeDetectorTail
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma annular_norm_le_two (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1) (x : ℝ) :
    ‖DyadicTransfer.annularCutoff V x‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans (by linarith [hV x,hV (2*x)])

lemma inverseCoefficient_norm_le_two (χ : Character) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (Dstar D : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖ ≤ 2 := by
  simp only [inverseCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*1*1*2 := by
      gcongr
      · exact CubicEisenstein.norm_ideal_moebius_le_one I
      · exact weighted_norm_le_one χ s hs I
      · exact hV _
      · exact annular_norm_le_two V hV _
    _ = _ := by norm_num

lemma plainCoefficient_norm_le_two (χ : Character) (V : ℝ → ℂ)
    (hV : ∀ x, ‖V x‖ ≤ 1) (N : ℝ) (s : ℂ) (hs : 0 ≤ s.re) (I : Ideal O) :
    ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖ ≤ 2 := by
  simp only [plainCoefficient,norm_mul]
  calc
    _ ≤ (1 : ℝ)*2 := mul_le_mul (weighted_norm_le_one χ s hs I)
      (annular_norm_le_two V hV _) (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

def expandedSet (U : ℝ) : Finset (Ideal O) := idealsUpTo ⌈16*U^21⌉₊

lemma expandedSet_count (U : ℝ) (hU : 1 ≤ U) :
    ((expandedSet U).card : ℝ) ≤ 4096*U^21 := by
  have hp : 1 ≤ U^21 := one_le_pow₀ hU
  have hc : (1 : ℝ) ≤ ⌈16*U^21⌉₊ := (by linarith : (1 : ℝ) ≤ 16*U^21).trans (Nat.le_ceil _)
  have h := DescentFiberCost.finite_ideal_count_real (expandedSet U) (⌈16*U^21⌉₊ : ℝ) hc
    (fun I hI => Ideal.absNorm_eq_zero_iff.not.mp (by have := (mem_idealsUpTo.mp hI).1; omega))
    (fun I hI => by exact_mod_cast (mem_idealsUpTo.mp hI).2)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 16*U^21 by positivity)
  linarith

theorem coefficient_mass (χ : Character) (V : ℝ → ℂ) (hV : ∀ x, ‖V x‖ ≤ 1)
    (U Dstar D N : ℝ) (hU : 1 ≤ U) (s : ℂ) (hs : 0 ≤ s.re) :
    ((∑ I ∈ expandedSet U, ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖)*
      (∑ I ∈ expandedSet U, ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖)) ≤
      67108864*U^42 := by
  have hi : (∑ I ∈ expandedSet U,
      ‖inverseCoefficient χ V (DyadicTransfer.annularCutoff V) Dstar D s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => inverseCoefficient_norm_le_two χ V hV Dstar D s hs I)
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hp : (∑ I ∈ expandedSet U,
      ‖plainCoefficient χ (DyadicTransfer.annularCutoff V) N s I‖) ≤ 8192*U^21 := by
    have h := Finset.sum_le_sum (s := expandedSet U)
      (fun I hI => plainCoefficient_norm_le_two χ V hV N s hs I)
    simp only [Finset.sum_const,nsmul_eq_mul] at h
    linarith [expandedSet_count U hU]
  have hh := mul_le_mul hi hp
    (Finset.sum_nonneg (fun I hI => norm_nonneg _)) (by positivity)
  apply hh.trans_eq
  ring

end SevenEighths.HeckeDetectorCoefficientBounds

end

end OAI
end OAIOriginalModule1283

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFinite
Source SHA256: 1cad5f111e1143f0095b5a5663ffe5dd05a6f6900a5d64b3f00f22085127a997
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1284



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorFinite
open HeckeFamily HeckeDetectorWitnessArithmetic HeckeDetectorTail HeckeDetectorPartition
open CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def pairSet (U : ℝ) : Finset (Ideal O × Ideal O) :=
  (idealsUpTo ⌈2*U⌉₊) ×ˢ (idealsUpTo ⌈2*U⌉₊)

lemma pairCoefficient_zero_left (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (0,J) = 0 := by
  simp only [pairCoefficient,zero_mul,map_zero,mul_zero]

lemma pairCoefficient_zero_right (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (J : Ideal O) :
    pairCoefficient χ V T D Y U s (J,0) = 0 := by
  simp only [pairCoefficient,mul_zero,map_zero,zero_mul]

theorem pairCoefficient_support (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ)
    (p : Ideal O × Ideal O) (hp : p ∉ pairSet U) :
    pairCoefficient χ V T D Y U s p = 0 := by
  by_cases h1 : p.1 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h1]
    exact pairCoefficient_zero_left χ V T D Y U s p.2
  by_cases h2 : p.2 = 0
  · change pairCoefficient χ V T D Y U s (p.1,p.2) = 0
    rw [h2]
    exact pairCoefficient_zero_right χ V T D Y U s p.1
  have hprod : p.1*p.2 ≠ 0 := mul_ne_zero h1 h2
  have hnpos : 0 < Ideal.absNorm (p.1*p.2) := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hprod)
  have hnorm : 2*U ≤ (Ideal.absNorm (p.1*p.2) : ℝ) := by
    by_contra h
    have hb : Ideal.absNorm (p.1*p.2) ≤ ⌈2*U⌉₊ := by
      exact_mod_cast (le_trans (lt_of_not_ge h).le (Nat.le_ceil (2*U)))
    have hh1 : Ideal.absNorm p.1 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_right p.1 p.2))
    have hh2 : Ideal.absNorm p.2 ≤ Ideal.absNorm (p.1*p.2) :=
      Nat.le_of_dvd hnpos (map_dvd Ideal.absNorm (dvd_mul_left p.2 p.1))
    apply hp
    exact Finset.mem_product.mpr
      ⟨mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h1),hh1.trans hb⟩,
       mem_idealsUpTo.mpr ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr h2),hh2.trans hb⟩⟩
  have hz := hT ((Ideal.absNorm (p.1*p.2) : ℝ)/U) ((le_div_iff₀ hU).mpr hnorm)
  simp only [pairCoefficient,hz,mul_zero]

theorem pair_fiber (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) :
    (∑' p : MulFiber I, pairCoefficient χ V T D Y U s p.val) =
      terminalTerm χ V T D Y U s I := by
  have h := weighted_fiber χ V D s I
  unfold terminalTerm exponentialTerm
  rw [←h,←tsum_mul_right,←tsum_mul_right,←tsum_mul_right]
  apply tsum_congr
  intro p
  simp only [pairCoefficient,p.property]

theorem terminal_sum_eq_pair_sum (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ p ∈ pairSet U, pairCoefficient χ V T D Y U s p := by
  have hfinite : Function.HasFiniteSupport (pairCoefficient χ V T D Y U s) := by
    apply (pairSet U).finite_toSet.subset
    intro p hp
    by_contra hn
    exact hp (pairCoefficient_support χ V T D Y U hU hT s p hn)
  have hsum := (summable_of_hasFiniteSupport hfinite).hasSum.tsum_fiberwise
    (fun p : Ideal O × Ideal O => p.1*p.2)
  change HasSum (fun I : Ideal O => ∑' p : MulFiber I, pairCoefficient χ V T D Y U s p.val)
    (∑' p, pairCoefficient χ V T D Y U s p) at hsum
  simp_rw [pair_fiber] at hsum
  rw [hsum.tsum_eq]
  exact tsum_eq_sum (pairCoefficient_support χ V T D Y U hU hT s)

def dyadicBlock (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (j k : ℕ) : ℂ :=
  ∑ p ∈ pairSet U, pairCoefficient χ V T D Y U s p *
    DyadicTransfer.annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
    DyadicTransfer.annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k)

theorem terminal_sum_eq_dyadic (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    (∑' I : Ideal O, terminalTerm χ V T D Y U s I) =
      ∑ j ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
        ∑ k ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1), dyadicBlock χ V T D Y U s j k := by
  have hX : (0 : ℝ) < ⌈2*U⌉₊ := lt_of_lt_of_le (by positivity) (Nat.le_ceil (2*U))
  rw [terminal_sum_eq_pair_sum χ V T D Y U hU hT s]
  apply actual_pair_reassembly χ V T hV hVzero D Y U _ _ hX hX s
  intro p hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hp
  obtain ⟨hp1,hp1b⟩ := mem_idealsUpTo.mp h1
  obtain ⟨hp2,hp2b⟩ := mem_idealsUpTo.mp h2
  exact ⟨Ideal.absNorm_eq_zero_iff.not.mp (by omega),
    Ideal.absNorm_eq_zero_iff.not.mp (by omega),by exact_mod_cast hp1b,by exact_mod_cast hp2b⟩

theorem exists_dyadic_block (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hU : 0 < U) (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (c : ℝ)
    (hc : c ≤ ‖∑' I : Ideal O, terminalTerm χ V T D Y U s I‖) :
    ∃ j ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
      ∃ k ∈ Finset.range (length (⌈2*U⌉₊ : ℝ)+1),
        c ≤ (((length (⌈2*U⌉₊ : ℝ)+1 : ℕ) : ℝ)^2)*‖dyadicBlock χ V T D Y U s j k‖ := by
  rw [terminal_sum_eq_dyadic χ V T D Y U hU hT hV hVzero s] at hc
  obtain ⟨j,hj,k,hk,hb⟩ := exists_large_pair (length (⌈2*U⌉₊ : ℝ))
    (length (⌈2*U⌉₊ : ℝ)) (dyadicBlock χ V T D Y U s)
  exact ⟨j,hj,k,hk,by simpa only [pow_two] using hc.trans hb⟩

theorem nonzero_block_scale_bounds (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ)
    (hD : 0 < D) (hU : 0 < U)
    (hT : ∀ x : ℝ, 2 ≤ x → T x = 0)
    (hV : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1)
    (hVzero : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) (j k : ℕ)
    (hb : dyadicBlock χ V T D Y U s j k ≠ 0) :
    (2 : ℝ)^j < 4*D ∧ D/8 < (2 : ℝ)^j*(2 : ℝ)^k ∧
      (2 : ℝ)^j*(2 : ℝ)^k < 8*U := by
  obtain ⟨p,hp,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hk := (mul_ne_zero_iff.mp hne).2
  have hj := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).2
  have hc := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1
  simp only [pairCoefficient,ne_eq,mul_eq_zero,not_or] at hc
  obtain ⟨⟨⟨⟨⟨hmu,hfirst⟩,hweight⟩,hexp⟩,hproduct⟩,hterminal⟩ := hc
  apply pair_scale_bounds V T hV hVzero hT
    (Ideal.absNorm p.1) (Ideal.absNorm p.2) D U (by positivity) (by positivity)
    hD hU j k hj hk hfirst
  · simpa only [map_mul,Nat.cast_mul] using hproduct
  · simpa only [map_mul,Nat.cast_mul] using hterminal

end SevenEighths.HeckeDetectorFinite

end

end OAI
end OAIOriginalModule1284

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorBudget
Source SHA256: 9e41194ee21e1ad7aa6f698638b19420293f71d33f7bd863e7191f2d70118f80
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1285


namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorBudget
open HeckeDetectorPartition

lemma source_length_bound (U : ℝ) (hU : 2 ≤ U) :
    ((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ) ≤ 25*Real.logb 2 U := by
  have hUp : 0 < U := by linarith
  have hp : 1 ≤ U^21 := one_le_pow₀ (by linarith) (n := 21)
  have hc : (1 : ℝ) ≤ ⌈2*U^21⌉₊ := le_trans (by linarith) (Nat.le_ceil (2*U^21))
  have hcu : (⌈2*U^21⌉₊ : ℝ) ≤ 4*U^21 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2*U^21 by positivity)
    linarith
  have hl : 1 ≤ Real.logb 2 U := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by norm_num : (0 : ℝ)<2) hU
    simpa using h
  have hb := length_bound (⌈2*U^21⌉₊ : ℝ) hc
  have hm := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2) (by linarith : (0 : ℝ)<⌈2*U^21⌉₊) hcu
  have he : Real.logb 2 (4*U^21) = 2+21*Real.logb 2 U := by
    rw [Real.logb_mul (by norm_num) (by positivity),Real.logb_pow]
    have hfour : Real.logb 2 4 = 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num,Real.logb_pow]
      norm_num
    rw [hfour]
    norm_num
  rw [he] at hm
  push_cast
  linarith

lemma source_pair_count_bound (U : ℝ) (hU : 2 ≤ U) :
    (((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ)^2) ≤ 625*(Real.logb 2 U)^2 := by
  have h := source_length_bound U hU
  have hl : 0 ≤ Real.logb 2 U := Real.logb_nonneg (by norm_num) (by linarith)
  nlinarith [sq_nonneg (((length (⌈2*U^21⌉₊ : ℝ)+1 : ℕ) : ℝ)-25*Real.logb 2 U)]

end SevenEighths.HeckeDetectorBudget

end

end OAI
end OAIOriginalModule1285

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorZeros
Source SHA256: c976e6f433fd0963051eb31cd16607ac9c7d0d4f0fcb9810e173ee730a400727
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1286




namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology
namespace SevenEighths.HeckeDetectorZeros
open HeckeFamily

def rectangle (T : ℝ) : Set ℂ :=
  {s | (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T}

theorem rectangle_compact (T : ℝ) : IsCompact (rectangle T) := by
  have heq : rectangle T = Set.Icc (51/100 : ℝ) 1 ×ℂ Set.Icc (-T) T := by
    ext z
    simp only [rectangle, Set.mem_ofPred_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le]
    tauto
  rw [heq]
  exact isCompact_Icc.reProdIm isCompact_Icc

def zeros (χ : Character) (T : ℝ) : Set ℂ := {s ∈ rectangle T | LFunction χ s = 0}

theorem zeros_finite (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) :
    (zeros χ T).Finite := by
  have ha : AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (LFunction_entire_nonprincipal χ hχ)
  have hcod := ha.preimage_zero_mem_codiscreteWithin
    (LFunction_ne_zero_of_one_lt_re χ (by norm_num : 1 < (2 : ℂ).re))
    (Set.mem_univ (2 : ℂ)) isConnected_univ
  have hfin := (rectangle_compact T).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (Set.subset_univ (rectangle T)) hcod)
  convert hfin using 1
  ext s
  simp [zeros]

def zeroFinset (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) : Finset ℂ :=
  (zeros_finite χ hχ T).toFinset

@[simp] theorem mem_zeroFinset (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) (s : ℂ) :
    s ∈ zeroFinset χ hχ T ↔
      (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
  simp only [zeroFinset, Set.Finite.mem_toFinset, zeros, rectangle, Set.mem_ofPred_eq]
  tauto

variable {ι : Type*} [Fintype ι]

def familyZeros (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    Finset (ι × ℂ) :=
  Finset.univ.biUnion (fun i => (zeroFinset (χ i) (hχ i) T).image (fun s => (i,s)))

@[simp] theorem mem_familyZeros (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (T : ℝ) (i : ι) (s : ℂ) :
    (i,s) ∈ familyZeros χ hχ T ↔
      (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ LFunction (χ i) s = 0 := by
  simp [familyZeros]

def realParts (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) : Finset ℝ :=
  insert (51/100) ((familyZeros χ hχ T).image (fun p => p.2.re))

theorem realParts_nonempty (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    (realParts χ hχ T).Nonempty := Finset.insert_nonempty _ _

def zeroMaximum (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) : ℝ :=
  (realParts χ hχ T).max' (realParts_nonempty χ hχ T)

theorem zeroMaximum_mem (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    zeroMaximum χ hχ T ∈ realParts χ hχ T := Finset.max'_mem _ _

theorem zeroMaximum_bounds (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    (51/100 : ℝ) ≤ zeroMaximum χ hχ T ∧ zeroMaximum χ hχ T ≤ 1 := by
  constructor
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨⟨i,s⟩, hs, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_familyZeros χ hχ T i s |>.mp hs).2.1

theorem zero_re_le_maximum (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (T : ℝ) (i : ι) {s : ℂ} (hs : (51/100 : ℝ) ≤ s.re)
    (ht : |s.im| ≤ T) (hz : LFunction (χ i) s = 0) : s.re ≤ zeroMaximum χ hχ T := by
  have hle : s.re ≤ 1 := by
    by_contra hn
    exact LFunction_ne_zero_of_one_lt_re (χ i) (lt_of_not_ge hn) hz
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i,s), (mem_familyZeros χ hχ T i s).mpr ⟨hs, hle, ht, hz⟩, rfl⟩)

theorem maximum_attained (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ)
    (hmax : (51/100 : ℝ) < zeroMaximum χ hχ T) :
    ∃ i s, LFunction (χ i) s = 0 ∧ |s.im| ≤ T ∧ s.re = zeroMaximum χ hχ T := by
  have hm := zeroMaximum_mem χ hχ T
  rcases Finset.mem_insert.mp hm with hm | hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i,s⟩, hs, heq⟩ := Finset.mem_image.mp hm
    have hz := (mem_familyZeros χ hχ T i s).mp hs
    exact ⟨i,s,hz.2.2.2,hz.2.2.1,heq⟩

theorem zeroMaximum_mono (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    {T T' : ℝ} (hT : T ≤ T') : zeroMaximum χ hχ T ≤ zeroMaximum χ hχ T' := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i,s,hz,ht,heq⟩ := maximum_attained χ hχ T hm
    rw [← heq]
    apply zero_re_le_maximum χ hχ T' i _ (ht.trans hT) hz
    rw [heq]
    exact hm.le
  · exact hm.trans (zeroMaximum_bounds χ hχ T').1

theorem nonzero_on_buffered_disk (χ : ι → Character) (hχ : ∀ j, (χ j).residue ≠ 1)
    (T a e : ℝ) (i : ℕ) (hT : 2 < T) (ha : (51/100 : ℝ) ≤ a) (he : 0 < e)
    (hmax : zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e)
    (j : ι) (t : ℝ) (ht : |t| ≤ (3*i+2 : ℕ)*T)
    {s : ℂ} (hs : s ∈ Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    LFunction (χ j) s ≠ 0 := by
  have hn : ‖s-((2 : ℂ)+t*Complex.I)‖ ≤ 2-a-2*e := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2 : ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (s-((2 : ℂ)+t*Complex.I))
  norm_num at hr hi
  have hre : a+2*e ≤ s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  have him : |s.im| ≤ 3*(i+1 : ℕ)*T := by
    have ht' := abs_add_le (s.im-t) t
    rw [sub_add_cancel] at ht'
    push_cast at ht ⊢
    nlinarith [hi.trans hn]
  intro hz
  have hle := zero_re_le_maximum χ hχ (3*(i+1 : ℕ)*T) j (by linarith) him hz
  linarith

theorem exists_actual_buffered_bin (χ : ι → Character)
    (hχ : ∀ j, (χ j).residue ≠ 1) (T e : ℝ) (hT : 2 < T) (he : 0 < e)
    (n : ℕ) (hn : 0 < n) (hwidth : (49/100 : ℝ) ≤ n*e) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ n ∧
      let a : ℝ := 51/100+e*k
      a ≤ 1 ∧ a ≤ zeroMaximum χ hχ (3*i*T) ∧
      zeroMaximum χ hχ (3*i*T) < a+e ∧
      zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e ∧
      (51/100 < a → ∃ j s, LFunction (χ j) s = 0 ∧ a ≤ s.re ∧
        s.re < a+e ∧ |s.im| ≤ 3*i*T) ∧
      (∀ j t, |t| ≤ (3*i+2 : ℕ)*T → ∀ s ∈
        Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction (χ j) s ≠ 0) := by
  let M : ℕ → ℝ := fun j => zeroMaximum χ hχ (3*(j+1 : ℕ)*T)
  obtain ⟨i,hk,k,hone,hlo,hhi,hnext⟩ := Detector.exists_buffered_bin M hn he
    (fun j _ => zeroMaximum_bounds χ hχ _) hwidth
  refine ⟨i+1,k,by omega,by omega,hone,hlo,hhi,?_,?_,?_⟩
  · exact hnext
  · intro ha
    obtain ⟨j,s,hz,ht,hs⟩ := maximum_attained χ hχ (3*(i+1 : ℕ)*T) (lt_of_lt_of_le ha hlo)
    exact ⟨j,s,hz,by rw [hs]; exact hlo,by rw [hs]; exact hhi,ht⟩
  · intro j t ht s hs
    apply nonzero_on_buffered_disk χ hχ T (51/100+e*k) e (i+1) hT
      (by nlinarith [Nat.cast_nonneg (α := ℝ) k]) he hnext j t ht hs

end SevenEighths.HeckeDetectorZeros

end

end OAI
end OAIOriginalModule1286

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Dirichlet
Source SHA256: 8b33d23c18ec5b85a13043aa775841389903247645fc00536cc2b3286332ff7d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1287


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDirichlet
open HeckeFamily

variable {q : ℕ}

def modulus (q : ℕ) : Ideal O := Ideal.span {(q : O)}

theorem modulus_ne_bot [NeZero q] : modulus q ≠ ⊥ := by
  simpa only [modulus, ne_eq, Ideal.span_singleton_eq_bot] using
    (Nat.cast_ne_zero.mpr (NeZero.ne q) : (q : O) ≠ 0)

theorem quotient_modulus_zero : (q : O ⧸ modulus q) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (modulus q))]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem norm_span_dvd (z : O) :
    z ∣ (Ideal.absNorm (Ideal.span {z}) : O) := by
  have h : (Ideal.absNorm (Ideal.span {z}) : ℤ) =
      ShortDraftLatticeCount.q (ActualEisensteinCoordinates.coords z) := by
    rw [← ActualEisensteinCubic.qNat_eq_absNorm_span]
    exact Int.toNat_of_nonneg (ShortDraftLatticeCount.qO_nonneg z)
  rw [← Int.cast_natCast, h]
  exact ⟨_, ActualEisensteinCubic.coordinate_norm_eq_mul_conjO z⟩

theorem quotient_unit_of_norm_unit (z : O)
    (hz : IsUnit (Ideal.absNorm (Ideal.span {z}) : ZMod q)) :
    IsUnit (Ideal.Quotient.mk (modulus q) z) := by
  have hc := (ZMod.isUnit_iff_coprime _ _).mp hz
  have hi : IsCoprime (Ideal.absNorm (Ideal.span {z}) : O ⧸ modulus q) (q : O ⧸ modulus q) := by
    simpa only [map_natCast] using hc.isCoprime.map (Int.castRingHom (O ⧸ modulus q))
  rw [quotient_modulus_zero, isCoprime_zero_right] at hi
  obtain ⟨w, hw⟩ := norm_span_dvd z
  have hn : (Ideal.absNorm (Ideal.span {z}) : O ⧸ modulus q) =
      Ideal.Quotient.mk (modulus q) z * Ideal.Quotient.mk (modulus q) w := by
    rw [← map_mul, ← hw, map_natCast]
  rw [hn] at hi
  exact isUnit_of_mul_isUnit_left hi

def residue (χ : DirichletCharacter ℂ q) : MulChar (O ⧸ modulus q) ℂ where
  toFun x := Quotient.liftOn' x (InitialMeanSquare.normCharacter χ) (by
    intro a b hab
    exact CanonicalCoefficientClass.normCharacter_factorsModulo χ a b
      ((modulus q).quotientRel_def.mp hab))
  map_one' := (InitialMeanSquare.normCharacter χ).map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact (InitialMeanSquare.normCharacter χ).map_mul a b
  map_nonunit' x hx := by
    refine Quotient.inductionOn' x (fun z hz => ?_) hx
    change χ (Ideal.absNorm (Ideal.span {z})) = 0
    apply MulChar.map_nonunit
    exact fun h => hz (quotient_unit_of_norm_unit z h)

@[simp] theorem residue_mk (χ : DirichletCharacter ℂ q) (z : O) :
    residue χ (Ideal.Quotient.mk (modulus q) z) = χ (Ideal.absNorm (Ideal.span {z})) := rfl

theorem residue_unit_trivial (χ : DirichletCharacter ℂ q) (u : Oˣ) :
    residue χ (Ideal.Quotient.mk (modulus q) (u : O)) = 1 := by
  rw [residue_mk, Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top]
  simp

variable [NeZero q]

def character (χ : DirichletCharacter ℂ q) : Character :=
  Character.ofResidue (modulus q) modulus_ne_bot (residue χ) (residue_unit_trivial χ)

@[simp] theorem elementCoeff_character (χ : DirichletCharacter ℂ q) (z : O) :
    elementCoeff (character χ) z = χ (Ideal.absNorm (Ideal.span {z})) := rfl

theorem idealCoeff_character (χ : DirichletCharacter ℂ q) (I : Ideal O) (hI : I ≠ 0) :
    idealCoeff (character χ) I = χ (Ideal.absNorm I) := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator I]
  rw [idealCoeff_span _ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI),
    elementCoeff_character, ConcretePrimeRowBridge.span_idealGenerator]

theorem moebius_idealCoeff_character (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    (UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff (character χ) I =
      ShortDraftHeckeBridge.baseChangeWeight χ I := by
  by_cases hI : I = 0
  · subst I
    unfold ShortDraftHeckeBridge.baseChangeWeight
    rw [UniqueFactorizationMonoid.moebius_zero]
    simp
  · rw [idealCoeff_character χ I hI]
    rfl

theorem inverseSeries_eq_pairInverse_LSeries (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    IdealEuler.inverseSeries (idealCoeff (character χ)) s =
      LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ (ShortDraftHeckeBridge.baseChangeChar χ)) s := by
  rw [IdealEuler.inverseSeries]
  have ht (I : Ideal O) : (UniqueFactorizationMonoid.moebius I : ℂ) *
      IdealEuler.weighted (idealCoeff (character χ)) s I =
      ShortDraftHeckeBridge.baseChangeWeight χ I * CubicEisenstein.fullIdealWeight s I := by
    change (UniqueFactorizationMonoid.moebius I : ℂ) *
      (idealCoeff (character χ) I * CubicEisenstein.fullIdealWeight s I) = _
    rw [← mul_assoc, moebius_idealCoeff_character]
  simp_rw [ht]
  rw [SmoothMobiusCorrection.idealDirichlet_eq_LSeries _
    (ConcretePrimeRowBridge.baseChangeWeight_norm_le_one χ) s hs]
  exact ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse χ
    (ShortDraftHeckeBridge.baseChangeChar χ) _
    (ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff χ) s

theorem LFunction_eq_dirichlet_product_right (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LFunction (character χ) s = χ.LFunction s *
      (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s := by
  have hH := inverseSeries_mul_LFunction (character χ) hs
  have hD := ShortDraftHeckeBridge.pair_inverse_euler_identity χ
    (ShortDraftHeckeBridge.baseChangeChar χ) s hs
  rw [inverseSeries_eq_pairInverse_LSeries χ hs] at hH
  have hne : LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ
      (ShortDraftHeckeBridge.baseChangeChar χ)) s ≠ 0 := by
    intro h
    rw [h, zero_mul] at hH
    exact zero_ne_one hH
  apply mul_left_cancel₀ hne
  rw [hH, mul_comm, hD]

theorem LFunction_eq_dirichlet_product (χ : DirichletCharacter ℂ q)
    {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    LFunction (character χ) s = χ.LFunction s *
      (ShortDraftHeckeBridge.baseChangeChar χ).LFunction s := by
  let U : Set ℂ := {0,1}ᶜ
  have hU : IsOpen U := (Set.toFinite ({0,1} : Set ℂ)).isClosed.isOpen_compl
  have hpc : IsPreconnected U :=
    ((Set.toFinite ({0,1} : Set ℂ)).countable.isConnected_compl_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isPreconnected
  have hmem : s ∈ U := by simp [U, h0, h1]
  have htwo : (2 : ℂ) ∈ U := by norm_num [U]
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := LFunction (character χ))
    (g := fun z => χ.LFunction z * (ShortDraftHeckeBridge.baseChangeChar χ).LFunction z)
    _ _ hpc htwo _ hmem
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hz' : z ≠ 0 ∧ z ≠ 1 := by simpa [U] using hz
    exact (LFunction_differentiableAt _ hz'.1 (Or.inl hz'.2)).differentiableWithinAt
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have hz' : z ≠ 1 := by simp only [U, Set.mem_compl_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hz; exact hz.2
    exact ((χ.differentiableAt_LFunction z (Or.inl hz')).mul
      ((ShortDraftHeckeBridge.baseChangeChar χ).differentiableAt_LFunction z
        (Or.inl hz'))).differentiableWithinAt
  · filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact LFunction_eq_dirichlet_product_right χ hz

theorem dirichlet_seven_eighths_of_hecke
    (hH : ∀ (η : Character) (s : ℂ), (7/8 : ℝ) < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8 : ℝ) < s.re)
    (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h := hH (character χ) s hs (Or.inl hs1)
  rw [LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_seven_eighths_of_hecke
    (hH : ∀ (η : Character) (s : ℂ), (7/8 : ℝ) < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (s : ℂ) (hs : (7/8 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_seven_eighths_of_hecke hH (1 : DirichletCharacter ℂ 1) s hs
    (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end SevenEighths.HeckeDirichlet

end

end OAI
end OAIOriginalModule1287

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.IdealOperations
Source SHA256: 81fb7846d22a952e64ca4e97177b11aa443a0a7b9be827a6be13da8576c8f01e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1288



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem idealCoeff_product (χ ψ : Character) (I : Ideal O) :
    idealCoeff (χ.product ψ) I = idealCoeff χ I * idealCoeff ψ I :=
  IdealCharacter.ofResidue_product _ _ _ _ _ _ I

theorem exists_primitive_character (χ : Character) :
    ∃ ψ : Character,
      χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  obtain ⟨M, φ, hφ, hM, hM₀, hprim, hnorm, hmask, _⟩ :=
    IdealCharacter.exists_primitive_associate χ.modulus χ.residue χ.unit_trivial
  exact ⟨Character.ofResidue M hM₀ φ hφ, hM, hprim, hnorm, hmask⟩

theorem exists_primitive_product_character (χ ψ : Character) :
    ∃ ρ : Character,
      χ.modulus ⊓ ψ.modulus ≤ ρ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ρ.residue ∧
      ρ.modulus.absNorm ≤ χ.modulus.absNorm * ψ.modulus.absNorm ∧
      ∀ I : Ideal O, idealCoeff χ I * idealCoeff ψ I =
        if IsCoprime I (χ.modulus ⊓ ψ.modulus) then idealCoeff ρ I else 0 := by
  let : Finite (O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Finite (O ⧸ ψ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient ψ.modulus_ne_bot
  obtain ⟨M, φ, hφ, hM, hM₀, hprim, hnorm, hmask, _⟩ :=
    IdealCharacter.exists_primitive_product_associate χ.modulus ψ.modulus
      χ.residue ψ.residue χ.unit_trivial ψ.unit_trivial
  exact ⟨Character.ofResidue M hM₀ φ hφ, hM, hprim, hnorm, hmask⟩

end SevenEighths.HeckeFamily

end

end OAI
end OAIOriginalModule1288

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Conjugation
Source SHA256: 2350c2d8eb7ee17af11ac6d3ee52fd57ac4e48e3a97ae16058041a95b70c8278
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1289



namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex
namespace SevenEighths.HeckeFamily

theorem idealCoeff_inverse_conj (χ : Character) (J : Ideal O) :
    idealCoeff χ.inverse J=conj (idealCoeff χ J) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  by_cases hJ : J=0
  · subst J
    rw [map_zero,map_zero,map_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,
    idealCoeff_span χ.inverse hg,idealCoeff_span χ hg]
  exact (MulChar.star_apply' χ.residue _).symm

theorem idealTerm_inverse_conj (χ : Character) (s : ℂ) (J : Ideal O) :
    idealTerm χ.inverse s J=conj (idealTerm χ (conj s) J) := by
  by_cases hJ : J=0
  · subst J
    simp only [idealTerm,map_zero,zero_div]
  have hN : (0 : ℝ)<J.absNorm := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hpow := Complex.cpow_conj ((J.absNorm : ℝ) : ℂ) (conj s)
    (by rw [Complex.arg_ofReal_of_nonneg hN.le]; exact Real.pi_ne_zero.symm)
  simp only [conj_ofReal, conj_conj] at hpow
  unfold idealTerm
  rw [idealCoeff_inverse_conj,map_div₀]
  congr 1

theorem LFunction_inverse_conj (χ : Character) (hχ : χ.residue≠1) (s : ℂ) :
    LFunction χ.inverse s=conj (LFunction χ (conj s)) := by
  have hi : χ.inverse.residue≠1 := by
    change χ.residue⁻¹≠1
    simpa only [ne_eq,inv_eq_one] using hχ
  have hA := LFunction_entire_nonprincipal χ.inverse hi
  have hB : Differentiable ℂ (fun z => conj (LFunction χ (conj z))) := by
    intro z
    simpa only [Function.comp_def,conj_conj] using
      (LFunction_entire_nonprincipal χ hχ (conj z)).conj_conj
  have he : LFunction χ.inverse=(fun z => conj (LFunction χ (conj z))) := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hA).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hB) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    rw [LFunction_eq_ideal_tsum χ.inverse hz,LFunction_eq_ideal_tsum χ (by simpa using hz),conj_tsum]
    exact tsum_congr (idealTerm_inverse_conj χ z)
  exact congr_fun he s

end SevenEighths.HeckeFamily

end

end OAI
end OAIOriginalModule1289

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion
Source SHA256: 9a0844dc067d7a136c751af204d5ef48c64b0d0ebc5384ad718bb572e734a2f3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1290



namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.HeckeDetectorFamilyInclusion
open HeckeFamily HeckeDetectorZeros Complex

theorem maximum_le_of_inclusion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ)
    (hinclude : ∀ i,∃ j, ∀ s : ℂ, LFunction (χ i) s=LFunction (ψ j) s) :
    zeroMaximum χ hχ T≤zeroMaximum ψ hψ T := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T hm
    obtain ⟨j,hj⟩ := hinclude i
    rw [←hs]
    apply zero_re_le_maximum ψ hψ T j
    · rw [hs]
      exact hm.le
    · exact ht
    · rw [←hj s]
      exact hz
  · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

theorem maximum_sum_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum χ hχ T≤zeroMaximum (Sum.elim χ ψ) (Sum.rec hχ hψ) T := by
  apply maximum_le_of_inclusion
  intro i
  exact ⟨Sum.inl i,fun _ => rfl⟩

theorem maximum_sum_right {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : ι→Character) (ψ : κ→Character)
    (hχ : ∀ i,(χ i).residue≠1) (hψ : ∀ j,(ψ j).residue≠1) (T : ℝ) :
    zeroMaximum ψ hψ T≤zeroMaximum (Sum.elim χ ψ) (Sum.rec hχ hψ) T := by
  apply maximum_le_of_inclusion
  intro i
  exact ⟨Sum.inr i,fun _ => rfl⟩

theorem inverse_nonprincipal (χ : Character) (hχ : χ.residue≠1) : χ.inverse.residue≠1 := by
  change χ.residue⁻¹≠1
  simpa only [ne_eq,inv_eq_one] using hχ

theorem maximum_inverse {ι : Type*} [Fintype ι] (χ : ι→Character)
    (hχ : ∀ i,(χ i).residue≠1) (T : ℝ) :
    zeroMaximum (fun i => (χ i).inverse) (fun i => inverse_nonprincipal (χ i) (hχ i)) T=
      zeroMaximum χ hχ T := by
  let ψ := fun i => (χ i).inverse
  have hψ := fun i => inverse_nonprincipal (χ i) (hχ i)
  apply le_antisymm
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum ψ hψ T) with hm | hm
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained ψ hψ T hm
      rw [LFunction_inverse_conj (χ i) (hχ i),map_eq_zero] at hz
      have hh := zero_re_le_maximum χ hχ T i (s:=conj s)
        (by simpa only [conj_re,hs] using hm.le) (by simpa using ht) hz
      simpa only [conj_re,hs] using hh
    · exact hm.trans (zeroMaximum_bounds χ hχ T).1
  · rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
    · obtain ⟨i,s,hz,ht,hs⟩ := maximum_attained χ hχ T hm
      have hz' : LFunction (ψ i) (conj s)=0 := by
        rw [LFunction_inverse_conj (χ i) (hχ i),conj_conj,hz,map_zero]
      have hh := zero_re_le_maximum ψ hψ T i (s:=conj s)
        (by simpa only [conj_re,hs] using hm.le) (by simpa using ht) hz'
      simpa only [conj_re,hs] using hh
    · exact hm.trans (zeroMaximum_bounds ψ hψ T).1

end SevenEighths.HeckeDetectorFamilyInclusion

end

end OAI
end OAIOriginalModule1290

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.RowClosure
Source SHA256: de7e714eb48cc959993b8e58311cae6090e3258670a5c5618db6d98b19b986ea
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1291


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeRowClosure
open HeckeFamily
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem periodic_of_primary (M : Ideal O)
    (hM : M ≤ Ideal.span {λ₀ ^ 2}) (G F : O →* ℂ)
    (hF : CanonicalCoefficientClass.FactorsModulo M F)
    (hu : ∀ (u : Oˣ) x, G ((u : O) * x) = G x)
    (hz : ∀ x, λ₀ ∣ x → G x = 0)
    (hagree : ∀ x, λ₀ ^ 2 ∣ x - 1 → G x = F x) :
    CanonicalCoefficientClass.FactorsModulo M G := by
  intro x y hxy
  have hdiff : λ₀ ^ 2 ∣ x - y := Ideal.mem_span_singleton.mp (hM hxy)
  have hdiff' : λ₀ ∣ x - y := (dvd_pow_self λ₀ (by decide : 2 ≠ 0)).trans hdiff
  by_cases hx : λ₀ ∣ x
  · have hy : λ₀ ∣ y := by
      convert dvd_sub hx hdiff' using 1 ; ring
    rw [hz x hx, hz y hy]
  · have hg := PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff x |>.mpr hx
    have hspec := CompletedGauss.primaryGenerator_spec (Ideal.span {x}) hg
    obtain ⟨u, hu'⟩ := Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
    have hp : λ₀ ^ 2 ∣ (u : O) * x - 1 := by
      have hp' : λ₀ ^ 2 ∣ CompletedGauss.primaryGenerator (Ideal.span {x}) - 1 := hspec.2
      rwa [mul_comm, hu']
    have hq : λ₀ ^ 2 ∣ (u : O) * y - 1 := by
      have hd := hdiff.trans (dvd_mul_left (x-y) (u : O))
      convert dvd_sub hp hd using 1 ; ring
    rw [← hu u x, ← hu u y, hagree _ hp, hagree _ hq]
    apply hF
    simpa only [mul_sub] using M.mul_mem_left (u : O) hxy

def quotientRow (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) : (O ⧸ M) →* ℂ where
  toFun x := Quotient.liftOn' x G (fun a b hab => hG a b (M.quotientRel_def.mp hab))
  map_one' := G.map_one
  map_mul' x y := by
    refine Quotient.inductionOn₂' x y ?_
    exact G.map_mul

@[simp] theorem quotientRow_mk (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) (z : O) :
    quotientRow M G hG (Ideal.Quotient.mk M z) = G z := rfl

def residueRow (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) : MulChar (O ⧸ M) ℂ :=
  MulChar.ofUnitHom (Units.map (quotientRow M G hG))

theorem residueRow_mk (M : Ideal O) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G) (z : O) :
    residueRow M G hG (Ideal.Quotient.mk M z) =
      if IsUnit (Ideal.Quotient.mk M z) then G z else 0 := by
  by_cases hz : IsUnit (Ideal.Quotient.mk M z)
  · obtain ⟨u, hu⟩ := hz
    rw [ite_eq_left (hu ▸ u.isUnit), ← hu]
    change MulChar.ofUnitHom (Units.map (quotientRow M G hG)) (u : O ⧸ M) = G z
    rw [MulChar.ofUnitHom_coe]
    change quotientRow M G hG (u : O ⧸ M) = G z
    rw [hu, quotientRow_mk]
  · rw [ite_eq_right hz]
    exact MulChar.map_nonunit _ hz

def rowCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G)
    (hu : ∀ u : Oˣ, G (u : O) = 1) : Character :=
  Character.ofResidue M hM (residueRow M G hG) (by
    intro u
    rw [residueRow_mk, ite_eq_left (u.isUnit.map (Ideal.Quotient.mk M)), hu])

theorem elementCoeff_rowCharacter (M : Ideal O) (hM : M ≠ ⊥) (G : O →* ℂ)
    (hG : CanonicalCoefficientClass.FactorsModulo M G)
    (hu : ∀ u : Oˣ, G (u : O) = 1) (z : O) :
    elementCoeff (rowCharacter M hM G hG hu) z =
      if IsUnit (Ideal.Quotient.mk M z) then G z else 0 := residueRow_mk M G hG z

def elementHom (η : Character) : O →* ℂ where
  toFun := elementCoeff η
  map_one' := elementCoeff_one η
  map_mul' := elementCoeff_mul η

theorem elementHom_periodic (η : Character) :
    CanonicalCoefficientClass.FactorsModulo η.modulus (elementHom η) := by
  intro x y hxy
  apply congrArg η.residue
  exact Ideal.Quotient.eq.mpr hxy

theorem elementHom_norm (η : Character) (x : O) : ‖elementHom η x‖ ≤ 1 := by
  let : Finite (O ⧸ η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O ⧸ η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _

theorem rowTwist_unit_mul (η : Character) (m f z : O) (u : Oˣ) (n : O) :
    CanonicalRowCompletion.rowTwist (elementHom η) m f z ((u : O)*n) =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  change elementCoeff η ((u : O)*n) * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {(u : O)*n}) = elementCoeff η n * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {n})
  rw [elementCoeff_unit_mul, Ideal.span_singleton_mul_left_unit u.isUnit]

theorem rowTwist_unit (η : Character) (m f z : O) (u : Oˣ) :
    CanonicalRowCompletion.rowTwist (elementHom η) m f z (u : O) = 1 := by
  simpa using rowTwist_unit_mul η m f z u 1

theorem rowTwist_periodic (η : Character) (m f z : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hr : CanonicalQuadraticSieve.Supported (Ideal.span {r}))
    (hpr : λ₀ ^ 2 ∣ r-1) (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    CanonicalCoefficientClass.FactorsModulo
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r})
      (CanonicalRowCompletion.rowTwist (elementHom η) m f z) := by
  refine periodic_of_primary _ ?_ _
    (CanonicalRowCompletion.actualPeriodicRow (elementHom η) m u a b r hr)
    (CanonicalRowCompletion.actualPeriodicRow_periodic _ _ (elementHom_periodic η) _ _ _ _ _ hr)
    (rowTwist_unit_mul η m f z) ?_ ?_
  · have hd3 : λ₀ ^ 2 ∣ (3 : O) := ActualEisensteinCubic.lambda_sq_dvd_three
    have hd72 : λ₀ ^ 2 ∣ (72 : O) := hd3.trans ⟨24, by norm_num⟩
    exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans
      ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hd72))
  · intro n hn
    apply CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2
    intro hs
    exact ((CanonicalQuadraticSieve.supported_span_iff n).mp hs).1 hn
  · exact CanonicalRowCompletion.rowTwist_eq_actualPeriodicRow_primary
      _ _ _ _ hmLam hm2 u a b r hr hpr hx

theorem rowTwist_nonzero_coprime (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (hn : CanonicalRowCompletion.rowTwist (elementHom η) m f z n ≠ 0) :
    CanonicalQuadraticSieve.Supported (Ideal.span {n}) ∧ IsCoprime n (m^6*f^4*z) := by
  have hs : CanonicalQuadraticSieve.Supported (Ideal.span {n}) := by
    by_contra h
    exact hn (CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 h)
  refine ⟨hs, ?_⟩
  have hrow : CanonicalRowCompletion.idealRowHom (m^6*f^4*z) (Ideal.span {n}) ≠ 0 :=
    right_ne_zero_of_mul hn
  have hp := pow_ne_zero 6 hrow
  rw [← CanonicalRowCompletion.idealRowHom_argument_pow _ _ _ hs,
    CanonicalRowCompletion.idealRowHom_sixth_mask _ _ hs] at hp
  by_cases hc : IsCoprime (Ideal.span {n}) (Ideal.span {m^6*f^4*z})
  · exact (Ideal.isCoprime_span_singleton_iff _ _).mp hc
  · simp [hc] at hp

theorem rowTwist_nonzero_unit (η : Character) (m f z n : O)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m)
    (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r)
    (hn : CanonicalRowCompletion.rowTwist (elementHom η) m f z n ≠ 0) :
    IsUnit (Ideal.Quotient.mk
      (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}) n) := by
  obtain ⟨hs, hc⟩ := rowTwist_nonzero_coprime η m f z n hmLam hm2 hn
  have hm : IsCoprime n m := hc.of_isCoprime_of_dvd_right ⟨m^5*f^4*z, by ring⟩
  have hr : IsCoprime n r := hc.of_isCoprime_of_dvd_right
    ⟨m^6*((u : O)*λ₀^a*(2 : O)^b), by
      rw [show m^6*f^4*z = m^6*(f^4*z) by ring, hx]; ring⟩
  have h2 := hm.of_isCoprime_of_dvd_right hm2
  have h9 := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n
    ((CanonicalQuadraticSieve.supported_span_iff n).mp hs).1).symm
  have h72 : IsCoprime n (72 : O) := by
    convert (h2.pow_right : IsCoprime n ((2 : O)^3)).mul_right h9 using 1 ; norm_num
  have he : elementCoeff η n ≠ 0 := left_ne_zero_of_mul hn
  have hη : IsCoprime (Ideal.span {n}) η.modulus := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
    exact MulChar.apply_ne_zero_iff.mp he
  rw [IdealCharacter.isUnit_mk_iff_isCoprime, IsCoprime.mul_right_iff,
    IsCoprime.mul_right_iff, IsCoprime.mul_right_iff]
  exact ⟨⟨⟨hη, (Ideal.isCoprime_span_singleton_iff _ _).mpr hm⟩,
    (Ideal.isCoprime_span_singleton_iff _ _).mpr h72⟩,
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hr⟩

theorem exists_row_character (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character, ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, hM, _, _, _⟩ :=
    CanonicalRowCompletion.exists_actual_periodic_row (elementHom η) η.modulus
      η.modulus_ne_bot (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}
  let G := CanonicalRowCompletion.rowTwist (elementHom η) m f z
  have hG := rowTwist_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨rowCharacter M hM G hG (rowTwist_unit η m f z), ?_⟩
  intro n
  rw [elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx h)))

def rowConductorBound (η : Character) (m f z : O) : ℕ :=
  η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm *
    ((Ideal.span {f}).absNorm ^ 4 * (Ideal.span {z}).absNorm)

theorem row_modulus_norm_le (η : Character) (m f z : O)
    (hf : f ≠ 0) (hz : z ≠ 0) (u : Oˣ) (a b : ℕ) (r : O)
    (hx : f^4*z = (u : O)*λ₀^a*(2 : O)^b*r) :
    (η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}).absNorm ≤
      rowConductorBound η m f z := by
  have hprod : (Ideal.span {f^4*z} : Ideal O) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (pow_ne_zero _ hf) hz)
  let : Finite (O ⧸ Ideal.span {f^4*z}) := Ring.HasFiniteQuotients.finiteQuotient hprod
  have hle : (Ideal.span {f^4*z} : Ideal O) ≤ Ideal.span {r} := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Ideal.mem_span_singleton.mpr
    exact ⟨(u : O)*λ₀^a*(2 : O)^b, by rw [hx]; ring⟩
  have hn := FiniteConductor.absNorm_le_of_le hle
  have heq : (Ideal.span {f^4*z} : Ideal O) = (Ideal.span {f})^4 * Ideal.span {z} := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  rw [heq, map_mul, map_pow] at hn
  simpa only [rowConductorBound, map_mul] using
    Nat.mul_le_mul_left
      (η.modulus.absNorm * (Ideal.span {m}).absNorm * (Ideal.span {(72 : O)}).absNorm) hn

theorem exists_row_character_with_conductor (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ : Character, χ.modulus.absNorm ≤ rowConductorBound η m f z ∧
      ∀ n : O, elementCoeff χ n =
        CanonicalRowCompletion.rowTwist (elementHom η) m f z n := by
  obtain ⟨u, a, b, r, hr, hpr, hx, hM, _, _, _⟩ :=
    CanonicalRowCompletion.exists_actual_periodic_row (elementHom η) η.modulus
      η.modulus_ne_bot (elementHom_periodic η) (elementHom_norm η) m f z hm hf hz hmLam hm2
  let M := η.modulus * Ideal.span {m} * Ideal.span {(72 : O)} * Ideal.span {r}
  let G := CanonicalRowCompletion.rowTwist (elementHom η) m f z
  have hG := rowTwist_periodic η m f z hmLam hm2 u a b r hr hpr hx
  refine ⟨rowCharacter M hM G hG (rowTwist_unit η m f z),
    row_modulus_norm_le η m f z hf hz u a b r hx, ?_⟩
  intro n
  rw [elementCoeff_rowCharacter]
  split_ifs with hn
  · rfl
  · exact Eq.symm (not_not.mp (fun h => hn (rowTwist_nonzero_unit η m f z n hmLam hm2 u a b r hx h)))

theorem idealCoeff_eq_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I = idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) I := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero, zero_mul]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
  have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
  rw [← hs, idealCoeff_span χ hn, heq]
  change elementCoeff η n * _ = idealCoeff η (Ideal.span {n}) * _
  rw [idealCoeff_span η hn]
  rfl

theorem exists_primitive_row (η : Character) (m f z : O)
    (hm : m ≠ 0) (hf : f ≠ 0) (hz : z ≠ 0)
    (hmLam : λ₀ ∣ m) (hm2 : (2 : O) ∣ m) :
    ∃ χ ψ : Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.modulus.absNorm ≤ rowConductorBound η m f z ∧
      (∀ I : Ideal O, idealCoeff χ I =
        idealCoeff η I * CanonicalRowCompletion.idealRowHom (m^6*f^4*z) I) ∧
      (∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff ψ I else 0) := by
  obtain ⟨χ, hnorm, heq⟩ := exists_row_character_with_conductor η m f z hm hf hz hmLam hm2
  obtain ⟨ψ, _, hp, hn, hmask⟩ := exists_primitive_character χ
  exact ⟨χ, ψ, hp, hn.trans hnorm, idealCoeff_eq_row η χ m f z heq, hmask⟩

end SevenEighths.HeckeRowClosure

end

end OAI
end OAIOriginalModule1291

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.ExceptionalRows
Source SHA256: 955dc446f26ad210c5e8bde67f0b4495e7a543d0c59d03c86f51999be8ea2aa0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1292


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeExceptionalRows
open HeckeFamily UniqueFactorizationMonoid

def rows (S : Finset (Ideal O)) : Set O :=
  {u | u ≠ 0 ∧ ∀ P ∈ normalizedFactors (Ideal.span {u}),
    P ∈ S ∧ (normalizedFactors (Ideal.span {u})).count P < 6}

def bound (S : Finset (Ideal O)) : ℕ := ((∏ P ∈ S, P)^5).absNorm

theorem row_ideal_dvd (S : Finset (Ideal O)) {u : O} (hu : u ∈ rows S) :
    (Ideal.span {u} : Ideal O) ∣ (∏ P ∈ S, P)^5 := by
  have hI : (Ideal.span {u} : Ideal O) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hu.1
  have hle : normalizedFactors (Ideal.span {u}) ≤ 5 • S.val := by
    apply Multiset.le_iff_count.mpr
    intro P
    by_cases hP : P ∈ normalizedFactors (Ideal.span {u})
    · have hp := hu.2 P hP
      have hc : S.val.count P = 1 := Multiset.count_eq_one_of_mem S.nodup hp.1
      rw [Multiset.count_nsmul, hc]
      omega
    · simp only [Multiset.count_eq_zero.mpr hP]
      exact Nat.zero_le _
  have hd := Multiset.prod_dvd_prod_of_le hle
  rw [Ideal.prod_normalizedFactors_eq_self hI, Multiset.prod_nsmul] at hd
  change (Ideal.span {u} : Ideal O) ∣ (S.prod id)^5
  simpa only [Finset.prod_val] using hd

theorem row_norm_bound (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    {u : O} (hu : u ∈ rows S) : (Ideal.span {u}).absNorm ≤ bound S := by
  have hd := map_dvd Ideal.absNorm (row_ideal_dvd S hu)
  apply Nat.le_of_dvd _ hd
  apply Nat.pos_of_ne_zero
  rw [ne_eq, Ideal.absNorm_eq_zero_iff]
  exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero))

theorem rows_subset_normDisk (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    rows S ⊆ (ConcretePrimeRowBridge.rowNormDisk (bound S) : Set O) := by
  intro u hu
  apply ConcretePrimeRowBridge.mem_rowNormDisk.mpr
  refine ⟨?_, row_norm_bound S hS hu⟩
  apply Nat.pos_of_ne_zero
  simpa only [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] using hu.1

theorem rows_finite (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) : (rows S).Finite :=
  (ConcretePrimeRowBridge.rowNormDisk (bound S)).finite_toSet.subset (rows_subset_normDisk S hS)

end SevenEighths.HeckeExceptionalRows

end

end OAI
end OAIOriginalModule1292

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.RowNonprincipal
