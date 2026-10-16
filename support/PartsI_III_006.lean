  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := v2_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma v2_marked_differentiableAt_z (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : RHV2.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := v2_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem v2_local_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : RHV2.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9/10 < w.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := v2_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hc := v2_principalDomain_unramifiedClosed_analytic_w (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := v2_marked_differentiableAt_w η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := v2_correction_ne_zero η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem v2_local_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : RHV2.boundary ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4/25 < z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := v2_principalDomain_unramifiedClosed_analytic_z (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := v2_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz.le
  have hmc := v2_marked_differentiableAt_z η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := v2_correction_ne_zero η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma v2_marked_bound (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : RHV2.boundary ≤ x.re)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1/2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith)
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans (rpow_le_half Q _ hQ (by linarith))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : 1-x.re-w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have he := unramified_marked_error_bound (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordK Q η x w) (coordW Q 1 w) (coordD Q η 1 x) hR hV hqi hD
  have h1 : 12*‖coordR Q A x z‖*(1+‖coordW Q 1 w‖) ≤ 12 := by
    calc
      _ ≤ 12*(1/2:ℝ)*(1+1) := by gcongr
      _ = _ := by norm_num
  have h2 : 4*‖coordK Q η x w‖*‖coordV Q z‖ ≤ 2 := by
    calc
      _ ≤ 4*1*(1/2:ℝ) := by gcongr
      _ = _ := by norm_num
  have hn := norm_sub_le (PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x)
    (coordD Q η 1 x)
  rw [add_sub_cancel_right] at hn
  change ‖PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x‖ ≤ _ at he
  linarith

lemma v2_replacement_bound (V W D P B q : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hV : ‖V‖ ≤ 1/2) (hW : ‖W‖ ≤ 1) (hD : ‖D‖ ≤ 1/2)
    (hP : ‖P‖ ≤ 16) (hB : ‖B‖ ≤ R) (hq : ‖q‖ ≤ 1) :
    ‖compensatedReplacement V W D P B q‖ ≤ 200*(1+R) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hV1 : ‖1-V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have hW1 : ‖1-W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have hBq : ‖B-q‖ ≤ R+1 := (norm_sub_le B q).trans (add_le_add hB hq)
  have hVW : ‖1-V*W‖ ≤ 2 := by
    have hn := norm_sub_le (1 : ℂ) (V*W)
    rw [norm_one,norm_mul] at hn
    have hm : ‖V‖*‖W‖ ≤ 1/2 := by
      calc
        _ ≤ (1/2:ℝ)*1 := by gcongr
        _ = _ := by ring
    linarith
  have hi := inv_one_sub_norm_le_two D hD
  unfold compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (‖B-q‖*‖1-V‖*‖1-W‖*‖P‖ + ‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*P) (q*(1-V*W))
    _ ≤ ((R+1)*2*2*16+1*2)*2 := by gcongr
    _ ≤ 200*(1+R) := by linarith

lemma v2_localBound_nonneg (Bx Bz : ℝ) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) : 0 ≤ localBound Bx Bz P := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold localBound
  positivity

theorem v2_local_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (RHV2.boundary) Bx) (hw : 19/20 ≤ w.re)
    (hz : z.re ∈ Icc (33/200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by dsimp [Q]; exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB : ‖star (idealCoeff η P.val)*(Q : ℂ)^x‖ ≤ Q^Bx := by
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (idealCoeff_norm_le_one η _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ)^(-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by simpa only [coordW,one_mul] using hq
  have hD : ‖coordD Q (idealCoeff η P.val) 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 _ 1 x (idealCoeff_norm_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith [hx.1]))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    v2_marked_bound Q (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) x w z hQ
      (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := v2_replacement_bound _ _ _ _ _ _ (Q^Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := v2_correction_inverse_bound η S hS P hP x w z hx.1 (by linarith) (by linarith [hz.1])
  have hp : ‖(Q : ℂ)^(z-1)‖ ≤ Q^(Bz-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    simpa only [Complex.sub_re,Complex.one_re] using sub_le_sub_right hz.2 1
  unfold localMultiplier
  dsimp only
  rw [div_eq_mul_inv,norm_mul,norm_mul]
  change _ ≤ Q^(Bz-1)*(400*(1+Q^Bx))
  calc
    _ ≤ Q^(Bz-1)*(200*(1+Q^Bx)*2) := by gcongr
    _ = _ := by ring

lemma v2_selectedBound_nonneg (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (Bx Bz : ℝ) :
    0 ≤ selectedBound T Bx Bz := Finset.prod_nonneg (fun P _ => v2_localBound_nonneg Bx Bz P)

lemma v2_slotBound_nonneg {ι : Type*} (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (Bx Bz : ℝ) : 0 ≤ slotBound J T b Bx Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply Finset.prod_nonneg
  intro j hj
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (norm_nonneg _) (v2_localBound_nonneg Bx Bz P))

theorem v2_selected_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x z : ℂ)
    (hx : RHV2.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => selectedMultiplier η T x w z) {w : ℂ | 9/10 < w.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => v2_local_analytic_w η S hS P (hT P hp) x z hx hz)

theorem v2_selected_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w : ℂ)
    (hx : RHV2.boundary ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => selectedMultiplier η T x w z) {z : ℂ | 4/25 < z.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => v2_local_analytic_z η S hS P (hT P hp) x w hx hw)

theorem v2_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : RHV2.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9/10 < w.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (v2_local_analytic_w η S hS P (hT j hj P hp) x z hx hz)

theorem v2_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : RHV2.boundary ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4/25 < z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (v2_local_analytic_z η S hS P (hT j hj P hp) x w hx hw)

theorem v2_selected_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (RHV2.boundary) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖selectedMultiplier η T x w z‖ ≤ selectedBound T Bx Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simp only [selectedMultiplier,selectedBound,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun P hp => v2_local_norm_bound η S hS P (hT P hp) x w z Bx Bz hx hw hz)

theorem v2_slot_norm_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (RHV2.boundary) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simp only [slotMultiplier,slotBound,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (v2_local_norm_bound η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma v2_global_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (x w z : ℂ) (hx : RHV2.boundary ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z‖ ≤ 3/2 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hb := v2_principalDomain_globalClosedCorrection_bound η S hS x w z hx hw hz
  have hn := norm_add_le (globalClosedCorrection η S x w z-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem v2_combined_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : RHV2.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9/10 < w.re} :=
  (v2_principalDomain_globalClosedCorrection_analytic_w η S hS x z hx hz).mul (v2_slot_analytic_w η S hS J T b hT x z hx hz)

theorem v2_combined_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : RHV2.boundary ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4/25 < z.re} :=
  (v2_principalDomain_globalClosedCorrection_analytic_z η S hS x w hx hw).mul (v2_slot_analytic_z η S hS J T b hT x w hx hw)

theorem v2_combined_slot_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (RHV2.boundary) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3/2)*slotBound J T b Bx Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [norm_mul]
  exact mul_le_mul (v2_global_norm_bound η S hS x w z hx.1 (by linarith) (by linarith [hz.1]))
    (v2_slot_norm_bound η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem v2_selected_initial_identity (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ)
    (hx : 3/2 < x.re) (hw : 2 < w.re) (hz : 1/6 < z.re) :
    (∏ P ∈ T, (Ideal.absNorm P.val : ℂ)^(z-1)) *
      spectralCompensatedHigh S T η x w z
        (fun P => star (idealCoeff η P.val)*(Ideal.absNorm P.val : ℂ)^x)
        (fun P => (Ideal.absNorm P.val : ℂ)^(-w)) =
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w /
        LFunction (η.excludePrimes S hS.prime) x) *
        (globalClosedCorrection η S x w z * selectedMultiplier η T x w z) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [spectralCompensatedHigh_continued S hS T hT η x w z _ _ hx hw hz]
  simp only [selectedMultiplier,localMultiplier,Finset.prod_mul_distrib,Complex.ofReal_natCast]
  ring_nf

theorem v2_source_w_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : RHV2.boundary ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1< cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
        LFunction (fixedPrincipal M) w) (19/20) cw := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY
    (η.excludePrimes S hS.prime) s z hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (v2_slotBound_nonneg J T b _ _)) 0
  · exact (v2_combined_slot_analytic_w η S hS.tail J T b hT s z hs (by linarith)).continuousOn.mono
      (by intro w hw; change (9/10:ℝ)< w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using v2_combined_slot_bound η S hS.tail J T b hT s
      ((x : ℂ)+t*I) z s.re z.re ⟨hs,le_rfl⟩ (by simpa using hx.1) ⟨hz,le_rfl⟩

theorem v2_source_z_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : RHV2.boundary ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0< e) (he' : e≤2/3) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
        LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply PrincipalMellinGrowth.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ
    (η.excludePrimes S hS.prime) s hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) he he'
    (mul_nonneg (by norm_num) (v2_slotBound_nonneg J T b _ _)) 0
  · exact (v2_combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using v2_combined_slot_bound η S hS.tail J T b hT s
      1 ((x : ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)

theorem v2_source_multiplier_differentiable_w {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : RHV2.boundary ≤ s.re) (hz : 4/25 ≤ z.re) :
    DifferentiableOn ℂ (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {w : ℂ | 9/10 < w.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hM := CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (v2_combined_slot_analytic_w η S hS.tail J T b hT s z hs hz).differentiableOn
  have hYn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he : (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun w => ((X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z /
      LFunction (η.excludePrimes S hS.prime) s) * (Y:ℂ)^(w-1) * mellin W1 w *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext w; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hYn)

theorem v2_source_multiplier_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : RHV2.boundary ≤ s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {z : ℂ | 4/25 < z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono (by intro z hz; change 0 < z.re; change (4/25:ℝ)< z.re at hz; linarith)
  have hH := (v2_combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hXn : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hZn : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have he : (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w / LFunction (η.excludePrimes S hS.prime) s) *
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext z; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hXn | exact Or.inl hZn)

theorem v2_source_w_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : RHV2.boundary ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0) {cw : ℝ} (hcw : 1< cw) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral cw (fun w => K w z * LFunction (fixedPrincipal M) w) =
      verticalIntegral (19/20) (fun w => K w z * LFunction (fixedPrincipal M) w) +
        K 1 z * fixedPrincipalResidue M := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  apply PrincipalMellinResidues.source_w_shift (fixedPrincipal M) _ z hcw
  · exact (v2_source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY s z hs (by linarith)).mono (by intro w hw; change (9/10:ℝ)< w.re; linarith [hw.1])
  · exact v2_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1 M X Y Z hY s z hs hz hEta hcw

theorem v2_source_residue_z_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : RHV2.boundary ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0< e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral (1/6+e) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) =
      verticalIntegral (33/200) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) +
        K 1 (1/6) * fixedPrincipalResidue M / 6 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  apply PrincipalMellinResidues.source_residue_z_shift (fixedPrincipal M) _ he
  · exact (v2_source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s 1 hs
      (by norm_num)).mono (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · exact v2_source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ s hs hEta he he'


theorem v2_fixed_source_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (η : Character) (s : ℂ) (hs : RHV2.boundary ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1< cw) (he : 0< e) (he' : e≤2/3) :
    let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  constructor
  · intro z hz
    exact v2_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏ P ∈ S, P) X Y Z hY s z hs (by rw [hz]; linarith) hEta hcw
  · exact v2_source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0
      (∏ P ∈ S, P) X Y Z hX hZ s hs hEta he he'

lemma v2_boundary_mul_const (F : ℂ → ℂ) (a b : ℝ) (h : BoundaryControl F a b) (c : ℂ) :
    BoundaryControl (fun z => F z*c) a b := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  refine ⟨h.left.mul_const c,h.right.mul_const c,?_,?_⟩
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.lower.mul_const c
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.upper.mul_const c

theorem v2_fixed_source_ordered_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (η : Character) (s : ℂ) (hs : RHV2.boundary ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1< cw) (he : 0< e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hh := v2_fixed_source_boundaries S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ η s hs hEta hcw he he'
  dsimp only at hh ⊢
  refine ⟨?_,hh.2⟩
  intro z hz
  convert v2_boundary_mul_const _ _ _ (hh.1 z hz) (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
  funext w
  ring

theorem v2_uniform_closed_box_bound {ι : Type*} (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (Bx Bw Bz : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Character) (s w z : ℂ),
      s.re ∈ Icc (RHV2.boundary) Bx → w.re ∈ Icc (19/20) Bw → z.re ∈ Icc (33/200) Bz →
      ‖globalClosedCorrection η S s w z * slotMultiplier η J T b s w z‖ ≤ C :=
  ⟨(3/2)*slotBound J T b Bx Bz,
    mul_nonneg (by norm_num) (v2_slotBound_nonneg J T b Bx Bz),
    fun η s w z hs hw hz => v2_combined_slot_bound η S hS J T b hT s w z Bx Bz hs hw.1 hz⟩

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule171
/- END RHZeroFreeExtension.analytic_high.V2FiniteProduct -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2FiniteProductX -/
section LocalModule172

set_option linter.unusedVariables false

/-! Domain continuation of the genuine source multiplier, including its
regular reciprocal at the principal point. No improved continuation is
postulated: the proofs combine new proved Euler analyticity with the generic
actual Hecke reciprocal on Re(s)> beta.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
open OAI OAI.SevenEighths
open OAI.ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds ProbeFiniteProductX
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma v2_marked_differentiableAt_x (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : RHV2.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := v2_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem v2_local_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | RHV2.boundary < x.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := v2_principalDomain_unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := v2_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx.le hz
  have hm := v2_marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := v2_correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem v2_selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => selectedMultiplier η T x w z) {x : ℂ | RHV2.boundary < x.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => v2_local_analytic_x η S hS P (hT P hp) w z hw hz)

theorem v2_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | RHV2.boundary < x.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (v2_local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem v2_window_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (W : ι → ℝ → ℂ) (scale : ι → ℝ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => windowMultiplier η J T W scale x w z) {x : ℂ | RHV2.boundary < x.re} :=
  v2_slot_analytic_x η S hS J T _ hT w z hw hz

theorem v2_combined_selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * selectedMultiplier η T x w z)
      {x : ℂ | RHV2.boundary < x.re} :=
  (v2_principalDomain_globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (v2_selected_analytic_x η S hS T hT w z hw hz)

theorem v2_combined_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {x : ℂ | RHV2.boundary < x.re} :=
  (v2_principalDomain_globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (v2_slot_analytic_x η S hS J T b hT w z hw hz)

theorem v2_continued_source_analytic_x {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (RHV2.boundary : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (RHV2.boundary : ℝ)< x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta< x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (v2_principalDomain_globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (v2_slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem v2_continued_source_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : x≠0) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simp only [continuedSourceMultiplier,sourceMultiplier,
    HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,div_eq_mul_inv]

theorem v2_continued_source_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a : ℝ) (w z : ℂ) :
    (fun t : ℝ => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z ((a:ℂ)+t*I) w z)
      =ᵐ[volume] (fun t : ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
        ((a:ℂ)+t*I) (globalClosedCorrection η S ((a:ℂ)+t*I))
          (slotMultiplier η J T b ((a:ℂ)+t*I)) w z) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply v2_continued_source_eq_raw
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem v2_source_analytic_x_off_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z)
      {x : ℂ | max (RHV2.boundary : ℝ) HeckeZeroSupremum.beta < x.re ∧ x≠1} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _
    ((Complex.isOpen_re_gt _).inter (isClosed_singleton.isOpen_compl))
  intro x hx
  have hx' : (RHV2.boundary : ℝ)< x.re := lt_of_le_of_lt (le_max_left _ _) hx.1
  have hβ : HeckeZeroSupremum.beta< x.re := lt_of_le_of_lt (le_max_right _ _) hx.1
  have hx0 : x≠0 := by intro h; simp only [h,zero_re] at hx'; linarith
  have hL := LFunction_differentiableAt (η.excludePrimes S hS.prime) hx0 (Or.inl hx.2)
  have hLn := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime) hβ (Or.inl hx.2)
  have hH := (v2_principalDomain_globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (v2_slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  unfold sourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem v2_continued_source_differentiable_strip {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : RHV2.boundary< a) (hβ : HeckeZeroSupremum.beta< a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤ x.re ∧ x.re≤ c} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply (v2_continued_source_analytic_x η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

theorem v2_continued_source_principal_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (w z : ℂ)
    (hχ : (η.excludePrimes S hS).residue=1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z 1 w z=0 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simp only [continuedSourceMultiplier,HeckeReciprocal.reciprocal_principal_one _ hχ,mul_zero,zero_mul]

end
end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_continued_source_analytic_x

end LocalModule172
/- END RHZeroFreeExtension.analytic_high.V2FiniteProductX -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2PrincipalContours -/
section LocalModule173

set_option linter.unusedVariables false

/-! Full actual ordered Mellin-contour, Fubini, and uniform-tail interface
on the perturbed x-domain. All functions, including arithmeticMultiplier and
continuedSourceMultiplier, remain upstream definitions. Domain-dependent
calls are supplied by newly proved bounds; the generic Mellin/Hecke APIs are
reused. The double residue retains the square of the principal residue.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O
local instance : Countable OAI.ActualEisensteinCubic.O := OAI.ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

@[fun_prop] lemma v2_measurable_const_cpow {α : Type*} [MeasurableSpace α] (Q : ℝ) (hQ : 0< Q)
    (f : α → ℂ) (hf : Measurable f) : Measurable (fun x => (Q:ℂ)^f x) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_cpow (Or.inl hn)).continuous.measurable).comp hf

lemma v2_ideal_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => idealClosedCorrection η P (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealClosedCorrection unramifiedClosed continuedCorrection markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma v2_global_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (S : Finset Id) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => globalClosedCorrection η S (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold globalClosedCorrection
  exact Measurable.tprod (fun P => v2_ideal_correction_measurable η P.val x w z hx hw hz)

lemma v2_local_multiplier_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => localMultiplier η P (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc := v2_ideal_correction_measurable η P x w z hx hw hz
  unfold localMultiplier compensatedReplacement idealMarkedClosed markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma v2_slot_multiplier_measurable {α ι : Type*} [MeasurableSpace α]
    (η : Character) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (x w z : α → ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => slotMultiplier η J T b (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold slotMultiplier
  apply Finset.measurable_prod
  intro j hj
  apply Finset.measurable_sum
  intro P hP
  exact measurable_const.mul (v2_local_multiplier_measurable η P x w z hx hw hz)

lemma v2_zBoxAmplitude_nonneg (M : Id) [NeZero M] (Bz : ℝ) : 0≤ zBoxAmplitude M Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold zBoxAmplitude
  exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _)))
    (principalConstant_pos M).le

lemma v2_fixed_principal_z_box_growth (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤ zBoxAmplitude M Bz*height t^3 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(6*((ξ:ℂ)+t*I) : ℂ).re by simp; linarith [hξ.1])
  have hn : ‖6*((ξ:ℂ)+t*I)+1‖≤ max 6 (6*Bz+1)*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    have hm : (6:ℝ)≤ max 6 (6*Bz+1) := le_max_left _ _
    have hm' : 6*ξ+1≤ max 6 (6*Bz+1) := (by linarith [hξ.2] : 6*ξ+1≤6*Bz+1).trans (le_max_right _ _)
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,
      mul_zero,sub_zero,add_zero,zero_add,mul_one,one_re,one_im]
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero,add_zero]
    rw [abs_of_pos (by linarith [hξ.1] : 0<6*ξ+1),abs_mul]
    norm_num
    unfold height
    nlinarith [mul_le_mul_of_nonneg_right hm (abs_nonneg t)]
  have hi : |(6*((ξ:ℂ)+t*I) : ℂ).im|=6*|t| := by simp [abs_mul]
  have ht : (3+6*|t|)^2≤36*height t^2 := by
    have hh : 3+6*|t|≤6*height t := by unfold height; linarith
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+6*|t|) hh 2
    simpa only [mul_pow,show (6:ℝ)^2=36 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have hmax : 0≤ max (6:ℝ) (6*Bz+1) := le_trans (by norm_num) (le_max_left _ _)
  have hh := (height_pos t).le
  rw [hi] at hb
  calc
    _ ≤ principalConstant M*‖6*((ξ:ℂ)+t*I)+1‖*(3+6*|t|)^2 := hb
    _ ≤ principalConstant M*(max 6 (6*Bz+1)*height t)*(36*height t^2) := by
      gcongr
    _ = _ := by unfold zBoxAmplitude; ring

lemma v2_LFunction_eq_pole_quotient (χ : Character) {s : ℂ} (h0 : s≠0) (h1 : s≠1) :
    LFunction χ s=HeckeOrigin.poleRemoved χ s/(s-1) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)).symm

lemma v2_LFunction_vertical_continuous (χ : Character) (a : ℝ) (ha0 : a≠0) (ha1 : a≠1) :
    Continuous (fun t : ℝ => LFunction χ ((a:ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h0 (t : ℝ) : (a:ℂ)+t*I≠0 := by intro h; exact ha0 (by simpa using congrArg Complex.re h)
  have h1 (t : ℝ) : (a:ℂ)+t*I≠1 := by intro h; exact ha1 (by simpa using congrArg Complex.re h)
  have hc := ((HeckeOrigin.poleRemoved_entire χ).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I))).div
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I-1)) (fun t => sub_ne_zero.mpr (h1 t))
  exact hc.congr (fun t => (v2_LFunction_eq_pole_quotient χ (h0 t) (h1 t)).symm)

lemma v2_reciprocal_vertical_continuous (χ : Character) (a : ℝ) (ha : HeckeZeroSupremum.beta< a) :
    Continuous (fun t : ℝ => HeckeReciprocal.reciprocal χ ((a:ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (HeckeReciprocal.reciprocal_differentiableAt χ (by simpa using ha)).continuousAt.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I)).continuousAt

lemma v2_LFunction_norm_le_of_poleRemoved (χ : Character) (s : ℂ) (h0 : s≠0) (h1 : s≠1)
    (A δ : ℝ) (hδ : 0<δ) (hd : δ≤‖s-1‖) (hA : ‖HeckeOrigin.poleRemoved χ s‖≤ A) :
    ‖LFunction χ s‖≤ A/δ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply (le_div_iff₀ hδ).mpr
  calc
    _ ≤ ‖LFunction χ s‖*‖s-1‖ := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = ‖HeckeOrigin.poleRemoved χ s‖ := by rw [HeckeOrigin.poleRemoved_eq χ h0 h1,norm_mul]; ring
    _ ≤ A := hA

lemma v2_fixed_principal_w_bound (M : Id) [NeZero M] {cw υ : ℝ} (hcw : 1< cw)
    (hυ : υ∈Icc (19/20 : ℝ) cw) (hυ1 : υ≠1) (t : ℝ) :
    ‖LFunction (fixedPrincipal M) ((υ:ℂ)+t*I)‖≤
      (wAmplitude M cw/|υ-1|)*height t^3 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h0 : (υ:ℂ)+t*I≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hυ.1]
  have h1 : (υ:ℂ)+t*I≠1 := by intro h; exact hυ1 (by simpa using congrArg Complex.re h)
  have hδ : 0 < |υ-1| := abs_pos.mpr (sub_ne_zero.mpr hυ1)
  have h := v2_LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ
    (pole_distance_vertical 1 υ t) (fixed_principal_w_growth M hcw hυ t)
  convert h using 1
  ring

lemma v2_fixed_principal_z_bound (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) (hξ1 : 6*ξ≠1) :
    ‖LFunction (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤
      (zBoxAmplitude M Bz/|6*ξ-1|)*height t^3 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h0 : (6*((ξ:ℂ)+t*I) : ℂ)≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hξ.1]
  have h1 : (6*((ξ:ℂ)+t*I) : ℂ)≠1 := by intro h; exact hξ1 (by simpa using congrArg Complex.re h)
  have hd : |6*ξ-1|≤‖6*((ξ:ℂ)+t*I)-1‖ := by
    simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+t*I)-1)
  have hδ : 0 < |6*ξ-1| := abs_pos.mpr (sub_ne_zero.mpr hξ1)
  have h := v2_LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ hd
    (v2_fixed_principal_z_box_growth M Bz ξ t hξ)
  convert h using 1
  ring

lemma v2_arithmetic_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    arithmeticMultiplier η S hS J T b X Y Z s w z*profile W0 W1 s w z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z *
        LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold arithmeticMultiplier profile continuedSourceMultiplier
  ring

lemma v2_arithmetic_onLines_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : HeckeZeroSupremum.beta< a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) (hυ0 : υ≠0) (hυ1 : υ≠1) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hH := v2_global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := v2_slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (v2_reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (v2_LFunction_vertical_continuous (fixedSourcePrincipal S hS) υ hυ0 hυ1).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.2))
  have hZL := (v2_LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun p : HeightSpace => 6*p.1.2))
  have hZL' : Measurable (fun p : HeightSpace => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+p.1.2*I))) := by
    convert hZL using 1
    funext p
    congr 1
    push_cast
    ring
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

lemma v2_boxScale_pos (X Y Z a Bs Bz cw : ℝ) : 0< boxScale X Y Z a Bs Bz cw := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold boxScale
  exact mul_pos (mul_pos (scaleBound_pos _ _ _) (scaleBound_pos _ _ _)) (scaleBound_pos _ _ _)

lemma v2_height_le_joint_s (t v u : ℝ) : height t≤ jointHeight t v u := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold height jointHeight; linarith [abs_nonneg v,abs_nonneg u]
lemma v2_height_le_joint_z (t v u : ℝ) : height v≤ jointHeight t v u := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg u]
lemma v2_height_le_joint_w (t v u : ℝ) : height u≤ jointHeight t v u := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg v]

lemma v2_arithmetic_onLines_bound_of_gaps {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (δw δz : ℝ) (hdw : 0<δw) (hdz : 0<δz)
    (hC : 0≤ C) (hR : ∀s : ℂ, a≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (p : HeightSpace)
    (hwgap : δw≤‖((υ:ℂ)+p.2*I)-1‖) (hzgap : δz≤‖6*((ξ:ℂ)+p.1.2*I)-1‖) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hx := cpow_le_scaleBound hX (1/2-((ξ:ℂ)+p.1.2*I))
    (show (1/2-((ξ:ℂ)+p.1.2*I) : ℂ).re∈Icc (1/2-Bz) (1/2-33/200) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero]
      norm_num only [show (1/2:ℂ).re=1/2 by norm_num]
      constructor <;> linarith [hξ.1,hξ.2])
  have hz := cpow_le_scaleBound hZ (((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)
    (show ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1) : ℂ).re∈Icc (a+33/200-1) (Bs+Bz-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hσ.1,hσ.2,hξ.1,hξ.2])
  have hy := cpow_le_scaleBound hY (((υ:ℂ)+p.2*I)-1)
    (show (((υ:ℂ)+p.2*I)-1 : ℂ).re∈Icc (19/20-1) (cw-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hυ.1,hυ.2])
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖≤ C*height p.1.1^2 := by
    apply (hR _ (by simpa using hσ.1)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg p.1.1]
  have hh := v2_combined_slot_bound η S hS.tail J T b hT ((σ:ℂ)+p.1.1*I)
    ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) Bs Bz
    (by simpa using And.intro (ha.trans hσ.1) hσ.2) (by simpa using hυ.1) (by simpa using hξ)
  have hw0 : (υ:ℂ)+p.2*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hυ.1]
  have hw1 : (υ:ℂ)+p.2*I≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hwgap; linarith
  have hz0 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hξ.1]
  have hz1 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hzgap; linarith
  have hlz0 := v2_LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hz0 hz1 _ _ hdz hzgap
    (v2_fixed_principal_z_box_growth (∏P∈S,P) Bz ξ p.1.2 hξ)
  have hlw0 := v2_LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hw0 hw1 _ _ hdw hwgap
    (fixed_principal_w_growth (∏P∈S,P) hcw hυ p.2)
  have hlz : ‖LFunction (fixedPrincipal (∏P∈S,P)) (6*((ξ:ℂ)+p.1.2*I))‖≤
      (zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3 := by convert hlz0 using 1; ring
  have hlw : ‖LFunction (fixedPrincipal (∏P∈S,P)) ((υ:ℂ)+p.2*I)‖≤
      (wAmplitude (∏P∈S,P) cw/δw)*height p.2^3 := by convert hlw0 using 1; ring
  have hp1 := (height_pos p.1.1).le
  have hp2 := (height_pos p.1.2).le
  have hp3 := (height_pos p.2).le
  have hpJ := (jointHeight_pos p.1.1 p.1.2 p.2).le
  have hsX := (scaleBound_pos X (1/2-Bz) (1/2-33/200)).le
  have hsY := (scaleBound_pos Y (19/20-1) (cw-1)).le
  have hsZ := (scaleBound_pos Z (a+33/200-1) (Bs+Bz-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (v2_slotBound_nonneg J T b Bs Bz)
  have hAZ := div_nonneg (v2_zBoxAmplitude_nonneg (∏P∈S,P) Bz) hdz.le
  have hAW := div_nonneg (wAmplitude_pos (∏P∈S,P) hcw).le hdw.le
  calc
    _ = ‖(X:ℂ)^(1/2-((ξ:ℂ)+p.1.2*I))‖ *
        ‖(Z:ℂ)^(((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)‖ *
        ‖(Y:ℂ)^(((υ:ℂ)+p.2*I)-1)‖ *
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖ *
        ‖globalClosedCorrection η S ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          slotMultiplier η J T b ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ := by
      simp only [arithmeticMultiplier,norm_mul]
    _ ≤ scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*height p.1.1^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*height p.2^3) := by
      gcongr <;> first | positivity | exact hlz | exact hlw
    _ ≤ scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*jointHeight p.1.1 p.1.2 p.2^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*jointHeight p.1.1 p.1.2 p.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*jointHeight p.1.1 p.1.2 p.2^3) := by
      gcongr <;> first | positivity | exact v2_height_le_joint_s _ _ _ | exact v2_height_le_joint_z _ _ _ | exact v2_height_le_joint_w _ _ _
    _ = _ := by unfold arithmeticAmplitude boxScale; ring

lemma v2_arithmetic_onLines_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1)
    (hC : 0≤ C) (hR : ∀s : ℂ, a≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (p : HeightSpace) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply v2_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ |υ-1| |6*ξ-1| (abs_pos.mpr (sub_ne_zero.mpr hυ1))
    (abs_pos.mpr (sub_ne_zero.mpr hξ1)) hC hR p
  · exact pole_distance_vertical 1 υ p.2
  · simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)

theorem v2_continued_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ υ
    (by linarith) (fun p : HeightSpace => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I))
    (v2_arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
      (by linarith) hξ1 (by linarith [hυ.1]) hυ1).aestronglyMeasurable
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|) 8
    (v2_arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
      ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR)
  apply hi.congr
  exact Eventually.of_forall (fun p => v2_arithmetic_profile_eq_source η S hS.prime J T b W0 W1 X Y Z _ _ _)

lemma v2_outer_height_ne_zero_ae : ∀ᵐp : HeightSpace ∂heightMeasure, p.1.1≠0 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hh : ∀ᵐp : ℝ×ℝ ∂volume.prod volume, p.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  exact Measure.quasiMeasurePreserving_fst.ae hh

lemma v2_continued_joint_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    (fun p : HeightSpace => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) =ᵐ[heightMeasure]
    (fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
      ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
      (slotMultiplier η J T b ((a:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  filter_upwards [v2_outer_height_ne_zero_ae] with p hp
  apply v2_continued_source_eq_raw
  · intro h; exact hp (by simpa using congrArg Complex.im h)
  · intro h; exact hp (by simpa using congrArg Complex.im h)

theorem v2_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply (v2_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1).congr
  filter_upwards [v2_continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ] with p hp
  rw [hp]

theorem v2_source_joint_fubini {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    ((∫p, F p ∂heightMeasure)=∫t : ℝ,∫v : ℝ,∫u : ℝ,F ((t,v),u)) ∧
    ((∫p, F p ∂heightMeasure)=∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((t,v),u)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  have hi := v2_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu

lemma v2_arithmeticAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) (hcw : 1< cw) (hC : 0≤ C) (hw : 0≤δw) (hz : 0≤δz) :
    0≤ arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hbox := (v2_boxScale_pos X Y Z a Bs Bz cw).le
  have hb := v2_slotBound_nonneg J T b Bs Bz
  have hza := v2_zBoxAmplitude_nonneg (∏P∈S,P) Bz
  have hwa := (wAmplitude_pos (∏P∈S,P) hcw).le
  unfold arithmeticAmplitude
  positivity

theorem v2_continued_source_slices {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) (N : ℕ) :
    ∃ C K : ℝ, 0≤ C ∧ 0< K ∧ ∀axis : SliceAxis,∀R : ℝ,
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume)≤
        arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1| *K/height R^N := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ υ υ (by linarith) 8 N
  refine ⟨C,K,hC,hK,?_⟩
  intro axis R
  let G : HeightSpace → ℂ := fun p => arithmeticMultiplier η S hS.prime J T b X Y Z
    ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)
  have hm := v2_arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
    (by linarith) hξ1 (by linarith [hυ.1]) hυ1
  have hbound := v2_arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
    ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR
  have hh := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩ axis R
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|)
    (v2_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a a ξ cw C _ _ hcw hC (abs_nonneg _) (abs_nonneg _))
    (fun q => G (sliceMap axis R q)) ((hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable)
    (fun q => hbound (sliceMap axis R q))
  simpa only [G,onLines,v2_arithmetic_profile_eq_source] using hh

theorem v2_source_w_leftover_outer_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    Integrable (fun v : ℝ => verticalIntegral (19/20) (fun w =>
      K w ((1/6+e:ℝ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime)
        (6*((1/6+e:ℝ)+v*I))*LFunction (fixedSourcePrincipal S hS.prime) w)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,K,hC,hK,hslice⟩ := v2_continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z a (1/6+e) (19/20) 3 hX hY hZ ha hβ
    (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  have hi := (hslice .s t).1
  have hs0 : (a:ℂ)+t*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hpair : Integrable (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I))
        ((19/20:ℝ)+q.2*I) ((1/6+e:ℝ)+q.1*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((1/6+e:ℝ)+q.1*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((19/20:ℝ)+q.2*I)) (volume.prod volume) := by
    simpa only [sliceMap,v2_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ hs0 hs1] using hi
  simpa only [verticalIntegral] using hpair.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem v2_source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0⊆Icc a0 b0) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : RHV2.boundary≤ s.re) (hη : LFunction (η.excludePrimes S hS.prime) s≠0)
    {e : ℝ} (he : 0< e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)) (33/200) (1/6+e) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 (∏P∈S,P)
    X Y Z hX hZ (η.excludePrimes S hS.prime) s hη
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) (AL := zBoxAmplitude (∏P∈S,P) (1/6+e))
    he (mul_nonneg (by norm_num) (v2_slotBound_nonneg J T b _ _))
    (v2_zBoxAmplitude_nonneg _ _) 0 3
  · exact (v2_combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using v2_combined_slot_bound η S hS.tail J T b hT s
      1 ((x:ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)
  · intro x hx t _
    exact v2_fixed_principal_z_box_growth (∏P∈S,P) (1/6+e) x t hx

theorem v2_source_ordered_at_height {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
    verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
    HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
    (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hs : (RHV2.boundary : ℝ)≤(((a:ℂ)+t*I) : ℂ).re := by simpa using ha
  have hη := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime)
    (show HeckeZeroSupremum.beta<(((a:ℂ)+t*I) : ℂ).re by simpa using hβ) (Or.inl hs1)
  have hzb := v2_source_z_boundary_any η S hS J T b hT W0 W1 a0 b0 ha0 hW0 X Y Z hX hZ
    ((a:ℂ)+t*I) hs hη he
  apply source_ordered_double_shift (fixedSourcePrincipal S hS.prime) _ hcw he
  · intro z hz
    apply (v2_source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith)).mono
    intro w hw
    change (9/10 : ℝ)< w.re
    linarith [hw.1]
  · intro z hz
    have hh := v2_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏P∈S,P) X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith) hη hcw
    convert v2_boundary_mul_const _ _ _ hh (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
    funext w
    dsimp only [fixedSourcePrincipal,fixedPrincipal]
    ring
  · apply (v2_source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
      ((a:ℂ)+t*I) 1 hs (by norm_num)).mono
    intro z hz
    change (4/25 : ℝ)< z.re
    linarith [hz.1]
  · exact hzb
  · exact v2_source_w_leftover_outer_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e t hX hY hZ ha hβ he hs1

theorem v2_source_ordered_ae {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e) :
    ∀ᵐt : ℝ, let s : ℂ := (a:ℂ)+t*I
      let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s)
      let π := fixedSourcePrincipal S hS.prime
      verticalIntegral (1/6+e) (fun z => verticalIntegral cw
        (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
      verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
      HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
      (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply v2_source_ordered_at_height η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e t cw hX hY hZ ha hβ hcw he
  intro h
  exact ht (by simpa using congrArg Complex.im h)

lemma v2_residue_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s z : ℂ) :
    residueArithmetic η S hS J T b X Z s z*profile W0 W1 s 1 z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s 1 z *
        LFunction (fixedSourcePrincipal S hS) (6*z) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold residueArithmetic profile continuedSourceMultiplier
  simp only [sub_self,Complex.cpow_zero,mul_one]
  ring

lemma v2_residue_arithmetic_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (X Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (hβ : HeckeZeroSupremum.beta< a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) :
    Measurable (fun q : ℝ×ℝ => residueArithmetic η S hS J T b X Z
      ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hH := v2_global_correction_measurable η S (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := v2_slot_multiplier_measurable η J T b (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (v2_reciprocal_vertical_continuous (η.excludePrimes S hS) a hβ).measurable.comp
    (by fun_prop : Measurable (fun q : ℝ×ℝ => q.1))
  have hL := (v2_LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun q : ℝ×ℝ => 6*q.2))
  have hL' : Measurable (fun q : ℝ×ℝ => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+q.2*I))) := by
    convert hL using 1
    funext q
    congr 1
    push_cast
    ring
  unfold residueArithmetic
  fun_prop (disch := aesop)

lemma v2_residue_arithmetic_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Z a ξ C : ℝ) (hX : 0< X) (hZ : 0< Z) (ha : RHV2.boundary≤ a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1)
    (hC : 0≤ C) (hR : ∀s : ℂ,a≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (q : ℝ×ℝ) :
    ‖residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)‖≤
      residueAmplitude S J T b X Z a ξ C*jointHeight q.1 q.2 0^5 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖≤ C*height q.1^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg q.1]
  have hh := v2_combined_slot_bound η S hS.tail J T b hT ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I) a ξ
    (by simpa using ha) (by norm_num) (by simpa using hξ)
  have hL := v2_fixed_principal_z_bound (∏P∈S,P) ξ ξ q.2 ⟨hξ,le_rfl⟩ hξ1
  have hX0 := (Real.rpow_pos_of_pos hX (1/2-ξ)).le
  have hZ0 := (Real.rpow_pos_of_pos hZ (a+ξ-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (v2_slotBound_nonneg J T b a ξ)
  have hA := div_nonneg (v2_zBoxAmplitude_nonneg (∏P∈S,P) ξ) (abs_nonneg (6*ξ-1))
  have hq1 := (height_pos q.1).le
  have hq2 := (height_pos q.2).le
  have hqJ := (jointHeight_pos q.1 q.2 0).le
  calc
    _ = X^(1/2-ξ)*Z^(a+ξ-1)*
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖ *
        ‖globalClosedCorrection η S ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
          slotMultiplier η J T b ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ := by
      simp only [residueArithmetic,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
        Complex.norm_cpow_eq_rpow_re_of_pos hZ]
      norm_num
    _ ≤ X^(1/2-ξ)*Z^(a+ξ-1)*(C*height q.1^2)*((3/2)*slotBound J T b a ξ)*
        ((zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)*height q.2^3) := by
      gcongr
      first | positivity | exact hL
    _ ≤ X^(1/2-ξ)*Z^(a+ξ-1)*(C*jointHeight q.1 q.2 0^2)*((3/2)*slotBound J T b a ξ)*
        ((zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr <;> first | positivity | exact v2_height_le_joint_s _ _ _ | exact v2_height_le_joint_z _ _ _
    _ = _ := by unfold residueAmplitude; ring

lemma v2_residueAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (X Z a ξ C : ℝ)
    (hX : 0≤ X) (hZ : 0≤ Z) (hC : 0≤ C) : 0≤ residueAmplitude S J T b X Z a ξ C := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hb := v2_slotBound_nonneg J T b a ξ
  have hza := v2_zBoxAmplitude_nonneg (∏P∈S,P) ξ
  unfold residueAmplitude
  positivity

theorem v2_continued_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) 5 0
  have hm := v2_residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hb := v2_residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hh := (hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
    (residueAmplitude S J T b X Z a ξ C)
    (v2_residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC)
    (fun q : ℝ×ℝ => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I))
    hm.aestronglyMeasurable hb).1
  apply hh.congr
  apply Eventually.of_forall
  intro q
  simpa only [sliceMap,onLines,ofReal_one,ofReal_zero,zero_mul,add_zero] using
    v2_residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)

theorem v2_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply (v2_continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1).congr
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  rw [v2_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem v2_source_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w))) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hi := v2_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  simpa only [verticalIntegral,integral_const_mul,mul_assoc] using
    (hi.integral_prod_left.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))).const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem v2_residue_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) 1 z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z))) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hi := v2_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  simpa only [verticalIntegral] using hi.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem v2_source_ordered_outer {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) +
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))) +
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  let R := HeckeReciprocal.regularizedL π 1
  let A := fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
    (fun w => K s w z*LFunction π (6*z)*LFunction π w))
  let B := fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
    (fun w => K s w z*LFunction π (6*z)*LFunction π w))
  let D := fun s => R*verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))
  let E := fun s => R^2/6*K s 1 (1/6)
  have hA : Integrable (fun t : ℝ => A ((a:ℂ)+t*I)) :=
    v2_source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) cw cw hX hY hZ ha hβ (by linarith) hcw ⟨by linarith,le_rfl⟩
      (by linarith) (ne_of_gt hcw)
  have hB : Integrable (fun t : ℝ => B ((a:ℂ)+t*I)) :=
    v2_source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) (19/20) cw hX hY hZ ha hβ (by linarith) hcw ⟨le_rfl,by linarith⟩
      (by linarith) (by norm_num)
  have hD : Integrable (fun t : ℝ => D ((a:ℂ)+t*I)) :=
    (v2_residue_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (33/200) hX hZ ha hβ le_rfl (by norm_num)).const_mul R
  have hp : ∀ᵐt : ℝ,A ((a:ℂ)+t*I)=B ((a:ℂ)+t*I)+D ((a:ℂ)+t*I)+E ((a:ℂ)+t*I) :=
    v2_source_ordered_ae η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e cw hX hY hZ ha hβ hcw he
  have hE : Integrable (fun t : ℝ => E ((a:ℂ)+t*I)) := by
    apply ((hA.sub hB).sub hD).congr
    filter_upwards [hp] with t ht
    change A ((a:ℂ)+t*I)-B ((a:ℂ)+t*I)-D ((a:ℂ)+t*I)=E ((a:ℂ)+t*I)
    rw [ht]
    ring
  have heq : verticalIntegral a A=verticalIntegral a (fun s => B s+D s+E s) := by
    unfold verticalIntegral
    congr 1
    exact integral_congr_ae hp
  rw [verticalIntegral_add a _ _ (hB.add hD) hE,verticalIntegral_add a _ _ hB hD] at heq
  change verticalIntegral a A=verticalIntegral a B+R*verticalIntegral a _+R^2/6*verticalIntegral a _
  rw [heq]
  simp only [D,E,verticalIntegral,integral_const_mul]
  ring

theorem v2_source_initial_ordered {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) =
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) +
    R*verticalIntegral 3 (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))) +
    R^2/6*verticalIntegral 3 (fun s => K s 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simpa only [show (1/6+11/6:ℝ)=2 by norm_num] using
    v2_source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z 3 (11/6) 3 hX hY hZ (by v2_geometry)
      (by linarith [HeckeZeroSupremum.beta_le_one]) (by v2_geometry) (by norm_num)

theorem v2_source_uniform_joint_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      6*ξ≠1→υ≠1→∀R : ℝ,0≤ R→
      (∫p : HeightSpace in outsideBox R,
        ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
          (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
          LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| * K/(1+R)^N := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := profile_uniform_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8 N
  obtain ⟨K0,hK0,hm⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ hξ1 hυ1 R hR0
  let A := arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1|
  have hA : 0≤ A := v2_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
    (abs_nonneg _) (abs_nonneg _)
  have hi := v2_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z σ ξ υ cw hX hY hZ (ha.trans hσ.1) (hβ.trans_le hσ.1) hξ.1 hcw hυ hξ1 hυ1
  have hmi := (hm σ hσ ξ hξ υ hυ).1
  have hbound := v2_arithmetic_onLines_bound η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ hξ1 hυ1 hC hR
  have hdom : ∀ᵐp : HeightSpace ∂heightMeasure,
      ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
      A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖) := by
    filter_upwards [v2_continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ] with p hp
    rw [←hp,←v2_arithmetic_profile_eq_source]
    rw [norm_mul]
    simpa only [mul_assoc,A,onLines] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg (onLines W0 W1 σ ξ υ p))
  calc
    _ ≤ ∫p : HeightSpace in outsideBox R,
        A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖) ∂heightMeasure :=
      integral_mono_ae hi.norm.integrableOn (hmi.const_mul A).integrableOn (ae_restrict_of_ae hdom)
    _ = A*(∫p : HeightSpace in outsideBox R,
        jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _ ≤ A*(K/(1+R)^N) := mul_le_mul_of_nonneg_left (hk σ hσ ξ hξ υ hυ R hR0) hA
    _ = _ := by dsimp [A]; ring

lemma v2_LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  classical
  have hm := ((HeckeOrigin.poleRemoved_entire χ).continuous.measurable).div
    (measurable_id.sub_const (1:ℂ))
  have h1 : Measurable (fun s : ℂ => if s=1 then LFunction χ 1 else HeckeOrigin.poleRemoved χ s/(s-1)) :=
    Measurable.ite (measurableSet_singleton (1:ℂ))
    (measurable_const : Measurable (fun _ : ℂ => LFunction χ 1)) hm
  have h0 : Measurable (fun s : ℂ => if s=0 then LFunction χ 0 else
      if s=1 then LFunction χ 1 else HeckeOrigin.poleRemoved χ s/(s-1)) :=
    Measurable.ite (measurableSet_singleton (0:ℂ))
    (measurable_const : Measurable (fun _ : ℂ => LFunction χ 0)) h1
  convert h0 using 1
  funext s
  split_ifs with hs0 hs1
  · subst s; rfl
  · subst s; rfl
  · exact v2_LFunction_eq_pole_quotient χ hs0 hs1

lemma v2_arithmetic_onLines_measurable_all {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : HeckeZeroSupremum.beta< a) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hH := v2_global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := v2_slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (v2_reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (v2_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => (υ:ℂ)+p.2*I))
  have hZL := (v2_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => 6*((ξ:ℂ)+p.1.2*I)))
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

lemma v2_joinWGap_pos (axis : SliceAxis) (υ : ℝ) (hυ : axis≠.w→υ≠1) : 0< joinWGap axis υ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold joinWGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hυ h))
lemma v2_joinZGap_pos (axis : SliceAxis) (ξ : ℝ) (hξ : axis≠.z→6*ξ≠1) : 0< joinZGap axis ξ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold joinZGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hξ h))

lemma v2_slice_w_gap (axis : SliceAxis) (R υ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinWGap axis υ≤‖((υ:ℂ)+(sliceMap axis R q).2*I)-1‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  cases axis
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using hR.trans (pole_distance_horizontal 1 υ R)
lemma v2_slice_z_gap (axis : SliceAxis) (R ξ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinZGap axis ξ≤‖6*((ξ:ℂ)+(sliceMap axis R q).1.2*I)-1‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  cases axis
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.1*I)-1)
  · have hi : 6*|R|≤‖6*((ξ:ℂ)+R*I)-1‖ := by
      simpa [abs_mul] using Complex.abs_im_le_norm (6*((ξ:ℂ)+R*I)-1)
    simpa [joinZGap,sliceMap] using (by linarith : (6:ℝ)≤6*|R|).trans hi
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.2*I)-1)

theorem v2_source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR0
  have hm := v2_arithmetic_onLines_measurable_all η S hS.prime J T b X Y Z σ ξ υ hX hY hZ (hβ.trans_le hσ.1)
  have hb (q : ℝ×ℝ) := v2_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C
    hX hY hZ ha hσ hξ hcw hυ (joinWGap axis υ) (joinZGap axis ξ)
    (v2_joinWGap_pos axis υ hυ1) (v2_joinZGap_pos axis ξ hξ1) hC hR (sliceMap axis R q)
    (v2_slice_w_gap axis R υ hR0 q) (v2_slice_z_gap axis R ξ hR0 q)
  have hh := hk σ hσ ξ hξ υ hυ axis R
    (arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ))
    (v2_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
      (v2_joinWGap_pos axis υ hυ1).le (v2_joinZGap_pos axis ξ hξ1).le)
    (fun q : ℝ×ℝ => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((σ:ℂ)+(sliceMap axis R q).1.1*I) ((υ:ℂ)+(sliceMap axis R q).2*I)
      ((ξ:ℂ)+(sliceMap axis R q).1.2*I))
    (hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable hb
  simpa only [onLines,v2_arithmetic_profile_eq_source] using hh

theorem v2_residue_uniform_moments {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Z→
      ∃C : ℝ,0≤ C ∧
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤ residueAmplitude S J T b X Z a ξ C*K := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) (5+N) 0
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  let A := residueAmplitude S J T b X Z a ξ C
  have hA : 0≤ A := v2_residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC
  let F : ℝ×ℝ → ℂ := fun q => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) *
    onLines W0 W1 a ξ 1 (sliceMap .w 0 q)
  have hm := v2_residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hFc : AEStronglyMeasurable F (volume.prod volume) := hm.aestronglyMeasurable.mul
    (((onLines_continuous W0 W1 a1 b1 ha1 hW1 a ξ 1 (by linarith)).comp
      (sliceMap_continuous .w 0)).aestronglyMeasurable)
  have hb := v2_residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hmom := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
  have hdom (q : ℝ×ℝ) : jointHeight q.1 q.2 0^N*‖F q‖≤
      A*(jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) := by
    dsimp only [F]
    rw [norm_mul]
    calc
      _ ≤ jointHeight q.1 q.2 0^N * ((A*jointHeight q.1 q.2 0^5)*
          ‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hb q) (norm_nonneg _))
          (pow_nonneg (jointHeight_pos _ _ _).le _)
      _ = _ := by rw [pow_add]; ring
  have hi : Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) := by
    apply (hmom.1.const_mul A).mono'
    · exact (by unfold jointHeight; fun_prop : Continuous (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)).aestronglyMeasurable.mul hFc.norm
    · apply Eventually.of_forall
      intro q
      simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)),sliceMap] using hdom q
  have hn : (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤ A*K := by
    calc
      _ ≤ ∫q : ℝ×ℝ,A*(jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖)
          ∂volume.prod volume := integral_mono hi (hmom.1.const_mul A) hdom
      _ = A*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖
          ∂volume.prod volume) := integral_const_mul _ _
      _ ≤ A*K := mul_le_mul_of_nonneg_left (by simpa only [sliceMap,pow_zero,div_one] using hmom.2) hA
  have heq : F =ᵐ[volume.prod volume] (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    dsimp only [F,onLines,sliceMap]
    simp only [ofReal_one,ofReal_zero,zero_mul,add_zero]
    rw [v2_residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z,
      v2_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
  have hweight : (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)=ᵐ[volume.prod volume]
      (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N) := Eventually.of_forall (fun _ => rfl)
  have heqw := hweight.mul (heq.fun_comp (fun z : ℂ => ‖z‖))
  exact ⟨hi.congr heqw, (integral_congr_ae heqw).symm.trans_le hn⟩

lemma v2_residueOutside_measurable (R : ℝ) : MeasurableSet (residueOutside R) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold residueOutside
  measurability

theorem v2_residue_uniform_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀R : ℝ,0≤ R→
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤
        residueAmplitude S J T b X Z a ξ C*K/(1+R)^N := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := v2_residue_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hi,hb⟩ := hk η S hS J T b hT X Y Z hX hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  let F := fun q : ℝ×ℝ =>
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
      (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
  have hF := v2_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  have hdom (q : ℝ×ℝ) (hq : q∈residueOutside R) :
      ‖F q‖≤ jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N := by
    have hh : 1+R≤ jointHeight q.1 q.2 0 := by
      rcases hq with h|h <;> unfold jointHeight <;> simp only [abs_zero,add_zero] <;>
        linarith [abs_nonneg q.1,abs_nonneg q.2]
    have hp := pow_le_pow_left₀ (by linarith : 0≤1+R) hh N
    apply (le_div_iff₀ (pow_pos (by linarith : 0<1+R) N)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (norm_nonneg (F q))
  change (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤_
  calc
    _ ≤ ∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N
        ∂volume.prod volume := setIntegral_mono_on hF.norm.integrableOn (hi.div_const _).integrableOn
          (v2_residueOutside_measurable R) hdom
    _ = (∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := integral_div _ _
    _ ≤ (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact setIntegral_le_integral hi (Eventually.of_forall (fun q =>
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

lemma v2_continued_high_slice_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ ξ υ : ℝ)
    (axis : SliceAxis) (R : ℝ) (hR : R≠0) :
    (fun q : ℝ×ℝ => let p := sliceMap axis R q
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS) ((υ:ℂ)+p.2*I)) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => let p := sliceMap axis R q
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS) ((υ:ℂ)+p.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,(sliceMap axis R q).1.1≠0 := by
    cases axis
    · exact Eventually.of_forall (fun _ => hR)
    · exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    · exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (σ:ℂ)+(sliceMap axis R q).1.1*I≠0 := by
    intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (σ:ℂ)+(sliceMap axis R q).1.1*I≠1 := by
    intro h; exact hq (by simpa using congrArg Complex.im h)
  dsimp only
  rw [v2_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma v2_source_axis_gaps {e : ℝ} (he : 0< e) :
    |(19/20:ℝ)-1|=1/20 ∧ |6*(1/6+e)-1|=6*e ∧ |6*(33/200:ℝ)-1|=1/100 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  constructor
  · norm_num
  constructor
  · rw [show 6*(1/6+e)-1=6*e by ring,abs_of_pos (by positivity)]
  · norm_num

theorem v2_raw_source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((σ:ℂ)+p.1.1*I) (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I))
        (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := v2_source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs Bz cw ha hβ hcw N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have hh := hc σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have heq := v2_continued_high_slice_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ axis R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

end
end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_source_uniform_joint_tails

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_residue_uniform_moments

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_raw_source_uniform_high_slices

end LocalModule173
/- END RHZeroFreeExtension.analytic_high.V2PrincipalContours -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2PrincipalTransport -/
section LocalModule174

set_option linter.unusedVariables false

/-! Actual ordered principal transport at the perturbed endpoint. The source
functions and positive Gaussian/tail measures are unchanged. Domain inputs
are supplied by freshly proved Euler and contour bounds; this file assumes
no improved transport theorem or physical high bound.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours ProbePrincipalTransport
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma v2_gaussianMoment_tendsto (n : ℕ) : Tendsto (gaussianMoment n) atTop (𝓝 0) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hb (t : ℝ) : gaussianMoment n t ≤ (2:ℝ)^(n-1)*Continuation.polynomialGaussian n t := by
    have h := add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg t) n
    unfold gaussianMoment height Continuation.polynomialGaussian
    calc
      _ ≤ ((2:ℝ)^(n-1)*(1^n+|t|^n))*Real.exp (-(t^2)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by simp only [one_pow]; ring
  exact squeeze_zero (gaussianMoment_nonneg n) hb
    (by simpa using (Continuation.polynomialGaussian_tendsto n).const_mul ((2:ℝ)^(n-1)))

lemma v2_gaussianMoment_even (n : ℕ) (t : ℝ) : gaussianMoment n (-t)=gaussianMoment n t := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simp [gaussianMoment,height]

lemma v2_gaussianMoment_tendsto_bot (n : ℕ) : Tendsto (gaussianMoment n) atBot (𝓝 0) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h := (v2_gaussianMoment_tendsto n).comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def,v2_gaussianMoment_even] using h

lemma v2_shifted_gaussian_integrable (n : ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => gaussianMoment n (t+v)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  exact (measurePreserving_add_right volume v).integrable_comp_of_integrable (gaussianMoment_integrable n)

lemma v2_shifted_gaussian_top (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (t+v)) atTop (𝓝 0) :=
  (v2_gaussianMoment_tendsto n).comp (tendsto_atTop_add_const_right _ v tendsto_id)

lemma v2_shifted_gaussian_bottom (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (-t+v)) atTop (𝓝 0) :=
by
  convert v2_shifted_gaussian_top n (-v) using 1
  funext t
  rw [←v2_gaussianMoment_even n (t + -v)]
  congr 1
  ring

theorem v2_verticalIntegral_eq_of_shifted_gaussian (F : ℂ → ℂ) {a c A : ℝ}
    (n : ℕ) (v : ℝ) (hac : a≤ c)
    (hF : DifferentiableOn ℂ F {s : ℂ | a≤ s.re ∧ s.re≤ c})
    (hb : ∀σ∈Icc a c,∀t : ℝ,‖F ((σ:ℂ)+t*I)‖≤ A*gaussianMoment n (t+v)) :
    verticalIntegral a F=verticalIntegral c F := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hc (σ : ℝ) (hσ : σ∈Icc a c) : Continuous (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    hF.continuousOn.comp_continuous (by fun_prop) (by intro t; simpa using hσ)
  have hi (σ : ℝ) (hσ : σ∈Icc a c) : Integrable (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    ((v2_shifted_gaussian_integrable n v).const_mul A).mono' (hc σ hσ).aestronglyMeasurable
      (Eventually.of_forall (hb σ hσ))
  have hj (T : ℝ) : ‖∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)‖≤ A*gaussianMoment n (T+v)*|c-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    exact hb σ (by simpa [uIcc_of_le hac] using uIoc_subset_uIcc hσ) T
  have ht : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hj
      (by simpa using ((v2_shifted_gaussian_top n v).const_mul A).mul_const |c-a|)
  have hbot : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+(-T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun T => by simpa only [Complex.ofReal_neg] using hj (-T))
      (by simpa using ((v2_shifted_gaussian_bottom n v).const_mul A).mul_const |c-a|)
  unfold verticalIntegral
  congr 1
  exact Continuation.vertical_integral_eq_of_horizontal_vanish F hac hF
    (hi a ⟨le_rfl,hac⟩) (hi c ⟨hac,le_rfl⟩) hbot ht

theorem v2_principal_box_majorant {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξlo : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξlo : 1/6<ξlo) :
    ∃ A : ℝ,0≤ A ∧ ∀σ∈Icc a 3,∀ξ∈Icc ξlo 2,∀p : HeightSpace,
      ‖continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2*I)‖≤ A*jointEnvelope 8 p := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hd⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 ξlo 2
    (by linarith) 10
  obtain ⟨E,hE,he⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) 3 3 10
  let A := arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
  let B := realGaussianBound a 3 ξlo 2*2^8*D*E
  have hA : 0≤ A := v2_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
    (by norm_num) hC (by norm_num) (by linarith)
  have hB : 0≤ B := by dsimp [B]; have := (realGaussianBound_pos a 3 ξlo 2).le; positivity
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro σ hσ ξ hξ p
  have hξ' : ξ∈Icc (33/200 : ℝ) 2 := ⟨by linarith [hξ.1],hξ.2⟩
  have hw : (2:ℝ)≤‖((3:ℂ)+p.2*I)-1‖ := by
    convert pole_distance_vertical 1 3 p.2 using 1; norm_num
  have hz : 6*ξlo-1≤‖6*((ξ:ℂ)+p.1.2*I)-1‖ := by
    have h := Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)
    have hh : 0≤6*ξ-1 := by linarith [hξ.1]
    simp only [sub_re,mul_re,ofReal_re,ofReal_im,add_re,I_re,I_im,mul_zero,
      zero_mul,sub_zero,add_zero,one_re] at h
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero] at h
    rw [abs_of_nonneg hh] at h
    exact le_trans (by linarith [hξ.1]) h
  have hb := v2_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a 3 2 3 σ ξ 3 C
    hX hY hZ ha hσ hξ' (by norm_num) (by norm_num) 2 (6*ξlo-1)
    (by norm_num) (by linarith) hC hR p hw hz
  have hp := profile_moment_majorant W0 W1 8 hσ hξ hD.le hE.le (hd ξ hξ)
    (he 3 ⟨le_rfl,le_rfl⟩) p
  rw [←v2_arithmetic_profile_eq_source,norm_mul]
  calc
    _ ≤ (A*jointHeight p.1.1 p.1.2 p.2^8)*‖profile W0 W1
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ 3 p‖) := by
      simp only [onLines,ofReal_ofNat]; ring
    _ ≤ A*(B*jointEnvelope 8 p) := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem v2_continued_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 1/6<ξ) (hξ2 : ξ≤2) (v u : ℝ) :
    verticalIntegral a (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 3 (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨A,hA,hb⟩ := v2_principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha.le hβ hξ
  have hh := v2_continued_source_differentiable_strip η S hS J T b hT W0 W1 X Y Z hZ
    ((3:ℂ)+u*I) ((ξ:ℂ)+v*I) (by norm_num) (by simpa using (show (4/25:ℝ)≤ξ by linarith)) ha hβ
    (c:=3)
  apply v2_verticalIntegral_eq_of_shifted_gaussian _ 8 v ha3
    ((hh.mul_const _).mul_const _) (A:=A*cauchy v*cauchy u)
  intro σ hσ t
  have h := hb σ hσ ξ ⟨le_rfl,hξ2⟩ ((t,v),u)
  simpa only [jointEnvelope,Prod.fst,Prod.snd,mul_assoc,mul_left_comm,mul_comm] using h

lemma v2_continued_source_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : RHV2.boundary≤ s.re) (hw : 9/10≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)
      {z : ℂ | 4/25< z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25< z.re} := (ProbeRadialMellin.radial_mellin_differentiable W0).mono
        (by intro z hz; change 0< z.re; change (4/25:ℝ)< z.re at hz; linarith)
  have hH := (v2_combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hnX : (X:ℂ)≠0 := by exact_mod_cast hX.ne'
  have hnZ : (Z:ℂ)≠0 := by exact_mod_cast hZ.ne'
  have he : (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)=
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s)*
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
        (globalClosedCorrection η S s w z*slotMultiplier η J T b s w z)) := by
    funext z; unfold continuedSourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hnX | exact Or.inl hnZ)

lemma v2_continued_principal_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : RHV2.boundary≤ s.re) (hw : 9/10≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w)
      {z : ℂ | 1/6< z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hK := v2_continued_source_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s w hs hw
  apply ((hK.mono (by intro z hz; change (4/25:ℝ)< z.re; change (1/6:ℝ)< z.re at hz; linarith)).mul ?_).mul_const
  intro z hz
  have h0 : (6*z:ℂ)≠0 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)< z.re at hz; linarith
  have h1 : (6*z:ℂ)≠1 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)< z.re at hz; linarith
  exact ((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) h0 (Or.inl h1)).comp z
    (differentiableAt_id.const_mul 6)).differentiableWithinAt

theorem v2_continued_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 1/6<ξ) (hξ2 : ξ≤2) (t u : ℝ) :
    verticalIntegral ξ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 2 (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨A,hA,hb⟩ := v2_principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha hβ hξ
  have hh := v2_continued_principal_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
    ((a:ℂ)+t*I) ((3:ℂ)+u*I) (by simpa using ha) (by norm_num)
  apply v2_verticalIntegral_eq_of_shifted_gaussian _ 8 t hξ2
    (hh.mono (by intro z hz; change (1/6:ℝ)< z.re; exact hξ.trans_le hz.1)) (A:=A*cauchy u)
  intro ζ hζ v
  have h := hb a ⟨le_rfl,ha3⟩ ζ hζ ((t,v),u)
  calc
    _ ≤ A*(gaussianMoment 8 (t+v)*cauchy v*cauchy u) := h
    _ ≤ A*(gaussianMoment 8 (t+v)*1*cauchy u) := by
      have hgu := gaussianMoment_nonneg 8 (t+v)
      have hcu := cauchy_nonneg u
      gcongr
      exact cauchy_le_one v
    _ = _ := by rw [add_comm t v]; ring

lemma v2_verticalIntegral_swap (F : ℂ → ℂ → ℂ) (a b : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ => F ((a:ℂ)+q.1*I) ((b:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun z => verticalIntegral b (F z))=
      verticalIntegral b (fun w => verticalIntegral a (fun z => F z w)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simp only [verticalIntegral,integral_const_mul]
  congr 2
  exact integral_integral_swap (f:=fun t u : ℝ => F ((a:ℂ)+t*I) ((b:ℂ)+u*I)) hi

lemma v2_verticalIntegral_triple_reverse (F : ℂ → ℂ → ℂ → ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace => F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w => F s w z)))=
      verticalIntegral υ (fun w => verticalIntegral ξ (fun z => verticalIntegral a (fun s => F s w z))) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h1 := integral_prod _ hi
  have h2 := integral_prod _ hi.integral_prod_left
  have h3 := integral_prod_symm _ hi
  have h4 : (∫u : ℝ,∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume)=
      ∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) := by
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu
  have he := h2.symm.trans (h1.symm.trans (h3.trans h4))
  simp only [verticalIntegral,integral_const_mul]
  congr 3

lemma v2_verticalIntegral_congr_line (F G : ℂ → ℂ) (a : ℝ)
    (h : ∀t : ℝ,F ((a:ℂ)+t*I)=G ((a:ℂ)+t*I)) : verticalIntegral a F=verticalIntegral a G := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold verticalIntegral
  congr 1
  exact integral_congr_ae (Eventually.of_forall h)

theorem v2_continued_triple_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (hξ : 1/6<ξ) (hξ2 : ξ≤2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral 3 (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  have hiA := v2_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha.le hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  have hi3 := v2_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 ξ 3 3 hX hY hZ (by v2_geometry) (hβ.trans_le ha3) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  rw [v2_verticalIntegral_triple_reverse F a ξ 3 hiA,v2_verticalIntegral_triple_reverse F 3 ξ 3 hi3]
  apply v2_verticalIntegral_congr_line
  intro u
  apply v2_verticalIntegral_congr_line
  intro v
  exact v2_continued_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 v u

theorem v2_continued_triple_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (hξ : 1/6<ξ) (hξ2 : ξ≤2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral a (fun s => verticalIntegral 2 (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  obtain ⟨Cξ,Kξ,hCξ,hKξ,hξi⟩ := v2_continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  obtain ⟨C2,K2,hC2,hK2,h2i⟩ := v2_continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 3 3 hX hY hZ ha hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  apply v2_verticalIntegral_congr_line
  intro t
  have hiξ := (hξi .s t).1
  have hi2 := (h2i .s t).1
  rw [v2_verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) ξ 3 hiξ,
    v2_verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) 2 3 hi2]
  apply v2_verticalIntegral_congr_line
  intro u
  exact v2_continued_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 t u

lemma v2_continued_triple_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w)))=
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w))) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  have h0 : (a:ℂ)+t*I≠0 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+t*I≠1 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  simp_rw [v2_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem v2_source_initial_placement {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  rw [←v2_continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z 3 2 3,
    ←v2_continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z a (1/6+e) 3]
  have hx := v2_continued_triple_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 hX hY hZ ha ha3 hβ (by norm_num) le_rfl
  have hz := v2_continued_triple_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a (1/6+e) hX hY hZ ha.le ha3 hβ (by linarith) (by linarith)
  exact hx.symm.trans hz.symm

theorem v2_source_initial_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  exact (v2_source_initial_placement η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2).trans
    (v2_source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e 3 hX hY hZ ha.le hβ (by norm_num) he)

lemma v2_continued_principal_measurable (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    {ι : Type*} (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (x w z : ℝ×(ℝ×ℝ) → ℂ) (hx : Continuous x) (hw : Continuous w) (hz : Continuous z)
    (hβ : ∀p,HeckeZeroSupremum.beta<(x p).re) (hz0 : ∀p,0<(z p).re) :
    Measurable (fun p => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z (x p) (w p) (z p)*
      LFunction (fixedSourcePrincipal S hS) (6*z p)*LFunction (fixedSourcePrincipal S hS) (w p)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hH := v2_global_correction_measurable η S x w z hx.measurable hw.measurable hz.measurable
  have hB := v2_slot_multiplier_measurable η J T b x w z hx.measurable hw.measurable hz.measurable
  have hR : Continuous (fun p => HeckeReciprocal.reciprocal (η.excludePrimes S hS) (x p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (HeckeReciprocal.reciprocal_differentiableAt _ (hβ p)).continuousAt.comp hx.continuousAt
  have hM0 : Continuous (fun p => mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (z p)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (ProbeRadialMellin.radial_mellin_analytic W0 _ (hz0 p)).continuousAt.comp hz.continuousAt
  have hM1 := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1
    (W1.smooth ⊤)).continuous.comp hw
  have hL6 := (v2_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p => 6*z p))
  have hLw := (v2_LFunction_measurable (fixedSourcePrincipal S hS)).comp hw.measurable
  have hm0 := hM0.measurable
  have hm1 := hM1.measurable
  have hmr := hR.measurable
  have hmx := hx.measurable
  have hmw := hw.measurable
  have hmz := hz.measurable
  unfold continuedSourceMultiplier
  fun_prop (disch := aesop)

lemma v2_strip_integrable_of_uniform_slices (F : ℝ×(ℝ×ℝ) → ℂ) (l r D : ℝ)
    (hlr : l≤ r) (hm : AEStronglyMeasurable F ((volume.restrict (Icc l r)).prod (volume.prod volume)))
    (hs : ∀σ∈Icc l r,Integrable (fun q => F (σ,q)) (volume.prod volume))
    (hb : ∀σ∈Icc l r,(∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)≤ D) :
    Integrable F ((volume.restrict (Icc l r)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc l r)).prod (volume.prod volume))≤(r-l)*D := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hm' := hm.norm.integral_prod_right'
  have hb' : ∀ᵐσ : ℝ ∂volume.restrict (Icc l r),
      ‖∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume‖≤ D := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb σ hσ
  have hi' : Integrable (fun σ : ℝ => ∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)
      (volume.restrict (Icc l r)) :=
    (integrableOn_const (s:=Icc l r) (C:=D) (hs:=by simp [Real.volume_Icc])).mono' hm' hb'
  have hi : Integrable F ((volume.restrict (Icc l r)).prod (volume.prod volume)) := by
    apply (integrable_prod_iff hm).mpr
    refine ⟨?_,hi'⟩
    filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
    exact hs σ hσ
  refine ⟨hi,?_⟩
  rw [integral_prod _ hi.norm]
  calc
    _ ≤ ∫σ : ℝ in Icc l r,D := integral_mono_ae hi' (integrableOn_const (hs:=by simp [Real.volume_Icc])) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with σ hσ
      exact hb σ hσ)
    _ = _ := by simp [sub_nonneg.mpr hlr,mul_comm]

theorem v2_uniform_high_x_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : RHV2.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀ξ∈Icc ξlo 2,∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc a 3)).prod (volume.prod volume))≤
      (3-a)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := v2_source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a 3 2 3 ha hβ (by norm_num) N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro ξ hξ R hR
  dsimp only
  let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
    ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
    LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
  have hcut := v2_continued_principal_measurable η S hS.prime J T b W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
    (fun p : ℝ×(ℝ×ℝ) => ((max a p.1:ℝ):ℂ)+R*I)
    (fun p : ℝ×(ℝ×ℝ) => (3:ℂ)+p.2.2*I)
    (fun p : ℝ×(ℝ×ℝ) => (ξ:ℂ)+p.2.1*I) (by fun_prop) (by fun_prop) (by fun_prop)
    (by intro p; simpa using hβ.trans_le (le_max_left a p.1))
    (by intro p; simpa using (show (0:ℝ)<ξ by linarith [hξ.1]))
  have hm : AEStronglyMeasurable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) := by
    apply hcut.aestronglyMeasurable.congr
    have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc a 3)).prod (volume.prod volume),p.1∈Icc a 3 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hh] with p hp
    dsimp [F]
    rw [max_eq_right hp.1]
  have hh (σ : ℝ) (hσ : σ∈Icc a 3) := hc σ hσ ξ ⟨by linarith [hξ.1],hξ.2⟩
    3 (by norm_num) .s (by intro _; norm_num) (by intro _; linarith [hξ.1]) R hR
  have hs (σ : ℝ) (hσ : σ∈Icc a 3) : Integrable (fun q => F (σ,q)) (volume.prod volume) := by
    simpa only [F,sliceMap,ofReal_ofNat] using (hh σ hσ).1
  have hb (σ : ℝ) (hσ : σ∈Icc a 3) : (∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)≤
      arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N := by
    have ht := (hh σ hσ).2
    norm_num [joinWGap,joinZGap,sliceMap] at ht
    simpa only [F,norm_mul] using ht
  exact v2_strip_integrable_of_uniform_slices F a 3 _ ha3 hm hs hb

theorem v2_uniform_high_z_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : RHV2.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (hξ2 : ξlo≤2) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume))≤
      (2-ξlo)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := v2_source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a 3 2 3 ha hβ (by norm_num) N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  dsimp only
  let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
    ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
    LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
    LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
  have hcut := v2_continued_principal_measurable η S hS.prime J T b W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
    (fun p : ℝ×(ℝ×ℝ) => (a:ℂ)+p.2.1*I)
    (fun p : ℝ×(ℝ×ℝ) => (3:ℂ)+p.2.2*I)
    (fun p : ℝ×(ℝ×ℝ) => ((max ξlo p.1:ℝ):ℂ)+R*I) (by fun_prop) (by fun_prop) (by fun_prop)
    (by intro p; simpa using hβ)
    (by intro p; simpa using (show (0:ℝ)< max ξlo p.1 by linarith [le_max_left ξlo p.1]))
  have hm : AEStronglyMeasurable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) := by
    apply hcut.aestronglyMeasurable.congr
    have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume),p.1∈Icc ξlo 2 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hh] with p hp
    dsimp [F]
    rw [max_eq_right hp.1]
  have hh (ξ : ℝ) (hξ : ξ∈Icc ξlo 2) := hc a ⟨le_rfl,ha3⟩ ξ ⟨by linarith [hξ.1],hξ.2⟩
    3 (by norm_num) .z (by intro _; norm_num) (by simp) R hR
  have hs (ξ : ℝ) (hξ : ξ∈Icc ξlo 2) : Integrable (fun q => F (ξ,q)) (volume.prod volume) := by
    simpa only [F,sliceMap,ofReal_ofNat] using (hh ξ hξ).1
  have hb (ξ : ℝ) (hξ : ξ∈Icc ξlo 2) : (∫q : ℝ×ℝ,‖F (ξ,q)‖ ∂volume.prod volume)≤
      arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N := by
    have ht := (hh ξ hξ).2
    norm_num [joinWGap,joinZGap,sliceMap] at ht
    simpa only [F,norm_mul] using ht
  exact v2_strip_integrable_of_uniform_slices F ξlo 2 _ hξ2 hm hs hb

lemma v2_high_x_join_ae_raw {ι : Type*} (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ R : ℝ) (hR : R≠0) :
    (fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.2.1*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I))
      =ᵐ[(volume.restrict (Icc a 3)).prod (volume.prod volume)]
    (fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((p.1:ℂ)+R*I)
      (globalClosedCorrection η S ((p.1:ℂ)+R*I)) (slotMultiplier η J T b ((p.1:ℂ)+R*I))
      ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.2.1*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply Eventually.of_forall
  intro p
  have h0 : (p.1:ℂ)+R*I≠0 := by intro h; exact hR (by simpa using congrArg Complex.im h)
  have h1 : (p.1:ℂ)+R*I≠1 := by intro h; exact hR (by simpa using congrArg Complex.im h)
  dsimp only
  rw [v2_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma v2_high_z_join_ae_raw {ι : Type*} (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξlo R : ℝ) :
    (fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((p.1:ℂ)+R*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I))
      =ᵐ[(volume.restrict (Icc ξlo 2)).prod (volume.prod volume)]
    (fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((a:ℂ)+p.2.1*I)
      (globalClosedCorrection η S ((a:ℂ)+p.2.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.2.1*I))
      ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
      LFunction (fixedSourcePrincipal S hS) (6*((p.1:ℂ)+R*I))*
      LFunction (fixedSourcePrincipal S hS) ((3:ℂ)+p.2.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume),p.2.1≠0 :=
    Measure.quasiMeasurePreserving_snd.ae
      (Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ)))
  filter_upwards [hh] with p hp
  have h0 : (a:ℂ)+p.2.1*I≠0 := by intro h; exact hp (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+p.2.1*I≠1 := by intro h; exact hp (by simpa using congrArg Complex.im h)
  rw [v2_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem v2_raw_uniform_high_x_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : RHV2.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀ξ∈Icc ξlo 2,∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((p.1:ℂ)+R*I)
        (globalClosedCorrection η S ((p.1:ℂ)+R*I)) (slotMultiplier η J T b ((p.1:ℂ)+R*I)) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc a 3)).prod (volume.prod volume))≤
      (3-a)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := v2_uniform_high_x_joins W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξlo ha ha3 hβ hξlo N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro ξ hξ R hR
  have hh := hc ξ hξ R hR
  have heq := v2_high_x_join_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

theorem v2_raw_uniform_high_z_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : RHV2.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξlo : 1/6<ξlo) (hξ2 : ξlo≤2) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.2.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.2.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.2.1*I)) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume))≤
      (2-ξlo)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  obtain ⟨K,hK,hk⟩ := v2_uniform_high_z_joins W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξlo ha ha3 hβ hξlo hξ2 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := hc R hR
  have heq := v2_high_z_join_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξlo R
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

theorem v2_source_initial_joint_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))+
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z)))+
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  have hh := v2_source_initial_ordered_at_a η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2
  have hf := (v2_source_joint_fubini η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 2 3 3 hX hY hZ (by v2_geometry) (hβ.trans_le ha3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have hi : (((1/(2*Real.pi):ℝ):ℂ)^3)*(∫p : HeightSpace,
      K ((3:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((2:ℂ)+p.1.2*I)*
        LFunction π (6*((2:ℂ)+p.1.2*I))*LFunction π ((3:ℂ)+p.2*I) ∂heightMeasure)=
      verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
        (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
    dsimp [K,π]
    simp only [ofReal_ofNat] at hf
    rw [hf]
    simp only [verticalIntegral,integral_const_mul,ofReal_ofNat]
    ring
  exact hi.trans hh

end
end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_source_initial_joint_ordered_at_a

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_raw_uniform_high_x_joins

end LocalModule174
/- END RHZeroFreeExtension.analytic_high.V2PrincipalTransport -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2PrincipalPhysical -/
section LocalModule175
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open Complex MeasureTheory
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours ProbePrincipalPhysical
local notation "Id" => Ideal HeckeFamily.O
theorem v2_principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHV2.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=> primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact v2_source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=> hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule175
/- END RHZeroFreeExtension.analytic_high.V2PrincipalPhysical -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2PrincipalSlot -/
section LocalModule176

set_option linter.unusedVariables false

/-! Sharp actual principal and region slot estimates on the new domain.
The unit cancellation and compensated local identity are unchanged. Bounds
use the exact v2 boundary, with a proved rational bracket for local arithmetic.
Correction inverses use the actual broad summable Euler estimate.
All slot/scalar functions are the original upstream mathematical objects.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open Complex
open OAI OAI.SevenEighths
open ProbeEuler ProbeLocal PrincipalSlotEstimate

theorem v2_principal_correction_defect {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re) :
    ‖unramifiedClosed Q A η 1 s 1 (1 / 6) - 1‖ ≤ 1 / 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have h := v2_unramifiedClosed_open_region_bound Q A η 1 s 1 (1 / 6)
    (by linarith) hA hη (by simp) (hBlo.trans hs) (by v2_geometry) (by v2_geometry)
  calc
    _ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) := h
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by v2_geometry)) (by v2_geometry)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem v2_principal_correction_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h := v2_principal_correction_defect hQ hA hη hs
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s 1 (1 / 6))
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem v2_principal_correction_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) ≠ 0 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (v2_principal_correction_lower_bound hQ hA hη hs)

theorem v2_principal_correction_inverse_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re) :
    ‖(unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹‖ ≤ 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hl := v2_principal_correction_lower_bound hQ hA hη hs
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖)).mpr
  linarith

theorem v2_unit_phase_inverse (η : ℂ) (hη : ‖η‖ = 1) : star η * η = 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hη]
  norm_num

theorem v2_principal_coord_cancellation {Q : ℝ} (hQ : 0 < Q) (η s : ℂ) (hη : ‖η‖ = 1) :
    (star η * (Q : ℂ) ^ s) * coordD Q η 1 s = 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold coordD
  simp only [star_one, mul_one]
  calc
    _ = (star η * η) * ((Q : ℂ) ^ s * (Q : ℂ) ^ (-s)) := by ring
    _ = 1 := by rw [v2_unit_phase_inverse η hη, ← Complex.cpow_add _ _ hQ0]; simp

theorem v2_principal_V {Q : ℝ} : coordV Q (1 / 6) = (Q : ℂ)⁻¹ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  norm_num [coordV, Complex.cpow_neg_one]

theorem v2_principal_W {Q : ℝ} : coordW Q 1 1 = (Q : ℂ)⁻¹ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simp [coordW, Complex.cpow_neg_one]

theorem v2_principal_B_norm {Q : ℝ} (hQ : 0 < Q) (η s : ℂ) (hη : ‖η‖ = 1) :
    ‖star η * (Q : ℂ) ^ s‖ = Q ^ s.re := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [norm_mul, norm_star, hη, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]

theorem v2_compensated_unit_error_bound (V W D P B q : ℂ) (T : ℝ)
    (_hT : 0 ≤ T) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1)
    (hD : ‖D‖ ≤ 1 / 2) (hq : ‖q‖ ≤ 1)
    (hVT : ‖V‖ ≤ T) (hDT : ‖D‖ ≤ T)
    (hE : ‖P + D‖ ≤ 28 * T) (hBE : ‖B‖ * ‖P + D‖ ≤ 28 * T)
    (hBD : B * D = 1) (hWq : W = q) :
    ‖compensatedReplacement V W D P B q + continuedCorrection V W D P‖ ≤ 720 * T := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h1V : ‖1 - V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have h1W : ‖1 - W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have h1q : ‖1 - q‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) q
    simp only [norm_one] at this
    linarith
  have hiV := inv_one_sub_norm_le_two V hV
  have hiD := inv_one_sub_norm_le_two D hD
  have hfac : ‖(1 - V) * (1 - W) / (1 - D)‖ ≤ 8 := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖1 - V‖ * ‖1 - W‖ * ‖(1 - D)⁻¹‖ ≤ (2 : ℝ) * 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hleft : ‖(1 - q) * (V / (1 - V) - D)‖ ≤ 6 * T := by
    calc
      _ = ‖1 - q‖ * ‖V / (1 - V) - D‖ := norm_mul _ _
      _ ≤ 2 * (‖V‖ * 2 + ‖D‖) := by
        gcongr
        calc
          _ ≤ ‖V / (1 - V)‖ + ‖D‖ := norm_sub_le _ _
          _ ≤ _ := by rw [div_eq_mul_inv, norm_mul]; gcongr
      _ ≤ 6 * T := by linarith
  have hright : ‖(B + 1 - q) * (P + D)‖ ≤ 84 * T := by
    have hc : ‖B + 1 - q‖ ≤ ‖B‖ + 2 := by
      calc
        _ = ‖B + (1 - q)‖ := by congr 1; ring
        _ ≤ ‖B‖ + ‖1 - q‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ = ‖B + 1 - q‖ * ‖P + D‖ := norm_mul _ _
      _ ≤ (‖B‖ + 2) * ‖P + D‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 84 * T := by nlinarith
  have hid := continued_normalized_cancellation V W D P B q 1
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD)
    hBD (by simpa using hWq)
  simp only [mul_one] at hid
  rw [hid, norm_mul]
  calc
    _ ≤ 8 * (‖(1 - q) * (V / (1 - V) - D)‖ + ‖(B + 1 - q) * (P + D)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 720 * T := by linarith

theorem v2_principal_marked_error_bounds {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHV2.boundary ≤ s.re) :
    ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(RHV2.boundary : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by
    have h := coordW_norm_le Q hQ0 (1 : ℂ) 1 (by simp)
    norm_num at h
    exact h.trans (by simpa using hpow (-1) 0 (by v2_geometry))
  have hR : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (3 - 6 * s.re) := by
    convert coordR_norm_le Q hQ0 A s (1 / 6) hA using 1
    norm_num
    congr 1
    ring
  have hD : ‖coordD Q η 1 s‖ ≤ Q ^ (-s.re) :=
    coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hK : ‖coordK Q η s 1‖ ≤ Q ^ (-s.re) := by
    convert coordK_norm_le Q hQ1 η s 1 hη.le using 1
    norm_num
  have hB := v2_principal_B_norm hQ0 η s hη
  have hRhalf : ‖coordR Q A s (1 / 6)‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q (3 - 6 * s.re) hQ4 (by linarith))
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by v2_geometry)
  have hDhalf : ‖coordD Q η 1 s‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [← v2_principal_V]; linarith
  have hE := unramified_marked_error_bound (coordR Q A s (1 / 6))
    (coordV Q (1 / 6)) (Q : ℂ)⁻¹ (coordK Q η s 1) (coordW Q 1 1)
    (coordD Q η 1 s) hRhalf hVhalf hq hDhalf
  change ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (-(RHV2.boundary : ℝ)) :=
    hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(RHV2.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ (-s.re) * Q ^ (-1 : ℝ) := by rw [hV]; gcongr
      _ = Q ^ (-s.re - 1) := by rw [← Real.rpow_add hQ0]; congr 1
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s (1 / 6)‖ ≤
      Q ^ (-(RHV2.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by rw [hB]; gcongr
      _ = Q ^ (3 - 5 * s.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ *
      (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) ≤ Q ^ (-(RHV2.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (-s.re) * Q ^ (-1 : ℝ)) := by rw [hB, hV]; gcongr
      _ = Q ^ (-1 : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hQ0]; simp
      _ ≤ _ := hpow _ _ (by v2_geometry)
  have hE' : ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s (1 / 6)‖ + 4 * (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s (1 / 6)))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem v2_principal_replacement_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHV2.boundary ≤ s.re) :
    ‖principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      720 * Q ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by v2_geometry)
  have hD := coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hDhalf := hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hWq : coordW Q 1 1 = (Q : ℂ) ^ (-1 : ℂ) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-1 : ℂ)‖ ≤ 1 := by
    rw [Complex.cpow_neg_one, ← v2_principal_V]; linarith
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by rw [hWq]; exact hq
  have hVT : ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(RHV2.boundary : ℝ)) := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by v2_geometry)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(RHV2.boundary : ℝ)) :=
    hD.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := v2_principal_marked_error_bounds hQ hA hη hs
  exact v2_compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hVhalf hW hDhalf hq hVT hDT hE.1 hE.2
    (v2_principal_coord_cancellation hQ0 η s hη) hWq

theorem v2_principal_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHV2.boundary ≤ s.re) :
    ‖principalSlot Q A η s + 1‖ ≤ 1440 * Q ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hn := v2_principal_correction_ne_zero hQ hA hη.le hs
  have he := v2_principal_replacement_error hQ hA hη hs
  have hi := v2_principal_correction_inverse_bound hQ hA hη.le hs
  have hid : principalSlot Q A η s + 1 =
      (principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)) *
        (unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹ := by
    unfold principalSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(RHV2.boundary : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem v2_actual_target_norm (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) :
    ‖HeckeFamily.elementCoeff η p‖ = 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : Finite (HeckeFamily.O ⧸ η.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ η.modulus) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := hp
  unfold HeckeFamily.elementCoeff
  rw [← hu]
  exact FiniteRayExpansion.norm_char_unit η.residue u

theorem v2_actual_principal_slot_error (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : RHV2.boundary ≤ s.re) :
    ‖principalSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(RHV2.boundary : ℝ)) :=
  v2_principal_slot_error hQ (actualAPhase_norm_le_one η p) (v2_actual_target_norm η p hp) hs

theorem v2_weighted_slot_error {ι : Type*} (S : Finset ι) (w : ι → ℝ) (B : ι → ℂ)
    (δ : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (hB : ∀ i ∈ S, ‖B i + 1‖ ≤ δ) :
    ‖(∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ)‖ ≤
      δ * ∑ i ∈ S, w i := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hid : (∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ) =
      ∑ i ∈ S, (w i : ℂ) * (B i + 1) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, Complex.ofReal_sum]
  rw [hid]
  calc
    _ ≤ ∑ i ∈ S, ‖(w i : ℂ) * (B i + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, δ * w i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hB i hi) (hw i hi)
    _ = _ := by rw [Finset.mul_sum]

theorem v2_weighted_slot_relative_error {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (B : ι → ℂ) (δ : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hB : ∀ i ∈ S, ‖B i + 1‖ ≤ δ) (hS : 0 < ∑ i ∈ S, w i) :
    ‖(∑ i ∈ S, (w i : ℂ) * B i) / (-(∑ i ∈ S, w i : ℝ) : ℂ) - 1‖ ≤ δ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hSc : ((∑ i ∈ S, w i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  have hid : (∑ i ∈ S, (w i : ℂ) * B i) / (-(∑ i ∈ S, w i : ℝ) : ℂ) - 1 =
      -((∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ)) /
        (∑ i ∈ S, w i : ℝ) := by field_simp; ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  exact (div_le_iff₀ hS).mpr (v2_weighted_slot_error S w B δ hw hB)

theorem v2_weighted_principal_slot_error {ι : Type*} (S : Finset ι) (w Q : ι → ℝ)
    (A η : ι → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : RHV2.boundary ≤ s.re) :
    ‖(∑ i ∈ S, (w i : ℂ) * principalSlot (Q i) (A i) (η i) s) +
        (∑ i ∈ S, w i : ℝ)‖ ≤
      (1440 * P ^ (-(RHV2.boundary : ℝ))) * ∑ i ∈ S, w i := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply v2_weighted_slot_error S w _ _ hw
  intro i hi
  apply (v2_principal_slot_error (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs).trans
  apply mul_le_mul_of_nonneg_left _ (by v2_geometry)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by v2_geometry)

theorem v2_product_error {κ : Type*} (S : Finset κ) (F : κ → ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hF : ∀ i ∈ S, ‖F i - 1‖ ≤ δ) :
    ‖(∏ i ∈ S, F i) - 1‖ ≤ (1 + δ) ^ S.card - 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have haF := hF a (Finset.mem_insert_self a S)
    have hSF : ∀ i ∈ S, ‖F i - 1‖ ≤ δ := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hprod := ih hSF
    have haN : ‖F a‖ ≤ 1 + δ := by
      have h := norm_sub_norm_le (F a) (1 : ℂ)
      simp only [norm_one] at h
      linarith
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = ‖F a * ((∏ i ∈ S, F i) - 1) + (F a - 1)‖ := by congr 1; ring
      _ ≤ ‖F a * ((∏ i ∈ S, F i) - 1)‖ + ‖F a - 1‖ := norm_add_le _ _
      _ ≤ (1 + δ) * ((1 + δ) ^ S.card - 1) + δ := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul haN hprod (norm_nonneg _) (by linarith)) haF
      _ = _ := by rw [pow_succ]; ring

theorem v2_product_error_linear (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 + δ) ^ n - 1 ≤ n * 2 ^ n * δ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by v2_geometry)
    have hbase : 0 ≤ (1 + δ) ^ n - 1 := by
      exact sub_nonneg.mpr (one_le_pow₀ (by linarith))
    calc
      _ = (1 + δ) * ((1 + δ) ^ n - 1) + δ := by rw [pow_succ]; ring
      _ ≤ 2 * ((n : ℝ) * 2 ^ n * δ) + δ := by
        gcongr
        linarith
      _ ≤ _ := by rw [Nat.cast_succ, pow_succ]; nlinarith

theorem v2_principalScalar_eq {κ : Type*} (S : Finset κ) (M : κ → ℝ) :
    principalScalar S M = ∏ i ∈ S, (-(M i : ℂ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  unfold principalScalar
  rw [Complex.ofReal_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem v2_principalScalar_ne_zero {κ : Type*} (S : Finset κ) (M : κ → ℝ)
    (hM : ∀ i ∈ S, 0 < M i) : principalScalar S M ≠ 0 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [v2_principalScalar_eq]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hM i hi).ne')

theorem v2_fixed_product_relative_error {κ : Type*} (S : Finset κ)
    (M : κ → ℝ) (W : κ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ i ∈ S, 0 < M i)
    (hW : ∀ i ∈ S, ‖W i + (M i : ℂ)‖ ≤ δ * M i) :
    ‖(∏ i ∈ S, W i) / principalScalar S M - 1‖ ≤ (1 + δ) ^ S.card - 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [v2_principalScalar_eq, ← Finset.prod_div_distrib]
  apply v2_product_error S _ δ hδ
  intro i hi
  have hMi : (M i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM i hi).ne'
  have hid : W i / (-(M i : ℂ)) - 1 = -(W i + (M i : ℂ)) / (M i : ℂ) := by
    field_simp
    ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hM i hi)]
  exact (div_le_iff₀ (hM i hi)).mpr (hW i hi)

theorem v2_fixed_product_relative_error_linear {κ : Type*} (S : Finset κ)
    (M : κ → ℝ) (W : κ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : ∀ i ∈ S, 0 < M i)
    (hW : ∀ i ∈ S, ‖W i + (M i : ℂ)‖ ≤ δ * M i) :
    ‖(∏ i ∈ S, W i) / principalScalar S M - 1‖ ≤ S.card * 2 ^ S.card * δ :=
  (v2_fixed_product_relative_error S M W δ hδ hM hW).trans
    (v2_product_error_linear S.card hδ hδ1)

theorem v2_weighted_principal_product_error {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : RHV2.boundary ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      (1 + 1440 * P ^ (-(RHV2.boundary : ℝ))) ^ S.card - 1 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply v2_fixed_product_relative_error S _ _ _ (by positivity) hM
  intro j hj
  exact v2_weighted_principal_slot_error (T j) (w j) (Q j) (A j) (η j) s P hP
    (hw j hj) (hQ j hj) (hA j hj) (hη j hj) hs

theorem v2_principal_geometric_bounds {Q : ℝ} {η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re) :
    ‖coordV Q (1 / 6)‖ ≤ 1 / 2 ∧ ‖coordW Q 1 1‖ ≤ 1 / 2 ∧
      ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    norm_num
    exact rpow_le_half Q (-1) hQ4 (by v2_geometry)
  refine ⟨hV, ?_, ?_⟩
  · rw [v2_principal_W, ← v2_principal_V]; exact hV
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans
      (rpow_le_half Q (-s.re) hQ4 (by linarith))

theorem v2_principal_correction_eq_raw {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) =
      localCorrection (coordV Q (1 / 6)) (coordW Q 1 1) (coordD Q η 1 s)
        (principalMarked Q A η s) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h := v2_principal_geometric_bounds hQ hη hs
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem v2_principal_raw_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re) :
    1 / 16 ≤ ‖principalRawFactor Q A η s‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hl := v2_principal_correction_lower_bound hQ hA hη hs
  have hg := v2_principal_geometric_bounds hQ hη hs
  have hV : ‖1 - coordV Q (1 / 6)‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordV Q (1 / 6))
    simp only [norm_one] at this
    linarith [hg.1]
  have hW : ‖1 - coordW Q 1 1‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordW Q 1 1)
    simp only [norm_one] at this
    linarith [hg.2.1]
  have hD := inv_one_sub_norm_le_two (coordD Q η 1 s) hg.2.2
  have hupper : ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      8 * ‖principalRawFactor Q A η s‖ := by
    rw [v2_principal_correction_eq_raw hQ hη hs]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖principalRawFactor Q A η s‖ *
      (‖1 - coordV Q (1 / 6)‖ * ‖1 - coordW Q 1 1‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖principalRawFactor Q A η s‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem v2_principal_raw_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re) :
    principalRawFactor Q A η s ≠ 0 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (v2_principal_raw_lower_bound hQ hA hη hs)

theorem v2_principal_slot_eq_raw {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re) :
    principalSlot Q A η s =
      (star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hg := v2_principal_geometric_bounds hQ hη hs
  have hn := v2_principal_correction_ne_zero hQ hA hη hs
  have hp := v2_principal_raw_ne_zero hQ hA hη hs
  have hr := compensatedReplacement_eq_raw (coordV Q (1 / 6)) (coordW Q 1 1)
    (coordD Q η 1 s) (principalMarked Q A η s) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-1 : ℂ))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← v2_principal_correction_eq_raw hQ hη hs] at hr
  unfold principalSlot principalReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem v2_principal_raw_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHV2.boundary ≤ s.re) :
    ‖(star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) + 1‖ ≤ 1440 * Q ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [← v2_principal_slot_eq_raw hQ hA hη.le hs]
  exact v2_principal_slot_error hQ hA hη hs

theorem v2_weighted_principal_product_error_linear {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : RHV2.boundary ≤ s.re)
    (hsmall : 1440 * P ^ (-(RHV2.boundary : ℝ)) ≤ 1)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      S.card * 2 ^ S.card * (1440 * P ^ (-(RHV2.boundary : ℝ))) :=
  (v2_weighted_principal_product_error S T w Q A η s P hP hs hw hQ hA hη hM).trans
    (v2_product_error_linear S.card (by positivity) hsmall)

theorem v2_region_correction_defect {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖unramifiedClosed Q A η 1 s w z - 1‖ ≤ 1 / 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  calc
    _ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) :=
      v2_unramifiedClosed_open_region_bound Q A η 1 s w z (by linarith) hA hη (by simp) (hBlo.trans hs) (by linarith) (by linarith)
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by v2_geometry)) (by v2_geometry)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem v2_region_correction_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s w z‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h := v2_region_correction_defect hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem v2_region_correction_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z ≠ 0 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (v2_region_correction_lower_bound hQ hA hη hs hw hz)

theorem v2_region_correction_inverse_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(unramifiedClosed Q A η 1 s w z)⁻¹‖ ≤ 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hl := v2_region_correction_lower_bound hQ hA hη hs hw hz
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s w z‖)).mpr
  linarith

theorem v2_region_geometric_bounds {Q : ℝ} {η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖coordV Q z‖ ≤ 1 / 2 ∧ ‖coordW Q 1 w‖ ≤ 1 / 2 ∧ ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ4 (by linarith)
  · exact (coordW_norm_le Q hQ0 1 w (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))

theorem v2_region_marked_error_bounds {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(RHV2.boundary : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 η s w hη.le
  have hB := v2_principal_B_norm hQ0 η s hη
  have hg := v2_region_geometric_bounds hQ hη.le hs hw hz
  have hRhalf : ‖coordR Q A s z‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ4 (by linarith))
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have hE := unramified_marked_error_bound (coordR Q A s z) (coordV Q z)
    (Q : ℂ)⁻¹ (coordK Q η s w) (coordW Q 1 w) (coordD Q η 1 s)
    hRhalf hg.1 hq hg.2.2
  change ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s z‖ ≤ Q ^ (-(RHV2.boundary : ℝ)) := hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s w‖ * ‖coordV Q z‖ ≤ Q ^ (-(RHV2.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s z‖ ≤ Q ^ (-(RHV2.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ * (‖coordK Q η s w‖ * ‖coordV Q z‖) ≤
      Q ^ (-(RHV2.boundary : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re)) := by rw [hB, hV]; gcongr
      _ = Q ^ (1 - w.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hE' : ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s z‖ + 4 * (‖coordK Q η s w‖ * ‖coordV Q z‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s z))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem v2_region_replacement_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z‖ ≤
      720 * Q ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hg := v2_region_geometric_bounds hQ hη.le hs hw hz
  have hWq : coordW Q 1 w = (Q : ℂ) ^ (-w) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by rw [← hWq]; linarith [hg.2.1]
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hVT : ‖coordV Q z‖ ≤ Q ^ (-(RHV2.boundary : ℝ)) := by
    rw [coordV_norm Q hQ0]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(RHV2.boundary : ℝ)) :=
    (coordD_norm_le Q hQ0 η 1 s hη.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := v2_region_marked_error_bounds hQ hA hη hs hw hz
  exact v2_compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (v2_principal_coord_cancellation hQ0 η s hη) hWq

theorem v2_region_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z + 1‖ ≤ 1440 * Q ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hn := v2_region_correction_ne_zero hQ hA hη.le hs hw hz
  have he := v2_region_replacement_error hQ hA hη hs hw hz
  have hi := v2_region_correction_inverse_bound hQ hA hη.le hs hw hz
  have hid : regionSlot Q A η s w z + 1 =
      (regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z) *
        (unramifiedClosed Q A η 1 s w z)⁻¹ := by
    unfold regionSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(RHV2.boundary : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

@[simp] theorem v2_region_slot_at_residue (Q : ℝ) (A η s : ℂ) :
    regionSlot Q A η s 1 (1 / 6) = principalSlot Q A η s := rfl

theorem v2_region_correction_eq_raw {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z =
      localCorrection (coordV Q z) (coordW Q 1 w) (coordD Q η 1 s)
        (regionMarked Q A η s w z) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have h := v2_region_geometric_bounds hQ hη hs hw hz
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem v2_region_raw_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 16 ≤ ‖regionRawFactor Q A η s w z‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hl := v2_region_correction_lower_bound hQ hA hη hs hw hz
  have hg := v2_region_geometric_bounds hQ hη hs hw hz
  have hV : ‖1 - coordV Q z‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordV Q z)
    simp only [norm_one] at this
    linarith [hg.1]
  have hW : ‖1 - coordW Q 1 w‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordW Q 1 w)
    simp only [norm_one] at this
    linarith [hg.2.1]
  have hD := inv_one_sub_norm_le_two (coordD Q η 1 s) hg.2.2
  have hupper : ‖unramifiedClosed Q A η 1 s w z‖ ≤
      8 * ‖regionRawFactor Q A η s w z‖ := by
    rw [v2_region_correction_eq_raw hQ hη hs hw hz]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖regionRawFactor Q A η s w z‖ *
      (‖1 - coordV Q z‖ * ‖1 - coordW Q 1 w‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖regionRawFactor Q A η s w z‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem v2_region_raw_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    regionRawFactor Q A η s w z ≠ 0 := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (v2_region_raw_lower_bound hQ hA hη hs hw hz)

theorem v2_region_slot_eq_raw {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    regionSlot Q A η s w z =
      (star η * (Q : ℂ) ^ s) * regionMarked Q A η s w z / regionRawFactor Q A η s w z -
        (Q : ℂ) ^ (-w) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hg := v2_region_geometric_bounds hQ hη hs hw hz
  have hn := v2_region_correction_ne_zero hQ hA hη hs hw hz
  have hp := v2_region_raw_ne_zero hQ hA hη hs hw hz
  have hr := compensatedReplacement_eq_raw (coordV Q z) (coordW Q 1 w)
    (coordD Q η 1 s) (regionMarked Q A η s w z) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-w))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← v2_region_correction_eq_raw hQ hη hs hw hz] at hr
  unfold regionSlot regionReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem v2_region_raw_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(star η * (Q : ℂ) ^ s) * regionMarked Q A η s w z / regionRawFactor Q A η s w z -
        (Q : ℂ) ^ (-w) + 1‖ ≤ 1440 * Q ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [← v2_region_slot_eq_raw hQ hA hη.le hs hw hz]
  exact v2_region_slot_error hQ hA hη hs hw hz

theorem v2_region_slot_norm_le {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z‖ ≤ 1 + 1440 * Q ^ (-(RHV2.boundary : ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have he := v2_region_slot_error hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (regionSlot Q A η s w z) (-1 : ℂ)
  simp only [norm_neg, norm_one, sub_neg_eq_add] at hn
  linarith

theorem v2_weighted_region_slot_norm {ι : Type*} (S : Finset ι) (b Q : ι → ℝ)
    (A η : ι → ℂ) (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hb : ∀ i ∈ S, 0 ≤ b i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : RHV2.boundary ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖∑ i ∈ S, (b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ ≤
      (1 + 1440 * P ^ (-(RHV2.boundary : ℝ))) * ∑ i ∈ S, b i * (Q i) ^ (z.re - 1) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  calc
    _ ≤ ∑ i ∈ S, ‖(b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (1 + 1440 * P ^ (-(RHV2.boundary : ℝ))) * (b i * (Q i) ^ (z.re - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hQi : 0 < Q i := by linarith [hQ i hi]
      have he := v2_region_slot_norm_le (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs hw hz
      have he' : ‖regionSlot (Q i) (A i) (η i) s w z‖ ≤ 1 + 1440 * P ^ (-(RHV2.boundary : ℝ)) := by
        apply he.trans
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by v2_geometry)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by v2_geometry)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi),
        Complex.norm_cpow_eq_rpow_re_of_pos hQi]
      simp only [Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_left he'
        (mul_nonneg (hb i hi) (Real.rpow_nonneg hQi.le _))).trans_eq (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

theorem v2_actual_region_slot_error (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s w z : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : RHV2.boundary ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s w z + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(RHV2.boundary : ℝ)) :=
  v2_region_slot_error hQ (actualAPhase_norm_le_one η p) (v2_actual_target_norm η p hp) hs hw hz

end
end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.v2_actual_principal_slot_error
#print axioms RHZeroFreeExtension.AnalyticHigh.v2_weighted_principal_product_error_linear
#print axioms RHZeroFreeExtension.AnalyticHigh.v2_actual_region_slot_error

end LocalModule176
/- END RHZeroFreeExtension.analytic_high.V2PrincipalSlot -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2SharpProduct -/
section LocalModule177

set_option linter.unusedVariables false

/-! Sharp fixed positive slot bounds for the genuine finite Euler product.
This derives the new exponent in the small-prime error from proved local
unit cancellation; no sharp product estimate is an input.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss HeckeFamily ProbePhysical ProbeEuler ProbeLocal ProbeFiniteProductBounds
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

theorem v2_slot_norm_bound_sharp {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤ b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : RHV2.boundary≤ s.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1+1440*Pmin^(-(RHV2.boundary : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using v2_weighted_region_slot_norm (T j) (b j)
    (fun P => (Ideal.absNorm P.val : ℝ)) (fun P => actualAPhase η (primaryGenerator P.val))
    (fun P => idealCoeff η P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
    (fun P _ => actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem v2_combined_slot_bound_sharp {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤ b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : RHV2.boundary≤ s.re) (hw : 19/20≤ w.re) (hz : 33/200≤ z.re) :
    ‖globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3/2) * ∏ j ∈ J, (1+1440*Pmin^(-(RHV2.boundary : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  rw [norm_mul]
  exact mul_le_mul (v2_global_norm_bound η S hS s w z hs (by linarith) (by linarith))
    (v2_slot_norm_bound_sharp η J T b Pmin hPmin hb hQ hη s w z hs hw hz) (norm_nonneg _) (by norm_num)


end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule177
/- END RHZeroFreeExtension.analytic_high.V2SharpProduct -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2RemainderBounds -/
section LocalModule178


noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
open OAI OAI.SevenEighths
open ProbePrincipalRemainderBounds
namespace RHZeroFreeExtension.AnalyticHigh
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma v2_remainder_active_prime_sum_bound (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (W : ℝ→ℝ)
    (c d B P ξ : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hP : 0< P)
    (hthreshold : 480≤ c*P) (hξ : ξ≤1)
    (hW : ∀x,0≤ W x ∧ W x≤ B) (hsupp : Function.support W⊆Icc c d) :
    (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))
      ≤(128*d*B*c^(ξ-1))*P^ξ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let A := T.filter (fun p=> W ((Ideal.absNorm p.val:ℝ)/P)≠0)
  have hA (p : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hp : p∈A) :
      c*P≤(Ideal.absNorm p.val:ℝ) ∧ (Ideal.absNorm p.val:ℝ)≤ d*P := by
    have h := hsupp (Finset.mem_filter.mp hp).2
    exact ⟨(le_div_iff₀ hP).mp h.1,(div_le_iff₀ hP).mp h.2⟩
  have he : (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))=
      ∑p∈A,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hw : W ((Ideal.absNorm p.val:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hp,hh⟩)
    simp [hw]
  have hcount : (A.card:ℝ)≤128*(d*P) := by
    have h := DescentFiberCost.finite_ideal_count_real (A.image Subtype.val) (d*P)
      (by nlinarith) (by
        intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact p.property.ne_zero)
      (by intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact (hA p hp).2)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h
  have hp (p : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hp : p∈A) : (Ideal.absNorm p.val:ℝ)^(ξ-1)≤ c^(ξ-1)*P^(ξ-1) := by
    rw [←Real.mul_rpow hc.le hP.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hP) (hA p hp).1 (by linarith)
  rw [he]
  calc
    _≤∑_p∈A,B*(c^(ξ-1)*P^(ξ-1)) := Finset.sum_le_sum (fun p hpA=>
      mul_le_mul (hW _).2 (hp p hpA) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB)
    _=(A.card:ℝ)*(B*(c^(ξ-1)*P^(ξ-1))) := by simp
    _≤(128*(d*P))*(B*(c^(ξ-1)*P^(ξ-1))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _=(128*d*B*c^(ξ-1))*P^ξ := by
      have heP : P*P^(ξ-1)=P^ξ := by
        calc
          _=P^(1:ℝ)*P^(ξ-1) := by rw [Real.rpow_one]
          _=P^ξ := by rw [←Real.rpow_add hP];congr 1;ring
      calc
        _=(128*d*B*c^(ξ-1))*(P*P^(ξ-1)) := by ring
        _=_ := by rw [heP]

def v2_remainder_slotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3/2)*∏_j∈J,(1+1440*(480:ℝ)^(-(RHV2.boundary:ℝ)))*(128*d*B*c^(ξ-1))

lemma v2_remainder_slotConstant_nonneg {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) : 0≤ v2_remainder_slotConstant J c d B ξ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hd0 : 0≤ d := hc.le.trans hd
  unfold v2_remainder_slotConstant
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _=> by positivity)

theorem v2_remainder_window_sharp_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hξ : ξ≤1)
    (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤ W j x ∧ W j x≤ B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0< P j)
    (hthreshold : ∀j∈J,480≤ c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j)
    (T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (s w z : ℂ)
    (hs : RHV2.boundary≤ s.re) (hw : 19/20≤ w.re) (hz : z.re=ξ) (hzlo : 33/200≤ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖≤
      v2_remainder_slotConstant J c d B ξ * ∏j∈J,(P j)^ξ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let A (j : ι) := (T j).filter (fun p=> W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hp : p∈A j) : c*P j≤(Ideal.absNorm p.val:ℝ) :=
    (le_div_iff₀ (hP j hj)).mp ((hsupp j hj) (Finset.mem_filter.mp hp).2).1
  have he : windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z =
      slotMultiplier η J A (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) s w z := by
    unfold windowMultiplier slotMultiplier
    apply Finset.prod_congr rfl
    intro j hj
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hh : W j ((Ideal.absNorm p.val:ℝ)/P j)=0 := by
      by_contra h; exact hn (Finset.mem_filter.mpr ⟨hp,h⟩)
    simp [hh]
  rw [he]
  have h := v2_combined_slot_bound_sharp η S hS J A
    (fun j p=> W j ((Ideal.absNorm p.val:ℝ)/P j)) 480 (by norm_num)
    (fun j hj p _=>(hW j hj _).1)
    (fun j hj p hp=>(hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp=> PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
      (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
        exact_mod_cast (hmod j hj).trans_le (hA j hj p hp)))) s w z hs hw (by rw [hz];exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _≤(3/2)*∏j∈J,(1+1440*(480:ℝ)^(-(RHV2.boundary:ℝ)))*((128*d*B*c^(ξ-1))*(P j)^ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro j hj; apply mul_nonneg (by positivity);exact Finset.sum_nonneg (fun p _=> by
          exact mul_nonneg (hW j hj _).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left (v2_remainder_active_prime_sum_bound (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [v2_remainder_slotConstant,←mul_assoc,Finset.prod_mul_distrib]

lemma v2_remainder_scalePower_nonneg {X Y Z a ξ υ : ℝ} (hX : 0≤ X) (hY : 0≤ Y) (hZ : 0≤ Z) :
    0≤ scalePower X Y Z a ξ υ := by unfold scalePower;positivity

section Pointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0< c) (hd : c≤ d) (hB : 0≤ B) (hξ : ξ≤1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤ W j x ∧ W j x≤ B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0< P j) (hthreshold : ∀j∈J,480≤ c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)< c*P j) (T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
  (ha : RHV2.boundary≤ a) (hυ : 19/20≤υ) (hzlo : 33/200≤ξ) (hC : 0≤ C)
  (hR : ∀s : ℂ,a≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

lemma v2_remainder_continued_source_sharp_pointwise (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)‖ ≤
    scalePower X Y Z a ξ υ*(C*v2_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight t v u^2*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  have hslot := v2_remainder_window_sharp_bound η S hS.tail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)
    (by simpa using ha) (by simpa using hυ) (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)‖≤ C*jointHeight t v u^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := v2_height_le_joint_s t v u
    have hh0 := height_pos t
    unfold height jointHeight at *
    nlinarith [abs_nonneg t,abs_nonneg v,abs_nonneg u]
  have hx : ‖(X:ℂ)^(1/2-((ξ:ℂ)+v*I))‖=X^(1/2-ξ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX];congr 1;simp
  have hz : ‖(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)‖=Z^(a+ξ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ];congr 1;simp
  have hy : ‖(Y:ℂ)^(((υ:ℂ)+u*I)-1)‖=Y^(υ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY];congr 1;simp
  have he : continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) =
      (X:ℂ)^(1/2-((ξ:ℂ)+v*I))*(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)*
      (Y:ℂ)^(((υ:ℂ)+u*I)-1)*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)*
      (globalClosedCorrection η S ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)*
        windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I))*
      onLines W0 W1 a ξ υ ((t,v),u) := by
    unfold continuedSourceMultiplier windowMultiplier onLines profile;ring
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,norm_mul,hx,hz,hy]
  calc
    _≤ X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)*(C*jointHeight t v u^2)*
      (v2_remainder_slotConstant J c d B ξ*(∏j∈J,(P j)^ξ))*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
      gcongr
    _=_ := by unfold scalePower;ring

lemma v2_remainder_full_sharp_pointwise (hυhi : υ≤2) (hυ1 : υ≠1) (hξ1 : 6*ξ≠1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
    (C*v2_remainder_slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*
      (wAmplitude (∏q∈S,q) 2/|υ-1|)) *
      (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))*
      (jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := v2_remainder_continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := v2_fixed_principal_z_bound (∏q∈S,q) 1 ξ p.1.2 ⟨hzlo,hξ⟩ hξ1
  have hlw := v2_fixed_principal_w_bound (∏q∈S,q) (by norm_num : (1:ℝ)<2) ⟨hυ,hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (v2_zBoxAmplitude_nonneg (∏q∈S,q) 1) (abs_nonneg (6*ξ-1))
  have hAW := div_nonneg (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le (abs_nonneg (υ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  have hslot := v2_remainder_slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := v2_remainder_scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
  have ht := (height_pos p.1.1).le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul,norm_mul]
  calc
    _≤(scalePower X Y Z a ξ υ*(C*v2_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*height p.1.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*height p.2^3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _≤(scalePower X Y Z a ξ υ*(C*v2_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*jointHeight p.1.1 p.1.2 p.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*jointHeight p.1.1 p.1.2 p.2^3) := by
      have hs := v2_remainder_scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
      gcongr <;> first | positivity | exact v2_height_le_joint_z _ _ _ | exact v2_height_le_joint_w _ _ _
    _=_ := by ring

omit hυ in
lemma v2_remainder_residue_sharp_pointwise (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ≤
    (C*v2_remainder_slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  have hBlo : (437/500 : ℝ) ≤ RHV2.boundary := by v2_geometry
  have hBhi : RHV2.boundary ≤ (9/10 : ℝ) := by v2_geometry
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := v2_remainder_continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one,ofReal_zero,zero_mul,add_zero] at h0
  have hlz := v2_fixed_principal_z_bound (∏p∈S,p) 1 ξ q.2 ⟨hzlo,hξ⟩ hξ1
  have hAZ := div_nonneg (v2_zBoxAmplitude_nonneg (∏p∈S,p) 1) (abs_nonneg (6*ξ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=> Real.rpow_nonneg (hP j hj).le _)
  have hslot := v2_remainder_slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := v2_remainder_scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _≤(scalePower X Y Z a ξ 1*(C*v2_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*height q.2^3) := by
      gcongr ; first | positivity | exact h0 | exact hlz
    _≤(scalePower X Y Z a ξ 1*(C*v2_remainder_slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr ; first | positivity | exact v2_height_le_joint_z _ _ _
