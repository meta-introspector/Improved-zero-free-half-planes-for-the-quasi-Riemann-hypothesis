    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx.le hz
  have hm := marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => selectedMultiplier η T x w z) {x : ℂ | 7/8 < x.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => local_analytic_x η S hS P (hT P hp) w z hw hz)

theorem slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | 7/8 < x.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem window_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : ι → ℝ → ℂ) (scale : ι → ℝ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => windowMultiplier η J T W scale x w z) {x : ℂ | 7/8 < x.re} :=
  slot_analytic_x η S hS J T _ hT w z hw hz

theorem combined_selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * selectedMultiplier η T x w z)
      {x : ℂ | 7/8 < x.re} :=
  (globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (selected_analytic_x η S hS T hT w z hw hz)

theorem combined_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {x : ℂ | 7/8 < x.re} :=
  (globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (slot_analytic_x η S hS J T b hT w z hw hz)

def continuedSourceMultiplier {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z) * (Z:ℂ)^(x+z-1) * (Y:ℂ)^(w-1) *
    Complex.exp ((x+z-1)^2) *
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z * mellin W1 w *
      HeckeReciprocal.reciprocal (η.excludePrimes S hS) x *
      globalClosedCorrection η S x w z * slotMultiplier η J T b x w z

theorem continued_source_analytic_x {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (7/8 : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (7/8 : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta<x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : x≠0) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  simp only [continuedSourceMultiplier,sourceMultiplier,
    HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,div_eq_mul_inv]

theorem continued_source_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a : ℝ) (w z : ℂ) :
    (fun t : ℝ => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z ((a:ℂ)+t*I) w z)
      =ᵐ[volume] (fun t : ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
        ((a:ℂ)+t*I) (globalClosedCorrection η S ((a:ℂ)+t*I))
          (slotMultiplier η J T b ((a:ℂ)+t*I)) w z) := by
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply continued_source_eq_raw
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem source_analytic_x_off_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z)
      {x : ℂ | max (7/8 : ℝ) HeckeZeroSupremum.beta < x.re ∧ x≠1} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _
    ((Complex.isOpen_re_gt _).inter (isClosed_singleton.isOpen_compl))
  intro x hx
  have hx' : (7/8 : ℝ)<x.re := lt_of_le_of_lt (le_max_left _ _) hx.1
  have hβ : HeckeZeroSupremum.beta<x.re := lt_of_le_of_lt (le_max_right _ _) hx.1
  have hx0 : x≠0 := by intro h; simp only [h,zero_re] at hx'; norm_num at hx'
  have hL := LFunction_differentiableAt (η.excludePrimes S hS.prime) hx0 (Or.inl hx.2)
  have hLn := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime) hβ (Or.inl hx.2)
  have hH := (globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  unfold sourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem continued_source_differentiable_strip {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : 7/8<a) (hβ : HeckeZeroSupremum.beta<a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤x.re ∧ x.re≤c} := by
  apply (continued_source_analytic_x η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

theorem continued_source_principal_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (w z : ℂ)
    (hχ : (η.excludePrimes S hS).residue=1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z 1 w z=0 := by
  simp only [continuedSourceMultiplier,HeckeReciprocal.reciprocal_principal_one _ hχ,mul_zero,zero_mul]

end SevenEighths.ProbeFiniteProductX
end

end OAI
end OAIOriginalModule2476

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalContours
Source SHA256: fefc1bbcb8eaab512a8d3b92bc2e374852333de8b8bee0ff43945fd0b8d9db8b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2477




namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O
local instance : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

@[fun_prop] lemma measurable_const_cpow {α : Type*} [MeasurableSpace α] (Q : ℝ) (hQ : 0<Q)
    (f : α → ℂ) (hf : Measurable f) : Measurable (fun x => (Q:ℂ)^f x) := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_cpow (Or.inl hn)).continuous.measurable).comp hf

lemma ideal_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => idealClosedCorrection η P (x t) (w t) (z t)) := by
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealClosedCorrection unramifiedClosed continuedCorrection markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma global_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (S : Finset Id) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => globalClosedCorrection η S (x t) (w t) (z t)) := by
  unfold globalClosedCorrection
  exact Measurable.tprod (fun P => ideal_correction_measurable η P.val x w z hx hw hz)

lemma local_multiplier_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => localMultiplier η P (x t) (w t) (z t)) := by
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc := ideal_correction_measurable η P x w z hx hw hz
  unfold localMultiplier compensatedReplacement idealMarkedClosed markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma slot_multiplier_measurable {α ι : Type*} [MeasurableSpace α]
    (η : Character) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (x w z : α → ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => slotMultiplier η J T b (x t) (w t) (z t)) := by
  unfold slotMultiplier
  apply Finset.measurable_prod
  intro j hj
  apply Finset.measurable_sum
  intro P hP
  exact measurable_const.mul (local_multiplier_measurable η P x w z hx hw hz)

def zBoxAmplitude (M : Id) (Bz : ℝ) : ℝ :=
  36*max 6 (6*Bz+1)*principalConstant M

lemma zBoxAmplitude_nonneg (M : Id) [NeZero M] (Bz : ℝ) : 0≤zBoxAmplitude M Bz := by
  unfold zBoxAmplitude
  exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _)))
    (principalConstant_pos M).le

lemma fixed_principal_z_box_growth (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤zBoxAmplitude M Bz*height t^3 := by
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(6*((ξ:ℂ)+t*I) : ℂ).re by simp; linarith [hξ.1])
  have hn : ‖6*((ξ:ℂ)+t*I)+1‖≤max 6 (6*Bz+1)*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    have hm : (6:ℝ)≤max 6 (6*Bz+1) := le_max_left _ _
    have hm' : 6*ξ+1≤max 6 (6*Bz+1) := (by linarith [hξ.2] : 6*ξ+1≤6*Bz+1).trans (le_max_right _ _)
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
  have hmax : 0≤max (6:ℝ) (6*Bz+1) := le_trans (by norm_num) (le_max_left _ _)
  have hh := (height_pos t).le
  rw [hi] at hb
  calc
    _ ≤ principalConstant M*‖6*((ξ:ℂ)+t*I)+1‖*(3+6*|t|)^2 := hb
    _ ≤ principalConstant M*(max 6 (6*Bz+1)*height t)*(36*height t^2) := by
      gcongr
    _ = _ := by unfold zBoxAmplitude; ring

lemma LFunction_eq_pole_quotient (χ : Character) {s : ℂ} (h0 : s≠0) (h1 : s≠1) :
    LFunction χ s=HeckeOrigin.poleRemoved χ s/(s-1) := by
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)).symm

lemma LFunction_vertical_continuous (χ : Character) (a : ℝ) (ha0 : a≠0) (ha1 : a≠1) :
    Continuous (fun t : ℝ => LFunction χ ((a:ℂ)+t*I)) := by
  have h0 (t : ℝ) : (a:ℂ)+t*I≠0 := by intro h; exact ha0 (by simpa using congrArg Complex.re h)
  have h1 (t : ℝ) : (a:ℂ)+t*I≠1 := by intro h; exact ha1 (by simpa using congrArg Complex.re h)
  have hc := ((HeckeOrigin.poleRemoved_entire χ).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I))).div
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I-1)) (fun t => sub_ne_zero.mpr (h1 t))
  exact hc.congr (fun t => (LFunction_eq_pole_quotient χ (h0 t) (h1 t)).symm)

lemma reciprocal_vertical_continuous (χ : Character) (a : ℝ) (ha : HeckeZeroSupremum.beta<a) :
    Continuous (fun t : ℝ => HeckeReciprocal.reciprocal χ ((a:ℂ)+t*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (HeckeReciprocal.reciprocal_differentiableAt χ (by simpa using ha)).continuousAt.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I)).continuousAt

lemma LFunction_norm_le_of_poleRemoved (χ : Character) (s : ℂ) (h0 : s≠0) (h1 : s≠1)
    (A δ : ℝ) (hδ : 0<δ) (hd : δ≤‖s-1‖) (hA : ‖HeckeOrigin.poleRemoved χ s‖≤A) :
    ‖LFunction χ s‖≤A/δ := by
  apply (le_div_iff₀ hδ).mpr
  calc
    _ ≤ ‖LFunction χ s‖*‖s-1‖ := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = ‖HeckeOrigin.poleRemoved χ s‖ := by rw [HeckeOrigin.poleRemoved_eq χ h0 h1,norm_mul]; ring
    _ ≤ A := hA

lemma fixed_principal_w_bound (M : Id) [NeZero M] {cw υ : ℝ} (hcw : 1<cw)
    (hυ : υ∈Icc (19/20 : ℝ) cw) (hυ1 : υ≠1) (t : ℝ) :
    ‖LFunction (fixedPrincipal M) ((υ:ℂ)+t*I)‖≤
      (wAmplitude M cw/|υ-1|)*height t^3 := by
  have h0 : (υ:ℂ)+t*I≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hυ.1]
  have h1 : (υ:ℂ)+t*I≠1 := by intro h; exact hυ1 (by simpa using congrArg Complex.re h)
  have hδ : 0 < |υ-1| := abs_pos.mpr (sub_ne_zero.mpr hυ1)
  have h := LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ
    (pole_distance_vertical 1 υ t) (fixed_principal_w_growth M hcw hυ t)
  convert h using 1
  ring

lemma fixed_principal_z_bound (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) (hξ1 : 6*ξ≠1) :
    ‖LFunction (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤
      (zBoxAmplitude M Bz/|6*ξ-1|)*height t^3 := by
  have h0 : (6*((ξ:ℂ)+t*I) : ℂ)≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hξ.1]
  have h1 : (6*((ξ:ℂ)+t*I) : ℂ)≠1 := by intro h; exact hξ1 (by simpa using congrArg Complex.re h)
  have hd : |6*ξ-1|≤‖6*((ξ:ℂ)+t*I)-1‖ := by
    simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+t*I)-1)
  have hδ : 0 < |6*ξ-1| := abs_pos.mpr (sub_ne_zero.mpr hξ1)
  have h := LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ hd
    (fixed_principal_z_box_growth M Bz ξ t hξ)
  convert h using 1
  ring

def arithmeticMultiplier {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Y Z : ℝ) (s w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*(Y:ℂ)^(w-1)*
    HeckeReciprocal.reciprocal (η.excludePrimes S hS) s *
    (globalClosedCorrection η S s w z*slotMultiplier η J T b s w z)*
    LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w

lemma arithmetic_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    arithmeticMultiplier η S hS J T b X Y Z s w z*profile W0 W1 s w z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z *
        LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w := by
  unfold arithmeticMultiplier profile continuedSourceMultiplier
  ring

lemma arithmetic_onLines_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : HeckeZeroSupremum.beta<a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) (hυ0 : υ≠0) (hυ1 : υ≠1) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hH := global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) υ hυ0 hυ1).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.2))
  have hZL := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
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

def boxScale (X Y Z a Bs Bz cw : ℝ) : ℝ :=
  scaleBound X (1/2-Bz) (1/2-33/200) * scaleBound Z (a+33/200-1) (Bs+Bz-1) *
    scaleBound Y (19/20-1) (cw-1)

lemma boxScale_pos (X Y Z a Bs Bz cw : ℝ) : 0<boxScale X Y Z a Bs Bz cw := by
  unfold boxScale
  exact mul_pos (mul_pos (scaleBound_pos _ _ _) (scaleBound_pos _ _ _)) (scaleBound_pos _ _ _)

def arithmeticAmplitude {ι : Type*} (S : Finset Id) (J : Finset ι)
    (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) : ℝ :=
  boxScale X Y Z a Bs Bz cw * C * ((3/2)*slotBound J T b Bs Bz) *
    (zBoxAmplitude (∏P∈S,P) Bz/δz) * (wAmplitude (∏P∈S,P) cw/δw)

lemma height_le_joint_s (t v u : ℝ) : height t≤jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg v,abs_nonneg u]
lemma height_le_joint_z (t v u : ℝ) : height v≤jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg u]
lemma height_le_joint_w (t v u : ℝ) : height u≤jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg v]

lemma arithmetic_onLines_bound_of_gaps {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (δw δz : ℝ) (hdw : 0<δw) (hdz : 0<δz)
    (hC : 0≤C) (hR : ∀s : ℂ, a≤s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤C*(1+|s.im|^2))
    (p : HeightSpace)
    (hwgap : δw≤‖((υ:ℂ)+p.2*I)-1‖) (hzgap : δz≤‖6*((ξ:ℂ)+p.1.2*I)-1‖) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz *
        jointHeight p.1.1 p.1.2 p.2^8 := by
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
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖≤C*height p.1.1^2 := by
    apply (hR _ (by simpa using hσ.1)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg p.1.1]
  have hh := combined_slot_bound η S hS.tail J T b hT ((σ:ℂ)+p.1.1*I)
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
  have hlz0 := LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hz0 hz1 _ _ hdz hzgap
    (fixed_principal_z_box_growth (∏P∈S,P) Bz ξ p.1.2 hξ)
  have hlw0 := LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hw0 hw1 _ _ hdw hwgap
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
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (slotBound_nonneg J T b Bs Bz)
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏P∈S,P) Bz) hdz.le
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
      gcongr <;> first | positivity | exact height_le_joint_s _ _ _ | exact height_le_joint_z _ _ _ | exact height_le_joint_w _ _ _
    _ = _ := by unfold arithmeticAmplitude boxScale; ring

lemma arithmetic_onLines_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1)
    (hC : 0≤C) (hR : ∀s : ℂ, a≤s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤C*(1+|s.im|^2))
    (p : HeightSpace) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  apply arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ |υ-1| |6*ξ-1| (abs_pos.mpr (sub_ne_zero.mpr hυ1))
    (abs_pos.mpr (sub_ne_zero.mpr hξ1)) hC hR p
  · exact pole_distance_vertical 1 υ p.2
  · simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)

theorem continued_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ υ
    (by linarith) (fun p : HeightSpace => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I))
    (arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
      (by linarith) hξ1 (by linarith [hυ.1]) hυ1).aestronglyMeasurable
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|) 8
    (arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
      ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR)
  apply hi.congr
  exact Eventually.of_forall (fun p => arithmetic_profile_eq_source η S hS.prime J T b W0 W1 X Y Z _ _ _)

lemma outer_height_ne_zero_ae : ∀ᵐp : HeightSpace ∂heightMeasure, p.1.1≠0 := by
  have hh : ∀ᵐp : ℝ×ℝ ∂volume.prod volume, p.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  exact Measure.quasiMeasurePreserving_fst.ae hh

lemma continued_joint_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    (fun p : HeightSpace => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) =ᵐ[heightMeasure]
    (fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
      ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
      (slotMultiplier η J T b ((a:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  filter_upwards [outer_height_ne_zero_ae] with p hp
  apply continued_source_eq_raw
  · intro h; exact hp (by simpa using congrArg Complex.im h)
  · intro h; exact hp (by simpa using congrArg Complex.im h)

theorem source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  apply (continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1).congr
  filter_upwards [continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ] with p hp
  rw [hp]

theorem source_joint_fubini {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    ((∫p, F p ∂heightMeasure)=∫t : ℝ,∫v : ℝ,∫u : ℝ,F ((t,v),u)) ∧
    ((∫p, F p ∂heightMeasure)=∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((t,v),u)) := by
  dsimp only
  have hi := source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu

lemma arithmeticAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) (hcw : 1<cw) (hC : 0≤C) (hw : 0≤δw) (hz : 0≤δz) :
    0≤arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hbox := (boxScale_pos X Y Z a Bs Bz cw).le
  have hb := slotBound_nonneg J T b Bs Bz
  have hza := zBoxAmplitude_nonneg (∏P∈S,P) Bz
  have hwa := (wAmplitude_pos (∏P∈S,P) hcw).le
  unfold arithmeticAmplitude
  positivity

theorem continued_source_slices {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) (N : ℕ) :
    ∃ C K : ℝ, 0≤C ∧ 0<K ∧ ∀axis : SliceAxis,∀R : ℝ,
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume)≤
        arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1| *K/height R^N := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ υ υ (by linarith) 8 N
  refine ⟨C,K,hC,hK,?_⟩
  intro axis R
  let G : HeightSpace → ℂ := fun p => arithmeticMultiplier η S hS.prime J T b X Y Z
    ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)
  have hm := arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
    (by linarith) hξ1 (by linarith [hυ.1]) hυ1
  have hbound := arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
    ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR
  have hh := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩ axis R
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|)
    (arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a a ξ cw C _ _ hcw hC (abs_nonneg _) (abs_nonneg _))
    (fun q => G (sliceMap axis R q)) ((hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable)
    (fun q => hbound (sliceMap axis R q))
  simpa only [G,onLines,arithmetic_profile_eq_source] using hh

theorem source_w_leftover_outer_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    Integrable (fun v : ℝ => verticalIntegral (19/20) (fun w =>
      K w ((1/6+e:ℝ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime)
        (6*((1/6+e:ℝ)+v*I))*LFunction (fixedSourcePrincipal S hS.prime) w)) := by
  obtain ⟨C,K,hC,hK,hslice⟩ := continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1
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
    simpa only [sliceMap,continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ hs0 hs1] using hi
  simpa only [verticalIntegral] using hpair.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0⊆Icc a0 b0) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : 7/8≤s.re) (hη : LFunction (η.excludePrimes S hS.prime) s≠0)
    {e : ℝ} (he : 0<e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)) (33/200) (1/6+e) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 (∏P∈S,P)
    X Y Z hX hZ (η.excludePrimes S hS.prime) s hη
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) (AL := zBoxAmplitude (∏P∈S,P) (1/6+e))
    he (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _))
    (zBoxAmplitude_nonneg _ _) 0 3
  · exact (combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)<z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using combined_slot_bound η S hS.tail J T b hT s
      1 ((x:ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)
  · intro x hx t _
    exact fixed_principal_z_box_growth (∏P∈S,P) (1/6+e) x t hx

theorem source_ordered_at_height {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (he : 0<e)
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
  dsimp only
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hs : (7/8 : ℝ)≤(((a:ℂ)+t*I) : ℂ).re := by simpa using ha
  have hη := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime)
    (show HeckeZeroSupremum.beta<(((a:ℂ)+t*I) : ℂ).re by simpa using hβ) (Or.inl hs1)
  have hzb := source_z_boundary_any η S hS J T b hT W0 W1 a0 b0 ha0 hW0 X Y Z hX hZ
    ((a:ℂ)+t*I) hs hη he
  apply source_ordered_double_shift (fixedSourcePrincipal S hS.prime) _ hcw he
  · intro z hz
    apply (source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith)).mono
    intro w hw
    change (9/10 : ℝ)<w.re
    linarith [hw.1]
  · intro z hz
    have hh := ProbeFiniteProductBounds.source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏P∈S,P) X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith) hη hcw
    convert boundary_mul_const _ _ _ hh (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
    funext w
    dsimp only [fixedSourcePrincipal,fixedPrincipal]
    ring
  · apply (source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
      ((a:ℂ)+t*I) 1 hs (by norm_num)).mono
    intro z hz
    change (4/25 : ℝ)<z.re
    linarith [hz.1]
  · exact hzb
  · exact source_w_leftover_outer_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e t hX hY hZ ha hβ he hs1

theorem source_ordered_ae {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (he : 0<e) :
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
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply source_ordered_at_height η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e t cw hX hY hZ ha hβ hcw he
  intro h
  exact ht (by simpa using congrArg Complex.im h)

def residueArithmetic {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Z : ℝ) (s z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*HeckeReciprocal.reciprocal (η.excludePrimes S hS) s *
    (globalClosedCorrection η S s 1 z*slotMultiplier η J T b s 1 z)*
    LFunction (fixedSourcePrincipal S hS) (6*z)

lemma residue_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s z : ℂ) :
    residueArithmetic η S hS J T b X Z s z*profile W0 W1 s 1 z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s 1 z *
        LFunction (fixedSourcePrincipal S hS) (6*z) := by
  unfold residueArithmetic profile continuedSourceMultiplier
  simp only [sub_self,Complex.cpow_zero,mul_one]
  ring

lemma residue_arithmetic_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (hβ : HeckeZeroSupremum.beta<a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) :
    Measurable (fun q : ℝ×ℝ => residueArithmetic η S hS J T b X Z
      ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) := by
  have hH := global_correction_measurable η S (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := slot_multiplier_measurable η J T b (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (reciprocal_vertical_continuous (η.excludePrimes S hS) a hβ).measurable.comp
    (by fun_prop : Measurable (fun q : ℝ×ℝ => q.1))
  have hL := (LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
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

def residueAmplitude {ι : Type*} (S : Finset Id) (J : Finset ι)
    (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Z a ξ C : ℝ) : ℝ :=
  X^(1/2-ξ)*Z^(a+ξ-1)*C*((3/2)*slotBound J T b a ξ)*
    (zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)

lemma residue_arithmetic_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Z a ξ C : ℝ) (hX : 0<X) (hZ : 0<Z) (ha : 7/8≤a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1)
    (hC : 0≤C) (hR : ∀s : ℂ,a≤s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤C*(1+|s.im|^2))
    (q : ℝ×ℝ) :
    ‖residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)‖≤
      residueAmplitude S J T b X Z a ξ C*jointHeight q.1 q.2 0^5 := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖≤C*height q.1^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg q.1]
  have hh := combined_slot_bound η S hS.tail J T b hT ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I) a ξ
    (by simpa using ha) (by norm_num) (by simpa using hξ)
  have hL := fixed_principal_z_bound (∏P∈S,P) ξ ξ q.2 ⟨hξ,le_rfl⟩ hξ1
  have hX0 := (Real.rpow_pos_of_pos hX (1/2-ξ)).le
  have hZ0 := (Real.rpow_pos_of_pos hZ (a+ξ-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (slotBound_nonneg J T b a ξ)
  have hA := div_nonneg (zBoxAmplitude_nonneg (∏P∈S,P) ξ) (abs_nonneg (6*ξ-1))
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
      gcongr <;> first | positivity | exact height_le_joint_s _ _ _ | exact height_le_joint_z _ _ _
    _ = _ := by unfold residueAmplitude; ring

lemma residueAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Z a ξ C : ℝ)
    (hX : 0≤X) (hZ : 0≤Z) (hC : 0≤C) : 0≤residueAmplitude S J T b X Z a ξ C := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hb := slotBound_nonneg J T b a ξ
  have hza := zBoxAmplitude_nonneg (∏P∈S,P) ξ
  unfold residueAmplitude
  positivity

theorem continued_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) 5 0
  have hm := residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hb := residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hh := (hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
    (residueAmplitude S J T b X Z a ξ C)
    (residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC)
    (fun q : ℝ×ℝ => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I))
    hm.aestronglyMeasurable hb).1
  apply hh.congr
  apply Eventually.of_forall
  intro q
  simpa only [sliceMap,onLines,ofReal_one,ofReal_zero,zero_mul,add_zero] using
    residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)

theorem residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  apply (continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1).congr
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  rw [continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem source_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ)
    (hcw : 1<cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w))) := by
  have hi := source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  simpa only [verticalIntegral,integral_const_mul,mul_assoc] using
    (hi.integral_prod_left.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))).const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem residue_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) 1 z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z))) := by
  have hi := residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  simpa only [verticalIntegral] using hi.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem source_ordered_outer {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (he : 0<e) :
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
    source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) cw cw hX hY hZ ha hβ (by linarith) hcw ⟨by linarith,le_rfl⟩
      (by linarith) (ne_of_gt hcw)
  have hB : Integrable (fun t : ℝ => B ((a:ℂ)+t*I)) :=
    source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) (19/20) cw hX hY hZ ha hβ (by linarith) hcw ⟨le_rfl,by linarith⟩
      (by linarith) (by norm_num)
  have hD : Integrable (fun t : ℝ => D ((a:ℂ)+t*I)) :=
    (residue_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (33/200) hX hZ ha hβ le_rfl (by norm_num)).const_mul R
  have hp : ∀ᵐt : ℝ,A ((a:ℂ)+t*I)=B ((a:ℂ)+t*I)+D ((a:ℂ)+t*I)+E ((a:ℂ)+t*I) :=
    source_ordered_ae η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
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

theorem source_initial_ordered {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
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
  simpa only [show (1/6+11/6:ℝ)=2 by norm_num] using
    source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z 3 (11/6) 3 hX hY hZ (by norm_num)
      (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num) (by norm_num)

theorem source_uniform_joint_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      6*ξ≠1→υ≠1→∀R : ℝ,0≤R→
      (∫p : HeightSpace in outsideBox R,
        ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
          (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
          LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| * K/(1+R)^N := by
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
  have hA : 0≤A := arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
    (abs_nonneg _) (abs_nonneg _)
  have hi := source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z σ ξ υ cw hX hY hZ (ha.trans hσ.1) (hβ.trans_le hσ.1) hξ.1 hcw hυ hξ1 hυ1
  have hmi := (hm σ hσ ξ hξ υ hυ).1
  have hbound := arithmetic_onLines_bound η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ hξ1 hυ1 hC hR
  have hdom : ∀ᵐp : HeightSpace ∂heightMeasure,
      ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
      A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖) := by
    filter_upwards [continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ] with p hp
    rw [←hp,←arithmetic_profile_eq_source]
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

lemma LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
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
  · exact LFunction_eq_pole_quotient χ hs0 hs1

lemma arithmetic_onLines_measurable_all {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : HeckeZeroSupremum.beta<a) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hH := global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => (υ:ℂ)+p.2*I))
  have hZL := (LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => 6*((ξ:ℂ)+p.1.2*I)))
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

def joinWGap (axis : SliceAxis) (υ : ℝ) : ℝ := if axis=.w then 1 else |υ-1|
def joinZGap (axis : SliceAxis) (ξ : ℝ) : ℝ := if axis=.z then 6 else |6*ξ-1|

lemma joinWGap_pos (axis : SliceAxis) (υ : ℝ) (hυ : axis≠.w→υ≠1) : 0<joinWGap axis υ := by
  unfold joinWGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hυ h))
lemma joinZGap_pos (axis : SliceAxis) (ξ : ℝ) (hξ : axis≠.z→6*ξ≠1) : 0<joinZGap axis ξ := by
  unfold joinZGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hξ h))

lemma slice_w_gap (axis : SliceAxis) (R υ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinWGap axis υ≤‖((υ:ℂ)+(sliceMap axis R q).2*I)-1‖ := by
  cases axis
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using hR.trans (pole_distance_horizontal 1 υ R)
lemma slice_z_gap (axis : SliceAxis) (R ξ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinZGap axis ξ≤‖6*((ξ:ℂ)+(sliceMap axis R q).1.2*I)-1‖ := by
  cases axis
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.1*I)-1)
  · have hi : 6*|R|≤‖6*((ξ:ℂ)+R*I)-1‖ := by
      simpa [abs_mul] using Complex.abs_im_le_norm (6*((ξ:ℂ)+R*I)-1)
    simpa [joinZGap,sliceMap] using (by linarith : (6:ℝ)≤6*|R|).trans hi
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.2*I)-1)

theorem source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR0
  have hm := arithmetic_onLines_measurable_all η S hS.prime J T b X Y Z σ ξ υ hX hY hZ (hβ.trans_le hσ.1)
  have hb (q : ℝ×ℝ) := arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C
    hX hY hZ ha hσ hξ hcw hυ (joinWGap axis υ) (joinZGap axis ξ)
    (joinWGap_pos axis υ hυ1) (joinZGap_pos axis ξ hξ1) hC hR (sliceMap axis R q)
    (slice_w_gap axis R υ hR0 q) (slice_z_gap axis R ξ hR0 q)
  have hh := hk σ hσ ξ hξ υ hυ axis R
    (arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ))
    (arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
      (joinWGap_pos axis υ hυ1).le (joinZGap_pos axis ξ hξ1).le)
    (fun q : ℝ×ℝ => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((σ:ℂ)+(sliceMap axis R q).1.1*I) ((υ:ℂ)+(sliceMap axis R q).2*I)
      ((ξ:ℂ)+(sliceMap axis R q).1.2*I))
    (hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable hb
  simpa only [onLines,arithmetic_profile_eq_source] using hh

theorem residue_uniform_moments {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Z→
      ∃C : ℝ,0≤C ∧
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤residueAmplitude S J T b X Z a ξ C*K := by
  obtain ⟨K,hK,hk⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) (5+N) 0
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  let A := residueAmplitude S J T b X Z a ξ C
  have hA : 0≤A := residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC
  let F : ℝ×ℝ → ℂ := fun q => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) *
    onLines W0 W1 a ξ 1 (sliceMap .w 0 q)
  have hm := residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hFc : AEStronglyMeasurable F (volume.prod volume) := hm.aestronglyMeasurable.mul
    (((onLines_continuous W0 W1 a1 b1 ha1 hW1 a ξ 1 (by linarith)).comp
      (sliceMap_continuous .w 0)).aestronglyMeasurable)
  have hb := residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
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
  have hn : (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤A*K := by
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
    rw [residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z,
      continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
  have hweight : (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)=ᵐ[volume.prod volume]
      (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N) := Eventually.of_forall (fun _ => rfl)
  have heqw := hweight.mul (heq.fun_comp (fun z : ℂ => ‖z‖))
  exact ⟨hi.congr heqw, (integral_congr_ae heqw).symm.trans_le hn⟩

def residueOutside (R : ℝ) : Set (ℝ×ℝ) := {q | R < |q.1| ∨ R < |q.2|}
lemma residueOutside_measurable (R : ℝ) : MeasurableSet (residueOutside R) := by
  unfold residueOutside
  measurability

theorem residue_uniform_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Z→
      ∃C : ℝ,0≤C ∧ ∀R : ℝ,0≤R→
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤
        residueAmplitude S J T b X Z a ξ C*K/(1+R)^N := by
  obtain ⟨K,hK,hk⟩ := residue_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hi,hb⟩ := hk η S hS J T b hT X Y Z hX hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  let F := fun q : ℝ×ℝ =>
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
      (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
  have hF := residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  have hdom (q : ℝ×ℝ) (hq : q∈residueOutside R) :
      ‖F q‖≤jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N := by
    have hh : 1+R≤jointHeight q.1 q.2 0 := by
      rcases hq with h|h <;> unfold jointHeight <;> simp only [abs_zero,add_zero] <;>
        linarith [abs_nonneg q.1,abs_nonneg q.2]
    have hp := pow_le_pow_left₀ (by linarith : 0≤1+R) hh N
    apply (le_div_iff₀ (pow_pos (by linarith : 0<1+R) N)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (norm_nonneg (F q))
  change (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤_
  calc
    _ ≤ ∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N
        ∂volume.prod volume := setIntegral_mono_on hF.norm.integrableOn (hi.div_const _).integrableOn
          (residueOutside_measurable R) hdom
    _ = (∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := integral_div _ _
    _ ≤ (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact setIntegral_le_integral hi (Eventually.of_forall (fun q =>
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

lemma continued_high_slice_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ ξ υ : ℝ)
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
  rw [continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma source_axis_gaps {e : ℝ} (he : 0<e) :
    |(19/20:ℝ)-1|=1/20 ∧ |6*(1/6+e)-1|=6*e ∧ |6*(33/200:ℝ)-1|=1/100 := by
  constructor
  · norm_num
  constructor
  · rw [show 6*(1/6+e)-1=6*e by ring,abs_of_pos (by positivity)]
  · norm_num

theorem raw_source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hcw : 1<cw) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((σ:ℂ)+p.1.1*I) (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I))
        (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  obtain ⟨K,hK,hk⟩ := source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs Bz cw ha hβ hcw N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have hh := hc σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have heq := continued_high_slice_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ axis R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

end SevenEighths.ProbePrincipalContours
end

end OAI
end OAIOriginalModule2477

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalInput
Source SHA256: 9e0b2065602d1db2574b5e5aa2a6c50e7096d44f04870994c9604a9f2b09834b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2478



namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeMellinBoundary
open PrincipalMellinResidues ProbeFiniteProductBounds
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma principalTuple_source_integrand {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    sourceMellinWeight W0 W1 X Y Z x w z*
      (∏i,(elementNorm (primaryGenerator (P i).val):ℂ)^(z-1))*
      indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η Finset.univ (fun i=>{P i}) (fun _ _=>1) x) w z*
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w := by
  have hnorm (i : Fin K) : (elementNorm (primaryGenerator (P i).val):ℂ)=(Ideal.absNorm (P i).val:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  rw [indexedCompensatedHigh_principal_continued η S hS P hP hPS x w z hx hw hz]
  unfold sourceMultiplier sourceMellinWeight
  simp only [hnorm,slotMultiplier,Finset.sum_singleton,one_mul,localMultiplier,
    Complex.ofReal_natCast,Finset.prod_mul_distrib]
  ring

theorem principalRowIntegral_eq_sourceMultiplier {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    principalRowIntegral η S (fun i=>primaryGenerator (P i).val) W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((3:ℂ)+t.1.1*Complex.I)
          (globalClosedCorrection η S ((3:ℂ)+t.1.1*Complex.I))
          (slotMultiplier η Finset.univ (fun i=>{P i}) (fun _ _=>1) ((3:ℂ)+t.1.1*Complex.I))
          ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*((2:ℂ)+t.1.2*Complex.I))*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+t.2*Complex.I) ∂heightMeasure := by
  unfold principalRowIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  exact principalTuple_source_integrand η S hS P hP hPS W0 W1 X Y Z
    ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2478

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalTransport
Source SHA256: 99dd35d116ce437bcb9fcb40abd411240684b570c6eb8a88ebd594f60df65870
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2479



namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalTransport
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma gaussianMoment_tendsto (n : ℕ) : Tendsto (gaussianMoment n) atTop (𝓝 0) := by
  have hb (t : ℝ) : gaussianMoment n t ≤ (2:ℝ)^(n-1)*Continuation.polynomialGaussian n t := by
    have h := add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg t) n
    unfold gaussianMoment height Continuation.polynomialGaussian
    calc
      _ ≤ ((2:ℝ)^(n-1)*(1^n+|t|^n))*Real.exp (-(t^2)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by simp only [one_pow]; ring
  exact squeeze_zero (gaussianMoment_nonneg n) hb
    (by simpa using (Continuation.polynomialGaussian_tendsto n).const_mul ((2:ℝ)^(n-1)))

lemma gaussianMoment_even (n : ℕ) (t : ℝ) : gaussianMoment n (-t)=gaussianMoment n t := by
  simp [gaussianMoment,height]

lemma gaussianMoment_tendsto_bot (n : ℕ) : Tendsto (gaussianMoment n) atBot (𝓝 0) := by
  have h := (gaussianMoment_tendsto n).comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def,gaussianMoment_even] using h

lemma shifted_gaussian_integrable (n : ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => gaussianMoment n (t+v)) := by
  exact (measurePreserving_add_right volume v).integrable_comp_of_integrable (gaussianMoment_integrable n)

lemma shifted_gaussian_top (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (t+v)) atTop (𝓝 0) :=
  (gaussianMoment_tendsto n).comp (tendsto_atTop_add_const_right _ v tendsto_id)

lemma shifted_gaussian_bottom (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (-t+v)) atTop (𝓝 0) :=
by
  convert shifted_gaussian_top n (-v) using 1
  funext t
  rw [←gaussianMoment_even n (t + -v)]
  congr 1
  ring

theorem verticalIntegral_eq_of_shifted_gaussian (F : ℂ → ℂ) {a c A : ℝ}
    (n : ℕ) (v : ℝ) (hac : a≤c)
    (hF : DifferentiableOn ℂ F {s : ℂ | a≤s.re ∧ s.re≤c})
    (hb : ∀σ∈Icc a c,∀t : ℝ,‖F ((σ:ℂ)+t*I)‖≤A*gaussianMoment n (t+v)) :
    verticalIntegral a F=verticalIntegral c F := by
  have hc (σ : ℝ) (hσ : σ∈Icc a c) : Continuous (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    hF.continuousOn.comp_continuous (by fun_prop) (by intro t; simpa using hσ)
  have hi (σ : ℝ) (hσ : σ∈Icc a c) : Integrable (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    ((shifted_gaussian_integrable n v).const_mul A).mono' (hc σ hσ).aestronglyMeasurable
      (Eventually.of_forall (hb σ hσ))
  have hj (T : ℝ) : ‖∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)‖≤A*gaussianMoment n (T+v)*|c-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    exact hb σ (by simpa [uIcc_of_le hac] using uIoc_subset_uIcc hσ) T
  have ht : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hj
      (by simpa using ((shifted_gaussian_top n v).const_mul A).mul_const |c-a|)
  have hbot : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+(-T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun T => by simpa only [Complex.ofReal_neg] using hj (-T))
      (by simpa using ((shifted_gaussian_bottom n v).const_mul A).mul_const |c-a|)
  unfold verticalIntegral
  congr 1
  exact Continuation.vertical_integral_eq_of_horizontal_vanish F hac hF
    (hi a ⟨le_rfl,hac⟩) (hi c ⟨hac,le_rfl⟩) hbot ht

theorem principal_box_majorant {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξlo : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξlo : 1/6<ξlo) :
    ∃ A : ℝ,0≤A ∧ ∀σ∈Icc a 3,∀ξ∈Icc ξlo 2,∀p : HeightSpace,
      ‖continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2*I)‖≤A*jointEnvelope 8 p := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hd⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 ξlo 2
    (by linarith) 10
  obtain ⟨E,hE,he⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) 3 3 10
  let A := arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
  let B := realGaussianBound a 3 ξlo 2*2^8*D*E
  have hA : 0≤A := arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
    (by norm_num) hC (by norm_num) (by linarith)
  have hB : 0≤B := by dsimp [B]; have := (realGaussianBound_pos a 3 ξlo 2).le; positivity
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
  have hb := arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a 3 2 3 σ ξ 3 C
    hX hY hZ ha hσ hξ' (by norm_num) (by norm_num) 2 (6*ξlo-1)
    (by norm_num) (by linarith) hC hR p hw hz
  have hp := profile_moment_majorant W0 W1 8 hσ hξ hD.le hE.le (hd ξ hξ)
    (he 3 ⟨le_rfl,le_rfl⟩) p
  rw [←arithmetic_profile_eq_source,norm_mul]
  calc
    _ ≤ (A*jointHeight p.1.1 p.1.2 p.2^8)*‖profile W0 W1
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ 3 p‖) := by
      simp only [onLines,ofReal_ofNat]; ring
    _ ≤ A*(B*jointEnvelope 8 p) := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem continued_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 1/6<ξ) (hξ2 : ξ≤2) (v u : ℝ) :
    verticalIntegral a (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 3 (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha.le hβ hξ
  have hh := continued_source_differentiable_strip η S hS J T b hT W0 W1 X Y Z hZ
    ((3:ℂ)+u*I) ((ξ:ℂ)+v*I) (by norm_num) (by simpa using (show (4/25:ℝ)≤ξ by linarith)) ha hβ
    (c:=3)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 v ha3
    ((hh.mul_const _).mul_const _) (A:=A*cauchy v*cauchy u)
  intro σ hσ t
  have h := hb σ hσ ξ ⟨le_rfl,hξ2⟩ ((t,v),u)
  simpa only [jointEnvelope,Prod.fst,Prod.snd,mul_assoc,mul_left_comm,mul_comm] using h

lemma continued_source_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : 7/8≤s.re) (hw : 9/10≤w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)
      {z : ℂ | 4/25<z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25<z.re} := (ProbeRadialMellin.radial_mellin_differentiable W0).mono
        (by intro z hz; change 0<z.re; change (4/25:ℝ)<z.re at hz; linarith)
  have hH := (combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
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

lemma continued_principal_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s w : ℂ) (hs : 7/8≤s.re) (hw : 9/10≤w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w)
      {z : ℂ | 1/6<z.re} := by
  have hK := continued_source_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s w hs hw
  apply ((hK.mono (by intro z hz; change (4/25:ℝ)<z.re; change (1/6:ℝ)<z.re at hz; linarith)).mul ?_).mul_const
  intro z hz
  have h0 : (6*z:ℂ)≠0 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)<z.re at hz; linarith
  have h1 : (6*z:ℂ)≠1 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)<z.re at hz; linarith
  exact ((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) h0 (Or.inl h1)).comp z
    (differentiableAt_id.const_mul 6)).differentiableWithinAt

theorem continued_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξ : 1/6<ξ) (hξ2 : ξ≤2) (t u : ℝ) :
    verticalIntegral ξ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 2 (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  obtain ⟨A,hA,hb⟩ := principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha hβ hξ
  have hh := continued_principal_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
    ((a:ℂ)+t*I) ((3:ℂ)+u*I) (by simpa using ha) (by norm_num)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 t hξ2
    (hh.mono (by intro z hz; change (1/6:ℝ)<z.re; exact hξ.trans_le hz.1)) (A:=A*cauchy u)
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

lemma verticalIntegral_swap (F : ℂ → ℂ → ℂ) (a b : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ => F ((a:ℂ)+q.1*I) ((b:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun z => verticalIntegral b (F z))=
      verticalIntegral b (fun w => verticalIntegral a (fun z => F z w)) := by
  simp only [verticalIntegral,integral_const_mul]
  congr 2
  exact integral_integral_swap (f:=fun t u : ℝ => F ((a:ℂ)+t*I) ((b:ℂ)+u*I)) hi

lemma verticalIntegral_triple_reverse (F : ℂ → ℂ → ℂ → ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace => F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w => F s w z)))=
      verticalIntegral υ (fun w => verticalIntegral ξ (fun z => verticalIntegral a (fun s => F s w z))) := by
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

lemma verticalIntegral_congr_line (F G : ℂ → ℂ) (a : ℝ)
    (h : ∀t : ℝ,F ((a:ℂ)+t*I)=G ((a:ℂ)+t*I)) : verticalIntegral a F=verticalIntegral a G := by
  unfold verticalIntegral
  congr 1
  exact integral_congr_ae (Eventually.of_forall h)

theorem continued_triple_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (hξ : 1/6<ξ) (hξ2 : ξ≤2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral 3 (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  have hiA := continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha.le hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  have hi3 := continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 ξ 3 3 hX hY hZ (by norm_num) (hβ.trans_le ha3) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  rw [verticalIntegral_triple_reverse F a ξ 3 hiA,verticalIntegral_triple_reverse F 3 ξ 3 hi3]
  apply verticalIntegral_congr_line
  intro u
  apply verticalIntegral_congr_line
  intro v
  exact continued_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 v u

theorem continued_triple_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (hξ : 1/6<ξ) (hξ2 : ξ≤2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral a (fun s => verticalIntegral 2 (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  obtain ⟨Cξ,Kξ,hCξ,hKξ,hξi⟩ := continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  obtain ⟨C2,K2,hC2,hK2,h2i⟩ := continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 3 3 hX hY hZ ha hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  apply verticalIntegral_congr_line
  intro t
  have hiξ := (hξi .s t).1
  have hi2 := (h2i .s t).1
  rw [verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) ξ 3 hiξ,
    verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) 2 3 hi2]
  apply verticalIntegral_congr_line
  intro u
  exact continued_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 t u

lemma continued_triple_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w)))=
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w))) := by
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  have h0 : (a:ℂ)+t*I≠0 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+t*I≠1 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  simp_rw [continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem source_initial_placement {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
  dsimp only
  rw [←continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z 3 2 3,
    ←continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z a (1/6+e) 3]
  have hx := continued_triple_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 hX hY hZ ha ha3 hβ (by norm_num) le_rfl
  have hz := continued_triple_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a (1/6+e) hX hY hZ ha.le ha3 hβ (by linarith) (by linarith)
  exact hx.symm.trans hz.symm

theorem source_initial_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
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
  exact (source_initial_placement η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2).trans
    (source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e 3 hX hY hZ ha.le hβ (by norm_num) he)

lemma continued_principal_measurable (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    {ι : Type*} (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (x w z : ℝ×(ℝ×ℝ) → ℂ) (hx : Continuous x) (hw : Continuous w) (hz : Continuous z)
    (hβ : ∀p,HeckeZeroSupremum.beta<(x p).re) (hz0 : ∀p,0<(z p).re) :
    Measurable (fun p => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z (x p) (w p) (z p)*
      LFunction (fixedSourcePrincipal S hS) (6*z p)*LFunction (fixedSourcePrincipal S hS) (w p)) := by
  have hH := global_correction_measurable η S x w z hx.measurable hw.measurable hz.measurable
  have hB := slot_multiplier_measurable η J T b x w z hx.measurable hw.measurable hz.measurable
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
  have hL6 := (LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p => 6*z p))
  have hLw := (LFunction_measurable (fixedSourcePrincipal S hS)).comp hw.measurable
  have hm0 := hM0.measurable
  have hm1 := hM1.measurable
  have hmr := hR.measurable
  have hmx := hx.measurable
  have hmw := hw.measurable
  have hmz := hz.measurable
  unfold continuedSourceMultiplier
  fun_prop (disch := aesop)

lemma strip_integrable_of_uniform_slices (F : ℝ×(ℝ×ℝ) → ℂ) (l r D : ℝ)
    (hlr : l≤r) (hm : AEStronglyMeasurable F ((volume.restrict (Icc l r)).prod (volume.prod volume)))
    (hs : ∀σ∈Icc l r,Integrable (fun q => F (σ,q)) (volume.prod volume))
    (hb : ∀σ∈Icc l r,(∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume)≤D) :
    Integrable F ((volume.restrict (Icc l r)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc l r)).prod (volume.prod volume))≤(r-l)*D := by
  have hm' := hm.norm.integral_prod_right'
  have hb' : ∀ᵐσ : ℝ ∂volume.restrict (Icc l r),
      ‖∫q : ℝ×ℝ,‖F (σ,q)‖ ∂volume.prod volume‖≤D := by
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

theorem uniform_high_x_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξlo : 1/6<ξlo) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀ξ∈Icc ξlo 2,∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((p.1:ℂ)+R*I) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc a 3)).prod (volume.prod volume))≤
      (3-a)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
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
  have hcut := continued_principal_measurable η S hS.prime J T b W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
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
  exact strip_integrable_of_uniform_slices F a 3 _ ha3 hm hs hb

theorem uniform_high_z_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξlo : 1/6<ξlo) (hξ2 : ξlo≤2) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((a:ℂ)+p.2.1*I) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume))≤
      (2-ξlo)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
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
  have hcut := continued_principal_measurable η S hS.prime J T b W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
    (fun p : ℝ×(ℝ×ℝ) => (a:ℂ)+p.2.1*I)
    (fun p : ℝ×(ℝ×ℝ) => (3:ℂ)+p.2.2*I)
    (fun p : ℝ×(ℝ×ℝ) => ((max ξlo p.1:ℝ):ℂ)+R*I) (by fun_prop) (by fun_prop) (by fun_prop)
    (by intro p; simpa using hβ)
    (by intro p; simpa using (show (0:ℝ)<max ξlo p.1 by linarith [le_max_left ξlo p.1]))
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
  exact strip_integrable_of_uniform_slices F ξlo 2 _ hξ2 hm hs hb

lemma high_x_join_ae_raw {ι : Type*} (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
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
  apply Eventually.of_forall
  intro p
  have h0 : (p.1:ℂ)+R*I≠0 := by intro h; exact hR (by simpa using congrArg Complex.im h)
  have h1 : (p.1:ℂ)+R*I≠1 := by intro h; exact hR (by simpa using congrArg Complex.im h)
  dsimp only
  rw [continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma high_z_join_ae_raw {ι : Type*} (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
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
  have hh : ∀ᵐp : ℝ×(ℝ×ℝ) ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume),p.2.1≠0 :=
    Measure.quasiMeasurePreserving_snd.ae
      (Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ)))
  filter_upwards [hh] with p hp
  have h0 : (a:ℂ)+p.2.1*I≠0 := by intro h; exact hp (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+p.2.1*I≠1 := by intro h; exact hp (by simpa using congrArg Complex.im h)
  rw [continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem raw_uniform_high_x_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξlo : 1/6<ξlo) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀ξ∈Icc ξlo 2,∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((p.1:ℂ)+R*I)
        (globalClosedCorrection η S ((p.1:ℂ)+R*I)) (slotMultiplier η J T b ((p.1:ℂ)+R*I)) ((3:ℂ)+p.2.2*I) ((ξ:ℂ)+p.2.1*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.2.1*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc a 3)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc a 3)).prod (volume.prod volume))≤
      (3-a)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 |6*ξ-1| *K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := uniform_high_x_joins W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξlo ha ha3 hβ hξlo N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro ξ hξ R hR
  have hh := hc ξ hξ R hR
  have heq := high_x_join_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

theorem raw_uniform_high_z_joins {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξlo : ℝ) (ha : 7/8≤a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a)
    (hξlo : 1/6<ξlo) (hξ2 : ξlo≤2) (N : ℕ) :
    ∃ K : ℝ,0<K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
      ∃C : ℝ,0≤C ∧ ∀R : ℝ,1≤|R|→
      let F := fun p : ℝ×(ℝ×ℝ) => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.2.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.2.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.2.1*I)) ((3:ℂ)+p.2.2*I) ((p.1:ℂ)+R*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((p.1:ℂ)+R*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2.2*I)
      Integrable F ((volume.restrict (Icc ξlo 2)).prod (volume.prod volume)) ∧
      (∫p : ℝ×(ℝ×ℝ),‖F p‖ ∂(volume.restrict (Icc ξlo 2)).prod (volume.prod volume))≤
      (2-ξlo)*(arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 6*K/height R^N) := by
  obtain ⟨K,hK,hk⟩ := uniform_high_z_joins W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a ξlo ha ha3 hβ hξlo hξ2 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := hc R hR
  have heq := high_z_join_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξlo R
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

theorem source_initial_joint_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
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
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  have hh := source_initial_ordered_at_a η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2
  have hf := (source_joint_fubini η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 2 3 3 hX hY hZ (by norm_num) (hβ.trans_le ha3) (by norm_num)
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

end SevenEighths.ProbePrincipalTransport
end

end OAI
end OAIOriginalModule2479

/-! Original module: OAI.NumberTheory.DirichletL.PrincipalSignalComparison
Source SHA256: 3609a84d40122a6137bfa44fcb41f2830046e3456b77d72c34eb83f5c29b0e7b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2480







namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace SevenEighths.PrincipalSignalComparison
open HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

theorem raw_inverse_ae_reciprocal (χ : Character) (a : ℝ) :
    (fun t : ℝ => (LFunction χ ((a : ℂ)+t*I))⁻¹) =ᵐ[volume]
      (fun t => HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I)) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
  apply (HeckeReciprocal.reciprocal_eq_inv χ ?_ ?_).symm
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem raw_quotient_integral_eq (χ : Character) (a : ℝ) (F : ℝ → ℂ) :
    (∫ t : ℝ, F t / LFunction χ ((a : ℂ)+t*I)) =
      ∫ t : ℝ, F t * HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I) := by
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  simp only [div_eq_mul_inv, ht]

variable {κ ι : Type*}

def slotMass (T : κ → Finset ι) (w : κ → ι → ℝ) (j : κ) : ℝ := ∑ p ∈ T j, w j p

def slotProduct (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) : ℂ :=
  ∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s

def slotRatio (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) : ℂ :=
  slotProduct S T w Q A η s / PrincipalSlotEstimate.principalScalar S (slotMass T w)

structure SlotBounds (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (P : ℝ) : Prop where
  lower : 480 ≤ P
  small : 1440 * P ^ (-(7/8 : ℝ)) ≤ 1
  weight_nonneg : ∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p
  norm_lower : ∀ j ∈ S, ∀ p ∈ T j, P ≤ Q j p
  phase_bound : ∀ j ∈ S, ∀ p ∈ T j, ‖A j p‖ ≤ 1
  target_unit : ∀ j ∈ S, ∀ p ∈ T j, ‖η j p‖ = 1
  mass_pos : ∀ j ∈ S, 0 < slotMass T w j

def slotErrorConstant (S : Finset κ) : ℝ := S.card * 2 ^ S.card * 1440

theorem slot_scalar_ne_zero (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P) :
    PrincipalSlotEstimate.principalScalar S (slotMass T w) ≠ 0 :=
  PrincipalSlotEstimate.principalScalar_ne_zero S _ h.mass_pos

theorem slotRatio_error (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P)
    {s : ℂ} (hs : 7/8 ≤ s.re) :
    ‖slotRatio S T w Q A η s - 1‖ ≤ slotErrorConstant S * P ^ (-(7/8 : ℝ)) := by
  change ‖(∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s) /
    PrincipalSlotEstimate.principalScalar S (fun j => ∑ p ∈ T j, w j p) - 1‖ ≤ _
  simpa only [slotErrorConstant, mul_assoc] using
    weighted_principal_product_error_linear S T w Q A η s P h.lower hs h.small
      h.weight_nonneg h.norm_lower h.phase_bound h.target_unit h.mass_pos

theorem slotRatio_bound (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P)
    {s : ℂ} (hs : 7/8 ≤ s.re) :
    ‖slotRatio S T w Q A η s‖ ≤ 1 + slotErrorConstant S * P ^ (-(7/8 : ℝ)) := by
  have hn := norm_add_le (slotRatio S T w Q A η s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith [slotRatio_error S T w Q A η h hs]

theorem principalSlot_differentiableAt {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7/8 ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQnz : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  have hQslit : (Q : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hQ0
  have hg := principal_geometric_bounds hQ hη hs
  have hV := one_sub_ne_zero_of_norm_le_half _ hg.1
  have hD := one_sub_ne_zero_of_norm_le_half _ hg.2.2
  have hR : 1-coordR Q A s (1/6) ≠ 0 := by
    apply one_sub_ne_zero_of_norm_le_half
    apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
    apply rpow_le_half Q _ hQ4
    norm_num
    linarith
  have hr := coordR_differentiable Q hQ0 A (1/6)
  have hd := coordD_differentiable Q hQ0 η 1
  have hk := coordK_differentiable Q hQ0 η 1
  have hp : DifferentiableAt ℂ (principalMarked Q A η) s := by
    unfold principalMarked markedFactor
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  have hb : Differentiable ℂ (fun s : ℂ => star η * (Q : ℂ)^s) :=
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hQ0.ne'))).const_mul _
  have hrep : DifferentiableAt ℂ (principalReplacement Q A η) s := by
    unfold principalReplacement compensatedReplacement
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  exact hrep.div (unramifiedClosed_differentiableAt Q hQ0 A η 1 s 1 (1/6) hR hV hD)
    (principal_correction_ne_zero hQ hA hη hs)

theorem slotRatio_continuous_line (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : SlotBounds S T w Q A η P) {a : ℝ} (ha : 7/8 ≤ a) :
    Continuous (fun t : ℝ => slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  have hc (j : κ) (hj : j ∈ S) (p : ι) (hp : p ∈ T j) :
      Continuous (fun t : ℝ => principalSlot (Q j p) (A j p) (η j p) ((a : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (principalSlot_differentiableAt (h.lower.trans (h.norm_lower j hj p hp))
      (h.phase_bound j hj p hp) (h.target_unit j hj p hp).le
      (by simpa using ha)).continuousAt.comp (by fun_prop)
  unfold slotRatio slotProduct
  apply Continuous.div_const
  apply continuous_finsetProd
  intro j hj
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (hc j hj p hp)

def slotResidue (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) : ℂ :=
  (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
    (Z : ℂ)^(((a : ℂ)+t*I)-11/16) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
      H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I)

theorem slotResidue_eq_reciprocal (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H a Z S T w Q A η = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) (-11/16) Z ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I) := by
  unfold slotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

def kernel (χ : Character) (H : ℂ → ℂ) (a Z : ℝ) (t : ℝ) : ℂ :=
  gaussianContourIntegrand (quotient χ H) (-11/16) Z ((a : ℂ)+t*I)

def kernelEnvelope (a C Z : ℝ) : ℝ :=
  Z^(a-11/16) * Real.exp ((a-5/6)^2) * ((3/2)*C)

theorem kernel_continuous (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    {a Z : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (kernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (HeckeSignalShift.quotient_holomorphic χ H hH ha hβ) (-11/16) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem kernel_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖kernel χ H a Z t‖ ≤ kernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := HeckeSignalShift.quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+(-11/16))*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold kernelEnvelope polynomialGaussian; ring_nf

theorem kernel_integrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (kernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (kernelEnvelope a C Z)).mono'
    (kernel_continuous χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (kernel_norm_bound χ H hb ha ha2 hC hZ hR))

theorem slotResidue_bound_of_reciprocal_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : SlotBounds S T w Q A η P) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
      ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
        (HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a-11/16) * P^(-(7/8 : ℝ)) := by
  have hZ0 : 0 < Z := by linarith
  have hP0 : 0 < P := by linarith [h.lower]
  have hg := kernel_integrable χ H hH hb ha ha2 hβ hC hZ0 hR
  have hc := slotRatio_continuous_line S T w Q A η h ha.le
  have hbound (t : ℝ) := slotRatio_bound S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have herror (t : ℝ) := slotRatio_error S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have heint := hg.mul_bdd (hc.sub continuous_const).aestronglyMeasurable (ae_of_all _ herror)
  have heq : slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I) - 1) := by
    rw [slotResidue_eq_reciprocal,
      HeckeSignalBounds.contour_shift_left χ H hH hb (-11/16) a ha ha2 hβ hZ,
      ← mul_sub]
    change (1/(2*Real.pi) : ℂ) *
      ((∫ t : ℝ, kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) -
        ∫ t : ℝ, kernel χ H a Z t) = _
    rw [← integral_sub hint hg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    change kernel χ H a Z t * _ - kernel χ H a Z t = _
    ring_nf
  rw [heq, norm_mul]
  have he0 : 0 ≤ slotErrorConstant S * P^(-(7/8 : ℝ)) := by
    unfold slotErrorConstant
    positivity
  have hbnd (t : ℝ) :
      ‖kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I)-1)‖ ≤
        (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(7/8 : ℝ)))) *
          polynomialGaussian 2 t := by
    rw [norm_mul]
    calc
      _ ≤ (kernelEnvelope a C Z * polynomialGaussian 2 t) *
          (slotErrorConstant S * P^(-(7/8 : ℝ))) :=
        mul_le_mul (kernel_norm_bound χ H hb ha ha2 hC hZ0 hR t) (herror t)
          (norm_nonneg _) (mul_nonneg (by unfold kernelEnvelope; positivity)
            (polynomialGaussian_nonneg 2 t))
      _ = _ := by ring_nf
  have hn := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable 2).const_mul
      (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(7/8 : ℝ)))))
    (ae_of_all _ hbnd)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  convert hm using 1
  unfold kernelEnvelope HeckeSignalShift.infinityConstant
  ring_nf

theorem exists_slotResidue_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset ι) (w Q : κ → ι → ℝ)
      (A η : κ → ι → ℂ) (P Z : ℝ), SlotBounds S T w Q A η P → 1 ≤ Z →
      Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
        ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
          D * Z^(a-11/16) * P^(-(7/8 : ℝ)) := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  refine ⟨HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  · intro T w Q A η P Z h hZ
    exact slotResidue_bound_of_reciprocal_bound χ H hH hb ha ha2 hβ hC hR S T w Q A η h hZ

theorem raw_slot_integrable (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)-11/16) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
        H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
          slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  apply hi.congr
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  unfold kernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf

private instance : IsPrincipalIdealRing HeckeFamily.O := IsCyclotomicExtension.Rat.three_pid K

theorem idealCoeff_norm_one_of_coprime (χ : Character) (J : Ideal HeckeFamily.O)
    (hJ : J ≠ ⊥) (hc : IsCoprime J χ.modulus) : ‖idealCoeff χ J‖ = 1 := by
  let := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ χ.modulus) := Fintype.ofFinite _
  have hu : IsUnit (Ideal.Quotient.mk χ.modulus (Submodule.IsPrincipal.generator J)) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime χ.modulus _).mpr (by
      simpa only [Ideal.span_singleton_generator] using hc)
  obtain ⟨u, hu⟩ := hu
  change ‖IdealCharacter.value χ.modulus χ.residue J‖ = 1
  rw [IdealCharacter.value, ite_eq_right hJ, ← hu]
  exact FiniteRayExpansion.norm_char_unit χ.residue u

open ProbePhysical ActualEisensteinCubic CompletedGauss

theorem prime_coprime_of_norm_gt (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val) : IsCoprime P.val η.modulus := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  rw [Ideal.isCoprime_iff_codisjoint,
    ← (Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint]
  intro hle
  have hn : 0 < Ideal.absNorm η.modulus := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  exact (Nat.not_le_of_gt hN) (Nat.le_of_dvd hn (Ideal.absNorm_dvd_absNorm_of_le hle))

def annularPrimeWeight (W : ℝ → ℝ) (scale : ℝ) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : ℝ :=
  W ((Ideal.absNorm P.val : ℝ)/scale) * (Ideal.absNorm P.val : ℝ)^(-(5/6 : ℝ))

theorem annularPrimeWeight_nonneg (W : ℝ → ℝ) (hW : ∀ x, 0 ≤ W x)
    (scale : ℝ) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : 0 ≤ annularPrimeWeight W scale P :=
  mul_nonneg (hW _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem annularPrimeWeight_norm_lower (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : c*scale ≤ (Ideal.absNorm P.val : ℝ) :=
  (le_div_iff₀ hscale).mp (hW _ (left_ne_zero_of_mul hw))

theorem annularPrimeWeight_target_unit (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (η : Character)
    (hthreshold : (Ideal.absNorm η.modulus : ℝ) < c*scale) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : ‖idealCoeff η P.val‖ = 1 := by
  have hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val := by
    exact_mod_cast hthreshold.trans_le (annularPrimeWeight_norm_lower W c scale hscale hW P hw)
  exact idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero (prime_coprime_of_norm_gt η P hN)

def sourceCorrection (η : Character) (E : Finset (Ideal HeckeFamily.O)) (s : ℂ) : ℂ :=
  globalClosedCorrection η E s 1 (1/6)

theorem sourceCorrection_eq_principal (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) : sourceCorrection η E = principalCorrection η E := by
  funext s
  exact source_globalCorrection_principal E hE η s

theorem sourceCorrection_differentiable (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) :
    DifferentiableOn ℂ (sourceCorrection η E) {s : ℂ | 7/8 < s.re} :=
  (globalClosedCorrection_analytic_x η E hE.tail 1 (1/6) (by norm_num) (by norm_num)).differentiableOn

theorem sourceCorrection_bound (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (s : ℂ) (hs : 7/8 < s.re) :
    ‖sourceCorrection η E s - 1‖ ≤ 1/2 :=
  globalClosedCorrection_bound η E hE.tail s 1 (1/6) hs.le (by norm_num) (by norm_num)

def actualSlotResidue (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (a Z : ℝ) (S : Finset κ)
    (T : κ → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (w : κ → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ) : ℂ :=
  slotResidue (η.excludePrimes E hE.prime) (sourceCorrection η E) a Z S T w
    (fun _ P => Ideal.absNorm P.val)
    (fun _ P => actualAPhase η (primaryGenerator P.val)) (fun _ P => idealCoeff η P.val)

theorem actual_principal_slot (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (s : ℂ) :
    compensatedReplacement (coordV (Ideal.absNorm P.val) (1/6))
      (coordW (Ideal.absNorm P.val) 1 1) (coordD (Ideal.absNorm P.val) (idealCoeff η P.val) 1 s)
      (idealMarkedClosed η P s 1 (1/6))
      (star (idealCoeff η P.val) * (Ideal.absNorm P.val : ℂ)^s)
      ((Ideal.absNorm P.val : ℂ)^(-1 : ℂ)) / idealClosedCorrection η P s 1 (1/6) =
      principalSlot (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
        (idealCoeff η P.val) s := rfl

theorem exists_actualSlotResidue_bound (η : Character) (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) {a : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (w : κ → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ) (P Z : ℝ),
      480 ≤ P → 1440 * P^(-(7/8 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      ‖actualSlotResidue η E hE a Z S T w -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D * Z^(a-11/16) * P^(-(7/8 : ℝ)) := by
  obtain ⟨D, hD, hb⟩ := exists_slotResidue_bound (ι := _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (sourceCorrection_differentiable η E hE) (sourceCorrection_bound η E hE)
    ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro T w P Z hP hsmall hw hnorm hcop hmass hZ
  exact (hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z
    ⟨hP, hsmall, hw, hnorm, fun j hj p hp => actualAPhase_norm_le_one η _,
      fun j hj p hp => idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp),
      hmass⟩ hZ).2

open PrincipalMellinResidues

theorem source_normalizer_cast (S : Finset κ) (T : κ → Finset ι) (w : κ → ι → ℝ)
    {Z ℓ : ℝ} (hZ : 0 < Z) :
    (Probe.principalScalar S Z ℓ (slotMass T w) : ℂ) =
      (Z : ℂ)^(((-ℓ/6 : ℝ) : ℂ)) * PrincipalSlotEstimate.principalScalar S (slotMass T w) := by
  simp only [Probe.principalScalar, PrincipalSlotEstimate.principalScalar,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_cpow hZ.le]
  ring_nf

theorem source_normalizer_ne_zero (S : Finset κ) (T : κ → Finset ι)
    (w : κ → ι → ℝ) {Z ℓ : ℝ} (hZ : 0 < Z)
    (hm : ∀ j ∈ S, 0 < slotMass T w j) :
    (Probe.principalScalar S Z ℓ (slotMass T w) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Probe.principalScalar_ne_zero S hZ hm)

theorem source_power_identity {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    ((Z^(17/48 : ℝ) : ℝ) : ℂ)^(1/3 : ℂ) * (Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)) * (Z : ℂ)^(s-11/16) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le (17/48) (1/3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring_nf

theorem normalized_source_double_residue (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character)
    (Y Z : ℝ) (hZ : 0 < Z) (s : ℂ) (H B : ℂ → ℂ → ℂ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1/6) = slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^(17/48 : ℝ)) Y Z χ s H B 1 (1/6)) /
        (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ)) =
      (Z : ℂ)^(s-11/16) * Complex.exp ((s-5/6)^2) * H 1 (1/6) / LFunction χ s *
        slotRatio S T w Q A η s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := source_power_identity hZ s
  have hz : (Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M * (sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)) *
          ((Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ)^(s-11/16) * Complex.exp ((s-5/6)^2) * H 1 (1/6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf

def sourceResidueIntegral (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal HeckeFamily.O) [NeZero M]
    (χ : Character) (a X Y Z : ℝ) (H B : ℂ → ℂ → ℂ → ℂ) : ℂ :=
  verticalIntegral a (fun s => fixedPrincipalResidue M ^ 2 / 6 *
    sourceMultiplier W0 W1 X Y Z χ s (H s) (B s) 1 (1/6))

theorem sourceResidueIntegral_normalized (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A η ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M χ a (Z^(17/48 : ℝ)) Y Z H B /
      (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ)) =
        slotResidue χ (fun s => H s 1 (1/6)) a Z S T w Q A η := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm), ?_⟩
  unfold sourceResidueIntegral verticalIntegral slotResidue
  norm_num only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact normalized_source_double_residue W0 W1 M χ Y Z hZ _ (H _) (B _) S T w Q A η hc (hB _)

theorem source_double_residue_integrable (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A η ((a : ℂ)+t*I))
    (hi : Integrable (fun t : ℝ => kernel χ (fun s => H s 1 (1/6)) a Z t *
      slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ => fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^(17/48 : ℝ)) Y Z χ ((a : ℂ)+t*I)
        (H ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) := by
  have hiraw := raw_slot_integrable χ (fun s => H s 1 (1/6)) a Z S T w Q A η hi
  have hn := mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm (ℓ := 1/6))
  apply (hiraw.mul_const
    (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ))).congr
  filter_upwards [] with t
  exact ((div_eq_iff hn).mp (normalized_source_double_residue W0 W1 M χ Y Z hZ _
    (H _) (B _) S T w Q A η hc (hB _))).symm

def activePools (T : κ → Finset ι) (w : κ → ι → ℝ) (j : κ) : Finset ι :=
  (T j).filter (fun p => w j p ≠ 0)

theorem slotMass_active (T : κ → Finset ι) (w : κ → ι → ℝ) :
    slotMass (activePools T w) w = slotMass T w := by
  funext j
  simp only [slotMass, activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem slotProduct_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    slotProduct S (activePools T w) w Q A η s = slotProduct S T w Q A η s := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem slotRatio_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    slotRatio S (activePools T w) w Q A η s = slotRatio S T w Q A η s := by
  rw [slotRatio, slotRatio, slotProduct_active, slotMass_active]

theorem slotResidue_active (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H a Z S (activePools T w) w Q A η = slotResidue χ H a Z S T w Q A η := by
  simp only [slotResidue, slotRatio_active]

theorem slotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (7/8)*ell)
    (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset ι) (w Q : ℝ → κ → ι → ℝ) (A η : ℝ → κ → ι → ℂ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      SlotBounds S (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z) (c0*Z^ell)) :
    (fun Z : ℝ => slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
        signal χ H (-11/16) Z) =O[atTop] (fun Z : ℝ => Z^(a-11/16-saving)) := by
  obtain ⟨D, hD, hd⟩ := exists_slotResidue_bound χ H hH hb ha ha2 hβ S
  apply IsBigO.of_bound (D*c0^(-(7/8 : ℝ)))
  filter_upwards [hdata, eventually_ge_atTop (1 : ℝ)] with Z hz hZ
  have hZ0 : 0 < Z := by linarith
  have he := (hd (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z)
    (c0*Z^ell) Z hz hZ).2
  rw [slotResidue_active] at he
  have hp : (c0*Z^ell)^(-(7/8 : ℝ)) = c0^(-(7/8 : ℝ))*Z^(ell*(-(7/8 : ℝ))) := by
    rw [Real.mul_rpow hc0.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
  rw [hp] at he
  have hpow : Z^(a-11/16+ell*(-(7/8 : ℝ))) ≤ Z^(a-11/16-saving) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have he' : ‖slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
      signal χ H (-11/16) Z‖ ≤ (D*c0^(-(7/8 : ℝ)))*Z^(a-11/16-saving) := by
    calc
      _ ≤ D*Z^(a-11/16)*(c0^(-(7/8 : ℝ))*Z^(ell*(-(7/8 : ℝ)))) := he
      _ = (D*c0^(-(7/8 : ℝ)))*Z^(a-11/16+ell*(-(7/8 : ℝ))) := by
        rw [Real.rpow_add hZ0]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hZ0 _)] using he'

theorem actualSlotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (7/8)*ell)
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (w : ℝ → κ → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      SlotBounds S (activePools (T Z) (w Z)) (w Z) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
        (c0*Z^ell)) :
    (fun Z : ℝ => actualSlotResidue η E hE a Z S (T Z) (w Z) -
        signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z)
      =O[atTop] (fun Z : ℝ => Z^(a-11/16-saving)) :=
  slotResidue_isBigO S c0 ell saving hc0 hsaving (η.excludePrimes E hE.prime)
    (sourceCorrection η E) (sourceCorrection_differentiable η E hE)
    (sourceCorrection_bound η E hE) ha ha2 hβ T w
    (fun _ _ p => Ideal.absNorm p.val)
    (fun _ _ p => actualAPhase η (primaryGenerator p.val)) (fun _ _ p => idealCoeff η p.val) hdata

theorem fixedPrincipal_product_eq (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    fixedPrincipal (∏ p ∈ E, p) = fixedSourcePrincipal E hE.prime := rfl

theorem exists_normalized_actual_source_bound (E : Finset (Ideal HeckeFamily.O))
    (hE : SourceExclusions E) (η : Character) {a : ℝ}
    (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (T : κ → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
      (w : κ → _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℝ) (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P^(-(7/8 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) = slotProduct S T w (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val)
          ((a : ℂ)+t*I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z^(17/48 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z^(17/48 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D * Z^(a-11/16) * P^(-(7/8 : ℝ)) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hb⟩ := exists_slotResidue_bound (ι := _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (sourceCorrection_differentiable η E hE) (sourceCorrection_bound η E hE) ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := sourceResidueIntegral_normalized W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z (by linarith) (globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
    (fun _ p => idealCoeff η p.val) hc hmass hB
  have hslots : SlotBounds S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P :=
    ⟨hP, hsmall, hw, hnorm, fun _ _ p _ => actualAPhase_norm_le_one η _,
      fun j hj p hp => idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp), hmass⟩
  have hbnd := hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z hslots hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact source_double_residue_integrable W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
      a Y Z (by linarith) (globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryGenerator p.val))
      (fun _ p => idealCoeff η p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2

end SevenEighths.PrincipalSignalComparison
end

end OAI
end OAIOriginalModule2480

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalNormalizer
Source SHA256: c2d65a5ac9f76ea88939f3875661cf5c078b4543503b111c7999e3680e1700f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2481




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrincipalNormalizer
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
local notation "O" => HeckeFamily.O

theorem sourceResidueConstant_positive (M : Ideal O) [NeZero M]
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hreal0 : ∀y,(W0 y).im=0) (hreal1 : ∀y,(W1 y).im=0)
    (hpos0 : ∀y,0≤(W0 y).re) (hpos1 : ∀y,0≤(W1 y).re) (hne0 : W0≠0) (hne1 : W1≠0) :
    ∃c : ℝ,0<c ∧ sourceResidueConstant W0 W1 M=(c:ℂ) := by
  obtain ⟨hp0,hi0⟩ := ProbeRadialMellin.radial_mellin_one_sixth_pos W0 a0 b0 ha0 hW0 hreal0 hpos0 hne0
  obtain ⟨hp1,hi1⟩ := ProbeRadialMellin.positive_source_mellin W1 a1 b1 ha1 hW1 hreal1 hpos1 hne1 1
  obtain ⟨R,hR,hres⟩ := HeckePrincipalResidue.fixed_principal_residue_positive M
  have hr : fixedPrincipalResidue M=(R:ℂ) := by
    rw [fixedPrincipalResidue,←HeckeOrigin.poleRemoved_one]
    exact hres
  have he0 : mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (1/6)=
      ((mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (1/6)).re:ℂ) :=
    Complex.ext (by simp) (by simpa using hi0)
  have he1 : mellin W1 1=((mellin W1 1).re:ℂ) :=
    Complex.ext (by simp) (by simpa using hi1)
  refine ⟨(mellin W1 1).re*(mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (1/6)).re*R^2/6,?_,?_⟩
  · norm_num only [Complex.ofReal_one] at hp1
    positivity
  · unfold sourceResidueConstant
    rw [he0,he1,hr]
    push_cast
    rfl

theorem sourceResidueConstant_ne_zero (M : Ideal O) [NeZero M]
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hreal0 : ∀y,(W0 y).im=0) (hreal1 : ∀y,(W1 y).im=0)
    (hpos0 : ∀y,0≤(W0 y).re) (hpos1 : ∀y,0≤(W1 y).re) (hne0 : W0≠0) (hne1 : W1≠0) :
    sourceResidueConstant W0 W1 M≠0 := by
  obtain ⟨c,hc,he⟩ := sourceResidueConstant_positive M W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hreal0 hreal1 hpos0 hpos1 hne0 hne1
  rw [he]
  exact Complex.ofReal_ne_zero.mpr hc.ne'

theorem signed_source_normalizer_ne_zero {κ ι : Type*} [DecidableEq κ]
    (M : Ideal O) [NeZero M] (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hreal0 : ∀y,(W0 y).im=0) (hreal1 : ∀y,(W1 y).im=0)
    (hpos0 : ∀y,0≤(W0 y).re) (hpos1 : ∀y,0≤(W1 y).re) (hne0 : W0≠0) (hne1 : W1≠0)
    (S : Finset κ) (T : κ→Finset ι) (w : κ→ι→ℝ) (Z ℓ : ℝ) (hZ : 0<Z)
    (hm : ∀j∈S,0<slotMass T w j) :
    sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ℓ (slotMass T w):ℂ)≠0 :=
  mul_ne_zero (sourceResidueConstant_ne_zero M W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hreal0 hreal1 hpos0 hpos1 hne0 hne1) (source_normalizer_ne_zero S T w hZ hm)

end SevenEighths.ProbePrincipalNormalizer
end

end OAI
end OAIOriginalModule2481

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds
Source SHA256: de3b03a6fc50f24fe83e865fe2c6895c9d2900e1989ed611cc1780465102424f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2482



namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma active_prime_sum_bound (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : ℝ→ℝ)
    (c d B P ξ : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hP : 0<P)
    (hthreshold : 480≤c*P) (hξ : ξ≤1)
    (hW : ∀x,0≤W x ∧ W x≤B) (hsupp : Function.support W⊆Icc c d) :
    (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))
      ≤(128*d*B*c^(ξ-1))*P^ξ := by
  let A := T.filter (fun p=>W ((Ideal.absNorm p.val:ℝ)/P)≠0)
  have hA (p : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hp : p∈A) :
      c*P≤(Ideal.absNorm p.val:ℝ) ∧ (Ideal.absNorm p.val:ℝ)≤d*P := by
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
  have hp (p : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hp : p∈A) : (Ideal.absNorm p.val:ℝ)^(ξ-1)≤c^(ξ-1)*P^(ξ-1) := by
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

def slotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3/2)*∏_j∈J,(1+1440*(480:ℝ)^(-(7/8:ℝ)))*(128*d*B*c^(ξ-1))

lemma slotConstant_nonneg {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0<c) (hd : c≤d) (hB : 0≤B) : 0≤slotConstant J c d B ξ := by
  have hd0 : 0≤d := hc.le.trans hd
  unfold slotConstant
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _=>by positivity)

theorem window_sharp_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hξ : ξ≤1)
    (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤W j x ∧ W j x≤B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0<P j)
    (hthreshold : ∀j∈J,480≤c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j)
    (T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (s w z : ℂ)
    (hs : 7/8≤s.re) (hw : 19/20≤w.re) (hz : z.re=ξ) (hzlo : 33/200≤ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖≤
      slotConstant J c d B ξ * ∏j∈J,(P j)^ξ := by
  let A (j : ι) := (T j).filter (fun p=>W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hp : p∈A j) : c*P j≤(Ideal.absNorm p.val:ℝ) :=
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
  have h := combined_slot_bound_sharp η S hS J A
    (fun j p=>W j ((Ideal.absNorm p.val:ℝ)/P j)) 480 (by norm_num)
    (fun j hj p _=>(hW j hj _).1)
    (fun j hj p hp=>(hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp=>PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
      (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
        exact_mod_cast (hmod j hj).trans_le (hA j hj p hp)))) s w z hs hw (by rw [hz];exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _≤(3/2)*∏j∈J,(1+1440*(480:ℝ)^(-(7/8:ℝ)))*((128*d*B*c^(ξ-1))*(P j)^ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro j hj; apply mul_nonneg (by positivity);exact Finset.sum_nonneg (fun p _=>by
          exact mul_nonneg (hW j hj _).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left (active_prime_sum_bound (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [slotConstant,←mul_assoc,Finset.prod_mul_distrib]

def scalePower (X Y Z a ξ υ : ℝ) : ℝ :=
  X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)

lemma scalePower_nonneg {X Y Z a ξ υ : ℝ} (hX : 0≤X) (hY : 0≤Y) (hZ : 0≤Z) :
    0≤scalePower X Y Z a ξ υ := by unfold scalePower;positivity

section Pointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hξ : ξ≤1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤W j x ∧ W j x≤B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0<P j) (hthreshold : ∀j∈J,480≤c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) (T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
  (ha : 7/8≤a) (hυ : 19/20≤υ) (hzlo : 33/200≤ξ) (hC : 0≤C)
  (hR : ∀s : ℂ,a≤s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

lemma continued_source_sharp_pointwise (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)‖ ≤
    scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight t v u^2*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
  have hslot := window_sharp_bound η S hS.tail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)
    (by simpa using ha) (by simpa using hυ) (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)‖≤C*jointHeight t v u^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := height_le_joint_s t v u
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
    _≤X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)*(C*jointHeight t v u^2)*
      (slotConstant J c d B ξ*(∏j∈J,(P j)^ξ))*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
      gcongr
    _=_ := by unfold scalePower;ring

lemma full_sharp_pointwise (hυhi : υ≤2) (hυ1 : υ≠1) (hξ1 : 6*ξ≠1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*
      (wAmplitude (∏q∈S,q) 2/|υ-1|)) *
      (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))*
      (jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := fixed_principal_z_bound (∏q∈S,q) 1 ξ p.1.2 ⟨hzlo,hξ⟩ hξ1
  have hlw := fixed_principal_w_bound (∏q∈S,q) (by norm_num : (1:ℝ)<2) ⟨hυ,hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏q∈S,q) 1) (abs_nonneg (6*ξ-1))
  have hAW := div_nonneg (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le (abs_nonneg (υ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
  have ht := (height_pos p.1.1).le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul,norm_mul]
  calc
    _≤(scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*height p.1.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*height p.2^3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _≤(scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*jointHeight p.1.1 p.1.2 p.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*jointHeight p.1.1 p.1.2 p.2^3) := by
      have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
      gcongr <;> first | positivity | exact height_le_joint_z _ _ _ | exact height_le_joint_w _ _ _
    _=_ := by ring

omit hυ in
lemma residue_sharp_pointwise (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ≤
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one,ofReal_zero,zero_mul,add_zero] at h0
  have hlz := fixed_principal_z_bound (∏p∈S,p) 1 ξ q.2 ⟨hzlo,hξ⟩ hξ1
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏p∈S,p) 1) (abs_nonneg (6*ξ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _≤(scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*height q.2^3) := by
      gcongr ; first | positivity | exact h0 | exact hlz
    _≤(scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr ; first | positivity | exact height_le_joint_z _ _ _
    _=_ := by ring
end Pointwise

lemma vertical_triple_eq_joint (F : ℂ→ℂ→ℂ→ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace=>F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s=>verticalIntegral ξ (fun z=>verticalIntegral υ (fun w=>F s w z))) =
    (((1/(2*Real.pi):ℝ):ℂ))^3*
      ∫p : HeightSpace,F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) ∂heightMeasure := by
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma vertical_pair_eq_joint (F : ℂ→ℂ→ℂ) (a ξ : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ=>F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun s=>verticalIntegral ξ (fun z=>F s z)) =
    (((1/(2*Real.pi):ℝ):ℂ))^2*
      ∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume := by
  rw [integral_prod _ hi]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma normalizer_norm_pos : 0<‖(((1/(2*Real.pi):ℝ):ℂ))‖ := by
  apply norm_pos_iff.mpr
  exact_mod_cast (one_div_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero))

section Uniform
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
  (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
  (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
  (a ξ : ℝ) (ha : a∈Icc (7/8:ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
  (hξ : ξ∈Icc (33/200:ℝ) 1) (hξ1 : 6*ξ≠1)
include hc hd hB ha0 ha1 hW0 hW1 ha hβ hξ hξ1

theorem full_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    Integrable F heightMeasure ∧
      (∫p,‖F p‖ ∂heightMeasure)≤K/(|6*ξ-1| *|υ-1|)*
        (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (7/8) 2 (33/200) 1 (19/20) 2 (by norm_num) 8
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏q∈S,q) 1*wAmplitude (∏q∈S,q) 2*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := zBoxAmplitude_nonneg (∏q∈S,q) 1
  have hWA := (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le
  have hK : 0≤K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ 2 hX hY hZ ha.1 hβ hξ.1 (by norm_num) hυ hξ1 hυ1
  have hae := continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ
  have hae' := (hae.mul (EventuallyEq.rfl (f:=fun p : HeightSpace=>
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))))).mul
    (EventuallyEq.rfl (f:=fun p : HeightSpace=>LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)))
  refine ⟨hi.congr hae',?_⟩
  refine (integral_congr_ae (hae'.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*(wAmplitude (∏q∈S,q) 2/|υ-1|)
  let E := scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)
  have hA : 0≤A := by dsimp [A];positivity
  have hE : 0≤E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ υ hυ
  calc
    _≤∫p : HeightSpace,A*E*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) ∂heightMeasure := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro p
      exact full_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a υ C hX hY hZ ha.1 hυ.1 hξ.1 hC hR hυ.2 hυ1 hξ1 p
    _=A*E*(∫p : HeightSpace,jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _≤A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/(|6*ξ-1| *|υ-1|)*E := by dsimp [A,K];simp only [div_eq_mul_inv,mul_inv_rev];ring
    _≤(K+1)/(|6*ξ-1| *|υ-1|)*E := by gcongr;linarith

theorem residue_scale_bound :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let F := fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
    Integrable F (volume.prod volume) ∧
      (∫q,‖F q‖ ∂volume.prod volume)≤K/|6*ξ-1| *
        (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (7/8) 2 (33/200) 1 1 1 (by norm_num) 5 0
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏p∈S,p) 1*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := zBoxAmplitude_nonneg (∏p∈S,p) 1
  have hK : 0≤K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha.1 hβ hξ.1 hξ1
  have hae : (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I)) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    rw [continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
    rfl
  refine ⟨hi.congr hae,?_⟩
  refine (integral_congr_ae (hae.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)
  let E := scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)
  have hA : 0≤A := by dsimp [A];positivity
  have hE : 0≤E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ 1 ⟨le_rfl,le_rfl⟩ .w 0
  simp only [sliceMap,pow_zero,div_one] at hp
  calc
    _≤∫q : ℝ×ℝ,A*E*(jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) ∂volume.prod volume := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro q
      exact residue_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a C hX hY hZ ha.1 hξ.1 hC hR hξ1 q
    _=A*E*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖ ∂volume.prod volume) := integral_const_mul _ _
    _≤A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/|6*ξ-1| *E := by dsimp [A,K];ring
    _≤(K+1)/|6*ξ-1| *E := by gcongr;linarith

theorem full_vertical_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖verticalIntegral a (fun s=>verticalIntegral ξ (fun z=>verticalIntegral υ
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := full_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 υ hυ hυ1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^3
  have hk : 0<k := pow_pos normalizer_norm_pos _
  refine ⟨k*K,mul_pos hk hK,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [vertical_triple_eq_joint _ a ξ υ hh.1,norm_mul,norm_pow]
  calc
    _≤k*(∫p : HeightSpace,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le
    _≤k*(K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))) :=
      mul_le_mul_of_nonneg_left hh.2 hk.le
    _=_ := by ring

theorem residue_vertical_scale_bound :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral ξ
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := residue_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1
  let R := HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^2
  have hk : 0<k := pow_pos normalizer_norm_pos _
  refine ⟨(1+‖R‖)*k*K,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [vertical_pair_eq_joint _ a ξ hh.1,norm_mul,norm_mul,norm_pow]
  calc
    _≤(1+‖R‖)*(k*(∫q : ℝ×ℝ,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ∂volume.prod volume)) := by
      apply mul_le_mul (by dsimp [R];linarith [norm_nonneg (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)])
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le) (by positivity) (by positivity)
    _≤(1+‖R‖)*(k*(K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)))) := by
      gcongr;exact hh.2
    _=_ := by ring
end Uniform

theorem ordered_remainders_scale_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (7/8:ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
    (he : 0<e) (hehi : e≤5/6) :
    ∃C : ℝ,0<C ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*(scalePower X Y Z a (1/6+e) (19/20)*(∏j∈J,(P j)^(1/6+e)))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      C*(scalePower X Y Z a (33/200) 1*(∏j∈J,(P j)^(33/200:ℝ)))) := by
  obtain ⟨A,hA,hfirst⟩ := full_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (1/6+e) ha hβ ⟨by linarith,by linarith⟩ (by linarith)
    (19/20) (by norm_num) (by norm_num)
  obtain ⟨D,hD,hsecond⟩ := residue_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (33/200) ha hβ (by norm_num) (by norm_num)
  refine ⟨(10/3)*A+100*D,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hf := hfirst W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  have hg := hsecond W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hf hg
  have hegap : |6*((1/6:ℝ)+e)-1|=6*e := by rw [abs_of_pos (by linarith)];ring
  rw [hegap] at hf
  norm_num only [show |(19/20:ℝ)-1|=1/20 by norm_num] at hf
  norm_num only [show |6*(33/200:ℝ)-1|=1/100 by norm_num] at hg
  have hm (ξ : ℝ) : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  constructor
  · apply hf.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    have heq : A/(6*e*(1/20))=((10/3)*A)/e := by field_simp;ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  · apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    norm_num
    linarith

lemma source_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=1/6) (Z a ξ υ : ℝ) (hZ : 0<Z) :
    scalePower (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a ξ υ *
      (∏j∈J,(Z^(ell j))^ξ) =
    Z^(a-11/16+(13/16)*(ξ-1/6)+(23/48)*(υ-1)) := by
  have hp : (∏j∈J,(Z^(ell j))^ξ)=Z^((1/6)*ξ) := by
    simp only [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,hell]
  rw [hp,scalePower,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma source_w_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=1/6) (Z a e : ℝ) (hZ : 0<Z) :
    scalePower (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a (1/6+e) (19/20) *
      (∏j∈J,(Z^(ell j))^(1/6+e)) = Z^(a-11/16+(13/16)*e-23/960) := by
  rw [source_scale_identity J ell hell Z a (1/6+e) (19/20) hZ]
  congr 1;ring

lemma source_z_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=1/6) (Z a : ℝ) (hZ : 0<Z) :
    scalePower (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a (33/200) 1 *
      (∏j∈J,(Z^(ell j))^(33/200:ℝ)) = Z^(a-11/16-13/9600) := by
  rw [source_scale_identity J ell hell Z a (33/200) 1 hZ]
  congr 1;ring

lemma eventual_annulus_threshold {ι : Type*} (η : Character) (J : Finset ι)
    (c : ℝ) (hc : 0<c) (ell : ι→ℝ) (hell : ∀j∈J,0<ell j) :
    ∃Z0 : ℝ,1≤Z0 ∧ ∀Z : ℝ,Z0≤Z→∀j∈J,
      480≤c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j) := by
  have hh : ∀ᶠZ : ℝ in atTop,∀j∈J,
      480≤c*Z^(ell j) ∧ (Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j) := by
    apply (Filter.eventually_all_finset J).mpr
    intro j hj
    have ht := (tendsto_rpow_atTop (hell j hj)).const_mul_atTop hc
    exact (ht.eventually (eventually_ge_atTop 480)).and
      (ht.eventually (eventually_gt_atTop (Ideal.absNorm η.modulus:ℝ)))
  obtain ⟨Z0,hZ0⟩ := eventually_atTop.mp hh
  refine ⟨max 1 Z0,le_max_left _ _,?_⟩
  intro Z hZ
  exact hZ0 Z ((le_max_right _ _).trans hZ)

theorem source_remainders_power_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (7/8:ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
    (he : 0<e) (hehi : e≤5/6) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=1/6) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0<Z→
    (∀j∈J,480≤c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(a-11/16+(13/16)*e-23/960)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤C*Z^(a-11/16-13/9600)) := by
  obtain ⟨C,hC,hbound⟩ := ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=>Z^(ell j)) (fun _ _=>Real.rpow_pos_of_pos hZ _)
    hthreshold hmod T hT (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [source_w_scale_identity J ell hell Z a e hZ,source_z_scale_identity J ell hell Z a hZ] at hh
  exact hh

lemma source_w_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-11/16+(13/16)*e-23/960≤β-11/16-17/48000 := by linarith

lemma source_z_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-11/16-13/9600≤β-11/16-17/48000 := by linarith

theorem source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : HeckeZeroSupremum.beta+e∈Icc (7/8:ℝ) 2) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=1/6) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1≤Z→
    (∀j∈J,480≤c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>verticalIntegral (1/6+e)
      (fun z=>verticalIntegral (19/20) (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=>verticalIntegral (33/200) (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      C*Z^(HeckeZeroSupremum.beta-11/16-17/48000)) := by
  obtain ⟨C,hC,hbound⟩ := source_remainders_power_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e ha (by linarith) he (by linarith)
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound ell hell W hW hsupp T hT Z (by linarith) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end SevenEighths.ProbePrincipalRemainderBounds

end

end OAI
end OAIOriginalModule2482

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalResidueActual
Source SHA256: 5f80db68ee4b367665ee80adb34c97ed740b79ea3250517d816a71e69fb47013
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2483



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SevenEighths.ProbePrincipalResidueActual
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
open ProbeFiniteProductBounds ProbeEuler ProbeLocal HeckeSignal ProbePhysical Continuation
open ActualEisensteinCubic CompletedGauss

def residueWeights {κ : Type*} (W : κ → ℝ → ℝ) (scale : κ → ℝ)
    (j : κ) (p : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : ℝ :=
  W j ((Ideal.absNorm p.val : ℝ)/scale j) * (Ideal.absNorm p.val : ℝ)^(-(5/6 : ℝ))

theorem actual_window_residue {κ : Type*} (η : Character) (S : Finset κ)
    (T : κ → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (s : ℂ) :
    windowMultiplier η S T (fun j t => (W j t : ℂ)) scale s 1 (1/6) =
      slotProduct S T (residueWeights W scale) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryGenerator p.val))
        (fun _ p => idealCoeff η p.val) s := by
  exact window_at_residue η S T W scale s

theorem normalized_actual_window_residue {κ : Type*}
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 7/8<a) (ha2 : a≤2) (hβ : HeckeZeroSupremum.beta<a) (S : Finset κ) :
    letI : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃D : ℝ, 0≤D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0<a0 → 0<a1 → Function.support W0⊆Set.Icc a0 b0 →
      Function.support W1⊆Set.Icc a1 b1 →
      (∀y,(W0 y).im=0) → (∀y,(W1 y).im=0) →
      (∀y,0≤(W0 y).re) → (∀y,0≤(W1 y).re) → W0≠0 → W1≠0 →
      ∀ (T : κ → Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480≤P → 1440*P^(-(7/8 : ℝ))≤1 →
      (∀j∈S,∀p∈T j,0≤W j ((Ideal.absNorm p.val : ℝ)/scale j)) →
      (∀j∈S,∀p∈T j,P≤(Ideal.absNorm p.val : ℝ)) →
      (∀j∈S,∀p∈T j,IsCoprime p.val η.modulus) →
      (∀j∈S,0<slotMass T (residueWeights W scale) j) → 1≤Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏p∈E,p) *
        (Probe.principalScalar S Z (1/6) (slotMass T (residueWeights W scale)) : ℂ)
      normer≠0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏p∈E,p)^2/6 *
        sourceMultiplier W0 W1 (Z^(17/48 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I))
          (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏p∈E,p) (η.excludePrimes E hE.prime)
          a (Z^(17/48 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D*Z^(a-11/16)*P^(-(7/8 : ℝ)) := by
  dsimp only
  let : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D,hD,hbound⟩ := exists_normalized_actual_source_bound E hE η ha ha2 hβ S
  refine ⟨D,hD,?_⟩
  intro W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W scale P Y Z hP hsmall hW hnorm hcop hmass hZ
  refine hbound W0 W1 T (residueWeights W scale) P Y Z
    (windowMultiplier η S T (fun j t => (W j t : ℂ)) scale)
    hP hsmall ?_ hnorm hcop hmass hZ ?_ ?_
  · intro j hj p hp
    exact mul_nonneg (hW j hj p hp) (Real.rpow_nonneg (by positivity) _)
  · exact ProbePrincipalNormalizer.sourceResidueConstant_ne_zero (∏p∈E,p)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  · intro t
    exact actual_window_residue η S T W scale _

end SevenEighths.ProbePrincipalResidueActual
end

end OAI
end OAIOriginalModule2483

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RaySlots
Source SHA256: ec7b98c29e44366622912f329f3a78fe430f7747bd8fc9c79ae5e3100378eb37
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2484



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PNT.AnnularPrimeMass
open PrincipalSignalComparison ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

def pool (C : Set Id) (S : Finset Id) (a b x : ℝ) : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal :=
  (annularPrimeIdeals C a b x \ S).subtype (fun P=>Prime P)

@[simp] theorem mem_pool (C : Set Id) (S : Finset Id) (a b x : ℝ) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) :
    P∈pool C S a b x ↔ P.val∈C ∧ ⌊x*a⌋₊<Ideal.absNorm P.val ∧
      Ideal.absNorm P.val≤⌊x*b⌋₊ ∧ P.val∉S := by
  simp only [pool,Finset.mem_subtype,Finset.mem_sdiff,mem_annularPrimeIdeals,P.property]
  tauto

theorem pool_norm_bounds (C : Set Id) (S : Finset Id) {a b x : ℝ}
    (ha : 0≤a) (hab : a≤b) (hx : 0<x) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P∈pool C S a b x) :
    x*a<(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤x*b :=
  norm_bounds_of_mem_annularPrimeIdeals ha hab hx
    (Finset.mem_sdiff.mp (Finset.mem_subtype.mp hP)).1

lemma pool_sum (C : Set Id) (S : Finset Id) (a b x : ℝ) (f : Id→ℝ) :
    (∑P∈pool C S a b x,f P.val)=∑P∈annularPrimeIdeals C a b x\S,f P := by
  apply Finset.sum_bij (fun P _=>P.val)
  · intro P hP
    exact Finset.mem_subtype.mp hP
  · intro P hP Q hQ he
    exact Subtype.ext he
  · intro P hP
    have hp : Prime P := ((mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1).2.1
    exact ⟨⟨P,hp⟩,Finset.mem_subtype.mpr hP,rfl⟩
  · intro P hP
    rfl

theorem pool_mass_eq_deleted (C : Set Id) (S : Finset Id) (W : ℝ→ℝ)
    {a b x : ℝ} (ha : 0<a) (hab : a≤b)
    (hsupp : Function.support W⊆Set.Ioo a b) (hx : 0<x) :
    (∑P∈pool C S a b x,W ((Ideal.absNorm P.val:ℝ)/x)*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)))=
      weightedPrimeSumDeleted C S W x := by
  rw [pool_sum C S a b x (fun P=>W ((Ideal.absNorm P:ℝ)/x)*(Ideal.absNorm P:ℝ)^(-(5/6:ℝ))),
    weightedPrimeSumDeleted_eq_annular C S W ha hab hsupp hx]
  norm_num

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

theorem ray_pool_mass_eventually_positive (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hWne : W≠0) :
    ∀ᶠx : ℝ in atTop,0<∑P∈pool (RayQuotient.identityClass M H) S a b x,
      W ((Ideal.absNorm P.val:ℝ)/x)*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  filter_upwards [RayPrimeNormalizer.eventually_pos M H hH S W hW hc hp hW0 hWne,
    eventually_gt_atTop (0:ℝ)] with x hx hx0
  rw [pool_mass_eq_deleted _ _ _ ha hab hsupp hx0]
  exact hx

theorem ray_pool_mass_eventually_lower_bound (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hWne : W≠0) :
    ∃c : ℝ,0<c ∧ ∀ᶠx : ℝ in atTop,c*x^(1/6:ℝ)/Real.log x≤
      ∑P∈pool (RayQuotient.identityClass M H) S a b x,
        W ((Ideal.absNorm P.val:ℝ)/x)*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  obtain ⟨c,hc0,hbound⟩ := RayPrimeNormalizer.eventually_lower_bound M H hH S W hW hc hp hW0 hWne
  refine ⟨c,hc0,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with x hx hx0
  rw [pool_mass_eq_deleted _ _ _ ha hab hsupp hx0]
  exact hx

end SevenEighths.ProbeRaySlots
end

end OAI
end OAIOriginalModule2484

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RayNormalization
Source SHA256: 87553b4b2eced80b5fa9d4b51bcd2b574fc26fd9532aaffa6e707d4016a1a462
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2485



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRayNormalization
open HeckeFamily ProbePhysical ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

theorem log_power_absorption (c ell d : ℝ) (hc : 0<c) (hell : 0<ell) (hd : 0<d) :
    ∀ᶠZ : ℝ in atTop,Z^(ell/6-d)≤c*(Z^ell)^(1/6:ℝ)/Real.log (Z^ell) := by
  have hh := (isLittleO_log_rpow_atTop hd).bound (div_pos hc hell)
  filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  have hZ0 : 0<Z := by linarith
  have hlog : 0<Real.log Z := Real.log_pos hZ1
  have hzd : 0<Z^d := Real.rpow_pos_of_pos hZ0 _
  have hb : ell*Real.log Z≤c*Z^d := by
    have hb' : Real.log Z≤(c/ell)*Z^d := by
      simpa only [Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos hzd] using hZ
    calc
      _ ≤ ell*((c/ell)*Z^d) := mul_le_mul_of_nonneg_left hb' hell.le
      _ = _ := by field_simp
  rw [Real.log_rpow hZ0,←Real.rpow_mul hZ0.le]
  apply (le_div_iff₀ (mul_pos hell hlog)).mpr
  calc
    Z^(ell/6-d)*(ell*Real.log Z) ≤ Z^(ell/6-d)*(c*Z^d) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZ0.le _)
    _ = c*Z^(ell*(1/6:ℝ)) := by
      rw [mul_left_comm,←Real.rpow_add hZ0]
      congr 1
      ring_nf

theorem principalScalar_inverse_of_slot_bounds {ι : Type*} (J : Finset ι)
    (ell mass : ι→ℝ) (Z d eps : ℝ) (hZ : 1≤Z) (_hd : 0≤d)
    (hbudget : d*J.card≤eps) (hm : ∀i∈J,Z^(ell i/6-d)≤mass i) :
    |(Probe.principalScalar J Z (∑i∈J,ell i) mass)⁻¹|≤Z^eps := by
  have hZ0 : 0<Z := by linarith
  have hm0 : ∀i∈J,0≤mass i := fun i hi=>(Real.rpow_nonneg hZ0.le _).trans (hm i hi)
  have hprod : Z^(∑i∈J,(ell i/6-d))≤∏i∈J,mass i := by
    rw [Real.rpow_sum_of_pos hZ0]
    exact Finset.prod_le_prod₀ (fun i _=>Real.rpow_nonneg hZ0.le _) hm
  have hn : |Probe.principalScalar J Z (∑i∈J,ell i) mass|=
      Z^(-(∑i∈J,ell i)/6)*(∏i∈J,mass i) := by
    unfold Probe.principalScalar
    rw [abs_mul,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
      abs_of_pos (Real.rpow_pos_of_pos hZ0 _),abs_of_nonneg (Finset.prod_nonneg hm0)]
  have hpow : Z^(-(∑i∈J,ell i)/6)*Z^(∑i∈J,(ell i/6-d))=Z^(-d*J.card) := by
    rw [←Real.rpow_add hZ0]
    congr 1
    rw [Finset.sum_sub_distrib,←Finset.sum_div,Finset.sum_const,nsmul_eq_mul]
    ring
  have hl : Z^(-eps)≤|Probe.principalScalar J Z (∑i∈J,ell i) mass| := by
    calc
      _ ≤ Z^(-d*J.card) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
      _ = Z^(-(∑i∈J,ell i)/6)*Z^(∑i∈J,(ell i/6-d)) := hpow.symm
      _ ≤ _ := by rw [hn];exact mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hZ0.le _)
  rw [abs_inv]
  have hi := (inv_le_inv₀ ((Real.rpow_pos_of_pos hZ0 (-eps)).trans_le hl)
    (Real.rpow_pos_of_pos hZ0 (-eps))).mpr hl
  simpa only [Real.rpow_neg hZ0.le,inv_inv] using hi

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

theorem ray_slot_subpower_lower (S : Finset Id) (W : ℝ→ℝ)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) (hsupp : Function.support W⊆Set.Ioo a b)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W⊆Set.Ioi 0)
    (hW0 : ∀y,0≤W y) (hWne : W≠0) (ell d : ℝ) (hell : 0<ell) (hd : 0<d) :
    ∀ᶠZ : ℝ in atTop,Z^(ell/6-d)≤
      ∑P∈pool (RayQuotient.identityClass M H) S a b (Z^ell),
        W ((Ideal.absNorm P.val:ℝ)/(Z^ell))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
  obtain ⟨c,hc0,hbound⟩ := ray_pool_mass_eventually_lower_bound M H hH S W a b ha hab hsupp hW hc hp hW0 hWne
  filter_upwards [(tendsto_rpow_atTop hell).eventually hbound,log_power_absorption c ell d hc0 hell hd]
    with Z hZ hlog
  exact hlog.trans hZ

theorem ray_principalScalar_inverse_subpower {ι : Type*} (J : Finset ι)
    (S : Finset Id) (W : ι→ℝ→ℝ) (a b ell : ι→ℝ)
    (ha : ∀i∈J,0<a i) (hab : ∀i∈J,a i≤b i)
    (hsupp : ∀i∈J,Function.support (W i)⊆Set.Ioo (a i) (b i))
    (hW : ∀i∈J,ContDiff ℝ ∞ (W i)) (hc : ∀i∈J,HasCompactSupport (W i))
    (hp : ∀i∈J,tsupport (W i)⊆Set.Ioi 0)
    (hW0 : ∀i∈J,∀y,0≤W i y) (hWne : ∀i∈J,W i≠0) (hell : ∀i∈J,0<ell i)
    (eps : ℝ) (heps : 0<eps) :
    ∀ᶠZ : ℝ in atTop,
      |(Probe.principalScalar J Z (∑i∈J,ell i) (fun i=>
        ∑P∈pool (RayQuotient.identityClass M H) S (a i) (b i) (Z^(ell i)),
          W i ((Ideal.absNorm P.val:ℝ)/(Z^(ell i)))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ))))⁻¹|≤Z^eps := by
  let d : ℝ := eps/(J.card+1)
  have hd : 0<d := div_pos heps (by positivity)
  have hb : d*J.card≤eps := by
    dsimp [d]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : (0:ℝ)<J.card+1)]
    nlinarith
  have hm : ∀ᶠZ : ℝ in atTop,∀i∈J,Z^(ell i/6-d)≤
      ∑P∈pool (RayQuotient.identityClass M H) S (a i) (b i) (Z^(ell i)),
        W i ((Ideal.absNorm P.val:ℝ)/(Z^(ell i)))*(Ideal.absNorm P.val:ℝ)^(-(5/6:ℝ)) := by
    apply (Filter.eventually_all_finset J).mpr
    intro i hi
    exact ray_slot_subpower_lower M H hH S (W i) (a i) (b i) (ha i hi) (hab i hi)
      (hsupp i hi) (hW i hi) (hc i hi) (hp i hi) (hW0 i hi) (hWne i hi) (ell i) d (hell i hi) hd
  filter_upwards [hm,eventually_ge_atTop (1:ℝ)] with Z hmass hZ
  exact principalScalar_inverse_of_slot_bounds J ell _ Z d eps hZ hd.le hb hmass

end SevenEighths.ProbeRayNormalization
end

end OAI
end OAIOriginalModule2485

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RayPhaseAmplitude
Source SHA256: 1a832ccbff8266593d1b06157c2555659cbd21771b5f94d876bc9cf0b53f8bdd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2486



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PNT.AnnularPrimeMass
local notation "Id" => Ideal HeckeFamily.O

lemma pool_sum_complex (C : Set Id) (S : Finset Id) (a b x : ℝ) (f : Id→ℂ) :
    (∑P∈pool C S a b x,f P.val)=∑P∈annularPrimeIdeals C a b x\S,f P := by
  apply Finset.sum_bij (fun P _=>P.val)
  · intro P hP;exact Finset.mem_subtype.mp hP
  · intro P hP Q hQ he;exact Subtype.ext he
  · intro P hP
    have hp : Prime P := ((mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1).2.1
    exact ⟨⟨P,hp⟩,Finset.mem_subtype.mpr hP,rfl⟩
  · intro P hP;rfl

theorem weighted_pool_eq_annular (C : Set Id) (S : Finset Id)
    (W : ℝ→ℂ) (a b D : ℝ) (ha : 0<a) (_hab : a≤b) (hD : 0<D)
    (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤a*D) (g : Id→ℂ) :
    (∑P∈pool C S a b D,W ((P.val.absNorm:ℝ)/D)*g P.val)=
      ∑P∈(HeckePrimeAnnular.annulusSet b D).filter (fun P=>Prime P ∧ P∈C),
        W ((P.absNorm:ℝ)/D)*g P := by
  rw [pool_sum_complex C S a b D (fun P=>W ((P.absNorm:ℝ)/D)*g P)]
  have hsub : annularPrimeIdeals C a b D\S⊆
      (HeckePrimeAnnular.annulusSet b D).filter (fun P=>Prime P ∧ P∈C) := by
    intro P hP
    have hp := (mem_annularPrimeIdeals C a b D P).mp (Finset.mem_sdiff.mp hP).1
    apply Finset.mem_filter.mpr
    refine ⟨?_,hp.2.1,hp.1⟩
    apply ConcretePrimeRowBridge.mem_idealsUpTo.mpr
    refine ⟨Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1.ne_zero),?_⟩
    apply hp.2.2.2.trans
    apply Nat.floor_mono
    nlinarith [le_max_right (1:ℝ) b]
  apply Finset.sum_subset hsub
  intro P hP hnot
  have hw : W ((P.absNorm:ℝ)/D)=0 := by
    by_contra hn
    have hy := hW hn
    have hp := (Finset.mem_filter.mp hP).2
    apply hnot
    apply Finset.mem_sdiff.mpr
    constructor
    · apply (mem_annularPrimeIdeals C a b D P).mpr
      refine ⟨hp.2,hp.1,?_,?_⟩
      · apply (Nat.floor_lt (mul_nonneg hD.le ha.le)).mpr
        have := (lt_div_iff₀ hD).mp hy.1
        nlinarith
      · apply Nat.le_floor
        have := (div_lt_iff₀ hD).mp hy.2
        nlinarith
    · intro hs
      have := hS P hs
      have := (lt_div_iff₀ hD).mp hy.1
      linarith
  simp only [hw,zero_mul]

theorem central_phase_eq_amplitude (M : Id) [NeZero M]
    [Finite (HeckeFamily.O ⧸ M)] (H : Subgroup (HeckeFamily.O ⧸ M)ˣ)
    (S : Finset Id) (u : HeckeFamily.O) (W : ℝ→ℂ) (a b D : ℝ)
    (ha : 0<a) (hab : a≤b) (hD : 0<D) (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤a*D) (z : ℂ) :
    (∑P∈pool (RayQuotient.identityClass M H) S a b D,
      W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u P.val)))=
      -(D:ℂ)^(z-1/2)*HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z := by
  have he := weighted_pool_eq_annular (RayQuotient.identityClass M H) S W a b D ha hab hD hW hS
    (fun P=>(P.absNorm:ℂ)^(z-1)*(-star (CanonicalRowCompletion.idealRowHom u P)))
  simp_rw [mul_assoc] at ⊢
  rw [he]
  unfold HeckePrimeRow.canonicalPrimeAmplitude
  rw [←mul_assoc,neg_mul,←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  have hexp : (z-(1/2:ℂ)) + -(1/2:ℂ)=z-1 := by ring
  rw [hexp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hprime := (Finset.mem_filter.mp hP).2.1
  have hn : (0:ℝ)<P.absNorm := by exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hprime.ne_zero)
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hn.le hD.le]
  have hd : (D:ℂ)^(z-1)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  field_simp
  simp only [starRingEnd_apply,Complex.ofReal_natCast]
  ring

theorem central_phase_norm (M : Id) [NeZero M]
    [Finite (HeckeFamily.O ⧸ M)] (H : Subgroup (HeckeFamily.O ⧸ M)ˣ)
    (S : Finset Id) (u : HeckeFamily.O) (W : ℝ→ℂ) (a b D : ℝ)
    (ha : 0<a) (hab : a≤b) (hD : 0<D) (hW : Function.support W⊆Set.Ioo a b)
    (hS : ∀P∈S,(P.absNorm:ℝ)≤a*D) (z : ℂ) :
    ‖∑P∈pool (RayQuotient.identityClass M H) S a b D,
      W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u P.val))‖=
      D^(z.re-1/2)*‖HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z‖ := by
  rw [central_phase_eq_amplitude M H S u W a b D ha hab hD hW hS z,
    norm_mul,norm_neg,Complex.norm_cpow_eq_rpow_re_of_pos hD]
  norm_num

theorem power_fixed_exclusions (S : Finset Id) (a ellMin : ℝ) (ha : 0<a) (hmin : 0<ellMin)
    {ι : Type*} (ell : ι→ℝ) (hell : ∀j,ellMin≤ell j) :
    ∀ᶠZ : ℝ in Filter.atTop,∀j,∀P∈S,(P.absNorm:ℝ)≤a*Z^(ell j) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop ha
  filter_upwards [ht.eventually (Filter.eventually_ge_atTop (∑P∈S,(P.absNorm:ℝ))),
    Filter.eventually_ge_atTop (1:ℝ)] with Z hnorm hZ j P hP
  calc
    (P.absNorm:ℝ) ≤ ∑Q∈S,(Q.absNorm:ℝ) := Finset.single_le_sum (fun Q _=>Nat.cast_nonneg _) hP
    _ ≤ a*Z^ellMin := hnorm
    _ ≤ a*Z^(ell j) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) ha.le

end SevenEighths.ProbeRaySlots
end

end OAI
end OAIOriginalModule2486

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RayPoolDisjoint
Source SHA256: eec96f4c382be0cadee250ac904cd2ce20aefbf4a882b8caf7d681486b1915af
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2487


namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical
local notation "Id" => Ideal HeckeFamily.O

lemma annular_power_separation (a b r s : ℝ) (ha : 0<a) (hrs : r<s) :
    ∀ᶠZ : ℝ in atTop,b*Z^r<a*Z^s := by
  have hh := (tendsto_rpow_atTop (show 0<s-r by linarith)).eventually (eventually_gt_atTop (b/a))
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  have ht : b<a*Z^(s-r) := by
    have h := (div_lt_iff₀ ha).mp hZ
    nlinarith
  have hp : 0<Z^r := Real.rpow_pos_of_pos hZ0 _
  calc
    b*Z^r < (a*Z^(s-r))*Z^r := mul_lt_mul_of_pos_right ht hp
    _=a*Z^s := by rw [mul_assoc,←Real.rpow_add hZ0];congr 1;congr 1;ring

theorem power_pools_eventually_disjoint {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀i j, i≠j→Disjoint (pool C S (a i) (b i) (Z^(ell i)))
      (pool C S (a j) (b j) (Z^(ell j))) := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i=j
  · exact Filter.Eventually.of_forall (fun Z hn=>(hn hij).elim)
  have hne : ell i≠ell j := fun h=>hij (hell h)
  rcases lt_or_gt_of_ne hne with hlt|hgt
  · filter_upwards [annular_power_separation (a j) (b i) (ell i) (ell j) (ha j) hlt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith
  · filter_upwards [annular_power_separation (a i) (b j) (ell j) (ell i) (ha i) hgt,
      eventually_gt_atTop (0:ℝ)] with Z hsep hZ _
    apply Finset.disjoint_left.mpr
    intro P hPi hPj
    have hi := pool_norm_bounds C S (ha i).le (hab i) (Real.rpow_pos_of_pos hZ _) P hPi
    have hj := pool_norm_bounds C S (ha j).le (hab j) (Real.rpow_pos_of_pos hZ _) P hPj
    nlinarith

theorem power_pool_tuples_eventually_injective {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (a b ell : ι→ℝ)
    (ha : ∀i,0<a i) (hab : ∀i,a i≤b i) (hell : Function.Injective ell) :
    ∀ᶠZ : ℝ in atTop,∀P:(∀i,pool C S (a i) (b i) (Z^(ell i))),
      Function.Injective (fun i=>(P i).val) := by
  filter_upwards [power_pools_eventually_disjoint C S a b ell ha hab hell] with Z hZ P
  intro i j heq
  by_contra hn
  have hq : (P i).val=(P j).val := heq
  exact Finset.disjoint_left.mp (hZ i j hn) (P i).property (by rw [hq];exact (P j).property)
end SevenEighths.ProbeRaySlots
end

end OAI
end OAIOriginalModule2487

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RayPoolGood
Source SHA256: d53b6c0311ae4703aa6291371e227e2252f879719e10362f25b1a2ae292710b1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2488


namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical CanonicalQuadraticSieve PrincipalSignalComparison
local notation "Id" => Ideal HeckeFamily.O

theorem prime_coprime_of_norm_gt (η : Character) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hN : (η.modulus.absNorm:ℝ)<(P.val.absNorm:ℝ)) : IsCoprime P.val η.modulus := by
  apply Ideal.coprime_of_no_prime_ge
  intro J hPJ hηJ hJ
  have hmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have heq := hmax.eq_of_le hJ.ne_top hPJ
  rw [←heq] at hηJ
  have hd : P.val∣η.modulus := Ideal.dvd_iff_le.mpr hηJ
  have hn := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot))
    (map_dvd Ideal.absNorm hd)
  exact (not_le_of_gt hN) (by exact_mod_cast hn)

theorem pool_eventually_target_coprime (C : Set Id) (S : Finset Id) (η : Character)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∀ᶠx : ℝ in atTop,∀P∈pool C S a b x,IsCoprime P.val η.modulus := by
  filter_upwards [eventually_gt_atTop ((η.modulus.absNorm:ℝ)/a),eventually_gt_atTop (0:ℝ)] with x hx hx0
  intro P hP
  apply prime_coprime_of_norm_gt η P
  exact ((div_lt_iff₀ ha).mp hx).trans (pool_norm_bounds C S ha.le hab hx0 P hP).1

theorem pool_eventually_target_unit_value (C : Set Id) (S : Finset Id) (η : Character)
    (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∀ᶠx : ℝ in atTop,∀P∈pool C S a b x,‖idealCoeff η P.val‖=1 := by
  filter_upwards [pool_eventually_target_coprime C S η a b ha hab] with x hx
  intro P hP
  exact idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero (hx P hP)

theorem pool_supported (C : Set Id) (S : Finset Id) (hS : SourceExclusions S)
    (a b x : ℝ) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P∈pool C S a b x) : Supported P.val :=
  outside_prime_supported S hS.bad P ((mem_pool C S a b x P).mp hP).2.2.2

theorem pool_target_coprime_at_power (C : Set Id) (S : Finset Id) (η : Character)
    (a b ell : ℝ) (ha : 0<a) (hab : a≤b) (hell : 0<ell) :
    ∀ᶠZ : ℝ in atTop,∀P∈pool C S a b (Z^ell),IsCoprime P.val η.modulus :=
  (tendsto_rpow_atTop hell).eventually (pool_eventually_target_coprime C S η a b ha hab)

end SevenEighths.ProbeRaySlots
end

end OAI
