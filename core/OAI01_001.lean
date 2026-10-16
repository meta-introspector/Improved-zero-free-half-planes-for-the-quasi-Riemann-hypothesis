lemma inv_one_sub_norm_le_two (a : ℂ) (ha : ‖a‖ ≤ 1/2) : ‖(1-a)⁻¹‖ ≤ 2 := by
  have hl := norm_sub_norm_le (1 : ℂ) a
  simp only [norm_one] at hl
  have hd : 0 < ‖1-a‖ := by linarith
  rw [norm_inv, ← one_div, div_le_iff₀ hd]
  linarith

theorem unramified_marked_error_bound (R V qInv K W D : ℂ)
    (hR : ‖R‖ ≤ 1/2) (hV : ‖V‖ ≤ 1/2) (hq : ‖qInv‖ ≤ 1) (hD : ‖D‖ ≤ 1/2) :
    ‖ProbeEuler.markedFactor R V qInv K (-D + W*R) 1 + D‖ ≤
      12 * ‖R‖ * (1 + ‖W‖) + 4 * ‖K‖ * ‖V‖ := by
  rw [ProbeEuler.unramified_marked_error R V qInv K W D
    (one_sub_ne_zero_of_norm_le_half R hR) (one_sub_ne_zero_of_norm_le_half V hV),
    div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
  have hnum : ‖R*((1-qInv)+(1-V)*(W-D))-K*V‖ ≤
      ‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖ := by
    calc
      _ ≤ ‖R*((1-qInv)+(1-V)*(W-D))‖ + ‖K*V‖ := norm_sub_le _ _
      _ = ‖R‖ * ‖(1-qInv)+(1-V)*(W-D)‖ + ‖K‖*‖V‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖R‖ * (‖1-qInv‖ + ‖1-V‖*‖W-D‖) + ‖K‖*‖V‖ := by
        gcongr
        simpa only [norm_mul] using norm_add_le (1-qInv) ((1-V)*(W-D))
      _ ≤ ‖R‖ * (2 + (1+‖V‖)*(‖W‖+‖D‖)) + ‖K‖*‖V‖ := by
        gcongr
        · calc ‖1-qInv‖ ≤ ‖(1:ℂ)‖+‖qInv‖ := norm_sub_le _ _
               _ ≤ 2 := by simp only [norm_one]; linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) V
        · exact norm_sub_le W D
  have hv := inv_one_sub_norm_le_two V hV
  have hr := inv_one_sub_norm_le_two R hR
  calc
    _ ≤ (‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖) * (2*2) := by
      gcongr
    _ ≤ 12 * ‖R‖ * (1+‖W‖) + 4*‖K‖*‖V‖ := by
      have he : 2 + (1+‖V‖)*(‖W‖+‖D‖) ≤ 3*(1+‖W‖) := by
        have : (1+‖V‖)*(‖W‖+‖D‖) ≤ (3/2:ℝ)*(‖W‖+1/2) := by gcongr ; linarith
        nlinarith [norm_nonneg W]
      nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg R)]

theorem continuedCorrection_defect_bound (V W D Pstar : ℂ)
    (hV : ‖V‖ ≤ 1/2) (hD : ‖D‖ ≤ 1/2) :
    ‖continuedCorrection V W D Pstar - 1‖ ≤
      2 * (‖D‖ * (‖V‖+‖W‖+‖V‖*‖W‖) + ‖V‖*‖W‖ +
        2*(1+‖W‖)*‖Pstar+D‖) := by
  rw [continuedCorrection_defect _ _ _ _ (one_sub_ne_zero_of_norm_le_half D hD),
    div_eq_mul_inv, norm_mul]
  have hA : ‖V+W-V*W‖ ≤ ‖V‖+‖W‖+‖V‖*‖W‖ := by
    calc
      _ ≤ ‖V+W‖+‖V*W‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_add_le V W
  have hnum : ‖D*(V+W-V*W)-V*W+(1-V)*(1-W)*(Pstar+D)‖ ≤
      ‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖ := by
    calc
      _ ≤ ‖D*(V+W-V*W)-V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := norm_add_le _ _
      _ ≤ ‖D*(V+W-V*W)‖+‖V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖D‖*‖V+W-V*W‖+‖V‖*‖W‖+‖1-V‖*‖1-W‖*‖Pstar+D‖ := by simp only [norm_mul]
      _ ≤ _ := by
        gcongr
        · calc ‖1-V‖ ≤ 1+‖V‖ := by simpa only [norm_one] using norm_sub_le (1:ℂ) V
               _ ≤ 2 := by linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) W
  calc
    _ ≤ (‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖)*2 := by
      gcongr
      exact inv_one_sub_norm_le_two D hD
    _ = _ := by ring

end SevenEighths.ProbeLocal
end

end OAI
end OAIOriginalModule0021

/-! Original module: OAI.NumberTheory.DirichletL.Detector.NormalProduct
Source SHA256: 5422bbcb8d26d29deb76d2b0f5a614720deadc0535b9928893c8fa533f107f63
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0022





namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeEuler

lemma factor_ne_zero_of_defect (a : ℂ) (ha : ‖a-1‖ ≤ 1/2) : a ≠ 0 := by
  intro h
  rw [h] at ha
  norm_num at ha

lemma norm_log_le_defect (a : ℂ) (ha : ‖a-1‖ ≤ 1/2) :
    ‖Complex.log a‖ ≤ (3/2:ℝ)*‖a-1‖ := by
  simpa only [add_sub_cancel] using Complex.norm_log_one_add_half_le_self ha

lemma log_summable_of_defect {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    Summable (fun i => ‖Complex.log (F i)‖) := by
  apply (hb.mul_left (3/2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  exact (norm_log_le_defect _ ((hF i).trans (hhalf i))).trans
    (mul_le_mul_of_nonneg_left (hF i) (by norm_num))

lemma product_eq_exp_log {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    (∏' i, F i) = Complex.exp (∑' i, Complex.log (F i)) := by
  apply HasProd.tprod_eq
  apply ((log_summable_of_defect F b hb hF hhalf).of_norm.hasSum.cexp).congr
  intro s
  apply Finset.prod_congr rfl
  intro i hi
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hF i).trans (hhalf i)))

lemma norm_log_sum_le {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2) :
    ‖∑' i, Complex.log (F i)‖ ≤ (3/2:ℝ) * ∑' i, b i := by
  have hs := log_summable_of_defect F b hb hF hhalf
  calc
    _ ≤ ∑' i, ‖Complex.log (F i)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' i, (3/2:ℝ)*b i := Summable.tsum_le_tsum
      (fun i => (norm_log_le_defect _ ((hF i).trans (hhalf i))).trans
        (mul_le_mul_of_nonneg_left (hF i) (by norm_num))) hs (hb.mul_left _)
    _ = _ := tsum_mul_left

theorem product_defect_le {ι : Type*} (F : ι → ℂ) (b : ι → ℝ)
    (hb : Summable b) (hF : ∀ i, ‖F i-1‖ ≤ b i) (hhalf : ∀ i, b i ≤ 1/2)
    (hsmall : (∑' i, b i) ≤ 1/6) : ‖(∏' i, F i)-1‖ ≤ 1/2 := by
  have hlog := norm_log_sum_le F b hb hF hhalf
  have hlog1 : ‖∑' i, Complex.log (F i)‖ ≤ 1 := by linarith
  rw [product_eq_exp_log F b hb hF hhalf]
  exact (Complex.norm_exp_sub_one_le hlog1).trans (by linarith)

theorem normalProduct_analytic {ι : Type*} (F : ι → ℂ → ℂ) (b : ι → ℝ)
    (U : Set ℂ) (hU : IsOpen U) (hb : Summable b)
    (hF : ∀ i, AnalyticOnNhd ℂ (F i) U)
    (hbound : ∀ i s, s ∈ U → ‖F i s-1‖ ≤ b i)
    (hhalf : ∀ i, b i ≤ 1/2) :
    AnalyticOnNhd ℂ (fun s => ∏' i, F i s) U := by
  have hlogs : ∀ i, DifferentiableOn ℂ (fun s => Complex.log (F i s)) U := by
    intro i
    apply (hF i).differentiableOn.clog
    intro s hs
    have hsmall : ‖F i s-1‖ < 1 := lt_of_le_of_lt ((hbound i s hs).trans (hhalf i)) (by norm_num)
    simpa only [add_sub_cancel] using Complex.mem_slitPlane_of_norm_lt_one hsmall
  have hd := Complex.differentiableOn_tsum_of_summable_norm (hb.mul_left (3/2)) hlogs hU
    (fun i s hs => (norm_log_le_defect _ ((hbound i s hs).trans (hhalf i))).trans
      (mul_le_mul_of_nonneg_left (hbound i s hs) (by norm_num)))
  apply DifferentiableOn.analyticOnNhd _ hU
  apply hd.cexp.congr
  intro s hs
  exact product_eq_exp_log (fun i => F i s) b hb (fun i => hbound i s hs) hhalf

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule0022

/-! Original module: OAI.NumberTheory.DirichletL.Endpoint
Source SHA256: 155fffbc6da45d459f2f9eada01f51dbae6b961ae8a456e603c59b13efe9baa5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0023







namespace OAI

namespace SevenEighths.Endpoint

noncomputable section

def denominator (y : ℝ) : ℝ := (37 + 34 * y) / 18

def primeWeight (y : ℝ) : ℝ := (7 + 18 * y + 8 * y ^ 2) / 9

def balanceDenominator (δ y : ℝ) : ℝ :=
  (5 / 6 - δ) * denominator y + δ * primeWeight y

def certificateWeight (y : ℝ) : ℝ := 51 + 41 * y

def balancedCutoff (δ y : ℝ) : ℝ :=
  1 + δ * primeWeight y / (2 * balanceDenominator δ y)

def balancedRowCount (δ y : ℝ) : ℝ :=
  1 - 5 / 6 + (5 / 6 - δ) * balancedCutoff δ y

def balancedExponent (δ y : ℝ) : ℝ :=
  -(1 / 48) + (2 / 3) * δ + δ * (1 / 2 - y) / 6 -
    (13 / 16) * (1 - balancedRowCount δ y)

theorem denominator_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    7 / 9 ≤ denominator y ∧ denominator y ≤ 3 := by
  dsimp [denominator]
  constructor <;> linarith

theorem primeWeight_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    7 / 9 ≤ primeWeight y ∧ primeWeight y ≤ 2 := by
  have hs := sq_nonneg y
  have ht := mul_nonneg hy0 (sub_nonneg.mpr hy1)
  dsimp [primeWeight]
  constructor <;> nlinarith

theorem balanceDenominator_bounds {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    35 / 54 ≤ balanceDenominator δ y ∧ balanceDenominator δ y ≤ 5 / 2 := by
  obtain ⟨hd0, hd1⟩ := denominator_bounds hy0 hy1
  obtain ⟨hp0, hp1⟩ := primeWeight_bounds hy0 hy1
  have ha : 0 ≤ 5 / 6 - δ := sub_nonneg.mpr hδ1
  have hl1 := mul_le_mul_of_nonneg_left hd0 ha
  have hl2 := mul_le_mul_of_nonneg_left hp0 hδ0
  have hu1 := mul_le_mul_of_nonneg_left hd1 ha
  have hu2 := mul_le_mul_of_nonneg_left (le_trans hp1 (by norm_num : (2 : ℝ) ≤ 3)) hδ0
  dsimp [balanceDenominator]
  constructor <;> nlinarith

theorem endpoint_identity (δ y : ℝ) (hJ : balanceDenominator δ y ≠ 0) :
    10368 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) =
      (3 + 5 * y) * ((4 * certificateWeight y * δ - 79) ^ 2 + 49) +
      4 * y * (4 * certificateWeight y * δ *
        ((1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y) + 265 + 3485 * y) := by
  unfold balancedExponent balancedRowCount balancedCutoff
  field_simp
  simp only [balanceDenominator, denominator, primeWeight, certificateWeight]
  ring

theorem balanced_endpoint_margin {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    (49 : ℝ) / 440640 ≤ -balancedExponent δ y := by
  obtain ⟨hJlo, hJhi⟩ := balanceDenominator_bounds hδ0 hδ1 hy0 hy1
  have hJpos : 0 < balanceDenominator δ y := by linarith
  have hvpos : 0 < certificateWeight y := by dsimp [certificateWeight]; linarith
  have hinner : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y := by
    have hp : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * δ := by positivity
    linarith
  have hrest : 0 ≤ 4 * y * (4 * certificateWeight y * δ *
      ((1 + 3 * y) * (15 + 32 * y) * δ + 9 - 13 * y) + 265 + 3485 * y) := by
    positivity
  have hsq : 0 ≤ (3 + 5 * y) * (4 * certificateWeight y * δ - 79) ^ 2 := by
    positivity
  have hid := endpoint_identity δ y (ne_of_gt hJpos)
  have hcert : 49 * (3 + 5 * y) ≤
      10368 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hid, hrest, hsq]
  have hvhi : certificateWeight y ≤ 17 * (3 + 5 * y) := by
    dsimp [certificateWeight]
    linarith
  have hscaled : 49 * certificateWeight y ≤
      176256 * certificateWeight y * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hcert, hvhi]
  have hcancel : 49 ≤ 176256 * balanceDenominator δ y * (-balancedExponent δ y) := by
    nlinarith only [hscaled, hvpos]
  have hEpos : 0 < -balancedExponent δ y := by
    by_contra hn
    have hn' : -balancedExponent δ y ≤ 0 := le_of_not_gt hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hJpos) hn'
    nlinarith only [hcancel, hp]
  have hup := mul_le_mul_of_nonneg_right hJhi (le_of_lt hEpos)
  nlinarith only [hcancel, hup]

theorem balanced_endpoint_strict {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    balancedExponent δ y < -(1 / 10000 : ℝ) := by
  have h := balanced_endpoint_margin hδ0 hδ1 hy0 hy1
  norm_num at *
  linarith

end

end SevenEighths.Endpoint

end OAI
end OAIOriginalModule0023

/-! Original module: OAI.NumberTheory.DirichletL.EulerFactors
Source SHA256: 50f6f2d96896496111c5e21f79dc8ba20ddd0dfba0421da1a83650361f239572
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0024






namespace OAI

namespace SevenEighths.EulerFactors

noncomputable section

def factor (N : ℝ) (a s : ℂ) : ℂ := 1 - a * (N : ℂ) ^ (-s)

theorem norm_term_lt_one {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : ‖a * (N : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N),
    Complex.neg_re]
  calc
    ‖a‖ * N ^ (-s.re) ≤ 1 * N ^ (-s.re) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by linarith) _)
    _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hN (neg_neg_of_pos hs)

theorem factor_ne_zero {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : factor N a s ≠ 0 := by
  intro h
  have heq : a * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hlt := norm_term_lt_one hN ha hs
  rw [heq, norm_one] at hlt
  exact (lt_irrefl _ hlt)

theorem differentiable_factor {N : ℝ} (hN : 0 < N) (a : ℂ) :
    Differentiable ℂ (factor N a) := by
  exact (differentiable_const (1 : ℂ)).sub ((differentiable_const a).mul
    (differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))))

def deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ) (a : ι → ℂ)
    (s : ℂ) : ℂ := ∏ p ∈ S, factor (N p) (a p) s

theorem deletedProduct_ne_zero {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : deletedProduct S N a s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact factor_ne_zero (hN p hp) (ha p hp) hs

theorem differentiable_deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 0 < N p) :
    Differentiable ℂ (deletedProduct S N a) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Differentiable ℂ (fun _ : ℂ => (1 : ℂ))
    exact differentiable_const _
  | @insert p S hp ih =>
    have hpN := hN p (Finset.mem_insert_self p S)
    have hSN : ∀ q ∈ S, 0 < N q := fun q hq => hN q (Finset.mem_insert_of_mem hq)
    have heq : deletedProduct (insert p S) N a =
        fun s => factor (N p) (a p) s * deletedProduct S N a s := by
      funext s
      simp only [deletedProduct, Finset.prod_insert hp]
    rw [heq]
    exact (differentiable_factor hpN (a p)).mul (ih hSN)

theorem deleted_eq_zero_iff {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {L Ldeleted : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hidentity : Ldeleted s = deletedProduct S N a s * L s) :
    Ldeleted s = 0 ↔ L s = 0 := by
  rw [hidentity, mul_eq_zero]
  exact or_iff_right (deletedProduct_ne_zero S N a hN ha hs)

end

end SevenEighths.EulerFactors

end OAI
end OAIOriginalModule0024

/-! Original module: OAI.NumberTheory.DirichletL.FiniteFourier
Source SHA256: 2bf96ef222c6a2d587e00567ca46688b378bb11547621ea3037270e0905ff84c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0025







namespace OAI

open scoped BigOperators

namespace SevenEighths.FiniteFourier

noncomputable section

variable {R : Type*} [CommRing R] [Fintype R]

def IsPrimitiveOnIdeals (χ : MulChar R ℂ) : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → ∃ u : Rˣ, (u : R) - 1 ∈ I ∧ χ (u : R) ≠ 1

theorem IsPrimitiveOnIdeals.inv {χ : MulChar R ℂ} (hχ : IsPrimitiveOnIdeals χ) :
    IsPrimitiveOnIdeals χ⁻¹ := by
  intro I hI
  obtain ⟨u, hu, hχu⟩ := hχ I hI
  refine ⟨u, hu, ?_⟩
  intro hinv
  apply hχu
  simpa only [← MulChar.star_apply', star_star, star_one] using congrArg star hinv

theorem primitiveOnIdeals_of_field {F : Type*} [Field F]
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) : IsPrimitiveOnIdeals χ := by
  intro I hI
  have htop : I = ⊤ := (Ideal.eq_bot_or_top I).resolve_left hI
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hχ
  exact ⟨u, by rw [htop]; trivial, hu⟩

def transform (ψ : AddChar R ℂ) (f : R → ℂ) (a : R) : ℂ :=
  ∑ x : R, f x * ψ (a * x)

theorem transform_inversion (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f : R → ℂ) (x : R) :
    (∑ a : R, transform ψ f a * ψ (-(a * x))) =
      (Fintype.card R : ℂ) * f x := by
  classical
  simp only [transform, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ y : R, ∑ a : R, f y * ψ (a * y) * ψ (-(a * x))) =
        ∑ y : R, f y * ∑ a : R, ψ (a * (y - x)) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    _ = (Fintype.card R : ℂ) * f x := by
      simp only [AddChar.sum_mulShift _ hψ, sub_eq_zero]
      simp [mul_ite, mul_comm]

theorem exists_nonzero_annihilator {a : R} (ha : ¬ IsUnit a) :
    ∃ b : R, b ≠ 0 ∧ a * b = 0 := by
  by_contra! h
  apply ha
  apply IsLeftRegular.isUnit_of_finite
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro b hb
  by_contra hb0
  exact h b hb0 hb

theorem exists_unit_stabilizer (χ : MulChar R ℂ) (hχ : IsPrimitiveOnIdeals χ)
    {a : R} (ha : ¬ IsUnit a) :
    ∃ u : Rˣ, a * (u : R) = a ∧ χ (u : R) ≠ 1 := by
  obtain ⟨b, hb, hab⟩ := exists_nonzero_annihilator ha
  have hI : Ideal.span ({b} : Set R) ≠ ⊥ := by
    intro hI
    have hbI := Ideal.mem_span_singleton_self b
    rw [hI] at hbI
    exact hb hbI
  obtain ⟨u, hu, hχu⟩ := hχ _ hI
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hu
  refine ⟨u, ?_, hχu⟩
  have hzero : a * ((u : R) - 1) = 0 := by
    rw [hc, ← mul_assoc, hab, zero_mul]
  linear_combination hzero

theorem gaussSum_mulShift_nonunit_eq_zero (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ)
    {a : R} (ha : ¬ IsUnit a) :
    gaussSum χ (ψ.mulShift a) = 0 := by
  obtain ⟨u, hu, hχu⟩ := exists_unit_stabilizer χ hχ ha
  have hshift : (ψ.mulShift a).mulShift (u : R) = ψ.mulShift a := by
    ext x
    simp only [AddChar.mulShift_apply, ← mul_assoc, hu]
  have heq := gaussSum_mulShift χ (ψ.mulShift a) u
  rw [hshift] at heq
  exact eq_zero_of_mul_eq_self_left hχu heq

theorem primitive_gaussSum_mulShift (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (a : R) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : IsUnit a
  · simpa only [ha.unit_spec] using gaussSum_mulShift_eq χ ψ ha.unit
  · rw [gaussSum_mulShift_nonunit_eq_zero χ hχ ψ ha,
      MulChar.map_nonunit _ ha, zero_mul]

theorem transform_primitive_character (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (a : R) :
    transform ψ χ a = χ⁻¹ a * gaussSum χ ψ := by
  exact primitive_gaussSum_mulShift χ hχ ψ a

theorem primitive_gaussSum_mul_conjugate (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * star (gaussSum χ ψ) = (Fintype.card R : ℂ) := by
  have hinv := transform_inversion ψ hψ (fun x => χ x) 1
  simp only [transform_primitive_character χ hχ, mul_one, map_one, mul_one] at hinv
  rw [star_gaussSum_eq]
  calc
    gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ =
        ∑ a : R, (χ⁻¹ a * gaussSum χ ψ) * ψ (-a) := by
      change gaussSum χ ψ * (∑ a : R, χ⁻¹ a * ψ⁻¹ a) = _
      rw [Finset.mul_sum]
      simp only [AddChar.inv_apply]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (Fintype.card R : ℂ) := hinv

theorem primitive_gaussSum_norm_sq (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card R : ℝ) := by
  apply Complex.ofReal_inj.mp
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simpa only [starRingEnd_apply, mul_comm, Complex.ofReal_natCast] using
    primitive_gaussSum_mul_conjugate χ hχ ψ hψ

theorem primitive_gaussSum_norm (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card R : ℝ) := by
  rw [← primitive_gaussSum_norm_sq χ hχ ψ hψ, Real.sqrt_sq (norm_nonneg _)]

theorem primitive_gaussSum_ne_zero (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ≠ 0 := by
  intro hzero
  have h := primitive_gaussSum_mul_conjugate χ hχ ψ hψ
  rw [hzero, zero_mul] at h
  exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) h.symm

theorem primitive_character_expansion (χ : MulChar R ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (a : R) :
    χ a = (∑ x : R, χ⁻¹ x * ψ (a * x)) / gaussSum χ⁻¹ ψ := by
  apply (eq_div_iff (primitive_gaussSum_ne_zero χ⁻¹ hχ.inv ψ hψ)).mpr
  simpa only [inv_inv, transform] using
    (transform_primitive_character χ⁻¹ hχ.inv ψ a).symm

end

end SevenEighths.FiniteFourier

end OAI
end OAIOriginalModule0025

/-! Original module: OAI.NumberTheory.DirichletL.FiniteConductor
Source SHA256: efff3ee4999760e7db7b797896074878bfe220865fe5679f96e6f23e2f8c5955
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0026








namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

theorem exists_character_factor_iff {G H : Type*} [Group G] [CommGroup H]
    [Finite H] (q : G →* H) (χ : G →* ℂˣ) :
    (∃ φ : H →* ℂˣ, φ.comp q = χ) ↔ q.ker ≤ χ.ker := by
  constructor
  · rintro ⟨φ, rfl⟩ g hg
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp hg, map_one]
  · intro hker
    have hker' : q.rangeRestrict.ker ≤ χ.ker := by
      simpa only [MonoidHom.ker_rangeRestrict] using hker
    let θ : q.range →* ℂˣ :=
      MonoidHom.liftOfSurjective q.rangeRestrict q.rangeRestrict_surjective ⟨χ, hker'⟩
    have hθ : θ.comp q.rangeRestrict = χ := MonoidHom.liftOfRightInverse_comp ..
    obtain ⟨φ, hφ⟩ := MonoidHom.domRestrict_surjective ℂ q.range θ
    refine ⟨φ, ?_⟩
    calc
      φ.comp q = (φ.domRestrict q.range).comp q.rangeRestrict := rfl
      _ = θ.comp q.rangeRestrict := by rw [← hφ]; rfl
      _ = χ := hθ

variable {R : Type*} [CommRing R] [Finite R]

def quotientUnits (I : Ideal R) : Rˣ →* (R ⧸ I)ˣ :=
  Units.map (Ideal.Quotient.mk I).toMonoidHom

def FactorsThroughIdeal (χ : MulChar R ℂ) (I : Ideal R) : Prop :=
  ∃ φ : MulChar (R ⧸ I) ℂ,
    φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom

omit [Finite R] in
theorem quotientUnits_eq_one_iff (I : Ideal R) (u : Rˣ) :
    quotientUnits I u = 1 ↔ (u : R) - 1 ∈ I := by
  rw [← Units.val_inj]
  exact Ideal.Quotient.mk_eq_one_iff_sub_mem _

theorem factorsThroughIdeal_iff (χ : MulChar R ℂ) (I : Ideal R) :
    FactorsThroughIdeal χ I ↔
      ∀ u : Rˣ, (u : R) - 1 ∈ I → χ (u : R) = 1 := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hfactor : FactorsThroughIdeal χ I ↔
      ∃ φ : (R ⧸ I)ˣ →* ℂˣ, φ.comp (quotientUnits I) = χ.toUnitHom := by
    constructor
    · rintro ⟨φ, hφ⟩
      exact ⟨φ.toUnitHom, hφ⟩
    · rintro ⟨φ, hφ⟩
      refine ⟨MulChar.ofUnitHom φ, ?_⟩
      simpa only [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq,
        Equiv.apply_symm_apply] using hφ
  rw [hfactor, exists_character_factor_iff]
  constructor
  · intro h u hu
    have hunit := h ((quotientUnits_eq_one_iff I u).mpr hu)
    exact congrArg Units.val hunit
  · intro h u hu
    apply Units.ext
    exact h u ((quotientUnits_eq_one_iff I u).mp hu)

theorem primitiveOnIdeals_iff_no_descent (χ : MulChar R ℂ) :
    IsPrimitiveOnIdeals χ ↔ ∀ I : Ideal R, I ≠ ⊥ → ¬ FactorsThroughIdeal χ I := by
  simp only [IsPrimitiveOnIdeals, factorsThroughIdeal_iff]
  push Not
  rfl

theorem FactorsThroughIdeal.mono {χ : MulChar R ℂ} {I J : Ideal R}
    (h : FactorsThroughIdeal χ I) (hJI : J ≤ I) : FactorsThroughIdeal χ J := by
  rw [factorsThroughIdeal_iff] at h ⊢
  exact fun u hu => h u (hJI hu)

theorem FactorsThroughIdeal.inv {χ : MulChar R ℂ} {I : Ideal R}
    (h : FactorsThroughIdeal χ I) : FactorsThroughIdeal χ⁻¹ I := by
  rw [factorsThroughIdeal_iff] at h ⊢
  intro u hu
  rw [← MulChar.star_apply', h u hu, star_one]

omit [Finite R] in

theorem factorization_with_source_mask (χ : MulChar R ℂ) (I : Ideal R)
    (φ : MulChar (R ⧸ I) ℂ)
    (hφ : φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom) (a : R) :
    χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  classical
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    simp only [u.isUnit, ite_true]
    exact (congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ).symm
  · simp only [ha, ite_false, MulChar.map_nonunit _ ha]

theorem exists_primitive_quotient (χ : MulChar R ℂ) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I := by
  classical
  let : Finite (Ideal R) := Finite.of_injective
    (fun I : Ideal R => (I : Set R)) SetLike.coe_injective
  have hbot : FactorsThroughIdeal χ ⊥ := by
    rw [factorsThroughIdeal_iff]
    intro u hu
    have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
    rw [hu1, map_one]
  obtain ⟨I, hI⟩ := (Set.toFinite {I : Ideal R | FactorsThroughIdeal χ I}).exists_maximal
    ⟨⊥, hbot⟩
  obtain ⟨φ, hφ⟩ := hI.1
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  refine ⟨I, φ, hφ, ?_, hI⟩
  apply (primitiveOnIdeals_iff_no_descent φ).mpr
  intro J hJ hdesc
  let K : Ideal R := J.comap (Ideal.Quotient.mk I)
  have hK : FactorsThroughIdeal χ K := by
    apply (factorsThroughIdeal_iff χ K).mpr
    intro u hu
    have huJ : ((quotientUnits I u : (R ⧸ I)ˣ) : R ⧸ I) - 1 ∈ J := by
      change Ideal.Quotient.mk I ((u : R) - 1) ∈ J at hu
      change Ideal.Quotient.mk I (u : R) - 1 ∈ J
      simpa only [map_sub, map_one] using hu
    have heq := congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ
    exact heq.symm.trans ((factorsThroughIdeal_iff φ J).mp hdesc _ huJ)
  have hIK : I ≤ K := by
    intro x hx
    change Ideal.Quotient.mk I x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J.zero_mem
  have hKI : K ≤ I := hI.2 hK hIK
  apply hJ
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hKI hx)

theorem exists_primitive_quotient_with_mask (χ : MulChar R ℂ) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      ∀ a : R, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  obtain ⟨I, φ, hφ, hprimitive, hmaximal⟩ := exists_primitive_quotient χ
  exact ⟨I, φ, hprimitive, hmaximal, factorization_with_source_mask χ I φ hφ⟩

end

end SevenEighths.FiniteConductor

end OAI
end OAIOriginalModule0026

/-! Original module: OAI.NumberTheory.DirichletL.CharacterTransport
Source SHA256: 2d856e1a80ece941771a722c15f4587845acd6fa67ff19f34684c2a69a2c4911
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0027


namespace OAI

namespace SevenEighths.CharacterTransport

open SevenEighths.FiniteFourier

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

def pullback (e : R ≃+* S) (χ : MulChar S ℂ) : MulChar R ℂ where
  toFun := fun x => χ (e x)
  map_one' := by simp
  map_mul' := by intro x y; simp
  map_nonunit' := by
    intro x hx
    apply χ.map_nonunit
    intro h
    apply hx
    simpa using h.map e.symm.toMonoidHom

@[simp] theorem pullback_apply (e : R ≃+* S) (χ : MulChar S ℂ) (x : R) :
    pullback e χ x = χ (e x) := rfl

@[simp] theorem pullback_symm (e : R ≃+* S) (χ : MulChar S ℂ) :
    pullback e.symm (pullback e χ) = χ := by
  apply MulChar.ext'
  intro x
  simp

@[simp] theorem pullback_mul (e : R ≃+* S) (χ ψ : MulChar S ℂ) :
    pullback e (χ * ψ) = pullback e χ * pullback e ψ := by
  apply MulChar.ext'
  intro x
  rfl

theorem primitive_pullback (e : R ≃+* S) (χ : MulChar S ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : IsPrimitiveOnIdeals (pullback e χ) := by
  intro I hI
  let J : Ideal S := I.comap e.symm.toRingHom
  have hJ : J ≠ ⊥ := by
    intro hJ
    apply hI
    apply le_antisymm _ bot_le
    intro x hx
    have he : e x ∈ J := by
      change e.symm (e x) ∈ I
      simpa using hx
    rw [hJ] at he
    have hx0 : x = 0 := e.injective (by simpa using he)
    exact hx0
  obtain ⟨u, hu, hχu⟩ := hχ J hJ
  let v : Rˣ := Units.map e.symm.toMonoidHom u
  refine ⟨v, ?_, ?_⟩
  · change e.symm (u : S) - 1 ∈ I
    change e.symm ((u : S) - 1) ∈ I at hu
    simpa only [map_sub, map_one] using hu
  · simpa [v, pullback] using hχu

theorem primitive_pullback_iff (e : R ≃+* S) (χ : MulChar S ℂ) :
    IsPrimitiveOnIdeals (pullback e χ) ↔ IsPrimitiveOnIdeals χ := by
  constructor
  · intro h
    simpa using primitive_pullback e.symm (pullback e χ) h
  · exact primitive_pullback e χ

end

end SevenEighths.CharacterTransport

end OAI
end OAIOriginalModule0027

/-! Original module: OAI.NumberTheory.DirichletL.ConductorBounds
Source SHA256: bfa719ff42741cdac6021c2f0e3a684daadce8a1bfe3aa4261ed03e0bb4ffafe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0028




namespace OAI

namespace SevenEighths.FiniteConductor

open SevenEighths.FiniteFourier
open scoped Classical

noncomputable section

section QuotientBounds

variable {R : Type*} [CommRing R]

theorem quotient_card_le_of_le {I J : Ideal R} [Finite (R ⧸ J)] (hJI : J ≤ I) :
    Nat.card (R ⧸ I) ≤ Nat.card (R ⧸ J) :=
  Nat.card_le_card_of_surjective _ (Ideal.Quotient.factor_surjective hJI)

theorem quotient_inf_card_le_mul (I J : Ideal R) [Finite (R ⧸ I)] [Finite (R ⧸ J)] :
    Nat.card (R ⧸ I ⊓ J) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) := by
  let f : R ⧸ I ⊓ J →+* (R ⧸ I) × (R ⧸ J) :=
    (Ideal.Quotient.factor inf_le_left).prod (Ideal.Quotient.factor inf_le_right)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.fst hx),
      Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Prod.snd hx)⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

noncomputable def quotientComapEquiv (M : Ideal R) (I : Ideal (R ⧸ M)) :
    R ⧸ I.comap (Ideal.Quotient.mk M) ≃+* (R ⧸ M) ⧸ I :=
  RingEquiv.ofBijective (Ideal.quotientMap I (Ideal.Quotient.mk M) le_rfl)
    ⟨Ideal.quotientMap_injective,
      Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective⟩

theorem quotientComapEquiv_mk (M : Ideal R) (I : Ideal (R ⧸ M)) (a : R) :
    quotientComapEquiv M I (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk I (Ideal.Quotient.mk M a) := rfl

theorem quotient_comap_card (M : Ideal R) (I : Ideal (R ⧸ M)) :
    Nat.card (R ⧸ I.comap (Ideal.Quotient.mk M)) = Nat.card ((R ⧸ M) ⧸ I) :=
  Nat.card_congr (quotientComapEquiv M I).toEquiv

end QuotientBounds

section FiniteRing

variable {R : Type*} [CommRing R] [Finite R]

theorem primitive_of_maximal_descent (χ : MulChar R ℂ) (I : Ideal R)
    (φ : MulChar (R ⧸ I) ℂ)
    (hφ : φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom)
    (hI : Maximal (FactorsThroughIdeal χ) I) : IsPrimitiveOnIdeals φ := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  apply (primitiveOnIdeals_iff_no_descent φ).mpr
  intro J hJ hdesc
  let K : Ideal R := J.comap (Ideal.Quotient.mk I)
  have hK : FactorsThroughIdeal χ K := by
    apply (factorsThroughIdeal_iff χ K).mpr
    intro u hu
    have huJ : ((quotientUnits I u : (R ⧸ I)ˣ) : R ⧸ I) - 1 ∈ J := by
      change Ideal.Quotient.mk I ((u : R) - 1) ∈ J at hu
      change Ideal.Quotient.mk I (u : R) - 1 ∈ J
      simpa only [map_sub, map_one] using hu
    have heq := congrArg (fun f : Rˣ →* ℂˣ => ((f u : ℂˣ) : ℂ)) hφ
    exact heq.symm.trans ((factorsThroughIdeal_iff φ J).mp hdesc _ huJ)
  have hIK : I ≤ K := by
    intro x hx
    change Ideal.Quotient.mk I x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J.zero_mem
  have hKI : K ≤ I := hI.2 hK hIK
  apply hJ
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hKI hx)

theorem exists_primitive_quotient_above (χ : MulChar R ℂ) (J : Ideal R)
    (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I := by
  let : Finite (Ideal R) := Finite.of_injective
    (fun I : Ideal R => (I : Set R)) SetLike.coe_injective
  obtain ⟨I, hJI, hI⟩ := Finite.exists_le_maximal hJ
  obtain ⟨φ, hφ⟩ := hI.1
  exact ⟨I, φ, hJI, hφ, primitive_of_maximal_descent χ I φ hφ hI, hI⟩

theorem exists_primitive_quotient_above_with_bound_and_mask
    (χ : MulChar R ℂ) (J : Ideal R) (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal R) (φ : MulChar (R ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      Nat.card (R ⧸ I) ≤ Nat.card (R ⧸ J) ∧
      ∀ a : R, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  let : Finite (R ⧸ J) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal⟩ := exists_primitive_quotient_above χ J hJ
  exact ⟨I, φ, hJI, hφ, hprimitive, hmaximal, quotient_card_le_of_le hJI,
    factorization_with_source_mask χ I φ hφ⟩

theorem FactorsThroughIdeal.mul {χ ψ : MulChar R ℂ} {I J : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (hψ : FactorsThroughIdeal ψ J) :
    FactorsThroughIdeal (χ * ψ) (I ⊓ J) := by
  rw [factorsThroughIdeal_iff] at hχ hψ ⊢
  intro u hu
  rw [MulChar.mul_apply, hχ u hu.1, hψ u hu.2, one_mul]

theorem exists_primitive_product_quotient_with_bound_and_mask
    (χ ψ : MulChar R ℂ) (I J : Ideal R)
    (hχ : FactorsThroughIdeal χ I) (hψ : FactorsThroughIdeal ψ J) :
    ∃ (K : Ideal R) (φ : MulChar (R ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ φ.toUnitHom.comp (quotientUnits K) = (χ * ψ).toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal (χ * ψ)) K ∧
      Nat.card (R ⧸ K) ≤ Nat.card (R ⧸ I) * Nat.card (R ⧸ J) ∧
      ∀ a : R, χ a * ψ a = if IsUnit a then φ (Ideal.Quotient.mk K a) else 0 := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  let : Finite (R ⧸ J) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := J))
  obtain ⟨K, φ, hIK, hφ, hprimitive, hmaximal, hcard, hmask⟩ :=
    exists_primitive_quotient_above_with_bound_and_mask (χ * ψ) (I ⊓ J) (hχ.mul hψ)
  exact ⟨K, φ, hIK, hφ, hprimitive, hmaximal,
    hcard.trans (quotient_inf_card_le_mul I J), hmask⟩

end FiniteRing

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]

theorem absNorm_le_of_le {I J : Ideal A} [Finite (A ⧸ J)] (hJI : J ≤ I) :
    I.absNorm ≤ J.absNorm := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    quotient_card_le_of_le hJI

theorem absNorm_inf_le_mul (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    (I ⊓ J).absNorm ≤ I.absNorm * J.absNorm := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using
    quotient_inf_card_le_mul I J

theorem absNorm_comap_eq_quotient_card (M : Ideal A) (I : Ideal (A ⧸ M)) :
    (I.comap (Ideal.Quotient.mk M)).absNorm = Nat.card ((A ⧸ M) ⧸ I) := by
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply] using quotient_comap_card M I

theorem absNorm_comap_le (M : Ideal A) [Finite (A ⧸ M)] (I : Ideal (A ⧸ M)) :
    (I.comap (Ideal.Quotient.mk M)).absNorm ≤ M.absNorm := by
  apply absNorm_le_of_le
  intro a ha
  change Ideal.Quotient.mk M a ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact I.zero_mem

theorem exists_primitive_residue_quotient_above_with_norm_and_mask
    (M : Ideal A) [Finite (A ⧸ M)] (χ : MulChar (A ⧸ M) ℂ)
    (J : Ideal (A ⧸ M)) (hJ : FactorsThroughIdeal χ J) :
    ∃ (I : Ideal (A ⧸ M)) (φ : MulChar ((A ⧸ M) ⧸ I) ℂ),
      J ≤ I ∧ φ.toUnitHom.comp (quotientUnits I) = χ.toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal χ) I ∧
      (I.comap (Ideal.Quotient.mk M)).absNorm ≤
        (J.comap (Ideal.Quotient.mk M)).absNorm ∧
      ∀ a : A ⧸ M, χ a = if IsUnit a then φ (Ideal.Quotient.mk I a) else 0 := by
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal, hcard, hmask⟩ :=
    exists_primitive_quotient_above_with_bound_and_mask χ J hJ
  refine ⟨I, φ, hJI, hφ, hprimitive, hmaximal, ?_, hmask⟩
  simpa only [absNorm_comap_eq_quotient_card] using hcard

theorem exists_primitive_residue_product_with_norm_and_mask
    (M : Ideal A) [Finite (A ⧸ M)] (χ ψ : MulChar (A ⧸ M) ℂ)
    (I J : Ideal (A ⧸ M))
    (hχ : FactorsThroughIdeal χ I) (hψ : FactorsThroughIdeal ψ J) :
    ∃ (K : Ideal (A ⧸ M)) (φ : MulChar ((A ⧸ M) ⧸ K) ℂ),
      I ⊓ J ≤ K ∧ φ.toUnitHom.comp (quotientUnits K) = (χ * ψ).toUnitHom ∧
      IsPrimitiveOnIdeals φ ∧ Maximal (FactorsThroughIdeal (χ * ψ)) K ∧
      (K.comap (Ideal.Quotient.mk M)).absNorm ≤
        (I.comap (Ideal.Quotient.mk M)).absNorm *
          (J.comap (Ideal.Quotient.mk M)).absNorm ∧
      ∀ a : A ⧸ M, χ a * ψ a = if IsUnit a then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hIK, hφ, hprimitive, hmaximal, hcard, hmask⟩ :=
    exists_primitive_product_quotient_with_bound_and_mask χ ψ I J hχ hψ
  refine ⟨K, φ, hIK, hφ, hprimitive, hmaximal, ?_, hmask⟩
  simpa only [absNorm_comap_eq_quotient_card] using hcard

end

end SevenEighths.FiniteConductor

end OAI
end OAIOriginalModule0028

/-! Original module: OAI.NumberTheory.DirichletL.ConductorPresentation
Source SHA256: 1e0d47927205772b9c006920d6c740ff682f8baa1f413808c9a227410a345f91
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0029



namespace OAI

namespace SevenEighths

namespace FiniteConductor

variable {R : Type*} [CommRing R] [Finite R]

theorem FactorsThroughIdeal.bot (χ : MulChar R ℂ) : FactorsThroughIdeal χ ⊥ := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
  rw [hu1, map_one]

theorem FactorsThroughIdeal.pow {χ : MulChar R ℂ} {I : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (n : ℕ) : FactorsThroughIdeal (χ ^ n) I := by
  rw [factorsThroughIdeal_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply_coe, hχ u hu, one_pow]

end FiniteConductor

namespace ConductorPresentation

open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical

noncomputable section

section Transport

variable {A : Type*} [CommRing A]

def quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) : MulChar (A ⧸ I.comap (Ideal.Quotient.mk M)) ℂ :=
  CharacterTransport.pullback (quotientComapEquiv M I) φ

@[simp] theorem quotientCharacter_mk (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (a : A) :
    quotientCharacter M I φ (Ideal.Quotient.mk _ a) =
      φ (Ideal.Quotient.mk I (Ideal.Quotient.mk M a)) := rfl

theorem primitive_quotientCharacter (M : Ideal A) (I : Ideal (A ⧸ M))
    (φ : MulChar ((A ⧸ M) ⧸ I) ℂ) (hφ : IsPrimitiveOnIdeals φ) :
    IsPrimitiveOnIdeals (quotientCharacter M I φ) :=
  CharacterTransport.primitive_pullback _ _ hφ

theorem source_le_comap (M : Ideal A) (I : Ideal (A ⧸ M)) :
    M ≤ I.comap (Ideal.Quotient.mk M) := by
  intro a ha
  change Ideal.Quotient.mk M a ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact I.zero_mem

theorem unit_factorization_of_mask (M K : Ideal A) (hMK : M ≤ K)
    (χ : MulChar (A ⧸ M) ℂ) (φ : MulChar (A ⧸ K) ℂ)
    (hmask : ∀ a : A, χ (Ideal.Quotient.mk M a) =
      if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0) :
    φ.toUnitHom.comp (Units.map (Ideal.Quotient.factor hMK).toMonoidHom) =
      χ.toUnitHom := by
  apply MonoidHom.ext
  intro u
  apply Units.ext
  change φ (Ideal.Quotient.factor hMK (u : A ⧸ M)) = χ (u : A ⧸ M)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : A ⧸ M)
  have h := hmask a
  simp only [ha, u.isUnit, ite_true] at h
  simpa only [← ha, Ideal.Quotient.factor_mk] using h.symm

end Transport

variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]

theorem comap_ne_bot (M : Ideal A) [Finite (A ⧸ M)] (I : Ideal (A ⧸ M)) :
    I.comap (Ideal.Quotient.mk M) ≠ ⊥ := by
  let : Finite ((A ⧸ M) ⧸ I) :=
    Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hpos : 0 < (I.comap (Ideal.Quotient.mk M)).absNorm := by
    rw [absNorm_comap_eq_quotient_card]
    exact Nat.card_pos
  intro hzero
  rw [hzero, Ideal.absNorm_bot] at hpos
  exact (lt_irrefl 0) hpos

theorem exists_primitive_presentation_above_quotient
    (M : Ideal A) [Finite (A ⧸ M)] (χ : MulChar (A ⧸ M) ℂ)
    (J : Ideal (A ⧸ M)) (hJ : FactorsThroughIdeal χ J) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ J.comap (Ideal.Quotient.mk M) ≤ K ∧ K ≠ ⊥ ∧
      IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ (J.comap (Ideal.Quotient.mk M)).absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨I, ψ, hJI, hψ, hprimitive, hmaximal, hnorm, hmask⟩ :=
    exists_primitive_residue_quotient_above_with_norm_and_mask M χ J hJ
  refine ⟨I.comap (Ideal.Quotient.mk M), quotientCharacter M I ψ,
    source_le_comap M I, Ideal.comap_mono hJI, comap_ne_bot M I,
    primitive_quotientCharacter M I ψ hprimitive, hnorm, ?_⟩
  intro a
  simpa only [quotientCharacter_mk] using hmask (Ideal.Quotient.mk M a)

theorem exists_primitive_presentation (M : Ideal A) [Finite (A ⧸ M)]
    (χ : MulChar (A ⧸ M) ℂ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ M.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨K, φ, hMK, hbotK, hK, hprimitive, hnorm, hmask⟩ :=
    exists_primitive_presentation_above_quotient M χ ⊥ (FactorsThroughIdeal.bot χ)
  refine ⟨K, φ, hMK, hK, hprimitive, ?_, hmask⟩
  simpa only [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using hnorm

theorem exists_primitive_presentation_above
    (M L : Ideal A) [Finite (A ⧸ M)] (hML : M ≤ L)
    (χ : MulChar (A ⧸ M) ℂ)
    (hL : FactorsThroughIdeal χ (L.map (Ideal.Quotient.mk M))) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ L ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ L.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  simpa only [Ideal.comap_map_mk hML] using
    exists_primitive_presentation_above_quotient M χ (L.map (Ideal.Quotient.mk M)) hL

theorem exists_primitive_product_presentation
    (M L₁ L₂ : Ideal A) [Finite (A ⧸ M)] (hML₁ : M ≤ L₁) (hML₂ : M ≤ L₂)
    (χ ψ : MulChar (A ⧸ M) ℂ)
    (hχ : FactorsThroughIdeal χ (L₁.map (Ideal.Quotient.mk M)))
    (hψ : FactorsThroughIdeal ψ (L₂.map (Ideal.Quotient.mk M))) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ L₁ ⊓ L₂ ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧
      K.absNorm ≤ L₁.absNorm * L₂.absNorm ∧
      ∀ a : A, χ (Ideal.Quotient.mk M a) * ψ (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 := by
  obtain ⟨I, φ, hJI, hφ, hprimitive, hmaximal, hnorm, hmask⟩ :=
    exists_primitive_residue_product_with_norm_and_mask M χ ψ
      (L₁.map (Ideal.Quotient.mk M)) (L₂.map (Ideal.Quotient.mk M)) hχ hψ
  refine ⟨I.comap (Ideal.Quotient.mk M), quotientCharacter M I φ,
    source_le_comap M I, ?_, comap_ne_bot M I,
    primitive_quotientCharacter M I φ hprimitive, ?_, ?_⟩
  · have h := Ideal.comap_mono (f := Ideal.Quotient.mk M) hJI
    simpa only [Ideal.comap_inf, Ideal.comap_map_mk hML₁, Ideal.comap_map_mk hML₂] using h
  · simpa only [Ideal.comap_map_mk hML₁, Ideal.comap_map_mk hML₂] using hnorm
  · intro a
    simpa only [quotientCharacter_mk] using hmask (Ideal.Quotient.mk M a)

theorem exists_primitive_power_presentation
    (M L : Ideal A) [Finite (A ⧸ M)] (hML : M ≤ L)
    (χ : MulChar (A ⧸ M) ℂ)
    (hχ : FactorsThroughIdeal χ (L.map (Ideal.Quotient.mk M))) (n : ℕ) :
    ∃ (K : Ideal A) (φ : MulChar (A ⧸ K) ℂ),
      M ≤ K ∧ L ≤ K ∧ K ≠ ⊥ ∧ IsPrimitiveOnIdeals φ ∧ K.absNorm ≤ L.absNorm ∧
      ∀ a : A, (χ ^ n) (Ideal.Quotient.mk M a) =
        if IsUnit (Ideal.Quotient.mk M a) then φ (Ideal.Quotient.mk K a) else 0 :=
  exists_primitive_presentation_above M L hML (χ ^ n) (hχ.pow n)

end

end ConductorPresentation

end SevenEighths

end OAI
end OAIOriginalModule0029

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.ChineseRemainder
Source SHA256: 8884d2987203e1ffffde1a4a69663a41915d11e8be255e6688376a167e9c21e4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0030


namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open Finset Complex

open scoped Classical

namespace GaussCRT

theorem gauss_sum_chinese_product (m n : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ)
    (ψm : AddChar (ZMod m) ℂ) (ψn : AddChar (ZMod n) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      ψm ((ZMod.chineseRemainder h x).1) *
      ψn ((ZMod.chineseRemainder h x).2)) =
      gaussSum χm ψm * gaussSum χn ψn := by
  let e := (ZMod.chineseRemainder h).toEquiv
  let F : ZMod m × ZMod n → ℂ :=
    fun z => χm z.1 * χn z.2 * ψm z.1 * ψn z.2
  calc
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      ψm ((ZMod.chineseRemainder h x).1) *
      ψn ((ZMod.chineseRemainder h x).2)) =
        ∑ x : ZMod (m * n), F (e x) := rfl
    _ = ∑ z : ZMod m × ZMod n, F z := Equiv.sum_comp e F
    _ = ∑ z : ZMod m, ∑ w : ZMod n, F (z, w) := Fintype.sum_prod_type F
    _ = gaussSum χm ψm * gaussSum χn ψn := by
      simp only [F, gaussSum]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      ring

def leftAddChar (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod m) ℂ where
  toFun z := ψ ((ZMod.chineseRemainder h).symm (z, 0))
  map_zero_eq_one' := by
    change ψ ((ZMod.chineseRemainder h).symm (0 : ZMod m × ZMod n)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ ((ZMod.chineseRemainder h).symm (z + w, 0)) =
      ψ ((ZMod.chineseRemainder h).symm (z, 0)) *
        ψ ((ZMod.chineseRemainder h).symm (w, 0))
    rw [show (z + w, (0 : ZMod n)) = (z, 0) + (w, 0) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

def rightAddChar (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) : AddChar (ZMod n) ℂ where
  toFun z := ψ ((ZMod.chineseRemainder h).symm (0, z))
  map_zero_eq_one' := by
    change ψ ((ZMod.chineseRemainder h).symm (0 : ZMod m × ZMod n)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ ((ZMod.chineseRemainder h).symm (0, z + w)) =
      ψ ((ZMod.chineseRemainder h).symm (0, z)) *
        ψ ((ZMod.chineseRemainder h).symm (0, w))
    rw [show ((0 : ZMod m), z + w) = (0, z) + (0, w) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

theorem addChar_crt_factor (m n : ℕ) (h : m.Coprime n)
    (ψ : AddChar (ZMod (m * n)) ℂ) (x : ZMod (m * n)) :
    ψ x =
      leftAddChar m n h ψ ((ZMod.chineseRemainder h x).1) *
      rightAddChar m n h ψ ((ZMod.chineseRemainder h x).2) := by
  let z := ZMod.chineseRemainder h x
  have hz : (z.1, (0 : ZMod n)) + ((0 : ZMod m), z.2) = z := by
    ext <;> simp
  calc
    ψ x = ψ ((ZMod.chineseRemainder h).symm z) := by simp [z]
    _ = ψ ((ZMod.chineseRemainder h).symm (z.1, 0) +
          (ZMod.chineseRemainder h).symm (0, z.2)) := by
          rw [← map_add, hz]
    _ = _ := by rw [AddChar.map_add_eq_mul]; rfl

theorem gauss_sum_crt (m n : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)] (h : m.Coprime n)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ)
    (ψ : AddChar (ZMod (m * n)) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) * ψ x) =
      gaussSum χm (leftAddChar m n h ψ) *
      gaussSum χn (rightAddChar m n h ψ) := by
  simp_rw [addChar_crt_factor m n h ψ]
  convert gauss_sum_chinese_product m n h χm χn
    (leftAddChar m n h ψ) (rightAddChar m n h ψ) using 1 ;
      congr 1 ; ext x ; ring

theorem crt_left_axis (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n]
    (hr : ((n * r : ℕ) : ZMod m) = 1) (z : ZMod m) :
    (ZMod.chineseRemainder h).symm (z, 0) =
      ((n * r * z.val : ℕ) : ZMod (m * n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [(ZMod.chineseRemainder h).apply_symm_apply]
  have hfst (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).1 =
      (x.cast : ZMod m) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast]
  have hsnd (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).2 =
      (x.cast : ZMod n) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast]
  apply Prod.ext
  · rw [hfst, ZMod.cast_natCast (by simp : m ∣ m * n) (n * r * z.val)]
    simp only [ Nat.cast_mul]
    rw [← Nat.cast_mul (α := ZMod m) n r, hr, one_mul,
      ZMod.natCast_zmod_val]
  · rw [hsnd, ZMod.cast_natCast (by simp : n ∣ m * n) (n * r * z.val)]
    simp [Nat.cast_mul]

theorem leftAddChar_std_apply (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hr : ((n * r : ℕ) : ZMod m) = 1) (z : ZMod m) :
    leftAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      (ZMod.stdAddChar (N := m)) ((r : ZMod m) * z) := by
  have hleft :
      leftAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      ZMod.stdAddChar ((n * r * z.val : ℕ) : ZMod (m * n)) := by
    change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (z, 0)) = _
    rw [crt_left_axis m n r h hr z]
  have hz : ((r : ZMod m) * z) = ((r * z.val : ℕ) : ZMod m) := by
    rw [← ZMod.natCast_zmod_val z]
    simp [Nat.cast_mul]
  rw [hleft, hz]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have h1 := ZMod.stdAddChar_coe (N := m * n) (j := (n * r * z.val : ℤ))
  have h2 := ZMod.stdAddChar_coe (N := m) (j := (r * z.val : ℤ))
  norm_cast at h1 h2 ⊢
  rw [h1, h2]
  congr 1
  field_simp
  simp only [Nat.cast_mul]
  ring

theorem crt_right_axis (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n]
    (hr : ((m * r : ℕ) : ZMod n) = 1) (z : ZMod n) :
    (ZMod.chineseRemainder h).symm (0, z) =
      ((m * r * z.val : ℕ) : ZMod (m * n)) := by
  apply (ZMod.chineseRemainder h).injective
  rw [(ZMod.chineseRemainder h).apply_symm_apply]
  have hfst (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).1 =
      (x.cast : ZMod m) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast]
  have hsnd (x : ZMod (m * n)) : ((ZMod.chineseRemainder h) x).2 =
      (x.cast : ZMod n) := by
        simp [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast]
  apply Prod.ext
  · rw [hfst, ZMod.cast_natCast (by simp : m ∣ m * n) (m * r * z.val)]
    simp [Nat.cast_mul]
  · rw [hsnd, ZMod.cast_natCast (by simp : n ∣ m * n) (m * r * z.val)]
    simp only [Nat.cast_mul]
    rw [← Nat.cast_mul (α := ZMod n) m r, hr, one_mul,
      ZMod.natCast_zmod_val]

theorem rightAddChar_std_apply (m n r : ℕ) (h : m.Coprime n)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (hr : ((m * r : ℕ) : ZMod n) = 1) (z : ZMod n) :
    rightAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      (ZMod.stdAddChar (N := n)) ((r : ZMod n) * z) := by
  have hright :
      rightAddChar m n h (ZMod.stdAddChar (N := m * n)) z =
      ZMod.stdAddChar ((m * r * z.val : ℕ) : ZMod (m * n)) := by
    change ZMod.stdAddChar ((ZMod.chineseRemainder h).symm (0, z)) = _
    rw [crt_right_axis m n r h hr z]
  have hz : ((r : ZMod n) * z) = ((r * z.val : ℕ) : ZMod n) := by
    rw [← ZMod.natCast_zmod_val z]
    simp [Nat.cast_mul]
  rw [hright, hz]
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have h1 := ZMod.stdAddChar_coe (N := m * n) (j := (m * r * z.val : ℤ))
  have h2 := ZMod.stdAddChar_coe (N := n) (j := (r * z.val : ℤ))
  norm_cast at h1 h2 ⊢
  rw [h1, h2]
  congr 1
  field_simp
  simp only [Nat.cast_mul]
  ring

theorem gauss_shift_cross (m n r : ℕ) [NeZero m]
    (χ : MulChar (ZMod m) ℂ)
    (hr : ((n * r : ℕ) : ZMod m) = 1) :
    gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
      χ (n : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by
  have hrprod : (n : ZMod m) * (r : ZMod m) = 1 := by
    simpa only [Nat.cast_mul] using hr
  have hur : IsUnit (r : ZMod m) :=
    IsUnit.of_mul_eq_one_right (n : ZMod m) hrprod
  have hcharprod : χ (n : ZMod m) * χ (r : ZMod m) = 1 := by
    rw [← map_mul, hrprod, map_one]
  have hshift := gaussSum_mulShift χ (ZMod.stdAddChar (N := m)) hur.unit
  have hshift' : χ (r : ZMod m) *
      gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
      gaussSum χ (ZMod.stdAddChar (N := m)) := by
    simpa only [hur.unit_spec] using hshift
  calc
    gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
        (χ (n : ZMod m) * χ (r : ZMod m)) *
          gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) := by
            rw [hcharprod, one_mul]
    _ = χ (n : ZMod m) *
          (χ (r : ZMod m) *
            gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m))) := by ring
    _ = χ (n : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by rw [hshift']

theorem gauss_sum_crt_standard (m n r s : ℕ)
    [NeZero m] [NeZero n] [NeZero (m * n)]
    (h : m.Coprime n)
    (hr : ((n * r : ℕ) : ZMod m) = 1)
    (hs : ((m * s : ℕ) : ZMod n) = 1)
    (χm : MulChar (ZMod m) ℂ) (χn : MulChar (ZMod n) ℂ) :
    (∑ x : ZMod (m * n),
      χm ((ZMod.chineseRemainder h x).1) *
      χn ((ZMod.chineseRemainder h x).2) *
      (ZMod.stdAddChar (N := m * n)) x) =
      χm (n : ZMod m) * χn (m : ZMod n) *
        gaussSum χm (ZMod.stdAddChar (N := m)) *
        gaussSum χn (ZMod.stdAddChar (N := n)) := by
  have hleft : leftAddChar m n h (ZMod.stdAddChar (N := m * n)) =
      (ZMod.stdAddChar (N := m)).mulShift (r : ZMod m) := by
    ext z
    exact leftAddChar_std_apply m n r h hr z
  have hright : rightAddChar m n h (ZMod.stdAddChar (N := m * n)) =
      (ZMod.stdAddChar (N := n)).mulShift (s : ZMod n) := by
    ext z
    exact rightAddChar_std_apply m n s h hs z
  rw [gauss_sum_crt m n h χm χn (ZMod.stdAddChar (N := m * n)),
      hleft, hright,
      gauss_shift_cross m n r χm hr,
      gauss_shift_cross n m s χn hs]
  ring

end GaussCRT

open scoped Classical

namespace IdealGaussCRT

variable {T R S : Type*} [CommRing T] [CommRing R] [CommRing S]

def leftAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar R ℂ where
  toFun z := ψ (e.symm (z, 0))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (z + w, 0)) = ψ (e.symm (z, 0)) * ψ (e.symm (w, 0))
    rw [show (z + w, (0 : S)) = (z, 0) + (w, 0) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

def rightAddChar (e : T ≃+* R × S) (ψ : AddChar T ℂ) : AddChar S ℂ where
  toFun z := ψ (e.symm (0, z))
  map_zero_eq_one' := by
    change ψ (e.symm (0 : R × S)) = 1
    rw [map_zero, AddChar.map_zero_eq_one]
  map_add_eq_mul' z w := by
    change ψ (e.symm (0, z + w)) = ψ (e.symm (0, z)) * ψ (e.symm (0, w))
    rw [show ((0 : R), z + w) = (0, z) + (0, w) by ext <;> simp,
      map_add, AddChar.map_add_eq_mul]

theorem addChar_crt_factor (e : T ≃+* R × S) (ψ : AddChar T ℂ) (x : T) :
    ψ x = leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2 := by
  let z := e x
  have hz : (z.1, (0 : S)) + ((0 : R), z.2) = z := by ext <;> simp
  calc
    ψ x = ψ (e.symm z) := by simp [z]
    _ = ψ (e.symm (z.1, 0) + e.symm (0, z.2)) := by rw [← map_add, hz]
    _ = _ := by rw [AddChar.map_add_eq_mul]; rfl

theorem gauss_sum_crt [Fintype T] [Fintype R] [Fintype S]
    (e : T ≃+* R × S) (χR : MulChar R ℂ) (χS : MulChar S ℂ)
    (ψ : AddChar T ℂ) :
    (∑ x : T, χR (e x).1 * χS (e x).2 * ψ x) =
      gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
  simp_rw [addChar_crt_factor e ψ]
  let F : R × S → ℂ := fun z =>
    χR z.1 * χS z.2 * leftAddChar e ψ z.1 * rightAddChar e ψ z.2
  calc
    (∑ x : T,
      χR (e x).1 * χS (e x).2 *
        (leftAddChar e ψ (e x).1 * rightAddChar e ψ (e x).2)) =
        ∑ x : T, F (e x) := by congr 1; ext x; simp [F]; ring
    _ = ∑ z : R × S, F z := Equiv.sum_comp e.toEquiv F
    _ = ∑ z : R, ∑ w : S, F (z, w) := Fintype.sum_prod_type F
    _ = gaussSum χR (leftAddChar e ψ) * gaussSum χS (rightAddChar e ψ) := by
      simp only [F, gaussSum]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      ring

theorem gauss_sum_ideal_crt {A : Type*} [CommRing A]
    (I J : Ideal A) (h : IsCoprime I J)
    [Fintype (A ⧸ I * J)] [Fintype (A ⧸ I)] [Fintype (A ⧸ J)]
    (χI : MulChar (A ⧸ I) ℂ) (χJ : MulChar (A ⧸ J) ℂ)
    (ψ : AddChar (A ⧸ I * J) ℂ) :
    (∑ x : A ⧸ I * J,
      χI (Ideal.Quotient.factor (Ideal.mul_le_left : I * J ≤ I) x) *
      χJ (Ideal.Quotient.factor (Ideal.mul_le_right : I * J ≤ J) x) * ψ x) =
      gaussSum χI (leftAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) *
      gaussSum χJ (rightAddChar (Ideal.quotientMulEquivQuotientProd I J h) ψ) := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  convert gauss_sum_crt e χI χJ ψ using 1
  congr 1
  ext x
  simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
    Ideal.quotientMulEquivQuotientProd_snd]

noncomputable def quotientAddChar {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) : AddChar (A ⧸ I) ℂ where
  toFun := fun x => Quotient.liftOn' x ψ (by
    intro a b hab
    have hsub : a - b ∈ I := I.quotientRel_def.mp hab
    have h := ψ.map_add_eq_mul (a - b) b
    rw [sub_add_cancel] at h
    rw [hper _ hsub, one_mul] at h
    exact h)
  map_zero_eq_one' := by
    change ψ 0 = 1
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' := by
    intro x y
    refine Quotient.inductionOn₂' x y ?_
    intro a b
    exact AddChar.map_add_eq_mul ψ a b

@[simp] theorem quotientAddChar_mk {A : Type*} [CommRing A]
    (I : Ideal A) (ψ : AddChar A ℂ)
    (hper : ∀ a : A, a ∈ I → ψ a = 1) (a : A) :
    quotientAddChar I ψ hper (Ideal.Quotient.mk I a) = ψ a := rfl

theorem principal_coprime_of_bezout {A : Type*} [CommRing A]
    {a b u v : A} (h : u * a + v * b = 1) :
    IsCoprime (Ideal.span {a}) (Ideal.span {b}) := by
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨u * a, ?_, v * b, ?_, h⟩
  · exact Ideal.mem_span_singleton.mpr ⟨u, by ring⟩
  · exact Ideal.mem_span_singleton.mpr ⟨v, by ring⟩

theorem bezout_of_principal_coprime {A : Type*} [CommRing A]
    {a b : A} (h : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    ∃ u v : A, u * a + v * b = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp h
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp hx
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hy
  refine ⟨u, v, ?_⟩
  rw [hu, hv] at hxy
  convert hxy using 1; ring

theorem crt_left_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (x : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (x * v * b) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).1 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change x - x * v * b ∈ I
    rw [Ideal.mem_span_singleton]
    refine ⟨x * u, ?_⟩
    calc
      x - x * v * b = x * (u * a + v * b) - x * v * b := by rw [hbez]; ring
      _ = a * (x * u) := by ring
  · change (e (e.symm (Ideal.Quotient.mk I x, 0))).2 =
      (e (Ideal.Quotient.mk (I * J) (x * v * b))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨x * v, by ring⟩

theorem crt_right_inverse_coordinate {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) (y : A) :
    (Ideal.quotientMulEquivQuotientProd
      (Ideal.span {a}) (Ideal.span {b})
      (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y) =
      Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) (y * u * a) := by
  let I : Ideal A := Ideal.span {a}
  let J : Ideal A := Ideal.span {b}
  let e := Ideal.quotientMulEquivQuotientProd I J
    (principal_coprime_of_bezout hbez)
  apply e.injective
  apply Prod.ext
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).1 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).1
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.Quotient.factor_mk]
    symm
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.mem_span_singleton.mpr ⟨y * u, by ring⟩
  · change (e (e.symm (0, Ideal.Quotient.mk J y))).2 =
      (e (Ideal.Quotient.mk (I * J) (y * u * a))).2
    rw [e.apply_symm_apply]
    simp only [e, Ideal.quotientMulEquivQuotientProd_snd,
      Ideal.Quotient.factor_mk]
    apply Ideal.Quotient.eq.mpr
    change y - y * u * a ∈ J
    rw [Ideal.mem_span_singleton]
    refine ⟨y * v, ?_⟩
    calc
      y - y * u * a = y * (u * a + v * b) - y * u * a := by rw [hbez]; ring
      _ = b * (y * v) := by ring

noncomputable def rawTraceChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A) : AddChar A ℂ where
  toFun x := ψ (ι x / (ι c * lam))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [map_add, add_div, AddChar.map_add_eq_mul]

theorem rawTraceChar_period {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (x : A) (hx : x ∈ Ideal.span {c}) :
    rawTraceChar ι ψ lam c x = 1 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
  rw [hy]
  change ψ (ι (c * y) / (ι c * lam)) = 1
  rw [map_mul]
  have hfrac : ι c * ι y / (ι c * lam) = ι y / lam := by
    field_simp
  rw [hfrac]
  exact hbase y

noncomputable def traceModChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    AddChar (A ⧸ Ideal.span {c}) ℂ :=
  quotientAddChar (Ideal.span {c}) (rawTraceChar ι ψ lam c)
    (rawTraceChar_period ι ψ lam c hc hlam hbase)

@[simp] theorem traceModChar_mk {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (c : A)
    (hc : ι c ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) (x : A) :
    traceModChar ι ψ lam c hc hlam hbase
      (Ideal.Quotient.mk (Ideal.span {c}) x) =
      ψ (ι x / (ι c * lam)) := rfl

noncomputable def traceProdChar {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (a b : A)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    AddChar (A ⧸ (Ideal.span {a}) * (Ideal.span {b})) ℂ :=
  quotientAddChar ((Ideal.span {a}) * (Ideal.span {b}))
    (rawTraceChar ι ψ lam (a * b)) (by
      intro x hx
      have hx' : x ∈ Ideal.span {a * b} := by
        simpa only [Ideal.span_singleton_mul_span_singleton] using hx
      exact rawTraceChar_period ι ψ lam (a * b)
        (by simpa only [map_mul] using mul_ne_zero ha hb)
        hlam hbase x hx')

@[simp] theorem traceProdChar_mk {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ) (a b : A)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) (x : A) :
    traceProdChar ι ψ lam a b ha hb hlam hbase
      (Ideal.Quotient.mk ((Ideal.span {a}) * (Ideal.span {b})) x) =
      ψ (ι x / (ι (a * b) * lam)) := rfl

theorem leftAddChar_traceProd {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    leftAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam a ha hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {a}) v) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro x
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (Ideal.Quotient.mk (Ideal.span {a}) x, 0)) =
    (traceModChar ι ψ lam a ha hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {a}) v)
      (Ideal.Quotient.mk (Ideal.span {a}) x)
  rw [crt_left_inverse_coordinate hbez x]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp

theorem rightAddChar_traceProd {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1) :
    rightAddChar
      (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez))
      (traceProdChar ι ψ lam a b ha hb hlam hbase) =
      (traceModChar ι ψ lam b hb hlam hbase).mulShift
        (Ideal.Quotient.mk (Ideal.span {b}) u) := by
  ext z
  refine Quotient.inductionOn' z ?_
  intro y
  change traceProdChar ι ψ lam a b ha hb hlam hbase
      ((Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
        (principal_coprime_of_bezout hbez)).symm
        (0, Ideal.Quotient.mk (Ideal.span {b}) y)) =
    (traceModChar ι ψ lam b hb hlam hbase).mulShift
      (Ideal.Quotient.mk (Ideal.span {b}) u)
      (Ideal.Quotient.mk (Ideal.span {b}) y)
  rw [crt_right_inverse_coordinate hbez y]
  simp only [traceProdChar_mk, AddChar.mulShift_apply, ← map_mul,
    traceModChar_mk]
  congr 1
  simp only [map_mul]
  field_simp

theorem bezout_inverse_left {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) :
    (Ideal.Quotient.mk (Ideal.span {a}) b) *
      (Ideal.Quotient.mk (Ideal.span {a}) v) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change b * v - 1 ∈ Ideal.span {a}
  rw [Ideal.mem_span_singleton]
  refine ⟨-u, ?_⟩
  calc
    b * v - 1 = b * v - (u * a + v * b) := by rw [hbez]
    _ = a * -u := by ring

theorem bezout_inverse_right {A : Type*} [CommRing A]
    {a b u v : A} (hbez : u * a + v * b = 1) :
    (Ideal.Quotient.mk (Ideal.span {b}) a) *
      (Ideal.Quotient.mk (Ideal.span {b}) u) = 1 := by
  rw [← map_mul]
  apply Ideal.Quotient.eq.mpr
  change a * u - 1 ∈ Ideal.span {b}
  rw [Ideal.mem_span_singleton]
  refine ⟨-v, ?_⟩
  calc
    a * u - 1 = a * u - (u * a + v * b) := by rw [hbez]
    _ = b * -v := by ring

theorem gauss_shift_bezout_left {A : Type*} [CommRing A]
    {a b u v : A} [Fintype (A ⧸ Ideal.span {a})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (ψ : AddChar (A ⧸ Ideal.span {a}) ℂ) :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {a}) v)) =
      χ (Ideal.Quotient.mk (Ideal.span {a}) b) * gaussSum χ ψ := by
  let mb := Ideal.Quotient.mk (Ideal.span {a}) b
  let mv := Ideal.Quotient.mk (Ideal.span {a}) v
  have hprod : mb * mv = 1 := bezout_inverse_left hbez
  have hu : IsUnit mv := IsUnit.of_mul_eq_one_right mb hprod
  have hχ : χ mb * χ mv = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mv * gaussSum χ (ψ.mulShift mv) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mv) =
        (χ mb * χ mv) * gaussSum χ (ψ.mulShift mv) := by rw [hχ, one_mul]
    _ = χ mb * (χ mv * gaussSum χ (ψ.mulShift mv)) := by ring
    _ = χ mb * gaussSum χ ψ := by rw [hshift']

theorem gauss_shift_bezout_right {A : Type*} [CommRing A]
    {a b u v : A} [Fintype (A ⧸ Ideal.span {b})]
    (hbez : u * a + v * b = 1)
    (χ : MulChar (A ⧸ Ideal.span {b}) ℂ)
    (ψ : AddChar (A ⧸ Ideal.span {b}) ℂ) :
    gaussSum χ (ψ.mulShift (Ideal.Quotient.mk (Ideal.span {b}) u)) =
      χ (Ideal.Quotient.mk (Ideal.span {b}) a) * gaussSum χ ψ := by
  let ma := Ideal.Quotient.mk (Ideal.span {b}) a
  let mu := Ideal.Quotient.mk (Ideal.span {b}) u
  have hprod : ma * mu = 1 := bezout_inverse_right hbez
  have hu : IsUnit mu := IsUnit.of_mul_eq_one_right ma hprod
  have hχ : χ ma * χ mu = 1 := by rw [← map_mul, hprod, map_one]
  have hshift := gaussSum_mulShift χ ψ hu.unit
  have hshift' : χ mu * gaussSum χ (ψ.mulShift mu) = gaussSum χ ψ := by
    simpa only [hu.unit_spec] using hshift
  calc
    gaussSum χ (ψ.mulShift mu) =
        (χ ma * χ mu) * gaussSum χ (ψ.mulShift mu) := by rw [hχ, one_mul]
    _ = χ ma * (χ mu * gaussSum χ (ψ.mulShift mu)) := by ring
    _ = χ ma * gaussSum χ ψ := by rw [hshift']

theorem gauss_sum_trace_crt {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    {a b u v : A} (hbez : u * a + v * b = 1)
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})]
    [Fintype (A ⧸ Ideal.span {b})]
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (χa : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (A ⧸ Ideal.span {b}) ℂ) :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      traceProdChar ι ψ lam a b ha hb hlam hbase x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (traceModChar ι ψ lam a ha hlam hbase) *
      gaussSum χb (traceModChar ι ψ lam b hb hlam hbase) := by
  let e := Ideal.quotientMulEquivQuotientProd (Ideal.span {a})
    (Ideal.span {b}) (principal_coprime_of_bezout hbez)
  have h := gauss_sum_ideal_crt (Ideal.span {a}) (Ideal.span {b})
    (principal_coprime_of_bezout hbez) χa χb
    (traceProdChar ι ψ lam a b ha hb hlam hbase)
  rw [leftAddChar_traceProd ι ψ lam hbez ha hb hlam hbase,
      rightAddChar_traceProd ι ψ lam hbez ha hb hlam hbase,
      gauss_shift_bezout_left hbez χa (traceModChar ι ψ lam a ha hlam hbase),
      gauss_shift_bezout_right hbez χb (traceModChar ι ψ lam b hb hlam hbase)] at h
  calc
    _ = (χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
          gaussSum χa (traceModChar ι ψ lam a ha hlam hbase)) *
        (χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
          gaussSum χb (traceModChar ι ψ lam b hb hlam hbase)) := h
    _ = _ := by ring

theorem gauss_sum_trace_crt_of_coprime {A : Type*} [CommRing A]
    (ι : A →+* ℂ) (ψ : AddChar ℂ ℂ) (lam : ℂ)
    (a b : A)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (A ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (A ⧸ Ideal.span {a})]
    [Fintype (A ⧸ Ideal.span {b})]
    (ha : ι a ≠ 0) (hb : ι b ≠ 0) (hlam : lam ≠ 0)
    (hbase : ∀ x : A, ψ (ι x / lam) = 1)
    (χa : MulChar (A ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (A ⧸ Ideal.span {b}) ℂ) :
    (∑ x : A ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      traceProdChar ι ψ lam a b ha hb hlam hbase x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (traceModChar ι ψ lam a ha hlam hbase) *
      gaussSum χb (traceModChar ι ψ lam b hb hlam hbase) := by
  obtain ⟨u, v, hbez⟩ := bezout_of_principal_coprime hcop
  exact gauss_sum_trace_crt ι ψ lam hbez ha hb hlam hbase χa χb

end IdealGaussCRT

end

end OAI
end OAIOriginalModule0030

/-! Original module: OAI.NumberTheory.DirichletL.HeathBrownIteration
Source SHA256: 4a8f3bf7c261b5322473146b07968a3762951df575659e95f03ec0f37a6d784c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0031







namespace OAI

namespace SevenEighths.HeathBrownIteration

noncomputable section

def step (x : ℝ) : ℝ := (6 * x - 4) / (3 * x - 1)

theorem step_sub (x : ℝ) (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 = 2 * (x - 4 / 3) / (3 * x - 1) := by
  have hd : 3 * x - 1 ≠ 0 := by linarith
  apply (eq_div_iff hd).mpr
  unfold step
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring

theorem step_gt {x : ℝ} (hx : (4 / 3 : ℝ) < x) :
    (4 / 3 : ℝ) < step x := by
  have h := step_sub x hx.le
  have hp : 0 < 2 * (x - 4 / 3) / (3 * x - 1) :=
    div_pos (mul_pos (by norm_num) (sub_pos.mpr hx)) (by linarith)
  linarith

theorem step_error_le {x : ℝ} (hx : (4 / 3 : ℝ) ≤ x) :
    step x - 4 / 3 ≤ (2 / 3 : ℝ) * (x - 4 / 3) := by
  rw [step_sub x hx]
  apply (div_le_iff₀ (by linarith : 0 < 3 * x - 1)).mpr
  nlinarith [sq_nonneg (x - 4 / 3)]

theorem step_lt {x : ℝ} (hx : (4 / 3 : ℝ) < x) : step x < x := by
  have h := step_error_le hx.le
  linarith

def exponent : ℕ → ℝ
  | 0 => 2
  | n + 1 => step (exponent n)

theorem exponent_bounds (n : ℕ) :
    (4 / 3 : ℝ) < exponent n ∧ exponent n ≤ 2 := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    exact ⟨step_gt ih.1, (step_lt ih.1).le.trans ih.2⟩

theorem exponent_error_le (n : ℕ) :
    exponent n - 4 / 3 ≤ (2 / 3 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num [exponent]
  | succ n ih =>
    calc
      exponent (n + 1) - 4 / 3 ≤ (2 / 3 : ℝ) * (exponent n - 4 / 3) :=
        step_error_le (exponent_bounds n).1.le
      _ ≤ (2 / 3 : ℝ) * (2 / 3 : ℝ) ^ (n + 1) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 / 3 : ℝ) ^ (n + 1 + 1) := by rw [pow_succ]; ring

theorem exists_exponent_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, exponent n < 4 / 3 + ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 / 3 : ℝ) < 1)
  refine ⟨n, ?_⟩
  have hp : (2 / 3 : ℝ) ^ (n + 1) ≤ (2 / 3 : ℝ) ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (by norm_num) _) (by norm_num)
  have he := exponent_error_le n
  linarith

theorem finite_improvement {P : ℝ → Prop} (hstart : P 2)
    (himprove : ∀ x : ℝ, (4 / 3 : ℝ) < x → x ≤ 2 → P x → P (step x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, (4 / 3 : ℝ) < x ∧ x ≤ 2 ∧ x < 4 / 3 + ε ∧ P x := by
  have hp (n : ℕ) : P (exponent n) := by
    induction n with
    | zero => exact hstart
    | succ n ih => exact himprove _ (exponent_bounds n).1 (exponent_bounds n).2 ih
  obtain ⟨n, hn⟩ := exists_exponent_lt hε
  exact ⟨exponent n, (exponent_bounds n).1, (exponent_bounds n).2, hn, hp n⟩

end

end SevenEighths.HeathBrownIteration

end OAI
end OAIOriginalModule0031

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialMarkedReserve
Source SHA256: 80b2747c502a06196d92003f14cf587dfc08fddcd462865a171d5a82976b038d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0032


namespace OAI

namespace SevenEighths.InverseInitialMarkedReserve

theorem exists_reserve (εm:ℝ)(hε:0<εm):
    ∃ρ gap η τ π eps loss:ℝ,
      0<ρ ∧ ρ≤1/4 ∧ ρ≤εm/4 ∧
      0<gap ∧ 2*gap≤ρ ∧
      0<η ∧ η≤1/7 ∧ η≤gap/50 ∧
      0<τ ∧ τ≤gap/50 ∧ 0<π ∧ 0<eps ∧ 0<loss ∧
      ρ+15*η+π+eps+loss≤εm:=by
  let ρ:=min (εm/4) (1/4)
  have hρ:0<ρ:=lt_min (by linarith) (by norm_num)
  have hρa:ρ≤εm/4:=min_le_left _ _
  have hρb:ρ≤1/4:=min_le_right _ _
  refine ⟨ρ,ρ/4,ρ/400,ρ/400,ρ/16,ρ/16,ρ/16,hρ,hρb,hρa,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem shifted_capacity (ρ gap η r r' ell G:ℝ)
    (hρ:0<ρ)(hρmax:ρ≤1/4)(hgap:2*gap≤ρ)
    (hη:0<η)(hηmax:η≤1/7)(hr:0≤r)(hell:0≤ell)
    (_hG:0≤G)(hGmax:G≤ell)(hlo:r-η≤r')(hhi:r'≤r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3):
    0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤r'+ell-2*G ∧
      r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧
      r'+ell+7*η≤2:=by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

end SevenEighths.InverseInitialMarkedReserve

end OAI
end OAIOriginalModule0032

/-! Original module: OAI.NumberTheory.DirichletL.LogarithmicControl
Source SHA256: d9d50528ba706c6b8704ebeb1b82232dd78bf382db3617e52fabf7ae17726bd1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0033









namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter Metric Complex

namespace SevenEighths.LogarithmicControl

theorem differentiableOn_of_exp_eq {U : Set ℂ} (hU : IsOpen U)
    {L g : ℂ → ℂ} (hL : DifferentiableOn ℂ L U)
    (hg : ContinuousOn g U) (he : EqOn (Complex.exp ∘ g) L U) :
    DifferentiableOn ℂ g U := by
  intro z hz
  have hgc : ContinuousAt g z := (hg z hz).continuousAt (hU.mem_nhds hz)
  have hLc : DifferentiableAt ℂ L z := (hL z hz).differentiableAt (hU.mem_nhds hz)
  have hs := Complex.hasStrictDerivAt_exp (g z)
  let inv := hs.localInverse Complex.exp (Complex.exp (g z)) (g z)
    (Complex.exp_ne_zero _)
  have hi : DifferentiableAt ℂ inv (L z) := by
    rw [← he hz]
    exact (hs.to_localInverse (Complex.exp_ne_zero _)).hasDerivAt.differentiableAt
  have heq : (fun w ↦ inv (L w)) =ᶠ[𝓝 z] g := by
    have hlocal := hgc.eventually (hs.eventually_left_inverse (Complex.exp_ne_zero _))
    filter_upwards [hlocal, hU.mem_nhds hz] with w hw hwU
    simpa only [← he hwU, Function.comp_apply] using hw
  exact ((hi.comp z hLc).congr_of_eventuallyEq heq.symm).differentiableWithinAt

theorem exists_holomorphic_log {L : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R))
    (h0 : ∀ z ∈ ball c R, L z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) L (ball c R) := by
  let : ContractibleSpace (ball c R) := contractibleSpace_ball hR
  have hsc : IsSimplyConnected (ball c R) := by
    change SimplyConnectedSpace (ball c R)
    infer_instance
  obtain ⟨g, hg, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc
    isOpen_ball hL.continuousOn (by
      rintro ⟨z, hz, heq⟩
      exact h0 z hz heq)
  exact ⟨g, differentiableOn_of_exp_eq isOpen_ball hL hg he, he⟩

theorem exists_holomorphic_log_normalized {L : ℂ → ℂ} {c m : ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball c R))
    (h0 : ∀ z ∈ ball c R, L z ≠ 0) (hm : Complex.exp m = L c) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      EqOn (Complex.exp ∘ g) L (ball c R) ∧ g c = m := by
  obtain ⟨g, hg, he⟩ := exists_holomorphic_log hR hL h0
  refine ⟨fun z ↦ g z + (m - g c), hg.add_const _, ?_, by simp⟩
  intro z hz
  change Complex.exp (g z + (m - g c)) = L z
  have hez : Complex.exp (g z) = L z := he hz
  have hec : Complex.exp (g c) = L c := he (mem_ball_self hR)
  rw [Complex.exp_add, Complex.exp_sub, hm, hez,
    hec, div_self (h0 c (mem_ball_self hR)), mul_one]

theorem log_eqOn_of_eq_center {g h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) (hh : DifferentiableOn ℂ h (ball c r))
    (he : EqOn (Complex.exp ∘ g) (Complex.exp ∘ h) (ball c r)) (hc : g c = h c) :
    EqOn g h (ball c r) := by
  have hcm : c ∈ ball c r := mem_ball_self hr
  have hgc := (hg.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hhc := (hh.continuousOn c hcm).continuousAt (isOpen_ball.mem_nhds hcm)
  have hs := Complex.hasStrictDerivAt_exp (g c)
  have hleft := hs.eventually_left_inverse (Complex.exp_ne_zero _)
  have hgleft := hgc.eventually hleft
  have hhc' : Tendsto h (𝓝 c) (𝓝 (g c)) := by
    rw [hc]
    exact hhc.tendsto
  have hhleft := hhc'.eventually hleft
  have heq : g =ᶠ[𝓝 c] h := by
    filter_upwards [hgleft, hhleft, isOpen_ball.mem_nhds hcm] with z hz1 hz2 hz
    rw [← hz1, ← hz2]
    exact congrArg _ (he hz)
  exact (hg.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq
    (hh.analyticOnNhd isOpen_ball) (convex_ball c r).isPreconnected hcm heq

theorem borel_caratheodory_closedBall {g : ℂ → ℂ} {c : ℂ} {r R M A : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 < M) (hA : 0 ≤ A)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hRe : ∀ z ∈ ball c R, (g z).re ≤ M) (hc : ‖g c‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ 2 * M * r / (R - r) + A * (R + r) / (R - r) := by
  have hzn : ‖z - c‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hzR : ‖z - c‖ < R := hzn.trans_lt hrR
  have hRp : 0 < R := hr.trans_lt hrR
  have hg' : DifferentiableOn ℂ (fun w ↦ g (c + w)) (ball 0 R) := by
    apply hg.comp ((differentiable_const c).add differentiable_id).differentiableOn
    intro w hw
    simpa [mem_ball, dist_eq_norm] using hw
  have hb := Complex.borelCaratheodory hM hg' (fun w hw ↦ hRe _ (by
    simpa [mem_ball, dist_eq_norm] using hw)) (hr.trans_lt hrR)
    (show z - c ∈ ball 0 R by simpa using hzR)
  simp only [add_sub_cancel, add_zero] at hb
  refine hb.trans ?_
  apply add_le_add
  · gcongr
  · gcongr

theorem three_circles {g : ℂ → ℂ} {c z : ℂ} {r R S A B : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRS : R < S)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B)
    (hzr : r ≤ ‖z - c‖) (hzR : ‖z - c‖ ≤ R) :
    ‖g z‖ ≤ A ^ (1 - (Real.log ‖z - c‖ - Real.log r) /
      (Real.log R - Real.log r)) *
      B ^ ((Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)) := by
  let F : ℂ → ℂ := fun w ↦ g (c + Complex.exp w)
  have hRp : 0 < R := hr.trans hrR
  have hlog : Real.log r < Real.log R := Real.log_lt_log hr hrR
  have hmap (w : ℂ) (hw : w.re ≤ Real.log R) : c + Complex.exp w ∈ closedBall c R := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
    exact (Real.exp_le_exp.mpr hw).trans_eq (Real.exp_log hRp)
  have hclosed : closure (HadamardThreeLines.verticalStrip (Real.log r) (Real.log R)) ⊆
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R) := by
    apply closure_minimal
    · intro w hw
      exact ⟨hw.1.le, hw.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hd : DiffContOnCl ℂ F
      (HadamardThreeLines.verticalStrip (Real.log r) (Real.log R)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    have hm := hmap w (hclosed hw).2
    have hm' : c + Complex.exp w ∈ ball c S :=
      closedBall_subset_ball hRS hm
    exact ((hg _ hm').differentiableAt (isOpen_ball.mem_nhds hm')).comp w
      ((differentiableAt_const c).add (Complex.differentiable_exp w)) |>.differentiableWithinAt
  have hbound : BddAbove ((norm ∘ F) ''
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hb _ (hmap w hw.2)
  have hzn : 0 < ‖z - c‖ := hr.trans_le hzr
  have hz0 : z - c ≠ 0 := norm_pos_iff.mp hzn
  have hw : Complex.log (z - c) ∈
      HadamardThreeLines.verticalClosedStrip (Real.log r) (Real.log R) := by
    change Real.log r ≤ (Complex.log (z - c)).re ∧
      (Complex.log (z - c)).re ≤ Real.log R
    simp only [Complex.log_re]
    exact ⟨Real.log_le_log hr hzr, Real.log_le_log hzn hzR⟩
  have h := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    hlog hw hd hbound (a := A) (b := B) ?_ ?_
  · simpa [F, Complex.exp_log hz0, Complex.log_re] using h
  · intro w hw
    apply ha
    simp only [mem_preimage, mem_singleton_iff] at hw
    simp [mem_closedBall, dist_eq_norm, hw, Complex.norm_exp, Real.exp_log hr]
  · intro w hw
    exact hb _ (hmap w (le_of_eq hw))

theorem three_circles_power_bound {g : ℂ → ℂ} {c z : ℂ} {r ρ R S A B T : ℝ}
    (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R) (hRS : R < S)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c S))
    (ha : ∀ w ∈ closedBall c r, ‖g w‖ ≤ A)
    (hb : ∀ w ∈ closedBall c R, ‖g w‖ ≤ B * T)
    (hz : z ∈ closedBall c ρ) :
    ‖g z‖ ≤ A * B * T ^ ((Real.log ρ - Real.log r) /
      (Real.log R - Real.log r)) := by
  let θ := (Real.log ρ - Real.log r) / (Real.log R - Real.log r)
  have hlogR : 0 < Real.log R - Real.log r :=
    sub_pos.mpr (Real.log_lt_log hr (hrρ.trans hρR))
  have hθ0 : 0 ≤ θ := div_nonneg
    (sub_nonneg.mpr (Real.log_le_log hr hrρ.le)) hlogR.le
  have hθ1 : θ ≤ 1 := (div_le_one hlogR).mpr (by
    linarith [Real.log_le_log (hr.trans hrρ) hρR.le])
  have hzn : ‖z - c‖ ≤ ρ := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hBp : 0 ≤ B := zero_le_one.trans hB
  have hTp : 0 ≤ T := zero_le_one.trans hT
  have hp1 : 1 ≤ T ^ θ := Real.one_le_rpow hT hθ0
  by_cases hzr : ‖z - c‖ ≤ r
  · have hgz := ha z (by simpa [mem_closedBall, dist_eq_norm] using hzr)
    exact hgz.trans (by nlinarith [mul_le_mul hB hp1 zero_le_one hBp])
  · have hzr' : r ≤ ‖z - c‖ := (lt_of_not_ge hzr).le
    have hzx : 0 < ‖z - c‖ := hr.trans_le hzr'
    let x := (Real.log ‖z - c‖ - Real.log r) / (Real.log R - Real.log r)
    have hx0 : 0 ≤ x := div_nonneg
      (sub_nonneg.mpr (Real.log_le_log hr hzr')) hlogR.le
    have hxθ : x ≤ θ := (div_le_div_iff_of_pos_right hlogR).mpr (by
      linarith [Real.log_le_log hzx hzn])
    have hx1 : x ≤ 1 := hxθ.trans hθ1
    have h := three_circles hr (hrρ.trans hρR) hRS hg ha hb hzr' (hzn.trans hρR.le)
    have hAa : A ^ (1 - x) ≤ A := by
      simpa using Real.rpow_le_rpow_of_exponent_le hA (show 1 - x ≤ 1 by linarith)
    have hBb : B ^ x ≤ B := by
      simpa using Real.rpow_le_rpow_of_exponent_le hB hx1
    have hTT : T ^ x ≤ T ^ θ := Real.rpow_le_rpow_of_exponent_le hT hxθ
    calc
      ‖g z‖ ≤ A ^ (1 - x) * (B * T) ^ x := h
      _ = A ^ (1 - x) * (B ^ x * T ^ x) := by rw [Real.mul_rpow hBp hTp]
      _ ≤ A * (B * T ^ θ) := mul_le_mul hAa
        (mul_le_mul hBb hTT (Real.rpow_nonneg hTp _) hBp)
        (by positivity) hAp
      _ = A * B * T ^ θ := by ring

def uniformTheta (e : ℝ) : ℝ := 1 - Real.log (1 + e) / Real.log (200 / 49)

theorem uniformTheta_mem {e : ℝ} (he : 0 < e) (he' : e < 1 / 1000) :
    0 < uniformTheta e ∧ uniformTheta e < 1 := by
  have hD : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hn : 0 < Real.log (1 + e) := Real.log_pos (by linarith)
  have hnD : Real.log (1 + e) < Real.log (200 / 49) :=
    Real.log_lt_log (by linarith) (by linarith)
  unfold uniformTheta
  constructor
  · linarith [(div_lt_one hD).mpr hnD]
  · linarith [div_pos hn hD]

theorem three_circles_exponent_uniform {a e : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) :
    (Real.log (2 - a - 6 * e) - Real.log (49 / 100)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) ≤ uniformTheta e := by
  have hr : (0 : ℝ) < 49 / 100 := by norm_num
  have h6 : (49 / 100 : ℝ) < 2 - a - 6 * e := by linarith
  have h4 : (49 / 100 : ℝ) < 2 - a - 4 * e := by linarith
  have h6p : 0 < 2 - a - 6 * e := hr.trans h6
  have h4p : 0 < 2 - a - 4 * e := hr.trans h4
  have hep : 0 < 1 + e := by linarith
  have hD : 0 < Real.log (2 - a - 4 * e) - Real.log (49 / 100) :=
    sub_pos.mpr (Real.log_lt_log hr h4)
  have hU : 0 < Real.log (200 / 49) := Real.log_pos (by norm_num)
  have hDU : Real.log (2 - a - 4 * e) - Real.log (49 / 100) ≤
      Real.log (200 / 49) := by
    rw [← Real.log_div h4p.ne' hr.ne']
    apply Real.log_le_log (div_pos h4p hr)
    apply (div_le_iff₀ hr).mpr
    norm_num
    linarith
  have hprod : (2 - a - 6 * e) * (1 + e) ≤ 2 - a - 4 * e := by
    have : 2 - a - 6 * e ≤ 2 := by linarith
    nlinarith
  have hdiff : Real.log (1 + e) ≤ Real.log (2 - a - 4 * e) -
      Real.log (2 - a - 6 * e) := by
    have h := Real.log_le_log (mul_pos h6p hep) hprod
    rw [Real.log_mul h6p.ne' hep.ne'] at h
    linarith
  have hfrac : Real.log (1 + e) / Real.log (200 / 49) ≤
      (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
      (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
    gcongr
    exact (Real.log_pos (by linarith : 1 < 1 + e)).le.trans hdiff
  calc
    _ = 1 - (Real.log (2 - a - 4 * e) - Real.log (2 - a - 6 * e)) /
        (Real.log (2 - a - 4 * e) - Real.log (49 / 100)) := by
      apply eq_sub_iff_add_eq.mpr
      rw [← add_div]
      convert div_self hD.ne' using 1
      ring
    _ ≤ uniformTheta e := sub_le_sub_left hfrac 1

theorem exp_sublinear_le {θ K ε : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1)
    (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ x : ℝ, 1 ≤ x →
      Real.exp (K * x ^ θ) ≤ D * Real.exp (ε * x) := by
  have ht : Tendsto (fun x : ℝ ↦ K * x ^ (-(1 - θ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - θ)).const_mul K
  obtain ⟨X, hX⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  let Y := max 1 X
  refine ⟨Real.exp (K * Y ^ θ), Real.exp_pos _, ?_⟩
  intro x hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hYp : 0 < Y := zero_lt_one.trans_le (le_max_left _ _)
  by_cases hxy : x ≤ Y
  · have h1 : Real.exp (K * x ^ θ) ≤ Real.exp (K * Y ^ θ) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hxp.le hxy hθ) hK
    exact h1.trans (le_mul_of_one_le_right (Real.exp_pos _).le
      (Real.one_le_exp (by positivity)))
  · have hlarge := hX x ((le_max_right 1 X).trans (lt_of_not_ge hxy).le)
    have heq : K * x ^ θ = (K * x ^ (-(1 - θ))) * x := by
      have hp := Real.rpow_add hxp (-(1 - θ)) 1
      rw [Real.rpow_one] at hp
      rw [mul_assoc, ← hp]
      congr 2
      ring
    have hlin : K * x ^ θ ≤ ε * x := by
      rw [heq]
      exact mul_le_mul_of_nonneg_right hlarge.le hxp.le
    exact (Real.exp_le_exp.mpr hlin).trans (le_mul_of_one_le_left
      (Real.exp_pos _).le (Real.one_le_exp (mul_nonneg hK (Real.rpow_nonneg hYp.le _))))

def outerConstant (e A M : ℝ) : ℝ := (4 * M + 4 * A) / e

theorem outerConstant_ge_one {e A M : ℝ} (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) : 1 ≤ outerConstant e A M := by
  unfold outerConstant
  apply (le_div_iff₀ he).mpr
  nlinarith

theorem outer_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 4 * e)) :
    ‖g z‖ ≤ outerConstant e A M * T := by
  have hAp : 0 ≤ A := zero_le_one.trans hA
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hb := borel_caratheodory_closedBall (by linarith : 0 ≤ 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 3 * e) (mul_pos hMp hTp) hAp
    (hg.mono (ball_subset_ball (by linarith))) hRe hc hz
  have hgap : 2 - a - 3 * e - (2 - a - 4 * e) = e := by ring
  rw [hgap] at hb
  have hfirst : 2 * (M * T) * (2 - a - 4 * e) ≤ 4 * M * T := by
    nlinarith [mul_le_mul_of_nonneg_left
      (show 2 - a - 4 * e ≤ 2 by linarith) (show 0 ≤ 2 * M * T by positivity)]
  have hsecond : A * (2 - a - 3 * e + (2 - a - 4 * e)) ≤ 4 * A * T := by
    have h1 := mul_le_mul_of_nonneg_left
      (show 2 - a - 3 * e + (2 - a - 4 * e) ≤ 4 by linarith) hAp
    nlinarith [mul_le_mul_of_nonneg_left hT (show 0 ≤ 4 * A by positivity)]
  refine hb.trans ?_
  rw [← add_div]
  unfold outerConstant
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right he).mpr (by nlinarith)

theorem inner_log_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hin : ∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c (2 - a - 6 * e)) :
    ‖g z‖ ≤ A * outerConstant e A M * T ^ uniformTheta e := by
  have hB := outerConstant_ge_one he he' hA hM
  have hb : ∀ w ∈ closedBall c (2 - a - 4 * e), ‖g w‖ ≤ outerConstant e A M * T :=
    fun w hw ↦ outer_log_bound ha ha' he he' hA hM hT hg hRe
      (hin c (mem_closedBall_self (by norm_num))) hw
  have h := three_circles_power_bound (by norm_num : (0 : ℝ) < 49 / 100)
    (by linarith : 49 / 100 < 2 - a - 6 * e)
    (by linarith : 2 - a - 6 * e < 2 - a - 4 * e)
    (by linarith : 2 - a - 4 * e < 2 - a - 2 * e)
    hA hB hT hg hin hb hz
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT (three_circles_exponent_uniform ha ha' he he'))
    (by positivity))

theorem logarithm_derivative_bound {g : ℂ → ℂ} {c : ℂ} {a e A M T : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000)
    (hA : 1 ≤ A) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hg : DifferentiableOn ℂ g (ball c (2 - a - 2 * e)))
    (hRe : ∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * T)
    (hc : ‖g c‖ ≤ A) {z : ℂ} (hz : z ∈ closedBall c (2 - a - 8 * e)) :
    ‖deriv g z‖ ≤ (outerConstant e A M / (2 * e)) * T := by
  have hzn : dist z c ≤ 2 - a - 8 * e := hz
  have hsub : closedBall z (2 * e) ⊆ ball c (2 - a - 2 * e) := by
    intro w hw
    have hw' : dist w z ≤ 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c < _
    linarith
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith : 0 < 2 * e)
    (hg.diffContOnCl_ball hsub) (C := outerConstant e A M * T) ?_
  · exact h.trans_eq (by ring)
  · intro w hw
    apply outer_log_bound ha ha' he he' hA hM hT hg hRe hc
    have hw' : dist w z = 2 * e := hw
    have hdist := dist_triangle w z c
    change dist w c ≤ _
    linarith

theorem zero_free_disk_logarithm {L E : ℂ → ℂ} {c : ℂ} {a e A M C : ℝ}
    (ha' : a ≤ 1) (he : 0 < e) (he' : e < 1 / 1000) (hC : 0 < C)
    (hL : DifferentiableOn ℂ L (ball c (2 - a - 2 * e)))
    (h0 : ∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0)
    (hpoly : ∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M)
    (hE : DifferentiableOn ℂ E (ball c (1 / 2)))
    (hEL : EqOn (Complex.exp ∘ E) L (ball c (1 / 2)))
    (hEb : ∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c (2 - a - 2 * e)) ∧
      EqOn (Complex.exp ∘ g) L (ball c (2 - a - 2 * e)) ∧
      (∀ z ∈ closedBall c (49 / 100), ‖g z‖ ≤ A) ∧
      (∀ z ∈ ball c (2 - a - 3 * e), (g z).re ≤ M * Real.log C) := by
  have hR : (1 / 2 : ℝ) < 2 - a - 2 * e := by linarith
  obtain ⟨g, hg, hge, hgc⟩ := exists_holomorphic_log_normalized
    (by linarith : 0 < 2 - a - 2 * e) hL h0
    (hEL (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
  have hgE : EqOn g E (ball c (1 / 2)) := log_eqOn_of_eq_center (by norm_num)
    (hg.mono (ball_subset_ball hR.le)) hE
    (fun z hz ↦ (hge (ball_subset_ball hR.le hz)).trans (hEL hz).symm) hgc
  refine ⟨g, hg, hge, ?_, ?_⟩
  · intro z hz
    rw [hgE (closedBall_subset_ball (by norm_num : (49 / 100 : ℝ) < 1 / 2) hz)]
    exact hEb z hz
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) := ball_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hp := hpoly z hz
    rw [← hez, Complex.norm_exp, Real.rpow_def_of_pos hC] at hp
    simpa [mul_comm] using Real.exp_le_exp.mp hp

theorem logarithmic_derivative_eq {L g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (he : EqOn (Complex.exp ∘ g) L U)
    {z : ℂ} (hz : z ∈ U) : deriv L z / L z = deriv g z := by
  have hgz := (hg z hz).differentiableAt (hU.mem_nhds hz)
  have hd := hgz.hasDerivAt.cexp
  have heq : L =ᶠ[𝓝 z] (fun w ↦ Complex.exp (g w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (he hw).symm
  have hdl := hd.congr_of_eventuallyEq heq
  rw [hdl.deriv]
  have hez : Complex.exp (g z) = L z := he hz
  rw [← hez]
  field_simp

theorem logarithmic_control {e A M ε : ℝ}
    (he : 0 < e) (he' : e < 1 / 1000) (hA : 1 ≤ A) (hM : 1 ≤ M) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (a C : ℝ) (L E : ℂ → ℂ) (c : ℂ),
      1 / 2 ≤ a → a ≤ 1 → Real.exp 1 ≤ C →
      DifferentiableOn ℂ L (ball c (2 - a - 2 * e)) →
      (∀ z ∈ ball c (2 - a - 2 * e), L z ≠ 0) →
      (∀ z ∈ ball c (2 - a - 3 * e), ‖L z‖ ≤ C ^ M) →
      DifferentiableOn ℂ E (ball c (1 / 2)) →
      EqOn (Complex.exp ∘ E) L (ball c (1 / 2)) →
      (∀ z ∈ closedBall c (49 / 100), ‖E z‖ ≤ A) →
      (∀ z ∈ closedBall c (2 - a - 6 * e), ‖L z‖ + ‖(L z)⁻¹‖ ≤ D * C ^ ε) ∧
      (∀ z ∈ closedBall c (2 - a - 8 * e),
        ‖deriv L z / L z‖ ≤ (outerConstant e A M / (2 * e)) * Real.log C) := by
  have hθ := uniformTheta_mem he he'
  have hB := outerConstant_ge_one he he' hA hM
  have hK : 0 ≤ A * outerConstant e A M := by positivity
  obtain ⟨D, hD, hDb⟩ := exp_sublinear_le hθ.1.le hθ.2 hK hε
  refine ⟨2 * D, by positivity, ?_⟩
  intro a C L E c ha ha' hC hL h0 hpoly hE hEL hEb
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hT : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  obtain ⟨g, hg, hge, hgin, hgRe⟩ :=
    zero_free_disk_logarithm ha' he he' hCp hL h0 hpoly hE hEL hEb
  constructor
  · intro z hz
    have hz' : z ∈ ball c (2 - a - 2 * e) :=
      closedBall_subset_ball (by linarith) hz
    have hez : Complex.exp (g z) = L z := hge hz'
    have hb := inner_log_bound ha ha' he he' hA hM hT hg hgRe hgin hz
    have hp : Real.exp (A * outerConstant e A M * Real.log C ^ uniformTheta e) ≤
        D * C ^ ε := by
      convert hDb (Real.log C) hT using 1
      rw [Real.rpow_def_of_pos hCp, mul_comm ε]
    have hu : ‖L z‖ ≤ D * C ^ ε := by
      rw [← hez, Complex.norm_exp]
      exact (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hb)).trans hp
    have hl : ‖(L z)⁻¹‖ ≤ D * C ^ ε := by
      rw [← hez, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
      have hre : -(g z).re ≤ ‖g z‖ :=
        (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      exact (Real.exp_le_exp.mpr (hre.trans hb)).trans hp
    nlinarith
  · intro z hz
    rw [logarithmic_derivative_eq isOpen_ball hg hge
      (closedBall_subset_ball (by linarith) hz)]
    exact logarithm_derivative_bound ha ha' he he' hA hM hT hg hgRe
      (hgin c (mem_closedBall_self (by norm_num))) hz

theorem conductor_height_scale_ge_exp (Q t : ℝ) (hQ : 1 ≤ Q) :
    Real.exp 1 ≤ 2 * Q * (3 + |t|) ^ 2 := by
  have hs : 9 ≤ (3 + |t|) ^ 2 := by nlinarith [abs_nonneg t]
  have hq := mul_le_mul_of_nonneg_right hQ (sq_nonneg (3 + |t|))
  nlinarith [Real.exp_one_lt_three]

theorem absorb_polynomial_constant {K p : ℝ} (hp : 0 ≤ p) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ C : ℝ, Real.exp 1 ≤ C → K * C ^ p ≤ C ^ M := by
  let J := max 1 K
  have hJ : 1 ≤ J := le_max_left _ _
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hlogJ : 0 ≤ Real.log J := Real.log_nonneg hJ
  refine ⟨p + Real.log J + 1, by linarith, ?_⟩
  intro C hC
  have hCp : 0 < C := (Real.exp_pos 1).trans_le hC
  have hlogC : 1 ≤ Real.log C := by simpa using Real.log_le_log (Real.exp_pos 1) hC
  have hJC : J ≤ C ^ Real.log J := by
    rw [Real.rpow_def_of_pos hCp, ← Real.exp_log hJp]
    simp only [Real.log_exp]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    K * C ^ p ≤ J * C ^ p := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hCp.le _)
    _ ≤ C ^ Real.log J * C ^ p := mul_le_mul_of_nonneg_right hJC
      (Real.rpow_nonneg hCp.le _)
    _ = C ^ (p + Real.log J) := by rw [← Real.rpow_add hCp]; congr 1; ring
    _ ≤ C ^ (p + Real.log J + 1) := Real.rpow_le_rpow_of_exponent_le
      ((show (1 : ℝ) ≤ Real.exp 1 by exact Real.one_le_exp (by norm_num)).trans hC)
      (by linarith)

theorem disk_re_gt {a e t : ℝ} {z : ℂ}
    (hz : z ∈ ball (2 + (t : ℂ) * Complex.I) (2 - a - 2 * e)) :
    a + 2 * e < z.re := by
  have hn : ‖z - (2 + (t : ℂ) * Complex.I)‖ < 2 - a - 2 * e := by
    simpa [mem_ball, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z - (2 + (t : ℂ) * Complex.I))
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, zero_mul, sub_zero, add_zero] at hr
  norm_num at hr
  linarith [neg_le_abs (z.re - 2)]

theorem same_height_mem_disk {a e t v x : ℝ} (hev : 8 * e ≤ v)
    (hx : a + v ≤ x) (hx' : x ≤ 2) :
    (x : ℂ) + (t : ℂ) * Complex.I ∈
      closedBall (2 + (t : ℂ) * Complex.I) (2 - a - 8 * e) := by
  rw [mem_closedBall, dist_eq_norm]
  have heq : (x : ℂ) + (t : ℂ) * Complex.I - (2 + (t : ℂ) * Complex.I) =
      ((x - 2 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : x - 2 ≤ 0)]
  linarith

theorem principal_regularizer_norm_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(s - 1) / (s + 1)‖ ≤ 1 := by
  have hn : ‖s - 1‖ ≤ ‖s + 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero, Complex.add_re, Complex.add_im, add_zero]
    nlinarith
  rw [norm_div]
  exact div_le_one_of_le₀ hn (norm_nonneg _)

theorem principal_reciprocal_transfer {s Z L : ℂ} (hs : 0 ≤ s.re)
    (hL : L = ((s - 1) / (s + 1)) * Z) (h0 : L ≠ 0) : ‖Z⁻¹‖ ≤ ‖L⁻¹‖ := by
  have hf0 : (s - 1) / (s + 1) ≠ 0 := by
    intro hf
    apply h0
    rw [hL, hf, zero_mul]
  have heq : Z⁻¹ = ((s - 1) / (s + 1)) * L⁻¹ := by
    rw [hL, mul_inv]
    rw [← mul_assoc, mul_inv_cancel₀ hf0, one_mul]
  rw [heq, norm_mul]
  exact (mul_le_mul_of_nonneg_right (principal_regularizer_norm_le_one hs)
    (norm_nonneg _)).trans_eq (one_mul _)

end SevenEighths.LogarithmicControl

end

end OAI
end OAIOriginalModule0033

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.ExponentialSmoothing
Source SHA256: cf2ef440e2058d798f362b45d09db9ff7464911c750978c20713bf0f96a41491
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0034


namespace OAI

open scoped BigOperators
open MulChar AddChar

open scoped BigOperators

namespace AnalyticBridge

variable {Ω : Type*}

theorem weighted_cauchy_sq
    (S : Finset Ω) (w U V : Ω → ℂ) :
    ‖∑ ω ∈ S, w ω * U ω * star (V ω)‖ ^ 2 ≤
      (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ ^ 2) *
        (∑ ω ∈ S, ‖w ω‖ * ‖V ω‖ ^ 2) := by
  have htri : ‖∑ ω ∈ S, w ω * U ω * star (V ω)‖ ≤
      ∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖ := by
    calc
      ‖∑ ω ∈ S, w ω * U ω * star (V ω)‖ ≤
          ∑ ω ∈ S, ‖w ω * U ω * star (V ω)‖ := norm_sum_le _ _
      _ = ∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖ := by
        apply Finset.sum_congr rfl
        intro ω hω
        simp [ ]
  have hnonneg : 0 ≤ ∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖ :=
    Finset.sum_nonneg (by intro ω hω; positivity)
  have hsq :
      (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖) ^ 2 ≤
        (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ ^ 2) *
          (∑ ω ∈ S, ‖w ω‖ * ‖V ω‖ ^ 2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
      (fun ω hω => by positivity) (fun ω hω => by positivity)
    intro ω hω
    (convert le_refl ((‖w ω‖ * ‖U ω‖ * ‖V ω‖) ^ 2) using 1 ; ring)
  exact (sq_le_sq₀ (norm_nonneg _) hnonneg).2 htri |>.trans hsq

theorem fiber_mass_bound {Λ : Type*} [DecidableEq Λ]
    (S : Finset Ω) (T : Finset Λ) (label : Ω → Λ)
    (weight : Ω → ℝ) (A : Λ → ℂ) (M : ℝ)
    (hmap : ∀ ω ∈ S, label ω ∈ T)
    (hfiber : ∀ a ∈ T,
      (∑ ω ∈ S with label ω = a, weight ω) ≤ M) :
    (∑ ω ∈ S, weight ω * ‖A (label ω)‖ ^ 2) ≤
      M * (∑ a ∈ T, ‖A a‖ ^ 2) := by
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    (∑ a ∈ T, ∑ ω ∈ S with label ω = a,
        weight ω * ‖A (label ω)‖ ^ 2) =
      ∑ a ∈ T, (∑ ω ∈ S with label ω = a, weight ω) * ‖A a‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ω hω
        have hl : label ω = a := (Finset.mem_filter.mp hω).2
        rw [hl]
    _ ≤ ∑ a ∈ T, M * ‖A a‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right (hfiber a ha) (sq_nonneg _)
    _ = M * (∑ a ∈ T, ‖A a‖ ^ 2) := by rw [Finset.mul_sum]

theorem reassembled_bilinear_bound
    {Λ₁ Λ₂ : Type*} [DecidableEq Λ₁] [DecidableEq Λ₂]
    (S : Finset Ω) (T₁ : Finset Λ₁) (T₂ : Finset Λ₂)
    (label₁ : Ω → Λ₁) (label₂ : Ω → Λ₂)
    (w : Ω → ℂ) (A : Λ₁ → ℂ) (B : Λ₂ → ℂ)
    (M₁ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁)
    (hmap₁ : ∀ ω ∈ S, label₁ ω ∈ T₁)
    (hmap₂ : ∀ ω ∈ S, label₂ ω ∈ T₂)
    (hfiber₁ : ∀ a ∈ T₁,
      (∑ ω ∈ S with label₁ ω = a, ‖w ω‖) ≤ M₁)
    (hfiber₂ : ∀ a ∈ T₂,
      (∑ ω ∈ S with label₂ ω = a, ‖w ω‖) ≤ M₂) :
    ‖∑ ω ∈ S, w ω * A (label₁ ω) * star (B (label₂ ω))‖ ^ 2 ≤
      (M₁ * ∑ a ∈ T₁, ‖A a‖ ^ 2) *
        (M₂ * ∑ a ∈ T₂, ‖B a‖ ^ 2) := by
  have hcs := weighted_cauchy_sq S w (fun ω => A (label₁ ω))
    (fun ω => B (label₂ ω))
  have hside₁ := fiber_mass_bound S T₁ label₁
    (fun ω => ‖w ω‖) A M₁ hmap₁ hfiber₁
  have hside₂ := fiber_mass_bound S T₂ label₂
    (fun ω => ‖w ω‖) B M₂ hmap₂ hfiber₂
  calc
    ‖∑ ω ∈ S, w ω * A (label₁ ω) * star (B (label₂ ω))‖ ^ 2 ≤
      (∑ ω ∈ S, ‖w ω‖ * ‖A (label₁ ω)‖ ^ 2) *
        (∑ ω ∈ S, ‖w ω‖ * ‖B (label₂ ω)‖ ^ 2) := hcs
    _ ≤ (M₁ * ∑ a ∈ T₁, ‖A a‖ ^ 2) *
        (M₂ * ∑ a ∈ T₂, ‖B a‖ ^ 2) := by
      have hlow₂ :
          0 ≤ ∑ ω ∈ S, ‖w ω‖ * ‖B (label₂ ω)‖ ^ 2 :=
        Finset.sum_nonneg (by intro ω hω; positivity)
      have hupp₁ : 0 ≤ M₁ * ∑ a ∈ T₁, ‖A a‖ ^ 2 := by positivity
      exact mul_le_mul hside₁ hside₂ hlow₂ hupp₁

theorem square_label_count (F : Finset ℕ) (y E : ℕ)
    (hy : y ≠ 0) (hF : ∀ f ∈ F, f ^ 2 * E ∣ y) :
    F.card ≤ y.divisors.card := by
  apply Finset.card_le_card
  intro f hf
  apply Nat.mem_divisors.mpr
  constructor
  · apply Nat.dvd_trans (Nat.dvd_mul_right f (f * E))
    simpa [pow_two, mul_assoc] using hF f hf
  · exact hy

theorem four_factor_label_count (Q : Finset (ℕ × ℕ × ℕ × ℕ))
    (F : ℕ) (hF : F ≠ 0)
    (hQ : ∀ q ∈ Q, q.1 * q.2.1 * q.2.2.1 * q.2.2.2 = F) :
    Q.card ≤ F.divisors.card ^ 4 := by
  let D := F.divisors
  have hsubset : Q ⊆ D ×ˢ (D ×ˢ (D ×ˢ D)) := by
    intro q hq
    rcases q with ⟨J, C, e, v⟩
    have hprod := hQ (J, C, e, v) hq
    have hJ : J ∣ F := by
      refine ⟨C * e * v, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = J * (C * e * v) := by ring
    have hC : C ∣ F := by
      refine ⟨J * e * v, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = C * (J * e * v) := by ring
    have he : e ∣ F := by
      refine ⟨J * C * v, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = e * (J * C * v) := by ring
    have hv : v ∣ F := by
      refine ⟨J * C * e, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = v * (J * C * e) := by ring
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨hJ, hF⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨hC, hF⟩
    apply Finset.mem_product.mpr
    exact ⟨Nat.mem_divisors.mpr ⟨he, hF⟩,
      Nat.mem_divisors.mpr ⟨hv, hF⟩⟩
  have hcard := Finset.card_le_card hsubset
  simpa [D, Finset.card_product, pow_succ, pow_zero, mul_assoc] using hcard

structure CRTChoice where
  J : ℕ
  C : ℕ
  e : ℕ
  v : ℕ
  s : ℕ
  J2 : ℕ
  b1 : ℕ
  b2 : ℕ
  A1 : ℕ
  A2 : ℕ
  d : ℕ
  kpp : ℕ
  deriving DecidableEq

private def CRTChoice.coordinates (q : CRTChoice) :
    (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) :=
  ((q.J, q.C, q.e, q.v), (q.s, q.J2, q.b1, q.b2),
    (q.A1, q.A2, q.d, q.kpp))

private theorem CRTChoice.coordinates_injective :
    Function.Injective CRTChoice.coordinates := by
  intro x y h
  cases x
  cases y
  simp only [CRTChoice.coordinates, Prod.mk.injEq] at h ⊢
  simp_all

theorem fixed_crt_choice_count
    (Q : Finset CRTChoice) (F K b0 : ℕ)
    (hF : F ≠ 0) (hK : K ≠ 0) (hb0 : b0 ≠ 0)
    (hQ : ∀ q ∈ Q,
      q.J * q.C * q.e * q.v = F ∧
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ F * b0 ∧ q.d * q.e * q.kpp = K) :
    Q.card ≤ F.divisors.card ^ 6 *
      (b0 ^ 2 * F ^ 3).divisors.card ^ 4 *
      (F * b0).divisors.card * K.divisors.card := by
  let DF := F.divisors
  let P := b0 ^ 2 * F ^ 3
  let DP := P.divisors
  let DFB := (F * b0).divisors
  let DK := K.divisors
  let T := (DF ×ˢ (DF ×ˢ (DF ×ˢ DF))) ×ˢ
      ((DF ×ˢ (DF ×ˢ (DP ×ˢ DP))) ×ˢ
      (DP ×ˢ (DP ×ˢ (DFB ×ˢ DK))))
  have hP : P ≠ 0 := by simp [P, hb0, hF]
  have hmap : Set.MapsTo CRTChoice.coordinates (Q : Set CRTChoice) (T : Set _) := by
    intro q hq
    obtain ⟨hlabel, hJ, hbprod, hA1, hA2, hd, hrow⟩ := hQ q hq
    have hJdvd : q.J ∣ F := by
      refine ⟨q.C * q.e * q.v, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.J * (q.C * q.e * q.v) := by ring
    have hsF : q.s ∣ F := by
      apply Nat.dvd_trans _ hJdvd
      refine ⟨q.J2, ?_⟩
      exact hJ
    have hJ2F : q.J2 ∣ F := by
      apply Nat.dvd_trans _ hJdvd
      refine ⟨q.s, ?_⟩
      simpa [mul_comm] using hJ
    have hcore : q.J2 ^ 2 * q.s ∣ F ^ 3 := by
      convert mul_dvd_mul (pow_dvd_pow_of_dvd hJ2F 2) hsF using 1 ; ring
    have hbP : q.b1 * q.b2 ∣ P := by
      rw [hbprod]
      convert Nat.mul_dvd_mul_left (b0 ^ 2) hcore using 1 ; ring
    have hb1P : q.b1 ∣ P := (Nat.dvd_mul_right q.b1 q.b2).trans hbP
    have hb2P : q.b2 ∣ P := (Nat.dvd_mul_left q.b2 q.b1).trans hbP
    have hkppK : q.kpp ∣ K := by
      refine ⟨q.d * q.e, ?_⟩
      calc K = q.d * q.e * q.kpp := hrow.symm
           _ = q.kpp * (q.d * q.e) := by ring
    have hC : q.C ∣ F := by
      refine ⟨q.J * q.e * q.v, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.C * (q.J * q.e * q.v) := by ring
    have he : q.e ∣ F := by
      refine ⟨q.J * q.C * q.v, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.e * (q.J * q.C * q.v) := by ring
    have hv : q.v ∣ F := by
      refine ⟨q.J * q.C * q.e, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.v * (q.J * q.C * q.e) := by ring
    change CRTChoice.coordinates q ∈ T
    simp only [CRTChoice.coordinates, T, Finset.mem_product]
    exact ⟨⟨Nat.mem_divisors.mpr ⟨hJdvd, hF⟩,
      Nat.mem_divisors.mpr ⟨hC, hF⟩,
      Nat.mem_divisors.mpr ⟨he, hF⟩,
      Nat.mem_divisors.mpr ⟨hv, hF⟩⟩,
      ⟨⟨Nat.mem_divisors.mpr ⟨hsF, hF⟩,
        Nat.mem_divisors.mpr ⟨hJ2F, hF⟩,
        Nat.mem_divisors.mpr ⟨hb1P, hP⟩,
        Nat.mem_divisors.mpr ⟨hb2P, hP⟩⟩,
       ⟨Nat.mem_divisors.mpr ⟨hA1.trans hbP, hP⟩,
        Nat.mem_divisors.mpr ⟨hA2.trans hbP, hP⟩,
        Nat.mem_divisors.mpr ⟨hd, mul_ne_zero hF hb0⟩,
        Nat.mem_divisors.mpr ⟨hkppK, hK⟩⟩⟩⟩
  have hcard := Finset.card_le_card_of_injOn CRTChoice.coordinates hmap
    CRTChoice.coordinates_injective.injOn
  convert hcard using 1
  simp [T, DF, DP, DFB, DK, P, Finset.card_product]
  ring

theorem b0_count_scale
    (b0 J2 s c B : ℝ)
    (hb0 : 0 ≤ b0) (hJ2 : 0 ≤ J2) (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hsc : s ≤ c)
    (hprod : b0 ^ 2 * J2 ^ 2 * s ≤ B ^ 2) :
    b0 * (s * J2) ≤ B * Real.sqrt c := by
  have hl : 0 ≤ b0 * (s * J2) := by positivity
  have hr : 0 ≤ B * Real.sqrt c := by positivity
  apply (sq_le_sq₀ hl hr).mp
  calc
    (b0 * (s * J2)) ^ 2 = (b0 ^ 2 * J2 ^ 2 * s) * s := by ring
    _ ≤ B ^ 2 * s := mul_le_mul_of_nonneg_right hprod hs
    _ ≤ B ^ 2 * c := mul_le_mul_of_nonneg_left hsc (sq_nonneg _)
    _ = (B * Real.sqrt c) ^ 2 := by rw [mul_pow, Real.sq_sqrt hc]

private def bit6 (b : Bool) : ZMod 6 := if b then 1 else 0
def localExponent (π ε1 ε2 : Bool) : ZMod 6 :=
  bit6 ε1 - bit6 ε2 + 3 * bit6 π
def finalExponent1 (π ε1 ε2 : Bool) : ZMod 6 :=
  let e := localExponent π ε1 ε2
  4 * bit6 ε1 + (if e = 0 then 0 else 1 + e) + bit6 π * (bit6 ε1 + bit6 ε2)
private def finalExponent2 (π ε1 ε2 : Bool) : ZMod 6 :=
  let e := localExponent π ε1 ε2
  4 * bit6 ε2 + (if e = 0 then 0 else 1 - e) + bit6 π * (bit6 ε1 + bit6 ε2)

theorem local_parity_table (π ε1 ε2 : Bool) :
    finalExponent1 π ε1 ε2 =
        (if π || (ε1 && ε2) then 4 else 0 : ZMod 6) ∧
      finalExponent2 π ε1 ε2 =
        (if π || (ε1 && ε2) then 4 else 0 : ZMod 6) := by
  cases π <;> cases ε1 <;> cases ε2 <;> decide

theorem inactive_conductor_case (π ε1 ε2 : Bool)
    (h : localExponent π ε1 ε2 = 0) :
    π = false ∧ ε1 = ε2 := by
  revert h
  cases π <;> cases ε1 <;> cases ε2 <;> decide

theorem new_label_squarefree
    (J C g e v : ℕ)
    (hJ : Squarefree J) (hC : Squarefree C)
    (he : Squarefree e) (hv : Squarefree v)
    (hCJ : C.Coprime J)
    (hg : g.Coprime (C * J))
    (hvold : v.Coprime (g * C * J))
    (he_g : e ∣ g) : Squarefree (J * C * e * v) := by
  have hJC : J.Coprime C := hCJ.symm
  have hJCe : (J * C).Coprime e := by
    have h := Nat.Coprime.of_dvd_left he_g hg
    simpa [mul_comm] using h.symm
  have hdiv : J * C * e ∣ g * C * J := by
    have h := Nat.mul_dvd_mul_left (J * C) he_g
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hJCev : (J * C * e).Coprime v :=
    (Nat.Coprime.of_dvd_right hdiv hvold).symm
  apply Nat.squarefree_mul_iff.mpr
  refine ⟨hJCev, ?_, hv⟩
  apply Nat.squarefree_mul_iff.mpr
  refine ⟨hJCe, ?_, he⟩
  exact Nat.squarefree_mul_iff.mpr ⟨hJC, hJ, hC⟩

end AnalyticBridge

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ExpBound

theorem exp_neg_le_half {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-t) ≤ (1 : ℝ) / 2 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hinv : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he)
  exact (Real.exp_le_exp.mpr (by linarith)).trans hinv

theorem norm_tsum_exp_le_two
    (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (t : ℝ) (ht : 1 ≤ t)
    (hsum : Summable (fun n : ℕ => a n * Real.exp (-(n : ℝ) * t))) :
    ‖∑' n : ℕ, a n * Real.exp (-(n : ℝ) * t)‖ ≤
      2 * Real.exp (-t) := by
  let r : ℝ := Real.exp (-t)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrhalf : r ≤ (1 : ℝ) / 2 := exp_neg_le_half ht
  have hbound (n : ℕ) :
      ‖a (n + 1) * (Real.exp (-(↑(n + 1) : ℝ) * t) : ℂ)‖ ≤
        r * ((1 : ℝ) / 2) ^ n := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(↑(n + 1) : ℝ) * t) = r ^ (n + 1) := by
      dsimp [r]
      rw [show -(↑(n + 1) : ℝ) * t = (↑(n + 1) : ℝ) * (-t) by ring,
        Real.exp_nat_mul]
    rw [hexp, pow_succ]
    calc
      ‖a (n + 1)‖ * (r ^ n * r) ≤
          1 * (r ^ n * r) := by gcongr; exact ha _
      _ ≤ r * ((1 : ℝ) / 2) ^ n := by
        have hp : r ^ n ≤ ((1 : ℝ) / 2) ^ n := pow_le_pow_left₀ hr0 hrhalf _
        nlinarith [mul_nonneg (sub_nonneg.mpr hp) hr0]
  have hbdsum : Summable (fun n : ℕ => r * ((1 : ℝ) / 2) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)).mul_left r
  have hshift :
      (∑' n : ℕ, a n * Real.exp (-(n : ℝ) * t)) =
        ∑' n : ℕ, a (n + 1) * Real.exp (-(↑(n + 1) : ℝ) * t) := by
    have h := hsum.sum_add_tsum_nat_add 1
    simpa [ha0] using h.symm
  rw [hshift]
  have hnormsum : Summable (fun n : ℕ =>
      ‖a (n + 1) * (Real.exp (-(↑(n + 1) : ℝ) * t) : ℂ)‖) :=
    hbdsum.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  calc
    ‖∑' n : ℕ, a (n + 1) * Real.exp (-(↑(n + 1) : ℝ) * t)‖ ≤
        ∑' n : ℕ,
          ‖a (n + 1) * (Real.exp (-(↑(n + 1) : ℝ) * t) : ℂ)‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, r * ((1 : ℝ) / 2) ^ n :=
      hnormsum.tsum_le_tsum hbound hbdsum
    _ = 2 * Real.exp (-t) := by
      rw [tsum_mul_left, tsum_geometric_two]
      dsimp [r]
      ring

end ExpBound

namespace ShortDraftMellin

theorem inverse_mellin_analytic
    (A : ℝ → ℂ) (σ : ℝ)
    (hlocal : LocallyIntegrableOn A (Set.Ioi 0))
    (htop : A =O[atTop] (fun t : ℝ => t ^ σ))
    (hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0)) :
    AnalyticOnNhd ℂ (fun s : ℂ => mellin A (-s)) {s : ℂ | σ < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt σ)).2
  intro s hs
  change σ < s.re at hs
  have htop' : A =O[atTop] (fun t : ℝ => t ^ (-(-σ))) := by
    simpa only [neg_neg] using htop
  have hbot : A =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (-((-s).re - 1))) := by
    exact hzero.isBigO.trans (isBigO_zero _ _)
  have hdiff : DifferentiableAt ℂ (mellin A) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow hlocal htop'
      (by simpa using neg_lt_neg hs) hbot (by linarith)
  exact (hdiff.comp s (differentiableAt_id.neg)).differentiableWithinAt

theorem dirichlet_zero_free_of_mellin_bound
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (σ : ℝ) (hσ : σ < 1)
    (A : ℝ → ℂ) (W : ℂ → ℂ)
    (hlocal : LocallyIntegrableOn A (Set.Ioi 0))
    (htop : A =O[atTop] (fun t : ℝ => t ^ σ))
    (hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (hW : Differentiable ℂ W)
    (heq : ∀ s : ℂ, 1 < s.re →
      χ.LFunction s * mellin A (-s) = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hL : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hM : AnalyticOnNhd ℂ (fun s : ℂ => mellin A (-s)) U :=
    inverse_mellin_analytic A σ hlocal htop hzero
  have hWa : AnalyticOnNhd ℂ W U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2 hW.differentiableOn
  have htwo : (2 : ℂ) ∈ U := by
    change σ < (2 : ℂ).re
    norm_num at *
    linarith
  have heventual : (fun s : ℂ => χ.LFunction s * mellin A (-s)) =ᶠ[𝓝 (2 : ℂ)] W := by
    filter_upwards [((Complex.isOpen_re_gt 1).mem_nhds (by norm_num :
      (2 : ℂ) ∈ {s : ℂ | 1 < s.re}))] with s hs
    exact heq s hs
  have hid : Set.EqOn (fun s : ℂ => χ.LFunction s * mellin A (-s)) W U :=
    (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hWa
      ((convex_halfSpace_re_gt σ).isPreconnected) htwo heventual
  intro hzeroL
  have heqρ := hid hρ
  change χ.LFunction ρ * mellin A (-ρ) = W ρ at heqρ
  rw [hzeroL, zero_mul] at heqρ
  exact hWρ heqρ.symm

theorem mellin_of_exponential_smoothing
    (a : ℕ → ℂ) (F : ℝ → ℂ) (s : ℂ)
    (hs : 1 < s.re) (ha0 : a 0 = 0)
    (hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n : ℕ => a n * Real.exp (-(n : ℝ) * t)) (F t))
    (hlsum : LSeriesSummable a s) :
    mellin (fun D : ℝ => F D⁻¹) (-s) = Complex.Gamma s * LSeries a s := by
  have hp (n : ℕ) : a n = 0 ∨ 0 < (n : ℝ) := by
    rcases n with _ | n
    · exact Or.inl ha0
    · exact Or.inr (by exact_mod_cast Nat.succ_pos n)
  have hnorm : (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ s.re) =
      fun n : ℕ => ‖LSeries.term a s n‖ := by
    funext n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst n
      simp [ha0]
    · simp [hn]
  have hsum : Summable (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ s.re) := by
    rw [hnorm]
    exact hlsum.norm
  have hM := hasSum_mellin hp (by linarith) hF hsum
  have hterm (n : ℕ) : Complex.Gamma s * a n / (n : ℝ) ^ s =
      Complex.Gamma s * LSeries.term a s n := by
    by_cases hn : n = 0
    · subst n
      simp [ha0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      simp only [Complex.ofReal_natCast]
      ring
  have hM' : HasSum (fun n : ℕ => Complex.Gamma s * LSeries.term a s n) (mellin F s) := by
    simpa only [hterm] using hM
  have hseries : HasSum (fun n : ℕ => Complex.Gamma s * LSeries.term a s n)
      (Complex.Gamma s * LSeries a s) := by
    simpa only [LSeries] using hlsum.hasSum.mul_left (Complex.Gamma s)
  have heq : mellin F s = Complex.Gamma s * LSeries a s := hM'.unique hseries
  simpa only [mellin_comp_inv, neg_neg] using heq

theorem dirichlet_exponential_mellin_identity
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (F : ℝ → ℂ)
    (hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n : ℕ =>
        χ n * (ArithmeticFunction.moebius n : ℂ) *
          Real.exp (-(n : ℝ) * t)) (F t))
    (s : ℂ) (hs : 1 < s.re) :
    χ.LFunction s * mellin (fun D : ℝ => F D⁻¹) (-s) =
      Complex.Gamma s := by
  let a : ℕ → ℂ :=
    (fun n : ℕ => χ n) * (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
  have ha0 : a 0 = 0 := by simp [a]
  have hsum : LSeriesSummable a s := by
    simpa only [a] using
      (DirichletCharacter.LSeriesSummable_mul χ
        (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs))
  have hM := mellin_of_exponential_smoothing a F s hs ha0 hF hsum
  have hprod : LSeries (χ ·) s * LSeries a s = 1 := by
    simpa only [a] using
      DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  rw [χ.LFunction_eq_LSeries hs, hM]
  calc
    LSeries (χ ·) s * (Complex.Gamma s * LSeries a s) =
        (LSeries (χ ·) s * LSeries a s) * Complex.Gamma s := by ring
    _ = Complex.Gamma s := by rw [hprod, one_mul]

theorem mobius_char_exp_summable
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ =>
      χ n * (ArithmeticFunction.moebius n : ℂ) *
        Real.exp (-(n : ℝ) * t)) := by
  have hexp : Summable (fun n : ℕ => Real.exp (-(n : ℝ) * t)) := by
    convert (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr ht)) using 1
    ext n
    congr 1
    ring
  apply hexp.of_norm_bounded
  intro n
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hprod : ‖χ n‖ * ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
      (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
      mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]
  nlinarith [mul_nonneg (sub_nonneg.mpr hprod)
    (le_of_lt (Real.exp_pos (-(n : ℝ) * t)))]

noncomputable def mobiusExpSum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑' n : ℕ, χ n * (ArithmeticFunction.moebius n : ℂ) *
    Real.exp (-(n : ℝ) * t)

theorem mobiusExpSum_norm_le_two
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖mobiusExpSum χ t‖ ≤ 2 * Real.exp (-t) := by
  have hcoeff (n : ℕ) :
      ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
      (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
      mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]
  exact ExpBound.norm_tsum_exp_le_two
    (fun n => χ n * (ArithmeticFunction.moebius n : ℂ))
    (by simp) hcoeff t ht
    (mobius_char_exp_summable χ t (lt_of_lt_of_le zero_lt_one ht))

theorem mobiusExpSum_flat_at_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun D : ℝ => D ^ b) := by
  have hExp : (fun t : ℝ => mobiusExpSum χ t) =O[atTop]
      (fun t : ℝ => Real.exp (-t)) := by
    apply isBigO_iff_isBigOWith.mpr
    refine ⟨2, IsBigOWith.of_bound ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      mobiusExpSum_norm_le_two χ t ht
  have hpow : (fun t : ℝ => mobiusExpSum χ t) =O[atTop]
      (fun t : ℝ => t ^ (-b)) := by
    apply hExp.trans
    simpa only [one_mul, neg_one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-b)).isBigO
  have hcomp := hpow.comp_tendsto tendsto_inv_nhdsGT_zero
  refine hcomp.congr (fun _ => rfl) ?_
  intro D
  dsimp
  rw [← Real.rpow_neg_eq_inv_rpow]
  simp

theorem dirichlet_exp_mellin_identity
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    χ.LFunction s *
      mellin (fun D : ℝ => mobiusExpSum χ D⁻¹) (-s) =
        Complex.Gamma s := by
  apply dirichlet_exponential_mellin_identity χ (mobiusExpSum χ)
  · intro t ht
    exact (mobius_char_exp_summable χ t ht).hasSum
  · exact hs

theorem inverse_mellin_analytic_of_flat
    (A : ℝ → ℂ) (σ : ℝ)
    (hlocal : LocallyIntegrableOn A (Set.Ioi 0))
    (htop : A =O[atTop] (fun t : ℝ => t ^ σ))
    (hflat : ∀ b : ℝ, A =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ b)) :
    AnalyticOnNhd ℂ (fun s : ℂ => mellin A (-s)) {s : ℂ | σ < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt σ)).2
  intro s hs
  change σ < s.re at hs
  have htop' : A =O[atTop] (fun t : ℝ => t ^ (-(-σ))) := by
    simpa only [neg_neg] using htop
  have hbot : A =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (-((-s).re - 1))) := hflat _
  have hdiff : DifferentiableAt ℂ (mellin A) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow hlocal htop'
      (by simpa using neg_lt_neg hs) hbot (by linarith)
  exact (hdiff.comp s (differentiableAt_id.neg)).differentiableWithinAt

theorem dirichlet_exp_zero_free_of_power_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn
      (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0))
    (htop : (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (hflat : ∀ b : ℝ,
      (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[𝓝[>] (0 : ℝ)]
        (fun D : ℝ => D ^ b))
    (ρ : ℂ) (hρ : σ < ρ.re) : χ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hL : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => mobiusExpSum χ D⁻¹) (-s)) U :=
    inverse_mellin_analytic_of_flat _ σ hlocal htop hflat
  have hW : AnalyticOnNhd ℂ Complex.Gamma U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hopen).2
    intro s hs
    apply (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    have hreal : s.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hspos : 0 < s.re := lt_trans hσpos hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hWρ : Complex.Gamma ρ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (lt_trans hσpos hρ)
  exact ShortDraft.zero_free_of_analytic_identity σ hσ χ.LFunction
    (fun s => mellin (fun D : ℝ => mobiusExpSum χ D⁻¹) (-s))
    Complex.Gamma hL hM hW
    (fun s hs => dirichlet_exp_mellin_identity χ s hs) ρ hρ hWρ

end ShortDraftMellin


end OAI
end OAIOriginalModule0034

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.LogProfiles
Source SHA256: ff8735e421a2ee659df15272704206f2d114d7e2a849e8a755d545508f4038be
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0035


namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftMellin

theorem mobiusExpSum_continuousOn_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ContinuousOn (mobiusExpSum χ) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  change 0 < t at ht
  let δ : ℝ := t / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδt : δ < t := by dsimp [δ]; linarith
  have hexp : Summable (fun n : ℕ => Real.exp (-(n : ℝ) * δ)) := by
    convert (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hδ)) using 1
    ext n
    congr 1
    ring
  have hcontTerm (n : ℕ) : ContinuousOn
      (fun u : ℝ => χ n * (ArithmeticFunction.moebius n : ℂ) *
        Real.exp (-(n : ℝ) * u)) (Set.Ici δ) := by
    fun_prop
  have hcoeff (n : ℕ) :
      ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
      (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
      mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]
  have hbound (n : ℕ) (u : ℝ) (hu : u ∈ Set.Ici δ) :
      ‖χ n * (ArithmeticFunction.moebius n : ℂ) *
        Real.exp (-(n : ℝ) * u)‖ ≤
      Real.exp (-(n : ℝ) * δ) := by
    have hnu : -(n : ℝ) * u ≤ -(n : ℝ) * δ := by
      have hu' : δ ≤ u := hu
      nlinarith [mul_le_mul_of_nonneg_left hu'
        (Nat.cast_nonneg (α := ℝ) n)]
    have hexpmon := Real.exp_le_exp.mpr hnu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ *
          Real.exp (-(n : ℝ) * u) ≤
          1 * Real.exp (-(n : ℝ) * u) :=
        mul_le_mul_of_nonneg_right (hcoeff n) (Real.exp_pos _).le
      _ ≤ Real.exp (-(n : ℝ) * δ) := by simpa using hexpmon
  have hcontHalf : ContinuousOn (mobiusExpSum χ) (Set.Ici δ) := by
    change ContinuousOn
      (fun u : ℝ => ∑' n : ℕ,
        χ n * (ArithmeticFunction.moebius n : ℂ) *
          Real.exp (-(n : ℝ) * u)) (Set.Ici δ)
    exact continuousOn_tsum hcontTerm hexp hbound
  exact (hcontHalf.continuousAt (Ici_mem_nhds hδt)).continuousWithinAt

theorem mobiusExpSum_inv_continuousOn_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ContinuousOn (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0) := by
  apply (mobiusExpSum_continuousOn_pos χ).comp
    (continuousOn_inv₀.mono (by
      intro D hD
      exact ne_of_gt hD))
  intro D hD
  exact inv_pos.mpr (show 0 < D from hD)

theorem mobiusExpSum_inv_locallyIntegrableOn_pos
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    LocallyIntegrableOn
      (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0) :=
  (mobiusExpSum_inv_continuousOn_pos χ).locallyIntegrableOn measurableSet_Ioi

theorem dirichlet_exp_zero_free_of_power_bound_only
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) : χ.LFunction ρ ≠ 0 := by
  exact dirichlet_exp_zero_free_of_power_bound χ hχ σ hσpos hσ
    (mobiusExpSum_inv_locallyIntegrableOn_pos χ) htop
    (mobiusExpSum_flat_at_zero χ) ρ hρ

theorem principal_dirichlet_exp_zero_free_of_power_bound_only
    (q : ℕ) [NeZero q]
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => mobiusExpSum
        (1 : DirichletCharacter ℂ q) D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ ≠ 0 := by
  let U : Set ℂ := {s | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLregular : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunctionTrivChar₁ q) U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin
        (fun D : ℝ => mobiusExpSum (1 : DirichletCharacter ℂ q) D⁻¹) (-s)) U :=
    inverse_mellin_analytic_of_flat _ σ
      (mobiusExpSum_inv_locallyIntegrableOn_pos 1) htop
      (mobiusExpSum_flat_at_zero 1)
  have hW : AnalyticOnNhd ℂ Complex.Gamma U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hopen).2
    intro s hs
    apply (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    have hreal : s.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hspos : 0 < s.re := lt_trans hσpos hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      DirichletCharacter.LFunctionTrivChar₁ q s =
        (s - 1) * DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q) s := by
    intro s _ hs
    simp [DirichletCharacter.LFunctionTrivChar₁,
      DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
  have heq : ∀ s : ℂ, 1 < s.re →
      DirichletCharacter.LFunctionTrivChar₁ q s *
        mellin (fun D : ℝ => mobiusExpSum
          (1 : DirichletCharacter ℂ q) D⁻¹) (-s) =
        (s - 1) * Complex.Gamma s := by
    intro s hs
    rw [hregular s (lt_trans hσ hs) (by
      intro h; subst s; norm_num at hs)]
    rw [mul_assoc, dirichlet_exp_mellin_identity 1 s hs]
  have hWρ : Complex.Gamma ρ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (lt_trans hσpos hρ)
  exact ShortDraft.zero_free_of_regularized_analytic_identity σ hσ
    (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))
    (DirichletCharacter.LFunctionTrivChar₁ q)
    (fun s => mellin (fun D : ℝ => mobiusExpSum
      (1 : DirichletCharacter ℂ q) D⁻¹) (-s))
    Complex.Gamma hLregular hM hW hregular heq ρ hρ hρone hWρ

def ExponentialMobiusPowerBound : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ),
    (23 / 24 : ℝ) < σ → σ < 1 →
      (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[atTop]
        (fun D : ℝ => D ^ σ)

theorem dirichletTarget_of_exponentialMobiusPowerBound
    (hbound : ExponentialMobiusPowerBound) : ShortDraft.DirichletTarget := by
  intro q _ χ s h23 hprincipal
  by_cases hs : s.re < 1
  · let σ : ℝ := ((23 / 24 : ℝ) + s.re) / 2
    have hσ23 : (23 / 24 : ℝ) < σ := by dsimp [σ]; linarith
    have hσs : σ < s.re := by dsimp [σ]; linarith
    have hσone : σ < 1 := lt_trans hσs hs
    have hσpos : 0 < σ := lt_trans (by norm_num : (0 : ℝ) < 23 / 24) hσ23
    by_cases hχ : χ = 1
    · subst χ
      have hsone : s ≠ 1 := by
        intro h; exact hprincipal ⟨rfl, h⟩
      exact principal_dirichlet_exp_zero_free_of_power_bound_only q σ
        hσpos hσone (hbound q 1 σ hσ23 hσone) s hσs hsone
    · exact dirichlet_exp_zero_free_of_power_bound_only χ hχ σ
        hσpos hσone (hbound q χ σ hσ23 hσone) s hσs
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ s
      (le_of_not_gt hs) hprincipal

end ShortDraftMellin

namespace FiniteRingSieve

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

omit [DecidableEq R] in
private theorem sum_chars_zero {a : R} (ha : a ≠ 1) :
    (∑ χ : MulChar R ℂ, χ a) = 0 := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity R ℂ ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' => rfl

theorem sum_chars (a : R) :
    (∑ χ : MulChar R ℂ, χ a) =
      if a = 1 then (Fintype.card Rˣ : ℂ) else 0 := by
  split_ifs with ha
  · subst a
    simp only [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hc : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
      simpa only [Nat.card_eq_fintype_card] using
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ
    exact_mod_cast hc
  · exact sum_chars_zero ha

theorem unit_char_orthogonal (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, star (χ (u : R)) * χ (v : R)) =
      if u = v then (Fintype.card Rˣ : ℂ) else 0 := by
  calc
    _ = ∑ χ : MulChar R ℂ, χ ((u⁻¹ * v : Rˣ) : R) := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit,
        Units.val_mul, map_mul]
    _ = if ((u⁻¹ * v : Rˣ) : R) = 1 then (Fintype.card Rˣ : ℂ) else 0 :=
      sum_chars _
    _ = _ := by simp only [Units.val_eq_one, inv_mul_eq_one]

theorem complete_character_plancherel (a : Rˣ → ℂ) :
    (∑ χ : MulChar R ℂ, ‖∑ u : Rˣ, a u * χ (u : R)‖ ^ 2) =
      (Fintype.card Rˣ : ℝ) * ∑ u : Rˣ, ‖a u‖ ^ 2 := by
  classical
  have hnorm (χ : MulChar R ℂ) :
      (↑(‖∑ u : Rˣ, a u * χ (u : R)‖ ^ 2) : ℂ) =
        (∑ u : Rˣ, star (a u) * star (χ (u : R))) *
          (∑ v : Rˣ, a v * χ (v : R)) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, starRingEnd_apply]
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  simp_rw [hnorm]
  calc
    (∑ χ : MulChar R ℂ,
        (∑ u : Rˣ, star (a u) * star (χ (u : R))) *
          (∑ v : Rˣ, a v * χ (v : R))) =
      ∑ u : Rˣ, ∑ v : Rˣ,
        (star (a u) * a v) *
          ∑ χ : MulChar R ℂ, star (χ (u : R)) * χ (v : R) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        congr 1
        funext u
        rw [Finset.sum_comm]
        congr 1
        funext v
        calc
          (∑ χ : MulChar R ℂ,
              star (a u) * star (χ (u : R)) * (a v * χ (v : R))) =
            ∑ χ : MulChar R ℂ,
              (star (a u) * a v) * (star (χ (u : R)) * χ (v : R)) := by
              apply Finset.sum_congr rfl
              intro χ _
              ring
          _ = _ := by rfl
    _ = (Fintype.card Rˣ : ℂ) * ∑ u : Rˣ, (↑(‖a u‖ ^ 2) : ℂ) := by
        simp_rw [unit_char_orthogonal]
        simp_rw [mul_ite]
        simp only [mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        simp [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, Finset.mul_sum,
          mul_comm, mul_left_comm]

end FiniteRingSieve

namespace FiniteFieldSieve

variable {F : Type*} [Field F] [Fintype F]

private theorem complex_sum_cauchy {ι : Type*} (S : Finset ι) (x y : ι → ℂ) :
    ‖∑ i ∈ S, x i * y i‖ ^ 2 ≤
      (∑ i ∈ S, ‖x i‖ ^ 2) * ∑ i ∈ S, ‖y i‖ ^ 2 := by
  have htri : ‖∑ i ∈ S, x i * y i‖ ≤ ∑ i ∈ S, ‖x i‖ * ‖y i‖ := by
    simpa only [norm_mul] using norm_sum_le S (fun i => x i * y i)
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
      (fun i hi => mul_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr htri
  exact hsquare.trans (Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖x i‖)
    (fun i => ‖y i‖))

private theorem character_norm_le_one (χ : MulChar F ℂ) (u : F) : ‖χ u‖ ≤ 1 := by
  let : Fintype Fˣ := Fintype.ofFinite _
  by_cases hu : u = 0
  · rw [hu, MulChar.map_zero]
    simp
  · let v : Fˣ := Units.mk0 u hu
    have hv : (v : F) = u := rfl
    rw [← hv]
    have h : ‖χ (v : F)‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using
        Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity v)
    exact h.le

theorem primitive_gauss_norm_sq (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hnorm : ((‖gaussSum χ ψ‖ ^ 2 : ℝ) : ℂ) =
      gaussSum χ ψ * star (gaussSum χ ψ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    simp only [starRingEnd_apply, mul_comm]
  apply Complex.ofReal_inj.mp
  rw [hnorm]
  exact h

theorem gauss_shift_all (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (n : F) :
    gaussSum χ (ψ.mulShift n) = χ⁻¹ n * gaussSum χ ψ := by
  by_cases hn : n = 0
  · subst n
    simp only [AddChar.mulShift_zero, MulChar.map_zero, zero_mul]
    exact gaussSum_one_right hχ
  · let u : Fˣ := Units.mk0 n hn
    have hu : (u : F) = n := rfl
    rw [← hu]
    exact gaussSum_mulShift_eq χ ψ u

theorem character_gauss_expansion (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (n : F) :
    χ n * gaussSum χ⁻¹ ψ =
      ∑ u : F, χ⁻¹ u * ψ (n * u) := by
  calc
    χ n * gaussSum χ⁻¹ ψ = gaussSum χ⁻¹ (ψ.mulShift n) := by
      simpa using (gauss_shift_all χ⁻¹ ψ (by simpa using hχ) n).symm
    _ = _ := by simp [gaussSum, AddChar.mulShift_apply, mul_comm]

theorem character_sum_le_additive_energy {ι : Type*} (I : Finset ι)
    (n : ι → F) (a : ι → ℂ) (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖∑ i ∈ I, a i * χ (n i)‖ ^ 2 ≤
      ∑ u : F, ‖∑ i ∈ I, a i * ψ (n i * u)‖ ^ 2 := by
  classical
  let g := gaussSum χ⁻¹ ψ
  let T (u : F) := ∑ i ∈ I, a i * ψ (n i * u)
  let S := ∑ i ∈ I, a i * χ (n i)
  have hsum : g * S = ∑ u : F, χ⁻¹ u * T u := by
    calc
      g * S = ∑ i ∈ I, a i * (χ (n i) * g) := by
        rw [mul_comm g S, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i ∈ I, a i *
          (∑ u : F, χ⁻¹ u * ψ (n i * u)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [character_gauss_expansion χ ψ hχ (n i)]
      _ = ∑ u : F, χ⁻¹ u * T u := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hmass : (∑ u : F, ‖χ⁻¹ u‖ ^ 2) ≤ (Fintype.card F : ℝ) := by
    calc
      _ ≤ ∑ u : F, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro u _
        have hu := character_norm_le_one χ⁻¹ u
        nlinarith [norm_nonneg (χ⁻¹ u)]
      _ = _ := by simp
  have hcauchy := complex_sum_cauchy (Finset.univ : Finset F)
    (fun u => χ⁻¹ u) T
  have hgauss : ‖g‖ ^ 2 = (Fintype.card F : ℝ) := by
    exact primitive_gauss_norm_sq χ⁻¹ ψ (by simpa using hχ) hψ
  have hnonneg : 0 ≤ ∑ u : F, ‖T u‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpre : (Fintype.card F : ℝ) * ‖S‖ ^ 2 ≤
      (Fintype.card F : ℝ) * ∑ u : F, ‖T u‖ ^ 2 := by
    calc
      _ = ‖g * S‖ ^ 2 := by rw [norm_mul, mul_pow, hgauss]
      _ = ‖∑ u : F, χ⁻¹ u * T u‖ ^ 2 := by rw [hsum]
      _ ≤ (∑ u : F, ‖χ⁻¹ u‖ ^ 2) * ∑ u : F, ‖T u‖ ^ 2 := hcauchy
      _ ≤ _ := mul_le_mul_of_nonneg_right hmass hnonneg
  have hcard : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  exact (mul_le_mul_iff_of_pos_left hcard).mp hpre

end FiniteFieldSieve

namespace ProductResidueSieve

variable {R S : Type*} [CommRing R] [CommRing S]

def mulCharProd (χ : MulChar R ℂ) (η : MulChar S ℂ) : MulChar (R × S) ℂ where
  toFun x := χ x.1 * η x.2
  map_one' := by simp
  map_mul' x y := by simp [mul_mul_mul_comm]
  map_nonunit' x hx := by
    rw [Prod.isUnit_iff] at hx
    by_cases h₁ : IsUnit x.1
    · have h₂ : ¬IsUnit x.2 := by tauto
      simp [MulChar.map_nonunit η h₂]
    · simp [MulChar.map_nonunit χ h₁]

def addCharProd (ψ : AddChar R ℂ) (φ : AddChar S ℂ) : AddChar (R × S) ℂ where
  toFun x := ψ x.1 * φ x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

@[simp] theorem mulCharProd_apply (χ : MulChar R ℂ) (η : MulChar S ℂ) (x : R × S) :
    mulCharProd χ η x = χ x.1 * η x.2 := rfl

@[simp] theorem addCharProd_apply (ψ : AddChar R ℂ) (φ : AddChar S ℂ) (x : R × S) :
    addCharProd ψ φ x = ψ x.1 * φ x.2 := rfl

end ProductResidueSieve

open MeasureTheory Real
open scoped FourierTransform SchwartzMap

open scoped ContDiff

namespace FourierBridge

theorem schwartz_log_inversion (g : 𝓢(ℝ, ℂ)) (y : ℝ) :
    g y = ∫ t : ℝ,
      Complex.exp ((↑(2 * Real.pi * inner ℝ t y) * Complex.I)) * (𝓕 g) t := by
  have hinv : (𝓕⁻ (𝓕 g) : 𝓢(ℝ, ℂ)) = g := by simp
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f y) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
  simpa only [smul_eq_mul] using h.symm

noncomputable def logProfile
    (W : ℝ → ℂ) (F : ℝ → ℂ) (R a : ℝ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) : 𝓢(ℝ, ℂ) := by
  let G : ℝ → ℂ := fun y => W y * F (R * Real.exp (a * y))
  have harg : ContDiff ℝ ∞ (fun y : ℝ => R * Real.exp (a * y)) := by
    fun_prop
  have hGs : ContDiff ℝ ∞ G := by
    dsimp [G]
    exact hWs.mul (hFs.comp harg)
  have hGc : HasCompactSupport G := by
    dsimp [G]
    exact hWc.mul_right
  exact hGc.toSchwartzMap hGs

theorem logProfile_apply
    (W : ℝ → ℂ) (F : ℝ → ℂ) (R a y : ℝ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    logProfile W F R a hWc hWs hFs y = W y * F (R * Real.exp (a * y)) := rfl

theorem smooth_log_separation
    (W : ℝ → ℂ) (F : ℝ → ℂ) (R a y : ℝ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    W y * F (R * Real.exp (a * y)) =
      ∫ t : ℝ, Complex.exp ((↑(2 * Real.pi * inner ℝ t y) * Complex.I)) *
        (𝓕 (logProfile W F R a hWc hWs hFs)) t := by
  rw [← logProfile_apply W F R a y hWc hWs hFs]
  exact schwartz_log_inversion _ _

theorem fourier_coefficient_moment (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖ ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        (SchwartzMap.seminorm ℝ (J + (volume : Measure ℝ).integrablePower) 0) (𝓕 g)) := by
  simpa using SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume (𝓕 g) J 0

theorem logProfile_coefficient_integrable
    (W F : ℝ → ℂ) (R a : ℝ) (J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    Integrable (fun t : ℝ => ‖t‖ ^ J *
      ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖) volume :=
  (𝓕 (logProfile W F R a hWc hWs hFs)).integrable_pow_mul volume J

theorem logProfile_coefficient_moment
    (W F : ℝ → ℂ) (R a : ℝ) (J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖ ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((SchwartzMap.seminorm ℝ 0 0)
          (𝓕 (logProfile W F R a hWc hWs hFs)) +
        (SchwartzMap.seminorm ℝ (J + (volume : Measure ℝ).integrablePower) 0)
          (𝓕 (logProfile W F R a hWc hWs hFs))) :=
  fourier_coefficient_moment _ J

theorem logProfile_pointwise_decay
    (W F : ℝ → ℂ) (R a m CW CF : ℝ) (A : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWbound : ∀ y, ‖W y‖ ≤ CW)
    (hlower : ∀ y, W y ≠ 0 → m ≤ Real.exp (a * y))
    (hFdecay : ∀ u, 0 ≤ u → (1 + u) ^ A * ‖F u‖ ≤ CF)
    (y : ℝ) :
    m ^ A * (1 + R) ^ A * ‖W y * F (R * Real.exp (a * y))‖ ≤
      CW * CF := by
  by_cases hWy : W y = 0
  · simp [hWy, mul_nonneg hCW hCF]
  have hE : m ≤ Real.exp (a * y) := hlower y hWy
  have hu : 0 ≤ R * Real.exp (a * y) := by positivity
  have hscale : m * (1 + R) ≤ 1 + R * Real.exp (a * y) := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hE)]
  have hpow : (m * (1 + R)) ^ A ≤
      (1 + R * Real.exp (a * y)) ^ A := by gcongr
  have hbase : (m * (1 + R)) ^ A * ‖F (R * Real.exp (a * y))‖ ≤ CF :=
    (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
      (hFdecay _ hu)
  rw [Complex.norm_mul]
  calc
    m ^ A * (1 + R) ^ A * (‖W y‖ * ‖F (R * Real.exp (a * y))‖) =
      ‖W y‖ * ((m * (1 + R)) ^ A * ‖F (R * Real.exp (a * y))‖) := by rw [mul_pow]; ring
    _ ≤ CW * ((m * (1 + R)) ^ A * ‖F (R * Real.exp (a * y))‖) :=
      mul_le_mul_of_nonneg_right (hWbound y) (by positivity)
    _ ≤ CW * CF := mul_le_mul_of_nonneg_left hbase hCW

theorem logProfile_zero_seminorm_decay
    (W F : ℝ → ℂ) (R a m CW CF : ℝ) (A : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWbound : ∀ y, ‖W y‖ ≤ CW)
    (hlower : ∀ y, W y ≠ 0 → m ≤ Real.exp (a * y))
    (hFdecay : ∀ u, 0 ≤ u → (1 + u) ^ A * ‖F u‖ ≤ CF)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    m ^ A * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ 0 0) (logProfile W F R a hWc hWs hFs) ≤
      CW * CF := by
  let g := logProfile W F R a hWc hWs hFs
  let scale := m ^ A * (1 + R) ^ A
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hnum : 0 ≤ CW * CF := mul_nonneg hCW hCF
  have hbound : ∀ y, ‖g y‖ ≤ CW * CF / scale := by
    intro y
    apply (le_div_iff₀ hscale).mpr
    have hp := logProfile_pointwise_decay W F R a m CW CF A hR hm hm1
      hCW hCF hWbound hlower hFdecay y
    simpa [g, scale, logProfile_apply, mul_comm, mul_left_comm, mul_assoc] using hp
  have hsemi : (SchwartzMap.seminorm ℝ 0 0) g ≤ CW * CF / scale := by
    apply SchwartzMap.seminorm_le_bound ℝ 0 0 g (div_nonneg hnum hscale.le)
    intro y
    simpa using hbound y
  calc
    scale * (SchwartzMap.seminorm ℝ 0 0) g ≤ scale * (CW * CF / scale) :=
      mul_le_mul_of_nonneg_left hsemi hscale.le
    _ = CW * CF := by field_simp

theorem exp_argument_derivative_bound
    (R a y H : ℝ) (i : ℕ)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun z : ℝ => R * Real.exp (a * z)) y‖ ≤
      (H ^ 2 * (1 + R)) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hR,
    abs_of_pos (Real.exp_pos _), abs_pow]
  have hpowH : H ≤ H ^ i := by
    calc H = H ^ 1 := by ring
         _ ≤ H ^ i := pow_le_pow_right₀ hH hi
  have hpowR : R ≤ (1 + R) ^ i := by
    calc R ≤ 1 + R := by linarith
         _ = (1 + R) ^ 1 := by ring
         _ ≤ (1 + R) ^ i := pow_le_pow_right₀ (by linarith) hi
  calc
    R * (|a| ^ i * Real.exp (a * y)) ≤ R * (H ^ i * H) := by gcongr
    _ ≤ (1 + R) ^ i * (H ^ i * H ^ i) := by gcongr
    _ = (H ^ 2 * (1 + R)) ^ i := by simp only [mul_pow, pow_two]; ring

theorem coupled_factor_derivative_bound
    (F : ℝ → ℂ) (R a y H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hj : j ≤ n)
    (_hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
      j.factorial * (CF / (1 + R * Real.exp (a * y)) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j := by
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
  have hu : 0 ≤ R * Real.exp (a * y) := by positivity
  have hden : 0 < (1 + R * Real.exp (a * y)) ^ (A + n) := by positivity
  apply norm_iteratedFDeriv_comp_le hF harg (by simp) y
  · intro i hi
    apply (le_div_iff₀ hden).mpr
    simpa [mul_comm] using hFdecay i (hi.trans hj) _ hu
  · intro i hi₁ hi₂
    exact exp_argument_derivative_bound R a y H i hR hH ha hexp hi₁

theorem derivative_scale_absorption
    (R u m H CF : ℝ) (A n j : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m)
    (_hH : 0 ≤ H) (hCF : 0 ≤ CF)
    (hu : 0 ≤ u) (hlower : m * (1 + R) ≤ 1 + u)
    (hj : j ≤ n) :
    m ^ (A + n) * (1 + R) ^ A *
      ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j) ≤
      (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hRp : 1 ≤ 1 + R := by linarith
  have hden : 0 < (1 + u) ^ (A + n) := by positivity
  have hpowR : (1 + R) ^ (A + j) ≤ (1 + R) ^ (A + n) :=
    pow_le_pow_right₀ hRp (Nat.add_le_add_left hj A)
  have hscale : m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j ≤
      (1 + u) ^ (A + n) := by
    calc
      m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j =
          m ^ (A + n) * (1 + R) ^ (A + j) := by rw [pow_add]; ring
      _ ≤ m ^ (A + n) * (1 + R) ^ (A + n) :=
        mul_le_mul_of_nonneg_left hpowR (by positivity)
      _ = (m * (1 + R)) ^ (A + n) := by rw [mul_pow]
      _ ≤ (1 + u) ^ (A + n) := by gcongr
  let Q : ℝ := (j.factorial : ℝ) * CF * (H ^ 2) ^ j
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQscale : Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) ≤
      Q * (1 + u) ^ (A + n) := mul_le_mul_of_nonneg_left hscale hQ
  calc
    m ^ (A + n) * (1 + R) ^ A *
        ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
          (H ^ 2 * (1 + R)) ^ j) =
      Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) /
        (1 + u) ^ (A + n) := by dsimp [Q]; rw [mul_pow]; ring
    _ ≤ Q := (div_le_iff₀ hden).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hQscale)
    _ = (j.factorial : ℝ) * CF * (H ^ 2) ^ j := rfl

theorem coupled_factor_uniform_derivative
    (F : ℝ → ℂ) (R a y m H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hexpLower : m ≤ Real.exp (a * y))
    (hexpUpper : Real.exp (a * y) ≤ H)
    (hj : j ≤ n) (hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    m ^ (A + n) * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
        (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hcomp := coupled_factor_derivative_bound F R a y H CF A n j hF hR hH
    ha hexpUpper hj hCF hFdecay
  have hscale : 0 ≤ m ^ (A + n) * (1 + R) ^ A := by positivity
  have hlower : m * (1 + R) ≤ 1 + R * Real.exp (a * y) := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hexpLower)]
  exact (mul_le_mul_of_nonneg_left hcomp hscale).trans
    (derivative_scale_absorption R (R * Real.exp (a * y)) m H CF A n j
      hR hm (by linarith) hCF (by positivity) hlower hj)

theorem logProfile_derivative_decay
    (W F : ℝ → ℂ) (R a m H CW CF : ℝ) (A n : ℕ)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWderiv : ∀ i ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧ Real.exp (a * y) ≤ H)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (y : ℝ) :
    m ^ (A + n) * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ n (fun z : ℝ => W z * F (R * Real.exp (a * z))) y‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i)) := by
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
  have hG : ContDiff ℝ ∞ (fun z : ℝ => F (R * Real.exp (a * z))) :=
    hFs.comp harg
  have hprod := norm_iteratedFDeriv_mul_le hWs hG y (n := n) (by simp)
  have hscale : 0 ≤ m ^ (A + n) * (1 + R) ^ A := by positivity
  calc
    m ^ (A + n) * (1 + R) ^ A *
        ‖iteratedFDeriv ℝ n (fun z : ℝ => W z * F (R * Real.exp (a * z))) y‖ ≤
      (m ^ (A + n) * (1 + R) ^ A) *
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i W y‖ *
          ‖iteratedFDeriv ℝ (n - i)
            (fun z : ℝ => F (R * Real.exp (a * z))) y‖) :=
      mul_le_mul_of_nonneg_left hprod hscale
    _ = ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i W y‖ *
          ((m ^ (A + n) * (1 + R) ^ A) *
            ‖iteratedFDeriv ℝ (n - i)
              (fun z : ℝ => F (R * Real.exp (a * z))) y‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hWi : ‖iteratedFDeriv ℝ i W y‖ = 0
      · simp [hWi]
        positivity
      obtain ⟨hLower, hUpper⟩ := hwindow y ⟨i, hi', hWi⟩
      have hGbound := coupled_factor_uniform_derivative F R a y m H CF A n
        (n - i) hFs hR hm hm1 hH ha hLower hUpper (Nat.sub_le n i)
        hCF hFdecay
      have hWbound := hWderiv i hi' y
      gcongr

theorem logProfile_uniform_seminorm
    (W F : ℝ → ℂ) (R a m H L CW CF : ℝ) (A n k : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWderiv : ∀ i ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    m ^ (A + n) * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ k n) (logProfile W F R a hWc hWs hFs) ≤
      L ^ k * (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i))) := by
  let g := logProfile W F R a hWc hWs hFs
  have hgeq : (g : ℝ → ℂ) = fun z => W z * F (R * Real.exp (a * z)) := by
    funext z
    exact logProfile_apply W F R a z hWc hWs hFs
  let scale := m ^ (A + n) * (1 + R) ^ A
  let C := ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * CW *
          ((n - i).factorial * CF * (H ^ 2) ^ (n - i))
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hLC : 0 ≤ L ^ k * C := by positivity
  have hpoint (y : ℝ) :
      scale * (|y| ^ k * ‖iteratedDeriv n g y‖) ≤ L ^ k * C := by
    by_cases hactive : ∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0
    · obtain ⟨hlower, hupper, habs⟩ := hwindow y hactive
      have hraw := logProfile_derivative_decay W F R a m H CW CF A n
        hWs hFs hR hm hm1 hH ha hCW hCF hWderiv
        (by intro z hz; obtain ⟨h₁,h₂,_⟩ := hwindow z hz; exact ⟨h₁,h₂⟩)
        hFdecay y
      have hnorm : scale * ‖iteratedDeriv n g y‖ ≤ C := by
        rw [hgeq]
        simpa [scale, C, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hraw
      calc
        scale * (|y| ^ k * ‖iteratedDeriv n g y‖) =
          |y| ^ k * (scale * ‖iteratedDeriv n g y‖) := by ring
        _ ≤ |y| ^ k * C :=
          mul_le_mul_of_nonneg_left hnorm (pow_nonneg (abs_nonneg _) _)
        _ ≤ L ^ k * C :=
          mul_le_mul_of_nonneg_right (by gcongr) hC
    · have hzero (i : ℕ) (hi : i ≤ n) :
          ‖iteratedFDeriv ℝ i W y‖ = 0 := by
        by_contra hne
        exact hactive ⟨i, hi, hne⟩
      have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
      have hG : ContDiff ℝ ∞ (fun z : ℝ => F (R * Real.exp (a * z))) :=
        hFs.comp harg
      have hprod := norm_iteratedFDeriv_mul_le hWs hG y (n := n) (by simp)
      have hsumzero :
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i W y‖ *
              ‖iteratedFDeriv ℝ (n - i)
                (fun z : ℝ => F (R * Real.exp (a * z))) y‖) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
        ring
      have hnormzero : ‖iteratedDeriv n g y‖ = 0 := by
        have hzero' :
            ‖iteratedFDeriv ℝ n
              (fun z : ℝ => W z * F (R * Real.exp (a * z))) y‖ = 0 :=
          le_antisymm (hprod.trans_eq hsumzero) (norm_nonneg _)
        rw [hgeq]
        simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hzero'
      simp [hnormzero, hLC]
  have hsemi : (SchwartzMap.seminorm ℝ k n) g ≤ L ^ k * C / scale := by
    apply SchwartzMap.seminorm_le_bound' ℝ k n g (div_nonneg hLC hscale.le)
    intro y
    exact (le_div_iff₀ hscale).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hpoint y)
  calc
    scale * (SchwartzMap.seminorm ℝ k n) g ≤ scale * (L ^ k * C / scale) :=
      mul_le_mul_of_nonneg_left hsemi hscale.le
    _ = L ^ k * C := by field_simp

theorem fourier_seminorm_from_derivative_integrals
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) :
    (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by
  have hpoint (w : ℝ) :=
    Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (K := ⊤) (N := ⊤) (f := (g : ℝ → ℂ)) (g.smooth ⊤)
      (by intro a b ha hb; exact g.integrable_pow_mul_iteratedFDeriv volume a b)
      (k := 0) (n := k) (by simp) (by simp) w
  have hpoint' (w : ℝ) :
      ‖w‖ ^ k * ‖(𝓕 g) w‖ ≤
        (2 : ℝ) ^ k *
          ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
            ∫ v : ℝ, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g v‖ := by
    simpa [SchwartzMap.fourier_coe] using hpoint w
  apply SchwartzMap.seminorm_le_bound ℝ k 0 (𝓕 g) (by positivity)
  intro w
  simpa using hpoint' w

theorem uniform_fourier_seminorm_transfer
    (g : 𝓢(ℝ, ℂ)) (k : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (_hC : 0 ≤ C)
