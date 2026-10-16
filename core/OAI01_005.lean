noncomputable def dualPhase (k l : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * ((k : ℝ) * x + (l : ℝ) * y) : ℝ) : ℂ)) * Complex.I)

private theorem shifted_dual_term {t : ℝ} (ht : 0 < t) (x y : ℝ) (k l : ℤ) :
    C t x y *
      RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,l) =
      RankTwoPoisson.eisGauss (4 / (3 * t)) (k,-l) * dualPhase k l x y := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [C, Q, RankTwoAffine.dualGaussian, RankTwoPoisson.eisGauss,
    RankTwoPoisson.eisQ, dualPhase, A, B, D, U, V]
  rw [show RankTwoComplex.schur (t : ℂ) ((-t / 2 : ℝ) : ℂ) (t : ℂ) =
      (((3 * t) / 4 : ℝ) : ℂ) from schur_eis ht]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem shifted_real_gauss_summable {t : ℝ} (ht : 0 < t) (y : ℝ) :
    Summable (fun n : ℤ => Real.exp (-Real.pi * t * ((n : ℝ) + y) ^ 2)) := by
  have ht2 : 0 < t / 2 := by positivity
  have hbase := RankTwoPoisson.real_gauss_summable ht2
  have hmaj : Summable (fun n : ℤ =>
      Real.exp (Real.pi * t * y ^ 2) *
        Real.exp (-Real.pi * (t / 2) * (n : ℝ) ^ 2)) :=
    hbase.mul_left _
  refine hmaj.of_norm_bounded ?_
  intro n
  have hs : (n : ℝ) ^ 2 / 2 - y ^ 2 ≤ ((n : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) + 2 * y)]
  have hm := mul_le_mul_of_nonneg_left hs (mul_pos Real.pi_pos ht).le
  have he : -Real.pi * t * ((n : ℝ) + y) ^ 2 ≤
      Real.pi * t * y ^ 2 + -Real.pi * (t / 2) * (n : ℝ) ^ 2 := by
    nlinarith [hm]
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_add] using
    (Real.exp_le_exp.mpr he)

noncomputable def middlePhase (k n : ℤ) (x y : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * (k : ℝ) * (x - ((n : ℝ) + y) / 2) : ℝ) : ℂ)) * Complex.I)

private theorem middlePhase_norm (k n : ℤ) (x y : ℝ) :
    ‖middlePhase k n x y‖ = 1 := by
  simp [middlePhase, Complex.norm_exp, Complex.mul_re]

private theorem shifted_middle_term {t : ℝ} (ht : 0 < t) (x y : ℝ) (k n : ℤ) :
    C t x y *
      RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,n) =
      RankTwoPoisson.cg ((t⁻¹ : ℝ) : ℂ) k *
        Complex.exp (((-Real.pi * (3 * t / 4) * ((n : ℝ) + y) ^ 2 : ℝ) : ℂ)) *
        middlePhase k n x y := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  dsimp [C, Q, RankTwoAffine.firstGaussian, RankTwoPoisson.cg,
    middlePhase, A, B, D, U, V]
  rw [show RankTwoComplex.schur (t : ℂ) ((-t / 2 : ℝ) : ℂ) (t : ℂ) =
      (((3 * t) / 4 : ℝ) : ℂ) from schur_eis ht]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp [ht0]
  ring_nf
  simp [Complex.I_sq]
  ring

private theorem middle_norm {t : ℝ} (ht : 0 < t) (x y : ℝ) (k n : ℤ) :
    ‖C t x y *
      RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) (k,n)‖ =
      Real.exp (-Real.pi * t⁻¹ * (k : ℝ) ^ 2) *
      Real.exp (-Real.pi * (3 * t / 4) * ((n : ℝ) + y) ^ 2) := by
  rw [shifted_middle_term ht]
  simp [ middlePhase_norm, RankTwoPoisson.cg, Complex.norm_exp,
    ← Complex.ofReal_intCast, ← Complex.ofReal_pow, mul_assoc]

private theorem affine_middle_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have ht3 : 0 < 3 * t / 4 := by positivity
  have h1 := RankTwoPoisson.real_gauss_summable htinv
  have h2 := shifted_real_gauss_summable ht3 y
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * t⁻¹ * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (3 * t / 4) * ((z.2 : ℝ) + y) ^ 2)) :=
    h1.mul_of_nonneg h2 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hCmid : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.firstGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    refine hmaj.of_norm_bounded ?_
    intro z
    rw [middle_norm ht]
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have h := hCmid.mul_left (C t x y)⁻¹
  convert h using 1
  ext z
  simp [hC]

theorem dualPhase_norm (k l : ℤ) (x y : ℝ) :
    ‖dualPhase k l x y‖ = 1 := by
  simp [dualPhase, Complex.norm_exp, Complex.mul_re]

private theorem affine_dual_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have htd : 0 < 4 / (3 * t) := by positivity
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable htd)
  have hCdual : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    refine hE.norm.of_norm_bounded ?_
    intro z
    rw [shifted_dual_term ht]
    simp [ dualPhase_norm]
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have h := hCdual.mul_left (C t x y)⁻¹
  convert h using 1
  ext z
  simp [hC]

private theorem shifted_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (shifted t x y) := by
  have ht4 : 0 < t / 4 := by positivity
  have h1 := RankTwoPoisson.real_gauss_summable ht4
  have hbase : Summable (fun z : ℤ × ℤ =>
      Real.exp (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2) *
      Real.exp (-Real.pi * (t / 4) * (z.2 : ℝ) ^ 2)) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  have hmaj : Summable (fun z : ℤ × ℤ =>
      Real.exp (Real.pi * t * (x ^ 2 + y ^ 2) / 2) *
        (Real.exp (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2) *
         Real.exp (-Real.pi * (t / 4) * (z.2 : ℝ) ^ 2))) :=
    hbase.mul_left _
  refine hmaj.of_norm_bounded ?_
  intro z
  have hq : (((z.1 : ℝ) + x) ^ 2 + ((z.2 : ℝ) + y) ^ 2) / 2 ≤
      Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) := by
    dsimp [Q]
    nlinarith [sq_nonneg (((z.1 : ℝ) + x) - ((z.2 : ℝ) + y))]
  have hm : (z.1 : ℝ) ^ 2 / 2 - x ^ 2 ≤ ((z.1 : ℝ) + x) ^ 2 := by
    nlinarith [sq_nonneg ((z.1 : ℝ) + 2 * x)]
  have hn : (z.2 : ℝ) ^ 2 / 2 - y ^ 2 ≤ ((z.2 : ℝ) + y) ^ 2 := by
    nlinarith [sq_nonneg ((z.2 : ℝ) + 2 * y)]
  have hl : ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) / 4 -
      (x ^ 2 + y ^ 2) / 2 ≤ Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) := by
    nlinarith [hq, hm, hn]
  have hpt : 0 ≤ Real.pi * t := (mul_pos Real.pi_pos ht).le
  have hmul := mul_le_mul_of_nonneg_left hl hpt
  have he : -Real.pi * t * Q ((z.1 : ℝ) + x) ((z.2 : ℝ) + y) ≤
      Real.pi * t * (x ^ 2 + y ^ 2) / 2 +
        (-Real.pi * (t / 4) * (z.1 : ℝ) ^ 2 +
         -Real.pi * (t / 4) * (z.2 : ℝ) ^ 2) := by
    nlinarith [hmul]
  simpa [shifted, Complex.norm_exp, Real.exp_add, mul_assoc] using
    (Real.exp_le_exp.mpr he)

private theorem affine_original_summable {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    Summable (RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y)) := by
  have hS := shifted_summable ht x y
  have hC : C t x y ≠ 0 := Complex.exp_ne_zero _
  have hCA : Summable (fun z : ℤ × ℤ =>
      C t x y * RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) :=
    hS.congr (fun z => shifted_eq_affine t x y z.1 z.2)
  have h := hCA.mul_left (C t x y)⁻¹
  convert h using 1
  ext z
  simp [hC]

theorem shifted_eisenstein_gaussian_poisson {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    (∑' z : ℤ × ℤ, shifted t x y z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2) *
            dualPhase z.1 z.2 x y := by
  have ha : 0 < (A t).re := by simpa [A] using ht
  have hδ := schur_eis_pos ht
  have hO := affine_original_summable ht x y
  have hM := affine_middle_summable ht x y
  have hD := affine_dual_summable ht x y
  let pref : ℂ :=
    (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
      (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ))
  have haff :
      (∑' z : ℤ × ℤ,
        RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) =
      pref * (∑' z : ℤ × ℤ,
        RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
    have h := RankTwoAffine.affine_gaussian_poisson ha hδ hO hM hD
    rw [schur_eis ht] at h
    exact h
  calc
    (∑' z : ℤ × ℤ, shifted t x y z) =
        C t x y * (∑' z : ℤ × ℤ,
          RankTwoAffine.binaryGaussian (A t) (B t) (D t) (U t x y) (V t x y) z) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro z
      exact shifted_eq_affine t x y z.1 z.2
    _ = C t x y * (pref * (∑' z : ℤ × ℤ,
          RankTwoAffine.dualGaussian (A t) (B t) (D t) (U t x y) (V t x y) z)) := by
      rw [haff]
    _ = pref * (∑' z : ℤ × ℤ,
          C t x y * RankTwoAffine.dualGaussian (A t) (B t) (D t)
            (U t x y) (V t x y) z) := by
      rw [tsum_mul_left]
      ring
    _ = pref * (∑' z : ℤ × ℤ,
          RankTwoPoisson.eisGauss (4 / (3 * t)) (z.1,-z.2) *
            dualPhase z.1 z.2 x y) := by
      congr 1
      apply tsum_congr
      intro z
      exact shifted_dual_term ht x y z.1 z.2

end RankTwoEisShift

end

end OAI
end OAIOriginalModule0062

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.GaussianDualLimit
Source SHA256: f665567f3702c04d2a05c64ef2850f7a9eac3e67d6a3ab6f4594892fcda67d91
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0063


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical

namespace ActualEisensteinCubic

theorem principal_absNorm_pow (p : O) (k : ℕ) :
    Ideal.absNorm (Ideal.span {p ^ k}) =
      (Ideal.absNorm (Ideal.span {p})) ^ k := by
  rw [← Ideal.span_singleton_pow]
  exact map_pow Ideal.absNorm (Ideal.span {p}) k

theorem sixth_power_rows_within_norm_cutoff
    {β : Type*} (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (hD : 1 ≤ D)
    (hupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hcover : ∀ u : O,
      (Ideal.absNorm (Ideal.span {u}) : ℝ) ≤
        (D : ℝ) ^ (11 / 10 : ℝ) → u ∈ rows) :
    selected.image (fun i => p i ^ 6) ⊆ rows := by
  classical
  intro u hu
  rcases Finset.mem_image.mp hu with ⟨i, hi, rfl⟩
  apply hcover
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  calc
    (Ideal.absNorm (Ideal.span {p i ^ 6}) : ℝ) =
        (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ 6 := by
          exact_mod_cast principal_absNorm_pow (p i) 6
    _ ≤ ((D : ℝ) ^ (11 / 60 : ℝ)) ^ 6 := by
          gcongr
          exact hupper i hi
    _ = (D : ℝ) ^ (11 / 10 : ℝ) := by
          rw [← Real.rpow_mul_natCast hDpos.le (11 / 60 : ℝ) 6]
          congr 1
          norm_num

end ActualEisensteinCubic
namespace OscillatoryDeterminant

open Complex

private def q (a b : ℂ) : ℂ := a*a-a*b+b*b

private noncomputable def A (t a b : ℂ) : ℂ := t + 2*Complex.I*b/q a b
private noncomputable def B (t a b : ℂ) : ℂ := -t/2-2*Complex.I*a/q a b
private noncomputable def D (t a b : ℂ) : ℂ := t + 2*Complex.I*(a-b)/q a b

theorem determinant (t a b : ℂ) (hq : q a b ≠ 0) :
    A t a b * D t a b - (B t a b)^2 =
      4/q a b + 3*t^2/4 := by
  dsimp [A, B, D]
  field_simp [hq]
  dsimp [q]
  ring_nf
  simp [Complex.I_sq]
  ring

end OscillatoryDeterminant

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_bilinear_coordinates (u v m n : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (ActualEisensteinCoordinates.eval u v) *
        eisEmbedding (ActualEisensteinCoordinates.eval m n) / eisLam) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((u*n+v*m-v*n : ℤ) : ℂ)) := by
  rw [← map_mul, ActualEisensteinCoordinates.eval_mul]
  rw [eisEmbedding_eval]
  simpa using
    breveE_int_trace_div 1 (u*m-v*n) (u*n+v*m-v*n) (by norm_num)

theorem breveE_standard_dual_frequency (k l m n : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (ActualEisensteinCoordinates.eval (k+l) k) *
        eisEmbedding (ActualEisensteinCoordinates.eval m n) / eisLam) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((k*m+l*n : ℤ) : ℂ)) := by
  rw [breveE_bilinear_coordinates]
  congr 1
  push_cast
  ring

end ActualEisensteinCubic
namespace EisensteinFiberShift

def Q (x y : ℝ) : ℝ := x*x-x*y+y*y
def q (a b : ℝ) : ℝ := Q a b
noncomputable def shiftX (a b x y : ℝ) : ℝ := ((a-b)*x+b*y)/q a b
noncomputable def shiftY (a b x y : ℝ) : ℝ := (-b*x+a*y)/q a b

theorem exact_shift (a b x y m n : ℝ) (hq : q a b ≠ 0) :
    Q (x+a*m-b*n) (y+b*m+(a-b)*n) =
      q a b * Q (m+shiftX a b x y) (n+shiftY a b x y) := by
  dsimp [shiftX, shiftY, Q]
  field_simp [hq]
  dsimp [q, Q]
  ring

end EisensteinFiberShift

namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

noncomputable def rowNormBall (H : ℕ) : Finset O := by
  classical
  let I : Finset ℤ := Finset.Icc (-((H : ℤ) + 1)) ((H : ℤ) + 1)
  exact (I.product I).image (fun v => eval v.1 v.2)

theorem mem_rowNormBall_of_qNat_le (H : ℕ) (u : O)
    (h : qNat u ≤ H) : u ∈ rowNormBall H := by
  classical
  have hq : q (coords u) ≤ (H : ℤ) := by
    change (q (coords u)).toNat ≤ H at h
    have hnonneg := qO_nonneg u
    omega
  let a := (coords u).1
  let b := (coords u).2
  have hab : a ^ 2 - a * b + b ^ 2 ≤ (H : ℤ) := hq
  obtain ⟨ha2, hb2⟩ := coordinate_squares a b (H : ℤ)
    (by positivity) hab
  have hH : (0 : ℤ) ≤ H := by positivity
  have haL : -((H : ℤ) + 1) ≤ a := by nlinarith [sq_nonneg (H : ℤ)]
  have haU : a ≤ (H : ℤ) + 1 := by nlinarith [sq_nonneg (H : ℤ)]
  have hbL : -((H : ℤ) + 1) ≤ b := by nlinarith [sq_nonneg (H : ℤ)]
  have hbU : b ≤ (H : ℤ) + 1 := by nlinarith [sq_nonneg (H : ℤ)]
  unfold rowNormBall
  apply Finset.mem_image.mpr
  refine ⟨coords u, ?_, eval_coords u⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨haL, haU⟩,
     Finset.mem_Icc.mpr ⟨hbL, hbU⟩⟩

theorem mem_rowNormBall_of_absNorm_le (H : ℕ) (u : O)
    (h : Ideal.absNorm (Ideal.span {u}) ≤ H) :
    u ∈ rowNormBall H := by
  apply mem_rowNormBall_of_qNat_le
  simpa only [ActualEisensteinCubic.qNat_eq_absNorm_span] using h

end ShortDraftLatticeCount
namespace EisensteinGaussianPrefactor

theorem sqrt_product (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt t * Real.sqrt (3*t/4) =
      Real.sqrt 3 * t / 2 := by
  have h3 : Real.sqrt (3/4 : ℝ) = Real.sqrt 3 / 2 := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 3)]
    rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have harg : 3*t/4 = (3/4:ℝ)*t := by ring
  rw [harg, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3/4), h3]
  calc
    Real.sqrt t * (Real.sqrt 3 / 2 * Real.sqrt t) =
        Real.sqrt 3 / 2 * (Real.sqrt t)^2 := by ring
    _ = Real.sqrt 3 * t / 2 := by rw [Real.sq_sqrt ht]; ring

theorem eta_times_prefactor (η q : ℝ) (hη : 0 < η) (hq : 0 < q) :
    η * (1 / Real.sqrt (η*q)) *
      (1 / Real.sqrt (3*(η*q)/4)) =
      2 / (Real.sqrt 3 * q) := by
  have ht : 0 < η*q := mul_pos hη hq
  have hsqrt : Real.sqrt (η*q) * Real.sqrt (3*(η*q)/4) =
      Real.sqrt 3 * (η*q) / 2 := sqrt_product (η*q) ht.le
  have hne1 : Real.sqrt (η*q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hne2 : Real.sqrt (3*(η*q)/4) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    positivity
  have hne3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  calc
    η * (1 / Real.sqrt (η*q)) *
        (1 / Real.sqrt (3*(η*q)/4)) =
        η / (Real.sqrt (η*q) * Real.sqrt (3*(η*q)/4)) := by ring
    _ = η / (Real.sqrt 3 * (η*q) / 2) := by rw [hsqrt]
    _ = 2 / (Real.sqrt 3 * q) := by
      field_simp

end EisensteinGaussianPrefactor

namespace ActualEisensteinCubic

theorem sixth_power_rows_in_rowNormBall
    {β : Type*} (selected : Finset β) (p : β → O)
    (D H : ℕ) (hD : 1 ≤ D)
    (hupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : (D : ℝ) ^ (11 / 10 : ℝ) ≤ (H : ℝ)) :
    selected.image (fun i => p i ^ 6) ⊆
      ShortDraftLatticeCount.rowNormBall H := by
  apply sixth_power_rows_within_norm_cutoff selected p
    (ShortDraftLatticeCount.rowNormBall H) D hD hupper
  intro u hu
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le H
  exact_mod_cast hu.trans hH

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_oscillatory_gaussian_coordinate
    (a b m n : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval m n
    (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ)) =
      Complex.exp (-(Real.pi : ℂ) *
        ((η : ℂ) * ((m*m-m*n+n*n : ℤ) : ℂ) -
          2 * Complex.I *
            (((-b*m*m+2*a*m*n+(b-a)*n*n : ℤ) : ℂ) /
              ((a*a-a*b+b*b : ℤ) : ℂ)))) := by
  dsimp only
  rw [quadraticTraceModChar_coordinate a b m n hc]
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval m n)‖ : ℂ)^2) =
      ((m*m-m*n+n*n : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_eval_norm_sq m n
  rw [hnormC]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end ActualEisensteinCubic

namespace EisensteinGaussianPrefactor

theorem complex_eta_times_prefactor (η q : ℝ) (hη : 0 < η) (hq : 0 < q) :
    (η : ℂ) *
      (1 / ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ)) *
      (1 / (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ))) =
      ((2 / (Real.sqrt 3 * q) : ℝ) : ℂ) := by
  have ht : 0 ≤ η*q := (mul_pos hη hq).le
  have hs : 0 ≤ 3*(η*q)/4 := by positivity
  have hpow1 : ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ) =
      (Real.sqrt (η*q) : ℂ) := by
    calc
      ((η*q : ℝ) : ℂ) ^ (1/2 : ℂ) =
          ((η*q : ℝ) : ℂ) ^ (((1/2 : ℝ) : ℂ)) := by norm_num
      _ = (((η*q) ^ (1/2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow ht (1/2 : ℝ)).symm
      _ = (Real.sqrt (η*q) : ℂ) := by rw [← Real.sqrt_eq_rpow]
  have hpow2 : (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ)) =
      (Real.sqrt (3*(η*q)/4) : ℂ) := by
    calc
      (((3*(η*q)/4 : ℝ) : ℂ) ^ (1/2 : ℂ)) =
          (((3*(η*q)/4 : ℝ) : ℂ) ^ (((1/2 : ℝ) : ℂ))) := by norm_num
      _ = (((3*(η*q)/4) ^ (1/2 : ℝ) : ℝ) : ℂ) :=
        (Complex.ofReal_cpow hs (1/2 : ℝ)).symm
      _ = (Real.sqrt (3*(η*q)/4) : ℂ) := by rw [← Real.sqrt_eq_rpow]
  rw [hpow1, hpow2]
  exact_mod_cast eta_times_prefactor η q hη hq

end EisensteinGaussianPrefactor

namespace ActualEisensteinCubic

theorem finite_actual_prime_extraction_dyadic_ball
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : (D : ℝ) ^ (11 / 10 : ℝ) ≤ (H : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ ShortDraftLatticeCount.rowNormBall H,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      384 * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  apply finite_actual_prime_extraction_dyadic P hgood columns support weight
    selected p (ShortDraftLatticeCount.rowNormBall H) D ε hD hε hp hprime
    hinj ?_ hsupport hcolnorm hweight hnormlower hcount hmean
  exact sixth_power_rows_in_rowNormBall selected p D H hD hnormupper hH

end ActualEisensteinCubic
namespace OscillatoryDeterminant

open Complex

noncomputable def r (t a b : ℂ) : ℂ := 1 + 3 * q a b * t^2 / 16

theorem inverse_quadratic (t a b k l : ℂ)
    (hq : q a b ≠ 0) (hr : r t a b ≠ 0) :
    (D t a b * k^2 - 2 * B t a b * k*l + A t a b * l^2) /
      (A t a b * D t a b - (B t a b)^2) =
      (t * q a b / (4 * r t a b)) * (k^2+k*l+l^2) +
        Complex.I / (2 * r t a b) *
          ((a-b)*k^2+2*a*k*l+b*l^2) := by
  rw [determinant t a b hq]
  have hden : 4/q a b + 3*t^2/4 = 4*r t a b/q a b := by
    dsimp [r]
    field_simp [hq]
    ring
  rw [hden]
  dsimp [A, B, D]
  field_simp [hq, hr]
  dsimp [q] at *
  ring_nf
  try simp [Complex.I_sq]

end OscillatoryDeterminant
open Filter Real Asymptotics

private theorem cheby_small_log :
    ∀ᶠ Y : ℝ in atTop, Real.log (Y + 2) ≤ (Real.log 2 / 80) * (Y + 2) := by
  have hsmall : (fun x : ℝ => Real.log x) =o[atTop] id := by
    simpa only [pow_one] using (Real.isLittleO_pow_log_id_atTop (n := 1))
  have hbound := hsmall.bound (by positivity : 0 < Real.log (2 : ℝ) / 80)
  have hshift : Tendsto (fun Y : ℝ => Y + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  filter_upwards [hshift.eventually hbound,
    eventually_ge_atTop (1 : ℝ)] with Y hY hY1
  simpa only [Function.comp_def, id_eq, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ Y + 2)),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ Y + 2)] using hY

theorem rational_prime_three_interval_real_count :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((Real.log 2) / 20) * (Y / Real.log Y) ≤
        (Nat.primeCounting ⌊Y⌋₊ : ℝ) -
          (Nat.primeCounting ⌊Y / 3⌋₊ : ℝ) := by
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hε : 0 < Real.log (2 : ℝ) / 4 := by positivity
  obtain ⟨X₀, hX₀⟩ := (eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le hε))
  obtain ⟨X₁, hX₁⟩ := (eventually_atTop.1 cheby_small_log)
  refine ⟨max 729 (max (3 * X₀) X₁), ?_⟩
  intro Y hY
  have hY729 : (729 : ℝ) ≤ Y := le_trans (le_max_left _ _) hY
  have hYX₀ : X₀ ≤ Y / 3 := by
    linarith [le_max_left (3 * X₀) X₁, le_max_right (729 : ℝ) (max (3 * X₀) X₁)]
  have hYX₁ : X₁ ≤ Y := by
    linarith [le_max_right (3 * X₀) X₁, le_max_right (729 : ℝ) (max (3 * X₀) X₁)]
  have hYpos : (0 : ℝ) < Y := by linarith
  have hY3pos : (0 : ℝ) < Y / 3 := by positivity
  have hlogYpos : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogY3pos : 0 < Real.log (Y / 3) := Real.log_pos (by linarith)
  have hlog3 : 6 * Real.log (3 : ℝ) ≤ Real.log Y := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 729) hY729
    calc
      6 * Real.log (3 : ℝ) = Real.log ((3 : ℝ) ^ 6) := by rw [Real.log_pow]; ring
      _ = Real.log 729 := by norm_num
      _ ≤ Real.log Y := h
  have hlogY3 : 5 / 6 * Real.log Y ≤ Real.log (Y / 3) := by
    rw [Real.log_div (ne_of_gt hYpos) (by norm_num : (3 : ℝ) ≠ 0)]
    linarith
  have hlogerror : Real.log (Y + 2) ≤ (Real.log 2 / 40) * Y := by
    have hbound := hX₁ Y hYX₁
    have hprod : 0 ≤ Real.log 2 * (Y - 2) :=
      mul_nonneg hlog2pos.le (by linarith)
    nlinarith
  have hconsterror : Real.log (2 : ℝ) ≤ (Real.log 2 / 40) * Y := by
    have hprod : 0 ≤ Real.log 2 * (Y - 40) :=
      mul_nonneg hlog2pos.le (by linarith)
    nlinarith
  have hnumlo : (19 / 20 : ℝ) * Real.log 2 * Y ≤
      (Y - 1) * Real.log 2 - Real.log (Y + 2) := by
    nlinarith [hlogerror, hconsterror]
  have hPlo : (19 / 20 : ℝ) * Real.log 2 * (Y / Real.log Y) ≤
      (Nat.primeCounting ⌊Y⌋₊ : ℝ) := by
    calc
      _ = ((19 / 20 : ℝ) * Real.log 2 * Y) / Real.log Y := by ring
      _ ≤ ((Y - 1) * Real.log 2 - Real.log (Y + 2)) / Real.log Y :=
        (div_le_div_of_nonneg_right hnumlo hlogYpos.le)
      _ ≤ _ := Chebyshev.pi_ge' (by linarith)
  have hfrac : (Y / 3) / Real.log (Y / 3) ≤ (2 / 5 : ℝ) * (Y / Real.log Y) := by
    have hprod : 0 ≤ Y * (Real.log (Y / 3) - 5 / 6 * Real.log Y) :=
      mul_nonneg hYpos.le (sub_nonneg.mpr hlogY3)
    have hq : (Y / 3) / Real.log (Y / 3) ≤
        ((2 / 5 : ℝ) * Y) / Real.log Y := by
      apply (div_le_div_iff₀ hlogY3pos hlogYpos).mpr
      nlinarith
    convert hq using 1 ; ring
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; ring
  have hcoeff : 0 ≤ Real.log 4 + Real.log 2 / 4 := by positivity
  have hPup : (Nat.primeCounting ⌊Y / 3⌋₊ : ℝ) ≤
      (9 / 10 : ℝ) * Real.log 2 * (Y / Real.log Y) := by
    calc
      _ ≤ (Real.log 4 + Real.log 2 / 4) * ((Y / 3) / Real.log (Y / 3)) :=
        by simpa only [mul_div_assoc] using hX₀ (Y / 3) hYX₀
      _ ≤ (Real.log 4 + Real.log 2 / 4) * ((2 / 5 : ℝ) * (Y / Real.log Y)) :=
        mul_le_mul_of_nonneg_left hfrac hcoeff
      _ = (9 / 10 : ℝ) * Real.log 2 * (Y / Real.log Y) := by rw [hlog4]; ring
  have htarget : (Real.log 2 / 20) * (Y / Real.log Y) =
      ((19 / 20 : ℝ) - 9 / 10) * Real.log 2 * (Y / Real.log Y) := by ring
  rw [htarget]
  linarith

theorem rational_prime_three_interval_count :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      ((Real.log 2) / 20) * (Y / Real.log Y) ≤
        (((Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime).card : ℝ) := by
  obtain ⟨Y₀, hY₀⟩ := rational_prime_three_interval_real_count
  refine ⟨max 729 Y₀, ?_⟩
  intro Y hY
  have hY729 : (729 : ℝ) ≤ Y := le_trans (le_max_left _ _) hY
  have hfloor : ⌊Y / 3⌋₊ ≤ ⌊Y⌋₊ :=
    Nat.floor_mono (by linarith : Y / 3 ≤ Y)
  have hsubset : Nat.primesLE ⌊Y / 3⌋₊ ⊆ Nat.primesLE ⌊Y⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.mem_primesLE.mp hp).1.trans hfloor, (Nat.mem_primesLE.mp hp).2⟩
  have hset : (Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime =
      Nat.primesLE ⌊Y⌋₊ \ Nat.primesLE ⌊Y / 3⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hp⟩
      exact ⟨⟨hhi, hp⟩, fun hh => (not_le_of_gt hlo) hh.1⟩
    · rintro ⟨⟨hhi, hp⟩, hnot⟩
      exact ⟨⟨lt_of_not_ge (fun hle => hnot ⟨hle, hp⟩), hhi⟩, hp⟩
  have hcard : ((Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime).card =
      Nat.primeCounting ⌊Y⌋₊ - Nat.primeCounting ⌊Y / 3⌋₊ := by
    rw [hset, Finset.card_sdiff_of_subset hsubset,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hpile : Nat.primeCounting ⌊Y / 3⌋₊ ≤ Nat.primeCounting ⌊Y⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting,
      ← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card hsubset
  rw [hcard, Nat.cast_sub hpile]
  exact hY₀ Y (le_trans (le_max_right _ _) hY)

namespace RankTwoLimit

section

open scoped Topology

open RankTwoPoisson RankTwoEisShift Filter

private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]

private theorem eisQ_pos {z : ℤ × ℤ} (hz : z ≠ (0,0)) :
    0 < RankTwoPoisson.eisQ z := by
  by_cases hm : z.1 = 0
  · have hn : z.2 ≠ 0 := by
      intro h0
      exact hz (Prod.ext hm h0)
    have hnR : (z.2 : ℝ) ≠ 0 := by exact_mod_cast hn
    have h := RankTwoPoisson.eisQ_lower z
    nlinarith [sq_pos_of_ne_zero hnR]
  · have hmR : (z.1 : ℝ) ≠ 0 := by exact_mod_cast hm
    have h := RankTwoPoisson.eisQ_lower z
    nlinarith [sq_pos_of_ne_zero hmR, sq_nonneg (z.2 : ℝ)]

private theorem eisGauss_norm (T : ℝ) (z : ℤ × ℤ) :
    ‖RankTwoPoisson.eisGauss T z‖ =
      Real.exp (-Real.pi * T * RankTwoPoisson.eisQ z) := by
  simp [RankTwoPoisson.eisGauss, Complex.norm_exp]

noncomputable def dualTerm (T : ℝ) (x y : ℝ) (z : ℤ × ℤ) : ℂ :=
  RankTwoPoisson.eisGauss T (z.1,-z.2) * RankTwoEisShift.dualPhase z.1 z.2 x y

noncomputable def limitTerm (z : ℤ × ℤ) : ℂ :=
  if z = (0,0) then 1 else 0

private theorem dualTerm_tendsto (x y : ℝ) (z : ℤ × ℤ) :
    Tendsto (fun T : ℝ => dualTerm T x y z) atTop (𝓝 (limitTerm z)) := by
  by_cases hz : z = (0,0)
  · subst z
    simp [dualTerm, limitTerm, RankTwoPoisson.eisGauss,
      RankTwoPoisson.eisQ, RankTwoEisShift.dualPhase]
  · have hz' : (z.1,-z.2) ≠ ((0,0) : ℤ × ℤ) := by
      intro h
      apply hz
      have h1 : z.1 = 0 := by simpa using congrArg Prod.fst h
      have h2 : z.2 = 0 := by simpa using congrArg Prod.snd h
      exact Prod.ext h1 h2
    have hq := eisQ_pos hz'
    have hneg : -Real.pi * RankTwoPoisson.eisQ (z.1,-z.2) < 0 := by
      nlinarith [mul_pos Real.pi_pos hq]
    have harg : Tendsto
        (fun T : ℝ => -Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2))
        atTop atBot := by
      convert tendsto_id.const_mul_atTop_of_neg hneg using 1
      ext T
      simp [mul_assoc, mul_comm]
    have hexp : Tendsto
        (fun T : ℝ => Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp harg
    have hc : Tendsto (fun T : ℝ => RankTwoPoisson.eisGauss T (z.1,-z.2))
        atTop (𝓝 (0 : ℂ)) := by
      have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp hexp
      have heq : (fun T : ℝ =>
          ((Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)) : ℝ) : ℂ)) =
          (fun T : ℝ => RankTwoPoisson.eisGauss T (z.1,-z.2)) := by
        funext T
        simp [RankTwoPoisson.eisGauss, Complex.ofReal_exp]
      change Tendsto (fun T : ℝ =>
        ((Real.exp (-Real.pi * T * RankTwoPoisson.eisQ (z.1,-z.2)) : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) at hh
      rw [heq] at hh
      exact hh
    simpa [dualTerm, limitTerm, hz] using
      hc.mul_const (RankTwoEisShift.dualPhase z.1 z.2 x y)

theorem dual_sum_tendsto_one (x y : ℝ) :
    Tendsto (fun T : ℝ => ∑' z : ℤ × ℤ, dualTerm T x y z)
      atTop (𝓝 (1 : ℂ)) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss 1 (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable (by norm_num))
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ z : ℤ × ℤ,
      ‖dualTerm T x y z‖ ≤ ‖RankTwoPoisson.eisGauss 1 (z.1,-z.2)‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT z
    rw [dualTerm, norm_mul, RankTwoEisShift.dualPhase_norm, mul_one,
      eisGauss_norm, eisGauss_norm]
    have hq := eisQ_nonneg (z.1,-z.2)
    have hpq : 0 ≤ Real.pi * RankTwoPoisson.eisQ (z.1,-z.2) :=
      mul_nonneg Real.pi_pos.le hq
    have hm := mul_le_mul_of_nonneg_right hT hpq
    apply Real.exp_le_exp.mpr
    nlinarith [hm]
  have h := tendsto_tsum_of_dominated_convergence hE.norm
    (dualTerm_tendsto x y) hbound
  simpa [limitTerm] using h

end

open scoped Topology
open Filter

theorem dual_sum_tendsto_one_small_t (x y : ℝ) :
    Tendsto (fun t : ℝ => ∑' z : ℤ × ℤ, dualTerm (4 / (3 * t)) x y z)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hT : Tendsto (fun t : ℝ => (4 / 3 : ℝ) * t⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4 / 3)).2
      tendsto_inv_nhdsGT_zero
  have h := (dual_sum_tendsto_one x y).comp hT
  simpa [Function.comp_def, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

end RankTwoLimit

end

end OAI
end OAIOriginalModule0063

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.GaussianFiberMass
Source SHA256: 3a282037cb84afc186e3f2e374369543ca08f14fdd7529d3eddf48d9cf995690
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0064


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_real_trace_div (r : ℝ) (u v : ℤ) :
    ShortDraftTrace.breveE
      ((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / (r : ℂ)) := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj u v
  have hL : ((u : ℂ) + (v : ℂ) * omega3) / eisLam +
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) = (v : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ)) +
      star (((((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ))))) = _
  rw [show star (((u : ℂ) + (v : ℂ) * omega3) / eisLam / (r : ℂ)) =
      star (((u : ℂ) + (v : ℂ) * omega3) / eisLam) / (r : ℂ) by simp]
  rw [← add_div, hL]
  congr 1
  ring

theorem breveE_real_trace_of_O (r : ℝ) (z : O) :
    ShortDraftTrace.breveE (eisEmbedding z / eisLam / (r : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((ActualEisensteinCoordinates.coords z).2 : ℂ) / (r : ℂ)) := by
  rw [← ActualEisensteinCoordinates.eval_coords z]
  rw [eisEmbedding_eval]
  simp only [ShortDraftLatticeCount.coords_eval]
  exact breveE_real_trace_div r _ _

end ActualEisensteinCubic
namespace SqrtBranch
open Complex

private theorem arg_ne_pi_of_re_pos {a : ℂ} (ha : 0 < a.re) : a.arg ≠ Real.pi := by
  intro h
  have := (Complex.arg_eq_pi_iff.mp h).1
  linarith

theorem cpow_half_product {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    a ^ (1 / 2 : ℂ) * (((r : ℂ) / a) ^ (1 / 2 : ℂ)) =
      (r : ℂ) ^ (1 / 2 : ℂ) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have harg := arg_ne_pi_of_re_pos ha
  have hlog : Complex.log ((r : ℂ) / a) = (Real.log r : ℂ) - Complex.log a := by
    rw [div_eq_mul_inv, Complex.log_ofReal_mul hr (inv_ne_zero ha0),
      Complex.log_inv a harg]
    ring
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hdiv : (r : ℂ) / a ≠ 0 := div_ne_zero hr0 ha0
  rw [Complex.cpow_def_of_ne_zero ha0,
    Complex.cpow_def_of_ne_zero hdiv,
    Complex.cpow_def_of_ne_zero hr0, hlog, ← Complex.exp_add]
  congr 1
  rw [Complex.ofReal_log hr.le]
  ring

theorem prefactor_product {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    (1 / a ^ (1 / 2 : ℂ)) * (1 / (((r : ℂ) / a) ^ (1 / 2 : ℂ))) =
      1 / ((r : ℂ) ^ (1 / 2 : ℂ)) := by
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm] using
    congrArg (fun z : ℂ => z⁻¹) (cpow_half_product ha hr)

end SqrtBranch

namespace PowerExtraction

theorem from_mean_square_and_prime_rows_with_loss
    (D ε J A C M : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ M * J)
    (hmean : J * A ^ 2 ≤
      2 * M * D ^ ((21 / 10 : ℝ) + ε) +
        2 * J * C ^ 2 * D ^ (49 / 30 : ℝ)) :
    A ≤ 2 * (M + C) * D ^ ((23 / 24 : ℝ) + ε) := by
  let E : ℝ := (23 / 24 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hMJpos : 0 < M * J :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hcount
  have hJpos : 0 < J := by
    nlinarith
  have hbase : D ^ ((21 / 10 : ℝ) + ε) ≤
      (M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      D ^ ((21 / 10 : ℝ) + ε) =
          D ^ ((11 / 60 : ℝ) - ε) *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              rw [← Real.rpow_add hDpos]
              congr 1
              ring
      _ ≤ (M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
  have hpow : M * D ^ ((21 / 10 : ℝ) + ε) ≤
      M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      M * D ^ ((21 / 10 : ℝ) + ε) ≤
          M * ((M * J) * D ^ ((23 / 12 : ℝ) + 2 * ε)) :=
            mul_le_mul_of_nonneg_left hbase hMpos.le
      _ = M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by ring
  have herr : D ^ (49 / 30 : ℝ) ≤
      D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hcoeff : 2 * M ^ 2 + 2 * C ^ 2 ≤ 4 * (M + C) ^ 2 := by
    nlinarith [mul_nonneg hMpos.le hCpos.le]
  have hT : 0 ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by positivity
  have hmain : J * A ^ 2 ≤
      4 * (M + C) ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      J * A ^ 2 ≤
          2 * M * D ^ ((21 / 10 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) := hmean
      _ ≤ 2 * (M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              have hleft :
                  2 * M * D ^ ((21 / 10 : ℝ) + ε) ≤
                    2 * (M ^ 2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε)) := by
                nlinarith [hpow]
              have hright :
                  2 * J * C ^ 2 * D ^ (49 / 30 : ℝ) ≤
                    2 * J * C ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
                exact mul_le_mul_of_nonneg_left herr (by positivity)
              linarith
      _ = (2 * M ^ 2 + 2 * C ^ 2) *
            (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) := by ring
      _ ≤ 4 * (M + C) ^ 2 *
            (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) :=
              mul_le_mul_of_nonneg_right hcoeff hT
      _ = 4 * (M + C) ^ 2 * J *
            D ^ ((23 / 12 : ℝ) + 2 * ε) := by ring
  have hsq : A ^ 2 ≤
      4 * (M + C) ^ 2 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    nlinarith
  have hexp : (23 / 12 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((23 / 12 : ℝ) + 2 * ε) := by rw [hexp]
  have htarget : 0 ≤ 2 * (M + C) * D ^ E := by positivity
  apply (sq_le_sq₀ hA htarget).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith

end PowerExtraction

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_fiber_gaussian_eq_shifted
    (a b x y m n : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) (η : ℝ) :
    Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding
        (ActualEisensteinCoordinates.eval x y +
          ActualEisensteinCoordinates.eval a b *
            ActualEisensteinCoordinates.eval m n)‖ ^ 2 : ℂ)) =
      RankTwoEisShift.shifted
        (η * ((a*a-a*b+b*b : ℤ) : ℝ))
        (EisensteinFiberShift.shiftX (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ))
        (EisensteinFiberShift.shiftY (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ))
        (m,n) := by
  have hqZ : a*a-a*b+b*b ≠ 0 :=
    ne_of_gt (coordinate_norm_pos_of_nonzero a b hc)
  have hqR : EisensteinFiberShift.q (a : ℝ) (b : ℝ) ≠ 0 := by
    dsimp [EisensteinFiberShift.q, EisensteinFiberShift.Q]
    exact_mod_cast hqZ
  have hshift := EisensteinFiberShift.exact_shift
    (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ) (m : ℝ) (n : ℝ) hqR
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval x y +
        ActualEisensteinCoordinates.eval a b *
          ActualEisensteinCoordinates.eval m n)‖ : ℂ)^2) =
      (((a*a-a*b+b*b)*(m*m-m*n+n*n) +
        ((2*a-b)*x+(2*b-a)*y)*m +
        (-(a+b)*x+(2*a-b)*y)*n +
        (x*x-x*y+y*y) : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_fiber_norm_sq a b x y m n
  rw [hnormC]
  dsimp [RankTwoEisShift.shifted, RankTwoEisShift.Q]
  congr 1
  dsimp [EisensteinFiberShift.Q, EisensteinFiberShift.q] at hshift
  have hshiftC := congrArg (fun v : ℝ => (v : ℂ)) hshift
  push_cast at hshiftC ⊢
  linear_combination -(Real.pi : ℂ) * (η : ℂ) * hshiftC

end ActualEisensteinCubic

namespace EisensteinAbelFiber

open scoped Topology
open Filter

theorem shifted_gaussian_mass (x y : ℝ) :
    Tendsto (fun t : ℝ => (t : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z))
      (𝓝[>] (0 : ℝ)) (𝓝 (((2 / Real.sqrt 3 : ℝ) : ℂ))) := by
  have hpoint (t : ℝ) (ht : 0 < t) :
      (t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z) =
        ((2 / Real.sqrt 3 : ℝ) : ℂ) *
          (∑' z : ℤ × ℤ, RankTwoLimit.dualTerm (4 / (3 * t)) x y z) := by
    rw [RankTwoEisShift.shifted_eisenstein_gaussian_poisson ht x y]
    have hpre := EisensteinGaussianPrefactor.complex_eta_times_prefactor
      t 1 ht (by norm_num)
    simp only [mul_one] at hpre
    change (t : ℂ) *
        ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) = _
    calc
      (t : ℂ) * ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) =
        (((t : ℂ) * (1 / (t : ℂ) ^ (1 / 2 : ℂ))) *
          (1 / (((3 * t / 4 : ℝ) : ℂ) ^ (1 / 2 : ℂ)))) *
          (∑' z : ℤ × ℤ,
            RankTwoLimit.dualTerm (4 / (3 * t)) x y z) := by ring
      _ = _ := by rw [hpre]
  have hlim := (RankTwoLimit.dual_sum_tendsto_one_small_t x y).const_mul
    (((2 / Real.sqrt 3 : ℝ) : ℂ))
  have heq : (fun t : ℝ => (t : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t x y z)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ((2 / Real.sqrt 3 : ℝ) : ℂ) *
        (∑' z : ℤ × ℤ, RankTwoLimit.dualTerm (4 / (3 * t)) x y z)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hpoint t ht
  simpa using hlim.congr' heq.symm

theorem scaled_shifted_gaussian_mass (q : ℝ) (hq : 0 < q)
    (x y : ℝ) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted (η*q) x y z))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 * q) : ℝ) : ℂ))) := by
  have hscale : Tendsto (fun η : ℝ => η*q)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hid : Tendsto (fun η : ℝ => η)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      simpa using hid.mul_const q
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact mul_pos hη hq
  have hlim := (shifted_gaussian_mass x y).comp hscale
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hlim' := hlim.const_mul (1 / (q : ℂ))
  convert hlim' using 1
  · funext η
    dsimp
    push_cast
    field_simp [hqC]
  · push_cast
    field_simp [hqC]

end EisensteinAbelFiber

namespace ActualEisensteinCubic

section

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_fiber_gaussian_mass (a b x y : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : ℤ × ℤ,
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding
            (ActualEisensteinCoordinates.eval x y +
              ActualEisensteinCoordinates.eval a b *
                ActualEisensteinCoordinates.eval z.1 z.2)‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 *
        (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ))) := by
  have hq : 0 < (((a*a-a*b+b*b : ℤ) : ℝ)) := by
    exact_mod_cast coordinate_norm_pos_of_nonzero a b hc
  let u := EisensteinFiberShift.shiftX (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
  let v := EisensteinFiberShift.shiftY (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ)
  have h := EisensteinAbelFiber.scaled_shifted_gaussian_mass
    (((a*a-a*b+b*b : ℤ) : ℝ)) hq u v
  convert h using 1
  funext η
  congr 1
  apply tsum_congr
  intro z
  exact actual_fiber_gaussian_eq_shifted a b x y z.1 z.2 hc η

end

section

open EisensteinEmbedding ConcreteTraceCRT Complex

def latticeCoordEquiv : O ≃ ℤ × ℤ where
  toFun := ActualEisensteinCoordinates.coords
  invFun z := ActualEisensteinCoordinates.eval z.1 z.2
  left_inv := ActualEisensteinCoordinates.eval_coords
  right_inv z := ShortDraftLatticeCount.coords_eval z.1 z.2

theorem eis_gaussian_summable {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))) := by
  have hbase := RankTwoPoisson.eis_gauss_summable hη
  have hcomp : Summable (fun z : O =>
      RankTwoPoisson.eisGauss η (latticeCoordEquiv z)) :=
    (latticeCoordEquiv.summable_iff).2 hbase
  convert hcomp using 1
  funext z
  let p := ActualEisensteinCoordinates.coords z
  have hz : z = ActualEisensteinCoordinates.eval p.1 p.2 :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz]
  have hnormC : ((‖eisEmbedding
      (ActualEisensteinCoordinates.eval p.1 p.2)‖ : ℂ)^2) =
      ((p.1*p.1-p.1*p.2+p.2*p.2 : ℤ) : ℂ) := by
    exact_mod_cast eisEmbedding_eval_norm_sq p.1 p.2
  rw [hnormC]
  change _ = RankTwoPoisson.eisGauss η
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval p.1 p.2))
  rw [ShortDraftLatticeCount.coords_eval]
  dsimp [RankTwoPoisson.eisGauss, RankTwoPoisson.eisQ]
  congr 1
  push_cast
  ring

theorem actual_oscillatory_kernel_summable (c : O) (hc : c ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    Summable (fun z : O =>
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  have hbase := (eis_gaussian_summable hη).norm
  apply hbase.of_norm_bounded
  intro z
  simp only [norm_mul]
  rw [AddChar.norm_apply]
  simp

end

theorem finite_actual_prime_extraction_dyadic_ball_with_loss
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε M : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hM : 1 ≤ M)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : (D : ℝ) ^ (11 / 10 : ℝ) ≤ (H : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
      M * (selected.card : ℝ))
    (hmean :
      (∑ u ∈ ShortDraftLatticeCount.rowNormBall H,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        M * (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      2 * (M + 192) * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let rows := ShortDraftLatticeCount.rowNormBall H
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have hrows : selected.image (fun i => p i ^ 6) ⊆ rows :=
    sixth_power_rows_in_rowNormBall selected p D H hD hnormupper hH
  have hinjRows : Set.InjOn (fun i => p i ^ 6) (selected : Set β) := by
    apply sixth_power_rows_injective selected
      (fun i => (Ideal.span {p i} : Ideal O)) p
    · exact hprime
    · intro i hi; rfl
    · exact hinj
  have happrox : ∀ i ∈ selected,
      ‖A 1 - A (p i ^ 6)‖ ≤
        192 * (D : ℝ) ^ (49 / 60 : ℝ) := by
    intro i hi
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p i ^ 6))‖ ≤ _
    exact (prime_sixth_row_approx_ideal_norm P hgood columns support
      weight (p i) (hp i hi) (hprime i hi) D hsupport hcolnorm hweight).trans
      (PowerExtraction.dyadic_prime_error_bound D
        (Ideal.absNorm (Ideal.span {p i})) hD (hnormlower i hi))
  have hmean' : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      M * (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
  have hextract := ShortDraft.complex_row_extraction rows selected
    (fun i => p i ^ 6) A 1
    (192 * (D : ℝ) ^ (49 / 60 : ℝ))
    (M * (D : ℝ) ^ ((21 / 10 : ℝ) + ε))
    (by positivity) hrows hinjRows happrox hmean'
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hpow : ((D : ℝ) ^ (49 / 60 : ℝ)) ^ 2 =
      (D : ℝ) ^ (49 / 30 : ℝ) := by
    calc
      ((D : ℝ) ^ (49 / 60 : ℝ)) ^ 2 =
          (D : ℝ) ^ ((49 / 60 : ℝ) * 2) :=
            (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = (D : ℝ) ^ (49 / 30 : ℝ) := by congr 1; norm_num
  have herror : (192 * (D : ℝ) ^ (49 / 60 : ℝ)) ^ 2 =
      192 ^ 2 * (D : ℝ) ^ (49 / 30 : ℝ) := by
    rw [mul_pow, hpow]
  rw [herror] at hextract
  have hbound := PowerExtraction.from_mean_square_and_prime_rows_with_loss
    (D : ℝ) ε (selected.card : ℝ) ‖A 1‖ 192 M hDreal hε
    (norm_nonneg _) (by norm_num) hM hcount
    (by simpa only [mul_assoc] using hextract)
  simpa only [hone] using hbound

end ActualEisensteinCubic
namespace GaussianPhasePointwise

theorem exp_imag_diff_le (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) -
      Complex.exp (Complex.I * (v : ℂ))‖ ≤ |u - v| := by
  have heq :
      Complex.exp (Complex.I * (u : ℂ)) -
        Complex.exp (Complex.I * (v : ℂ)) =
      (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) *
        Complex.exp (Complex.I * (v : ℂ)) := by
    rw [sub_mul, one_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v))

theorem exp_imag_denominator_error (θ A η : ℝ) (hA : 0 ≤ A) :
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
      |θ| * (A * η ^ 2) := by
  let r : ℝ := 1 + A * η ^ 2
  have hAη : 0 ≤ A * η ^ 2 := mul_nonneg hA (sq_nonneg _)
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hdiff : |θ / r - θ| = |θ| * ((r - 1) / r) := by
    have heq : θ / r - θ = -θ * ((r - 1) / r) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_neg, abs_of_nonneg (div_nonneg (by linarith) hrpos.le)]
  have hfrac : (r - 1) / r ≤ r - 1 := by
    apply (div_le_iff₀ hrpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hr)]
  have hbound := exp_imag_diff_le (θ / r) θ
  dsimp [r] at hbound ⊢
  calc
    ‖Complex.exp (Complex.I * ((θ / (1 + A * η ^ 2) : ℝ) : ℂ)) -
      Complex.exp (Complex.I * (θ : ℂ))‖ ≤
        |θ / (1 + A * η ^ 2) - θ| := hbound
    _ = |θ| * (((1 + A * η ^ 2) - 1) / (1 + A * η ^ 2)) := hdiff
    _ ≤ |θ| * (A * η ^ 2) := by
      have hfrac' := hfrac
      dsimp [r] at hfrac'
      nlinarith [mul_nonneg (abs_nonneg θ) (sub_nonneg.mpr hfrac')]

end GaussianPhasePointwise

namespace ActualEisensteinCubic

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_O_fiber_gaussian_mass (c r : O) (hc : c ≠ 0) :
    let a := (ActualEisensteinCoordinates.coords c).1
    let b := (ActualEisensteinCoordinates.coords c).2
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' w : O, Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding (r+c*w)‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 / (Real.sqrt 3 *
        (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ))) := by
  dsimp only
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let x := (ActualEisensteinCoordinates.coords r).1
  let y := (ActualEisensteinCoordinates.coords r).2
  have hceq : c = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords c).symm
  have hreq : r = ActualEisensteinCoordinates.eval x y :=
    (ActualEisensteinCoordinates.eval_coords r).symm
  have hcE : ActualEisensteinCoordinates.eval a b ≠ 0 := by
    rw [← hceq]
    exact hc
  have hmass := actual_fiber_gaussian_mass a b x y hcE
  convert hmass using 1
  funext η
  congr 1
  let W : O → ℂ := fun w => Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
    (‖eisEmbedding (r+c*w)‖ ^ 2 : ℂ))
  have hsum := (latticeCoordEquiv.symm.tsum_eq W).symm
  have happly (z : ℤ × ℤ) : latticeCoordEquiv.symm z =
      ActualEisensteinCoordinates.eval z.1 z.2 := rfl
  simpa only [W, hceq, hreq, happly] using hsum

theorem original_abel_gauss_limit (c : O) (hc : c ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let a := (ActualEisensteinCoordinates.coords c).1
    let b := (ActualEisensteinCoordinates.coords c).2
    let K : ℂ := ((2 / (Real.sqrt 3 *
      (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {c},
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc) (r ^ 2))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let K : ℂ := ((2 / (Real.sqrt 3 *
    (((a*a-a*b+b*b : ℤ) : ℝ))) : ℝ) : ℂ)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let W (η : ℝ) (z : O) := Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
    (‖eisEmbedding z‖ ^ 2 : ℂ))
  have hfiber (r : O ⧸ Ideal.span {c}) :
      Tendsto (fun η : ℝ => (η : ℂ) *
        (∑' w : O, W η (GaussianShiftedPartition.representative c r + c*w)))
        (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    simpa only [K, a, b, W] using
      actual_O_fiber_gaussian_mass c
        (GaussianShiftedPartition.representative c r) hc
  have hsum : Tendsto (fun η : ℝ =>
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) * K)) := by
    apply tendsto_finsetSum Finset.univ
    intro r hr
    exact (hfiber r).const_mul (ψ (r ^ 2))
  have hpoint (η : ℝ) (hη : 0 < η) :
      (η : ℂ) * (∑' z : O, ψ
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z) =
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w))) := by
    have hpart := GaussianShiftedPartition.actual_quadratic_shifted_partition
      c hc (W η) (actual_oscillatory_kernel_summable c hc hη)
    change (∑' z : O, ψ (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z) =
      ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ∑' w : O, W η (GaussianShiftedPartition.representative c r + c*w) at hpart
    rw [hpart, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have heq : (fun η : ℝ => (η : ℂ) *
      (∑' z : O, ψ (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) * W η z)) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative c r + c*w)))) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hpoint η hη
  have hlim := hsum.congr' heq.symm
  simpa only [K, ψ, W, Finset.mul_sum, mul_comm] using hlim

end ActualEisensteinCubic

end

end OAI
end OAIOriginalModule0064

/-! Original module: OAI.NumberTheory.DirichletL.Poisson.GaussianMoments
Source SHA256: 748ddcf5d8126be339ac5d05dd8d67a7dc0c232f055c9cbfc84b98889fafcbd9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0065


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics

namespace GaussianMoment

theorem x_exp_neg_le (x : ℝ) (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have hlin : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-x)).le
  calc
    x * Real.exp (-x) = 2 * ((x / 2) * Real.exp (-x)) := by ring
    _ ≤ 2 * (Real.exp (x / 2) * Real.exp (-x)) := by
      gcongr
    _ = 2 * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

theorem gaussian_moment_term_bound (q t : ℝ) (hq : 0 ≤ q) (ht : 0 < t) :
    q * Real.exp (-t * q) ≤
      (2 / t) * Real.exp (-(t * q / 2)) := by
  have h := x_exp_neg_le (t * q) (mul_nonneg ht.le hq)
  have hpos : 0 ≤ t := ht.le
  calc
    q * Real.exp (-t * q) =
        ((t * q) * Real.exp (-(t * q))) / t := by
          field_simp
    _ ≤ (2 * Real.exp (-(t * q / 2))) / t :=
      div_le_div_of_nonneg_right h hpos
    _ = (2 / t) * Real.exp (-(t * q / 2)) := by ring

end GaussianMoment
namespace ActualEisensteinCubic

section

open ShortDraftLatticeCount

theorem rational_sixth_row_approx_two_factors
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (r a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (D : ℕ)
    (hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, r ∈ P i) → a ∣ n ∨ b ∣ n)
    (hcolnorm : ∀ n ∈ columns, qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (r ^ 6))‖ ≤
      (64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) : ℕ) := by
  classical
  let Bad := columns.filter (fun n => ∃ i ∈ support n, r ∈ P i)
  let Sa := columns.filter (fun n => a ∣ n)
  let Sb := columns.filter (fun n => b ∣ n)
  have hsub : Bad ⊆ Sa ∪ Sb := by
    intro n hn
    obtain ⟨hcol, hbad⟩ := Finset.mem_filter.mp hn
    rcases hfactor n hcol hbad with hna | hnb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcol, hna⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcol, hnb⟩)
  have hSa : Sa.card ≤ 64 * (D / qNat a + 1) :=
    finite_divisible_count a ha Sa D
      (by intro n hn; exact (Finset.mem_filter.mp hn).2)
      (by intro n hn; exact hcolnorm n (Finset.mem_filter.mp hn).1)
  have hSb : Sb.card ≤ 64 * (D / qNat b + 1) :=
    finite_divisible_count b hb Sb D
      (by intro n hn; exact (Finset.mem_filter.mp hn).2)
      (by intro n hn; exact hcolnorm n (Finset.mem_filter.mp hn).1)
  have hcard : Bad.card ≤
      64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) := by
    calc
      Bad.card ≤ (Sa ∪ Sb).card := Finset.card_le_card hsub
      _ ≤ Sa.card + Sb.card := Finset.card_union_le Sa Sb
      _ ≤ 64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) :=
        Nat.add_le_add hSa hSb
  calc
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (r ^ 6))‖ ≤
        ∑ n ∈ Bad, ‖weight n‖ :=
      finiteSquarefreeRow_difference_norm P hgood columns support weight r
    _ ≤ ∑ n ∈ Bad, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hweight n (Finset.mem_filter.mp hn).1
    _ = (Bad.card : ℝ) := by simp
    _ ≤ (64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) : ℕ) := by
      exact_mod_cast hcard

theorem rational_qNat (r : ℕ) (hr : r ≠ 0) :
    qNat (r : O) = r ^ 2 := by
  calc
    qNat (r : O) = Ideal.absNorm (Ideal.span {(r : O)}) :=
      qNat_eq_absNorm_span _
    _ = Nat.card (O ⧸ Ideal.span {(r : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = r ^ 2 := rational_modulus_card r hr

theorem rational_qNat_pow (r k : ℕ) (hr : r ≠ 0) :
    qNat ((r : O) ^ k) = (r ^ 2) ^ k := by
  induction k with
  | zero =>
      simpa using rational_qNat 1 (by decide)
  | succ k ih =>
      calc
        qNat ((r : O) ^ (k + 1)) =
            qNat ((r : O) ^ k) * qNat (r : O) := by
          rw [pow_succ, qNat_mul]
        _ = (r ^ 2) ^ k * (r ^ 2) := by rw [ih, rational_qNat r hr]
        _ = (r ^ 2) ^ (k + 1) := (pow_succ (r ^ 2) k).symm

theorem rational_sixth_injective :
    Function.Injective (fun r : ℕ => (r : O) ^ 6) := by
  intro r s hrs
  have hcast : ((r ^ 6 : ℕ) : O) = ((s ^ 6 : ℕ) : O) := by
    simpa only [Nat.cast_pow] using hrs
  exact Nat.pow_left_injective (by decide : 6 ≠ 0) (Nat.cast_injective hcast)

theorem rational_sixth_norm_interval
    (L r R : ℕ) (hr : r.Prime) (hL : L ≤ r) (hR : r ≤ R) :
    L ^ 12 ≤ qNat ((r : O) ^ 6) ∧
      qNat ((r : O) ^ 6) ≤ R ^ 12 := by
  rw [rational_qNat_pow r 6 hr.ne_zero]
  have hpow : (r ^ 2) ^ 6 = r ^ 12 := by ring
  rw [hpow]
  exact ⟨Nat.pow_le_pow_left hL 12, Nat.pow_le_pow_left hR 12⟩

theorem rational_qNat_eq_one_iff (x : O) : qNat x = 1 ↔ IsUnit x := by
  rw [qNat_eq_absNorm_span, Ideal.absNorm_eq_one_iff,
    Ideal.span_singleton_eq_top]

theorem rational_prime_factor_cases (r : ℕ) (hr : r.Prime) :
    (Ideal.span {(r : O)} : Ideal O).IsMaximal ∨
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧ (r : O) = a * b ∧
      qNat a = r ∧ qNat b = r ∧
      (Ideal.span {a} : Ideal O).IsMaximal ∧
      (Ideal.span {b} : Ideal O).IsMaximal := by
  have hru : ¬ IsUnit (r : O) := by
    rw [← rational_qNat_eq_one_iff, rational_qNat r hr.ne_zero]
    have htwo := hr.two_le
    nlinarith
  rcases irreducible_or_factor hru with hirr | ⟨a, b, hna, hnb, hab⟩
  · left
    exact PrincipalIdealRing.isMaximal_of_irreducible hirr
  · right
    have hqa1 : qNat a ≠ 1 := by
      intro h
      exact hna ((rational_qNat_eq_one_iff a).mp h)
    have hqb1 : qNat b ≠ 1 := by
      intro h
      exact hnb ((rational_qNat_eq_one_iff b).mp h)
    have hqprod : qNat a * qNat b = r ^ 2 := by
      rw [← qNat_mul, ← hab, rational_qNat r hr.ne_zero]
    obtain ⟨hqa, hqb⟩ := (hr.mul_eq_prime_sq_iff hqa1 hqb1).mp hqprod
    have ha0 : a ≠ 0 := by
      intro h
      have hqa0 : qNat a = 0 := by simp [h, qNat_eq_absNorm_span]
      rw [hqa] at hqa0
      exact hr.ne_zero hqa0
    have hb0 : b ≠ 0 := by
      intro h
      have hqb0 : qNat b = 0 := by simp [h, qNat_eq_absNorm_span]
      rw [hqb] at hqb0
      exact hr.ne_zero hqb0
    have hpa : Prime a := by
      apply Ideal.prime_of_irreducible_absNorm_span ha0
      rw [← qNat_eq_absNorm_span, hqa]
      exact hr.prime.irreducible
    have hpb : Prime b := by
      apply Ideal.prime_of_irreducible_absNorm_span hb0
      rw [← qNat_eq_absNorm_span, hqb]
      exact hr.prime.irreducible
    exact ⟨a, b, ha0, hb0, hab, hqa, hqb,
      PrincipalIdealRing.isMaximal_of_irreducible hpa.irreducible,
      PrincipalIdealRing.isMaximal_of_irreducible hpb.irreducible⟩

theorem maximal_ideal_eq_span_of_mem
    (Q : Ideal O) (hQ : Q.IsMaximal) (a : O)
    (ha : (Ideal.span {a} : Ideal O).IsMaximal) (hamem : a ∈ Q) :
    Q = Ideal.span {a} := by
  have hle : (Ideal.span {a} : Ideal O) ≤ Q :=
    (Ideal.span_singleton_le_iff_mem _).mpr hamem
  exact (ha.eq_of_le hQ.ne_top hle).symm

theorem rational_prime_ideal_cover (r : ℕ) (hr : r.Prime) :
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧
      r ≤ qNat a ∧ r ≤ qNat b ∧
      ∀ (Q : Ideal O), Q.IsMaximal → (r : O) ∈ Q →
        Q = Ideal.span {a} ∨ Q = Ideal.span {b} := by
  rcases rational_prime_factor_cases r hr with hmax |
      ⟨a, b, ha0, hb0, hab, hqa, hqb, hma, hmb⟩
  · have hr0 : (r : O) ≠ 0 := by exact_mod_cast hr.ne_zero
    have hq : qNat (r : O) = r ^ 2 := rational_qNat r hr.ne_zero
    have hrle : r ≤ r ^ 2 := by nlinarith [hr.two_le]
    refine ⟨(r : O), (r : O), hr0, hr0, ?_, ?_, ?_⟩
    · rw [hq]; exact hrle
    · rw [hq]; exact hrle
    · intro Q hQ hrQ
      exact Or.inl (maximal_ideal_eq_span_of_mem Q hQ (r : O) hmax hrQ)
  · refine ⟨a, b, ha0, hb0, ?_, ?_, ?_⟩
    · rw [hqa]
    · rw [hqb]
    · intro Q hQ hrQ
      rw [hab] at hrQ
      rcases hQ.isPrime.mem_or_mem hrQ with haQ | hbQ
      · exact Or.inl (maximal_ideal_eq_span_of_mem Q hQ a hma haQ)
      · exact Or.inr (maximal_ideal_eq_span_of_mem Q hQ b hmb hbQ)

end

theorem rational_prime_sixth_row_approx
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (r : ℕ) (hr : r.Prime) (D : ℕ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, ShortDraftLatticeCount.qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) ((r : O) ^ 6))‖ ≤
      (128 * (D / r + 1) : ℕ) := by
  obtain ⟨a, b, ha0, hb0, hra, hrb, hcover⟩ :=
    rational_prime_ideal_cover r hr
  have hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, (r : O) ∈ P i) → a ∣ n ∨ b ∣ n := by
    intro n hn ⟨i, hi, hri⟩
    rcases hcover (P i) (inferInstance) hri with hPa | hPb
    · have hmem : n ∈ (Ideal.span {a} : Ideal O) := by
        rw [← hPa]
        exact hsupport n hn i hi
      exact Or.inl (Ideal.mem_span_singleton.mp hmem)
    · have hmem : n ∈ (Ideal.span {b} : Ideal O) := by
        rw [← hPb]
        exact hsupport n hn i hi
      exact Or.inr (Ideal.mem_span_singleton.mp hmem)
  have hrow := rational_sixth_row_approx_two_factors
    P hgood columns support weight (r : O) a b ha0 hb0 D
    hfactor hcolnorm hweight
  have hAdiv : D / ShortDraftLatticeCount.qNat a ≤ D / r :=
    Nat.div_le_div_left hra hr.pos
  have hBdiv : D / ShortDraftLatticeCount.qNat b ≤ D / r :=
    Nat.div_le_div_left hrb hr.pos
  have hnat :
      64 * (D / ShortDraftLatticeCount.qNat a + 1) +
      64 * (D / ShortDraftLatticeCount.qNat b + 1) ≤
      128 * (D / r + 1) := by omega
  exact hrow.trans (by exact_mod_cast hnat)

end ActualEisensteinCubic

open ActualEisensteinCubic

namespace RationalPrimeExtraction

noncomputable def selected (Y : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime

theorem lower_count_and_extract
    [DecidableEq O] (A : O → ℂ) (rows : Finset O) (E B : ℝ) (hE : 0 ≤ E) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (selected Y).image (fun r : ℕ => (r : O) ^ 6) ⊆ rows →
      (∀ r ∈ selected Y, ‖A 1 - A ((r : O) ^ 6)‖ ≤ E) →
      (∑ u ∈ rows, ‖A u‖ ^ 2) ≤ B →
      (Real.log 2 / 20) * (Y / Real.log Y) * ‖A 1‖ ^ 2 ≤
        2 * B + 2 * ((selected Y).card : ℝ) * E ^ 2 := by
  obtain ⟨Y₀, hcount⟩ := rational_prime_three_interval_count
  refine ⟨Y₀, ?_⟩
  intro Y hY hrows happrox hmean
  have hcard : (Real.log 2 / 20) * (Y / Real.log Y) ≤
      ((selected Y).card : ℝ) := hcount Y hY
  have hinj : Set.InjOn (fun r : ℕ => (r : O) ^ 6)
      ((selected Y : Finset ℕ) : Set ℕ) := by
    intro r _ s _ hrs
    exact rational_sixth_injective hrs
  have hmain := ShortDraft.complex_row_extraction rows (selected Y)
    (fun r : ℕ => (r : O) ^ 6) A 1 E B hE hrows hinj happrox hmean
  have hsquared : 0 ≤ ‖A 1‖ ^ 2 := sq_nonneg _
  exact (mul_le_mul_of_nonneg_right hcard hsquared).trans hmain

end RationalPrimeExtraction

namespace OscSpecial

private theorem real_quadratic_lower {u v w : ℝ}
    (hu : 0 < u) (hv : 0 < v) (_hdet : 0 < u * v - w ^ 2)
    (x y : ℝ) :
    ((u * v - w ^ 2) / (u + v)) * (x ^ 2 + y ^ 2) ≤
      u * x ^ 2 - 2 * w * x * y + v * y ^ 2 := by
  have hsum : 0 < u + v := add_pos hu hv
  have hid :
      (u + v) * (u * x ^ 2 - 2 * w * x * y + v * y ^ 2) -
        (u * v - w ^ 2) * (x ^ 2 + y ^ 2) =
      (u * x - w * y) ^ 2 + (w * x - v * y) ^ 2 := by ring
  have hsq := add_nonneg (sq_nonneg (u * x - w * y))
    (sq_nonneg (w * x - v * y))
  have hnum : (u * v - w ^ 2) * (x ^ 2 + y ^ 2) ≤
      (u + v) * (u * x ^ 2 - 2 * w * x * y + v * y ^ 2) := by
    linarith
  have h : ((u * v - w ^ 2) * (x ^ 2 + y ^ 2)) / (u + v) ≤
      u * x ^ 2 - 2 * w * x * y + v * y ^ 2 :=
    (div_le_iff₀ hsum).2 (by simpa only [mul_comm] using hnum)
  simpa only [div_mul_eq_mul_div] using h

private theorem schur_eq_real_det_div {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ)) :
    RankTwoComplex.schur a b d = (R : ℂ) / a := by
  unfold RankTwoComplex.schur
  rw [← hdet]
  field_simp [ha]

private theorem determinant_real_components {a b d : ℂ} {R : ℝ}
    (hdet : a * d - b ^ 2 = (R : ℂ)) :
    a.re * d.re - a.im * d.im - b.re ^ 2 + b.im ^ 2 = R ∧
    a.re * d.im + a.im * d.re - 2 * b.re * b.im = 0 := by
  constructor
  · have h := congrArg Complex.re hdet
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re] at h
    have hb : (b ^ 2).re = b.re ^ 2 - b.im ^ 2 := by
      rw [pow_two, Complex.mul_re]
      ring
    rw [hb] at h
    linarith
  · have h := congrArg Complex.im hdet
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im] at h
    have hb : (b ^ 2).im = 2 * b.re * b.im := by
      rw [pow_two, Complex.mul_im]
      ring
    rw [hb] at h
    linarith

private theorem first_real_coefficients {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ)) :
    (a⁻¹).re = a.re / Complex.normSq a ∧
    (RankTwoComplex.schur a b d).re = R * a.re / Complex.normSq a ∧
    (Complex.I * b / a).re =
      (b.re * a.im - b.im * a.re) / Complex.normSq a := by
  constructor
  · exact Complex.inv_re a
  constructor
  · rw [schur_eq_real_det_div ha hdet]
    simp [Complex.div_re]
  · rw [Complex.div_re]
    simp [Complex.mul_re, Complex.mul_im]
    ring

private theorem first_real_determinant {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ)) :
    (a.re / Complex.normSq a) * (R * a.re / Complex.normSq a) -
      ((b.re * a.im - b.im * a.re) / Complex.normSq a) ^ 2 =
      (a.re * d.re - b.re ^ 2) / Complex.normSq a := by
  have hN : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  obtain ⟨hr, hi⟩ := determinant_real_components hdet
  have hid :
      R * a.re ^ 2 - (b.re * a.im - b.im * a.re) ^ 2 =
      (a.re ^ 2 + a.im ^ 2) * (a.re * d.re - b.re ^ 2) -
        a.im * a.re * (a.re * d.im + a.im * d.re - 2 * b.re * b.im) := by
    rw [← hr]
    ring
  rw [hi, mul_zero, sub_zero] at hid
  simp only [Complex.normSq_apply] at hN ⊢
  have hN' : a.re ^ 2 + a.im ^ 2 ≠ 0 := by simpa [pow_two] using hN
  field_simp [hN']
  nlinarith [hid]

private noncomputable def middleForm (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  a⁻¹ * (z.1 : ℂ) ^ 2 -
    2 * (Complex.I * b / a) * (z.1 : ℂ) * (z.2 : ℂ) +
    RankTwoComplex.schur a b d * (z.2 : ℂ) ^ 2

private theorem middleForm_real (a b d : ℂ) (z : ℤ × ℤ) :
    (middleForm a b d z).re =
      (a⁻¹).re * (z.1 : ℝ) ^ 2 -
      2 * (Complex.I * b / a).re * (z.1 : ℝ) * (z.2 : ℝ) +
      (RankTwoComplex.schur a b d).re * (z.2 : ℝ) ^ 2 := by
  simp [middleForm, Complex.add_re, Complex.sub_re, Complex.mul_re, pow_two]

private theorem middleForm_exp (a b d : ℂ) (z : ℤ × ℤ) :
    RankTwoComplex.firstGaussian a b d z =
      Complex.exp (-(Real.pi : ℂ) * middleForm a b d z) := by
  simp only [RankTwoComplex.firstGaussian, middleForm]
  rw [← Complex.exp_add]
  congr 1
  simp [div_eq_mul_inv]
  ring

private theorem firstGaussian_summable {a b d : ℂ} {R : ℝ}
    (ha : 0 < a.re) (hR : 0 < R)
    (hdet : a * d - b ^ 2 = (R : ℂ))
    (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.firstGaussian a b d) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  let u : ℝ := a.re / Complex.normSq a
  let v : ℝ := R * a.re / Complex.normSq a
  let w : ℝ := (b.re * a.im - b.im * a.re) / Complex.normSq a
  have hu : 0 < u := div_pos ha hN
  have hv : 0 < v := div_pos (mul_pos hR ha) hN
  have hq : 0 < u * v - w ^ 2 := by
    dsimp [u, v, w]
    rw [first_real_determinant ha0 hdet]
    exact div_pos hpd hN
  let eps : ℝ := (u * v - w ^ 2) / (u + v)
  have heps : 0 < eps := div_pos hq (add_pos hu hv)
  have hcoeff := first_real_coefficients ha0 hdet
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (middleForm a b d z).re := by
    rw [middleForm_real, hcoeff.1, hcoeff.2.1, hcoeff.2.2]
    exact real_quadratic_lower hu hv hq (z.1 : ℝ) (z.2 : ℝ)
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (middleForm a b d) heps hbound).congr (fun z => (middleForm_exp a b d z).symm)

private noncomputable def originalForm (a b d : ℂ) (z : ℤ × ℤ) : ℂ :=
  a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2

private theorem originalForm_real (a b d : ℂ) (z : ℤ × ℤ) :
    (originalForm a b d z).re =
      a.re * (z.1 : ℝ) ^ 2 + 2 * b.re * (z.1 : ℝ) * (z.2 : ℝ) +
      d.re * (z.2 : ℝ) ^ 2 := by
  simp [originalForm, Complex.add_re, Complex.mul_re, pow_two]

private theorem originalGaussian_summable {a b d : ℂ}
    (ha : 0 < a.re) (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.binaryGaussian a b d) := by
  have hd : 0 < d.re := by
    by_contra h
    have h' : d.re ≤ 0 := le_of_not_gt h
    have hm := mul_nonpos_of_nonneg_of_nonpos ha.le h'
    nlinarith [sq_nonneg b.re]
  let eps : ℝ := (a.re * d.re - b.re ^ 2) / (a.re + d.re)
  have heps : 0 < eps := div_pos hpd (add_pos ha hd)
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (originalForm a b d z).re := by
    rw [originalForm_real]
    dsimp [eps]
    convert real_quadratic_lower (w := -b.re) ha hd (by simpa using hpd)
      (z.1 : ℝ) (z.2 : ℝ) using 1 <;> ring
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (originalForm a b d) heps hbound).congr (fun z => by rfl)

noncomputable def inverseForm (a b d : ℂ) (R : ℝ) (z : ℤ × ℤ) : ℂ :=
  (d * (z.1 : ℂ) ^ 2 - 2 * b * (z.1 : ℂ) * (z.2 : ℂ) +
    a * (z.2 : ℂ) ^ 2) / (R : ℂ)

private theorem inverseForm_real (a b d : ℂ) {R : ℝ} (hR : R ≠ 0) (z : ℤ × ℤ) :
    (inverseForm a b d R z).re =
      (d.re * (z.1 : ℝ) ^ 2 - 2 * b.re * (z.1 : ℝ) * (z.2 : ℝ) +
        a.re * (z.2 : ℝ) ^ 2) / R := by
  simp [inverseForm, Complex.div_re, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.normSq_apply, pow_two]
  field_simp [hR]

theorem dualGaussian_inverseForm {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hR : R ≠ 0)
    (hdet : a * d - b ^ 2 = (R : ℂ)) (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian a b d z =
      Complex.exp (-(Real.pi : ℂ) * inverseForm a b d R z) := by
  unfold RankTwoComplex.dualGaussian
  rw [← Complex.exp_add]
  congr 1
  rw [schur_eq_real_det_div ha hdet]
  dsimp [inverseForm]
  have hdet0 : a * d - b ^ 2 ≠ 0 := by rw [hdet]; exact_mod_cast hR
  rw [← hdet]
  field_simp [ha, hdet0] ; ring

private theorem dualGaussian_summable {a b d : ℂ} {R : ℝ}
    (ha : 0 < a.re) (hR : 0 < R)
    (hdet : a * d - b ^ 2 = (R : ℂ))
    (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.dualGaussian a b d) := by
  have hd : 0 < d.re := by
    by_contra h
    have h' : d.re ≤ 0 := le_of_not_gt h
    have hm := mul_nonpos_of_nonneg_of_nonpos ha.le h'
    nlinarith [sq_nonneg b.re]
  let eps : ℝ := ((d.re * a.re - b.re ^ 2) / (d.re + a.re)) / R
  have heps : 0 < eps := div_pos (div_pos (by nlinarith [hpd]) (add_pos hd ha)) hR
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (inverseForm a b d R z).re := by
    rw [inverseForm_real a b d hR.ne']
    have hbase := real_quadratic_lower (u := d.re) (v := a.re) (w := b.re)
      hd ha (by nlinarith [hpd]) (z.1 : ℝ) (z.2 : ℝ)
    have hdivide := div_le_div_of_nonneg_right hbase hR.le
    simpa [eps, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdivide
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (inverseForm a b d R) heps hbound).congr
      (fun z => (dualGaussian_inverseForm ha0 hR.ne' hdet z).symm)

theorem binary_gaussian_poisson_real_det {a b d : ℂ} {R : ℝ}
    (ha : 0 < a.re) (hR : 0 < R)
    (hdet : a * d - b ^ 2 = (R : ℂ))
    (hpd : 0 < a.re * d.re - b.re ^ 2) :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian a b d z) =
      (1 / ((R : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  have hδ : 0 < (RankTwoComplex.schur a b d).re := by
    rw [schur_eq_real_det_div ha0 hdet]
    simpa [Complex.div_re] using div_pos (mul_pos hR ha) hN
  have hO := originalGaussian_summable ha hpd
  have hM := firstGaussian_summable ha hR hdet hpd
  have hD := dualGaussian_summable ha hR hdet hpd
  calc
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian a b d z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (RankTwoComplex.schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z :=
      RankTwoComplex.binary_gaussian_poisson ha hδ hO hM hD
    _ = (1 / ((R : ℂ) ^ (1 / 2 : ℂ))) *
          ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z := by
      rw [schur_eq_real_det_div ha0 hdet,
        SqrtBranch.prefactor_product ha hR]

noncomputable def q (a b : ℝ) : ℝ := a ^ 2 - a * b + b ^ 2
noncomputable def A (η a b : ℝ) : ℂ :=
  (η : ℂ) + 2 * Complex.I * (b : ℂ) / (q a b : ℂ)
noncomputable def B (η a b : ℝ) : ℂ :=
  -(η : ℂ) / 2 - 2 * Complex.I * (a : ℂ) / (q a b : ℂ)
noncomputable def D (η a b : ℝ) : ℂ :=
  (η : ℂ) + 2 * Complex.I * ((a-b : ℝ) : ℂ) / (q a b : ℂ)
noncomputable def R (η a b : ℝ) : ℝ := 4 / q a b + 3 * η ^ 2 / 4

theorem coefficient_re (η a b : ℝ) (_hq : q a b ≠ 0) :
    (A η a b).re = η ∧ (B η a b).re = -η / 2 ∧ (D η a b).re = η := by
  simp [A, B, D, Complex.div_re, Complex.normSq_apply]

theorem oscillatory_determinant (η a b : ℝ) (hq : q a b ≠ 0) :
    A η a b * D η a b - (B η a b) ^ 2 = (R η a b : ℂ) := by
  have hqc : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq
  have hqexpr : (q a b : ℂ) = (a : ℂ) ^ 2 - (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2 := by
    simp [q]
  have hRcast : (R η a b : ℂ) = 4 / (q a b : ℂ) + 3 * (η : ℂ) ^ 2 / 4 := by
    simp [R]
  rw [hRcast]
  dsimp [A, B, D]
  field_simp [hqc]
  rw [hqexpr]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem real_positive_definite {η a b : ℝ} (hη : 0 < η) (hq : q a b ≠ 0) :
    0 < (A η a b).re * (D η a b).re - (B η a b).re ^ 2 := by
  obtain ⟨hA, hB, hD⟩ := coefficient_re η a b hq
  rw [hA, hB, hD]
  nlinarith [sq_pos_of_pos hη]

end OscSpecial

end

end OAI
end OAIOriginalModule0065

/-! Original module: OAI.NumberTheory.DirichletL.Poisson.OscillatoryGaussian
Source SHA256: a57d5f82137b5908d287a50eee88f6a6d7810c1eff3f1b5f8960134723cc70dd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0066


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic

namespace OscSpecial

theorem oscillatory_gaussian_poisson {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian (A η a b) (B η a b) (D η a b) z) =
      (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ,
          RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have ha : 0 < (A η a b).re := by
    rw [(coefficient_re η a b hq0).1]
    exact hη
  have hR : 0 < R η a b := by
    unfold R
    positivity
  exact binary_gaussian_poisson_real_det ha hR
    (oscillatory_determinant η a b hq0)
    (real_positive_definite hη hq0)

noncomputable def r (η a b : ℝ) : ℝ := 1 + 3 * q a b * η ^ 2 / 16

theorem r_pos {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    0 < r η a b := by
  unfold r
  positivity

private theorem inverseForm_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    inverseForm (A η a b) (B η a b) (D η a b) (R η a b) z =
      ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
        ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
      Complex.I / (2 * (r η a b : ℂ)) *
        (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
          2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
          (b : ℂ) * (z.2 : ℂ) ^ 2) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hqc : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq0
  have hr0 : r η a b ≠ 0 := (r_pos hη hq).ne'
  have hrc : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hR : 0 < R η a b := by unfold R; positivity
  have hRc : (R η a b : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hRexpr : (R η a b : ℂ) = 4 * (r η a b : ℂ) / (q a b : ℂ) := by
    simp [R, r]
    field_simp [hqc]
    ring
  have hqexpr : (q a b : ℂ) = (a : ℂ) ^ 2 - (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2 := by
    simp [q]
  have hrexpr : (r η a b : ℂ) = 1 + 3 * (q a b : ℂ) * (η : ℂ) ^ 2 / 16 := by
    simp [r]
  dsimp [inverseForm, A, B, D]
  rw [hRexpr]
  field_simp [hqc, hrc]
  push_cast
  ring

theorem dualGaussian_explicit {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      Complex.exp (-(Real.pi : ℂ) *
        (((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ))) *
          ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) +
         Complex.I / (2 * (r η a b : ℂ)) *
          (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
            2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
            (b : ℂ) * (z.2 : ℂ) ^ 2))) := by
  have hq0 : q a b ≠ 0 := hq.ne'
  have hA0 : A η a b ≠ 0 := by
    intro h
    have hAr : (A η a b).re = η := (coefficient_re η a b hq0).1
    simp [h] at hAr
    linarith
  have hR : 0 < R η a b := by unfold R; positivity
  rw [dualGaussian_inverseForm hA0 hR.ne'
    (oscillatory_determinant η a b hq0) z,
    inverseForm_explicit hη hq z]

end OscSpecial

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem dual_quadratic_trace_coeff (a b k l : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)).2 =
      (a-b)*k^2+2*a*k*l+b*l^2 := by
  rw [pow_two, ActualEisensteinCoordinates.eval_mul (k+l) k (k+l) k]
  rw [ActualEisensteinCoordinates.eval_mul]
  rw [ShortDraftLatticeCount.coords_eval]
  ring

private theorem coords_neg_second (z : O) :
    (ActualEisensteinCoordinates.coords (-z)).2 =
      -(ActualEisensteinCoordinates.coords z).2 := by
  let a := (ActualEisensteinCoordinates.coords z).1
  let b := (ActualEisensteinCoordinates.coords z).2
  have hz : z = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz]
  have hneg : -ActualEisensteinCoordinates.eval a b =
      ActualEisensteinCoordinates.eval (-a) (-b) := by
    simp only [ActualEisensteinCoordinates.eval]
    push_cast
    ring
  rw [hneg, ShortDraftLatticeCount.coords_eval,
    ShortDraftLatticeCount.coords_eval]

theorem breveE_dual_quadratic_real_scale
    (r : ℝ) (a b k l : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
        eisLam / ((4*r : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) /
        ((4*r : ℝ) : ℂ)) := by
  rw [breveE_real_trace_of_O]
  have hneg : (ActualEisensteinCoordinates.coords
      (-(ActualEisensteinCoordinates.eval a b *
        (ActualEisensteinCoordinates.eval (k+l) k)^2))).2 =
      -((a-b)*k^2+2*a*k*l+b*l^2) := by
    have hp := dual_quadratic_trace_coeff a b k l
    rw [coords_neg_second]
    simpa using congrArg Neg.neg hp
  rw [hneg]
  congr 1
  push_cast
  ring_nf

end

section

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem original_abel_gamma_limit (c : O) (hc : c ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((2 / (Real.sqrt 3 * ‖eisEmbedding c‖) : ℝ) : ℂ) *
        quadraticGammaO c hc))) := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let a := (ActualEisensteinCoordinates.coords c).1
  let b := (ActualEisensteinCoordinates.coords c).2
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let S : ℂ := ∑ r : O ⧸ Ideal.span {c}, ψ (r ^ 2)
  have hceq : c = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords c).symm
  have hq : (((a*a-a*b+b*b : ℤ) : ℝ)) = ‖eisEmbedding c‖ ^ 2 := by
    calc
      (((a*a-a*b+b*b : ℤ) : ℝ)) =
          ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ ^ 2 :=
        (eisEmbedding_eval_norm_sq a b).symm
      _ = ‖eisEmbedding c‖ ^ 2 := by rw [← hceq]
  have hn : ‖eisEmbedding c‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hc))
  have hnC : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hsqrtC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  have hgamma : quadraticGammaO c hc = S / (‖eisEmbedding c‖ : ℂ) := rfl
  have h := original_abel_gauss_limit c hc
  convert h using 1
  rw [hgamma, hq]
  push_cast
  field_simp [hnC, hsqrtC]
  dsimp only [S]

end

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_oscillatory_binary_coordinate
    (a b m n : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval m n
    (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ)) =
      RankTwoComplex.binaryGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (m,n) := by
  have hqZ : a*a-a*b+b*b ≠ 0 :=
    (coordinate_norm_pos_of_nonzero a b hc).ne'
  have hqC : (((a*a-a*b+b*b : ℤ) : ℂ)) ≠ 0 := by exact_mod_cast hqZ
  dsimp only
  rw [actual_oscillatory_gaussian_coordinate a b m n hc η]
  unfold RankTwoComplex.binaryGaussian OscSpecial.A OscSpecial.B
    OscSpecial.D OscSpecial.q
  congr 1
  push_cast
  field_simp [hqC]
  ring

theorem actual_oscillatory_sum_eq_binary
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      ∑' p : ℤ × ℤ,
        RankTwoComplex.binaryGaussian
          (OscSpecial.A η (a : ℝ) (b : ℝ))
          (OscSpecial.B η (a : ℝ) (b : ℝ))
          (OscSpecial.D η (a : ℝ) (b : ℝ)) p := by
  let W : O → ℂ := fun z =>
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates
        (ActualEisensteinCoordinates.eval a b) hc)
      (Ideal.Quotient.mk (Ideal.span {ActualEisensteinCoordinates.eval a b}) z ^ 2) *
    Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
      (‖eisEmbedding z‖ ^ 2 : ℂ))
  have h := (latticeCoordEquiv.symm.tsum_eq W).symm
  simpa only [W, latticeCoordEquiv] using
    (show (∑' z : O, W z) =
      ∑' p : ℤ × ℤ,
        RankTwoComplex.binaryGaussian
          (OscSpecial.A η (a : ℝ) (b : ℝ))
          (OscSpecial.B η (a : ℝ) (b : ℝ))
          (OscSpecial.D η (a : ℝ) (b : ℝ)) p from by
      calc
        (∑' z : O, W z) = ∑' p : ℤ × ℤ, W (latticeCoordEquiv.symm p) := h
        _ = _ := by
          apply tsum_congr
          intro p
          have hp : latticeCoordEquiv.symm p =
              ActualEisensteinCoordinates.eval p.1 p.2 := rfl
          rw [hp]
          exact actual_oscillatory_binary_coordinate a b p.1 p.2 hc η)

def dualFrequencyEquiv : (ℤ × ℤ) ≃ O where
  toFun p := ActualEisensteinCoordinates.eval (p.1 + p.2) p.1
  invFun y := ((ActualEisensteinCoordinates.coords y).2,
    (ActualEisensteinCoordinates.coords y).1 -
      (ActualEisensteinCoordinates.coords y).2)
  left_inv p := by
    rcases p with ⟨k,l⟩
    simp only [  ShortDraftLatticeCount.coords_eval]
    ext <;> ring
  right_inv y := by
    change ActualEisensteinCoordinates.eval
      ((ActualEisensteinCoordinates.coords y).2 +
        ((ActualEisensteinCoordinates.coords y).1 -
          (ActualEisensteinCoordinates.coords y).2))
      (ActualEisensteinCoordinates.coords y).2 = y
    convert ActualEisensteinCoordinates.eval_coords y using 1 ; ring_nf

theorem dualFrequencyEquiv_norm_sq (k l : ℤ) :
    ‖eisEmbedding (dualFrequencyEquiv (k,l))‖ ^ 2 =
      (((k^2+k*l+l^2 : ℤ) : ℝ)) := by
  change ‖eisEmbedding (ActualEisensteinCoordinates.eval (k+l) k)‖ ^ 2 = _
  rw [eisEmbedding_eval_norm_sq]
  ring_nf

theorem dualFrequencyEquiv_trace_phase (r : ℝ) (a b k l : ℤ) :
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
        (dualFrequencyEquiv (k,l))^2)) /
        eisLam / ((4*r : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) /
        ((4*r : ℝ) : ℂ)) := by
  exact breveE_dual_quadratic_real_scale r a b k l

end ActualEisensteinCubic

namespace GaussianMoment

open scoped Topology
open Filter

noncomputable def realGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * RankTwoPoisson.eisQ z)

theorem realGauss_nonneg (t : ℝ) (z : ℤ × ℤ) :
    0 ≤ realGauss t z := (Real.exp_pos _).le

theorem realGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (realGauss t) := by
  have h := (RankTwoPoisson.eis_gauss_summable ht).norm
  convert h using 1
  funext z
  dsimp [realGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp

theorem realGauss_cast (t : ℝ) (z : ℤ × ℤ) :
    (realGauss t z : ℂ) = RankTwoEisShift.shifted t 0 0 z := by
  dsimp [realGauss, RankTwoPoisson.eisQ,
    RankTwoEisShift.shifted, RankTwoEisShift.Q]
  rw [← Complex.ofReal_exp]
  congr 1
  ring_nf

theorem real_gaussian_mass :
    Tendsto (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  have hC := EisensteinAbelFiber.shifted_gaussian_mass 0 0
  have hRe := (Complex.continuous_re.tendsto
    (((2 / Real.sqrt 3 : ℝ) : ℂ))).comp hC
  have hsum (t : ℝ) :
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
        (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) := by
    calc
      (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z) =
          ∑' z : ℤ × ℤ, (realGauss t z : ℂ) := by
            apply tsum_congr
            intro z
            exact (realGauss_cast t z).symm
      _ = (((∑' z : ℤ × ℤ, realGauss t z) : ℝ) : ℂ) :=
        (Complex.ofReal_tsum (realGauss t)).symm
  have hfun (t : ℝ) :
      t * (∑' z : ℤ × ℤ, realGauss t z) =
        (((t : ℂ) * (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z)).re) := by
    rw [hsum]
    norm_cast
  have hEq :
      (fun t : ℝ => t * (∑' z : ℤ × ℤ, realGauss t z)) =
        (Complex.re ∘
          (fun t : ℝ => (t : ℂ) *
            (∑' z : ℤ × ℤ, RankTwoEisShift.shifted t 0 0 z))) := by
    funext t
    exact hfun t
  rw [← hEq] at hRe
  simpa only [Complex.ofReal_re] using hRe

end GaussianMoment

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem dual_gaussian_is_actual_trace_phase
    (a b k l : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let r : ℝ := OscSpecial.r η (a : ℝ) (b : ℝ)
    RankTwoComplex.dualGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) (k,l) =
      Complex.exp (-(Real.pi : ℂ) *
        ((η : ℂ) * (q : ℂ) / (4 * (r : ℂ))) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      ShortDraftTrace.breveE
        (eisEmbedding (-(c * y^2)) / eisLam / ((4*r : ℝ) : ℂ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  dsimp only
  rw [OscSpecial.dualGaussian_explicit hη hq (k,l)]
  rw [dualFrequencyEquiv_trace_phase (OscSpecial.r η (a : ℝ) (b : ℝ)) a b k l]
  have hnormC : ((‖eisEmbedding (dualFrequencyEquiv (k,l))‖ : ℂ)^2) =
      (((k^2+k*l+l^2 : ℤ) : ℂ)) := by
    exact_mod_cast dualFrequencyEquiv_norm_sq k l
  rw [hnormC]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem actual_oscillatory_poisson
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let r : ℝ := OscSpecial.r η (a : ℝ) (b : ℝ)
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      (1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' y : O,
          Complex.exp (-(Real.pi : ℂ) *
            ((η : ℂ) * (q : ℂ) / (4 * (r : ℂ))) *
            (‖eisEmbedding y‖ ^ 2 : ℂ)) *
          ShortDraftTrace.breveE
            (eisEmbedding (-(c * y^2)) / eisLam / ((4*r : ℝ) : ℂ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  dsimp only
  rw [actual_oscillatory_sum_eq_binary a b hc η,
    OscSpecial.oscillatory_gaussian_poisson hη hq]
  congr 1
  let W : O → ℂ := fun y =>
    Complex.exp (-(Real.pi : ℂ) *
      ((η : ℂ) * (OscSpecial.q (a : ℝ) (b : ℝ) : ℂ) /
        (4 * (OscSpecial.r η (a : ℝ) (b : ℝ) : ℂ))) *
      (‖eisEmbedding y‖ ^ 2 : ℂ)) *
    ShortDraftTrace.breveE
      (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
        eisLam /
        ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))
  calc
    (∑' p : ℤ × ℤ,
      RankTwoComplex.dualGaussian
        (OscSpecial.A η (a : ℝ) (b : ℝ))
        (OscSpecial.B η (a : ℝ) (b : ℝ))
        (OscSpecial.D η (a : ℝ) (b : ℝ)) p) =
        ∑' p : ℤ × ℤ, W (dualFrequencyEquiv p) := by
      apply tsum_congr
      intro p
      simpa only [W] using
        dual_gaussian_is_actual_trace_phase a b p.1 p.2 hc η hη
    _ = ∑' y : O, W y := dualFrequencyEquiv.tsum_eq W

end ActualEisensteinCubic

namespace OscSpecial

private theorem R_eq_four_r_div_q {η a b : ℝ} (hq : q a b ≠ 0) :
    R η a b = 4 * r η a b / q a b := by
  unfold R r
  field_simp [hq]
  ring

private theorem sqrt_R_eq {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b) :
    Real.sqrt (R η a b) = 2 * Real.sqrt (r η a b) / Real.sqrt (q a b) := by
  rw [R_eq_four_r_div_q hq.ne']
  rw [Real.sqrt_div' (4 * r η a b) hq.le]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hs4]

theorem prefactor_eq_real_sqrt {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    (1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ) := by
  have hR : 0 ≤ R η a b := by unfold R; positivity
  have hqS : Real.sqrt (q a b) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hrS : Real.sqrt (r η a b) ≠ 0 :=
    (Real.sqrt_pos.mpr (r_pos hη hq)).ne'
  have hcpow : (R η a b : ℂ) ^ (1 / 2 : ℂ) =
      ((R η a b) ^ (1 / 2 : ℝ) : ℝ) := by
    simpa using (Complex.ofReal_cpow hR (1 / 2 : ℝ)).symm
  rw [hcpow]
  simp only [Complex.ofReal_div]
  rw [← Real.sqrt_eq_rpow, sqrt_R_eq hη hq]
  push_cast
  field_simp [hqS, hrS]

open scoped Topology
open Filter

theorem prefactor_tendsto {a b : ℝ} (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) := by
  have hrcont : Continuous (fun η : ℝ => r η a b) := by
    unfold r
    fun_prop
  have hr : Tendsto (fun η : ℝ => r η a b) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [r] using (hrcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun η : ℝ => Real.sqrt (r η a b))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have hd : Tendsto (fun η : ℝ => Real.sqrt (q a b) /
      (2 * Real.sqrt (r η a b))) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (q a b) / 2)) := by
    convert tendsto_const_nhds.div (tendsto_const_nhds.mul hs)
      (by norm_num : (2 : ℝ) * 1 ≠ 0) using 1 ; simp
  have hc : Tendsto (fun η : ℝ =>
      ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (((Real.sqrt (q a b) / 2 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hd
  have heq : (fun η : ℝ => 1 / ((R η a b : ℂ) ^ (1 / 2 : ℂ))) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ((Real.sqrt (q a b) / (2 * Real.sqrt (r η a b)) : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact prefactor_eq_real_sqrt hη hq
  exact hc.congr' heq.symm

end OscSpecial

namespace GaussianMoment

open scoped Topology
open Filter

private theorem eisQ_nonneg (z : ℤ × ℤ) : 0 ≤ RankTwoPoisson.eisQ z := by
  have h := RankTwoPoisson.eisQ_lower z
  nlinarith [sq_nonneg (z.1 : ℝ), sq_nonneg (z.2 : ℝ)]

private theorem moment_term_bound {t : ℝ} (ht : 0 < t) (z : ℤ × ℤ) :
    RankTwoPoisson.eisQ z * realGauss t z ≤
      (2 / (Real.pi * t)) * realGauss (t / 2) z := by
  have h := gaussian_moment_term_bound (RankTwoPoisson.eisQ z) (Real.pi * t)
    (eisQ_nonneg z) (mul_pos Real.pi_pos ht)
  convert h using 1 <;> dsimp [realGauss] <;> ring_nf

private theorem moment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => RankTwoPoisson.eisQ z * realGauss t z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  exact hmajor.of_nonneg_of_le
    (fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z))
    (moment_term_bound ht)

private theorem moment_tsum_bound {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
      (2 / (Real.pi * t)) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z) := by
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * realGauss (t / 2) z) :=
    (realGauss_summable (t := t / 2) (half_pos ht)).mul_left _
  have h := Summable.tsum_le_tsum (moment_term_bound ht)
    (moment_summable ht) hmajor
  simpa only [tsum_mul_left] using h

private theorem moment_tsum_nonneg (t : ℝ) :
    0 ≤ (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) := by
  exact tsum_nonneg fun z => mul_nonneg (eisQ_nonneg z) (realGauss_nonneg t z)

private theorem half_tendsto_within :
    Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => t / 2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact half_pos ht

private theorem t_tendsto_zero :
    Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
  tendsto_id.mono_left nhdsWithin_le_nhds

private theorem scaled_half_mass_tendsto :
    Tendsto
      (fun t : ℝ => (t / 2) *
        (∑' z : ℤ × ℤ, realGauss (t / 2) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 / Real.sqrt 3)) := by
  simpa only [Function.comp_def] using real_gaussian_mass.comp half_tendsto_within

theorem scaled_moment_vanishes :
    Tendsto
      (fun t : ℝ => t ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hright : Tendsto
      (fun t : ℝ => (4 / Real.pi) * t *
        ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := (t_tendsto_zero.mul scaled_half_mass_tendsto).const_mul (4 / Real.pi)
    simpa only [zero_mul, mul_zero, Function.comp_def, mul_assoc] using h
  have hleft : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact mul_nonneg (pow_nonneg ht.le _) (moment_tsum_nonneg t)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    have h := moment_tsum_bound ht
    have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht.le _
    have hmul := mul_le_mul_of_nonneg_left h ht3
    calc
      t ^ 3 * (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss t z) ≤
          t ^ 3 * ((2 / (Real.pi * t)) *
            (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := hmul
      _ = (4 / Real.pi) * t *
          ((t / 2) * (∑' z : ℤ × ℤ, realGauss (t / 2) z)) := by
        field_simp [ht.ne']
        ring

end GaussianMoment

end

end OAI
end OAIOriginalModule0066

/-! Original module: OAI.NumberTheory.DirichletL.PrimeCounting.Progressions
Source SHA256: 6fdc9180de7cbafd2e78164f97d2f9b6fdaa7d21523b6fe42a8f900ced80c665
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0067


namespace OAI

namespace SevenEighths.PNT

open Filter ArithmeticFunction LSeries
open scoped Topology

theorem residueClass_chebyshev {q : ℕ} (a : ZMod q) :
    ∃ C : ℝ, ∀ N : ℕ,
      cumsum (fun n : ℕ => ‖(vonMangoldt.residueClass a n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨C, fun N => le_trans ?_ (hC N)⟩
  unfold cumsum
  apply Finset.sum_le_sum
  intro n hn
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldt.residueClass_nonneg a n),
    abs_of_nonneg vonMangoldt_nonneg] using vonMangoldt.residueClass_le a n

theorem residueClass_summable {q : ℕ} (a : ZMod q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (vonMangoldt.residueClass a n : ℂ)) σ) := by
  have hs : LSeriesSummable (fun n => (vonMangoldt.residueClass a n : ℂ)) (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      lt_of_le_of_lt (vonMangoldt.abscissaOfAbsConv_residueClass_le_one a) (by
        exact_mod_cast hσ)
  simpa only [← nterm_eq_norm_term] using hs.norm

theorem residueClass_ratio_tendsto {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N : ℕ => cumsum (vonMangoldt.residueClass a) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (vonMangoldt.residueClass_nonneg a)
    (fun σ hσ => residueClass_summable a hσ)
    (residueClass_chebyshev a)
    (vonMangoldt.continuousOn_LFunctionResidueClassAux a)
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
    vonMangoldt.eqOn_LFunctionResidueClassAux ha

end SevenEighths.PNT

end OAI
end OAIOriginalModule0067

/-! Original module: OAI.NumberTheory.DirichletL.PrimeCounting.PrimeMass
Source SHA256: 0117055741a1b13bfdab6f68b2ee8965eba05b4d59339aa6ec3a5574e0bcc408
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0068


namespace OAI

namespace SevenEighths.PNT

open Filter ArithmeticFunction
open scoped Topology BigOperators

theorem cumsum_div_tendsto_zero_of_summable_div {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hsum : Summable (fun n => f n / n)) :
    Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 0) := by
  let F : ℕ → ℕ → ℝ := fun N n => if n < N then f n / N else 0
  have hlim (n : ℕ) : Tendsto (fun N => F N n) atTop (𝓝 0) := by
    apply (tendsto_const_div_atTop_nhds_zero_nat (f n)).congr'
    filter_upwards [eventually_gt_atTop n] with N hN
    simp [F, hN]
  have hbound : ∀ N n, ‖F N n‖ ≤ f n / n := by
    intro N n
    by_cases hn : n = 0
    · subst n
      simp [F, hzero]
    by_cases hN : n < N
    · simp only [F, ite_eq_left hN, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (hf n) (Nat.cast_nonneg N))]
      exact div_le_div_of_nonneg_left (hf n)
        (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_ne_zero hn)
        (show (n : ℝ) ≤ N by exact_mod_cast hN.le)
    · simp only [F, ite_eq_right hN, norm_zero]
      exact div_nonneg (hf n) (by positivity)
  have h := tendsto_tsum_of_dominated_convergence hsum hlim
    (Filter.Eventually.of_forall hbound)
  have heq (N : ℕ) : (∑' n, F N n) = cumsum f N / N := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => by
      simp only [Finset.mem_range] at hn
      simp [F, hn])]
    rw [cumsum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    simp [F, Finset.mem_range.mp hn]
  simpa only [heq, tsum_zero] using h

theorem retained_ratio_tendsto {f : ℕ → ℝ} {A : ℝ} (keep : ℕ → Prop)
    [DecidablePred keep] (hf : ∀ n, 0 ≤ f n) (hzero : f 0 = 0)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (hremainder : Summable (fun n => (if keep n then 0 else f n) / n)) :
    Tendsto (fun N : ℕ => cumsum (fun n => if keep n then f n else 0) N / N)
      atTop (𝓝 A) := by
  have hrem := cumsum_div_tendsto_zero_of_summable_div
    (f := fun n => if keep n then 0 else f n)
    (fun n => by split_ifs <;> first | exact le_rfl | exact hf n)
    (by simp [hzero]) hremainder
  have h := hmass.sub hrem
  have heq (N : ℕ) :
      cumsum f N / N - cumsum (fun n => if keep n then 0 else f n) N / N =
      cumsum (fun n => if keep n then f n else 0) N / N := by
    rw [← sub_div]
    congr 1
    simp only [cumsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp
  simpa only [heq, sub_zero] using h

theorem prime_residueClass_ratio_tendsto {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N : ℕ =>
      cumsum (fun n => if n.Prime then vonMangoldt.residueClass a n else 0) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) :=
  retained_ratio_tendsto Nat.Prime (vonMangoldt.residueClass_nonneg a)
    (vonMangoldt.residueClass_apply_zero a) (residueClass_ratio_tendsto a ha)
    (vonMangoldt.summable_residueClass_non_primes_div a)

end SevenEighths.PNT

end OAI
end OAIOriginalModule0068

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.RationalApproximation
Source SHA256: 012355cc98f2de5f32ba6d9a09d0f7702f2b17f4b28bfb4c3d09143e416083f6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0069


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic

open Filter

namespace RationalQuant

private theorem cpos : 0 < Real.log 2 / 20 := by
  have h : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

theorem eventual_log_absorption (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → 2 ≤ D →
      D ^ ((4 / 45 : ℝ) - ε) ≤
        (Real.log 2 / 20) *
          (D ^ (4 / 45 : ℝ) / Real.log (D ^ (4 / 45 : ℝ))) := by
  have hsmall := (isLittleO_log_rpow_atTop hε).bound cpos
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp hsmall
  refine ⟨D₀, ?_⟩
  intro D hD hDtwo
  have hDpos : 0 < D := by linarith
  have hDone : 1 ≤ D := by linarith
  have hlogDpos : 0 < Real.log D := Real.log_pos (by linarith)
  have hpowpos : 0 < D ^ (4 / 45 : ℝ) := Real.rpow_pos_of_pos hDpos _
  have hlogYpos : 0 < Real.log (D ^ (4 / 45 : ℝ)) := by
    rw [Real.log_rpow hDpos]
    positivity
  have hlogD : Real.log D ≤
      (Real.log 2 / 20) * D ^ ε := by
    have h := hD₀ D hD
    simpa only [Real.norm_eq_abs, abs_of_pos hlogDpos,
      abs_of_pos (Real.rpow_pos_of_pos hDpos ε)] using h
  have hYleD : D ^ (4 / 45 : ℝ) ≤ D := by
    calc
      D ^ (4 / 45 : ℝ) ≤ D ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hDone (by norm_num)
      _ = D := by simp
  have hlogY : Real.log (D ^ (4 / 45 : ℝ)) ≤
      (Real.log 2 / 20) * D ^ ε :=
    (Real.log_le_log hpowpos hYleD).trans hlogD
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlogYpos).mpr
  calc
    D ^ ((4 / 45 : ℝ) - ε) * Real.log (D ^ (4 / 45 : ℝ)) ≤
        D ^ ((4 / 45 : ℝ) - ε) *
          ((Real.log 2 / 20) * D ^ ε) :=
          mul_le_mul_of_nonneg_left hlogY (Real.rpow_nonneg hDpos.le _)
    _ = (Real.log 2 / 20) * D ^ (4 / 45 : ℝ) := by
      calc
        D ^ ((4 / 45 : ℝ) - ε) *
            ((Real.log 2 / 20) * D ^ ε) =
            (Real.log 2 / 20) *
              (D ^ ((4 / 45 : ℝ) - ε) * D ^ ε) := by ring
        _ = (Real.log 2 / 20) *
            D ^ (((4 / 45 : ℝ) - ε) + ε) := by
              rw [← Real.rpow_add hDpos]
        _ = (Real.log 2 / 20) * D ^ (4 / 45 : ℝ) := by
              congr 1
              ring_nf

theorem scale_large_eventually (Y₀ : ℝ) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      2 ≤ D ∧ Y₀ ≤ D ^ (4 / 45 : ℝ) := by
  let M : ℝ := max 1 Y₀
  refine ⟨max 2 (M ^ (45 / 4 : ℝ)), ?_⟩
  intro D hD
  have hD2 : 2 ≤ D := (le_max_left _ _).trans hD
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_left _ _)
  have hpowle : M ^ (45 / 4 : ℝ) ≤ D :=
    (le_max_right _ _).trans hD
  have hroot : M ≤ D ^ (4 / 45 : ℝ) := by
    calc
      M = (M ^ (45 / 4 : ℝ)) ^ (4 / 45 : ℝ) := by
        rw [← Real.rpow_mul hMpos.le]
        have hmul : (45 / 4 : ℝ) * (4 / 45 : ℝ) = 1 := by norm_num
        rw [hmul]
        simp
      _ ≤ D ^ (4 / 45 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hMpos.le _) hpowle (by norm_num)
  exact ⟨hD2, (le_max_right _ _).trans hroot⟩

theorem from_rational_prime_rows_with_constant
    (D ε J A C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hJ : D ^ ((4 / 45 : ℝ) - ε) ≤ J)
    (hmean : J * A ^ 2 ≤
      2 * D ^ ((31 / 15 : ℝ) + ε) +
      2 * J * C ^ 2 * D ^ (82 / 45 : ℝ)) :
    A ≤ 2 * C * D ^ ((89 / 90 : ℝ) + ε) := by
  let E : ℝ := (89 / 90 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hJpos : 0 < J := lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hJ
  have hpow :
      D ^ ((31 / 15 : ℝ) + ε) ≤
        J * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    calc
      D ^ ((31 / 15 : ℝ) + ε) =
          D ^ ((4 / 45 : ℝ) - ε) *
            D ^ ((89 / 45 : ℝ) + 2 * ε) := by
            rw [← Real.rpow_add hDpos]
            congr 1
            ring
      _ ≤ J * D ^ ((89 / 45 : ℝ) + 2 * ε) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
  have herr : D ^ (82 / 45 : ℝ) ≤
      D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hP : 0 ≤ J * D ^ ((89 / 45 : ℝ) + 2 * ε) := by positivity
  have hsq : A ^ 2 ≤
      4 * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    have hmain : J * A ^ 2 ≤
        4 * J * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
      calc
        J * A ^ 2 ≤
            2 * D ^ ((31 / 15 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (82 / 45 : ℝ) := hmean
        _ ≤ 2 * (J * D ^ ((89 / 45 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
              gcongr
        _ ≤ 4 * J * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hP]
    nlinarith
  have hexp : (89 / 45 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((89 / 45 : ℝ) + 2 * ε) := by rw [hexp]
  have htwo : 0 ≤ 2 * C * D ^ E := by positivity
  apply (sq_le_sq₀ hA htwo).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith

theorem rational_row_error_power
    (D r : ℕ) (hD : 1 ≤ D)
    (hrlo : (D : ℝ) ^ (4 / 45 : ℝ) / 3 < (r : ℝ)) :
    ((128 * (D / r + 1) : ℕ) : ℝ) ≤
      512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
  let X : ℝ := (D : ℝ) ^ (4 / 45 : ℝ)
  let P : ℝ := (D : ℝ) ^ (41 / 45 : ℝ)
  let q : ℝ := (D / r : ℕ)
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hXpos : 0 < X := Real.rpow_pos_of_pos hDpos _
  have hqnonneg : 0 ≤ q := by positivity
  have hP1 : 1 ≤ P := by
    calc
      1 = (D : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (D : ℝ) ^ (41 / 45 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hDreal (by norm_num)
  have hDP : (D : ℝ) = X * P := by
    dsimp [X, P]
    rw [← Real.rpow_add hDpos]
    norm_num
  have hdivnat : D / r * r ≤ D := Nat.div_mul_le_self D r
  have hdivreal : q * (r : ℝ) ≤ (D : ℝ) := by
    change ((D / r : ℕ) : ℝ) * (r : ℝ) ≤ (D : ℝ)
    exact_mod_cast hdivnat
  have hXr : X ≤ 3 * (r : ℝ) := by
    dsimp [X] at hrlo ⊢
    linarith
  have hXq : X * q ≤ 3 * (D : ℝ) := by
    calc
      X * q ≤ (3 * (r : ℝ)) * q :=
        mul_le_mul_of_nonneg_right hXr hqnonneg
      _ ≤ 3 * (D : ℝ) := by nlinarith [hdivreal]
  have hq : q ≤ 3 * P := by
    apply le_of_mul_le_mul_left (a := X) ?_ hXpos
    calc
      X * q ≤ 3 * (D : ℝ) := hXq
      _ = X * (3 * P) := by rw [hDP]; ring
  have hfinal : (128 : ℝ) * (q + 1) ≤ 512 * P := by
    nlinarith [hq, hP1]
  simpa [q, P] using hfinal

end RationalQuant

open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

namespace RationalPrimeExtraction

theorem eventual_count_power (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      2 ≤ D ∧
      (D : ℝ) ^ ((4 / 45 : ℝ) - ε) ≤
        ((selected ((D : ℝ) ^ (4 / 45 : ℝ))).card : ℝ) := by
  obtain ⟨Y₀, hcount⟩ := rational_prime_three_interval_count
  obtain ⟨Dlog, hlog⟩ := RationalQuant.eventual_log_absorption ε hε
  obtain ⟨Dscale, hscale⟩ := RationalQuant.scale_large_eventually Y₀
  refine ⟨max Dlog Dscale, ?_⟩
  intro D hD
  have hDl : Dlog ≤ (D : ℝ) := (le_max_left _ _).trans hD
  have hDs : Dscale ≤ (D : ℝ) := (le_max_right _ _).trans hD
  obtain ⟨hDtwo, hY⟩ := hscale (D : ℝ) hDs
  have hDtwoNat : 2 ≤ D := by exact_mod_cast hDtwo
  have habs := hlog (D : ℝ) hDl hDtwo
  have hprime := hcount ((D : ℝ) ^ (4 / 45 : ℝ)) hY
  exact ⟨hDtwoNat, habs.trans (by simpa only [selected] using hprime)⟩

theorem selected_rows_in_ball [DecidableEq O] (D : ℕ) (hD : 1 ≤ D) :
    (selected ((D : ℝ) ^ (4 / 45 : ℝ))).image
      (fun r : ℕ => (r : O) ^ 6) ⊆
      rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊ := by
  classical
  intro u hu
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
  have hrI : r ∈ Finset.Ioc
      ⌊(D : ℝ) ^ (4 / 45 : ℝ) / 3⌋₊
      ⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ :=
    (Finset.mem_filter.mp hr).1
  have hrprime : r.Prime := (Finset.mem_filter.mp hr).2
  have hrupper : r ≤ ⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ :=
    (Finset.mem_Ioc.mp hrI).2
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hYpos : 0 ≤ (D : ℝ) ^ (4 / 45 : ℝ) :=
    Real.rpow_nonneg hDpos.le _
  have hrupperCast : (r : ℝ) ≤
      (⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hrupper
  have hrupperReal : (r : ℝ) ≤ (D : ℝ) ^ (4 / 45 : ℝ) :=
    hrupperCast.trans (Nat.floor_le hYpos)
  have hnorm : qNat ((r : O) ^ 6) = r ^ 12 := by
    rw [rational_qNat_pow r 6 hrprime.ne_zero]
    ring
  have hpow : (r : ℝ) ^ 12 ≤
      ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 := by gcongr
  have hYpow : ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 =
      (D : ℝ) ^ (16 / 15 : ℝ) := by
    calc
      ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 =
          (D : ℝ) ^ ((4 / 45 : ℝ) * (12 : ℕ)) :=
          (Real.rpow_mul_natCast hDpos.le _ 12).symm
      _ = (D : ℝ) ^ (16 / 15 : ℝ) := by congr 1; norm_num
  have hnormreal : (qNat ((r : O) ^ 6) : ℝ) ≤
      (⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊ : ℝ) := by
    rw [hnorm]
    exact (by exact_mod_cast hpow :
      ((r ^ 12 : ℕ) : ℝ) ≤ ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12).trans
        (hYpow.le.trans (Nat.le_ceil _))
  exact mem_rowNormBall_of_qNat_le _ _ (by exact_mod_cast hnormreal)

theorem selected_row_error_bound (D : ℕ) (hD : 1 ≤ D)
    (r : ℕ) (hr : r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ))) :
    ((128 * (D / r + 1) : ℕ) : ℝ) ≤
      512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
  have hrlo : ⌊(D : ℝ) ^ (4 / 45 : ℝ) / 3⌋₊ < r :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
  exact RationalQuant.rational_row_error_power D r hD
    (Nat.lt_of_floor_lt hrlo)

end RationalPrimeExtraction

open ActualEisensteinCubic ShortDraftLatticeCount

namespace RationalPrimeExtraction

theorem eventual_finite_extraction (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      ∀ A : O → ℂ,
      (∀ r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ)),
        ‖A 1 - A ((r : O) ^ 6)‖ ≤
          512 * (D : ℝ) ^ (41 / 45 : ℝ)) →
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖A u‖ ^ 2) ≤
          (D : ℝ) ^ ((31 / 15 : ℝ) + ε) →
      ‖A 1‖ ≤ 1024 * (D : ℝ) ^ ((89 / 90 : ℝ) + ε) := by
  obtain ⟨D₀, hcount⟩ := eventual_count_power ε hε
  refine ⟨D₀, ?_⟩
  intro D hD A happrox hmean
  classical
  obtain ⟨hDtwo, hJcount⟩ := hcount D hD
  have hDone : 1 ≤ D := by omega
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hDone
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  let S := selected ((D : ℝ) ^ (4 / 45 : ℝ))
  let rows := rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊
  let E : ℝ := 512 * (D : ℝ) ^ (41 / 45 : ℝ)
  let M : ℝ := (D : ℝ) ^ ((31 / 15 : ℝ) + ε)
  have hrows : S.image (fun r : ℕ => (r : O) ^ 6) ⊆ rows :=
    selected_rows_in_ball D hDone
  have hinj : Set.InjOn (fun r : ℕ => (r : O) ^ 6) (S : Set ℕ) := by
    intro r _ s _ hrs
    exact rational_sixth_injective hrs
  have hextract := ShortDraft.complex_row_extraction rows S
    (fun r : ℕ => (r : O) ^ 6) A 1 E M
    (by dsimp [E]; positivity) hrows hinj happrox hmean
  have herr : E ^ 2 = 512 ^ 2 * (D : ℝ) ^ (82 / 45 : ℝ) := by
    dsimp [E]
    rw [mul_pow]
    congr 1
    calc
      ((D : ℝ) ^ (41 / 45 : ℝ)) ^ 2 =
          (D : ℝ) ^ ((41 / 45 : ℝ) * (2 : ℕ)) :=
          (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = (D : ℝ) ^ (82 / 45 : ℝ) := by congr 1; norm_num
  rw [herr] at hextract
  have hextract' : (S.card : ℝ) * ‖A 1‖ ^ 2 ≤
      2 * (D : ℝ) ^ ((31 / 15 : ℝ) + ε) +
      2 * (S.card : ℝ) * 512 ^ 2 *
        (D : ℝ) ^ (82 / 45 : ℝ) := by
    dsimp [M] at hextract
    nlinarith [hextract]
  have hbound := RationalQuant.from_rational_prime_rows_with_constant
    (D : ℝ) ε (S.card : ℝ) ‖A 1‖ 512 hDreal hε.le
    (norm_nonneg _) (by norm_num) hJcount hextract'
  simpa only [show (2 : ℝ) * 512 = 1024 by norm_num] using hbound

open ActualEisensteinCubic ShortDraftLatticeCount

theorem actual_rational_prime_extraction
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      (∀ n ∈ columns, qNat n ≤ D) →
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((31 / 15 : ℝ) + ε) →
      ‖∑ n ∈ columns, weight n‖ ≤
        1024 * (D : ℝ) ^ ((89 / 90 : ℝ) + ε) := by
  obtain ⟨D₁, hgeneric⟩ := eventual_finite_extraction ε hε
  refine ⟨max 2 D₁, ?_⟩
  intro D hD hcolnorm hmean
  classical
  have hDtwoReal : (2 : ℝ) ≤ D := (le_max_left _ _).trans hD
  have hDtwo : 2 ≤ D := by exact_mod_cast hDtwoReal
  have hDone : 1 ≤ D := by omega
  have hDgeneric : D₁ ≤ (D : ℝ) := (le_max_right _ _).trans hD
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have happrox : ∀ r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ)),
      ‖A 1 - A ((r : O) ^ 6)‖ ≤
        512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
    intro r hr
    have hrprime : r.Prime := (Finset.mem_filter.mp hr).2
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) ((r : O) ^ 6))‖ ≤ _
    exact (rational_prime_sixth_row_approx P hgood columns support weight
      r hrprime D hsupport hcolnorm hweight).trans
      (selected_row_error_bound D hDone r hr)
  have hmean' :
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖A u‖ ^ 2) ≤ (D : ℝ) ^ ((31 / 15 : ℝ) + ε) := hmean
  have hbound := hgeneric D hDgeneric A happrox hmean'
  simpa only [hone] using hbound

end RationalPrimeExtraction

namespace OscSpecial

noncomputable def phaseBoundConstant (a b : ℝ) : ℝ :=
  2 * (|a - b| + |a| + |b|) + 1

theorem phaseBoundConstant_pos (a b : ℝ) :
    0 < phaseBoundConstant a b := by
  unfold phaseBoundConstant
  positivity

theorem quadratic_phase_abs_le (a b k l : ℝ) :
    |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
      phaseBoundConstant a b * (k ^ 2 + k * l + l ^ 2) := by
  let Q : ℝ := k ^ 2 + k * l + l ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    nlinarith [sq_nonneg (k + l), sq_nonneg k, sq_nonneg l]
  have hsum : k ^ 2 + l ^ 2 ≤ 2 * Q := by
    dsimp [Q]
    nlinarith [sq_nonneg (k + l)]
  have hcross : 2 * |k| * |l| ≤ k ^ 2 + l ^ 2 := by
    nlinarith [sq_nonneg (|k| - |l|), sq_abs k, sq_abs l]
  have hk : k ^ 2 ≤ 2 * Q := by nlinarith [hsum, sq_nonneg l]
  have hl : l ^ 2 ≤ 2 * Q := by nlinarith [hsum, sq_nonneg k]
  have hkl : 2 * |k| * |l| ≤ 2 * Q := hcross.trans hsum
  have h1 := mul_le_mul_of_nonneg_left hk (abs_nonneg (a - b))
  have h2 := mul_le_mul_of_nonneg_left hkl (abs_nonneg a)
  have h3 := mul_le_mul_of_nonneg_left hl (abs_nonneg b)
  have htri :
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
        |a - b| * k ^ 2 + 2 * |a| * |k| * |l| + |b| * l ^ 2 := by
    calc
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
          |(a - b) * k ^ 2| + |2 * a * k * l| + |b * l ^ 2| := by
        calc
          _ ≤ |(a - b) * k ^ 2 + 2 * a * k * l| + |b * l ^ 2| := abs_add_le _ _
          _ ≤ _ := by
            have hh := abs_add_le ((a - b) * k ^ 2) (2 * a * k * l)
            linarith
      _ = _ := by
        simp [abs_mul,  abs_of_nonneg (sq_nonneg k),
          abs_of_nonneg (sq_nonneg l)]
  unfold phaseBoundConstant
  nlinarith [htri, h1, h2, h3, hQ]

end OscSpecial

namespace GaussianMoment

open scoped Topology
open Filter

theorem scaled_moment_vanishes_const (K : ℝ) (hK : 0 < K) :
    Tendsto
      (fun η : ℝ => η ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss (K * η) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hscale : Tendsto (fun η : ℝ => K * η)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun η : ℝ => K * η) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      change 0 < η at hη
      exact mul_pos hK hη
  have h := scaled_moment_vanishes.comp hscale
  have h' := h.const_mul (1 / K ^ 3)
  convert h' using 1
  · funext η
    dsimp [Function.comp_def]
    field_simp [hK.ne']
  · simp

end GaussianMoment

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

private theorem breveE_period_div_lam_O (z : O) :
    ShortDraftTrace.breveE (eisEmbedding z / eisLam) = 1 := by
  let a := (ActualEisensteinCoordinates.coords z).1
  let b := (ActualEisensteinCoordinates.coords z).2
  have hz : z = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz, eisEmbedding_eval]
  exact ConcreteBreveE.breveE_period_coordinates a b

noncomputable def fixedDualPhase (c y : O) : ℂ :=
  ShortDraftTrace.breveE (eisEmbedding (-(c*y^2)) / eisLam / (4 : ℂ))

theorem fixedDualPhase_period_two (c y w : O) :
    fixedDualPhase c (y + 2*w) = fixedDualPhase c y := by
  let d : O := -(c * (y*w+w^2))
  have hO : -(c * (y + 2*w)^2) = -(c*y^2) + 4*d := by
    dsimp [d]
    ring
  have h4 : eisEmbedding (4*d) = 4 * eisEmbedding d := by
    simp only [map_mul, map_ofNat]
  have harg :
      eisEmbedding (-(c * (y + 2*w)^2)) / eisLam / (4 : ℂ) =
        eisEmbedding (-(c*y^2)) / eisLam / (4 : ℂ) +
          eisEmbedding d / eisLam := by
    rw [hO, map_add, h4]
    ring
  unfold fixedDualPhase
  rw [harg, AddChar.map_add_eq_mul, breveE_period_div_lam_O, mul_one]

theorem fixedDualPhase_eq_of_mod_two (c y z : O)
    (h : Ideal.Quotient.mk (Ideal.span {(2 : O)}) y =
      Ideal.Quotient.mk (Ideal.span {(2 : O)}) z) :
    fixedDualPhase c y = fixedDualPhase c z := by
  have hsub : y-z ∈ Ideal.span {(2 : O)} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hsub
  have hy : y = z + 2*w := by
    calc
      y = z+(y-z) := by ring
      _ = z+2*w := by rw [hw]
  rw [hy, fixedDualPhase_period_two]

theorem fixedDualPhase_weighted_partition (c : O) (W : O → ℂ)
    (hsum : Summable (fun y : O => fixedDualPhase c y * W y)) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑' y : O, fixedDualPhase c y * W y) =
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
          ∑' w : O,
            W (GaussianShiftedPartition.representative 2 r + 2*w) := by
  let h2 : (2 : O) ≠ 0 := by norm_num
  let : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_quotient_span h2
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.tsum_by_finite_fibers
    (Ideal.Quotient.mk (Ideal.span {(2 : O)})) _ hsum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {(2 : O)})) ⁻¹' {r}),
      fixedDualPhase c z.1 * W z.1) =
        ∑' w : O, fixedDualPhase c
          (GaussianShiftedPartition.representative 2 r + 2*w) *
          W (GaussianShiftedPartition.representative 2 r + 2*w) :=
      GaussianFiberEquiv.fiber_tsum 2 h2 r
        (GaussianShiftedPartition.representative 2 r)
        (GaussianShiftedPartition.representative_spec 2 r)
        (fun y => fixedDualPhase c y * W y)
    _ =
        ∑' w : O, fixedDualPhase c
          (GaussianShiftedPartition.representative 2 r) *
          W (GaussianShiftedPartition.representative 2 r + 2*w) := by
      apply tsum_congr
      intro w
      rw [fixedDualPhase_period_two]
    _ = _ := tsum_mul_left

end ActualEisensteinCubic

namespace OscSpecial

open scoped Topology
open Filter

noncomputable def dualScale (η a b : ℝ) : ℝ :=
  η * q a b / (4 * r η a b)

theorem dualScale_tendsto (a b : ℝ) (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have hnum : ContinuousAt (fun η : ℝ => η * q a b) 0 := by fun_prop
  have hden : ContinuousAt (fun η : ℝ => 4 * r η a b) 0 := by
    change ContinuousAt
      (fun η : ℝ => 4 * (1 + 3 * q a b * η ^ 2 / 16)) 0
    fun_prop
  have hden0 : 4 * r 0 a b ≠ 0 := by simp [r]
  have hcont : ContinuousAt (fun η : ℝ => dualScale η a b) 0 := by
    exact hnum.div hden hden0
  have hlim : Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [dualScale] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact hlim
  · filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hr : 0 < r η a b := by
      unfold r
      positivity
    exact div_pos (mul_pos hη hq) (mul_pos (by norm_num) hr)

theorem abel_mass_dual_scale (a b : ℝ) (hq : 0 < q a b)
    (F : ℝ → ℂ) (L : ℂ)
    (hF : Tendsto (fun t : ℝ => (t : ℂ) * F t)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun η : ℝ => (η : ℂ) * F (dualScale η a b))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((4 / q a b : ℝ) : ℂ) * L)) := by
  have hscale := dualScale_tendsto a b hq
  have hF' := hF.comp hscale
  have hrcont : ContinuousAt
      (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ)) 0 := by
    change ContinuousAt
      (fun η : ℝ => ((4 * (1 + 3 * q a b * η ^ 2 / 16) / q a b : ℝ) : ℂ)) 0
    fun_prop
  have hr : Tendsto (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((4 / q a b : ℝ) : ℂ)) := by
    simpa [r] using hrcont.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := hr.mul hF'
  have heq : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      (η : ℂ) * F (dualScale η a b) =
        ((4 * r η a b / q a b : ℝ) : ℂ) *
          (((dualScale η a b : ℝ) : ℂ) * F (dualScale η a b)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hrpos : 0 < r η a b := by
      unfold r
      positivity
    have hqC : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hrC : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    dsimp [dualScale]
    push_cast
    field_simp [hqC, hrC]
  exact hprod.congr' (heq.mono fun η h => h.symm)

end OscSpecial

end

end OAI
end OAIOriginalModule0069

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.AbelPhaseLimit
Source SHA256: 53993b78f3b59061c136fbf292f1c1291dac99c0ef9a8378b035f984e66fd78e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0070


namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

private theorem sum_zmod_two_square (f : ZMod 2 × ZMod 2 → ℂ) :
    (∑ p : ZMod 2 × ZMod 2, f p) =
      f (0,0) + f (0,1) + f (1,0) + f (1,1) := by
  rw [Fintype.sum_prod_type]
  have hu : (Finset.univ : Finset (ZMod 2)) = {0,1} := rfl
  simp [hu]
  ring

theorem fixedDualPhase_quotient_two_four_residues (c : O) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑ r : O ⧸ Ideal.span {(2 : O)},
      fixedDualPhase c (GaussianShiftedPartition.representative 2 r)) =
      fixedDualPhase c (ActualEisensteinCoordinates.eval 0 0) +
      fixedDualPhase c (ActualEisensteinCoordinates.eval 0 1) +
      fixedDualPhase c (ActualEisensteinCoordinates.eval 1 0) +
      fixedDualPhase c (ActualEisensteinCoordinates.eval 1 1) := by
  let h2 : (2 : O) ≠ 0 := by norm_num
  let : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_quotient_span h2
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let e := rationalCoordEquiv 2 (by norm_num)
  let P : O ⧸ Ideal.span {(2 : O)} → ℂ :=
    fun r => fixedDualPhase c (GaussianShiftedPartition.representative 2 r)
  have hpoint (p : ZMod 2 × ZMod 2) :
      P (e p) = fixedDualPhase c
        (ActualEisensteinCoordinates.eval (ZMod.cast p.1) (ZMod.cast p.2)) := by
    dsimp only [P]
    apply fixedDualPhase_eq_of_mod_two
    rw [GaussianShiftedPartition.representative_spec]
    exact rationalCoordEquiv_apply 2 (by norm_num) p.1 p.2
  have hsum : (∑ r : O ⧸ Ideal.span {(2 : O)}, P r) =
      ∑ p : ZMod 2 × ZMod 2,
        fixedDualPhase c
          (ActualEisensteinCoordinates.eval (ZMod.cast p.1) (ZMod.cast p.2)) := by
    calc
      (∑ r : O ⧸ Ideal.span {(2 : O)}, P r) =
          ∑ p : ZMod 2 × ZMod 2, P (e p) := (e.sum_comp P).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpoint p
  rw [show (∑ r : O ⧸ Ideal.span {(2 : O)},
      fixedDualPhase c (GaussianShiftedPartition.representative 2 r)) =
      ∑ r : O ⧸ Ideal.span {(2 : O)}, P r from rfl]
  rw [hsum, sum_zmod_two_square]
  have hcast1 : (ZMod.cast (1 : ZMod 2) : ℤ) = 1 := by decide
  simp only [ZMod.cast_zero, hcast1]

theorem fixedDualPhase_coordinates (a b x y : ℤ) :
    fixedDualPhase (ActualEisensteinCoordinates.eval a b)
      (ActualEisensteinCoordinates.eval x y) =
      ShortDraftTrace.breveE
        ((-(((a : ℂ)+(b : ℂ)*omega3) *
          (((x : ℂ)+(y : ℂ)*omega3)^2))) / eisLam / 4) := by
  unfold fixedDualPhase
  rw [map_neg, map_mul, map_pow, eisEmbedding_eval, eisEmbedding_eval]

theorem fixedDualPhase_four_terms (a b : ℤ) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑ r : O ⧸ Ideal.span {(2 : O)},
      fixedDualPhase (ActualEisensteinCoordinates.eval a b)
        (GaussianShiftedPartition.representative 2 r)) / 2 =
      breveGaussianFourTerms a b := by
  let : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    finite_quotient_span (by norm_num : (2 : O) ≠ 0)
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  rw [fixedDualPhase_quotient_two_four_residues]
  rw [fixedDualPhase_coordinates a b 0 0,
    fixedDualPhase_coordinates a b 0 1,
    fixedDualPhase_coordinates a b 1 0,
    fixedDualPhase_coordinates a b 1 1]
  unfold breveGaussianFourTerms
  norm_num
  ring_nf

end ActualEisensteinCubic

namespace OscSpecial

noncomputable def dualQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 + (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2

noncomputable def dualTrace (a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  (a - b) * (z.1 : ℝ) ^ 2 + 2 * a * (z.1 : ℝ) * (z.2 : ℝ) +
    b * (z.2 : ℝ) ^ 2

noncomputable def phaseA (a b : ℝ) : ℝ := 3 * q a b / 16
noncomputable def phaseAngle (a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  -(Real.pi / 2) * dualTrace a b z
noncomputable def dualAmp (η a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * (η * q a b / (4 * r η a b)) * dualQ z)
noncomputable def dualVarTerm (η a b : ℝ) (z : ℤ × ℤ) : ℂ :=
  (dualAmp η a b z : ℂ) *
    Complex.exp (Complex.I * ((phaseAngle a b z / r η a b : ℝ) : ℂ))
noncomputable def dualFixedTerm (η a b : ℝ) (z : ℤ × ℤ) : ℂ :=
  (dualAmp η a b z : ℂ) *
    Complex.exp (Complex.I * (phaseAngle a b z : ℂ))

private theorem dualQ_nonneg (z : ℤ × ℤ) : 0 ≤ dualQ z := by
  unfold dualQ
  nlinarith [sq_nonneg ((z.1 : ℝ) + (z.2 : ℝ)), sq_nonneg (z.1 : ℝ),
    sq_nonneg (z.2 : ℝ)]

private theorem phaseAngle_bound (a b : ℝ) (z : ℤ × ℤ) :
    |phaseAngle a b z| ≤
      (Real.pi / 2) * phaseBoundConstant a b * dualQ z := by
  have h := quadratic_phase_abs_le a b (z.1 : ℝ) (z.2 : ℝ)
  dsimp [phaseAngle, dualTrace, dualQ]
  rw [abs_mul, abs_neg, abs_of_pos (half_pos Real.pi_pos)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left h (half_pos Real.pi_pos).le

private theorem r_eq_one_add_phaseA (η a b : ℝ) :
    r η a b = 1 + phaseA a b * η ^ 2 := by
  unfold r phaseA
  ring

private theorem phaseA_nonneg {a b : ℝ} (hq : 0 ≤ q a b) :
    0 ≤ phaseA a b := by
  unfold phaseA
  positivity

theorem dual_phase_term_error {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
      dualAmp η a b z *
        ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
        (phaseA a b * η ^ 2) := by
  have hA : 0 ≤ phaseA a b := phaseA_nonneg hq.le
  have hamp : 0 ≤ dualAmp η a b z := (Real.exp_pos _).le
  have hphase := GaussianPhasePointwise.exp_imag_denominator_error
    (phaseAngle a b z) (phaseA a b) η hA
  rw [← r_eq_one_add_phaseA η a b] at hphase
  have hangle := phaseAngle_bound a b z
  have hangle' := mul_le_mul_of_nonneg_right hangle
    (mul_nonneg hA (sq_nonneg η))
  dsimp [dualVarTerm, dualFixedTerm]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hamp]
  nlinarith [mul_le_mul_of_nonneg_left hphase hamp,
    mul_le_mul_of_nonneg_left hangle' hamp]

noncomputable def dualRealGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * dualQ z)

private theorem dualRealGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (dualRealGauss t) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss t (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable ht)
  convert hE.norm using 1
  funext z
  dsimp [dualRealGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_re]
  congr 1
  dsimp [dualQ, RankTwoPoisson.eisQ]
  push_cast
  ring

private theorem dualMoment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => dualQ z * dualRealGauss t z) := by
  have hmaj : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * dualRealGauss (t / 2) z) :=
    (dualRealGauss_summable (half_pos ht)).mul_left _
  apply hmaj.of_nonneg_of_le
  · intro z
    exact mul_nonneg (dualQ_nonneg z) (Real.exp_pos _).le
  · intro z
    have h := GaussianMoment.gaussian_moment_term_bound
      (dualQ z) (Real.pi * t) (dualQ_nonneg z) (mul_pos Real.pi_pos ht)
    convert h using 1 <;> dsimp [dualRealGauss] <;> ring_nf

private theorem dualAmp_eq_realGauss (η a b : ℝ) (z : ℤ × ℤ) :
    dualAmp η a b z = dualRealGauss (η * q a b / (4 * r η a b)) z := rfl

private theorem dualAmp_norm_var (η a b : ℝ) (z : ℤ × ℤ) :
    ‖dualVarTerm η a b z‖ = dualAmp η a b z := by
  dsimp [dualVarTerm]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real]
  exact abs_of_nonneg (Real.exp_pos _).le

private theorem dualAmp_norm_fixed (η a b : ℝ) (z : ℤ × ℤ) :
    ‖dualFixedTerm η a b z‖ = dualAmp η a b z := by
  dsimp [dualFixedTerm]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real]
  exact abs_of_nonneg (Real.exp_pos _).le

private theorem dualAmp_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualAmp η a b) := by
  have hr : 0 < r η a b := r_pos hη hq
  have ht : 0 < η * q a b / (4 * r η a b) := by positivity
  convert dualRealGauss_summable ht using 1
  funext z
  exact dualAmp_eq_realGauss η a b z

private theorem dualVar_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualVarTerm η a b) :=
  (dualAmp_summable hη hq).of_norm_bounded
    (fun z => le_of_eq (dualAmp_norm_var η a b z))

private theorem dualFixed_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualFixedTerm η a b) :=
  (dualAmp_summable hη hq).of_norm_bounded
    (fun z => le_of_eq (dualAmp_norm_fixed η a b z))

private theorem dualAmp_le_small {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (hrle : r η a b ≤ 2)
    (z : ℤ × ℤ) :
    dualAmp η a b z ≤ dualRealGauss (η * q a b / 8) z := by
  have hr : 0 < r η a b := r_pos hη hq
  have hp : 0 < η * q a b := mul_pos hη hq
  have ht : η * q a b / 8 ≤ η * q a b / (4 * r η a b) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (by positivity : 0 < 4 * r η a b)).2
    nlinarith [mul_le_mul_of_nonneg_left hrle hp.le]
  dsimp [dualAmp, dualRealGauss]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right ht
    (mul_nonneg Real.pi_pos.le (dualQ_nonneg z))
  nlinarith [hm]

noncomputable def phaseErrorConstant (a b : ℝ) : ℝ :=
  (Real.pi / 2) * phaseBoundConstant a b * phaseA a b

private theorem phaseErrorConstant_nonneg {a b : ℝ} (hq : 0 < q a b) :
    0 ≤ phaseErrorConstant a b := by
  unfold phaseErrorConstant
  exact mul_nonneg (mul_nonneg (half_pos Real.pi_pos).le
    (phaseBoundConstant_pos a b).le) (phaseA_nonneg hq.le)

theorem normalized_dual_phase_sum_error {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (hrle : r η a b ≤ 2) :
    η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
      (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖ ≤
      phaseErrorConstant a b * η ^ 3 *
        (∑' z : ℤ × ℤ,
          dualQ z * dualRealGauss (η * q a b / 8) z) := by
  let t : ℝ := η * q a b / 8
  have ht : 0 < t := by dsimp [t]; positivity
  have hK : 0 ≤ phaseErrorConstant a b := phaseErrorConstant_nonneg hq
  have hpoint (z : ℤ × ℤ) :
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
        (phaseErrorConstant a b * η ^ 2) *
          (dualQ z * dualRealGauss t z) := by
    have hbase := dual_phase_term_error hη hq z
    have hamp := dualAmp_le_small hη hq hrle z
    have hfac : 0 ≤
        ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (half_pos Real.pi_pos).le
          (phaseBoundConstant_pos a b).le) (dualQ_nonneg z))
        (mul_nonneg (phaseA_nonneg hq.le) (sq_nonneg η))
    have hmul := mul_le_mul_of_nonneg_right hamp hfac
    dsimp [t, phaseErrorConstant]
    calc
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
        dualAmp η a b z *
          ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := hbase
      _ ≤ dualRealGauss (η * q a b / 8) z *
          ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := by nlinarith [hmul]
      _ = ((Real.pi / 2 * phaseBoundConstant a b * phaseA a b) * η ^ 2) *
          (dualQ z * dualRealGauss (η * q a b / 8) z) := by ring
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (phaseErrorConstant a b * η ^ 2) *
        (dualQ z * dualRealGauss t z)) :=
    (dualMoment_summable ht).mul_left _
  have hnorm : Summable (fun z : ℤ × ℤ =>
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖) :=
    hmajor.of_nonneg_of_le (fun z => norm_nonneg _) hpoint
  have hsum := norm_tsum_le_tsum_norm hnorm
  have htsum := Summable.tsum_le_tsum hpoint hnorm hmajor
  have hvar := dualVar_summable hη hq
  have hfixed := dualFixed_summable hη hq
  calc
    η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
      (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖ =
      η * ‖(∑' z : ℤ × ℤ, (dualVarTerm η a b z - dualFixedTerm η a b z))‖ := by
        rw [hvar.tsum_sub hfixed]
    _ ≤ η * (∑' z : ℤ × ℤ,
          ‖dualVarTerm η a b z - dualFixedTerm η a b z‖) :=
      mul_le_mul_of_nonneg_left hsum hη.le
    _ ≤ η * (∑' z : ℤ × ℤ,
          (phaseErrorConstant a b * η ^ 2) *
            (dualQ z * dualRealGauss t z)) :=
      mul_le_mul_of_nonneg_left htsum hη.le
    _ = phaseErrorConstant a b * η ^ 3 *
          (∑' z : ℤ × ℤ, dualQ z * dualRealGauss (η * q a b / 8) z) := by
      rw [tsum_mul_left]
      dsimp [t]
      ring

open scoped Topology
open Filter

private theorem dual_moment_reindex (t : ℝ) :
    (∑' z : ℤ × ℤ, dualQ z * dualRealGauss t z) =
      ∑' z : ℤ × ℤ,
        RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  calc
    (∑' z : ℤ × ℤ, dualQ z * dualRealGauss t z) =
        ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisQ (e z) * GaussianMoment.realGauss t (e z) := by
      apply tsum_congr
      intro z
      have hQ : RankTwoPoisson.eisQ (e z) = dualQ z := by
        rcases z with ⟨k,l⟩
        change (k : ℝ) ^ 2 - (k : ℝ) * ((-l : ℤ) : ℝ) +
          ((-l : ℤ) : ℝ) ^ 2 =
          (k : ℝ) ^ 2 + (k : ℝ) * (l : ℝ) + (l : ℝ) ^ 2
        push_cast
        ring
      simp only [GaussianMoment.realGauss, dualRealGauss, hQ]
    _ = ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z :=
      e.tsum_eq (fun z : ℤ × ℤ =>
        RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z)

theorem normalized_dual_phase_sum_error_tendsto_zero {a b : ℝ}
    (hq : 0 < q a b) :
    Tendsto
      (fun η : ℝ =>
        η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
          (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let K : ℝ := q a b / 8
  have hK : 0 < K := by dsimp [K]; positivity
  have hmoment :
      Tendsto
        (fun η : ℝ => η ^ 3 *
          (∑' z : ℤ × ℤ,
            dualQ z * dualRealGauss (η * q a b / 8) z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert GaussianMoment.scaled_moment_vanishes_const K hK using 1
    funext η
    dsimp [K]
    rw [dual_moment_reindex]
    ring_nf
  have hright :
      Tendsto
        (fun η : ℝ => phaseErrorConstant a b * η ^ 3 *
          (∑' z : ℤ × ℤ,
            dualQ z * dualRealGauss (η * q a b / 8) z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert hmoment.const_mul (phaseErrorConstant a b) using 1
    · funext η
      ring
    · simp
  have hr_lim : Tendsto (fun η : ℝ => r η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun η : ℝ => r η a b) 0 := by
      unfold r
      fun_prop
    simpa [r] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hrle : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), r η a b ≤ 2 := by
    have hevent : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), x ≤ 2 :=
      eventually_le_nhds (by norm_num)
    exact hr_lim.eventually hevent
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hright
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact mul_nonneg hη.le (norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin, hrle] with η hη hbound
    exact normalized_dual_phase_sum_error hη hq hbound

theorem dualGaussian_eq_dualVarTerm {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      dualVarTerm η a b z := by
  rw [dualGaussian_explicit hη hq z]
  have hQ :
      ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) =
        (dualQ z : ℂ) := by
    dsimp [dualQ]
    push_cast
    ring
  have hT :
      (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
        2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
        (b : ℂ) * (z.2 : ℂ) ^ 2) =
        (dualTrace a b z : ℂ) := by
    dsimp [dualTrace]
    push_cast
    ring
  rw [hQ, hT]
  have hrC : (r η a b : ℂ) ≠ 0 := by
    exact_mod_cast (r_pos hη hq).ne'
  have harg :
      -(Real.pi : ℂ) *
        ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ)) *
          (dualQ z : ℂ) +
          Complex.I / (2 * (r η a b : ℂ)) * (dualTrace a b z : ℂ)) =
      (((-Real.pi * (η * q a b / (4 * r η a b)) * dualQ z : ℝ) : ℂ)) +
        Complex.I * ((phaseAngle a b z / r η a b : ℝ) : ℂ) := by
    dsimp [phaseAngle]
    push_cast
    field_simp [hrC]
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  rfl

end OscSpecial

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT

theorem osc_q_eq_eis_norm_sq (a b : ℤ) :
    OscSpecial.q (a : ℝ) (b : ℝ) =
      ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ ^ 2 := by
  rw [eisEmbedding_eval_norm_sq]
  dsimp [OscSpecial.q]
  push_cast
  ring

theorem two_coordinate_norm_four :
    let a := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((a*a-a*b+b*b : ℤ) : ℝ)) = 4 := by
  have h2 : (2 : O) = ActualEisensteinCoordinates.eval 2 0 := by
    simp [ActualEisensteinCoordinates.eval]
  rw [h2, ShortDraftLatticeCount.coords_eval]
  norm_num

end ActualEisensteinCubic

open Filter
open scoped Topology

theorem abel_transfer (P V W : ℝ → ℂ) (p w : ℂ)
    (hP : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 p))
    (hW : Tendsto (fun η : ℝ => (η : ℂ) * W η) (𝓝[>] (0 : ℝ)) (𝓝 w))
    (hE : Tendsto (fun η => η * ‖V η - W η‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Tendsto (fun η : ℝ => (η : ℂ) * (P η * V η))
      (𝓝[>] (0 : ℝ)) (𝓝 (p * w)) := by
  have hdiff : Tendsto (fun η : ℝ => (η : ℂ) * (V η - W η))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun η : ℝ => ‖(η : ℂ) * (V η - W η)‖) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun η => η * ‖V η - W η‖) := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    exact hE.congr' heq.symm
  have hV : Tendsto (fun η : ℝ => (η : ℂ) * V η)
      (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    convert hW.add hdiff using 1
    · funext η; ring
    · simp
  convert hP.mul hV using 1
  · funext η; ring

namespace ActualEisensteinCubic

section

theorem gamma_scalar (n : ℝ) (hn : 0 < n) (G S : ℂ)
    (h : (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * G) =
      (((n / 2 : ℝ) : ℂ) *
        (((4 / (n*n) : ℝ) : ℂ) *
          (((2 / (Real.sqrt 3 * 4) : ℝ) : ℂ) * S)))) :
    G = S / 2 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast at h
  field_simp [hnC, hsC] at h
  calc
    G = (2 * G) / 2 := by ring
    _ = S / 2 := by rw [h]

open EisensteinEmbedding ConcreteTraceCRT Complex

private theorem breveE_norm_one_all (z : ℂ) :
    ‖ShortDraftTrace.breveE z‖ = 1 := by
  change ‖Complex.exp (2 * Real.pi * Complex.I * (z + star z))‖ = 1
  rw [Complex.norm_exp]
  have hr : (2 * (Real.pi : ℂ) * Complex.I * (z + star z)).re = 0 := by
    simp [Complex.mul_re]
  rw [hr, Real.exp_zero]

theorem fixedDualPhase_norm_one (c y : O) :
    ‖fixedDualPhase c y‖ = 1 := by
  unfold fixedDualPhase
  exact breveE_norm_one_all _

end

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem variableDualPhase_abel_limit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' y : O, fixedDualPhase c y *
        Complex.exp (-(Real.pi : ℂ) *
          (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
          (‖eisEmbedding y‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r))) := by
  let h2 : (2 : O) ≠ 0 := by norm_num
  let : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_quotient_span h2
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let c : O := ActualEisensteinCoordinates.eval a b
  let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
  let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
  let L2 : ℂ := ((2 / (Real.sqrt 3 *
    (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
  let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
  let W (η : ℝ) (y : O) := Complex.exp
    (-(Real.pi : ℂ) *
      (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
      (‖eisEmbedding y‖ ^ 2 : ℂ))
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  have hfiber (r : O ⧸ Ideal.span {(2 : O)}) :
      Tendsto (fun η : ℝ => (η : ℂ) *
        (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w)))
        (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    let F : ℝ → ℂ := fun t => ∑' w : O,
      Complex.exp (-(Real.pi : ℂ) * (t : ℂ) *
        (‖eisEmbedding (GaussianShiftedPartition.representative 2 r + 2*w)‖ ^ 2 : ℂ))
    have hbase : Tendsto (fun t : ℝ => (t : ℂ) * F t)
        (𝓝[>] (0 : ℝ)) (𝓝 L2) := by
      simpa only [F, L2, a2, b2] using
        actual_O_fiber_gaussian_mass (2 : O)
          (GaussianShiftedPartition.representative 2 r) h2
    have h := OscSpecial.abel_mass_dual_scale (a : ℝ) (b : ℝ) hq F L2 hbase
    simpa only [W, F, K] using h
  have hsum : Tendsto (fun η : ℝ =>
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) * K)) := by
    apply tendsto_finsetSum Finset.univ
    intro r hr
    exact (hfiber r).const_mul _
  have hpoint (η : ℝ) (hη : 0 < η) :
      (η : ℂ) * (∑' y : O, fixedDualPhase c y * W η y) =
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w))) := by
    have hrpos : 0 < OscSpecial.r η (a : ℝ) (b : ℝ) := by
      unfold OscSpecial.r
      positivity
    have htpos : 0 < OscSpecial.dualScale η (a : ℝ) (b : ℝ) := by
      unfold OscSpecial.dualScale
      positivity
    have hbase := (eis_gaussian_summable htpos).norm
    have hkernel : Summable (fun y : O => fixedDualPhase c y * W η y) := by
