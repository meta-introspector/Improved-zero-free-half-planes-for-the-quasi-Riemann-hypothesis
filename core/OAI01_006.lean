      apply hbase.of_norm_bounded
      intro y
      simp only [norm_mul]
      have hp : ‖fixedDualPhase c y‖ = 1 := fixedDualPhase_norm_one c y
      rw [hp, one_mul]
    have hpart := fixedDualPhase_weighted_partition c (W η) hkernel
    rw [hpart, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have heq : (fun η : ℝ => (η : ℂ) *
      (∑' y : O, fixedDualPhase c y * W η y)) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w)))) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hpoint η hη
  have hlim := hsum.congr' heq.symm
  have hKsum :
      (∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) * K) =
      K * ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) := by
    rw [← Finset.sum_mul, mul_comm]
  rw [hKsum] at hlim
  exact hlim

end ActualEisensteinCubic

end

end OAI
end OAIOriginalModule0070

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.ThetaLocalRows
Source SHA256: 785995f2ef45c7b5a3ca7885fd7433d44e5be445154c17706e5c465dc36e774e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0071


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
open Filter
open scoped Topology

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_fixed_kernel_eq_dualFixedTerm
    (a b k l : ℤ) (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      fixedDualPhase c y =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) (k,l) := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let y : O := dualFrequencyEquiv (k,l)
  have hnormC : ((‖eisEmbedding y‖ : ℂ)^2) =
      (((k^2+k*l+l^2 : ℤ) : ℂ)) := by
    exact_mod_cast dualFrequencyEquiv_norm_sq k l
  have hreal : Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) =
      (OscSpecial.dualAmp η (a : ℝ) (b : ℝ) (k,l) : ℂ) := by
    rw [hnormC]
    dsimp [OscSpecial.dualAmp, OscSpecial.dualScale, OscSpecial.dualQ]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase : fixedDualPhase c y =
      Complex.exp (Complex.I *
        (OscSpecial.phaseAngle (a : ℝ) (b : ℝ) (k,l) : ℂ)) := by
    have h := breveE_dual_quadratic_real_scale 1 a b k l
    have harg : fixedDualPhase c y =
        Complex.exp (-(2 * Real.pi * Complex.I *
          (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) / (4 : ℂ)) := by
      change ShortDraftTrace.breveE
        (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
          (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
          eisLam / (4 : ℂ)) = _
      simpa using h
    rw [harg]
    congr 1
    dsimp [OscSpecial.phaseAngle, OscSpecial.dualTrace]
    push_cast
    ring
  dsimp only
  rw [hreal, hphase]
  rfl

open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped Topology
open Filter

noncomputable def actualVariableDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  ShortDraftTrace.breveE
    (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
      eisLam /
      ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))

noncomputable def actualFixedDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  fixedDualPhase (ActualEisensteinCoordinates.eval a b) y

private theorem dualScale_cast (η a b : ℝ) :
    (OscSpecial.dualScale η a b : ℂ) =
      (η : ℂ) * (OscSpecial.q a b : ℂ) /
        (4 * (OscSpecial.r η a b : ℂ)) := by
  dsimp [OscSpecial.dualScale]
  push_cast
  ring

theorem actual_variable_kernel_eq_dualVarTerm
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) (z : ℤ × ℤ) :
    actualVariableDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  have h := (dual_gaussian_is_actual_trace_phase
    a b z.1 z.2 hc η hη).symm.trans
      (OscSpecial.dualGaussian_eq_dualVarTerm hη hq z)
  unfold actualVariableDualKernel
  rw [dualScale_cast]
  exact h

theorem actual_fixed_kernel_eq_dualFixedTerm_point
    (a b : ℤ) (η : ℝ) (z : ℤ × ℤ) :
    actualFixedDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by
  rcases z with ⟨k,l⟩
  exact actual_fixed_kernel_eq_dualFixedTerm a b k l η

theorem actual_dual_phase_error_tendsto_zero
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    Tendsto
      (fun η : ℝ => η * ‖
        (∑' y : O, actualVariableDualKernel a b η y) -
        (∑' y : O, actualFixedDualKernel a b η y)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  have hbase := OscSpecial.normalized_dual_phase_sum_error_tendsto_zero hq
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  change 0 < η at hη
  have hvar :
      (∑' y : O, actualVariableDualKernel a b η y) =
        ∑' z : ℤ × ℤ, OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
    calc
      (∑' y : O, actualVariableDualKernel a b η y) =
          ∑' z : ℤ × ℤ,
            actualVariableDualKernel a b η (dualFrequencyEquiv z) :=
        (dualFrequencyEquiv.tsum_eq (actualVariableDualKernel a b η)).symm
      _ = _ := by
        apply tsum_congr
        intro z
        exact actual_variable_kernel_eq_dualVarTerm a b hc η hη z
  have hfixed :
      (∑' y : O, actualFixedDualKernel a b η y) =
        ∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by
    calc
      (∑' y : O, actualFixedDualKernel a b η y) =
          ∑' z : ℤ × ℤ,
            actualFixedDualKernel a b η (dualFrequencyEquiv z) :=
        (dualFrequencyEquiv.tsum_eq (actualFixedDualKernel a b η)).symm
      _ = _ := by
        apply tsum_congr
        intro z
        exact actual_fixed_kernel_eq_dualFixedTerm_point a b η z
  rw [hvar, hfixed]

end

section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actualFixedAbelLimit (a b : ℤ)
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
      (∑' y : O, actualFixedDualKernel a b η y))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r))) := by
  simpa only [actualFixedDualKernel, mul_comm] using
    variableDualPhase_abel_limit a b hc

end

section

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_oscillatory_poisson_kernel
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      (1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' y : O, actualVariableDualKernel a b η y := by
  dsimp only
  rw [actual_oscillatory_poisson a b hc η hη]
  congr 1
  apply tsum_congr
  intro y
  unfold actualVariableDualKernel
  rw [dualScale_cast]

end

section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actualVariableAbelLimit (a b : ℤ)
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
      ((1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1/2 : ℂ))) *
        (∑' y : O, actualVariableDualKernel a b η y)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ) *
        (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
          fixedDualPhase c (GaussianShiftedPartition.representative 2 r))))) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  exact abel_transfer
    (fun η => 1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1/2 : ℂ)))
    (fun η => ∑' y : O, actualVariableDualKernel a b η y)
    (fun η => ∑' y : O, actualFixedDualKernel a b η y)
    _ _ (OscSpecial.prefactor_tendsto hq)
    (actualFixedAbelLimit a b hc)
    (actual_dual_phase_error_tendsto_zero a b hc)

theorem actualOriginalAbelDualLimit (a b : ℤ)
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
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ) *
        (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
          fixedDualPhase c (GaussianShiftedPartition.representative 2 r))))) := by
  apply (actualVariableAbelLimit a b hc).congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  change 0 < η at hη
  rw [actual_oscillatory_poisson_kernel a b hc η hη]

end

section

theorem dual_abel_coefficient (a b : ℤ)
    (hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ)) :
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) *
      ((2 / (Real.sqrt 3 *
        (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)) =
      ((2 / (Real.sqrt 3 * OscSpecial.q (a : ℝ) (b : ℝ)) : ℝ) : ℂ) := by
  dsimp only
  rw [two_coordinate_norm_four]
  have hqC : (OscSpecial.q (a : ℝ) (b : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hsC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast
  field_simp [hqC, hsC]

theorem full_dual_abel_coefficient (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) *
        ((2 / (Real.sqrt 3 *
          (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ))) =
      (((2 / (Real.sqrt 3 * ‖ConcreteTraceCRT.eisEmbedding c‖) : ℝ) : ℂ) / 2) := by
  dsimp only
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  rw [dual_abel_coefficient a b hq]
  have hqnorm := osc_q_eq_eis_norm_sq a b
  have hsqrt : Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) =
      ‖ConcreteTraceCRT.eisEmbedding
        (ActualEisensteinCoordinates.eval a b)‖ := by
    rw [hqnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hsqrt, hqnorm]
  have hn : (‖ConcreteTraceCRT.eisEmbedding
      (ActualEisensteinCoordinates.eval a b)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (norm_pos_iff.mpr
      (ConcreteTraceCRT.eisEmbedding_ne_zero hc)))
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast
  field_simp [hn, hs]

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem quadraticGammaO_eq_fourTerms (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    quadraticGammaO (ActualEisensteinCoordinates.eval a b) hc =
      breveGaussianFourTerms a b := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let n : ℝ := ‖eisEmbedding c‖
  let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
  let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
  let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
  let L2 : ℂ := ((2 / (Real.sqrt 3 *
    (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
  let : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    finite_quotient_span (by norm_num : (2 : O) ≠ 0)
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let S : ℂ := ∑ r : O ⧸ Ideal.span {(2 : O)},
    fixedDualPhase c (GaussianShiftedPartition.representative 2 r)
  have hEq0 := tendsto_nhds_unique
    (original_abel_gamma_limit c hc)
    (actualOriginalAbelDualLimit a b hc)
  have hEq : (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * quadraticGammaO c hc) =
      (((Real.sqrt q / 2 : ℝ) : ℂ) *
        ((((4 / q : ℝ) : ℂ) * L2) * S)) := by
    simpa only [c, n, q, a2, b2, L2, S, mul_assoc] using hEq0
  have hC : (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) * L2)) =
      (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) / 2) := by
    simpa only [c, n, q, a2, b2, L2] using
      full_dual_abel_coefficient a b hc
  have hA : ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) ≠ 0 := by
    have hn : 0 < n := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
    have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast (ne_of_gt (div_pos (by norm_num : (0 : ℝ) < 2)
      (mul_pos hs hn)))
  have hG : quadraticGammaO c hc = S / 2 := by
    apply mul_left_cancel₀ hA
    calc
      ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * quadraticGammaO c hc =
          ((Real.sqrt q / 2 : ℝ) : ℂ) *
            ((((4 / q : ℝ) : ℂ) * L2) * S) := hEq
      _ = (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) / 2) * S := by rw [← mul_assoc, hC]
      _ = ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * (S / 2) := by ring
  change quadraticGammaO c hc = breveGaussianFourTerms a b
  calc
    quadraticGammaO c hc = S / 2 := hG
    _ = breveGaussianFourTerms a b := fixedDualPhase_four_terms a b

end

theorem quadraticGammaO_formula (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    quadraticGammaO (ActualEisensteinCoordinates.eval a b) hc =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  rw [quadraticGammaO_eq_fourTerms a b hc, breveGaussianFourTerms_formula]

end ActualEisensteinCubic

theorem theta_counter_lambda_eq : ActualEisensteinCubic.lambda =
    ActualEisensteinCoordinates.eval (-1) 1 := by
  have homega : ActualEisensteinCubic.omega = ActualEisensteinCoordinates.omega := by
    rfl
  rw [ActualEisensteinCubic.lambda, ActualEisensteinCoordinates.eval, homega]
  ring

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

private noncomputable def pSeven : ActualEisensteinCubic.O := ActualEisensteinCoordinates.eval 1 3
private noncomputable def PSeven : Ideal ActualEisensteinCubic.O := Ideal.span {pSeven}

private theorem pSeven_norm : ShortDraftLatticeCount.qNat pSeven = 7 := by
  unfold ShortDraftLatticeCount.qNat pSeven
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

private theorem pSeven_ne : pSeven ≠ 0 := by
  intro h
  have hh : ActualEisensteinCoordinates.eval 1 3 = ActualEisensteinCoordinates.eval 0 0 := by
    simpa [pSeven, ActualEisensteinCoordinates.eval] using h
  have := (ActualEisensteinCoordinates.unique_coordinates hh).1
  omega

private theorem PSeven_absNorm : Ideal.absNorm PSeven = 7 := by
  simpa only [PSeven, ActualEisensteinCubic.qNat_eq_absNorm_span] using pSeven_norm

private theorem PSeven_maximal : PSeven.IsMaximal := by
  have hprime : PSeven.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by
    rw [PSeven_absNorm, Nat.irreducible_iff_nat_prime]
    exact (by decide : Nat.Prime 7))
  apply hprime.isMaximal
  exact Ideal.span_singleton_eq_bot.not.mpr pSeven_ne

private theorem lambda7_norm :
    ShortDraftLatticeCount.qNat (ActualEisensteinCoordinates.eval (-1) 1) = 3 := by
  unfold ShortDraftLatticeCount.qNat
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

private theorem nonreal_cube_ne_conj (γ z : ℂ) (hz : z ≠ 0)
    (hIm : z.im ≠ 0)
    (hc : γ ^ 3 = -z / (‖z‖ : ℂ)) : γ ≠ star γ := by
  intro hγ
  have hstar : star (γ ^ 3) = γ ^ 3 := by
    rw [star_pow, ← hγ]
  have hn : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hq : -(star z) / (‖z‖ : ℂ) = -z / (‖z‖ : ℂ) := by
    calc
      -(star z) / (‖z‖ : ℂ) = star (γ ^ 3) := by
        rw [hc, star_div₀]
        simp
      _ = γ ^ 3 := hstar
      _ = _ := hc
  have heq : star z = z := by
    have hh := (div_left_inj' hn).mp hq
    exact neg_injective hh
  exact hIm (Complex.conj_eq_iff_im.mp heq)

private theorem pSeven_embedding_im_ne_zero : (eisEmbedding pSeven).im ≠ 0 := by
  rw [pSeven, ActualEisensteinCubic.eisEmbedding_eval]
  have h : ((((1 : ℤ) : ℂ) + ((3 : ℤ) : ℂ) * omega3).im) = 3 * omega3.im := by
    simp
  rw [h]
  exact mul_ne_zero (by norm_num) omega3_im_ne_zero

noncomputable def thetaGammaSeven : ℂ := by
  letI : PSeven.IsMaximal := PSeven_maximal
  exact breveGamma2 PSeven
    (by
      rw [theta_counter_lambda_eq]
      intro hh
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hh
      have hnorm := congrArg ShortDraftLatticeCount.qNat hx
      rw [ShortDraftLatticeCount.qNat_mul, pSeven_norm, lambda7_norm] at hnorm
      omega)
    pSeven rfl pSeven_ne

theorem thetaGammaSeven_cube :
    thetaGammaSeven ^ 3 = -eisEmbedding pSeven / (‖eisEmbedding pSeven‖ : ℂ) := by
  unfold thetaGammaSeven
  let : PSeven.IsMaximal := PSeven_maximal
  exact ActualEisensteinCubic.breveGamma2_cube PSeven
    (by
      rw [theta_counter_lambda_eq]
      intro hh
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hh
      have hnorm := congrArg ShortDraftLatticeCount.qNat hx
      rw [ShortDraftLatticeCount.qNat_mul, pSeven_norm, lambda7_norm] at hnorm
      omega)
    pSeven rfl pSeven_ne
    (by
      rw [theta_counter_lambda_eq]
      refine ⟨-1, ?_⟩
      rw [pow_two, ActualEisensteinCoordinates.eval_mul]
      norm_num [pSeven, ActualEisensteinCoordinates.eval])

theorem thetaGammaSeven_ne_conj : thetaGammaSeven ≠ star thetaGammaSeven := by
  have hz : eisEmbedding pSeven ≠ 0 := by
    intro h
    have := pSeven_embedding_im_ne_zero
    rw [h] at this
    exact this rfl
  exact nonreal_cube_ne_conj thetaGammaSeven (eisEmbedding pSeven) hz
    pSeven_embedding_im_ne_zero thetaGammaSeven_cube

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem direct_theta_jone_inversion (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum χ⁻¹ (ψ.mulShift a) := by
  classical
  have hchar : χ⁻¹ * χ ^ 2 = χ := by group
  rw [hchar]
  calc
    (∑ h : Fˣ, χ (h : F) * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, χ⁻¹ (y : F) * ψ (a * (y : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro y
      simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
      rw [MulChar.inv_apply']
      simp
    _ = gaussSum χ⁻¹ (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]

theorem direct_theta_jone_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) * χ x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        (χ ^ 2) σ * gaussSum χ (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (χ⁻¹ * χ ^ 2) (h : F) *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient χ ψ hχ, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, direct_theta_jone_inversion χ ψ (ε * x)]
  have hinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by group
      _ = 1 := by rw [h]; simp
  rw [gaussSum_mulShift_any χ⁻¹ ψ hinv (ε * x)]
  simp only [inv_inv, map_mul]
  ring

theorem direct_theta_jone_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (σ : Fˣ) (ε : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * 0) * ((h⁻¹ : Fˣ) : F))) = 0 := by
  rw [direct_theta_jone_local_row χ ψ hχ σ ε 0]
  simp

omit [Fintype F] [DecidableEq F] in
theorem direct_theta_jone_not_quadratic (χ : MulChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) : χ ≠ χ ^ 3 := by
  intro h
  apply hχ₂
  calc
    χ ^ 2 = χ ^ 3 * χ⁻¹ := by group
    _ = χ * χ⁻¹ := by rw [← h]
    _ = 1 := by group

end ShortDraftLocal

end

end OAI
end OAIOriginalModule0071

/-! Original module: OAI.NumberTheory.DirichletL.Mellin.LocalNonvanishing
Source SHA256: 74e3eb47b546ccc6759405b0e686bafd3e5691b48925f45303ae1137b9016c5d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0072


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
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar

open Filter Asymptotics

namespace TargetLocalReduction

def LocalExponentialMobiusBound : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
      ∃ σ : ℝ, 0 < σ ∧ σ < ρ.re ∧ σ < 1 ∧
        (fun D : ℝ => ShortDraftMellin.mobiusExpSum χ D⁻¹) =O[atTop]
          (fun D : ℝ => D ^ σ)

theorem dirichletTarget_of_localBound
    (hbound : LocalExponentialMobiusBound) : ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · obtain ⟨σ, hσpos, hσρ, hσone, htop⟩ := hbound q χ ρ h23 hρ
    by_cases hχ : χ = 1
    · subst χ
      have hρone : ρ ≠ 1 := by
        intro h
        exact hprincipal ⟨rfl, h⟩
      exact ShortDraftMellin.principal_dirichlet_exp_zero_free_of_power_bound_only
        q σ hσpos hσone htop ρ hσρ hρone
    · exact ShortDraftMellin.dirichlet_exp_zero_free_of_power_bound_only
        χ hχ σ hσpos hσone htop ρ hσρ
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal

end TargetLocalReduction

namespace ActualEisensteinCubic

open AddChar MulChar

theorem canonical_A5_jone_direct (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (χ ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) * χ x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hχ : canonicalSextic P hgood ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one P hgood hchar
        (j := 1) (by decide) (by decide))
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.direct_theta_jone_local_row
    (canonicalSextic P hgood) ψ hχ σ ε x

theorem canonical_A5_jone_direct_not_quadratic (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    canonicalSextic P hgood ≠ (canonicalSextic P hgood) ^ 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let hχ₂ : canonicalSextic P hgood ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar
      (j := 2) (by decide) (by decide)
  exact ShortDraftLocal.direct_theta_jone_not_quadratic
    (canonicalSextic P hgood) hχ₂

theorem canonical_A5_jone_direct_scalar_ne_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (ε : O ⧸ P) (hε : ε ≠ 0) :
    let χ := canonicalSextic P hgood
    ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
      gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) ≠ 0 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ P) ℂ := canonicalSextic P hgood
  have hχ : χ ≠ 1 := by
    simpa only [χ, pow_one] using
      (canonicalSextic_pow_ne_one P hgood hchar
        (j := 1) (by decide) (by decide))
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by group
      _ = 1 := by rw [h]; simp
  have hcard : (Fintype.card (O ⧸ P) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(0 : O ⧸ P)⟩).ne'
  have hψshift : (ψ.mulShift (-1)).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one
      (hψ (neg_ne_zero.mpr (one_ne_zero : (1 : O ⧸ P) ≠ 0)))
  have hg1 : gaussSum χ (ψ.mulShift (-1)) ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard hχ hψshift
  have hg2 : gaussSum χ⁻¹ ψ ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard hχinv hψ
  have hχε : χ ε ≠ 0 := χ.apply_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mpr hε)
  dsimp only
  rw [Nat.card_eq_fintype_card]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero hcard) hg1) hg2) hχε

theorem canonical_A5_jone_trace_scalar_ne_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (ε : O ⧸ P) (hε : ε ≠ 0) :
    let χ := canonicalSextic P hgood
    let ψ : AddChar (O ⧸ P) ℂ := hP.symm ▸
      ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp
    ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
      gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) ≠ 0 := by
  subst P
  exact canonical_A5_jone_direct_scalar_ne_zero (Ideal.span {p}) hgood hchar
    (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (PrimitiveTrace.eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp)
    ε hε

end ActualEisensteinCubic

open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter

namespace ShortDraftHeckeBridge

abbrev O := ActualEisensteinSieve.O

noncomputable def normFiberCoeff (weight : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset, weight I

noncomputable def pairInverseCoeff
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ℕ → ℂ :=
  (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) ⍟
    (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ))

theorem normFiber_LSeries_eq_pair_inverse
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (s : ℂ) :
    LSeries (normFiberCoeff weight) s = LSeries (pairInverseCoeff χ ψ) s := by
  exact LSeries_congr (fun {n} hn => hcoeff n hn) s

theorem pair_inverse_euler_identity
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (s : ℂ) (hs : 1 < s.re) :
    χ.LFunction s * ψ.LFunction s * LSeries (pairInverseCoeff χ ψ) s = 1 := by
  have hχsum : LSeriesSummable (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s := by
    exact DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hψsum : LSeriesSummable (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s := by
    exact DirichletCharacter.LSeriesSummable_mul ψ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  rw [pairInverseCoeff, LSeries_convolution' hχsum hψsum,
    χ.LFunction_eq_LSeries hs, ψ.LFunction_eq_LSeries hs]
  have hχ := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hψ := DirichletCharacter.LSeries.mul_mu_eq_one ψ hs
  change LSeries (χ ·) s * LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s = 1 at hχ
  change LSeries (ψ ·) s * LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s = 1 at hψ
  calc
    LSeries (χ ·) s * LSeries (ψ ·) s *
      (LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s *
        LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s) =
      (LSeries (χ ·) s * LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s) *
      (LSeries (ψ ·) s * LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s) := by ring
    _ = 1 := by rw [hχ, hψ]; ring

theorem pair_zero_free_of_normFiber_continuation
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (σ : ℝ) (hσ : σ < 1) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hMseries : ∀ s : ℂ, 1 < s.re → M s = LSeries (normFiberCoeff weight) s)
    (ρ : ℂ) (hρ : σ < ρ.re) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (ψ.differentiable_LFunction hψ).differentiableOn
  have hL : AnalyticOnNhd ℂ (fun s => χ.LFunction s * ψ.LFunction s) U :=
    hLχ.mul hLψ
  have hW : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) U := analyticOnNhd_const
  have heq : ∀ s : ℂ, 1 < s.re →
      (χ.LFunction s * ψ.LFunction s) * M s = 1 := by
    intro s hs
    rw [hMseries s hs, normFiber_LSeries_eq_pair_inverse χ ψ weight hcoeff s]
    exact pair_inverse_euler_identity χ ψ s hs
  have hprod : χ.LFunction ρ * ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_analytic_identity σ hσ
      (fun s => χ.LFunction s * ψ.LFunction s) M (fun _ => (1 : ℂ))
      hL hM hW heq ρ hρ one_ne_zero
  exact mul_ne_zero_iff.mp hprod

theorem pair_zero_free_of_normFiber_continuation_principal_left
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff (1 : DirichletCharacter ℂ q) ψ n)
    (σ : ℝ) (hσ : σ < 1) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hMseries : ∀ s : ℂ, 1 < s.re → M s = LSeries (normFiberCoeff weight) s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLregular₁ : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunctionTrivChar₁ q) U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
  have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (ψ.differentiable_LFunction hψ).differentiableOn
  have hLregular : AnalyticOnNhd ℂ
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) U :=
    hLregular₁.mul hLψ
  have hW : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) U := analyticOnNhd_const
  have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s =
        (s - 1) *
          (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
            ψ.LFunction s) := by
    intro s _ hs
    simp [DirichletCharacter.LFunctionTrivChar₁,
      DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
    ring
  have heq : ∀ s : ℂ, 1 < s.re →
      (DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) * M s =
        (s - 1) * 1 := by
    intro s hs
    rw [hregular s (lt_trans hσ hs) (by
      intro h; subst s; norm_num at hs)]
    rw [hMseries s hs, normFiber_LSeries_eq_pair_inverse 1 ψ weight hcoeff s]
    calc
      (s - 1) * (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
          ψ.LFunction s) * LSeries (pairInverseCoeff 1 ψ) s =
        (s - 1) * (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
          ψ.LFunction s * LSeries (pairInverseCoeff 1 ψ) s) := by ring
      _ = (s - 1) * 1 := by rw [pair_inverse_euler_identity 1 ψ s hs]
  have hprod :
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ *
        ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_regularized_analytic_identity σ hσ
      (fun s => DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s *
        ψ.LFunction s)
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s)
      M (fun _ => (1 : ℂ)) hLregular hM hW hregular heq ρ hρ hρone
      one_ne_zero
  exact mul_ne_zero_iff.mp hprod

theorem pairInverseCoeff_comm
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    pairInverseCoeff χ ψ = pairInverseCoeff ψ χ := by
  simp only [pairInverseCoeff, LSeries.convolution, mul_comm]

theorem pair_zero_free_of_normFiber_continuation_principal_right
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff χ (1 : DirichletCharacter ℂ r) n)
    (σ : ℝ) (hσ : σ < 1) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hMseries : ∀ s : ℂ, 1 < s.re → M s = LSeries (normFiberCoeff weight) s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    χ.LFunction ρ ≠ 0 ∧
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ r) ρ ≠ 0 := by
  have hcoeff' : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff (1 : DirichletCharacter ℂ r) χ n := by
    intro n hn
    rw [hcoeff n hn, pairInverseCoeff_comm]
  have h := pair_zero_free_of_normFiber_continuation_principal_left
    (q := r) (r := q) χ hχ weight hcoeff' σ hσ M hM hMseries ρ hρ hρone
  exact ⟨h.2, h.1⟩

end ShortDraftHeckeBridge
private theorem pairing_algebra
    (g1 g2 gm G alpha eps t : ℂ)
    (halpha : alpha * star alpha = 1)
    (hg1 : g1 * star g1 = 1)
    (hprod : g1 * g2 = -alpha * G)
    (hpair : g1 * gm = eps) :
    (-star g1) * G * t = (star alpha * g2) * t ∧
    (-gm) * G * t = eps * (star alpha * g2) * t ∧
    (-g1) * star G * t⁻¹ = (alpha * star g2) * t⁻¹ ∧
    (-star gm) * star G * t⁻¹ = star eps * (alpha * star g2) * t⁻¹ := by
  have h2 : g2 = -(star g1) * alpha * G := by
    calc
      g2 = (g1 * star g1) * g2 := by rw [hg1]; ring
      _ = star g1 * (g1 * g2) := by ring
      _ = star g1 * (-alpha * G) := by rw [hprod]
      _ = _ := by ring
  have hA : star alpha * g2 = (-star g1) * G := by
    rw [h2]
    calc
      star alpha * (-(star g1) * alpha * G) =
          (alpha * star alpha) * ((-star g1) * G) := by ring
      _ = (-star g1) * G := by rw [halpha]; ring
  have hm : gm = eps * star g1 := by
    calc
      gm = (g1 * star g1) * gm := by rw [hg1]; ring
      _ = star g1 * (g1 * gm) := by ring
      _ = eps * star g1 := by rw [hpair]; ring
  have hB : (-gm) * G = eps * (star alpha * g2) := by
    rw [hm, hA]
    ring
  have hC : (-g1) * star G = alpha * star g2 := by
    have h := congrArg (fun z : ℂ => star z) hA
    simp only [star_mul, star_neg, star_star] at h
    calc
      (-g1) * star G = star G * (-g1) := by ring
      _ = star g2 * alpha := h.symm
      _ = alpha * star g2 := by ring
  have hD : (-star gm) * star G = star eps * (alpha * star g2) := by
    have h := congrArg (fun z : ℂ => star z) hB
    simpa only [star_mul, star_neg, star_star, mul_comm, mul_left_comm, mul_assoc] using h
  exact ⟨by rw [hA], by rw [hB], by rw [hC], by rw [hD]⟩

namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
open scoped ComplexConjugate

private theorem breveGamma1_mul_star_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * star (breveGamma1 P hgood p hP hp) = 1 := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℝ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hnormO := primary_generator_mul_conj_eq_card
    (Ideal.span {p}) hgood p rfl hprimary
  have hnormC := congrArg eisEmbedding hnormO
  rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
  have hs : (s : ℂ) ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hsreal : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℝ) := by
    exact Complex.ofReal_injective (by exact_mod_cast hs)
  have hcard : 0 < (Fintype.card (O ⧸ Ideal.span {p}) : ℝ) := by positivity
  have hsroot : s = Real.sqrt (Fintype.card (O ⧸ Ideal.span {p})) := by
    nlinarith [Real.sq_sqrt hcard.le, Real.sqrt_nonneg
      (Fintype.card (O ⧸ Ideal.span {p})), norm_nonneg (eisEmbedding p)]
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  have hnorm : ‖breveGamma1 (Ideal.span {p}) hgood p rfl hp‖ = 1 := by
    change ‖gaussSum χ ψ / (s : ℂ)‖ = 1
    rw [norm_div, ShortDraftGauss.norm_gaussSum_eq_sqrt_card χ ψ hχ1 hψ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (eisEmbedding p))]
    rw [← hsroot]
    exact div_self hs0
  rw [← starRingEnd_apply, Complex.mul_conj', hnorm]
  norm_num

theorem first_poisson_prime_sign_pairing
    (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) :
    let alpha : ℂ := eisEmbedding p / (‖eisEmbedding p‖ : ℂ)
    let g1 := breveGamma1 P hgood p hP hp
    let g2 := breveGamma2 P hgood p hP hp
    let gm := breveGammaMinus1 P hgood p hP hp
    let G := breveLocalG P hgood p hP hp
    let t := canonicalSextic P hgood (Ideal.Quotient.mk P h)
    let eps := canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O))
    (-star g1) * G * t = (star alpha * g2) * t ∧
    (-gm) * G * t = eps * (star alpha * g2) * t ∧
    (-g1) * star G * t⁻¹ = (alpha * star g2) * t⁻¹ ∧
    (-star gm) * star G * t⁻¹ = star eps * (alpha * star g2) * t⁻¹ := by
  have hz : eisEmbedding p ≠ 0 := eisEmbedding_ne_zero hp
  have hs : (‖eisEmbedding p‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hanorm : ‖eisEmbedding p / (‖eisEmbedding p‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (eisEmbedding p))]
    exact div_self (norm_ne_zero_iff.mpr hz)
  have ha : (eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) *
      star (eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', hanorm]
    norm_num
  have hg1 := breveGamma1_mul_star_one P hgood hchar p hP hp hprimary
  have hprod := breveGamma1_gamma2_eq_neg_alpha_G
    P hgood hchar p hP hp hprimary
  have hprod' :
      breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
        -(eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) *
          breveLocalG P hgood p hP hp := by
    simpa only [neg_div] using hprod
  have hpair := breveGamma1_gammaMinus1
    P hgood hchar p hP hp hprimary
  dsimp only
  exact pairing_algebra
    (breveGamma1 P hgood p hP hp)
    (breveGamma2 P hgood p hP hp)
    (breveGammaMinus1 P hgood p hP hp)
    (breveLocalG P hgood p hP hp)
    (eisEmbedding p / (‖eisEmbedding p‖ : ℂ))
    (canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O)))
    (canonicalSextic P hgood (Ideal.Quotient.mk P h))
    ha hg1 hprod' hpair

end ActualEisensteinCubic

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem direct_theta_jtwo_mask (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (a : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 2 * χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hchar : (χ⁻¹) ^ 2 * χ ^ 2 = 1 := by group
  rw [hchar]
  simp only [MulChar.one_apply_coe, one_mul]
  calc
    (∑ h : Fˣ, ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ψ (a * (y : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro h
      simp
    _ = _ := additive_unit_sum ψ hψ a

theorem direct_theta_jtwo_fourier_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) (hψ : ψ ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 2) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum (χ ^ 2) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card Fˣ : ℂ) else -1)) := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 2) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        (χ ^ 2) σ * gaussSum (χ ^ 2) (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (((χ⁻¹) ^ 2 * χ ^ 2) (h : F)) *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient (χ ^ 2) ψ hχ₂, map_mul]
    simp only [MulChar.mul_apply]
    have hpow : (χ ^ 2)⁻¹ = (χ⁻¹) ^ 2 := by group
    rw [hpow]
    ring
  rw [hsum, direct_theta_jtwo_mask χ ψ hψ (ε * x)]
  ring

theorem direct_theta_active_zero_inversion (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (a : F) :
    (∑ h : Fˣ, (χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum ((χ ^ 2)⁻¹) (ψ.mulShift a) := by
  classical
  calc
    (∑ h : Fˣ, (χ ^ 2) (h : F) * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ((χ ^ 2)⁻¹) (y : F) * ψ (a * (y : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro y
      simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
      rw [MulChar.inv_apply']
      simp
    _ = gaussSum ((χ ^ 2)⁻¹) (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]

theorem direct_theta_active_zero_fourier_row (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hχ₂ : χ ^ 2 ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (-(Fintype.card F : ℂ)⁻¹) *
      (∑ h : Fˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      -(χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  classical
  have hχ₂inv : (χ ^ 2)⁻¹ ≠ 1 := by
    intro h
    apply hχ₂
    calc χ ^ 2 = ((χ ^ 2)⁻¹)⁻¹ := by group
      _ = 1 := by rw [h]; simp
  have hsum :
      (∑ h : Fˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        (χ ^ 2) σ *
          (∑ h : Fˣ, (χ ^ 2) (h : F) *
            ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [map_mul]
    ring
  rw [hsum, direct_theta_active_zero_inversion χ ψ (ε * x)]
  rw [gaussSum_mulShift_any ((χ ^ 2)⁻¹) ψ hχ₂inv (ε * x)]
  simp only [inv_inv, map_mul]
  ring

theorem direct_theta_active_zero_full_row (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hχ₂ : χ ^ 2 ≠ 1) (hψ : ψ ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 0) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      -(χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ 0) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      -(∑ h : Fˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro h _
    rw [pow_zero, trivial_fourier_coefficient ψ hψ h,
      ite_eq_right (Units.ne_zero h)]
    ring
  rw [hsum]
  convert direct_theta_active_zero_fourier_row χ ψ hχ₂ σ ε x using 1 ; ring

end ShortDraftLocal

end

end OAI
end OAIOriginalModule0072

/-! Original module: OAI.NumberTheory.DirichletL.Arithmetic.NormFiberMellin
Source SHA256: e8a5265dfb958a162151ab06820b9651246a8593aa09d815383744c302c24bf6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0073


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
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar

namespace ShortDraftLocal

theorem no_quadratic_scalar {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ≠ χ ^ 3) (c : ℂ) (hc : c ≠ 0) :
    ¬ ∃ d : ℂ, ∀ x : F, c * χ x = d * (χ ^ 3) x := by
  rintro ⟨d, hd⟩
  have hcd : c = d := by
    have h := hd 1
    simpa using h
  apply hχ
  ext x
  have h := hd x
  rw [← hcd] at h
  exact mul_left_cancel₀ hc h

end ShortDraftLocal

open MulChar AddChar

namespace ActualEisensteinCubic

theorem canonical_A5_jtwo_direct (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 2) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (χ ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ 2) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Nat.card (O ⧸ P)ˣ : ℂ) else -1)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hχ₂ : (canonicalSextic P hgood) ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar
      (j := 2) (by decide) (by decide)
  dsimp
  simp only [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.direct_theta_jtwo_fourier_row
    (canonicalSextic P hgood) ψ hχ₂ hψ σ ε x

theorem canonical_A5_jzero_direct_active (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (-(Nat.card (O ⧸ P) : ℂ)⁻¹) *
      (∑ h : (O ⧸ P)ˣ, (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(χ ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hχ₂ : (canonicalSextic P hgood) ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar
      (j := 2) (by decide) (by decide)
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.direct_theta_active_zero_fourier_row
    (canonicalSextic P hgood) ψ hχ₂ σ ε x

theorem canonical_A5_jzero_direct_full (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(χ ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum ((χ ^ 2)⁻¹) ψ * (χ ^ 2) ε) * (χ ^ 2) x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hχ₂ : (canonicalSextic P hgood) ^ 2 ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar
      (j := 2) (by decide) (by decide)
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.direct_theta_active_zero_full_row
    (canonicalSextic P hgood) ψ hχ₂ hψ σ ε x

end ActualEisensteinCubic

namespace ShortDraftHeckeBridge

noncomputable def chiMinusThree : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

noncomputable def baseChangeWeight {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * χ (Ideal.absNorm I)

theorem baseChangeWeight_prime {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ P = -χ (Ideal.absNorm P) := by
  rw [baseChangeWeight, hP.irreducible.moebius_eq]
  norm_num

noncomputable def invCharAF {q : ℕ} (χ : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  (toArithmeticFunction (χ ·)).pmul (ArithmeticFunction.moebius : ArithmeticFunction ℂ)

theorem invCharAF_apply {q : ℕ} (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : n ≠ 0) :
    invCharAF χ n = χ n * (ArithmeticFunction.moebius n : ℂ) := by
  change ((toArithmeticFunction (χ ·)).pmul
    (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) n = _
  rw [ArithmeticFunction.pmul_apply]
  simp [toArithmeticFunction, hn]

private theorem invCharAF_mult {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (invCharAF χ).IsMultiplicative := by
  exact (χ.isMultiplicative_toArithmeticFunction).pmul
    (ArithmeticFunction.isMultiplicative_moebius.intCast)

noncomputable def pairAF {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  invCharAF χ * invCharAF ψ

theorem pairAF_mult {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) :
    (pairAF χ ψ).IsMultiplicative :=
  (invCharAF_mult χ).mul (invCharAF_mult ψ)

theorem pairAF_eq_pairInverseCoeff {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (n : ℕ) : pairAF χ ψ n = pairInverseCoeff χ ψ n := by
  rw [pairAF, ← ArithmeticFunction.coe_mul]
  apply congrFun
  exact (LSeries.convolution_congr
    (fun {k} hk => invCharAF_apply χ hk)
    (fun {k} hk => invCharAF_apply ψ hk))

theorem normFiber_eq_pair_of_prime_powers
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hb : (toArithmeticFunction (normFiberCoeff weight)).IsMultiplicative)
    (hlocal : ∀ p k : ℕ, p.Prime →
      (toArithmeticFunction (normFiberCoeff weight)) (p ^ k) =
        pairAF χ ψ (p ^ k))
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff weight n = pairInverseCoeff χ ψ n := by
  have heq : toArithmeticFunction (normFiberCoeff weight) = pairAF χ ψ :=
    (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
      _ hb _ (pairAF_mult χ ψ)).2 hlocal
  have h := congrFun (congrArg DFunLike.coe heq) n
  calc
    normFiberCoeff weight n = (toArithmeticFunction (normFiberCoeff weight)) n := by
      simp [toArithmeticFunction, hn]
    _ = pairAF χ ψ n := h
    _ = pairInverseCoeff χ ψ n := pairAF_eq_pairInverseCoeff χ ψ n

theorem pairAF_prime {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) {p : ℕ} (hp : p.Prime) :
    pairAF χ ψ p = -(χ p + ψ p) := by
  have h1χ : invCharAF χ 1 = 1 := (invCharAF_mult χ).map_one
  have h1ψ : invCharAF ψ 1 = 1 := (invCharAF_mult ψ).map_one
  have hpχ : invCharAF χ p = -χ p := by
    rw [invCharAF_apply χ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hpψ : invCharAF ψ p = -ψ p := by
    rw [invCharAF_apply ψ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [hp.divisors]
  have hnot : 1 ∉ ({p} : Finset ℕ) := by simpa using hp.ne_one.symm
  rw [Finset.sum_insert hnot, Finset.sum_singleton]
  simp [Nat.div_one, Nat.div_self hp.pos, h1χ, h1ψ, hpχ, hpψ]

theorem pairAF_prime_sq {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) {p : ℕ} (hp : p.Prime) :
    pairAF χ ψ (p ^ 2) = χ p * ψ p := by
  have h1χ : invCharAF χ 1 = 1 := (invCharAF_mult χ).map_one
  have h1ψ : invCharAF ψ 1 = 1 := (invCharAF_mult ψ).map_one
  have hpχ : invCharAF χ p = -χ p := by
    rw [invCharAF_apply χ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hpψ : invCharAF ψ p = -ψ p := by
    rw [invCharAF_apply ψ hp.ne_zero, ArithmeticFunction.moebius_apply_prime hp]
    simp
  have hp2χ : invCharAF χ (p ^ 2) = 0 := by
    rw [invCharAF_apply χ (pow_ne_zero 2 hp.ne_zero),
      ArithmeticFunction.moebius_apply_prime_pow hp (by decide)]
    simp
  have hp2ψ : invCharAF ψ (p ^ 2) = 0 := by
    rw [invCharAF_apply ψ (pow_ne_zero 2 hp.ne_zero),
      ArithmeticFunction.moebius_apply_prime_pow hp (by decide)]
    simp
  have hdiv : (p ^ 2).divisors = ({1, p, p ^ 2} : Finset ℕ) := by
    ext x
    rw [Nat.mem_divisors_prime_pow hp 2]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj, rfl⟩
      interval_cases j <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, by decide, by simp⟩
      · exact ⟨1, by decide, by simp⟩
      · exact ⟨2, by decide, by simp⟩
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [hdiv]
  have hpge : 2 ≤ p := hp.two_le
  have h1p2 : 1 ≠ p ^ 2 := by nlinarith
  have hpp2 : p ≠ p ^ 2 := by nlinarith
  have hnot1 : 1 ∉ ({p, p ^ 2} : Finset ℕ) := by
    simp [hp.ne_one.symm, h1p2]
  have hnotp : p ∉ ({p ^ 2} : Finset ℕ) := by
    simp [hpp2]
  rw [Finset.sum_insert hnot1, Finset.sum_insert hnotp, Finset.sum_singleton]
  have hdivp : p ^ 2 / p = p := by simp [pow_two, hp.pos]
  simp [Nat.div_one, hdivp, h1χ,  hpχ, hpψ, hp2χ, hp2ψ]

theorem chiMinusThree_two : chiMinusThree (2 : ℕ) = -1 := by
  have h3 : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have h21 : (2 : ZMod 3) ≠ 1 := by decide
  change ((quadraticChar (ZMod 3) (2 : ZMod 3) : ℤ) : ℂ) = -1
  rw [quadraticChar_eq_pow_of_char_ne_two h3 h2]
  simp [h21]

theorem chiMinusThree_ne_one : chiMinusThree ≠ 1 := by
  intro h
  have hh := congrArg (fun ξ : DirichletCharacter ℂ 3 => ξ (2 : ℕ)) h
  rw [chiMinusThree_two] at hh
  have hunit : IsUnit (2 : ZMod 3) := by decide
  change (-1 : ℂ) = (1 : DirichletCharacter ℂ 3) (2 : ZMod 3) at hh
  rw [MulChar.one_apply hunit] at hh
  norm_num at hh

theorem not_both_principal {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ¬ ((χ.changeLevel (Nat.dvd_mul_right q 3) = 1) ∧
      χ.changeLevel (Nat.dvd_mul_right q 3) *
        chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q) = 1) := by
  rintro ⟨hχ, hprod⟩
  rw [hχ, one_mul] at hprod
  have hη : chiMinusThree = 1 :=
    (DirichletCharacter.changeLevel_eq_one_iff (Nat.dvd_mul_left 3 q)).mp hprod
  exact chiMinusThree_ne_one hη

end ShortDraftHeckeBridge
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

noncomputable def normFiberExpSum (weight : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)

noncomputable def normFiberMellin (weight : Ideal O → ℂ) (s : ℂ) : ℂ :=
  mellin (fun D : ℝ => normFiberExpSum weight D⁻¹) (-s) / Complex.Gamma s

theorem pairInverseCoeff_zero
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) :
    pairInverseCoeff χ ψ 0 = 0 := by
  simp [pairInverseCoeff]

theorem pairInverseCoeff_LSeriesSummable
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (pairInverseCoeff χ ψ) s := by
  have hχ : LSeriesSummable
      (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s :=
    DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hψ : LSeriesSummable
      (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s :=
    DirichletCharacter.LSeriesSummable_mul ψ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  exact hχ.convolution hψ

private theorem mobius_char_coeff_norm_le_one
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
    (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
    mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]

theorem pairInverseCoeff_norm_le
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (n : ℕ) : ‖pairInverseCoeff χ ψ n‖ ≤ (n : ℝ) := by
  rw [pairInverseCoeff, LSeries.convolution_def]
  have hcard : (n.divisorsAntidiagonal.card : ℝ) ≤ n := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
    exact_mod_cast Nat.card_divisors_le_self n
  calc
    ‖∑ p ∈ n.divisorsAntidiagonal,
        (χ p.1 * (ArithmeticFunction.moebius p.1 : ℂ)) *
        (ψ p.2 * (ArithmeticFunction.moebius p.2 : ℂ))‖ ≤
      ∑ p ∈ n.divisorsAntidiagonal,
        ‖(χ p.1 * (ArithmeticFunction.moebius p.1 : ℂ)) *
        (ψ p.2 * (ArithmeticFunction.moebius p.2 : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      have hχ := mobius_char_coeff_norm_le_one χ p.1
      have hψ := mobius_char_coeff_norm_le_one ψ p.2
      nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
        (norm_nonneg (ψ p.2 * (ArithmeticFunction.moebius p.2 : ℂ))),
        mul_nonneg (sub_nonneg.mpr hψ)
          (norm_nonneg (χ p.1 * (ArithmeticFunction.moebius p.1 : ℂ)))]
    _ = (n.divisorsAntidiagonal.card : ℝ) := by simp
    _ ≤ n := hcard

theorem normFiberCoeff_norm_le
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (n : ℕ) : ‖normFiberCoeff weight n‖ ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0]
  · rw [hcoeff n hn]
    exact pairInverseCoeff_norm_le χ ψ n

theorem normFiberExpSum_summable
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)) := by
  have hexp : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) * t)) := by
    convert Real.summable_pow_mul_exp_neg_nat_mul 1 ht using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  apply hexp.of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right
    (normFiberCoeff_norm_le χ ψ weight hcoeff ha0 n) (Real.exp_pos _).le

theorem normFiberExpSum_continuousOn_pos
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0) :
    ContinuousOn (normFiberExpSum weight) (Set.Ioi (0 : ℝ)) := by
  intro t ht
  change 0 < t at ht
  let eps0 : ℝ := t / 2
  have heps0 : 0 < eps0 := by dsimp [eps0]; linarith
  have heps0t : eps0 < t := by dsimp [eps0]; linarith
  have hexp : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(n : ℝ) * eps0)) := by
    convert Real.summable_pow_mul_exp_neg_nat_mul 1 heps0 using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  have hcontTerm (n : ℕ) : ContinuousOn
      (fun u : ℝ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * u))
      (Set.Ici eps0) := by
    fun_prop
  have hbound (n : ℕ) (u : ℝ) (hu : u ∈ Set.Ici eps0) :
      ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * u)‖ ≤
        (n : ℝ) * Real.exp (-(n : ℝ) * eps0) := by
    have hnu : -(n : ℝ) * u ≤ -(n : ℝ) * eps0 := by
      have hu' : eps0 ≤ u := hu
      nlinarith [mul_le_mul_of_nonneg_left hu'
        (Nat.cast_nonneg (α := ℝ) n)]
    have hexpmon := Real.exp_le_exp.mpr hnu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖normFiberCoeff weight n‖ * Real.exp (-(n : ℝ) * u) ≤
          (n : ℝ) * Real.exp (-(n : ℝ) * u) :=
        mul_le_mul_of_nonneg_right
          (normFiberCoeff_norm_le χ ψ weight hcoeff ha0 n) (Real.exp_pos _).le
      _ ≤ (n : ℝ) * Real.exp (-(n : ℝ) * eps0) :=
        mul_le_mul_of_nonneg_left hexpmon (Nat.cast_nonneg (α := ℝ) n)
  have hcontHalf : ContinuousOn (normFiberExpSum weight) (Set.Ici eps0) := by
    change ContinuousOn
      (fun u : ℝ => ∑' n : ℕ,
        normFiberCoeff weight n * Real.exp (-(n : ℝ) * u)) (Set.Ici eps0)
    exact continuousOn_tsum hcontTerm hexp hbound
  exact (hcontHalf.continuousAt (Ici_mem_nhds heps0t)).continuousWithinAt

theorem normFiberExpSum_inv_locallyIntegrableOn_pos
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0) :
    LocallyIntegrableOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0) := by
  have hcont : ContinuousOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0) := by
    apply (normFiberExpSum_continuousOn_pos χ ψ weight hcoeff ha0).comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    exact inv_pos.mpr (show 0 < D from hD)
  exact hcont.locallyIntegrableOn measurableSet_Ioi

theorem normFiberExpSum_norm_le_exp
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖normFiberExpSum weight t‖ ≤
      (∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ) / 2)) *
        Real.exp (-t / 2) := by
  have hmajor : Summable (fun n : ℕ =>
      (n : ℝ) * Real.exp (-(n : ℝ) / 2)) := by
    convert Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1 / 2) using 1
    ext n
    simp only [pow_one]
    congr 1
    ring_nf
  have hbound (n : ℕ) :
      ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)‖ ≤
        ((n : ℝ) * Real.exp (-(n : ℝ) / 2)) * Real.exp (-t / 2) := by
    by_cases hn : n = 0
    · subst n
      simp [ha0]
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hdiff : -(n : ℝ) * t ≤ -(n : ℝ) / 2 - t / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr ht)]
    have hexp : Real.exp (-(n : ℝ) * t) ≤
        Real.exp (-(n : ℝ) / 2) * Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      convert hdiff using 1
      ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      ‖normFiberCoeff weight n‖ * Real.exp (-(n : ℝ) * t) ≤
          (n : ℝ) * Real.exp (-(n : ℝ) * t) :=
        mul_le_mul_of_nonneg_right
          (normFiberCoeff_norm_le χ ψ weight hcoeff ha0 n) (Real.exp_pos _).le
      _ ≤ ((n : ℝ) * Real.exp (-(n : ℝ) / 2)) * Real.exp (-t / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hexp
          (Nat.cast_nonneg (α := ℝ) n)]
  have hnormsum : Summable (fun n : ℕ =>
      ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)‖) :=
    (hmajor.mul_right (Real.exp (-t / 2))).of_nonneg_of_le
      (fun _ => norm_nonneg _) hbound
  calc
    ‖normFiberExpSum weight t‖ ≤
      ∑' n : ℕ, ‖normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ,
        ((n : ℝ) * Real.exp (-(n : ℝ) / 2)) * Real.exp (-t / 2) :=
      hnormsum.tsum_le_tsum hbound (hmajor.mul_right _)
    _ = (∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ) / 2)) *
        Real.exp (-t / 2) := by rw [tsum_mul_right]

theorem normFiberExpSum_flat_at_zero
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (b : ℝ) :
    (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun D : ℝ => D ^ b) := by
  let C : ℝ := ∑' n : ℕ, (n : ℝ) * Real.exp (-(n : ℝ) / 2)
  have hExp : (fun t : ℝ => normFiberExpSum weight t) =O[atTop]
      (fun t : ℝ => Real.exp (-t / 2)) := by
    apply isBigO_iff_isBigOWith.mpr
    refine ⟨C, IsBigOWith.of_bound ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      normFiberExpSum_norm_le_exp χ ψ weight hcoeff ha0 t ht
  have hpow : (fun t : ℝ => normFiberExpSum weight t) =O[atTop]
      (fun t : ℝ => t ^ (-b)) := by
    apply hExp.trans
    have heq : (fun t : ℝ => Real.exp (-t / 2)) =
        (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) := by
      funext t
      congr 1
      ring
    rw [heq]
    exact
      (isLittleO_exp_neg_mul_rpow_atTop
        (by norm_num : (0 : ℝ) < 1 / 2) (-b)).isBigO
  have hcomp := hpow.comp_tendsto tendsto_inv_nhdsGT_zero
  refine hcomp.congr (fun _ => rfl) ?_
  intro D
  dsimp
  rw [← Real.rpow_neg_eq_inv_rpow]
  simp

theorem normFiberExpSum_mellin
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (hexp : ∀ t : ℝ, 0 < t → Summable
      (fun n : ℕ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)))
    (s : ℂ) (hs : 1 < s.re) :
    mellin (fun D : ℝ => normFiberExpSum weight D⁻¹) (-s) =
      Complex.Gamma s * LSeries (normFiberCoeff weight) s := by
  apply ShortDraftMellin.mellin_of_exponential_smoothing
    (normFiberCoeff weight) (normFiberExpSum weight) s hs ha0
  · intro t ht
    exact (hexp t ht).hasSum
  · exact (LSeriesSummable_congr s (fun {n} hn => hcoeff n hn)).mpr
      (pairInverseCoeff_LSeriesSummable χ ψ s hs)

theorem normFiberMellin_analytic
    (weight : Ideal O → ℂ) (σ : ℝ) (hσpos : 0 < σ)
    (hlocal : LocallyIntegrableOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0))
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (hflat : ∀ b : ℝ,
      (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[𝓝[>] (0 : ℝ)]
        (fun D : ℝ => D ^ b)) :
    AnalyticOnNhd ℂ (normFiberMellin weight) {s : ℂ | σ < s.re} := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => normFiberExpSum weight D⁻¹) (-s)) U :=
    ShortDraftMellin.inverse_mellin_analytic_of_flat _ σ hlocal htop hflat
  have hGamma : AnalyticOnNhd ℂ Complex.Gamma U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hopen).2
    intro s hs
    apply (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    have hreal : s.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hspos : 0 < s.re := lt_trans hσpos hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hGamma0 : ∀ s ∈ U, Complex.Gamma s ≠ 0 := by
    intro s hs
    exact Complex.Gamma_ne_zero_of_re_pos (lt_trans hσpos hs)
  exact hM.div hGamma hGamma0

theorem normFiberMellin_eq_LSeries
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (hexp : ∀ t : ℝ, 0 < t → Summable
      (fun n : ℕ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)))
    (s : ℂ) (hs : 1 < s.re) :
    normFiberMellin weight s = LSeries (normFiberCoeff weight) s := by
  rw [normFiberMellin, normFiberExpSum_mellin χ ψ weight hcoeff ha0 hexp s hs]
  exact mul_div_cancel_left₀ _
    (Complex.Gamma_ne_zero_of_re_pos (lt_trans zero_lt_one hs))

theorem pair_zero_free_of_normFiber_exp_power_bound
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (hexp : ∀ t : ℝ, 0 < t → Summable
      (fun n : ℕ => normFiberCoeff weight n * Real.exp (-(n : ℝ) * t)))
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0))
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (hflat : ∀ b : ℝ,
      (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[𝓝[>] (0 : ℝ)]
        (fun D : ℝ => D ^ b))
    (ρ : ℂ) (hρ : σ < ρ.re) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  exact pair_zero_free_of_normFiber_continuation χ ψ hχ hψ weight hcoeff
    σ hσ (normFiberMellin weight)
    (normFiberMellin_analytic weight σ hσpos hlocal htop hflat)
    (fun s hs => normFiberMellin_eq_LSeries χ ψ weight hcoeff ha0 hexp s hs)
    ρ hρ

theorem normFiberMellin_analytic_of_coeff
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ : ℝ) (hσpos : 0 < σ)
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ)) :
    AnalyticOnNhd ℂ (normFiberMellin weight) {s : ℂ | σ < s.re} :=
  normFiberMellin_analytic weight σ hσpos
    (normFiberExpSum_inv_locallyIntegrableOn_pos χ ψ weight hcoeff ha0)
    htop (normFiberExpSum_flat_at_zero χ ψ weight hcoeff ha0)

theorem normFiberMellin_eq_LSeries_of_coeff
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (s : ℂ) (hs : 1 < s.re) :
    normFiberMellin weight s = LSeries (normFiberCoeff weight) s :=
  normFiberMellin_eq_LSeries χ ψ weight hcoeff ha0
    (normFiberExpSum_summable χ ψ weight hcoeff ha0) s hs

theorem pair_zero_free_of_normFiber_exp_power_bound_only
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  exact pair_zero_free_of_normFiber_continuation χ ψ hχ hψ weight hcoeff
    σ hσ (normFiberMellin weight)
    (normFiberMellin_analytic_of_coeff χ ψ weight hcoeff ha0 σ hσpos htop)
    (fun s hs => normFiberMellin_eq_LSeries_of_coeff χ ψ weight hcoeff ha0 s hs)
    ρ hρ

theorem pair_zero_free_of_normFiber_exp_power_bound_principal_left
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff (1 : DirichletCharacter ℂ q) ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  exact pair_zero_free_of_normFiber_continuation_principal_left ψ hψ
    weight hcoeff σ hσ (normFiberMellin weight)
    (normFiberMellin_analytic_of_coeff 1 ψ weight hcoeff ha0 σ hσpos htop)
    (fun s hs => normFiberMellin_eq_LSeries_of_coeff 1 ψ weight hcoeff ha0 s hs)
    ρ hρ hρone

theorem pair_zero_free_of_normFiber_exp_power_bound_principal_right
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      normFiberCoeff weight n =
        pairInverseCoeff χ (1 : DirichletCharacter ℂ r) n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    χ.LFunction ρ ≠ 0 ∧
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ r) ρ ≠ 0 := by
  exact pair_zero_free_of_normFiber_continuation_principal_right χ hχ
    weight hcoeff σ hσ (normFiberMellin weight)
    (normFiberMellin_analytic_of_coeff χ 1 weight hcoeff ha0 σ hσpos htop)
    (fun s hs => normFiberMellin_eq_LSeries_of_coeff χ 1 weight hcoeff ha0 s hs)
    ρ hρ hρone

end ShortDraftHeckeBridge

end

end OAI
end OAIOriginalModule0073

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.NormFiberCharacters
Source SHA256: 65bd032797c30d9d9ab5c7ee4d98eb8ee552e4333516e1f771a390faf6be765c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0074


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
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

theorem normFiberCoeff_baseChangeWeight_zero {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 0 = 0 := by
  classical
  unfold normFiberCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 0 := by
    simpa using hI
  have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
  subst I
  rw [baseChangeWeight]
  have hz : UniqueFactorizationMonoid.moebius (⊥ : Ideal O) = 0 := by
    simpa only [Ideal.zero_eq_bot] using
      (UniqueFactorizationMonoid.moebius_zero (α := Ideal O))
  rw [hz]
  simp

noncomputable def baseChangeChar {q : ℕ} (χ : DirichletCharacter ℂ q) :
    DirichletCharacter ℂ (q * 3) :=
  χ.changeLevel (Nat.dvd_mul_right q 3) *
    chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q)

theorem baseChangeChar_ne_one_of_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ = 1) :
    baseChangeChar χ ≠ 1 := by
  intro h
  apply not_both_principal χ
  constructor
  · simp [hχ]
  · exact h

end ShortDraftHeckeBridge
namespace ActualEisensteinCubic

open MulChar AddChar

theorem canonical_A5_jone_no_quadratic_model (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (σ : (O ⧸ P)ˣ) (ε : O ⧸ P) (hε : ε ≠ 0) :
    let χ := canonicalSextic P hgood
    ¬ ∃ d : ℂ, ∀ x : O ⧸ P,
      (Nat.card (O ⧸ P) : ℂ)⁻¹ *
        (∑ h : (O ⧸ P)ˣ,
          (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
          (χ ^ 2) (σ * h) *
          ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
        d * (χ ^ 3) x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ P) ℂ := canonicalSextic P hgood
  let S : ℂ := (Nat.card (O ⧸ P) : ℂ)⁻¹ *
    gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε
  let c : ℂ := (χ ^ 2) σ * S
  have hχ : χ ≠ χ ^ 3 := canonical_A5_jone_direct_not_quadratic P hgood hchar
  have hS : S ≠ 0 := by
    simpa only [S, χ] using
      canonical_A5_jone_direct_scalar_ne_zero P hgood hchar ψ hψ ε hε
  have hσ : (χ ^ 2) (σ : O ⧸ P) ≠ 0 :=
    (χ ^ 2).apply_ne_zero_iff.mpr σ.isUnit
  have hc : c ≠ 0 := mul_ne_zero hσ hS
  dsimp
  intro hmodel
  apply ShortDraftLocal.no_quadratic_scalar χ hχ c hc
  obtain ⟨d, hd⟩ := hmodel
  refine ⟨d, ?_⟩
  intro x
  have hrow := canonical_A5_jone_direct P hgood hchar ψ σ ε x
  have hx := hd x
  dsimp only at hrow hx
  calc
    c * χ x =
      (Nat.card (O ⧸ P) : ℂ)⁻¹ *
        (∑ h : (O ⧸ P)ˣ,
          (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
          (χ ^ 2) (σ * h) *
          ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
            rw [hrow]
    _ = d * (χ ^ 3) x := hx

end ActualEisensteinCubic

namespace ShortDraftHeckeBridge

theorem ideals_isRelPrime_of_norms_coprime (I J : Ideal O)
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    IsRelPrime I J := by
  have hcast : IsCoprime ((Ideal.absNorm I : ℕ) : O)
      ((Ideal.absNorm J : ℕ) : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime h).map (Int.castRingHom O)
  obtain ⟨a, b, hab⟩ := hcast
  apply IsCoprime.isRelPrime
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨a * (Ideal.absNorm I : O),
    I.mul_mem_left a (Ideal.absNorm_mem I),
    b * (Ideal.absNorm J : O),
    J.mul_mem_left b (Ideal.absNorm_mem J), hab⟩

theorem baseChangeWeight_mul_of_coprime_norms {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I J : Ideal O)
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    baseChangeWeight χ (I * J) =
      baseChangeWeight χ I * baseChangeWeight χ J := by
  have hrel := ideals_isRelPrime_of_norms_coprime I J h
  simp only [baseChangeWeight, map_mul, hrel.moebius_mul, Int.cast_mul, Nat.cast_mul]
  ring

theorem baseChangeChar_apply_of_coprime {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ)
    (h : n.Coprime (q * 3)) :
    baseChangeChar χ n = χ n * chiMinusThree n := by
  have hc : IsCoprime (n : ℤ) (q * 3 : ℕ) := by
    simpa [Int.isCoprime_iff_nat_coprime, Int.natAbs_mul] using h
  rw [baseChangeChar, MulChar.mul_apply]
  have hχ : χ.changeLevel (Nat.dvd_mul_right q 3) n = χ n := by
    simpa using (DirichletCharacter.changeLevel_eq_cast_of_dvd' χ
      (Nat.dvd_mul_right q 3) hc)
  have hη : chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q) n =
      chiMinusThree n := by
    simpa using (DirichletCharacter.changeLevel_eq_cast_of_dvd' chiMinusThree
      (Nat.dvd_mul_left 3 q) hc)
  rw [hχ, hη]

theorem chiMinusThree_three : chiMinusThree (3 : ℕ) = 0 := by
  simpa using (DirichletCharacter.apply_eq_zero_iff chiMinusThree 3).mpr
    (by simp [Int.isCoprime_iff_nat_coprime])

theorem baseChangeChar_three {q : ℕ} (χ : DirichletCharacter ℂ q) :
    baseChangeChar χ (3 : ℕ) = 0 := by
  simpa using (DirichletCharacter.apply_eq_zero_iff (baseChangeChar χ) 3).mpr
    (by
      intro hc
      have hn : Nat.Coprime 3 (q * 3) := by
        simpa [Int.isCoprime_iff_nat_coprime, Int.natAbs_mul] using hc
      have hself : Nat.Coprime 3 3 := hn.of_dvd_right (Nat.dvd_mul_left 3 q)
      norm_num at hself)

private abbrev K := CyclotomicField 3 ℚ
private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K

private theorem orderOf_mod3_eq_one {p : ℕ} (h : p % 3 = 1) :
    orderOf (p : ZMod 3) = 1 := by
  have hc : (p : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' p 1 3).2 (by simpa using h)
  simp [hc]

private theorem orderOf_mod3_eq_two {p : ℕ} (h : p % 3 = 2) :
    orderOf (p : ZMod 3) = 2 := by
  have hc : (p : ZMod 3) = 2 :=
    (ZMod.natCast_eq_natCast_iff' p 2 3).2 (by simpa using h)
  rw [hc]
  have hdvd : orderOf (2 : ZMod 3) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 3) ^ 2 = 1)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).1 hdvd with h1 | h2
  · have h21 : (2 : ZMod 3) = 1 := orderOf_eq_one_iff.mp h1
    exact False.elim ((by decide : (2 : ZMod 3) ≠ 1) h21)
  · exact h2

private theorem degree_two : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 K]
  decide

private theorem gal_card_two : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  exact degree_two

private theorem not_dvd_three {p : ℕ} (hp : p.Prime) (hneq : p ≠ 3) : ¬ p ∣ 3 := by
  intro hd
  have h := (Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd
  rcases h with h1 | h3
  · exact hp.ne_one h1
  · exact hneq h3

theorem split_count_of_mod_one {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_one hmod, gal_card_two] at hmain
  omega

theorem inert_count_of_mod_two {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_two hmod, gal_card_two] at hmain
  omega

theorem ramified_count :
    ((Ideal.span {(3 : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 3 K

theorem absNorm_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_one hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf, pow_one]

theorem absNorm_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 2 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_two hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf]

theorem absNorm_ramified
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(3 : ℤ)})] :
    Ideal.absNorm P = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hfin : (Ideal.span {(3 : ℤ)}).inertiaDegIn O = 1 := by
    simpa using IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime 3 K
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(3 : ℤ)}) P Gal(K/ℚ)]
    exact hfin
  rw [← Ideal.pow_inertiaDeg 3 P, hf, pow_one]

theorem norm_prime_implies_over {p : ℕ} (hp : p.Prime) (I : Ideal O)
    (hI : Ideal.absNorm I = p) :
    I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  have hprime : I.IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by
      rw [hI]
      exact (Nat.irreducible_iff_nat_prime p).2 hp)
  have hover : I.LiesOver (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    rw [Ideal.under_def, algebraMap_int_eq]
    simpa [hI] using Ideal.span_singleton_absNorm (I := I) (hI ▸ hp)
  exact ⟨hprime, hover⟩

theorem norm_p_fiber_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    {I : Ideal O | Ideal.absNorm I = p} =
      (Ideal.span {(p : ℤ)}).primesOver O := by
  ext I
  constructor
  · exact norm_prime_implies_over hp I
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := hI.2
    exact absNorm_split hp hmod I

theorem norm_p_fiber_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    {I : Ideal O | Ideal.absNorm I = p} = ∅ := by
  ext I
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hI
  have hOver := norm_prime_implies_over hp I hI
  let : I.IsPrime := hOver.1
  let : I.LiesOver (Ideal.span {(p : ℤ)}) := hOver.2
  have hNorm := absNorm_inert hp hmod I
  have hpge := hp.two_le
  nlinarith

theorem norm_three_fiber :
    {I : Ideal O | Ideal.absNorm I = 3} =
      (Ideal.span {(3 : ℤ)}).primesOver O := by
  ext I
  constructor
  · exact norm_prime_implies_over (by decide) I
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(3 : ℤ)}) := hI.2
    exact absNorm_ramified I

theorem norm_p_sq_fiber_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    {I : Ideal O | Ideal.absNorm I = p ^ 2} =
      (Ideal.span {(p : ℤ)}).primesOver O := by
  ext I
  constructor
  · intro hI
    have hdiv : p ∣ Ideal.absNorm I := by
      rw [hI]
      exact dvd_pow_self p (by decide)
    obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hdiv
    have : P.IsPrime := hPmax.isPrime
    have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
    have hPN : Ideal.absNorm P = p ^ 2 := absNorm_inert hp hmod P
    obtain ⟨J, hIJ⟩ := hPdiv
    have hJN : Ideal.absNorm J = 1 := by
      have heq := congrArg Ideal.absNorm hIJ
      simp only [map_mul] at heq
      rw [hI, hPN] at heq
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith
    have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJN
    subst J
    simp only [Ideal.mul_top] at hIJ
    subst I
    exact ⟨inferInstance, inferInstance⟩
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := hI.2
    exact absNorm_inert hp hmod I

theorem norm_p_sq_split_factors {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (I : Ideal O) (hI : Ideal.absNorm I = p ^ 2) :
    ∃ P Q : Ideal O,
      P ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
      Q ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
      I = P * Q := by
  have hdiv : p ∣ Ideal.absNorm I := by
    rw [hI]
    exact dvd_pow_self p (by decide)
  obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hdiv
  have : P.IsPrime := hPmax.isPrime
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
  have hPN : Ideal.absNorm P = p := absNorm_split hp hmod P
  obtain ⟨Q, hIQ⟩ := hPdiv
  have hQN : Ideal.absNorm Q = p := by
    have heq := congrArg Ideal.absNorm hIQ
    simp only [map_mul] at heq
    rw [hI, hPN] at heq
    have hppos := hp.pos
    nlinarith
  exact ⟨P, Q, ⟨inferInstance, inferInstance⟩,
    norm_prime_implies_over hp Q hQN, hIQ⟩

theorem norm_p_sq_fiber_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    {I : Ideal O | Ideal.absNorm I = p ^ 2} =
      {I : Ideal O | ∃ P Q : Ideal O,
        P ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
        Q ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
        I = P * Q} := by
  ext I
  constructor
  · exact norm_p_sq_split_factors hp hmod I
  · rintro ⟨P, Q, hP, hQ, rfl⟩
    have : P.IsPrime := hP.1
    have : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
    have : Q.IsPrime := hQ.1
    have : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQ.2
    change Ideal.absNorm (P * Q) = p ^ 2
    rw [map_mul, absNorm_split hp hmod P, absNorm_split hp hmod Q, pow_two]

theorem norm_nine_fiber_ramified :
    {I : Ideal O | Ideal.absNorm I = 9} =
      {I : Ideal O | ∃ P : Ideal O,
        P ∈ (Ideal.span {(3 : ℤ)}).primesOver O ∧ I = P ^ 2} := by
  ext I
  constructor
  · intro hI
    have hdiv : 3 ∣ Ideal.absNorm I := by
      rw [hI]
      decide
    obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' (by decide : Nat.Prime 3) I hdiv
    have : P.IsPrime := hPmax.isPrime
    have : P.LiesOver (Ideal.span {(3 : ℤ)}) := ⟨hPunder.symm⟩
    have hPN : Ideal.absNorm P = 3 := absNorm_ramified P
    obtain ⟨Q, hIQ⟩ := hPdiv
    have hQN : Ideal.absNorm Q = 3 := by
      have heq := congrArg Ideal.absNorm hIQ
      simp only [map_mul] at heq
      rw [hI, hPN] at heq
      omega
    have hQover := norm_prime_implies_over (by decide : Nat.Prime 3) Q hQN
    have hPover : P ∈ (Ideal.span {(3 : ℤ)}).primesOver O :=
      ⟨inferInstance, inferInstance⟩
    have hfinite : ((Ideal.span {(3 : ℤ)}).primesOver O).Finite := by
      rw [← norm_three_fiber]
      exact Ideal.finite_setOfPred_absNorm_eq 3
    have hsub : ∀ {A B : Ideal O},
        A ∈ (Ideal.span {(3 : ℤ)}).primesOver O →
        B ∈ (Ideal.span {(3 : ℤ)}).primesOver O → A = B :=
      (Set.ncard_le_one_iff hfinite).mp (by rw [ramified_count])
    have hPQ : P = Q := hsub hPover hQover
    refine ⟨P, hPover, ?_⟩
    rw [hIQ, ← hPQ, pow_two]
  · rintro ⟨P, hP, rfl⟩
    have : P.IsPrime := hP.1
    have : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
    change Ideal.absNorm (P ^ 2) = 9
    rw [map_pow, absNorm_ramified P]
    norm_num

theorem dirichletTarget_of_ideal_base_change
    (hcoeff : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (n : ℕ), n ≠ 0 →
        normFiberCoeff (baseChangeWeight χ) n =
          pairInverseCoeff χ (baseChangeChar χ) n)
    (hbound : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        ∃ σ : ℝ, 0 < σ ∧ σ < ρ.re ∧
          (fun D : ℝ => normFiberExpSum (baseChangeWeight χ) D⁻¹) =O[atTop]
            (fun D : ℝ => D ^ σ)) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · obtain ⟨σ, hσpos, hσρ, htop⟩ := hbound q χ ρ h23 hρ
    have hσone : σ < 1 := lt_trans hσρ hρ
    have hρone : ρ ≠ 1 := by
      intro hh
      subst ρ
      norm_num at hρ
    have hc := hcoeff q χ
    have hz := normFiberCoeff_baseChangeWeight_zero χ
    by_cases hχ : χ = 1
    · have hψ : baseChangeChar χ ≠ 1 :=
        baseChangeChar_ne_one_of_one χ hχ
      have hc' : ∀ n : ℕ, n ≠ 0 →
          normFiberCoeff (baseChangeWeight χ) n =
            pairInverseCoeff (1 : DirichletCharacter ℂ q)
              (baseChangeChar χ) n := by
        intro n hn
        simpa only [hχ] using hc n hn
      have hpair := pair_zero_free_of_normFiber_exp_power_bound_principal_left
        (q := q) (baseChangeChar χ) hψ (baseChangeWeight χ)
        hc' hz σ hσpos hσone htop ρ hσρ hρone
      simpa only [hχ] using hpair.1
    · by_cases hψ : baseChangeChar χ = 1
      · have hc' : ∀ n : ℕ, n ≠ 0 →
            normFiberCoeff (baseChangeWeight χ) n =
              pairInverseCoeff χ (1 : DirichletCharacter ℂ (q * 3)) n := by
          intro n hn
          simpa only [hψ] using hc n hn
        exact (pair_zero_free_of_normFiber_exp_power_bound_principal_right
          χ hχ (baseChangeWeight χ) hc' hz σ hσpos hσone htop ρ hσρ hρone).1
      · exact (pair_zero_free_of_normFiber_exp_power_bound_only
          χ (baseChangeChar χ) hχ hψ (baseChangeWeight χ)
          (fun n hn => hc n hn) hz σ hσpos hσone htop ρ hσρ).1
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal

theorem local_inert_p {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    normFiberCoeff (baseChangeWeight χ) p = 0 := by
  have hf := norm_p_fiber_inert hp hmod
  unfold normFiberCoeff
  simp [hf]

theorem local_split_p {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    normFiberCoeff (baseChangeWeight χ) p = -(2 : ℂ) * χ p := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) p
  have hcard : hf.toFinset.card = 2 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = p} hf]
    rw [norm_p_fiber_split hp hmod]
    exact split_count_of_mod_one hp hmod
  have hsum : normFiberCoeff (baseChangeWeight χ) p =
      ∑ I ∈ hf.toFinset, -χ p := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hnorm : Ideal.absNorm I = p := hf.mem_toFinset.mp hI
    have hprime : Prime I :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Ideal.irreducible_of_irreducible_absNorm (by
          rw [hnorm]
          exact (Nat.irreducible_iff_nat_prime p).2 hp))
    rw [baseChangeWeight_prime χ I hprime, hnorm]
  rw [hsum]
  simp [hcard]

theorem local_ramified_three {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 3 = -χ 3 := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) 3
  have hcard : hf.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = 3} hf]
    rw [norm_three_fiber]
    exact ramified_count
  have hsum : normFiberCoeff (baseChangeWeight χ) 3 =
      ∑ I ∈ hf.toFinset, -χ 3 := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hnorm : Ideal.absNorm I = 3 := hf.mem_toFinset.mp hI
    have hprime : Prime I :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Ideal.irreducible_of_irreducible_absNorm (by
          rw [hnorm]
          exact (Nat.irreducible_iff_nat_prime 3).2 (by decide)))
    simpa only [hnorm, Nat.cast_ofNat] using baseChangeWeight_prime χ I hprime
  rw [hsum]
  simp [hcard]

theorem local_inert_p_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) = -χ (p ^ 2) := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) (p ^ 2)
  have hcard : hf.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = p ^ 2} hf]
    rw [norm_p_sq_fiber_inert hp hmod]
    exact inert_count_of_mod_two hp hmod
  have hsum : normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
      ∑ I ∈ hf.toFinset, -χ (p ^ 2) := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hover : I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
      rw [← norm_p_sq_fiber_inert hp hmod]
      exact hf.mem_toFinset.mp hI
    have hnorm : Ideal.absNorm I = p ^ 2 := hf.mem_toFinset.mp hI
    let : I.IsPrime := hover.1
    have hprime : Prime I := Ideal.prime_of_isPrime (by
      intro hbot
      have : Ideal.absNorm I = 0 := by rw [hbot]; simp
      rw [hnorm] at this
      exact (pow_ne_zero 2 hp.ne_zero) this) inferInstance
    simpa only [hnorm, Nat.cast_pow] using baseChangeWeight_prime χ I hprime
  rw [hsum]
  simp [hcard]

theorem local_ramified_nine {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 9 = 0 := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) 9
  unfold normFiberCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 9 := hf.mem_toFinset.mp hI
  have hfactor : I ∈ {I : Ideal O | ∃ P : Ideal O,
      P ∈ (Ideal.span {(3 : ℤ)}).primesOver O ∧ I = P ^ 2} := by
    rw [← norm_nine_fiber_ramified]
    exact hnorm
  obtain ⟨P, hP, rfl⟩ := hfactor
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
  have hPN : Ideal.absNorm P = 3 := absNorm_ramified P
  have hnotunit : ¬ IsUnit P := by
    intro hunit
    have htop : P = ⊤ := Ideal.isUnit_iff.mp hunit
    rw [htop, Ideal.absNorm_top] at hPN
    norm_num at hPN
  have hnot : ¬ Squarefree (P ^ 2) := by
    intro hsq
    apply hnotunit
    exact hsq P (by rw [pow_two])
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hnot]
  simp

private theorem baseChangeWeight_prime_sq_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ (P ^ 2) = 0 := by
  have hnot : ¬ Squarefree (P ^ 2) := by
    intro hsq
    have hunit : IsUnit P := hsq P (by rw [pow_two])
    exact hP.irreducible.not_isUnit hunit
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hnot]
  simp

theorem local_split_p_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) = χ (p ^ 2) := by
  classical
  let s : Set (Ideal O) := (Ideal.span {(p : ℤ)}).primesOver O
  obtain ⟨P, Q, hPQ, hset⟩ := Set.ncard_eq_two.mp (split_count_of_mod_one hp hmod)
  have hPover : P ∈ s := by
    change P ∈ (Ideal.span {(p : ℤ)}).primesOver O
    rw [hset]
    simp
  have hQover : Q ∈ s := by
    change Q ∈ (Ideal.span {(p : ℤ)}).primesOver O
    rw [hset]
    simp
  let : P.IsPrime := hPover.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPover.2
  let : Q.IsPrime := hQover.1
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQover.2
  have hPN : Ideal.absNorm P = p := absNorm_split hp hmod P
  have hQN : Ideal.absNorm Q = p := absNorm_split hp hmod Q
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hPN
    exact hp.ne_zero hPN.symm
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hQN
    exact hp.ne_zero hQN.symm
  have hPprime : Prime P := Ideal.prime_of_isPrime hPne inferInstance
  have hQprime : Prime Q := Ideal.prime_of_isPrime hQne inferInstance
  have : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hPne
  have : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQne
  have hrel : IsRelPrime P Q := (Ideal.isCoprime_of_isMaximal hPQ).isRelPrime
  have hmu : UniqueFactorizationMonoid.moebius (P * Q) = 1 := by
    rw [hrel.moebius_mul, hPprime.irreducible.moebius_eq,
      hQprime.irreducible.moebius_eq]
    norm_num
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) (p ^ 2)
  have hmem : P * Q ∈ hf.toFinset := by
    rw [hf.mem_toFinset]
    change Ideal.absNorm (P * Q) = p ^ 2
    rw [map_mul, hPN, hQN, pow_two]
  calc
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
        ∑ I ∈ hf.toFinset, baseChangeWeight χ I := by rfl
    _ = baseChangeWeight χ (P * Q) := by
      apply Finset.sum_eq_single (P * Q)
      · intro I hImem hneq
        have hnorm : Ideal.absNorm I = p ^ 2 := hf.mem_toFinset.mp hImem
        obtain ⟨A, B, hA, hB, rfl⟩ := norm_p_sq_split_factors hp hmod I hnorm
        rw [hset] at hA hB
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
        rcases hA with hAP | hAQ <;> rcases hB with hBP | hBQ
        · rw [hAP, hBP]
          simpa only [pow_two] using baseChangeWeight_prime_sq_zero χ P hPprime
        · exact False.elim (hneq (by rw [hAP, hBQ]))
        · exact False.elim (hneq (by rw [hAQ, hBP, mul_comm]))
        · rw [hAQ, hBQ]
          simpa only [pow_two] using baseChangeWeight_prime_sq_zero χ Q hQprime
      · intro hnot
        exact False.elim (hnot hmem)
    _ = χ (p ^ 2) := by
      rw [baseChangeWeight, hmu]
      have hnorm : Ideal.absNorm (P * Q) = p ^ 2 := by
        rw [map_mul, hPN, hQN, pow_two]
      simp [hnorm, Nat.cast_pow]

theorem local_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 1 = 1 := by
  classical
  have hfinset : (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {⊤} := by
    ext I
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact Ideal.absNorm_eq_one_iff
  unfold normFiberCoeff
  rw [hfinset]
  simp only [Finset.sum_singleton]
  change baseChangeWeight χ ⊤ = 1
  have hunit : IsUnit (⊤ : Ideal O) := Ideal.isUnit_iff.mpr rfl
  have hmu : UniqueFactorizationMonoid.moebius (⊤ : Ideal O) = 1 := hunit.moebius_eq
  change (UniqueFactorizationMonoid.moebius (⊤ : Ideal O) : ℂ) *
    χ (Ideal.absNorm (⊤ : Ideal O)) = 1
  rw [hmu, Ideal.absNorm_top]
  simp

end ShortDraftHeckeBridge

end

end OAI
end OAIOriginalModule0074

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.LocalEulerIdentities
Source SHA256: 2ac43e029b570b5804aa1b1f5a9142b2736678c84fed57905365d898029014b0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0075


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
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

theorem chiMinusThree_mod_one (n : ℕ) (h : n % 3 = 1) :
    chiMinusThree n = 1 := by
  have hc : (n : ZMod 3) = 1 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 1 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = 1
  rw [hc]
  simp

theorem chiMinusThree_mod_two (n : ℕ) (h : n % 3 = 2) :
    chiMinusThree n = -1 := by
  have hc : (n : ZMod 3) = 2 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 2 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = -1
  rw [hc]
  change chiMinusThree (2 : ℕ) = -1
  exact chiMinusThree_two

theorem chiMinusThree_mod_zero (n : ℕ) (h : n % 3 = 0) :
    chiMinusThree n = 0 := by
  have hc : (n : ZMod 3) = 0 := by
    calc
      (n : ZMod 3) = ((n % 3 : ℕ) : ZMod 3) := by simp
      _ = 0 := by rw [h]; simp
  change ((quadraticChar (ZMod 3) (n : ZMod 3) : ℤ) : ℂ) = 0
  rw [hc]
  simp

private theorem invCharAF_prime_pow_ge_two {q : ℕ}
    (χ : DirichletCharacter ℂ q) {p j : ℕ} (hp : p.Prime) (hj : 2 ≤ j) :
    invCharAF χ (p ^ j) = 0 := by
  rw [invCharAF_apply χ (pow_ne_zero j hp.ne_zero),
    ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
  simp [show j ≠ 1 by omega]

theorem pairAF_prime_pow_ge_three {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    {p k : ℕ} (hp : p.Prime) (hk : 3 ≤ k) :
    pairAF χ ψ (p ^ k) = 0 := by
  rw [pairAF, ArithmeticFunction.mul_apply]
  conv_lhs => rw [Nat.sum_divisorsAntidiagonal
    (fun a b => invCharAF χ a * invCharAF ψ b)]
  rw [Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_eq_zero
  intro i hi
  have hik : i ≤ k := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
  have hdiv : p ^ k / p ^ i = p ^ (k - i) := by
    have heq : k - i + i = k := Nat.sub_add_cancel hik
    calc
      p ^ k / p ^ i = (p ^ (k - i) * p ^ i) / p ^ i := by rw [← pow_add, heq]
      _ = p ^ (k - i) := by simp [hp.ne_zero]
  rw [hdiv]
  by_cases hii : 2 ≤ i
  · rw [invCharAF_prime_pow_ge_two χ hp hii, zero_mul]
  · have hki : 2 ≤ k - i := by omega
    rw [invCharAF_prime_pow_ge_two ψ hp hki, mul_zero]

private instance : IsCyclotomicExtension {3} ℚ ActualEisensteinSieve.K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private theorem base_ring_rank_two : Module.finrank ℤ O = 2 := by
  rw [NumberField.RingOfIntegers.rank ActualEisensteinSieve.K,
    IsCyclotomicExtension.Rat.finrank 3 ActualEisensteinSieve.K]
  decide

theorem baseChangeWeight_zero_of_norm_prime_pow_ge_three {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k)
    (I : Ideal O) (hI : Ideal.absNorm I = p ^ k) :
    baseChangeWeight χ I = 0 := by
  by_cases hμ : UniqueFactorizationMonoid.moebius I = 0
  · simp [baseChangeWeight, hμ]
  have hsq : Squarefree I := by
    by_contra hnsq
    exact hμ (UniqueFactorizationMonoid.moebius_of_not_squarefree hnsq)
  have hmem : ((p ^ k : ℕ) : O) ∈ I := by
    simpa only [hI] using Ideal.absNorm_mem I
  have hspanle : Ideal.span {((p : O) ^ k)} ≤ I :=
    (Ideal.span_singleton_le_iff_mem I).mpr (by simpa using hmem)
  have hpowdiv : I ∣ (Ideal.span {(p : O)}) ^ k := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_iff_le.mpr hspanle
  have hdiv : I ∣ Ideal.span {(p : O)} :=
    (hsq.dvd_pow_iff_dvd (by omega : k ≠ 0)).mp hpowdiv
  have hnormdiv := map_dvd Ideal.absNorm hdiv
  rw [hI, Ideal.absNorm_span_natCast, base_ring_rank_two] at hnormdiv
  have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hnormdiv
  omega

theorem normFiberCoeff_baseChangeWeight_prime_pow_ge_three {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k) :
    normFiberCoeff (baseChangeWeight χ) (p ^ k) = 0 := by
  classical
  unfold normFiberCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = p ^ k := by simpa using hI
  exact baseChangeWeight_zero_of_norm_prime_pow_ge_three χ hp hk I hnorm

theorem normFiberCoeff_eq_pairAF_prime_pow_ge_three {q p k : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hk : 3 ≤ k) :
    normFiberCoeff (baseChangeWeight χ) (p ^ k) =
      pairAF χ (baseChangeChar χ) (p ^ k) := by
  rw [normFiberCoeff_baseChangeWeight_prime_pow_ge_three χ hp hk,
    pairAF_prime_pow_ge_three χ (baseChangeChar χ) hp hk]

theorem char_prime_zero_of_dvd_level {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hd : p ∣ q) :
    χ p = 0 := by
  have hnot : ¬ IsCoprime (p : ℤ) (q : ℕ) := by
    intro hc
    have hn : p.Coprime q := by
      simpa [Int.isCoprime_iff_nat_coprime] using hc
    exact (hp.coprime_iff_not_dvd.mp hn) hd
  simpa using (DirichletCharacter.apply_eq_zero_iff χ (p : ℤ)).mpr hnot

theorem baseChangeChar_prime_zero_of_dvd_q {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hd : p ∣ q) :
    baseChangeChar χ p = 0 := by
  have hd' : p ∣ q * 3 := dvd_mul_of_dvd_left hd 3
  exact char_prime_zero_of_dvd_level (baseChangeChar χ) hp hd'

end ShortDraftHeckeBridge

namespace NormSplitArithmetic

theorem eq_parts_of_coprime_square_bounds {a b m n : ℕ}
    (hcop : m.Coprime n) (ha2 : a ∣ m ^ 2) (hb2 : b ∣ n ^ 2)
    (hprod : a * b = m * n) : a = m ∧ b = n := by
  have hm2n : (m ^ 2).Coprime n :=
    (Nat.coprime_pow_left_iff (by decide) m n).mpr hcop
  have hmn2 : m.Coprime (n ^ 2) :=
    (Nat.coprime_pow_right_iff (by decide) m n).mpr hcop
  have han : a.Coprime n := hm2n.coprime_dvd_left ha2
  have hmb : m.Coprime b := hmn2.coprime_dvd_right hb2
  have ha_mn : a ∣ m * n := ⟨b, hprod.symm⟩
  have hm_ab : m ∣ a * b := ⟨n, hprod⟩
  have hn_ab : n ∣ a * b := ⟨m, by rw [hprod, mul_comm]⟩
  have ha_m : a ∣ m := han.dvd_of_dvd_mul_right ha_mn
  have hm_a : m ∣ a := hmb.dvd_of_dvd_mul_right hm_ab
  have hb_n : b ∣ n := by
    have hbn : b.Coprime m := (hmn2.symm).coprime_dvd_left hb2
    have hb_mn : b ∣ n * m := ⟨a, by
      calc
        n * m = m * n := mul_comm n m
        _ = a * b := hprod.symm
        _ = b * a := mul_comm a b⟩
    exact hbn.dvd_of_dvd_mul_right hb_mn
  have hn_b : n ∣ b := han.symm.dvd_of_dvd_mul_left hn_ab
  exact ⟨Nat.dvd_antisymm ha_m hm_a, Nat.dvd_antisymm hb_n hn_b⟩

end NormSplitArithmetic

namespace NormFiberCRT

abbrev O := ActualEisensteinSieve.O
abbrev K := ActualEisensteinSieve.K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private theorem ring_rank_two : Module.finrank ℤ O = 2 := by
  rw [NumberField.RingOfIntegers.rank K,
    IsCyclotomicExtension.Rat.finrank 3 K]
  decide

theorem ideal_eq_factors (I : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m * n) :
    I = (I ⊔ Ideal.span {(m : O)}) * (I ⊔ Ideal.span {(n : O)}) := by
  let A : Ideal O := Ideal.span {(m : O)}
  let B : Ideal O := Ideal.span {(n : O)}
  have hcast : IsCoprime (m : O) (n : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime hcop).map (Int.castRingHom O)
  have hAB : A ⊔ B = ⊤ := by
    exact Ideal.isCoprime_iff_sup_eq.mp
      ((Ideal.isCoprime_span_singleton_iff (m : O) (n : O)).mpr hcast)
  have hmnmem : ((m * n : ℕ) : O) ∈ I := by
    simpa only [hI] using Ideal.absNorm_mem I
  have hABle : A * B ≤ I := by
    change Ideal.span {(m : O)} * Ideal.span {(n : O)} ≤ I
    rw [Ideal.span_singleton_mul_span_singleton]
    exact (Ideal.span_singleton_le_iff_mem I).mpr (by simpa using hmnmem)
  have hJcop : (I ⊔ A) ⊔ (I ⊔ B) = ⊤ := by
    calc
      (I ⊔ A) ⊔ (I ⊔ B) = I ⊔ (A ⊔ B) := by ac_rfl
      _ = ⊤ := by rw [hAB, sup_top_eq]
  apply le_antisymm
  · rw [Ideal.mul_eq_inf_of_coprime hJcop]
    exact le_inf le_sup_left le_sup_left
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
    exact sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left)
      (sup_le Ideal.mul_le_right hABle)

theorem ideal_factor_norms (I : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span {(m : O)}) = m ∧
      Ideal.absNorm (I ⊔ Ideal.span {(n : O)}) = n := by
  have hAm : Ideal.absNorm (Ideal.span {(m : O)}) = m ^ 2 := by
    rw [Ideal.absNorm_span_natCast, ring_rank_two]
  have hBn : Ideal.absNorm (Ideal.span {(n : O)}) = n ^ 2 := by
    rw [Ideal.absNorm_span_natCast, ring_rank_two]
  have hmdiv : Ideal.absNorm (I ⊔ Ideal.span {(m : O)}) ∣ m ^ 2 := by
    rw [← hAm]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hndiv : Ideal.absNorm (I ⊔ Ideal.span {(n : O)}) ∣ n ^ 2 := by
    rw [← hBn]
    exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hprod := congrArg Ideal.absNorm (ideal_eq_factors I m n hcop hI)
  rw [map_mul, hI] at hprod
  exact NormSplitArithmetic.eq_parts_of_coprime_square_bounds hcop hmdiv hndiv hprod.symm

end NormFiberCRT

namespace NormFiberMult

abbrev O := ActualEisensteinSieve.O

private theorem ideal_sup_span_norm_left (I J : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m)
    (hJ : Ideal.absNorm J = n) :
    I * J ⊔ Ideal.span {(m : O)} = I := by
  let A : Ideal O := Ideal.span {(m : O)}
  have hmI : A ≤ I := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    simpa only [hI] using Ideal.absNorm_mem I
  have hnJ : (n : O) ∈ J := by
    simpa only [hJ] using Ideal.absNorm_mem J
  have hnspan : Ideal.span {(n : O)} ≤ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr hnJ
  have hcast : IsCoprime (m : O) (n : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime hcop).map (Int.castRingHom O)
  have hAB : A ⊔ Ideal.span {(n : O)} = ⊤ := by
    exact Ideal.isCoprime_iff_sup_eq.mp
      ((Ideal.isCoprime_span_singleton_iff (m : O) (n : O)).mpr hcast)
  have hJA : J ⊔ A = ⊤ := by
    apply top_unique
    calc
      ⊤ = A ⊔ Ideal.span {(n : O)} := hAB.symm
      _ ≤ J ⊔ A := sup_le le_sup_right (hnspan.trans le_sup_left)
  apply le_antisymm
  · exact sup_le Ideal.mul_le_left hmI
  · calc
      I = I * (J ⊔ A) := by rw [hJA]; simp
      _ = I * J ⊔ I * A := by rw [Ideal.mul_sup]
      _ ≤ I * J ⊔ A := sup_le le_sup_left
        (Ideal.mul_le_right.trans le_sup_right)

private theorem ideal_sup_span_norm_right (I J : Ideal O) (m n : ℕ)
    (hcop : m.Coprime n) (hI : Ideal.absNorm I = m)
    (hJ : Ideal.absNorm J = n) :
    I * J ⊔ Ideal.span {(n : O)} = J := by
  simpa only [mul_comm] using
    ideal_sup_span_norm_left J I n m hcop.symm hJ hI

theorem weighted_norm_fiber_mul (weight : Ideal O → ℂ)
    (hweight : ∀ I J : Ideal O,
      (Ideal.absNorm I).Coprime (Ideal.absNorm J) →
      weight (I * J) = weight I * weight J)
    (m n : ℕ) (hcop : m.Coprime n) :
    (∑ K ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) (m * n)).toFinset,
       weight K) =
    (∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) m).toFinset,
       weight I) *
    (∑ J ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset,
       weight J) := by
  let F (k : ℕ) : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_eq (S := O) k).toFinset
  have hmem (k : ℕ) (I : Ideal O) : I ∈ F k ↔ Ideal.absNorm I = k := by
    simp [F]
  change (∑ K ∈ F (m * n), weight K) =
    (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J)
  calc
    (∑ K ∈ F (m * n), weight K) =
        ∑ p ∈ (F m).product (F n), weight (p.1 * p.2) := by
      refine Finset.sum_bij'
        (fun K _ => (K ⊔ Ideal.span {(m : O)},
                     K ⊔ Ideal.span {(n : O)}))
        (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
      · intro K hK
        have hKnorm : Ideal.absNorm K = m * n := (hmem _ _).mp hK
        obtain ⟨hm, hn⟩ := NormFiberCRT.ideal_factor_norms K m n hcop hKnorm
        simp [Finset.mem_product, hmem, hm, hn]
      · intro p hp
        have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
        have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
        exact (hmem _ _).mpr (by rw [map_mul, hm, hn])
      · intro K hK
        exact (NormFiberCRT.ideal_eq_factors K m n hcop ((hmem _ _).mp hK)).symm
      · intro p hp
        have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
        have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
        apply Prod.ext
        · exact ideal_sup_span_norm_left p.1 p.2 m n hcop hm hn
        · exact ideal_sup_span_norm_right p.1 p.2 m n hcop hm hn
      · intro K hK
        exact congrArg weight
          (NormFiberCRT.ideal_eq_factors K m n hcop ((hmem _ _).mp hK))
    _ = ∑ p ∈ (F m).product (F n), weight p.1 * weight p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hm : Ideal.absNorm p.1 = m := (hmem _ _).mp (Finset.mem_product.mp hp).1
      have hn : Ideal.absNorm p.2 = n := (hmem _ _).mp (Finset.mem_product.mp hp).2
      exact hweight p.1 p.2 (by simpa [hm, hn] using hcop)
    _ = (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J) := by
      calc
        (∑ p ∈ (F m).product (F n), weight p.1 * weight p.2) =
            ∑ I ∈ F m, ∑ J ∈ F n, weight I * weight J := by
          exact Finset.sum_product' (F m) (F n) (fun I J => weight I * weight J)
        _ = (∑ I ∈ F m, weight I) * (∑ J ∈ F n, weight J) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]

end NormFiberMult

namespace ShortDraftHeckeBridge

theorem baseChange_normFiber_mul {q : ℕ}
    (χ : DirichletCharacter ℂ q) (m n : ℕ) (hcop : m.Coprime n) :
    normFiberCoeff (baseChangeWeight χ) (m * n) =
      normFiberCoeff (baseChangeWeight χ) m *
        normFiberCoeff (baseChangeWeight χ) n := by
  exact NormFiberMult.weighted_norm_fiber_mul (baseChangeWeight χ)
    (fun I J h => baseChangeWeight_mul_of_coprime_norms χ I J h) m n hcop

theorem normFiberCoeff_baseChangeWeight_one {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 1 = 1 := by
  have hsingle :
      (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {⊤} := by
    ext I
    simp [Ideal.absNorm_eq_one_iff]
  unfold normFiberCoeff
  rw [hsingle]
  simp [baseChangeWeight, ← Ideal.one_eq_top]

theorem baseChange_normFiber_isMultiplicative {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (toArithmeticFunction (normFiberCoeff (baseChangeWeight χ))).IsMultiplicative := by
  constructor
  · simp [toArithmeticFunction, normFiberCoeff_baseChangeWeight_one]
  · intro m n hcop
    by_cases hm : m = 0
    · simp [hm, toArithmeticFunction]
    by_cases hn : n = 0
    · simp [hn, toArithmeticFunction]
    simpa [toArithmeticFunction, hm, hn, mul_ne_zero hm hn] using
      baseChange_normFiber_mul χ m n hcop

theorem baseChangeChar_prime_apply {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    baseChangeChar χ p = χ p * chiMinusThree p := by
  by_cases hq : p ∣ q
  · rw [baseChangeChar_prime_zero_of_dvd_q χ hp hq,
      char_prime_zero_of_dvd_level χ hp hq, zero_mul]
  by_cases h3 : p = 3
  · subst p
    rw [baseChangeChar_three, chiMinusThree_three, mul_zero]
  have hn3 : ¬p ∣ 3 := by
    intro hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd with h1 | h3'
    · exact hp.ne_one h1
    · exact h3 h3'
  have hnot : ¬p ∣ q * 3 := by
    intro hd
    rcases hp.dvd_mul.mp hd with hq' | h3'
    · exact hq hq'
    · exact hn3 h3'
  exact baseChangeChar_apply_of_coprime χ p
    (hp.coprime_iff_not_dvd.mpr hnot)

theorem normFiberCoeff_eq_pairAF_prime {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    normFiberCoeff (baseChangeWeight χ) p =
      pairAF χ (baseChangeChar χ) p := by
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  have hcase : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcase with h0 | h1 | h2
  · have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have heq : p = 3 := by
      rcases (Nat.dvd_prime hp).1 hdiv with h1' | h3
      · norm_num at h1'
      · exact h3.symm
    subst p
    rw [local_ramified_three χ,
      pairAF_prime χ (baseChangeChar χ) (by decide),
      baseChangeChar_three χ]
    ring_nf
  · rw [local_split_p χ hp h1, pairAF_prime χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_one p h1]
    ring
  · rw [local_inert_p χ hp h2, pairAF_prime χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_two p h2]
    ring

theorem normFiberCoeff_eq_pairAF_prime_sq {q p : ℕ}
    (χ : DirichletCharacter ℂ q) (hp : p.Prime) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
      pairAF χ (baseChangeChar χ) (p ^ 2) := by
  have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
  have hcase : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcase with h0 | h1 | h2
  · have hdiv : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have heq : p = 3 := by
      rcases (Nat.dvd_prime hp).1 hdiv with h1' | h3
      · norm_num at h1'
      · exact h3.symm
    subst p
    have h3 : pairAF χ (baseChangeChar χ) 9 =
        χ (3 : ℕ) * baseChangeChar χ (3 : ℕ) := by
      simpa only [show (3 : ℕ) ^ 2 = 9 by norm_num] using
        (pairAF_prime_sq χ (baseChangeChar χ) (by decide : Nat.Prime 3))
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, local_ramified_nine χ,
      h3, baseChangeChar_three χ]
    ring
  · rw [local_split_p_sq χ hp h1, pairAF_prime_sq χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_one p h1]
    simp only [map_pow]
    ring
  · rw [local_inert_p_sq χ hp h2, pairAF_prime_sq χ (baseChangeChar χ) hp,
      baseChangeChar_prime_apply χ hp, chiMinusThree_mod_two p h2]
    simp only [map_pow]
    ring

theorem normFiberCoeff_eq_pairInverseCoeff_of_local
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hprime : ∀ p : ℕ, p.Prime →
      normFiberCoeff (baseChangeWeight χ) p = pairAF χ (baseChangeChar χ) p)
    (hprimeSq : ∀ p : ℕ, p.Prime →
      normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
        pairAF χ (baseChangeChar χ) (p ^ 2))
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff (baseChangeWeight χ) n =
      pairInverseCoeff χ (baseChangeChar χ) n := by
  apply normFiber_eq_pair_of_prime_powers χ (baseChangeChar χ)
    (baseChangeWeight χ) (baseChange_normFiber_isMultiplicative χ) ?_ n hn
  intro p k hp
  by_cases hk0 : k = 0
  · simpa [hk0] using
      (baseChange_normFiber_isMultiplicative χ).map_one.trans
        ((pairAF_mult χ (baseChangeChar χ)).map_one).symm
  by_cases hk1 : k = 1
  · simpa [hk1, toArithmeticFunction, hp.ne_zero] using hprime p hp
  by_cases hk2 : k = 2
  · simpa [hk2, toArithmeticFunction, hp.ne_zero] using hprimeSq p hp
  have hk3 : 3 ≤ k := by omega
  change (if p ^ k = 0 then (0 : ℂ) else
    normFiberCoeff (baseChangeWeight χ) (p ^ k)) = _
  rw [ite_eq_right (pow_ne_zero k hp.ne_zero)]
  exact normFiberCoeff_eq_pairAF_prime_pow_ge_three χ hp hk3

theorem normFiberCoeff_baseChange_eq_pairInverseCoeff
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (n : ℕ) (hn : n ≠ 0) :
    normFiberCoeff (baseChangeWeight χ) n =
      pairInverseCoeff χ (baseChangeChar χ) n := by
  exact normFiberCoeff_eq_pairInverseCoeff_of_local χ
    (fun p hp => normFiberCoeff_eq_pairAF_prime χ hp)
    (fun p hp => normFiberCoeff_eq_pairAF_prime_sq χ hp) n hn

theorem dirichletTarget_of_normFiber_exp_bound
    (hbound : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        ∃ σ : ℝ, 0 < σ ∧ σ < ρ.re ∧
          (fun D : ℝ => normFiberExpSum (baseChangeWeight χ) D⁻¹) =O[atTop]
            (fun D : ℝ => D ^ σ)) :
    ShortDraft.DirichletTarget := by
  apply dirichletTarget_of_ideal_base_change ?_ hbound
  intro q _ χ n hn
  exact normFiberCoeff_baseChange_eq_pairInverseCoeff χ n hn

end ShortDraftHeckeBridge
open Filter Asymptotics

namespace ShortDraftHeckeBridge

private theorem rpow_le_one_add_of_exponent_Icc (x σ : ℝ)
    (hx : 0 ≤ x) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) : x ^ σ ≤ 1 + x := by
  by_cases hx1 : x ≤ 1
  · have h := Real.rpow_le_one hx hx1 hσ0
    linarith
  · have h := Real.rpow_le_self_of_one_le (le_of_not_ge hx1) hσ1
    linarith

private theorem tsum_add_one_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, ((n : ℝ) + 1) * r ^ n) = 1 / (1 - r) ^ 2 := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    (tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr)

private theorem summable_add_one_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr)

theorem geometric_rpow_moment_bound
    (σ D r : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hD : 1 ≤ D) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hscale : 1 / (D * (1 - r)) ≤ 2) :
    (1 - r) * (∑' n : ℕ, (((n : ℝ) + 1) ^ σ) * r ^ n) ≤
      3 * D ^ σ := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDpow : 0 ≤ D ^ σ := (Real.rpow_pos_of_pos hDpos σ).le
  have hrpow : ∀ n : ℕ,
      (((n : ℝ) + 1) ^ σ) * r ^ n ≤
      D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n)) := by
    intro n
    have hn : 0 ≤ ((n : ℝ) + 1) / D := by positivity
    have heq : D * (((n : ℝ) + 1) / D) = (n : ℝ) + 1 := by field_simp
    have hbase : ((n : ℝ) + 1) ^ σ ≤
        D ^ σ * (1 + ((n : ℝ) + 1) / D) := by
      calc
        ((n : ℝ) + 1) ^ σ =
            (D * (((n : ℝ) + 1) / D)) ^ σ := by rw [heq]
        _ = D ^ σ * (((n : ℝ) + 1) / D) ^ σ :=
          Real.mul_rpow hDpos.le hn
        _ ≤ D ^ σ * (1 + ((n : ℝ) + 1) / D) :=
          mul_le_mul_of_nonneg_left
            (rpow_le_one_add_of_exponent_Icc _ _ hn hσ0 hσ1) hDpow
    have hrn : 0 ≤ r ^ n := pow_nonneg hr0 _
    calc
      (((n : ℝ) + 1) ^ σ) * r ^ n ≤
          (D ^ σ * (1 + ((n : ℝ) + 1) / D)) * r ^ n :=
        mul_le_mul_of_nonneg_right hbase hrn
      _ = D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n)) := by ring
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs0 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hrnorm
  have hs1 : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) :=
    summable_add_one_mul_geometric hr0 hr1
  have hsdom : Summable (fun n : ℕ =>
      D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n))) :=
    ((hs0.add (hs1.mul_left D⁻¹)).mul_left (D ^ σ))
  have hslow : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ σ) * r ^ n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg
      (Real.rpow_nonneg (by positivity) σ) (pow_nonneg hr0 _)) hrpow hsdom
  have hsum := Summable.tsum_le_tsum hrpow hslow hsdom
  have hgap : 0 ≤ 1 - r := sub_nonneg.mpr hr1.le
  have hgeom : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
    tsum_geometric_of_norm_lt_one hrnorm
  have hlin := tsum_add_one_mul_geometric hr0 hr1
  have hgap_ne : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  calc
    (1 - r) * (∑' n : ℕ, (((n : ℝ) + 1) ^ σ) * r ^ n) ≤
        (1 - r) * (∑' n : ℕ,
          D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n))) :=
      mul_le_mul_of_nonneg_left hsum hgap
    _ = D ^ σ * (1 + 1 / (D * (1 - r))) := by
      rw [tsum_mul_left, Summable.tsum_add hs0 (hs1.mul_left D⁻¹),
        tsum_mul_left, hgeom, hlin]
      field_simp
    _ ≤ 3 * D ^ σ := by
      nlinarith [mul_nonneg hDpow (sub_nonneg.mpr hscale)]

noncomputable def prefixCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a k

theorem tsum_eq_one_sub_mul_tsum_prefix
    (a : ℕ → ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Summable (fun n : ℕ => a n * (r : ℂ) ^ n)) :
    (∑' n : ℕ, a n * (r : ℂ) ^ n) =
      (1 - (r : ℂ)) * (∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n) := by
  have hrC : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hg : Summable (fun n : ℕ => (r : ℂ) ^ n) :=
    summable_geometric_of_norm_lt_one hrC
  have hconv := hasSum_sum_range_mul_of_summable_norm hf.norm hg.norm
  have hcoeff (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        (a k * (r : ℂ) ^ k) * (r : ℂ) ^ (n - k)) =
      prefixCoeff a n * (r : ℂ) ^ n := by
    calc
      (∑ k ∈ Finset.range (n + 1),
        (a k * (r : ℂ) ^ k) * (r : ℂ) ^ (n - k)) =
          ∑ k ∈ Finset.range (n + 1), a k * (r : ℂ) ^ n := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hkn]
      _ = prefixCoeff a n * (r : ℂ) ^ n := by
        rw [prefixCoeff, Finset.sum_mul]
  have hconvEq := hconv.tsum_eq
  simp_rw [hcoeff] at hconvEq
  rw [tsum_geometric_of_norm_lt_one hrC] at hconvEq
  have hne : (1 - (r : ℂ)) ≠ 0 := by
    exact sub_ne_zero.mpr (by norm_cast; exact (ne_of_lt hr1).symm)
  calc
    (∑' n : ℕ, a n * (r : ℂ) ^ n) =
      (1 - (r : ℂ)) *
        ((∑' n : ℕ, a n * (r : ℂ) ^ n) * (1 - (r : ℂ))⁻¹) := by
          field_simp
    _ = (1 - (r : ℂ)) * (∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n) := by
      rw [hconvEq]

theorem exp_inv_geometric_gap (D : ℝ) (hD : 1 ≤ D) :
    1 / (D * (1 - Real.exp (-D⁻¹))) ≤ 2 := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hden : 0 < D + 1 := by linarith
  have hx : 0 < D⁻¹ := inv_pos.mpr hDpos
  have hbase : 0 < 1 + D⁻¹ := by positivity
  have hexp : 1 + D⁻¹ ≤ Real.exp D⁻¹ := by
    linarith [Real.add_one_le_exp D⁻¹]
  have he : Real.exp (-D⁻¹) ≤ (1 + D⁻¹)⁻¹ := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le hbase hexp
  have hrew : (1 + D⁻¹)⁻¹ = D / (D + 1) := by
    field_simp
  rw [hrew] at he
  have hhalf : (1 / 2 : ℝ) ≤ D * (1 - Real.exp (-D⁻¹)) := by
    calc
      (1 / 2 : ℝ) ≤ D / (D + 1) := by
        apply (le_div_iff₀ hden).2
        nlinarith
      _ = D * (1 - D / (D + 1)) := by
        field_simp
        ring
      _ ≤ D * (1 - Real.exp (-D⁻¹)) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left he 1) hDpos.le
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  norm_num at h ⊢
  exact h

theorem normFiberExpSum_le_of_prefix_power
    {q r₀ : ℕ} [NeZero q] [NeZero r₀]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r₀)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ C : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖prefixCoeff (normFiberCoeff weight) n‖ ≤ C * (((n : ℝ) + 1) ^ σ))
    (D : ℝ) (hD : 1 ≤ D) :
    ‖normFiberExpSum weight D⁻¹‖ ≤ 3 * C * D ^ σ := by
  let a : ℕ → ℂ := normFiberCoeff weight
  let r : ℝ := Real.exp (-D⁻¹)
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have ht : 0 < D⁻¹ := inv_pos.mpr hDpos
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hpow (n : ℕ) : Real.exp (-(n : ℝ) * D⁻¹) = r ^ n := by
    dsimp [r]
    convert Real.exp_nat_mul (-D⁻¹) n using 1 ; ring_nf
  have hf : Summable (fun n : ℕ => a n * (r : ℂ) ^ n) := by
    have h := normFiberExpSum_summable χ ψ weight hcoeff ha0 D⁻¹ ht
    simpa only [a, hpow, Complex.ofReal_pow] using h
  have hS : normFiberExpSum weight D⁻¹ =
      ∑' n : ℕ, a n * (r : ℂ) ^ n := by
    unfold normFiberExpSum
    apply tsum_congr
    intro n
    simp only [a, hpow, Complex.ofReal_pow]
  have habel := tsum_eq_one_sub_mul_tsum_prefix a r hr0 hr1 hf
  have hlin : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) :=
    summable_add_one_mul_geometric hr0 hr1
  have hmoment : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ σ) * r ^ n) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) σ) (pow_nonneg hr0 _))
      (fun n => ?_) hlin
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith) hσ1) (pow_nonneg hr0 _)
  have hdom : Summable (fun n : ℕ => C * ((((n : ℝ) + 1) ^ σ) * r ^ n)) :=
    hmoment.mul_left C
  have hpoint (n : ℕ) :
      ‖prefixCoeff a n * (r : ℂ) ^ n‖ ≤
        C * ((((n : ℝ) + 1) ^ σ) * r ^ n) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    have h := mul_le_mul_of_nonneg_right (hprefix n) (pow_nonneg hr0 n)
    convert h using 1 ; ring
  have hnorm : Summable (fun n : ℕ => ‖prefixCoeff a n * (r : ℂ) ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hdom
  have hgap : 0 ≤ 1 - r := sub_nonneg.mpr hr1.le
  have hmomentBound := geometric_rpow_moment_bound σ D r hσ0 hσ1 hD hr0 hr1
    (exp_inv_geometric_gap D hD)
  calc
    ‖normFiberExpSum weight D⁻¹‖ =
        ‖(1 - (r : ℂ)) * (∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n)‖ := by
          rw [hS, habel]
    _ = (1 - r) * ‖∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n‖ := by
      have hreal : (1 - (r : ℂ)) = ((1 - r : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgap]
    _ ≤ (1 - r) * (∑' n : ℕ, ‖prefixCoeff a n * (r : ℂ) ^ n‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) hgap
    _ ≤ (1 - r) * (∑' n : ℕ,
          C * ((((n : ℝ) + 1) ^ σ) * r ^ n)) :=
      mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum hpoint hnorm hdom) hgap
    _ = C * ((1 - r) * (∑' n : ℕ, (((n : ℝ) + 1) ^ σ) * r ^ n)) := by
      rw [tsum_mul_left]
      ring
    _ ≤ C * (3 * D ^ σ) := mul_le_mul_of_nonneg_left hmomentBound hC
    _ = 3 * C * D ^ σ := by ring

theorem normFiberExpSum_isBigO_of_prefix_power
    {q r₀ : ℕ} [NeZero q] [NeZero r₀]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r₀)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ C : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖prefixCoeff (normFiberCoeff weight) n‖ ≤ C * (((n : ℝ) + 1) ^ σ)) :
    (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
  apply IsBigO.of_bound (3 * C)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
  have h := normFiberExpSum_le_of_prefix_power χ ψ weight hcoeff ha0
    σ C hσ0 hσ1 hC hprefix D hD
  have hDnonneg : 0 ≤ D := (zero_le_one.trans hD)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hDnonneg σ)] using h

end ShortDraftHeckeBridge

end

end OAI
end OAIOriginalModule0075

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeExtraction
Source SHA256: 1da3b4eabf405bcf8e37af8340154791b0b79ded6b552287914158976f0956e2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0076


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
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics

namespace ShortDraftHeckeBridge

theorem dirichletTarget_of_normFiber_prefix_power
    (hprefix : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        ∃ σ C : ℝ, 0 < σ ∧ σ < ρ.re ∧ σ ≤ 1 ∧ 0 ≤ C ∧
          ∀ n : ℕ,
            ‖prefixCoeff (normFiberCoeff (baseChangeWeight χ)) n‖ ≤
              C * (((n : ℝ) + 1) ^ σ)) :
    ShortDraft.DirichletTarget := by
  apply dirichletTarget_of_normFiber_exp_bound
  intro q _ χ ρ h23 hρ
  obtain ⟨σ, C, hσpos, hσρ, hσone, hC, hsum⟩ :=
    hprefix q χ ρ h23 hρ
  refine ⟨σ, hσpos, hσρ, ?_⟩
  apply normFiberExpSum_isBigO_of_prefix_power χ (baseChangeChar χ)
    (baseChangeWeight χ)
    (normFiberCoeff_baseChange_eq_pairInverseCoeff χ)
    (normFiberCoeff_baseChangeWeight_zero χ)
    σ C hσpos.le hσone hC hsum

end ShortDraftHeckeBridge
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace FiniteSFactor

abbrev O := NumberField.RingOfIntegers (CyclotomicField 3 ℚ)

theorem extract_prime_of_squarefree {I P : Ideal O}
    (hI : I ≠ ⊥) (hP : Prime P) (hsq : Squarefree I) (hdvd : P ∣ I) :
    ∃ J : Ideal O, IsRelPrime P J ∧ I = P * J := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  obtain ⟨J, hcop, hfactor⟩ := Ideal.eq_prime_pow_mul_coprime hI P
  have hmem : P ∈ normalizedFactors I := by
    rw [Ideal.mem_normalizedFactors_iff hI]
    exact ⟨Ideal.isPrime_of_prime hP, (Ideal.dvd_iff_le).mp hdvd⟩
  have hpos : 0 < (normalizedFactors I).count P := Multiset.count_pos.mpr hmem
  have hnodup : (normalizedFactors I).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hI).mp hsq
  have hle : (normalizedFactors I).count P ≤ 1 :=
    (Multiset.nodup_iff_count_le_one.mp hnodup) P
  have he : (normalizedFactors I).count P = 1 := by omega
  refine ⟨J, ?_, ?_⟩
  · exact IsCoprime.isRelPrime ((Ideal.isCoprime_iff_gcd).mpr (by simpa using hcop))
  · simpa [he] using hfactor

noncomputable def outsideWeight (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (I : Ideal O) : ℂ := by
  classical
  exact if ∀ P ∈ S, ¬ P ∣ I then w I else 0

theorem outsideWeight_mul (S : Finset (Ideal O))
    (hprime : ∀ P ∈ S, Prime P) (w : Ideal O → ℂ)
    (I J : Ideal O) (hweight : w (I * J) = w I * w J) :
    outsideWeight S w (I * J) =
      outsideWeight S w I * outsideWeight S w J := by
  classical
  let good (K : Ideal O) : Prop := ∀ P ∈ S, ¬ P ∣ K
  have hleft : good (I * J) → good I := by
    intro h P hP hd
    exact h P hP (dvd_mul_of_dvd_left hd J)
  have hright : good (I * J) → good J := by
    intro h P hP hd
    exact h P hP (dvd_mul_of_dvd_right hd I)
  have hboth : good I → good J → good (I * J) := by
    intro hI hJ P hP hd
    rcases (hprime P hP).dvd_mul.mp hd with hdI | hdJ
    · exact hI P hP hdI
    · exact hJ P hP hdJ
  change (if good (I * J) then w (I * J) else 0) =
    (if good I then w I else 0) * (if good J then w J else 0)
  by_cases hI : good I
  · by_cases hJ : good J
    · have hIJ := hboth hI hJ
      simp [hI, hJ, hIJ, hweight]
    · have hIJ : ¬good (I * J) := fun h => hJ (hright h)
      simp [hI, hJ, hIJ]
  · have hIJ : ¬good (I * J) := fun h => hI (hleft h)
    simp [hI, hIJ]

noncomputable def fiber (n : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset

theorem mem_fiber {n : ℕ} {I : Ideal O} : I ∈ fiber n ↔ Ideal.absNorm I = n := by
  simp [fiber]

noncomputable def badFiber (P : Ideal O) (m : ℕ) : Finset (Ideal O) := by
  classical
  exact (fiber (Ideal.absNorm P * m)).filter (fun I => Squarefree I ∧ P ∣ I)

noncomputable def goodFiber (P : Ideal O) (m : ℕ) : Finset (Ideal O) := by
  classical
  exact (fiber m).filter (fun J => Squarefree J ∧ ¬ P ∣ J)

theorem mem_badFiber {P : Ideal O} {m : ℕ} {I : Ideal O} :
    I ∈ badFiber P m ↔ Ideal.absNorm I = Ideal.absNorm P * m ∧ Squarefree I ∧ P ∣ I := by
  classical
  simp [badFiber, mem_fiber]

theorem mem_goodFiber {P : Ideal O} {m : ℕ} {J : Ideal O} :
    J ∈ goodFiber P m ↔ Ideal.absNorm J = m ∧ Squarefree J ∧ ¬P ∣ J := by
  classical
  simp [goodFiber, mem_fiber]

private noncomputable def pick (P : Ideal O) (hP : Prime P) (m : ℕ)
    (I : Ideal O) (hI : I ∈ badFiber P m) : Ideal O :=
  Classical.choose (extract_prime_of_squarefree
    ((mem_badFiber.mp hI).2.1.ne_zero) hP
    (mem_badFiber.mp hI).2.1 (mem_badFiber.mp hI).2.2)

private theorem pick_spec (P : Ideal O) (hP : Prime P) (m : ℕ)
    (I : Ideal O) (hI : I ∈ badFiber P m) :
    IsRelPrime P (pick P hP m I hI) ∧ I = P * pick P hP m I hI := by
  unfold pick
  exact Classical.choose_spec (extract_prime_of_squarefree
    ((mem_badFiber.mp hI).2.1.ne_zero) hP
    (mem_badFiber.mp hI).2.1 (mem_badFiber.mp hI).2.2)

theorem squarefree_prime_fiber_sum (P : Ideal O) (hP : Prime P)
    (m : ℕ) (w : Ideal O → ℂ) :
    (∑ I ∈ badFiber P m, w I) =
      ∑ J ∈ goodFiber P m, w (P * J) := by
  classical
  have hPnorm : Ideal.absNorm P ≠ 0 :=
    (Ideal.absNorm_eq_zero_iff).not.mpr hP.ne_zero
  refine Finset.sum_bij' (pick P hP m) (fun J _ => P * J) ?_ ?_ ?_ ?_ ?_
  · intro I hI
    have hinfo := pick_spec P hP m I hI
    have hJnorm : Ideal.absNorm (pick P hP m I hI) = m := by
      have hInorm := (mem_badFiber.mp hI).1
      rw [hinfo.2, map_mul] at hInorm
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hPnorm) hInorm
    have hJsq : Squarefree (pick P hP m I hI) := by
      have hsqI := (mem_badFiber.mp hI).2.1
      rw [hinfo.2] at hsqI
      exact hsqI.of_mul_right
    have hJnot : ¬P ∣ pick P hP m I hI :=
      hP.irreducible.isRelPrime_iff_not_dvd.mp hinfo.1
    exact mem_goodFiber.mpr ⟨hJnorm, hJsq, hJnot⟩
  · intro J hJ
    have hJnorm := (mem_goodFiber.mp hJ).1
    have hJsq := (mem_goodFiber.mp hJ).2.1
    have hJnot := (mem_goodFiber.mp hJ).2.2
    have hsq : Squarefree (P * J) :=
      squarefree_mul_iff.mpr ⟨hP.irreducible.isRelPrime_iff_not_dvd.mpr hJnot,
        hP.irreducible.squarefree, hJsq⟩
    exact mem_badFiber.mpr ⟨by rw [map_mul, hJnorm], hsq, dvd_mul_right P J⟩
  · intro I hI
    exact (pick_spec P hP m I hI).2.symm
  · intro J hJ
    have hPJ : P * J ∈ badFiber P m := by
      have hJnorm := (mem_goodFiber.mp hJ).1
      have hJsq := (mem_goodFiber.mp hJ).2.1
      have hJnot := (mem_goodFiber.mp hJ).2.2
      exact mem_badFiber.mpr ⟨by rw [map_mul, hJnorm],
        squarefree_mul_iff.mpr ⟨hP.irreducible.isRelPrime_iff_not_dvd.mpr hJnot,
          hP.irreducible.squarefree, hJsq⟩, dvd_mul_right P J⟩
    have hchosen := (pick_spec P hP m (P * J) hPJ).2
    exact (mul_left_cancel₀ hP.ne_zero hchosen).symm
  · intro I hI
    exact congrArg w (pick_spec P hP m I hI).2

open scoped Classical

noncomputable def exceptPrimeCoeff (P : Ideal O) (w : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ fiber n, if ¬P ∣ I then w I else 0

private theorem sum_filter_squarefree (pred : Ideal O → Prop) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0) (n : ℕ) :
    (∑ I ∈ fiber n, if pred I then w I else 0) =
      ∑ I ∈ (fiber n).filter (fun I => Squarefree I ∧ pred I), w I := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hsq : Squarefree I
  · simp [hsq]
  · simp [hsq, hzero I hsq]

theorem restore_one_prime (P : Ideal O) (hP : Prime P)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ J, ¬P ∣ J → w (P * J) = w P * w J)
    (m : ℕ) :
    (∑ I ∈ fiber (Ideal.absNorm P * m), w I) =
      exceptPrimeCoeff P w (Ideal.absNorm P * m) +
        w P * exceptPrimeCoeff P w m := by
  classical
  let n := Ideal.absNorm P * m
  have hsplit : (∑ I ∈ fiber n, w I) =
      (∑ I ∈ fiber n, if ¬P ∣ I then w I else 0) +
      (∑ I ∈ fiber n, if P ∣ I then w I else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    by_cases h : P ∣ I <;> simp [h]
  have hbad : (∑ I ∈ fiber n, if P ∣ I then w I else 0) =
      ∑ I ∈ badFiber P m, w I := by
    rw [badFiber]
    exact sum_filter_squarefree (fun I => P ∣ I) w hzero n
  have hgood : (∑ J ∈ goodFiber P m, w J) = exceptPrimeCoeff P w m := by
    rw [goodFiber, exceptPrimeCoeff, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hsq : Squarefree J
    · simp [hsq]
    · simp [hsq, hzero J hsq]
  calc
    (∑ I ∈ fiber n, w I) =
        (∑ I ∈ fiber n, if ¬P ∣ I then w I else 0) +
          (∑ I ∈ fiber n, if P ∣ I then w I else 0) := hsplit
    _ = exceptPrimeCoeff P w n + ∑ I ∈ badFiber P m, w I := by
      rw [hbad]
      rfl
    _ = exceptPrimeCoeff P w n + ∑ J ∈ goodFiber P m, w (P * J) := by
      rw [squarefree_prime_fiber_sum P hP m w]
    _ = exceptPrimeCoeff P w n + w P * ∑ J ∈ goodFiber P m, w J := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro J hJ
      exact hmul J (mem_goodFiber.mp hJ).2.2
    _ = exceptPrimeCoeff P w n + w P * exceptPrimeCoeff P w m := by rw [hgood]

theorem restore_one_prime_all (P : Ideal O) (hP : Prime P)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ J, ¬P ∣ J → w (P * J) = w P * w J)
    (n : ℕ) :
    (∑ I ∈ fiber n, w I) = exceptPrimeCoeff P w n +
      (if Ideal.absNorm P ∣ n then
        w P * exceptPrimeCoeff P w (n / Ideal.absNorm P) else 0) := by
  classical
  by_cases hdiv : Ideal.absNorm P ∣ n
  · have hn : Ideal.absNorm P * (n / Ideal.absNorm P) = n :=
      Nat.mul_div_cancel' hdiv
    rw [← hn]
    have hPnorm : Ideal.absNorm P ≠ 0 :=
      (Ideal.absNorm_eq_zero_iff).not.mpr hP.ne_zero
    simpa [Nat.mul_div_cancel_left, hPnorm] using
      restore_one_prime P hP w hzero hmul (n / Ideal.absNorm P)
  · have hnone : ∀ I ∈ fiber n, ¬P ∣ I := by
      intro I hI hd
      apply hdiv
      have hnorm : Ideal.absNorm I = n := mem_fiber.mp hI
      rw [← hnorm]
      exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hd)
    simp only [ite_eq_right hdiv, add_zero]
    rw [exceptPrimeCoeff]
    apply Finset.sum_congr rfl
    intro I hI
    simp [hnone I hI]

open scoped Classical

noncomputable def outsideCoeff (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (n : ℕ) : ℂ :=
  ∑ I ∈ fiber n, outsideWeight S w I

private theorem outsideWeight_zero_of_not_squarefree (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (I : Ideal O) (hsq : ¬Squarefree I) : outsideWeight S w I = 0 := by
  by_cases hg : ∀ P ∈ S, ¬P ∣ I
  · simp [outsideWeight,  hzero I hsq]
  · simp [outsideWeight, hg]

private theorem outsideWeight_prime_of_not_mem (S : Finset (Ideal O))
    (hprime : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P)
    (hPnot : P ∉ S) (w : Ideal O → ℂ) :
    outsideWeight S w P = w P := by
  have hgood : ∀ Q ∈ S, ¬Q ∣ P := by
    intro Q hQ hd
    have heq : Q = P :=
      associated_iff_eq.mp ((hprime Q hQ).associated_of_dvd hP hd)
    exact hPnot (heq ▸ hQ)
  change (if ∀ Q ∈ S, ¬Q ∣ P then w P else 0) = w P
  exact ite_eq_left hgood

private theorem exceptPrimeCoeff_outsideWeight (S : Finset (Ideal O))
    (P : Ideal O) (w : Ideal O → ℂ) (n : ℕ) :
    exceptPrimeCoeff P (outsideWeight S w) n =
      outsideCoeff (insert P S) w n := by
  classical
  unfold exceptPrimeCoeff outsideCoeff
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hd : P ∣ I
  · simp [outsideWeight, hd]
  · by_cases hs : ∀ Q ∈ S, ¬Q ∣ I
    · simp [outsideWeight, hd]
    · simp [outsideWeight, hd, hs]

theorem restore_insert_prime (S : Finset (Ideal O))
    (hprime : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P)
    (hPnot : P ∉ S) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (n : ℕ) :
    outsideCoeff S w n = outsideCoeff (insert P S) w n +
      (if Ideal.absNorm P ∣ n then
        w P * outsideCoeff (insert P S) w (n / Ideal.absNorm P) else 0) := by
  have hzeroS : ∀ I, ¬Squarefree I → outsideWeight S w I = 0 :=
    outsideWeight_zero_of_not_squarefree S w hzero
  have hmulS : ∀ J, ¬P ∣ J →
      outsideWeight S w (P * J) = outsideWeight S w P * outsideWeight S w J := by
    intro J hnot
    apply outsideWeight_mul S hprime w P J
    exact hmul P J (hP.irreducible.isRelPrime_iff_not_dvd.mpr hnot)
  have hrest := restore_one_prime_all P hP (outsideWeight S w) hzeroS hmulS n
  unfold outsideCoeff at hrest ⊢
  rw [exceptPrimeCoeff_outsideWeight S P w n,
    exceptPrimeCoeff_outsideWeight S P w (n / Ideal.absNorm P),
    outsideWeight_prime_of_not_mem S hprime P hP hPnot w] at hrest
  exact hrest

end FiniteSFactor
namespace ShortDraftHeckeBridge

theorem baseChangeWeight_zero_of_not_squarefree {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I : Ideal O) (hsq : ¬Squarefree I) :
    baseChangeWeight χ I = 0 := by
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hsq]
  simp

theorem baseChangeWeight_mul_of_isRelPrime {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I J : Ideal O) (h : IsRelPrime I J) :
    baseChangeWeight χ (I * J) =
      baseChangeWeight χ I * baseChangeWeight χ J := by
  simp only [baseChangeWeight, map_mul, h.moebius_mul, Int.cast_mul, Nat.cast_mul]
  ring

theorem baseChange_restore_insert_prime {q : ℕ}
    (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S) (n : ℕ) :
    FiniteSFactor.outsideCoeff S (baseChangeWeight χ) n =
      FiniteSFactor.outsideCoeff (insert P S) (baseChangeWeight χ) n +
      (if Ideal.absNorm P ∣ n then
        baseChangeWeight χ P *
          FiniteSFactor.outsideCoeff (insert P S) (baseChangeWeight χ)
            (n / Ideal.absNorm P) else 0) := by
  exact FiniteSFactor.restore_insert_prime S hS P hP hPnot
    (baseChangeWeight χ) (baseChangeWeight_zero_of_not_squarefree χ)
    (baseChangeWeight_mul_of_isRelPrime χ) n

end ShortDraftHeckeBridge

namespace DyadicTransfer

noncomputable def annularCutoff (φ : ℝ → ℂ) (y : ℝ) : ℂ :=
  φ y - φ (2 * y)

theorem annularCutoff_eq_zero_of_le_half (φ : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    {y : ℝ} (hy : y ≤ 1 / 2) : annularCutoff φ y = 0 := by
  have hy1 : y ≤ 1 := by linarith
  have h2y : 2 * y ≤ 1 := by linarith
  simp [annularCutoff, hsmall y hy1, hsmall (2 * y) h2y]

theorem annularCutoff_eq_zero_of_two_le (φ : ℝ → ℂ)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    {y : ℝ} (hy : 2 ≤ y) : annularCutoff φ y = 0 := by
  have h2y : 2 ≤ 2 * y := by linarith
  simp [annularCutoff, hlarge y hy, hlarge (2 * y) h2y]

theorem partial_partition (φ : ℝ → ℂ) (x : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1),
      annularCutoff φ (x / (2 : ℝ) ^ k)) =
      φ (x / (2 : ℝ) ^ K) - φ (2 * x) := by
  induction K with
  | zero =>
      simp [annularCutoff]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      unfold annularCutoff
      have hpow : (2 : ℝ) ^ (K + 1) ≠ 0 := by positivity
      have hshift : 2 * (x / (2 : ℝ) ^ (K + 1)) = x / (2 : ℝ) ^ K := by
        rw [pow_succ]
        field_simp
      rw [hshift]
      ring

theorem partition_nat (φ : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    (n K : ℕ) (hn : 1 ≤ n) (hK : (n : ℝ) ≤ (2 : ℝ) ^ K) :
    (∑ k ∈ Finset.range (K + 1),
      annularCutoff φ ((n : ℝ) / (2 : ℝ) ^ k)) = 1 := by
  rw [partial_partition]
  have hpow : 0 < (2 : ℝ) ^ K := by positivity
  have hnsmall : (n : ℝ) / (2 : ℝ) ^ K ≤ 1 :=
    (div_le_iff₀ hpow).mpr (by simpa using hK)
  rw [hsmall _ hnsmall, hlarge]
  · ring
  · exact_mod_cast (show (2 : ℕ) ≤ 2 * n by omega)

noncomputable def expAnnularTest (φ : ℝ → ℂ) (D : ℝ) (k : ℕ) (y : ℝ) : ℂ :=
  annularCutoff φ y * Real.exp (-((2 : ℝ) ^ k / D) * y)

theorem expAnnularTest_eq_zero_of_le_half (φ : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    (D : ℝ) (k : ℕ) {y : ℝ} (hy : y ≤ 1 / 2) :
    expAnnularTest φ D k y = 0 := by
  simp [expAnnularTest, annularCutoff_eq_zero_of_le_half φ hsmall hy]

theorem expAnnularTest_eq_zero_of_two_le (φ : ℝ → ℂ)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    (D : ℝ) (k : ℕ) {y : ℝ} (hy : 2 ≤ y) :
    expAnnularTest φ D k y = 0 := by
  simp [expAnnularTest, annularCutoff_eq_zero_of_two_le φ hlarge hy]

theorem expAnnularTest_norm_le (φ : ℝ → ℂ) (D : ℝ) (k : ℕ)
    (hD : 0 < D) (M : ℝ) (hM : ∀ y : ℝ, ‖annularCutoff φ y‖ ≤ M)
    {y : ℝ} (hy : 1 / 2 ≤ y) :
    ‖expAnnularTest φ D k y‖ ≤
      M * Real.exp (-((2 : ℝ) ^ k / D) / 2) := by
  let t : ℝ := (2 : ℝ) ^ k / D
  have ht : 0 ≤ t := div_nonneg (by positivity) hD.le
  have harg : -(t * y) ≤ -t / 2 := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hy)]
  have hexp : Real.exp (-(t * y)) ≤ Real.exp (-t / 2) :=
    Real.exp_le_exp.mpr harg
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM y)
  calc
    ‖expAnnularTest φ D k y‖ = ‖annularCutoff φ y‖ * Real.exp (-(t * y)) := by
      rw [expAnnularTest, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      simp [t]
    _ ≤ M * Real.exp (-(t * y)) :=
      mul_le_mul_of_nonneg_right (hM y) (Real.exp_pos _).le
    _ ≤ M * Real.exp (-t / 2) := mul_le_mul_of_nonneg_left hexp hM0
    _ = M * Real.exp (-((2 : ℝ) ^ k / D) / 2) := rfl

theorem finite_exp_reassembly (a : ℕ → ℂ) (φ : ℝ → ℂ)
    (ha0 : a 0 = 0)
    (hsmall : ∀ y : ℝ, y ≤ 1 → φ y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → φ y = 0)
    (D : ℝ) (N K : ℕ)
    (hK : ∀ n ∈ Finset.range N, 1 ≤ n → (n : ℝ) ≤ (2 : ℝ) ^ K) :
    (∑ n ∈ Finset.range N, a n * Real.exp (-(n : ℝ) / D)) =
      ∑ k ∈ Finset.range (K + 1),
        ∑ n ∈ Finset.range N,
          a n * expAnnularTest φ D k ((n : ℝ) / (2 : ℝ) ^ k) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [ha0, expAnnularTest, annularCutoff]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hpart := partition_nat φ hsmall hlarge n K hn1 (hK n hn hn1)
    simp_rw [expAnnularTest]
    have hexp (k : ℕ) :
        Real.exp (-((2 : ℝ) ^ k / D) * ((n : ℝ) / (2 : ℝ) ^ k)) =
          Real.exp (-(n : ℝ) / D) := by
      congr 1
      have hpow : (2 : ℝ) ^ k ≠ 0 := by positivity
      field_simp
    simp_rw [hexp]
    rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hpart]
    simp

theorem finite_dyadic_piece_bound
    (F : ℕ → ℂ) (C r : ℝ) (hC : 0 ≤ C) (hr : 1 < r)
    (b : ℕ → ℝ) (hb : Summable b) (hb0 : ∀ m, 0 ≤ b m)
    (N M : ℕ)
    (hlow : ∀ k ≤ N, ‖F k‖ ≤ C * r ^ k)
    (hhigh : ∀ m, ‖F (N + 1 + m)‖ ≤ C * r ^ N * b m) :
    ‖∑ k ∈ Finset.range (N + 1 + M), F k‖ ≤
      C * (r ^ (N + 1) / (r - 1) + r ^ N * ∑' m, b m) := by
  have hr0 : 0 ≤ r := by linarith
  have hrden : 0 < r - 1 := by linarith
  have hlowSum :
      ‖∑ k ∈ Finset.range (N + 1), F k‖ ≤
        C * (r ^ (N + 1) / (r - 1)) := by
    calc
      ‖∑ k ∈ Finset.range (N + 1), F k‖ ≤
          ∑ k ∈ Finset.range (N + 1), ‖F k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (N + 1), C * r ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        exact hlow k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      _ = C * ((r ^ (N + 1) - 1) / (r - 1)) := by
        rw [← Finset.mul_sum, geom_sum_eq (ne_of_gt hr)]
      _ ≤ C * (r ^ (N + 1) / (r - 1)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact div_le_div_of_nonneg_right (by linarith) hrden.le
  have hhighSum :
      ‖∑ m ∈ Finset.range M, F (N + 1 + m)‖ ≤
        C * r ^ N * ∑' m, b m := by
    calc
      ‖∑ m ∈ Finset.range M, F (N + 1 + m)‖ ≤
          ∑ m ∈ Finset.range M, ‖F (N + 1 + m)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.range M, C * r ^ N * b m := by
        apply Finset.sum_le_sum
        intro m _
        exact hhigh m
      _ = C * r ^ N * ∑ m ∈ Finset.range M, b m := by
        rw [← Finset.mul_sum]
      _ ≤ C * r ^ N * ∑' m, b m := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (pow_nonneg hr0 N))
        exact hb.sum_le_tsum _ (fun m _ => hb0 m)
  rw [Finset.sum_range_add]
  calc
    ‖(∑ k ∈ Finset.range (N + 1), F k) +
      ∑ m ∈ Finset.range M, F (N + 1 + m)‖ ≤
        ‖∑ k ∈ Finset.range (N + 1), F k‖ +
          ‖∑ m ∈ Finset.range M, F (N + 1 + m)‖ := norm_add_le _ _
    _ ≤ C * (r ^ (N + 1) / (r - 1)) + C * r ^ N * ∑' m, b m :=
      add_le_add hlowSum hhighSum
    _ = C * (r ^ (N + 1) / (r - 1) + r ^ N * ∑' m, b m) := by ring

end DyadicTransfer

open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

namespace FiniteSFactor

theorem restore_two_primes (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q)
    (hne : P ≠ Q) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (n : ℕ) :
    outsideCoeff ∅ w n =
      (outsideCoeff (insert Q {P}) w n +
        (if Ideal.absNorm Q ∣ n then
          w Q * outsideCoeff (insert Q {P}) w (n / Ideal.absNorm Q) else 0)) +
      (if Ideal.absNorm P ∣ n then
        w P *
