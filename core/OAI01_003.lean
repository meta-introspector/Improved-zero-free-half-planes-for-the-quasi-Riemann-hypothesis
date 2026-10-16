  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχ4 : χ ^ 4 ≠ 1 := canonicalSextic_pow_ne_one P hgood hchar
    (by decide : (4:ℕ) ≠ 0) (by decide : (4:ℕ) < 6)
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hsum :
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) * gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (∑ h : (O ⧸ P)ˣ,
          (((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) h) *
            ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [ShortDraftLocal.nontrivial_fourier_coefficient (χ ^ 4) ψ hχ4 h,
      map_mul]
    simp only [inv_pow, MulChar.mul_apply]
    ring
  dsimp
  rw [hsum, ShortDraftLocal.sextic_fourth_mask χ ψ hχ6 hψ (ε * x)]
  ring

theorem canonical_A5_jzero_active (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        ((χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχ2 : χ ^ 2 ≠ 1 := canonicalSextic_pow_ne_one P hgood hchar
    (by decide : (2:ℕ) ≠ 0) (by decide : (2:ℕ) < 6)
  have hsum :
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
        (∑ h : (O ⧸ P)ˣ,
          ((χ⁻¹) ^ 2) (h : O ⧸ P) *
            ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    have hh : (h : O ⧸ P) ≠ 0 := Units.ne_zero h
    rw [pow_zero, ShortDraftLocal.trivial_fourier_coefficient ψ hψ h,
      ite_eq_right hh, map_mul]
    ring
  dsimp
  rw [hsum, ShortDraftLocal.active_zero_local_row χ ψ hχ2 ε x]
  ring

end ActualEisensteinCubic

namespace PrimitiveTrace

open Complex
open scoped ComplexConjugate
open EisensteinEmbedding ConcreteTraceCRT

private theorem complex_exp_trace_integer {t : ℂ}
    (ht : Complex.exp (2 * Real.pi * Complex.I * t) = 1) :
    ∃ n : ℤ, t = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp ht
  refine ⟨n, ?_⟩
  have hnonzero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero) Complex.I_ne_zero
  apply mul_left_cancel₀ hnonzero
  calc
    (2 * Real.pi * Complex.I : ℂ) * t = n * (2 * Real.pi * Complex.I) := by
      simpa only [mul_assoc] using hn
    _ = (2 * Real.pi * Complex.I : ℂ) * n := by ring

private theorem phase_integer {z : ℂ}
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1) :
    ∃ n : ℤ, z / eisLam + conj (z / eisLam) = n := by
  apply complex_exp_trace_integer
  exact hz

private theorem omega_conj : conj omega3 = omega3 ^ 2 := by
  have hs : omega3 ^ 2 = -omega3 - 1 := by
    linear_combination omega3_sq
  rw [hs]
  unfold omega3
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

private theorem reconstruction (z : ℂ) :
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := by
  have hquad := omega3_sq
  have hl : eisLam ≠ 0 := eisLam_ne_zero
  have hcl : conj eisLam = -eisLam := by
    simp only [eisLam, map_add, map_one, map_mul, map_ofNat, omega_conj]
    linear_combination 2 * hquad
  simp only [map_div₀, map_mul, omega_conj, hcl, div_neg]
  dsimp [eisLam] at *
  field_simp
  linear_combination (conj z) * hquad

private theorem in_coordinate_lattice_of_two_phases (z : ℂ)
    (hz : ShortDraftTrace.breveE (z / eisLam) = 1)
    (hwz : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1) :
    z ∈ coordinateSubring := by
  obtain ⟨b, hb⟩ := phase_integer hz
  obtain ⟨c, hc⟩ := phase_integer hwz
  change ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * omega3
  refine ⟨b + c, b, ?_⟩
  calc
    z = (z / eisLam + conj (z / eisLam)) +
      (omega3 * z / eisLam + conj (omega3 * z / eisLam)) +
      (z / eisLam + conj (z / eisLam)) * omega3 := reconstruction z
    _ = ((b + c : ℤ) : ℂ) + (b : ℂ) * omega3 := by
      rw [hb, hc]
      push_cast
      ring

theorem eisTraceModChar_breveE_ne_one
    (P : Ideal O) [P.IsMaximal] (p : O)
    (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp ≠ 1 := by
  intro hψ
  let ι := eisEmbedding
  let z : ℂ := (ι p)⁻¹
  have hpι : ι p ≠ 0 := eisEmbedding_ne_zero hp
  have hbase1 : ∀ x : O,
      ShortDraftTrace.breveE (ι x / (ι p * eisLam)) = 1 := by
    intro x
    have hpoint := congrArg
      (fun f : AddChar (O ⧸ Ideal.span {p}) ℂ =>
        f (Ideal.Quotient.mk (Ideal.span {p}) x)) hψ
    simpa only [eisTraceModChar, IdealGaussCRT.traceModChar_mk,
      AddChar.one_apply] using hpoint
  have h1 : ShortDraftTrace.breveE (z / eisLam) = 1 := by
    convert hbase1 1 using 1 ; dsimp [z, ι] ; simp ; field_simp
  have hw : ShortDraftTrace.breveE (omega3 * z / eisLam) = 1 := by
    convert hbase1 pb.gen using 1
    · rw [show ι pb.gen = omega3 from embedding_gen omega3 omega3_sq]
      dsimp [z]
      field_simp
  have hz := in_coordinate_lattice_of_two_phases z h1 hw
  obtain ⟨q, hq⟩ := toCoordinateSubring_surjective ⟨z, hz⟩
  have hιq : ι q = z := congrArg Subtype.val hq
  have hpq : p * q = 1 := by
    apply eisEmbedding_injective
    rw [map_mul, map_one, hιq]
    dsimp [z]
    exact mul_inv_cancel₀ hpι
  have hunit : IsUnit p := isUnit_iff_dvd_one.mpr ⟨q, hpq.symm⟩
  have htop : P = ⊤ := by
    rw [hP]
    exact Ideal.span_singleton_eq_top.mpr hunit
  exact (inferInstance : P.IsMaximal).ne_top htop

theorem eisTraceModChar_breveE_primitive
    (P : Ideal O) [P.IsMaximal] (p : O)
    (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp).IsPrimitive := by
  have : (Ideal.span {p}).IsMaximal := hP ▸ inferInstance
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  exact AddChar.IsPrimitive.of_ne_one
    (eisTraceModChar_breveE_ne_one P p hP hp)

end PrimitiveTrace

end

end OAI
end OAIOriginalModule0039

/-! Original module: OAI.NumberTheory.DirichletL.Fourier.PositiveLogProfiles
Source SHA256: 5fd3ab9a7523009f2ea23a36b42f220eee975e8db31b1205dc932509aa21f2e8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0040


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
open ActualEisensteinCubic
open ActualEisensteinCubic
open Filter
open scoped Topology
open ActualEisensteinCubic
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
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace TwoPassProfiles

theorem log_dyad_bound (r : ℝ) (hr₁ : 1 ≤ r) (hr₂ : r ≤ 2) :
    |Real.log r| ≤ Real.log 2 := by
  have hlog0 : 0 ≤ Real.log r := by
    simpa using Real.log_le_log (by positivity : (0 : ℝ) < 1) hr₁
  have hlog2 : Real.log r ≤ Real.log 2 :=
    Real.log_le_log (by linarith) hr₂
  simpa [abs_of_nonneg hlog0] using hlog2

end TwoPassProfiles

namespace ActualEisensteinCubic

theorem A3_primary_unit_eq_one (x : O) (hx : IsUnit x)
    (hprimary : lambda ^ 2 ∣ x - 1) : x = 1 := by
  let v : Oˣ := hx.unit
  have hv : (v : O) = x := hx.unit_spec
  have hvprimary : lambda ^ 2 ∣ (v : O) - 1 := by
    simpa only [hv] using hprimary
  have hunit : v = 1 ∨ v = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) v
    refine ⟨(1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_one] using hvprimary
  rcases hunit with h1 | hneg
  · calc
      x = (v : O) := hv.symm
      _ = 1 := by rw [h1]; rfl
  · have heq : (v : O) - 1 = -(2 : O) := by
      rw [hneg]
      norm_num
    rw [heq] at hvprimary
    have htwo : lambda ^ 2 ∣ (2 : O) := (dvd_neg).mp hvprimary
    exact False.elim (lambda_not_dvd_two
      ((dvd_pow_self lambda (by decide)).trans htwo))

theorem A3_ramified_zero_lower_left
    (a b c d u : O) (hdet : a * d - b * c = 1)
    (hC : c - u * d = 0)
    (hAprimary : lambda ^ 2 ∣ (a - u * b) - 1)
    (hdprimary : lambda ^ 2 ∣ d - 1) :
    a - u * b = 1 ∧ d = 1 ∧ c = u := by
  have hc : c = u * d := sub_eq_zero.mp hC
  have hprod : (a - u * b) * d = 1 := by
    calc
      (a - u * b) * d = a * d - b * c := by rw [hc]; ring
      _ = 1 := hdet
  have hAunit : IsUnit (a - u * b) := IsUnit.of_mul_eq_one d hprod
  have hdunit : IsUnit d :=
    IsUnit.of_mul_eq_one (a - u * b) (by simpa only [mul_comm] using hprod)
  have hA1 := A3_primary_unit_eq_one (a - u * b) hAunit hAprimary
  have hd1 := A3_primary_unit_eq_one d hdunit hdprimary
  exact ⟨hA1, hd1, by simpa only [hd1, mul_one] using hc⟩

theorem A3_unramified_zero_lower_left
    (a b c : O) (hdet : a * 0 - b * c = 1)
    (hcprimary : lambda ^ 2 ∣ c - 1) :
    c = 1 ∧ -b = 1 := by
  have hprod : (-b) * c = 1 := by linear_combination hdet
  have hcunit : IsUnit c :=
    IsUnit.of_mul_eq_one (-b) (by simpa only [mul_comm] using hprod)
  have hc1 := A3_primary_unit_eq_one c hcunit hcprimary
  refine ⟨hc1, ?_⟩
  simpa only [hc1, mul_one] using hprod

end ActualEisensteinCubic

namespace FourierBridge

open scoped ContDiff FourierTransform SchwartzMap

theorem coupled_double_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ : 𝓢(ℝ, ℂ))
    (a₁ a₂ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A₁ A₂ J₁ J₂ : ℕ) :
    ∃ (b₁ b₂ : ℝ → ℝ → ℂ) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 ≤ R₁ → 0 ≤ R₂ →
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
            F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
          ∫ t₁ : ℝ, (∫ t₂ : ℝ,
            (∏ j : ι, W j (y j)) *
              logPhase t₁ (∑ j : ι, a₁ j * y j) *
              logPhase t₂ (∑ j : ι, a₂ j * y j) *
              b₂ R₂ t₂) * b₁ R₁ t₁) ∧
        ((1 + R₁) ^ A₁ * (1 + R₂) ^ A₂) *
          ((∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ R₁ t₁‖) *
           (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ R₂ t₂‖)) ≤ C := by
  classical
  obtain ⟨b₁, C₁, hC₁, h₁⟩ :=
    coupled_log_separation_schwartz W F₁ a₁ M hM hWwindow A₁ J₁
  obtain ⟨b₂, C₂, hC₂, h₂⟩ :=
    coupled_log_separation_schwartz W F₂ a₂ M hM hWwindow A₂ J₂
  refine ⟨b₁, b₂, C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨hsep₁, hbound₁⟩ := h₁ R₁ hR₁
  obtain ⟨hsep₂, hbound₂⟩ := h₂ R₂ hR₂
  constructor
  · intro y
    let P : ℂ := ∏ j : ι, W j (y j)
    let s₁ : ℝ := ∑ j : ι, a₁ j * y j
    let s₂ : ℝ := ∑ j : ι, a₂ j * y j
    let Z₁ : ℂ := F₁ (R₁ * Real.exp s₁)
    let Z₂ : ℂ := F₂ (R₂ * Real.exp s₂)
    have hphase₁ (t : ℝ) :
        (∏ j : ι, W j (y j) * logPhase t (a₁ j * y j)) =
          P * logPhase t s₁ := by
      rw [Finset.prod_mul_distrib]
      simp only [P, s₁]
      congr 1
      simpa using (logPhase_sum (Finset.univ : Finset ι) t
        (fun j => a₁ j * y j)).symm
    have hphase₂ (t : ℝ) :
        (∏ j : ι, W j (y j) * logPhase t (a₂ j * y j)) =
          P * logPhase t s₂ := by
      rw [Finset.prod_mul_distrib]
      simp only [P, s₂]
      congr 1
      simpa using (logPhase_sum (Finset.univ : Finset ι) t
        (fun j => a₂ j * y j)).symm
    have hsep₁' : P * Z₁ =
        ∫ t₁ : ℝ, (P * logPhase t₁ s₁) * b₁ R₁ t₁ := by
      simpa only [P, Z₁, s₁, hphase₁] using hsep₁ y
    have hsep₂' : P * Z₂ =
        ∫ t₂ : ℝ, (P * logPhase t₂ s₂) * b₂ R₂ t₂ := by
      simpa only [P, Z₂, s₂, hphase₂] using hsep₂ y
    have hinner (t₁ : ℝ) :
        P * logPhase t₁ s₁ * Z₂ =
          ∫ t₂ : ℝ,
            (P * logPhase t₁ s₁ * logPhase t₂ s₂) *
              b₂ R₂ t₂ := by
      calc
        P * logPhase t₁ s₁ * Z₂ =
            logPhase t₁ s₁ * (P * Z₂) := by ring
        _ = logPhase t₁ s₁ *
            (∫ t₂ : ℝ, (P * logPhase t₂ s₂) * b₂ R₂ t₂) := by
              rw [hsep₂']
        _ = ∫ t₂ : ℝ,
            logPhase t₁ s₁ *
              ((P * logPhase t₂ s₂) * b₂ R₂ t₂) := by
                rw [integral_const_mul]
        _ = ∫ t₂ : ℝ,
            (P * logPhase t₁ s₁ * logPhase t₂ s₂) *
              b₂ R₂ t₂ := by
                apply integral_congr_ae
                filter_upwards [] with t₂
                ring
    change P * Z₁ * Z₂ = _
    calc
      P * Z₁ * Z₂ =
          (∫ t₁ : ℝ, (P * logPhase t₁ s₁) * b₁ R₁ t₁) * Z₂ := by
            rw [hsep₁']
      _ = ∫ t₁ : ℝ,
          ((P * logPhase t₁ s₁) * b₁ R₁ t₁) * Z₂ := by
            rw [integral_mul_const]
      _ = ∫ t₁ : ℝ,
          (P * logPhase t₁ s₁ * Z₂) * b₁ R₁ t₁ := by
            apply integral_congr_ae
            filter_upwards [] with t₁
            ring
      _ = ∫ t₁ : ℝ, (∫ t₂ : ℝ,
          (P * logPhase t₁ s₁ * logPhase t₂ s₂) *
            b₂ R₂ t₂) * b₁ R₁ t₁ := by
            apply integral_congr_ae
            filter_upwards [] with t₁
            rw [hinner t₁]
  · let I₁ : ℝ := ∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ R₁ t₁‖
    let I₂ : ℝ := ∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ R₂ t₂‖
    have hI₁ : 0 ≤ I₁ := by
      dsimp [I₁]
      apply integral_nonneg
      intro t
      positivity
    have hI₂ : 0 ≤ I₂ := by
      dsimp [I₂]
      apply integral_nonneg
      intro t
      positivity
    have hP₁ : 0 ≤ (1 + R₁) ^ A₁ := pow_nonneg (by linarith) _
    have hP₂ : 0 ≤ (1 + R₂) ^ A₂ := pow_nonneg (by linarith) _
    have hmul : ((1 + R₁) ^ A₁ * I₁) *
        ((1 + R₂) ^ A₂ * I₂) ≤ C₁ * C₂ := by
      exact mul_le_mul hbound₁ hbound₂
        (mul_nonneg hP₂ hI₂) hC₁
    simpa only [I₁, I₂, mul_comm, mul_left_comm, mul_assoc] using hmul

end FourierBridge

namespace InitialMeanSquareProfile

theorem dual_profile
    (H Z B F d s h v₁ v₂ : ℝ)
    (hH : H ≠ 0) (hZ : Z ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hd : d ≠ 0) (hs : s ≠ 0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
    H * h / (d * ((s * v₁) * (s * v₂))) =
      ((d * h) / (Z ^ 2 / (H * B ^ 2))) /
        (((d * s) / F) ^ 2 *
          (v₁ / (Z / (B * F))) * (v₂ / (Z / (B * F)))) := by
  field_simp

end InitialMeanSquareProfile

open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap

namespace LocalLogFourier

noncomputable def eulerDeriv (F : ℝ → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  iteratedDeriv j (fun t : ℝ => F (x * Real.exp t)) 0

theorem iteratedDeriv_log_eq_euler (F : ℝ → ℂ) (R s : ℝ) (j : ℕ) :
    iteratedDeriv j (fun z : ℝ => F (R * Real.exp z)) s =
      eulerDeriv F j (R * Real.exp s) := by
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have hshift : (fun t : ℝ => F ((R * Real.exp s) * Real.exp t)) =
      (fun t : ℝ => G (s + t)) := by
    funext t
    simp only [G, Real.exp_add, mul_assoc]
  unfold eulerDeriv
  rw [hshift]
  simpa [G] using (congrArg (fun h : ℝ → ℂ => h 0)
    (iteratedDeriv_comp_const_add j G s)).symm

theorem euler_two_regime_bound
    (F : ℝ → ℂ) (A K : ℕ) (Csmall Clarge : ℝ)
    (hCs : 0 ≤ Csmall) (hCl : 0 ≤ Clarge)
    (hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖eulerDeriv F i x‖ ≤ Csmall)
    (hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖eulerDeriv F i x‖ ≤ Clarge)
    (i : ℕ) (hi : i ≤ K) (x : ℝ) (hx : 0 < x) :
    (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤
      (2 : ℝ) ^ A * (Csmall + Clarge) := by
  by_cases hsmallx : x ≤ 1
  · have hpow : (1 + x) ^ A ≤ (2 : ℝ) ^ A := by gcongr; linarith
    calc
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤
        (2 : ℝ) ^ A * ‖eulerDeriv F i x‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ A * Csmall :=
        mul_le_mul_of_nonneg_left (hsmall i hi x hx hsmallx) (by positivity)
      _ ≤ (2 : ℝ) ^ A * (Csmall + Clarge) := by gcongr; linarith
  · have hx1 : 1 ≤ x := le_of_lt (lt_of_not_ge hsmallx)
    have hpow : (1 + x) ^ A ≤ ((2 : ℝ) * x) ^ A := by
      gcongr
      linarith
    calc
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤
        ((2 : ℝ) * x) ^ A * ‖eulerDeriv F i x‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = (2 : ℝ) ^ A * (x ^ A * ‖eulerDeriv F i x‖) := by rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ A * Clarge :=
        mul_le_mul_of_nonneg_left (hlarge i hi x hx1) (by positivity)
      _ ≤ (2 : ℝ) ^ A * (Csmall + Clarge) := by gcongr; linarith

noncomputable def positiveLogProfile
    (V F : ℝ → ℂ) (R : ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) : 𝓢(ℝ, ℂ) := by
  let arg : ℝ → ℝ := fun s => R * Real.exp s
  have harg : ContDiff ℝ ∞ arg := by
    dsimp [arg]
    fun_prop
  have hargpos : ∀ s, arg s ∈ Set.Ioi (0 : ℝ) := by
    intro s
    exact mul_pos hR (Real.exp_pos _)
  have hG : ContDiff ℝ ∞ (fun s => F (arg s)) := by
    simpa only [Function.comp_def] using hFpos.comp_contDiff harg hargpos
  have hH : ContDiff ℝ ∞ (fun s => V s * F (arg s)) := hVs.mul hG
  have hc : HasCompactSupport (fun s => V s * F (arg s)) := hVc.mul_right
  exact hc.toSchwartzMap hH

@[simp] theorem positiveLogProfile_apply
    (V F : ℝ → ℂ) (R s : ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) :
    positiveLogProfile V F R hVc hVs hFpos hR s =
      V s * F (R * Real.exp s) := rfl

theorem positive_log_separation
    (V F : ℝ → ℂ) (R s : ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) :
    V s * F (R * Real.exp s) =
      ∫ t : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ t s) * Complex.I) *
        (𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t := by
  rw [← positiveLogProfile_apply V F R s hVc hVs hFpos hR]
  exact FourierBridge.schwartz_log_inversion _ _

theorem euler_derivative_scale
    (F : ℝ → ℂ) (R s m CF : ℝ) (A i : ℕ)
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hms : m ≤ Real.exp s)
    (hF : (1 + R * Real.exp s) ^ A *
      ‖eulerDeriv F i (R * Real.exp s)‖ ≤ CF) :
    m ^ A * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ i (fun z : ℝ => F (R * Real.exp z)) s‖ ≤ CF := by
  have hscale : m * (1 + R) ≤ 1 + R * Real.exp s := by
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hms)]
  have hpow : (m * (1 + R)) ^ A ≤
      (1 + R * Real.exp s) ^ A := by gcongr
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_log_eq_euler]
  calc
    m ^ A * (1 + R) ^ A * ‖eulerDeriv F i (R * Real.exp s)‖ =
      (m * (1 + R)) ^ A * ‖eulerDeriv F i (R * Real.exp s)‖ := by rw [mul_pow]
    _ ≤ (1 + R * Real.exp s) ^ A *
      ‖eulerDeriv F i (R * Real.exp s)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ CF := hF

theorem positive_log_product_derivative_bound
    (V F : ℝ → ℂ) (R m CW CF : ℝ) (A n : ℕ)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s)
    (hEuler : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF)
    (s : ℝ) :
    m ^ A * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ n
        (fun z : ℝ => V z * F (R * Real.exp z)) s‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF := by
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp z) := by fun_prop
  have hG : ContDiff ℝ ∞ G := by
    dsimp [G]
    simpa only [Function.comp_def] using
      hFpos.comp_contDiff harg (by intro z; exact mul_pos hR (Real.exp_pos _))
  have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (by simp)
  have hS : 0 ≤ m ^ A * (1 + R) ^ A := by positivity
  calc
    m ^ A * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ n (fun z : ℝ => V z * F (R * Real.exp z)) s‖ ≤
      (m ^ A * (1 + R) ^ A) *
        (∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
            ‖iteratedFDeriv ℝ (n - i) G s‖) :=
      mul_le_mul_of_nonneg_left (by simpa [G] using hprod) hS
    _ = ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
        ((m ^ A * (1 + R) ^ A) * ‖iteratedFDeriv ℝ (n - i) G s‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      by_cases hVi : ‖iteratedFDeriv ℝ i V s‖ = 0
      · simp [hVi]
        positivity
      have hms := hwindow s ⟨i, hi', hVi⟩
      have hx : 0 < R * Real.exp s := mul_pos hR (Real.exp_pos _)
      have hGi := euler_derivative_scale F R s m CF A (n - i)
        hR hm hm1 hms (hEuler (n - i) (Nat.sub_le n i) _ hx)
      have hVi' := hVderiv i hi' s
      gcongr

theorem positive_log_uniform_seminorm
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A n k : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    m ^ A * (1 + R) ^ A *
      (SchwartzMap.seminorm ℝ k n)
        (positiveLogProfile V F R hVc hVs hFpos hR) ≤
      Lwin ^ k *
        (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF) := by
  let g := positiveLogProfile V F R hVc hVs hFpos hR
  let S := m ^ A * (1 + R) ^ A
  let C := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF
  have hS : 0 < S := by dsimp [S]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hLC : 0 ≤ Lwin ^ k * C := by positivity
  have hgeq : (g : ℝ → ℂ) =
      fun z => V z * F (R * Real.exp z) := by
    funext z
    exact positiveLogProfile_apply V F R z hVc hVs hFpos hR
  have hpoint (s : ℝ) :
      S * (|s| ^ k * ‖iteratedDeriv n g s‖) ≤ Lwin ^ k * C := by
    by_cases hactive : ∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0
    · obtain ⟨hms, habs⟩ := hwindow s hactive
      have hraw := positive_log_product_derivative_bound
        V F R m CW CF A n hVs hFpos hR hm hm1
        hCW hCF hVderiv
        (by intro z hz; exact (hwindow z hz).1)
        hEuler s
      have hnorm : S * ‖iteratedDeriv n g s‖ ≤ C := by
        rw [hgeq]
        simpa [S, C, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hraw
      calc
        S * (|s| ^ k * ‖iteratedDeriv n g s‖) =
          |s| ^ k * (S * ‖iteratedDeriv n g s‖) := by ring
        _ ≤ |s| ^ k * C :=
          mul_le_mul_of_nonneg_left hnorm (pow_nonneg (abs_nonneg _) _)
        _ ≤ Lwin ^ k * C :=
          mul_le_mul_of_nonneg_right (by gcongr) hC
    · have hzero (i : ℕ) (hi : i ≤ n) :
          ‖iteratedFDeriv ℝ i V s‖ = 0 := by
        by_contra hne
        exact hactive ⟨i, hi, hne⟩
      have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp z) := by fun_prop
      have hG : ContDiff ℝ ∞ (fun z : ℝ => F (R * Real.exp z)) := by
        simpa only [Function.comp_def] using
          hFpos.comp_contDiff harg (by intro z; exact mul_pos hR (Real.exp_pos _))
      have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (by simp)
      have hsumzero :
          (∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
              ‖iteratedFDeriv ℝ (n - i)
                (fun z : ℝ => F (R * Real.exp z)) s‖) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hzero i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
        ring
      have hnormzero : ‖iteratedDeriv n g s‖ = 0 := by
        have hzero' :
            ‖iteratedFDeriv ℝ n
              (fun z : ℝ => V z * F (R * Real.exp z)) s‖ = 0 :=
          le_antisymm (hprod.trans_eq hsumzero) (norm_nonneg _)
        rw [hgeq]
        simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hzero'
      simp [hnormzero, hLC]
  have hsemi : (SchwartzMap.seminorm ℝ k n) g ≤ Lwin ^ k * C / S := by
    apply SchwartzMap.seminorm_le_bound' ℝ k n g (div_nonneg hLC hS.le)
    intro s
    exact (le_div_iff₀ hS).mpr
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hpoint s)
  calc
    S * (SchwartzMap.seminorm ℝ k n) g ≤ S * (Lwin ^ k * C / S) :=
      mul_le_mul_of_nonneg_left hsemi hS.le
    _ = Lwin ^ k * C := by field_simp

noncomputable def derivativeConstant (n : ℕ) (CW CF : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * CW * CF

noncomputable def momentConstant (K : ℕ) (Lwin CW CF : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1),
    (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
      derivativeConstant n CW CF

theorem derivativeConstant_nonneg (n : ℕ) (CW CF : ℝ)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ derivativeConstant n CW CF := by
  unfold derivativeConstant
  positivity

theorem momentConstant_nonneg (K : ℕ) (Lwin CW CF : ℝ)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ momentConstant K Lwin CW CF := by
  unfold momentConstant
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (by positivity)
    (derivativeConstant_nonneg n CW CF hCW hCF)

theorem momentConstant_dominates (K n : ℕ) (Lwin CW CF : ℝ)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K) :
    (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
      derivativeConstant n CW CF ≤ momentConstant K Lwin CW CF := by
  unfold momentConstant
  apply Finset.single_le_sum
    (f := fun i : ℕ =>
      (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
        derivativeConstant i CW CF)
    (a := n)
  · intro i hi
    exact mul_nonneg (by positivity)
      (derivativeConstant_nonneg i CW CF hCW hCF)
  · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)

theorem positive_log_source_pair
    (V F : ℝ → ℂ) (R m Lwin CW CF C : ℝ) (A K n : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K)
    (hVderiv : ∀ i ≤ K, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF)
    (hCbound : ∀ j ≤ K,
      (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
        derivativeConstant j CW CF ≤ C) :
    (m ^ A * (1 + R) ^ A) *
      ((SchwartzMap.seminorm ℝ 0 n)
          (positiveLogProfile V F R hVc hVs hFpos hR) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n)
          (positiveLogProfile V F R hVc hVs hFpos hR)) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  let D : ℝ := derivativeConstant n CW CF
  let g := positiveLogProfile V F R hVc hVs hFpos hR
  have hVderiv_n : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW := by
    intro i hi s
    exact hVderiv i (hi.trans hn) s
  have hwindow_n : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin := by
    intro s hs
    obtain ⟨i, hi, hnonzero⟩ := hs
    exact hwindow s ⟨i, hi.trans hn, hnonzero⟩
  have hEuler_n : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF := by
    intro i hi x hx
    exact hEuler i (hi.trans hn) x hx
  have hzero := positive_log_uniform_seminorm
    V F R m Lwin CW CF A n 0 hVc hVs hFpos hR hm hm1
    hL hCW hCF hVderiv_n hwindow_n hEuler_n
  have hp := positive_log_uniform_seminorm
    V F R m Lwin CW CF A n p hVc hVs hFpos hR hm hm1
    hL hCW hCF hVderiv_n hwindow_n hEuler_n
  calc
    (m ^ A * (1 + R) ^ A) *
        ((SchwartzMap.seminorm ℝ 0 n) g +
          (SchwartzMap.seminorm ℝ p n) g) =
        (m ^ A * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ 0 n) g +
        (m ^ A * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ p n) g := by ring
    _ ≤ D + Lwin ^ p * D := by
      apply add_le_add
      · simpa [D, derivativeConstant, g] using hzero
      · simpa [D, derivativeConstant, g, p] using hp
    _ = (1 + Lwin ^ p) * D := by ring
    _ ≤ C := by simpa [D, p] using hCbound n hn

theorem positive_log_fourier_moment
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    (m ^ A * (1 + R) ^ A) *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t‖) ≤
      (2 : ℝ) ^ J *
        (FourierBridge.coefficientMomentBound 0
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF) +
         FourierBridge.coefficientMomentBound J
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF)) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let C := momentConstant K Lwin CW CF
  have hC : 0 ≤ C := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  apply FourierBridge.uniform_fourier_one_plus_moment _ J _ C (by positivity) hC
  intro n hn
  exact positive_log_source_pair V F R m Lwin CW CF C A K n
    hVc hVs hFpos hR hm hm1 hL hCW hCF
    (by simpa [K] using hn)
    (by simpa [K] using hVderiv)
    (by simpa [K] using hwindow)
    (by simpa [K] using hEuler)
    (by
      intro j hj
      simpa [C] using momentConstant_dominates K j Lwin CW CF hL hCW hCF hj)

theorem positive_log_fourier_bound
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    (1 + R) ^ A *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t‖) ≤
      ((2 : ℝ) ^ J *
        (FourierBridge.coefficientMomentBound 0
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF) +
         FourierBridge.coefficientMomentBound J
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF))) / m ^ A := by
  have hpow : 0 < m ^ A := pow_pos hm _
  apply (le_div_iff₀ hpow).mpr
  have hbase := positive_log_fourier_moment V F R m Lwin CW CF A J
    hVc hVs hFpos hR hm hm1 hL hCW hCF hVderiv hwindow hEuler
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbase

theorem coupled_positive_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F V : ℝ → ℂ) (R : ℝ)
    (a y : ι → ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R)
    (hactive : (∏ j : ι, W j (y j)) ≠ 0 →
      V (∑ j : ι, a j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F (R * Real.exp (∑ j : ι, a j * y j)) =
      ∫ t : ℝ,
        (∏ j : ι, W j (y j) *
          FourierBridge.logPhase t (a j * y j)) *
          (𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t := by
  classical
  let s : ℝ := ∑ j : ι, a j * y j
  let P : ℂ := ∏ j : ι, W j (y j)
  let b := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  have hsep : V s * F (R * Real.exp s) =
      ∫ t : ℝ, FourierBridge.logPhase t s * b t := by
    calc
      V s * F (R * Real.exp s) =
          ∫ t : ℝ, Complex.exp
            (↑(2 * Real.pi * inner ℝ t s) * Complex.I) * b t := by
        simpa [b] using
          (positive_log_separation V F R s hVc hVs hFpos hR)
      _ = ∫ t : ℝ, FourierBridge.logPhase t s * b t := by
        apply integral_congr_ae
        filter_upwards [] with t
        congr 1
        simp only [FourierBridge.logPhase, Real.inner_apply]
        congr 1
        push_cast
        ring
  have hcut : P * F (R * Real.exp s) =
      P * (V s * F (R * Real.exp s)) := by
    by_cases hP : P = 0
    · simp [hP]
    · rw [hactive (by simpa [P, s] using hP)]
      ring
  calc
    P * F (R * Real.exp s) = P * (V s * F (R * Real.exp s)) := hcut
    _ = P * (∫ t : ℝ, FourierBridge.logPhase t s * b t) := by rw [hsep]
    _ = ∫ t : ℝ, P * (FourierBridge.logPhase t s * b t) := by
      rw [integral_const_mul]
    _ = ∫ t : ℝ,
          (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a j * y j)) * b t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show FourierBridge.logPhase t s =
          ∏ j : ι, FourierBridge.logPhase t (a j * y j) by
        simpa [s] using FourierBridge.logPhase_sum
          (Finset.univ : Finset ι) t (fun j => a j * y j)]
      rw [Finset.prod_mul_distrib]
      simp only [P]
      ring

theorem coupled_positive_log_separation_uniform
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (A J : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : ℝ → ℂ,
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let Lwin : ℝ := T + 1
  let m : ℝ := Real.exp (-Lwin)
  have hL : 0 ≤ Lwin := by dsimp [Lwin]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -Lwin ≤ 0 by linarith))
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let P : ℝ := momentConstant K Lwin CW CF
  let B : ℝ := (2 : ℝ) ^ J *
    (FourierBridge.coefficientMomentBound 0 P +
      FourierBridge.coefficientMomentBound J P)
  let C : ℝ := B / m ^ A
  have hP : 0 ≤ P := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (FourierBridge.coefficientMomentBound_nonneg 0 P hP)
        (FourierBridge.coefficientMomentBound_nonneg J P hP))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR
  let b : ℝ → ℂ := fun t =>
    (𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t
  refine ⟨b, ?_, ?_⟩
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      FourierBridge.coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_positive_log_separation W F V R a y
      hVc hVs hFpos hR hactive
  · have hwindow' : ∀ s,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
          m ≤ Real.exp s ∧ |s| ≤ Lwin := by
      intro s hs
      exact ⟨(hwindow s hs).1, (hwindow s hs).2.2⟩
    have hbound := positive_log_fourier_bound V F R m Lwin CW CF A J
      hVc hVs hFpos hR hm hm1 hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa only [K] using hwindow')
      (by simpa [K] using hEuler)
    simpa [C, B, P, b, K, Lwin, m] using hbound

theorem coupled_positive_log_separation_two_regimes
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (A J : ℕ) (Csmall Clarge : ℝ)
    (hCs : 0 ≤ Csmall) (hCl : 0 ≤ Clarge)
    (hsmall : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x → x ≤ 1 →
        ‖eulerDeriv F i x‖ ≤ Csmall)
    (hlarge : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 1 ≤ x →
        x ^ A * ‖eulerDeriv F i x‖ ≤ Clarge) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : ℝ → ℂ,
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  apply coupled_positive_log_separation_uniform W F a M
    hM hWwindow hFpos A J
    ((2 : ℝ) ^ A * (Csmall + Clarge))
    (by positivity)
  intro i hi x hx
  exact euler_two_regime_bound F A
    (J + (volume : Measure ℝ).integrablePower)
    Csmall Clarge hCs hCl hsmall hlarge i hi x hx

theorem coupled_double_positive_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ : ℝ → ℂ)
    (a₁ a₂ M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos₁ : ContDiffOn ℝ ∞ F₁ (Set.Ioi 0))
    (hFpos₂ : ContDiffOn ℝ ∞ F₂ (Set.Ioi 0))
    (A₁ A₂ J₁ J₂ : ℕ) (CF₁ CF₂ : ℝ)
    (hCF₁ : 0 ≤ CF₁) (hCF₂ : 0 ≤ CF₂)
    (hEuler₁ : ∀ i ≤ J₁ + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A₁ * ‖eulerDeriv F₁ i x‖ ≤ CF₁)
    (hEuler₂ : ∀ i ≤ J₂ + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A₂ * ‖eulerDeriv F₂ i x‖ ≤ CF₂) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ →
        ∃ (b₁ b₂ : ℝ → ℂ),
          (∀ y : ι → ℝ,
            (∏ j : ι, W j (y j)) *
              F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
              F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
            ∫ t₁ : ℝ, (∫ t₂ : ℝ,
              (∏ j : ι, W j (y j)) *
                FourierBridge.logPhase t₁ (∑ j : ι, a₁ j * y j) *
                FourierBridge.logPhase t₂ (∑ j : ι, a₂ j * y j) *
                b₂ t₂) * b₁ t₁) ∧
          ((1 + R₁) ^ A₁ * (1 + R₂) ^ A₂) *
            ((∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) *
             (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖)) ≤ C := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ :=
    coupled_positive_log_separation_uniform W F₁ a₁ M
      hM hWwindow hFpos₁ A₁ J₁ CF₁ hCF₁ hEuler₁
  obtain ⟨C₂, hC₂, h₂⟩ :=
    coupled_positive_log_separation_uniform W F₂ a₂ M
      hM hWwindow hFpos₂ A₂ J₂ CF₂ hCF₂ hEuler₂
  refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, ?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₁, hsep₁, hbound₁⟩ := h₁ R₁ hR₁
  obtain ⟨b₂, hsep₂, hbound₂⟩ := h₂ R₂ hR₂
  refine ⟨b₁, b₂, ?_, ?_⟩
  · intro y
    let P : ℂ := ∏ j : ι, W j (y j)
    let s₁ : ℝ := ∑ j : ι, a₁ j * y j
    let s₂ : ℝ := ∑ j : ι, a₂ j * y j
    let Z₁ : ℂ := F₁ (R₁ * Real.exp s₁)
    let Z₂ : ℂ := F₂ (R₂ * Real.exp s₂)
    have hphase₁ (t : ℝ) :
        (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a₁ j * y j)) =
          P * FourierBridge.logPhase t s₁ := by
      rw [Finset.prod_mul_distrib]
      simp only [P, s₁]
      congr 1
      simpa using (FourierBridge.logPhase_sum (Finset.univ : Finset ι) t
        (fun j => a₁ j * y j)).symm
    have hphase₂ (t : ℝ) :
        (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a₂ j * y j)) =
          P * FourierBridge.logPhase t s₂ := by
      rw [Finset.prod_mul_distrib]
      simp only [P, s₂]
      congr 1
      simpa using (FourierBridge.logPhase_sum (Finset.univ : Finset ι) t
        (fun j => a₂ j * y j)).symm
    have hsep₁' : P * Z₁ =
        ∫ t₁ : ℝ, (P * FourierBridge.logPhase t₁ s₁) * b₁ t₁ := by
      simpa only [P, Z₁, s₁, hphase₁] using hsep₁ y
    have hsep₂' : P * Z₂ =
        ∫ t₂ : ℝ, (P * FourierBridge.logPhase t₂ s₂) * b₂ t₂ := by
      simpa only [P, Z₂, s₂, hphase₂] using hsep₂ y
    have hinner (t₁ : ℝ) :
        P * FourierBridge.logPhase t₁ s₁ * Z₂ =
          ∫ t₂ : ℝ,
            (P * FourierBridge.logPhase t₁ s₁ * FourierBridge.logPhase t₂ s₂) *
              b₂ t₂ := by
      calc
        P * FourierBridge.logPhase t₁ s₁ * Z₂ =
            FourierBridge.logPhase t₁ s₁ * (P * Z₂) := by ring
        _ = FourierBridge.logPhase t₁ s₁ *
            (∫ t₂ : ℝ, (P * FourierBridge.logPhase t₂ s₂) * b₂ t₂) := by
              rw [hsep₂']
        _ = ∫ t₂ : ℝ,
            FourierBridge.logPhase t₁ s₁ *
              ((P * FourierBridge.logPhase t₂ s₂) * b₂ t₂) := by
                rw [integral_const_mul]
        _ = ∫ t₂ : ℝ,
            (P * FourierBridge.logPhase t₁ s₁ * FourierBridge.logPhase t₂ s₂) *
              b₂ t₂ := by
                apply integral_congr_ae
                filter_upwards [] with t₂
                ring
    change P * Z₁ * Z₂ = _
    calc
      P * Z₁ * Z₂ =
          (∫ t₁ : ℝ, (P * FourierBridge.logPhase t₁ s₁) * b₁ t₁) * Z₂ := by
            rw [hsep₁']
      _ = ∫ t₁ : ℝ,
          ((P * FourierBridge.logPhase t₁ s₁) * b₁ t₁) * Z₂ := by
            rw [integral_mul_const]
      _ = ∫ t₁ : ℝ,
          (P * FourierBridge.logPhase t₁ s₁ * Z₂) * b₁ t₁ := by
            apply integral_congr_ae
            filter_upwards [] with t₁
            ring
      _ = ∫ t₁ : ℝ, (∫ t₂ : ℝ,
          (P * FourierBridge.logPhase t₁ s₁ * FourierBridge.logPhase t₂ s₂) *
            b₂ t₂) * b₁ t₁ := by
            apply integral_congr_ae
            filter_upwards [] with t₁
            rw [hinner t₁]
  · let I₁ : ℝ := ∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖
    let I₂ : ℝ := ∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖
    have hI₁ : 0 ≤ I₁ := by
      dsimp [I₁]
      apply integral_nonneg
      intro t
      positivity
    have hI₂ : 0 ≤ I₂ := by
      dsimp [I₂]
      apply integral_nonneg
      intro t
      positivity
    have hP₁ : 0 ≤ (1 + R₁) ^ A₁ := pow_nonneg (by linarith) _
    have hP₂ : 0 ≤ (1 + R₂) ^ A₂ := pow_nonneg (by linarith) _
    have hmul : ((1 + R₁) ^ A₁ * I₁) *
        ((1 + R₂) ^ A₂ * I₂) ≤ C₁ * C₂ := by
      exact mul_le_mul hbound₁ hbound₂
        (mul_nonneg hP₂ hI₂) hC₁
    simpa only [I₁, I₂, mul_comm, mul_left_comm, mul_assoc] using hmul

end LocalLogFourier

end

end OAI
end OAIOriginalModule0040

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization
Source SHA256: 39534abc411210d7f2e8736994a72cf46abda4e5b937dd2f507a00a6bd96324a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0041


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

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

theorem cubicGauss_normalized_cube_breveE
    (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1) :
    (gaussSum ((cubicChar P hgood).ringHomComp eisEmbedding)
      (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by
  subst P
  exact cubicGauss_normalized_cube_eis (Ideal.span {p}) hgood p rfl hprimary
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp)

end

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def breveGamma2 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood ^ 2)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

theorem canonicalSextic_pow_two (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 2 =
      (cubicChar P hgood).ringHomComp eisEmbedding := by
  change ((sexticChar P hgood).ringHomComp eisEmbedding) ^ 2 = _
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).1]

theorem breveGamma2_cube (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) (hprimary : lambda ^ 2 ∣ p - 1) :
    (breveGamma2 P hgood p hP hp) ^ 3 =
      -(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ) := by
  unfold breveGamma2
  rw [canonicalSextic_pow_two]
  exact cubicGauss_normalized_cube_breveE P hgood p hP hp hprimary

end ActualEisensteinCubic

namespace ShortDraftLocal

open AddChar MulChar

theorem general_inversion_gauss {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (a : F) :
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by
  classical
  calc
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) (y⁻¹)) *
          ψ (a * (y : F)) := by
            apply Fintype.sum_equiv (Equiv.inv Fˣ)
            intro y
            simp
    _ = ∑ y : Fˣ, (χ ^ (j + 2)) y * ψ (a * (y : F)) := by
      congr 1
      funext y
      congr 1
      have hchar : (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2)⁻¹) = χ ^ (j + 2) := by group
      rw [← hchar, MulChar.inv_apply']
    _ = gaussSum (χ ^ (j + 2)) (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]

theorem sextic_fourier_theta_row_general
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
    (hχj : χ ^ j ≠ 1) (hχj2 : χ ^ (j + 2) ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        (∑ h : Fˣ,
          (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
            ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient (χ ^ j) ψ hχj h, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, general_inversion_gauss χ ψ j (ε * x),
    gaussSum_mulShift_any (χ ^ (j + 2)) ψ hχj2 (ε * x), map_mul]
  ring

end ShortDraftLocal

namespace ActualEisensteinCubic

section

open AddChar MulChar

theorem canonical_A5_nonexceptional (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ)
    (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ j) t * ψ (-(h * t))) *
          (((χ⁻¹) ^ 2) (σ * h)) *
          ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := canonicalSextic P hgood
  have hχj : χ ^ j ≠ 1 :=
    canonicalSextic_pow_ne_one P hgood hchar hj0 hj6
  have hχj2 : χ ^ (j + 2) ≠ 1 := by
    have hcases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (3:ℕ) ≠ 0) (by decide : (3:ℕ) < 6)
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (4:ℕ) ≠ 0) (by decide : (4:ℕ) < 6)
    · exact canonicalSextic_pow_ne_one P hgood hchar
        (by decide : (5:ℕ) ≠ 0) (by decide : (5:ℕ) < 6)
    · have hχ1 : χ ≠ 1 := by
        simpa only [pow_one, χ] using canonicalSextic_pow_ne_one P hgood hchar
          (by decide : (1:ℕ) ≠ 0) (by decide : (1:ℕ) < 6)
      have hχ7 : χ ^ (5 + 2) = χ := by
        calc
          χ ^ (5 + 2) = χ ^ (6 + 1) := by congr 1
          _ = χ ^ 6 * χ := by rw [pow_add, pow_one]
          _ = χ := by rw [canonicalSextic_pow_six P hgood, one_mul]
      rw [hχ7]
      exact hχ1
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.sextic_fourier_theta_row_general χ ψ j hχj hχj2 σ ε x

end

open ConcreteTraceCRT PrimitiveTrace

theorem canonical_A5_jone_breveE (p : O) (hp : p ≠ 0)
    [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (σ : (O ⧸ Ideal.span {p})ˣ) (ε x : O ⧸ Ideal.span {p}) :
    let P := Ideal.span {p}
    let χ := canonicalSextic P hgood
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ * (χ ^ 3) ε) *
      (χ ^ 3) x := by
  exact canonical_A5_jone (Ideal.span {p}) hgood hchar
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) σ ε x

theorem canonical_A5_jfour_breveE (p : O) (hp : p ≠ 0)
    [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (σ : (O ⧸ Ideal.span {p})ˣ) (ε x : O ⧸ Ideal.span {p}) :
    let P := Ideal.span {p}
    let χ := canonicalSextic P hgood
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1)) := by
  exact canonical_A5_jfour (Ideal.span {p}) hgood hchar
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (eisTraceModChar_breveE_ne_one (Ideal.span {p}) p rfl hp) σ ε x

theorem canonical_A5_jzero_active_breveE (p : O) (hp : p ≠ 0)
    [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (σ : (O ⧸ Ideal.span {p})ˣ) (ε x : O ⧸ Ideal.span {p}) :
    let P := Ideal.span {p}
    let χ := canonicalSextic P hgood
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 0) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      -(((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        ((χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x)) := by
  exact canonical_A5_jzero_active (Ideal.span {p}) hgood hchar
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp)
    (eisTraceModChar_breveE_ne_one (Ideal.span {p}) p rfl hp) σ ε x

end ActualEisensteinCubic

namespace AnalyticBridge

theorem first_poisson_local_ratio_bound
    (c E A1 A2 s J2 J B : ℝ)
    (_hc : 0 ≤ c) (_hE : 0 ≤ E)
    (_hA1 : 0 < A1) (_hA2 : 0 < A2)
    (hs : 0 ≤ s) (hJ2 : 1 ≤ J2) (_hB : 0 ≤ B)
    (hJ : J = s * J2) (hJpos : 0 < J)
    (hJdyad : J ≤ B ^ 2)
    (hlocal : c * E / (A1 * A2) = s / J2 ^ 2) :
    c * E / (A1 * A2) ≤ B ^ 4 / J := by
  have hJ2sq : 1 ≤ J2 ^ 2 := by nlinarith
  have hsJ : s ≤ J := by rw [hJ]; nlinarith
  have hratio : s / J2 ^ 2 ≤ s :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hJself : J ≤ B ^ 4 / J :=
    (le_div_iff₀ hJpos).mpr (by nlinarith [sq_nonneg (B ^ 2 - J)])
  rw [hlocal]
  exact hratio.trans (hsJ.trans hJself)

theorem first_poisson_y_ball
    (L B F K A1 A2 C d c E J h y Y : ℝ)
    (_hL : 0 ≤ L) (_hB : 0 ≤ B) (_hF : 0 ≤ F)
    (hK : 0 < K) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hC : 0 < C) (hd : 0 ≤ d) (_hc : 0 ≤ c)
    (hE : 0 ≤ E) (hJ : 0 < J) (_hh : 0 ≤ h)
    (hfrequency : h ≤ L ^ 2 * c * d / (K * A1 * A2 * C ^ 2))
    (hy : y ≤ h * F ^ 2 * E)
    (hratio : c * E / (A1 * A2) ≤ B ^ 4 / J)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) :
    y ≤ Y := by
  have hfactor : 0 ≤ F ^ 2 * E := by positivity
  calc
    y ≤ h * F ^ 2 * E := hy
    _ ≤ (L ^ 2 * c * d / (K * A1 * A2 * C ^ 2)) * F ^ 2 * E :=
      by convert mul_le_mul_of_nonneg_right hfrequency hfactor using 1 <;> ring
    _ = (L ^ 2 * d * F ^ 2 / (K * C ^ 2)) * (c * E / (A1 * A2)) := by
      field_simp
    _ ≤ (L ^ 2 * d * F ^ 2 / (K * C ^ 2)) * (B ^ 4 / J) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = Y := by rw [hY]; field_simp

theorem restrict_positive_side_to_weight_support
    {Ω : Type*} (S : Finset Ω) (w : Ω → ℂ) (U : Ω → ℂ) :
    (∑ ω ∈ S with w ω ≠ 0, ‖w ω‖ * ‖U ω‖ ^ 2) =
      (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ ^ 2) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hw : w ω = 0 <;> simp [hw]

theorem weighted_cauchy_ball_enlargement
    {Ω Λ : Type*} [DecidableEq Λ]
    (S : Finset Ω) (T : Finset Λ) (label : Ω → Λ)
    (w : Ω → ℂ) (A B : Λ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁)
    (hsupport : ∀ ω ∈ S, w ω ≠ 0 → label ω ∈ T)
    (hfiber : ∀ a ∈ T,
      (∑ ω ∈ S with label ω = a, ‖w ω‖) ≤ M₁)
    (hfiber₂ : ∀ a ∈ T,
      (∑ ω ∈ S with label ω = a, ‖w ω‖) ≤ M₂) :
    ‖∑ ω ∈ S, w ω * A (label ω) * star (B (label ω))‖ ^ 2 ≤
      (M₁ * ∑ a ∈ T, ‖A a‖ ^ 2) *
        (M₂ * ∑ a ∈ T, ‖B a‖ ^ 2) := by
  classical
  let S' : Finset Ω := S.filter (fun ω => w ω ≠ 0)
  have hmap : ∀ ω ∈ S', label ω ∈ T := by
    intro ω hω
    exact hsupport ω (Finset.mem_filter.mp hω).1 (Finset.mem_filter.mp hω).2
  have hsum :
      (∑ ω ∈ S', w ω * A (label ω) * star (B (label ω))) =
      (∑ ω ∈ S, w ω * A (label ω) * star (B (label ω))) := by
    dsimp [S']
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hw : w ω = 0 <;> simp [hw]
  have hfiber' : ∀ a ∈ T,
      (∑ ω ∈ S' with label ω = a, ‖w ω‖) ≤ M₁ := by
    intro a ha
    have heq : (∑ ω ∈ S' with label ω = a, ‖w ω‖) =
        (∑ ω ∈ S with label ω = a, ‖w ω‖) := by
      dsimp [S']
      simp only [Finset.filter_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hl : label ω = a <;> by_cases hw : w ω = 0 <;> simp [hl, hw]
    rw [heq]
    exact hfiber a ha
  have hfiber₂' : ∀ a ∈ T,
      (∑ ω ∈ S' with label ω = a, ‖w ω‖) ≤ M₂ := by
    intro a ha
    have heq : (∑ ω ∈ S' with label ω = a, ‖w ω‖) =
        (∑ ω ∈ S with label ω = a, ‖w ω‖) := by
      dsimp [S']
      simp only [Finset.filter_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hl : label ω = a <;> by_cases hw : w ω = 0 <;> simp [hl, hw]
    rw [heq]
    exact hfiber₂ a ha
  rw [← hsum]
  exact reassembled_bilinear_bound S' T T label label w A B M₁ M₂
    hM₁ hmap hmap hfiber' hfiber₂'

theorem weighted_fourier_minkowski
    {Ω : Type*} (S : Finset Ω)
    (b : ℝ → ℂ) (φ : Ω → ℝ → ℂ) (J : ℕ) (H : ℝ)
    (_hH : 0 ≤ H)
    (hint : ∀ ω ∈ S,
      Integrable (fun t : ℝ => b t * φ ω t) volume)
    (hweight : Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume)
    (hφ : ∀ t : ℝ,
      ‖∑ ω ∈ S, φ ω t‖ ≤ H * (1 + ‖t‖) ^ J) :
    ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ ≤
      H * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
  have hR : Integrable
      (fun t : ℝ => H * ((1 + ‖t‖) ^ J * ‖b t‖)) volume :=
    hweight.const_mul H
  calc
    ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ =
        ‖∫ t : ℝ, ∑ ω ∈ S, b t * φ ω t‖ := by
      rw [integral_finsetSum S hint]
    _ ≤ ∫ t : ℝ, ‖∑ ω ∈ S, b t * φ ω t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, H * ((1 + ‖t‖) ^ J * ‖b t‖) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (by intro t; positivity))
        hR
      filter_upwards [] with t
      rw [← Finset.mul_sum, norm_mul]
      calc
        ‖b t‖ * ‖∑ ω ∈ S, φ ω t‖ ≤
            ‖b t‖ * (H * (1 + ‖t‖) ^ J) :=
          mul_le_mul_of_nonneg_left (hφ t) (norm_nonneg _)
        _ = H * ((1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ = H * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
      rw [integral_const_mul]

theorem weighted_fourier_minkowski_with_decay
    {Ω : Type*} (S : Finset Ω)
    (b : ℝ → ℂ) (φ : Ω → ℝ → ℂ)
    (A J : ℕ) (R H C : ℝ)
    (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hint : ∀ ω ∈ S,
      Integrable (fun t : ℝ => b t * φ ω t) volume)
    (hweight : Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume)
    (hφ : ∀ t : ℝ,
      ‖∑ ω ∈ S, φ ω t‖ ≤ H * (1 + ‖t‖) ^ J)
    (hcoeff : (1 + R) ^ A *
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C) :
    (1 + R) ^ A *
      ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ ≤ H * C := by
  have hM := weighted_fourier_minkowski S b φ J H hH hint hweight hφ
  calc
    (1 + R) ^ A *
      ‖∑ ω ∈ S, ∫ t : ℝ, b t * φ ω t‖ ≤
        (1 + R) ^ A *
          (H * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    _ = H * ((1 + R) ^ A *
      ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ ≤ H * C := mul_le_mul_of_nonneg_left hcoeff hH

theorem schwartz_fourier_one_plus_integrable
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ =>
      (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) volume := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa [b] using b.integrable_pow_mul volume 0
  have hIJ : Integrable
      (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hR : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hp := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num)
      (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hcont : Continuous
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
    fun_prop
  exact hR.mono_nonneg hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (by intro t; positivity))
    (Filter.Eventually.of_forall hpoint)

end AnalyticBridge

namespace JacobiQuadratic

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private def affineDouble (hchar : ringChar F ≠ 2) : F ≃ F where
  toFun x := 2 * x - 1
  invFun t := (t + 1) / 2
  left_inv := by
    intro x
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring
  right_inv := by
    intro t
    have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
    field_simp
    ring

private def oneSub : F ≃ F where
  toFun y := 1 - y
  invFun y := 1 - y
  left_inv := by intro y; ring
  right_inv := by intro y; ring

private theorem square_fiber (χ : MulChar F ℂ)
    (hchar : ringChar F ≠ 2) :
    (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, ((quadraticChar F y : ℂ) + 1) * χ (1 - y) := by
  classical
  have hfiber : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ y : F, (#{t : F | t ^ 2 = y}.toFinset : ℂ) * χ (1 - y) := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun t : F => t ^ 2) (f := fun t : F => χ (1 - t ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_congr rfl (fun t ht => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [ht])]
    simp
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact_mod_cast quadraticChar_card_sqrts hchar y

theorem jacobi_quadratic (χ : MulChar F ℂ)
    (hchar : ringChar F ≠ 2) (hχ : χ ≠ 1) :
    jacobiSum χ ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) =
      χ (4 : F) * jacobiSum χ χ := by
  classical
  let q : MulChar F ℂ := (quadraticChar F).ringHomComp (Int.castRingHom ℂ)
  have hsum0 : (∑ y : F, χ (1 - y)) = 0 := by
    have ht := (Equiv.sum_comp (oneSub (F := F)) χ)
    change (∑ y : F, χ ((oneSub (F := F)) y)) = 0
    exact ht.trans (MulChar.sum_eq_zero_of_ne_one hχ)
  have hfiber := square_fiber χ hchar
  have hsq : (∑ t : F, χ (1 - t ^ 2)) = jacobiSum χ q := by
    rw [hfiber]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    simp only [one_mul, hsum0, add_zero]
    exact jacobiSum_comm q χ
  have hchange : (∑ t : F, χ (1 - t ^ 2)) =
      ∑ x : F, χ (4 * x * (1 - x)) := by
    have ht := Equiv.sum_comp (affineDouble (F := F) hchar)
      (fun t : F => χ (1 - t ^ 2))
    convert ht.symm using 1
    · apply Finset.sum_congr rfl
      intro x _
      congr 1
      change 4 * x * (1 - x) = 1 - (2 * x - 1) ^ 2
      ring
  calc
    jacobiSum χ q = ∑ x : F, χ (4 * x * (1 - x)) := hsq.symm.trans hchange
    _ = χ (4 : F) * jacobiSum χ χ := by
      rw [jacobiSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [ map_mul]
      ring

theorem gauss_sextic_relation (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ4 : χ ^ 4 ≠ 1)
    (hχ3 : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ))
    (hχ6 : χ ^ 6 = 1) :
    χ (4 : F) * gaussSum χ ψ * (Fintype.card F : ℂ) =
      gaussSum (χ ^ 3) ψ * gaussSum (χ ^ 2) ψ ^ 2 := by

  let g1 := gaussSum χ ψ
  let g2 := gaussSum (χ ^ 2) ψ
  let g3 := gaussSum (χ ^ 3) ψ
  let g4 := gaussSum (χ ^ 4) ψ
  let J11 := jacobiSum χ χ
  let J13 := jacobiSum χ (χ ^ 3)
  have hprod2 : χ * χ = χ ^ 2 := (pow_two χ).symm
  have hprod4 : χ * χ ^ 3 = χ ^ 4 := by group
  have hJ12 : g2 * J11 = g1 * g1 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod2]; exact hχ2) ψ
      (χ := χ) (φ := χ)
    rw [hprod2] at h
    exact h
  have hJ13 : g4 * J13 = g1 * g3 := by
    have h := jacobiSum_mul_nontrivial (by rw [hprod4]; exact hχ4) ψ
      (χ := χ) (φ := χ ^ 3)
    rw [hprod4] at h
    exact h
  have hJquad : J13 = χ (4 : F) * J11 := by
    simpa only [J13, J11, hχ3] using jacobi_quadratic χ hchar hχ1
  have hg1ne : g1 ≠ 0 := by
    apply gaussSum_ne_zero_of_nontrivial
    · exact_mod_cast Fintype.card_pos.ne'
    · exact hχ1
    · exact hψ
  have h4inv : χ ^ 4 = (χ ^ 2)⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ ^ 2 * χ ^ 4 = χ ^ 6 := by group
      _ = 1 := hχ6
  have h4minus : (χ ^ 4) (-1 : F) = 1 := by
    rw [χ.pow_apply' (by decide : (4 : ℕ) ≠ 0), ← map_pow,
      show (-1 : F) ^ 4 = 1 by ring, map_one]
  have hG4inv : gaussSum (χ ^ 4) ψ⁻¹ = g4 := by
    have h := mul_gaussSum_inv_eq_gaussSum (χ ^ 4) ψ
    rw [h4minus, one_mul] at h
    exact h
  have hG24 : g2 * g4 = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ2 hψ
    rw [← h4inv, hG4inv] at h
    exact h
  have hbasic : g1 * g3 * g2 = χ (4 : F) * g4 * g1 ^ 2 := by
    calc
      g1 * g3 * g2 = (g4 * J13) * g2 := by rw [hJ13]
      _ = χ (4 : F) * g4 * (g2 * J11) := by rw [hJquad]; ring
      _ = χ (4 : F) * g4 * g1 ^ 2 := by rw [hJ12]; ring
  have hbasic' : g3 * g2 = χ (4 : F) * g4 * g1 := by
    apply mul_left_cancel₀ hg1ne
    calc
      g1 * (g3 * g2) = g1 * g3 * g2 := by ring
      _ = χ (4 : F) * g4 * g1 ^ 2 := hbasic
      _ = g1 * (χ (4 : F) * g4 * g1) := by ring
  calc
    χ (4 : F) * g1 * (Fintype.card F : ℂ) =
        χ (4 : F) * g1 * (g2 * g4) := by rw [hG24]
    _ = (χ (4 : F) * g4 * g1) * g2 := by ring
    _ = g3 * g2 ^ 2 := by rw [← hbasic']; ring

theorem normalized_gauss_sextic_relation (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ.IsPrimitive)
    (hχ1 : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (hχ4 : χ ^ 4 ≠ 1)
    (hχ3 : χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ))
    (hχ6 : χ ^ 6 = 1)
    (s : ℂ) (hs : s ^ 2 = (Fintype.card F : ℂ)) (hs0 : s ≠ 0) :
    χ (4 : F) * (gaussSum χ ψ / s) * (gaussSum (χ ^ 2) ψ / s) =
      (gaussSum (χ ^ 3) ψ / s) * (gaussSum (χ ^ 2) ψ / s) ^ 3 := by
  have hraw := gauss_sextic_relation χ ψ hchar hψ hχ1 hχ2 hχ4 hχ3 hχ6
  rw [← hs] at hraw
  field_simp
  linear_combination (gaussSum (χ ^ 2) ψ) * hraw

end JacobiQuadratic

end

end OAI
end OAIOriginalModule0041

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.SexticNormalization
Source SHA256: 11bc22bdaa6864eeb8792acc6cd1f33094e5c8726af5aad95e483b0d66656b76
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0042


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

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

noncomputable def breveGamma1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

noncomputable def breveGamma3 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood ^ 3)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

theorem canonicalSextic_pow_three_quadratic (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 3 =
      (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ) := by
  change ((sexticChar P hgood).ringHomComp eisEmbedding) ^ 3 = _
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).2.1]
  ext x
  change eisEmbedding ((quadraticChar (O ⧸ P) x : ℤ) : O) =
    ((quadraticChar (O ⧸ P) x : ℤ) : ℂ)
  simp

theorem breveGamma1_gamma2_relation (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
      (canonicalSextic P hgood
        (Ideal.Quotient.mk P (4 : O)))⁻¹ *
      breveGamma3 P hgood p hP hp *
        (breveGamma2 P hgood p hP hp) ^ 3 := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℂ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hχ2 : χ ^ 2 ≠ 1 := canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
    (by decide : (2 : ℕ) ≠ 0) (by decide : (2 : ℕ) < 6)
  have hχ4 : χ ^ 4 ≠ 1 := canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
    (by decide : (4 : ℕ) ≠ 0) (by decide : (4 : ℕ) < 6)
  have hχ3 : χ ^ 3 = (quadraticChar (O ⧸ Ideal.span {p})).ringHomComp
      (Int.castRingHom ℂ) := canonicalSextic_pow_three_quadratic (Ideal.span {p}) hgood
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six (Ideal.span {p}) hgood
  have hs : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    have hnormO := primary_generator_mul_conj_eq_card
      (Ideal.span {p}) hgood p rfl hprimary
    have hnormC := congrArg eisEmbedding hnormO
    rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  have hmul := JacobiQuadratic.normalized_gauss_sextic_relation
    χ ψ hchar hψ hχ1 hχ2 hχ4 hχ3 hχ6 s hs hs0
  have hfour : (4 : O ⧸ Ideal.span {p}) ≠ 0 := by
    have htwo : (2 : O ⧸ Ideal.span {p}) ≠ 0 := Ring.two_ne_zero hchar
    convert pow_ne_zero 2 htwo using 1 ; norm_num
  have hχfour : χ (4 : O ⧸ Ideal.span {p}) ≠ 0 :=
    χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hfour)
  change χ 4 * breveGamma1 (Ideal.span {p}) hgood p rfl hp *
    breveGamma2 (Ideal.span {p}) hgood p rfl hp =
    breveGamma3 (Ideal.span {p}) hgood p rfl hp *
      breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3 at hmul
  change breveGamma1 (Ideal.span {p}) hgood p rfl hp *
    breveGamma2 (Ideal.span {p}) hgood p rfl hp =
    (χ 4)⁻¹ * breveGamma3 (Ideal.span {p}) hgood p rfl hp *
      breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3
  calc
    breveGamma1 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp =
      (χ 4)⁻¹ * (χ 4 * breveGamma1 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp) := by field_simp
    _ = (χ 4)⁻¹ * (breveGamma3 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3) := by rw [hmul]
    _ = _ := by ring

end

section

open EisensteinEmbedding ConcreteTraceCRT IdealGaussCRT

private theorem breveE_period_O (x : O) :
    ShortDraftTrace.breveE (eisEmbedding x) = 1 := by
  obtain ⟨a, b, hx⟩ := exists_ab x
  rw [hx]
  change ShortDraftTrace.breveE
    (embedding omega3 omega3_sq (a + b * pb.gen : O)) = 1
  rw [embedding_apply_ab]
  change ShortDraftTrace.breveE
    ((a : ℂ) + (b : ℂ) * ShortDraftTrace.ω₃) = 1
  exact ShortDraftTrace.breveE_period_integer a b

private noncomputable def eisBreveModChar (p : O) (hp : p ≠ 0) :
    AddChar (O ⧸ Ideal.span {p}) ℂ :=
  traceModChar eisEmbedding ShortDraftTrace.breveE 1 p
    (eisEmbedding_ne_zero hp) one_ne_zero (by
      intro x
      simpa only [div_one] using breveE_period_O x)

theorem eisEmbedding_traceLambda :
    eisEmbedding traceLambda = eisLam := by
  have hgen : pb.gen = omega := by
    simpa only [pb, omega] using
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen
  change embedding omega3 omega3_sq (1 + 2 * omega : O) = 1 + 2 * omega3
  rw [← hgen]
  simp only [map_add, map_one, map_mul, map_ofNat, embedding_gen]

private theorem eisBreveModChar_eq_mulShift (p : O) (hp : p ≠ 0) :
    eisBreveModChar p hp =
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates p hp).mulShift
        (Ideal.Quotient.mk (Ideal.span {p}) traceLambda) := by
  apply DFunLike.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro x
  change ShortDraftTrace.breveE (eisEmbedding x / (eisEmbedding p * 1)) =
    ShortDraftTrace.breveE
      (eisEmbedding (traceLambda * x) / (eisEmbedding p * eisLam))
  congr 1
  rw [map_mul, eisEmbedding_traceLambda]
  field_simp [eisEmbedding_ne_zero hp, eisLam_ne_zero]

end

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

noncomputable def breveLocalG (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  (canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O)))⁻¹ *
    breveGamma3 P hgood p hP hp

theorem breveGamma1_gamma2_eq_neg_alpha_G (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
      (-(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ)) *
        breveLocalG P hgood p hP hp := by
  rw [breveGamma1_gamma2_relation P hgood hchar p hP hp hprimary,
    breveGamma2_cube P hgood p hP hp hprimary]
  unfold breveLocalG
  ring

end

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

noncomputable def breveGamma2Product
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    [haMax : (Ideal.span {a}).IsMaximal]
    [hbMax : (Ideal.span {b}).IsMaximal]
    (hgooda : lambda ∉ Ideal.span {a})
    (hgoodb : lambda ∉ Ideal.span {b}) : ℂ := by
  letI : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  letI : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let χa := canonicalSextic (Ideal.span {a}) hgooda
  let χb := canonicalSextic (Ideal.span {b}) hgoodb
  exact (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    (χa ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    (χb ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates
      a b ha hb x) / (‖eisEmbedding (a * b)‖ : ℂ)

theorem breveGamma2Product_crt
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    [haMax : (Ideal.span {a}).IsMaximal]
    [hbMax : (Ideal.span {b}).IsMaximal]
    (hgooda : lambda ∉ Ideal.span {a})
    (hgoodb : lambda ∉ Ideal.span {b})
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    breveGamma2Product a b ha hb hgooda hgoodb =
      (canonicalSextic (Ideal.span {a}) hgooda
        (Ideal.Quotient.mk (Ideal.span {a}) b)) ^ 2 *
      (canonicalSextic (Ideal.span {b}) hgoodb
        (Ideal.Quotient.mk (Ideal.span {b}) a)) ^ 2 *
      breveGamma2 (Ideal.span {a}) hgooda a rfl ha *
      breveGamma2 (Ideal.span {b}) hgoodb b rfl hb := by
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {b}) := finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let χa := canonicalSextic (Ideal.span {a}) hgooda
  let χb := canonicalSextic (Ideal.span {b}) hgoodb
  have hsum := gauss_sum_breveE_actual_O a b ha hb hcop (χa ^ 2) (χb ^ 2)
  have hnorm : (‖eisEmbedding (a * b)‖ : ℂ) =
      (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ) := by
    rw [map_mul, norm_mul]
    norm_cast
  change (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    (χa ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    (χb ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates a b ha hb x) /
      (‖eisEmbedding (a * b)‖ : ℂ) = _
  rw [hsum, hnorm]
  simp only [χa.pow_apply' (by decide : (2 : ℕ) ≠ 0),
    χb.pow_apply' (by decide : (2 : ℕ) ≠ 0)]
  unfold breveGamma2
  ring

end ActualEisensteinCubic

namespace ConcreteBreveE

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def normalizedTraceGauss
    (a : O) (ha : a ≠ 0) (χ : MulChar (O ⧸ Ideal.span {a}) ℂ) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  letI : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  exact gaussSum χ (eisTraceModChar ShortDraftTrace.breveE
    breveE_period_coordinates a ha) / (‖eisEmbedding a‖ : ℂ)

noncomputable def normalizedTraceGaussProduct
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) : ℂ := by
  letI : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  letI : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  exact (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    χa (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    χb (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates
      a b ha hb x) / (‖eisEmbedding (a * b)‖ : ℂ)

theorem normalizedTraceGaussProduct_crt
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    normalizedTraceGaussProduct a b ha hb χa χb =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      normalizedTraceGauss a ha χa * normalizedTraceGauss b hb χb := by
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {b}) := finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  have hsum := gauss_sum_breveE_actual_O a b ha hb hcop χa χb
  have hnorm : (‖eisEmbedding (a * b)‖ : ℂ) =
      (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ) := by
    rw [map_mul, norm_mul]
    norm_cast
  change (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    χa (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    χb (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates a b ha hb x) /
      (‖eisEmbedding (a * b)‖ : ℂ) = _
  rw [hsum, hnorm]
  unfold normalizedTraceGauss
  ring

end ConcreteBreveE

namespace FixedRayActiveSet

open scoped BigOperators

private theorem sum_zero_and_units {F : Type*} [Field F] [Fintype F]
    (f : F → ℂ) :
    (∑ x : F, f x) = f 0 + ∑ u : Fˣ, f (u : F) := by
  classical
  calc
    (∑ x : F, f x) = f 0 +
        ∑ x ∈ (Finset.univ : Finset F).erase 0, f x := by
          simpa only [add_comm] using
            (Finset.sum_erase_add (Finset.univ : Finset F) f
              (Finset.mem_univ (0 : F))).symm
    _ = f 0 + ∑ x : {x : F // x ≠ 0}, f x := by
      congr 1
      apply Finset.sum_subtype
      intro x
      simp
    _ = f 0 + ∑ u : Fˣ, f (u : F) := by
      congr 1
      apply (Fintype.sum_equiv (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
        (fun u : Fˣ => f (u : F))
        (fun x : {x : F // x ≠ 0} => f x) ?_).symm
      intro u
      rfl

theorem product_sum_by_active_set
    {ι : Type*} [Fintype ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (f : ∀ i, F i → ℂ) :
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
      ∑ A ∈ (Finset.univ : Finset ι).powerset,
        (∏ i ∈ A, ∑ u : (F i)ˣ, f i (u : F i)) *
          (∏ i ∈ (Finset.univ : Finset ι) \ A, f i 0) := by
  classical
  calc
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
        ∏ i, ∑ h : F i, f i h := by
          simpa using (Fintype.prod_sum (fun i (h : F i) => f i h)).symm
    _ = ∏ i, ((∑ u : (F i)ˣ, f i (u : F i)) + f i 0) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [sum_zero_and_units]
      ring
    _ = _ := Finset.prod_add
      (fun i => ∑ u : (F i)ˣ, f i (u : F i))
      (fun i => f i 0) Finset.univ

theorem branch_zero_of_local_mask
    {ι : Type*} [DecidableEq ι] (I A : Finset ι)
    (scalar dual inactive : ι → ℂ)
    (i : ι) (hi : i ∈ A) (hzero : dual i = 0) :
    (∏ k ∈ A, scalar k * dual k) *
      (∏ k ∈ I \ A, inactive k) = 0 := by
  have hprod : (∏ k ∈ A, scalar k * dual k) = 0 :=
    Finset.prod_eq_zero hi (by rw [hzero, mul_zero])
  rw [hprod, zero_mul]

theorem admissible_branch_count
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι → ℕ) :
    ((Finset.univ : Finset ι).powerset.filter
      (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)).card
      ≤ 2 ^ Fintype.card ι := by
  calc
    _ ≤ (Finset.univ : Finset ι).powerset.card := Finset.card_filter_le _ _
    _ = 2 ^ Fintype.card ι := by simp

private theorem branch_zero_outside_admissible
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι → ℕ) (scalar dual inactive : ι → ℂ)
    (hzero : ∀ i, j i ≠ 0 → inactive i = 0)
    (A : Finset ι)
    (hnot : ¬ (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A) :
    (∏ i ∈ A, scalar i * dual i) *
      (∏ i ∈ (Finset.univ : Finset ι) \ A, inactive i) = 0 := by
  obtain ⟨i, hiM, hiA⟩ := Finset.not_subset.mp hnot
  have hj : j i ≠ 0 := (Finset.mem_filter.mp hiM).2
  have hi : i ∈ (Finset.univ : Finset ι) \ A := by simp [hiA]
  have hprod : (∏ k ∈ (Finset.univ : Finset ι) \ A, inactive k) = 0 :=
    Finset.prod_eq_zero hi (hzero i hj)
  rw [hprod, mul_zero]

theorem assemble_local_A5
    {ι : Type*} [Fintype ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (j : ι → ℕ) (f : ∀ i, F i → ℂ)
    (scalar dual : ι → ℂ)
    (hzero : ∀ i, j i ≠ 0 → f i 0 = 0)
    (hactive : ∀ i, (∑ u : (F i)ˣ, f i (u : F i)) =
      scalar i * dual i) :
    (∑ h : ∀ i, F i, ∏ i, f i (h i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, scalar i * dual i) *
          (∏ i ∈ (Finset.univ : Finset ι) \ A, f i 0) := by
  classical
  rw [product_sum_by_active_set]
  have hreplace : ∀ A : Finset ι,
      (∏ i ∈ A, ∑ u : (F i)ˣ, f i (u : F i)) =
        ∏ i ∈ A, scalar i * dual i := by
    intro A
    apply Finset.prod_congr rfl
    intro i _
    exact hactive i
  conv_lhs =>
    arg 2
    ext A
    rw [hreplace A]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hAdmissible : (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A
  · simp [hAdmissible]
  · simp [hAdmissible,
      branch_zero_outside_admissible j scalar dual (fun i => f i 0)
        (fun i hj => hzero i hj)
        A hAdmissible]

end FixedRayActiveSet

namespace CubeInversion

theorem cube_index_filter_complex (m : ℕ) :
    (∑ h ∈ m.divisors, (ArithmeticFunction.moebius h : ℂ)) =
      if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact_mod_cast h

theorem cube_coefficient_filter
    (m : ℕ) (c W : ℕ → ℂ)
    (hc : ∀ a b, c (a * b) = c a * c b) :
    (∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
      if m = 1 then c m * W m else 0 := by
  have heq (h : ℕ) (hh : h ∈ m.divisors) :
      c h * c (m / h) = c m := by
    rw [← hc]
    congr 1
    exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hh)
  calc
    (∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
      (∑ h ∈ m.divisors,
        (ArithmeticFunction.moebius h : ℂ)) * (c m * W m) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro h hh
        calc
          (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m =
              (ArithmeticFunction.moebius h : ℂ) * (c h * c (m / h)) * W m := by ring
          _ = (ArithmeticFunction.moebius h : ℂ) * (c m * W m) := by
              rw [heq h hh]
              ring
    _ = if m = 1 then c m * W m else 0 := by
      rw [cube_index_filter_complex]
      split_ifs <;> simp

theorem finite_cube_inversion
    (S : Finset ℕ) (hS : 1 ∈ S) (c W : ℕ → ℂ)
    (hc : ∀ a b, c (a * b) = c a * c b) :
    (∑ m ∈ S, ∑ h ∈ m.divisors,
      (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W m) =
        c 1 * W 1 := by
  simp_rw [cube_coefficient_filter (c := c) (W := W) (hc := hc)]
  simp [hS]

theorem finite_cube_inversion_with_columns {N : Type*} [DecidableEq N]
    (columns : Finset N) (S : Finset ℕ) (hS : 1 ∈ S)
    (a : N → ℂ) (c : ℕ → ℂ) (W : N → ℕ → ℂ)
    (hc : ∀ x y, c (x * y) = c x * c y) :
    (∑ n ∈ columns, a n *
      (∑ m ∈ S, ∑ h ∈ m.divisors,
        (ArithmeticFunction.moebius h : ℂ) * c h * c (m / h) * W n m)) =
      ∑ n ∈ columns, a n * (c 1 * W n 1) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [finite_cube_inversion S hS c (W n) hc]

end CubeInversion

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

noncomputable def breveGammaMinus1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood)⁻¹
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

private theorem canonicalSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (canonicalSextic P hgood) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  change orderOf (Φ (sexticChar P hgood)) = 6
  rw [orderOf_injective Φ hΦ, sexticChar_order P hgood hchar]

theorem breveGamma1_gammaMinus1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGammaMinus1 P hgood p hP hp =
      canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O)) := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℂ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six (Ideal.span {p}) hgood
  have horder : orderOf χ = 6 :=
    canonicalSextic_order_six (Ideal.span {p}) hgood hchar
  have hχ5 : χ ^ 5 = χ⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ * χ ^ 5 = χ ^ 6 := by group
      _ = 1 := hχ6
  have hprod := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ1 hψ
  rw [horder, show 6 - 1 = 5 by decide, hχ5] at hprod
  have hs : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    have hnormO := primary_generator_mul_conj_eq_card
      (Ideal.span {p}) hgood p rfl hprimary
    have hnormC := congrArg eisEmbedding hnormO
    rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  change (gaussSum χ ψ / s) * (gaussSum χ⁻¹ ψ / s) = χ (-1)
  field_simp
  rw [hs]
  simpa only [mul_comm] using hprod

end ActualEisensteinCubic

namespace PowerExtraction

theorem from_mean_square_and_prime_rows
    (D ε J A : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A)
    (hJ : D ^ ((11 / 60 : ℝ) - ε) ≤ J)
    (hmean : J * A ^ 2 ≤
      2 * D ^ ((21 / 10 : ℝ) + ε) +
      2 * J * D ^ (49 / 30 : ℝ)) :
    A ≤ 2 * D ^ ((23 / 24 : ℝ) + ε) := by
  let E : ℝ := (23 / 24 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hJpos : 0 < J := lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hJ
  have hpow :
      D ^ ((21 / 10 : ℝ) + ε) ≤
        J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      D ^ ((21 / 10 : ℝ) + ε) =
          D ^ ((11 / 60 : ℝ) - ε) * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
            rw [← Real.rpow_add hDpos]
            congr 1
            ring
      _ ≤ J * D ^ ((23 / 12 : ℝ) + 2 * ε) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
  have herr : D ^ (49 / 30 : ℝ) ≤
      D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hsq : A ^ 2 ≤ 4 * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    have hmain : J * A ^ 2 ≤
        4 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
      calc
        J * A ^ 2 ≤
            2 * D ^ ((21 / 10 : ℝ) + ε) +
            2 * J * D ^ (49 / 30 : ℝ) := hmean
        _ ≤ 2 * (J * D ^ ((23 / 12 : ℝ) + 2 * ε)) +
            2 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by
              gcongr
        _ = 4 * J * D ^ ((23 / 12 : ℝ) + 2 * ε) := by ring
    nlinarith
  have hexp : (23 / 12 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((23 / 12 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) := (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((23 / 12 : ℝ) + 2 * ε) := by rw [hexp]
  have htwo : 0 ≤ 2 * D ^ E := by positivity
  apply (sq_le_sq₀ hA htwo).mp
  rw [mul_pow, hpow2]
  nlinarith

end PowerExtraction

end

end OAI
end OAIOriginalModule0042

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.LocalProductAssembly
Source SHA256: cda1a20b78d89a7d5c8c91ecae5f8ab2ee1d695d9a23394d3297404d63707d09
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0043



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

open ConcreteTraceCRT
open scoped ComplexConjugate

theorem canonicalSextic_inverse_eq_conj_on_units (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) (u : (O ⧸ P)ˣ) :
    (canonicalSextic P hgood (u : O ⧸ P))⁻¹ =
      star (canonicalSextic P hgood (u : O ⧸ P)) := by
  let χ := canonicalSextic P hgood
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hval : χ (u : O ⧸ P) ^ 6 = 1 := by
    rw [← χ.pow_apply_coe 6 u, hχ6, MulChar.one_apply_coe]
  exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hval (by decide))

theorem breveLocalG_eq_conjugate (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    breveLocalG P hgood p hP hp =
      star (canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O))) *
        breveGamma3 P hgood p hP hp := by
  have htwo : (2 : O ⧸ P) ≠ 0 := Ring.two_ne_zero hchar
  have hfour : (4 : O ⧸ P) ≠ 0 := by
    convert pow_ne_zero 2 htwo using 1 ; norm_num
  have hunit : IsUnit (4 : O ⧸ P) := isUnit_iff_ne_zero.mpr hfour
  let u : (O ⧸ P)ˣ := hunit.unit
  have hu : (u : O ⧸ P) = Ideal.Quotient.mk P (4 : O) := hunit.unit_spec
  unfold breveLocalG
  rw [← hu, canonicalSextic_inverse_eq_conj_on_units P hgood u]

end ActualEisensteinCubic

namespace FourierBridge
open scoped ContDiff FourierTransform SchwartzMap

theorem coupled_double_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F₁ F₂ V₁ V₂ : ℝ → ℂ)
    (R₁ R₂ : ℝ) (a₁ a₂ y : ι → ℝ)
    (hV₁c : HasCompactSupport V₁) (hV₁s : ContDiff ℝ ∞ V₁)
    (hF₁s : ContDiff ℝ ∞ F₁)
    (hV₂c : HasCompactSupport V₂) (hV₂s : ContDiff ℝ ∞ V₂)
    (hF₂s : ContDiff ℝ ∞ F₂)
    (hactive₁ : (∏ j : ι, W j (y j)) ≠ 0 →
      V₁ (∑ j : ι, a₁ j * y j) = 1)
    (hactive₂ : (∏ j : ι, W j (y j)) ≠ 0 →
      V₂ (∑ j : ι, a₂ j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j)) *
      F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j)) =
      ∫ t₁ : ℝ,
        (∫ t₂ : ℝ,
          (∏ j : ι,
            W j (y j) * logPhase t₁ (a₁ j * y j) *
              logPhase t₂ (a₂ j * y j)) *
            (𝓕 (logProfile V₂ F₂ R₂ 1 hV₂c hV₂s hF₂s)) t₂) *
          (𝓕 (logProfile V₁ F₁ R₁ 1 hV₁c hV₁s hF₁s)) t₁ := by
  classical
  let P : ℂ := ∏ j : ι, W j (y j)
  let Z₁ : ℂ := F₁ (R₁ * Real.exp (∑ j : ι, a₁ j * y j))
  let Z₂ : ℂ := F₂ (R₂ * Real.exp (∑ j : ι, a₂ j * y j))
  let b₁ := 𝓕 (logProfile V₁ F₁ R₁ 1 hV₁c hV₁s hF₁s)
  let b₂ := 𝓕 (logProfile V₂ F₂ R₂ 1 hV₂c hV₂s hF₂s)
  let Q (t₁ : ℝ) : ℂ :=
    ∏ j : ι, W j (y j) * logPhase t₁ (a₁ j * y j)
  let T (t₁ t₂ : ℝ) : ℂ :=
    ∏ j : ι,
      W j (y j) * logPhase t₁ (a₁ j * y j) *
        logPhase t₂ (a₂ j * y j)
  have hsep₁ : P * Z₁ = ∫ t₁ : ℝ, Q t₁ * b₁ t₁ := by
    simpa [P, Z₁, Q, b₁] using
      coupled_log_separation W F₁ V₁ R₁ a₁ y
        hV₁c hV₁s hF₁s hactive₁
  have hsep₂ (t₁ : ℝ) :
      Q t₁ * Z₂ = ∫ t₂ : ℝ, T t₁ t₂ * b₂ t₂ := by
    let W' : ι → ℝ → ℂ :=
      fun j z => W j z * logPhase t₁ (a₁ j * z)
    have hP : (∏ j : ι, W' j (y j)) = Q t₁ := rfl
    have hactive₂' : (∏ j : ι, W' j (y j)) ≠ 0 →
        V₂ (∑ j : ι, a₂ j * y j) = 1 := by
      intro hW'
      have hprod : (∏ j : ι, W j (y j)) ≠ 0 := by
        intro hz
        have hz' : (∏ j : ι, W' j (y j)) = 0 := by
          rw [show (∏ j : ι, W' j (y j)) =
            (∏ j : ι, W j (y j)) *
              (∏ j : ι, logPhase t₁ (a₁ j * y j)) by
                simp [W', Finset.prod_mul_distrib]]
          simp [hz]
        exact hW' hz'
      exact hactive₂ hprod
    simpa [W', Q, T, Z₂, b₂] using
      coupled_log_separation W' F₂ V₂ R₂ a₂ y
        hV₂c hV₂s hF₂s hactive₂'
  calc
    P * Z₁ * Z₂ = (∫ t₁ : ℝ, Q t₁ * b₁ t₁) * Z₂ := by rw [hsep₁]
    _ = ∫ t₁ : ℝ, (Q t₁ * b₁ t₁) * Z₂ := by rw [integral_mul_const]
    _ = ∫ t₁ : ℝ, (Q t₁ * Z₂) * b₁ t₁ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      ring
    _ = ∫ t₁ : ℝ,
          (∫ t₂ : ℝ, T t₁ t₂ * b₂ t₂) * b₁ t₁ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      rw [hsep₂ t₁]

end FourierBridge

namespace AnalyticBridge

theorem double_weighted_fourier_minkowski
    {Ω : Type*} (S : Finset Ω)
    (b₁ b₂ : ℝ → ℂ) (φ : Ω → ℝ → ℝ → ℂ)
    (J₁ J₂ : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hinner : ∀ t₁ : ℝ, ∀ ω ∈ S,
      Integrable (fun t₂ : ℝ => b₂ t₂ * φ ω t₁ t₂) volume)
    (houter : ∀ ω ∈ S,
      Integrable (fun t₁ : ℝ =>
        b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)) volume)
    (hweight₁ : Integrable
      (fun t₁ : ℝ => (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) volume)
    (hweight₂ : Integrable
      (fun t₂ : ℝ => (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖) volume)
    (hφ : ∀ t₁ t₂ : ℝ,
      ‖∑ ω ∈ S, φ ω t₁ t₂‖ ≤
        H * (1 + ‖t₁‖) ^ J₁ * (1 + ‖t₂‖) ^ J₂) :
    ‖∑ ω ∈ S,
        ∫ t₁ : ℝ,
          b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)‖ ≤
      H *
        (∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) *
        (∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖) := by
  let I₂ : ℝ := ∫ t₂ : ℝ, (1 + ‖t₂‖) ^ J₂ * ‖b₂ t₂‖
  have hI₂ : 0 ≤ I₂ :=
    integral_nonneg (fun t₂ => by positivity)
  have hinnerbound (t₁ : ℝ) :
      ‖∑ ω ∈ S, ∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂‖ ≤
        (H * (1 + ‖t₁‖) ^ J₁) * I₂ := by
    apply weighted_fourier_minkowski S b₂ (fun ω t₂ => φ ω t₁ t₂)
      J₂ (H * (1 + ‖t₁‖) ^ J₁) (by positivity)
      (hinner t₁) hweight₂
    intro t₂
    convert hφ t₁ t₂ using 1
  have houterbound :
      ‖∑ ω ∈ S,
          ∫ t₁ : ℝ,
            b₁ t₁ * (∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)‖ ≤
        (H * I₂) *
          (∫ t₁ : ℝ, (1 + ‖t₁‖) ^ J₁ * ‖b₁ t₁‖) := by
    apply weighted_fourier_minkowski S b₁
      (fun ω t₁ => ∫ t₂ : ℝ, b₂ t₂ * φ ω t₁ t₂)
      J₁ (H * I₂) (mul_nonneg hH hI₂)
      houter hweight₁
    intro t₁
    convert hinnerbound t₁ using 1 ; ring
  simpa [I₂, mul_assoc, mul_comm, mul_left_comm] using houterbound

end AnalyticBridge

namespace FourierBridge
open scoped FourierTransform SchwartzMap

theorem logPhase_norm (t y : ℝ) : ‖logPhase t y‖ = 1 := by
  simpa [logPhase] using
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t * y)

theorem logPhase_continuous_left (y : ℝ) :
    Continuous (fun t : ℝ => logPhase t y) := by
  unfold logPhase
  fun_prop

end FourierBridge

namespace AnalyticBridge
open scoped FourierTransform SchwartzMap

theorem bounded_separated_double_integrable
    {Ω : Type*} (S : Finset Ω)
    (g₁ g₂ : 𝓢(ℝ, ℂ)) (u v : Ω → ℝ → ℂ)
    (humeas : ∀ ω ∈ S, AEStronglyMeasurable (u ω) volume)
    (hvmeas : ∀ ω ∈ S, AEStronglyMeasurable (v ω) volume)
    (hubdd : ∀ ω ∈ S, ∃ M : ℝ, ∀ t : ℝ, ‖u ω t‖ ≤ M)
    (hvbdd : ∀ ω ∈ S, ∃ M : ℝ, ∀ t : ℝ, ‖v ω t‖ ≤ M) :
    (∀ t₁ : ℝ, ∀ ω ∈ S,
      Integrable (fun t₂ : ℝ =>
        (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂)) volume) ∧
    (∀ ω ∈ S,
      Integrable (fun t₁ : ℝ =>
        (𝓕 g₁) t₁ *
          (∫ t₂ : ℝ,
            (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂))) volume) := by
  have hb₁ : Integrable (fun t : ℝ => (𝓕 g₁) t) volume :=
    (𝓕 g₁).integrable
  have hb₂ : Integrable (fun t : ℝ => (𝓕 g₂) t) volume :=
    (𝓕 g₂).integrable
  have hvint (ω : Ω) (hω : ω ∈ S) :
      Integrable (fun t₂ : ℝ => (𝓕 g₂) t₂ * v ω t₂) volume := by
    obtain ⟨Mv, hMv⟩ := hvbdd ω hω
    exact hb₂.mul_bdd (hvmeas ω hω)
      (Filter.Eventually.of_forall hMv)
  constructor
  · intro t₁ ω hω
    have hmeas : AEStronglyMeasurable
        (fun t₂ : ℝ => u ω t₁ * v ω t₂) volume :=
      (hvmeas ω hω).const_mul (u ω t₁)
    obtain ⟨Mv, hMv⟩ := hvbdd ω hω
    have hbound : ∀ t₂ : ℝ,
        ‖u ω t₁ * v ω t₂‖ ≤ ‖u ω t₁‖ * Mv := by
      intro t₂
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hMv t₂) (norm_nonneg _)
    exact hb₂.mul_bdd hmeas (Filter.Eventually.of_forall hbound)
  · intro ω hω
    let Cv : ℂ := ∫ t₂ : ℝ, (𝓕 g₂) t₂ * v ω t₂
    have hfactor (t₁ : ℝ) :
        (∫ t₂ : ℝ,
          (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂)) = u ω t₁ * Cv := by
      calc
        (∫ t₂ : ℝ,
          (𝓕 g₂) t₂ * (u ω t₁ * v ω t₂)) =
            ∫ t₂ : ℝ, u ω t₁ * ((𝓕 g₂) t₂ * v ω t₂) := by
          apply integral_congr_ae
          filter_upwards [] with t₂
          ring
        _ = u ω t₁ * Cv := by rw [integral_const_mul]
    obtain ⟨Mu, hMu⟩ := hubdd ω hω
    have hmeas : AEStronglyMeasurable
        (fun t₁ : ℝ => u ω t₁ * Cv) volume :=
      (humeas ω hω).mul_const Cv
    have hbound : ∀ t₁ : ℝ,
        ‖u ω t₁ * Cv‖ ≤ Mu * ‖Cv‖ := by
      intro t₁
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hMu t₁) (norm_nonneg _)
    have hInt : Integrable
        (fun t₁ : ℝ => (𝓕 g₁) t₁ * (u ω t₁ * Cv)) volume :=
      hb₁.mul_bdd hmeas (Filter.Eventually.of_forall hbound)
    convert hInt using 1
    funext t₁
    rw [hfactor t₁]

end AnalyticBridge

namespace PowerExtraction

theorem from_finite_sixth_power_rows
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (D ε : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes,
      ‖A untwisted - A (row p)‖ ≤ D ^ (49 / 60 : ℝ))
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ (primes.card : ℝ))
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      D ^ ((21 / 10 : ℝ) + ε)) :
    ‖A untwisted‖ ≤ 2 * D ^ ((23 / 24 : ℝ) + ε) := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hextract := ShortDraft.complex_row_extraction rows primes row A untwisted
    (D ^ (49 / 60 : ℝ)) (D ^ ((21 / 10 : ℝ) + ε))
    (by positivity) hrows hinj happrox hmean
  have herror : (D ^ (49 / 60 : ℝ)) ^ 2 = D ^ (49 / 30 : ℝ) := by
    calc
      (D ^ (49 / 60 : ℝ)) ^ 2 = D ^ ((49 / 60 : ℝ) * 2) :=
        (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = D ^ (49 / 30 : ℝ) := by congr 1; norm_num
  rw [herror] at hextract
  exact from_mean_square_and_prime_rows D ε (primes.card : ℝ)
    ‖A untwisted‖ hD hε (norm_nonneg _) hcount hextract

end PowerExtraction

namespace ActualEisensteinCubic

section

open AddChar MulChar

private noncomputable def localA5Kernel (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x h : O ⧸ P) : ℂ :=
  let χ := canonicalSextic P hgood
  let q : ℂ := Nat.card (O ⧸ P)
  if h = 0 then (if j = 0 then 1 - q⁻¹ else 0)
  else q⁻¹ *
    (∑ t : O ⧸ P, (χ ^ j) t * ψ (-(h * t))) *
    (((χ⁻¹) ^ 2) ((σ : O ⧸ P) * h)) *
    ψ ((ε * x) * h⁻¹)

private theorem localA5Kernel_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    localA5Kernel P hgood ψ j σ ε x 0 =
      if j = 0 then 1 - (Nat.card (O ⧸ P) : ℂ)⁻¹ else 0 := by
  simp [localA5Kernel]

private theorem localA5Kernel_active_eq_raw (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    (∑ u : (O ⧸ P)ˣ, localA5Kernel P hgood ψ j σ ε x u) =
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ u : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P,
          (canonicalSextic P hgood ^ j) t * ψ (-(u * t))) *
        (((canonicalSextic P hgood)⁻¹) ^ 2) (σ * u) *
        ψ ((ε * x) * ((u⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have hu : (u : O ⧸ P) ≠ 0 := Units.ne_zero u
  simp only [localA5Kernel, ite_eq_right hu,
    Units.val_inv_eq_inv_val]
  ring

private noncomputable def localA5Output (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (j : ℕ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) : ℂ :=
  let χ := canonicalSextic P hgood
  let q : ℂ := Nat.card (O ⧸ P)
  if j = 0 then
    -(((χ⁻¹) ^ 2) σ) *
      (q⁻¹ * ((χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x))
  else if j = 4 then
    (((χ⁻¹) ^ 2) σ) *
      (q⁻¹ * gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1))
  else
    ((χ⁻¹) ^ 2) σ *
      (q⁻¹ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ * (χ ^ (j + 2))⁻¹ ε) *
      (χ ^ (j + 2))⁻¹ x

private theorem localA5Kernel_active_eq_output (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (j : ℕ) (hj6 : j < 6)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    (∑ u : (O ⧸ P)ˣ, localA5Kernel P hgood ψ j σ ε x u) =
      localA5Output P hgood ψ j σ ε x := by
  rw [localA5Kernel_active_eq_raw]
  by_cases hj0 : j = 0
  · subst j
    simpa only [localA5Output, ite_true] using
      canonical_A5_jzero_active P hgood hchar ψ hψ σ ε x
  by_cases hj4 : j = 4
  · subst j
    simpa [localA5Output] using
      canonical_A5_jfour P hgood hchar ψ hψ σ ε x
  simpa only [localA5Output, ite_eq_right hj0, ite_eq_right hj4] using
    canonical_A5_nonexceptional P hgood hchar ψ j hj0 hj6 hj4 σ ε x

theorem actual_local_product_assembly
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (ε x : ∀ i, O ⧸ Ideal.span {p i}) :
    (∑ h : ∀ i, O ⧸ Ideal.span {p i},
      ∏ i, localA5Kernel (Ideal.span {p i}) (hgood i)
        (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
        (j i) (σ i) (ε i) (x i) (h i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, localA5Output (Ideal.span {p i}) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i)) *
        (∏ i ∈ (Finset.univ : Finset ι) \ A,
          localA5Kernel (Ideal.span {p i}) (hgood i)
            (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
              ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
            (j i) (σ i) (ε i) (x i) 0) := by
  classical
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let f : ∀ i, (O ⧸ Ideal.span {p i}) → ℂ := fun i h =>
    localA5Kernel (Ideal.span {p i}) (hgood i)
      (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
      (j i) (σ i) (ε i) (x i) h
  let D : ι → ℂ := fun i => localA5Output (Ideal.span {p i}) (hgood i)
    (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
    (j i) (σ i) (ε i) (x i)
  have hzero : ∀ i, j i ≠ 0 → f i 0 = 0 := by
    intro i hj
    simp only [f, localA5Kernel_zero, ite_eq_right hj]
  have hactive : ∀ i, (∑ u : (O ⧸ Ideal.span {p i})ˣ,
      f i (u : O ⧸ Ideal.span {p i})) = 1 * D i := by
    intro i
    simp only [one_mul, f, D]
    exact localA5Kernel_active_eq_output (Ideal.span {p i})
      (hgood i) (hchar i)
      (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
      (PrimitiveTrace.eisTraceModChar_breveE_ne_one
        (Ideal.span {p i}) (p i) rfl (hp i))
      (j i) (hj6 i) (σ i) (ε i) (x i)
  have h := FixedRayActiveSet.assemble_local_A5
    (fun i => O ⧸ Ideal.span {p i}) j f (fun _ => 1) D hzero hactive
  simpa only [f, D, one_mul] using h

theorem actual_crt_product_assembly
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    [Fintype (O ⧸ ⨅ i, Ideal.span {p i})]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i}))
    (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (ε x : ∀ i, O ⧸ Ideal.span {p i}) :
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let e : (O ⧸ ⨅ i, P i) ≃+* ∀ i, O ⧸ P i :=
      Ideal.quotientInfRingEquivPiQuotient P (by
        intro i k hik
        exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik))
    (∑ z : O ⧸ ⨅ i, P i,
      ∏ i, localA5Kernel (P i) (hgood i)
        (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
        (j i) (σ i) (ε i) (x i) (e z i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, localA5Output (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i)) *
        (∏ i ∈ (Finset.univ : Finset ι) \ A,
          localA5Kernel (P i) (hgood i)
            (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
              ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
            (j i) (σ i) (ε i) (x i) 0) := by
  classical
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  have hcop : Pairwise (fun i k => IsCoprime (P i) (P k)) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik)
  let e : (O ⧸ ⨅ i, P i) ≃+* ∀ i, O ⧸ P i :=
    Ideal.quotientInfRingEquivPiQuotient P hcop
  have hsum :
      (∑ z : O ⧸ ⨅ i, P i,
        ∏ i, localA5Kernel (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i) (e z i)) =
      ∑ h : ∀ i, O ⧸ P i,
        ∏ i, localA5Kernel (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i) (h i) := by
    apply Fintype.sum_equiv e.toEquiv
    intro z
    rfl
  dsimp only
  rw [hsum]
  exact actual_local_product_assembly p hp hgood hchar j hj6 σ ε x

@[instance_reducible] noncomputable def crtIntersectionFintype
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i})) :
    Fintype (O ⧸ ⨅ i, Ideal.span {p i}) := by
  classical
  letI (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  have hcop : Pairwise
      (fun i k => IsCoprime (Ideal.span {p i}) (Ideal.span {p k})) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik)
  let e := Ideal.quotientInfRingEquivPiQuotient
    (fun i => Ideal.span {p i}) hcop
  exact Fintype.ofEquiv (∀ i, O ⧸ Ideal.span {p i}) e.symm.toEquiv

theorem actual_crt_product_assembly_finite
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i}))
    (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj6 : ∀ i, j i < 6)
    (σ : ∀ i, (O ⧸ Ideal.span {p i})ˣ)
    (ε x : ∀ i, O ⧸ Ideal.span {p i}) :
    letI : Fintype (O ⧸ ⨅ i, Ideal.span {p i}) :=
      crtIntersectionFintype p hdistinct
    let P : ι → Ideal O := fun i => Ideal.span {p i}
    let e : (O ⧸ ⨅ i, P i) ≃+* ∀ i, O ⧸ P i :=
      Ideal.quotientInfRingEquivPiQuotient P (by
        intro i k hik
        exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik))
    (∑ z : O ⧸ ⨅ i, P i,
      ∏ i, localA5Kernel (P i) (hgood i)
        (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
        (j i) (σ i) (ε i) (x i) (e z i)) =
      ∑ A ∈ ((Finset.univ : Finset ι).powerset.filter
        (fun A => (Finset.univ.filter (fun i => j i ≠ 0)) ⊆ A)),
        (∏ i ∈ A, localA5Output (P i) (hgood i)
          (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
            ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
          (j i) (σ i) (ε i) (x i)) *
        (∏ i ∈ (Finset.univ : Finset ι) \ A,
          localA5Kernel (P i) (hgood i)
            (ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
              ConcreteBreveE.breveE_period_coordinates (p i) (hp i))
            (j i) (σ i) (ε i) (x i) 0) := by
  classical
  let : Fintype (O ⧸ ⨅ i, Ideal.span {p i}) :=
    crtIntersectionFintype p hdistinct
  exact actual_crt_product_assembly p hdistinct hp hgood hchar j hj6 σ ε x

end

theorem canonicalSextic_sixth_power_mask (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (a : O) :
    canonicalSextic P hgood (Ideal.Quotient.mk P (a ^ 6)) =
      if a ∈ P then 0 else 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  rw [map_pow, ShortDraftSextic.sextic_power_is_unit_mask
    (canonicalSextic P hgood) (canonicalSextic_pow_six P hgood)]
  by_cases ha : a ∈ P
  · simp [ha, isUnit_iff_ne_zero, Ideal.Quotient.eq_zero_iff_mem]
  · simp [ha, isUnit_iff_ne_zero, Ideal.Quotient.eq_zero_iff_mem]

end ActualEisensteinCubic

namespace PoissonFirstLocal

private def localA (ε : Bool) (p : ℕ) : ℕ := if ε then p else 1
private def localC (parityBit ε₁ ε₂ : Bool) (p : ℕ) : ℕ :=
  if localE parityBit ε₁ ε₂ = 0 then 1 else p
private def localCorrectionE (parityBit ε₁ ε₂ : Bool) (p : ℕ) : ℕ :=
  if parityBit then localA ε₁ p * localA ε₂ p else 1
private def localS (parityBit : Bool) (p : ℕ) : ℕ := if parityBit then p else 1
private def localJ2 (parityBit ε₁ ε₂ : Bool) (p : ℕ) : ℕ :=
  if !parityBit && ε₁ && ε₂ then p else 1

theorem first_poisson_local_scale_identity
    (parityBit ε₁ ε₂ : Bool) (p : ℕ) :
    localC parityBit ε₁ ε₂ p * localCorrectionE parityBit ε₁ ε₂ p *
        (localJ2 parityBit ε₁ ε₂ p) ^ 2 =
      localA ε₁ p * localA ε₂ p * localS parityBit p := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;>
    simp [localC, localCorrectionE, localJ2, localS, localA,
      localE, bit,
      show (1 : ZMod 6) ≠ 0 by decide,

      show (3 : ZMod 6) ≠ 0 by decide,
      ] <;> ring_nf <;>
      (intro h; exfalso; revert h; decide)

theorem first_poisson_global_scale_identity
    (P : Finset ℕ) (parityBit ε₁ ε₂ : ℕ → Bool) :
    (∏ p ∈ P, localC (parityBit p) (ε₁ p) (ε₂ p) p) *
      (∏ p ∈ P, localCorrectionE (parityBit p) (ε₁ p) (ε₂ p) p) *
      (∏ p ∈ P, localJ2 (parityBit p) (ε₁ p) (ε₂ p) p) ^ 2 =
    (∏ p ∈ P, localA (ε₁ p) p) *
      (∏ p ∈ P, localA (ε₂ p) p) *
      (∏ p ∈ P, localS (parityBit p) p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    simp only [Finset.prod_insert hp]
    calc
      (localC (parityBit p) (ε₁ p) (ε₂ p) p *
          ∏ q ∈ P, localC (parityBit q) (ε₁ q) (ε₂ q) q) *
        (localCorrectionE (parityBit p) (ε₁ p) (ε₂ p) p *
          ∏ q ∈ P, localCorrectionE (parityBit q) (ε₁ q) (ε₂ q) q) *
        (localJ2 (parityBit p) (ε₁ p) (ε₂ p) p *
          ∏ q ∈ P, localJ2 (parityBit q) (ε₁ q) (ε₂ q) q) ^ 2 =
        (localC (parityBit p) (ε₁ p) (ε₂ p) p *
          localCorrectionE (parityBit p) (ε₁ p) (ε₂ p) p *
          localJ2 (parityBit p) (ε₁ p) (ε₂ p) p ^ 2) *
        ((∏ q ∈ P, localC (parityBit q) (ε₁ q) (ε₂ q) q) *
          (∏ q ∈ P, localCorrectionE (parityBit q) (ε₁ q) (ε₂ q) q) *
          (∏ q ∈ P, localJ2 (parityBit q) (ε₁ q) (ε₂ q) q) ^ 2) := by ring
      _ = (localA (ε₁ p) p * localA (ε₂ p) p * localS (parityBit p) p) *
        ((∏ q ∈ P, localA (ε₁ q) q) *
          (∏ q ∈ P, localA (ε₂ q) q) *
          (∏ q ∈ P, localS (parityBit q) q)) := by
        rw [first_poisson_local_scale_identity, ih]
      _ = (localA (ε₁ p) p * ∏ q ∈ P, localA (ε₁ q) q) *
          (localA (ε₂ p) p * ∏ q ∈ P, localA (ε₂ q) q) *
          (localS (parityBit p) p * ∏ q ∈ P, localS (parityBit q) q) := by ring

end PoissonFirstLocal

end

end OAI
end OAIOriginalModule0043

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase
Source SHA256: 2928d469a01996582b4c0ed9c3795d3ddde5a34c76b636a95616550858bf0ccb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0044


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

namespace TraceLambdaPhase

open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped ComplexConjugate

theorem eisLam_sq : eisLam ^ 2 = (-3 : ℂ) := by
  change (1 + 2 * omega3) ^ 2 = -3
  linear_combination 4 * omega3_sq

theorem exp_minus_four_pi_div_three :
    Complex.exp (-(4 : ℂ) * Real.pi * Complex.I / 3) = omega3 := by
  have hshift : Complex.exp (-(4 : ℂ) * Real.pi * Complex.I / 3) =
      Complex.exp ((2 : ℂ) * Real.pi * Complex.I / 3) := by
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-1, ?_⟩
    push_cast
    ring
  rw [hshift]
  have harg : ((2 : ℂ) * Real.pi * Complex.I / 3) =
      (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I]
  have htwo : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  rw [htwo, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  unfold omega3
  push_cast
  ring

theorem breveE_traceLambda_square :
    ShortDraftTrace.breveE (1 / (eisLam * eisLam)) = omega3 := by
  have harg : (1 : ℂ) / (eisLam * eisLam) = -(1 : ℂ) / 3 := by
    rw [← pow_two, eisLam_sq]
    ring
  rw [harg]
  change Complex.exp (2 * Real.pi * Complex.I *
    ((-(1 : ℂ) / 3) + conj (-(1 : ℂ) / 3))) = omega3
  have hconj : conj (-(1 : ℂ) / 3) = -(1 : ℂ) / 3 := by
    simp only [map_div₀, map_neg, map_one, map_ofNat]
  rw [hconj]
  convert exp_minus_four_pi_div_three using 1 ; ring_nf

end TraceLambdaPhase

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase

theorem traceLambda_ne_zero : traceLambda ≠ 0 := by
  intro h
  have hh := congrArg eisEmbedding h
  rw [eisEmbedding_traceLambda, map_zero] at hh
  exact eisLam_ne_zero hh

private theorem traceLambda_span_eq_lambda :
    Ideal.span {traceLambda} = Ideal.span {lambda} := by
  rw [traceLambda_eq_unit_mul_lambda]
  exact Ideal.span_singleton_mul_left_unit neg_omega_isUnit lambda

theorem traceLambda_quotient_card :
    Nat.card (O ⧸ Ideal.span {traceLambda}) = 3 := by
  rw [traceLambda_span_eq_lambda]
  exact ActualEisensteinSieve.lambda_card

private theorem traceLambda_quotient_maximal :
    (Ideal.span {traceLambda}).IsMaximal := by
  rw [traceLambda_span_eq_lambda]
  exact ActualEisensteinSieve.lambda_maximal

noncomputable def quadraticGammaTraceLambda : ℂ := by
  let c : O := traceLambda
  let hc : c ≠ 0 := traceLambda_ne_zero
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)

theorem quadraticGammaTraceLambda_eq_I : quadraticGammaTraceLambda = Complex.I := by
  let c : O := traceLambda
  let hc : c ≠ 0 := traceLambda_ne_zero
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  have hcard : Fintype.card (O ⧸ Ideal.span {c}) = 3 := by
    simpa only [Nat.card_eq_fintype_card] using traceLambda_quotient_card
  let e : ZMod 3 ≃+* (O ⧸ Ideal.span {c}) :=
    ZMod.ringEquivOfPrime _ Nat.prime_three hcard
  have hphase : ψ 1 = omega3 := by
    change ShortDraftTrace.breveE
      (eisEmbedding 1 / (eisEmbedding c * eisLam)) = omega3
    rw [map_one, show eisEmbedding c = eisLam from eisEmbedding_traceLambda]
    exact breveE_traceLambda_square
  have hsum : (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) = 1 + 2 * omega3 := by
    have hreindex := (e.toEquiv.sum_comp (fun x : O ⧸ Ideal.span {c} => ψ (x ^ 2))).symm
    rw [hreindex]
    have hfin : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
    rw [hfin]
    rw [Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3))),
      Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3))),
      Finset.sum_singleton]
    have h2sq : (2 : ZMod 3) ^ 2 = 1 := by decide
    have he2 : e (2 : ZMod 3) ^ 2 = 1 := by
      rw [← map_pow, h2sq, map_one]
    change ψ (e (0 : ZMod 3) ^ 2) +
      (ψ (e (1 : ZMod 3) ^ 2) + ψ (e (2 : ZMod 3) ^ 2)) =
        1 + 2 * omega3
    simp only [map_zero, map_one, zero_pow (by decide : 2 ≠ 0),
      one_pow, he2, map_zero_eq_one, hphase]
    ring
  have hLam : eisLam = (Real.sqrt 3 : ℝ) * Complex.I := by
    unfold eisLam omega3
    ring
  have hnorm : ‖eisEmbedding c‖ = Real.sqrt 3 := by
    rw [show eisEmbedding c = eisLam from eisEmbedding_traceLambda, hLam,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 (by norm_num))]
  unfold quadraticGammaTraceLambda
  change (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
      (‖eisEmbedding c‖ : ℂ) = Complex.I
  rw [hsum, hnorm]
  change eisLam / ((Real.sqrt 3 : ℝ) : ℂ) = Complex.I
  rw [hLam]
  field_simp

end ActualEisensteinCubic

namespace PoissonFirstLocal
open scoped Classical

def quotientUnitMask {R : Type*} [CommRing R] (z : R) : ℂ :=
  if IsUnit z then 1 else 0

private theorem quotientUnitMask_mul {R : Type*} [CommRing R]
    (a b : R) :
    quotientUnitMask (a * b) =
      quotientUnitMask a * quotientUnitMask b := by
  classical
  by_cases ha : IsUnit a <;> by_cases hb : IsUnit b <;>
    simp [quotientUnitMask, (Commute.all a b).isUnit_mul_iff, ha, hb]

def oldFactorRing {R : Type*} [CommRing R]
    (side parityBit ε₁ ε₂ : Bool) (z : R) (χ : MulChar R ℂ) : ℂ :=
  let q := χ z
  quotientUnitMask z * q ^ (4 * bit (if side then ε₂ else ε₁)) *
    q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
    q ^ EExp parityBit ε₁ ε₂

def newFactorRing {R : Type*} [CommRing R]
    (parityBit ε₁ ε₂ : Bool) (z : R) (χ : MulChar R ℂ) : ℂ :=
  if retained parityBit ε₁ ε₂ then (χ z) ^ 4 else quotientUnitMask z

theorem first_local_identity_ring {R : Type*} [CommRing R]
    (side parityBit ε₁ ε₂ : Bool)
    (z : R) (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1) :
    oldFactorRing side parityBit ε₁ ε₂ z χ =
      newFactorRing parityBit ε₁ ε₂ z χ := by
  let q := χ z
  by_cases hu : IsUnit z
  · have h6 : q ^ 6 = 1 := by
      dsimp [q]
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
      simp [MulChar.one_apply, hu]
    have hmask : quotientUnitMask z = 1 := by
      simp [quotientUnitMask, hu]
    change quotientUnitMask z * q ^ (4 * bit (if side then ε₂ else ε₁)) *
      q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
      q ^ EExp parityBit ε₁ ε₂ =
        (if retained parityBit ε₁ ε₂ then q ^ 4 else quotientUnitMask z)
    rw [hmask, one_mul, ← pow_add, ← pow_add]
    cases side
    · change q ^ (totalExp₁ parityBit ε₁ ε₂) =
        (if retained parityBit ε₁ ε₂ then q ^ 4 else 1)
      rw [pow_eq_pow_mod _ h6, (exponent_table parityBit ε₁ ε₂).1]
      split_ifs <;> simp
    · change q ^ (totalExp₂ parityBit ε₁ ε₂) =
        (if retained parityBit ε₁ ε₂ then q ^ 4 else 1)
      rw [pow_eq_pow_mod _ h6, (exponent_table parityBit ε₁ ε₂).2]
      split_ifs <;> simp
  · have hz : q = 0 := MulChar.map_nonunit χ hu
    simp [oldFactorRing, newFactorRing, quotientUnitMask, hu]

theorem first_prime_product_identity_ring
    {R : Type*} [CommRing R]
    (side : Bool) (P : Finset R)
    (parityBit ε₁ ε₂ : R → Bool)
    (χ : MulChar R ℂ) (hχ : χ ^ 6 = 1) :
    (∏ z ∈ P, oldFactorRing side (parityBit z) (ε₁ z) (ε₂ z) z χ) =
      (χ (∏ z ∈ P with retained (parityBit z) (ε₁ z) (ε₂ z), z)) ^ 4 *
      quotientUnitMask
        (∏ z ∈ P with ¬retained (parityBit z) (ε₁ z) (ε₂ z), z) := by
  classical
  calc
    (∏ z ∈ P, oldFactorRing side (parityBit z) (ε₁ z) (ε₂ z) z χ) =
      ∏ z ∈ P, newFactorRing (parityBit z) (ε₁ z) (ε₂ z) z χ := by
        apply Finset.prod_congr rfl
        intro z hz
        exact first_local_identity_ring side (parityBit z) (ε₁ z) (ε₂ z) z χ hχ
    _ = (∏ z ∈ P with retained (parityBit z) (ε₁ z) (ε₂ z),
          (χ z) ^ 4) *
        (∏ z ∈ P with ¬retained (parityBit z) (ε₁ z) (ε₂ z),
          quotientUnitMask z) := by
        simp only [newFactorRing]
        exact Finset.prod_ite _ _
    _ = _ := by
      have hchar (S : Finset R) :
          (∏ z ∈ S, (χ z) ^ 4) = (χ (∏ z ∈ S, z)) ^ 4 := by
        induction S using Finset.induction_on with
        | empty => simp
        | @insert z S hz ih => simp [hz, ih, map_mul, mul_pow]
      have hmask (S : Finset R) :
          (∏ z ∈ S, quotientUnitMask z) =
            quotientUnitMask (∏ z ∈ S, z) := by
        induction S using Finset.induction_on with
        | empty => simp [quotientUnitMask]
        | @insert z S hz ih =>
            simp [hz, ih, quotientUnitMask_mul]
      rw [hchar, hmask]

end PoissonFirstLocal

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE TraceLambdaPhase

noncomputable def quadraticGammaNegTraceLambda : ℂ := by
  let c : O := -traceLambda
  let hc : c ≠ 0 := neg_ne_zero.mpr traceLambda_ne_zero
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  exact (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)

theorem quadraticGammaNegTraceLambda_eq_neg_I :
    quadraticGammaNegTraceLambda = -Complex.I := by
  let c : O := -traceLambda
  let hc : c ≠ 0 := neg_ne_zero.mpr traceLambda_ne_zero
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE breveE_period_coordinates c hc
  have hspan : Ideal.span {c} = Ideal.span {traceLambda} := by
    change Ideal.span {-traceLambda} = Ideal.span {traceLambda}
    rw [show -traceLambda = (-1 : O) * traceLambda by ring]
    exact Ideal.span_singleton_mul_left_unit isUnit_neg_one traceLambda
  have hcard : Fintype.card (O ⧸ Ideal.span {c}) = 3 := by
    have hcardNat : Nat.card (O ⧸ Ideal.span {c}) = 3 := by
      rw [hspan]
      exact traceLambda_quotient_card
    simpa only [Nat.card_eq_fintype_card] using hcardNat
  let e : ZMod 3 ≃+* (O ⧸ Ideal.span {c}) :=
    ZMod.ringEquivOfPrime _ Nat.prime_three hcard
  have hphase : ψ 1 = omega3⁻¹ := by
    change ShortDraftTrace.breveE
      (eisEmbedding 1 / (eisEmbedding c * eisLam)) = omega3⁻¹
    rw [map_one, show eisEmbedding c = -eisLam by
      simp only [c, map_neg, eisEmbedding_traceLambda]]
    have harg : (1 : ℂ) / (-eisLam * eisLam) =
        -((1 : ℂ) / (eisLam * eisLam)) := by ring
    rw [harg, ShortDraftTrace.breveE.map_neg_eq_inv,
      breveE_traceLambda_square]
  have hsum : (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) =
      1 + 2 * omega3⁻¹ := by
    have hreindex := (e.toEquiv.sum_comp (fun x : O ⧸ Ideal.span {c} => ψ (x ^ 2))).symm
    rw [hreindex]
    have hfin : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
    rw [hfin]
    rw [Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3))),
      Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3))),
      Finset.sum_singleton]
    have h2sq : (2 : ZMod 3) ^ 2 = 1 := by decide
    have he2 : e (2 : ZMod 3) ^ 2 = 1 := by
      rw [← map_pow, h2sq, map_one]
    change ψ (e (0 : ZMod 3) ^ 2) +
      (ψ (e (1 : ZMod 3) ^ 2) + ψ (e (2 : ZMod 3) ^ 2)) =
        1 + 2 * omega3⁻¹
    simp only [map_zero, map_one, zero_pow (by decide : 2 ≠ 0),
      one_pow, he2, map_zero_eq_one, hphase]
    ring
  have hωcube : omega3 ^ 3 = 1 := by
    linear_combination (omega3 - 1) * omega3_sq
  have hωinv : omega3⁻¹ = omega3 ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using hωcube
  have hsumval : 1 + 2 * omega3⁻¹ = -eisLam := by
    rw [hωinv]
    dsimp [eisLam]
    linear_combination 2 * omega3_sq
  have hLam : eisLam = (Real.sqrt 3 : ℝ) * Complex.I := by
    unfold eisLam omega3
    ring
  have hnorm : ‖eisEmbedding c‖ = Real.sqrt 3 := by
    rw [show eisEmbedding c = -eisLam by
      simp only [c, map_neg, eisEmbedding_traceLambda], norm_neg, hLam,
      norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 (by norm_num))]
  unfold quadraticGammaNegTraceLambda
  change (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) /
      (‖eisEmbedding c‖ : ℂ) = -Complex.I
  rw [hsum, hsumval, hnorm, hLam]
  field_simp

end

noncomputable def finiteSquarefreeRow
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (u : O) : ℂ :=
  ∏ i ∈ S, canonicalSextic (P i) (hgood i) (Ideal.Quotient.mk (P i) u)

theorem finiteSquarefreeRow_sixth_power
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSquarefreeRow P hgood S (a ^ 6) =
      if ∃ i ∈ S, a ∈ P i then 0 else 1 := by
  classical
  simp only [finiteSquarefreeRow]
  by_cases hex : ∃ i ∈ S, a ∈ P i
  · obtain ⟨i, hi, hai⟩ := hex
    rw [ite_eq_left ⟨i, hi, hai⟩]
    apply Finset.prod_eq_zero hi
    rw [canonicalSextic_sixth_power_mask]
    simp [hai]
  · rw [ite_eq_right hex]
    apply Finset.prod_eq_one
    intro i hi
    rw [canonicalSextic_sixth_power_mask]
    simp [show a ∉ P i by intro hai; exact hex ⟨i, hi, hai⟩]

theorem finiteSquarefreeRow_difference
    {ι N : Type*} [DecidableEq N]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset N) (support : N → Finset ι)
    (weight : N → ℂ) (a : O) :
    (∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (a ^ 6)) =
      ∑ n ∈ columns.filter (fun n => ∃ i ∈ support n, a ∈ P i), weight n := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [finiteSquarefreeRow_sixth_power]
  by_cases h : ∃ i ∈ support n, a ∈ P i <;> simp [h]

theorem finiteSquarefreeRow_difference_norm
    {ι N : Type*} [DecidableEq N]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset N) (support : N → Finset ι)
    (weight : N → ℂ) (a : O) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (a ^ 6))‖ ≤
      ∑ n ∈ columns.filter (fun n => ∃ i ∈ support n, a ∈ P i), ‖weight n‖ := by
  rw [finiteSquarefreeRow_difference]
  exact norm_sum_le _ _

theorem first_local_identity_canonicalSextic
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (side parityBit ε₁ ε₂ : Bool) (z : O ⧸ P) :
    PoissonFirstLocal.oldFactorRing side parityBit ε₁ ε₂ z
        (canonicalSextic P hgood) =
      PoissonFirstLocal.newFactorRing parityBit ε₁ ε₂ z
        (canonicalSextic P hgood) := by
  exact PoissonFirstLocal.first_local_identity_ring
    side parityBit ε₁ ε₂ z (canonicalSextic P hgood)
    (canonicalSextic_pow_six P hgood)

theorem first_prime_product_canonicalSextic
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (S : Finset (O ⧸ P))
    (parityBit ε₁ ε₂ : O ⧸ P → Bool) (side : Bool) :
    (∏ z ∈ S,
      PoissonFirstLocal.oldFactorRing side
        (parityBit z) (ε₁ z) (ε₂ z) z
        (canonicalSextic P hgood)) =
      (canonicalSextic P hgood
        (∏ z ∈ S with
          PoissonFirstLocal.retained (parityBit z) (ε₁ z) (ε₂ z), z)) ^ 4 *
      PoissonFirstLocal.quotientUnitMask
        (∏ z ∈ S with
          ¬PoissonFirstLocal.retained (parityBit z) (ε₁ z) (ε₂ z), z) := by
  exact PoissonFirstLocal.first_prime_product_identity_ring side S
    parityBit ε₁ ε₂ (canonicalSextic P hgood)
    (canonicalSextic_pow_six P hgood)

end ActualEisensteinCubic

namespace AnalyticBridge

theorem first_poisson_y_ball_of_scale_identity
    (L B F K A1 A2 C d c E s J2 J h y Y : ℝ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hK : 0 < K) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hC : 0 < C) (hd : 0 ≤ d) (hc : 0 ≤ c)
    (hE : 0 ≤ E) (hs : 0 ≤ s) (hJ2 : 1 ≤ J2)
    (hJ : J = s * J2) (hJpos : 0 < J)
    (hJdyad : J ≤ B ^ 2) (hh : 0 ≤ h)
    (hscale : c * E * J2 ^ 2 = A1 * A2 * s)
    (hfrequency : h ≤ L ^ 2 * c * d / (K * A1 * A2 * C ^ 2))
    (hy : y ≤ h * F ^ 2 * E)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J)) :
    y ≤ Y := by
  have hdenA : A1 * A2 ≠ 0 := (mul_pos hA1 hA2).ne'
  have hdenJ2 : J2 ^ 2 ≠ 0 := by positivity
  have hratioeq : c * E / (A1 * A2) = s / J2 ^ 2 := by
    apply (div_eq_div_iff hdenA hdenJ2).mpr
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hscale
  have hratio := first_poisson_local_ratio_bound c E A1 A2 s J2 J B
    hc hE hA1 hA2 hs hJ2 hB hJ hJpos hJdyad hratioeq
  exact first_poisson_y_ball L B F K A1 A2 C d c E J h y Y
    hL hB hF hK hA1 hA2 hC hd hc hE hJpos hh
    hfrequency hy hratio hY

end AnalyticBridge

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

private def cuspMatrix (a b c d : R) : Matrix (Fin 2) (Fin 2) R := !![a,b;c,d]
private def unramifiedH (u : R) : Matrix (Fin 2) (Fin 2) R := U u * E
private def unramifiedHInv (u : R) : Matrix (Fin 2) (Fin 2) R := !![0,1;-1,u]

theorem A3_principal_matrix (a b c d : R) :
    cuspMatrix a b c d * (1 : Matrix (Fin 2) (Fin 2) R) =
      !![a,b;c,d] := by
  simp [cuspMatrix]

theorem A3_ramified_inverse (u : R) :
    L u * L (-u) = (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [lower_add]
  simp [L, Matrix.one_fin_two]

theorem A3_ramified_inverse_left (u : R) :
    L (-u) * L u = (1 : Matrix (Fin 2) (Fin 2) R) := by
  rw [lower_add]
  simp [L, Matrix.one_fin_two]

theorem A3_ramified_matrix (a b c d u : R) :
    cuspMatrix a b c d * L (-u) =
      !![a - u * b,b;c - u * d,d] := by
  simp [cuspMatrix, L, mul_comm, sub_eq_add_neg]

theorem A3_unramified_H (u : R) :
    unramifiedH u = !![u,-1;1,0] := by
  simp [unramifiedH, U, E]

theorem A3_unramified_inverse_right (u : R) :
    unramifiedH u * unramifiedHInv u =
      (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp [unramifiedH, unramifiedHInv, U, E, Matrix.one_fin_two]

theorem A3_unramified_inverse_left (u : R) :
    unramifiedHInv u * unramifiedH u =
      (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp [unramifiedH, unramifiedHInv, U, E, Matrix.one_fin_two]

theorem A3_unramified_matrix (a b c d u : R) :
    cuspMatrix a b c d * unramifiedHInv u =
      !![-b,a + u * b;-d,c + u * d] := by
  simp [cuspMatrix, unramifiedHInv, mul_comm]

theorem A3_ramified_det_relation (a b c d u : R)
    (hdet : a * d - b * c = 1) :
    a * (c - u * d) - c * (a - u * b) = -u := by
  calc
    a * (c - u * d) - c * (a - u * b) =
        -u * (a * d - b * c) := by ring
    _ = -u := by rw [hdet]; ring

theorem A3_ramified_reciprocity_congr (a b cprime d u : R)
    (hdet : a * d - b * (u * cprime) = 1) :
    (a - u * b) * cprime = 1 + a * (cprime - d) := by
  calc
    (a - u * b) * cprime =
        a * cprime + (a * d - b * (u * cprime)) - a * d := by ring
    _ = 1 + a * (cprime - d) := by rw [hdet]; ring

theorem A3_unramified_det_relation (a b c d : R)
    (hdet : a * d - b * c = 1) :
    (-b) * c = 1 - a * d := by linear_combination hdet

theorem A3_unramified_inverse_congr (a b c d : R)
    (hdet : a * d - b * c = 1) :
    a * d = 1 + b * c := by linear_combination hdet

end ShortDraftCusp

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem breveE_quarter_trace (a b : ℤ) :
    ShortDraftTrace.breveE
      ((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) =
      Complex.I ^ b := by
  have htrace := ShortDraftTrace.trace_div_lam omega3 omega3_sq
    ShortDraftTrace.omega_conj a b
  have hconj : ∀ z : ℂ, star (z / 4) = star z / 4 := by
    intro z
    simp
  change Complex.exp (2 * Real.pi * Complex.I *
    (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
      star (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4)))) = _
  rw [hconj]
  have hL : ((a : ℂ) + (b : ℂ) * omega3) / eisLam +
      star (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = (b : ℂ) := by
    simpa only [eisLam, Complex.star_def] using htrace
  have harg : 2 * Real.pi * Complex.I *
      (((((a : ℂ) + (b : ℂ) * omega3) / eisLam) / 4) +
        (star (((a : ℂ) + (b : ℂ) * omega3) / eisLam)) / 4) =
      (b : ℂ) * (Real.pi / 2 * Complex.I) := by
    rw [← add_div, hL]
    ring
  rw [harg, Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

noncomputable def breveGaussianFourTerms (a b : ℤ) : ℂ :=
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  (ShortDraftTrace.breveE (0 : ℂ) +
      ShortDraftTrace.breveE (((-c) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * omega3 ^ 2) / eisLam) / 4) +
      ShortDraftTrace.breveE (((-c * (1 + omega3) ^ 2) / eisLam) / 4)) / 2

theorem breveGaussianFourTerms_formula (a b : ℤ) :
    breveGaussianFourTerms a b =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  let c : ℂ := (a : ℂ) + (b : ℂ) * omega3
  have hfirst : ShortDraftTrace.breveE (((-c) / eisLam) / 4) =
      Complex.I ^ (-b) := by
    have hc : -c = ((-a : ℤ) : ℂ) + ((-b : ℤ) : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      ring
    rw [hc]
    exact breveE_quarter_trace (-a) (-b)
  have hsecond : ShortDraftTrace.breveE
      (((-c * omega3 ^ 2) / eisLam) / 4) = Complex.I ^ a := by
    have hc : -c * omega3 ^ 2 = ((a-b : ℤ) : ℂ) + (a : ℂ) * omega3 := by
      dsimp [c]
      push_cast
      linear_combination -(a : ℂ) * omega3_sq -
        (b : ℂ) * (omega3 - 1) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace (a-b) a
  have hthird : ShortDraftTrace.breveE
      (((-c * (1 + omega3) ^ 2) / eisLam) / 4) =
      Complex.I ^ (b-a) := by
    have hω : (1 + omega3) ^ 2 = omega3 := by
      linear_combination omega3_sq
    have hc : -c * (1 + omega3) ^ 2 =
        (b : ℂ) + ((b-a : ℤ) : ℂ) * omega3 := by
      rw [hω]
      dsimp [c]
      push_cast
      linear_combination -(b : ℂ) * omega3_sq
    rw [hc]
    exact breveE_quarter_trace b (b-a)
  dsimp [breveGaussianFourTerms]
  rw [hfirst, hsecond, hthird]
  simp only [map_zero_eq_one]

end ActualEisensteinCubic

end

end OAI
end OAIOriginalModule0044

/-! Original module: OAI.NumberTheory.DirichletL.Arithmetic.LatticeCount
Source SHA256: bcb2d1b0ad32fed28220e805fbaa2bb7b758aebb36c2647217560af7e27c97c5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0045


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

namespace ShortDraftLatticeCount

def q (x : ℤ × ℤ) : ℤ := x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem coordinate_squares (a b D : ℤ) (hD : 0 ≤ D)
    (h : a ^ 2 - a * b + b ^ 2 ≤ D) :
    a ^ 2 ≤ 2 * D ∧ b ^ 2 ≤ 2 * D := by
  constructor <;> nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (2 * a - b)]

theorem finite_lattice_count (S : Finset (ℤ × ℤ)) (D R : ℕ)
    (hR : 2 * D < R ^ 2)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ (2 * R + 1) ^ 2 := by
  let I : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)
  have hbox : S ⊆ I.product I := by
    intro x hx
    rcases x with ⟨a, b⟩
    have hD : (0 : ℤ) ≤ D := by positivity
    obtain ⟨ha, hb⟩ := coordinate_squares a b D hD (hS (a, b) hx)
    have hR' : 2 * (D : ℤ) < (R : ℤ) ^ 2 := by exact_mod_cast hR
    have hRnonneg : (0 : ℤ) ≤ R := by positivity
    apply Finset.mem_product.mpr
    constructor <;> simp only [I, Finset.mem_Icc] <;> constructor <;>
      nlinarith [sq_nonneg (a - R),
      sq_nonneg (a + R), sq_nonneg (b - R), sq_nonneg (b + R)]
  have hI : I.card = 2 * R + 1 := by
    dsimp [I]
    rw [Int.card_Icc]
    have hcast : (R : ℤ) + 1 + (R : ℤ) = ((R + 1 + R : ℕ) : ℤ) := by
      push_cast
      ring
    rw [sub_neg_eq_add, hcast, Int.toNat_natCast]
    ring
  calc
    S.card ≤ (I.product I).card := Finset.card_le_card hbox
    _ = I.card * I.card := Finset.card_product _ _
    _ = (2 * R + 1) ^ 2 := by rw [hI]; ring

theorem finite_lattice_count_linear (S : Finset (ℤ × ℤ)) (D : ℕ)
    (hS : ∀ x ∈ S, q x ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hR : 2 * D < (Nat.sqrt (2 * D) + 1) ^ 2 := by
    exact Nat.lt_succ_sqrt' _
  have hcount := finite_lattice_count S D (Nat.sqrt (2 * D) + 1) hR hS
  have hsquare : (Nat.sqrt (2 * D)) ^ 2 ≤ 2 * D := Nat.sqrt_le' _
  have hroot : Nat.sqrt (2 * D) ≤ 2 * D := Nat.sqrt_le_self _
  nlinarith

theorem actual_eisenstein_count
    (S : Finset ActualEisensteinCoordinates.O) (D : ℕ)
    (hS : ∀ x ∈ S, q (ActualEisensteinCoordinates.coords x) ≤ D) :
    S.card ≤ 64 * (D + 1) := by
  have hinj : Function.Injective ActualEisensteinCoordinates.coords := by
    intro x y hxy
    calc
      x = ActualEisensteinCoordinates.eval
          (ActualEisensteinCoordinates.coords x).1
          (ActualEisensteinCoordinates.coords x).2 :=
        (ActualEisensteinCoordinates.eval_coords x).symm
      _ = ActualEisensteinCoordinates.eval
          (ActualEisensteinCoordinates.coords y).1
          (ActualEisensteinCoordinates.coords y).2 := by rw [hxy]
      _ = y := ActualEisensteinCoordinates.eval_coords y
  have himage : (S.image ActualEisensteinCoordinates.coords).card = S.card :=
    Finset.card_image_of_injective S hinj
  have hbound : ∀ v ∈ S.image ActualEisensteinCoordinates.coords,
      q v ≤ D := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact hS x hx
  calc
    S.card = (S.image ActualEisensteinCoordinates.coords).card := himage.symm
    _ ≤ 64 * (D + 1) := finite_lattice_count_linear _ D hbound

end ShortDraftLatticeCount

namespace ActualEisensteinCubic

open ShortDraftCusp

theorem A3_cubicChar_neg_one
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) :
    cubicChar P hgood (-1 : O ⧸ P) = 1 := by
  let χ := cubicChar P hgood
  have hcube : χ (-1 : O ⧸ P) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply isUnit_neg_one
  have hminus : (-1 : O ⧸ P) ^ 3 = -1 := by ring
  calc
    χ (-1 : O ⧸ P) = χ ((-1 : O ⧸ P) ^ 3) := by rw [hminus]
    _ = χ (-1 : O ⧸ P) ^ 3 := by rw [map_pow]
    _ = 1 := hcube

theorem A3_ramified_local_character
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (a b c d u : O) (hdet : a * d - b * c = 1)
    (hA : a - u * b ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P a) *
      cubicChar P hgood (Ideal.Quotient.mk P (c - u * d)) =
      cubicChar P hgood (Ideal.Quotient.mk P (-u)) := by
  have hA0 : Ideal.Quotient.mk P (a - u * b) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hA
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_ramified_det_relation a b c d u hdet)
  simp only [map_sub, map_mul, map_neg, hA0, mul_zero, sub_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_sub, map_neg] using hh

theorem A3_ramified_reciprocity_local_character
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (a b cprime d u : O)
    (hdet : a * d - b * (u * cprime) = 1)
    (ha : a ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P (a - u * b)) *
      cubicChar P hgood (Ideal.Quotient.mk P cprime) = 1 := by
  have ha0 : Ideal.Quotient.mk P a = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr ha
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_ramified_reciprocity_congr a b cprime d u hdet)
  simp only [map_sub, map_mul, map_add, map_one, ha0, zero_mul,
    add_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_sub, map_one, ha0, zero_sub, add_zero] using hh

theorem A3_unramified_local_character
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (a b c d : O) (hdet : a * d - b * c = 1)
    (hb : -b ∈ P) :
    cubicChar P hgood (Ideal.Quotient.mk P a) *
      cubicChar P hgood (Ideal.Quotient.mk P d) = 1 := by
  have hb0 : Ideal.Quotient.mk P (-b) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr hb
  have hrel := congrArg (Ideal.Quotient.mk P)
    (A3_unramified_inverse_congr a b c d hdet)
  simp only [map_mul, map_add, map_one] at hrel
  have hbb : Ideal.Quotient.mk P b = 0 := by
    have h := congrArg Neg.neg hb0
    simpa only [map_neg, neg_zero, neg_neg] using h
  simp only [hbb, zero_mul, add_zero] at hrel
  have hh := congrArg (cubicChar P hgood) hrel
  simpa only [map_mul, map_one] using hh

end ActualEisensteinCubic

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

theorem A3_coprime_a_c (a b c d : R)
    (hdet : a * d - b * c = 1) : IsCoprime a c := by
  refine ⟨d, -b, ?_⟩
  linear_combination hdet

theorem A3_coprime_a_b (a b c d : R)
    (hdet : a * d - b * c = 1) : IsCoprime a b := by
  refine ⟨d, -c, ?_⟩
  linear_combination hdet

theorem A3_ramified_coprime_a_A (a b cprime d u : R)
    (hdet : a * d - b * (u * cprime) = 1) :
    IsCoprime a (a - u * b) := by
  refine ⟨d - cprime, cprime, ?_⟩
  linear_combination hdet

theorem A3_unramified_coprime_a_minus_b (a b c d : R)
    (hdet : a * d - b * c = 1) : IsCoprime a (-b) := by
  refine ⟨d, c, ?_⟩
  linear_combination hdet

end ShortDraftCusp

namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates

theorem coords_eval (a b : ℤ) :
    coords (eval a b) = (a, b) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext h.1 h.2

theorem qO_mul (x y : O) :
    q (coords (x * y)) = q (coords x) * q (coords y) := by
  have hxy : x * y = eval
      ((coords x).1 * (coords y).1 - (coords x).2 * (coords y).2)
      ((coords x).1 * (coords y).2 + (coords x).2 * (coords y).1 -
        (coords x).2 * (coords y).2) := by
    calc
      x * y = eval (coords x).1 (coords x).2 *
          eval (coords y).1 (coords y).2 := by rw [eval_coords, eval_coords]
      _ = _ := eval_mul _ _ _ _
  rw [hxy, coords_eval]
  exact ShortDraft.eisenstein_norm_mul (coords x) (coords y)

theorem qO_nonneg (x : O) : 0 ≤ q (coords x) := by
  exact ShortDraft.eisenstein_norm_nonneg (coords x)

theorem qO_pos {x : O} (hx : x ≠ 0) : 0 < q (coords x) := by
  have hne : q (coords x) ≠ 0 := by
    intro hzero
    have hc : coords x = (0, 0) :=
      (ShortDraft.eisenstein_norm_eq_zero_iff (coords x)).mp hzero
    apply hx
    calc
      x = eval (coords x).1 (coords x).2 := (eval_coords x).symm
      _ = 0 := by simp [hc, eval]
  exact lt_of_le_of_ne (qO_nonneg x) (Ne.symm hne)

def qNat (x : O) : ℕ := (q (coords x)).toNat

theorem qNat_mul (x y : O) : qNat (x * y) = qNat x * qNat y := by
  unfold qNat
  rw [qO_mul]
  exact Int.toNat_mul (qO_nonneg x) (qO_nonneg y)

theorem qNat_pos {x : O} (hx : x ≠ 0) : 0 < qNat x := by
  unfold qNat
  have hcast := Int.toNat_of_nonneg (qO_nonneg x)
  have hpos := qO_pos hx
  omega

theorem finite_multiples_count
    (p : O) (hp : p ≠ 0) (T : Finset O) (D : ℕ)
    (hT : ∀ x ∈ T, qNat (p * x) ≤ D) :
    T.card ≤ 64 * (D / qNat p + 1) := by
  have hbound : ∀ x ∈ T, q (coords x) ≤ (D / qNat p : ℕ) := by
    intro x hx
    have hmul := hT x hx
    rw [qNat_mul] at hmul
    have hdiv : qNat x ≤ D / qNat p :=
      (Nat.le_div_iff_mul_le (qNat_pos hp)).mpr (by
        simpa [mul_comm] using hmul)
    have hnat : qNat x = (q (coords x)) :=
      Int.toNat_of_nonneg (qO_nonneg x)
    have hdiv' : (qNat x : ℤ) ≤ (D / qNat p : ℕ) := by
      exact_mod_cast hdiv
    simpa only [hnat] using hdiv'
  exact actual_eisenstein_count T (D / qNat p) hbound

end ShortDraftLatticeCount

namespace AnalyticBridge

private def CRTChoice.childPair (q : CRTChoice) : ℕ × ℕ :=
  (q.d * q.e * q.kpp, q.J * q.C * q.e * q.v)

theorem second_passage_weighted_fiber
    (Q : Finset CRTChoice) (F K b0 : ℕ)
    (hF : F ≠ 0) (hK : K ≠ 0) (hb0 : b0 ≠ 0)
    (hQ : ∀ q ∈ Q,
      q.J * q.C * q.e * q.v = F ∧
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ F * b0 ∧ q.d * q.e * q.kpp = K)
    (w : CRTChoice → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hw : ∀ q ∈ Q, w q ≤ M) :
    (∑ q ∈ Q, w q) ≤ M *
      ((F.divisors.card ^ 6 *
        (b0 ^ 2 * F ^ 3).divisors.card ^ 4 *
        (F * b0).divisors.card * K.divisors.card : ℕ) : ℝ) := by
  have hcard := fixed_crt_choice_count Q F K b0 hF hK hb0 hQ
  calc
    (∑ q ∈ Q, w q) ≤ ∑ q ∈ Q, M := by
      apply Finset.sum_le_sum
      intro q hq
      exact hw q hq
    _ = (Q.card : ℝ) * M := by simp
    _ ≤ ((F.divisors.card ^ 6 *
        (b0 ^ 2 * F ^ 3).divisors.card ^ 4 *
        (F * b0).divisors.card * K.divisors.card : ℕ) : ℝ) * M := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
    _ = _ := by ring

theorem second_passage_positive_reassembly
    (Q : Finset CRTChoice) (T : Finset (ℕ × ℕ)) (b0 : ℕ)
    (hb0 : b0 ≠ 0)
    (w : CRTChoice → ℝ) (A : (ℕ × ℕ) → ℂ)
    (wmax M : ℝ) (hwmax : 0 ≤ wmax)
    (hweight : ∀ q ∈ Q, w q ≤ wmax)
    (hvalid : ∀ q ∈ Q,
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ (CRTChoice.childPair q).2 * b0)
    (hmap : ∀ q ∈ Q, CRTChoice.childPair q ∈ T)
    (hT : ∀ a ∈ T, a.1 ≠ 0 ∧ a.2 ≠ 0 ∧
      wmax *
        (((a.2.divisors.card ^ 6 *
          (b0 ^ 2 * a.2 ^ 3).divisors.card ^ 4 *
          (a.2 * b0).divisors.card * a.1.divisors.card : ℕ) : ℝ)) ≤ M) :
    (∑ q ∈ Q, w q * ‖A (CRTChoice.childPair q)‖ ^ 2) ≤
      M * (∑ a ∈ T, ‖A a‖ ^ 2) := by
  apply fiber_mass_bound Q T CRTChoice.childPair w A M hmap
  intro a ha
  obtain ⟨hK, hF, hbound⟩ := hT a ha
  let S := Q.filter (fun q => CRTChoice.childPair q = a)
  have hS : ∀ q ∈ S,
      q.J * q.C * q.e * q.v = a.2 ∧
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ a.2 * b0 ∧ q.d * q.e * q.kpp = a.1 := by
    intro q hq
    have hqQ : q ∈ Q := (Finset.mem_filter.mp hq).1
    have hqa : CRTChoice.childPair q = a := (Finset.mem_filter.mp hq).2
    obtain ⟨hJ, hb, hA1, hA2, hd⟩ := hvalid q hqQ
    have hrow : q.d * q.e * q.kpp = a.1 := congrArg Prod.fst hqa
    have hlabel : q.J * q.C * q.e * q.v = a.2 := congrArg Prod.snd hqa
    simp only [CRTChoice.childPair] at hrow hlabel hd
    rw [hlabel] at hd
    exact ⟨hlabel, hJ, hb, hA1, hA2, hd, hrow⟩
  have hsum := second_passage_weighted_fiber S a.2 a.1 b0
    hF hK hb0 hS w wmax hwmax (by
      intro q hq
      exact hweight q (Finset.mem_filter.mp hq).1)
  exact hsum.trans hbound

end AnalyticBridge

namespace ShortDraftLatticeCount

open ActualEisensteinCoordinates
