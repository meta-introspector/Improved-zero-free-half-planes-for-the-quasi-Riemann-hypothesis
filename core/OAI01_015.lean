lemma logPhase_iteratedFDeriv_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (logPhase t) x‖ = (2 * Real.pi * ‖t‖) ^ n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logPhase_iteratedDeriv]
  simp only [norm_mul, norm_pow, phaseDerivative_norm, logPhase_norm, mul_one]

def derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (SchwartzMap.seminorm ℝ k i) g

lemma derivativeSeminormSum_nonneg (g : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    0 ≤ derivativeSeminormSum g k n := by unfold derivativeSeminormSum; positivity

lemma seminorm_le_derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n i : ℕ) (hi : i ≤ n) :
    (SchwartzMap.seminorm ℝ k i) g ≤ derivativeSeminormSum g k n := by
  apply Finset.single_le_sum (s := Finset.range (n + 1))
    (f := fun j => (SchwartzMap.seminorm ℝ k j) g) (a := i)
  · intro j hj; positivity
  · exact Finset.mem_range.mpr (by omega)

theorem frequencyTwist_seminorm_bound (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
  apply SchwartzMap.seminorm_le_bound ℝ k n _
    (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (derivativeSeminormSum_nonneg _ _ _))
  intro x
  have hh := norm_iteratedFDeriv_mul_le (logPhase_temperate t).1 (g.smooth ⊤) x
    (n := n) (by exact_mod_cast le_top)
  have hfun : (frequencyTwist g t : ℝ → ℂ) = fun x => logPhase t x * g x := by
    funext x; exact frequencyTwist_apply g t x
  rw [hfun]
  calc
    _ ≤ ‖x‖^k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (logPhase t) x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (2 * Real.pi * ‖t‖)^i * (‖x‖^k * ‖iteratedFDeriv ℝ (n-i) g x‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [logPhase_iteratedFDeriv_norm]
      ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have hp : (2 * Real.pi * ‖t‖)^i ≤ (1 + 2 * Real.pi * ‖t‖)^n := by
        calc
          _ ≤ (1 + 2 * Real.pi * ‖t‖)^i := by gcongr; linarith
          _ ≤ _ := pow_le_pow_right₀ (by
            have hc : 0 ≤ 2 * Real.pi * ‖t‖ := by positivity
            linarith) hin
      have hs := (SchwartzMap.le_seminorm ℝ k (n-i) g x).trans
        (seminorm_le_derivativeSeminormSum g k n (n-i) (Nat.sub_le n i))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hs (by positivity)
        (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

theorem frequencyTwist_seminorm_polynomial (g : 𝓢(ℝ, ℂ)) (t : ℝ) (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n) (frequencyTwist g t) ≤
      ((2 : ℝ)^n * (1 + 2 * Real.pi)^n * derivativeSeminormSum g k n) * (1 + ‖t‖)^n := by
  have hsum := derivativeSeminormSum_nonneg g k n
  have hp : 1 + 2 * Real.pi * ‖t‖ ≤ (1 + 2 * Real.pi) * (1 + ‖t‖) := by
    nlinarith [Real.pi_pos, norm_nonneg t]
  calc
    _ ≤ (2 : ℝ)^n * (1 + 2 * Real.pi * ‖t‖)^n * derivativeSeminormSum g k n :=
      frequencyTwist_seminorm_bound g t k n
    _ ≤ (2 : ℝ)^n * ((1 + 2 * Real.pi) * (1 + ‖t‖))^n * derivativeSeminormSum g k n := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

def twistSourceBound (g : 𝓢(ℝ, ℂ)) (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1),
    ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i))

lemma twistSourceBound_nonneg (g : 𝓢(ℝ, ℂ)) (K : ℕ) : 0 ≤ twistSourceBound g K := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))

theorem profileSourceBound_frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) (K : ℕ) :
    profileSourceBound (frequencyTwist g t) K ≤ twistSourceBound g K * (1 + ‖t‖)^K := by
  unfold profileSourceBound twistSourceBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ K := Finset.mem_range_succ_iff.mp hi
  have hb := add_le_add (frequencyTwist_seminorm_polynomial g t 0 i)
    (frequencyTwist_seminorm_polynomial g t (volume : Measure ℝ).integrablePower i)
  have hn : 0 ≤ (2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (add_nonneg (derivativeSeminormSum_nonneg _ _ _) (derivativeSeminormSum_nonneg _ _ _))
  calc
    _ ≤ ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
        (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i)) *
          (1 + ‖t‖)^i := by convert hb using 1 ; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hin) hn

lemma fourierPointBound_mono (K : ℕ) {C D : ℝ} (hCD : C ≤ D) :
    fourierPointBound K C ≤ fourierPointBound K D := by
  unfold fourierPointBound fourierSeminormBound
  gcongr

lemma fourierPointBound_mul (K : ℕ) (C D : ℝ) :
    fourierPointBound K (C * D) = fourierPointBound K C * D := by
  unfold fourierPointBound fourierSeminormBound
  ring

theorem twisted_profile_fourier_envelope (g : 𝓢(ℝ, ℂ)) (t s : ℝ) (J : ℕ) :
    ‖(𝓕 (frequencyTwist g t)) s‖ ≤
      fourierPointBound (J + 2) (twistSourceBound g (J + 2)) *
        (1 + ‖t‖)^(J + 2) * FirstPassCubeLabels.firstLogDensity J s := by
  calc
    _ ≤ fourierPointBound (J + 2) (profileSourceBound (frequencyTwist g t) (J + 2)) *
        FirstPassCubeLabels.firstLogDensity J s := profile_fourier_envelope _ _ _
    _ ≤ fourierPointBound (J + 2) (twistSourceBound g (J + 2) * (1 + ‖t‖)^(J + 2)) *
        FirstPassCubeLabels.firstLogDensity J s :=
      mul_le_mul_of_nonneg_right (fourierPointBound_mono _ (profileSourceBound_frequencyTwist _ _ _))
        (FirstPassCubeLabels.firstLogDensity_nonneg _ _)
    _ = _ := by rw [fourierPointBound_mul]

end JointLogSeparation

section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
namespace JointLogSeparation
open FourierBridge

lemma integrable_phase_schwartz (b : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Integrable (fun t : ℝ => logPhase t x * b t) := by
  have h := FirstPassCubeLabels.integrable_log_pair b x 0 1
  convert h using 1
  funext t
  simp [logPhase, mul_comm]

theorem finite_triple_phase_integral {α : Type*} (s : Finset α)
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (x y z : α → ℝ) (c : α → ℂ) :
    (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (logPhase t₁ (x i) * b₁ t₁) * ((logPhase t₂ (y i) * b₂ t₂) *
        ((logPhase t₃ (z i) * b₃ t₃) * c i))) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∑ i ∈ s,
      (logPhase t₁ (x i) * b₁ t₁) * ((logPhase t₂ (y i) * b₂ t₂) *
        ((logPhase t₃ (z i) * b₃ t₃) * c i)) := by
  let f := fun i (t₁ t₂ t₃ : ℝ) =>
    (logPhase t₁ (x i) * b₁ t₁) * ((logPhase t₂ (y i) * b₂ t₂) *
        ((logPhase t₃ (z i) * b₃ t₃) * c i))
  have hi₃ (i : α) (t₁ t₂ : ℝ) : Integrable (f i t₁ t₂) :=
    (((integrable_phase_schwartz b₃ (z i)).mul_const (c i)).const_mul _).const_mul _
  have hi₂ (i : α) (t₁ : ℝ) : Integrable (fun t₂ => ∫ t₃ : ℝ, f i t₁ t₂ t₃) := by
    simp only [f, integral_const_mul, integral_mul_const]
    exact ((integrable_phase_schwartz b₂ (y i)).mul_const _).const_mul _
  have hi₁ (i : α) : Integrable (fun t₁ => ∫ t₂ : ℝ, ∫ t₃ : ℝ, f i t₁ t₂ t₃) := by
    simp only [f, integral_const_mul, integral_mul_const]
    exact (integrable_phase_schwartz b₁ (x i)).mul_const _
  change (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, f i t₁ t₂ t₃) = _
  rw [← integral_finsetSum _ (fun i _ => hi₁ i)]
  apply integral_congr_ae
  filter_upwards [] with t₁
  rw [← integral_finsetSum _ (fun i _ => hi₂ i t₁)]
  apply integral_congr_ae
  filter_upwards [] with t₂
  exact (integral_finsetSum _ (fun i _ => hi₃ i t₁ t₂)).symm

end JointLogSeparation

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog firstLogDensity)
open JointLogSeparation (outerWindow fixedColumnTest)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def postCommonSmoothPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ R : ℝ) : ℂ :=
  ∑ N ∈ F.powerset, ∑ M ∈ F.powerset,
    star (secondChildColumn p hp hcop hg Ψ₁ m f y₁ (fun _ => 1) N) *
      secondChildColumn p hp hcop hg Ψ₂ m f y₂ (fun _ => 1) M *
      (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        A₁ (z + columnLog p X₁ N) * A₂ (z + columnLog p X₂ M) *
        EisensteinSchwartzPoisson.paperRadialFourier W
          (R * Real.exp (kap - ud - 2 * ue - 2 * uv - columnLog p X₁ N - columnLog p X₂ M)))

def fixedSecondTest (V : ℝ → ℂ) (X t s : ℝ) (negative : Bool) (N : Finset ι) : ℂ :=
  if negative then star (fixedColumnTest V (t-s) (columnLog p X N))
  else fixedColumnTest V (t-s) (columnLog p X N)

theorem postCommonSmoothPair_fixed_tests
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ R : ℝ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ a a' : ℝ,
      outerWindow V z ud ue uv kap * V 5 a * V 6 a' * A₁ (z+a) * A₂ (z+a') *
        EisensteinSchwartzPoisson.paperRadialFourier W (R * Real.exp (kap-ud-2*ue-2*uv-a-a')) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
          logPhase t₃ (kap-ud-2*ue-2*uv) *
          fixedColumnTest (V 5) (t₁-t₃) a * fixedColumnTest (V 6) (t₂-t₃) a' *
          ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) :
    postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      (outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
        logPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
      star (fixedChildRow p hp hcop hg F Ψ₁ m
        (fixedSecondTest p (V 5) X₁ t₁ t₃ true) f y₁) *
      fixedChildRow p hp hcop hg F Ψ₂ m
        (fixedSecondTest p (V 6) X₂ t₂ t₃ false) f y₂ := by
  let B₁ := fun N => secondChildColumn p hp hcop hg Ψ₁ m f y₁ (fun _ => 1) N
  let B₂ := fun M => secondChildColumn p hp hcop hg Ψ₂ m f y₂ (fun _ => 1) M
  let q := fun (i : Finset ι × Finset ι) =>
    outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ i.1) * V 6 (columnLog p X₂ i.2) *
      star (B₁ i.1) * B₂ i.2
  let K := fun (i : Finset ι × Finset ι) (t₁ t₂ t₃ : ℝ) =>
    (logPhase t₁ (z + columnLog p X₁ i.1) * (𝓕 A₁) t₁) *
      ((logPhase t₂ (z + columnLog p X₂ i.2) * (𝓕 A₂) t₂) *
        ((logPhase t₃ (kap-ud-2*ue-2*uv-columnLog p X₁ i.1-columnLog p X₂ i.2) * b t₃) * q i))
  have hterm (N M : Finset ι) : star (B₁ N) * B₂ M *
      (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        A₁ (z+columnLog p X₁ N) * A₂ (z+columnLog p X₂ M) *
        EisensteinSchwartzPoisson.paperRadialFourier W
          (R * Real.exp (kap-ud-2*ue-2*uv-columnLog p X₁ N-columnLog p X₂ M))) =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, K (N,M) t₁ t₂ t₃ := by
    rw [hsep]
    simp_rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t₁
    apply integral_congr_ae
    filter_upwards [] with t₂
    apply integral_congr_ae
    filter_upwards [] with t₃
    have hphase := JointLogSeparation.seven_phase_factor z ud ue uv kap
      (columnLog p X₁ N) (columnLog p X₂ M) t₁ t₂ t₃
    dsimp only [K, q]
    unfold fixedColumnTest
    calc
      _ = (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
        star (B₁ N) * B₂ M) *
        (logPhase (t₁+t₂) z * logPhase t₃ (kap-ud-2*ue-2*uv) *
          logPhase (t₁-t₃) (columnLog p X₁ N) * logPhase (t₂-t₃) (columnLog p X₂ M)) *
        ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
      _ = _ := by rw [← hphase]; ring
  calc
    _ = ∑ i ∈ F.powerset ×ˢ F.powerset, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, K i t₁ t₂ t₃ := by
      simp only [postCommonSmoothPair, Finset.sum_product]
      exact Finset.sum_congr rfl (fun N _ => Finset.sum_congr rfl (fun M _ => hterm N M))
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∑ i ∈ F.powerset ×ˢ F.powerset, K i t₁ t₂ t₃ :=
      JointLogSeparation.finite_triple_phase_integral _ (𝓕 A₁) (𝓕 A₂) b _ _ _ q
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      simp only [Finset.sum_product]
      have hcols : (∑ N ∈ F.powerset, ∑ M ∈ F.powerset, K (N,M) t₁ t₂ t₃) =
          (outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
            logPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
          (∑ N ∈ F.powerset, star (B₁ N) * fixedColumnTest (V 5) (t₁-t₃) (columnLog p X₁ N)) *
          (∑ M ∈ F.powerset, B₂ M * fixedColumnTest (V 6) (t₂-t₃) (columnLog p X₂ M)) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro N hN
        apply Finset.sum_congr rfl
        intro M hM
        have hphase := JointLogSeparation.seven_phase_factor z ud ue uv kap
          (columnLog p X₁ N) (columnLog p X₂ M) t₁ t₂ t₃
        dsimp only [K, q]
        unfold fixedColumnTest
        calc
          _ = (outerWindow V z ud ue uv kap * V 5 (columnLog p X₁ N) * V 6 (columnLog p X₂ M) *
            star (B₁ N) * B₂ M) *
            (logPhase t₁ (z+columnLog p X₁ N) * logPhase t₂ (z+columnLog p X₂ M) *
              logPhase t₃ (kap-ud-2*ue-2*uv-columnLog p X₁ N-columnLog p X₂ M)) *
            ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by ring
          _ = _ := by rw [hphase]; ring
      rw [hcols]
      have hleft : (∑ N ∈ F.powerset, star (B₁ N) *
          fixedColumnTest (V 5) (t₁-t₃) (columnLog p X₁ N)) =
          star (fixedChildRow p hp hcop hg F Ψ₁ m
            (fixedSecondTest p (V 5) X₁ t₁ t₃ true) f y₁) := by
        simp only [fixedChildRow, star_sum]
        apply Finset.sum_congr rfl
        intro N hN
        simp only [secondChildColumn, fixedSecondTest, ite_true, B₁,
          star_mul, star_star, mul_one]
        ring
      have hright : (∑ N ∈ F.powerset, B₂ N *
          fixedColumnTest (V 6) (t₂-t₃) (columnLog p X₂ N)) =
          fixedChildRow p hp hcop hg F Ψ₂ m
            (fixedSecondTest p (V 6) X₂ t₂ t₃ false) f y₂ := by
        apply Finset.sum_congr rfl
        intro N hN
        simp only [secondChildColumn, fixedSecondTest, Bool.false_eq_true, ite_false, B₂, mul_one]
      rw [hleft, hright]

def separatedPostCommon (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
    (A₁ A₂ b : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ)
    (z ud ue uv kap X₁ X₂ : ℝ) : ℂ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
    (outerWindow V z ud ue uv kap * logPhase (t₁+t₂) z *
      logPhase t₃ (kap-ud-2*ue-2*uv) * ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃)) *
    star (fixedChildRow p hp hcop hg F Ψ₁ m
      (fixedSecondTest p (V 5) X₁ t₁ t₃ true) f y₁) *
    fixedChildRow p hp hcop hg F Ψ₂ m
      (fixedSecondTest p (V 6) X₂ t₂ t₃ false) f y₂

theorem postCommonSmoothPair_uniform_fixed_tests
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1+R)^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        C * firstLogDensity J t₁ * firstLogDensity J t₂ * firstLogDensity J t₃) ∧
      ∀ (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m f y₁ y₂ : O)
        (z ud ue uv kap X₁ X₂ : ℝ),
        postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V
          z ud ue uv kap X₁ X₂ R =
        separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ b V
          z ud ue uv kap X₁ X₂ := by
  obtain ⟨C, hC, hsep⟩ := JointLogSeparation.seven_kernel_separation A₁ A₂ W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hpoint, hint⟩ := hsep R hR
  refine ⟨b, hpoint, ?_⟩
  intro F Ψ₁ Ψ₂ m f y₁ y₂ z ud ue uv kap X₁ X₂
  exact postCommonSmoothPair_fixed_tests p hp hcop hg F Ψ₁ Ψ₂ m f y₁ y₂ A₁ A₂ W V
    z ud ue uv kap X₁ X₂ R b (hb z ud ue uv kap)

end SecondPassArithmetic
end

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem labeled_child_second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      (∑ x ∈ s, ‖w x‖ *
        ‖fixedChildRow p hp hcop hg F Ψ m H (label x)
          (if negative then -newRow x else newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := second_energy_selected_family (κ := Oˣ) ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale label F Ψ m H negative hb0 hB hL hvalid hmap ht hnorm hw hlabel
  let sel : OldTuple → Oˣ := fun x => if hx : x ∈ s then
    Classical.choose (exists_label_unit (label x) (newLabel x) (hlabel x hx)) else 1
  have hsel (x : OldTuple) (hx : x ∈ s) : label x = (sel x : O) * idealGenerator (newLabel x) := by
    simp only [sel, dite_eq_left hx]
    exact Classical.choose_spec (exists_label_unit (label x) (newLabel x) (hlabel x hx))
  have hh := hb s t b0 w B lengthScale (idealChildRow p hp hcop hg F Ψ m H negative)
    sel hb0 hB hL hvalid hmap ht hnorm hw
  convert hh using 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [hsel x hx]
  rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem support_child_label_span (x : OldTuple) (V : Finset ι)
    (hV : (∏ i ∈ V, Ideal.span {p i}) = x.v) :
    Ideal.span {idealGenerator (x.core 0) * idealGenerator (x.core 1) *
      idealGenerator (x.core 2) * ∏ i ∈ V, p i} = newLabel x := by
  simp only [newLabel, ← Ideal.span_singleton_mul_span_singleton, span_idealGenerator]
  rw [FiniteGaussPhase.span_finset_prod, hV]

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)

lemma rayMonoid_norm_le_one (χ : RayCharacter) (a : O) : ‖rayMonoid χ a‖ ≤ 1 :=
  FiniteRayExpansion.norm_char_le_one χ _

lemma secondRayMinus_norm_le (Ψ : O →* ℂ) (z : SecondRayIndex) (a : O) :
    ‖secondRayMinus Ψ z a‖ ≤ ‖Ψ a‖ := by
  simp only [secondRayMinus, MonoidHom.mul_apply, norm_mul, conjugateRayMonoid_apply, norm_star]
  calc
    _ ≤ 1 * (1 * ‖Ψ a‖) := by
      gcongr <;> exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by ring

lemma secondRayPlus_norm_le (Ψ : O →* ℂ) (z : SecondRayIndex) (a : O) :
    ‖secondRayPlus Ψ z a‖ ≤ ‖Ψ a‖ := by
  simp only [secondRayPlus, MonoidHom.mul_apply, norm_mul, conjugateRayMonoid_apply, rayMonoid_apply, norm_star]
  calc
    _ ≤ 1 * (1 * ‖Ψ a‖) := by
      gcongr <;> exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by ring

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondPreColumn_norm_le
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (m c d e k : O) (S : Finset ι) :
    ‖secondPreColumn p hp hcop hg Ψ m c d e k (fun _ => 1) S‖ ≤ ‖Ψ (∏ i ∈ S, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) S m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondPreColumn, norm_mul, norm_pow, norm_star, norm_one,
    columnCoefficient_norm_one p hp hcop hg hc S]
  calc
    _ ≤ 1 * ‖Ψ (∏ i ∈ S, p i)‖ * 1 * 1 ^ 4 * 1 * 1 * 1 * 1 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one _ hg S _
    _ = _ := by ring

theorem secondCommonWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O) (S : Finset ι) :
    ‖secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ S‖ ≤
      ‖Ψ₁ (∏ i ∈ S, p i)‖ * ‖Ψ₂ (∏ i ∈ S, p i)‖ := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hmu : ‖supportMobius (fun i => Ideal.span {p i}) S‖ = 1 := by
    have h := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj S)
    simp only [norm_mul, norm_one] at h
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) S)]
  simp only [secondCommonWeight, norm_mul, norm_star, hmu, one_mul]
  exact mul_le_mul (secondPreColumn_norm_le p hp hcop hg hc Ψ₁ _ _ _ _ _ S)
    (secondPreColumn_norm_le p hp hcop hg hc Ψ₂ _ _ _ _ _ S) (norm_nonneg _) (norm_nonneg _)

theorem secondTotalWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (z : SecondRayIndex) (S : Finset ι)
    (hΨ₁ : ‖Ψ₁ (∏ i ∈ S, p i)‖ ≤ 1) (hΨ₂ : ‖Ψ₂ (∏ i ∈ S, p i)‖ ≤ 1) :
    ‖secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,S)‖ ≤ ‖secondRayCoefficient z‖ := by
  have h := secondCommonWeight_norm_le p hp hcop hg hinj hc
    (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z) m r c d e k (-k) S
  have h₁ := (secondRayMinus_norm_le Ψ₁ z (∏ i ∈ S, p i)).trans hΨ₁
  have h₂ := (secondRayPlus_norm_le Ψ₂ z (∏ i ∈ S, p i)).trans hΨ₂
  have hc' : ‖secondCommonWeight p hp hcop hg (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
      m r c d e k (-k) S‖ ≤ 1 := by
    apply h.trans
    simpa using mul_le_mul h₁ h₂ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simp only [secondTotalWeight, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hc'

end

theorem secondRayCoefficient_mass :
    (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) ≤ 512 * 32 ^ 2 := by
  have hG := RayFourExpansion.gCoeff_sum_norm_le
  have hQ := RayFourExpansion.crossCoeff_sum_norm_le
  have heq : (∑ z : SecondRayIndex, ‖secondRayCoefficient z‖) =
      (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ a : RayCharacter, ‖gCoeff a‖) ^ 2 := by
    simp only [secondRayCoefficient, Fintype.sum_prod_type, norm_mul, norm_star, pow_two,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro χ hχ
    apply Finset.sum_congr rfl
    intro η hη
    ring
  rw [heq]
  exact mul_le_mul hQ (pow_le_pow_left₀ (by positivity) hG 2) (by positivity) (by norm_num)

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0123

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.ChildTransfer
Source SHA256: 03b89538c50ee0bda0fef887d70e084f03e767a9ae9207d623ba4c2e94bb5f06
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0124


namespace OAI

noncomputable section

namespace SecondPassArithmetic

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
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedSecondMode (s : Finset OldTuple) (w : OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ x ∈ s, w x *
    star (fixedChildRow p hp hcop hg F Ψ₁ m H₁ (label x) (newRow x)) *
      fixedChildRow p hp hcop hg F Ψ₂ m H₂ (label x) (-newRow x)

theorem fixed_second_mode_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (H₁ H₂ : Finset ι → ℂ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      ‖fixedSecondMode p hp hcop hg s w label F Ψ₁ Ψ₂ m H₁ H₂‖ ≤
        (B * C * (lengthScale * Ideal.absNorm b0)^ε) *
        Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖ ^ 2) *
        Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖ ^ 2) := by
  obtain ⟨C, hC, hpush⟩ := labeled_child_second_energy_pushforward p hp hcop hg ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale label F Ψ₁ Ψ₂ m H₁ H₂ hb0 hB hL hv hm ht hn hw hl
  let P₁ := fun x => fixedChildRow p hp hcop hg F Ψ₁ m H₁ (label x) (newRow x)
  let P₂ := fun x => fixedChildRow p hp hcop hg F Ψ₂ m H₂ (label x) (-newRow x)
  have h₁ := hpush s t b0 w B lengthScale label F Ψ₁ m H₁ false hb0 hB hL hv hm ht hn hw hl
  have h₂ := hpush s t b0 w B lengthScale label F Ψ₂ m H₂ true hb0 hB hL hv hm ht hn hw hl
  simp only [Bool.false_eq_true, ite_false, ite_true] at h₁ h₂
  let D : ℝ := B * C * (lengthScale * Ideal.absNorm b0)^ε
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hCau := DescentWeightedCauchy.weighted_cauchy s w P₂ P₁
  have hmode : fixedSecondMode p hp hcop hg s w label F Ψ₁ Ψ₂ m H₁ H₂ =
      ∑ x ∈ s, w x * P₂ x * star (P₁ x) := by
    unfold fixedSecondMode
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [P₁, P₂]
    ring
  rw [hmode]
  apply hCau.trans
  calc
    _ ≤ Real.sqrt (D * (∑ u : Oˣ, ∑ z ∈ t,
        ‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖ ^ 2)) *
      Real.sqrt (D * (∑ u : Oˣ, ∑ z ∈ t,
        ‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖ ^ 2)) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD, Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt D)^2 *
          Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₁ m H₁ false u z‖ ^ 2) *
          Real.sqrt (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ₂ m H₂ true u z‖ ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportConjugateSum)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondInputCoefficient_union (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (G U : Finset ι) (hd : Disjoint G U) :
    secondInputCoefficient p hg Ψ m c d H (G ∪ U) =
      secondInputCoefficient p hg Ψ m c d (fun _ => 1) G *
        secondInputCoefficient p hg Ψ m c d (fun V => H (G ∪ V)) U := by
  simp only [secondInputCoefficient, Finset.prod_union hd, map_mul,
    FirstPassCubeLabels.mask_union _ hg G U hd,
    FirstPassCubeLabels.row_union _ hg G U hd, mul_pow, mul_one]
  ring

def inputConjugateRow (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (z : O) : ℂ :=
  supportConjugateSum (fun i => Ideal.span {p i}) hg F
    (secondInputCoefficient p hg Ψ m c d H) z

theorem supportMobius_disjoint_mul
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (G U : Finset ι) (hd : Disjoint G U) :
    supportMobius (fun i => Ideal.span {p i}) (G ∪ U) =
      supportMobius (fun i => Ideal.span {p i}) G * supportMobius (fun i => Ideal.span {p i}) U := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  simp only [supportMobius, prime_product_moebius _ hprime hinj,
    Finset.card_union_of_disjoint hd, pow_add]

theorem inputConjugateRow_sq_overlap
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (z : O) :
    (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then
          (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
          rowCoprimeMask (fun i => Ideal.span {p i}) G z *
          (star (supportMobius (fun i => Ideal.span {p i}) U *
            secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) U) *
            (supportMobius (fun i => Ideal.span {p i}) V *
              secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) V) *
            (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z *
              star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z))) else 0 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hnorm (a : ℂ) : (↑(‖a‖ ^ 2) : ℂ) = star a * a := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hnorm]
  unfold inputConjugateRow supportConjugateSum
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [FiniteOverlapDecomposition.sum_pair_eq_overlap]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [ite_eq_left hd, ite_eq_left hd]
    have hGU : Disjoint G U := Finset.disjoint_left.mpr (fun i hi hu =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hu)).2 hi)
    have hGV : Disjoint G V := Finset.disjoint_left.mpr (fun i hi hv =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hV) hv)).2 hi)
    rw [supportMobius_disjoint_mul p hinj G U hGU, supportMobius_disjoint_mul p hinj G V hGV,
      secondInputCoefficient_union p hg Ψ m c d H G U hGU,
      secondInputCoefficient_union p hg Ψ m c d H G V hGV,
      FirstPassCubeLabels.row_union _ hg G U hGU,
      FirstPassCubeLabels.row_union _ hg G V hGV]
    simp only [star_mul, star_star, FirstCauchyArithmetic.star_supportMobius]
    have hmu := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj G
    have hrow := finiteSquarefreeRow_self_pair (fun i => Ideal.span {p i}) hg G z
    rw [hnorm]
    calc
      _ = (supportMobius (fun i => Ideal.span {p i}) G * supportMobius (fun i => Ideal.span {p i}) G) *
        (star (secondInputCoefficient p hg Ψ m c d (fun _ => 1) G) *
          secondInputCoefficient p hg Ψ m c d (fun _ => 1) G) *
        (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg G z) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg G z) *
        (star (supportMobius (fun i => Ideal.span {p i}) U *
            secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) U) *
          (supportMobius (fun i => Ideal.span {p i}) V *
            secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) V) *
          (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z *
            star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z))) := by
          simp only [star_mul, FirstCauchyArithmetic.star_supportMobius]
          ring
      _ = _ := by
        rw [hmu, hrow]
        simp only [star_mul, FirstCauchyArithmetic.star_supportMobius]
        ring
  · simp [hd]

end

section
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem commonProduct_mask
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (U G : Finset ι) :
    rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) =
      if Disjoint U G then 1 else 0 := by
  by_cases hd : Disjoint U G
  · rw [ite_eq_left hd, FirstPassCubeLabels.mask_prod _ hg U G p]
    apply Finset.prod_eq_one
    intro j hj
    have hh : ¬ ∃ i ∈ U, p j ∈ Ideal.span {p i} := by
      rintro ⟨i, hi, hpi⟩
      have hij : i ≠ j := fun he => Finset.disjoint_left.mp hd hi (he ▸ hj)
      exact (prime_generator_not_mem_of_ne (Ideal.span {p i}) (Ideal.span {p j})
        (fun he => hij (hinj he)) (p j) rfl) hpi
    simp [rowCoprimeMask, hh]
  · rw [ite_eq_right hd]
    obtain ⟨i, hiU, hiG⟩ := Finset.not_disjoint_iff.mp hd
    have hh : ∃ j ∈ U, (∏ i ∈ G, p i) ∈ Ideal.span {p j} :=
      ⟨i, hiU, Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hiG)⟩
    simp [rowCoprimeMask, hh]

theorem sum_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, A U) =
      ∑ U ∈ F.powerset, rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) * A U := by
  have hsub : (F \ G).powerset ⊆ F.powerset := Finset.powerset_mono.mpr Finset.sdiff_subset
  calc
    _ = ∑ U ∈ (F \ G).powerset,
        rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) * A U := by
      apply Finset.sum_congr rfl
      intro U hU
      have hd : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hG =>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hi)).2 hG)
      rw [commonProduct_mask p hg hinj U G, ite_eq_left hd, one_mul]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro U hUF hUG
      have hd : ¬ Disjoint U G := by
        intro hd
        apply hUG
        apply Finset.mem_powerset.mpr
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hUF) hi,
          fun hG => Finset.disjoint_left.mp hd hi hG⟩
      rw [commonProduct_mask p hg hinj U G, ite_eq_right hd, zero_mul]

omit [DecidableEq ι] in
theorem secondInputCoefficient_fixed_mask (Ψ : O →* ℂ) (m g c d : O)
    (H : Finset ι → ℂ) (U : Finset ι) :
    secondInputCoefficient p hg Ψ (m*g) c d H U =
      rowCoprimeMask (fun i => Ideal.span {p i}) U g * secondInputCoefficient p hg Ψ m c d H U := by
  rw [secondInputCoefficient, FirstPassCubeLabels.mask_mul _ hg U m g]
  unfold secondInputCoefficient
  ring

theorem inputConjugateRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (z : O) :
    inputConjugateRow p hg (F \ G) Ψ m c d H z =
      inputConjugateRow p hg F Ψ (m * ∏ i ∈ G, p i) c d H z := by
  unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  rw [sum_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  rw [secondInputCoefficient_fixed_mask]
  ring

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

theorem sum_pair_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset, A U V) =
      ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
        rowCoprimeMask (fun i => Ideal.span {p i}) U (∏ i ∈ G, p i) *
        rowCoprimeMask (fun i => Ideal.span {p i}) V (∏ i ∈ G, p i) * A U V := by
  rw [sum_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  rw [sum_remove_common_pool p hg hinj F G, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  ring

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
lemma star_mask (P : ι → Ideal O) (S : Finset ι) (a : O) :
    star (rowCoprimeMask P S a) = rowCoprimeMask P S a := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem input_pair_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
      if Disjoint U V then
        star (supportMobius (fun i => Ideal.span {p i}) U * secondInputCoefficient p hg Ψ₁ m c d H₁ U) *
        (supportMobius (fun i => Ideal.span {p i}) V * secondInputCoefficient p hg Ψ₂ m c d H₂ V) * K U V
      else 0) =
    ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
      if Disjoint U V then
        star (supportMobius (fun i => Ideal.span {p i}) U *
          secondInputCoefficient p hg Ψ₁ (m * ∏ i ∈ G, p i) c d H₁ U) *
        (supportMobius (fun i => Ideal.span {p i}) V *
          secondInputCoefficient p hg Ψ₂ (m * ∏ i ∈ G, p i) c d H₂ V) * K U V
      else 0 := by
  rw [sum_pair_remove_common_pool p hg hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [ite_eq_left hd, ite_eq_left hd, secondInputCoefficient_fixed_mask,
      secondInputCoefficient_fixed_mask]
    simp only [star_mul, star_mask]
    ring
  · simp [hd]

omit hg in

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem poisson_mask_generator_dvd (E G : Finset ι) (hEG : E ⊆ G) :
    primeSubsetGenerator (fun i => Ideal.span {p i}) E ∣ ∏ i ∈ G, p i := by
  have hs : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E} =
      Ideal.span {∏ i ∈ E, p i} := by
    rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator,
      FiniteGaussPhase.span_finset_prod]
  have ha := Ideal.span_singleton_eq_span_singleton.mp hs
  exact (dvd_dvd_iff_associated.mpr ha).1.trans (Finset.prod_dvd_prod_of_subset E G p hEG)

omit hg in
def secondMaskQuotient (E G : Finset ι) (hEG : E ⊆ G) : O :=
  Classical.choose (poisson_mask_generator_dvd p E G hEG)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
theorem secondMaskQuotient_spec (E G : Finset ι) (hEG : E ⊆ G) :
    (∏ i ∈ G, p i) = primeSubsetGenerator (fun i => Ideal.span {p i}) E *
      secondMaskQuotient p E G hEG :=
  Classical.choose_spec (poisson_mask_generator_dvd p E G hEG)

end

open ActualEisensteinCubic

theorem secondMaskQuotient_span {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (E G : Finset ι) (hEG : E ⊆ G) :
    Ideal.span {secondMaskQuotient p E G hEG} =
      ∏ i ∈ G \ E, Ideal.span {p i} := by
  have hE : (∏ i ∈ E, Ideal.span {p i}) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))
  have he : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E} =
      ∏ i ∈ E, Ideal.span {p i} := by
    rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator]
  apply mul_left_cancel₀ hE
  calc
    _ = Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E *
        secondMaskQuotient p E G hEG} := by rw [← he, Ideal.span_singleton_mul_span_singleton]
    _ = Ideal.span {∏ i ∈ G, p i} := by rw [← secondMaskQuotient_spec]
    _ = ∏ i ∈ G, Ideal.span {p i} := FiniteGaussPhase.span_finset_prod G p
    _ = _ := by simpa only [mul_comm] using
      (Finset.prod_sdiff (f := fun i => Ideal.span {p i}) hEG).symm

theorem secondMaskQuotient_norm {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (E G : Finset ι) (hEG : E ⊆ G) :
    ‖ConcreteTraceCRT.eisEmbedding (secondMaskQuotient p E G hEG)‖ ^ 2 =
      (Ideal.absNorm (∏ i ∈ G \ E, Ideal.span {p i}) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span, secondMaskQuotient_span]

end

section

open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def maskedSecondSource (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) G z *
    (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y)

def overlapPairWeight (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (G U V : Finset ι) : ℂ :=
  (↑(‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
    star (supportMobius (fun i => Ideal.span {p i}) U *
      secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) U) *
    (supportMobius (fun i => Ideal.span {p i}) V *
      secondInputCoefficient p hg Ψ m c d (fun S => H (G ∪ S)) V)

omit [DecidableEq ι] in
theorem maskedSecondSource_summable (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => rowCoprimeMask (fun i => Ideal.span {p i}) G z *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y)) := by
  have h := finiteSquarefreeRow_pair_radial_summable (fun i => Ideal.span {p i}) hg V U W Y hY
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ h.norm
  intro z
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) G z‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simpa only [norm_mul, one_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right hm
      (norm_nonneg ((star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y)))

theorem inputConjugateRow_smoothed_overlap
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ m c d H G U V *
          maskedSecondSource p hg G U V W Y else 0 := by
  let f := fun (G U V : Finset ι) (z : O) => if Disjoint U V then
    overlapPairWeight p hg Ψ m c d H G U V *
      (rowCoprimeMask (fun i => Ideal.span {p i}) G z *
        (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V z) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z) * W (‖eisEmbedding z‖ ^ 2 / Y))
    else 0
  have hf (G U V : Finset ι) : Summable (f G U V) := by
    by_cases hd : Disjoint U V
    · simpa only [f, ite_eq_left hd] using
        (maskedSecondSource_summable p hg G U V W Y hY).mul_left (overlapPairWeight p hg Ψ m c d H G U V)
    · simp only [f, ite_eq_right hd]
      exact summable_zero
  have he (z : O) : W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset, f G U V z := by
    rw [inputConjugateRow_sq_overlap p hg hinj]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro G hG
    apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro V hV
    by_cases hd : Disjoint U V
    · simp only [f, ite_eq_left hd, overlapPairWeight]
      ring
    · simp [f, hd]
  rw [tsum_congr he]
  rw [Summable.tsum_finsetSum (fun G _ => summable_sum (fun U _ => summable_sum (fun V _ => hf G U V)))]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Summable.tsum_finsetSum (fun U _ => summable_sum (fun V _ => hf G U V))]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Summable.tsum_finsetSum (fun V _ => hf G U V)]
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · simp only [f, ite_eq_left hd, maskedSecondSource]
    exact tsum_mul_left
  · simp [f, hd]

def maskedSecondDual (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (G U V : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  let n := ∏ i : activeSupport V U, p i.val
  ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
    ∑ E ∈ G.powerset,
      let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
      ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
        (‖eisEmbedding e‖ ^ 2 : ℝ)) *
        ∑' k : O, paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
          (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
          FirstCauchyArithmetic.activeGaussRowFactor p hp hinj hg V U e k

theorem inputConjugateRow_smoothed_second_poisson (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg F Ψ m c d H z‖ ^ 2) : ℂ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ m c d H G U V *
          maskedSecondDual p hg hp hinj G U V W Y else 0 := by
  rw [inputConjugateRow_smoothed_overlap p hg hinj F Ψ m c d H W Y hY]
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [ite_eq_left hd, ite_eq_left hd]
    congr 1
    exact masked_pair_second_poisson p hp hinj hg hc G U V hd W Y hY
  · simp [hd]

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeCoreCoefficient cubeOddSupport coreRayCoefficient coreRayTwist
  coreRayCharacter dilatedCoreRow dilatedRayColumn afterDilationLabel b0Label jLabel)
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)
open FourierBridge (logPhase)

abbrev FirstCoreIndex := RayCharacter × (RayCharacter × RayCharacter)

def sideRayMonoid (negative : Bool) (χ : RayCharacter) : O →* ℂ :=
  if negative then conjugateRayMonoid χ else rayMonoid χ

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def multiplicativeCoreColumn (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏ i ∈ S, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) S m * H S

def firstCoreTest (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (t : ℝ) (D U : Finset ι) : ℂ :=
  H (D ∪ U) *
    (if negative then star (V (y (D ∪ U)) * logPhase t (-(y (D ∪ U))))
      else V (y (D ∪ U)) * logPhase t (-(y (D ∪ U))))

def firstCoreOuter (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι) (r : FirstCoreIndex) : ℂ :=
  coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2 *
    (Ψ * coreRayTwist negative r.1 r.2.2) (∏ i ∈ D, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) D m *
    (if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg D (-1)) else 1)

def firstCoreTwist (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ)
    (r : FirstCoreIndex) : O →* ℂ :=
  sideRayMonoid negative χ * (Ψ * coreRayTwist negative r.1 r.2.2)

theorem cubeCoreCoefficient_ray_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) :
    cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S =
      ∑ r : FirstCoreIndex,
        coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2 *
          supportRay p (coreRayCharacter negative r.1 r.2.2) S * C S *
          (if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) else 1) *
          (if negative then star (V (y S) * logPhase t (-(y S))) else V (y S) * logPhase t (-(y S))) := by
  have hphase := FirstPassCubeLabels.core_phase_ray_expansion p hp hcop hg hc hpr
    (cubeOddSupport B v ε₁ ε₂) S negative
  have he : cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S =
      ((if negative then star (FirstPassCubeLabels.fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S)
          else FirstPassCubeLabels.fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
        MixedCrossSeparation.columnG p hp hcop hg S) * C S *
          (if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) else 1) *
          (if negative then star (V (y S) * logPhase t (-(y S))) else V (y S) * logPhase t (-(y S))) := by
    cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true] <;> ring
  rw [he, hphase]
  simp only [Fintype.sum_prod_type, Finset.sum_mul]

theorem dilatedCoreRow_eq_input_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O) :
    dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) V y c d t z =
    ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
      inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) (if negative then -z else z) := by
  unfold dilatedCoreRow dilatedRayColumn supportConjugateSum
  simp_rw [cubeCoreCoefficient_ray_family p hp hcop hg hc hpr]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [inputConjugateRow, supportConjugateSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hDU : Disjoint D U := Finset.disjoint_left.mpr (fun i hi hu =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hu)).2 hi)
  have hz : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (-z) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (-1) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z := by
    simpa only [neg_one_mul] using finiteSquarefreeRow_mul (fun i => Ideal.span {p i}) hg U (-1) z
  cases negative <;>
    simp only [multiplicativeCoreColumn, firstCoreOuter, firstCoreTwist, sideRayMonoid,
      firstCoreTest, secondInputCoefficient, afterDilationLabel, Bool.false_eq_true, ite_false, ite_true,
      Finset.prod_union hDU, map_mul, FirstPassCubeLabels.mask_union _ hg D U hDU,
      FirstPassCubeLabels.row_union _ hg D U hDU, FirstPassCubeLabels.mask_mul _ hg U,
      FirstPassCubeLabels.coreRayTwist_prod, MonoidHom.mul_apply, conjugateRayMonoid_apply, rayMonoid_apply,
      supportRay, coreRayCharacter, RayFourExpansion.rayCharacter_mul, hz, star_mul, mul_one] <;> ring

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0124

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.IntegratedTransfer
Source SHA256: cbaeaa1d49569dd16cceded786062dfb7e4272dcefc7d2cd3f870a33cae2b974
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0125


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
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory

section
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeOddSupport coreRayCoefficient coreRayTwist dilatedCoreRow
  b0Label jLabel firstLogDensity columnLog normalizedColumn firstOutputEnergy)
open FirstCauchyArithmetic (supportMobius supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)
open FourierBridge (logPhase)

lemma sideRayMonoid_norm_le_one (negative : Bool) (χ : RayCharacter) (a : O) :
    ‖sideRayMonoid negative χ a‖ ≤ 1 := by
  cases negative <;> simp only [sideRayMonoid, Bool.false_eq_true, ite_false, ite_true,
    conjugateRayMonoid_apply, rayMonoid_apply, norm_star]
  all_goals exact FiniteRayExpansion.norm_char_le_one _ _

lemma firstCoreTwist_norm_le (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ)
    (r : FirstCoreIndex) (a : O) :
    ‖firstCoreTwist negative χ Ψ r a‖ ≤ ‖Ψ a‖ := by
  have hc : ‖coreRayTwist negative r.1 r.2.2 a‖ ≤ 1 := by
    change ‖RayFourExpansion.rayCharacter (FirstPassCubeLabels.coreRayCharacter negative r.1 r.2.2) a‖ ≤ 1
    exact FiniteRayExpansion.norm_char_le_one _ _
  simp only [firstCoreTwist, MonoidHom.mul_apply, norm_mul]
  calc
    _ ≤ 1 * (‖Ψ a‖ * 1) := by gcongr; exact sideRayMonoid_norm_le_one _ _ _
    _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem firstCoreOuter_norm_le
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι) (r : FirstCoreIndex) :
    ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ ≤
      ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ *
        ‖Ψ (∏ i ∈ D, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) D m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  have hc : ‖coreRayTwist negative r.1 r.2.2 (∏ i ∈ D, p i)‖ ≤ 1 := by
    change ‖RayFourExpansion.rayCharacter (FirstPassCubeLabels.coreRayCharacter negative r.1 r.2.2) (∏ i ∈ D, p i)‖ ≤ 1
    exact FiniteRayExpansion.norm_char_le_one _ _
  have hs : ‖(if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg D (-1))
      else 1 : ℂ)‖ ≤ 1 := by
    cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true, norm_one, norm_star]
    · exact le_rfl
    · exact finiteSquarefreeRow_norm_le_one _ hg D _
  simp only [firstCoreOuter, norm_mul, MonoidHom.mul_apply]
  calc
    _ ≤ ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ *
        (‖Ψ (∏ i ∈ D, p i)‖ * 1) * 1 * 1 := by gcongr
    _ = _ := by ring

omit [DecidableEq ι] in
theorem firstCoreOuter_mass
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    (∑ r : FirstCoreIndex, ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖) ≤ 32 * 512 := by
  calc
    _ ≤ ∑ r : FirstCoreIndex,
        ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact (firstCoreOuter_norm_le p hg B v ε₁ ε₂ negative Ψ m D r).trans
        (mul_le_of_le_one_right (norm_nonneg _) hΨ)
    _ ≤ 32 * 512 := by
      simpa only [Fintype.sum_prod_type] using
        FirstPassCubeLabels.coreRayCoefficient_mass p (cubeOddSupport B v ε₁ ε₂) negative

theorem dilatedCoreRow_sq_le_input_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) V y c d t z‖ ^ 2 ≤
    (32 * 512) * ∑ r : FirstCoreIndex, ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
      ‖inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) (if negative then -z else z)‖ ^ 2 := by
  rw [dilatedCoreRow_eq_input_family p hp hcop hg hc hpr]
  let w := firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D
  let Q := fun r : FirstCoreIndex => inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (firstCoreTest H V y negative t D) (if negative then -z else z)
  have h := DescentWeightedCauchy.weighted_cauchy_sq Finset.univ w (fun _ => 1) (fun r => star (Q r))
  simp only [mul_one, star_star, norm_one, one_pow, norm_star] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (firstCoreOuter_mass p hg B v ε₁ ε₂ negative Ψ m D hΨ) (by positivity))

theorem firstCoreTest_continuous
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (D U : Finset ι) :
    Continuous (fun t : ℝ => firstCoreTest H V y negative t D U) := by
  have h := FourierBridge.logPhase_continuous_left (-(y (D ∪ U)))
  cases negative <;> simp only [firstCoreTest, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem firstCoreTest_norm
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ)
    (negative : Bool) (D U : Finset ι) (t : ℝ) :
    ‖firstCoreTest H V y negative t D U‖ = ‖firstCoreTest H V y negative 0 D U‖ := by
  cases negative <;> simp only [firstCoreTest, Bool.false_eq_true, ite_false, ite_true,
    norm_mul, norm_star, FourierBridge.logPhase_norm]

def firstCoreInputRow (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (z : O) : ℂ :=
  inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (firstCoreTest H V y negative t D) (if negative then -z else z)

theorem firstCoreInputRow_continuous
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (z : O) :
    Continuous (fun t : ℝ => firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z) := by
  unfold firstCoreInputRow inputConjugateRow supportConjugateSum secondInputCoefficient
  apply continuous_finsetSum
  intro U hU
  have ht := firstCoreTest_continuous H V y negative D U
  fun_prop

theorem firstCoreInputRow_uniform_bound
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (z : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ≤ M := by
  let q := fun (t : ℝ) (U : Finset ι) =>
    supportMobius (fun i => Ideal.span {p i}) U *
      secondInputCoefficient p hg (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) U *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (if negative then -z else z))
  refine ⟨∑ U ∈ (F \ D).powerset, ‖q 0 U‖, by positivity, ?_⟩
  intro t
  change ‖∑ U ∈ (F \ D).powerset, q t U‖ ≤ _
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro U hU
  simp only [q, secondInputCoefficient, norm_mul, firstCoreTest_norm]

theorem firstCoreInputRow_integrable
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (z : O) {k : ℝ → ℝ} (hk : Integrable k volume) :
    Integrable (fun t : ℝ => k t *
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) volume := by
  obtain ⟨M, hM, hb⟩ := firstCoreInputRow_uniform_bound p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z
  apply hk.mul_bdd (c := M ^ 2)
  · exact ((firstCoreInputRow_continuous p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z).norm.pow 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2)

end

open ActualEisensteinCubic
open FirstPassCubeLabels (cubeOddSupport coreRayCoefficient dilatedCoreRow b0Label jLabel
  firstLogDensity columnLog normalizedColumn firstOutputEnergy)
open RayFourExpansion (RayCharacter crossCoeff)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem dilatedCoreRow_energy_le_input_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (T : Finset O) (k : ℝ → ℝ) (hk : Integrable k volume) (hk0 : ∀ t, 0 ≤ k t)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    (∫ t : ℝ, k t * ∑ z ∈ T,
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
        (multiplicativeCoreColumn p Ψ m H) V y c d t z‖ ^ 2) ≤
    (32 * 512) * ∑ r : FirstCoreIndex, ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
      ∫ t : ℝ, k t * ∑ z ∈ T,
        ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2 := by
  let P := fun t z => dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
    (multiplicativeCoreColumn p Ψ m H) V y c d t z
  let Q := fun r t z => firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z
  let w := fun r => ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖
  have iP : Integrable (fun t : ℝ => k t * ∑ z ∈ T, ‖P t z‖ ^ 2) volume := by
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro z hz
    exact FirstPassCubeLabels.dilatedCoreRow_integrable p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) V y c d z hk
  have iQ (r : FirstCoreIndex) : Integrable (fun t : ℝ => k t * ∑ z ∈ T, ‖Q r t z‖ ^ 2) volume := by
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro z hz
    exact firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z hk
  have iR : Integrable (fun t : ℝ => ∑ r : FirstCoreIndex, w r * (k t * ∑ z ∈ T, ‖Q r t z‖ ^ 2)) volume :=
    integrable_finsetSum _ (fun r hr => (iQ r).const_mul (w r))
  have hpoint (t : ℝ) : k t * (∑ z ∈ T, ‖P t z‖ ^ 2) ≤
      (32 * 512) * ∑ r : FirstCoreIndex, w r * (k t * ∑ z ∈ T, ‖Q r t z‖ ^ 2) := by
    calc
      _ ≤ k t * ∑ z ∈ T, ((32 * 512) * ∑ r : FirstCoreIndex, w r * ‖Q r t z‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (hk0 t)
        apply Finset.sum_le_sum
        intro z hz
        exact dilatedCoreRow_sq_le_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂ negative χ Ψ m
          H V y c d t z hΨ
      _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro z hz
        ring
  calc
    _ ≤ ∫ t : ℝ, (32 * 512) * ∑ r : FirstCoreIndex, w r * (k t * ∑ z ∈ T, ‖Q r t z‖ ^ 2) :=
      integral_mono iP (iR.const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun r hr => (iQ r).const_mul (w r))]
      simp only [integral_const_mul]
      rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem normalizedColumn_multiplicativeCoreColumn
    (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) :
    normalizedColumn p (multiplicativeCoreColumn p Ψ m H) =
      multiplicativeCoreColumn p Ψ m (normalizedColumn p H) := by
  funext S
  simp only [normalizedColumn, multiplicativeCoreColumn, div_eq_mul_inv]
  ring

def firstInputFamilyEnergy (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) : ℝ :=
  ∑ a : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖crossCoeff a.1 a.2‖ * ∑ r : FirstCoreIndex,
      ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
        ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
          ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative
            (if negative then a.1 else a.2) Ψ m (normalizedColumn p H)
            V (columnLog p X) c d r t z‖ ^ 2

theorem firstInputFamilyEnergy_nonneg
    (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) :
    0 ≤ firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T := by
  unfold firstInputFamilyEnergy
  apply Finset.sum_nonneg
  intro a ha
  apply Finset.sum_nonneg
  intro D hD
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro r hr
  apply mul_nonneg (norm_nonneg _)
  apply integral_nonneg
  intro t
  exact mul_nonneg (FirstPassCubeLabels.firstLogDensity_nonneg J t)
    (Finset.sum_nonneg (fun z hz => sq_nonneg _))

theorem firstOutputEnergy_le_input_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ)
    (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O)
    (hΨ : ∀ D ∈ F.powerset, ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ negative
      (multiplicativeCoreColumn p Ψ m H) V X c d J T ≤
    (32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ negative Ψ m H V X c d J T := by
  unfold firstOutputEnergy firstInputFamilyEnergy
  rw [normalizedColumn_multiplicativeCoreColumn]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro D hD
  have h := dilatedCoreRow_energy_le_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂ negative
    (if negative then a.1 else a.2) Ψ m (normalizedColumn p H) V (columnLog p X) c d T
    (firstLogDensity J) (FirstPassCubeLabels.firstLogDensity_integrable J)
    (FirstPassCubeLabels.firstLogDensity_nonneg J) (hΨ D hD)
  have hh := mul_le_mul_of_nonneg_left h (norm_nonneg (crossCoeff a.1 a.2))
  simpa only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hh

end

open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label jLabel)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem firstCoreInputRow_smoothed_sign
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) =
    ∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p hg (F \ D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) z‖ ^ 2) : ℂ) := by
  cases negative
  · rfl
  · simpa only [firstCoreInputRow, Bool.true_eq, ite_true, Equiv.neg_apply, map_neg, norm_neg] using
      (Equiv.neg O).tsum_eq (fun z : O => W (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖inputConjugateRow p hg (F \ D) (firstCoreTwist true χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (firstCoreTest H V y true t D) z‖ ^ 2) : ℂ))

theorem firstCoreInputRow_smoothed_second_poisson
    (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) =
    ∑ G ∈ (F \ D).powerset, ∑ U ∈ ((F \ D) \ G).powerset, ∑ V' ∈ ((F \ D) \ G).powerset,
      if Disjoint U V' then
        overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (firstCoreTest H V y negative t D) G U V' *
          maskedSecondDual p hg hp hinj G U V' W Y
      else 0 := by
  rw [firstCoreInputRow_smoothed_sign]
  exact inputConjugateRow_smoothed_second_poisson p hg hp hinj hc (F \ D)
    (firstCoreTwist negative χ Ψ r) (m * b0Label p B v ε₁ ε₂)
    (c * jLabel p B v ε₁ ε₂) d (firstCoreTest H V y negative t D) W Y hY

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace JointLogSeparation

abbrev Frequency := ℝ × ℝ × ℝ

def tripleCoefficient (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (t : Frequency) : ℂ :=
  b₁ t.1 * (b₂ t.2.1 * b₃ t.2.2)

lemma tripleCoefficient_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) :
    Integrable (tripleCoefficient b₁ b₂ b₃) :=
  b₁.integrable.mul_prod (b₂.integrable.mul_prod b₃.integrable)

lemma tripleCoefficient_bounded_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (F : Frequency → ℂ) (hF : Continuous F) (M : ℝ) (hM : ∀ t, ‖F t‖ ≤ M) :
    Integrable (fun t => tripleCoefficient b₁ b₂ b₃ t * F t) :=
  (tripleCoefficient_integrable b₁ b₂ b₃).mul_bdd hF.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

lemma tripleCoefficient_norm_bounded_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (G : Frequency → ℝ) (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) :
    Integrable (fun t => ‖tripleCoefficient b₁ b₂ b₃ t‖ * G t) :=
  (tripleCoefficient_integrable b₁ b₂ b₃).norm.mul_bdd hG.aestronglyMeasurable
    (Filter.Eventually.of_forall hM)

lemma tripleCoefficient_slice_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (F : Frequency → ℂ) (hF : Continuous F) (M : ℝ) (hM : ∀ t, ‖F t‖ ≤ M) (x : ℝ) :
    Integrable (fun t : ℝ × ℝ => tripleCoefficient b₁ b₂ b₃ (x,t) * F (x,t)) := by
  have hc : Integrable (fun t : ℝ × ℝ => b₁ x * (b₂ t.1 * b₃ t.2)) :=
    (b₂.integrable.mul_prod b₃.integrable).const_mul (b₁ x)
  apply hc.mul_bdd
  · exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => hM (x,t))

lemma tripleCoefficient_norm_slice_integrable (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (G : Frequency → ℝ) (hG : Continuous G) (M : ℝ) (hM : ∀ t, ‖G t‖ ≤ M) (x : ℝ) :
    Integrable (fun t : ℝ × ℝ => ‖tripleCoefficient b₁ b₂ b₃ (x,t)‖ * G (x,t)) := by
  have hc : Integrable (fun t : ℝ × ℝ => ‖b₁ x * (b₂ t.1 * b₃ t.2)‖) :=
    ((b₂.integrable.mul_prod b₃.integrable).const_mul (b₁ x)).norm
  apply hc.mul_bdd
  · exact (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => hM (x,t))

lemma nested_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Frequency → E) (hf : Integrable f)
    (hslice : ∀ x : ℝ, Integrable (fun yz : ℝ × ℝ => f (x,yz))) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ, f (x,y,z)) = ∫ t : Frequency, f t := by
  rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), integral_prod _ hf]
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [Measure.volume_eq_prod] using (integral_prod _ (hslice x)).symm

theorem triple_integral_bound (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (F : Frequency → ℂ) (G : Frequency → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hG0 : ∀ t, 0 ≤ G t)
    (D M : ℝ) (hD : 0 ≤ D) (hM : ∀ t, G t ≤ M)
    (hpoint : ∀ t, ‖F t‖ ≤ D * G t) :
    ‖∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) * F (t₁,t₂,t₃)‖ ≤
    D * (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ * G (t₁,t₂,t₃)) := by
  have hFb : ∀ t, ‖F t‖ ≤ D * M := fun t => (hpoint t).trans (mul_le_mul_of_nonneg_left (hM t) hD)
  have hGb : ∀ t, ‖G t‖ ≤ M := fun t => by simpa [Real.norm_of_nonneg (hG0 t)] using hM t
  have hfi := tripleCoefficient_bounded_integrable b₁ b₂ b₃ F hF (D*M) hFb
  have hgi := tripleCoefficient_norm_bounded_integrable b₁ b₂ b₃ G hG M hGb
  rw [nested_eq_integral _ hfi (tripleCoefficient_slice_integrable b₁ b₂ b₃ F hF (D*M) hFb),
    nested_eq_integral _ hgi (tripleCoefficient_norm_slice_integrable b₁ b₂ b₃ G hG M hGb)]
  calc
    _ ≤ ∫ t : Frequency, ‖tripleCoefficient b₁ b₂ b₃ t * F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : Frequency, D * (‖tripleCoefficient b₁ b₂ b₃ t‖ * G t) := by
      apply integral_mono hfi.norm (hgi.const_mul D)
      intro t
      simp only [norm_mul]
      calc
        _ ≤ ‖tripleCoefficient b₁ b₂ b₃ t‖ * (D * G t) :=
          mul_le_mul_of_nonneg_left (hpoint t) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

end JointLogSeparation

namespace SecondPassIntegration
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open FirstPassCubeLabels (columnLog)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma fixedTest_continuous (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (N : Finset ι)
    (τ σ : Frequency → ℝ) (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun t => fixedSecondTest p V X (τ t) (σ t) negative N) := by
  have hh := (FourierBridge.logPhase_continuous_left (columnLog p X N)).comp (hτ.sub hσ)
  cases negative <;> simp only [fixedSecondTest, Bool.false_eq_true, ite_false, ite_true,
    fixedColumnTest] <;> fun_prop

lemma fixedColumn_norm_frequency (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X a b : ℝ)
    (negative : Bool) (N : Finset ι) :
    ‖secondChildColumn p hp hcop hg Ψ m f y (fixedSecondTest p V X a b negative) N‖ =
    ‖secondChildColumn p hp hcop hg Ψ m f y (fixedSecondTest p V X 0 0 negative) N‖ := by
  cases negative <;> simp only [secondChildColumn, fixedSecondTest, Bool.false_eq_true, ite_false,
    ite_true, fixedColumnTest, norm_mul, norm_star, FourierBridge.logPhase_norm]

lemma fixedRow_continuous (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X : ℝ)
    (negative : Bool) (τ σ : Frequency → ℝ) (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun t => fixedChildRow p hp hcop hg F Ψ m
      (fixedSecondTest p V X (τ t) (σ t) negative) f y) := by
  unfold fixedChildRow
  apply continuous_finsetSum
  intro N hN
  have hh := fixedTest_continuous p V X negative N τ σ hτ hσ
  unfold secondChildColumn
  fun_prop

def rowMagnitude (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X : ℝ)
    (negative : Bool) : ℝ :=
  ∑ N ∈ F.powerset,
    ‖secondChildColumn p hp hcop hg Ψ m f y (fixedSecondTest p V X 0 0 negative) N‖

lemma rowMagnitude_nonneg (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X : ℝ)
    (negative : Bool) : 0 ≤ rowMagnitude p hp hcop hg F Ψ m f y V X negative := by
  unfold rowMagnitude
  positivity

lemma fixedRow_norm_le (F : Finset ι) (Ψ : O →* ℂ) (m f y : O) (V : ℝ → ℂ) (X a b : ℝ)
    (negative : Bool) :
    ‖fixedChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b negative) f y‖ ≤
      rowMagnitude p hp hcop hg F Ψ m f y V X negative := by
  unfold fixedChildRow rowMagnitude
  apply (norm_sum_le _ _).trans_eq
  exact Finset.sum_congr rfl (fun N hN => fixedColumn_norm_frequency p hp hcop hg Ψ m f y V X a b negative N)

def childEnergy (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) : ℝ :=
  ∑ u : Oˣ, ∑ z ∈ T,
    ‖idealChildRow p hp hcop hg F Ψ m (fixedSecondTest p V X a b testNegative) rowNegative u z‖ ^ 2

def energyMagnitude (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) : ℝ :=
  ∑ u : Oˣ, ∑ z ∈ T,
    (rowMagnitude p hp hcop hg F Ψ m ((u : O) * ConcretePrimeRowBridge.idealGenerator z.1)
      (if rowNegative then -z.2 else z.2) V X testNegative) ^ 2

lemma childEnergy_nonneg (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) :
    0 ≤ childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative a b := by
  unfold childEnergy
  positivity

lemma childEnergy_le (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool) (a b : ℝ) :
    childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative a b ≤
      energyMagnitude p hp hcop hg F Ψ m T V X testNegative rowNegative := by
  unfold childEnergy energyMagnitude idealChildRow
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro z hz
  exact pow_le_pow_left₀ (norm_nonneg _) (fixedRow_norm_le p hp hcop hg F Ψ m _ _ V X a b testNegative) 2

lemma childEnergy_continuous (F : Finset ι) (Ψ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V : ℝ → ℂ) (X : ℝ) (testNegative rowNegative : Bool)
    (τ σ : Frequency → ℝ) (hτ : Continuous τ) (hσ : Continuous σ) :
    Continuous (fun t => childEnergy p hp hcop hg F Ψ m T V X testNegative rowNegative (τ t) (σ t)) := by
  unfold childEnergy
  apply continuous_finsetSum
  intro u hu
  apply continuous_finsetSum
  intro z hz
  unfold idealChildRow
  exact (fixedRow_continuous p hp hcop hg F Ψ m _ _ V X testNegative τ σ hτ hσ).norm.pow 2

end SecondPassIntegration

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def integratedSecondMode (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (s : Finset OldTuple) (w : Frequency → OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) *
    fixedSecondMode p hp hcop hg s (w (t₁,t₂,t₃)) label F Ψ₁ Ψ₂ m
      (fixedSecondTest p V₁ X₁ t₁ t₃ true) (fixedSecondTest p V₂ X₂ t₂ t₃ false)

def childGeometricMean (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (T : Finset (Ideal O × O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (q : Frequency) : ℝ :=
  Real.sqrt (childEnergy p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2) *
    Real.sqrt (childEnergy p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2)

theorem integrated_fixed_second_mode_transfer (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (T : Finset (Ideal O × O))
      (b0 : Ideal O) (w : Frequency → OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
      (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
      (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ T) →
      (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ q, ∀ x ∈ s, ‖w q x‖ ≤ B) → (∀ x ∈ s, Continuous (fun q => w q x)) →
      (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
      ‖integratedSecondMode p hp hcop hg b₁ b₂ b₃ s w label F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂‖ ≤
        (B * C * (lengthScale * Ideal.absNorm b0)^ε) *
        (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          ‖tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃)‖ *
            childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨C, hC, hb⟩ := fixed_second_mode_transfer p hp hcop hg ε hε
  refine ⟨C, hC, ?_⟩
  intro s T b0 w B lengthScale label F Ψ₁ Ψ₂ m V₁ V₂ X₁ X₂ b₁ b₂ b₃ hb0 hB hL hv hm ht hn hw hwc hl
  let f : Frequency → ℂ := fun q => fixedSecondMode p hp hcop hg s (w q) label F Ψ₁ Ψ₂ m
    (fixedSecondTest p V₁ X₁ q.1 q.2.2 true) (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false)
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m T V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m T V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m T V₁ X₁ true false) *
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m T V₂ X₂ false true)
  have hM : ∀ q, G q ≤ M := by
    intro q
    dsimp [G, childGeometricMean, M]
    gcongr
    · exact childEnergy_le p hp hcop hg F Ψ₁ m T V₁ X₁ true false q.1 q.2.2
    · exact childEnergy_le p hp hcop hg F Ψ₂ m T V₂ X₂ false true q.2.1 q.2.2
  have hf : Continuous f := by
    unfold f fixedSecondMode
    apply continuous_finsetSum
    intro x hx
    have hwx := hwc x hx
    have hc₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (label x) (newRow x) V₁ X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have hc₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (label x) (-newRow x) V₂ X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hwx.mul hc₁.star).mul hc₂
  have hpoint : ∀ q, ‖f q‖ ≤ (B * C * (lengthScale * Ideal.absNorm b0)^ε) * G q := by
    intro q
    have hh := hb s T b0 (w q) B lengthScale label F Ψ₁ Ψ₂ m
      (fixedSecondTest p V₁ X₁ q.1 q.2.2 true) (fixedSecondTest p V₂ X₂ q.2.1 q.2.2 false)
      hb0 hB hL hv hm ht hn (hw q) hl
    simpa only [f, G, childGeometricMean, childEnergy, mul_assoc] using hh
  exact triple_integral_bound b₁ b₂ b₃ f G hf hG hG0
    (B * C * (lengthScale * Ideal.absNorm b0)^ε) M (by positivity) hM hpoint

end SecondPassIntegration

end

end OAI
end OAIOriginalModule0125

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.RowMajorants
Source SHA256: d52d177d3b020f672d68290b522870617bc96eea472536b97c1c8a3c193e4f46
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0126


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
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem first_passage_transfer_input_family {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (H₁ H₂ : Finset ι → ℂ)
    (hΨ₁ : ∀ D ∈ F.powerset, ‖Ψ₁ (∏ i ∈ D, p i)‖ ≤ 1)
    (hΨ₂ : ∀ D ∈ F.powerset, ‖Ψ₂ (∏ i ∈ D, p i)‖ ≤ 1)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true (multiplicativeCoreColumn p Ψ₁ m₁ H₁)
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false (multiplicativeCoreColumn p Ψ₂ m₂ H₂)
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
  obtain ⟨K, hK, hb⟩ := FirstPassCubeLabels.first_passage_transfer p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ hv (multiplicativeCoreColumn p Ψ₁ m₁ H₁) (multiplicativeCoreColumn p Ψ₂ m₂ H₂)
    W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨(32 * 512) * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  have hf := hb lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  have h₁ := firstOutputEnergy_le_input_family p hp hcop hg hc hpr F B v ε₁ ε₂ true
    Ψ₁ m₁ H₁ V₁ X₁ c d J T hΨ₁
  have h₂ := firstOutputEnergy_le_input_family p hp hcop hg hc hpr F B v ε₁ ε₂ false
    Ψ₂ m₂ H₂ V₂ X₂ c d J T hΨ₂
  have hq : 0 ≤ lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ :=
    div_nonneg hL.le (norm_nonneg _)
  have hfactor : 0 ≤ M * K * Y ^ deltaLoss :=
    mul_nonneg (mul_nonneg hM hK) (Real.rpow_nonneg hY deltaLoss)
  calc
    _ ≤ (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (FirstPassCubeLabels.firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true
          (multiplicativeCoreColumn p Ψ₁ m₁ H₁) V₁ X₁ c d J T) *
        Real.sqrt (FirstPassCubeLabels.firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false
          (multiplicativeCoreColumn p Ψ₂ m₂ H₂) V₂ X₂ c d J T) := hf
    _ ≤ (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt ((32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt ((32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32 * 512),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32 * 512)]
      calc
        _ = (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
            (Real.sqrt (32 * 512)) ^ 2 *
            Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
            Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32 * 512)]; ring

end
section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem exists_rowMajorant : ∃ W : 𝓢(ℝ, ℂ),
    (∀ s : ℝ, 0 ≤ (W s).re) ∧
    (∀ s : ℝ, |s| ≤ 1 → W s = 1) ∧
    (∀ s : ℝ, 2 < s → W s = 0) := by
  obtain ⟨U, hUc, hUs, hUone, hUts, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff 1 (by norm_num)
  let f : ℝ → ℂ := fun s => U s * star (U s)
  have hfc : HasCompactSupport f := hUc.mul_right
  have hfs : ContDiff ℝ ∞ f := hUs.mul (Complex.conjCLE.contDiff.comp hUs)
  refine ⟨hfc.toSchwartzMap hfs, ?_, ?_, ?_⟩
  · intro s
    change 0 ≤ (U s * star (U s)).re
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (U s).re, sq_nonneg (U s).im]
  · intro s hs
    change U s * star (U s) = 1
    rw [hUone s hs]
    norm_num
  · intro s hs
    change U s * star (U s) = 0
    have hUz : U s = 0 := by
      by_contra hne
      have hu := hUts (subset_tsupport U (by exact hne))
      norm_num at hu
      linarith [hu.2]
    simp [hUz]

def rowMajorant : 𝓢(ℝ, ℂ) := Classical.choose exists_rowMajorant

lemma rowMajorant_nonneg (s : ℝ) : 0 ≤ (rowMajorant s).re :=
  (Classical.choose_spec exists_rowMajorant).1 s

lemma rowMajorant_one (s : ℝ) (hs : |s| ≤ 1) : rowMajorant s = 1 :=
  (Classical.choose_spec exists_rowMajorant).2.1 s hs

lemma rowMajorant_zero (s : ℝ) (hs : 2 < s) : rowMajorant s = 0 :=
  (Classical.choose_spec exists_rowMajorant).2.2 s hs

def rowMajorantBall (Y : ℝ) : Finset O := ShortDraftLatticeCount.rowNormBall (Nat.ceil (2 * Y))

lemma rowMajorant_zero_outside (Y : ℝ) (hY : 0 < Y) (z : O)
    (hz : z ∉ rowMajorantBall Y) : rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) = 0 := by
  have hn : Nat.ceil (2 * Y) < Ideal.absNorm (Ideal.span {z}) := by
    apply Nat.lt_of_not_ge
    intro hn
    exact hz (ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le _ z hn)
  have hn' : (Nat.ceil (2 * Y) : ℝ) < (Ideal.absNorm (Ideal.span {z}) : ℝ) := by exact_mod_cast hn
  apply rowMajorant_zero
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  apply (lt_div_iff₀ hY).2
  linarith [Nat.le_ceil (2 * Y)]

lemma rowMajorant_tsum_eq_sum (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) =
      ∑ z ∈ rowMajorantBall Y, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ) := by
  apply tsum_eq_sum
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz, zero_mul]

lemma rowMajorant_summable (P : O → ℂ) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun z : O => rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  intro z hz
  rw [rowMajorant_zero_outside Y hY z hz, zero_mul]

theorem finite_row_energy_le_rowMajorant (P : O → ℂ) (T : Finset O)
    (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    (∑ z ∈ T, ‖P z‖ ^ 2) ≤
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
  have hs := rowMajorant_summable P Y hY
  rw [Complex.re_tsum hs]
  calc
    _ = ∑ z ∈ T, (rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
      apply Finset.sum_congr rfl
      intro z hz
      have hratio : |‖eisEmbedding z‖ ^ 2 / Y| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)]
        apply (div_le_one hY).2
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact hT z hz
      rw [rowMajorant_one _ hratio, one_mul, Complex.ofReal_re]
    _ ≤ _ := by
      apply (Complex.hasSum_re hs.hasSum).summable.sum_le_tsum
      intro z hz
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem firstCoreInputRow_finite_le_second_poisson
    (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      (∑ G ∈ (F \ D).powerset, ∑ U ∈ ((F \ D) \ G).powerset, ∑ V' ∈ ((F \ D) \ G).powerset,
        if Disjoint U V' then
          overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
            (m * FirstPassCubeLabels.b0Label p B v ε₁ ε₂) (c * FirstPassCubeLabels.jLabel p B v ε₁ ε₂) d
            (firstCoreTest H V y negative t D) G U V' *
            maskedSecondDual p hg hp hinj G U V' rowMajorant Y
        else 0).re := by
  have he := firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂
    negative χ Ψ m H V y c d r t rowMajorant Y hY
  rw [← he]
  exact finite_row_energy_le_rowMajorant _ T Y hY hT

theorem firstCoreInputRow_majorant_integrable
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (Y : ℝ) (hY : 0 < Y)
    {k : ℝ → ℝ} (hk : Integrable k volume) :
    Integrable (fun t : ℝ => k t *
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re) volume := by
  simp_rw [rowMajorant_tsum_eq_sum _ Y hY, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro z hz
  convert (firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z hk).const_mul
    (rowMajorant (‖eisEmbedding z‖ ^ 2 / Y)).re using 1
  funext t
  ring

theorem firstCoreInputRow_integrated_le_majorant
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y)
    {k : ℝ → ℝ} (hk : Integrable k volume) (hk0 : ∀ t, 0 ≤ k t) :
    (∫ t : ℝ, k t * ∑ z ∈ T,
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
    ∫ t : ℝ, k t *
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) *
        (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)).re := by
  apply integral_mono
  · simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun z hz =>
      firstCoreInputRow_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r z hk)
  · exact firstCoreInputRow_majorant_integrable p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r Y hY hk
  · intro t
    exact mul_le_mul_of_nonneg_left (finite_row_energy_le_rowMajorant _ T Y hY hT) (hk0 t)

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondPreKernelPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    star (secondPreColumn p hp hcop hg Ψ₁ (m * (e * r)) c d e k₁ (fun _ => 1) S) *
      secondPreColumn p hp hcop hg Ψ₂ (m * (e * r)) c d e k₂ (fun _ => 1) T * K S T else 0

def secondChildKernelPair (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
    star (secondChildColumn p hp hcop hg Ψ₁ (m * r) (c * e * ∏ i ∈ V, p i)
      (d * e * k₁) (fun _ => 1) N) *
    secondChildColumn p hp hcop hg Ψ₂ (m * r) (c * e * ∏ i ∈ V, p i)
      (d * e * k₂) (fun _ => 1) M * K (V ∪ N) (V ∪ M)

theorem secondPreKernelPair_eq_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondPreKernelPair p hp hcop hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
      ∑ V ∈ F.powerset, secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  unfold secondPreKernelPair
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro V hV
  rw [secondCommonWeight, supportMobius, prime_product_moebius _ hprime hinj]
  simp only [secondChildKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hdN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hdM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondPreColumn_union p hp hcop hg hpr Ψ₁ m r c d e k₁ (fun _ => 1) V N hdN,
    secondPreColumn_union p hp hcop hg hpr Ψ₂ m r c d e k₂ (fun _ => 1) V M hdM, star_mul]
  ring

def secondKernelPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T * K S T else 0

theorem secondKernelPair_eq_pre
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k K =
      ∑ z : SecondRayIndex, secondRayCoefficient z *
        secondPreKernelPair p hp hcop hg F (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
          m r c d e k (-k) K := by
  have hterm (S T : Finset ι) :
      (if Disjoint S T then secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
        (fun _ => 1) (fun _ => 1) S T * K S T else 0) =
      ∑ z : SecondRayIndex, secondRayCoefficient z * (if Disjoint S T then
        star (secondPreColumn p hp hcop hg (secondRayMinus Ψ₁ z) (m * (e * r)) c d e k (fun _ => 1) S) *
        secondPreColumn p hp hcop hg (secondRayPlus Ψ₂ z) (m * (e * r)) c d e (-k) (fun _ => 1) T * K S T else 0) := by
    by_cases hd : Disjoint S T
    · simp only [ite_eq_left hd, secondGaussTerm]
      have h := congrArg (fun a : ℂ => a * K S T)
        (second_gauss_ray_expansion p hp hcop hg hinj hc hpr Ψ₁ Ψ₂
          (m * (e * r)) c d e k (fun _ => 1) (fun _ => 1) S T hd)
      simpa only [Fintype.sum_prod_type, secondRayCoefficient, secondRayMinus,
        secondRayPlus, Finset.sum_mul, mul_assoc] using h
    · simp [hd]
  unfold secondKernelPair
  simp_rw [hterm]
  calc
    _ = ∑ S ∈ F.powerset, ∑ z : SecondRayIndex, ∑ T ∈ F.powerset,
        secondRayCoefficient z * (if Disjoint S T then
        star (secondPreColumn p hp hcop hg (secondRayMinus Ψ₁ z) (m * (e * r)) c d e k (fun _ => 1) S) *
        secondPreColumn p hp hcop hg (secondRayPlus Ψ₂ z) (m * (e * r)) c d e (-k) (fun _ => 1) T * K S T else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [secondPreKernelPair, Finset.mul_sum]

theorem secondKernelPair_eq_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (K : Finset ι → Finset ι → ℂ) :
    secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k K =
      ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
            m r c d e k (-k) K := by
  rw [secondKernelPair_eq_pre p hp hcop hg hinj hc hpr]
  simp only [secondPreKernelPair_eq_children p hp hcop hg hinj hpr,
    secondTotalWeight, Finset.mul_sum, mul_assoc]

end SecondPassArithmetic

namespace CubicEisenstein
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal

def denominatorCondition (c d : O) : Prop := IsCoprime c d ∧ (3 : O) ∣ d-1
abbrev AdmissibleDenominator (c : O) := {d : O // denominatorCondition c d}
abbrev LevelLower := {c : O // (3 : O) ∣ c}

lemma denominatorCondition_shift (c d n : O) :
    denominatorCondition c (d+3*c*n) ↔ denominatorCondition c d := by
  constructor
  · rintro ⟨⟨a,b,h⟩,hd⟩
    refine ⟨⟨a+b*3*n,b,by linear_combination h⟩, ?_⟩
    have h3 : (3 : O) ∣ 3*c*n := ⟨c*n,by ring⟩
    convert dvd_sub hd h3 using 1 ; ring
  · rintro ⟨⟨a,b,h⟩,hd⟩
    refine ⟨⟨a-b*3*n,b,by linear_combination h⟩, ?_⟩
    have h3 : (3 : O) ∣ 3*c*n := ⟨c*n,by ring⟩
    convert dvd_add hd h3 using 1 ; ring

lemma row_symbol_shift (c d n : O) (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    symbol c (d+3*c*n)=symbol c d := by
  have hdn : (3 : O) ∣ d+3*c*n-1 := by
    convert dvd_add hd (show (3 : O) ∣ 3*c*n from ⟨c*n,by ring⟩) using 1 ; ring
  have h9 : (9 : O) ∣ d+3*c*n-d := by
    obtain ⟨c0,rfl⟩ := hc
    exact ⟨c0*n,by ring⟩
  exact symbol_denominator_congr c (d+3*c*n) d
    (lambda_sq_dvd_three.trans hdn) (lambda_sq_dvd_three.trans hd) h9
    ⟨3*n,by ring⟩

def primitiveSigmaEquiv : PrimitiveRow ≃ Σ c : LevelLower, AdmissibleDenominator c.1 where
  toFun r := ⟨⟨r.1 0,r.2.2.1⟩,⟨r.1 1,r.2.1,r.2.2.2⟩⟩
  invFun p := ⟨![p.1.1,p.2.1],p.2.2.1,p.1.2,p.2.2.2⟩
  left_inv r := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv p := by rfl

abbrev DenominatorResidue (c : O) := O ⧸ Ideal.span {3*c}
def denominatorRep (c : O) (r : DenominatorResidue c) : O :=
  GaussianShiftedPartition.representative (3*c) r
lemma denominatorRep_spec (c : O) (r : DenominatorResidue c) :
    Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r)=r :=
  GaussianShiftedPartition.representative_spec (3*c) r
abbrev AdmissibleResidue (c : O) :=
  {r : DenominatorResidue c // denominatorCondition c (denominatorRep c r)}

lemma finite_admissibleResidue (c : O) (hc : c ≠ 0) : Finite (AdmissibleResidue c) := by
  let : Finite (DenominatorResidue c) := finite_quotient_span (mul_ne_zero (by norm_num) hc)
  infer_instance

def residueDenominatorMap (c : O) (p : AdmissibleResidue c × O) : AdmissibleDenominator c :=
  ⟨denominatorRep c p.1.1+3*c*p.2,(denominatorCondition_shift c _ _).2 p.1.2⟩

lemma residueDenominatorMap_bijective (c : O) (hc : c ≠ 0) :
    Function.Bijective (residueDenominatorMap c) := by
  have h3c : 3*c ≠ 0 := mul_ne_zero (by norm_num) hc
  have hq (r : DenominatorResidue c) (n : O) :
      Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r+3*c*n)=r := by
    have hzero : Ideal.Quotient.mk (Ideal.span {3*c}) (3*c)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_add, map_mul, hzero, zero_mul, add_zero, denominatorRep_spec]
  constructor
  · rintro ⟨r,n⟩ ⟨t,m⟩ heq
    have h := congrArg Subtype.val heq
    change denominatorRep c r.1+3*c*n=denominatorRep c t.1+3*c*m at h
    have hrt : r=t := by
      apply Subtype.ext
      simpa only [hq] using congrArg (Ideal.Quotient.mk (Ideal.span {3*c})) h
    subst t
    have hnm : n=m := mul_left_cancel₀ h3c (add_left_cancel h)
    subst m
    rfl
  · intro d
    let r : DenominatorResidue c := Ideal.Quotient.mk (Ideal.span {3*c}) d.1
    have hr : Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r)=r := denominatorRep_spec c r
    have hdiv : 3*c ∣ d.1-denominatorRep c r := by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact hr.symm
    obtain ⟨n,hn⟩ := hdiv
    have hd : d.1=denominatorRep c r+3*c*n := by linear_combination hn
    have hrcond : denominatorCondition c (denominatorRep c r) := by
      apply (denominatorCondition_shift c _ n).1
      rw [← hd]
      exact d.2
    refine ⟨(⟨r,hrcond⟩,n), ?_⟩
    apply Subtype.ext
    exact hd.symm

def residueDenominatorEquiv (c : O) (hc : c ≠ 0) :
    AdmissibleResidue c × O ≃ AdmissibleDenominator c :=
  Equiv.ofBijective (residueDenominatorMap c) (residueDenominatorMap_bijective c hc)

lemma residueDenominatorEquiv_val (c : O) (hc : c ≠ 0) (p : AdmissibleResidue c × O) :
    ((residueDenominatorEquiv c hc) p).1=denominatorRep c p.1.1+3*c*p.2 := rfl

def primitiveTerm (z : ℂ) (v : ℝ) (s : ℂ) (c d : O) : ℂ :=
  eisEmbedding (symbol c d) *
    ((v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s

theorem primitive_terms_summable (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    Summable (fun p : Σ c : LevelLower, AdmissibleDenominator c.1 =>
      primitiveTerm z v s p.1.1 p.2.1) := by
  apply primitiveSigmaEquiv.summable_iff.mp
  exact (primitive_rows_summable_norm z v hv s hs).of_norm

theorem upperEisenstein_eq_by_lower (z : ℂ) (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    upperEisenstein z v hv s=
      ∑' c : LevelLower, ∑' d : AdmissibleDenominator c.1, primitiveTerm z v s c.1 d.1 := by
  rw [upperEisenstein_eq_primitive_rows]
  exact (primitiveSigmaEquiv.tsum_eq (fun p : Σ c : LevelLower, AdmissibleDenominator c.1 =>
    primitiveTerm z v s p.1.1 p.2.1)).trans (primitive_terms_summable z v hv s hs).tsum_sigma

theorem denominator_sum_residues (c : O) (hc : c ≠ 0) (f : O → ℂ)
    (hf : Summable (fun d : AdmissibleDenominator c => f d.1)) :
    (∑' d : AdmissibleDenominator c, f d.1)=
      ∑' r : AdmissibleResidue c, ∑' n : O, f (denominatorRep c r.1+3*c*n) := by
  have hsum := (residueDenominatorEquiv c hc).summable_iff.mpr hf
  exact ((residueDenominatorEquiv c hc).tsum_eq
    (fun d : AdmissibleDenominator c => f d.1)).symm.trans hsum.tsum_prod

lemma primitiveTerm_shift (z : ℂ) (v : ℝ) (s : ℂ) (c d n : O)
    (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    primitiveTerm z v s c (d+3*c*n)=
      primitiveTerm (z+3*eisEmbedding n) v s c d := by
  unfold primitiveTerm
  rw [row_symbol_shift c d n hc hd]
  have harg : eisEmbedding c*z+eisEmbedding (d+3*c*n)=
      eisEmbedding c*(z+3*eisEmbedding n)+eisEmbedding d := by
    simp only [map_add,map_mul,map_ofNat]
    ring
  rw [harg]

lemma denominator_zero_unique (d : AdmissibleDenominator 0) : d.1=1 := by
  apply A3_primary_unit_eq_one _ _ (lambda_sq_dvd_three.trans d.2.2)
  simpa only [isCoprime_zero_left] using d.2.1

lemma zero_lower_sum (z : ℂ) (v : ℝ) (s : ℂ) :
    (∑' d : AdmissibleDenominator 0, primitiveTerm z v s 0 d.1)=(v:ℂ)^s := by
  let d0 : AdmissibleDenominator 0 := ⟨1,isCoprime_one_right,by simp⟩
  rw [tsum_eq_single d0]
  · simp [primitiveTerm,d0,symbol_one]
  · intro d hd
    exfalso
    apply hd
    exact Subtype.ext (denominator_zero_unique d)

def residueSeries (z : ℂ) (v : ℝ) (s : ℂ) (c : O) : ℂ :=
  ∑' r : AdmissibleResidue c, ∑' n : O,
    primitiveTerm (z+3*eisEmbedding n) v s c (denominatorRep c r.1)

theorem upperEisenstein_eq_residue_series (z : ℂ) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (hs : 2 < s.re) :
    upperEisenstein z v hv s =
      ∑' c : LevelLower, if c.1=0 then (v:ℂ)^s else residueSeries z v s c.1 := by
  rw [upperEisenstein_eq_by_lower z v hv s hs]
  apply tsum_congr
  rintro ⟨c,hlevel⟩
  dsimp only
  split_ifs with hc
  · subst c
    exact zero_lower_sum z v s
  · have hsum : Summable (fun d : AdmissibleDenominator c => primitiveTerm z v s c d.1) :=
      (primitive_terms_summable z v hv s hs).sigma_factor ⟨c, hlevel⟩
    rw [denominator_sum_residues c hc (fun d : O => primitiveTerm z v s c d) hsum]
    apply tsum_congr
    intro r
    apply tsum_congr
    intro n
    exact primitiveTerm_shift z v s c (denominatorRep c r.1) n hlevel r.2.2

lemma residueSeries_finite (z : ℂ) (v : ℝ) (s : ℂ) (c : O) (hc : c ≠ 0) :
    letI : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
    residueSeries z v s c = ∑ r : AdmissibleResidue c, ∑' n : O,
      primitiveTerm (z+3*eisEmbedding n) v s c (denominatorRep c r.1) := by
  let : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
  exact tsum_fintype _

end CubicEisenstein

open MeasureTheory Set Module
open scoped BigOperators Classical ENNReal

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def periodBasis : Basis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.map (eisensteinLatticeMap 3 (by norm_num)).toLinearEquiv
lemma periodBasis_zero : periodBasis 0=3 := by
  simp [periodBasis,eisensteinLatticeMap,scaledBasisEquiv_apply]
lemma periodBasis_one : periodBasis 1=3*omega3 := by
  simp [periodBasis,eisensteinLatticeMap,scaledBasisEquiv_apply]

def periodLattice : Submodule ℤ ℂ := Submodule.span ℤ (Set.range periodBasis)
def periodDomain : Set ℂ := ZSpan.fundamentalDomain periodBasis

instance : Countable periodLattice := by unfold periodLattice; infer_instance
instance : VAddInvariantMeasure periodLattice ℂ volume :=
  inferInstanceAs (VAddInvariantMeasure periodLattice.toAddSubgroup ℂ volume)

lemma periodDomain_fundamental : IsAddFundamentalDomain periodLattice periodDomain volume :=
  ZSpan.isAddFundamentalDomain periodBasis volume
lemma periodDomain_measurable : MeasurableSet periodDomain :=
  ZSpan.fundamentalDomain_measurableSet periodBasis

lemma three_embedding_mem (n : O) : 3*eisEmbedding n ∈ periodLattice := by
  have hzero : periodBasis 0 ∈ periodLattice := Submodule.subset_span ⟨0,rfl⟩
  have hone : periodBasis 1 ∈ periodLattice := Submodule.subset_span ⟨1,rfl⟩
  have h := periodLattice.add_mem
    (periodLattice.smul_mem (ActualEisensteinCoordinates.coords n).1 hzero)
    (periodLattice.smul_mem (ActualEisensteinCoordinates.coords n).2 hone)
  rw [periodBasis_zero,periodBasis_one] at h
  convert h using 1
  conv_lhs => rw [← ActualEisensteinCoordinates.eval_coords n,eisEmbedding_eval]
  simp only [zsmul_eq_mul,]
  ring

def periodPoint (n : O) : periodLattice := ⟨3*eisEmbedding n,three_embedding_mem n⟩
lemma periodPoint_val (n : O) : (periodPoint n : ℂ)=3*eisEmbedding n := rfl
lemma periodPoint_bijective : Function.Bijective periodPoint := by
  constructor
  · intro n m h
    apply eisEmbedding_injective
    exact mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) (congrArg Subtype.val h)
  · intro p
    have h := (periodBasis.mem_span_iff_repr_mem ℤ p.1).mp p.2
    obtain ⟨a,ha⟩ := h 0
    obtain ⟨b,hb⟩ := h 1
    change (a:ℝ)=_ at ha
    change (b:ℝ)=_ at hb
    refine ⟨ActualEisensteinCoordinates.eval a b, ?_⟩
    apply Subtype.ext
    change 3*eisEmbedding (ActualEisensteinCoordinates.eval a b)=p.1
    rw [← periodBasis.sum_repr p.1,Fin.sum_univ_two,← ha,← hb,
      periodBasis_zero,periodBasis_one,eisEmbedding_eval]
    simp only [Complex.real_smul,Complex.ofReal_intCast]
    ring

def periodEquiv : O ≃ periodLattice := Equiv.ofBijective _ periodPoint_bijective

theorem integral_eq_period_integrals (f : ℂ → ℂ) (hf : Integrable f) :
    (∫ z : ℂ, f z)=∑' n : O,∫ z in periodDomain,f (z+3*eisEmbedding n) := by
  rw [periodDomain_fundamental.integral_eq_tsum'' f hf]
  rw [← periodEquiv.tsum_eq]
  apply tsum_congr
  intro n
  apply setIntegral_congr_fun periodDomain_measurable
  intro z hz
  change f (3*eisEmbedding n+z)=f (z+3*eisEmbedding n)
  rw [add_comm]

theorem lintegral_eq_period_lintegrals (f : ℂ → ℝ≥0∞) :
    (∫⁻ z : ℂ, f z)=∑' n : O,∫⁻ z in periodDomain,f (z+3*eisEmbedding n) := by
  rw [periodDomain_fundamental.lintegral_eq_tsum'' f]
  rw [← periodEquiv.tsum_eq]
  apply tsum_congr
  intro n
  apply setLIntegral_congr_fun periodDomain_measurable
  intro z hz
  change f (3*eisEmbedding n+z)=f (z+3*eisEmbedding n)
  rw [add_comm]

lemma periodDomain_volume : volume periodDomain=ENNReal.ofReal (9*Real.sqrt 3/2) := by
  have hunit : volume (ZSpan.fundamentalDomain Complex.basisOneI)=1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI volume)]
    exact Complex.orthonormalBasisOneI.volume_parallelepiped
  rw [periodDomain,ZSpan.measure_fundamentalDomain periodBasis volume Complex.basisOneI,hunit,mul_one]
  congr 1
  rw [Basis.det_apply,Matrix.det_fin_two]
  norm_num [Basis.toMatrix_apply,periodBasis_zero,periodBasis_one,
    Complex.coe_basisOneI_repr,EisensteinEmbedding.omega3_im]
  rw [abs_of_nonneg (by positivity)]
  ring

lemma periodization_lintegral_norm_ne_top (f : ℂ → ℂ) (hf : Integrable f) :
    (∑' n : O,∫⁻ z in periodDomain,‖f (z+3*eisEmbedding n)‖ₑ) ≠ ⊤ := by
  rw [← lintegral_eq_period_lintegrals (fun z => ‖f z‖ₑ)]
  exact hf.hasFiniteIntegral.ne

theorem integral_periodization (f : ℂ → ℂ) (hf : Integrable f) :
    (∫ z in periodDomain,∑' n : O,f (z+3*eisEmbedding n))=∫ z : ℂ,f z := by
  let : Countable O := latticeCoordEquiv.injective.countable
  rw [integral_tsum]
  · exact (integral_eq_period_integrals f hf).symm
  · intro n
    exact (hf.comp_add_right (3*eisEmbedding n)).aestronglyMeasurable.restrict
  · exact periodization_lintegral_norm_ne_top f hf

end CubicEisenstein

end

end OAI
end OAIOriginalModule0126

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.FourierCoefficients
Source SHA256: 73f35c200beb697d81223235ddba7c6d3529aa62c0857a42bdf65beb535a2001
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0127



namespace OAI

noncomputable section

namespace CubicEisenstein

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
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

open ActualEisensteinCubic ConcreteTraceCRT

lemma breveE_embedding_div_traceLambda (n : O) :
    ShortDraftTrace.breveE (eisEmbedding n/eisLam)=1 := by
  rw [← ActualEisensteinCoordinates.eval_coords n,eisEmbedding_eval]
  exact ConcreteBreveE.breveE_period_coordinates _ _

def cuspFrequency (h : O) : ℂ := eisEmbedding h/(3*eisLam)

lemma cuspFrequency_period (h n : O) :
    ShortDraftTrace.breveE (cuspFrequency h*(3*eisEmbedding n))=1 := by
  have heq : cuspFrequency h*(3*eisEmbedding n)=eisEmbedding (h*n)/eisLam := by
    rw [cuspFrequency,map_mul]
    field_simp
  rw [heq]
  exact breveE_embedding_div_traceLambda (h*n)

lemma cuspFrequency_negative_period (h n : O) (z : ℂ) :
    ShortDraftTrace.breveE (-cuspFrequency h*(z+3*eisEmbedding n))=
      ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  rw [mul_add,AddChar.map_add_eq_mul]
  have hp : ShortDraftTrace.breveE (-cuspFrequency h*(3*eisEmbedding n))=1 := by
    rw [neg_mul,AddChar.map_neg_eq_inv,cuspFrequency_period,inv_one]
  rw [hp,mul_one]

lemma trace_mul_integrable (f : ℂ → ℂ) (hf : Integrable f) (freq : ℂ) :
    Integrable (fun z => f z*ShortDraftTrace.breveE (-freq*z)) := by
  have hchar : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-freq*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul hchar.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun z => by simp only [norm_mul,breveE_norm,mul_one,le_refl]

lemma integrableOn_periodization (f : ℂ → ℂ) (hf : Integrable f) :
    IntegrableOn (fun z => ∑' n : O,f (z+3*eisEmbedding n)) periodDomain := by
  let : Countable O := latticeCoordEquiv.injective.countable
  have hm (n : O) : AEStronglyMeasurable (fun z => f (z+3*eisEmbedding n))
      (volume.restrict periodDomain) :=
    (hf.comp_add_right (3*eisEmbedding n)).aestronglyMeasurable.restrict
  refine ⟨AEStronglyMeasurable.tsum hm, ?_⟩
  change (∫⁻ z in periodDomain,‖∑' n : O,f (z+3*eisEmbedding n)‖ₑ)<⊤
  apply lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) _
  rw [lintegral_tsum (fun n => (hm n).enorm)]
  exact lt_top_iff_ne_top.mpr (periodization_lintegral_norm_ne_top f hf)

theorem integral_fourier_periodization (f : ℂ → ℂ) (hf : Integrable f) (h : O) :
    (∫ z in periodDomain,(∑' n : O,f (z+3*eisEmbedding n))*
      ShortDraftTrace.breveE (-cuspFrequency h*z))=
        ∫ z : ℂ,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  have heq : (fun z : ℂ => (∑' n : O,f (z+3*eisEmbedding n))*
      ShortDraftTrace.breveE (-cuspFrequency h*z)) =
      (fun z : ℂ => ∑' n : O,f (z+3*eisEmbedding n)*
        ShortDraftTrace.breveE (-cuspFrequency h*(z+3*eisEmbedding n))) := by
    funext z
    simp only [cuspFrequency_negative_period,tsum_mul_right]
  rw [heq]
  exact integral_periodization _ (trace_mul_integrable f hf (cuspFrequency h))

end

section
open MeasureTheory Set Filter Module
open scoped BigOperators Classical ENNReal MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT

lemma continuous_inverse_upper_operator (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => rowOperator (upperSection z v hv)⁻¹) := by
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_pi
  intro i
  simp only [rowOperator_apply,upperSection,
    Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  fin_cases i <;> simp only [] <;> fun_prop

lemma continuous_upper_rowBound (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => rowBound (upperSection z v hv)) :=
  continuous_const.mul (continuous_const.add (continuous_inverse_upper_operator v hv).norm)

lemma norm_mem_periodDomain (z : ℂ) (hz : z ∈ periodDomain) :
    ‖z‖ ≤ ∑ i : Fin 2, ‖periodBasis i‖ := by
  have heq := (ZSpan.fract_eq_self (b := periodBasis)).mpr hz
  simpa only [heq] using ZSpan.norm_fract_le periodBasis z

lemma exists_upper_rowBound (v : ℝ) (hv : 0 < v) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ periodDomain, rowBound (upperSection z v hv) ≤ C := by
  let R : ℝ := ∑ i : Fin 2, ‖periodBasis i‖
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).bddAbove_image
    (continuous_upper_rowBound v hv).continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro z hz
  apply (hC ?_).trans (le_max_right _ _)
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz,rfl⟩

lemma continuous_upper_summand (v : ℝ) (hv : 0 < v) (s : ℂ) (x : CuspCosets) :
    Continuous (fun z : ℂ => summand (upperSection z v hv) s x) := by
  simp_rw [summand_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    apply continuous_const.div
    · unfold heightDenominator
      fun_prop
    · intro z
      exact (heightDenominator_pos z v hv _ (embeddedRow_ne_zero x)).ne'
  · exact continuous_const
  · intro z
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos hv (heightDenominator_pos z v hv _ (embeddedRow_ne_zero x))

lemma upper_summable_majorant (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    ∃ M : CuspCosets → ℝ, Summable M ∧ (∀ x,0 ≤ M x) ∧
      ∀ z ∈ periodDomain, ∀ x, ‖summand (upperSection z v hv) s x‖ ≤ M x := by
  obtain ⟨C,hC,hbound⟩ := exists_upper_rowBound v hv
  refine ⟨fun x => C^(2*s.re)*‖rowCoordinates (cosetRow x)‖^(-(2*s.re)),?_,?_,?_⟩
  · have hsumm := summable_integer_four_rpow (2*s.re) (by linarith)
    have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
      rowCoordinates_injective.comp cosetRow_injective
    exact (hsumm.comp_injective hinj).mul_left _
  · intro x
    positivity
  · intro z hz x
    apply (norm_summand_bound (upperSection z v hv) s (by linarith) x).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (rowBound_pos _).le (hbound z hz) (by linarith)) (by positivity)

lemma periodDomain_finiteMeasure : IsFiniteMeasure (volume.restrict periodDomain) := by
  constructor
  rw [Measure.restrict_apply_univ,periodDomain_volume]
  exact ENNReal.ofReal_lt_top

theorem hasSum_integral_upperEisenstein (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun x : CuspCosets => ∫ z in periodDomain,
      summand (upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z))
      (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z)) := by
  let : Countable CuspCosets :=
    (rowCoordinates_injective.comp cosetRow_injective).countable
  let := periodDomain_finiteMeasure
  obtain ⟨M,hM,hMnonneg,hbound⟩ := upper_summable_majorant v hv s hs
  have hchar : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-freq*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  have hsum := hasSum_integral_of_dominated_convergence
    («μ» := volume.restrict periodDomain)
    (fun (x : CuspCosets) (_ : ℂ) => M x)
    (fun x => ((continuous_upper_summand v hv s x).mul hchar).aestronglyMeasurable.restrict)
    (fun x => (ae_restrict_mem periodDomain_measurable).mono fun z hz => by
      simpa only [Pi.mul_apply,norm_mul,breveE_norm,mul_one] using hbound z hz x)
    (Eventually.of_forall fun _ => hM)
    (integrable_const (∑' x,M x))
    (Eventually.of_forall fun z => (summable_summand (upperSection z v hv) s hs).hasSum.mul_right
      (ShortDraftTrace.breveE (-freq*z)))
  exact hsum

theorem integral_upperEisenstein_eq_sum (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z))=
      ∑' x : CuspCosets,∫ z in periodDomain,
        summand (upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z) :=
  (hasSum_integral_upperEisenstein v hv s freq hs).tsum_eq.symm

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

def shiftedHeightKernel (v : ℝ) (s b z : ℂ) : ℂ :=
  (v:ℂ)^(-s)*hyperbolicKernel s ((z+b)/(v:ℂ))

lemma shiftedHeightKernel_integrable (v : ℝ) (hv : 0 < v) (s b : ℂ) (hs : 1 < s.re) :
    Integrable (shiftedHeightKernel v s b) := by
  have h := ((hyperbolicKernel_integrable s hs).comp_smul (inv_ne_zero hv.ne')).comp_add_right b
  apply (h.const_mul ((v:ℂ)^(-s))).congr
  exact Eventually.of_forall fun z => by
    simp only [shiftedHeightKernel,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

lemma primitiveTerm_eq_shiftedHeightKernel (z : ℂ) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (c d : O) (hc : c ≠ 0) :
    primitiveTerm z v s c d =
      (eisEmbedding (symbol c d)*(‖eisEmbedding c‖^2:ℝ) ^ (-s:ℂ))*
        shiftedHeightKernel v s (eisEmbedding d/eisEmbedding c) z := by
  have hc' := eisEmbedding_ne_zero hc
  have hnorm : 0 < ‖eisEmbedding c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hc')
  have hfac : eisEmbedding c*z+eisEmbedding d =
      eisEmbedding c*(z+eisEmbedding d/eisEmbedding c) := by field_simp
  have heq : v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2) =
      ((‖eisEmbedding c‖^2*v)*(1+‖(z+eisEmbedding d/eisEmbedding c)/(v:ℂ)‖^2))⁻¹ := by
    rw [hfac,norm_mul,mul_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg hv.le]
    field_simp
    ; ring
  unfold primitiveTerm shiftedHeightKernel hyperbolicKernel
  rw [heq,Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg (by positivity),← Complex.cpow_neg]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_nonneg hnorm.le hv.le) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hnorm.le hv.le]
  ring

lemma primitiveTerm_integrable (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (c d : O) (hc : c ≠ 0) : Integrable (fun z => primitiveTerm z v s c d) := by
  simp_rw [primitiveTerm_eq_shiftedHeightKernel _ v hv s c d hc]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma traceIntegral_translate (f : ℂ → ℂ) (b freq : ℂ) :
    (∫ z : ℂ,f (z+b)*ShortDraftTrace.breveE (-freq*z))=
      ShortDraftTrace.breveE (freq*b)*(∫ z : ℂ,f z*ShortDraftTrace.breveE (-freq*z)) := by
  have heq (z : ℂ) : f (z+b)*ShortDraftTrace.breveE (-freq*z)=
      ShortDraftTrace.breveE (freq*b)*(f (z+b)*ShortDraftTrace.breveE (-freq*(z+b))) := by
    rw [mul_left_comm (ShortDraftTrace.breveE (freq*b)),
      ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [heq]
  rw [integral_const_mul,integral_add_right_eq_self (fun z => f z*ShortDraftTrace.breveE (-freq*z)) b]

lemma traceIntegral_scale (v : ℝ) (hv : 0 < v) (s freq : ℂ) :
    (∫ z : ℂ,hyperbolicKernel s (z/(v:ℂ))*ShortDraftTrace.breveE (-freq*z))=
      (v:ℂ)^2*sourceFourierKernel s (freq*v) := by
  have heq (z : ℂ) : hyperbolicKernel s (z/(v:ℂ))*ShortDraftTrace.breveE (-freq*z)=
      (fun w : ℂ => hyperbolicKernel s w*ShortDraftTrace.breveE (-(freq*v)*w)) (v⁻¹ • z) := by
    simp only [Complex.real_smul,Complex.ofReal_inv]
    congr 2
    · ring
    · field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  simp_rw [heq]
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ)
    (fun w : ℂ => hyperbolicKernel s w*ShortDraftTrace.breveE (-(freq*v)*w)) hv.le
  simpa only [Complex.finrank_real_complex,Complex.real_smul,Complex.ofReal_pow,sourceFourierKernel] using h

lemma traceIntegral_shiftedHeightKernel (v : ℝ) (hv : 0 < v) (s b freq : ℂ) :
    (∫ z : ℂ,shiftedHeightKernel v s b z*ShortDraftTrace.breveE (-freq*z))=
      (v:ℂ)^(2-s)*ShortDraftTrace.breveE (freq*b)*sourceFourierKernel s (freq*v) := by
  simp only [shiftedHeightKernel,mul_assoc]
  rw [integral_const_mul,traceIntegral_translate (fun z => hyperbolicKernel s (z/(v:ℂ))) b freq,
    traceIntegral_scale v hv s freq]
  have hp : (v:ℂ)^(-s)*(v:ℂ)^2=(v:ℂ)^(2-s) := by
    rw [← Complex.cpow_natCast,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
    congr 1
    ring
  calc
    _ = ((v:ℂ)^(-s)*(v:ℂ)^2)*ShortDraftTrace.breveE (freq*b)*sourceFourierKernel s (freq*v) := by ring
    _ = _ := by rw [hp]; ring

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Pointwise

open ActualEisensteinCubic ConcreteTraceCRT

lemma period_integral_translation (f : ℂ → ℂ)
    (hperiod : ∀ (n : O) (z : ℂ), f (z+3*eisEmbedding n)=f z) (b : ℂ) :
    (∫ z in periodDomain,f (b+z))=∫ z in periodDomain,f z := by
  have hperiod' (n : periodLattice) (z : ℂ) : f (n+ᵥz)=f z := by
    obtain ⟨m,rfl⟩ := periodEquiv.surjective n
    change f (3*eisEmbedding m+z)=f z
    simpa only [add_comm] using hperiod m z
  have hD := periodDomain_fundamental.vadd_of_comm b
  have heq := periodDomain_fundamental.setIntegral_eq hD hperiod'
  have hchange := (measurePreserving_add_left volume b).setIntegral_image_emb
    (measurableEmbedding_const_vadd b) f periodDomain
  exact hchange.symm.trans heq.symm

lemma breveE_quarter_eq_neg_one : ShortDraftTrace.breveE (1/4:ℂ)=-1 := by
  change Complex.exp (2*Real.pi*Complex.I*((1/4:ℂ)+starRingEnd ℂ (1/4:ℂ)))=-1
  norm_num only [map_div₀,map_one,map_ofNat]
  convert Complex.exp_pi_mul_I using 1 ; congr 1 ; ring

lemma cuspFrequency_ne_zero (h : O) (hh : h ≠ 0) : cuspFrequency h ≠ 0 :=
  div_ne_zero (eisEmbedding_ne_zero hh) (mul_ne_zero (by norm_num) eisLam_ne_zero)

theorem integral_cusp_character (h : O) :
    (∫ z in periodDomain,ShortDraftTrace.breveE (-cuspFrequency h*z))=
      if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0 := by
  by_cases hh : h=0
  · subst h
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
      AddChar.map_zero_eq_one,ite_true,setIntegral_const,measureReal_def,periodDomain_volume,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 9*Real.sqrt 3/2),Complex.real_smul,mul_one]
  · rw [ite_eq_right hh]
    let freq := cuspFrequency h
    let b : ℂ := -(4*freq)⁻¹
    have hfreq : freq ≠ 0 := cuspFrequency_ne_zero h hh
    have harg : -freq*b=(1/4:ℂ) := by dsimp [b]; field_simp
    have hphase : ShortDraftTrace.breveE (-freq*b)=-1 := by rw [harg,breveE_quarter_eq_neg_one]
    have heq := period_integral_translation
      (fun z => ShortDraftTrace.breveE (-freq*z))
      (fun n z => cuspFrequency_negative_period h n z) b
    have hpoint (z : ℂ) : ShortDraftTrace.breveE (-freq*(b+z))=
        -ShortDraftTrace.breveE (-freq*z) := by
      rw [mul_add,AddChar.map_add_eq_mul,hphase,neg_one_mul]
    simp_rw [hpoint,integral_neg] at heq
    linear_combination (-1/2:ℂ)*heq

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

def primitiveRowIntegral (v : ℝ) (s freq : ℂ) (c d : O) : ℂ :=
  ∫ z in periodDomain,primitiveTerm z v s c d*ShortDraftTrace.breveE (-freq*z)

lemma integral_summand_eq_primitiveRowIntegral (v : ℝ) (hv : 0 < v)
    (s freq : ℂ) (x : CuspCosets) :
    (∫ z in periodDomain,summand (upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z))=
      primitiveRowIntegral v s freq (cosetRow x 0) (cosetRow x 1) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [summand_upperSection,inverse_cosetCharacter_eq_row_symbol]
    rfl

lemma hasSum_primitiveRowIntegrals (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun p : Σ c : LevelLower,AdmissibleDenominator c.1 =>
      primitiveRowIntegral v s freq p.1.1 p.2.1)
      (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z)) := by
  apply primitiveSigmaEquiv.hasSum_iff.mp
  apply primitiveRowEquiv.hasSum_iff.mp
  exact (hasSum_integral_upperEisenstein v hv s freq hs).congr_fun
    fun x => (integral_summand_eq_primitiveRowIntegral v hv s freq x).symm

lemma primitiveRowIntegral_sum_translate (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (h c d : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hd : (3:O) ∣ d-1) :
    (∑' n : O,primitiveRowIntegral v s (cuspFrequency h) c (d+3*c*n))=
      ∫ z : ℂ,primitiveTerm z v s c d*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  have hint := trace_mul_integrable (fun z => primitiveTerm z v s c d)
    (primitiveTerm_integrable v hv s hs c d hc) (cuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [primitiveTerm_shift z v s c d n hlevel hd,cuspFrequency_negative_period]

lemma primitiveTerm_fourier_integral (v : ℝ) (hv : 0 < v) (s freq : ℂ)
    (c d : O) (hc : c ≠ 0) :
    (∫ z : ℂ,primitiveTerm z v s c d*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        (eisEmbedding (symbol c d)*ShortDraftTrace.breveE (freq*eisEmbedding d/eisEmbedding c)) := by
  simp_rw [primitiveTerm_eq_shiftedHeightKernel _ v hv s c d hc,mul_assoc]
  rw [integral_const_mul,integral_const_mul,traceIntegral_shiftedHeightKernel v hv s (eisEmbedding d/eisEmbedding c) freq]
  ring_nf

def arithmeticResidueSum (h c : O) : ℂ :=
  ∑' r : AdmissibleResidue c,eisEmbedding (symbol c (denominatorRep c r.1))*
    ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding (denominatorRep c r.1)/eisEmbedding c)

lemma arithmeticResidueSum_finite (h c : O) (hc : c ≠ 0) :
    letI : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
    arithmeticResidueSum h c = ∑ r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c r.1))*
      ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding (denominatorRep c r.1)/eisEmbedding c) := by
  let : Fintype (AdmissibleResidue c) := @Fintype.ofFinite _ (finite_admissibleResidue c hc)
  exact tsum_fintype _

lemma denominator_integral_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re)
    (h : O) (c : LevelLower) (hc : c.1 ≠ 0) :
    (∑' d : AdmissibleDenominator c.1,primitiveRowIntegral v s (cuspFrequency h) c.1 d.1)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        ((‖eisEmbedding c.1‖^2:ℝ):ℂ)^(-s)*arithmeticResidueSum h c.1 := by
  have hsum : Summable (fun d : AdmissibleDenominator c.1 =>
      primitiveRowIntegral v s (cuspFrequency h) c.1 d.1) :=
    (hasSum_primitiveRowIntegrals v hv s (cuspFrequency h) hs).summable.sigma_factor c
  rw [denominator_sum_residues c.1 hc
    (fun d : O => primitiveRowIntegral v s (cuspFrequency h) c.1 d) hsum]
  calc
    _ = ∑' r : AdmissibleResidue c.1, ∫ z : ℂ,
        primitiveTerm z v s c.1 (denominatorRep c.1 r.1)*
          ShortDraftTrace.breveE (-cuspFrequency h*z) := by
      apply tsum_congr
      intro r
      exact primitiveRowIntegral_sum_translate v hv s (by linarith) h c.1
        (denominatorRep c.1 r.1) hc c.2 r.2.2
    _ = _ := by
      simp_rw [primitiveTerm_fourier_integral v hv s (cuspFrequency h) c.1 _ hc]
      exact tsum_mul_left

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Matrix

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

instance : DiscreteTopology periodLattice := by unfold periodLattice; infer_instance
instance : IsZLattice ℝ periodLattice := by unfold periodLattice; infer_instance

lemma summable_embedding_rpow (k : ℝ) (hk : k < -2) :
    Summable (fun n : O => ‖eisEmbedding n‖^k) := by
  have hrank : Module.finrank ℤ periodLattice=2 := by
    rw [ZLattice.rank ℝ periodLattice,Complex.finrank_real_complex]
  have hs := ZLattice.summable_norm_rpow periodLattice k (by rw [hrank]; norm_num; exact hk)
  have hcomp := periodEquiv.summable_iff.mpr hs
  have hscale := hcomp.mul_left (((3:ℝ)^k)⁻¹)
  apply hscale.congr
  intro n
  change ((3:ℝ)^k)⁻¹*‖(3:ℂ)*eisEmbedding n‖^k=‖eisEmbedding n‖^k
  rw [norm_mul,show ‖(3:ℂ)‖=(3:ℝ) by norm_num,
    Real.mul_rpow (by norm_num) (norm_nonneg _)]
  rw [← mul_assoc,inv_mul_cancel₀ (Real.rpow_pos_of_pos (by norm_num) k).ne',one_mul]

lemma norm_row_symbol (c d : O) (hc : (3:O) ∣ c) (hd : denominatorCondition c d) :
    ‖eisEmbedding (symbol c d)‖=1 := by
  let r : PrimitiveRow := ⟨![c,d],hd.1,hc,hd.2⟩
  let x := primitiveRowEquiv.symm r
  have heq : (cosetCharacter x)⁻¹=eisEmbedding (symbol c d) := by
    rw [inverse_cosetCharacter_eq_row_symbol]
    change eisEmbedding (symbol (cosetRow (primitiveRowEquiv.symm r) 0)
      (cosetRow (primitiveRowEquiv.symm r) 1))=eisEmbedding (symbol c d)
    rw [primitiveRowEquiv_symm_row r]
    rfl
  rw [← heq,norm_inv,norm_cosetCharacter,inv_one]

lemma norm_arithmeticResidueSum_le (h c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    ‖arithmeticResidueSum h c‖ ≤ 9*‖eisEmbedding c‖^2 := by
  let : Finite (DenominatorResidue c) := finite_quotient_span (mul_ne_zero (by norm_num) hc)
  let : Fintype (DenominatorResidue c) := Fintype.ofFinite _
  let : Fintype (AdmissibleResidue c) := Fintype.ofFinite _
  have hcard : (Fintype.card (DenominatorResidue c):ℝ)=9*‖eisEmbedding c‖^2 := by
    have hh := eisEmbedding_norm_sq_eq_absNorm_span (3*c)
    simp only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] at hh
    rw [← hh,map_mul,map_ofNat,norm_mul,mul_pow]
    norm_num
  rw [arithmeticResidueSum,tsum_fintype]
  calc
    _ ≤ ∑ r : AdmissibleResidue c, ‖eisEmbedding (symbol c (denominatorRep c r.1))*
        ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding (denominatorRep c r.1)/eisEmbedding c)‖ :=
      norm_sum_le _ _
    _ = (Fintype.card (AdmissibleResidue c):ℝ) := by
      have hr (r : AdmissibleResidue c) :
          ‖eisEmbedding (symbol c (denominatorRep c r.1))‖=1 :=
        norm_row_symbol c (denominatorRep c r.1) hlevel r.2
      simp only [norm_mul,hr,breveE_norm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    _ ≤ (Fintype.card (DenominatorResidue c):ℝ) := by
      exact_mod_cast Fintype.card_subtype_le (fun r => denominatorCondition c (denominatorRep c r))
    _ = _ := hcard

def arithmeticDirichletTerm (s : ℂ) (h : O) (c : LevelLower) : ℂ :=
  if c.1=0 then 0 else ((‖eisEmbedding c.1‖^2:ℝ):ℂ)^(-s)*arithmeticResidueSum h c.1

lemma norm_arithmeticDirichletTerm_le (s : ℂ) (h : O) (c : LevelLower) :
    ‖arithmeticDirichletTerm s h c‖ ≤ 9*‖eisEmbedding c.1‖^(2-2*s.re) := by
  unfold arithmeticDirichletTerm
  split_ifs with hc
  · simp only [norm_zero]
    positivity
  · have hn : 0 < ‖eisEmbedding c.1‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn)]
    change (‖eisEmbedding c.1‖^2)^(-s.re)*‖arithmeticResidueSum h c.1‖ ≤ _
    calc
      _ ≤ (‖eisEmbedding c.1‖^2)^(-s.re)*(9*‖eisEmbedding c.1‖^2) :=
        mul_le_mul_of_nonneg_left (norm_arithmeticResidueSum_le h c.1 hc c.2) (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast_mul hn.le 2 (-s.re)]
        rw [show 2-2*s.re=2+2*(-s.re) by ring,Real.rpow_add hn]
        norm_num only [Nat.cast_ofNat,Real.rpow_two]
        ring

theorem arithmeticDirichletTerm_summable_norm (s : ℂ) (hs : 2 < s.re) (h : O) :
    Summable (fun c : LevelLower => ‖arithmeticDirichletTerm s h c‖) := by
  have hbase := (summable_embedding_rpow (2-2*s.re) (by linarith)).subtype
    (fun c : O => (3:O) ∣ c)
  exact (hbase.mul_left 9).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_arithmeticDirichletTerm_le s h)

def arithmeticDirichletSeries (s : ℂ) (h : O) : ℂ :=
  ∑' c : LevelLower,arithmeticDirichletTerm s h c

def scatteringCoefficient (s : ℂ) (h : O) : ℂ :=
  arithmeticDirichletSeries s h/((9*Real.sqrt 3/2:ℝ):ℂ)

end

open MeasureTheory Set Filter
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma zero_lower_integral (v : ℝ) (s : ℂ) (h : O) :
    (∑' d : AdmissibleDenominator 0,primitiveRowIntegral v s (cuspFrequency h) 0 d.1)=
      (v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0) := by
  let d0 : AdmissibleDenominator 0 := ⟨1,isCoprime_one_right,by simp⟩
  rw [tsum_eq_single d0]
  · simp only [d0,primitiveRowIntegral,primitiveTerm,map_zero,map_one,zero_mul,zero_add,
      norm_one,norm_zero,one_pow,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,
      div_one,symbol_one,map_one]
    rw [integral_const_mul,integral_cusp_character,one_mul]
  · intro d hd
    exact False.elim (hd (Subtype.ext (denominator_zero_unique d)))

lemma integral_upperEisenstein_arithmetic (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      (v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0)+
        ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*arithmeticDirichletSeries s h := by
  let c0 : LevelLower := ⟨0,dvd_zero _⟩
  let F (c : LevelLower) := ∑' d : AdmissibleDenominator c.1,
    primitiveRowIntegral v s (cuspFrequency h) c.1 d.1
  have hsum := hasSum_primitiveRowIntegrals v hv s (cuspFrequency h) hs
  have hF : Summable F := hsum.summable.sigma
  have hzero : F c0=(v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0) :=
    zero_lower_integral v s h
  calc
    _ = ∑' c : LevelLower,F c := hsum.tsum_eq.symm.trans hsum.summable.tsum_sigma
    _ = F c0+∑' c : LevelLower,if c=c0 then 0 else F c := hF.tsum_eq_add_tsum_ite c0
    _ = _ := by
      rw [hzero]
      congr 1
      rw [arithmeticDirichletSeries,← tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : c.1=0
      · have heq : c=c0 := Subtype.ext hc
        simp only [heq,ite_true,arithmeticDirichletTerm,c0,mul_zero]
      · have heq : c ≠ c0 := fun heq => hc (congrArg Subtype.val heq)
        rw [ite_eq_right heq]
        change (∑' d : AdmissibleDenominator c.1,
          primitiveRowIntegral v s (cuspFrequency h) c.1 d.1)=_
        rw [denominator_integral_formula v hv s hs h c hc]
        simp only [arithmeticDirichletTerm,ite_eq_right hc]
        ring

def eisensteinFourierCoefficient (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) : ℂ :=
  (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-cuspFrequency h*z))/
    ((9*Real.sqrt 3/2:ℝ):ℂ)

theorem eisensteinFourierCoefficient_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    eisensteinFourierCoefficient v hv s h=(if h=0 then (v:ℂ)^s else 0)+
      (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h := by
  rw [eisensteinFourierCoefficient,integral_upperEisenstein_arithmetic v hv s hs h,scatteringCoefficient]
  have hvol : ((9*Real.sqrt 3/2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  split_ifs <;> field_simp ; ring

theorem eisensteinConstantCoefficient_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    eisensteinFourierCoefficient v hv s 0=(v:ℂ)^s+
      (v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0 := by
  rw [eisensteinFourierCoefficient_formula v hv s hs 0]
  simp only [ite_true,cuspFrequency,map_zero,zero_div,zero_mul]
  rw [sourceFourierKernel_zero s (by linarith)]

theorem eisensteinFourierCoefficient_bessel (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re)
    (h : O) (hh : h ≠ 0) :
    eisensteinFourierCoefficient v hv s h=
      (v:ℂ)^(2-s)*
        ((2*Real.pi:ℂ)/Complex.Gamma s *
          (2*Real.pi*‖cuspFrequency h*v‖:ℂ)^(s-1)*
          schlafliBesselK (s-1) (4*Real.pi*‖cuspFrequency h*v‖))*
        scatteringCoefficient s h := by
  rw [eisensteinFourierCoefficient_formula v hv s hs h,ite_eq_right hh,zero_add]
  rw [sourceFourierKernel_bessel s (cuspFrequency h*v) (by linarith)
    (mul_ne_zero (cuspFrequency_ne_zero h hh) (Complex.ofReal_ne_zero.mpr hv.ne'))]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0127

/-! Original module: OAI.NumberTheory.DirichletL.Fourier.TupleWeights
Source SHA256: 3bf8c7fdf4ede391645c6244f113aa752c8b38831a843869dcc03afa1619840b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0128



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
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
namespace JointLogSeparation

theorem finite_triple_bounded_integral {α : Type*} (s : Finset α)
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (F : α → Frequency → ℂ)
    (hF : ∀ i ∈ s, Continuous (F i)) (M : α → ℝ)
    (hM : ∀ i ∈ s, ∀ q, ‖F i q‖ ≤ M i) :
    (∑ i ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) * F i (t₁,t₂,t₃)) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) * (∑ i ∈ s, F i (t₁,t₂,t₃)) := by
  have hc : Continuous (fun q => ∑ i ∈ s, F i q) := continuous_finsetSum _ hF
  have hb (q : Frequency) : ‖∑ i ∈ s, F i q‖ ≤ ∑ i ∈ s, M i :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => hM i hi q))
  have hi (i : α) (hi : i ∈ s) := tripleCoefficient_bounded_integrable b₁ b₂ b₃ (F i) (hF i hi) (M i) (hM i hi)
  have hs := tripleCoefficient_bounded_integrable b₁ b₂ b₃ (fun q => ∑ i ∈ s, F i q) hc _ hb
  calc
    _ = ∑ i ∈ s, ∫ q : Frequency, tripleCoefficient b₁ b₂ b₃ q * F i q := by
      apply Finset.sum_congr rfl
      intro i hmem
      exact nested_eq_integral _ (hi i hmem)
        (tripleCoefficient_slice_integrable b₁ b₂ b₃ (F i) (hF i hmem) (M i) (hM i hmem))
    _ = ∫ q : Frequency, ∑ i ∈ s, tripleCoefficient b₁ b₂ b₃ q * F i q :=
      (integral_finsetSum s hi).symm
    _ = ∫ q : Frequency, tripleCoefficient b₁ b₂ b₃ q * (∑ i ∈ s, F i q) := by
      simp only [Finset.mul_sum]
    _ = _ := (nested_eq_integral _ hs
      (tripleCoefficient_slice_integrable b₁ b₂ b₃ (fun q => ∑ i ∈ s, F i q) hc _ hb)).symm

end JointLogSeparation

namespace SecondPassIntegration

section
open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)
open FourierBridge (logPhase)

def tupleOuterWeight (V : Fin 7 → ℝ → ℂ) (w : OldTuple → ℂ)
    (z ud ue uv kap : OldTuple → ℝ) (q : Frequency) (x : OldTuple) : ℂ :=
  w x * outerWindow V (z x) (ud x) (ue x) (uv x) (kap x) *
    logPhase (q.1 + q.2.1) (z x) * logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)

lemma tupleOuterWeight_continuous (V : Fin 7 → ℝ → ℂ) (w : OldTuple → ℂ)
    (z ud ue uv kap : OldTuple → ℝ) (x : OldTuple) :
    Continuous (fun q => tupleOuterWeight V w z ud ue uv kap q x) := by
  have h₁ : Continuous (fun q : Frequency => logPhase (q.1 + q.2.1) (z x)) :=
    (FourierBridge.logPhase_continuous_left (z x)).comp
    (continuous_fst.add continuous_snd.fst)
  have h₂ : Continuous (fun q : Frequency => logPhase q.2.2 (kap x - ud x - 2 * ue x - 2 * uv x)) :=
    (FourierBridge.logPhase_continuous_left (kap x - ud x - 2 * ue x - 2 * uv x)).comp
    continuous_snd.snd
  unfold tupleOuterWeight
  fun_prop

lemma tupleOuterWeight_norm (V : Fin 7 → ℝ → ℂ) (w : OldTuple → ℂ)
    (z ud ue uv kap : OldTuple → ℝ) (q : Frequency) (x : OldTuple) :
    ‖tupleOuterWeight V w z ud ue uv kap q x‖ =
      ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ := by
  simp only [tupleOuterWeight, norm_mul, FourierBridge.logPhase_norm, mul_one]

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def tupleSourceSum (s : Finset OldTuple) (w : OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ R : ℝ) : ℂ :=
  ∑ x ∈ s, w x * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (label x)
    (newRow x) (-newRow x) A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R

theorem tupleSource_eq_integratedSecondMode
    (s : Finset OldTuple) (w : OldTuple → ℂ) (label : OldTuple → O)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (A₁ A₂ W b : 𝓢(ℝ, ℂ))
    (V : Fin 7 → ℝ → ℂ) (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ R : ℝ)
    (hsep : ∀ x ∈ s,
      postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
        A₁ A₂ W V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂ R =
      separatedPostCommon p hp hcop hg F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
        A₁ A₂ b V (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂) :
    tupleSourceSum p hp hcop hg s w label F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R =
      integratedSecondMode p hp hcop hg (𝓕 A₁) (𝓕 A₂) b s
        (tupleOuterWeight V w z ud ue uv kap) label F Ψ₁ Ψ₂ m (V 5) (V 6) X₁ X₂ := by
  let Q : OldTuple → Frequency → ℂ := fun x q =>
    tupleOuterWeight V w z ud ue uv kap q x *
      star (fixedChildRow p hp hcop hg F Ψ₁ m
        (fixedSecondTest p (V 5) X₁ q.1 q.2.2 true) (label x) (newRow x)) *
      fixedChildRow p hp hcop hg F Ψ₂ m
        (fixedSecondTest p (V 6) X₂ q.2.1 q.2.2 false) (label x) (-newRow x)
  let M : OldTuple → ℝ := fun x =>
    (‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖) *
      rowMagnitude p hp hcop hg F Ψ₁ m (label x) (newRow x) (V 5) X₁ true *
      rowMagnitude p hp hcop hg F Ψ₂ m (label x) (-newRow x) (V 6) X₂ false
  have hc (x : OldTuple) : Continuous (Q x) := by
    have hw := tupleOuterWeight_continuous V w z ud ue uv kap x
    have h₁ := fixedRow_continuous p hp hcop hg F Ψ₁ m (label x) (newRow x) (V 5) X₁ true
      (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
    have h₂ := fixedRow_continuous p hp hcop hg F Ψ₂ m (label x) (-newRow x) (V 6) X₂ false
      (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
    exact (hw.mul h₁.star).mul h₂
  have hbound (x : OldTuple) (q : Frequency) : ‖Q x q‖ ≤ M x := by
    dsimp only [Q, M]
    rw [norm_mul, norm_mul, norm_star, tupleOuterWeight_norm]
    have h₁ := fixedRow_norm_le p hp hcop hg F Ψ₁ m (label x) (newRow x) (V 5) X₁ q.1 q.2.2 true
    have h₂ := fixedRow_norm_le p hp hcop hg F Ψ₂ m (label x) (-newRow x) (V 6) X₂ q.2.1 q.2.2 false
    have hn₁ := rowMagnitude_nonneg p hp hcop hg F Ψ₁ m (label x) (newRow x) (V 5) X₁ true
    have hn₂ := rowMagnitude_nonneg p hp hcop hg F Ψ₂ m (label x) (-newRow x) (V 6) X₂ false
    gcongr
  calc
    _ = ∑ x ∈ s, ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * Q x (t₁,t₂,t₃) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hsep x hx]
      unfold separatedPostCommon
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      dsimp [tripleCoefficient, Q, tupleOuterWeight]
      ring
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃) * (∑ x ∈ s, Q x (t₁,t₂,t₃)) :=
      finite_triple_bounded_integral s (𝓕 A₁) (𝓕 A₂) b Q (fun x _ => hc x) M (fun x _ => hbound x)
    _ = _ := rfl

end

open ActualEisensteinCubic SecondPassArithmetic JointLogSeparation
open SecondPassFiber (OldTuple newLabel newRow Valid)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem tupleSource_uniform_transfer (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ, ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ j, 0 ≤ M j) (hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j) (A J : ℕ) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∃ Cₛ : ℝ, 0 ≤ Cₛ ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ t₁ t₂ t₃ : ℝ, (1 + R)^A * ‖(𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃‖ ≤
        Cₛ * FirstPassCubeLabels.firstLogDensity J t₁ *
          FirstPassCubeLabels.firstLogDensity J t₂ * FirstPassCubeLabels.firstLogDensity J t₃) ∧
      ∀ (s : Finset OldTuple) (T : Finset (Ideal O × O)) (b0 : Ideal O)
        (w : OldTuple → ℂ) (B lengthScale : ℝ) (label : OldTuple → O)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : OldTuple → ℝ) (X₁ X₂ : ℝ),
        b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
        (∀ x ∈ s, (newLabel x, newRow x) ∈ T) →
        (∀ z ∈ T, z.1 ≠ ⊥) → (∀ z ∈ T, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
        (∀ x ∈ s, ‖w x‖ * ‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        (∀ x ∈ s, Ideal.span {label x} = newLabel x) →
        ‖tupleSourceSum p hp hcop hg s w label F Ψ₁ Ψ₂ m A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
          (B * Cₐ * (lengthScale * Ideal.absNorm b0)^ε) *
          (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
            ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b (t₁,t₂,t₃)‖ *
              childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T (V 5) (V 6) X₁ X₂ (t₁,t₂,t₃)) := by
  obtain ⟨Cₐ, hCₐ, htrans⟩ := integrated_fixed_second_mode_transfer p hp hcop hg ε hε
  obtain ⟨Cₛ, hCₛ, hsep⟩ := postCommonSmoothPair_uniform_fixed_tests p hp hcop hg A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ, hCₐ, Cₛ, hCₛ, ?_⟩
  intro R hR
  obtain ⟨b, hpoint, hid⟩ := hsep R hR
  refine ⟨b, hpoint, ?_⟩
  intro s T b0 w B lengthScale label F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hb0 hB hL hv hm ht hn hw hl
  have hsource := tupleSource_eq_integratedSecondMode p hp hcop hg s w label F Ψ₁ Ψ₂ m A₁ A₂ W b
    V z ud ue uv kap X₁ X₂ R (fun x hx => hid F Ψ₁ Ψ₂ m (label x) (newRow x) (-newRow x)
      (z x) (ud x) (ue x) (uv x) (kap x) X₁ X₂)
  rw [hsource]
  apply htrans s T b0 (tupleOuterWeight V w z ud ue uv kap) B lengthScale label F Ψ₁ Ψ₂ m
    (V 5) (V 6) X₁ X₂ (𝓕 A₁) (𝓕 A₂) b hb0 hB hL hv hm ht hn
  · intro q x hx
    rw [tupleOuterWeight_norm]
    exact hw x hx
  · intro x hx
    exact tupleOuterWeight_continuous V w z ud ue uv kap x
  · exact hl

end SecondPassIntegration

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
namespace JointLogSeparation

def halfNormalizationMultiplier (U : ℝ → ℂ) (s : ℝ) : ℂ :=
  U s * (Real.exp (-s / 2) : ℂ)

lemma halfNormalization_temperate (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) : (halfNormalizationMultiplier U).HasTemperateGrowth := by
  apply (hUc.mul_right : HasCompactSupport (halfNormalizationMultiplier U)).hasTemperateGrowth
  change ContDiff ℝ ∞ (fun s : ℝ => U s * (Real.exp (-s / 2) : ℂ))
  have he : ContDiff ℝ ∞ (fun s : ℝ => Real.exp (-s / 2)) := by fun_prop
  exact hUs.mul (Complex.ofRealCLM.contDiff.comp he)

def halfNormalizationCLM (U : ℝ → ℂ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (halfNormalizationMultiplier U)).restrictScalars ℝ

lemma halfNormalizationCLM_apply (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (s : ℝ) :
    halfNormalizationCLM U g s = U s * (Real.exp (-s / 2) : ℂ) * g s := by
  exact SchwartzMap.smulLeftCLM_apply_apply (halfNormalization_temperate U hUc hUs) g s

lemma sqrt_exp_half (s : ℝ) : Real.sqrt (Real.exp s) = Real.exp (s / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos s).le (Real.exp_pos (s / 2)).le).mpr
  rw [← Real.exp_add]
  congr 1
  ring

theorem halfNormalization_exact (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1) (s : ℝ) :
    halfNormalizationCLM U g s = g s / (Real.sqrt (Real.exp s) : ℂ) := by
  rw [halfNormalizationCLM_apply U hUc hUs]
  by_cases hg : g s = 0
  · simp [hg]
  rw [hU s hg, one_mul, sqrt_exp_half]
  have he : (Real.exp (-s / 2) : ℂ) = ((Real.exp (s / 2) : ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv, ← Real.exp_neg]
    congr 2
    ring
  rw [he]
  exact (div_eq_inv_mul (g s) (Real.exp (s / 2) : ℂ)).symm

lemma halfNormalization_twist (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    halfNormalizationCLM U (frequencyTwist g t) = frequencyTwist (halfNormalizationCLM U g) t := by
  ext s
  simp only [halfNormalizationCLM_apply U hUc hUs, frequencyTwist_apply]
  ring

theorem halfNormalization_source_control (U : ℝ → ℂ) (S : Finset (ℕ × ℕ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ g : 𝓢(ℝ, ℂ),
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (halfNormalizationCLM U g) ≤
        C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) g :=
  EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control (halfNormalizationCLM U) S

end JointLogSeparation

namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels

lemma sqrtProductNorm {ι : Type*} (p : ι → O) (S : Finset ι) :
    Real.sqrt (primeProductNorm p S) = ‖ConcreteTraceCRT.eisEmbedding (∏ i ∈ S, p i)‖ := by
  simp only [primeProductNorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem columnLog_union_scale {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N)
    (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀) :
    columnLog p X (V ∪ N) =
      Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N := by
  have hV := primeProductNorm_pos p hp V
  have hN := primeProductNorm_pos p hp N
  unfold columnLog
  rw [primeProductNorm_union p V N hVN, ← Real.log_mul
    (ne_of_gt (div_pos (mul_pos hV hX₀) hX)) (ne_of_gt (div_pos hN hX₀))]
  congr 1
  field_simp

lemma halfNormalization_at_ratio (U : ℝ → ℂ) (hUc : HasCompactSupport U)
    (hUs : ContDiff ℝ ∞ U) (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1)
    (N X : ℝ) (hN : 0 < N) (hX : 0 < X) :
    halfNormalizationCLM U g (Real.log (N / X)) / (Real.sqrt X : ℂ) =
      g (Real.log (N / X)) / (Real.sqrt N : ℂ) := by
  rw [halfNormalization_exact U hUc hUs g hU, Real.exp_log (div_pos hN hX), div_div]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (div_pos hN hX).le]
  congr 2
  field_simp

theorem normalizedColumn_union_test {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N)
    (X X₀ : ℝ) (hX : 0 < X) (hX₀ : 0 < X₀)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g : 𝓢(ℝ, ℂ)) (hU : ∀ s, g s ≠ 0 → U s = 1) :
    normalizedColumn p (fun S => g (columnLog p X S)) (V ∪ N) =
      halfNormalizationCLM U g
        (Real.log (primeProductNorm p V * X₀ / X) + columnLog p X₀ N) / (Real.sqrt X : ℂ) := by
  rw [← columnLog_union_scale p hp V N hVN X X₀ hX hX₀]
  change g (Real.log (primeProductNorm p (V ∪ N) / X)) /
    (‖ConcreteTraceCRT.eisEmbedding (∏ i ∈ V ∪ N, p i)‖ : ℂ) = _
  rw [← sqrtProductNorm]
  exact (halfNormalization_at_ratio U hUc hUs g hU (primeProductNorm p (V ∪ N)) X
    (primeProductNorm_pos p hp _) hX).symm

end SecondPassIntegration
end

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

lemma lambdaIdeal_maximal : (Ideal.span {lambda} : Ideal O).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible PrimaryIdealUnitReindex.lambda_prime_actual.irreducible

lemma twoIdeal_maximal : (Ideal.span {(2 : O)} : Ideal O).IsMaximal := by
  simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal

lemma twoIdeal_characteristic : ringChar (O ⧸ Ideal.span {(2 : O)}) = 2 := by
  rw [← Ideal.span_singleton_neg (2 : O)]
  exact cubicTwoIdeal_residue_char

theorem supported_span_iff (z : O) :
    Supported (Ideal.span {z}) ↔ ¬lambda ∣ z ∧ ¬(2 : O) ∣ z := by
  constructor
  · intro h
    constructor
    · intro hz
      have hm : (Ideal.span {lambda} : Ideal O) ∈
          UniqueFactorizationMonoid.normalizedFactors (Ideal.span {z}) := by
        apply (Ideal.mem_normalizedFactors_iff h.1).mpr
        exact ⟨lambdaIdeal_maximal.isPrime,
          (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hz)⟩
      exact (h.2 _ hm).1 (Ideal.subset_span (by simp))
    · intro hz
      have hm : (Ideal.span {(2 : O)} : Ideal O) ∈
          UniqueFactorizationMonoid.normalizedFactors (Ideal.span {z}) := by
        apply (Ideal.mem_normalizedFactors_iff h.1).mpr
        exact ⟨twoIdeal_maximal.isPrime,
          (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_span_singleton.mpr hz)⟩
      exact (h.2 _ hm).2 twoIdeal_characteristic
  · rintro ⟨hLam, htwo⟩
    have hz : z ≠ 0 := fun heq => hLam (heq ▸ dvd_zero lambda)
    refine ⟨Ideal.span_singleton_eq_bot.not.mpr hz, ?_⟩
    intro P hP
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hzP : z ∈ P := ((Ideal.mem_normalizedFactors_iff
      (Ideal.span_singleton_eq_bot.not.mpr hz)).mp hP).2 (Ideal.subset_span (by simp))
    constructor
    · intro hlambdaP
      have heq := maximal_ideal_eq_span_of_mem P inferInstance lambda lambdaIdeal_maximal hlambdaP
      rw [heq] at hzP
      exact hLam (Ideal.mem_span_singleton.mp hzP)
    · intro hchar
      have htwoP : (2 : O) ∈ P := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        have hzero : (2 : O ⧸ P) = 0 := (ringChar.spec (O ⧸ P) 2).mpr (by rw [hchar])
        simpa only [map_ofNat] using hzero
      have heq := maximal_ideal_eq_span_of_mem P inferInstance (2 : O) twoIdeal_maximal htwoP
      rw [heq] at hzP
      exact htwo (Ideal.mem_span_singleton.mp hzP)

def badPrime (i : Bool) : Ideal O := if i then Ideal.span {(2 : O)} else Ideal.span {lambda}

instance badPrime_maximal (i : Bool) : (badPrime i).IsMaximal := by
  cases i
  · exact lambdaIdeal_maximal
  · exact twoIdeal_maximal

theorem badPrime_mask (z : O) :
    rowCoprimeMask badPrime Finset.univ z = if Supported (Ideal.span {z}) then 1 else 0 := by
  rw [supported_span_iff]
  simp only [rowCoprimeMask, Finset.mem_univ, true_and, Bool.exists_bool, badPrime,
    Bool.false_eq_true, ite_false, ite_true, Ideal.mem_span_singleton]
  by_cases hLam : lambda ∣ z <;> by_cases htwo : (2 : O) ∣ z <;> simp [hLam, htwo]

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator

theorem highKernelNorm_mono {M N K M' N' K' : ℝ}
    (hM : M ≤ M') (hN : N ≤ N') (hK : K' ≤ K) :
    highKernelNorm M N K ≤ highKernelNorm M' N' K' := by
  let r : highKernelRange M K → highKernelRange M' K' := fun I => ⟨I.val, by
    obtain ⟨hs, hn, hk⟩ := mem_highKernelRange.mp I.property
    exact mem_highKernelRange.mpr ⟨hs, hn.trans hM, hK.trans_lt hk⟩⟩
  have hr : Function.Injective r := fun I J h =>
    Subtype.ext (congrArg (fun I : highKernelRange M' K' => I.val) h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hr
    (rangeInclusion hN) (rangeInclusion_injective hN) (highKernelMatrix M' N' K')
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem highKernel_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖operator (fun i j => quadraticRow (cols j) (primaryGenerator (rows i)))‖ ^ 2 ≤
      highKernelNorm M N K := by
  let r : m → highKernelRange M K := fun i => ⟨rows i, hrows i⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (highKernelMatrix M N K)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2
theorem highKernel_quotient_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hdiv : ∀ j, D ∣ cols j) (M N K : ℝ)
    (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (fun i j =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)))‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
  apply highKernel_family_squared_norm_le rows (fun j => idealQuotient D (cols j)) hr
  · intro j k heq
    exact hc (idealQuotient_injective_on D (hdiv j) (hdiv k) heq)
  · exact hrows
  · intro j
    exact ⟨admissible_idealQuotient (hcols j).1 (hdiv j),
      idealQuotient_norm_le hD (hdiv j) N (hcols j).2⟩

theorem highKernel_quotientMatrix_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols) (M N K : ℝ)
    (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (quotientMatrix D rows cols)‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
  let S : Finset n := Finset.univ.filter (fun j => D ∣ cols j)
  let A : Matrix m S ℂ := fun i j =>
    quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i))
  have hnorm : ‖FiniteSieveOperator.operator A‖ ^ 2 ≤
      highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K := by
    apply highKernel_quotient_family_squared_norm_le D hD rows (fun j : S => cols j.val) hr
      (hc.comp Subtype.val_injective)
    · intro j
      exact (Finset.mem_filter.mp j.property).2
    · exact hrows
    · intro j
      exact hcols j.val
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _ (highKernelNorm_nonneg _ _ _)
  intro a
  have hinner (i : m) : (∑ j, quotientMatrix D rows cols i j * a j) =
      ∑ j : S, A i j * a j.val := by
    change (∑ j, (if D ∣ cols j then
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) else 0) * a j) =
      ∑ j : S, quadraticRow (idealQuotient D (cols j.val)) (primaryGenerator (rows i)) * a j.val
    rw [Finset.sum_coe_sort S (fun j : n =>
      quadraticRow (idealQuotient D (cols j)) (primaryGenerator (rows i)) * a j)]
    simp only [S, Finset.sum_filter, ite_mul, zero_mul]
  simp_rw [hinner]
  have henergy := FiniteSieveOperator.energy_bound A (fun j : S => a j.val)
  apply henergy.trans
  calc
    _ ≤ highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K * ∑ j : S, ‖a j.val‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hnorm (by positivity)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (highKernelNorm_nonneg _ _ _)
      rw [Finset.sum_coe_sort S (fun j : n => ‖a j‖ ^ 2)]
      exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator

def totalQuotient (D I : Ideal O) : Ideal O := if D ∣ I then idealQuotient D I else 1

theorem totalQuotient_ne_zero (D I : Ideal O) (hI : Admissible I) : totalQuotient D I ≠ 0 := by
  by_cases h : D ∣ I
  · simpa only [totalQuotient, ite_eq_left h] using (admissible_idealQuotient hI h).1
  · simp [totalQuotient, h]

theorem totalQuotient_norm_le (D I : Ideal O) (hI : Admissible I)
    (N : ℝ) (hN : 1 ≤ N) (hIN : (Ideal.absNorm I : ℝ) ≤ N) :
    (Ideal.absNorm (totalQuotient D I) : ℝ) ≤ N := by
  by_cases h : D ∣ I
  · rw [totalQuotient, ite_eq_left h]
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    exact (Nat.cast_le.mpr (Nat.le_of_dvd hn (map_dvd Ideal.absNorm (idealQuotient_dvd h)))).trans hIN
  · simpa only [totalQuotient, ite_eq_right h, map_one, Nat.cast_one] using hN

theorem gcd_eq_iff_quotient_coprime (D I J : Ideal O) (hD : D ≠ 0)
    (hDI : D ∣ I) (hDJ : D ∣ J) :
    gcd I J = D ↔ IsCoprime (idealQuotient D I) (idealQuotient D J) := by
  have he : gcd I J = D * gcd (idealQuotient D I) (idealQuotient D J) := by
    calc
      gcd I J = gcd (D * idealQuotient D I) (D * idealQuotient D J) := by
        rw [idealQuotient_mul hDI, idealQuotient_mul hDJ]
      _ = _ := by rw [_root_.gcd_mul_left, normalize_eq]
  rw [he, Ideal.isCoprime_iff_gcd]
  constructor
  · intro h
    exact mul_left_cancel₀ hD (h.trans (mul_one D).symm)
  · intro h
    rw [h, mul_one]

def gcdTerm {m n : Type*} (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (i : m) (j k : n) : ℂ :=
  if gcd (cols j) (cols k) = D then
    star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
      (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) else 0

def gcdBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, gcdTerm D rows cols a i j k

theorem gcdTerm_eq_quotient {m n : Type*}
    (D : Ideal O) (hD : D ≠ 0) (rows : m → Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (i : m) (j k : n) :
    gcdTerm D rows cols a i j k =
      (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow D (primaryGenerator (rows i))) *
      (if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) *
          (quotientMatrix D rows cols i k * (if D ∣ cols k then a k else 0)) else 0) := by
  by_cases hj : D ∣ cols j
  · by_cases hk : D ∣ cols k
    · simp only [gcdTerm, totalQuotient, quotientMatrix, ite_eq_left hj, ite_eq_left hk]
      rw [← gcd_eq_iff_quotient_coprime D (cols j) (cols k) hD hj hk]
      by_cases hg : gcd (cols j) (cols k) = D
      · rw [ite_eq_left hg, ite_eq_left hg, quadraticRow_divisor_factor _ D (hcols j) hj,
          quadraticRow_divisor_factor _ D (hcols k) hk]
        simp only [star_mul]
        ring
      · simp only [ite_eq_right hg, mul_zero]
    · have hg : gcd (cols j) (cols k) ≠ D := by
        intro he
        exact hk (he ▸ gcd_dvd_right (cols j) (cols k))
      simp only [gcdTerm, ite_eq_right hg]
      simp [quotientMatrix, hk]
  · have hg : gcd (cols j) (cols k) ≠ D := by
      intro he
      exact hj (he ▸ gcd_dvd_left (cols j) (cols k))
    simp only [gcdTerm, ite_eq_right hg]
    simp [quotientMatrix, hj]

theorem highKernel_gcdBlock_bound {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (ε : ℝ) (hε : 0 < ε) (D : Ideal O) (hD : D ≠ 0)
    (rows : m → Ideal O) (cols : n → Ideal O)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hN : 1 ≤ N) (hrows : ∀ i, rows i ∈ highKernelRange M K)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ) :
    ‖gcdBlock D rows cols a‖ ≤ highKernelNorm M (N / (Ideal.absNorm D : ℝ)) K *
      (supportConstant ε hε * N ^ ε) * ∑ j, ‖if D ∣ cols j then a j else 0‖ ^ 2 := by
  let w : m → ℂ := fun i =>
    star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow D (primaryGenerator (rows i))
  have hw (i : m) : ‖w i‖ ≤ 1 := by
    dsimp only [w]
    rw [norm_mul, norm_star]
    exact (mul_le_mul (quadraticRow_norm_le_one D _) (quadraticRow_norm_le_one D _)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have he : gcdBlock D rows cols a = ∑ i, w i * ∑ j, ∑ k,
      if IsCoprime (totalQuotient D (cols j)) (totalQuotient D (cols k)) then
        star (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) *
          (quotientMatrix D rows cols i k * (if D ∣ cols k then a k else 0)) else 0 := by
    unfold gcdBlock
    simp_rw [gcdTerm_eq_quotient D hD rows cols (fun j => (hcols j).1) a]
    simp only [w, Finset.mul_sum]
  rw [he]
  have hb := ideal_coprime_gram_operator_bound ε hε (fun j => totalQuotient D (cols j))
    (fun j => totalQuotient_ne_zero D _ (hcols j).1) N (by linarith)
    (fun j => totalQuotient_norm_le D _ (hcols j).1 N hN (hcols j).2)
    (quotientMatrix D rows cols) (fun j => if D ∣ cols j then a j else 0) w 1 (by norm_num) hw
  simp only [one_mul] at hb
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (highKernel_quotientMatrix_squared_norm_le D hD rows cols hr hc M N K hrows hcols)
      (mul_nonneg (supportConstant_pos ε hε).le (Real.rpow_nonneg (by linarith) _)))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0128

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.GcdReduction
Source SHA256: 9193efbb9c345834908432791717b7f33cf9580a417acb76e184effc8610c0b3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0129


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
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator IdealCoprimeSieveOperator DivisorBlockCauchy

def gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) : Finset (Ideal O) :=
  Finset.univ.image (fun p : n × n => gcd (cols p.1) (cols p.2))

theorem mem_gcdPool {n : Type*} [Fintype n] (cols : n → Ideal O) (j k : n) :
    gcd (cols j) (cols k) ∈ gcdPool cols :=
  Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩

theorem gcdPool_ne_zero {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hcols : ∀ j, cols j ≠ 0) (D : Ideal O) (hD : D ∈ gcdPool cols) : D ≠ 0 := by
  obtain ⟨⟨j, k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  intro h
  have hd := gcd_dvd_left (cols j) (cols k)
  rw [h, zero_dvd_iff] at hd
  exact hcols j hd

theorem energy_eq_gcd_blocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) :
    ((∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i)) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ gcdPool cols, gcdBlock D rows cols a := by
  have hp (i : m) (j k : n) : (∑ D ∈ gcdPool cols, gcdTerm D rows cols a i j k) =
      star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
        (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) := by
    rw [Finset.sum_eq_single (gcd (cols j) (cols k))]
    · simp only [gcdTerm, ite_true]
    · intro D hD hne
      exact ite_eq_right (Ne.symm hne)
    · exact fun h => (h (mem_gcdPool cols j k)).elim
  have hi (i : m) : (∑ D ∈ gcdPool cols, ∑ j, ∑ k, gcdTerm D rows cols a i j k) =
      ∑ j, ∑ k, star (quadraticRow (cols j) (primaryGenerator (rows i)) * a j) *
        (quadraticRow (cols k) (primaryGenerator (rows i)) * a k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
