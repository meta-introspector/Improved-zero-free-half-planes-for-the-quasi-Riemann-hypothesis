  simp only [← integral_const_mul]
  rw [← integral_finsetSum s (fun k hk =>
    (full_density_mode_integrable g b₁ b₂ b₃ a₁ a₂ ak (y k)).const_mul (c k))]
  apply integral_congr_ae
  filter_upwards with p
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0464

/-! Original module: OAI.NumberTheory.DirichletL.Descent.DensityAssembly
Source SHA256: 84849740e88dd7401458fb19f09d648e8b869478567874a94f832bad14b47b2d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0465


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem integrable_density_mode {ι : Type*} [Fintype ι]
    (D : Frequency × (ι → ℝ) → ℂ) (hD : Integrable D) (a₁ a₂ ak y : ι → ℝ) :
    Integrable (fun z : Frequency × (ι → ℝ) => D z *
      pureProfileMode a₁ a₂ ak y z.1 z.2) := by
  have hc : Continuous (fun z : Frequency × (ι → ℝ) => pureProfileMode a₁ a₂ ak y z.1 z.2) := by
    unfold pureProfileMode logPhase
    fun_prop
  exact hD.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => (pureProfileMode_norm a₁ a₂ ak y z.1 z.2).le))

theorem density_finite_sum {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (D : Frequency × (ι → ℝ) → ℂ) (hD : Integrable D) (a₁ a₂ ak : ι → ℝ)
    (c : κ → ℂ) (y : κ → ι → ℝ) :
    (∑ k ∈ s,c k * ∫ z : Frequency × (ι → ℝ),D z*pureProfileMode a₁ a₂ ak (y k) z.1 z.2) =
    ∫ z : Frequency × (ι → ℝ),D z * ∑ k ∈ s,c k*pureProfileMode a₁ a₂ ak (y k) z.1 z.2 := by
  simp only [← integral_const_mul]
  rw [← integral_finsetSum s (fun k hk => (integrable_density_mode D hD a₁ a₂ ak (y k)).const_mul (c k))]
  apply integral_congr_ae
  filter_upwards with z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0465

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstFreshMeasure
Source SHA256: 8b34c7fff4e07c4443fdcd7059d9da7f41cc8a632c29427501adbc50e0a19f12
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0466



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory JointLogSeparation
noncomputable section

def firstRelativeLog (q s : Fin 9 → ℝ) (i : Fin 9) : ℝ := Real.log (q i/s i)

theorem first_fresh_kernel_common_measure
    (W₁ W₂ : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hs₁ : Function.support W₁ ⊆ Set.Icc lo hi) (hs₂ : Function.support W₂ ⊆ Set.Icc lo hi)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ,ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ s : Fin 9 → ℝ, (∀ i, 0 < s i) → ∀ K : ℝ, 0 < K → ∃ b₃ : 𝓢(ℝ,ℂ),
      (∀ (ω₁ ω₂ : ℝ → ℂ) (q : Fin 9 → ℝ), (∀ i, 0 < q i) →
        (W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) ≠ 0 → ω₁ (q 7/s 7) = 1) →
        (W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) ≠ 0 → ω₂ (q 8/s 8) = 1) →
        (ω₁ (q 7/s 7) ≠ 0 → ω₂ (q 8/s 8) ≠ 0 → ∀ i, V i (firstRelativeLog q s i) = 1) →
        firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
          (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
        (firstRootScale s:ℂ)⁻¹ * (ω₁ (q 7/s 7)*ω₂ (q 8/s 8)) *
          ∫ z : Frequency × (Fin 9 → ℝ),
            fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z *
            pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2) ∧
      Integrable (fun z : Frequency × (Fin 9 → ℝ) => tripleHeight J z.1*coordinateHeight J z.2*
        ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ∧
      (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^A *
        (∫ z : Frequency × (Fin 9 → ℝ), tripleHeight J z.1*coordinateHeight J z.2*
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hs⟩ := first_full_profile_common_measure
    W₁ W₂ lo hi hlo hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro s hspos K hK
  obtain ⟨b₃,he,hI,hB⟩ := hs (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))
    (div_pos (mul_pos hK (hspos 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (hspos 3) (hspos 4))
        (sq_pos_of_pos (hspos 5))) (hspos 7)) (hspos 8)))
  refine ⟨b₃,?_,hI,hB⟩
  intro ω₁ ω₂ q hq hω₁ hω₂ hcut
  by_cases hw₁ : ω₁ (q 7/s 7) = 0
  · have hh : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0 := by
      by_contra hn
      have := hω₁ hn
      simp only [hw₁,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 8/s 8) = 0
  · have hh : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0 := by
      by_contra hn
      have := hω₂ hn
      simp only [hw₂,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₂,mul_zero,zero_mul,zero_div]
  have hcut' := hcut hw₁ hw₂
  have hnom := firstNormProfile_nominal W₁ W₂ Φ (fun _ _ => 1) s q hspos hq K
  have hfull : firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) =
      ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
    rw [full_density_mode_fubini]
    rw [show firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) =
        firstPoissonProfile W₁ W₂ Φ V (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (firstRelativeLog q s) from by
      unfold firstRelativeLog
      rw [firstPoissonProfile_log W₁ W₂ Φ V _ _ (fun i => div_pos (hq i) (hspos i))]
      simp only [firstRelativeLog] at hcut'
      simp only [firstNormProfile,hcut',Finset.prod_const_one]]
    simpa only [pureProfileMode_height] using he (firstRelativeLog q s)
  have hm : firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
      (ω₁ (q 7/s 7)*ω₂ (q 8/s 8)) *
      firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
        (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q := by
    by_cases h1 : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0
    · simp only [firstNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0
    · simp only [firstNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  rw [hm,hnom,hfull]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0466

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstModeColumns
Source SHA256: 6da8473ad8fbe65cf6d381ead2050144c1b6eca88b8a3c01b82d7fa75aa2aa35
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0467



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FourierBridge JointLogSeparation
open MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def firstCoordinates (a : Fin 7 → ℝ) (x y : ℝ) : Fin 9 → ℝ :=
  ![a 0,a 1,a 2,a 3,a 4,a 5,a 6,x,y]

def firstOuterPhase (h : Fin 9 → ℝ) (a : Fin 7 → ℝ) : ℂ :=
  ∏ i : Fin 7, logPhase (h ⟨i.val, by omega⟩) (a i)

theorem first_mode_split (a : Fin 7 → ℝ) (x y : ℝ)
    (v : Frequency × (Fin 9 → ℝ)) :
    pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstCoordinates a x y) v.1 v.2 =
      firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2) a *
      logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2 7) x *
      logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope v.1 v.2 8) y := by
  rw [pureProfileMode_height]
  simp [Fin.prod_univ_succ,firstCoordinates,firstOuterPhase]
  ring

def firstColumnMode (negative : Bool) {ι : Type*} (C : Finset ι → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * if negative then star (logPhase t (y S)) else logPhase t (y S)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem threeGaussRowFactor_first_mode (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (y₁ y₂ : Finset ι → ℝ) (t₁ t₂ : ℝ) (d h : Eis) :
    threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂
      (firstColumnMode true C₁ y₁ t₁) (firstColumnMode false C₂ y₂ t₂) d h =
    logPhase t₁ (y₁ N) * logPhase t₂ (y₂ P) *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  simp only [threeGaussRowFactor,firstColumnMode,Bool.false_eq_true,ite_false,ite_true,
    star_mul,star_star]
  ring

theorem actual_first_mode_ideal_rows
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstCoordinates a (y₁ N) (y₂ P)) z.1 z.2 else 0) =
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a *
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg F
        (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
          (firstColumnMode true C₁ y₁ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)) d)
        (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
          (firstColumnMode false C₂ y₂ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)) d) h := by
  rw [mul_assoc, ← sum_threeGaussRowFactor_eq_ideal_rows p hp hinj hcop hg hc hpr F B hFB]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hd : Disjoint N P
  · simp only [hd,ite_true]
    rw [first_mode_split,threeGaussRowFactor_first_mode]
    ring
  · simp [hd]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0467

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstModeAssembly
Source SHA256: 356608718cd11fcb786f3ec57a7ff68b7767d43681d636042031babc6124ff82
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0468


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic FirstPassCubeLabels FourierBridge JointLogSeparation
open MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstModeIdealRows (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (C₁ C₂ : Finset ι → ℂ) (d h : Eis) (a : Fin 7 → ℝ)
    (y₁ y₂ : Finset ι → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2) a *
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
    idealPairReindex p hg F
      (cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂
        (firstColumnMode true C₁ y₁ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)) d)
      (cubePlusCoefficient p hp hcop hg B v ε₁ ε₂
        (firstColumnMode false C₂ y₂ (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)) d) h

theorem first_gauss_common_integral
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ) (R : ℝ)
    (g : Fin 9 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R y =
      ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h *
        firstPoissonProfile W₁ W₂ Φ V R (firstCoordinates a (y₁ N) (y₂ P)) else 0) =
    ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
      firstModeIdealRows p hp hcop hg F B v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z := by
  let coeff := fun j : Finset ι × Finset ι => if Disjoint j.1 j.2 then
    threeGaussRowFactor p hp hcop hg j.1 j.2 B v ε₁ ε₂ C₁ C₂ d h else 0
  let coord := fun j : Finset ι × Finset ι => firstCoordinates a (y₁ j.1) (y₂ j.2)
  calc
    _ = ∑ j ∈ F.powerset ×ˢ F.powerset, coeff j *
        ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (coord j) z.1 z.2 := by
      simp only [Finset.sum_product,coeff,coord]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : Disjoint N P <;> simp [hd,he]
    _ = ∫ z : Frequency × (Fin 9 → ℝ), fullProfileDensity g b₁ b₂ b₃ z *
        ∑ j ∈ F.powerset ×ˢ F.powerset, coeff j *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (coord j) z.1 z.2 :=
      full_density_finite_sum _ g b₁ b₂ b₃ _ _ _ coeff coord
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      congr 1
      simp only [Finset.sum_product,coeff,coord,ite_mul,zero_mul]
      exact actual_first_mode_ideal_rows p hp hcop hg hinj hc hpr F B hFB
        v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z

theorem first_gauss_uniform_common_measure
    (W₁ W₂ : ℝ → ℂ) (lo hi : ℝ) (hlo : 0 < lo)
    (hs₁ : Function.support W₁ ⊆ Set.Icc lo hi)
    (hs₂ : Function.support W₂ ⊆ Set.Icc lo hi)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ,ℂ)) (C : ℝ), 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b₃ : 𝓢(ℝ,ℂ),
      (∀ (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
        (F B : Finset ι), Disjoint F B → ∀ (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (C₁ C₂ : Finset ι → ℂ) (d h : Eis) (a : Fin 7 → ℝ) (y₁ y₂ : Finset ι → ℝ),
        (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
          threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h *
            firstPoissonProfile W₁ W₂ Φ V R (firstCoordinates a (y₁ N) (y₂ P)) else 0) =
        ∫ z : Frequency × (Fin 9 → ℝ),
          fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z *
          firstModeIdealRows p hp hcop hg F B v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ z) ∧
      Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
        tripleHeight J z.1 * coordinateHeight J z.2 *
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ∧
      (1+R)^A * (∫ z : Frequency × (Fin 9 → ℝ),
        tripleHeight J z.1 * coordinateHeight J z.2 *
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ z‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hs⟩ := first_full_profile_common_measure
    W₁ W₂ lo hi hlo hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,he,hI,hB⟩ := hs R hR
  refine ⟨b₃,?_,hI,hB⟩
  intro hinj hc hpr F B hFB v ε₁ ε₂ C₁ C₂ d h a y₁ y₂
  apply first_gauss_common_integral p hp hcop hg hinj hc hpr F B hFB
    v ε₁ ε₂ C₁ C₂ d h a y₁ y₂ W₁ W₂ Φ V R
    (firstRootSchwartz V hV hS) b₁ b₂ b₃
  intro y
  rw [full_density_mode_fubini]
  simpa only [pureProfileMode_height] using he y

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0468

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondCutoffScale
Source SHA256: c12a72a3f038b7ebdd4c23b41e19f5a049e2fba9d0beb16f601f7fc2e082c7db
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0469



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_correlated_radius_bound {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (d : O) (G E : Finset ι)
    (Z delta theta g s Hc eta tau L : ℝ) (hZ : 0<Z) (hL0 : 0≤L)
    (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta))
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G)
    (hL : L≤Z^(s+4*eta)) :
    correlatedSecondRadius p d G E L (Z^(Hc+12*eta+tau)) (Z^tau) ≤
      Z^(2*(s-g)-Hc+delta+2*theta+eta) := by
  have hratio : primeProductNorm p E/primeProductNorm p G ≤ Z^(theta-g+2*eta) := by
    calc
      _ ≤ Z^(theta+eta)/Z^(g-eta) := div_le_div₀
        (Real.rpow_pos_of_pos hZ _).le hE (Real.rpow_pos_of_pos hZ _) hG
      _ = _ := by rw [←Real.rpow_sub hZ]; congr 1; ring
  have hratio0 : 0≤primeProductNorm p E/primeProductNorm p G :=
    div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hsq (x : ℝ) : (Z^x)^2=Z^(2*x) := by
    rw [pow_two,←Real.rpow_add hZ]
    congr 1
    ring
  calc
    _ ≤ Z^(delta+eta)*(Z^(theta-g+2*eta))^2*(Z^(s+4*eta))^2*
        Z^tau/Z^(Hc+12*eta+tau) := by
      unfold correlatedSecondRadius
      gcongr
    _ = _ := by
      rw [hsq,hsq,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      ring

theorem second_correlated_radius_childM {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (d : O) (G E : Finset ι)
    (Z M r ell V delta A B j t g theta eta tau L : ℝ) (hZ : 0<Z) (hL0 : 0≤L)
    (hd : ‖eisEmbedding d‖^2≤Z^(delta+eta))
    (hE : primeProductNorm p E≤Z^(theta+eta))
    (hG : Z^(g-eta)≤primeProductNorm p G)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    correlatedSecondRadius p d G E L
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) (Z^tau) ≤
      Z^(childM M ell A t g theta V j eta) := by
  have hb := second_correlated_radius_bound p hp d G E Z delta theta g (r-A-B-t)
    (firstPhysicalHeight M r ell V delta B j) eta tau L hZ hL0 hd hE hG hL
  convert hb using 1; congr 1
  unfold childM decrease firstPhysicalHeight
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0469

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondProfileIdentity
Source SHA256: 851d9ba10ac7e31a261133abc29153b2ea01826ca57e2d4d49d3d6db22d5b75b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0470



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondNormProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) : ℂ :=
  (∏ i, V i (Real.log (q i))) * W₁ (q 0*q 2*q 4) * W₂ (q 0*q 2*q 5) *
    paperRadialFourier Φ (R*q 3/(q 1*(q 2)^2*q 4*q 5)) /
      ((q 1:ℂ)*(q 2:ℂ)*(Real.sqrt (q 4):ℂ)*(Real.sqrt (q 5):ℂ))

lemma secondPoissonProfile_log (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    secondPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) =
      secondNormProfile W₁ W₂ Φ V R q := by
  have hleft : (∑ i, secondLeftSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 4) := by
    simp [Fin.sum_univ_succ,secondLeftSlope]; ring
  have hright : (∑ i, secondRightSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 5) := by
    simp [Fin.sum_univ_succ,secondRightSlope]; ring
  have hker : (∑ i, secondKernelSlope i * Real.log (q i)) =
      Real.log (q 3) - (Real.log (q 1)+Real.log (q 2)+Real.log (q 2)+Real.log (q 4)+Real.log (q 5)) := by
    simp [Fin.sum_univ_succ,secondKernelSlope]; ring
  unfold secondPoissonProfile secondNormProfile
  rw [hleft,hright,hker]
  simp only [Real.exp_add,Real.exp_sub,Real.exp_log (hq _)]
  have hk : R * (q 3/(q 1*q 2*q 2*q 4*q 5)) = R*q 3/(q 1*(q 2)^2*q 4*q 5) := by ring
  rw [hk]
  simp only [Fin.prod_univ_succ,secondRootWindows,inverseNormWindow,inverseRootWindow,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,Real.exp_log (hq _),Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,  Fin.val_mk]
  norm_num
  ring

theorem secondSourcePairKernel_profile {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (G V N M : Finset ι) (hVN : Disjoint V N) (hVM : Disjoint V M)
    (e k : Eis) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖eisEmbedding e‖^2 : ℂ)⁻¹ * secondSourcePairKernel p e k
      (fun U => W₁ (primeProductNorm p G * primeProductNorm p U))
      (fun U => W₂ (primeProductNorm p G * primeProductNorm p U)) Φ Y (V ∪ N) (V ∪ M) =
    secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
      ![primeProductNorm p G, ‖eisEmbedding e‖^2, primeProductNorm p V,
        ‖eisEmbedding k‖^2, primeProductNorm p N, primeProductNorm p M] := by
  have hs (S : Finset ι) : ‖eisEmbedding (∏ i ∈ S, p i)‖ = Real.sqrt (primeProductNorm p S) := by
    simp only [primeProductNorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hV : 0 ≤ primeProductNorm p V := (primeProductNorm_pos p hp V).le
  have hroots : Real.sqrt (primeProductNorm p V*primeProductNorm p N) *
      Real.sqrt (primeProductNorm p V*primeProductNorm p M) =
      primeProductNorm p V * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by
    rw [Real.sqrt_mul hV, Real.sqrt_mul hV]
    calc
      _ = (Real.sqrt (primeProductNorm p V))^2 * Real.sqrt (primeProductNorm p N) * Real.sqrt (primeProductNorm p M) := by ring
      _ = _ := by rw [Real.sq_sqrt hV]
  unfold secondSourcePairKernel secondNormProfile
  simp only [hs,primeProductNorm_union p V N hVN,primeProductNorm_union p V M hVM,
    Matrix.cons_val_zero,  Fin.isValue, Finset.prod_const_one, one_mul]
  have harg : Y * ‖eisEmbedding k‖^2 /
      (‖eisEmbedding e‖^2 * (primeProductNorm p V*primeProductNorm p N *
        (primeProductNorm p V*primeProductNorm p M))) =
      Y * ‖eisEmbedding k‖^2 / (‖eisEmbedding e‖^2 * (primeProductNorm p V)^2 *
        primeProductNorm p N * primeProductNorm p M) := by ring
  rw [harg]
  rw [← Complex.ofReal_mul, hroots]
  push_cast
  ring_nf

theorem secondNormProfile_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (G₀ E₀ V₀ K₀ X₀ Y : ℝ)
    (_hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (Y*K₀/(E₀*V₀^2*X₀^2))
          ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] := by
  have hleft : (q 0/G₀)*(q 2/V₀)*(q 4/X₀) = q 0*q 2*q 4/(G₀*V₀*X₀) := by ring
  have hright : (q 0/G₀)*(q 2/V₀)*(q 5/X₀) = q 0*q 2*q 5/(G₀*V₀*X₀) := by ring
  have harg : (Y*K₀/(E₀*V₀^2*X₀^2))*(q 3/K₀)/
      ((q 1/E₀)*(q 2/V₀)^2*(q 4/X₀)*(q 5/X₀)) =
      Y*q 3/(q 1*(q 2)^2*q 4*q 5) := by
    field_simp
  have hroot : Real.sqrt (q 4/X₀)*Real.sqrt (q 5/X₀) =
      Real.sqrt (q 4)*Real.sqrt (q 5)/X₀ := by
    rw [Real.sqrt_div (hq 4).le,Real.sqrt_div (hq 5).le]
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hX.le]
  have hc0 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (0:Fin 6) = q 0/G₀ := rfl
  have hc1 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (1:Fin 6) = q 1/E₀ := rfl
  have hc2 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (2:Fin 6) = q 2/V₀ := rfl
  have hc3 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (3:Fin 6) = q 3/K₀ := rfl
  have hc4 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (4:Fin 6) = q 4/X₀ := rfl
  have hc5 : ![q 0/G₀,q 1/E₀,q 2/V₀,q 3/K₀,q 4/X₀,q 5/X₀] (5:Fin 6) = q 5/X₀ := rfl
  unfold secondNormProfile
  simp only [Finset.prod_const_one,one_mul,hc0,hc1,hc2,hc3,hc4,hc5]
  rw [hleft,hright,harg]
  have hrootC : (Real.sqrt (q 4/X₀):ℂ)*(Real.sqrt (q 5/X₀):ℂ) =
      (Real.sqrt (q 4):ℂ)*(Real.sqrt (q 5):ℂ)/(X₀:ℂ) := by exact_mod_cast hroot
  rw [show (↑(q 1/E₀):ℂ)*↑(q 2/V₀)*↑(Real.sqrt (q 4/X₀))*↑(Real.sqrt (q 5/X₀)) =
      (↑(q 1/E₀):ℂ)*↑(q 2/V₀)*(↑(Real.sqrt (q 4/X₀))*↑(Real.sqrt (q 5/X₀))) from by ring,
    hrootC]
  have hEc : (E₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE.ne'
  have hVc : (V₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV.ne'
  have hXc : (X₀:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  push_cast
  field_simp [hEc,hVc,hXc]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0470

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondKernelMeasure
Source SHA256: a3d61f0ab7bf02f4f2547042535d1b22ca5f316915e962867ffa9fde7fa1cb17
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0471


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

def secondRelativeNorm (q : Fin 6 → ℝ) (G E V K X : ℝ) : Fin 6 → ℝ :=
  ![q 0/G,q 1/E,q 2/V,q 3/K,q 4/X,q 5/X]

def secondRelativeLog (q : Fin 6 → ℝ) (G E V K X : ℝ) (i : Fin 6) : ℝ :=
  Real.log (secondRelativeNorm q G E V K X i)

lemma secondRelativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (G E V K X : ℝ) (hG : 0 < G) (hE : 0 < E) (hV : 0 < V) (hK : 0 < K) (hX : 0 < X) :
    ∀ i, 0 < secondRelativeNorm q G E V K X i := by
  intro i
  fin_cases i
  · exact div_pos (hq 0) hG
  · exact div_pos (hq 1) hE
  · exact div_pos (hq 2) hV
  · exact div_pos (hq 3) hK
  · exact div_pos (hq 4) hX
  · exact div_pos (hq 5) hX

lemma secondNormProfile_eq_full_of_windows (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (R : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hV : ∀ i, V i (Real.log (q i)) = 1) :
    secondNormProfile W₁ W₂ Φ (fun _ _ => 1) R q =
      secondPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) := by
  rw [secondPoissonProfile_log W₁ W₂ Φ V R q hq]
  simp only [secondNormProfile, hV, Finset.prod_const_one]

theorem second_norm_kernel_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
        (∀ i, V i (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i) = 1) →
        secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
          (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
          ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
            ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
              fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
                (∏ i, logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
                  (t₁,t₂,t₃) u i) (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i))) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_full_profile_common_measure
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep (Y*K₀/(E₀*V₀^2*X₀^2)) (by positivity)
  refine ⟨b₃,?_,hi,hbound⟩
  intro q hq hcut
  rw [secondNormProfile_nominal W₁ W₂ Φ G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX q hq]
  change ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * secondNormProfile W₁ W₂ Φ (fun _ _ => 1)
      (Y*K₀/(E₀*V₀^2*X₀^2)) (secondRelativeNorm q G₀ E₀ V₀ K₀ X₀) = _
  rw [secondNormProfile_eq_full_of_windows W₁ W₂ Φ V _ _
    (secondRelativeNorm_pos q hq G₀ E₀ V₀ K₀ X₀ hG hE hV₀ hK hX) hcut, he]
  rfl

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0471

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondFiniteMeasure
Source SHA256: e3542085e053ab7442c9d93aa55bf8989e40c39142ccb70211de0dc67804ebe6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0472



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

universe u

theorem second_finite_source_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ {κ : Type u} (source : Finset κ) (c : κ → ℂ) (q : κ → Fin 6 → ℝ),
        (∀ x ∈ source, ∀ i, 0 < q x i) →
        (∀ x ∈ source, ∀ i, V i (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀ i) = 1) →
        (∑ x ∈ source, c x * secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
          (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (q x)) =
          ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
            ∫ p : Frequency × (Fin 6 → ℝ),
              fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p *
                ∑ x ∈ source, c x * pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
                  (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀) p.1 p.2) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_norm_kernel_common_measure
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  refine ⟨b₃,?_,hi,hbound⟩
  intro κ source c q hq hcut
  have hpoint (x : κ) (hx : x ∈ source) :
      secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
        (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (q x) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ p : Frequency × (Fin 6 → ℝ),
        fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀) p.1 p.2 := by
    rw [he (q x) (hq x hx) (hcut x hx),full_density_mode_fubini]
    simp only [pureProfileMode_height]
  calc
    _ = ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∑ x ∈ source, c x *
        ∫ p : Frequency × (Fin 6 → ℝ),
          fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (q x) G₀ E₀ V₀ K₀ X₀) p.1 p.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpoint x hx]
      ring
    _ = _ := by rw [full_density_finite_sum]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0472

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondFreshMeasure
Source SHA256: 792bf00639acc85dbbc41c5f1f32970785459bcb8ecba3fb0c16cd6843def8f0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0473


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem second_fresh_kernel_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (ω₁ ω₂ : ℝ → ℂ) (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
        (W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) ≠ 0 → ω₁ (q 4/X₀) = 1) →
        (W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) ≠ 0 → ω₂ (q 5/X₀) = 1) →
        (ω₁ (q 4/X₀) ≠ 0 → ω₂ (q 5/X₀) ≠ 0 →
          ∀ i, V i (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i) = 1) →
        secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
          (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
          ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
            ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
              fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
                (∏ i, logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
                  (t₁,t₂,t₃) u i) (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i))) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_norm_kernel_common_measure
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  refine ⟨b₃,?_,hi,hbound⟩
  intro ω₁ ω₂ q hq hω₁ hω₂ hcut
  by_cases hw₁ : ω₁ (q 4/X₀) = 0
  · have hW : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      have hh := hω₁ hn
      rw [hw₁] at hh
      exact zero_ne_one hh
    simp only [secondNormProfile,hW,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 5/X₀) = 0
  · have hW : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      have hh := hω₂ hn
      rw [hw₂] at hh
      exact zero_ne_one hh
    simp only [secondNormProfile,hW,hw₂,mul_zero,zero_mul,zero_div]
  have hm : secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
    (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
      secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
        (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q := by
    by_cases h1 : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  rw [hm,he q hq (hcut hw₁ hw₂)]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0473

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondWholeKernel
Source SHA256: 6c2d3e6ad9bbcb6c9cd43fae79bff063e3f09d58f90fb8b833e3dc6c21871c77
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0474


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondSourcePairKernel_mark_factors {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (A₁ A₂ : Finset ι) (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (S T : Finset ι) :
    secondSourcePairKernel p e k
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*H₁ U)
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*H₂ U) W Y S T =
      star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)) * primeMark slots₂ lists₂ a₂ (A₂ ∪ T) *
        secondSourcePairKernel p e k H₁ H₂ W Y S T := by
  simp only [secondSourcePairKernel,star_mul]
  ring

theorem secondChildKernelPair_whole_profile {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F G V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    (‖eisEmbedding e‖^2 : ℂ)⁻¹ * secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂
      m r c d e k (-k)
      (secondSourcePairKernel p e k
        (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U)*W₁ (primeProductNorm p G*primeProductNorm p U))
        (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U)*W₂ (primeProductNorm p G*primeProductNorm p U)) Φ Y) =
    ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
      (star (secondChildColumn p hp hcop hg Ψ₁ (m*r) (c*e*∏ i ∈ V,p i)
        (d*e*k) (fun _ => 1) N) *
        secondChildColumn p hp hcop hg Ψ₂ (m*r) (c*e*∏ i ∈ V,p i)
          (d*e*(-k)) (fun _ => 1) M) *
      (star (primeMark slots₁ lists₁ a₁ (A₁ ∪ (V ∪ N))) *
        primeMark slots₂ lists₂ a₂ (A₂ ∪ (V ∪ M))) *
      secondNormProfile (fun x => star (W₁ x)) W₂ Φ (fun _ _ => 1) Y
        ![primeProductNorm p G,‖eisEmbedding e‖^2,primeProductNorm p V,
          ‖eisEmbedding k‖^2,primeProductNorm p N,primeProductNorm p M] := by
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondSourcePairKernel_mark_factors]
  have hp := secondSourcePairKernel_profile p hp G V N M hVN hVM e k W₁ W₂ Φ Y
  rw [← hp]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0474

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualSecondProfile
Source SHA256: aa838143347c734cffd2353518fd77a7df4ed0dbbef22c67ca9af0fac8d93243
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0475



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

structure SecondProfileData (ι : Type*) where
  common : Finset ι
  overlap : Finset ι
  extractedLeft : Finset ι
  extractedRight : Finset ι
  rayLeft : Eis →* ℂ
  rayRight : Eis →* ℂ
  puncture : Eis
  quotient : Eis
  oldLabel : Eis
  oldDivisor : Eis
  divisor : Eis
  frequency : Eis

def secondActualNorms {ι : Type*} (p : ι → Eis) (x : SecondProfileData ι)
    (N M : Finset ι) : Fin 6 → ℝ :=
  ![primeProductNorm p x.common, ‖eisEmbedding x.divisor‖^2,
    primeProductNorm p x.overlap, ‖eisEmbedding x.frequency‖^2,
    primeProductNorm p N, primeProductNorm p M]

lemma secondActualNorms_pos {ι : Type*} (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
    (x : SecondProfileData ι) (he : x.divisor ≠ 0) (hk : x.frequency ≠ 0) (N M : Finset ι) :
    ∀ i, 0 < secondActualNorms p x N M i := by
  intro i
  fin_cases i
  · exact primeProductNorm_pos p hp x.common
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero he))
  · exact primeProductNorm_pos p hp x.overlap
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hk))
  · exact primeProductNorm_pos p hp N
  · exact primeProductNorm_pos p hp M

def secondActualCoefficient {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (N M : Finset ι) : ℂ :=
  star (secondChildColumn p hp hcop hg x.rayLeft (x.puncture*x.quotient)
    (x.oldLabel*x.divisor*∏ i ∈ x.overlap,p i) (x.oldDivisor*x.divisor*x.frequency) (fun _ => 1) N) *
  secondChildColumn p hp hcop hg x.rayRight (x.puncture*x.quotient)
    (x.oldLabel*x.divisor*∏ i ∈ x.overlap,p i) (x.oldDivisor*x.divisor*(-x.frequency)) (fun _ => 1) M *
  (star (primeMark slots₁ lists₁ a₁ (x.extractedLeft ∪ (x.overlap ∪ N))) *
    primeMark slots₂ lists₂ a₂ (x.extractedRight ∪ (x.overlap ∪ M)))

def actualSecondProfileRow {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) : ℂ :=
  (‖eisEmbedding x.divisor‖^2 : ℂ)⁻¹ *
  secondChildKernelPair p hp hcop hg F x.overlap x.rayLeft x.rayRight x.puncture x.quotient
    x.oldLabel x.oldDivisor x.divisor x.frequency (-x.frequency)
    (secondSourcePairKernel p x.divisor x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ (x.extractedLeft ∪ U)*
        W₁ (primeProductNorm p x.common*primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (x.extractedRight ∪ U)*
        W₂ (primeProductNorm p x.common*primeProductNorm p U/X)) Φ Y)

theorem actualSecondProfileRow_eq_whole {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    actualSecondProfileRow p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X =
      ∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          secondNormProfile (fun z => star (W₁ (z/X))) (fun z => W₂ (z/X)) Φ (fun _ _ => 1) Y
            (secondActualNorms p x N M) :=
  secondChildKernelPair_whole_profile p hp hcop hg F x.common x.overlap x.extractedLeft x.extractedRight
    x.rayLeft x.rayRight x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ (fun z => W₁ (z/X)) (fun z => W₂ (z/X)) Φ Y

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0475

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualSecondMeasure
Source SHA256: a9cb39dba2c21bd8490158ef67c422ce40c77c2359c25738e104da80ab182163
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0476



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondProfileIndices {κ ι : Type*} [DecidableEq ι]
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) :
    Finset (Σ _ : κ, Finset ι × Finset ι) :=
  source.sigma (fun j => (F \ (x j).overlap).powerset ×ˢ (F \ (x j).overlap).powerset)

lemma mem_secondProfileIndices {κ ι : Type*} [DecidableEq ι]
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι)
    (j : Σ _ : κ, Finset ι × Finset ι) : j ∈ secondProfileIndices source F x ↔
      j.1 ∈ source ∧ j.2.1 ∈ (F \ (x j.1).overlap).powerset ∧
        j.2.2 ∈ (F \ (x j.1).overlap).powerset := by
  simp only [secondProfileIndices,Finset.mem_sigma,Finset.mem_product]

theorem actualSecondProfileRows_eq_indexed {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X : ℝ) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X) =
    ∑ j ∈ secondProfileIndices source F x,
      (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
      secondNormProfile (fun z => star (W₁ (z/X))) (fun z => W₂ (z/X)) Φ (fun _ _ => 1) Y
        (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
  simp only [actualSecondProfileRow_eq_whole,secondProfileIndices,Finset.sum_sigma,
    Finset.sum_product,Finset.mul_sum,mul_assoc]

theorem actualSecondProfileRows_integral {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (g : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
          fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
              (t₁,t₂,t₃) u i) (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2)
                G₀ E₀ V₀ K₀ X₀ i))) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        fullProfileDensity g b₁ b₂ b₃ v *
          ∑ j ∈ secondProfileIndices source F x,
            (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
              slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
  rw [actualSecondProfileRows_eq_indexed]
  rw [← full_density_finite_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj, full_density_mode_fubini]
  simp only [pureProfileMode_height]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0476

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualSecondUniform
Source SHA256: cf6dae9b7698a05a69e32188dcb4a1f088acaa1e578c01cb2429dbfd682a2d69
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0477


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v w

def ActualSecondCommonMeasureAt (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 6 → ℝ → ℂ) (hV : ∀ i, ContDiff ℝ ∞ (V i))
    (hS : ∀ i, HasCompactSupport (V i))
    (G₀ E₀ V₀ K₀ X₀ Y : ℝ) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) : Prop :=
  ∀ {κ : Type u} {ι : Type v} {σ : Type w} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (weight : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ),
    (∀ j ∈ source, (x j).divisor ≠ 0 ∧ (x j).frequency ≠ 0) →
    (∀ j ∈ secondProfileIndices source F x, ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1) →
    (∑ j ∈ source, weight j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ z : Frequency × (Fin 6 → ℝ),
        fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ z *
          ∑ j ∈ secondProfileIndices source F x,
            (weight j.1 * secondActualCoefficient p hp hcop hg (x j.1)
              slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) z.1 z.2

theorem actual_second_uniform_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ G₀ E₀ V₀ K₀ X₀ Y : ℝ,
      0 < G₀ → 0 < E₀ → 0 < V₀ → 0 < K₀ → 0 < X₀ → 0 < Y →
      ∃ b₃ : 𝓢(ℝ, ℂ),
      ActualSecondCommonMeasureAt.{u,v,w} W₁ W₂ Φ V hV hS G₀ E₀ V₀ K₀ X₀ Y b₁ b₂ b₃ ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + Y*K₀/(E₀*V₀^2*X₀^2))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  have hstar : ContDiff ℝ ∞ (fun t => star (W₁ t)) := Complex.conjCLE.contDiff.comp hW₁
  have hsstar : Function.support (fun t => star (W₁ t)) ⊆ Set.Icc a b := by
    intro t ht
    apply hs₁
    simpa only [Function.mem_support,star_ne_zero] using ht
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := second_norm_kernel_common_measure
    (fun t => star (W₁ t)) W₂ a b ha hsstar hs₂ hstar hW₂ Φ V M hV hS hM hbox A J
  refine ⟨b₁,b₂,C,hC,?_⟩
  intro G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  obtain ⟨b₃,he,hi,hbound⟩ := hsep G₀ E₀ V₀ K₀ X₀ Y hG hE hV₀ hK hX hY
  refine ⟨b₃,?_,hi,hbound⟩
  intro κ ι σ _ _ p hp _ hcop hg source F x weight slots₁ slots₂ lists₁ lists₂ a₁ a₂ hn hcut
  apply actualSecondProfileRows_integral p hp hcop hg source F x weight
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y G₀ E₀ V₀ K₀ X₀
    (secondRootSchwartz V hV hS) b₁ b₂ b₃
  intro j hj
  have hj0 := (mem_secondProfileIndices source F x j).mp hj
  exact he (secondActualNorms p (x j.1) j.2.1 j.2.2)
    (secondActualNorms_pos p hp (x j.1) (hn j.1 hj0.1).1 (hn j.1 hj0.1).2 j.2.1 j.2.2)
    (hcut j hj)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0477

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramIdealSummation
Source SHA256: 4959986e463934cb7fb75ad973ffff351661e0d51592a6c1bfe460fc842bdf6d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0478


namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.ProbeGramCommon
open ActualEisensteinCubic CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

def gramIdealNorm (I : SupportedIdeal) : ℝ := Ideal.absNorm I.val

lemma gramIdealNorm_pos (I : SupportedIdeal) : 0 < gramIdealNorm I := by
  unfold gramIdealNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr I.property.1)

lemma gramIdealNorm_one_le (I : SupportedIdeal) : 1 ≤ gramIdealNorm I := by
  unfold gramIdealNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property.1)

theorem supportedIdeal_rpow_summable (r : ℝ) (hr : r < -1) :
    Summable (fun I : SupportedIdeal => gramIdealNorm I ^ r) := by
  have hs := CubicEisenstein.fullIdealWeight_summable_norm ((-r:ℝ):ℂ)
    (by simp only [Complex.ofReal_re]; linarith)
  have hinj : Function.Injective (fun I : SupportedIdeal => I.val) := Subtype.val_injective
  have ht := hs.comp_injective hinj
  apply ht.congr
  intro I
  rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property.1]
  have he : (Ideal.absNorm I.val:ℂ) = ((gramIdealNorm I:ℝ):ℂ) := by simp [gramIdealNorm]
  rw [he,Complex.norm_cpow_eq_rpow_re_of_pos (gramIdealNorm_pos I)]
  simp only [Complex.neg_re,Complex.ofReal_re,neg_neg]

theorem supportedIdeal_rpow_finite_bound (r : ℝ) (hr : r < -1) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : Finset SupportedIdeal,
      (∑ I ∈ F, gramIdealNorm I ^ r) ≤ K := by
  have hs := supportedIdeal_rpow_summable r hr
  let K := 1 + ∑' I : SupportedIdeal, gramIdealNorm I ^ r
  have hn : 0 ≤ ∑' I : SupportedIdeal, gramIdealNorm I ^ r :=
    tsum_nonneg (fun I => Real.rpow_nonneg (gramIdealNorm_pos I).le _)
  refine ⟨K, by dsimp [K]; linarith, ?_⟩
  intro F
  exact (hs.sum_le_tsum F (fun I _ => Real.rpow_nonneg (gramIdealNorm_pos I).le _)).trans
    (by dsimp [K]; linarith)

lemma ideal_sum_min_power_bound (t : ℝ) (ht : 0 < t) (A : ℕ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hA : θ ≤ A) : min 1 (t^A) ≤ t^θ := by
  by_cases h : t ≤ 1
  · apply (min_le_right _ _).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge ht h hA
  · exact (min_le_left _ _).trans (Real.one_le_rpow (le_of_not_ge h) hθ)

lemma gram_ideal_term_bound (δ Λ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hΛ : 0 < Λ) (A : ℕ) (hA : 1 ≤ A) (I J : SupportedIdeal) :
    gramIdealNorm I ^ (-2:ℝ) * gramIdealNorm J ^ (-2:ℝ) *
      min 1 ((gramIdealNorm I*gramIdealNorm J/Λ)^A) ≤
      Λ^(-1+δ) * (gramIdealNorm I^(-1-δ) * gramIdealNorm J^(-1-δ)) := by
  have hi := gramIdealNorm_pos I
  have hj := gramIdealNorm_pos J
  have ha : (1-δ:ℝ) ≤ A := by
    have hh : (1:ℝ) ≤ A := by exact_mod_cast hA
    linarith
  have hm := ideal_sum_min_power_bound (gramIdealNorm I*gramIdealNorm J/Λ)
    (by positivity) A (1-δ) (by linarith) ha
  apply (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq
  rw [Real.div_rpow (by positivity) hΛ.le,Real.mul_rpow hi.le hj.le,
    div_eq_mul_inv,← Real.rpow_neg hΛ.le]
  have hi' : gramIdealNorm I^(-2:ℝ)*gramIdealNorm I^(1-δ)=gramIdealNorm I^(-1-δ) := by
    rw [←Real.rpow_add hi]
    congr 1
    ring
  have hj' : gramIdealNorm J^(-2:ℝ)*gramIdealNorm J^(1-δ)=gramIdealNorm J^(-1-δ) := by
    rw [←Real.rpow_add hj]
    congr 1
    ring
  rw [show -(1-δ) = -1+δ by ring]
  calc
    _ = Λ^(-1+δ)*((gramIdealNorm I^(-2:ℝ)*gramIdealNorm I^(1-δ))*
        (gramIdealNorm J^(-2:ℝ)*gramIdealNorm J^(1-δ))) := by ring
    _ = _ := by rw [hi',hj']

theorem gram_supported_double_sum (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : ℕ), 1 ≤ A → ∀ (Λ : ℝ), 0 < Λ →
      ∀ (F G : Finset SupportedIdeal),
      (∑ I ∈ F, ∑ J ∈ G, gramIdealNorm I^(-2:ℝ) * gramIdealNorm J^(-2:ℝ) *
        min 1 ((gramIdealNorm I*gramIdealNorm J/Λ)^A)) ≤ K*Λ^(-1+δ) := by
  obtain ⟨C,hC,hb⟩ := supportedIdeal_rpow_finite_bound (-1-δ) (by linarith)
  refine ⟨C^2, by positivity, ?_⟩
  intro A hA Λ hΛ F G
  have hF := hb F
  have hG := hb G
  have hGn : 0 ≤ ∑ J ∈ G, gramIdealNorm J^(-1-δ) :=
    Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (gramIdealNorm_pos J).le _)
  calc
    _ ≤ ∑ I ∈ F, ∑ J ∈ G, Λ^(-1+δ)*
        (gramIdealNorm I^(-1-δ)*gramIdealNorm J^(-1-δ)) :=
      Finset.sum_le_sum (fun I _ => Finset.sum_le_sum
        (fun J _ => gram_ideal_term_bound δ Λ hδ hδ1 hΛ A hA I J))
    _ = Λ^(-1+δ)*((∑ I ∈ F, gramIdealNorm I^(-1-δ))*
        (∑ J ∈ G, gramIdealNorm J^(-1-δ))) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ Λ^(-1+δ)*C^2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [pow_two] using mul_le_mul hF hG hGn hC.le
    _ = _ := by ring

theorem gram_supported_exceptional_sum (ε : ℝ) (_hε : 0 ≤ ε) (hε1 : ε < 1/6) :
    ∃ K : ℝ, 0 < K ∧ ∀ (F G : Finset SupportedIdeal),
      (∑ I ∈ F, ∑ J ∈ G,
        gramIdealNorm I^(-7/6+ε:ℝ)*gramIdealNorm J^(-2:ℝ)) ≤ K := by
  obtain ⟨C,hC,hb⟩ := supportedIdeal_rpow_finite_bound (-7/6+ε) (by linarith)
  obtain ⟨D,hD,hd⟩ := supportedIdeal_rpow_finite_bound (-2) (by norm_num)
  refine ⟨C*D, by positivity, ?_⟩
  intro F G
  rw [← Finset.sum_mul_sum]
  exact mul_le_mul (hb F) (hd G)
    (Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (gramIdealNorm_pos J).le _)) hC.le

end SevenEighths.ProbeGramCommon

end

end OAI
end OAIOriginalModule0478

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramLatticeDecay
Source SHA256: 3deb1e33c61e6b0a79e024236a040e237f7bc3c9adc6ca94ccd313e767a9d889
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0479


namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramLatticeDecay
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

abbrev Joint := WithLp 2 (ℂ × ℂ)

def point (x y : ℂ) : Joint := WithLp.toLp 2 (x,y)

def sourceControl (S : Finset (ℕ × ℕ)) (W : 𝓢(Joint, ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ Joint ℂ) W

theorem sourceControl_nonneg (S : Finset (ℕ × ℕ)) (W : 𝓢(Joint, ℂ)) :
    0 ≤ sourceControl S W := apply_nonneg _ _

@[simp] theorem norm_point_sq (x y : ℂ) :
    ‖point x y‖^2 = ‖x‖^2 + ‖y‖^2 := WithLp.prod_norm_sq_eq_of_L2 _

theorem product_decay (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ((1+‖x‖^2)^2 * (1+‖y‖^2)^2) * ‖W (point x y)‖ ≤
      (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W := by
  have hx := WithLp.norm_fst_le ℂ (point x y)
  have hy := WithLp.norm_snd_le ℂ (point x y)
  change ‖x‖ ≤ ‖point x y‖ at hx
  change ‖y‖ ≤ ‖point x y‖ at hy
  have hx2 : 1+‖x‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hy2 : 1+‖y‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hpow : (1+‖x‖^2)^2 * (1+‖y‖^2)^2 ≤ (1+‖point x y‖)^8 := by
    calc
      _ ≤ ((1+‖point x y‖)^2)^2 * ((1+‖point x y‖)^2)^2 := by gcongr
      _ = _ := by ring
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (8,0)) (k := 8) (n := 0) le_rfl le_rfl W (point x y)
  simp only [norm_iteratedFDeriv_zero] at h
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans h

def physicalPoint (N : ℝ) (m : O × O) : Joint :=
  point (eisEmbedding m.1 / (Real.sqrt N : ℂ))
    (eisEmbedding m.2 / (Real.sqrt N : ℂ))

theorem physicalPoint_eq_smul (N : ℝ) (m : O × O) :
    physicalPoint N m = (Real.sqrt N)⁻¹ • point (eisEmbedding m.1) (eisEmbedding m.2) := by
  apply WithLp.ofLp_injective
  simp [physicalPoint, point, div_eq_mul_inv, Algebra.smul_def, mul_comm]

theorem physical_summable (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => ‖W (physicalPoint N m)‖) := by
  let g : O → ℝ := fun m => ((1+N⁻¹*‖eisEmbedding m‖^2)^2)⁻¹
  have hg : Summable g := scaled_eisenstein_cauchy_summable _ (inv_pos.mpr hN)
  have hp := hg.mul_of_nonneg hg (fun _ => by dsimp [g]; positivity)
    (fun _ => by dsimp [g]; positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hp.mul_left ((2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W))
  intro m
  have hb := product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
    (eisEmbedding m.2 / (Real.sqrt N : ℂ))
  have hnorm (m : O) : ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = N⁻¹*‖eisEmbedding m‖^2 := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN.le]
    ring
  simp only [hnorm] at hb
  change ‖W (physicalPoint N m)‖ ≤ ((2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W) * (g m.1*g m.2)
  dsimp only [g]
  rw [ ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [physicalPoint, mul_comm] using hb

theorem physical_lattice_bound :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (N : ℝ), 1 ≤ N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  refine ⟨Finset.Iic (8,0), (2:ℝ)^8 * (4*(1+Real.pi)^2)^2, by positivity, ?_⟩
  intro W N hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  let g : O → ℝ := fun m => ((1+N⁻¹*‖eisEmbedding m‖^2)^2)⁻¹
  have hg : Summable g := scaled_eisenstein_cauchy_summable _ (inv_pos.mpr hNp)
  have hp := hg.mul_of_nonneg hg (fun _ => by dsimp [g]; positivity)
    (fun _ => by dsimp [g]; positivity)
  have hpoint (m : O × O) : ‖W (physicalPoint N m)‖ ≤
      ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W) * (g m.1*g m.2) := by
    have hb := product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
      (eisEmbedding m.2 / (Real.sqrt N : ℂ))
    have hn (m : O) : ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = N⁻¹*‖eisEmbedding m‖^2 := by
      rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hNp.le]
      ring
    simp only [hn] at hb
    dsimp only [g]
    rw [ ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    simpa only [physicalPoint, mul_comm] using hb
  have hmass : (∑' m : O, g m) ≤ (4*(1+Real.pi)^2)*N := by
    have h := scaled_eisenstein_cauchy_small N⁻¹ (inv_pos.mpr hNp) ((inv_le_one₀ hNp).mpr hN)
    have hh := mul_le_mul_of_nonneg_left h hNp.le
    simpa only [g, ← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul, mul_comm] using hh
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(g m.1*g m.2) :=
      (physical_summable W N hNp).tsum_le_tsum hpoint (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, g m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*((4*(1+Real.pi)^2)*N)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by dsimp [g]; positivity)) hmass 2
    _ = _ := by ring

abbrev DualIndex := (ℤ × ℤ) × (ℤ × ℤ)

def dualPoint (p : DualIndex) : Joint :=
  point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)

def dualRow (p : DualIndex) : Fin 2 → O :=
  ![dualFrequencyEquiv p.1, dualFrequencyEquiv p.2]

def dualCoordinates (p : DualIndex) : (Fin 2 × Fin 2) → ℤ :=
  CubicEisenstein.rowCoordinates (dualRow p)

theorem dualCoordinates_injective : Function.Injective dualCoordinates := by
  intro p q hp
  have h := CubicEisenstein.rowCoordinates_injective hp
  apply Prod.ext
  · exact dualFrequencyEquiv.injective (congrFun h 0)
  · exact dualFrequencyEquiv.injective (congrFun h 1)

@[simp] theorem dualCoordinates_zero : dualCoordinates 0 = 0 := by
  have hzero : ActualEisensteinCoordinates.coords (0 : O) = (0,0) := by
    simpa [ActualEisensteinCoordinates.eval] using ShortDraftLatticeCount.coords_eval 0 0
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [dualCoordinates, CubicEisenstein.rowCoordinates, dualRow,
      dualFrequencyEquiv, ActualEisensteinCoordinates.eval, hzero]

theorem dualCoordinates_norm_le (p : DualIndex) :
    ‖dualCoordinates p‖ ≤ 2 * ‖dualPoint p‖ := by
  have hc := CubicEisenstein.coordinates_norm_bound (dualRow p)
  have hp : ‖fun i => eisEmbedding (dualRow p i)‖ ≤ ‖dualPoint p‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    have h1 := explicitDualFrequency_norm_sq 1 p.1
    have h2 := explicitDualFrequency_norm_sq 1 p.2
    norm_num only [norm_one, one_pow, div_one] at h1 h2
    have hq := norm_point_sq (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)
    fin_cases i
    · change ‖eisEmbedding (dualFrequencyEquiv p.1)‖ ≤ ‖dualPoint p‖
      dsimp only [dualPoint]
      nlinarith [sq_nonneg ‖eisEmbedding (dualFrequencyEquiv p.2)‖,
        norm_nonneg (point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)),
        norm_nonneg (eisEmbedding (dualFrequencyEquiv p.1))]
    · change ‖eisEmbedding (dualFrequencyEquiv p.2)‖ ≤ ‖dualPoint p‖
      dsimp only [dualPoint]
      nlinarith [sq_nonneg ‖eisEmbedding (dualFrequencyEquiv p.1)‖,
        norm_nonneg (point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)),
        norm_nonneg (eisEmbedding (dualFrequencyEquiv p.2))]
  exact hc.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

theorem dualPoint_norm_pos (p : DualIndex) (hp : p ≠ 0) : 0 < ‖dualPoint p‖ := by
  have hc : dualCoordinates p ≠ 0 := by
    intro h
    exact hp (dualCoordinates_injective (h.trans dualCoordinates_zero.symm))
  have hh := norm_pos_iff.mpr hc
  have hb := dualCoordinates_norm_le p
  linarith

theorem dual_power_summable (k : ℝ) (hk : 4 < k) :
    Summable (fun p : {p : DualIndex // p ≠ 0} => ‖dualPoint p.val‖ ^ (-k)) := by
  have hs : Summable (fun p : {p : DualIndex // p ≠ 0} => ‖dualCoordinates p.val‖ ^ (-k)) :=
    (CubicEisenstein.summable_integer_four_rpow k hk).comp_injective
    (dualCoordinates_injective.comp (Subtype.val_injective))
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _) _
    (hs.mul_left ((2:ℝ)^k))
  intro p
  have hc : 0 < ‖dualCoordinates p.val‖ := norm_pos_iff.mpr (by
    intro h
    exact p.property (dualCoordinates_injective (h.trans dualCoordinates_zero.symm)))
  have h := Real.rpow_le_rpow_of_nonpos (half_pos hc)
    (by have := dualCoordinates_norm_le p.val; linarith : ‖dualCoordinates p.val‖ / 2 ≤ ‖dualPoint p.val‖)
    (by linarith : -k ≤ 0)
  calc
    _ ≤ (‖dualCoordinates p.val‖ / 2) ^ (-k) := h
    _ = (2:ℝ)^k * ‖dualCoordinates p.val‖ ^ (-k) := by
      rw [Real.div_rpow (norm_nonneg _) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      simp only [div_inv_eq_mul, mul_comm]

def scaledDualPoint (L : ℝ) (u : ℂ) (p : DualIndex) : Joint :=
  point (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)

theorem norm_scaledDualPoint (L : ℝ) (hL : 0 ≤ L) (u : ℂ) (hu : ‖u‖ = 1)
    (p : DualIndex) : ‖scaledDualPoint L u p‖ = L * ‖dualPoint p‖ := by
  have h1 := norm_point_sq (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)
  have h2 := norm_point_sq (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)
  simp only [norm_mul, hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL,
    one_mul] at h1
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  change ‖point (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)‖^2 =
      (L*‖point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)‖)^2
  simp only [h1, mul_pow, h2]
  ring

theorem fourier_seminorm_control (k : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(Joint, ℂ),
      SchwartzMap.seminorm ℝ k 0 (𝓕 W) ≤ C * sourceControl S W := by
  let T : 𝓢(Joint, ℂ) →L[ℝ] 𝓢(Joint, ℂ) := SchwartzMap.fourierTransformCLM ℝ
  let q : Seminorm ℝ 𝓢(Joint, ℂ) := (SchwartzMap.seminorm ℝ k 0).comp T.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℝ Joint ℂ).continuous_seminorm (k,0)).comp T.continuous
  obtain ⟨S,C,hC,hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Joint ℂ) q hq
  refine ⟨S,C,?_,?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

theorem scaledDual_decay (F : 𝓢(Joint, ℂ)) (k : ℕ) (L : ℝ) (hL : 0 < L)
    (u : ℂ) (hu : ‖u‖ = 1) (p : DualIndex) (hp : p ≠ 0) :
    ‖F (scaledDualPoint L u p)‖ ≤ SchwartzMap.seminorm ℝ k 0 F *
      L^(-(k:ℝ)) * ‖dualPoint p‖^(-(k:ℝ)) := by
  have hn : 0 < ‖scaledDualPoint L u p‖ := by
    rw [norm_scaledDualPoint L hL.le u hu]
    exact mul_pos hL (dualPoint_norm_pos p hp)
  have hb := SchwartzMap.norm_pow_mul_le_seminorm ℝ F k (scaledDualPoint L u p)
  have hh : ‖F (scaledDualPoint L u p)‖ ≤
      SchwartzMap.seminorm ℝ k 0 F * ‖scaledDualPoint L u p‖^(-(k:ℝ)) := by
    rw [Real.rpow_neg hn.le, Real.rpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (pow_pos hn k)]
    simpa only [mul_comm] using hb
  rw [norm_scaledDualPoint L hL.le u hu,
    Real.mul_rpow hL.le (norm_nonneg _)] at hh
  simpa only [mul_assoc] using hh

theorem dual_fourier_summable (A : ℕ) (hA : 2 < A)
    (W : 𝓢(Joint, ℂ)) (L : ℝ) (hL : 0 < L) (u : ℂ) (hu : ‖u‖ = 1) :
    Summable (fun p : {p : DualIndex // p ≠ 0} => ‖(𝓕 W) (scaledDualPoint L u p.val)‖) := by
  have hdim : (4:ℝ) < ((2*A:ℕ):ℝ) := by exact_mod_cast (by omega : 4 < 2*A)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((dual_power_summable ((2*A:ℕ):ℝ) hdim).mul_left
      (SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ))))
  intro p
  exact scaledDual_decay (𝓕 W) (2*A) L hL u hu p.val p.property

theorem dual_fourier_lattice_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (L : ℝ), 1 ≤ L → ∀ (u : ℂ), ‖u‖ = 1 →
        (∑' p : {p : DualIndex // p ≠ 0}, ‖(𝓕 W) (scaledDualPoint L u p.val)‖) ≤
          C * sourceControl S W * L^(-((2*A:ℕ):ℝ)) := by
  obtain ⟨S,C,hC,hbound⟩ := fourier_seminorm_control (2*A)
  let mass : ℝ := ∑' p : {p : DualIndex // p ≠ 0}, ‖dualPoint p.val‖^(-((2*A:ℕ):ℝ))
  have hm : 0 ≤ mass := tsum_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨S,C*(mass+1),mul_pos hC (by positivity),?_⟩
  intro W L hL u hu
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hdim : (4:ℝ) < ((2*A:ℕ):ℝ) := by exact_mod_cast (by omega : 4 < 2*A)
  calc
    _ ≤ ∑' p : {p : DualIndex // p ≠ 0},
        (SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ))) *
          ‖dualPoint p.val‖^(-((2*A:ℕ):ℝ)) :=
      (dual_fourier_summable A hA W L hLp u hu).tsum_le_tsum
        (fun p => scaledDual_decay (𝓕 W) (2*A) L hLp u hu p.val p.property)
        ((dual_power_summable ((2*A:ℕ):ℝ) hdim).mul_left _)
    _ = SchwartzMap.seminorm ℝ (2*A) 0 (𝓕 W) * L^(-((2*A:ℕ):ℝ)) * mass := tsum_mul_left
    _ ≤ (C * sourceControl S W) * L^(-((2*A:ℕ):ℝ)) * (mass+1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (hbound W) (Real.rpow_nonneg hLp.le _)
      · linarith
      · exact hm
      · exact mul_nonneg (mul_nonneg hC.le (sourceControl_nonneg S W)) (Real.rpow_nonneg hLp.le _)
    _ = _ := by ring

theorem sourceControl_mono {S T : Finset (ℕ × ℕ)} (hST : S ⊆ T)
    (W : 𝓢(Joint, ℂ)) : sourceControl S W ≤ sourceControl T W :=
  Seminorm.le_def.mp (Finset.sup_mono hST) W

theorem joint_lattice_bounds (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      (∀ (W : 𝓢(Joint, ℂ)) (N : ℝ), 1 ≤ N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2) ∧
      (∀ (W : 𝓢(Joint, ℂ)) (L : ℝ), 1 ≤ L → ∀ (u : ℂ), ‖u‖ = 1 →
        (∑' p : {p : DualIndex // p ≠ 0}, ‖(𝓕 W) (scaledDualPoint L u p.val)‖) ≤
          C * sourceControl S W * L^(-((2*A:ℕ):ℝ))) := by
  obtain ⟨S₁,C₁,hC₁,h₁⟩ := physical_lattice_bound
  obtain ⟨S₂,C₂,hC₂,h₂⟩ := dual_fourier_lattice_bound A hA
  refine ⟨S₁∪S₂,C₁+C₂,add_pos hC₁ hC₂,?_,?_⟩
  · intro W N hN
    apply (h₁ W N hN).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right hC₂.le)
      (sourceControl_mono Finset.subset_union_left W) (sourceControl_nonneg _ _) (by positivity)
  · intro W L hL u hu
    apply (h₂ W L hL u hu).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact mul_le_mul (le_add_of_nonneg_left hC₁.le)
      (sourceControl_mono Finset.subset_union_right W) (sourceControl_nonneg _ _) (by positivity)

end ProbeGramLatticeDecay

end

end OAI
end OAIOriginalModule0479

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramAnnularLattice
Source SHA256: a9ccbd0bc3e40cac77aed15e5d1d9e95efdebad72309ef1e0fee3fcfbf2ef66f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0480



namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramAnnularLattice
open ProbeGramLatticeDecay ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def AnnularSupport (a b : ℝ) (W : 𝓢(Joint, ℂ)) : Prop :=
  Function.support W ⊆ {z : Joint | a ≤ ‖z.fst‖^2 ∧ ‖z.fst‖^2 ≤ b ∧
    a ≤ ‖z.snd‖^2 ∧ ‖z.snd‖^2 ≤ b}

theorem scaled_embedding_norm_sq (m : O) (N : ℝ) (hN : 0 ≤ N) :
    ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = ‖eisEmbedding m‖^2 / N := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN]

theorem physical_sample_eq_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (W : 𝓢(Joint, ℂ)) (hW : AnnularSupport a b W)
    (N : ℝ) (hN : 0 < N) (hsmall : N < b⁻¹) (m : O × O) :
    W (physicalPoint N m) = 0 := by
  by_contra h
  have hw := hW h
  change a ≤ ‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2 ∧
    ‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2 ≤ b ∧ _ at hw
  have hm : m.1 ≠ 0 := by
    intro hz
    have hh := hw.1
    rw [hz, map_zero, zero_div, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hh
    linarith
  have hl := one_le_eisenstein_norm_sq m.1 hm
  have hu := hw.2.1
  rw [scaled_embedding_norm_sq m.1 N hN.le, div_le_iff₀ hN] at hu
  have hs : b*N < 1 := by
    have hh := mul_lt_mul_of_pos_left hsmall hb
    simpa only [mul_inv_cancel₀ hb.ne'] using hh
  linarith

def cauchyWeight (m : O) : ℝ := ((1+‖eisEmbedding m‖^2)^2)⁻¹

theorem cauchyWeight_summable : Summable cauchyWeight := by
  change Summable (fun m : O => ((1+‖eisEmbedding m‖^2)^2)⁻¹)
  simpa only [one_mul] using scaled_eisenstein_cauchy_summable 1 zero_lt_one

theorem cauchyWeight_mass_le : (∑' m : O, cauchyWeight m) ≤ 4*(1+Real.pi)^2 := by
  simpa only [cauchyWeight, one_mul] using scaled_eisenstein_cauchy_small 1 zero_lt_one le_rfl

theorem physical_subunit_majorant (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) (m : O × O) :
    ‖W (physicalPoint N m)‖ ≤ (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W *
      (cauchyWeight m.1 * cauchyWeight m.2) := by
  have hn (m : O) : ‖eisEmbedding m‖^2 ≤ ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 := by
    rw [scaled_embedding_norm_sq m N hN.le, le_div_iff₀ hN]
    exact mul_le_of_le_one_right (sq_nonneg _) hN1
  have hd : (1+‖eisEmbedding m.1‖^2)^2 * (1+‖eisEmbedding m.2‖^2)^2 ≤
      (1+‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2)^2 *
        (1+‖eisEmbedding m.2 / (Real.sqrt N : ℂ)‖^2)^2 := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.1)) 2)
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.2)) 2) (by positivity) (by positivity)
  have hp := (mul_le_mul_of_nonneg_right hd (norm_nonneg (W (physicalPoint N m)))).trans
    (product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
      (eisEmbedding m.2 / (Real.sqrt N : ℂ)))
  dsimp only [cauchyWeight]
  rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using hp

theorem physical_subunit_bound (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) :
    (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤
      ((2:ℝ)^8*(4*(1+Real.pi)^2)^2) * sourceControl (Finset.Iic (8,0)) W := by
  have hg := cauchyWeight_summable
  have hp := hg.mul_of_nonneg hg (fun _ => by unfold cauchyWeight; positivity)
    (fun _ => by unfold cauchyWeight; positivity)
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*
        (cauchyWeight m.1*cauchyWeight m.2) :=
      (physical_summable W N hN).tsum_le_tsum (physical_subunit_majorant W N hN hN1)
        (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, cauchyWeight m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(4*(1+Real.pi)^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by unfold cauchyWeight; positivity))
        cauchyWeight_mass_le 2
    _ = _ := by ring

theorem annular_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W → ∀ (N : ℝ), 0 < N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  obtain ⟨S₀,C₀,hC₀,h₀⟩ := physical_lattice_bound
  let K : ℝ := (2:ℝ)^8*(4*(1+Real.pi)^2)^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : 0 < b := ha.trans hab
  refine ⟨S₀ ∪ Finset.Iic (8,0),C₀ + K*b^2,by positivity,?_⟩
  intro W hW N hN
  have hS₀ := sourceControl_mono (S := S₀) (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_left W
  have hS₁ := sourceControl_mono (S := Finset.Iic (8,0))
    (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_right W
  by_cases hN1 : 1 ≤ N
  · apply (h₀ W N hN1).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right (by positivity)) hS₀
      (sourceControl_nonneg _ _) (by positivity)
  · by_cases hs : N < b⁻¹
    · have hz : (∑' m : O × O, ‖W (physicalPoint N m)‖) = 0 := by
        calc
          _ = ∑' _m : O × O, (0:ℝ) := tsum_congr (fun m => by
            rw [physical_sample_eq_zero a b ha hb W hW N hN hs m, norm_zero])
          _ = 0 := tsum_zero
      rw [hz]
      exact mul_nonneg (mul_nonneg (by positivity) (sourceControl_nonneg _ _)) (sq_nonneg _)
    · have hBN : 1 ≤ b*N := by
        have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hs) hb.le
        simpa only [mul_inv_cancel₀ hb.ne'] using hh
      have hBN2 : 1 ≤ b^2*N^2 := by nlinarith [sq_nonneg (b*N-1)]
      calc
        _ ≤ K * sourceControl (Finset.Iic (8,0)) W :=
          physical_subunit_bound W N hN (le_of_not_ge hN1)
        _ ≤ K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W :=
          mul_le_mul_of_nonneg_left hS₁ hK.le
        _ ≤ (K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W) * (b^2*N^2) :=
          le_mul_of_one_le_right (mul_nonneg hK.le (sourceControl_nonneg _ _)) hBN2
        _ = (K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by ring
        _ ≤ (C₀+K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀.le)
              (sourceControl_nonneg _ _)) (sq_nonneg _)

theorem weighted_summable (W : 𝓢(Joint, ℂ)) (d : O × O → ℂ) (B : ℝ)
    (hd : ∀ m, ‖d m‖ ≤ B) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => d m * W (physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((physical_summable W N hN).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)

theorem annular_weighted_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W →
      ∀ (d : O × O → ℂ) (B : ℝ), 0 ≤ B → (∀ m, ‖d m‖ ≤ B) →
      ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O => d m * W (physicalPoint N m)) ∧
        ‖∑' m : O × O, d m * W (physicalPoint N m)‖ ≤ C * sourceControl S W * B * N^2 := by
  obtain ⟨S,C,hC,hbound⟩ := annular_lattice_bound a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW d B hB hd N hN
  refine ⟨weighted_summable W d B hd N hN,?_⟩
  calc
    _ ≤ ∑' m : O × O, B * ‖W (physicalPoint N m)‖ := by
      apply (norm_tsum_le_tsum_norm ((weighted_summable W d B hd N hN).norm)).trans
      apply ((weighted_summable W d B hd N hN).norm).tsum_le_tsum _
        ((physical_summable W N hN).mul_left B)
      intro m
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)
    _ = B * ∑' m : O × O, ‖W (physicalPoint N m)‖ := tsum_mul_left
    _ ≤ B * (C * sourceControl S W * N^2) := mul_le_mul_of_nonneg_left (hbound W hW N hN) hB
    _ = _ := by ring

end ProbeGramAnnularLattice

end

end OAI
end OAIOriginalModule0480

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramJointConstruction
Source SHA256: e015a207789cb04eff2db13b45812e361290c69ad021408d86f63d5414ab6d74
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0481




namespace OAI

noncomputable section
open Filter Set
open scoped Classical SchwartzMap ContDiff Topology

namespace ProbeGramJointConstruction
open ProbeGramLatticeDecay EisensteinSchwartzPoisson

def q1 (z : Joint) : ℝ := ‖z.fst‖^2
def q2 (z : Joint) : ℝ := ‖z.snd‖^2

lemma q1_smooth : ContDiff ℝ ∞ q1 :=
  (WithLp.fstL 2 ℝ ℂ ℂ).contDiff.norm_sq ℂ
lemma q2_smooth : ContDiff ℝ ∞ q2 :=
  (WithLp.sndL 2 ℝ ℂ ℂ).contDiff.norm_sq ℂ

lemma norm_sq_eq (z : Joint) : ‖z‖^2 = q1 z + q2 z :=
  WithLp.prod_norm_sq_eq_of_L2 z

def log1 (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  CompletedHeight.patchedLog a b ha (q1 z)
def log2 (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  CompletedHeight.patchedLog a b ha (q2 z)
def phase (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  log1 a b ha z - log2 a b ha z
def rootScale (a b : ℝ) (ha : 0<a) (z : Joint) : ℝ :=
  Real.exp (-(log1 a b ha z + log2 a b ha z)/2)
def amplitude (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (z : Joint) : ℂ :=
  W (q1 z)*star (W (q2 z))*Complex.exp (-((log1 a b ha z+log2 a b ha z):ℂ))

lemma patchedLog_smooth (a b : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (CompletedHeight.patchedLog a b ha) :=
  contDiff_id.add (CompletedHeight.logCorrection_smooth a b ha)
lemma log1_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (log1 a b ha) :=
  (patchedLog_smooth a b ha).comp q1_smooth
lemma log2_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (log2 a b ha) :=
  (patchedLog_smooth a b ha).comp q2_smooth
lemma phase_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (phase a b ha) :=
  (log1_smooth a b ha).sub (log2_smooth a b ha)
lemma rootScale_smooth (a b : ℝ) (ha : 0<a) : ContDiff ℝ ∞ (rootScale a b ha) :=
  (((log1_smooth a b ha).add (log2_smooth a b ha)).neg.div_const 2).exp
lemma rootScale_pos (a b : ℝ) (ha : 0<a) (z : Joint) : 0<rootScale a b ha z :=
  Real.exp_pos _
lemma amplitude_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (a b : ℝ) (ha : 0<a) :
    ContDiff ℝ ∞ (amplitude W a b ha) := by
  unfold amplitude
  have h1 := hW.comp q1_smooth
  have h2 := hW.comp q2_smooth
  have hl := (log1_smooth a b ha).add (log2_smooth a b ha)
  simpa only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_add, Complex.conjCLE_apply, Complex.star_def] using
    (h1.mul (Complex.conjCLE.contDiff.comp h2)).mul
      ((Complex.ofRealCLM.contDiff.comp hl).neg.cexp)

def rawProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint) : ℂ :=
  (W (q1 z)*(q1 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
    star (W (q2 z)*(q2 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
    paperRadialFourier U (T/(q1 z*q2 z))

def patchedProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) : ℂ :=
  amplitude W a b ha z * FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z) *
    paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z)

lemma patchedProfile_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (v T : ℝ) :
    ContDiff ℝ ∞ (patchedProfile W U a b ha v T) := by
  have h1 := amplitude_smooth W hW a b ha
  have h2 := phase_smooth a b ha
  have h3 := rootScale_smooth a b ha
  have h4 := (paperFourierRayCLM U).smooth (⊤ : ℕ∞)
  have hp : ContDiff ℝ ∞ (fun z => FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z)) := by
    unfold FourierBridge.logPhase
    exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul h2)).mul contDiff_const).cexp
  exact (h1.mul hp).mul (h4.comp (contDiff_const.mul h3))

lemma rawProfile_zero_left (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint)
    (hz : W (q1 z)=0) : rawProfile W U v T z=0 := by simp [rawProfile,hz]
lemma rawProfile_zero_right (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (v T : ℝ) (z : Joint)
    (hz : W (q2 z)=0) : rawProfile W U v T z=0 := by simp [rawProfile,hz]
lemma patchedProfile_zero_left (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) (hz : W (q1 z)=0) : patchedProfile W U a b ha v T z=0 := by
  simp [patchedProfile,amplitude,hz]
lemma patchedProfile_zero_right (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (v T : ℝ) (z : Joint) (hz : W (q2 z)=0) : patchedProfile W U a b ha v T z=0 := by
  simp [patchedProfile,amplitude,hz]

def sourceCompact (b : ℝ) : Set Joint := Metric.closedBall 0 (1+2*b)
lemma sourceCompact_isCompact (b : ℝ) : IsCompact (sourceCompact b) :=
  isCompact_closedBall _ _

lemma support_amplitude (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) :
    Function.support (amplitude W a b ha)⊆{z | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b} := by
  intro z hz
  have h1 : W (q1 z)≠0 := fun h => hz (by simp [amplitude,h])
  have h2 : W (q2 z)≠0 := fun h => hz (by simp [amplitude,h])
  exact ⟨(hs h1).1,(hs h1).2,(hs h2).1,(hs h2).2⟩

lemma annulus_subset_sourceCompact (a b : ℝ) (ha : 0<a) (hab : a<b) :
    {z : Joint | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b}⊆sourceCompact b := by
  intro z hz
  change dist z 0≤1+2*b
  rw [dist_zero_right]
  have hn := norm_sq_eq z
  have hb : 0<b := ha.trans hab
  nlinarith [norm_nonneg z, sq_nonneg (‖z‖-1),hz.2.1,hz.2.2.2]

lemma tsupport_amplitude_subset (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) :
    tsupport (amplitude W a b ha)⊆sourceCompact b := by
  exact closure_minimal ((support_amplitude W a b ha hs).trans
    (annulus_subset_sourceCompact a b ha hab)) Metric.isClosed_closedBall

lemma amplitude_hasCompactSupport (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) : HasCompactSupport (amplitude W a b ha) :=
  HasCompactSupport.of_support_subset_isCompact (sourceCompact_isCompact b)
    ((support_amplitude W a b ha hs).trans (annulus_subset_sourceCompact a b ha hab))

lemma patchedProfile_hasCompactSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    HasCompactSupport (patchedProfile W U a b ha v T) :=
  ((amplitude_hasCompactSupport W a b ha hab hs).mul_right).mul_right

lemma norm_power_pair (v x y : ℝ) (hx : 0<x) (hy : 0<y) :
    (x:ℂ)^(-1+(v:ℂ)*Complex.I)*star ((y:ℂ)^(-1+(v:ℂ)*Complex.I)) =
      Complex.exp (-((Real.log x+Real.log y):ℂ))*
        FourierBridge.logPhase (v/(2*Real.pi)) (Real.log x-Real.log y) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
  rw [←Complex.ofReal_log hx.le,←Complex.ofReal_log hy.le]
  simp only [Complex.star_def,←Complex.exp_conj,map_mul,map_add,map_neg,map_one,
    Complex.conj_ofReal,Complex.conj_I]
  unfold FourierBridge.logPhase
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  have hpi : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

lemma sqrt_reciprocal_product (T x y : ℝ) (hT : 0≤T) (hx : 0<x) (hy : 0<y) :
    Real.sqrt (T/(x*y))=Real.sqrt T*Real.exp (-(Real.log x+Real.log y)/2) := by
  have he : Real.exp (-(Real.log x+Real.log y)/2)^2=(x*y)⁻¹ := by
    rw [←Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(-(Real.log x+Real.log y)/2)=-(Real.log x+Real.log y) by ring,
      Real.exp_neg,Real.exp_add,Real.exp_log hx,Real.exp_log hy]
  have hl := Real.sq_sqrt (div_nonneg hT (mul_pos hx hy).le)
  have hr : (Real.sqrt T*Real.exp (-(Real.log x+Real.log y)/2))^2=T/(x*y) := by
    rw [mul_pow,Real.sq_sqrt hT,he,div_eq_mul_inv]
  nlinarith [Real.sqrt_nonneg (T/(x*y)),Real.sqrt_nonneg T,
    Real.exp_pos (-(Real.log x+Real.log y)/2),mul_nonneg (Real.sqrt_nonneg T)
      (Real.exp_pos (-(Real.log x+Real.log y)/2)).le]

theorem rawProfile_eq_patchedProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Icc a b)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    rawProfile W U v T z=patchedProfile W U a b ha v T z := by
  by_cases h1 : W (q1 z)=0
  · rw [rawProfile_zero_left W U v T z h1,patchedProfile_zero_left W U a b ha v T z h1]
  by_cases h2 : W (q2 z)=0
  · rw [rawProfile_zero_right W U v T z h2,patchedProfile_zero_right W U a b ha v T z h2]
  have hx := ha.trans_le (hs h1).1
  have hy := ha.trans_le (hs h2).1
  have hl1 : log1 a b ha z=Real.log (q1 z) := CompletedHeight.patchedLog_eq_log a b ha _ (hs h1)
  have hl2 : log2 a b ha z=Real.log (q2 z) := CompletedHeight.patchedLog_eq_log a b ha _ (hs h2)
  have hker : paperRadialFourier U (T/(q1 z*q2 z)) =
      paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) := by
    rw [paperRadialFourier_eq_ray]
    change paperFourierRayCLM U (Real.sqrt (T/(q1 z*q2 z))) = _
    rw [sqrt_reciprocal_product T _ _ hT hx hy]
    simp only [rootScale,hl1,hl2]
  unfold rawProfile patchedProfile amplitude phase
  rw [hker,hl1,hl2]
  simp only [star_mul]
  calc
    _ = (W (q1 z)*star (W (q2 z)))*
        ((q1 z:ℂ)^(-1+(v:ℂ)*Complex.I)*star ((q2 z:ℂ)^(-1+(v:ℂ)*Complex.I)))*
        paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) := by ring
    _ = _ := by rw [norm_power_pair v _ _ hx hy];ring

def amplitudeSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) : 𝓢(Joint,ℂ) :=
  (amplitude_hasCompactSupport W a b ha hab hs).toSchwartzMap (amplitude_smooth W hW a b ha)

@[simp] lemma amplitudeSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (z : Joint) :
    amplitudeSchwartz W a b ha hab hs hW z=amplitude W a b ha z := rfl

lemma rawProfile_smooth (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) : ContDiff ℝ ∞ (rawProfile W U v T) := by
  have he : rawProfile W U v T=patchedProfile W U a b ha v T :=
    funext (rawProfile_eq_patchedProfile W U a b ha hs v T hT)
  rw [he]
  exact patchedProfile_smooth W hW U a b ha v T

lemma support_rawProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    Function.support (rawProfile W U v T)⊆{z | a≤q1 z ∧ q1 z≤b ∧ a≤q2 z ∧ q2 z≤b} := by
  intro z hz
  have h1 : W (q1 z)≠0 := fun h => hz (rawProfile_zero_left W U v T z h)
  have h2 : W (q2 z)≠0 := fun h => hz (rawProfile_zero_right W U v T z h)
  exact ⟨(hs h1).1,(hs h1).2,(hs h2).1,(hs h2).2⟩

lemma rawProfile_hasCompactSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b) (hs : Function.support W⊆Icc a b) (v T : ℝ) :
    HasCompactSupport (rawProfile W U v T) :=
  HasCompactSupport.of_support_subset_isCompact (sourceCompact_isCompact b)
    ((support_rawProfile W U a b hs v T).trans (annulus_subset_sourceCompact a b ha hab))

def jointProfile (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) : 𝓢(Joint,ℂ) :=
  (rawProfile_hasCompactSupport W U a b ha hab hs v T).toSchwartzMap
    (rawProfile_smooth W U a b ha hs hW v T hT)

@[simp] theorem jointProfile_apply (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    jointProfile W U a b ha hab hs hW v T hT z=rawProfile W U v T z := rfl

theorem jointProfile_factorization (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) :
    jointProfile W U a b ha hab hs hW v T hT z=
      amplitude W a b ha z * FourierBridge.logPhase (v/(2*Real.pi)) (phase a b ha z) *
        paperFourierRayCLM U (Real.sqrt T*rootScale a b ha z) :=
  rawProfile_eq_patchedProfile W U a b ha hs v T hT z

theorem jointProfile_annularSupport (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) :
    ProbeGramAnnularLattice.AnnularSupport a b (jointProfile W U a b ha hab hs hW v T hT) :=
  support_rawProfile W U a b hs v T

lemma jointProfile_zero_scale (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (v : ℝ) (z : Joint) :
    jointProfile W U a b ha hab hs hW v 0 (by positivity) z=
      (W (q1 z)*(q1 z:ℂ)^(-1+(v:ℂ)*Complex.I))*
        star (W (q2 z)*(q2 z:ℂ)^(-1+(v:ℂ)*Complex.I))*paperRadialFourier U 0 := by
  simp only [jointProfile_apply,rawProfile,zero_div]

lemma jointProfile_zero_of_left_small (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) (hz : q1 z<a) :
    jointProfile W U a b ha hab hs hW v T hT z=0 := by
  apply rawProfile_zero_left
  by_contra h
  exact (not_le.mpr hz) (hs h).1

lemma jointProfile_zero_of_right_small (W : ℝ→ℂ) (U : 𝓢(ℝ,ℂ))
    (a b : ℝ) (ha : 0<a) (hab : a<b)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (v T : ℝ) (hT : 0≤T) (z : Joint) (hz : q2 z<a) :
    jointProfile W U a b ha hab hs hW v T hT z=0 := by
  apply rawProfile_zero_right
  by_contra h
  exact (not_le.mpr hz) (hs h).1

end ProbeGramJointConstruction

end

end OAI
end OAIOriginalModule0481

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramJointProfile
Source SHA256: 7e93c802f68e5b8031c8dec1d507ef34f4c306d2459329a167fb173c18e1a62c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0482





namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set FourierBridge
namespace ProbeGramJointProfile
open ProbeGramLatticeDecay EisensteinSchwartzPoisson

def rayControl (B n : ℕ) (g : 𝓢(ℝ, ℂ)) : ℝ :=
  (Finset.Iic (2*B+n,n)).sup (schwartzSeminormFamily ℝ ℝ ℂ) g

lemma rayControl_nonneg (B n : ℕ) (g : 𝓢(ℝ, ℂ)) :
    0 ≤ rayControl B n g := apply_nonneg _ _

lemma mul_derivative_bound {f g : Joint → ℂ} (n : ℕ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Joint)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hfb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C)
    (hgb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (fun y => f y * g y) x‖ ≤ 2^n*C*D := by
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ :=
      norm_iteratedFDeriv_mul_le hf hg x (by simp)
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (hfb i (Finset.mem_range_succ_iff.mp hi)) (by positivity))
        (hgb (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      norm_cast

lemma compact_derivatives {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set Joint} (hK : IsCompact K) {f : Joint → F}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i ≤ n, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ D := by
    obtain ⟨D, hD⟩ := hK.bddAbove_image
      (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.continuousOn
    exact ⟨D, fun x hx => hD (Set.mem_image_of_mem _ hx)⟩
  choose D hD using hb
  refine ⟨1 + ∑ i ∈ Finset.range (n+1), |D i|, by
    have hn : 0 ≤ ∑ i ∈ Finset.range (n+1), |D i| := by positivity
    linarith, ?_⟩
  intro i hi x hx
  have hs : |D i| ≤ ∑ j ∈ Finset.range (n+1), |D j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_range.mpr (by omega))
  exact (hD i x hx).trans ((le_abs_self _).trans (by linarith))

lemma compact_positive_margin {K : Set Joint} (hK : IsCompact K)
    {h : Joint → ℝ} (hc : Continuous h) (hp : ∀ x ∈ K, 0 < h x) :
    ∃ m : ℝ, 0 < m ∧ m ≤ 1 ∧ ∀ x ∈ K, m ≤ h x := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hm⟩ := hK.exists_isMinOn hne hc.continuousOn
    exact ⟨min 1 (h x), lt_min zero_lt_one (hp x hx), min_le_left _ _,
      fun y hy => (min_le_right _ _).trans (hm hy)⟩
  · exact ⟨1, zero_lt_one, le_rfl, fun x hx => False.elim (hne ⟨x,hx⟩)⟩

lemma scaled_argument_derivative {h : Joint → ℝ} (hh : ContDiff ℝ ∞ h)
    {D R : ℝ} (hD : 1 ≤ D) (hR : 0 ≤ R) (i : ℕ) (hi : 1 ≤ i)
    (x : Joint) (hb : ‖iteratedFDeriv ℝ i h x‖ ≤ D) :
    ‖iteratedFDeriv ℝ i (fun y => R*h y) x‖ ≤ (D^2*(1+R))^i := by
  have he : iteratedFDeriv ℝ i (fun y => R*h y) x = R • iteratedFDeriv ℝ i h x :=
    by simpa only [smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (a := R) (i := i) (x := x)
        ((hh.of_le (by exact_mod_cast le_top)).contDiffAt))
  rw [he, norm_smul, Real.norm_of_nonneg hR]
  have hDi : D ≤ D^i := by
    calc D = D^1 := by simp
         _ ≤ D^i := pow_le_pow_right₀ hD hi
  have hRi : R ≤ (1+R)^i := by
    calc R ≤ 1+R := by linarith
         _ = (1+R)^1 := by simp
         _ ≤ (1+R)^i := pow_le_pow_right₀ (by linarith) hi
  calc
    R * ‖iteratedFDeriv ℝ i h x‖ ≤ R*D := mul_le_mul_of_nonneg_left hb hR
    _ ≤ (1+R)^i * D^i := mul_le_mul hRi hDi (by linarith) (by positivity)
    _ ≤ (D^2*(1+R))^i := by
      rw [mul_pow, pow_two, mul_pow]
      have hhD : 1 ≤ D^i := one_le_pow₀ hD
      nlinarith [mul_nonneg (show 0 ≤ (1+R)^i by positivity)
        (show 0 ≤ (D^i)^2-D^i by nlinarith)]

lemma normalized_phase_derivative (v x : ℝ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (logPhase (v/(2*Real.pi))) x‖ = |v|^i := by
  rw [JointLogSeparation.logPhase_iteratedFDeriv_norm, norm_div,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi), Real.norm_eq_abs]
  congr 1
  field_simp

lemma phase_derivative_bound {φ : Joint → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {D : ℝ} (hD : 1 ≤ D) (n j : ℕ) (hj : j ≤ n)
    (x : Joint) (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i φ x‖ ≤ D) (v : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y => logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
      (n.factorial : ℝ)*D^n*(1+|v|)^n := by
  have hcomp := norm_iteratedFDeriv_comp_le (JointLogSeparation.logPhase_temperate (v/(2*Real.pi))).1
    hφ (n := j) (by simp) x (C := (1+|v|)^n) (D := D)
  have hc : ∀ i ≤ j, ‖iteratedFDeriv ℝ i (logPhase (v/(2*Real.pi))) (φ x)‖ ≤
      (1+|v|)^n := by
    intro i hi
    rw [normalized_phase_derivative]
    exact (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |v| ≤ 1+|v|) i).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg v]) (hi.trans hj))
  have hd : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i φ x‖ ≤ D^i := by
    intro i hi hij
    exact (hb i (hij.trans hj)).trans (by
      calc D = D^1 := by simp
           _ ≤ D^i := pow_le_pow_right₀ hD hi)
  calc
    _ ≤ (j.factorial : ℝ)*(1+|v|)^n*D^j := hcomp hc hd
    _ ≤ (n.factorial : ℝ)*(1+|v|)^n*D^n := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) (by positivity))
        (pow_le_pow_right₀ hD hj) (by positivity) (by positivity)
    _ = _ := by ring

lemma kernel_derivative_bound {h : Joint → ℝ} (hh : ContDiff ℝ ∞ h)
    {D m R : ℝ} (hD : 1 ≤ D) (hm : 0 < m) (hm1 : m ≤ 1) (hR : 0 ≤ R)
    (B n j : ℕ) (hj : j ≤ n) (x : Joint)
    (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i h x‖ ≤ D) (hl : m ≤ h x)
    (g : 𝓢(ℝ, ℂ)) :
    ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (((n.factorial : ℝ)*2^(2*B+n)*(D^2)^n/m^(2*B+n))*rayControl B n g) /
        (1+R)^(2*B) := by
  have hu : 0 ≤ R*h x := mul_nonneg hR (hm.le.trans hl)
  have hden : 0 < (1+R*h x)^(2*B+n) := by positivity
  have harg : ContDiff ℝ ∞ (fun y => R*h y) := contDiff_const.mul hh
  have hcomp : ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g/(1+R*h x)^(2*B+n))*
        (D^2*(1+R))^j := by
    apply norm_iteratedFDeriv_comp_le (g.smooth ⊤) harg (by simp) x
    · intro i hi
      apply (le_div_iff₀ hden).mpr
      have hd := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (2*B+n,n)) (k := 2*B+n) (n := i) le_rfl (hi.trans hj) g (R*h x)
      change (1+‖R*h x‖)^(2*B+n) * ‖iteratedFDeriv ℝ i g (R*h x)‖ ≤
        2^(2*B+n)*rayControl B n g at hd
      rw [Real.norm_of_nonneg hu] at hd
      simpa only [mul_comm] using hd
    · intro i hi hij
      exact scaled_argument_derivative hh hD hR i hi x (hb i (hij.trans hj))
  have hscale : m*(1+R) ≤ 1+R*h x := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hl)]
  have habs := FourierBridge.derivative_scale_absorption R (R*h x) m D
    (2^(2*B+n)*rayControl B n g) (2*B) n j hR hm (by linarith)
    (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)) hu hscale hj
  have hbound : m^(2*B+n)*(1+R)^(2*B)*
      ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
      (n.factorial : ℝ)*(2^(2*B+n)*rayControl B n g)*(D^2)^n := by
    calc
      _ ≤ m^(2*B+n)*(1+R)^(2*B)*
          ((j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g/(1+R*h x)^(2*B+n))*
            (D^2*(1+R))^j) := mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ ≤ (j.factorial : ℝ)*(2^(2*B+n)*rayControl B n g)*(D^2)^j := habs
      _ ≤ _ := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj)
            (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)))
          (pow_le_pow_right₀ (one_le_pow₀ hD) hj) (by positivity)
          (mul_nonneg (by positivity) (mul_nonneg (by positivity) (rayControl_nonneg _ _ _)))
  apply (le_div_iff₀ (by positivity : 0 < (1+R)^(2*B))).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < m^(2*B+n))).mpr
  convert hbound using 1 <;> ring

def amplitudeControl (n : ℕ) (A : 𝓢(Joint, ℂ)) : ℝ :=
  (Finset.Iic (0,n)).sup (schwartzSeminormFamily ℝ Joint ℂ) A

lemma amplitudeControl_nonneg (n : ℕ) (A : 𝓢(Joint, ℂ)) :
    0 ≤ amplitudeControl n A := apply_nonneg _ _

lemma amplitude_derivative_bound (n i : ℕ) (hi : i ≤ n)
    (A : 𝓢(Joint, ℂ)) (x : Joint) :
    ‖iteratedFDeriv ℝ i A x‖ ≤ amplitudeControl n A := by
  have hp : schwartzSeminormFamily ℝ Joint ℂ (0, i) ≤
      (Finset.Iic (0,n)).sup (schwartzSeminormFamily ℝ Joint ℂ) :=
    Finset.le_sup (Finset.mem_Iic.mpr ⟨le_rfl, hi⟩)
  have hz : ‖iteratedFDeriv ℝ i A x‖ ≤ SchwartzMap.seminorm ℝ 0 i A := by
    simpa using SchwartzMap.le_seminorm ℝ 0 i A x
  exact hz.trans (Seminorm.le_def.mp hp A)

theorem compact_profile_seminorm
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (g : 𝓢(ℝ, ℂ)) (v R : ℝ), 0 ≤ R →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x)) →
      SchwartzMap.seminorm ℝ k n F ≤
        C*amplitudeControl n A*rayControl B n g*(1+|v|)^n/(1+R)^(2*B) := by
  obtain ⟨Dφ, hDφ, hbφ⟩ := compact_derivatives hK hφ n
  obtain ⟨Dh, hDh, hbh⟩ := compact_derivatives hK hh n
  obtain ⟨m, hm, hm1, hml⟩ := compact_positive_margin hK hh.continuous hhpos
  obtain ⟨L0, hL0⟩ := hK.bddAbove_image (continuous_norm.continuousOn : ContinuousOn (fun x : Joint => ‖x‖) K)
  let D := max Dφ Dh
  let L := max 1 L0
  have hD : 1 ≤ D := hDφ.trans (le_max_left _ _)
  have hL : 1 ≤ L := le_max_left _ _
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let Cg : ℝ := (n.factorial : ℝ)*2^(2*B+n)*(D^2)^n/m^(2*B+n)
  have hCg : 0 < Cg := by dsimp [Cg]; positivity
  let Cp : ℝ := (n.factorial : ℝ)*D^n
  have hCp : 0 < Cp := by dsimp [Cp]; positivity
  refine ⟨L^k*2^n*2^n*Cp*Cg, by positivity, ?_⟩
  intro A hA g v R hR F hF
  have hp : ContDiff ℝ ∞ (fun y => logPhase (v/(2*Real.pi)) (φ y)) :=
    (JointLogSeparation.logPhase_temperate _).1.comp hφ
  have hg : ContDiff ℝ ∞ (fun y => g (R*h y)) :=
    (g.smooth ⊤).comp (contDiff_const.mul hh)
  have hFfun : (F : Joint → ℂ) =
      fun x => A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x) := funext hF
  have hFs : tsupport (F : Joint → ℂ) ⊆ K := by
    rw [hFfun]
    exact (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hA
  have hAn := amplitudeControl_nonneg n A
  have hgn := rayControl_nonneg B n g
  have hden : 0 < (1+R)^(2*B) := by positivity
  apply SchwartzMap.seminorm_le_bound ℝ k n F (by positivity)
  intro x
  by_cases hx : x ∈ K
  · have hxb : ‖x‖ ≤ L := (hL0 (mem_image_of_mem _ hx)).trans (le_max_right _ _)
    have hpbd (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
          Cp*(1+|v|)^n :=
      phase_derivative_bound hφ hD n j hj x
        (fun i hi => (hbφ i hi x hx).trans (le_max_left _ _)) v
    have hgbd (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => g (R*h y)) x‖ ≤
          Cg*rayControl B n g/(1+R)^(2*B) :=
      kernel_derivative_bound hh hD hm hm1 hR B n j hj x
        (fun i hi => (hbh i hi x hx).trans (le_max_right _ _)) (hml x hx) g
    have hap (j : ℕ) (hj : j ≤ n) :
        ‖iteratedFDeriv ℝ j (fun y => A y * logPhase (v/(2*Real.pi)) (φ y)) x‖ ≤
          2^n*amplitudeControl n A*(Cp*(1+|v|)^n) := by
      calc
        _ ≤ 2^j*amplitudeControl n A*(Cp*(1+|v|)^n) :=
          mul_derivative_bound j (A.smooth ⊤) hp x hAn (by positivity)
            (fun i hi => amplitude_derivative_bound n i (hi.trans hj) A x)
            (fun i hi => hpbd i (hi.trans hj))
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hAn) (by positivity)
    have hb := mul_derivative_bound n ((A.smooth ⊤).mul hp) hg x
      (C := 2^n*amplitudeControl n A*(Cp*(1+|v|)^n))
      (D := Cg*rayControl B n g/(1+R)^(2*B)) (by positivity) (by positivity) hap hgbd
    rw [hFfun]
    calc
      _ ≤ L^k * (2^n*(2^n*amplitudeControl n A*(Cp*(1+|v|)^n))*
          (Cg*rayControl B n g/(1+R)^(2*B))) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxb _) hb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ n (F : Joint → ℂ) x = 0 := by
      apply Function.notMem_support.mp
      intro hx'
      exact hx (hFs ((support_iteratedFDeriv_subset n) hx'))
    rw [hz, norm_zero, mul_zero]
    positivity

lemma amplitudeControl_mono {n N : ℕ} (hn : n ≤ N) (A : 𝓢(Joint, ℂ)) :
    amplitudeControl n A ≤ amplitudeControl N A := by
  exact Seminorm.le_def.mp (Finset.sup_mono (by
    intro p hp
    exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp) ⟨le_rfl, hn⟩))) A

lemma rayControl_mono (B : ℕ) {n N : ℕ} (hn : n ≤ N) (g : 𝓢(ℝ, ℂ)) :
    rayControl B n g ≤ rayControl B N g := by
  exact Seminorm.le_def.mp (Finset.sup_mono (by
    intro p hp
    exact Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp hp) ⟨by omega, hn⟩))) g

def heightOrder (H : Finset (ℕ × ℕ)) : ℕ := H.sup Prod.snd

theorem compact_profile_finite
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (g : 𝓢(ℝ, ℂ)) (v R : ℝ), 0 ≤ R →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) * g (R*h x)) →
      sourceControl H F ≤
        C*amplitudeControl (heightOrder H) A*rayControl B (heightOrder H) g*
          (1+|v|)^(heightOrder H)/(1+R)^(2*B) := by
  have hc (p : ℕ × ℕ) := compact_profile_seminorm hK hφ hh hhpos B p.1 p.2
  choose C hC hbound using hc
  let D : ℝ := 1+∑ p ∈ H, C p
  have hD : 0 < D := by
    have hs : 0 ≤ ∑ p ∈ H, C p := Finset.sum_nonneg (fun p _ => (hC p).le)
    dsimp [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro A hA g v R hR F hF
  have hAn := amplitudeControl_nonneg (heightOrder H) A
  have hgn := rayControl_nonneg B (heightOrder H) g
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro p hp
  have hn : p.2 ≤ heightOrder H := Finset.le_sup hp
  have hCD : C p ≤ D := by
    have hs := Finset.single_le_sum (fun p _ => (hC p).le) hp
    dsimp [D]
    linarith
  exact (hbound p A hA g v R hR F hF).trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul
    · exact mul_le_mul
        (mul_le_mul hCD (amplitudeControl_mono hn A)
          (amplitudeControl_nonneg _ _) hD.le)
        (rayControl_mono B hn g) (rayControl_nonneg _ _ _) (by positivity)
    · exact pow_le_pow_right₀ (by linarith [abs_nonneg v]) hn
    · positivity
    · positivity)

lemma sqrt_decay_absorption (T : ℝ) (hT : 0 ≤ T) (B : ℕ) :
    (1+T)^B ≤ (1+Real.sqrt T)^(2*B) := by
  have hbase : 1+T ≤ (1+Real.sqrt T)^2 := by
    nlinarith [Real.sq_sqrt hT, Real.sqrt_nonneg T]
  calc
    _ ≤ ((1+Real.sqrt T)^2)^B := pow_le_pow_left₀ (by positivity) hbase B
    _ = _ := by rw [pow_mul]

theorem compact_fourier_profile_finite
    {K : Set Joint} (hK : IsCompact K) {φ h : Joint → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hhpos : ∀ x ∈ K, 0 < h x) (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (A : 𝓢(Joint, ℂ)), tsupport (A : Joint → ℂ) ⊆ K →
      ∀ (U : 𝓢(ℝ, ℂ)) (v T : ℝ), 0 ≤ T →
      ∀ (F : 𝓢(Joint, ℂ)),
      (∀ x, F x = A x * logPhase (v/(2*Real.pi)) (φ x) *
        paperFourierRayCLM U (Real.sqrt T*h x)) →
      sourceControl H F ≤ C*amplitudeControl (heightOrder H) A*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^(heightOrder H)/(1+T)^B := by
  obtain ⟨D, hD, hbound⟩ := compact_profile_finite hK hφ hh hhpos B H
  obtain ⟨S, E, hE, hEbound⟩ := schwartzCLM_finite_seminorm_control
    paperFourierRayCLM (Finset.Iic (2*B+heightOrder H,heightOrder H))
  refine ⟨S, D*E, by positivity, ?_⟩
  intro A hA U v T hT F hF
  have hAn := amplitudeControl_nonneg (heightOrder H) A
  have hUn : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := apply_nonneg _ _
  have hg := hEbound U
  change rayControl B (heightOrder H) (paperFourierRayCLM U) ≤
    E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U at hg
  calc
    _ ≤ D*amplitudeControl (heightOrder H) A*
        rayControl B (heightOrder H) (paperFourierRayCLM U)*
        (1+|v|)^(heightOrder H)/(1+Real.sqrt T)^(2*B) :=
      hbound A hA (paperFourierRayCLM U) v (Real.sqrt T) (Real.sqrt_nonneg _) F hF
    _ ≤ D*amplitudeControl (heightOrder H) A*
        (E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        (1+|v|)^(heightOrder H)/(1+Real.sqrt T)^(2*B) := by
      gcongr
    _ ≤ D*amplitudeControl (heightOrder H) A*
        (E*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)*
        (1+|v|)^(heightOrder H)/(1+T)^B :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (sqrt_decay_absorption T hT B)
    _ = _ := by ring

open ProbeGramJointConstruction

theorem jointProfile_homogeneous (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W)
        (U : 𝓢(ℝ, ℂ)) (v T : ℝ) (hT : 0 ≤ T),
      sourceControl H (jointProfile W U a b ha hab hs hW v T hT) ≤
        C*amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW)*
          S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*
          (1+|v|)^(heightOrder H)/(1+T)^B := by
  obtain ⟨S, C, hC, hb⟩ := compact_fourier_profile_finite
    (sourceCompact_isCompact b) (phase_smooth a b ha) (rootScale_smooth a b ha)
    (fun z _ => rootScale_pos a b ha z) B H
  refine ⟨S, C, hC, ?_⟩
  intro W hs hW U v T hT
  exact hb (amplitudeSchwartz W a b ha hab hs hW)
    (tsupport_amplitude_subset W a b ha hab hs) U v T hT
    (jointProfile W U a b ha hab hs hW v T hT)
    (jointProfile_factorization W U a b ha hab hs hW v T hT)

theorem jointProfile_uniform_degree (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (B : ℕ) (H : Finset (ℕ × ℕ)) :
    ∃ (J : ℕ) (S : Finset (ℕ × ℕ)),
      ∀ (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W),
      ∃ C : ℝ, 0 < C ∧ ∀ (U : 𝓢(ℝ, ℂ)) (v T : ℝ) (hT : 0 ≤ T),
        sourceControl H (jointProfile W U a b ha hab hs hW v T hT) ≤
          C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J/(1+T)^B := by
  obtain ⟨S, C, hC, hb⟩ := jointProfile_homogeneous a b ha hab B H
  refine ⟨heightOrder H, S, ?_⟩
  intro W hs hW
  let A := amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW)
  have hA : 0 ≤ A := amplitudeControl_nonneg _ _
  refine ⟨C*(1+A), by positivity, ?_⟩
  intro U v T hT
  have hU : 0 ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := apply_nonneg _ _
  exact (hb W hs hW U v T hT).trans (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by dsimp [A]; linarith :
        amplitudeControl (heightOrder H) (amplitudeSchwartz W a b ha hab hs hW) ≤ 1+A) hC.le) hU)

end ProbeGramJointProfile

end

end OAI
end OAIOriginalModule0482

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramPeriodicPoisson
Source SHA256: 681a2be922084dfcd5900dcd733d3512b265758ae7ff8fdff60cb5a7fb2114d3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0483




namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramPeriodicPoisson

abbrev Joint := WithLp 2 (ℂ × ℂ)

def point (x y : ℂ) : Joint := WithLp.toLp 2 (x, y)

def embeddingPair (m : ActualEisensteinCubic.O × ActualEisensteinCubic.O) : Joint :=
  point (ConcreteTraceCRT.eisEmbedding m.1) (ConcreteTraceCRT.eisEmbedding m.2)

@[simp] theorem norm_point_sq (x y : ℂ) :
    ‖point x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

def leftInjection : ℂ →L[ℝ] Joint :=
  (((WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm.toLinearMap).comp
    (LinearMap.inl ℝ ℂ ℂ)).toContinuousLinearMap

def rightInjection : ℂ →L[ℝ] Joint :=
  (((WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm.toLinearMap).comp
    (LinearMap.inr ℝ ℂ ℂ)).toContinuousLinearMap

@[simp] theorem point_eq_add (x y : ℂ) :
    point x y = leftInjection x + rightInjection y := by
  change WithLp.toLp 2 (x,y) = WithLp.toLp 2 (x,0) + WithLp.toLp 2 (0,y)
  rw [← WithLp.toLp_add]
  simp

theorem slice_isometry (y : ℂ) : Isometry (fun x : ℂ => point x y) := by
  apply Isometry.of_dist_eq
  intro x z
  simp only [dist_eq_norm, point_eq_add, add_sub_add_right_eq_sub, ← map_sub]
  exact WithLp.norm_toLp_fst 2 ℂ ℂ (x-z)

theorem slice_temperate (y : ℂ) :
    (fun x : ℂ => point x y).HasTemperateGrowth := by
  simp only [point_eq_add]
  fun_prop

def leftSlice (W : 𝓢(Joint, ℂ)) (y : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (slice_temperate y)
    (slice_isometry y).antilipschitzWith W

@[simp] theorem leftSlice_apply (W : 𝓢(Joint, ℂ)) (y x : ℂ) :
    leftSlice W y x = W (point x y) := rfl

theorem fourier_joint_eq_iterated (f : Joint → ℂ) (hf : Integrable f) (ξ η : ℂ) :
    𝓕 f (point ξ η) =
      𝓕 (fun x : ℂ => 𝓕 (fun y : ℂ => f (point x y)) η) ξ := by
  let w : Joint := point ξ η
  let G : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z w) • f z
  have hG : Integrable G := (Real.fourierIntegral_convergent_iff w).mpr hf
  have hGp : Integrable (fun z : ℂ × ℂ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℂ ℂ).integrable_comp_of_integrable hG
  calc
    𝓕 f (point ξ η) = ∫ z : Joint, G z := rfl
    _ = ∫ z : ℂ × ℂ, G (WithLp.toLp 2 z) :=
      ((WithLp.volume_preserving_toLp ℂ ℂ).integral_comp
        (MeasurableEquiv.toLp 2 (ℂ × ℂ)).measurableEmbedding G).symm
    _ = ∫ x : ℂ, ∫ y : ℂ, G (WithLp.toLp 2 (x, y)) := integral_prod _ hGp
    _ = _ := by
      simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          simp only [G, w, point, WithLp.prod_inner_apply,
            neg_add, Real.fourierChar.map_add_eq_mul, Circle.smul_def, smul_eq_mul,
            Circle.coe_mul, mul_assoc]

def partialFourier (W : 𝓢(Joint, ℂ)) (η x : ℂ) : ℂ :=
  𝓕 (fun y : ℂ => W (point x y)) η

def planeMajorant (y : ℂ) : ℝ := ((1 + ‖y‖ ^ 2) ^ 2)⁻¹

theorem planeMajorant_integrable : Integrable planeMajorant := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume)
    (r := 4) (by norm_num)
  change Integrable (fun y : ℂ => ((1 + ‖y‖ ^ 2) ^ 2)⁻¹)
  convert h using 1
  funext y
  rw [show -(4:ℝ)/2 = -(2:ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_two]

def majorantConstant (W : 𝓢(Joint, ℂ)) : ℝ :=
  SchwartzMap.seminorm ℝ 0 0 W + 2 * SchwartzMap.seminorm ℝ 2 0 W +
    SchwartzMap.seminorm ℝ 4 0 W

theorem norm_le_planeMajorant (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ‖W (point x y)‖ ≤ majorantConstant W * planeMajorant y := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ W (point x y)
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ W 2 (point x y)
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ W 4 (point x y)
  have hy : ‖y‖^2 ≤ ‖point x y‖^2 := by rw [norm_point_sq]; exact le_add_of_nonneg_left (sq_nonneg _)
  have hy4 : ‖y‖^4 ≤ ‖point x y‖^4 := by nlinarith [sq_nonneg (‖x‖^2)]
  have hm2 := mul_le_mul_of_nonneg_right hy (norm_nonneg (W (point x y)))
  have hm4 := mul_le_mul_of_nonneg_right hy4 (norm_nonneg (W (point x y)))
  rw [planeMajorant, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  dsimp [majorantConstant]
  nlinarith

theorem partialFourier_continuous (W : 𝓢(Joint, ℂ)) (η : ℂ) :
    Continuous (partialFourier W η) := by
  change Continuous (fun x : ℂ => ∫ y : ℂ,
    Real.fourierChar (-inner ℝ y η) • W (point x y))
  apply continuous_of_dominated (bound := fun y => majorantConstant W * planeMajorant y)
  · intro x
    exact ((by fun_prop : Continuous (fun y : ℂ => Real.fourierChar (-inner ℝ y η))).smul
      (W.continuous.comp (show Continuous (fun y : ℂ => point x y) from by
        simp only [point_eq_add]; fun_prop))).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul] using
        norm_le_planeMajorant W x y
  · exact planeMajorant_integrable.const_mul _
  · exact Eventually.of_forall fun y =>
      continuous_const.smul (W.continuous.comp (slice_isometry y).continuous)

theorem partialFourier_integrable (W : 𝓢(Joint, ℂ)) (η : ℂ) :
    Integrable (partialFourier W η) := by
  let G : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z.snd η) • W z
  have hG : Integrable G := W.integrable.norm.mono'
    (by fun_prop : Continuous G).aestronglyMeasurable
    (Eventually.of_forall fun z => by
      simp only [G, Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      exact le_rfl)
  have hGp : Integrable (fun z : ℂ × ℂ => G (WithLp.toLp 2 z)) :=
    (WithLp.volume_preserving_toLp ℂ ℂ).integrable_comp_of_integrable hG
  change Integrable (fun x : ℂ => ∫ y : ℂ,
    Real.fourierChar (-inner ℝ y η) • W (point x y))
  exact hGp.integral_prod_left

def partialFourierSchwartz (W : 𝓢(Joint, ℂ)) (η : ℂ) : 𝓢(ℂ, ℂ) :=
  𝓕⁻ (leftSlice (𝓕 W) η)

theorem partialFourierSchwartz_apply (W : 𝓢(Joint, ℂ)) (η x : ℂ) :
    partialFourierSchwartz W η x = partialFourier W η x := by
  have heq : 𝓕 (partialFourier W η) = (leftSlice (𝓕 W) η : ℂ → ℂ) := by
    funext ξ
    change 𝓕 (fun x : ℂ => 𝓕 (fun y : ℂ => W (point x y)) η) ξ = _
    rw [← fourier_joint_eq_iterated W W.integrable ξ η]
    exact (congrFun (SchwartzMap.fourier_coe W) (point ξ η)).symm
  have hi : Integrable (𝓕 (partialFourier W η)) := by
    rw [heq]
    exact (leftSlice (𝓕 W) η).integrable
  change (𝓕⁻ (leftSlice (𝓕 W) η)) x = _
  rw [congrFun (SchwartzMap.fourierInv_coe (leftSlice (𝓕 W) η)) x, ← heq]
  exact (partialFourier_integrable W η).fourierInv_fourier_eq hi
    (partialFourier_continuous W η).continuousAt

theorem fourier_partialFourierSchwartz (W : 𝓢(Joint, ℂ)) (ξ η : ℂ) :
    𝓕 (partialFourierSchwartz W η) ξ = (𝓕 W) (point ξ η) := by
  simp [partialFourierSchwartz]

theorem jointCLM_finite_seminorm_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : 𝓢(Joint, ℂ) →L[ℝ] 𝓢(E, ℂ)) (S : Finset (ℕ × ℕ)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(Joint, ℂ),
      S.sup (schwartzSeminormFamily ℝ E ℂ) (T W) ≤
        C * s.sup (schwartzSeminormFamily ℝ Joint ℂ) W := by
  let q : Seminorm ℝ 𝓢(Joint, ℂ) :=
    (S.sup (schwartzSeminormFamily ℝ E ℂ)).comp T.toLinearMap
  have hq : Continuous q :=
    (((schwartz_withSeminorms ℝ E ℂ).finset_sups).continuous_seminorm S).comp T.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Joint ℂ) q hq
  refine ⟨s, C, ?_, ?_⟩
  · exact_mod_cast (pos_iff_ne_zero.mpr hC : 0 < C)
  · intro W
    exact Seminorm.le_def.mp hbound W

def productDecayConstant (W : 𝓢(Joint, ℂ)) : ℝ :=
  2 ^ (8:ℕ) * (Finset.Iic (8,0)).sup (schwartzSeminormFamily ℝ Joint ℂ) W

theorem product_decay (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ((1+‖x‖^2)^2 * (1+‖y‖^2)^2) * ‖W (point x y)‖ ≤ productDecayConstant W := by
  have hx := WithLp.norm_fst_le ℂ (point x y)
  have hy := WithLp.norm_snd_le ℂ (point x y)
  change ‖x‖ ≤ ‖point x y‖ at hx
  change ‖y‖ ≤ ‖point x y‖ at hy
  have hx2 : 1+‖x‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hy2 : 1+‖y‖^2 ≤ (1+‖point x y‖)^2 := by nlinarith [norm_nonneg (point x y), norm_nonneg x, norm_nonneg y]
  have hpow : (1+‖x‖^2)^2 * (1+‖y‖^2)^2 ≤ (1+‖point x y‖)^8 := by
    calc
      _ ≤ ((1+‖point x y‖)^2)^2 * ((1+‖point x y‖)^2)^2 := by gcongr
      _ = _ := by ring
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (8,0)) (k := 8) (n := 0) le_rfl le_rfl W (point x y)
  simp only [norm_iteratedFDeriv_zero] at h
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans h

theorem norm_le_product_majorant (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    ‖W (point x y)‖ ≤ productDecayConstant W * (planeMajorant x * planeMajorant y) := by
  rw [planeMajorant, planeMajorant, ← mul_inv, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm] using product_decay W x y

theorem planeMajorant_eisenstein_summable :
    Summable (fun m : ActualEisensteinCubic.O =>
      planeMajorant (ConcreteTraceCRT.eisEmbedding m)) := by
  have hs := CubicEisenstein.summable_embedding_rpow (-4) (by norm_num)
  rw [← Finset.summable_compl_iff (s := ({0} : Finset ActualEisensteinCubic.O))]
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    (hs.subtype (fun m : ActualEisensteinCubic.O => m ∉ ({0} : Finset _)))
  intro m
  have hm : m.val ≠ 0 := by simpa using m.property
  have hn : 0 < ‖ConcreteTraceCRT.eisEmbedding m.val‖ := norm_pos_iff.mpr
    (ConcreteTraceCRT.eisEmbedding_ne_zero hm)
  change ((1+‖ConcreteTraceCRT.eisEmbedding m.val‖^2)^2)⁻¹ ≤
    ‖ConcreteTraceCRT.eisEmbedding m.val‖ ^ (-4:ℝ)
  rw [show (-4:ℝ) = -(4:ℝ) by rfl, Real.rpow_neg hn.le, Real.rpow_ofNat]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg (‖ConcreteTraceCRT.eisEmbedding m.val‖^2)]

theorem joint_eisenstein_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
      ‖W (embeddingPair m)‖) := by
  have hs := planeMajorant_eisenstein_summable.mul_of_nonneg
    planeMajorant_eisenstein_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (hs.mul_left (productDecayConstant W))
  intro m
  exact norm_le_product_majorant W _ _

theorem joint_weighted_summable {R : Type*} (q : ActualEisensteinCubic.O → R)
    (a : R × R → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B) (W : 𝓢(Joint, ℂ)) :
    Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
      a (q m.1,q m.2) * W (embeddingPair m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((joint_eisenstein_summable_norm W).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)

open scoped LineDeriv

theorem leftSlice_lineDeriv (F : 𝓢(Joint, ℂ)) (η v : ℂ) :
    ∂_{v} (leftSlice F η) = leftSlice (∂_{leftInjection v} F) η := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, leftSlice_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hd : HasFDerivAt (fun x : ℂ => point x η) leftInjection x := by
    simp only [point_eq_add]
    exact leftInjection.hasFDerivAt.add_const _
  have hc := (F.hasFDerivAt (point x η)).comp x hd
  change fderiv ℝ ((F : Joint → ℂ) ∘ (fun y => point y η)) x v = _
  rw [hc.fderiv]
  rfl

theorem norm_inverse_lineDeriv (g : 𝓢(ℂ, ℂ)) (v x : ℂ) :
    ‖(𝓕⁻ (∂_{v} g)) x‖ = (2 * Real.pi) * |inner ℝ x v| * ‖(𝓕⁻ g) x‖ := by
  have ht : (fun u : ℂ => inner ℝ u v).HasTemperateGrowth := by fun_prop
  have hc : ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [SchwartzMap.fourierInv_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply ht,
    norm_smul]
  rw [hc]
  simp only [Real.norm_eq_abs, mul_assoc]

theorem inner_sq_mul_norm_inverse_le (g : 𝓢(ℂ, ℂ)) (v x : ℂ) :
    (inner ℝ x v)^2 * ‖(𝓕⁻ g) x‖ ≤ ‖(𝓕⁻ (∂_{v} (∂_{v} g))) x‖ := by
  rw [norm_inverse_lineDeriv, norm_inverse_lineDeriv]
  have hp : 1 ≤ (2 * Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  calc
    _ ≤ ((2 * Real.pi)^2 * (inner ℝ x v)^2) * ‖(𝓕⁻ g) x‖ :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg _) hp) (norm_nonneg _)
    _ = _ := by rw [← sq_abs (inner ℝ x v)]; ring

theorem norm_sq_mul_norm_inverse_le (g : 𝓢(ℂ, ℂ)) (x : ℂ) :
    ‖x‖^2 * ‖(𝓕⁻ g) x‖ ≤
      ‖(𝓕⁻ (∂_{(1:ℂ)} (∂_{(1:ℂ)} g))) x‖ +
      ‖(𝓕⁻ (∂_{Complex.I} (∂_{Complex.I} g))) x‖ := by
  have h1 := inner_sq_mul_norm_inverse_le g 1 x
  have hi := inner_sq_mul_norm_inverse_le g Complex.I x
  have he : (inner ℝ x (1:ℂ))^2 + (inner ℝ x Complex.I)^2 = ‖x‖^2 := by
    rw [Complex.sq_norm]
    simp [Complex.inner, Complex.normSq_apply, sq]
  rw [← he, add_mul]
  exact add_le_add h1 hi

theorem norm_inverse_leftSlice_le (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
      productDecayConstant F * planeMajorant η * ∫ y : ℂ, planeMajorant y := by
  have hb : Integrable (fun y : ℂ =>
      productDecayConstant F * planeMajorant η * planeMajorant y) :=
    planeMajorant_integrable.const_mul _
  have h := norm_integral_le_of_norm_le
    (f := fun y : ℂ => Real.fourierChar (inner ℝ y x) • leftSlice F η y) hb
    (Eventually.of_forall fun y => by
      simpa only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul,
        leftSlice_apply, mul_left_comm, mul_assoc, mul_comm] using norm_le_product_majorant F y η)
  rw [congrFun (SchwartzMap.fourierInv_coe (leftSlice F η)) x, Real.fourierInv_eq]
  simpa only [integral_const_mul] using h

def leftSecondReal (F : 𝓢(Joint, ℂ)) : 𝓢(Joint, ℂ) :=
  ∂_{leftInjection (1:ℂ)} (∂_{leftInjection (1:ℂ)} F)

def leftSecondImag (F : 𝓢(Joint, ℂ)) : 𝓢(Joint, ℂ) :=
  ∂_{leftInjection Complex.I} (∂_{leftInjection Complex.I} F)

def sliceIntegralBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  productDecayConstant F * ∫ y : ℂ, planeMajorant y

def firstDecayBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  sliceIntegralBound F + sliceIntegralBound (leftSecondReal F) +
    sliceIntegralBound (leftSecondImag F)

def secondDecayBound (F : 𝓢(Joint, ℂ)) : ℝ :=
  firstDecayBound F + firstDecayBound (leftSecondReal F) +
    firstDecayBound (leftSecondImag F)

theorem inverse_leftSlice_weight_le (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2) * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
      ‖(𝓕⁻ (leftSlice F η)) x‖ +
      ‖(𝓕⁻ (leftSlice (leftSecondReal F) η)) x‖ +
      ‖(𝓕⁻ (leftSlice (leftSecondImag F) η)) x‖ := by
  have h := norm_sq_mul_norm_inverse_le (leftSlice F η) x
  simp only [leftSlice_lineDeriv] at h
  change ‖x‖^2 * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤
    ‖(𝓕⁻ (leftSlice (leftSecondReal F) η)) x‖ +
    ‖(𝓕⁻ (leftSlice (leftSecondImag F) η)) x‖ at h
  nlinarith

theorem inverse_leftSlice_first_decay (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2) * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤ firstDecayBound F * planeMajorant η := by
  apply (inverse_leftSlice_weight_le F η x).trans
  have h0 := norm_inverse_leftSlice_le F η x
  have h1 := norm_inverse_leftSlice_le (leftSecondReal F) η x
  have h2 := norm_inverse_leftSlice_le (leftSecondImag F) η x
  dsimp [firstDecayBound, sliceIntegralBound]
  nlinarith

theorem inverse_leftSlice_second_decay (F : 𝓢(Joint, ℂ)) (η x : ℂ) :
    (1+‖x‖^2)^2 * ‖(𝓕⁻ (leftSlice F η)) x‖ ≤ secondDecayBound F * planeMajorant η := by
  have h := mul_le_mul_of_nonneg_left (inverse_leftSlice_weight_le F η x)
    (show 0 ≤ 1+‖x‖^2 by positivity)
  have h0 := inverse_leftSlice_first_decay F η x
  have h1 := inverse_leftSlice_first_decay (leftSecondReal F) η x
  have h2 := inverse_leftSlice_first_decay (leftSecondImag F) η x
  dsimp [secondDecayBound]
  nlinarith

theorem norm_partialFourier_le (W : 𝓢(Joint, ℂ)) (η x : ℂ) :
    ‖partialFourier W η x‖ ≤
      secondDecayBound (𝓕 W) * (planeMajorant x * planeMajorant η) := by
  rw [← partialFourierSchwartz_apply]
  change ‖(𝓕⁻ (leftSlice (𝓕 W) η)) x‖ ≤ _
  have h := inverse_leftSlice_second_decay (𝓕 W) η x
  have hd : ‖(𝓕⁻ (leftSlice (𝓕 W) η)) x‖ ≤
      secondDecayBound (𝓕 W) * planeMajorant η / (1+‖x‖^2)^2 :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith [h])
  convert hd using 1
  simp only [planeMajorant, div_eq_mul_inv]
  ring

open EisensteinSchwartzPoisson hiding O

theorem planeMajorant_cartesian_summable :
    Summable (fun p : ℤ × ℤ => planeMajorant (complexPoint (p.1:ℝ) (p.2:ℝ))) := by
  apply Summable.of_nonneg_of_le (fun _ => by unfold planeMajorant; positivity) _
    summable_int_cauchy_product
  intro p
  change ((1+‖complexPoint (p.1:ℝ) (p.2:ℝ)‖^2)^2)⁻¹ ≤ _
  rw [← mul_inv]
  apply inv_anti₀ (by positivity)
  rw [Complex.sq_norm]
  simp only [complexPoint, Complex.normSq_apply]
  nlinarith [sq_nonneg (p.1:ℝ), sq_nonneg (p.2:ℝ),
    mul_nonneg (sq_nonneg (p.1:ℝ)) (sq_nonneg (p.2:ℝ))]

def cartesianPoint (p : ℤ × ℤ) : ℂ := complexPoint (p.1:ℝ) (p.2:ℝ)

theorem joint_cartesian_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖W (point (cartesianPoint p.1) (cartesianPoint p.2))‖) := by
  have hs := planeMajorant_cartesian_summable.mul_of_nonneg
    planeMajorant_cartesian_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_le_product_majorant W _ _) (hs.mul_left (productDecayConstant W))

theorem partialFourier_cartesian_summable_norm (W : 𝓢(Joint, ℂ)) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖partialFourier W (cartesianPoint p.2) (cartesianPoint p.1)‖) := by
  have hs := planeMajorant_cartesian_summable.mul_of_nonneg
    planeMajorant_cartesian_summable
    (fun _ => by unfold planeMajorant; positivity)
    (fun _ => by unfold planeMajorant; positivity)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => norm_partialFourier_le W _ _) (hs.mul_left (secondDecayBound (𝓕 W)))

theorem rightSlice_isometry (x : ℂ) : Isometry (fun y : ℂ => point x y) := by
  apply Isometry.of_dist_eq
  intro y z
  simp only [dist_eq_norm, point_eq_add, add_sub_add_left_eq_sub, ← map_sub]
  exact WithLp.norm_toLp_snd 2 ℂ ℂ (y-z)

def rightSlice (W : 𝓢(Joint, ℂ)) (x : ℂ) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (by simp only [point_eq_add]; fun_prop : (fun y : ℂ => point x y).HasTemperateGrowth)
    (rightSlice_isometry x).antilipschitzWith W

@[simp] theorem rightSlice_apply (W : 𝓢(Joint, ℂ)) (x y : ℂ) :
    rightSlice W x y = W (point x y) := rfl

theorem rightSlice_poisson (W : 𝓢(Joint, ℂ)) (x : ℂ) :
    (∑' p : ℤ × ℤ, W (point x (cartesianPoint p))) =
      ∑' p : ℤ × ℤ, partialFourier W (cartesianPoint p) x := by
  have h := integer_pair_poisson (rightSlice W x)
  have hcoe : (rightSlice W x : ℂ → ℂ) = fun y => W (point x y) := rfl
  simpa only [rightSlice_apply, SchwartzMap.fourier_coe, hcoe, partialFourier, cartesianPoint] using h

private theorem joint_cartesian_eq_partial (W : 𝓢(Joint, ℂ)) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
  have hp := (joint_cartesian_summable_norm W).of_norm
  have hm := (partialFourier_cartesian_summable_norm W).of_norm
  calc
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        W (point (cartesianPoint m) (cartesianPoint n)) := hp.tsum_prod
    _ = ∑' m : ℤ × ℤ, ∑' n : ℤ × ℤ,
        partialFourier W (cartesianPoint n) (cartesianPoint m) := by
      apply tsum_congr
      intro m
      exact rightSlice_poisson W _
    _ = _ := hm.tsum_comm.symm

private theorem partial_cartesian_poisson (W : 𝓢(Joint, ℂ)) (n : ℤ × ℤ) :
    (∑' m : ℤ × ℤ, partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' m : ℤ × ℤ, (𝓕 W) (point (cartesianPoint m) (cartesianPoint n)) := by
  calc
    _ = ∑' m : ℤ × ℤ, partialFourierSchwartz W (cartesianPoint n) (cartesianPoint m) :=
      tsum_congr fun m =>
        (partialFourierSchwartz_apply W (cartesianPoint n) (cartesianPoint m)).symm
    _ = ∑' m : ℤ × ℤ,
        (𝓕 (partialFourierSchwartz W (cartesianPoint n)) : 𝓢(ℂ, ℂ)) (cartesianPoint m) := by
      simpa only [cartesianPoint] using
        integer_pair_poisson (partialFourierSchwartz W (cartesianPoint n))
    _ = _ := tsum_congr fun m =>
      fourier_partialFourierSchwartz W (cartesianPoint m) (cartesianPoint n)

private theorem cartesian_swap_tsum (F : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ, F (point (cartesianPoint m) (cartesianPoint n))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), F (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  have hF := (joint_cartesian_summable_norm F).of_norm
  exact hF.tsum_comm.trans hF.tsum_prod.symm

private theorem partial_cartesian_eq_fourier (W : 𝓢(Joint, ℂ)) :
    (∑' n : ℤ × ℤ, ∑' m : ℤ × ℤ,
      partialFourier W (cartesianPoint n) (cartesianPoint m)) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (tsum_congr (partial_cartesian_poisson W)).trans (cartesian_swap_tsum (𝓕 W))

theorem joint_cartesian_poisson (W : 𝓢(Joint, ℂ)) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (point (cartesianPoint p.1) (cartesianPoint p.2))) =
      ∑' p : (ℤ × ℤ) × (ℤ × ℤ), (𝓕 W) (point (cartesianPoint p.1) (cartesianPoint p.2)) := by
  exact (joint_cartesian_eq_partial W).trans (partial_cartesian_eq_fourier W)

def blockMap (A : ℂ ≃L[ℝ] ℂ) : Joint ≃L[ℝ] Joint :=
  ((A.toLinearEquiv.prodCongr A.toLinearEquiv).withLpCongr 2).toContinuousLinearEquiv

@[simp] theorem blockMap_apply (A : ℂ ≃L[ℝ] ℂ) (z : Joint) :
    blockMap A z = point (A z.fst) (A z.snd) := rfl

@[simp] theorem blockMap_symm_apply (A : ℂ ≃L[ℝ] ℂ) (z : Joint) :
    (blockMap A).symm z = point (A.symm z.fst) (A.symm z.snd) := rfl

theorem blockMap_det (A : ℂ ≃L[ℝ] ℂ) :
    LinearMap.det (blockMap A : Joint →ₗ[ℝ] Joint) =
      LinearMap.det (A : ℂ →ₗ[ℝ] ℂ) ^ 2 := by
  have h := LinearMap.det_conj
    ((A : ℂ →ₗ[ℝ] ℂ).prodMap (A : ℂ →ₗ[ℝ] ℂ))
    (WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).symm
  rw [LinearMap.det_prodMap] at h
  convert h using 1 <;> first | rfl | ring

def jointInverseJacobian (A : Joint ≃L[ℝ] Joint) : ℝ :=
  |(LinearMap.det (A : Joint →ₗ[ℝ] Joint))⁻¹|

theorem jointInverseJacobian_blockMap (A : ℂ ≃L[ℝ] ℂ) :
    jointInverseJacobian (blockMap A) = inverseJacobian A ^ 2 := by
  rw [jointInverseJacobian, blockMap_det, ← inv_pow, abs_pow]
  rfl

def jointDual (A : Joint ≃L[ℝ] Joint) : Joint →L[ℝ] Joint :=
  A.symm.toContinuousLinearMap.adjoint

theorem joint_inner_linear_dual (A : Joint ≃L[ℝ] Joint) (x y : Joint) :
    inner ℝ (A x) (jointDual A y) = inner ℝ x y := by
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  simp

theorem jointDual_blockMap (A : ℂ ≃L[ℝ] ℂ) (ξ η : ℂ) :
    jointDual (blockMap A) (point ξ η) = point (dualMap A ξ) (dualMap A η) := by
  apply ext_inner_left ℝ
  intro z
  rw [jointDual, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (point (A.symm z.fst) (A.symm z.snd)) (point ξ η) = _
  simp only [point, WithLp.prod_inner_apply, dualMap,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem joint_integral_comp_linearEquiv (A : Joint ≃L[ℝ] Joint) (f : Joint → ℂ) :
    (∫ x : Joint, f (A x)) = jointInverseJacobian A • ∫ x : Joint, f x := by
  have h := integral_map_equiv («μ» := (volume : Measure Joint))
    A.toHomeomorph.toMeasurableEquiv f
  have hm : Measure.map A (volume : Measure Joint) =
      ENNReal.ofReal (jointInverseJacobian A) • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
  change (∫ y : Joint, f y ∂Measure.map A volume) = (∫ x : Joint, f (A x)) at h
  rw [hm, integral_smul_measure, ENNReal.toReal_ofReal
    (show 0 ≤ jointInverseJacobian A from abs_nonneg _)] at h
  exact h.symm

theorem joint_fourier_comp_linearEquiv (A : Joint ≃L[ℝ] Joint)
    (f : Joint → ℂ) (w : Joint) :
    𝓕 (f ∘ A) w = jointInverseJacobian A • 𝓕 f (jointDual A w) := by
  let H : Joint → ℂ := fun z => Real.fourierChar (-inner ℝ z (jointDual A w)) • f z
  calc
    𝓕 (f ∘ A) w = ∫ x : Joint, H (A x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [H, joint_inner_linear_dual, Function.comp_apply]
        rfl
    _ = jointInverseJacobian A • ∫ z : Joint, H z := joint_integral_comp_linearEquiv A H
    _ = _ := rfl

def jointTranslate (W : 𝓢(Joint, ℂ)) (b : Joint) : 𝓢(Joint, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (g := fun z : Joint => z+b)
    (by fun_prop) (isometry_add_right b).antilipschitzWith W

def jointAffine (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b : Joint) : 𝓢(Joint, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A (jointTranslate W b)

@[simp] theorem jointAffine_apply (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b z : Joint) :
    jointAffine W A b z = W (A z+b) := rfl

theorem joint_fourier_affine (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b w : Joint) :
    (𝓕 (jointAffine W A b)) w =
      jointInverseJacobian A •
        (Real.fourierChar (inner ℝ b (jointDual A w)) • (𝓕 W) (jointDual A w)) := by
  rw [congrFun (SchwartzMap.fourier_coe _) w]
  change 𝓕 ((fun z => W (z+b)) ∘ A) w = _
  rw [joint_fourier_comp_linearEquiv]
  have ht : 𝓕 (fun z => W (z+b)) (jointDual A w) =
      Real.fourierChar (inner ℝ b (jointDual A w)) • 𝓕 (W : Joint → ℂ) (jointDual A w) :=
    congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure Joint) (innerₗ Joint) (W : Joint → ℂ) b) (jointDual A w)
  rw [ht]
  rw [congrFun (SchwartzMap.fourier_coe W) (jointDual A w)]

theorem joint_affine_poisson (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) (b : Joint) :
    (∑' p : (ℤ × ℤ) × (ℤ × ℤ),
      W (A (point (cartesianPoint p.1) (cartesianPoint p.2))+b)) =
      jointInverseJacobian A • ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        Real.fourierChar (inner ℝ b
          (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))) •
        (𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2))) := by
  have h := joint_cartesian_poisson (jointAffine W A b)
  simp only [jointAffine_apply, joint_fourier_affine] at h
  rw [tsum_const_smul''] at h
  exact h

def jointFrequency (c : ℂ) (hc : c ≠ 0) (p : (ℤ × ℤ) × (ℤ × ℤ)) : Joint :=
  point (eisensteinDualFrequency c hc p.1) (eisensteinDualFrequency c hc p.2)

open ActualEisensteinCubic ConcreteTraceCRT

theorem actual_joint_coset_poisson (W : 𝓢(Joint, ℂ)) (b : O × O) (c : O) (hc : c ≠ 0) :
    (∑' m : O × O, W (embeddingPair (b.1+c*m.1,b.2+c*m.2))) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
          Real.fourierChar (inner ℝ (embeddingPair b)
            (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
            (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  let A := eisensteinLatticeMap (eisEmbedding c) (eisEmbedding_ne_zero hc)
  have h := joint_affine_poisson W (blockMap A) (embeddingPair b)
  simp only [jointInverseJacobian_blockMap, jointDual_blockMap] at h
  rw [eisenstein_inverseJacobian] at h
  calc
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ), W (embeddingPair
        (b.1+c*latticeCoordEquiv.symm p.1,b.2+c*latticeCoordEquiv.symm p.2)) :=
      ((latticeCoordEquiv.symm.prodCongr latticeCoordEquiv.symm).tsum_eq _).symm
    _ = ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
        W (blockMap A (point (cartesianPoint p.1) (cartesianPoint p.2))+embeddingPair b) := by
      apply tsum_congr
      intro p
      congr 1
      change point (eisEmbedding (b.1+c*ActualEisensteinCoordinates.eval p.1.1 p.1.2))
        (eisEmbedding (b.2+c*ActualEisensteinCoordinates.eval p.2.1 p.2.2)) = _
      simp only [map_add, map_mul, blockMap_apply, point]
      rw [← eisensteinLatticeMap_point (eisEmbedding c) (eisEmbedding_ne_zero hc) p.1,
        ← eisensteinLatticeMap_point (eisEmbedding c) (eisEmbedding_ne_zero hc) p.2]
      change point (eisEmbedding b.1 + A (cartesianPoint p.1))
        (eisEmbedding b.2 + A (cartesianPoint p.2)) =
          point (A (cartesianPoint p.1)+eisEmbedding b.1)
            (A (cartesianPoint p.2)+eisEmbedding b.2)
      simp only [add_comm]
    _ = _ := h

theorem joint_dual_summable_norm (W : 𝓢(Joint, ℂ)) (A : Joint ≃L[ℝ] Joint) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖) := by
  have hJ : 0 < jointInverseJacobian A :=
    abs_pos.mpr (inv_ne_zero A.toLinearEquiv.isUnit_det'.ne_zero)
  have hs := joint_cartesian_summable_norm (𝓕 (jointAffine W A 0))
  have hn (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (jointAffine W A 0)) (point (cartesianPoint p.1) (cartesianPoint p.2))‖ =
      jointInverseJacobian A *
        ‖(𝓕 W) (jointDual A (point (cartesianPoint p.1) (cartesianPoint p.2)))‖ := by
    rw [joint_fourier_affine]
    simp [abs_of_pos hJ]
  simp_rw [hn] at hs
  have hi := hs.mul_left (jointInverseJacobian A)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ hJ.ne', one_mul] using hi

theorem jointFrequency_summable_norm (W : 𝓢(Joint, ℂ)) (c : ℂ) (hc : c ≠ 0) :
    Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) => ‖(𝓕 W) (jointFrequency c hc p)‖) := by
  have h := joint_dual_summable_norm W (blockMap (eisensteinLatticeMap c hc))
  simpa only [jointDual_blockMap, jointFrequency, eisensteinDualFrequency, cartesianPoint] using h

abbrev Residue (c : O) := O ⧸ Ideal.span {c}

def quotientPair (c : O) (m : O × O) : Residue c × Residue c :=
  (Ideal.Quotient.mk (Ideal.span {c}) m.1, Ideal.Quotient.mk (Ideal.span {c}) m.2)

def representativePair (c : O) (r : Residue c × Residue c) : O × O :=
  (GaussianShiftedPartition.representative c r.1, GaussianShiftedPartition.representative c r.2)

def jointFiberSplit (c : O) (r : Residue c × Residue c) :
    (quotientPair c ⁻¹' {r}) ≃
      ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r.1}) ×
      ((Ideal.Quotient.mk (Ideal.span {c})) ⁻¹' {r.2}) where
  toFun z := (⟨z.1.1, congrArg Prod.fst z.2⟩, ⟨z.1.2, congrArg Prod.snd z.2⟩)
  invFun z := ⟨(z.1.1,z.2.1), Prod.ext z.1.2 z.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem joint_fiber_tsum (c : O) (hc : c ≠ 0) (r : Residue c × Residue c)
    (W : O × O → ℂ) :
    (∑' m : quotientPair c ⁻¹' {r}, W m.1) =
      ∑' m : O × O, W ((representativePair c r).1+c*m.1,
        (representativePair c r).2+c*m.2) := by
  let e1 := GaussianFiberEquiv.fiberEquiv c hc r.1
    (GaussianShiftedPartition.representative c r.1)
    (GaussianShiftedPartition.representative_spec c r.1)
  let e2 := GaussianFiberEquiv.fiberEquiv c hc r.2
    (GaussianShiftedPartition.representative c r.2)
    (GaussianShiftedPartition.representative_spec c r.2)
  let e := (e1.prodCongr e2).trans (jointFiberSplit c r).symm
  exact (e.tsum_eq (fun m => W m.1)).symm

def residueFourier (c : O) (hc : c ≠ 0) (a : Residue c × Residue c → ℂ)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) : ℂ :=
  ∑' r : Residue c × Residue c, a r *
    (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
      (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)

theorem actual_joint_periodic_poisson (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    letI : Finite (Residue c) := finite_quotient_span hc
    letI : Fintype (Residue c) := Fintype.ofFinite _
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      ∑ r : Residue c × Residue c, a r *
        ((2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
          ∑' p : (ℤ × ℤ) × (ℤ × ℤ),
            Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
              (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
              (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  have ha (r : Residue c × Residue c) : ‖a r‖ ≤ ∑ t : Residue c × Residue c, ‖a t‖ :=
    Finset.single_le_sum (fun t _ => norm_nonneg (a t)) (Finset.mem_univ r)
  have hs := joint_weighted_summable (Ideal.Quotient.mk (Ideal.span {c})) a _ ha W
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition (quotientPair c) a
    (fun m => W (embeddingPair m)) hs]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact (joint_fiber_tsum c hc r (fun m => W (embeddingPair m))).trans
    (actual_joint_coset_poisson W (representativePair c r) c hc)

theorem actual_joint_periodic_fourier (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    (∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)) =
      (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
        ∑' p : (ℤ × ℤ) × (ℤ × ℤ), residueFourier c hc a p *
          (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p) := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  rw [actual_joint_periodic_poisson W c hc a]
  have hs (r : Residue c × Residue c) : Summable (fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
      a r * (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) •
        (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [Circle.norm_smul] using
      jointFrequency_summable_norm W (eisEmbedding c) (eisEmbedding_ne_zero hc)
  simp_rw [mul_smul_comm, ← tsum_mul_left]
  rw [← Finset.smul_sum, ← Summable.tsum_finsetSum (fun r _ => hs r)]
  congr 1
  apply tsum_congr
  intro p
  simp only [residueFourier, tsum_fintype, Circle.smul_def, smul_eq_mul,
    Finset.sum_mul, mul_assoc]

@[simp] theorem jointFrequency_zero (c : ℂ) (hc : c ≠ 0) :
    jointFrequency c hc 0 = 0 := by
  have h : complexPoint (0:ℝ) 0 = 0 := by apply Complex.ext <;> rfl
  simp [jointFrequency, eisensteinDualFrequency, h, point]

@[simp] theorem residueFourier_zero (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    residueFourier c hc a 0 = ∑' r, a r := by
  simp [residueFourier]

theorem residueFourier_norm_le (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    ‖residueFourier c hc a p‖ ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 * B := by
  classical
  let : Finite (Residue c) := finite_quotient_span hc
  let : Fintype (Residue c) := Fintype.ofFinite _
  rw [residueFourier, tsum_fintype]
  calc
    _ ≤ ∑ r : Residue c × Residue c, ‖a r *
        (Real.fourierChar (inner ℝ (embeddingPair (representativePair c r))
          (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r : Residue c × Residue c, B := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [norm_mul, Circle.norm_coe, mul_one] using hB r
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
        Nat.cast_mul, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Nat.card_eq_fintype_card, Residue, pow_two]

theorem principal_joint_inverse_covolume (c : O) (hc : c ≠ 0) :
    (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 *
      (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 = 4/3 := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hc)
  rw [← eisEmbedding_norm_sq_eq_absNorm_span]
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  nlinarith

theorem norm_periodic_zero_mean_le (W : 𝓢(Joint, ℂ)) (c : O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ r, ‖a r‖ ≤ B)
    (hmean : (∑' r, a r) = 0) :
    ‖∑' m : O × O, a (quotientPair c m) * W (embeddingPair m)‖ ≤
      (4/3:ℝ) * B *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
  let F (p : (ℤ × ℤ) × (ℤ × ℤ)) := residueFourier c hc a p *
    (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hF0 : F 0 = 0 := by simp [F, hmean]
  have hnorm (p : (ℤ × ℤ) × (ℤ × ℤ)) : ‖F p‖ ≤ q^2 * B *
      ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (residueFourier_norm_le c hc a B hB p) (norm_nonneg _)
  have hsF : Summable (fun p => ‖F p‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
      ((jointFrequency_summable_norm W (eisEmbedding c) (eisEmbedding_ne_zero hc)).mul_left _)
  have heq : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, F p.val) = ∑' p, F p := by
    apply tsum_subtype_eq_of_support_subset
    intro p hp
    change F p ≠ 0 at hp
    exact fun h => hp (h ▸ hF0)
  have hb : ‖∑' p, F p‖ ≤ q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
    rw [← heq]
    have hs1 : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} => ‖F p.val‖) :=
      hsF.subtype (fun p => p ≠ 0)
    have hm : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} =>
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      (jointFrequency_summable_norm W (eisEmbedding c)
        (eisEmbedding_ne_zero hc)).subtype (fun p => p ≠ 0)
    have ht : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, ‖F p.val‖) ≤
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, q^2 * B *
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ :=
      Summable.tsum_le_tsum (fun p => hnorm p.val) hs1 (hm.mul_left (q^2*B))
    exact (norm_tsum_le_tsum_norm hs1).trans (by simpa only [tsum_mul_left] using ht)
  rw [actual_joint_periodic_fourier W c hc a, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (2/(Real.sqrt 3*‖eisEmbedding c‖^2))^2 * (q^2 * B *
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, principal_joint_inverse_covolume c hc]

def scaleMap (t : ℝ) (ht : 0 < t) : Joint ≃L[ℝ] Joint :=
  blockMap (complexMulEquiv ((t⁻¹:ℝ):ℂ)
    (Complex.ofReal_ne_zero.mpr (inv_ne_zero ht.ne')))

@[simp] theorem scaleMap_apply (t : ℝ) (ht : 0 < t) (z : Joint) :
    scaleMap t ht z = t⁻¹ • z := by
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [scaleMap, blockMap_apply, complexMulEquiv_apply, point, Algebra.smul_def]

theorem scaleMap_dual (t : ℝ) (ht : 0 < t) (z : Joint) :
    jointDual (scaleMap t ht) z = t • z := by
  have hz : z = point z.fst z.snd := rfl
  conv_lhs => rw [hz]
  rw [scaleMap, jointDual_blockMap, dual_mul_apply, dual_mul_apply]
  apply WithLp.ofLp_injective
  apply Prod.ext <;> simp [point, Algebra.smul_def]

theorem scaleMap_inverseJacobian (t : ℝ) (ht : 0 < t) :
    jointInverseJacobian (scaleMap t ht) = t^4 := by
  rw [scaleMap, jointInverseJacobian_blockMap, inverseJacobian, complexMulEquiv_det,
    abs_inv, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos ht, ← inv_pow, inv_inv]
  ring

def scaledSource (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) : 𝓢(Joint, ℂ) :=
  jointAffine W (scaleMap t ht) 0

@[simp] theorem scaledSource_apply (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) (z : Joint) :
    scaledSource W t ht z = W (t⁻¹ • z) := by
  simp [scaledSource]

theorem fourier_scaledSource (W : 𝓢(Joint, ℂ)) (t : ℝ) (ht : 0 < t) (z : Joint) :
    (𝓕 (scaledSource W t ht)) z = t^4 • (𝓕 W) (t • z) := by
  rw [scaledSource, joint_fourier_affine, scaleMap_inverseJacobian, scaleMap_dual]
  simp

theorem scaledSource_physicalPoint (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N) (m : O × O) :
    scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN) (embeddingPair m) =
      W (ProbeGramLatticeDecay.physicalPoint N m) := by
  rw [scaledSource_apply, ProbeGramLatticeDecay.physicalPoint_eq_smul]
  rfl

def generatorRotation (c : ℂ) : ℂ := (‖c‖:ℂ) / starRingEnd ℂ c

theorem norm_generatorRotation (c : ℂ) (hc : c ≠ 0) : ‖generatorRotation c‖ = 1 := by
  simp [generatorRotation, Complex.norm_real, norm_ne_zero_iff.mpr hc]

theorem scaled_jointFrequency_eq (c : ℂ) (hc : c ≠ 0) (N : ℝ) (hN : 0 < N)
    (p : (ℤ × ℤ) × (ℤ × ℤ)) :
    Real.sqrt N • jointFrequency c hc p =
      ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/‖c‖^2)) (generatorRotation c) p := by
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hs : Real.sqrt (N/‖c‖^2) = Real.sqrt N / ‖c‖ := by
    rw [Real.sqrt_div hN.le, Real.sqrt_sq (norm_nonneg c)]
  have hcoord (v : ℤ × ℤ) : (Real.sqrt N:ℂ) * eisensteinDualFrequency c hc v =
      generatorRotation c * (Real.sqrt (N/‖c‖^2):ℂ) * explicitDualFrequency 1 v := by
    rw [eisensteinDualFrequency_explicit, hs]
    simp only [generatorRotation, explicitDualFrequency, map_one, div_one, Complex.ofReal_div]
    have hnC : (‖c‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
    field_simp
  apply WithLp.ofLp_injective
  change (Real.sqrt N • eisensteinDualFrequency c hc p.1,
    Real.sqrt N • eisensteinDualFrequency c hc p.2) = _
  apply Prod.ext
  · simpa [Algebra.smul_def, ProbeGramLatticeDecay.scaledDualPoint, ProbeGramLatticeDecay.point] using hcoord p.1
  · simpa [Algebra.smul_def, ProbeGramLatticeDecay.scaledDualPoint, ProbeGramLatticeDecay.point] using hcoord p.2

theorem sqrt_ratio_decay (N q : ℝ) (hN : 0 < N) (hq : 0 < q) (A : ℕ) :
    (Real.sqrt (N/q))^(-((2*A:ℕ):ℝ)) = (q/N)^A := by
  rw [Real.rpow_neg (Real.sqrt_nonneg _), Real.rpow_natCast, pow_mul,
    Real.sq_sqrt (div_nonneg hN.le hq.le), ← inv_pow, inv_div]

theorem physical_weighted_summable (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N)
    (d : O × O → ℂ) (B : ℝ) (hB : ∀ m, ‖d m‖ ≤ B) :
    Summable (fun m : O × O => d m * W (ProbeGramLatticeDecay.physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((ProbeGramLatticeDecay.physical_summable W N hN).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _)

theorem principal_high_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : O) (_hc : c ≠ 0)
        (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖a r‖ ≤ B) → (∑' r, a r) = 0 →
        ∀ (N : ℝ), 0 < N → (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N →
        ‖∑' m : O × O, a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A := by
  obtain ⟨S,C,hC,hhigh⟩ := ProbeGramLatticeDecay.dual_fourier_lattice_bound A hA
  refine ⟨S,(4/3)*C,mul_pos (by norm_num) hC,?_⟩
  intro W c hc a B hB0 hB hmean N hN hscale
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hq : 0 < q := by
    dsimp only [q]
    rw [← eisEmbedding_norm_sq_eq_absNorm_span]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
  have hL : 1 ≤ Real.sqrt (N/q) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only [one_pow]
    exact (le_div_iff₀ hq).mpr (by simpa only [one_mul] using hscale)
  let u : ℂ := generatorRotation (eisEmbedding c)
  have hu : ‖u‖ = 1 := norm_generatorRotation _ (eisEmbedding_ne_zero hc)
  have ht4 : (Real.sqrt N)^4 = N^2 := by
    rw [show (4:ℕ) = 2*2 by norm_num, pow_mul, Real.sq_sqrt hN.le]
  have hf (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ =
      N^2 * ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p)‖ := by
    rw [fourier_scaledSource, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), ht4,
      scaled_jointFrequency_eq _ _ N hN]
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
  have h := norm_periodic_zero_mean_le
    (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)) c hc a B hB hmean
  simp_rw [scaledSource_physicalPoint W N hN, hf, tsum_mul_left] at h
  have hD := hhigh W (Real.sqrt (N/q)) hL u hu
  rw [sqrt_ratio_decay N q hN hq A] at hD
  calc
    _ ≤ (4/3:ℝ)*B*(N^2 *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p.val)‖) := h
    _ ≤ (4/3:ℝ)*B*(N^2 *
        (C * ProbeGramLatticeDecay.sourceControl S W * (q/N)^A)) := by
      gcongr
    _ = _ := by ring

theorem norm_physical_weighted_le (W : 𝓢(Joint, ℂ)) (N : ℝ) (hN : 0 < N)
    (d : O × O → ℂ) (B : ℝ) (hB : ∀ m, ‖d m‖ ≤ B) :
    ‖∑' m : O × O, d m * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
      B * ∑' m : O × O, ‖W (ProbeGramLatticeDecay.physicalPoint N m)‖ := by
  have hbound (m : O × O) : ‖d m * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
      B * ‖W (ProbeGramLatticeDecay.physicalPoint N m)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB m) (norm_nonneg _)
  have hs := ProbeGramLatticeDecay.physical_summable W N hN
  have hsD := Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound (hs.mul_left B)
  apply (norm_tsum_le_tsum_norm hsD).trans
  have h := Summable.tsum_le_tsum hbound hsD (hs.mul_left B)
  simpa only [tsum_mul_left] using h

theorem principal_periodic_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : O), c ≠ 0 →
        ∀ (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖a r‖ ≤ B) → (∑' r, a r) = 0 → ∀ (N : ℝ), 1 ≤ N →
        Summable (fun m : O × O =>
          a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A) := by
  obtain ⟨Sl,Cl,hCl,hl⟩ := ProbeGramLatticeDecay.physical_lattice_bound
  obtain ⟨Sh,Ch,hCh,hh⟩ := principal_high_bound A hA
  refine ⟨Sl∪Sh,Cl+Ch,add_pos hCl hCh,?_⟩
  intro W c hc a B hB0 hB hm N hN
  have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
  refine ⟨physical_weighted_summable W N hNp _ B (fun m => hB _),?_⟩
  have hSl : Cl*ProbeGramLatticeDecay.sourceControl Sl W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_right hCh.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_left W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hSh : Ch*ProbeGramLatticeDecay.sourceControl Sh W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_left hCl.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)/N := div_nonneg (by positivity) hNp.le
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hNp).mpr hscale)
    rw [min_eq_right hp]
    exact (hh W c hc a B hB0 hB hm N hNp hscale).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hB0) (sq_nonneg _))
        (pow_nonneg hratio _))
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A :=
      one_le_pow₀ ((le_div_iff₀ hNp).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    calc
      _ ≤ B * ∑' m : O × O, ‖W (ProbeGramLatticeDecay.physicalPoint N m)‖ :=
        norm_physical_weighted_le W N hNp _ B (fun m => hB _)
      _ ≤ B * (Cl*ProbeGramLatticeDecay.sourceControl Sl W*N^2) :=
        mul_le_mul_of_nonneg_left (hl W N hN) hB0
      _ = Cl*ProbeGramLatticeDecay.sourceControl Sl W*B*N^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSl hB0) (sq_nonneg _)

def idealQuotientPair (r : Ideal O) (m : O × O) : (O ⧸ r) × (O ⧸ r) :=
  (Ideal.Quotient.mk r m.1, Ideal.Quotient.mk r m.2)

theorem ideal_periodic_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (r : Ideal O), r ≠ 0 →
        ∀ (a : (O ⧸ r) × (O ⧸ r) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖a v‖ ≤ B) → (∑' v, a v) = 0 → ∀ (N : ℝ), 1 ≤ N →
        Summable (fun m : O × O =>
          a (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, a (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ)/N)^A) := by
  obtain ⟨S,C,hC,h⟩ := principal_periodic_bound A hA
  refine ⟨S,C,hC,?_⟩
  intro W r hr
  obtain ⟨c,hc,heq⟩ : ∃ c : O, c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨ConcretePrimeRowBridge.idealGenerator r,
      ConcretePrimeRowBridge.idealGenerator_ne_zero r hr,
      ConcretePrimeRowBridge.span_idealGenerator r⟩
  subst r
  exact h W c hc

theorem principal_annular_periodic_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (c : O), c ≠ 0 → ∀ (d : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ r, ‖d r‖ ≤ B) → (∑' r, d r) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A) := by
  obtain ⟨Sl,Cl,hCl,hl⟩ := ProbeGramAnnularLattice.annular_weighted_lattice_bound a b ha hab
  obtain ⟨Sh,Ch,hCh,hh⟩ := principal_high_bound A hA
  refine ⟨Sl∪Sh,Cl+Ch,add_pos hCl hCh,?_⟩
  intro W hW c hc d B hB0 hB hm N hN
  refine ⟨physical_weighted_summable W N hN _ B (fun m => hB _),?_⟩
  have hSl : Cl*ProbeGramLatticeDecay.sourceControl Sl W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_right hCh.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_left W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hSh : Ch*ProbeGramLatticeDecay.sourceControl Sh W ≤
      (Cl+Ch)*ProbeGramLatticeDecay.sourceControl (Sl∪Sh) W :=
    mul_le_mul (le_add_of_nonneg_left hCl.le)
      (ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W)
      (ProbeGramLatticeDecay.sourceControl_nonneg _ _) (by positivity)
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)/N := div_nonneg (by positivity) hN.le
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hN).mpr hscale)
    rw [min_eq_right hp]
    exact (hh W c hc d B hB0 hB hm N hN hscale).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSh hB0) (sq_nonneg _))
        (pow_nonneg hratio _))
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ)/N)^A :=
      one_le_pow₀ ((le_div_iff₀ hN).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    exact (hl W hW (fun m => d (quotientPair c m)) B hB0
      (fun m => hB _) N hN).2.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSl hB0) (sq_nonneg _))

theorem ideal_annular_periodic_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (r : Ideal O), r ≠ 0 → ∀ (d : (O ⧸ r) × (O ⧸ r) → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖d v‖ ≤ B) → (∑' v, d v) = 0 → ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O =>
          d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : O × O, d (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ)/N)^A) := by
  obtain ⟨S,C,hC,h⟩ := principal_annular_periodic_bound A hA a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW r hr
  obtain ⟨c,hc,heq⟩ : ∃ c : O, c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨ConcretePrimeRowBridge.idealGenerator r,
      ConcretePrimeRowBridge.idealGenerator_ne_zero r hr,
      ConcretePrimeRowBridge.span_idealGenerator r⟩
  subst r
  exact h W hW c hc

end ProbeGramPeriodicPoisson

end

end OAI
end OAIOriginalModule0483

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGramExceptional
Source SHA256: 350cb3efaee0d998f134aa74b998dffb1850170006eafdd6729a89fafe181b6c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0484


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CenteredExceptionalCount IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramRemainders (F : Finset O) : Finset Id :=
  F.image (fun z=>sixthRemainder (Ideal.span {z}))

lemma lowGramRemainders_nonzero (F : Finset O) (R : Id) (hR : R∈lowGramRemainders F) : R≠0 := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hR
  exact sixthRemainder_ne_zero _

theorem lowGramRemainders_card (F : Finset O) (G : Id)
    (hres : ∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0) :
    (lowGramRemainders F).card≤6^(primeSupport G).card := by
  have hlt (R : lowGramRemainders F) (P : Id) : valuation R.val P<6 := by
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp R.property
    rw [←he]
    exact sixthRemainder_valuation_lt _ _
  let code : lowGramRemainders F→(primeSupport G→Fin 6) := fun R P=>⟨valuation R.val P.val,hlt R P.val⟩
  have hinj : Function.Injective code := by
    intro R T he
    apply Subtype.ext
    apply ideal_eq_of_valuation_eq (lowGramRemainders_nonzero F R.val R.property)
      (lowGramRemainders_nonzero F T.val T.property)
    intro P
    by_cases hp : P∈primeSupport G
    · exact congrArg Fin.val (congrFun he ⟨P,hp⟩)
    · obtain ⟨r,hr,her⟩ := Finset.mem_image.mp R.property
      obtain ⟨t,ht,het⟩ := Finset.mem_image.mp T.property
      rw [←her,←het,sixthRemainder_valuation,sixthRemainder_valuation,hres r hr P hp,hres t ht P hp]
  have hh := Fintype.card_le_of_injective code hinj
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hh

theorem lowGramExceptional_raw_count (F : Finset O) (G : Id) (H : ℝ) (hH : 0≤H)
    (hF : ∀z∈F,z≠0)
    (hres : ∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0)
    (hN : ∀z∈F,(Ideal.absNorm (Ideal.span {z}):ℝ)≤H) :
    (F.card:ℝ)≤768*(6:ℝ)^(primeSupport G).card*H^(1/6:ℝ) := by
  have hh := element_count_remainder_family F (lowGramRemainders F)
    (lowGramRemainders_nonzero F) H hH hF (fun z hz=>Finset.mem_image.mpr ⟨z,hz,rfl⟩) hN
  calc
    _ ≤ ∑R∈lowGramRemainders F,768*(H/(Ideal.absNorm R:ℝ))^(1/6:ℝ) := hh
    _ ≤ ∑_R∈lowGramRemainders F,768*H^(1/6:ℝ) := by
      apply Finset.sum_le_sum
      intro R hR
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.rpow_le_rpow (div_nonneg hH (Nat.cast_nonneg _)) _ (by norm_num)
      exact div_le_self hH (norm_one_le (lowGramRemainders_nonzero F R hR))
    _ = (lowGramRemainders F).card*(768*H^(1/6:ℝ)) := by simp
    _ ≤ ((6:ℝ)^(primeSupport G).card)*(768*H^(1/6:ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast lowGramRemainders_card F G hres
    _ = _ := by ring

theorem lowGramExceptional_count (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀G : Id,G≠0→∀F : Finset O,∀H : ℝ,0≤H→
      (∀z∈F,z≠0)→
      (∀z∈F,∀P∉primeSupport G,valuation (Ideal.span {z}) P%6=0)→
      (∀z∈F,(Ideal.absNorm (Ideal.span {z}):ℝ)≤H)→
      (F.card:ℝ)≤C*(Ideal.absNorm G:ℝ)^ε*H^(1/6:ℝ) := by
  obtain ⟨C,hC,hb⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/3) (by positivity)
  refine ⟨768*C^3,by positivity,?_⟩
  intro G hG F H hH hF hres hN
  have hp : (6:ℝ)^(primeSupport G).card≤C^3*(Ideal.absNorm G:ℝ)^ε := by
    calc
      _ ≤ ((2:ℝ)^3)^(primeSupport G).card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      _ = ((2:ℝ)^(primeSupport G).card)^3 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _ ≤ (C*(Ideal.absNorm G:ℝ)^(ε/3))^3 := pow_le_pow_left₀ (by positivity) (hb G hG) 3
      _ = _ := by
        rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg (Ideal.absNorm G))]
        congr 2
        norm_num
  apply (lowGramExceptional_raw_count F G H hH hF hres hN).trans
  calc
    _ ≤ 768*(C^3*(Ideal.absNorm G:ℝ)^ε)*H^(1/6:ℝ) := by gcongr
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule0484

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramFrequencySummation
Source SHA256: d1c71bdee596df79381076f24c4a2284d4d32d569846b81863313f44ee3e5bb2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0485



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.ProbeGramFrequencySummation
local notation "O" => ActualEisensteinCubic.O

def frequencyNorm (k : O) : ℝ := Ideal.absNorm (Ideal.span {k})

lemma frequencyNorm_nonneg (k : O) : 0 ≤ frequencyNorm k := Nat.cast_nonneg _

lemma frequencyNorm_one_le (k : O) (hk : k ≠ 0) : 1 ≤ frequencyNorm k := by
  unfold frequencyNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hk))

theorem finite_weighted_of_count {α : Type*} (E : Finset α) (q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (C d H : ℝ) (hC : 0 ≤ C) (hd : d ≤ 1) (hH : 0 < H)
    (hcount : ∀ F : Finset α, F ⊆ E → ∀ R : ℝ, 0 < R →
      (∀ x ∈ F, q x ≤ R) → (F.card : ℝ) ≤ C * R ^ d) :
    ∑ x ∈ E, (1 + q x / H) ^ (-2 : ℝ) ≤ 4 * C * H ^ d := by
  have hex (x : α) : ∃ n : ℕ, (2:ℝ)^n ≤ 1 + q x / H ∧
      1 + q x / H < (2:ℝ)^(n+1) :=
    exists_nat_pow_near (by linarith [div_nonneg (hq x) hH.le]) (by norm_num)
  let bin (x : α) : ℕ := Classical.choose (hex x)
  have hlo (x : α) : (2:ℝ)^(bin x) ≤ 1 + q x / H := (Classical.choose_spec (hex x)).1
  have hhi (x : α) : 1 + q x / H < (2:ℝ)^(bin x+1) := (Classical.choose_spec (hex x)).2
  have hbin (n : ℕ) :
      ∑ x ∈ E.filter (fun x => bin x = n), (1 + q x / H) ^ (-2 : ℝ) ≤
        (2*C*H^d) * (1/2:ℝ)^n := by
    let F := E.filter (fun x => bin x = n)
    have hcard : (F.card:ℝ) ≤ C * ((2:ℝ)^(n+1)*H)^d := by
      apply hcount F (Finset.filter_subset _ _) _ (by positivity)
      intro x hx
      have he := (Finset.mem_filter.mp hx).2
      have hh := hhi x
      rw [he] at hh
      have hqdiv : q x/H ≤ (2:ℝ)^(n+1) := by linarith
      exact (div_le_iff₀ hH).mp hqdiv
    have hweight (x : α) (hx : x∈F) : (1+q x/H)^(-2:ℝ) ≤ (1/4:ℝ)^n := by
      have hl := hlo x
      rw [(Finset.mem_filter.mp hx).2] at hl
      apply (Real.rpow_le_rpow_of_nonpos (by positivity) hl (by norm_num)).trans_eq
      rw [Real.rpow_neg (by positivity), Real.rpow_two, ← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]
      norm_num
    have hp : ((2:ℝ)^(n+1))^d ≤ (2:ℝ)^(n+1) :=
      Real.rpow_le_self_of_one_le (one_le_pow₀ (by norm_num)) hd
    calc
      _ ≤ (F.card:ℝ)*(1/4:ℝ)^n := by
        apply (Finset.sum_le_sum hweight).trans_eq
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C*((2:ℝ)^(n+1)*H)^d)*(1/4:ℝ)^n :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ (C*((2:ℝ)^(n+1)*H^d))*(1/4:ℝ)^n := by
        rw [Real.mul_rpow (by positivity) hH.le]
        gcongr
      _ = (2*C*H^d)*((2:ℝ)^n*(1/4:ℝ)^n) := by rw [pow_succ]; ring
      _ = _ := by rw [←mul_pow]; norm_num
  have hsum : (∑ x∈E,(1+q x/H)^(-2:ℝ)) =
      ∑ n∈E.image bin, ∑ x∈E.filter (fun x=>bin x=n), (1+q x/H)^(-2:ℝ) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) _
  rw [hsum]
  apply (Finset.sum_le_sum (fun n _=>hbin n)).trans
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)).mul_left (2*C*H^d)
  apply (Summable.sum_le_tsum _ (by intro n _; positivity) hs).trans_eq
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)]
  ring

theorem nonzero_frequency_count (E : Finset O) (R : ℝ) (hR : 0 < R)
    (hE : ∀ k∈E, k≠0) (hN : ∀ k∈E, frequencyNorm k≤R) :
    (E.card:ℝ) ≤ 128*R := by
  by_cases hr : 1≤R
  · apply DescentFiberCost.finite_element_count_real E R hr
    intro k hk
    simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,frequencyNorm]
      using hN k hk
  · have he : E=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro k hk
      have hh := frequencyNorm_one_le k (hE k hk)
      have hb := hN k hk
      linarith)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem frequency_weighted_sum :
    ∃ K : ℝ, 0<K ∧ ∀ (E : Finset O) (H : ℝ), 0<H →
      (∀ k∈E,k≠0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤ K*H := by
  refine ⟨512,by norm_num,?_⟩
  intro E H hH hE
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    128 1 H (by norm_num) (by norm_num) hH (by
      intro F hFE R hR hN
      simpa only [Real.rpow_one] using
        nonzero_frequency_count F R hR (fun k hk=>hE k (hFE hk)) hN)
  norm_num only [Real.rpow_one,show (4:ℝ)*128=512 by norm_num] at hh
  exact hh

theorem exceptional_frequency_weighted_sum (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ, 0<K ∧ ∀ G : Ideal O, G≠0 → ∀ (E : Finset O) (H : ℝ), 0<H →
      (∀ k∈E,k≠0) →
      (∀ k∈E,∀ P∉IdealMobiusDivisorSum.primeSupport G,
        CenteredExceptionalCount.valuation (Ideal.span {k}) P % 6=0) →
      ∑ k∈E,(1+frequencyNorm k/H)^(-2:ℝ) ≤
        K*(Ideal.absNorm G:ℝ)^ε*H^(1/6:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := ProbePhysical.lowGramExceptional_count ε hε
  refine ⟨4*C,by positivity,?_⟩
  intro G hG E H hH hE hres
  have hh := finite_weighted_of_count E frequencyNorm frequencyNorm_nonneg
    (C*(Ideal.absNorm G:ℝ)^ε) (1/6) H (by positivity) (by norm_num) hH (by
      intro F hFE R hR hN
      exact hcount G hG F R hR.le (fun k hk=>hE k (hFE hk))
        (fun k hk=>hres k (hFE hk)) hN)
  convert hh using 1
  ring

end SevenEighths.ProbeGramFrequencySummation

end

end OAI
end OAIOriginalModule0485

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Phase
Source SHA256: 410cb5e78d9182c1d215bf98800886db38237408e6cc270b1d649c4f529cfc66
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0486


namespace OAI

noncomputable section
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates QuadraticGaussRay ConcreteTraceCRT
open QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

def G (a : O) : ℂ := fixedGQuotientValue (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)

def reciprocitySign (a b : O) : ℂ :=
  (quadraticRaySign (residue a) (residue b) : ℂ)

theorem G_mul (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    G (a * b) = G a * G b * reciprocitySign a b := by
  change fixedGValue (residue (a * b)) = fixedGValue (residue a) * fixedGValue (residue b) * reciprocitySign a b
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_mul, mul_inv_rev, residue_mul]
  rw [quadraticRayValue_mul _ _ ha hb]
  unfold reciprocitySign
  ring

theorem reciprocitySign_mul_right (a b c : O) :
    reciprocitySign a (b * c) = reciprocitySign a b * reciprocitySign a c := by
  simp only [reciprocitySign, residue_mul, quadraticRaySign_mul_right, Int.cast_mul]

theorem reciprocitySign_sq (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    reciprocitySign a b ^ 2 = 1 := by
  unfold reciprocitySign
  exact_mod_cast quadraticRaySign_sq (residue a) (residue b) ha hb

theorem reciprocitySign_cube_right (a b : O)
    (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hb : EisensteinEPrimaryPhase.odd (residue b)) :
    reciprocitySign a (b ^ 3) = reciprocitySign a b := by
  rw [show b ^ 3 = b ^ 2 * b by ring, reciprocitySign_mul_right,
    pow_two, reciprocitySign_mul_right]
  have hs := reciprocitySign_sq a b ha hb
  calc
    _ = reciprocitySign a b ^ 2 * reciprocitySign a b := by ring
    _ = reciprocitySign a b := by rw [hs, one_mul]

theorem G_completed_index (c n : O)
    (hc : EisensteinEPrimaryPhase.odd (residue c))
    (hn : EisensteinEPrimaryPhase.odd (residue n)) :
    G (c * n ^ 3) = G c * reciprocitySign c n * G (n ^ 3) := by
  have hn3 : EisensteinEPrimaryPhase.odd (residue (n ^ 3)) := by
    rw [show n ^ 3 = (n * n) * n by ring, residue_mul, residue_mul]
    exact QuadraticAllOddCRT.odd_mul _ _ (QuadraticAllOddCRT.odd_mul _ _ hn hn) hn
  rw [G_mul c (n ^ 3) hc hn3, reciprocitySign_cube_right c n hc hn]
  ring

theorem quadraticRayValue_cube (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) :
    quadraticRayValue (EisensteinEPrimaryPhase.mul
      (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayValue r := by
  have he : ∀ r : EisensteinEPrimaryPhase.Coord, EisensteinEPrimaryPhase.odd r →
      quadraticRayExponent (EisensteinEPrimaryPhase.mul
        (EisensteinEPrimaryPhase.mul r r) r) = quadraticRayExponent r := by decide
  rw [quadraticRayValue_eq_fourthRoot _ (odd_mul _ _ (odd_mul _ _ hr hr) hr),
    he r hr, ← quadraticRayValue_eq_fourthRoot r hr]

theorem G_cube (a : O) (ha : EisensteinEPrimaryPhase.odd (residue a))
    (hu : IsUnit (Ideal.Quotient.mk cubicTwoIdeal a)) :
    G (a ^ 3) = quadraticRayValue (residue a) := by
  have hχ := congrArg
    (fun η : MulChar (O ⧸ cubicTwoIdeal) O => η (Ideal.Quotient.mk cubicTwoIdeal a))
    (cubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), MulChar.one_apply hu] at hχ
  have hc := congrArg eisEmbedding hχ
  simp only [map_pow, map_one] at hc
  change fixedGValue (residue (a ^ 3)) = quadraticRayValue (residue a)
  simp only [fixedGValue, ← fixed_two_mk_eq_residue_lift]
  simp only [map_pow, hc, inv_one, one_mul]
  rw [show a ^ 3 = (a * a) * a by ring, residue_mul, residue_mul]
  exact quadraticRayValue_cube (residue a) ha

end SevenEighths.ProbePhase
end

end OAI
end OAIOriginalModule0486

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Completed
Source SHA256: aacdde1452e633f7190ef1170925afa84cb14f38222898cf4ca6c91cae7b843a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0487



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompleted
open ActualEisensteinCubic CompletedGauss
open RayFourExpansion QuadraticGaussRay SecondPassArithmetic

local notation "O" => ActualEisensteinCubic.O

def completedIndex (I J : Ideal O) : O := primaryGenerator I * primaryGenerator J ^ 3

def completedMask (S : Finset (Ideal O)) (D I J : Ideal O) : ℂ :=
  if D ∣ I * J ^ 3 ∧ ∀ p ∈ S, ¬p ∣ I * J ^ 3 then 1 else 0

def completedCorrection (I J : Ideal O) : ℂ :=
  rayMask (completedIndex I J) *
    star (fixedGQuotientValue
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (completedIndex I J)))

theorem completedCorrection_eq_phase (I J : Ideal O) :
    completedCorrection I J = rayMask (completedIndex I J) *
      star (ProbePhase.G (completedIndex I J)) := rfl

theorem completedMask_norm_le_one (S : Finset (Ideal O)) (D I J : Ideal O) :
    ‖completedMask S D I J‖ ≤ 1 := by
  unfold completedMask
  split_ifs <;> norm_num

theorem completedCorrection_norm_le_two (I J : Ideal O) :
    ‖completedCorrection I J‖ ≤ 2 := by
  have hm : ‖rayMask (completedIndex I J)‖ ≤ 1 := by
    unfold rayMask
    split_ifs <;> norm_num
  unfold completedCorrection
  rw [norm_mul, norm_star]
  exact (mul_le_mul hm (fixedGQuotientValue_norm_le_two _) (norm_nonneg _) (by norm_num)).trans_eq
    (by norm_num)

def markedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedMask S D I J * summand Ψ W X I J

def correctedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedCorrection I J * markedSummand S D Ψ W X I J

def markedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, markedSummand S D Ψ W X p.1 p.2

def correctedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, correctedSummand S D Ψ W X p.1 p.2

def correctionCoeff (χ : RayCharacter) : ℂ :=
  phaseCoeff (fun r => star (fixedGQuotientValue r)) χ

theorem correctionCoeff_sum_norm_le :
    (∑ χ : RayCharacter, ‖correctionCoeff χ‖) ≤ 32 := by
  have h := phaseCoeff_sum_norm_le (fun r => star (fixedGQuotientValue r)) 2
    (fun u => by simpa only [norm_star] using fixedGQuotientValue_norm_le_two (u : RayRing))
  simpa only [correctionCoeff] using h.trans_eq (by norm_num : (16 : ℝ) * 2 = 32)

theorem completedIndex_eq_primaryGenerator (I J : Ideal O) :
    completedIndex I J = primaryGenerator (I * J ^ 3) := by
  simp only [completedIndex, primaryGenerator_mul, CubicEisenstein.primaryGenerator_pow]

theorem completedMask_zero_of_excluded (S : Finset (Ideal O)) (D I J p : Ideal O)
    (hp : p ∈ S) (hpdiv : p ∣ I * J ^ 3) : completedMask S D I J = 0 := by
  unfold completedMask
  rw [ite_eq_right]
  intro h
  exact h.2 p hp hpdiv

theorem completedMask_zero_of_not_marked (S : Finset (Ideal O)) (D I J : Ideal O)
    (hD : ¬D ∣ I * J ^ 3) : completedMask S D I J = 0 := by
  simp [completedMask, hD]

theorem completedCorrection_expansion (I J : Ideal O) :
    completedCorrection I J =
      ∑ χ : RayCharacter, correctionCoeff χ * rayCharacter χ (completedIndex I J) := by
  exact phase_expansion (fun r => star (fixedGQuotientValue r)) (completedIndex I J)

theorem correctedSummand_ray_expansion (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) :
    correctedSummand S D Ψ W X I J =
      ∑ χ : RayCharacter, correctionCoeff χ *
        markedSummand S D (rayMonoid χ * Ψ) W X I J := by
  unfold correctedSummand
  rw [completedCorrection_expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro χ _
  unfold markedSummand
  rw [CanonicalRowCompletion.summand_mul_fixed_twist]
  simp only [rayMonoid_apply, completedIndex]
  ring

theorem markedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => markedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
  intro p hp
  exact fun hz => hp (by simp only [markedSummand, hz, mul_zero])

theorem correctedSummand_summable (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : Ideal O × Ideal O => correctedSummand S D Ψ W X p.1 p.2) := by
  apply summable_of_hasFiniteSupport
  apply (completedT_finite_support Ψ W hW X hX).subset
