    (hsource : ∀ i ≤ k,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := by
  let V : ℝ := 2 ^ (volume : Measure ℝ).integrablePower *
    ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hI (i : ℕ) (hi : i ≤ k) :
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤ V * C := by
    have hbase := SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume g 0 i
    have hbase' :
        (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) := by
      simpa [V] using hbase
    calc
      S * (∫ t : ℝ, ‖iteratedFDeriv ℝ i g t‖) ≤
          S * (V * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) :=
        mul_le_mul_of_nonneg_left hbase' hS
      _ = V * (S * ((SchwartzMap.seminorm ℝ 0 i) g +
            (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)) := by ring
      _ ≤ V * C := mul_le_mul_of_nonneg_left (hsource i hi) hV
  have hFourier := fourier_seminorm_from_derivative_integrals g k
  calc
    S * (SchwartzMap.seminorm ℝ k 0) (𝓕 g) ≤
      S * ((2 : ℝ) ^ k *
        ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
          ∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) :=
      mul_le_mul_of_nonneg_left hFourier hS
    _ = (2 : ℝ) ^ k *
      ∑ p ∈ Finset.range 1 ×ˢ Finset.range (k + 1),
        S * (∫ t : ℝ, ‖t‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 g t‖) := by
      simp only [Finset.mul_sum]
      ring_nf
    _ ≤ (2 : ℝ) ^ k *
      ∑ _p ∈ Finset.range 1 ×ˢ Finset.range (k + 1), V * C := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : p.1 = 0 := by
        have hlt := Finset.mem_range.mp (Finset.mem_product.mp hp).1
        omega
      have hp2 : p.2 ≤ k := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
      simpa [hp0] using hI p.2 hp2
    _ = (2 : ℝ) ^ k * (k + 1) * V * C := by
      simp []
      ring
    _ = (2 : ℝ) ^ k * (k + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C := rfl

theorem uniform_fourier_coefficient_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C) := by
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  let K := J + p
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hfourier_zero := uniform_fourier_seminorm_transfer g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hfourier_K := uniform_fourier_seminorm_transfer g K S C hS hC
    (by intro i hi; exact hsource i (by simpa [K, p] using hi))
  have hmoment := fourier_coefficient_moment g J
  calc
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
        S * (V * ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
          (SchwartzMap.seminorm ℝ K 0) (𝓕 g))) :=
      mul_le_mul_of_nonneg_left (by simpa [V, K, p] using hmoment) hS
    _ = V * (S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        S * (SchwartzMap.seminorm ℝ K 0) (𝓕 g)) := by ring
    _ ≤ V * ((2 : ℝ) ^ 0 * (0 + 1) * V * C +
        (2 : ℝ) ^ K * (K + 1) * V * C) := by
      apply mul_le_mul_of_nonneg_left _ hV
      exact add_le_add (by simpa [V] using hfourier_zero)
        (by simpa [K, V] using hfourier_K)
    _ = _ := by simp [V, K, p, Nat.cast_add]

noncomputable def profileDerivativeConstant (n : ℕ) (H CW CF : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * CW *
      ((n - i).factorial * CF * (H ^ 2) ^ (n - i))

theorem profileDerivativeConstant_nonneg (n : ℕ) (H CW CF : ℝ)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ profileDerivativeConstant n H CW CF := by
  unfold profileDerivativeConstant
  apply Finset.sum_nonneg
  intro i hi
  positivity

noncomputable def profileMomentConstant (K : ℕ) (L H CW CF : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K + 1),
    (1 + L ^ (volume : Measure ℝ).integrablePower) *
      profileDerivativeConstant j H CW CF

theorem profileMomentConstant_nonneg (K : ℕ) (L H CW CF : ℝ)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ profileMomentConstant K L H CW CF := by
  unfold profileMomentConstant
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (by positivity)
    (profileDerivativeConstant_nonneg j H CW CF hCW hCF)

theorem profileMomentConstant_dominates (K j : ℕ) (L H CW CF : ℝ)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) (hj : j ≤ K) :
    (1 + L ^ (volume : Measure ℝ).integrablePower) *
      profileDerivativeConstant j H CW CF ≤
      profileMomentConstant K L H CW CF := by
  unfold profileMomentConstant
  apply Finset.single_le_sum
    (f := fun i : ℕ =>
      (1 + L ^ (volume : Measure ℝ).integrablePower) *
        profileDerivativeConstant i H CW CF)
    (a := j)
  · intro i hi
    exact mul_nonneg (by positivity)
      (profileDerivativeConstant_nonneg i H CW CF hCW hCF)
  · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)

theorem uniform_logProfile_source_pair
    (W F : ℝ → ℂ) (R a m H L CW CF C : ℝ) (A K n : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K)
    (hWderiv : ∀ i ≤ K, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ K, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ K, ∀ i ≤ j, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (hCbound : ∀ j ≤ K,
      (1 + L ^ (volume : Measure ℝ).integrablePower) *
        profileDerivativeConstant j H CW CF ≤ C) :
    (m ^ (A + K) * (1 + R) ^ A) *
      ((SchwartzMap.seminorm ℝ 0 n)
          (logProfile W F R a hWc hWs hFs) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n)
          (logProfile W F R a hWc hWs hFs)) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  let D : ℝ := profileDerivativeConstant n H CW CF
  let g := logProfile W F R a hWc hWs hFs
  have hWderiv_n : ∀ i ≤ n, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW := by
    intro i hi y
    exact hWderiv i (hi.trans hn) y
  have hwindow_n : ∀ y,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L := by
    intro y hy
    obtain ⟨i, hi, hnonzero⟩ := hy
    exact hwindow y ⟨i, hi.trans hn, hnonzero⟩
  have hFdecay_n : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF :=
    hFdecay n hn
  have hzero := logProfile_uniform_seminorm W F R a m H L CW CF A n 0
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF
    hWderiv_n hwindow_n hFdecay_n
  have hp := logProfile_uniform_seminorm W F R a m H L CW CF A n p
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF
    hWderiv_n hwindow_n hFdecay_n
  have hscale : m ^ (A + K) * (1 + R) ^ A ≤
      m ^ (A + n) * (1 + R) ^ A :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one hm.le hm1 (by omega)) (by positivity)
  have hsemi0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 n) g := by positivity
  have hsemip : 0 ≤ (SchwartzMap.seminorm ℝ p n) g := by positivity
  have hzero' : (m ^ (A + K) * (1 + R) ^ A) *
      (SchwartzMap.seminorm ℝ 0 n) g ≤ D := by
    calc
      _ ≤ (m ^ (A + n) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ 0 n) g :=
        mul_le_mul_of_nonneg_right hscale hsemi0
      _ ≤ D := by simpa [D, profileDerivativeConstant, g] using hzero
  have hp' : (m ^ (A + K) * (1 + R) ^ A) *
      (SchwartzMap.seminorm ℝ p n) g ≤ L ^ p * D := by
    calc
      _ ≤ (m ^ (A + n) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ p n) g :=
        mul_le_mul_of_nonneg_right hscale hsemip
      _ ≤ L ^ p * D := by simpa [D, profileDerivativeConstant, g, p] using hp
  calc
    (m ^ (A + K) * (1 + R) ^ A) *
        ((SchwartzMap.seminorm ℝ 0 n) g +
          (SchwartzMap.seminorm ℝ p n) g) =
        (m ^ (A + K) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ 0 n) g +
        (m ^ (A + K) * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ p n) g := by ring
    _ ≤ D + L ^ p * D := add_le_add hzero' hp'
    _ = (1 + L ^ p) * D := by ring
    _ ≤ C := by simpa [D, p] using hCbound n hn

theorem uniform_logProfile_coefficient_moment
    (W F : ℝ → ℂ) (R a m H L CW CF C : ℝ) (A J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) (hC : 0 ≤ C)
    (hWderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ i ≤ j, ∀ u, 0 ≤ u →
        (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (hCbound : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      (1 + L ^ (volume : Measure ℝ).integrablePower) *
        profileDerivativeConstant j H CW CF ≤ C) :
    (m ^ (A + (J + (volume : Measure ℝ).integrablePower)) *
      (1 + R) ^ A) *
      (∫ t : ℝ, ‖t‖ ^ J *
        ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C) := by
  apply uniform_fourier_coefficient_moment _ J _ C (by positivity) hC
  intro i hi
  exact uniform_logProfile_source_pair W F R a m H L CW CF C A
    (J + (volume : Measure ℝ).integrablePower) i
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF hi
    hWderiv hwindow hFdecay hCbound

theorem uniform_logProfile_coefficient_moment_explicit
    (W F : ℝ → ℂ) (R a m H L CW CF : ℝ) (A J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ i ≤ j, ∀ u, 0 ≤ u →
        (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    (m ^ (A + (J + (volume : Measure ℝ).integrablePower)) *
      (1 + R) ^ A) *
      (∫ t : ℝ, ‖t‖ ^ J *
        ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
          profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
          profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF) := by
  apply uniform_logProfile_coefficient_moment W F R a m H L CW CF
    (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
      L H CW CF) A J
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF
    (profileMomentConstant_nonneg _ L H CW CF hL hCW hCF)
    hWderiv hwindow hFdecay
  intro j hj
  exact profileMomentConstant_dominates _ j L H CW CF hL hCW hCF hj

noncomputable def coefficientMomentBound (J : ℕ) (C : ℝ) : ℝ :=
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  V * (V * C + (2 : ℝ) ^ (J + p) * (J + p + 1) * V * C)

theorem coefficientMomentBound_nonneg (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ coefficientMomentBound J C := by
  unfold coefficientMomentBound
  positivity

theorem uniform_fourier_one_plus_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) ≤
      (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa using b.integrable_pow_mul volume 0
  have hIJ : Integrable (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hIrhs : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hpow := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hintegral :
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
    calc
      _ ≤ ∫ t : ℝ, (2 : ℝ) ^ J *
          (‖b t‖ + ‖t‖ ^ J * ‖b t‖) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (by intro t; positivity))
          hIrhs (Filter.Eventually.of_forall hpoint)
      _ = (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
        rw [integral_const_mul, integral_add hI0 hIJ]
  have hbound0 := uniform_fourier_coefficient_moment g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hboundJ := uniform_fourier_coefficient_moment g J S C hS hC hsource
  calc
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        S * ((2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖))) :=
      mul_le_mul_of_nonneg_left hintegral hS
    _ = (2 : ℝ) ^ J *
        (S * (∫ t : ℝ, ‖b t‖) +
          S * (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by ring
    _ ≤ (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · simpa [coefficientMomentBound, b] using hbound0
      · simpa [coefficientMomentBound, b] using hboundJ

noncomputable def logPhase (t y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t * y : ℝ) : ℂ) * Complex.I)

theorem logPhase_add (t u v : ℝ) :
    logPhase t (u + v) = logPhase t u * logPhase t v := by
  unfold logPhase
  convert Complex.exp_add _ _ using 1 ; push_cast ; ring_nf

theorem logPhase_zero (t : ℝ) : logPhase t 0 = 1 := by
  simp [logPhase]

theorem logPhase_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ℝ) (z : ι → ℝ) :
    logPhase t (∑ i ∈ s, z i) = ∏ i ∈ s, logPhase t (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logPhase_zero]
  | @insert i s hi ih => simp [hi, logPhase_add, ih]

theorem coupled_cutoff_active
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (V : ℝ → ℂ) (a y M : ι → ℝ)
    (hwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hVone : ∀ s,
      |s| ≤ ∑ j : ι, |a j| * M j → V s = 1)
    (hprod : (∏ j : ι, W j (y j)) ≠ 0) :
    V (∑ j : ι, a j * y j) = 1 := by
  classical
  apply hVone
  calc
    |∑ j : ι, a j * y j| ≤ ∑ j : ι, |a j * y j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : ι, |a j| * M j := by
      apply Finset.sum_le_sum
      intro j hj
      have hnonzero : W j (y j) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ j)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hwindow j (y j) hnonzero) (abs_nonneg _)

theorem exists_complex_smooth_cutoff (T : ℝ) (hT : 0 ≤ T) :
    ∃ V : ℝ → ℂ,
      HasCompactSupport V ∧
      ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      tsupport V ⊆ Set.Icc (-(T + 1)) (T + 1) ∧
      V 0 = 1 := by
  let U : Set ℝ := Set.Ioo (-(T + 1)) (T + 1)
  let K : Set ℝ := Set.Icc (-T) T
  have hU : IsOpen U := isOpen_Ioo
  have hK : IsClosed K := isClosed_Icc
  have hKU : K ⊆ U := by
    intro s hs
    rcases hs with ⟨hleft, hright⟩
    constructor <;> linarith
  obtain ⟨f, hf, _, hsupport, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hU hK hKU
  let V : ℝ → ℂ := fun s => (f s : ℂ)
  have hf' : ContDiff ℝ ∞ f := by simpa using hf
  have hVs : ContDiff ℝ ∞ V := Complex.ofRealCLM.contDiff.comp hf'
  have hVsupport : Function.support V = Function.support f := by
    ext s
    simp [V, Function.mem_support]
  have hVsupportI : Function.support V ⊆
      Set.Icc (-(T + 1)) (T + 1) := by
    intro s hs
    rw [hVsupport, hsupport] at hs
    exact ⟨hs.1.le, hs.2.le⟩
  have hVtsupportI : tsupport V ⊆
      Set.Icc (-(T + 1)) (T + 1) :=
    closure_minimal hVsupportI isClosed_Icc
  have hVc : HasCompactSupport V :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hVsupportI
  have hone' : ∀ s, |s| ≤ T → V s = 1 := by
    intro s hs
    have hsK : s ∈ K := by simpa [K, abs_le] using hs
    have hfs : f s = 1 := (hone s).mp hsK
    simp [V, hfs]
  exact ⟨V, hVc, hVs, hone', hVtsupportI,
    hone' 0 (by simpa using hT)⟩

theorem exists_complex_smooth_cutoff_with_derivative_bounds
    (T : ℝ) (K : ℕ) (hT : 0 ≤ T) :
    ∃ (V : ℝ → ℂ) (CW : ℝ),
      HasCompactSupport V ∧ ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      0 ≤ CW ∧
      (∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i V y‖ ≤ CW) ∧
      (∀ y,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
          Real.exp (-(T + 1)) ≤ Real.exp y ∧
          Real.exp y ≤ Real.exp (T + 1) ∧ |y| ≤ T + 1) := by
  obtain ⟨V, hVc, hVs, hVone, hVsupport, _⟩ :=
    exists_complex_smooth_cutoff T hT
  obtain ⟨CW, hCW, hVderiv⟩ :=
    hVc.exists_bound_iteratedFDeriv hVs K
  refine ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, ?_⟩
  intro y hy
  obtain ⟨i, hi, hnonzero⟩ := hy
  have hyderiv : y ∈ Function.support (iteratedFDeriv ℝ i V) := by
    simpa [Function.mem_support] using hnonzero
  have hysupport : y ∈ tsupport V :=
    (support_iteratedFDeriv_subset i) hyderiv
  have hyinterval := hVsupport hysupport
  have hylower : -(T + 1) ≤ y := hyinterval.1
  have hyupper : y ≤ T + 1 := hyinterval.2
  constructor
  · exact Real.exp_le_exp.mpr hylower
  constructor
  · exact Real.exp_le_exp.mpr hyupper
  · exact abs_le.mpr ⟨hylower, hyupper⟩

noncomputable def schwartzDerivativeDecayConstant
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) : ℝ :=
  (2 : ℝ) ^ M *
    ∑ i ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 i) F +
        (SchwartzMap.seminorm ℝ M i) F)

theorem schwartzDerivativeDecayConstant_nonneg
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) :
    0 ≤ schwartzDerivativeDecayConstant F M K := by
  unfold schwartzDerivativeDecayConstant
  positivity

theorem schwartz_derivative_decay_finite
    (F : 𝓢(ℝ, ℂ)) (A K j i : ℕ) (u : ℝ)
    (hj : j ≤ K) (hi : i ≤ j) (hu : 0 ≤ u) :
    (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤
      schwartzDerivativeDecayConstant F (A + K) K := by
  let M := A + K
  let T : ℝ := (SchwartzMap.seminorm ℝ 0 i) F +
    (SchwartzMap.seminorm ℝ M i) F
  let N : ℝ := ‖iteratedFDeriv ℝ i F u‖
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpow : (1 + u) ^ (A + j) ≤ (1 + u) ^ M :=
    pow_le_pow_right₀ (by linarith) (by dsimp [M]; omega)
  have hadd := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) hu M
  have htwo : (2 : ℝ) ^ (M - 1) ≤ (2 : ℝ) ^ M :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le M 1)
  have hsum : (1 + u) ^ M * N ≤ (2 : ℝ) ^ M *
      (N + u ^ M * N) := by
    calc
      (1 + u) ^ M * N ≤
          (2 : ℝ) ^ (M - 1) * (1 ^ M + u ^ M) * N :=
        mul_le_mul_of_nonneg_right hadd hN
      _ ≤ (2 : ℝ) ^ M * (1 ^ M + u ^ M) * N := by
        gcongr
      _ = (2 : ℝ) ^ M * (N + u ^ M * N) := by
        simp; ring
  have h0 : N ≤ (SchwartzMap.seminorm ℝ 0 i) F := by
    simpa [N] using SchwartzMap.le_seminorm ℝ 0 i F u
  have hM : u ^ M * N ≤ (SchwartzMap.seminorm ℝ M i) F := by
    simpa [N, Real.norm_eq_abs, abs_of_nonneg hu] using
      SchwartzMap.le_seminorm ℝ M i F u
  have hT : N + u ^ M * N ≤ T := add_le_add h0 hM
  have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
  have hTsum : T ≤ ∑ k ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 k) F +
        (SchwartzMap.seminorm ℝ M k) F) := by
    apply Finset.single_le_sum
      (f := fun k : ℕ =>
        (SchwartzMap.seminorm ℝ 0 k) F +
          (SchwartzMap.seminorm ℝ M k) F)
      (a := i)
    · intro k hk
      positivity
    · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hi.trans hj))
  calc
    (1 + u) ^ (A + j) * N ≤ (1 + u) ^ M * N :=
      mul_le_mul_of_nonneg_right hpow hN
    _ ≤ (2 : ℝ) ^ M * (N + u ^ M * N) := hsum
    _ ≤ (2 : ℝ) ^ M * T :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (2 : ℝ) ^ M *
        (∑ k ∈ Finset.range (K + 1),
          ((SchwartzMap.seminorm ℝ 0 k) F +
            (SchwartzMap.seminorm ℝ M k) F)) :=
      mul_le_mul_of_nonneg_left hTsum (by positivity)
    _ = schwartzDerivativeDecayConstant F (A + K) K := rfl

theorem coupled_log_separation
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F V : ℝ → ℂ) (R : ℝ)
    (a y : ι → ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFs : ContDiff ℝ ∞ F)
    (hactive : (∏ j : ι, W j (y j)) ≠ 0 →
      V (∑ j : ι, a j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F (R * Real.exp (∑ j : ι, a j * y j)) =
      ∫ t : ℝ,
        (∏ j : ι, W j (y j) * logPhase t (a j * y j)) *
          (𝓕 (logProfile V F R 1 hVc hVs hFs)) t := by
  classical
  let s : ℝ := ∑ j : ι, a j * y j
  let P : ℂ := ∏ j : ι, W j (y j)
  let b := 𝓕 (logProfile V F R 1 hVc hVs hFs)
  have hsep : V s * F (R * Real.exp s) =
      ∫ t : ℝ, logPhase t s * b t := by
    calc
      V s * F (R * Real.exp s) =
          ∫ t : ℝ, Complex.exp
            ((↑(2 * Real.pi * inner ℝ t s) * Complex.I)) * b t := by
        simpa [b] using
          (smooth_log_separation V F R 1 s hVc hVs hFs)
      _ = ∫ t : ℝ, logPhase t s * b t := by
        apply integral_congr_ae
        filter_upwards [] with t
        congr 1
        simp only [logPhase, Real.inner_apply]
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
    _ = P * (∫ t : ℝ, logPhase t s * b t) := by rw [hsep]
    _ = ∫ t : ℝ, P * (logPhase t s * b t) := by
      rw [integral_const_mul]
    _ = ∫ t : ℝ,
          (∏ j : ι, W j (y j) * logPhase t (a j * y j)) * b t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show logPhase t s = ∏ j : ι, logPhase t (a j * y j) by
        simpa [s] using logPhase_sum (Finset.univ : Finset ι) t
          (fun j => a j * y j)]
      rw [Finset.prod_mul_distrib]
      simp only [P]
      ring

theorem coupled_log_coefficient_bound
    (V F : ℝ → ℂ) (R m H L CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (hL : 0 ≤ L)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ y,
      ‖iteratedFDeriv ℝ i V y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
        m ≤ Real.exp y ∧ Real.exp y ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ i ≤ j, ∀ u, 0 ≤ u →
        (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    (m ^ (A + (J + (volume : Measure ℝ).integrablePower)) *
      (1 + R) ^ A) *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (logProfile V F R 1 hVc hVs hFs)) t‖) ≤
      (2 : ℝ) ^ J *
        (coefficientMomentBound 0
          (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF) +
        coefficientMomentBound J
          (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF)) := by
  apply uniform_fourier_one_plus_moment _ J _ _ (by positivity)
    (profileMomentConstant_nonneg _ L H CW CF hL hCW hCF)
  intro i hi
  exact uniform_logProfile_source_pair V F R 1 m H L CW CF
    (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
      L H CW CF) A
    (J + (volume : Measure ℝ).integrablePower) i
    hVc hVs hFs hR hm hm1 hH (by simpa using hH)
    hL hCW hCF hi hVderiv
    (by simpa only [one_mul] using hwindow)
    hFdecay
    (by intro j hj
        exact profileMomentConstant_dominates _ j L H CW CF
          hL hCW hCF hj)

theorem coupled_log_separation_schwartz
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : 𝓢(ℝ, ℂ)) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ (b : ℝ → ℝ → ℂ) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 ≤ R →
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) * logPhase t (a j * y j)) *
              b R t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b R t‖) ≤ C := by
  classical
  let T : ℝ := ∑ j : ι, |a j| * M j
  have hT : 0 ≤ T := by
    dsimp [T]
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (abs_nonneg _) (hM j)
  let K : ℕ := J + (volume : Measure ℝ).integrablePower
  let L : ℝ := T + 1
  let m : ℝ := Real.exp (-L)
  let H : ℝ := Real.exp L
  let CF : ℝ := schwartzDerivativeDecayConstant F (A + K) K
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hm : 0 < m := Real.exp_pos _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    simpa using (Real.exp_le_exp.mpr (show -L ≤ 0 by linarith))
  have hH : 1 ≤ H := by
    dsimp [H]
    simpa using (Real.exp_le_exp.mpr hL)
  have hCF : 0 ≤ CF := schwartzDerivativeDecayConstant_nonneg F (A + K) K
  obtain ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, hwindow⟩ :=
    exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  let b : ℝ → ℝ → ℂ :=
    fun R t => (𝓕 (logProfile V F R 1 hVc hVs (F.smooth ⊤))) t
  let P : ℝ := profileMomentConstant K L H CW CF
  let B : ℝ := (2 : ℝ) ^ J *
    (coefficientMomentBound 0 P + coefficientMomentBound J P)
  let C : ℝ := B / m ^ (A + K)
  have hP : 0 ≤ P :=
    profileMomentConstant_nonneg K L H CW CF hL hCW hCF
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity)
      (add_nonneg
        (coefficientMomentBound_nonneg 0 P hP)
        (coefficientMomentBound_nonneg J P hP))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨b, C, hC, ?_⟩
  intro R hR
  constructor
  · intro y
    have hactive : (∏ j : ι, W j (y j)) ≠ 0 →
        V (∑ j : ι, a j * y j) = 1 :=
      coupled_cutoff_active W V a y M hWwindow
        (by simpa [T] using hVone)
    simpa [b] using coupled_log_separation W F V R a y
      hVc hVs (F.smooth ⊤) hactive
  · have hbound := coupled_log_coefficient_bound V F R m H L CW CF A J
      hVc hVs (F.smooth ⊤) hR hm hm1 hH hL hCW hCF
      (by simpa [K] using hVderiv)
      (by simpa [m, H, L, K] using hwindow)
      (by intro j hj i hi u hu
          exact schwartz_derivative_decay_finite F A K j i u
            (by simpa [K] using hj) hi hu)
    have hmPow : 0 < m ^ (A + K) := pow_pos hm _
    dsimp [C]
    apply (le_div_iff₀ hmPow).mpr
    simpa [B, P, b, K, m, H, L, CF,
      mul_comm, mul_left_comm, mul_assoc] using hbound

end FourierBridge

end OAI
end OAIOriginalModule0035

/-! Original module: OAI.NumberTheory.DirichletL.ChineseRemainder.AdditiveCharacters
Source SHA256: faab90406b9a9982bd194d85f10bbd5bea3901950b9e66e1767813c1f7bd6e36
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0036


namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

namespace ShortDraftCRT

open AddChar

variable {K : Type*} [Field K]

theorem addChar_crt_pair (ψ : AddChar K ℂ) (m n u v z : K)
    (hm : m ≠ 0) (hn : n ≠ 0) (hbez : u * n + v * m = 1) :
    ψ (z / (m * n)) = ψ (u * z / m) * ψ (v * z / n) := by
  rw [← map_add_eq_mul]
  congr 1
  calc
    z / (m * n) = z * (u * n + v * m) / (m * n) := by rw [hbez, mul_one]
    _ = u * z / m + v * z / n := by
      field_simp

theorem addChar_crt_of_isCoprime
    {R : Type*} [CommRing R] (ι : R →+* K) (ψ : AddChar K ℂ)
    (m n : R) (z : K)
    (hcop : IsCoprime n m) (hm : ι m ≠ 0) (hn : ι n ≠ 0) :
    ∃ u v : R,
      u * n + v * m = 1 ∧
      ψ (z / (ι m * ι n)) =
        ψ (ι u * z / ι m) * ψ (ι v * z / ι n) := by
  obtain ⟨u, v, hbez⟩ := hcop
  refine ⟨u, v, hbez, ?_⟩
  apply addChar_crt_pair ψ (ι m) (ι n) (ι u) (ι v) z hm hn
  simpa only [map_add, map_mul, map_one] using congrArg ι hbez

theorem bezout_with_lam_cube {R : Type*} [CommRing R] (lam c₀ r : R)
    (hcop : IsCoprime r (lam ^ 3 * c₀)) :
    ∃ u v : R,
      u * r + v * c₀ = 1 ∧
      lam ^ 3 ∣ v ∧
      lam ^ 3 * c₀ ∣ u * r - 1 := by
  obtain ⟨u, w, hbez⟩ := hcop
  refine ⟨u, w * lam ^ 3, ?_, ⟨w, by ring⟩, ?_⟩
  · calc
      u * r + (w * lam ^ 3) * c₀ = u * r + w * (lam ^ 3 * c₀) := by ring
      _ = 1 := hbez
  · refine ⟨-w, ?_⟩
    linear_combination hbez

theorem normalized_crt_pair {R : Type*} [CommRing R]
    (ι : R →+* K) (ψ : AddChar K ℂ)
    (lam c₀ r d x u w : R)
    (hlam : ι lam ≠ 0) (hc₀ : ι c₀ ≠ 0) (hr : ι r ≠ 0)
    (hbez : u * r + (lam ^ 3 * w) * c₀ = 1) :
    ψ (-(ι d * (ι x / ι lam ^ 4)) / (ι c₀ * ι r)) =
      ψ (-(ι d * ι u * (ι x / ι lam ^ 4)) / ι c₀) *
        ψ (ι (-d * w * x) / (ι lam * ι r)) := by
  have hbezK : ι u * ι r + ι (lam ^ 3 * w) * ι c₀ = 1 := by
    simpa only [map_add, map_mul, map_one] using congrArg ι hbez
  have hsplit := addChar_crt_pair ψ (ι c₀) (ι r) (ι u)
    (ι (lam ^ 3 * w)) (-(ι d * (ι x / ι lam ^ 4))) hc₀ hr hbezK
  rw [hsplit]
  congr 1
  · congr 1
    ring
  · congr 1
    simp only [map_mul, map_pow, map_neg]
    field_simp

theorem coprime_cross_numerator
    {R : Type*} [CommRing R] (a c₀ h r : R)
    (hfixed : IsCoprime a c₀)
    (hmoving : IsCoprime h r)
    (hmod : IsCoprime c₀ r) :
    IsCoprime (a * r + h * c₀) (c₀ * r) := by
  have hc₀ : IsCoprime (a * r + h * c₀) c₀ := by
    have hbase : IsCoprime (a * r) c₀ := hfixed.mul_left hmod.symm
    exact (IsCoprime.add_mul_right_left_iff).mpr hbase
  have hr : IsCoprime (a * r + h * c₀) r := by
    have hbase : IsCoprime (h * c₀) r := hmoving.mul_left hmod
    rw [add_comm]
    exact (IsCoprime.add_mul_right_left_iff).mpr hbase
  exact hc₀.mul_right hr

variable {R : Type*} [CommRing R]

def crossDen (c₀ : R) : List (R × R) → R
  | [] => c₀
  | (p, _) :: xs => crossDen c₀ xs * p

def crossNum (a c₀ : R) : List (R × R) → R
  | [] => a
  | (p, h) :: xs => crossNum a c₀ xs * p + h * crossDen c₀ xs

def GoodRows (c₀ : R) : List (R × R) → Prop
  | [] => True
  | (p, h) :: xs =>
      GoodRows c₀ xs ∧ IsCoprime h p ∧ IsCoprime (crossDen c₀ xs) p

theorem coprime_cross_num_list (a c₀ : R) (rows : List (R × R))
    (hbase : IsCoprime a c₀) (hrows : GoodRows c₀ rows) :
    IsCoprime (crossNum a c₀ rows) (crossDen c₀ rows) := by
  revert hrows
  induction rows with
  | nil =>
      intro _
      simpa [crossNum, crossDen] using hbase
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      intro hrows
      rcases hrows with ⟨hrows, hhp, hdp⟩
      simpa [crossNum, crossDen] using
        coprime_cross_numerator (crossNum a c₀ rows)
          (crossDen c₀ rows) h p (ih hrows) hhp hdp

theorem crossDen_ne_zero (ι : R →+* K) (c₀ : R)
    (rows : List (R × R)) (hc₀ : ι c₀ ≠ 0)
    (hp : ∀ ph ∈ rows, ι ph.1 ≠ 0) :
    ι (crossDen c₀ rows) ≠ 0 := by
  revert hp
  induction rows with
  | nil =>
      intro _
      simpa [crossDen] using hc₀
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      intro hp
      simp only [crossDen, map_mul]
      exact mul_ne_zero (ih (by
        intro ph hmem
        exact hp ph (List.mem_cons_of_mem _ hmem)))
        (hp (p, h) (List.mem_cons_self ..))

theorem crossDen_eq_product (c₀ : R) (rows : List (R × R)) :
    crossDen c₀ rows = c₀ * (rows.map Prod.fst).prod := by
  induction rows with
  | nil => simp [crossDen]
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      simp only [crossDen, List.map_cons, List.prod_cons, ih]
      ring

theorem crossNum_mod_head (a c₀ p h : R) (rows : List (R × R)) :
    p ∣ crossNum a c₀ ((p, h) :: rows) - h * crossDen c₀ rows := by
  refine ⟨crossNum a c₀ rows, ?_⟩
  simp only [crossNum]
  ring

private theorem product_coprime_of_each (p : R) (rows : List (R × R))
    (h : ∀ ph ∈ rows, IsCoprime ph.1 p) :
    IsCoprime (rows.map Prod.fst).prod p := by
  induction rows with
  | nil => simpa using (isCoprime_one_left : IsCoprime (1 : R) p)
  | cons ph rows ih =>
      rcases ph with ⟨q, k⟩
      simp only [List.map_cons, List.prod_cons]
      exact (h (q, k) (List.mem_cons_self ..)).mul_left
        (ih (by
          intro ph hmem
          exact h ph (List.mem_cons_of_mem _ hmem)))

theorem goodRows_of_pairwise (c₀ : R) (rows : List (R × R))
    (hfixed : ∀ ph ∈ rows, IsCoprime c₀ ph.1)
    (hfreq : ∀ ph ∈ rows, IsCoprime ph.2 ph.1)
    (hpair : rows.Pairwise fun x y => IsCoprime x.1 y.1) :
    GoodRows c₀ rows := by
  induction rows with
  | nil => trivial
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      have hpairhead : ∀ ph ∈ rows, IsCoprime p ph.1 :=
        (List.pairwise_cons.mp hpair).1
      have hpairtail : rows.Pairwise fun x y => IsCoprime x.1 y.1 :=
        (List.pairwise_cons.mp hpair).2
      have hrest : GoodRows c₀ rows := ih
        (by intro ph hmem; exact hfixed ph (List.mem_cons_of_mem _ hmem))
        (by intro ph hmem; exact hfreq ph (List.mem_cons_of_mem _ hmem))
        hpairtail
      have hprod : IsCoprime ((rows.map Prod.fst).prod) p :=
        product_coprime_of_each p rows (by
          intro ph hmem
          exact (hpairhead ph hmem).symm)
      refine ⟨hrest, hfreq (p, h) (List.mem_cons_self ..), ?_⟩
      rw [crossDen_eq_product]
      exact (hfixed (p, h) (List.mem_cons_self ..)).mul_left hprod

theorem cross_fraction_eq (ι : R →+* K) (a c₀ : R)
    (rows : List (R × R)) (hc₀ : ι c₀ ≠ 0)
    (hp : ∀ ph ∈ rows, ι ph.1 ≠ 0) :
    ι (crossNum a c₀ rows) / ι (crossDen c₀ rows) =
      ι a / ι c₀ +
        (rows.map fun ph => ι ph.2 / ι ph.1).sum := by
  revert hp
  induction rows with
  | nil =>
      intro _
      simp [crossNum, crossDen]
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      intro hp
      have hden : ι (crossDen c₀ rows) ≠ 0 :=
        crossDen_ne_zero ι c₀ rows hc₀ (by
          intro ph hmem
          exact hp ph (List.mem_cons_of_mem _ hmem))
      have hp₀ : ι p ≠ 0 := hp (p, h) (List.mem_cons_self ..)
      simp only [crossNum, crossDen, map_add, map_mul,
        List.map_cons, List.sum_cons]
      calc
        (ι (crossNum a c₀ rows) * ι p + ι h * ι (crossDen c₀ rows)) /
            (ι (crossDen c₀ rows) * ι p) =
          ι (crossNum a c₀ rows) / ι (crossDen c₀ rows) + ι h / ι p := by
            field_simp
        _ = ι a / ι c₀ +
            (ι h / ι p + (rows.map fun ph => ι ph.2 / ι ph.1).sum) := by
          rw [ih (by
            intro ph hmem
            exact hp ph (List.mem_cons_of_mem _ hmem))]
          ring

theorem fixed_ray_denominator (a c₀ : R) (rows : List (R × R))
    (hbase : IsCoprime a c₀)
    (hfixed : ∀ ph ∈ rows, IsCoprime c₀ ph.1)
    (hfreq : ∀ ph ∈ rows, IsCoprime ph.2 ph.1)
    (hpair : rows.Pairwise fun x y => IsCoprime x.1 y.1) :
    IsCoprime (crossNum a c₀ rows) (crossDen c₀ rows) ∧
      crossDen c₀ rows = c₀ * (rows.map Prod.fst).prod := by
  exact ⟨coprime_cross_num_list a c₀ rows hbase
    (goodRows_of_pairwise c₀ rows hfixed hfreq hpair),
    crossDen_eq_product c₀ rows⟩

theorem local_epsilon_identity (lam t σ h : K)
    (hlam : lam ≠ 0) (ht : t ≠ 0) (hσ : σ ≠ 0) (hh : h ≠ 0) :
    (-(lam ^ 3 * t * σ)⁻¹) * h⁻¹ * lam ^ 3 =
      -((σ * h)⁻¹) * t⁻¹ := by
  field_simp

theorem addChar_congr_of_dvd
    (ι : R →+* K) (ψ : AddChar K ℂ) (lam d a b x : R)
    (hlam : ι lam ≠ 0) (hd : ι d ≠ 0)
    (hperiod : ∀ y : R, ψ (ι y / ι lam) = 1)
    (hcong : d ∣ a - b) :
    ψ (ι a * ι x / (ι lam * ι d)) =
      ψ (ι b * ι x / (ι lam * ι d)) := by
  obtain ⟨k, hk⟩ := hcong
  have ha : a = b + d * k := by
    calc
      a = b + (a - b) := by ring
      _ = b + d * k := by rw [hk]
  rw [ha, map_add, map_mul]
  have hsplit :
      (ι b + ι d * ι k) * ι x / (ι lam * ι d) =
        ι b * ι x / (ι lam * ι d) + ι (k * x) / ι lam := by
    simp only [map_mul]
    field_simp
  rw [hsplit, map_add_eq_mul, hperiod, mul_one]

private theorem list_prod_coprime_right (p : R) (ps : List R)
    (h : ∀ q ∈ ps, IsCoprime q p) : IsCoprime ps.prod p := by
  induction ps with
  | nil => simpa using (isCoprime_one_left : IsCoprime (1 : R) p)
  | cons q ps ih =>
      simp only [List.prod_cons]
      exact (h q (List.mem_cons_self ..)).mul_left
        (ih (by intro x hx; exact h x (List.mem_cons_of_mem _ hx)))

private theorem list_prod_ne_zero (ι : R →+* K) (ps : List R)
    (h : ∀ p ∈ ps, ι p ≠ 0) : ι ps.prod ≠ 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.prod_cons, map_mul]
      exact mul_ne_zero (h p (List.mem_cons_self ..))
        (ih (by intro q hq; exact h q (List.mem_cons_of_mem _ hq)))

theorem addChar_crt_list_codifferent (ι : R →+* K) (ψ : AddChar K ℂ)
    (lam z : R) (ps : List R)
    (hlam : ι lam ≠ 0)
    (hperiod : ∀ y : R, ψ (ι y / ι lam) = 1)
    (hpair : ps.Pairwise IsCoprime)
    (hp : ∀ p ∈ ps, ι p ≠ 0) :
    ∃ ws : List R, ws.length = ps.length ∧
      ψ (ι z / (ι lam * ι ps.prod)) =
        (List.zipWith (fun p w => ψ (ι (w * z) / (ι lam * ι p))) ps ws).prod := by
  revert z hpair hp
  induction ps with
  | nil =>
      intro z _ _
      refine ⟨[], rfl, ?_⟩
      simpa using hperiod z
  | cons p ps ih =>
      intro z hpair hp
      have hhead : ∀ q ∈ ps, IsCoprime p q :=
        (List.pairwise_cons.mp hpair).1
      have htail : ps.Pairwise IsCoprime :=
        (List.pairwise_cons.mp hpair).2
      have hcop : IsCoprime ps.prod p :=
        list_prod_coprime_right p ps (by
          intro q hq
          exact (hhead q hq).symm)
      have htailnonzero : ι ps.prod ≠ 0 :=
        list_prod_ne_zero ι ps (by
          intro q hq
          exact hp q (List.mem_cons_of_mem _ hq))
      have hpnonzero : ι p ≠ 0 := hp p (List.mem_cons_self ..)
      obtain ⟨u, v, hbez, hsplit⟩ :=
        addChar_crt_of_isCoprime ι ψ p ps.prod (ι z / ι lam)
          hcop hpnonzero htailnonzero
      obtain ⟨ws, hlen, htailphase⟩ := ih (v * z) htail (by
        intro q hq
        exact hp q (List.mem_cons_of_mem _ hq))
      refine ⟨u :: ws.map (· * v), by simp [hlen], ?_⟩
      simp only [List.prod_cons, map_mul]
      have hden : ι z / (ι lam * (ι p * ι ps.prod)) =
          (ι z / ι lam) / (ι p * ι ps.prod) := by field_simp
      rw [hden]
      rw [hsplit]
      simp only [List.zipWith_cons_cons, List.prod_cons]
      have hfirst : ψ (ι u * (ι z / ι lam) / ι p) =
          ψ (ι (u * z) / (ι lam * ι p)) := by
        congr 1
        simp only [map_mul]
        field_simp
      have hsecond : ψ (ι v * (ι z / ι lam) / ι ps.prod) =
          ψ (ι (v * z) / (ι lam * ι ps.prod)) := by
        congr 1
        simp only [map_mul]
        field_simp
      rw [hfirst, hsecond, htailphase]
      simp only [map_mul]
      congr 1
      rw [List.zipWith_map_right]
      simp only [map_mul, mul_assoc]

end ShortDraftCRT

namespace ShortDraftDescent

theorem binary_energy_descent
    {Node : Type*} (rank : Node → ℕ) (energy mass : Node → ℝ)
    (left right : Node → Node) (costLeft costRight : Node → ℝ)
    (henergy : ∀ x, 0 ≤ energy x)
    (hmass : ∀ x, 0 ≤ mass x)
    (hcostLeft : ∀ x, 0 ≤ costLeft x)
    (hcostRight : ∀ x, 0 ≤ costRight x)
    (hterminal : ∀ x, rank x = 0 → energy x ≤ mass x)
    (hstep : ∀ x, rank x ≠ 0 →
      rank (left x) < rank x ∧ rank (right x) < rank x ∧
      energy x ^ 2 ≤
        (costLeft x * energy (left x)) *
          (costRight x * energy (right x)) ∧
      costLeft x * mass (left x) ≤ mass x ∧
      costRight x * mass (right x) ≤ mass x) :
    ∀ x, energy x ≤ mass x := by
  have H : ∀ n : ℕ, ∀ x, rank x = n → energy x ≤ mass x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · exact hterminal x (hx.trans hn)
      obtain ⟨hrl, hrr, hE, hMl, hMr⟩ := hstep x (by omega)
      have hEl := ih (rank (left x)) (by omega) (left x) rfl
      have hEr := ih (rank (right x)) (by omega) (right x) rfl
      have hcl := mul_le_mul_of_nonneg_left hEl (hcostLeft x)
      have hcr := mul_le_mul_of_nonneg_left hEr (hcostRight x)
      have hcl0 : 0 ≤ costLeft x * energy (left x) :=
        mul_nonneg (hcostLeft x) (henergy (left x))
      have hcr0 : 0 ≤ costRight x * energy (right x) :=
        mul_nonneg (hcostRight x) (henergy (right x))
      have hml0 : 0 ≤ costLeft x * mass (left x) :=
        mul_nonneg (hcostLeft x) (hmass (left x))
      have hmr0 : 0 ≤ costRight x * mass (right x) :=
        mul_nonneg (hcostRight x) (hmass (right x))
      have hprod₁ :
          (costLeft x * energy (left x)) *
            (costRight x * energy (right x)) ≤
          (costLeft x * mass (left x)) *
            (costRight x * mass (right x)) :=
        mul_le_mul hcl hcr hcr0 hml0
      have hprod₂ :
          (costLeft x * mass (left x)) *
            (costRight x * mass (right x)) ≤ mass x ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hMl) hmr0,
          mul_nonneg (hmass x) (sub_nonneg.mpr hMr)]
      have hsq : energy x ^ 2 ≤ mass x ^ 2 :=
        le_trans hE (le_trans hprod₁ hprod₂)
      nlinarith [henergy x, hmass x]
  intro x
  exact H (rank x) x rfl

theorem contraction_terminates_after_3001
    (z : ℝ) (K : ℕ → ℝ) (hz : 1 < z)
    (hK0 : K 0 ≤ z ^ 3000)
    (hcontract : ∀ n, K (n + 1) ≤ K n / z) :
    K 3001 < 1 := by
  have hz0 : 0 < z := by linarith
  have hbound (n : ℕ) : K n * z ^ n ≤ K 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hcontract n
        have hstep : K (n + 1) * z ≤ K n := by
          exact (le_div_iff₀ hz0).mp hs
        calc
          K (n + 1) * z ^ (n + 1) =
              (K (n + 1) * z) * z ^ n := by rw [pow_succ]; ring
          _ ≤ K n * z ^ n :=
            mul_le_mul_of_nonneg_right hstep (pow_nonneg (le_of_lt hz0) n)
          _ ≤ K 0 := ih
  have h3001 := hbound 3001
  have hpow : z ^ 3000 < z ^ 3001 := by
    calc
      z ^ 3000 = z ^ 3000 * 1 := by ring
      _ < z ^ 3000 * z :=
        mul_lt_mul_of_pos_left hz (pow_pos hz0 _)
      _ = z ^ 3001 := by ring
  have hlt : K 3001 * z ^ 3001 < z ^ 3001 :=
    lt_of_le_of_lt (h3001.trans hK0) hpow
  by_contra h
  have hge : 1 ≤ K 3001 := le_of_not_gt h
  nlinarith [mul_nonneg (sub_nonneg.mpr hge)
    (le_of_lt (pow_pos hz0 3001))]

end ShortDraftDescent

namespace ShortDraftTrace

open Complex
open scoped ComplexConjugate

section Generic

variable (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
  (hconj : conj ω = ω ^ 2)

include hω hconj

omit hconj in
private lemma lam_ne_zero : (1 + 2 * ω : ℂ) ≠ 0 := by
  intro h
  have hw : ω = -(1 : ℂ) / 2 := by linear_combination h / 2
  rw [hw] at hω
  norm_num at hω

private lemma conj_lam : conj (1 + 2 * ω) = -(1 + 2 * ω) := by
  rw [map_add, map_one, map_mul, map_ofNat, hconj]
  linear_combination 2 * hω

omit hconj in
private lemma omega_sub_square : ω - ω ^ 2 = 1 + 2 * ω := by
  linear_combination -hω

theorem trace_div_lam (a b : ℤ) :
    ((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω) +
      conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) = (b : ℂ) := by
  have hl := lam_ne_zero ω hω
  simp only [map_div₀, map_add, map_intCast, map_mul, hconj,
    conj_lam ω hω hconj]
  rw [div_neg, ← sub_eq_add_neg, ← sub_div]
  calc
    ((a : ℂ) + (b : ℂ) * ω - ((a : ℂ) + (b : ℂ) * ω ^ 2)) /
        (1 + 2 * ω) = (b : ℂ) * (ω - ω ^ 2) / (1 + 2 * ω) := by ring
    _ = (b : ℂ) := by rw [omega_sub_square ω hω]; field_simp

theorem trace_character_period (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)) +
       conj (((a : ℂ) + (b : ℂ) * ω) / (1 + 2 * ω)))) = 1 := by
  rw [trace_div_lam ω hω hconj a b]
  calc
    _ = Complex.exp ((b : ℂ) * (2 * Real.pi * Complex.I)) := by congr 1; ring
    _ = Complex.exp (2 * Real.pi * Complex.I) ^ b := Complex.exp_int_mul _ _
    _ = 1 := by rw [Complex.exp_two_pi_mul_I, one_zpow]

end Generic

noncomputable def ω₃ : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℝ) * Complex.I) / 2

private theorem omega_sq : ω₃ ^ 2 = -ω₃ - 1 := by
  have hs : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    norm_cast
  have hquad : ω₃ ^ 2 + ω₃ + 1 =
      (3 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) / 4 := by
    unfold ω₃
    ring
  rw [hs', Complex.I_sq] at hquad
  norm_num at hquad
  linear_combination hquad

theorem omega_conj : conj ω₃ = ω₃ ^ 2 := by
  rw [omega_sq]
  unfold ω₃
  simp only [map_div₀, map_add, map_neg, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem eisenstein_trace_period (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I *
      ((((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) +
       conj (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)))) = 1 := by
  apply trace_character_period ω₃
  · rw [omega_sq]; ring
  · exact omega_conj

noncomputable def breveE : AddChar ℂ ℂ where
  toFun z := Complex.exp (2 * Real.pi * Complex.I * (z + conj z))
  map_zero_eq_one' := by simp
  map_add_eq_mul' z w := by
    have harg : 2 * Real.pi * Complex.I * (z + w + conj (z + w)) =
        2 * Real.pi * Complex.I * (z + conj z) +
          2 * Real.pi * Complex.I * (w + conj w) := by
      rw [map_add]
      ring
    rw [harg, Complex.exp_add]

theorem breveE_period_lam (a b : ℤ) :
    breveE (((a : ℂ) + (b : ℂ) * ω₃) / (1 + 2 * ω₃)) = 1 := by
  exact eisenstein_trace_period a b

theorem breveE_period_integer (a b : ℤ) :
    breveE ((a : ℂ) + (b : ℂ) * ω₃) = 1 := by
  have htrace : ((a : ℂ) + (b : ℂ) * ω₃) +
      conj ((a : ℂ) + (b : ℂ) * ω₃) = ((2 * a - b : ℤ) : ℂ) := by
    rw [map_add, map_intCast, map_mul, map_intCast, omega_conj, omega_sq]
    push_cast
    ring
  change Complex.exp (2 * Real.pi * Complex.I *
    (((a : ℂ) + (b : ℂ) * ω₃) + conj ((a : ℂ) + (b : ℂ) * ω₃))) = 1
  rw [htrace]
  calc
    _ = Complex.exp (((2 * a - b : ℤ) : ℂ) *
          (2 * Real.pi * Complex.I)) := by congr 1; ring
    _ = Complex.exp (2 * Real.pi * Complex.I) ^ (2 * a - b : ℤ) :=
        Complex.exp_int_mul _ _
    _ = 1 := by rw [Complex.exp_two_pi_mul_I, one_zpow]

private theorem lam_eq_sqrt3_mul_I :
    1 + 2 * ω₃ = (Real.sqrt 3 : ℝ) * Complex.I := by
  unfold ω₃
  ring

private theorem sub_conj_eq (z : ℂ) :
    z - conj z = 2 * (z.im : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]
    ring

theorem breveE_div_lam_eq_e (z : ℂ) :
    breveE (z / (1 + 2 * ω₃)) =
      Complex.exp (4 * Real.pi * Complex.I * (z.im / Real.sqrt 3)) := by
  have hs : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hl : ((Real.sqrt 3 : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hs) Complex.I_ne_zero
  change Complex.exp (2 * Real.pi * Complex.I *
    (z / (1 + 2 * ω₃) + conj (z / (1 + 2 * ω₃)))) = _
  rw [lam_eq_sqrt3_mul_I]
  have hc : conj (((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) =
      -(((Real.sqrt 3 : ℝ) : ℂ) * Complex.I) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [map_div₀, hc, div_neg, ← sub_eq_add_neg, ← sub_div, sub_conj_eq]
  congr 1
  field_simp
  ring

def eisensteinSubring : Subring ℂ where
  carrier := {z | ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * ω₃}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    push_cast
    ring
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c - b * d, ?_⟩
    push_cast
    linear_combination (b : ℂ) * (d : ℂ) * omega_sq

noncomputable def lamEis : eisensteinSubring :=
  ⟨1 + 2 * ω₃, ⟨1, 2, by norm_num⟩⟩

theorem breveE_period_eisenstein (x : eisensteinSubring) :
    breveE (((x : ℂ) / (lamEis : ℂ))) = 1 := by
  obtain ⟨a, b, h⟩ := x.property
  change breveE ((x : ℂ) / (1 + 2 * ω₃)) = 1
  rw [h]
  exact breveE_period_lam a b

end ShortDraftTrace

end OAI
end OAIOriginalModule0036

/-! Original module: OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
Source SHA256: 20641a475a52f4d80d0461973465346a5fdaa4b21107e94bbac8cfd96b100167
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0037



namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section

namespace ShortDraftCusp

variable {R : Type*} [CommRing R]

def U (t : R) : Matrix (Fin 2) (Fin 2) R := !![1,t;0,1]
def L (t : R) : Matrix (Fin 2) (Fin 2) R := !![1,0;t,1]
def E : Matrix (Fin 2) (Fin 2) R := !![0,-1;1,0]

theorem upper_inversion_lower (u v : R) :
    U u * E * L (-v) = !![u + v, -1; 1, 0] := by
  simp [U,E,L]

theorem lower_add (u v : R) : L u * L v = L (u + v) := by
  simp [L]

theorem cusp19_matrix (ω : R) (hω : ω ^ 2 + ω + 1 = 0) :
    U ω * E * L (-(ω ^ 2)) = !![-1,-1;1,0] := by
  rw [upper_inversion_lower]
  have hw : ω + ω ^ 2 = -1 := by linear_combination hω
  rw [hw]

theorem cusp10_matrix (ω : R) :
    U (-ω) * E * L (-ω) = E := by
  rw [upper_inversion_lower]
  simp [E]

theorem ramified_plus_matrix (ω : R) (hω : ω ^ 2 + ω + 1 = 0) :
    L (1 + 2 * ω) = L (2 + 3 * ω) * L (ω ^ 2) := by
  rw [lower_add]
  congr 1
  linear_combination -hω

theorem ramified_minus_matrix (ω : R) :
    L (-(1 + 2 * ω)) = L (-1 - 3 * ω) * L ω := by
  rw [lower_add]
  congr 1
  ring

theorem principal_case_div_three (a b c d : R)
    (hdet : a * d - b * c = 1)
    (ha : a = 1) (hb : b = 0) (hc : c = 0) :
    (!![a,b;c,d] : Matrix (Fin 2) (Fin 2) R) = 1 := by
  subst a
  subst b
  subst c
  have hd : d = 1 := by simpa using hdet
  subst d
  simp [Matrix.one_fin_two]

theorem principal_case_ramified (a b c d u : R)
    (hdet : a * d - b * c = 1)
    (ha : a = 1) (hb : b = 0) (hc : c = u) :
    (!![a - u * b,b;c - u * d,d] : Matrix (Fin 2) (Fin 2) R) = 1 := by
  subst a
  subst b
  subst c
  have hd : d = 1 := by simpa using hdet
  subst d
  simp [Matrix.one_fin_two]

theorem principal_case_unramified (a b c d u : R)
    (hdet : a * d - b * c = 1)
    (hc : c = 1) (hd : d = 0) (hu : u = a) :
    (!![-b,a + u * b;-d,c + u * d] : Matrix (Fin 2) (Fin 2) R) = 1 := by
  subst c
  subst d
  subst u
  have hb : b = -1 := by linear_combination -hdet
  subst b
  simp [Matrix.one_fin_two]

end ShortDraftCusp

namespace ShortDraftConcretePhase
open ShortDraftTrace

theorem concrete_fixed_phase_congr (d a b x : eisensteinSubring)
    (hd : d ≠ 0) (hcong : d ∣ a - b) :
    breveE ((a : ℂ) * (x : ℂ) / ((lamEis : ℂ) * (d : ℂ))) =
      breveE ((b : ℂ) * (x : ℂ) / ((lamEis : ℂ) * (d : ℂ))) := by
  apply ShortDraftCRT.addChar_congr_of_dvd
    (Subring.subtype eisensteinSubring) breveE lamEis d a b x
  · have hs : (Real.sqrt 3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    change (1 + 2 * ω₃ : ℂ) ≠ 0
    have hLam : 1 + 2 * ω₃ = (Real.sqrt 3 : ℝ) * Complex.I := by
      unfold ω₃
      ring
    rw [hLam]
    exact mul_ne_zero (by exact_mod_cast hs) Complex.I_ne_zero
  · change (d : ℂ) ≠ 0
    intro h
    apply hd
    exact Subtype.ext h
  · exact breveE_period_eisenstein
  · exact hcong

end ShortDraftConcretePhase

namespace ShortDraftGauss

open Complex
open scoped ComplexConjugate

variable {F : Type*} [Field F] [Fintype F]

theorem norm_gaussSum_eq_sqrt_card (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  let g := gaussSum χ ψ
  have hprod : g * conj g = (Fintype.card F : ℂ) := by
    have h := gaussSum_mul_gaussSum_eq_card hχ hψ
    rw [← star_gaussSum_eq] at h
    simpa only [g, Complex.star_def] using h
  have hnorm : ‖g‖ ^ 2 = (Fintype.card F : ℝ) := by
    apply Complex.ofReal_injective
    calc
      ((‖g‖ ^ 2 : ℝ) : ℂ) = (‖g‖ : ℂ) ^ 2 := by norm_cast
      _ = g * conj g := (Complex.mul_conj' g).symm
      _ = (Fintype.card F : ℂ) := hprod
      _ = ((Fintype.card F : ℝ) : ℂ) := by norm_cast
  have hcard : (0 : ℝ) ≤ Fintype.card F := by positivity
  have hsqrt := Real.sq_sqrt hcard
  nlinarith [norm_nonneg g, Real.sqrt_nonneg (Fintype.card F)]

theorem norm_normalized_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖((Real.sqrt (Fintype.card F) : ℝ) : ℂ)⁻¹ * gaussSum χ ψ‖ = 1 := by
  have hcard : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hsqrt : Real.sqrt (Fintype.card F) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 hcard), norm_gaussSum_eq_sqrt_card χ ψ hχ hψ]
  exact inv_mul_cancel₀ hsqrt

end ShortDraftGauss

namespace EisensteinRayPhase

abbrev SquareClass := ZMod 2 × ZMod 2

def R (a b : SquareClass) : ℤ :=
  (-1) ^ (a.1.val * b.2.val + a.2.val * b.1.val + a.2.val * b.2.val)

theorem R_symmetric (a b : SquareClass) : R a b = R b a := by
  decide +revert

theorem R_mul_left (a b c : SquareClass) : R (a + b) c = R a c * R b c := by
  decide +revert

theorem R_mul_right (a b c : SquareClass) : R a (b + c) = R a b * R a c := by
  decide +revert

theorem R_self (a : SquareClass) : R a a = (-1) ^ (a.2.val) := by
  decide +revert

end EisensteinRayPhase

namespace ShortDraftSextic
open scoped Classical
variable {R : Type*} [CommRing R]

theorem sextic_power_is_unit_mask (χ : MulChar R ℂ)
    (hχ : χ ^ 6 = 1) (u : R) :
    χ (u ^ 6) = if IsUnit u then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
  by_cases hu : IsUnit u
  · simp [hu, MulChar.one_apply]
  · simp [hu]

end ShortDraftSextic

namespace ShortDraftGaussJacobi
open Finset

variable {F : Type*} [Field F] [Fintype F]

theorem sum_cubic_jacobi_reduction_zero (m : ℕ)
    (hm : 2 * m < Fintype.card F - 1) :
    (∑ x : F, x ^ m * (1 - x) ^ m) = 0 := by
  classical
  simp_rw [sub_eq_add_neg, add_pow]
  simp only [one_pow, one_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have he : m + (m - j) < Fintype.card F - 1 := by
    have hle : m - j ≤ m := Nat.sub_le m j
    omega
  calc
    (∑ x : F, x ^ m * ((-x) ^ (m - j) * ↑(m.choose j))) =
        ((-1 : F) ^ (m - j) * ↑(m.choose j)) *
          ∑ x : F, x ^ (m + (m - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [neg_pow, pow_add]
      ring
    _ = 0 := by rw [FiniteField.sum_pow_lt_card_sub_one F _ he]; ring

theorem jacobiSum_reduction_zero {R : Type*} [CommRing R]
    (χ : MulChar F R) (ρ : R →+* F) (m : ℕ)
    (hχ : ∀ x : F, ρ (χ x) = x ^ m)
    (hm : 2 * m < Fintype.card F - 1) :
    ρ (jacobiSum χ χ) = 0 := by
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, hχ]
  exact sum_cubic_jacobi_reduction_zero m hm

theorem cubic_jacobi_product (χ : MulChar F ℂ)
    (horder : orderOf χ = 3)
    (hchar : ringChar ℂ ≠ ringChar F) :
    jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = (Fintype.card F : ℂ) := by
  have hχ : χ ≠ 1 := by
    intro h
    simp [h] at horder
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have ho : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [horder] at ho
    norm_num at ho
  exact jacobiSum_mul_jacobiSum_inv hchar hχ hχ hχ2

theorem cubic_gauss_cube (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (horder : orderOf χ = 3) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 3 = (Fintype.card F : ℂ) * jacobiSum χ χ := by
  have hχ : χ ≠ 1 := by
    intro h
    simp [h] at horder
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have ho : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [horder] at ho
    norm_num at ho
  have hneg : χ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (n := 3) (by decide)
      (by simpa [horder] using (pow_orderOf_eq_one χ))
  have hj := jacobiSum_mul_nontrivial hχ2 ψ
  have hg := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ hψ
  simp only [horder, Nat.reduceSub, pow_two] at hg
  rw [hneg, one_mul] at hg
  calc
    gaussSum χ ψ ^ 3 = gaussSum χ ψ * (gaussSum χ ψ * gaussSum χ ψ) := by ring
    _ = gaussSum χ ψ * (gaussSum (χ * χ) ψ * jacobiSum χ χ) := by rw [hj]
    _ = (Fintype.card F : ℂ) * jacobiSum χ χ := by rw [← mul_assoc, hg]

theorem normalized_cubic_gauss_cube (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (horder : orderOf χ = 3) (hψ : ψ.IsPrimitive) :
    (gaussSum χ ψ / (Real.sqrt (Fintype.card F : ℝ) : ℂ)) ^ 3 =
      jacobiSum χ χ / (Real.sqrt (Fintype.card F : ℝ) : ℂ) := by
  let s : ℂ := Real.sqrt (Fintype.card F : ℝ)
  have hcard : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hs : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (Real.sqrt_pos.2 hcard).ne'
  have hs2 : s ^ 2 = (Fintype.card F : ℂ) := by
    dsimp [s]
    exact_mod_cast Real.sq_sqrt hcard.le
  rw [div_pow, cubic_gauss_cube χ ψ horder hψ, ← hs2]
  field_simp
  change s ^ 2 * jacobiSum χ χ = jacobiSum χ χ * s ^ 2
  ring

end ShortDraftGaussJacobi

namespace ShortDraftQuadraticGauss
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadratic_gauss_as_square_phase (ψ : AddChar F ℂ)
    (hchar : ringChar F ≠ 2) (hψ : ψ ≠ 1) :
    gaussSum ((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) ψ =
      ∑ x : F, ψ (x ^ 2) := by
  have hfiber : (∑ x : F, ψ (x ^ 2)) =
      ∑ y : F, (#{x : F | x ^ 2 = y}.toFinset : ℂ) * ψ y := by
    rw [← Finset.sum_fiberwise (s := Finset.univ)
      (g := fun x : F => x ^ 2) (f := fun x : F => ψ (x ^ 2))]
    apply Finset.sum_congr rfl
    intro y _
    have hterm : (∑ x ∈ Finset.univ with x ^ 2 = y, ψ (x ^ 2)) =
        (#{x : F | x ^ 2 = y}.toFinset : ℂ) * ψ y := by
      rw [Finset.sum_congr rfl (fun x hx => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hx])]
      simp
    exact hterm
  have hcount (y : F) :
      (#{x : F | x ^ 2 = y}.toFinset : ℂ) =
        (quadraticChar F y : ℂ) + 1 := by
    exact_mod_cast quadraticChar_card_sqrts hchar y
  rw [hfiber]
  simp_rw [hcount, add_mul]
  rw [Finset.sum_add_distrib]
  have hzero : (∑ y : F, ψ y) = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  simp only [one_mul, hzero, add_zero]
  rfl

end ShortDraftQuadraticGauss

namespace ShortDraftQuotientPhase
variable {A B : Type*} [CommGroup A] [CommGroup B]

theorem quotient_phase (R : A → A → B) (G : A → B)
    (hRright : ∀ a b c, R a (b * c) = R a b * R a c)
    (hRsym : ∀ a b, R a b = R b a)
    (hRone : ∀ a, R a 1 = 1)
    (hRtwo : ∀ a b, R a b ^ 2 = 1)
    (hGmul : ∀ a b, G (a * b) = G a * G b * R a b)
    (hGone : G 1 = 1)
    (a b : A) :
    R a a * (G a)⁻¹ * G b * R a b = G (b * a⁻¹) := by
  have hRinv (x y : A) : R x y⁻¹ = (R x y)⁻¹ := by
    have h := hRright x y y⁻¹
    rw [mul_inv_cancel, hRone] at h
    have h' : R x y⁻¹ * R x y = 1 := by
      simpa [mul_comm] using h.symm
    exact (mul_eq_one_iff_eq_inv).mp h'
  have hRinv_eq (x y : A) : R x y⁻¹ = R x y := by
    rw [hRinv]
    have hsq : R x y * R x y = 1 := by
      simpa [pow_two] using hRtwo x y
    exact ((mul_eq_one_iff_eq_inv).mp hsq).symm
  have hGaInv : G a⁻¹ = R a a * (G a)⁻¹ := by
    have h := hGmul a a⁻¹
    rw [mul_inv_cancel, hGone, hRinv_eq] at h
    have ht : G a * G a⁻¹ = (R a a)⁻¹ :=
      (mul_eq_one_iff_eq_inv).mp h.symm
    have hsq : R a a * R a a = 1 := by
      simpa [pow_two] using hRtwo a a
    have hr : (R a a)⁻¹ = R a a :=
      ((mul_eq_one_iff_eq_inv).mp hsq).symm
    calc
      G a⁻¹ = (G a)⁻¹ * (G a * G a⁻¹) := by group
      _ = R a a * (G a)⁻¹ := by rw [ht, hr]; ac_rfl
  rw [hGmul b a⁻¹, hGaInv, hRinv_eq b a, hRsym b a]
  ac_rfl

end ShortDraftQuotientPhase

namespace EisensteinEPrimaryPhase

abbrev Coord := ZMod 4 × ZMod 4
abbrev Bit := ZMod 2

def mul (x y : Coord) : Coord :=
  (x.1 * y.1 - x.2 * y.2,
   x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def odd (x : Coord) : Prop := x.1.val % 2 = 1 ∨ x.2.val % 2 = 1

instance : DecidablePred odd := fun x =>
  inferInstanceAs (Decidable (x.1.val % 2 = 1 ∨ x.2.val % 2 = 1))

def rep (e f : Bit) : Coord :=
  if f = 0 then (if e = 0 then (1, 0) else (-1, 0))
  else (if e = 0 then (1, 2) else (-1, -2))

def norm (x : Coord) : ZMod 4 :=
  x.1 * x.1 - x.1 * x.2 + x.2 * x.2

def ePrimary (x : Coord) : Prop :=
  let cube := mul (mul x x) x
  cube.1 - 2 * cube.2 = 1

instance : DecidablePred ePrimary := fun x =>
  inferInstanceAs (Decidable ((mul (mul x x) x).1 -
    2 * (mul (mul x x) x).2 = 1))

theorem exists_squareclass (x : Coord) (hx : odd x) :
    ∃ (e f : Bit) (u : Coord), odd u ∧ x = mul (rep e f) (mul u u) := by
  decide +revert

theorem squareclass_bits_unique (e f e' f' : Bit) (u v : Coord)
    (hu : odd u) (hv : odd v)
    (h : mul (rep e f) (mul u u) = mul (rep e' f') (mul v v)) :
    e = e' ∧ f = f' := by
  decide +revert

theorem ePrimary_squareclass (e f : Bit) (u : Coord) (hu : odd u) :
    ePrimary (mul (rep e f) (mul u u)) ↔ e = 0 := by
  decide +revert

theorem norm_squareclass (e f : Bit) (u : Coord) (hu : odd u) :
    norm (mul (rep e f) (mul u u)) = (if f = 0 then 1 else 3) := by
  decide +revert

def signBit (x : Coord) : Bit := if ePrimary x then 0 else 1
def normBit (x : Coord) : Bit := if norm x = 1 then 0 else 1
def bits (x : Coord) : Bit × Bit := (signBit x, normBit x)

theorem bits_squareclass (e f : Bit) (u : Coord) (hu : odd u) :
    bits (mul (rep e f) (mul u u)) = (e, f) := by
  decide +revert

theorem odd_mul (x y : Coord) (hx : odd x) (hy : odd y) : odd (mul x y) := by
  decide +revert

theorem bits_mul (x y : Coord) (hx : odd x) (hy : odd y) :
    bits (mul x y) = bits x + bits y := by
  decide +revert

end EisensteinEPrimaryPhase

namespace ShortDraftGaussianPhaseTable
abbrev SquareClass := ZMod 2 × ZMod 2

def phase (a : SquareClass) : ZMod 4 :=
  if a.2 = 0 then 0 else if a.1 = 0 then 1 else 3

def reciprocity (a b : SquareClass) : ZMod 4 :=
  2 * ((a.1.val * b.2.val + a.2.val * b.1.val + a.2.val * b.2.val : ℕ) : ZMod 4)

theorem phase_cocycle (a b : SquareClass) :
    phase (a + b) = phase a + phase b + reciprocity a b := by
  decide +revert

end ShortDraftGaussianPhaseTable

namespace ActualEisensteinCoordinates
abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K
private instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ
private theorem hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta 3 ℚ K) 3 :=
  IsCyclotomicExtension.zeta_spec 3 ℚ K
def omega : O := hζ.toInteger
private def pb : PowerBasis ℤ O := hζ.integralPowerBasis

private theorem pb_dim : pb.dim = 2 := by
  simp [pb, Nat.totient_prime Nat.prime_three]

theorem pb_gen : pb.gen = omega := by
  exact hζ.integralPowerBasis_gen

theorem exists_coordinates (x : O) :
    ∃ a b : ℤ, x = (a : O) + (b : O) * omega := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let a : ℤ := (pb.basis.repr x) i0
  let b : ℤ := (pb.basis.repr x) i1
  refine ⟨a, b, ?_⟩
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
  have hi0 : (i0 : ℕ) = 0 := rfl
  have hi1 : (i1 : ℕ) = 1 := rfl
  simpa [a, b, hi0, hi1, pb_gen, smul_eq_mul, mul_comm] using hsum.symm

private def i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
private def i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩

def eval (a b : ℤ) : O := (a : O) + (b : O) * omega

private theorem eval_basis (a b : ℤ) :
    eval a b = a • pb.basis i0 + b • pb.basis i1 := by
  simp [eval, PowerBasis.basis_eq_pow, i0, i1, pb_gen, mul_comm]

theorem unique_coordinates {a b c d : ℤ}
    (h : eval a b = eval c d) : a = c ∧ b = d := by
  have h0 := congrArg (fun x : O => (pb.basis.repr x) i0) h
  have h1 := congrArg (fun x : O => (pb.basis.repr x) i1) h
  have hne : i0 ≠ i1 := by decide
  rw [eval_basis, eval_basis] at h0 h1
  constructor
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, ite_eq_left, ite_eq_right hne.symm,
      smul_eq_mul, mul_one, mul_zero, add_zero] using h0
  · simpa only [map_add, map_smul, pb.basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, ite_eq_left, ite_eq_right hne,
      smul_eq_mul, mul_one, mul_zero, zero_add] using h1

private theorem omega_sq : omega ^ 2 = -omega - 1 := by
  simpa [omega] using IsCyclotomicExtension.Rat.Three.eta_sq hζ

theorem conventional_lambda_eq_neg_delta_square :
    omega - 1 = -eval 1 2 * omega ^ 2 := by
  have hc : omega ^ 3 = 1 := hζ.toInteger_cube_eq_one
  calc
    omega - 1 = -omega ^ 2 - 2 * omega ^ 3 := by
      rw [omega_sq, hc]
      ring
    _ = -eval 1 2 * omega ^ 2 := by
      simp only [eval]
      push_cast
      ring

theorem eval_mul (a b c d : ℤ) :
    eval a b * eval c d = eval (a*c-b*d) (a*d+b*c-b*d) := by
  simp only [eval]
  calc
    ((a : O) + (b : O) * omega) * ((c : O) + (d : O) * omega)
      = (a : O) * c + ((a : O) * d + (b : O) * c) * omega +
          ((b : O) * d) * omega ^ 2 := by ring
    _ = ((a*c-b*d : ℤ) : O) + ((a*d+b*c-b*d : ℤ) : O) * omega := by
          rw [omega_sq]
          push_cast
          ring

theorem eval_congr_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    ∃ z : O, eval a b - eval c d = 4 * z := by
  have ha4 : (4 : ℤ) ∣ a-c := (ZMod.intCast_eq_intCast_iff_dvd_sub c a 4).mp ha.symm
  have hb4 : (4 : ℤ) ∣ b-d := (ZMod.intCast_eq_intCast_iff_dvd_sub d b 4).mp hb.symm
  obtain ⟨u, hu⟩ := ha4
  obtain ⟨v, hv⟩ := hb4
  refine ⟨(u : O) + (v : O) * omega, ?_⟩
  dsimp [eval]
  rw [show a = c + 4*u by omega, show b = d + 4*v by omega]
  push_cast
  ring

private theorem exists_pair (x : O) :
    ∃ p : ℤ × ℤ, eval p.1 p.2 = x := by
  obtain ⟨a, b, h⟩ := exists_coordinates x
  exact ⟨(a, b), h.symm⟩

def coords (x : O) : ℤ × ℤ := Classical.choose (exists_pair x)

theorem eval_coords (x : O) : eval (coords x).1 (coords x).2 = x :=
  Classical.choose_spec (exists_pair x)

def residue (x : O) : EisensteinEPrimaryPhase.Coord :=
  ((coords x).1, (coords x).2)

theorem residue_eval (a b : ℤ) :
    residue (eval a b) = ((a : ZMod 4), (b : ZMod 4)) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext (congrArg (fun n : ℤ => (n : ZMod 4)) h.1)
    (congrArg (fun n : ℤ => (n : ZMod 4)) h.2)

theorem residue_mul (x y : O) :
    residue (x*y) = EisensteinEPrimaryPhase.mul (residue x) (residue y) := by
  calc
    residue (x*y) = residue (eval (coords x).1 (coords x).2 *
        eval (coords y).1 (coords y).2) := by rw [eval_coords, eval_coords]
    _ = EisensteinEPrimaryPhase.mul (residue x) (residue y) := by
      rw [eval_mul, residue_eval]
      simp [residue, EisensteinEPrimaryPhase.mul]

theorem residue_pow_two (x : O) :
    residue (x^2) = EisensteinEPrimaryPhase.mul (residue x) (residue x) := by
  simpa [pow_two] using residue_mul x x

theorem congr_mod_four_of_residue_eq {x y : O}
    (h : residue x = residue y) : ∃ z : O, x-y = 4*z := by
  rw [←eval_coords x, ←eval_coords y]
  apply eval_congr_mod_four
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

def lift (v : EisensteinEPrimaryPhase.Coord) : O :=
  eval (v.1.val : ℤ) (v.2.val : ℤ)

theorem residue_lift (v : EisensteinEPrimaryPhase.Coord) :
    residue (lift v) = v := by
  simp [lift, residue_eval]

theorem exists_squareclass_mod_four (x : O)
    (hx : EisensteinEPrimaryPhase.odd (residue x)) :
    ∃ (e f : EisensteinEPrimaryPhase.Bit) (u z : O),
      x - lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2 = 4 * z := by
  obtain ⟨e, f, v, hv, hclass⟩ :=
    EisensteinEPrimaryPhase.exists_squareclass (residue x) hx
  refine ⟨e, f, lift v, ?_⟩
  apply congr_mod_four_of_residue_eq
  rw [residue_mul, residue_pow_two, residue_lift, residue_lift]
  exact hclass

theorem ePrimary_squareclass_actual
    (e f : EisensteinEPrimaryPhase.Bit) (u : O)
    (hu : EisensteinEPrimaryPhase.odd (residue u)) :
    EisensteinEPrimaryPhase.ePrimary
      (residue (lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2)) ↔ e = 0 := by
  rw [residue_mul, residue_pow_two, residue_lift]
  exact EisensteinEPrimaryPhase.ePrimary_squareclass e f (residue u) hu

theorem norm_squareclass_actual
    (e f : EisensteinEPrimaryPhase.Bit) (u : O)
    (hu : EisensteinEPrimaryPhase.odd (residue u)) :
    EisensteinEPrimaryPhase.norm
      (residue (lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2)) =
      (if f = 0 then 1 else 3) := by
  rw [residue_mul, residue_pow_two, residue_lift]
  exact EisensteinEPrimaryPhase.norm_squareclass e f (residue u) hu

private theorem residue_two : residue (2 : O) = (2, 0) := by
  have h : eval 2 0 = (2 : O) := by simp [eval]
  rw [← h, residue_eval]
  norm_num

private theorem not_odd_mul_two (v : EisensteinEPrimaryPhase.Coord) :
    ¬ EisensteinEPrimaryPhase.odd
      (EisensteinEPrimaryPhase.mul (2, 0) v) := by
  decide +revert

private theorem not_odd_cast_zero (v : EisensteinEPrimaryPhase.Coord)
    (h : ¬ EisensteinEPrimaryPhase.odd v) :
    (ZMod.cast v.1 : ZMod 2) = 0 ∧
      (ZMod.cast v.2 : ZMod 2) = 0 := by
  decide +revert

theorem odd_residue_iff_not_two_dvd (x : O) :
    EisensteinEPrimaryPhase.odd (residue x) ↔ ¬ (2 : O) ∣ x := by
  constructor
  · intro hx hdiv
    obtain ⟨y, hy⟩ := hdiv
    rw [hy, residue_mul, residue_two] at hx
    exact not_odd_mul_two (residue y) hx
  · intro hdiv
    by_contra hodd
    obtain ⟨ha, hb⟩ := not_odd_cast_zero (residue x) hodd
    have ha' : ((coords x).1 : ZMod 2) = 0 := by
      simpa [residue, ZMod.cast_intCast (by decide : 2 ∣ 4)] using ha
    have hb' : ((coords x).2 : ZMod 2) = 0 := by
      simpa [residue, ZMod.cast_intCast (by decide : 2 ∣ 4)] using hb
    obtain ⟨a, ha2⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coords x).1 2).mp ha'
    obtain ⟨b, hb2⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (coords x).2 2).mp hb'
    apply hdiv
    refine ⟨eval a b, ?_⟩
    rw [← eval_coords x]
    dsimp [eval]
    rw [ha2, hb2]
    push_cast
    ring
def rayBits (x : O) : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit :=
  EisensteinEPrimaryPhase.bits (residue x)

theorem rayBits_mul (x y : O)
    (hx : ¬ (2 : O) ∣ x) (hy : ¬ (2 : O) ∣ y) :
    rayBits (x*y) = rayBits x + rayBits y := by
  unfold rayBits
  rw [residue_mul]
  exact EisensteinEPrimaryPhase.bits_mul _ _
    ((odd_residue_iff_not_two_dvd x).mpr hx)
    ((odd_residue_iff_not_two_dvd y).mpr hy)

def rayPhaseBits (a b : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) : ℤ :=
  (-1) ^ (a.1.val * b.2.val + a.2.val * b.1.val + a.2.val * b.2.val)

private theorem rayPhaseBits_symmetric (a b : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) :
    rayPhaseBits a b = rayPhaseBits b a := by
  decide +revert

private theorem rayPhaseBits_mul_left
    (a b c : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) :
    rayPhaseBits (a+b) c = rayPhaseBits a c * rayPhaseBits b c := by
  decide +revert

private theorem rayPhaseBits_mul_right
    (a b c : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) :
    rayPhaseBits a (b+c) = rayPhaseBits a b * rayPhaseBits a c := by
  decide +revert

def rayPhase (x y : O) : ℤ := rayPhaseBits (rayBits x) (rayBits y)

theorem rayPhase_symmetric (x y : O) : rayPhase x y = rayPhase y x :=
  rayPhaseBits_symmetric _ _

theorem rayPhase_mul_left (x y z : O)
    (hx : ¬ (2 : O) ∣ x) (hy : ¬ (2 : O) ∣ y) :
    rayPhase (x*y) z = rayPhase x z * rayPhase y z := by
  unfold rayPhase
  rw [rayBits_mul x y hx hy]
  exact rayPhaseBits_mul_left _ _ _

theorem rayPhase_mul_right (x y z : O)
    (hy : ¬ (2 : O) ∣ y) (hz : ¬ (2 : O) ∣ z) :
    rayPhase x (y*z) = rayPhase x y * rayPhase x z := by
  unfold rayPhase
  rw [rayBits_mul y z hy hz]
  exact rayPhaseBits_mul_right _ _ _
end ActualEisensteinCoordinates

end

end OAI
end OAIOriginalModule0037

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.FiniteFourier
Source SHA256: 0e8e4184de91161a75802e3a26abfd19a322dffa6441968bf9caeb25800b5d7c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0038



namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

namespace ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]

theorem gauss_transform (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ x : F, χ x * ψ (h * x)) =
      if h = 0 then 0 else (χ h)⁻¹ * gaussSum χ ψ := by
  classical
  by_cases hh : h = 0
  · subst h
    simp only [zero_mul, map_zero_eq_one, mul_one, ite_true]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  · have hu : IsUnit h := isUnit_iff_ne_zero.mpr hh
    have hshift := gaussSum_mulShift_eq χ ψ hu.unit
    simp only [gaussSum, AddChar.mulShift_apply] at hshift
    simpa only [hu.unit_spec, ite_eq_right hh, inv_apply_eq_inv' χ h, gaussSum] using hshift

theorem product_gauss_transform
    {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, Field (E i)] [∀ i, Fintype (E i)]
    (χ : ∀ i, MulChar (E i) ℂ) (ψ : ∀ i, AddChar (E i) ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : ∀ i, E i) :
    (∑ x : ∀ i, E i, ∏ i, χ i (x i) * ψ i (h i * x i)) =
      ∏ i, if h i = 0 then 0 else (χ i (h i))⁻¹ * gaussSum (χ i) (ψ i) := by
  classical
  calc
    (∑ x : ∀ i, E i, ∏ i, χ i (x i) * ψ i (h i * x i)) =
        ∏ i, ∑ x : E i, χ i x * ψ i (h i * x) := by
      simpa using (Fintype.prod_sum
        (fun i (x : E i) => χ i x * ψ i (h i * x))).symm
    _ = ∏ i, if h i = 0 then 0 else (χ i (h i))⁻¹ * gaussSum (χ i) (ψ i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact gauss_transform (χ i) (ψ i) (hχ i) (h i)

end ShortDraftFiniteGaussFourier

namespace PoissonChildCRT
open scoped Classical

variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)

theorem inverse_as_row_and_label (hχ : χ ^ 6 = 1) (e : ℕ) :
    (χ (e : ZMod n))⁻¹ = χ (e : ZMod n) * (χ (e : ZMod n)) ^ 4 := by
  by_cases he : IsUnit (e : ZMod n)
  · have h6 : (χ (e : ZMod n)) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
      simp [MulChar.one_apply, he]
    apply inv_eq_of_mul_eq_one_right
    calc
      χ (e : ZMod n) * (χ (e : ZMod n) * χ (e : ZMod n) ^ 4)
          = (χ (e : ZMod n)) ^ 6 := by ring
      _ = 1 := h6
  · have hz : χ (e : ZMod n) = 0 := MulChar.map_nonunit χ he
    simp [hz]

theorem child_row_label_identity (hχ : χ ^ 6 = 1)
    (d e k J C v : ℕ) :
    (χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4
      = χ ((d * e * k : ℕ) : ZMod n) *
        (χ ((J * C * e * v : ℕ) : ZMod n)) ^ 4 := by
  rw [inverse_as_row_and_label n χ hχ e]
  simp only [Nat.cast_mul, map_mul]
  ring

def mask (n m : ℕ) : ℂ := if n.Coprime m then 1 else 0

theorem mask_mul (n a b : ℕ) :
    mask n (a * b) = mask n a * mask n b := by
  classical
  simp only [mask]
  by_cases hab : n.Coprime (a * b)
  · have ha : n.Coprime a := (Nat.coprime_mul_iff_right.mp hab).1
    have hb : n.Coprime b := (Nat.coprime_mul_iff_right.mp hab).2
    rw [ite_eq_left hab, ite_eq_left ha, ite_eq_left hb]
    norm_num
  · have hna_or_hnb : ¬ n.Coprime a ∨ ¬ n.Coprime b := by
      by_contra h
      exact hab (Nat.coprime_mul_iff_right.mpr ⟨not_not.mp (not_or.mp h).1,
        not_not.mp (not_or.mp h).2⟩)
    rcases hna_or_hnb with hna | hnb
    · rw [ite_eq_right hab, ite_eq_right hna]
      simp
    · rw [ite_eq_right hab, ite_eq_right hnb]
      simp

theorem mask_absorb_char (e : ℕ) :
    mask n e * χ (e : ZMod n) = χ (e : ZMod n) := by
  by_cases he : n.Coprime e
  · simp [mask, he]
  · have hnu : ¬ IsUnit (e : ZMod n) := by
      intro hu
      exact he ((ZMod.isUnit_iff_coprime e n).mp hu).symm
    have hz : χ (e : ZMod n) = 0 := MulChar.map_nonunit χ hnu
    simp [mask, he, hz]

theorem mask_absorb_inv_char (e : ℕ) :
    mask n e * (χ (e : ZMod n))⁻¹ = (χ (e : ZMod n))⁻¹ := by
  by_cases he : n.Coprime e
  · simp [mask, he]
  · have hnu : ¬ IsUnit (e : ZMod n) := by
      intro hu
      exact he ((ZMod.isUnit_iff_coprime e n).mp hu).symm
    have hz : χ (e : ZMod n) = 0 := MulChar.map_nonunit χ hnu
    simp [mask, he, hz]

theorem child_row_label_with_mask (hχ : χ ^ 6 = 1)
    (b0 t g e r d k J C v : ℕ) (hg : g = e * r) :
    mask n (b0 * t) * mask n g *
      ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4)
      = mask n (b0 * t * r) *
        (χ ((d * e * k : ℕ) : ZMod n) *
          (χ ((J * C * e * v : ℕ) : ZMod n)) ^ 4) := by
  rw [hg, mask_mul n e r]
  have hmask : mask n (b0 * t) * (mask n e * mask n r) =
      mask n (b0 * t * r) * mask n e := by
    rw [mask_mul n (b0 * t) r]
    ring
  rw [hmask]
  have hprior : mask n e *
      ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4) =
      ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4) := by
    calc
      mask n e * ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
          (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4)
          = (mask n e * (χ (e : ZMod n))⁻¹) *
              (χ (d : ZMod n) * χ (k : ZMod n) *
                (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4) := by ring
      _ = _ := by rw [mask_absorb_inv_char n χ e]; ring
  rw [mul_assoc, hprior, child_row_label_identity n χ hχ d e k J C v]

theorem sum_child_row_label_with_mask
    (S : Finset ℕ) (χ : (n : ℕ) → MulChar (ZMod n) ℂ)
    (hχ : ∀ n, χ n ^ 6 = 1) (a : ℕ → ℂ)
    (b0 t g e r d k J C v : ℕ) (hg : g = e * r) :
    (∑ n ∈ S, a n *
      (mask n (b0 * t) * mask n g *
        ((χ n (e : ZMod n))⁻¹ * χ n (d : ZMod n) * χ n (k : ZMod n) *
          (χ n ((J * C : ℕ) : ZMod n)) ^ 4 *
          (χ n (v : ZMod n)) ^ 4))) =
    (∑ n ∈ S, a n *
      (mask n (b0 * t * r) *
        (χ n ((d * e * k : ℕ) : ZMod n) *
          (χ n ((J * C * e * v : ℕ) : ZMod n)) ^ 4))) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [child_row_label_with_mask n (χ n) (hχ n) b0 t g e r d k J C v hg]

end PoissonChildCRT

namespace PoissonFirstLocal
open scoped Classical

def bit (b : Bool) : ℕ := if b then 1 else 0
def localE (parityBit ε₁ ε₂ : Bool) : ZMod 6 :=
  (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * (bit parityBit : ZMod 6)
def cExp₁ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if localE parityBit ε₁ ε₂ = 0 then 0 else ((1 : ZMod 6) + localE parityBit ε₁ ε₂).val
def cExp₂ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if localE parityBit ε₁ ε₂ = 0 then 0 else ((1 : ZMod 6) - localE parityBit ε₁ ε₂).val
def EExp (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if parityBit then bit ε₁ + bit ε₂ else 0
def retained (parityBit ε₁ ε₂ : Bool) : Bool := parityBit || (ε₁ && ε₂)
def totalExp₁ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  4 * bit ε₁ + cExp₁ parityBit ε₁ ε₂ + EExp parityBit ε₁ ε₂
def totalExp₂ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  4 * bit ε₂ + cExp₂ parityBit ε₁ ε₂ + EExp parityBit ε₁ ε₂

theorem exponent_table (parityBit ε₁ ε₂ : Bool) :
    totalExp₁ parityBit ε₁ ε₂ % 6 = (if retained parityBit ε₁ ε₂ then 4 else 0) ∧
    totalExp₂ parityBit ε₁ ε₂ % 6 = (if retained parityBit ε₁ ε₂ then 4 else 0) := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

def mask (n p : ℕ) : ℂ := if n.Coprime p then 1 else 0

private theorem mask_mul (n a b : ℕ) :
    mask n (a * b) = mask n a * mask n b := by
  classical
  simp only [mask]
  by_cases hab : n.Coprime (a * b)
  · have ha : n.Coprime a := (Nat.coprime_mul_iff_right.mp hab).1
    have hb : n.Coprime b := (Nat.coprime_mul_iff_right.mp hab).2
    rw [ite_eq_left hab, ite_eq_left ha, ite_eq_left hb]
    norm_num
  · have hna_or_hnb : ¬ n.Coprime a ∨ ¬ n.Coprime b := by
      by_contra h
      exact hab (Nat.coprime_mul_iff_right.mpr ⟨not_not.mp (not_or.mp h).1,
        not_not.mp (not_or.mp h).2⟩)
    rcases hna_or_hnb with hna | hnb
    · rw [ite_eq_right hab, ite_eq_right hna]
      simp
    · rw [ite_eq_right hab, ite_eq_right hnb]
      simp

def oldFactor (side : Bool) (parityBit ε₁ ε₂ : Bool)
    (n p : ℕ) (χ : MulChar (ZMod n) ℂ) : ℂ :=
  let q := χ (p : ZMod n)
  mask n p * q ^ (4 * bit (if side then ε₂ else ε₁)) *
    q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
    q ^ EExp parityBit ε₁ ε₂

def newFactor (parityBit ε₁ ε₂ : Bool)
    (n p : ℕ) (χ : MulChar (ZMod n) ℂ) : ℂ :=
  if retained parityBit ε₁ ε₂ then (χ (p : ZMod n)) ^ 4 else mask n p

theorem first_local_identity (side parityBit ε₁ ε₂ : Bool)
    (n p : ℕ) (χ : MulChar (ZMod n) ℂ) (hχ : χ ^ 6 = 1) :
    oldFactor side parityBit ε₁ ε₂ n p χ = newFactor parityBit ε₁ ε₂ n p χ := by
  let q := χ (p : ZMod n)
  by_cases hcop : n.Coprime p
  · have hunit : IsUnit (p : ZMod n) :=
      (ZMod.isUnit_iff_coprime p n).mpr hcop.symm
    have h6 : q ^ 6 = 1 := by
      dsimp [q]
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
      simp [MulChar.one_apply, hunit]
    have hmask : mask n p = 1 := by simp [mask, hcop]
    change mask n p * q ^ (4 * bit (if side then ε₂ else ε₁)) *
      q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
      q ^ EExp parityBit ε₁ ε₂ =
      (if retained parityBit ε₁ ε₂ then q ^ 4 else mask n p)
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
  · have hnu : ¬ IsUnit (p : ZMod n) := by
      intro hu
      exact hcop ((ZMod.isUnit_iff_coprime p n).mp hu).symm
    have hzero : q = 0 := MulChar.map_nonunit χ hnu
    simp [oldFactor, newFactor, mask, hcop, q, hzero]

private theorem char_prod_four (n : ℕ) (χ : MulChar (ZMod n) ℂ)
    (S : Finset ℕ) :
    (∏ p ∈ S, (χ (p : ZMod n)) ^ 4) =
      (χ ((∏ p ∈ S, p : ℕ) : ZMod n)) ^ 4 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      simp [hp, ih, Nat.cast_mul, map_mul, mul_pow]

private theorem mask_prod (n : ℕ) (S : Finset ℕ) :
    (∏ p ∈ S, mask n p) = mask n (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mask]
  | @insert p S hp ih =>
      simp [hp, ih]
      exact (mask_mul n p (∏ p ∈ S, p)).symm

theorem first_prime_product_identity
    (side : Bool) (P : Finset ℕ)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (n : ℕ) (χ : MulChar (ZMod n) ℂ) (hχ : χ ^ 6 = 1) :
    (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p χ) =
      (χ ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
      mask n (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) := by
  classical
  calc
    (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p χ) =
        ∏ p ∈ P, newFactor (parityBit p) (ε₁ p) (ε₂ p) n p χ := by
          apply Finset.prod_congr rfl
          intro p hp
          exact first_local_identity side (parityBit p) (ε₁ p) (ε₂ p) n p χ hχ
    _ = (∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p),
            (χ (p : ZMod n)) ^ 4) *
          (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), mask n p) := by
          simp only [newFactor]
          exact Finset.prod_ite _ _
    _ = _ := by
          rw [char_prod_four, mask_prod]

theorem mask_redundant_overlap
    (n J B₀ b₀ m : ℕ) (χ : MulChar (ZMod n) ℂ)
    (hB : B₀ ∣ b₀) (hb : b₀ ∣ (B₀ * J) ^ m) :
    (χ (J : ZMod n)) ^ 4 * mask n B₀ =
      (χ (J : ZMod n)) ^ 4 * mask n b₀ := by
  by_cases hJ : n.Coprime J
  · have hiff : n.Coprime B₀ ↔ n.Coprime b₀ := by
      constructor
      · intro hB₀
        have hprod : n.Coprime (B₀ * J) := hB₀.mul_right hJ
        exact Nat.Coprime.of_dvd_right hb (hprod.pow_right m)
      · intro hb₀
        exact Nat.Coprime.of_dvd_right hB hb₀
    simp only [mask]
    split_ifs with h₁ h₂ <;> simp_all
  · have hnu : ¬ IsUnit (J : ZMod n) := by
      intro hu
      exact hJ ((ZMod.isUnit_iff_coprime J n).mp hu).symm
    have hz : χ (J : ZMod n) = 0 := MulChar.map_nonunit χ hnu
    simp [hz]

theorem first_prime_product_with_b0
    (side : Bool) (P : Finset ℕ)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (n b₀ m : ℕ) (χ : MulChar (ZMod n) ℂ) (hχ : χ ^ 6 = 1)
    (hB : (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) ∣ b₀)
    (hb : b₀ ∣
      ((∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) *
       (∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p)) ^ m) :
    (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p χ) =
      (χ ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
      mask n b₀ := by
  rw [first_prime_product_identity side P parityBit ε₁ ε₂ n χ hχ]
  exact mask_redundant_overlap n _ _ b₀ m χ hB hb

theorem sum_first_prime_product_identity
    (S P : Finset ℕ) (side : Bool)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (χ : (n : ℕ) → MulChar (ZMod n) ℂ)
    (hχ : ∀ n, χ n ^ 6 = 1) (a : ℕ → ℂ) :
    (∑ n ∈ S, a n *
      (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p (χ n))) =
    (∑ n ∈ S, a n *
      ((χ n ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
       mask n (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p))) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [first_prime_product_identity side P parityBit ε₁ ε₂ n (χ n) (hχ n)]

theorem sum_first_prime_product_with_b0
    (S P : Finset ℕ) (side : Bool)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (χ : (n : ℕ) → MulChar (ZMod n) ℂ)
    (hχ : ∀ n, χ n ^ 6 = 1) (a : ℕ → ℂ)
    (b₀ m : ℕ)
    (hB : (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) ∣ b₀)
    (hb : b₀ ∣
      ((∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) *
       (∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p)) ^ m) :
    (∑ n ∈ S, a n *
      (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p (χ n))) =
    (∑ n ∈ S, a n *
      ((χ n ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
       mask n b₀)) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [first_prime_product_with_b0 side P parityBit ε₁ ε₂ n b₀ m (χ n) (hχ n) hB hb]

end PoissonFirstLocal

open Finset Complex

namespace ActualCubicChar

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]

omit [IsDomain R] in
private theorem cubic_roots_surjective (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    Function.Surjective (restrictRootsOfUnity ρ 3) := by
  intro η
  have hη : ((η : Fˣ) : F) ^ 3 = 1 := by
    exact (mem_rootsOfUnity' 3 (η : Fˣ)).mp η.property
  obtain ⟨j, _, hj⟩ := hζF.eq_pow_of_pow_eq_one hη
  let z : rootsOfUnity 3 R := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  refine ⟨z ^ j, ?_⟩
  apply rootsOfUnity.coe_injective
  change ρ (ζ ^ j) = ((η : Fˣ) : F)
  rw [map_pow]
  exact hj

private noncomputable def cubic_roots_equiv (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    rootsOfUnity 3 R ≃* rootsOfUnity 3 F := by
  classical
  letI : Fintype (rootsOfUnity 3 R) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  apply MulEquiv.ofBijective (restrictRootsOfUnity ρ 3)
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · exact cubic_roots_surjective ρ ζ hζ hζF
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hζ.card_rootsOfUnity, hζF.card_rootsOfUnity]

variable [Fintype F]

private theorem euler_jacobi_sum_zero (m : ℕ)
    (hm : 2 * m < Fintype.card F - 1) :
    (∑ x : F, x ^ m * (1 - x) ^ m) = 0 := by
  classical
  simp_rw [sub_eq_add_neg, add_pow]
  simp only [one_pow, one_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have he : m + (m - j) < Fintype.card F - 1 := by
    have hle : m - j ≤ m := Nat.sub_le m j
    omega
  calc
    (∑ x : F, x ^ m * ((-x) ^ (m - j) * ↑(m.choose j))) =
        ((-1 : F) ^ (m - j) * ↑(m.choose j)) *
          ∑ x : F, x ^ (m + (m - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [neg_pow, pow_add]
      ring
    _ = 0 := by rw [FiniteField.sum_pow_lt_card_sub_one F _ he]; ring

private def euler_to_roots (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    Fˣ →* rootsOfUnity 3 F where
  toFun u := rootsOfUnity.mkOfPowEq ((u : F) ^ m) (by
    rw [← pow_mul, ← hq]
    exact FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero)
  map_one' := by
    apply rootsOfUnity.coe_injective
    simp
  map_mul' u v := by
    apply rootsOfUnity.coe_injective
    simp [mul_pow]

private noncomputable def cubicResidueChar (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) : MulChar F R :=
  MulChar.ofUnitHom <|
    (Subgroup.subtype _).comp <|
      (cubic_roots_equiv ρ ζ hζ hζF).symm.toMonoidHom.comp
        (euler_to_roots m hq)

theorem cubicResidueChar_reduce_unit (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) (u : Fˣ) :
    ρ (cubicResidueChar ρ ζ hζ hζF m hq (u : F)) = (u : F) ^ m := by
  let e := cubic_roots_equiv ρ ζ hζ hζF
  simp only [cubicResidueChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (u : F) ^ m
  have he := e.apply_symm_apply (euler_to_roots m hq u)
  have he' := congrArg (fun v : rootsOfUnity 3 F => ((v : Fˣ) : F)) he
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (((euler_to_roots m hq u : rootsOfUnity 3 F) : Fˣ) : F) at he'
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (u : F) ^ m at he'
  exact he'

theorem cubicResidueChar_pow_three (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    cubicResidueChar ρ ζ hζ hζF m hq ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [(cubicResidueChar ρ ζ hζ hζF m hq).pow_apply_coe,
    MulChar.one_apply_coe]
  simp only [cubicResidueChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
  let v : rootsOfUnity 3 R :=
    (cubic_roots_equiv ρ ζ hζ hζF).symm (euler_to_roots m hq u)
  change (((v : Rˣ) : R) ^ 3) = 1
  exact (mem_rootsOfUnity' 3 (v : Rˣ)).mp v.property

end ActualCubicChar

namespace ActualEisensteinCubic

section

open NumberField

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def lambda : O := omega - 1

noncomputable instance quotientFintype (P : Ideal O) [P.IsMaximal] :
    Fintype (O ⧸ P) := Fintype.ofFinite _

noncomputable instance quotientField (P : Ideal O) [P.IsMaximal] :
    Field (O ⧸ P) := Ideal.Quotient.field P

theorem omega_primitive : IsPrimitiveRoot omega 3 := by
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot

def traceLambda : O := 1 + 2 * omega

theorem traceLambda_eq_unit_mul_lambda : traceLambda = -omega * lambda := by
  have hrel : omega ^ 2 + omega + 1 = 0 := by
    simpa only [IsCyclotomicExtension.Rat.Three.coe_eta, omega] using
      (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
        (IsCyclotomicExtension.zeta_spec 3 ℚ K))
  dsimp [traceLambda, lambda]
  linear_combination hrel

theorem neg_omega_isUnit : IsUnit (-omega) :=
  (omega_primitive.isUnit (by decide)).neg

theorem traceLambda_mem_iff (P : Ideal O) : traceLambda ∈ P ↔ lambda ∈ P := by
  rw [traceLambda_eq_unit_mul_lambda, mul_comm]
  exact P.mul_unit_mem_iff_mem neg_omega_isUnit

theorem traceLambda_sq_dvd_iff (x : O) :
    traceLambda ^ 2 ∣ x ↔ lambda ^ 2 ∣ x := by
  rw [traceLambda_eq_unit_mul_lambda, mul_pow]
  exact (neg_omega_isUnit.pow 2).mul_left_dvd

theorem omega_reduced_primitive (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hpow : (ρ omega) ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hne : ρ omega ≠ 1 := by
    intro he
    apply hgood
    have hz : ρ (omega - 1) = 0 := by rw [map_sub, he, map_one, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hz
  apply IsPrimitiveRoot.mk_of_lt _ (by decide) hpow
  intro l hl0 hl3
  have hl : l = 1 ∨ l = 2 := by omega
  rcases hl with rfl | rfl
  · simpa using hne
  · intro h2
    apply hne
    calc
      ρ omega = (ρ omega) ^ 2 * ρ omega := by rw [h2, one_mul]
      _ = (ρ omega) ^ 3 := by ring
      _ = 1 := hpow

theorem card_sub_one_div_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    3 ∣ Nat.card (O ⧸ P) - 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let hζ := omega_reduced_primitive P hgood
  let u : (O ⧸ P)ˣ := (hζ.isUnit (by decide)).unit
  have hu : IsPrimitiveRoot u 3 := hζ.isUnit_unit (by decide)
  have h := orderOf_dvd_natCard u
  rw [← hu.eq_orderOf] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using h

noncomputable def cubicChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  exact ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq

theorem cubicChar_reduce (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    (Ideal.Quotient.mk P) (cubicChar P hgood x) =
      x ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  rw [Nat.card_eq_fintype_card]
  change (Ideal.Quotient.mk P)
      (ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
        omega_primitive (omega_reduced_primitive P hgood) m hq x) = x ^ m
  by_cases hx : x = 0
  · subst x
    rw [(ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
      omega_primitive (omega_reduced_primitive P hgood) m hq).map_zero,
      map_zero, zero_pow hm.ne']
  · let u : (O ⧸ P)ˣ := (isUnit_iff_ne_zero.mpr hx).unit
    have hu : (u : O ⧸ P) = x := (isUnit_iff_ne_zero.mpr hx).unit_spec
    rw [← hu]
    exact ActualCubicChar.cubicResidueChar_reduce_unit
      (Ideal.Quotient.mk P) omega omega_primitive
      (omega_reduced_primitive P hgood) m hq u

theorem cubicChar_pow_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ^ 3 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  change ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq ^ 3 = 1
  exact ActualCubicChar.cubicResidueChar_pow_three
    (Ideal.Quotient.mk P) omega omega_primitive
    (omega_reduced_primitive P hgood) m hq

theorem cubicChar_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ≠ 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  intro hχ
  have hall : ∀ u : (O ⧸ P)ˣ, u ^ m = 1 := by
    intro u
    apply Units.ext
    have hr := cubicChar_reduce P hgood (u : O ⧸ P)
    rw [hχ, MulChar.one_apply_coe, map_one] at hr
    simpa only [Units.val_pow_eq_pow_val, Units.val_one,
      Nat.card_eq_fintype_card] using hr.symm
  have hdvd := (FiniteField.forall_pow_eq_one_iff (O ⧸ P) m).mp hall
  rw [hq] at hdvd
  have hle := Nat.le_of_dvd hm hdvd
  omega

theorem cubicChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : orderOf (cubicChar P hgood) = 3 := by
  have hdvd : orderOf (cubicChar P hgood) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (cubicChar_pow_three P hgood)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact False.elim ((cubicChar_ne_one P hgood) (orderOf_eq_one_iff.mp h1))
  · exact h3

theorem cubicJacobi_primary (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ z ∈ Algebra.adjoin ℤ {omega},
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) =
        -1 + z * lambda ^ 2 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  simpa only [lambda] using
    (exists_jacobiSum_eq_neg_one_add (n := 3) (by decide)
      (cubicChar_pow_three P hgood) (cubicChar_pow_three P hgood)
      (by simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three P hgood)
      omega_primitive)

theorem cubicJacobi_mem_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) ∈ P := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 2 * m < Fintype.card (O ⧸ P) - 1 := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_reduce P hgood]
  simp only [Nat.card_eq_fintype_card]
  exact ActualCubicChar.euler_jacobi_sum_zero m hm

theorem cubicJacobi_product (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ =
        (Nat.card (O ⧸ P) : O) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let ι : O →+* K := algebraMap O K
  let ψ := (cubicChar P hgood).ringHomComp ι
  have hchar : ringChar K ≠ ringChar (O ⧸ P) := by
    rw [ringChar.eq_zero]
    exact (CharP.char_is_prime (O ⧸ P) (ringChar (O ⧸ P))).ne_zero.symm
  have hψ : ψ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff RingOfIntegers.coe_injective).mpr
      (cubicChar_ne_one P hgood)
  have hχ2 : cubicChar P hgood * cubicChar P hgood ≠ 1 := by
    intro h
    have hd : orderOf (cubicChar P hgood) ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hψ2 : ψ * ψ ≠ 1 := by
    rw [show ψ * ψ =
      (cubicChar P hgood * cubicChar P hgood).ringHomComp ι by
        exact (MulChar.ringHomComp_mul _ _ _).symm]
    exact (MulChar.ringHomComp_ne_one_iff RingOfIntegers.coe_injective).mpr hχ2
  have hprod := jacobiSum_mul_jacobiSum_inv hchar hψ hψ hψ2
  apply RingOfIntegers.coe_injective
  change ι (jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹) =
    ι (Nat.card (O ⧸ P) : O)
  rw [map_mul, ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp,
    ← MulChar.ringHomComp_inv]
  simpa only [ψ, Nat.card_eq_fintype_card, map_natCast] using hprod

private noncomputable def conjK : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

noncomputable def conjO : O ≃+* O :=
  RingOfIntegers.mapRingEquiv conjK.toRingEquiv

theorem conjO_omega : conjO omega = omega ^ 2 := by
  apply RingOfIntegers.coe_injective
  change conjK (IsCyclotomicExtension.zeta 3 ℚ K) =
    (IsCyclotomicExtension.zeta 3 ℚ K) ^ 2
  exact IsCyclotomicExtension.fromZetaAut_spec
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

private theorem conjO_cubic_root (x : O) (hx : x ^ 3 = 1) :
    conjO x = x ^ 2 := by
  obtain ⟨j, _, hj⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  rw [← hj, map_pow, conjO_omega]
  simp only [← pow_mul]
  rw [Nat.mul_comm]

theorem cubicChar_conj_eq_inv (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    conjO (cubicChar P hgood x) = (cubicChar P hgood)⁻¹ x := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let χ := cubicChar P hgood
  have hinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using cubicChar_pow_three P hgood
  rw [hinv, χ.pow_apply' (by decide)]
  by_cases hx : x = 0
  · subst x
    rw [χ.map_zero, map_zero, zero_pow (by decide)]
  · have hχ3 : χ x ^ 3 = 1 := by
      rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    exact conjO_cubic_root (χ x) hχ3

theorem cubicJacobi_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ := by
  classical
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_conj_eq_inv P hgood]
  rfl

theorem cubicJacobi_mul_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
        (Nat.card (O ⧸ P) : O) := by
  rw [cubicJacobi_conj P hgood]
  exact cubicJacobi_product P hgood

end

private noncomputable def quadraticCharO (P : Ideal O) [P.IsMaximal] :
    MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  exact (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)

theorem quadraticCharO_sq (P : Ideal O) [P.IsMaximal] :
    quadraticCharO P ^ 2 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  change ((quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)) ^ 2 = 1
  exact ((quadraticChar_isQuadratic (O ⧸ P)).comp (Int.castRingHom O)).sq_eq_one

noncomputable def sexticChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O :=
  cubicChar P hgood ^ 2 * quadraticCharO P

theorem sexticChar_powers (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    sexticChar P hgood ^ 2 = cubicChar P hgood ∧
    sexticChar P hgood ^ 3 = quadraticCharO P ∧
    sexticChar P hgood ^ 6 = 1 := by
  have hc := cubicChar_pow_three P hgood
  have hq := quadraticCharO_sq P
  let c := cubicChar P hgood
  let q := quadraticCharO P
  have htwo : (c ^ 2 * q) ^ 2 = c := by
    calc
      (c ^ 2 * q) ^ 2 = c ^ 4 * q ^ 2 := by rw [mul_pow, ← pow_mul]
      _ = c := by rw [hq]; calc
        c ^ 4 * 1 = c ^ 3 * c := by group
        _ = c := by rw [hc, one_mul]
  have hthree : (c ^ 2 * q) ^ 3 = q := by
    calc
      (c ^ 2 * q) ^ 3 = (c ^ 3) ^ 2 * (q ^ 2) * q := by simp [mul_pow]; group
      _ = q := by rw [hc, hq]; group
  refine ⟨htwo, hthree, ?_⟩
  calc
    (c ^ 2 * q) ^ 6 = ((c ^ 2 * q) ^ 3) ^ 2 := by group
    _ = 1 := by rw [hthree, hq]

theorem cubicJacobi_unit_multiple (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hnorm : p * conjO p = (Nat.card (O ⧸ P) : O)) :
    ∃ u : Oˣ, jacobiSum (cubicChar P hgood) (cubicChar P hgood) = p * u := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hdiv : p ∣ J := (Ideal.mem_span_singleton).mp (hP ▸ cubicJacobi_mem_prime P hgood)
  obtain ⟨v, hv⟩ := hdiv
  have hqne : (Nat.card (O ⧸ P) : O) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hpne : p * conjO p ≠ 0 := by rw [hnorm]; exact hqne
  have hvnorm : v * conjO v = 1 := by
    apply mul_left_cancel₀ hpne
    calc
      (p * conjO p) * (v * conjO v) = (p * v) * conjO (p * v) := by
        rw [map_mul]; ring
      _ = J * conjO J := by rw [hv]
      _ = (Nat.card (O ⧸ P) : O) := cubicJacobi_mul_conj P hgood
      _ = (p * conjO p) * 1 := by rw [← hnorm, mul_one]
  have hvunit : IsUnit v := IsUnit.of_mul_eq_one (conjO v) hvnorm
  refine ⟨hvunit.unit, ?_⟩
  simpa only [hvunit.unit_spec] using hv

theorem lambda_not_dvd_two : ¬ lambda ∣ (2 : O) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprime : Prime lambda :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'
  let I : Ideal O := Ideal.span {lambda}
  have hI : I.IsMaximal := by
    have hp : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hprime
    have hne : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hprime.ne_zero
    exact hp.isMaximal hne
  let : I.IsMaximal := hI
  let : Field (O ⧸ I) := Ideal.Quotient.field I
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  have hcard : Nat.card (O ⧸ I) = 3 := by
    change Nat.card (O ⧸ Ideal.span {omega - 1}) = 3
    rw [omega,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
        (by decide)]
    norm_num
  intro hdiv
  have hmem : (2 : O) ∈ I := (Ideal.mem_span_singleton).mpr hdiv
  have hzero : (2 : O ⧸ I) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  have hchar : ringChar (O ⧸ I) = 2 := by
    have hdvd : ringChar (O ⧸ I) ∣ 2 := (ringChar.spec (O ⧸ I) 2).mp hzero
    exact (Nat.prime_dvd_prime_iff_eq
      (CharP.char_is_prime (O ⧸ I) (ringChar (O ⧸ I))) Nat.prime_two).mp hdvd
  have heven := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, hcard] at heven
  norm_num at heven

theorem cubicJacobi_eq_neg_primary_generator (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hnorm : p * conjO p = (Nat.card (O ⧸ P) : O))
    (hprimary : lambda ^ 2 ∣ p - 1) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  obtain ⟨u, hJu⟩ := cubicJacobi_unit_multiple P hgood p hP hnorm
  change J = p * (u : O) at hJu
  obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
  have hJmod : lambda ^ 2 ∣ J + 1 := by
    refine ⟨z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring
  have hucong : lambda ^ 2 ∣ (u : O) + 1 := by
    have heq : (u : O) + 1 = (J + 1) - (p - 1) * (u : O) := by
      rw [hJu]
      ring
    rw [heq]
    exact dvd_sub hJmod (dvd_mul_of_dvd_left hprimary _)
  have hunit : u = 1 ∨ u = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
    refine ⟨(-1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_neg, Int.cast_one, sub_neg_eq_add] using hucong
  rcases hunit with h1 | hneg
  · have htwo : lambda ^ 2 ∣ (2 : O) := by
      simpa [h1, one_add_one_eq_two] using hucong
    exact False.elim (lambda_not_dvd_two ((dvd_pow_self lambda (by decide)).trans htwo))
  · rw [hneg] at hJu
    simpa only [Units.val_neg, Units.val_one, mul_neg, mul_one] using hJu

private theorem conjK_ne_refl : conjK ≠ AlgEquiv.refl := by
  intro he
  have hw : omega ^ 2 = omega := by
    have hc : conjO omega = omega := by
      apply NumberField.RingOfIntegers.coe_injective
      change conjK (omega : K) = (omega : K)
      rw [he]
      rfl
    exact conjO_omega.symm.trans hc
  have hw1 : omega = 1 := by
    have hunit : IsUnit omega := omega_primitive.isUnit (by decide)
    apply (mul_left_cancel₀ hunit.ne_zero)
    calc
      omega * omega = omega ^ 2 := by ring
      _ = omega := hw
      _ = omega * 1 := by ring
  exact (omega_primitive.ne_one (by decide)) hw1

private theorem galois_card_two : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ K,
    IsCyclotomicExtension.finrank (n := 3) K
      (Polynomial.cyclotomic.irreducible_rat (by decide))]
  decide

private theorem galois_univ_pair [DecidableEq (K ≃ₐ[ℚ] K)] :
    (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {(AlgEquiv.refl : K ≃ₐ[ℚ] K), conjK} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, galois_card_two, Finset.card_pair]
  exact conjK_ne_refl.symm

private theorem norm_eq_mul_conjK (p : O) :
    ((Algebra.norm ℚ (p : K) : ℚ) : K) = (p : K) * conjK (p : K) := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  have h := Algebra.norm_eq_prod_automorphisms ℚ (p : K)
  rw [galois_univ_pair, Finset.prod_pair conjK_ne_refl.symm] at h
  simpa using h

theorem norm_int_eq_mul_conjO (p : O) :
    ((Algebra.norm ℤ p : ℤ) : O) = p * conjO p := by
  apply NumberField.RingOfIntegers.coe_injective
  change ((Algebra.norm ℤ p : ℤ) : K) = (p : K) * conjK (p : K)
  have h := norm_eq_mul_conjK p
  rw [← Algebra.coe_norm_int p] at h
  exact h

private theorem generator_mul_conj_eq_sign_card (P : Ideal O) [P.IsMaximal]
    (p : O) (hP : P = Ideal.span {p}) :
    p * conjO p = (Nat.card (O ⧸ P) : O) ∨
      p * conjO p = -(Nat.card (O ⧸ P) : O) := by
  have habs : (Algebra.norm ℤ p).natAbs = Nat.card (O ⧸ P) := by
    calc
      (Algebra.norm ℤ p).natAbs = Ideal.absNorm (Ideal.span {p}) :=
        (Ideal.absNorm_span_singleton p).symm
      _ = Ideal.absNorm P := by rw [← hP]
      _ = Nat.card (O ⧸ P) := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : (Algebra.norm ℤ p) * (Algebra.norm ℤ p) =
      (Nat.card (O ⧸ P) : ℤ) * (Nat.card (O ⧸ P) : ℤ) := by
    apply (Int.natAbs_eq_iff_mul_self_eq).mp
    simpa using habs
  have hzero : (Algebra.norm ℤ p - (Nat.card (O ⧸ P) : ℤ)) *
      (Algebra.norm ℤ p + (Nat.card (O ⧸ P) : ℤ)) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hzero with hpos | hneg
  · left
    have heq : Algebra.norm ℤ p = (Nat.card (O ⧸ P) : ℤ) := sub_eq_zero.mp hpos
    simp [← norm_int_eq_mul_conjO p, heq]
  · right
    have heq : Algebra.norm ℤ p = -(Nat.card (O ⧸ P) : ℤ) := add_eq_zero_iff_eq_neg.mp hneg
    simp [← norm_int_eq_mul_conjO p, heq]

theorem cubicJacobi_unit_multiple_of_principal (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p}) :
    ∃ u : Oˣ, jacobiSum (cubicChar P hgood) (cubicChar P hgood) = p * u := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hdiv : p ∣ J := (Ideal.mem_span_singleton).mp (hP ▸ cubicJacobi_mem_prime P hgood)
  obtain ⟨v, hv⟩ := hdiv
  have hqne : (Nat.card (O ⧸ P) : O) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hnorm := generator_mul_conj_eq_sign_card P p hP
  have hpne : p * conjO p ≠ 0 := by
    rcases hnorm with h | h
    · rw [h]; exact hqne
    · rw [h]; exact neg_ne_zero.mpr hqne
  have hprod : (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := by
    calc
      (p * conjO p) * (v * conjO v) = (p * v) * conjO (p * v) := by
        rw [map_mul]; ring
      _ = J * conjO J := by rw [hv]
      _ = (Nat.card (O ⧸ P) : O) := cubicJacobi_mul_conj P hgood
  have hvnorm : v * conjO v = 1 ∨ v * conjO v = -1 := by
    rcases hnorm with hpos | hneg
    · left
      apply mul_left_cancel₀ hpne
      calc
        (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := hprod
        _ = (p * conjO p) * 1 := by rw [hpos]; ring
    · right
      apply mul_left_cancel₀ hpne
      calc
        (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := hprod
        _ = (p * conjO p) * -1 := by rw [hneg]; ring
  have hvunit : IsUnit v := by
    rcases hvnorm with h | h
    · exact IsUnit.of_mul_eq_one (conjO v) h
    · apply IsUnit.of_mul_eq_one (-conjO v)
      rw [mul_neg, h]
      ring
  refine ⟨hvunit.unit, ?_⟩
  simpa only [hvunit.unit_spec] using hv

theorem cubicJacobi_eq_neg_primary_generator_of_principal (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  obtain ⟨u, hJu⟩ := cubicJacobi_unit_multiple_of_principal P hgood p hP
  change J = p * (u : O) at hJu
  obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
  have hJmod : lambda ^ 2 ∣ J + 1 := by
    refine ⟨z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring
  have hucong : lambda ^ 2 ∣ (u : O) + 1 := by
    have heq : (u : O) + 1 = (J + 1) - (p - 1) * (u : O) := by
      rw [hJu]
      ring
    rw [heq]
    exact dvd_sub hJmod (dvd_mul_of_dvd_left hprimary _)
  have hunit : u = 1 ∨ u = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
    refine ⟨(-1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_neg, Int.cast_one, sub_neg_eq_add] using hucong
  rcases hunit with h1 | hneg
  · have htwo : lambda ^ 2 ∣ (2 : O) := by
      simpa [h1, one_add_one_eq_two] using hucong
    exact False.elim (lambda_not_dvd_two ((dvd_pow_self lambda (by decide)).trans htwo))
  · rw [hneg] at hJu
    simpa only [Units.val_neg, Units.val_one, mul_neg, mul_one] using hJu

theorem cubicJacobi_generates_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    P = Ideal.span {jacobiSum (cubicChar P hgood) (cubicChar P hgood)} := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hnormJ : Algebra.norm ℤ J = (Nat.card (O ⧸ P) : ℤ) := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → O))
    change ((Algebra.norm ℤ J : ℤ) : O) = (Nat.card (O ⧸ P) : O)
    rw [norm_int_eq_mul_conjO]
    exact cubicJacobi_mul_conj P hgood
  have habsJ : Ideal.absNorm (Ideal.span {J}) = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_span_singleton, hnormJ]
    simp
  have habsP : Ideal.absNorm P = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hle : Ideal.span {J} ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr (cubicJacobi_mem_prime P hgood)
  obtain ⟨Q, hQ⟩ := (Ideal.dvd_iff_le).mpr hle
  have hq : Nat.card (O ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hQnorm : Ideal.absNorm Q = 1 := by
    have heq : Nat.card (O ⧸ P) = Nat.card (O ⧸ P) * Ideal.absNorm Q := by
      calc
        Nat.card (O ⧸ P) = Ideal.absNorm (Ideal.span {J}) := habsJ.symm
        _ = Ideal.absNorm (P * Q) := by rw [hQ]
        _ = Ideal.absNorm P * Ideal.absNorm Q := map_mul Ideal.absNorm P Q
        _ = Nat.card (O ⧸ P) * Ideal.absNorm Q := by rw [habsP]
    exact (mul_left_cancel₀ hq (heq.symm.trans (by ring)))
  have hQtop : Q = ⊤ := Ideal.absNorm_eq_one_iff.mp hQnorm
  change P = Ideal.span {J}
  rw [hQ, hQtop, ← Ideal.one_eq_top, mul_one]

theorem cubicJacobi_exists_primary_generator (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ p : O, P = Ideal.span {p} ∧ lambda ^ 2 ∣ p - 1 ∧
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  refine ⟨-J, ?_, ?_, by simp [J]⟩
  · have h := cubicJacobi_generates_prime P hgood
    simpa only [J, Ideal.span_singleton_neg] using h
  · obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
    refine ⟨-z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring

private theorem hgood_from_trace (P : Ideal O) (hgood : traceLambda ∉ P) :
    lambda ∉ P := by
  intro h
  exact hgood ((traceLambda_mem_iff P).mpr h)

theorem cubicJacobi_eq_neg_primary_generator_trace (P : Ideal O) [P.IsMaximal]
    (hgood : traceLambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : traceLambda ^ 2 ∣ p - 1) :
    jacobiSum (cubicChar P (hgood_from_trace P hgood))
      (cubicChar P (hgood_from_trace P hgood)) = -p := by
  let hgood' : lambda ∉ P := hgood_from_trace P hgood
  simpa only using cubicJacobi_eq_neg_primary_generator_of_principal
    P hgood' p hP ((traceLambda_sq_dvd_iff (p - 1)).mp hprimary)

theorem cubicGauss_cube {E : Type*} [Field E] (ι : O →+* E)
    (hι : Function.Injective ι) (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 =
      -(ι p) * (Nat.card (O ⧸ P) : E) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := cubicChar P hgood
  let ξ := χ.ringHomComp ι
  have hχ3 : χ ^ 3 = 1 := cubicChar_pow_three P hgood
  have hχne : χ ≠ 1 := cubicChar_ne_one P hgood
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have hd : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hξne : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff hι).mpr hχne
  have hξ2 : ξ * ξ ≠ 1 := by
    rw [show ξ * ξ = (χ * χ).ringHomComp ι by
      exact (MulChar.ringHomComp_mul χ χ ι).symm]
    exact (MulChar.ringHomComp_ne_one_iff hι).mpr hχ2
  have hχinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using hχ3
  have hξinv : ξ⁻¹ = ξ ^ 2 := by
    change (χ.ringHomComp ι)⁻¹ = (χ.ringHomComp ι) ^ 2
    rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_pow, hχinv]
  have hξmul : ξ * ξ = ξ⁻¹ := by rw [hξinv, pow_two]
  have hχneg : χ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hχ3
  have hξneg : ξ (-1) = 1 := by
    change ι (χ (-1)) = 1
    rw [hχneg, map_one]
  have hξinvneg : ξ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hξneg, inv_one]
  have hgs : gaussSum ξ ψ * gaussSum ξ⁻¹ ψ = (Nat.card (O ⧸ P) : E) := by
    have h := gaussSum_mul_gaussSum_eq_card hξne hψ
    have hshift := mul_gaussSum_inv_eq_gaussSum ξ⁻¹ ψ
    rw [hξinvneg, one_mul] at hshift
    rw [hshift] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hJ : jacobiSum ξ ξ = -(ι p) := by
    change jacobiSum (χ.ringHomComp ι) (χ.ringHomComp ι) = -(ι p)
    rw [jacobiSum_ringHomComp]
    rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
      map_neg]
  have hgj : gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ = gaussSum ξ ψ * gaussSum ξ ψ := by
    simpa only [hξmul] using jacobiSum_mul_nontrivial hξ2 ψ
  calc
    gaussSum ξ ψ ^ 3 = (gaussSum ξ ψ * gaussSum ξ ψ) * gaussSum ξ ψ := by ring
    _ = (gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ) * gaussSum ξ ψ := by rw [hgj]
    _ = (gaussSum ξ ψ * gaussSum ξ⁻¹ ψ) * jacobiSum ξ ξ := by ring
    _ = -(ι p) * (Nat.card (O ⧸ P) : E) := by rw [hgs, hJ]; ring

private noncomputable def complexEmbedding : K →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift

noncomputable def ringComplex : O →+* ℂ :=
  complexEmbedding.toRingHom.comp (algebraMap O K)

theorem ringComplex_injective : Function.Injective ringComplex :=
  complexEmbedding.injective.comp NumberField.RingOfIntegers.coe_injective

private theorem ringComplex_conjO (x : O) :
    ringComplex (conjO x) = star (ringComplex x) := by
  let z := ringComplex omega
  have hz3 : z ^ 3 = 1 := by
    change ringComplex omega ^ 3 = 1
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz3
    exact zero_ne_one hz3
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz3 (by decide)
  have hzstar : star z = z ^ 2 := by
    apply mul_left_cancel₀ hz0
    calc
      z * star z = 1 := by rw [← starRingEnd_apply, Complex.mul_conj', hznorm]; norm_num
      _ = z * z ^ 2 := by rw [← pow_succ', hz3]
  have hhom : ringComplex.comp conjO.toRingHom = (starRingEnd ℂ).comp ringComplex := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen]
    change ringComplex (conjO omega) = star (ringComplex omega)
    rw [conjO_omega, map_pow]
    exact hzstar.symm
  have hx := congrArg (fun f : O →+* ℂ => f x) hhom
  exact hx

theorem cubicGauss_cube_complex (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
      (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P)) ^ 3 =
      -(ringComplex p) * (Nat.card (O ⧸ P) : ℂ) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  exact cubicGauss_cube ringComplex ringComplex_injective P hgood p hP hprimary
    (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P))
    (AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (O ⧸ P))

theorem primary_generator_mul_conj_eq_card (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    p * conjO p = (Nat.card (O ⧸ P) : O) := by
  have h := cubicJacobi_mul_conj P hgood
  rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
    map_neg] at h
  simpa only [neg_mul_neg] using h

theorem cubicGauss_normalized_cube_complex (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    (gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
      (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P)) /
      (‖ringComplex p‖ : ℂ)) ^ 3 =
      -(ringComplex p) / (‖ringComplex p‖ : ℂ) := by
  let z := ringComplex p
  let g := gaussSum ((cubicChar P hgood).ringHomComp ringComplex)
    (AddChar.FiniteField.primitiveChar_to_Complex (O ⧸ P))
  have hnormO := primary_generator_mul_conj_eq_card P hgood p hP hprimary
  have hnormC := congrArg ringComplex hnormO
  rw [map_mul, ringComplex_conjO, map_natCast] at hnormC
  have hq : (Nat.card (O ⧸ P) : ℂ) = (‖z‖ : ℂ) ^ 2 := by
    simpa only [z, ← starRingEnd_apply, Complex.mul_conj'] using hnormC.symm
  have hqne : (Nat.card (O ⧸ P) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hn0 : (‖z‖ : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hq
    exact hqne hq
  have hg : g ^ 3 = -z * (Nat.card (O ⧸ P) : ℂ) :=
    cubicGauss_cube_complex P hgood p hP hprimary
  change (g / (‖z‖ : ℂ)) ^ 3 = -z / (‖z‖ : ℂ)
  rw [div_pow, hg, hq]
  field_simp

theorem cubicGauss_cube_mulShift {E : Type*} [Field E] (ι : O →+* E)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (ψ : AddChar (O ⧸ P) E) (a : (O ⧸ P)ˣ) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) (ψ.mulShift a) ^ 3 =
      gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let χ := (cubicChar P hgood).ringHomComp ι
  have hχ3 : χ ^ 3 = 1 := by
    change ((cubicChar P hgood).ringHomComp ι) ^ 3 = 1
    rw [MulChar.ringHomComp_pow, cubicChar_pow_three P hgood,
      MulChar.ringHomComp_one]
  have hχinv3 : (χ⁻¹ a) ^ 3 = 1 := by
    have h : (χ⁻¹) ^ 3 = 1 := by rw [inv_pow, hχ3, inv_one]
    rw [← (χ⁻¹).pow_apply_coe, h, MulChar.one_apply_coe]
  change gaussSum χ (ψ.mulShift a) ^ 3 = gaussSum χ ψ ^ 3
  rw [gaussSum_mulShift_eq, mul_pow, hχinv3, one_mul]

theorem quadraticCharO_ne_one (P : Ideal O) [P.IsMaximal]
    (hchar : ringChar (O ⧸ P) ≠ 2) : quadraticCharO P ≠ 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  change (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O) ≠ 1
  exact (MulChar.ringHomComp_ne_one_iff
    (Int.cast_injective (α := O))).2 (quadraticChar_ne_one hchar)

theorem sexticChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (sexticChar P hgood) = 6 := by
  have h2 := (sexticChar_powers P hgood).1
  have h3 := (sexticChar_powers P hgood).2.1
  have h6 := (sexticChar_powers P hgood).2.2
  have hdiv : orderOf (sexticChar P hgood) ∣ 6 :=
    orderOf_dvd_of_pow_eq_one h6
  have hne2 : orderOf (sexticChar P hgood) ≠ 2 := by
    intro he
    have hχ2 := pow_orderOf_eq_one (sexticChar P hgood)
    rw [he, h2] at hχ2
    exact cubicChar_ne_one P hgood hχ2
  have hne3 : orderOf (sexticChar P hgood) ≠ 3 := by
    intro he
    have hχ3 := pow_orderOf_eq_one (sexticChar P hgood)
    rw [he, h3] at hχ3
    exact quadraticCharO_ne_one P hchar hχ3
  have hne1 : orderOf (sexticChar P hgood) ≠ 1 := by
    intro he
    have hχ1 := orderOf_eq_one_iff.mp he
    rw [hχ1] at h2
    exact cubicChar_ne_one P hgood (by simpa using h2.symm)
  have hne0 : orderOf (sexticChar P hgood) ≠ 0 := by
    intro he
    norm_num [he] at hdiv
  have hpos : 0 < orderOf (sexticChar P hgood) := Nat.pos_of_ne_zero hne0
  have hle : orderOf (sexticChar P hgood) ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
  have hne4 : orderOf (sexticChar P hgood) ≠ 4 := by
    intro he
    norm_num [he] at hdiv
  have hne5 : orderOf (sexticChar P hgood) ≠ 5 := by
    intro he
    norm_num [he] at hdiv
  omega

theorem sexticChar_ne_quadratic_power (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    sexticChar P hgood ≠ (sexticChar P hgood) ^ 3 := by
  intro h
  have htwo : (sexticChar P hgood) ^ 2 = 1 := by
    calc
      (sexticChar P hgood) ^ 2 =
          (sexticChar P hgood) ^ 3 * (sexticChar P hgood)⁻¹ := by group
      _ = 1 := by rw [← h]; group
  have hdiv : orderOf (sexticChar P hgood) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one htwo
  rw [sexticChar_order P hgood hchar] at hdiv
  norm_num at hdiv

theorem sexticChar_reduce_unit (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (u : (O ⧸ P)ˣ) :
    (Ideal.Quotient.mk P) (sexticChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((Nat.card (O ⧸ P) - 1) / 6) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let N := Fintype.card (O ⧸ P)
  let m := (N - 1) / 6
  have hthree : 3 ∣ N - 1 := by
    simpa only [N, Nat.card_eq_fintype_card] using card_sub_one_div_three P hgood
  have hodd : N % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  have hN : 1 < N := Fintype.one_lt_card
  have hsix : 6 ∣ N - 1 := by omega
  have hsize : N - 1 = 6 * m := by
    dsimp [m]
    exact (Nat.mul_div_cancel_left' hsix).symm
  have hthird : (N - 1) / 3 = 2 * m := by omega
  have hhalf : N / 2 = 3 * m := by omega
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hquad : ρ (quadraticCharO P (u : O ⧸ P)) =
      (u : O ⧸ P) ^ (N / 2) := by
    change (quadraticChar (O ⧸ P) (u : O ⧸ P) : O ⧸ P) = _
    exact quadraticChar_eq_pow_of_char_ne_two' hchar (u : O ⧸ P)
  have hcub : ρ (cubicChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((N - 1) / 3) := by
    simpa only [N, Nat.card_eq_fintype_card] using cubicChar_reduce P hgood (u : O ⧸ P)
  have hfermat : (u : O ⧸ P) ^ (N - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero u)
  change ρ ((cubicChar P hgood ^ 2 * quadraticCharO P) (u : O ⧸ P)) = _
  rw [MulChar.mul_apply, MulChar.pow_apply', map_mul, map_pow, hcub, hquad]
  rw [hthird, hhalf]
  simpa only [Nat.card_eq_fintype_card, N, m] using
    (show ((u : O ⧸ P) ^ (2 * m)) ^ 2 * (u : O ⧸ P) ^ (3 * m) =
      (u : O ⧸ P) ^ m by
      calc
        ((u : O ⧸ P) ^ (2 * m)) ^ 2 * (u : O ⧸ P) ^ (3 * m) =
            (u : O ⧸ P) ^ (7 * m) := by
              rw [← pow_mul, ← pow_add]
              congr 1
              omega
        _ = (u : O ⧸ P) ^ m * (u : O ⧸ P) ^ (N - 1) := by
          rw [hsize, ← pow_add]; congr 1; omega
        _ = (u : O ⧸ P) ^ m := by rw [hfermat, mul_one])
  all_goals norm_num

theorem quotient_char_ne_two_of_two_not_mem (P : Ideal O) [P.IsMaximal]
    (h2 : (2 : O) ∉ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  intro heq
  have hz : ((ringChar (O ⧸ P) : ℕ) : O ⧸ P) = 0 := ringChar.Nat.cast_ringChar
  rw [heq] at hz
  apply h2
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (by simpa only [map_ofNat, Nat.cast_ofNat] using hz)

theorem sexticChar_zero_iff_mem (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (a : O) :
    sexticChar P hgood (Ideal.Quotient.mk P a) = 0 ↔ a ∈ P := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  rw [MulChar.apply_eq_zero_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using
    (Ideal.Quotient.eq_zero_iff_mem (I := P) (a := a))

theorem sexticChar_pow_zero_iff_mem (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (j : ℕ) (a : O) :
    (sexticChar P hgood ^ j) (Ideal.Quotient.mk P a) = 0 ↔ a ∈ P := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  rw [MulChar.apply_eq_zero_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using
    (Ideal.Quotient.eq_zero_iff_mem (I := P) (a := a))

end ActualEisensteinCubic

end

end OAI
end OAIOriginalModule0038

/-! Original module: OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding
Source SHA256: ce0a59ae784c27a535e465b0cc6a112bef83435b66c3a9bcb274ac05dbb4febe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0039




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

namespace EisensteinEmbedding

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

noncomputable def ζ : K := IsCyclotomicExtension.zeta 3 ℚ K
noncomputable def pb : PowerBasis ℤ O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis

noncomputable def omega3 : ℂ := ((-1 : ℂ) + (Real.sqrt 3 : ℝ) * Complex.I) / 2

theorem omega3_sq : omega3 ^ 2 + omega3 + 1 = 0 := by
  have hs : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs' : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by norm_cast
  have hquad : omega3 ^ 2 + omega3 + 1 =
      (3 + ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 * Complex.I ^ 2) / 4 := by
    unfold omega3
    ring
  rw [hs', Complex.I_sq] at hquad
  norm_num at hquad
  exact hquad

theorem omega3_im : omega3.im = Real.sqrt 3 / 2 := by
  simp [omega3]

theorem omega3_im_ne_zero : omega3.im ≠ 0 := by
  rw [omega3_im]
  exact div_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num))) (by norm_num)

theorem lam_ne_zero (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    1 + 2 * w ≠ 0 := by
  intro h
  have hw' : w = -(1 : ℂ) / 2 := by linear_combination h / 2
  rw [hw'] at hw
  norm_num at hw

theorem pb_minpoly : minpoly ℤ pb.gen =
    (Polynomial.X : Polynomial ℤ) ^ 2 + Polynomial.X + 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hgen : pb.gen = hζ.toInteger := by
    simpa only [pb] using hζ.integralPowerBasis_gen
  rw [hgen]
  calc
    minpoly ℤ (hζ.toInteger : O) =
        minpoly ℤ (hζ.toInteger : K) :=
          (NumberField.RingOfIntegers.minpoly_coe hζ.toInteger).symm
    _ = minpoly ℤ (IsCyclotomicExtension.zeta 3 ℚ K) := by
          exact congrArg (minpoly ℤ) hζ.coe_toInteger
    _ = Polynomial.cyclotomic 3 ℤ :=
          (Polynomial.cyclotomic_eq_minpoly hζ (by decide)).symm
    _ = _ := Polynomial.cyclotomic_three ℤ

noncomputable def embedding (w : ℂ) (hw : w ^ 2 + w + 1 = 0) : O →+* ℂ :=
  (pb.lift w (by
    rw [pb_minpoly]
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hw)).toRingHom

theorem embedding_gen (w : ℂ) (hw : w ^ 2 + w + 1 = 0) :
    embedding w hw pb.gen = w := by
  exact pb.lift_gen w (by
    rw [pb_minpoly]
    simpa only [map_add, map_pow, map_one, Polynomial.aeval_X] using hw)

theorem pb_dim : pb.dim = 2 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hdim := hζ.integralPowerBasis_dim
  have htot : Nat.totient 3 = 2 := by decide
  simpa only [pb, htot] using hdim

theorem exists_ab (x : O) : ∃ a b : ℤ, x = a + b * pb.gen := by
  let i0 : Fin pb.dim := ⟨0, by rw [pb_dim]; decide⟩
  let i1 : Fin pb.dim := ⟨1, by rw [pb_dim]; decide⟩
  let c := pb.basis.repr x
  have h := pb.basis.sum_repr x
  have huniv : (Finset.univ : Finset (Fin pb.dim)) = {i0, i1} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    have hi := i.isLt
    have hd := pb_dim
    simp only [i0, i1, Fin.ext_iff]
    omega
  rw [huniv, Finset.sum_insert (by simp [i0, i1]), Finset.sum_singleton] at h
  refine ⟨c i0, c i1, ?_⟩
  simpa only [pb.coe_basis, i0, i1, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, zsmul_eq_mul, mul_one] using h.symm

theorem embedding_apply_ab (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (a b : ℤ) :
    embedding w hw (a + b * pb.gen : O) =
      (a : ℂ) + (b : ℂ) * w := by
  simp only [map_add, map_mul, map_intCast, embedding_gen]

theorem embedding_injective (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (him : w.im ≠ 0) : Function.Injective (embedding w hw) := by
  intro x y hxy
  have hz : embedding w hw (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨a, b, hrepr⟩ := exists_ab (x - y)
  rw [hrepr, embedding_apply_ab] at hz
  have himz := congrArg Complex.im hz
  have hb : b = 0 := by
    simp only [Complex.add_im, Complex.intCast_im, zero_add,
      Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero, Complex.zero_im] at himz
    have hbc : (b : ℝ) = 0 := (mul_eq_zero.mp himz).resolve_right him
    exact_mod_cast hbc
  have ha : a = 0 := by
    rw [hb, Int.cast_zero, zero_mul, add_zero] at hz
    exact_mod_cast hz
  have hzero : x - y = 0 := by rw [hrepr, ha, hb]; simp
  exact sub_eq_zero.mp hzero

theorem trace_period_on_ringOfIntegers
    (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (ψ : AddChar ℂ ℂ) (lam : ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * w) / lam) = 1) :
    ∀ x : O, ψ (embedding w hw x / lam) = 1 := by
  intro x
  obtain ⟨a, b, hrepr⟩ := exists_ab x
  rw [hrepr, embedding_apply_ab]
  exact hperiod a b

end EisensteinEmbedding

namespace ConcreteTraceCRT

open EisensteinEmbedding IdealGaussCRT

noncomputable def eisEmbedding : O →+* ℂ := embedding omega3 omega3_sq

theorem eisEmbedding_injective : Function.Injective eisEmbedding :=
  embedding_injective omega3 omega3_sq omega3_im_ne_zero

theorem eisEmbedding_ne_zero {a : O} (ha : a ≠ 0) : eisEmbedding a ≠ 0 := by
  intro h
  exact ha (eisEmbedding_injective (by simpa using h))

noncomputable def eisLam : ℂ := 1 + 2 * omega3

theorem eisLam_ne_zero : eisLam ≠ 0 := lam_ne_zero omega3 omega3_sq

theorem eisPeriod (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1) :
    ∀ x : O, ψ (eisEmbedding x / eisLam) = 1 :=
  trace_period_on_ringOfIntegers omega3 omega3_sq ψ eisLam hperiod

def coordinateSubring : Subring ℂ where
  carrier := {z | ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * omega3}
  zero_mem' := ⟨0, 0, by simp⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a + c, b + d, ?_⟩
    push_cast
    ring
  neg_mem' := by
    rintro x ⟨a, b, rfl⟩
    refine ⟨-a, -b, ?_⟩
    push_cast
    ring
  mul_mem' := by
    rintro x y ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    refine ⟨a * c - b * d, a * d + b * c - b * d, ?_⟩
    push_cast
    linear_combination (b : ℂ) * (d : ℂ) * omega3_sq

theorem coordinateSubring_eq_traceSubring :
    coordinateSubring = ShortDraftTrace.eisensteinSubring := by
  rfl

noncomputable def toCoordinateSubring : O →+* coordinateSubring :=
  eisEmbedding.codRestrict coordinateSubring (by
    intro x
    obtain ⟨a, b, hrepr⟩ := exists_ab x
    rw [hrepr]
    change embedding omega3 omega3_sq (a + b * pb.gen : O) ∈ coordinateSubring
    rw [embedding_apply_ab]
    exact ⟨a, b, rfl⟩)

theorem toCoordinateSubring_injective : Function.Injective toCoordinateSubring := by
  intro x y h
  apply eisEmbedding_injective
  exact congrArg Subtype.val h

theorem toCoordinateSubring_surjective : Function.Surjective toCoordinateSubring := by
  rintro ⟨z, a, b, hz⟩
  refine ⟨(a + b * pb.gen : O), ?_⟩
  apply Subtype.ext
  change eisEmbedding (a + b * pb.gen : O) = z
  change embedding omega3 omega3_sq (a + b * pb.gen : O) = z
  rw [embedding_apply_ab]
  exact hz.symm

noncomputable def ringOfIntegersEquivCoordinateSubring : O ≃+* coordinateSubring :=
  RingEquiv.ofBijective toCoordinateSubring
    ⟨toCoordinateSubring_injective, toCoordinateSubring_surjective⟩

noncomputable def eisTraceModChar
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1)
    (a : O) (ha : a ≠ 0) : AddChar (O ⧸ Ideal.span {a}) ℂ :=
  traceModChar eisEmbedding ψ eisLam a
    (eisEmbedding_ne_zero ha) eisLam_ne_zero (eisPeriod ψ hperiod)

noncomputable def eisTraceProdChar
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ a b : ℤ,
      ψ (((a : ℂ) + (b : ℂ) * omega3) / eisLam) = 1)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0) :
    AddChar (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) ℂ :=
  traceProdChar eisEmbedding ψ eisLam a b
    (eisEmbedding_ne_zero ha) (eisEmbedding_ne_zero hb)
    eisLam_ne_zero (eisPeriod ψ hperiod)

theorem gauss_sum_actual_O
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ c d : ℤ,
      ψ (((c : ℂ) + (d : ℂ) * omega3) / eisLam) = 1)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (O ⧸ Ideal.span {a})]
    [Fintype (O ⧸ Ideal.span {b})]
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      eisTraceProdChar ψ hperiod a b ha hb x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (eisTraceModChar ψ hperiod a ha) *
      gaussSum χb (eisTraceModChar ψ hperiod b hb) := by
  simpa only [eisTraceProdChar, eisTraceModChar] using
    gauss_sum_trace_crt_of_coprime eisEmbedding ψ eisLam a b hcop
      (eisEmbedding_ne_zero ha) (eisEmbedding_ne_zero hb)
      eisLam_ne_zero (eisPeriod ψ hperiod) χa χb

theorem finite_quotient_span {a : O} (ha : a ≠ 0) :
    Finite (O ⧸ Ideal.span {a}) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  intro h
  exact ha (Ideal.span_singleton_eq_bot.mp h)

theorem finite_quotient_product {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) :
    Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  intro h
  have hab : a * b = 0 := Ideal.span_singleton_eq_bot.mp (by
    simpa only [Ideal.span_singleton_mul_span_singleton] using h)
  exact mul_ne_zero ha hb hab

end ConcreteTraceCRT

namespace ConcreteBreveE

open EisensteinEmbedding ConcreteTraceCRT

theorem breveE_period_coordinates :
    ∀ c d : ℤ,
      ShortDraftTrace.breveE
        (((c : ℂ) + (d : ℂ) * omega3) / eisLam) = 1 := by
  intro c d
  change ShortDraftTrace.breveE
    (((c : ℂ) + (d : ℂ) * ShortDraftTrace.ω₃) /
      (1 + 2 * ShortDraftTrace.ω₃)) = 1
  exact ShortDraftTrace.breveE_period_lam c d

theorem coordinateSubring_eq : coordinateSubring =
    ShortDraftTrace.eisensteinSubring := by
  rfl

noncomputable def ringOfIntegersEquivShortDraftE :
    O ≃+* ShortDraftTrace.eisensteinSubring :=
  coordinateSubring_eq ▸ ringOfIntegersEquivCoordinateSubring

theorem gauss_sum_breveE_actual_O
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (O ⧸ Ideal.span {a})]
    [Fintype (O ⧸ Ideal.span {b})]
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates
        a b ha hb x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (eisTraceModChar ShortDraftTrace.breveE
        breveE_period_coordinates a ha) *
      gaussSum χb (eisTraceModChar ShortDraftTrace.breveE
        breveE_period_coordinates b hb) := by
  exact gauss_sum_actual_O ShortDraftTrace.breveE
    breveE_period_coordinates a b ha hb hcop χa χb

end ConcreteBreveE

namespace ActualEisensteinCubic

theorem eisEmbedding_conjO (x : O) :
    ConcreteTraceCRT.eisEmbedding (conjO x) =
      star (ConcreteTraceCRT.eisEmbedding x) := by
  let ι := ConcreteTraceCRT.eisEmbedding
  let z := ι omega
  have hz3 : z ^ 3 = 1 := by
    change ι omega ^ 3 = 1
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hz3
    exact zero_ne_one hz3
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz3 (by decide)
  have hzstar : star z = z ^ 2 := by
    apply mul_left_cancel₀ hz0
    calc
      z * star z = 1 := by rw [← starRingEnd_apply, Complex.mul_conj', hznorm]; norm_num
      _ = z * z ^ 2 := by rw [← pow_succ', hz3]
  have hhom : ι.comp conjO.toRingHom = (starRingEnd ℂ).comp ι := by
    apply RingHom.toIntAlgHom_injective
    apply (IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis.algHom_ext
    rw [(IsCyclotomicExtension.zeta_spec 3 ℚ K).integralPowerBasis_gen]
    change ι (conjO omega) = star (ι omega)
    rw [conjO_omega, map_pow]
    exact hzstar.symm
  have hx := congrArg (fun f : O →+* ℂ => f x) hhom
  exact hx

theorem cubicGauss_normalized_cube_eis (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive) :
    (gaussSum ((cubicChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ψ /
      (‖ConcreteTraceCRT.eisEmbedding p‖ : ℂ)) ^ 3 =
      -(ConcreteTraceCRT.eisEmbedding p) /
        (‖ConcreteTraceCRT.eisEmbedding p‖ : ℂ) := by
  let z := ConcreteTraceCRT.eisEmbedding p
  let g := gaussSum ((cubicChar P hgood).ringHomComp
    ConcreteTraceCRT.eisEmbedding) ψ
  have hnormO := primary_generator_mul_conj_eq_card P hgood p hP hprimary
  have hnormC := congrArg ConcreteTraceCRT.eisEmbedding hnormO
  rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
  have hq : (Nat.card (O ⧸ P) : ℂ) = (‖z‖ : ℂ) ^ 2 := by
    simpa only [z, ← starRingEnd_apply, Complex.mul_conj'] using hnormC.symm
  have hqne : (Nat.card (O ⧸ P) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hn0 : (‖z‖ : ℂ) ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hq
    exact hqne hq
  have hg : g ^ 3 = -z * (Nat.card (O ⧸ P) : ℂ) :=
    cubicGauss_cube ConcreteTraceCRT.eisEmbedding
      ConcreteTraceCRT.eisEmbedding_injective P hgood p hP hprimary ψ hψ
  change (g / (‖z‖ : ℂ)) ^ 3 = -z / (‖z‖ : ℂ)
  rw [div_pow, hg, hq]
  field_simp

open AddChar MulChar

private theorem sextic_complex_pow_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : j < 6) :
    ((sexticChar P hgood).ringHomComp ringComplex) ^ j ≠ 1 := by
  rw [MulChar.ringHomComp_pow]
  apply (MulChar.ringHomComp_ne_one_iff ringComplex_injective).2
  apply pow_ne_one_of_lt_orderOf hj0
  rwa [sexticChar_order P hgood hchar]

theorem sextic_local_fourier_nonzero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6)
    (h : O ⧸ P) (hh : h ≠ 0) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ j) y * ψ (-h * y)) =
    ((((sexticChar P hgood).ringHomComp ringComplex) ^ j) h)⁻¹ *
      gaussSum (((sexticChar P hgood).ringHomComp ringComplex) ^ j)
        (ψ.mulShift (-1)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ P) ℂ := ((sexticChar P hgood).ringHomComp ringComplex) ^ j
  have hχ : χ ≠ 1 := sextic_complex_pow_ne_one P hgood hchar hj0 hj6
  have ht := ShortDraftFiniteGaussFourier.gauss_transform χ (ψ.mulShift (-1)) hχ h
  rw [ite_eq_right hh] at ht
  simpa only [χ, AddChar.mulShift_apply, neg_one_mul, mul_assoc,
    neg_mul, one_mul] using ht

theorem sextic_local_fourier_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ j) y * ψ (-(0 : O ⧸ P) * y)) =
    0 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ P) ℂ := ((sexticChar P hgood).ringHomComp ringComplex) ^ j
  have hχ : χ ≠ 1 := sextic_complex_pow_ne_one P hgood hchar hj0 hj6
  simpa only [χ, neg_zero, zero_mul, map_zero_eq_one, mul_one] using
    MulChar.sum_eq_zero_of_ne_one hχ

theorem sextic_local_fourier_jzero_nonzero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (hψ : ψ.IsPrimitive) (h : O ⧸ P) (hh : h ≠ 0) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ 0) y * ψ (-h * y)) =
      -1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hneg : -h ≠ 0 := neg_ne_zero.mpr hh
  have hnon : ψ.mulShift (-h) ≠ 1 := hψ hneg
  have ht := gaussSum_one_left hnon
  simpa only [pow_zero, gaussSum, AddChar.mulShift_apply] using ht

theorem sextic_local_fourier_jzero_zero (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ 0) y *
        ψ (-(0 : O ⧸ P) * y)) = (Nat.card (O ⧸ P) : ℂ) - 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hsum := MulChar.sum_one_eq_card_units (R := O ⧸ P) (R' := ℂ)
  have hcard : (Fintype.card (O ⧸ P) : ℂ) =
      (Fintype.card (O ⧸ P)ˣ : ℂ) + 1 := by
    exact_mod_cast (Fintype.card_eq_card_units_add_one (α := O ⧸ P))
  simpa only [pow_zero, neg_zero, zero_mul, map_zero_eq_one, mul_one,
    Nat.card_eq_fintype_card, hcard, add_sub_cancel_right] using hsum

open AddChar MulChar

noncomputable def canonicalSextic (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) ℂ :=
  (sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding

theorem canonicalSextic_pow_six (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : canonicalSextic P hgood ^ 6 = 1 := by
  change ((sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ^ 6 = 1
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).2.2,
    MulChar.ringHomComp_one]

theorem canonicalSextic_pow_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : j < 6) :
    canonicalSextic P hgood ^ j ≠ 1 := by
  change ((sexticChar P hgood).ringHomComp ConcreteTraceCRT.eisEmbedding) ^ j ≠ 1
  rw [MulChar.ringHomComp_pow]
  apply (MulChar.ringHomComp_ne_one_iff
    ConcreteTraceCRT.eisEmbedding_injective).2
  apply pow_ne_one_of_lt_orderOf hj0
  rwa [sexticChar_order P hgood hchar]

theorem canonical_A5_jone (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      ((χ⁻¹) ^ 2) σ *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ * (χ ^ 3) ε) *
      (χ ^ 3) x := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  dsimp
  rw [Nat.card_eq_fintype_card]
  exact ShortDraftLocal.sextic_fourier_theta_row
    (canonicalSextic P hgood) ψ (canonicalSextic_pow_six P hgood)
    (canonicalSextic_pow_ne_one P hgood hchar (by decide : (3:ℕ) ≠ 0)
      (by decide : (3:ℕ) < 6)) σ ε x

theorem canonical_A5_jfour (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ ≠ 1)
    (σ : (O ⧸ P)ˣ) (ε x : O ⧸ P) :
    let χ := canonicalSextic P hgood
    (Nat.card (O ⧸ P) : ℂ)⁻¹ *
      (∑ h : (O ⧸ P)ˣ,
        (∑ t : O ⧸ P, (χ ^ 4) t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : (O ⧸ P)ˣ) : O ⧸ P))) =
      (((χ⁻¹) ^ 2) σ) *
      ((Nat.card (O ⧸ P) : ℂ)⁻¹ *
        gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (if ε * x = 0 then (Fintype.card (O ⧸ P)ˣ : ℂ) else -1)) := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
