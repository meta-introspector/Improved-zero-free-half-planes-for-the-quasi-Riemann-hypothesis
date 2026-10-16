    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V X d h b =
    ∫ t : ℝ, ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
        ‖rayPairWeight p r D h‖ *
        (‖beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D‖ ^ 2 *
          ‖dilatedRayColumn p hg F D
            (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative
              (normalizedColumn p C) V (columnLog p X) t)
            negative (if negative then r.1 else r.2) p B v ε₁ ε₂ c d
            (h * f ^ 2 * dilationLabel p B v ε₁ ε₂)‖ ^ 2) := by
  unfold firstColumnEnergy
  rw [normalized_originalLabelColumn]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  unfold rayIdealEnergy
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  rw [rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv negative _
    (normalizedColumn p C) V (columnLog p X) t c d f h, norm_mul, mul_pow]

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

def firstDivisorWeight {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (E : Finset ι) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
    (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)

theorem retained_first_kernel_energy_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale →
      ∀ (Ω : Finset (Finset ι × O)) (w : Finset ι × O → ℂ),
      (∀ x ∈ Ω, x.2 ≠ 0) → ∃ b : (Finset ι × O) → 𝓢(ℝ, ℂ),
      (∀ x ∈ Ω, Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b x t‖) volume ∧
        (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2) ^ A *
            (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b x t‖) ≤ K) ∧
      ‖∑ x ∈ Ω, (w x * firstDivisorWeight p x.1) *
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
        Real.sqrt (∑ x ∈ Ω, ‖w x * firstDivisorWeight p x.1‖ *
          firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁
            (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2 (b x)) *
        Real.sqrt (∑ x ∈ Ω, ‖w x * firstDivisorWeight p x.1‖ *
          firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂
            (primeSubsetGenerator (fun i => Ideal.span {p i}) x.1) x.2 (b x)) := by
  obtain ⟨K, hK, hs⟩ := actual_first_kernel_energy_bound p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL Ω w hΩ
  let d := fun x : Finset ι × O => primeSubsetGenerator (fun i => Ideal.span {p i}) x.1
  have hfam : ∀ x : Finset ι × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ Ω →
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
      (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ (d x) x.2) ^ A *
        (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ K ∧
      ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale (d x) x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
        Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ (d x) x.2 b) *
        Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ (d x) x.2 b) := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨b, hb⟩ := hs lengthScale hL (d x) x.2 (primeSubsetGenerator_ne_zero _ _) (hΩ x hx)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  refine ⟨b, fun x hx => ⟨(hb x hx).1, (hb x hx).2.1⟩, ?_⟩
  let U := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ (d x) x.2 (b x)
  let V := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ (d x) x.2 (b x)
  let a := fun x => ‖w x * firstDivisorWeight p x.1‖
  let q := lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hU (x) : 0 ≤ U x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ _ _ _
  have hV (x) : 0 ≤ V x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ _ _ _
  have hterm (x) : a x * (Real.sqrt (U x) * Real.sqrt (V x)) =
      Real.sqrt (a x * U x) * Real.sqrt (a x * V x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt (a x)) ^ 2 * (Real.sqrt (U x) * Real.sqrt (V x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ Ω, ‖(w x * firstDivisorWeight p x.1) *
        actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale (d x) x.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x ∈ Ω, q * (Real.sqrt (a x * U x) * Real.sqrt (a x * V x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ a x * (q * Real.sqrt (U x) * Real.sqrt (V x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2.2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ Ω, Real.sqrt (a x * U x) * Real.sqrt (a x * V x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ Ω, a x * U x) * Real.sqrt (∑ x ∈ Ω, a x * V x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le Ω
        (fun x => mul_nonneg (norm_nonneg _) (hU x))
        (fun x => mul_nonneg (norm_nonneg _) (hV x))) hq
    _ = _ := (mul_assoc _ _ _).symm

end

section
open scoped BigOperators Classical
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)

theorem blockRow_norm_le_one {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S : Finset ι) (e : ι → ℕ) (a : O) : ‖blockRow p hg S e a‖ ≤ 1 := by
  rw [blockRow_eq_product, norm_prod]
  calc
    _ ≤ ∏ i ∈ S, (1 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i hi
      let : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
      exact FiniteRayExpansion.norm_char_le_one _ _
    _ = 1 := by simp

theorem cubeBaseFactor_norm_le_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (d h : O) :
    ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ ≤ 1 := by
  have he : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂,
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val ≠ 0 := by
    intro i hi
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hi).2
  simp only [cubeBaseFactor, norm_mul, norm_star,
    gaussBlock_norm_one p hp hcop hg hc _ _ he (fun _ _ => ZMod.val_lt _), one_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg _ _ _)).trans (blockRow_norm_le_one p hg _ _ _)

theorem rayPairWeight_norm_le {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : O) :
    ‖rayPairWeight p r D h‖ ≤ ‖crossCoeff r.1 r.2‖ := by
  rw [norm_rayPairWeight p hinj hc]
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) D h‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  exact mul_le_of_le_one_right (norm_nonneg _) hm

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FourierBridge (logPhase)

def firstLogDensity (J : ℕ) (t : ℝ) : ℝ := ((1 + ‖t‖) ^ (J + 2))⁻¹

theorem firstLogDensity_nonneg (J : ℕ) (t : ℝ) : 0 ≤ firstLogDensity J t := by
  unfold firstLogDensity
  positivity

theorem firstLogDensity_integrable (J : ℕ) : Integrable (firstLogDensity J) volume := by
  have h := integrable_one_add_norm (E := ℝ) («μ» := (volume : Measure ℝ))
    (r := (J + 2 : ℕ)) (by norm_num; linarith [Nat.cast_nonneg (α := ℝ) J])
  convert h using 1
  funext t
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rfl

theorem firstLogDensity_moment_integrable (J : ℕ) :
    Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * firstLogDensity J t) volume := by
  convert firstLogDensity_integrable 0 using 1
  funext t
  have ht : 1 + ‖t‖ ≠ 0 := ne_of_gt (by positivity)
  simp only [firstLogDensity, zero_add, pow_add, mul_inv_rev]
  field_simp

theorem two_variable_radial_envelope (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
        ∫ t : ℝ, (V₁ x * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) ∧
      (∀ t : ℝ, (1 + R) ^ A * ‖b t‖ ≤ K * firstLogDensity J t) := by
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let M : Bool → ℝ := fun j => if j then M₂ else M₁
  have hM : ∀ j, 0 ≤ M j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ M j := by
    intro j; cases j
    · exact hV₁
    · exact hV₂
  obtain ⟨K, hK, hsep⟩ := EisensteinSchwartzPoisson.paperRadialFourier_log_separation_envelope
    W V (fun _ => -1) M hM hV A (J + 2)
  refine ⟨K, hK, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, _, hpoint⟩ := hsep R hR
  refine ⟨b, ?_, ?_⟩
  · intro x y
    have hs := hb (fun j => if j then y else x)
    simpa only [V, Fintype.prod_bool, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
      neg_one_mul, mul_neg_one, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using hs
  · intro t
    rw [firstLogDensity, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖t‖) (J + 2))).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hpoint t

theorem actualFirstKernel_eq_separated {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (lengthScale : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W
      (firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h * Real.exp (-x-y)) =
      ∫ t : ℝ, (V₁ x * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) :
    actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h =
    ((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        idealPairReindex p hg F
          (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
            (normalizedColumn p C₁) V₁ (columnLog p X₁) t d)
          (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
            (normalizedColumn p C₂) V₂ (columnLog p X₂) t d) h := by
  have hs := cube_integral_of_radial_separation p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ (normalizedColumn p C₁) (normalizedColumn p C₂) d h W V₁ V₂
    (columnLog p X₁) (columnLog p X₂)
    (firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) b hsep
  simp only [cubeLogCoefficient, Bool.false_eq_true, ite_false, ite_true]
  rw [← hs.2]
  unfold actualFirstKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · rw [ite_eq_left hNP, ite_eq_left hNP]
    have hNB := hFB.mono_left (Finset.mem_powerset.mp hN)
    have hPB := hFB.mono_left (Finset.mem_powerset.mp hP)
    rw [actual_radial_argument p hp N P (cubeActiveSupport B v ε₁ ε₂) hNP
      (hNB.mono_right (Finset.filter_subset _ _))
      (hPB.mono_right (Finset.filter_subset _ _)) lengthScale X₁ X₂ hX₁ hX₂ d h]
    have hpre := actual_pair_prefactor p hp hcop hg N P B hNP hNB hPB v ε₁ ε₂ C₁ C₂ lengthScale d h
    calc
      _ = (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P) *
          paperRadialFourier W (lengthScale * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)))) *
          (((lengthScale : ℂ) / (‖eisEmbedding (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
            threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h) := by ring
      _ = _ := by rw [hpre]; ring
  · simp [hNP]

theorem actual_first_kernel_energy_envelope {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_envelope W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  have hR : 0 < firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h := by
    unfold firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  rw [actualFirstKernel_eq_separated p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ lengthScale d h b hsep, norm_mul]
  have hi := cube_integral_norm_le_energy p hg F
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
      (normalizedColumn p C₁) V₁ (columnLog p X₁) t d)
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
      (normalizedColumn p C₂) V₂ (columnLog p X₂) t d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ false _ _ _ t d S)
    h b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
    abs_of_nonneg (norm_nonneg _)]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi (div_nonneg hL.le (norm_nonneg _))

end FirstPassCubeLabels

end

end OAI
end OAIOriginalModule0111

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.DivisorBlocks
Source SHA256: 48be5e32c0a93e4db774fb62cd825cba57c02074ed646a5bd8dbab81968d3f60
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0112


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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks

def quotientBlock {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  blockValue left right (fun D => quotientMatrix D rows left)
    (fun E => quotientMatrix E rows right) a b D E

theorem canonical_divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 ≤
      256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
        (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
        (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  have hS0 (D) (hD : D ∈ S) : D ≠ 0 := by
    intro hz
    have hh := (hS D hD).1
    simp only [hz, map_zero, Nat.cast_zero] at hh
    linarith
  have hT0 (E) (hE : E ∈ T) : E ≠ 0 := by
    intro hz
    have hh := (hT E hE).1
    simp only [hz, map_zero, Nat.cast_zero] at hh
    linarith
  have hA (D) (hD : D ∈ S) :
      ‖FiniteSieveOperator.operator (quotientMatrix D rows left)‖ ^ 2 ≤ sieveNorm M (N / D₁) := by
    apply (quotientMatrix_squared_norm_le D (hS0 D hD) rows left hr hl M N hrows hleft).trans
    exact sieveNorm_mono le_rfl (div_le_div_of_nonneg_left (by linarith) (by linarith) (hS D hD).1)
  have hB (E) (hE : E ∈ T) :
      ‖FiniteSieveOperator.operator (quotientMatrix E rows right)‖ ^ 2 ≤ sieveNorm M (N / D₂) := by
    apply (quotientMatrix_squared_norm_le E (hT0 E hE) rows right hr hri M N hrows hright).trans
    exact sieveNorm_mono le_rfl (div_le_div_of_nonneg_left (by linarith) (by linarith) (hT E hE).1)
  have hsCard := DescentFiberCost.finite_ideal_count_real S (2 * D₁) (by linarith)
    hS0 (fun D hD => (hS D hD).2)
  have htCard := DescentFiberCost.finite_ideal_count_real T (2 * D₂) (by linarith)
    hT0 (fun E hE => (hT E hE).2)
  have hh := divisor_block_bound ε hε S T left right (fun j => (hleft j).1.1)
    (fun k => (hright k).1.1) N N (by linarith) (by linarith)
    (fun j => (hleft j).2) (fun k => (hright k).2)
    (fun D => quotientMatrix D rows left) (fun E => quotientMatrix E rows right) a b
    (sieveNorm M (N / D₁)) (sieveNorm M (N / D₂)) (sieveNorm_nonneg _ _) (sieveNorm_nonneg _ _) hA hB
  have hs := (supportConstant_pos ε hε).le
  have hd := (divisorConstant_pos ε hε).le
  have hb1 := sieveNorm_nonneg M (N / D₁)
  have hb2 := sieveNorm_nonneg M (N / D₂)
  change (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 ≤ _ at hh
  apply hh.trans
  calc
    _ ≤ (128 * (2 * D₁)) * (128 * (2 * D₂)) *
        (sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
          (supportConstant ε hε * N ^ ε) * (supportConstant ε hε * N ^ ε)) *
        ((divisorConstant ε hε * N ^ ε) * ∑ j, ‖a j‖ ^ 2) *
        ((divisorConstant ε hε * N ^ ε) * ∑ k, ‖b k‖ ^ 2) := by gcongr
    _ = _ := by ring

end

section
open ConcretePrimeRowBridge ActualEisensteinCubic

theorem quadraticRow_norm_le_one (I : Ideal O) (z : O) : ‖quadraticRow I z‖ ≤ 1 := by
  by_cases hI : Admissible I
  · rw [quadraticRow, dite_eq_left hI]
    exact QuadraticMainOperatorBound.ideal_quadraticRow_norm_le_one {I}
      (singletonPositive I hI) (singletonGood I hI) I z
  · simp [quadraticRow, hI]

theorem quadraticRow_mul (I J : Ideal O) (hIJ : Admissible (I * J)) (z : O) :
    quadraticRow (I * J) z = quadraticRow I z * quadraticRow J z := by
  have hI : Admissible I := admissible_of_dvd hIJ (dvd_mul_right I J)
  have hJ : Admissible J := admissible_of_dvd hIJ (dvd_mul_left J I)
  let F : Finset (Ideal O) := {I, J, I * J}
  have hF : ∀ K ∈ F, Admissible K := by
    intro K hK
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl
    · exact hI
    · exact hJ
    · exact hIJ
  have hIF : I ∈ F := by simp [F]
  have hJF : J ∈ F := by simp [F]
  have hIJF : I * J ∈ F := by simp [F]
  have hu : idealSupport F (I * J) = idealSupport F I ∪ idealSupport F J := by
    ext P
    simp only [mem_idealSupport_iff, UniqueFactorizationMonoid.normalizedFactors_mul hI.1 hJ.1,
      Multiset.mem_add, Finset.mem_union]
  have hd : Disjoint (idealSupport F I) (idealSupport F J) := by
    apply Finset.disjoint_left.mpr
    intro P hPI hPJ
    have hpI := (mem_idealSupport_iff F I P).mp hPI
    have hpJ := (mem_idealSupport_iff F J P).mp hPJ
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val hpI
    have hi : P.val ∣ I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpI
    have hj : P.val ∣ J := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hpJ
    exact hp.not_isUnit ((IsRelPrime.of_squarefree_mul hIJ.2.1) hi hj)
  rw [quadraticRow_eq F hF (I * J) hIJF z, quadraticRow_eq F hF I hIF z,
    quadraticRow_eq F hF J hJF z]
  unfold idealSexticRow finiteSquarefreeRow
  rw [hu, Finset.prod_union hd, mul_pow]

theorem quadraticRow_divisor_factor (I D : Ideal O) (hI : Admissible I) (hD : D ∣ I) (z : O) :
    quadraticRow I z = quadraticRow D z * quadraticRow (idealQuotient D I) z := by
  have h := quadraticRow_mul D (idealQuotient D I) (by rwa [idealQuotient_mul hD]) z
  simpa only [idealQuotient_mul hD] using h

end

open IdealDivisorBilinearBlocks CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

def originalBlock {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) : ℝ :=
  blockValue left right (fun _ i j => quadraticRow (left j) (primaryGenerator (rows i)))
    (fun _ i k => quadraticRow (right k) (primaryGenerator (rows i))) a b D E

theorem original_entry_factor {m n : Type*} (rows : m → Ideal O) (cols : n → Ideal O)
    (hcols : ∀ j, Admissible (cols j)) (a : n → ℂ) (D : Ideal O) (i : m) (j : n) :
    quadraticRow (cols j) (primaryGenerator (rows i)) * (if D ∣ cols j then a j else 0) =
      quadraticRow D (primaryGenerator (rows i)) *
        (quotientMatrix D rows cols i j * (if D ∣ cols j then a j else 0)) := by
  by_cases h : D ∣ cols j
  · simp only [h, ite_true, quotientMatrix]
    rw [quadraticRow_divisor_factor (cols j) D (hcols j) h]
    ring
  · simp [h, quotientMatrix]

theorem originalBlock_le_quotientBlock {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) :
    originalBlock rows left right a b D E ≤ quotientBlock rows left right a b D E := by
  change (∑ i, _) ≤ ∑ i, _
  apply Finset.sum_le_sum
  intro i _
  have heq : (∑ j, ∑ k, if IsCoprime (left j) (right k) then
      star (quadraticRow (left j) (primaryGenerator (rows i)) * (if D ∣ left j then a j else 0)) *
      (quadraticRow (right k) (primaryGenerator (rows i)) * (if E ∣ right k then b k else 0)) else 0) =
      (star (quadraticRow D (primaryGenerator (rows i))) * quadraticRow E (primaryGenerator (rows i))) *
        (∑ j, ∑ k, if IsCoprime (left j) (right k) then
          star (quotientMatrix D rows left i j * (if D ∣ left j then a j else 0)) *
          (quotientMatrix E rows right i k * (if E ∣ right k then b k else 0)) else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : IsCoprime (left j) (right k)
    · rw [ite_eq_left h, ite_eq_left h]
      rw [original_entry_factor rows left hleft a D i j,
        original_entry_factor rows right hright b E i k, star_mul]
      ring
    · simp only [ite_eq_right h, mul_zero]
  change ‖∑ j, ∑ k, if IsCoprime (left j) (right k) then
      star (quadraticRow (left j) (primaryGenerator (rows i)) * (if D ∣ left j then a j else 0)) *
      (quadraticRow (right k) (primaryGenerator (rows i)) * (if E ∣ right k then b k else 0)) else 0‖ ≤ _
  rw [heq, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_mul, norm_star]
  exact (mul_le_mul (quadraticRow_norm_le_one D _) (quadraticRow_norm_le_one E _)
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem original_rectangular_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, originalBlock rows left right a b D E) ^ 2 ≤
      (∑ D ∈ S, ∑ E ∈ T, quotientBlock rows left right a b D E) ^ 2 := by
  apply pow_le_pow_left₀
  · exact Finset.sum_nonneg (fun D _ => Finset.sum_nonneg (fun E _ =>
      blockValue_nonneg left right _ _ a b D E))
  · apply Finset.sum_le_sum
    intro D hD
    exact Finset.sum_le_sum (fun E hE => originalBlock_le_quotientBlock
      rows left right hleft hright a b D E)

theorem canonical_original_divisor_block_bound {m n p : Type*}
    [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, originalBlock rows left right a b D E) ^ 2 ≤
      256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
        (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
        (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
  exact (original_rectangular_bound S T rows left right
    (fun j => (hleft j).1) (fun k => (hright k).1) a b).trans
      (canonical_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
        rows left right hr hl hri hrows hleft hright a b)

end CanonicalQuadraticSieve

namespace FiniteSieveRestriction
open FiniteSieveOperator

theorem squared_norm_row_partition {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n ℂ) (P : m → Prop) [DecidablePred P] :
    ‖operator A‖ ^ 2 ≤
      ‖operator (fun (i : {i : m // P i}) j => A i.val j)‖ ^ 2 +
      ‖operator (fun (i : {i : m // ¬ P i}) j => A i.val j)‖ ^ 2 := by
  apply squared_norm_le_of_energy _ _ (by positivity)
  intro a
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i => ‖∑ j, A i j * a j‖ ^ 2)]
  have h₁ := energy_bound (fun (i : {i : m // P i}) j => A i.val j) a
  have h₂ := energy_bound (fun (i : {i : m // ¬ P i}) j => A i.val j) a
  exact (add_le_add h₁ h₂).trans_eq (by ring)
end FiniteSieveRestriction

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel FiniteSieveOperator

def Supported (I : Ideal O) : Prop :=
  I ≠ 0 ∧ ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2

def fullRange (M : ℝ) : Finset (Ideal O) := (idealsUpTo ⌊M⌋₊).filter Supported

theorem mem_fullRange {M : ℝ} {I : Ideal O} :
    I ∈ fullRange M ↔ Supported I ∧ (Ideal.absNorm I : ℝ) ≤ M := by
  rw [fullRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hM : 0 ≤ M := by
      by_contra hn
      have hz : ⌊M⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hM)
  · rintro ⟨ha, hN⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => ha.1 (Ideal.absNorm_eq_zero_iff.mp h)),
      Nat.le_floor hN⟩, ha⟩

theorem admissible_supported {I : Ideal O} (hI : Admissible I) : Supported I :=
  ⟨hI.1, hI.2.2⟩

theorem squarefreePart_eq_self {I : Ideal O} (hI : Squarefree I) : squarefreePart I = I := by
  have h := (squarePart_mul_squarefree (show (1 : Ideal O) ≠ 0 from one_ne_zero) hI).2
  simpa only [one_pow, one_mul] using h

def highKernelRange (M K : ℝ) : Finset (Ideal O) :=
  (fullRange M).filter (fun I => K < (Ideal.absNorm (squarefreePart I) : ℝ))

theorem mem_highKernelRange {M K : ℝ} {I : Ideal O} :
    I ∈ highKernelRange M K ↔
      Supported I ∧ (Ideal.absNorm I : ℝ) ≤ M ∧ K < (Ideal.absNorm (squarefreePart I) : ℝ) := by
  simp only [highKernelRange, Finset.mem_filter, mem_fullRange, and_assoc]

def highKernelMatrix (M N K : ℝ) : Matrix (highKernelRange M K) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)

def highKernelNorm (M N K : ℝ) : ℝ := ‖operator (highKernelMatrix M N K)‖ ^ 2

theorem highKernelNorm_nonneg (M N K : ℝ) : 0 ≤ highKernelNorm M N K := sq_nonneg _

theorem sieveNorm_le_low_add_high (M N K : ℝ) :
    sieveNorm M N ≤ sieveNorm K N + highKernelNorm M N K := by
  let P : idealRange M → Prop := fun I => (Ideal.absNorm I.val : ℝ) ≤ K
  let lo := {I : idealRange M // P I}
  let hi := {I : idealRange M // ¬ P I}
  have hlo : ‖operator (fun (I : lo) (J : idealRange N) => matrix M N I.val J)‖ ^ 2 ≤
      sieveNorm K N := by
    apply family_squared_norm_le (fun I : lo => I.val.val) (fun J : idealRange N => J.val)
    · intro I J h
      apply Subtype.ext
      exact Subtype.ext h
    · exact Subtype.val_injective
    · intro I
      exact ⟨(mem_idealRange.mp I.val.property).1, I.property⟩
    · intro J
      exact mem_idealRange.mp J.property
  let toHigh : hi → highKernelRange M K := fun I => ⟨I.val.val, by
    apply mem_highKernelRange.mpr
    have hI := mem_idealRange.mp I.val.property
    refine ⟨admissible_supported hI.1, hI.2, ?_⟩
    rw [squarefreePart_eq_self hI.1.2.1]
    exact lt_of_not_ge I.property⟩
  have hhighinj : Function.Injective toHigh := by
    intro I J h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : highKernelRange M K => I.val) h
  have hhi := FiniteSieveRestriction.submatrix_norm_le toHigh hhighinj
    (fun J : idealRange N => J) Function.injective_id (highKernelMatrix M N K)
  have hhisq : ‖operator (fun (I : hi) (J : idealRange N) => matrix M N I.val J)‖ ^ 2 ≤
      highKernelNorm M N K := pow_le_pow_left₀ (norm_nonneg _) hhi 2
  exact (FiniteSieveRestriction.squared_norm_row_partition (matrix M N) P).trans (add_le_add hlo hhisq)

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
namespace QuadraticKernelTransfer
open FourierBridge EisensteinSchwartzPoisson

theorem sum_norm_integral_bound {ι : Type*} [Fintype ι]
    (b : ℝ → ℂ) (φ : ι → ℝ → ℂ) (H : ℝ)
    (hint : ∀ i, Integrable (fun t => b t * φ i t))
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀ t, (∑ i, ‖φ i t‖) ≤ H) :
    (∑ i, ‖∫ t, b t * φ i t‖) ≤ H * ∫ t, ‖b t‖ := by
  calc
    _ ≤ ∑ i, ∫ t, ‖b t * φ i t‖ := Finset.sum_le_sum (fun i _ => norm_integral_le_integral_norm _)
    _ = ∫ t, ∑ i, ‖b t * φ i t‖ := (integral_finsetSum _ (fun i _ => (hint i).norm)).symm
    _ ≤ ∫ t, H * ‖b t‖ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => by positivity)) (hb.const_mul H)
      filter_upwards [] with t
      simp only [norm_mul, ← Finset.mul_sum]
      calc
        _ ≤ ‖b t‖ * H := mul_le_mul_of_nonneg_left (hφ t) (norm_nonneg _)
        _ = _ := mul_comm _ _
    _ = _ := integral_const_mul _ _

theorem radial_two_variable_window (W : 𝓢(ℝ, ℂ))
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ x y : ℝ, |x| ≤ L₁ → |y| ≤ L₂ →
        paperRadialFourier W (R * Real.exp (x+y)) =
          ∫ t, logPhase t x * logPhase t y * b t) ∧
      (1 + R) ^ A * (∫ t, ‖b t‖) ≤ C := by
  let V₁ : ℝ → ℂ := fun x => if |x| ≤ L₁ then 1 else 0
  let V₂ : ℝ → ℂ := fun x => if |x| ≤ L₂ then 1 else 0
  let V : Bool → ℝ → ℂ := fun j => if j then V₂ else V₁
  let lengthScale : Bool → ℝ := fun j => if j then L₂ else L₁
  have hL : ∀ j, 0 ≤ lengthScale j := by intro j; cases j <;> assumption
  have hV : ∀ j x, V j x ≠ 0 → |x| ≤ lengthScale j := by
    intro j x h
    cases j
    · change |x| ≤ L₁
      change (if |x| ≤ L₁ then (1 : ℂ) else 0) ≠ 0 at h
      by_contra hx
      exact h (by simp [hx])
    · change |x| ≤ L₂
      change (if |x| ≤ L₂ then (1 : ℂ) else 0) ≠ 0 at h
      by_contra hx
      exact h (by simp [hx])
  obtain ⟨C, hC, hs⟩ := paperRadialFourier_log_separation_envelope W V (fun _ => 1) lengthScale hL hV A 0
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, _, hmass, _⟩ := hs R hR
  refine ⟨b, ?_, ?_⟩
  · intro x y hx hy
    have h := hb (fun j => if j then y else x)
    simpa only [V, V₁, V₂, lengthScale, Fintype.prod_bool, Fintype.sum_bool,
      Bool.false_eq_true, ↓reduceIte, ite_eq_left hx, ite_eq_left hy, one_mul, mul_one,
      add_comm, mul_comm, mul_left_comm, mul_assoc] using h
  · simpa only [pow_zero, one_mul] using hmass

theorem radial_phase_integrable (b : 𝓢(ℝ, ℂ)) (c : ℂ) (x y : ℝ) :
    Integrable (fun t => b t * (logPhase t x * (c * logPhase t y))) := by
  apply (b.integrable.norm.mul_const ‖c‖).mono'
  · have hx := logPhase_continuous_left x
    have hy := logPhase_continuous_left y
    exact (by fun_prop : Continuous (fun t => b t * (logPhase t x * (c * logPhase t y)))).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [norm_mul, logPhase_norm, one_mul, mul_one]
    exact le_rfl

theorem radial_matrix_kernel_transfer (W : 𝓢(ℝ, ℂ))
    (L₁ L₂ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n : Type*} [Fintype m] [Fintype n]
        (c : m → n → ℂ) (x : m → ℝ) (y : n → ℝ) (H : ℝ),
        0 ≤ H → (∀ i, |x i| ≤ L₁) → (∀ j, |y j| ≤ L₂) →
        (∀ t, (∑ i, ‖∑ j, c i j * logPhase t (y j)‖) ≤ H) →
        (1 + R) ^ A * (∑ i, ‖∑ j, c i j *
          paperRadialFourier W (R * Real.exp (x i + y j))‖) ≤ C * H := by
  obtain ⟨C, hC, hs⟩ := radial_two_variable_window W L₁ L₂ hL₁ hL₂ A
  refine ⟨C, hC, ?_⟩
  intro R hR m n _ _ c x y H hH hx hy hphase
  obtain ⟨b, hb, hmass⟩ := hs R hR
  let φ : m → ℝ → ℂ := fun i t => logPhase t (x i) * ∑ j, c i j * logPhase t (y j)
  have hint (i : m) : Integrable (fun t => b t * φ i t) := by
    have h := integrable_finsetSum (Finset.univ : Finset n)
      (fun j _ => radial_phase_integrable b (c i j) (x i) (y j))
    simpa only [φ, Finset.mul_sum] using h
  have hid (i : m) : (∑ j, c i j * paperRadialFourier W (R * Real.exp (x i + y j))) =
      ∫ t, b t * φ i t := by
    rw [show (fun t => b t * φ i t) = fun t =>
      ∑ j, b t * (logPhase t (x i) * (c i j * logPhase t (y j))) by
        funext t; simp only [φ, Finset.mul_sum]]
    rw [integral_finsetSum _ (fun j _ => radial_phase_integrable b (c i j) (x i) (y j))]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb _ _ (hx i) (hy j), ← integral_const_mul]
    congr 1
    funext t
    ring
  have hp (t : ℝ) : (∑ i, ‖φ i t‖) ≤ H := by
    simpa only [φ, norm_mul, logPhase_norm, one_mul] using hphase t
  have hi := sum_norm_integral_bound b φ H hint b.integrable.norm hp
  simp only [← hid] at hi
  calc
    _ ≤ (1 + R) ^ A * (H * ∫ t, ‖b t‖) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ = H * ((1 + R) ^ A * ∫ t, ‖b t‖) := by ring
    _ ≤ H * C := mul_le_mul_of_nonneg_left hmass hH
    _ = _ := mul_comm _ _

end QuadraticKernelTransfer

namespace CanonicalQuadraticSieve
open FourierBridge EisensteinSchwartzPoisson QuadraticKernelTransfer
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks

section
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def quotientTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (quotientMatrix D rows left i j * (if D ∣ left j then a j else 0)) *
      (quotientMatrix E rows right i k * (if E ∣ right k then b k else 0)) else 0

def divisorBlockCost (ε : ℝ) (hε : 0 < ε) (D₁ D₂ M N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  256 ^ 2 * D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
    (supportConstant ε hε * divisorConstant ε hε) ^ 2 * (N ^ ε) ^ 4 *
    (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2)

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem quotientTerm_phase (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p)
    (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    quotientTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k =
    quotientTerm rows left right a b D E i j k * logPhase t (y j + z k) := by
  unfold quotientTerm
  rw [logPhase_add]
  by_cases hc : IsCoprime (left j) (right k) <;>
    by_cases hD : D ∣ left j <;> by_cases hE : E ∣ right k <;>
      simp only [hc, hD, hE, ↓reduceIte, mul_zero, zero_mul, star_zero, star_mul, star_star] ; ring

theorem canonical_divisor_block_phase_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    (∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, quotientTerm rows left right a b D E i j k * logPhase t (y j + z k)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  have hb := canonical_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright
    (fun j => a j * star (logPhase t (y j))) (fun k => b k * logPhase t (z k))
  simp only [norm_mul, norm_star, logPhase_norm, mul_one] at hb
  change (∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k,
    quotientTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k‖) ^ 2 ≤
    divisorBlockCost ε hε D₁ D₂ M N a b at hb
  simp only [quotientTerm_phase] at hb
  have hcost : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := (sq_nonneg _).trans hb
  have hs := Real.sq_sqrt hcost
  have hp := Real.sqrt_nonneg (divisorBlockCost ε hε D₁ D₂ M N a b)
  have hsum : 0 ≤ ∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, quotientTerm rows left right a b D E i j k * logPhase t (y j + z k)‖ := by positivity
  nlinarith
end

theorem canonical_radial_divisor_block_bound
    (W : 𝓢(ℝ, ℂ)) (L₁ L₂ L₃ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ M N : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hN : 1 ≤ N)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (x : S → T → m → ℝ) (y : n → ℝ) (z : p → ℝ),
        (∀ D E i, |x D E i| ≤ L₁) → (∀ j, |y j| ≤ L₂) → (∀ k, |z k| ≤ L₃) →
        (1 + R) ^ A * (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
          quotientTerm rows left right a b D.val E.val i j k *
            paperRadialFourier W (R * Real.exp (x D E i + (y j + z k)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  obtain ⟨C, hC, hker⟩ := radial_matrix_kernel_transfer W L₁ (L₂ + L₃) hL₁ (add_nonneg hL₂ hL₃) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n p _ _ _ _ _ _ ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright a b x y z hx hy hz
  let c : (S × T × m) → (n × p) → ℂ := fun i j =>
    quotientTerm rows left right a b i.1.val i.2.1.val i.2.2 j.1 j.2
  have hp (t : ℝ) : (∑ i : S × T × m, ‖∑ j : n × p, c i j * logPhase t (y j.1 + z j.2)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
    have hb := canonical_divisor_block_phase_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
      rows left right hr hl hri hrows hleft hright a b y z t
    simp only [c, Fintype.sum_prod_type]
    let v : Ideal O → Ideal O → ℝ := fun D E => ∑ i,
      ‖∑ j, ∑ k, quotientTerm rows left right a b D E i j k * logPhase t (y j + z k)‖
    change (∑ D : S, ∑ E : T, v D.val E.val) ≤ _
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, v D E.val)]
    have he (D : Ideal O) := Finset.sum_coe_sort T (v D)
    simp_rw [he]
    exact hb
  have hb := hker R hR c (fun i => x i.1 i.2.1 i.2.2) (fun j => y j.1 + z j.2)
    (Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b)) (Real.sqrt_nonneg _)
    (fun i => hx i.1 i.2.1 i.2.2)
    (fun j => (abs_add_le _ _).trans (add_le_add (hy j.1) (hz j.2))) hp
  simpa only [c, Fintype.sum_prod_type] using hb

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open FourierBridge EisensteinSchwartzPoisson QuadraticKernelTransfer
open IdealCoprimeSieveOperator DivisorBlockCauchy IdealDivisorBilinearBlocks

section
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (quadraticRow (left j) (CompletedGauss.primaryGenerator (rows i)) * (if D ∣ left j then a j else 0)) *
      (quadraticRow (right k) (CompletedGauss.primaryGenerator (rows i)) * (if E ∣ right k then b k else 0)) else 0

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTerm_phase (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p)
    (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    originalTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k =
    originalTerm rows left right a b D E i j k * logPhase t (y j + z k) := by
  unfold originalTerm
  rw [logPhase_add]
  by_cases hc : IsCoprime (left j) (right k) <;>
    by_cases hD : D ∣ left j <;> by_cases hE : E ∣ right k <;>
      simp only [hc, hD, hE, ↓reduceIte, mul_zero, zero_mul, star_zero, star_mul, star_star] ; ring

theorem canonical_original_divisor_block_phase_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    (∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * logPhase t (y j + z k)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  have hb := canonical_original_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright
    (fun j => a j * star (logPhase t (y j))) (fun k => b k * logPhase t (z k))
  simp only [norm_mul, norm_star, logPhase_norm, mul_one] at hb
  change (∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k,
    originalTerm rows left right (fun j => a j * star (logPhase t (y j)))
      (fun k => b k * logPhase t (z k)) D E i j k‖) ^ 2 ≤
    divisorBlockCost ε hε D₁ D₂ M N a b at hb
  simp only [originalTerm_phase] at hb
  have hcost : 0 ≤ divisorBlockCost ε hε D₁ D₂ M N a b := (sq_nonneg _).trans hb
  have hs := Real.sq_sqrt hcost
  have hp := Real.sqrt_nonneg (divisorBlockCost ε hε D₁ D₂ M N a b)
  have hsum : 0 ≤ ∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * logPhase t (y j + z k)‖ := by positivity
  nlinarith
end

theorem canonical_original_radial_divisor_block_bound
    (W : 𝓢(ℝ, ℂ)) (L₁ L₂ L₃ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ M N : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hN : 1 ≤ N)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
        (_hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (x : S → T → m → ℝ) (y : n → ℝ) (z : p → ℝ),
        (∀ D E i, |x D E i| ≤ L₁) → (∀ j, |y j| ≤ L₂) → (∀ k, |z k| ≤ L₃) →
        (1 + R) ^ A * (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
          originalTerm rows left right a b D.val E.val i j k *
            paperRadialFourier W (R * Real.exp (x D E i + (y j + z k)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
  obtain ⟨C, hC, hker⟩ := radial_matrix_kernel_transfer W L₁ (L₂ + L₃) hL₁ (add_nonneg hL₂ hL₃) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n p _ _ _ _ _ _ ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright a b x y z hx hy hz
  let c : (S × T × m) → (n × p) → ℂ := fun i j =>
    originalTerm rows left right a b i.1.val i.2.1.val i.2.2 j.1 j.2
  have hp (t : ℝ) : (∑ i : S × T × m, ‖∑ j : n × p, c i j * logPhase t (y j.1 + z j.2)‖) ≤
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b) := by
    have hb := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
      rows left right hr hl hri hrows hleft hright a b y z t
    simp only [c, Fintype.sum_prod_type]
    let v : Ideal O → Ideal O → ℝ := fun D E => ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * logPhase t (y j + z k)‖
    change (∑ D : S, ∑ E : T, v D.val E.val) ≤ _
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, v D E.val)]
    have he (D : Ideal O) := Finset.sum_coe_sort T (v D)
    simp_rw [he]
    exact hb
  have hb := hker R hR c (fun i => x i.1 i.2.1 i.2.2) (fun j => y j.1 + z j.2)
    (Real.sqrt (divisorBlockCost ε hε D₁ D₂ M N a b)) (Real.sqrt_nonneg _)
    (fun i => hx i.1 i.2.1 i.2.2)
    (fun j => (abs_add_le _ _).trans (add_le_add (hy j.1) (hz j.2))) hp
  simpa only [c, Fintype.sum_prod_type] using hb

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0112

/-! Original module: OAI.NumberTheory.DirichletL.Reciprocity.CubicJacobi
Source SHA256: 7fe0e2350ea2e264ce57b84fa1f15549978a9501f0d1d03a7ca1a13d41edc7fe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0113


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

open scoped BigOperators Classical

namespace CubicJacobiGlobal
abbrev O := ActualEisensteinCubic.O
abbrev K := ActualEisensteinCubic.K
open ActualEisensteinCubic CompletedGauss

def primeValue (P : Ideal O) (x : O) : O :=
  if h : P.IsMaximal ∧ lambda ∉ P then
    letI : P.IsMaximal := h.1
    cubicChar P h.2 (Ideal.Quotient.mk P x)
  else 0

@[simp] theorem primeValue_eq (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O) :
    primeValue P x = cubicChar P hgood (Ideal.Quotient.mk P x) := by
  simp only [primeValue, dite_eq_left (show P.IsMaximal ∧ lambda ∉ P from
    ⟨inferInstance, hgood⟩)]

def idealSymbol (I : Ideal O) (x : O) : O :=
  if I = 0 then 0 else
    ((UniqueFactorizationMonoid.normalizedFactors I).map (fun P => primeValue P x)).prod

@[simp] theorem idealSymbol_zero (x : O) : idealSymbol 0 x = 0 := by simp [idealSymbol]
@[simp] theorem idealSymbol_bot (x : O) : idealSymbol ⊥ x = 0 := idealSymbol_zero x
@[simp] theorem idealSymbol_one (x : O) : idealSymbol 1 x = 1 := by
  rw [idealSymbol, ite_eq_right one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl
@[simp] theorem idealSymbol_top (x : O) : idealSymbol ⊤ x = 1 := by
  simpa only [Ideal.one_eq_top] using idealSymbol_one x

theorem idealSymbol_mul (I J : Ideal O) (x : O) :
    idealSymbol (I * J) x = idealSymbol I x * idealSymbol J x := by
  classical
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  simp only [idealSymbol, ite_eq_right hI, ite_eq_right hJ, ite_eq_right (mul_ne_zero hI hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add,
    Multiset.prod_add]

def symbol (x y : O) : O := idealSymbol (Ideal.span {y}) x

@[simp] theorem symbol_one (x : O) : symbol x 1 = 1 := by simp [symbol]
@[simp] theorem symbol_zero (x : O) : symbol x 0 = 0 := by simp [symbol]

theorem symbol_mul_denominator (x y z : O) :
    symbol x (y * z) = symbol x y * symbol x z := by
  rw [symbol, ← Ideal.span_singleton_mul_span_singleton, idealSymbol_mul]
  rfl

theorem idealSymbol_prime (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (x : O) :
    idealSymbol P x = cubicChar P hgood (Ideal.Quotient.mk P x) := by
  have hP0 : P ≠ 0 := NeZero.ne _
  have hp : Prime P := Ideal.prime_of_isPrime hP0 (inferInstance : P.IsPrime)
  rw [idealSymbol, ite_eq_right hP0,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible]
  simpa using primeValue_eq P hgood x

private theorem factor_good (I : Ideal O) (hI : primaryGenerator I ≠ 0)
    (P : Ideal O) (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    P.IsMaximal ∧ lambda ∉ P := by
  exact ⟨(primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)).1,
    (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)).2.1⟩

theorem idealSymbol_map_mul (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x y : O) :
    idealSymbol I (x * y) = idealSymbol I x * idealSymbol I y := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  simp only [idealSymbol, ite_eq_right hI0]
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hg := factor_good I hI P hP
  let : P.IsMaximal := hg.1
  simp only [primeValue_eq P hg.2, map_mul]

theorem idealSymbol_map_one (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    idealSymbol I 1 = 1 := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  rw [idealSymbol, ite_eq_right hI0]
  apply Multiset.prod_eq_one
  intro y hy
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hy
  have hg := factor_good I hI P hP
  let : P.IsMaximal := hg.1
  simp only [primeValue_eq P hg.2, map_one]

theorem idealSymbol_map_multiset_prod (I : Ideal O) (hI : primaryGenerator I ≠ 0)
    (s : Multiset O) :
    idealSymbol I s.prod = (s.map (idealSymbol I)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [idealSymbol_map_one I hI]
  | @cons a s ih => simp [idealSymbol_map_mul I hI, ih]

theorem symbol_prime (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) (x : O) :
    symbol x p = primeValue (Ideal.span {p}) x := by
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  rw [symbol, idealSymbol_prime _ hg, primeValue_eq _ hg]

theorem idealSymbol_reciprocity (I J : Ideal O)
    (hI : primaryGenerator I ≠ 0) (hJ : primaryGenerator J ≠ 0) :
    idealSymbol I (primaryGenerator J) = idealSymbol J (primaryGenerator I) := by
  classical
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  have hJ0 := primaryGenerator_ne_zero_ideal J hJ
  rw [primaryGenerator, ite_eq_right hJ0, idealSymbol_map_multiset_prod I hI,
    primaryGenerator, ite_eq_right hI0, idealSymbol_map_multiset_prod J hJ]
  simp only [Multiset.map_map, Function.comp_def, idealSymbol, ite_eq_right hI0, ite_eq_right hJ0]
  rw [Multiset.prod_map_prod_map]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro Q hQ
  have hgP := factor_good I hI P hP
  have hgQ := factor_good J hJ Q hQ
  let : P.IsMaximal := hgP.1
  let : Q.IsMaximal := hgQ.1
  have hp := (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)).2.2
  have hq := (primaryPrime_spec Q (primaryPrime_factor_ne_zero J Q hJ hQ)).2.2
  rw [primeValue_eq P hgP.2, primeValue_eq Q hgQ.2]
  exact cubic_reciprocity_primary P Q hgP.2 hgQ.2
    (primaryPrime P) (primaryPrime Q) hp.1.symm hq.1.symm hp.2 hq.2

theorem symbol_reciprocity (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hap : lambda ^ 2 ∣ a - 1) (hbp : lambda ^ 2 ∣ b - 1) :
    symbol a b = symbol b a := by
  have haG := primaryGenerator_span a ha hap
  have hbG := primaryGenerator_span b hb hbp
  have h := idealSymbol_reciprocity (Ideal.span {b}) (Ideal.span {a})
    (by rwa [hbG]) (by rwa [haG])
  simpa only [symbol, haG, hbG] using h

theorem idealSymbol_congr (I : Ideal O) {x y : O} (hxy : x - y ∈ I) :
    idealSymbol I x = idealSymbol I y := by
  classical
  by_cases hI : I = 0
  · simp only [hI, idealSymbol_zero]
  simp only [idealSymbol, ite_eq_right hI]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hle := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
  by_cases hg : P.IsMaximal ∧ lambda ∉ P
  · let : P.IsMaximal := hg.1
    rw [primeValue_eq P hg.2, primeValue_eq P hg.2,
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hle hxy)]
  · simp only [primeValue, dite_eq_right hg]

theorem symbol_congr {x y d : O} (hxy : d ∣ x - y) :
    symbol x d = symbol y d :=
  idealSymbol_congr _ (Ideal.mem_span_singleton.mpr hxy)

end CubicJacobiGlobal

namespace CubicRamified

abbrev O := ActualEisensteinCubic.O
abbrev K := ActualEisensteinCubic.K
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

lemma lambda_def : lambda = omega - 1 := rfl

theorem cubicValue_cube (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (x : O) (hx : x ∉ P) :
    (cubicChar P hg (Ideal.Quotient.mk P x)) ^ 3 = 1 := by
  rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
  exact MulChar.one_apply (isUnit_iff_ne_zero.mpr
    (Ideal.Quotient.eq_zero_iff_mem.not.mpr hx))

theorem cubicValue_ne_zero (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (x : O) (hx : x ∉ P) :
    cubicChar P hg (Ideal.Quotient.mk P x) ≠ 0 := by
  have h := cubicValue_cube P hg x hx
  intro hz
  rw [hz, zero_pow (by decide)] at h
  exact zero_ne_one h

theorem ramified_comparison
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hqP : q ∉ P) (_hpQ : p ∉ Q)
    (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r) :
    (cubicChar P hgP (Ideal.Quotient.mk P lambda)) ^ 2 *
        cubicChar P hgP (Ideal.Quotient.mk P u) =
      (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) := by
  have hp0 : p ≠ 0 := by
    intro hz
    apply (NeZero.ne P)
    simp [hP, hz]
  have hq0 : q ≠ 0 := by
    intro hz
    apply (NeZero.ne Q)
    simp [hQ, hz]
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hrP : r ∉ P := by
    intro hrP
    have hd : p - q ∈ P := by rw [hfactor]; exact P.mul_mem_left _ hrP
    have hmem := P.sub_mem hpP hd
    exact hqP (by convert hmem using 1 ; ring)
  have hrr : cubicChar P hgP (Ideal.Quotient.mk P r) =
      cubicChar Q hgQ (Ideal.Quotient.mk Q r) := by
    have heq : symbol p r = symbol q r := symbol_congr
      (by rw [hfactor]; exact dvd_mul_left r _)
    have h := (symbol_reciprocity r p hr0 hp0 hr hp).trans
      (heq.trans (symbol_reciprocity q r hq0 hr0 hq hr))
    simpa only [symbol, ← hP, ← hQ, idealSymbol_prime _ hgP,
      idealSymbol_prime _ hgQ] using h
  have heq : cubicChar P hgP (Ideal.Quotient.mk P (p - q)) =
      cubicChar Q hgQ (Ideal.Quotient.mk Q (p - q)) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hpP, zero_sub,
      neg_eq_neg_one_mul, map_mul, A3_cubicChar_neg_one P hgP, one_mul,
      map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hqQ, sub_zero]
    exact cubic_reciprocity_primary P Q hgP hgQ p q hP hQ hp hq
  simp only [hfactor, map_mul, map_pow] at heq
  rw [← hrr] at heq
  exact mul_right_cancel₀ (cubicValue_ne_zero P hgP r hrP) heq

def sevenPrime : O := 1 + 3 * omega
def sevenIdeal : Ideal O := Ideal.span {sevenPrime}

theorem sevenPrime_norm : ShortDraftLatticeCount.qNat sevenPrime = 7 := by
  change ShortDraftLatticeCount.qNat (ActualEisensteinCoordinates.eval 1 3) = 7
  unfold ShortDraftLatticeCount.qNat
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

theorem sevenPrime_ne_zero : sevenPrime ≠ 0 := by
  intro hz
  change ActualEisensteinCoordinates.eval 1 3 = 0 at hz
  have hh : ActualEisensteinCoordinates.eval 1 3 =
      ActualEisensteinCoordinates.eval 0 0 :=
    hz.trans (by simp [ActualEisensteinCoordinates.eval])
  have h := (ActualEisensteinCoordinates.unique_coordinates hh).1
  norm_num at h

theorem sevenIdeal_norm : Ideal.absNorm sevenIdeal = 7 := by
  rw [sevenIdeal, ← qNat_eq_absNorm_span, sevenPrime_norm]

instance sevenIdeal_isMaximal : sevenIdeal.IsMaximal := by
  have hp : sevenIdeal.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by
    rw [sevenIdeal_norm, Nat.irreducible_iff_nat_prime]
    decide)
  exact hp.isMaximal (Ideal.span_singleton_eq_bot.not.mpr sevenPrime_ne_zero)

theorem sevenPrime_primary : lambda ^ 2 ∣ sevenPrime - 1 := by
  refine ⟨-1, ?_⟩
  rw [lambda_def]
  dsimp [sevenPrime]
  linear_combination omega_sq_for_norm

theorem sevenIdeal_good : lambda ∉ sevenIdeal :=
  primary_maximal_divisor_good sevenPrime sevenPrime_primary sevenIdeal
    (Ideal.subset_span (by simp []))

theorem twoIdeal_card : Nat.card (O ⧸ cubicTwoIdeal) = 4 := by
  change Ideal.absNorm cubicTwoIdeal = 4
  rw [cubicTwoIdeal, ← qNat_eq_absNorm_span]
  rw [show (-2 : O) = ActualEisensteinCoordinates.eval (-2) 0 by
    simp [ActualEisensteinCoordinates.eval]]
  unfold ShortDraftLatticeCount.qNat
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

theorem sevenIdeal_card : Nat.card (O ⧸ sevenIdeal) = 7 := sevenIdeal_norm

theorem cubicValue_lambda_two :
    cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal lambda) =
      omega ^ 2 := by
  have heq : Ideal.Quotient.mk cubicTwoIdeal lambda =
      Ideal.Quotient.mk cubicTwoIdeal (omega ^ 2) := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    rw [cubicTwoIdeal, Ideal.mem_span_singleton]
    refine ⟨-omega, ?_⟩
    rw [lambda_def]
    linear_combination -omega_sq_for_norm
  rw [heq, map_pow, map_pow, cubicChar_omega, twoIdeal_card]
  norm_num

theorem cubicValue_lambda_seven :
    cubicChar sevenIdeal sevenIdeal_good (Ideal.Quotient.mk sevenIdeal lambda) = 1 := by
  apply cubic_roots_reduce_injective sevenIdeal sevenIdeal_good
    (cubicValue_cube sevenIdeal sevenIdeal_good lambda sevenIdeal_good) (by simp)
  rw [cubicChar_reduce, sevenIdeal_card]
  norm_num only [Nat.reduceSub, Nat.reduceDiv]
  rw [← map_pow]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [sevenIdeal, Ideal.mem_span_singleton]
  refine ⟨-1, ?_⟩
  rw [lambda_def]
  dsimp [sevenPrime]
  linear_combination omega_sq_for_norm

open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

def primaryCoord (A B : ℤ) : O := ActualEisensteinCoordinates.eval (1 + 3 * A) (3 * B)

theorem primaryCoord_eq (A B : ℤ) :
    primaryCoord A B = 1 + 3 * (A : O) + 3 * (B : O) * omega := by
  simp only [primaryCoord, ActualEisensteinCoordinates.eval]
  push_cast
  rfl

theorem primaryCoord_primary (A B : ℤ) : lambda ^ 2 ∣ primaryCoord A B - 1 := by
  rw [primaryCoord_eq]
  apply lambda_sq_dvd_three.trans
  exact ⟨(A : O) + (B : O) * omega, by ring⟩

theorem primaryCoord_ne_zero (A B : ℤ) : primaryCoord A B ≠ 0 := by
  intro hz
  have hcoord : ActualEisensteinCoordinates.eval (1 + 3 * A) (3 * B) =
      ActualEisensteinCoordinates.eval 0 0 := by
    exact hz.trans (by simp [ActualEisensteinCoordinates.eval])
  have h := (ActualEisensteinCoordinates.unique_coordinates hcoord).1
  omega

lemma primary_card_exponent (N : ℕ) (A B : ℤ) (hN : 1 < N)
    (hn : (N : ℤ) = 1 + 9*(A^2-A*B+B^2)+3*(2*A-B)) :
    ((N-1)/3)%3 = ((2*A-B)%3).toNat %3 := by
  have hsub : ((N-1 : ℕ) : ℤ) = (N : ℤ)-1 := by omega
  have hdiv : (((N-1)/3 : ℕ) : ℤ) = 3*(A^2-A*B+B^2)+(2*A-B) := by
    rw [Int.natCast_ediv, hsub]
    have hh : (N : ℤ)-1 = 3*(3*(A^2-A*B+B^2)+(2*A-B)) := by omega
    rw [hh]
    omega
  have hrem : (((2*A-B)%3).toNat : ℤ) = (2*A-B)%3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  omega

theorem cubicValue_omega_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ) (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P omega) =
      omega ^ ((2 * A - B) % 3).toNat := by
  have hn : (Nat.card (O ⧸ P) : ℤ) =
      (1 + 3 * A)^2 - (1 + 3 * A)*(3 * B) + (3 * B)^2 := by
    change (Ideal.absNorm P : ℤ) = _
    rw [hP, ← qNat_eq_absNorm_span]
    unfold ShortDraftLatticeCount.qNat
    rw [Int.toNat_of_nonneg (ShortDraftLatticeCount.qO_nonneg _)]
    rw [primaryCoord, ShortDraftLatticeCount.coords_eval]
    rfl
  have hn' : (Nat.card (O ⧸ P) : ℤ) =
      1 + 9*(A^2 - A*B + B^2) + 3*(2*A-B) := by nlinarith [hn]
  rw [cubicChar_omega]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : 1 < Nat.card (O ⧸ P) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  exact primary_card_exponent (Nat.card (O ⧸ P)) A B hcard hn'

theorem ramified_comparison_of_factor
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hu : u ≠ 0) (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r) :
    (cubicChar P hgP (Ideal.Quotient.mk P lambda)) ^ 2 *
        cubicChar P hgP (Ideal.Quotient.mk P u) =
      (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) := by
  have hlam : lambda ≠ 0 := fun hz => hgP (hz ▸ P.zero_mem)
  have hne : P ≠ Q := by
    intro heq
    have hpq : p = q := primary_associated_eq p q
      (Ideal.span_singleton_eq_span_singleton.mp (hP.symm.trans (heq.trans hQ))) hp hq
    have hz : lambda ^ 2 * u * r = 0 := by rw [← hfactor, hpq, sub_self]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hlam) hu) hr0 hz
  exact ramified_comparison P Q hgP hgQ p q u r hP hQ hp hq
    (prime_generator_not_mem_of_ne P Q hne q hQ)
    (prime_generator_not_mem_of_ne Q P hne.symm p hP) hr0 hr hfactor

open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

lemma omega_ne_zero : omega ≠ 0 := omega_primitive.ne_zero (by decide)
lemma omega_isUnit : IsUnit omega := omega_primitive.isUnit (by decide)
lemma omega_four : omega ^ 4 = omega := by
  calc
    _ = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_primitive.pow_eq_one, one_mul]
lemma omega_five : omega ^ 5 = omega ^ 2 := by
  calc
    _ = omega ^ 3 * omega ^ 2 := by ring
    _ = _ := by rw [omega_primitive.pow_eq_one, one_mul]

lemma cubicValue_neg (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) (x : O) :
    cubicChar P hg (Ideal.Quotient.mk P (-x)) =
      cubicChar P hg (Ideal.Quotient.mk P x) := by
  rw [map_neg, neg_eq_neg_one_mul, map_mul, A3_cubicChar_neg_one, one_mul]

lemma cubicValue_omega_two :
    cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal omega) =
      omega := by rw [cubicChar_omega, twoIdeal_card] ; norm_num
lemma cubicValue_omega_seven :
    cubicChar sevenIdeal sevenIdeal_good (Ideal.Quotient.mk sevenIdeal omega) =
      omega ^ 2 := by rw [cubicChar_omega, sevenIdeal_card]

lemma eq_of_cube_one_of_sq_eq (z w : O) (hz : z ^ 3 = 1)
    (hw : w ^ 3 = 1) (hsq : z ^ 2 = w ^ 2) : z = w := by
  have hw0 : w ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at hw; exact zero_ne_one hw
  apply mul_right_cancel₀ (pow_ne_zero 2 hw0)
  calc
    z * w ^ 2 = z ^ 3 := by rw [← hsq]; ring
    _ = 1 := hz
    _ = w * w ^ 2 := by rw [← hw]; ring

lemma supplement_of_factor
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hu : IsUnit u) (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r)
    (j : ℕ)
    (hscalar : (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) =
      (omega ^ j)^2 * cubicChar P hgP (Ideal.Quotient.mk P u)) :
    cubicChar P hgP (Ideal.Quotient.mk P lambda) = omega ^ j := by
  apply eq_of_cube_one_of_sq_eq
  · exact cubicValue_cube P hgP lambda hgP
  · rw [← pow_mul, Nat.mul_comm j, pow_mul, omega_primitive.pow_eq_one, one_pow]
  · apply mul_right_cancel₀ (cubicValue_ne_zero P hgP u (Ideal.notMem_of_isUnit P hu))
    exact (ramified_comparison_of_factor P Q hgP hgQ p q u r hP hQ hp hq
      hu.ne_zero hr0 hr hfactor).trans hscalar

lemma omega_six : omega ^ 6 = 1 := by
  calc
    _ = omega ^ 3 * omega ^ 3 := by ring
    _ = 1 := by rw [omega_primitive.pow_eq_one, one_mul]

lemma omega_seven : omega ^ 7 = omega := by
  calc
    _ = omega ^ 3 * omega ^ 4 := by ring
    _ = omega := by rw [omega_primitive.pow_eq_one, one_mul] ; exact omega_four

lemma omega_eight : omega ^ 8 = omega ^ 2 := by
  calc
    _ = omega ^ 3 * omega ^ 5 := by ring
    _ = omega ^ 2 := by rw [omega_primitive.pow_eq_one, one_mul] ; exact omega_five

private theorem supplement_case00 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+0) (3*l+0)) (-2) (-(omega ^ 2))
    (primaryCoord (k) (l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 2).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg, map_pow, cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, ]
    all_goals ring_nf
    all_goals simp only [  omega_six,
      ]

private theorem supplement_case01 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+0) (3*l+1)) (-2) (omega ^ 1)
    (primaryCoord (l) (-k + l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 1) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [  cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

private theorem supplement_case02 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+0) (3*l+2)) sevenPrime (-(omega ^ 0))
    (primaryCoord (-k + l) (-k)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 0).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_seven,
        pow_zero,  map_one]

private theorem supplement_case10 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+1) (3*l+0)) (-2) (omega ^ 2)
    (primaryCoord (-k - 1) (-l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 2) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [ map_pow, cubicValue_lambda_two,
      cubicValue_omega_two, hw,  pow_one]
    all_goals ring_nf

private theorem supplement_case11 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+1) (3*l+1)) sevenPrime (-(omega ^ 2))
    (primaryCoord (k) (l)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 2).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg, map_pow, cubicValue_lambda_seven,
      cubicValue_omega_seven, hw,  pow_one]
    all_goals ring_nf

private theorem supplement_case12 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+1) (3*l+2)) (-2) (-(omega ^ 1))
    (primaryCoord (-l - 1) (k - l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 1).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

private theorem supplement_case20 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+2) (3*l+0)) sevenPrime (-(omega ^ 1))
    (primaryCoord (-l) (k - l + 1)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 1).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_seven,
      cubicValue_omega_seven, hw,  pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

private theorem supplement_case21 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+2) (3*l+1)) (-2) (-(omega ^ 0))
    (primaryCoord (-k + l - 1) (-k - 1)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 0).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_two,
        pow_zero,  map_one]

private theorem supplement_case22 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+2) (3*l+2)) (-2) (omega ^ 0)
    (primaryCoord (k - l) (k + 1)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 0) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [  cubicValue_lambda_two,
        pow_zero,  map_one]

theorem cubicValue_lambda_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ)
    (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ (A % 3).toNat := by
  have hA : A = 3 * (A / 3) + A % 3 := by omega
  have hB : B = 3 * (B / 3) + B % 3 := by omega
  have hAa : A % 3 = 0 ∨ A % 3 = 1 ∨ A % 3 = 2 := by omega
  have hBb : B % 3 = 0 ∨ B % 3 = 1 ∨ B % 3 = 2 := by omega
  rcases hAa with ha | ha | ha <;> rcases hBb with hb | hb | hb
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case00 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case01 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case02 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case10 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case11 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case12 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case20 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case21 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case22 P hg (A/3) (B/3) hp

end CubicRamified

end

end OAI
end OAIOriginalModule0113

/-! Original module: OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
Source SHA256: b393ffbece71820d28827135c26a9e81139329825d452aff1b70ecae9ce80249
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0114



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

open scoped BigOperators Classical

namespace CubicRamified
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

def cubicExp (n : ℤ) : O := omega ^ (n % 3).toNat

lemma cubicExp_eq_of_dvd_sub {a b : ℤ} (h : 3 ∣ a - b) : cubicExp a = cubicExp b := by
  obtain ⟨k, hk⟩ := h
  have heq : a % 3 = b % 3 := by omega
  simp only [cubicExp, heq]

lemma cubicExp_add (a b : ℤ) : cubicExp (a + b) = cubicExp a * cubicExp b := by
  simp only [cubicExp, ← pow_add]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  omega

@[simp] lemma cubicExp_zero : cubicExp 0 = 1 := by simp [cubicExp]

def linearRay (u v : ℤ) (x : O) : O :=
  cubicExp (u * (((ActualEisensteinCoordinates.coords x).1 - 1) / 3) +
    v * ((ActualEisensteinCoordinates.coords x).2 / 3))

lemma linearRay_primaryCoord (u v A B : ℤ) :
    linearRay u v (primaryCoord A B) = cubicExp (u*A + v*B) := by
  simp only [linearRay, primaryCoord, ShortDraftLatticeCount.coords_eval]
  rw [show (1 + 3*A - 1) / 3 = A by omega,
    show 3*B / 3 = B by omega]

lemma exists_primaryCoord (x : O) (hx : lambda ^ 2 ∣ x - 1) :
    ∃ A B : ℤ, x = primaryCoord A B := by
  have hthree : (3 : O) ∣ lambda ^ 2 := by
    refine ⟨-omega, ?_⟩
    rw [lambda_def]
    linear_combination omega_sq_for_norm
  obtain ⟨z, hz⟩ := hthree.trans hx
  obtain ⟨A, B, hAB⟩ := ActualEisensteinCoordinates.exists_coordinates z
  change z = (A : O) + (B : O) * omega at hAB
  refine ⟨A, B, ?_⟩
  rw [primaryCoord_eq]
  rw [hAB] at hz
  linear_combination hz

lemma primaryCoord_mul (A B C D : ℤ) :
    primaryCoord A B * primaryCoord C D =
      primaryCoord (A+C+3*(A*C-B*D)) (B+D+3*(A*D+B*C-B*D)) := by
  simp only [primaryCoord, ActualEisensteinCoordinates.eval_mul]
  congr 1 <;> ring

lemma linearRay_one (u v : ℤ) : linearRay u v 1 = 1 := by
  have hone : (1 : O) = primaryCoord 0 0 := by rw [primaryCoord_eq]; simp
  conv_lhs => rw [hone, linearRay_primaryCoord]
  simp

lemma linearRay_mul (u v : ℤ) (x y : O)
    (hx : lambda ^ 2 ∣ x - 1) (hy : lambda ^ 2 ∣ y - 1) :
    linearRay u v (x*y) = linearRay u v x * linearRay u v y := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord x hx
  obtain ⟨C,D,rfl⟩ := exists_primaryCoord y hy
  rw [primaryCoord_mul]
  simp only [linearRay_primaryCoord]
  rw [← cubicExp_add]
  apply cubicExp_eq_of_dvd_sub
  refine ⟨u*(A*C-B*D)+v*(A*D+B*C-B*D), ?_⟩
  ring

theorem symbol_eq_linearRay_of_prime (x : O) (u v : ℤ)
    (hprime : ∀ p : O, Prime p → lambda ^ 2 ∣ p-1 → symbol x p = linearRay u v p)
    (y : O) (hy : lambda ^ 2 ∣ y-1) : symbol x y = linearRay u v y := by
  obtain ⟨A,B,hyAB⟩ := exists_primaryCoord y hy
  have hy0 : y ≠ 0 := by rw [hyAB]; exact primaryCoord_ne_zero A B
  obtain ⟨s,hsprod,hs⟩ := exists_primary_prime_factorization y hy0 hy
  rw [← hsprod]
  clear hsprod hyAB hy hy0 A B y
  induction s using Multiset.induction_on with
  | empty => simp only [Multiset.prod_zero, symbol_one, linearRay_one]
  | @cons p s ih =>
    have hp := hs p (Multiset.mem_cons_self _ _)
    have hss : ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r-1 :=
      fun r hr => hs r (Multiset.mem_cons_of_mem hr)
    rw [Multiset.prod_cons, symbol_mul_denominator,
      hprime p hp.1 hp.2, ih hss,
      linearRay_mul u v p s.prod hp.2 (primary_multiset_prod s (fun r hr => (hss r hr).2))]

theorem symbol_lambda_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol lambda y = linearRay 1 0 y := by
  apply symbol_eq_linearRay_of_prime lambda 1 0 _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_lambda_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp [cubicExp]

theorem symbol_omega_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol omega y = linearRay 2 (-1) y := by
  apply symbol_eq_linearRay_of_prime omega 2 (-1) _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_omega_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp [cubicExp, sub_eq_add_neg]

theorem cubicValue_traceLambda_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ) (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P traceLambda) = cubicExp (-B) := by
  have htrace : traceLambda = -omega * lambda := by
    change 1 + 2 * omega = -omega * (omega - 1)
    linear_combination omega_sq_for_norm
  rw [htrace, map_mul, map_mul, cubicValue_neg,
    cubicValue_omega_primary P hg A B hP, cubicValue_lambda_primary P hg A B hP]
  change cubicExp (2*A-B) * cubicExp A = cubicExp (-B)
  rw [← cubicExp_add]
  exact cubicExp_eq_of_dvd_sub ⟨A, by ring⟩

theorem symbol_traceLambda_eq_linearRay (y : O) (hy : lambda ^ 2 ∣ y-1) :
    symbol traceLambda y = linearRay 0 (-1) y := by
  apply symbol_eq_linearRay_of_prime traceLambda 0 (-1) _ y hy
  intro p hp hprimary
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  obtain ⟨A,B,hpAB⟩ := exists_primaryCoord p hprimary
  rw [symbol, idealSymbol_prime _ hg]
  have hc := cubicValue_traceLambda_primary (Ideal.span {p}) hg A B (by rw [hpAB])
  rw [hc, hpAB, linearRay_primaryCoord]
  simp

theorem linearRay_congr_mod_nine (u v : ℤ) (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    linearRay u v x = linearRay u v y := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord x hx
  obtain ⟨C,D,rfl⟩ := exists_primaryCoord y hy
  obtain ⟨z,hz⟩ := hxy
  obtain ⟨E,F,hEF⟩ := ActualEisensteinCoordinates.exists_coordinates z
  change z = (E : O) + (F : O) * omega at hEF
  have hcoords : ActualEisensteinCoordinates.eval (3*(A-C)) (3*(B-D)) =
      ActualEisensteinCoordinates.eval (9*E) (9*F) := by
    have he (a b : ℤ) : ActualEisensteinCoordinates.eval a b =
        (a : O) + (b : O) * omega := rfl
    simp only [he]
    rw [hEF, primaryCoord_eq, primaryCoord_eq] at hz
    push_cast
    linear_combination hz
  have hab := ActualEisensteinCoordinates.unique_coordinates hcoords
  have ha : A-C = 3*E := by omega
  have hb : B-D = 3*F := by omega
  rw [linearRay_primaryCoord, linearRay_primaryCoord]
  apply cubicExp_eq_of_dvd_sub
  refine ⟨u*E+v*F, ?_⟩
  linear_combination u*ha + v*hb

theorem symbol_lambda_congr_mod_nine (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol lambda x = symbol lambda y := by
  rw [symbol_lambda_eq_linearRay x hx, symbol_lambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 1 0 x y hx hy hxy

theorem symbol_traceLambda_congr_mod_nine (x y : O)
    (hx : lambda ^ 2 ∣ x-1) (hy : lambda ^ 2 ∣ y-1) (hxy : (9 : O) ∣ x-y) :
    symbol traceLambda x = symbol traceLambda y := by
  rw [symbol_traceLambda_eq_linearRay x hx, symbol_traceLambda_eq_linearRay y hy]
  exact linearRay_congr_mod_nine 0 (-1) x y hx hy hxy

end CubicRamified

namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified

theorem primary_ne_zero (a : O) (ha : lambda ^ 2 ∣ a-1) : a ≠ 0 := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  exact primaryCoord_ne_zero A B

theorem symbol_one_numerator (a : O) (ha : lambda ^ 2 ∣ a-1) : symbol 1 a = 1 := by
  apply idealSymbol_map_one
  rw [primaryGenerator_span a (primary_ne_zero a ha) ha]
  exact primary_ne_zero a ha

theorem symbol_mul_numerator (x y a : O) (ha : lambda ^ 2 ∣ a-1) :
    symbol (x*y) a = symbol x a * symbol y a := by
  apply idealSymbol_map_mul
  rw [primaryGenerator_span a (primary_ne_zero a ha) ha]
  exact primary_ne_zero a ha

theorem symbol_pow_numerator (x a : O) (ha : lambda ^ 2 ∣ a-1) (n : ℕ) :
    symbol (x^n) a = symbol x a ^ n := by
  induction n with
  | zero => simp only [pow_zero, symbol_one_numerator a ha]
  | succ n ih => rw [pow_succ, symbol_mul_numerator _ _ a ha, ih, pow_succ]

theorem symbol_neg_one (a : O) (ha : lambda ^ 2 ∣ a-1) : symbol (-1) a = 1 := by
  have h := symbol_eq_linearRay_of_prime (-1) 0 0 (fun p hp hprimary => by
    let : (Ideal.span {p} : Ideal O).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
      primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
    rw [symbol, idealSymbol_prime _ hg, map_neg, map_one, A3_cubicChar_neg_one]
    simp [linearRay]) a ha
  simpa [linearRay] using h

theorem symbol_neg_numerator (x a : O) (ha : lambda ^ 2 ∣ a-1) :
    symbol (-x) a = symbol x a := by
  rw [neg_eq_neg_one_mul, symbol_mul_numerator _ _ a ha, symbol_neg_one a ha, one_mul]

theorem symbol_isUnit_ne_zero (x a : O) (hx : IsUnit x) (ha : lambda ^ 2 ∣ a-1) :
    symbol x a ≠ 0 := by
  obtain ⟨u,rfl⟩ := hx
  have h : symbol (u : O) a * symbol (↑u⁻¹ : O) a = 1 := by
    rw [← symbol_mul_numerator _ _ a ha, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, symbol_one_numerator a ha]
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem symbol_unit_congr_mod_nine (x a b : O) (hx : IsUnit x)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) (hab : (9 : O) ∣ a-b) :
    symbol x a = symbol x b := by
  obtain ⟨u,rfl⟩ := hx
  let ζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (ζ.toInteger_isPrimitiveRoot.isUnit (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu : u ∈ ([1, -1, η, -η, η^2, -η^2] : List Oˣ) :=
    IsCyclotomicExtension.Rat.Three.Units.mem ζ u
  have hω : symbol omega a = symbol omega b := by
    rw [symbol_omega_eq_linearRay a ha, symbol_omega_eq_linearRay b hb]
    exact linearRay_congr_mod_nine 2 (-1) a b ha hb hab
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · simp only [h, Units.val_one, symbol_one_numerator _ ha, symbol_one_numerator _ hb]
  · simp only [h, Units.val_neg, Units.val_one, symbol_neg_one _ ha, symbol_neg_one _ hb]
  · simpa only [h, hη] using hω
  · simpa only [h, Units.val_neg, hη, symbol_neg_numerator _ _ ha,
      symbol_neg_numerator _ _ hb] using hω
  · simpa only [h, Units.val_pow_eq_pow_val, hη, symbol_pow_numerator _ _ ha,
      symbol_pow_numerator _ _ hb] using congrArg (fun t : O => t^2) hω
  · simpa only [h, Units.val_neg, Units.val_pow_eq_pow_val, hη,
      symbol_neg_numerator _ _ ha, symbol_neg_numerator _ _ hb,
      symbol_pow_numerator _ _ ha, symbol_pow_numerator _ _ hb]
      using congrArg (fun t : O => t^2) hω

private theorem associated_congr_denominator {x y a b : O} (hxy : Associated x y)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) (hab : (9 : O) ∣ a-b)
    (hy : symbol y a = symbol y b) : symbol x a = symbol x b := by
  obtain ⟨u,hu⟩ := hxy
  apply mul_right_cancel₀ (symbol_isUnit_ne_zero (u : O) a u.isUnit ha)
  calc
    symbol x a * symbol (u : O) a = symbol y a := by
      rw [← symbol_mul_numerator _ _ a ha, hu]
    _ = symbol y b := hy
    _ = symbol x b * symbol (u : O) b := by rw [← hu, symbol_mul_numerator _ _ b hb]
    _ = symbol x b * symbol (u : O) a := by
      rw [symbol_unit_congr_mod_nine (u : O) b a u.isUnit hb ha (by simpa only [neg_sub] using dvd_neg.mpr hab)]

private theorem ramified_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

private theorem symbol_prime_denominator_congr (p a b : O) (hp : Prime p)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1)
    (h9 : (9 : O) ∣ a-b) (hpab : p ∣ a-b) : symbol p a = symbol p b := by
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  by_cases hg : lambda ∉ (Ideal.span {p} : Ideal O)
  · obtain ⟨q,hq,hprimary,-⟩ := cubicJacobi_exists_primary_generator (Ideal.span {p}) hg
    have hpq : Associated p q := Ideal.span_singleton_eq_span_singleton.mp hq
    apply associated_congr_denominator hpq ha hb h9
    have hq0 : q ≠ 0 := (hpq.prime_iff.mp hp).ne_zero
    rw [symbol_reciprocity q a hq0 (primary_ne_zero a ha) hprimary ha,
      symbol_reciprocity q b hq0 (primary_ne_zero b hb) hprimary hb]
    exact symbol_congr (hpq.dvd'.trans hpab)
  · have hdiv : p ∣ lambda := Ideal.mem_span_singleton.mp (not_not.mp hg)
    apply associated_congr_denominator (hp.associated_of_dvd ramified_prime hdiv) ha hb h9
    exact symbol_lambda_congr_mod_nine a b ha hb h9

theorem symbol_denominator_congr (x a b : O)
    (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1)
    (h9 : (9 : O) ∣ a-b) (hx : x ∣ a-b) : symbol x a = symbol x b := by
  induction x using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => have heq : a = b := sub_eq_zero.mp (zero_dvd_iff.mp hx); rw [heq]
  | h₂ u hu => exact symbol_unit_congr_mod_nine u a b hu ha hb h9
  | h₃ x p hx0 hp ih =>
    have hpab : p ∣ a-b := (dvd_mul_right p x).trans hx
    have hxab : x ∣ a-b := (dvd_mul_left x p).trans hx
    rw [symbol_mul_numerator _ _ a ha, symbol_mul_numerator _ _ b hb,
      symbol_prime_denominator_congr p a b hp ha hb h9, ih hxab]
    exact hpab

end CubicJacobiGlobal

namespace PrimaryIdealUnitReindex
open ActualEisensteinCubic ActualEisensteinCoordinates ShortDraftLatticeCount

def unitCoordinates : Finset (ℤ × ℤ) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)}

theorem q_eq_one_iff_unitCoordinates (z : ℤ × ℤ) : q z = 1 ↔ z ∈ unitCoordinates := by
  rcases z with ⟨a, b⟩
  constructor
  · intro h
    have hs := coordinate_squares a b 1 (by norm_num) (le_of_eq h)
    have ha : -1 ≤ a ∧ a ≤ 1 := by constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
    have hb : -1 ≤ b ∧ b ≤ 1 := by constructor <;> nlinarith [sq_nonneg (b - 1), sq_nonneg (b + 1)]
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    interval_cases a <;> interval_cases b <;> norm_num [q, unitCoordinates] at *
  · intro h
    simp only [unitCoordinates, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h | h <;> rw [h] <;> norm_num [q]

theorem unit_coordinate_mem (u : Oˣ) : coords u.val ∈ unitCoordinates := by
  apply (q_eq_one_iff_unitCoordinates _).mp
  have hn := (rational_qNat_eq_one_iff u.val).mpr u.isUnit
  have hz := qO_nonneg u.val
  change (q (coords u.val)).toNat = 1 at hn
  have hi : ((q (coords u.val)).toNat : ℤ) = 1 := by exact_mod_cast hn
  simpa only [Int.toNat_of_nonneg hz] using hi

def unitCoordinateMap (u : Oˣ) : {z : ℤ × ℤ // z ∈ unitCoordinates} :=
  ⟨coords u.val, unit_coordinate_mem u⟩

theorem unitCoordinateMap_bijective : Function.Bijective unitCoordinateMap := by
  constructor
  · intro u v huv
    apply Units.ext
    have hc := congrArg Subtype.val huv
    have he := congrArg (fun z : ℤ × ℤ => eval z.1 z.2) hc
    simpa only [unitCoordinateMap, eval_coords] using he
  · intro z
    have hq := (q_eq_one_iff_unitCoordinates z.val).mpr z.property
    have hu : IsUnit (eval z.val.1 z.val.2) := by
      apply (rational_qNat_eq_one_iff _).mp
      simp only [qNat, coords_eval, hq]
      norm_num
    refine ⟨hu.unit, Subtype.ext ?_⟩
    change coords hu.unit.val = z.val
    rw [hu.unit_spec, coords_eval]

def unitCoordinateEquiv : Oˣ ≃ {z : ℤ × ℤ // z ∈ unitCoordinates} :=
  Equiv.ofBijective unitCoordinateMap unitCoordinateMap_bijective

theorem card_units_eq_six : Nat.card Oˣ = 6 := by
  rw [Nat.card_congr unitCoordinateEquiv, Nat.card_eq_fintype_card, Fintype.card_coe]
  norm_num [unitCoordinates]

end PrimaryIdealUnitReindex

open scoped BigOperators Classical SchwartzMap
namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open GaussGeneratorTransport QuadraticGaussRay EisensteinSchwartzPoisson
open PrimaryIdealUnitReindex CompletedGauss

theorem rowCoprimeMask_unit_mul {α : Type*} (R : α → Ideal O)
    (S : Finset α) (u : Oˣ) (z : O) :
    rowCoprimeMask R S (u.val * z) = rowCoprimeMask R S z := by
  simp only [rowCoprimeMask, Ideal.unit_mul_mem_iff_mem _ u.isUnit]

theorem rowCoprimeMask_norm_le_one {α : Type*} (R : α → Ideal O)
    (S : Finset α) (z : O) : ‖rowCoprimeMask R S z‖ ≤ 1 := by
  unfold rowCoprimeMask
  split_ifs <;> simp

theorem masked_two_rows_radial_summable
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (Q : κ → Ideal O) [∀ i, (Q i).IsMaximal] (hgq : ∀ i, lambda ∉ Q i) (k : κ → ℕ)
    (R : α → Ideal O) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => rowCoprimeMask R S z *
      (finiteSexticRow P hg j z * finiteSexticRow Q hgq k z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hW
  intro z
  simp only [norm_mul]
  calc
    _ ≤ 1 * (1 * 1) * ‖W (‖eisEmbedding z‖ ^ 2 / M)‖ := by
      gcongr
      · exact rowCoprimeMask_norm_le_one R S z
      · exact QuadraticInitialBound.finiteSexticRow_norm_le_one P hg j z
      · exact QuadraticInitialBound.finiteSexticRow_norm_le_one Q hgq k z
    _ = _ := by ring

theorem quadratic_pair_lattice_eq_primary_ideal_sum
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (q : κ → O) (hq : ∀ i, q i ≠ 0) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hcopq : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {q i})))
    (hgq : ∀ i, lambda ∉ Ideal.span {q i})
    (hcharq : ∀ i, ringChar (O ⧸ Ideal.span {q i}) ≠ 2)
    (hray : residue (∏ i, p i) = residue (∏ i, q i))
    (R : α → Ideal O) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, if lambda ∣ z then 0 else rowCoprimeMask R S z *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) z *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) =
    (Nat.card Oˣ : ℂ) * ∑' I : GoodIdeal,
      rowCoprimeMask R S (primaryGenerator I.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (primaryGenerator I.val) *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (primaryGenerator I.val)) *
      W ((Ideal.absNorm I.val : ℝ) / M) := by
  have hs := masked_two_rows_radial_summable (fun i => Ideal.span {p i}) hg (fun _ => 3)
    (fun i => Ideal.span {q i}) hgq (fun _ => 3) R S W M hM
  have hu (u : Oˣ) (I : GoodIdeal) :
      rowCoprimeMask R S (u.val * primaryGenerator I.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (u.val * primaryGenerator I.val) *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (u.val * primaryGenerator I.val)) *
      W (‖eisEmbedding (u.val * primaryGenerator I.val)‖ ^ 2 / M) =
      rowCoprimeMask R S (primaryGenerator I.val) *
      (finiteSexticRow (fun i => Ideal.span {p i}) hg (fun _ => 3) (primaryGenerator I.val) *
        finiteSexticRow (fun i => Ideal.span {q i}) hgq (fun _ => 3) (primaryGenerator I.val)) *
      W (‖eisEmbedding (primaryGenerator I.val)‖ ^ 2 / M) := by
    rw [rowCoprimeMask_unit_mul, quadratic_pair_unit_invariant p hp hcop hg hchar
      q hq hcopq hgq hcharq hray, norm_eisEmbedding_unit_mul]
  have ht := tsum_ramified_mask_unit_invariant _ hs hu
  have hn (I : GoodIdeal) := primaryGenerator_norm_sq I.val I.property
  simpa only [hn] using ht

end QuadraticUnitInvariance

namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem canonical_masked_radial_poisson_product
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (j : ι → ℕ) (hj0 : ∀ i, j i ≠ 0) (hj6 : ∀ i, j i < 6)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, rowCoprimeMask R S z * finiteSexticRow (fun i => Ideal.span {p i}) hg j z *
      W (‖eisEmbedding z‖ ^ 2 / M)) =
    ((M : ℂ) * canonicalProductGauss p hp hcop hg j / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
      ∑ E ∈ S.powerset,
        let d := primeSubsetGenerator R E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
          finiteSexticRow (fun i => Ideal.span {p i}) hg j d / (‖eisEmbedding d‖ ^ 2 : ℝ)) *
        ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) *
          paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 /
            (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding (∏ i, p i)‖ ^ 2)) := by
  have ht := canonical_masked_radial_poisson_collected R hinj S
    (fun i => Ideal.span {p i}) hcop hg hchar j hj0 hj6 W M hM
  dsimp only at ht
  rw [finitePrimeModulus_norm_eq_product p] at ht
  rw [ht]
  let a : Finset α → ℂ := fun E =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) *
      finiteSexticRow (fun i => Ideal.span {p i}) hg j (primeSubsetGenerator R E) /
      (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 : ℝ)
  let F : Finset α → ℝ → ℂ := fun E t => paperRadialFourier W
    (M * t / (‖eisEmbedding (primeSubsetGenerator R E)‖ ^ 2 * ‖eisEmbedding (∏ i, p i)‖ ^ 2))
  have hu := gauss_weighted_finite_radial_sum_transport p hp hcop hg j S.powerset a F
  change ((M : ℂ) * canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg j /
      (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
        (∑ E ∈ S.powerset, a E * ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) *
          F E (‖eisEmbedding h‖ ^ 2)) = _
  calc
    _ = ((M : ℂ) / (‖eisEmbedding (∏ i, p i)‖ : ℂ)) *
      (canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg j *
        ∑ E ∈ S.powerset, a E * ∑' h : O,
          star (finiteSexticRow (fun i => Ideal.span {p i}) hg j h) * F E (‖eisEmbedding h‖ ^ 2)) := by ring
    _ = _ := by rw [hu]; ring
end GaussGeneratorTransport

namespace QuadraticUnitInvariance
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates
open QuadraticGaussRay MixedCrossSeparation QuadraticInitialBound
open GaussGeneratorTransport EisensteinSchwartzPoisson

theorem odd_of_quadraticRayValue_norm_eq_one (r : EisensteinEPrimaryPhase.Coord)
    (hr : ‖quadraticRayValue r‖ = 1) : EisensteinEPrimaryPhase.odd r := by
  rcases r with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [EisensteinEPrimaryPhase.odd, quadraticRayValue, breveGaussianFourTerms_formula,
      zpow_neg, Complex.I_sq, Complex.I_pow_three, Complex.inv_I, ZMod.val] at *

theorem quadraticBlock_union_eq_one_of_same_ray
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B)
    (hray : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i)) :
    quadraticBlock p hp hg (A ∪ B) = 1 := by
  have hnorm := norm_quadraticBlock p hp hcop hg hchar A
  rw [quadraticBlock_eq_rayValue p hp hcop hg hchar A] at hnorm
  have hodd := odd_of_quadraticRayValue_norm_eq_one _ hnorm
  rw [quadraticBlock_eq_rayValue p hp hcop hg hchar (A ∪ B), Finset.prod_union hd]
  exact quadraticRayValue_same_residue_product _ _ hodd hray

theorem same_ray_quadratic_pair_poisson
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (R : α → Ideal O) [∀ i, (R i).IsMaximal] (hinj : Function.Injective R) (S : Finset α)
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B)
    (hray : residue (∏ i ∈ A, p i) = residue (∏ i ∈ B, p i))
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    let n := ∏ i ∈ A ∪ B, p i
    let χ := fun z => quadraticRow (fun i => Ideal.span {p i}) hg A z *
      quadraticRow (fun i => Ideal.span {p i}) hg B z
    (∑' z : O, rowCoprimeMask R S z * χ z * W (‖eisEmbedding z‖ ^ 2 / M)) =
      ((M : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        ∑ E ∈ S.powerset,
          let d := primeSubsetGenerator R E
          ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, R i) : ℂ) * χ d /
            (‖eisEmbedding d‖ ^ 2 : ℝ)) *
          ∑' h : O, χ h * paperRadialFourier W
            (M * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding d‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) := by
  have hcAB : Pairwise (Function.onFun IsCoprime
      (fun i : (A ∪ B : Finset ι) => Ideal.span {p i.val})) := by
    intro i k hik
    exact hcop (fun h => hik (Subtype.ext h))
  have ht := canonical_masked_radial_poisson_product R hinj S
    (fun i : (A ∪ B : Finset ι) => p i.val) (fun i => hp i.val) hcAB
    (fun i => hg i.val) (fun i => hchar i.val) (fun _ => 3)
    (fun _ => by decide) (fun _ => by decide) W M hM
  have hγ := quadraticBlock_union_eq_one_of_same_ray p hp hcop hg hchar A B hd hray
  rw [quadraticBlock_eq_productGauss p hp hcop hg (A ∪ B)] at hγ
  rw [hγ, mul_one, Finset.prod_coe_sort] at ht
  have hrow (z : O) : finiteSexticRow (fun i : (A ∪ B : Finset ι) => Ideal.span {p i.val})
      (fun i => hg i.val) (fun _ => 3) z =
      quadraticRow (fun i => Ideal.span {p i}) hg A z *
        quadraticRow (fun i => Ideal.span {p i}) hg B z := by
    rw [← quadraticRow_eq_canonical (fun i => Ideal.span {p i}) hg (A ∪ B) z,
      quadraticRow_disjoint_union _ _ _ _ hd]
  simp only [hrow, star_mul, quadraticRow_star] at ht
  simpa only [mul_comm] using ht

end QuadraticUnitInvariance

open scoped BigOperators Classical SchwartzMap
namespace EisensteinSchwartzPoisson
open ActualEisensteinCubic ConcreteTraceCRT

theorem paperRadialFourier_nonzero_lattice_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        (∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let F : O → ℝ := fun h => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖
  have hs := paperRadialFourier_lattice_summable_norm W K hK0
  let f : {h : O // h ≠ 0} → {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} :=
    fun h => ⟨h.val, by nlinarith [one_le_eisenstein_norm_sq h.val h.property]⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg
      (fun z : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2} => z.val) hab)
  have hi : (∑' h : {h : O // h ≠ 0}, F h.val) ≤
      ∑' h : {h : O // K ≤ K * ‖eisEmbedding h‖ ^ 2}, F h.val := by
    exact (hs.subtype (fun h => h ≠ 0)).tsum_le_tsum_of_inj f hf
      (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype _)
  have ht := hb W K K hK0 hK0.le
  simpa only [min_eq_left hK, one_pow, one_mul] using hi.trans ht

theorem paperRadialFourier_nonzero_sum_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K : ℝ), 1 ≤ K →
        ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / (1 + K) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_nonzero_lattice_decay A
  refine ⟨s, C, hC, ?_⟩
  intro W K hK
  have hs := paperRadialFourier_lattice_summable_norm W K (lt_of_lt_of_le zero_lt_one hK)
  have he : (∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)) =
      ∑' h : {h : O // h ≠ 0}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [ite_eq_right h.property]
  rw [he]
  exact (norm_tsum_le_tsum_norm (hs.subtype _)).trans (hb W K hK)

theorem principal_tail_scalar (A : ℕ) (B x N M : ℝ)
    (hB : 0 ≤ B) (hx : 0 < x) (hxN : x ≤ N) (hM : 0 < M) :
    (M / x) * (B / (1 + M / x) ^ (A + 1)) ≤ B * (N / M) ^ A := by
  have hu : 0 < M / x := div_pos hM hx
  calc
    _ ≤ (M / x) * (B / (M / x) ^ (A + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      exact div_le_div_of_nonneg_left hB (pow_pos hu _) (pow_le_pow_left₀ hu.le (by linarith) _)
    _ = B * (x / M) ^ A := by
      simp only [div_pow, pow_succ]
      field_simp

    _ ≤ B * (N / M) ^ A := by
      gcongr

theorem maskedPrincipalRemainder_large_scale (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) ≤ M →
        ‖maskedPrincipalRemainder P S W M‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_nonzero_sum_decay (A + 1)
  refine ⟨s, C, hC, ?_⟩
  intro α _ P _ S W M hM hsize
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let N := (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  let n := fun E : Finset α => (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hn (E : Finset α) : 0 < n E := by
    dsimp [n]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  have hnN (E : Finset α) (hE : E ∈ S.powerset) : n E ≤ N := by
    have hd := Finset.prod_dvd_prod_of_subset E S P (Finset.mem_powerset.mp hE)
    have hdN := map_dvd Ideal.absNorm hd
    have hpos : 0 < Ideal.absNorm (∏ i ∈ S, P i) := by
      have hh := hn S
      dsimp only [n] at hh
      exact_mod_cast hh
    dsimp only [n, N]
    exact_mod_cast Nat.le_of_dvd hpos hdN
  have ht (E : Finset α) (hE : E ∈ S.powerset) :
      ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W
        (M * ‖eisEmbedding h‖ ^ 2 / n E)‖ ≤ B / (1 + M / n E) ^ (A + 1) := by
    have hscale : 1 ≤ M / n E := (le_div_iff₀ (hn E)).mpr (by simpa using (hnN E hE).trans hsize)
    have h := hb W (M / n E) hscale
    convert h using 1 ; congr 2 ; funext z ; congr 2 ; ring
  let f := fun E : Finset α =>
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)
  have hf (E : Finset α) (hE : E ∈ S.powerset) :
      ‖f E‖ ≤ (1 / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
    dsimp [f]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    gcongr
    · exact QuadraticInitialBound.norm_ideal_moebius_le_one _
    · exact ht E hE
  change ‖(M : ℂ) * ∑ E ∈ S.powerset, f E‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * ∑ E ∈ S.powerset, ‖f E‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM.le
    _ ≤ M * ∑ E ∈ S.powerset, (1 / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
      gcongr with E hE
      exact hf E hE
    _ = ∑ E ∈ S.powerset, (M / n E) * (B / (1 + M / n E) ^ (A + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _
      ring
    _ ≤ ∑ E ∈ S.powerset, B * (N / M) ^ A := by
      apply Finset.sum_le_sum
      intro E hE
      exact principal_tail_scalar A B (n E) N M hB (hn E) (hnN E hE) hM
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

end EisensteinSchwartzPoisson

end

end OAI
end OAIOriginalModule0114

/-! Original module: OAI.NumberTheory.DirichletL.Poisson.QuadraticProfiles
Source SHA256: c132cd3f3731f2589379f8affc780f1ded9283841f1c225e63eeb34b53cfc018
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0115



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

open scoped BigOperators Classical SchwartzMap FourierTransform
namespace EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT

def quadraticSquareProfileCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ
    (show (fun x : ℝ => x ^ 2).HasTemperateGrowth by fun_prop)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, norm_pow]
      nlinarith [sq_nonneg (‖x‖ - 1)]⟩

@[simp] theorem quadraticSquareProfileCLM_apply (W : 𝓢(ℝ, ℂ)) :
    quadraticSquareProfileCLM W = quadraticSquareProfile W := by
  ext x
  rw [quadraticSquareProfile_apply]
  rfl

def realAxisProfileCLM : 𝓢(ℂ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ
    (show (fun x : ℝ => (x : ℂ)).HasTemperateGrowth by fun_prop)
    ⟨1, 1, fun x => by simp only [pow_one, one_mul, Complex.norm_real]; linarith⟩

@[simp] theorem realAxisProfileCLM_apply (f : 𝓢(ℂ, ℂ)) :
    realAxisProfileCLM f = horizontalSlice f 0 := by
  ext x
  simp only [realAxisProfileCLM, SchwartzMap.compCLM_apply, Function.comp_apply,
    horizontalSlice_apply, complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero]

def squareFrequencyScaleCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (2 / Real.sqrt 3) (by positivity)))).restrictScalars ℝ

def quadraticTransformedSquareProfileCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) •
    squareFrequencyScaleCLM.comp (realAxisProfileCLM.comp radialFourierCLM)

@[simp] theorem quadraticTransformedSquareProfileCLM_apply (W : 𝓢(ℝ, ℂ)) :
    quadraticTransformedSquareProfileCLM W = quadraticTransformedSquareProfile W := by
  simp only [quadraticTransformedSquareProfileCLM, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, radialFourierCLM_apply, realAxisProfileCLM_apply,
    squareFrequencyScaleCLM, quadraticTransformedSquareProfile]
  rfl

theorem two_profile_seminorm_control
    (T₁ T₂ : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (s : Finset (ℕ × ℕ)) :
    ∃ (t : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T₁ W) +
        s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T₂ W) ≤
          C * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨t₁, C₁, hC₁, h₁⟩ := schwartzCLM_finite_seminorm_control T₁ s
  obtain ⟨t₂, C₂, hC₂, h₂⟩ := schwartzCLM_finite_seminorm_control T₂ s
  refine ⟨t₁ ∪ t₂, C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro W
  have ht₁ : t₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ≤
      (t₁ ∪ t₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) := Finset.sup_mono Finset.subset_union_left
  have ht₂ : t₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) ≤
      (t₁ ∪ t₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) := Finset.sup_mono Finset.subset_union_right
  have hb₁ := (h₁ W).trans (mul_le_mul_of_nonneg_left (Seminorm.le_def.mp ht₁ W) hC₁.le)
  have hb₂ := (h₂ W).trans (mul_le_mul_of_nonneg_left (Seminorm.le_def.mp ht₂ W) hC₂.le)
  nlinarith

theorem quadratic_principal_difference_large_scale (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) ≤ M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by
  obtain ⟨t, C₀, hC₀, hrem⟩ := maskedPrincipalRemainder_large_scale A
  obtain ⟨s, C₁, hC₁, hctrl⟩ := two_profile_seminorm_control
    quadraticTransformedSquareProfileCLM quadraticSquareProfileCLM t
  refine ⟨s, C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro α _ P _ hinj S W M hM hsize
  have hbound := hctrl W
  simp only [quadraticTransformedSquareProfileCLM_apply, quadraticSquareProfileCLM_apply] at hbound
  have h₁ := hrem P S (quadraticTransformedSquareProfile W) M hM hsize
  have h₂ := hrem P S (quadraticSquareProfile W) M hM hsize
  rw [quadratic_square_poisson_main_cancel P hinj S W M hM]
  calc
    _ ≤ ‖maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M‖ +
        ‖maskedPrincipalRemainder P S (quadraticSquareProfile W) M‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ S.card * (C₀ * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A +
        (2 : ℝ) ^ S.card * (C₀ * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := add_le_add h₁ h₂
    _ = (2 : ℝ) ^ S.card * C₀ *
        (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W) +
          t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by ring
    _ ≤ (2 : ℝ) ^ S.card * C₀ *
        (C₁ * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by
      gcongr
    _ = _ := by ring

open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound

theorem paperRadialFourier_nonzero_sum_uniform (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    K * ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
      pvControl W := by
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  have he : (∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)) =
      ∑' h : {h : O // h ≠ 0}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [ite_eq_right h.property]
  rw [he]
  exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hs.subtype _)) hK.le).trans
    (pv_lattice_bound W K hK)

theorem maskedPrincipalRemainder_uniform {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖maskedPrincipalRemainder P S W M‖ ≤ (2 : ℝ) ^ S.card * pvControl W := by
  let n := fun E : Finset α => (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)
  have hn (E : Finset α) : 0 < n E := by
    dsimp [n]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  let f := fun E : Finset α =>
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)
  have hf (E : Finset α) : M * ‖f E‖ ≤ pvControl W := by
    have ht := paperRadialFourier_nonzero_sum_uniform W (M / n E) (div_pos hM (hn E))
    have he (h : O) : M / n E * ‖eisEmbedding h‖ ^ 2 = M * ‖eisEmbedding h‖ ^ 2 / n E := by ring
    simp only [he] at ht
    have hm := norm_ideal_moebius_le_one (∏ i ∈ E, P i)
    dsimp only [f]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    calc
      _ = ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ((M / n E) * ‖∑' h : O, if h = 0 then 0 else
            paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)‖) := by dsimp [n]; ring
      _ ≤ 1 * pvControl W := mul_le_mul hm ht (by positivity) zero_le_one
      _ = _ := one_mul _
  change ‖(M : ℂ) * ∑ E ∈ S.powerset, f E‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * ∑ E ∈ S.powerset, ‖f E‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM.le
    _ = ∑ E ∈ S.powerset, M * ‖f E‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ E ∈ S.powerset, pvControl W := Finset.sum_le_sum (fun E _ => hf E)
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem quadratic_principal_difference_uniform :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s, C, hC, hb⟩ := two_profile_seminorm_control
    quadraticTransformedSquareProfileCLM quadraticSquareProfileCLM pvSeminorms
  refine ⟨s, pvConstant * C, mul_pos pvConstant_pos hC, ?_⟩
  intro α _ P _ hinj S W M hM
  have hbound := hb W
  simp only [quadraticTransformedSquareProfileCLM_apply, quadraticSquareProfileCLM_apply] at hbound
  rw [quadratic_square_poisson_main_cancel P hinj S W M hM]
  calc
    _ ≤ ‖maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M‖ +
        ‖maskedPrincipalRemainder P S (quadraticSquareProfile W) M‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ S.card * pvControl (quadraticTransformedSquareProfile W) +
        (2 : ℝ) ^ S.card * pvControl (quadraticSquareProfile W) :=
      add_le_add (maskedPrincipalRemainder_uniform P S _ M hM) (maskedPrincipalRemainder_uniform P S _ M hM)
    _ = (2 : ℝ) ^ S.card * pvConstant *
        (pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W) +
          pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) := by unfold pvControl; ring
    _ ≤ (2 : ℝ) ^ S.card * pvConstant * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
      exact mul_le_mul_of_nonneg_left hbound (mul_nonneg (by positivity) pvConstant_pos.le)
    _ = _ := by ring

theorem two_regime_decay (A : ℕ) (f B₀ B₁ M N : ℝ)
    (_hf : 0 ≤ f) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hM : 0 < M) (hN : 0 < N)
    (hsmall : f ≤ B₀) (hlarge : N ≤ M → f ≤ B₁ * (N / M) ^ A) :
    f ≤ (2 : ℝ) ^ A * (B₀ + B₁) / (1 + M / N) ^ A := by
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + M / N) A)).mpr
  by_cases hMN : M ≤ N
  · have hratio : M / N ≤ 1 := (div_le_one hN).mpr hMN
    have hp : (1 + M / N) ^ A ≤ (2 : ℝ) ^ A :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ ≤ B₀ * (2 : ℝ) ^ A := mul_le_mul hsmall hp (by positivity) hB₀
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) A]
  · have hNM : N ≤ M := le_of_not_ge hMN
    have hratio : N / M ≤ 1 := (div_le_one hM).mpr hNM
    have hp : (1 + N / M) ^ A ≤ (2 : ℝ) ^ A :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have he : N / M * (1 + M / N) = 1 + N / M := by field_simp; ring
    calc
      _ ≤ (B₁ * (N / M) ^ A) * (1 + M / N) ^ A :=
        mul_le_mul_of_nonneg_right (hlarge hNM) (by positivity)
      _ = B₁ * (1 + N / M) ^ A := by rw [mul_assoc, ← mul_pow, he]
      _ ≤ B₁ * (2 : ℝ) ^ A := mul_le_mul_of_nonneg_left hp hB₁
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) A]

theorem quadratic_principal_difference_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            (1 + M / (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)) ^ A := by
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := quadratic_principal_difference_uniform
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := quadratic_principal_difference_large_scale A
  refine ⟨s₀ ∪ s₁, (2 : ℝ) ^ A * (C₀ + C₁), by positivity, ?_⟩
  intro α _ P _ hinj S W M hM
  let N := (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  let Q := (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let d := (2 : ℝ) ^ S.card
  let deltaLoss := ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
    (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖
  have hN : 0 < N := by
    dsimp [N]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P S)))
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hd : 0 ≤ d := by positivity
  have hq₀ : s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W
  have hq₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hb₀ : deltaLoss ≤ d * (C₀ * Q) := by
    apply (h₀ P hinj S W M hM).trans
    dsimp only [d]
    gcongr
  have hb₁ : N ≤ M → deltaLoss ≤ d * (C₁ * Q) * (N / M) ^ A := by
    intro hsize
    apply (h₁ P hinj S W M hM hsize).trans
    dsimp only [d, N]
    gcongr
  have h := two_regime_decay A deltaLoss (d * (C₀ * Q)) (d * (C₁ * Q)) M N
    (norm_nonneg _) (by positivity) (by positivity) hM hN hb₀ hb₁
  calc
    _ = deltaLoss := rfl
    _ ≤ (2 : ℝ) ^ A * (d * (C₀ * Q) + d * (C₁ * Q)) / (1 + M / N) ^ A := h
    _ = _ := by dsimp [d, N, Q]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic MixedCrossSeparation FirstCauchyArithmetic RayFourExpansion

theorem supportRay_star {ι : Type*} (p : ι → ActualEisensteinCubic.O) (χ : RayCharacter) (S : Finset ι) :
    supportRay p (star χ) S = star (supportRay p χ S) := by
  simp only [supportRay, rayCharacter, MulChar.star_apply]

theorem supportRay_mul {ι : Type*} (p : ι → ActualEisensteinCubic.O) (χ η : RayCharacter) (S : Finset ι) :
    supportRay p (χ * η) S = supportRay p χ S * supportRay p η S := by
  simp only [supportRay, rayCharacter, MulChar.mul_apply]

theorem columnG_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnG p hp hcop hg S = ∑ χ : RayCharacter, gCoeff χ * supportRay p χ S := by
  have h := canonicalProductG_character_expansion (fun i : S => p i.val)
    (fun i => hp i.val) (columnPrimeCoprime p hcop S) (fun i => hg i.val)
    (fun i => hc i.val) (fun i => hpr i.val)
  simpa only [columnG, supportRay, Finset.prod_coe_sort] using h

def coreRayCharacter (negative : Bool) (χ ξ : RayCharacter) : RayCharacter :=
  (if negative then star χ else χ) * ξ

def coreRayCoefficient {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) : ℂ :=
  (if negative then star (crossCoeff χ η * supportRay p η F)
    else crossCoeff χ η * supportRay p η F) * gCoeff ξ

theorem core_phase_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F S : Finset ι) (negative : Bool) :
    (if negative then star (fixedRayExpansion p F S) else fixedRayExpansion p F S) *
        columnG p hp hcop hg S =
      ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        coreRayCoefficient p F negative χ η ξ * supportRay p (coreRayCharacter negative χ ξ) S := by
  rw [columnG_ray_expansion p hp hcop hg hc hpr S]
  cases negative <;> simp only [Bool.false_eq_true,  ite_false, ite_true,
    fixedRayExpansion, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum,
    coreRayCoefficient, coreRayCharacter, supportRay_mul, supportRay_star]
  · conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    apply Finset.sum_congr rfl
    intro ξ _
    ring
  · conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    apply Finset.sum_congr rfl
    intro ξ _
    ring

theorem coreRayCoefficient_norm_le {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) :
    ‖coreRayCoefficient p F negative χ η ξ‖ ≤ ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
  have hη : ‖supportRay p η F‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one η _
  have hmul : ‖crossCoeff χ η‖ * ‖supportRay p η F‖ ≤ ‖crossCoeff χ η‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hη
  cases negative <;> simp only [coreRayCoefficient, Bool.false_eq_true,
    ite_false, ite_true, norm_mul, norm_star]
  all_goals exact mul_le_mul_of_nonneg_right hmul (norm_nonneg _)

theorem coreRayCoefficient_mass {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
      ‖coreRayCoefficient p F negative χ η ξ‖) ≤ 32 * 512 := by
  calc
    _ ≤ ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
      gcongr with χ _ η _ ξ _
      exact coreRayCoefficient_norm_le p F negative χ η ξ
    _ = (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ ξ : RayCharacter, ‖gCoeff ξ‖) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ 512 * 32 := mul_le_mul crossCoeff_sum_norm_le gCoeff_sum_norm_le (by positivity) (by norm_num)
    _ = 32 * 512 := by ring

def coreRayTwist (negative : Bool) (χ ξ : RayCharacter) : ActualEisensteinCubic.O →* ℂ where
  toFun a := rayCharacter (coreRayCharacter negative χ ξ) a
  map_one' := by simp [rayCharacter]
  map_mul' a b := rayCharacter_mul _ a b

@[simp] theorem coreRayTwist_prod {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (S : Finset ι) (negative : Bool) (χ ξ : RayCharacter) :
    coreRayTwist negative χ ξ (∏ i ∈ S, p i) =
      supportRay p (coreRayCharacter negative χ ξ) S := rfl

@[simp] theorem twisted_core_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (S : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (negative : Bool) (χ ξ : RayCharacter) :
    (Ψ * coreRayTwist negative χ ξ) (∏ i ∈ S, p i) =
      Ψ (∏ i ∈ S, p i) * supportRay p (coreRayCharacter negative χ ξ) S := rfl

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

theorem actual_first_kernel_uniform_energy_envelope {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ C₁ C₂ : Finset ι → ℂ,
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_envelope W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  have hR : 0 < firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h := by
    unfold firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  intro C₁ C₂
  rw [actualFirstKernel_eq_separated p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ lengthScale d h b hsep, norm_mul]
  have hi := cube_integral_norm_le_energy p hg F
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
      (normalizedColumn p C₁) V₁ (columnLog p X₁) t d)
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
      (normalizedColumn p C₂) V₂ (columnLog p X₂) t d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ false _ _ _ t d S)
    h b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
    abs_of_nonneg (norm_nonneg _)]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi (div_nonneg hL.le (norm_nonneg _))

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)

section FixedColumn
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
  (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
  (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)

def dilatedCoreRow (t : ℝ) (z : O) : ℂ :=
  dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
    negative χ p B v ε₁ ε₂ c d z

private theorem cubeCoreCoefficient_continuous (S : Finset ι) :
    Continuous (fun t : ℝ => cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S) := by
  cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true]
  all_goals
    have h := FourierBridge.logPhase_continuous_left (-(y S))
    fun_prop

private theorem norm_cubeCoreCoefficient (S : Finset ι) (t : ℝ) :
    ‖cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S‖ =
      ‖cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y 0 S‖ := by
  cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true,
    norm_mul, norm_star, FourierBridge.logPhase_norm]

theorem dilatedCoreRow_continuous (z : O) :
    Continuous (fun t : ℝ => dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z) := by
  unfold dilatedCoreRow dilatedRayColumn supportConjugateSum
  apply continuous_finsetSum
  intro U hU
  have h := cubeCoreCoefficient_continuous p hp hcop hg B v ε₁ ε₂ negative C V y (D ∪ U)
  fun_prop

theorem dilatedCoreRow_uniform_bound (z : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z‖ ≤ M := by
  let q := fun (t : ℝ) (U : Finset ι) =>
    FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) U *
      ((if negative then star (FirstCauchyArithmetic.supportRay p χ U)
        else FirstCauchyArithmetic.supportRay p χ U) *
        cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t (D ∪ U) *
        afterDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ c d U) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z)
  refine ⟨∑ U ∈ (F \ D).powerset, ‖q 0 U‖, by positivity, ?_⟩
  intro t
  change ‖∑ U ∈ (F \ D).powerset, q t U‖ ≤ _
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro U hU
  simp only [q, norm_mul, norm_cubeCoreCoefficient]

theorem dilatedCoreRow_integrable (z : O) {k : ℝ → ℝ} (hk : Integrable k volume) :
    Integrable (fun t : ℝ => k t *
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z‖ ^ 2) volume := by
  obtain ⟨M, hM, hb⟩ := dilatedCoreRow_uniform_bound p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d z
  apply hk.mul_bdd (c := M ^ 2)
  · exact ((dilatedCoreRow_continuous p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d z).norm.pow 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2)
end FixedColumn

def firstRayIntegrand {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (c d f h : O) (b : 𝓢(ℝ, ℂ)) (t : ℝ) : ℝ :=
  ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ * ‖rayPairWeight p r D h‖ *
    ‖rayIdealRow p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d)
      negative (if negative then r.1 else r.2) D h‖ ^ 2

theorem firstRayIntegrand_integrable {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    Integrable (firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d f h b) volume := by
  have hi := dilatedCoreRow_integrable p hp hcop hg F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) C V y c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂)
    b.integrable.norm
  convert hi.mul_const (‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ * ‖rayPairWeight p r D h‖ *
    ‖beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D‖ ^ 2) using 1
  funext t
  simp only [firstRayIntegrand, rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv,
    norm_mul, mul_pow, dilatedCoreRow]
  ring

theorem first_ray_energy_integral (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ)
      (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ)
      (b : Ideal O × O → 𝓢(ℝ, ℂ)) (J : ℕ) (M H Y : ℝ),
      0 ≤ M → 0 ≤ H → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t) →
      (∑ x ∈ s, ‖w x‖ * ∫ t : ℝ,
        firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d
          (ConcretePrimeRowBridge.idealGenerator x.1) x.2 (b x) t) ≤
      (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) *
        ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
          ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C V y c d t z‖ ^ 2 := by
  obtain ⟨K, hK, hpoint⟩ := first_cube_energy_small_power deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc F D B v ε₁ ε₂ hv negative r C V y c d s T w b J M H Y hM hH hY hs hmap hT hnorm hw hdom
  let Ψ := fun t z => dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) C V y c d t z
  let source := fun t : ℝ => ∑ x ∈ s, ‖w x‖ *
    firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d
      (ConcretePrimeRowBridge.idealGenerator x.1) x.2 (b x) t
  let target := fun t : ℝ => firstLogDensity J t * ∑ z ∈ T, ‖Ψ t z‖ ^ 2
  have isource : Integrable source volume := by
    apply integrable_finsetSum
    intro x hx
    exact (firstRayIntegrand_integrable p hp hinj hcop hg F D B v ε₁ ε₂ hv negative r C V y c d _ _ (b x)).const_mul ‖w x‖
  have itarget : Integrable target volume := by
    simp only [target, Finset.mul_sum]
    exact integrable_finsetSum _ (fun z hz =>
      dilatedCoreRow_integrable p hp hcop hg F D B v ε₁ ε₂ negative
        (if negative then r.1 else r.2) C V y c d z (firstLogDensity_integrable J))
  have hst (t : ℝ) : source t ≤ (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) * target t := by
    let wt := fun x : Ideal O × O => w x * (b x t) *
      cubeBaseFactor p hp hg B v ε₁ ε₂ d x.2 * rayPairWeight p r D x.2
    have hwt (x) (hx : x ∈ s) : ‖wt x‖ ≤ M * H * firstLogDensity J t * ‖crossCoeff r.1 r.2‖ := by
      simp only [wt, norm_mul]
      calc
        _ ≤ M * (H * firstLogDensity J t) * 1 * ‖crossCoeff r.1 r.2‖ := by
          have hden := firstLogDensity_nonneg J t
          gcongr <;> first
            | positivity
            | exact hw x hx
            | exact hdom x hx t
            | exact cubeBaseFactor_norm_le_one p hp hcop hg hc B v ε₁ ε₂ d x.2
            | exact rayPairWeight_norm_le p hinj hc r D x.2
        _ = _ := by ring
    have hh := hpoint p hp hinj hcop hg F D B v ε₁ ε₂ hv negative
      (if negative then r.1 else r.2) C V y t c d s T wt
      (M * H * firstLogDensity J t * ‖crossCoeff r.1 r.2‖) Y
      (by exact mul_nonneg (mul_nonneg (mul_nonneg hM hH) (firstLogDensity_nonneg J t)) (norm_nonneg _))
      hY hs hmap hT hnorm hwt
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [firstRayIntegrand, wt, norm_mul]
      ring
    · dsimp only [target, Ψ, dilatedCoreRow]
      ring
  calc
    _ = ∫ t : ℝ, source t := by
      rw [integral_finsetSum _ (fun x hx =>
        (firstRayIntegrand_integrable p hp hinj hcop hg F D B v ε₁ ε₂ hv negative r C V y c d _ _ (b x)).const_mul ‖w x‖)]
      exact Finset.sum_congr rfl (fun x hx => (integral_const_mul _ _).symm)
    _ ≤ ∫ t : ℝ, (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) * target t :=
      integral_mono isource (itarget.const_mul _) hst
    _ = _ := integral_const_mul _ _

end FirstPassCubeLabels

end

end OAI
end OAIOriginalModule0115

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage
Source SHA256: e9492fb326d01810d11f6f52c6bad9649e3809d0d37516cf6fafede43eca9a14
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0116


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

namespace FirstPassCubeLabels

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)

theorem firstColumnEnergy_eq_sum_integrals {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V X d h b =
    ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      ∫ t : ℝ, firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r
        (normalizedColumn p C) V (columnLog p X) c d f h b t := by
  have hi (r : RayCharacter × RayCharacter) (D : Finset ι) :=
    firstRayIntegrand_integrable p hp hinj hcop hg F D B v ε₁ ε₂ hv negative r
      (normalizedColumn p C) V (columnLog p X) c d f h b
  calc
    _ = ∫ t : ℝ, ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r
        (normalizedColumn p C) V (columnLog p X) c d f h b t := by
      unfold firstColumnEnergy
      rw [normalized_originalLabelColumn]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [rayIdealEnergy, firstRayIntegrand, Finset.mul_sum, mul_assoc]
    _ = _ := by
      rw [integral_finsetSum _ (fun r hr => integrable_finsetSum _ (fun D hD => hi r D))]
      apply Finset.sum_congr rfl
      intro r hr
      exact integral_finsetSum _ (fun D hD => hi r D)

theorem first_column_energy_integral (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ)
      (b : Ideal O × O → 𝓢(ℝ, ℂ)) (J : ℕ) (M H Y : ℝ),
      0 ≤ M → 0 ≤ H → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t) →
      (∑ x ∈ s, ‖w x‖ * firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator x.1))
          V X d x.2 (b x)) ≤
      (M * H * K * Y ^ deltaLoss) * ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
        ‖crossCoeff r.1 r.2‖ * ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
          ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) (normalizedColumn p C) V (columnLog p X) c d t z‖ ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := first_ray_energy_integral deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hv negative C V X c d s T w b J M H Y hM hH hY hs hmap hT hnorm hw hdom
  simp_rw [firstColumnEnergy_eq_sum_integrals p hp hinj hcop hg F B v ε₁ ε₂ hv,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro D hD
  have h := hbound p hp hinj hcop hg hc F D B v ε₁ ε₂ hv negative r
    (normalizedColumn p C) V (columnLog p X) c d s T w b J M H Y
    hM hH hY hs hmap hT hnorm hw hdom
  simpa only [mul_assoc, Finset.mul_sum] using h

open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)

def firstOutputEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖crossCoeff r.1 r.2‖ * ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
        (if negative then r.1 else r.2) (normalizedColumn p C) V (columnLog p X) c d t z‖ ^ 2

theorem firstOutputEnergy_nonneg {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) :
    0 ≤ firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ negative C V X c d J T := by
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro D hD
  apply mul_nonneg (norm_nonneg _)
  apply integral_nonneg
  intro t
  exact mul_nonneg (firstLogDensity_nonneg J t) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem first_passage_transfer {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (C₁ C₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
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
        (originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T) := by
  obtain ⟨H, hH, hsep⟩ := actual_first_kernel_uniform_energy_envelope p hp hinj hcop hg hc hpr F B hFB
    v ε₁ ε₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ 0 J
  obtain ⟨K, hK, hpush⟩ := first_column_energy_integral deltaLoss hδ
  refine ⟨H * K, mul_nonneg hH hK.le, ?_⟩
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  let A₁ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let A₂ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let q := lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hfam : ∀ x : Ideal O × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ s →
      (∀ t : ℝ, ‖b t‖ ≤ H * firstLogDensity J t) ∧
      ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
        q * Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 b) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨b, hb, hk⟩ := hsep lengthScale hL d x.2 hd (hnonzero x hx)
      refine ⟨b, fun _ => ⟨?_, hk (A₁ x) (A₂ x)⟩⟩
      simpa only [pow_zero, one_mul] using hb
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  let E₁ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 (b x)
  let E₂ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 (b x)
  let O₁ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T
  let O₂ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T
  let P := M * H * K * Y ^ deltaLoss
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (mul_nonneg hM hH) hK.le) (Real.rpow_nonneg hY deltaLoss)
  have hE₁ (x) : 0 ≤ E₁ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ true _ _ _ _ _ _
  have hE₂ (x) : 0 ≤ E₂ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ false _ _ _ _ _ _
  have hdom : ∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t := fun x hx => (hb x hx).1
  have hsum₁ : (∑ x ∈ s, ‖w x‖ * E₁ x) ≤ P * O₁ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv true C₁ V₁ X₁ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hsum₂ : (∑ x ∈ s, ‖w x‖ * E₂ x) ≤ P * O₂ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv false C₂ V₂ X₂ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hterm (x) : ‖w x‖ * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) =
      Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt ‖w x‖) ^ 2 * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ s, ‖w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s, q * (Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ ‖w x‖ * (q * Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ s, Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ s, ‖w x‖ * E₁ x) * Real.sqrt (∑ x ∈ s, ‖w x‖ * E₂ x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le s
        (fun x => mul_nonneg (norm_nonneg _) (hE₁ x))
        (fun x => mul_nonneg (norm_nonneg _) (hE₂ x))) hq
    _ ≤ q * (Real.sqrt (P * O₁) * Real.sqrt (P * O₂)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hsum₁) (Real.sqrt_le_sqrt hsum₂)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hq
    _ = _ := by
      rw [Real.sqrt_mul hP, Real.sqrt_mul hP]
      calc
        _ = q * (Real.sqrt P)^2 * Real.sqrt O₁ * Real.sqrt O₂ := by ring
        _ = _ := by rw [Real.sq_sqrt hP]; dsimp only [P]; ring

end

open ActualEisensteinCubic
open ConcretePrimeRowBridge (conjugateIdealRowSum mobiusIdealColumn idealPairPoissonKernel
  primePool mem_primePool_iff conjugateIdealRowSum_smoothed_summable
  conjugateIdealRowSum_smoothed_poisson)
open FirstCauchyArithmetic (supportIdealFamily supportIdealFamily_pos supportIdealFamily_good
  recoveredSupport supportRay)
open RayFourExpansion (RayCharacter)
open ConcreteTraceCRT (eisEmbedding)

def dilatedIdealCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool) (χ : RayCharacter)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (I : Ideal O) : ℂ :=
  let U := recoveredSupport (fun i => Ideal.span {p i}) (F \ D) I
  (if negative then star (supportRay p χ U) else supportRay p χ U) *
    cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t (D ∪ U) *
    afterDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ c d U

theorem dilatedCoreRow_eq_ideal {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool) (χ : RayCharacter)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O) :
    dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z =
    conjugateIdealRowSum (supportIdealFamily (fun i => Ideal.span {p i}) (F \ D))
      (supportIdealFamily_pos (fun i => Ideal.span {p i}) (F \ D))
      (supportIdealFamily_good (fun i => Ideal.span {p i}) hg (F \ D))
      (dilatedIdealCoefficient p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t) z :=
  FirstCauchyArithmetic.supportConjugateSum_eq_conjugateIdealRowSum
    (fun i => Ideal.span {p i}) hinj hg (F \ D) _ z

theorem supportFamily_primePool_char {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    ∀ Q : primePool (supportIdealFamily (fun i => Ideal.span {p i}) S),
      ringChar (O ⧸ Q.val) ≠ 2 := by
  intro Q
  obtain ⟨I, hI, hQ⟩ := mem_primePool_iff.mp Q.property
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hI
  have hp' (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hU0 : (∏ i ∈ U, Ideal.span {p i}) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => (hp' i).ne_zero)
  obtain ⟨hprime, hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hU0).mp hQ
  obtain ⟨i, hi, hdi⟩ := (hprime.dvd_finsetProd_iff (fun i => Ideal.span {p i})).mp hdiv
  have he : Q.val = Ideal.span {p i} := associated_iff_eq.mp (hprime.associated_of_dvd (hp' i) hdi)
  change ringChar (O ⧸ Q.val) ≠ 2
  rw [he]
  exact hc i

theorem dilatedCoreRow_smoothed_summable {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool) (χ : RayCharacter)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / lengthScale) *
      (↑(‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z‖ ^ 2) : ℂ)) := by
  simp_rw [dilatedCoreRow_eq_ideal p hp hinj hcop hg F D B v ε₁ ε₂ negative χ C V y c d t]
  exact conjugateIdealRowSum_smoothed_summable _ _ _ _ W lengthScale hL

theorem dilatedCoreRow_second_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool) (χ : RayCharacter)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    let H := supportIdealFamily (fun i => Ideal.span {p i}) (F \ D)
    let A := dilatedIdealCoefficient p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / lengthScale) *
      (↑(‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z‖ ^ 2) : ℂ)) =
    ∑ I ∈ H, ∑ J ∈ H, (star (mobiusIdealColumn A I) * mobiusIdealColumn A J) *
      idealPairPoissonKernel H (supportIdealFamily_pos (fun i => Ideal.span {p i}) (F \ D))
        (supportIdealFamily_good (fun i => Ideal.span {p i}) hg (F \ D)) J I W lengthScale := by
  dsimp only
  simp_rw [dilatedCoreRow_eq_ideal p hp hinj hcop hg F D B v ε₁ ε₂ negative χ C V y c d t]
  exact conjugateIdealRowSum_smoothed_poisson _ _ _ (supportFamily_primePool_char p hc (F \ D)) _ W lengthScale hL

end FirstPassCubeLabels

namespace SecondPassArithmetic

section
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient columnG convertedColumnBlock quadraticCrossPhase
  columnPrimeCoprime columnCoefficient_cancel_false columnCoefficient_cancel_true)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

theorem columnCoefficient_norm_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    ‖columnCoefficient p hp hcop hg S‖ = 1 := by
  rw [FirstPassCubeLabels.columnCoefficient_eq_gaussBlock, norm_mul, norm_star,
    FiniteGaussPhase.norm_angularFactor _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)),
    FirstPassCubeLabels.gaussBlock_norm_one p hp hcop hg hc S (fun _ => 2)
      (fun _ _ => by decide) (fun _ _ => by decide), one_mul]

theorem columnCoefficient_mul_star {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    columnCoefficient p hp hcop hg S * star (columnCoefficient p hp hcop hg S) = 1 := by
  rw [← starRingEnd_apply, Complex.mul_conj', columnCoefficient_norm_one p hp hcop hg hc S]
  norm_num

theorem convertedColumnBlock_restore {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    convertedColumnBlock p hp hg S false =
      star (columnCoefficient p hp hcop hg S) * columnG p hp hcop hg S ∧
    convertedColumnBlock p hp hg S true =
      columnCoefficient p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
        star (columnG p hp hcop hg S) := by
  have ha := columnCoefficient_mul_star p hp hcop hg hc S
  constructor
  · have h := congrArg (fun z => star (columnCoefficient p hp hcop hg S) * z)
      (columnCoefficient_cancel_false p hp hcop hg hc hpr S)
    calc
      _ = (columnCoefficient p hp hcop hg S * star (columnCoefficient p hp hcop hg S)) *
          convertedColumnBlock p hp hg S false := by rw [ha, one_mul]
      _ = _ := by convert h using 1 ; ring
  · have h := congrArg (fun z => columnCoefficient p hp hcop hg S * z)
      (columnCoefficient_cancel_true p hp hcop hg hc hpr S)
    calc
      _ = (columnCoefficient p hp hcop hg S * star (columnCoefficient p hp hcop hg S)) *
          convertedColumnBlock p hp hg S true := by rw [ha, one_mul]
      _ = _ := by convert h using 1 <;> ring

def secondColumnMinus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (e k : O) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * star (columnG p hp hcop hg S) * C S *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k

def secondColumnPlus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (e k : O) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1) *
    star (columnG p hp hcop hg S) * C S *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k

theorem mobius_second_gauss_restore {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) (hd : Disjoint S T)
    (C₁ C₂ : Finset ι → ℂ) (e k : O) :
    star (supportMobius (fun i => Ideal.span {p i}) S * C₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * C₂ T) *
      activeGaussRowFactor p hp hinj hg T S e k =
    quadraticCrossPhase p hg T S * star (secondColumnMinus p hp hcop hg C₁ e k S) *
      secondColumnPlus p hp hcop hg C₂ e k T := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hmS := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj S
  have hmT := FirstCauchyArithmetic.supportMobius_sq _ hprime hinj T
  have hr (u : O) :
      finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) T S)
        (fun i => hg i.val) (activeExponent T S) u =
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T u) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S u := by
    have hh := finiteSquarefreeRow_pair_activeSupport (fun i => Ideal.span {p i}) hg T S u
    simpa [Finset.disjoint_iff_inter_eq_empty.mp hd.symm, rowCoprimeMask] using hh.symm
  unfold activeGaussRowFactor
  dsimp only
  rw [FirstCauchyArithmetic.active_productGauss_eq_mobius_converted p hp hinj hg hc hpr,
    MixedCrossSeparation.activeConvertedGauss_eq_columnBlocks p hp hg hpr T S,
    Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.sdiff_eq_self_of_disjoint hd,
    (convertedColumnBlock_restore p hp hcop hg hc hpr S).1,
    (convertedColumnBlock_restore p hp hcop hg hc hpr T).2, hr e, hr k]
  simp only [secondColumnMinus, secondColumnPlus, star_mul, star_star,
    FirstCauchyArithmetic.star_supportMobius]
  calc
    _ = (supportMobius (fun i => Ideal.span {p i}) S * supportMobius (fun i => Ideal.span {p i}) S) *
      (supportMobius (fun i => Ideal.span {p i}) T * supportMobius (fun i => Ideal.span {p i}) T) *
      (quadraticCrossPhase p hg T S *
        (star (columnCoefficient p hp hcop hg S) * columnG p hp hcop hg S * star (C₁ S) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k)) *
        (columnCoefficient p hp hcop hg T * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T (-1) *
          star (columnG p hp hcop hg T) * C₂ T * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T e) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T k)) := by ring
    _ = _ := by rw [hmS, hmT]; ring

end
section

open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient)
open FirstPassCubeLabels (row_union mask_union mask_mul)

section Masks
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem mask_star_row (e : O) :
    rowCoprimeMask P S e * star (finiteSquarefreeRow P hg S e) =
      star (finiteSquarefreeRow P hg S e) := by
  by_cases h : ∃ i ∈ S, e ∈ P i
  · have hm : rowCoprimeMask P S e = 0 := by simp [rowCoprimeMask, h]
    rw [FirstPassCubeLabels.row_zero_of_mask_zero P hg S e hm]
    simp
  · simp [rowCoprimeMask, h]

theorem second_child_masked (m r c d e k v : O) :
    rowCoprimeMask P S (m * (e * r)) *
      star (finiteSquarefreeRow P hg S e) *
      finiteSquarefreeRow P hg S d * finiteSquarefreeRow P hg S k *
      finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S v ^ 4 =
    rowCoprimeMask P S (m * r) *
      finiteSquarefreeRow P hg S (d * e * k) *
      finiteSquarefreeRow P hg S (c * e * v) ^ 4 := by
  have hr := finiteSquarefreeRow_second_child P hg S d e k c 1 v
  simp only [mul_one] at hr
  rw [mask_mul P hg S m (e * r), mask_mul P hg S e r,
    mask_mul P hg S m r]
  calc
    _ = (rowCoprimeMask P S m * rowCoprimeMask P S r) *
      (rowCoprimeMask P S e * star (finiteSquarefreeRow P hg S e)) *
      finiteSquarefreeRow P hg S d * finiteSquarefreeRow P hg S k *
      finiteSquarefreeRow P hg S c ^ 4 * finiteSquarefreeRow P hg S v ^ 4 := by ring
    _ = _ := by
      rw [mask_star_row]
      have hh := congrArg (fun z : ℂ => (rowCoprimeMask P S m * rowCoprimeMask P S r) * z) hr
      convert hh using 1 <;> ring
end Masks

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondPreColumn (Ψ : O →* ℂ) (m c d e k : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏ i ∈ S, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d *
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S e) *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S k * H S

def secondChildColumn (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S * Ψ (∏ i ∈ S, p i) *
    rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S f ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S y * H S

theorem secondPreColumn_union
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m r c d e k : O) (H : Finset ι → ℂ)
    (V N : Finset ι) (hd : Disjoint V N) :
    secondPreColumn p hp hcop hg Ψ (m * (e * r)) c d e k H (V ∪ N) =
      secondPreColumn p hp hcop hg Ψ (m * (e * r)) c d e k (fun _ => 1) V *
      secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
        (fun U => H (V ∪ U)) N := by
  have hA := FirstPassCubeLabels.columnCoefficient_union_row_four
    p hp hcop hg hpr N V hd.symm
  rw [Finset.union_comm N V] at hA
  have hrow := second_child_masked (fun i => Ideal.span {p i}) hg N m r c d e k (∏ i ∈ V, p i)
  simp only [secondPreColumn, secondChildColumn, hA, Finset.prod_union hd,
    map_mul, row_union _ hg V N hd, mask_union _ hg V N hd,
    mul_pow, star_mul, mul_one]
  calc
    _ = (columnCoefficient p hp hcop hg V * Ψ (∏ i ∈ V, p i) *
      rowCoprimeMask (fun i => Ideal.span {p i}) V (m * (e * r)) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V c ^ 4 *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V d *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V e) *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V k) *
      (columnCoefficient p hp hcop hg N * Ψ (∏ i ∈ N, p i) *
        (rowCoprimeMask (fun i => Ideal.span {p i}) N (m * (e * r)) *
          star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N e) *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N d *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N k *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N c ^ 4 *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg N (∏ i ∈ V, p i) ^ 4) *
        H (V ∪ N)) := by ring
    _ = _ := by rw [hrow]; ring

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondSeparatedPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (H₁ H₂ : Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset,
    if Disjoint S T then
      star (secondPreColumn p hp hcop hg Ψ₁ (m * (e * r)) c d e k₁ H₁ S) *
        secondPreColumn p hp hcop hg Ψ₂ (m * (e * r)) c d e k₂ H₂ T
    else 0

def secondCommonWeight (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O) (V : Finset ι) : ℂ :=
  supportMobius (fun i => Ideal.span {p i}) V *
    star (secondPreColumn p hp hcop hg Ψ₁ (m * (e * r)) c d e k₁ (fun _ => 1) V) *
      secondPreColumn p hp hcop hg Ψ₂ (m * (e * r)) c d e k₂ (fun _ => 1) V

def secondChildSum (F V : Finset ι) (Ψ : O →* ℂ)
    (m r c d e k : O) (H : Finset ι → ℂ) : ℂ :=
  ∑ N ∈ (F \ V).powerset,
    secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
      (fun U => H (V ∪ U)) N

theorem secondSeparatedPair_eq_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (H₁ H₂ : Finset ι → ℂ) :
    secondSeparatedPair p hp hcop hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ H₁ H₂ =
      ∑ V ∈ F.powerset, secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
        star (secondChildSum p hp hcop hg F V Ψ₁ m r c d e k₁ H₁) *
          secondChildSum p hp hcop hg F V Ψ₂ m r c d e k₂ H₂ := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  unfold secondSeparatedPair
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro V hV
  rw [secondCommonWeight, supportMobius, prime_product_moebius _ hprime hinj]
  simp only [secondChildSum, star_sum, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N₁ hN₁
  apply Finset.sum_congr rfl
  intro N₂ hN₂
  have hdis₁ : Disjoint V N₁ := Finset.disjoint_left.mpr (fun i hi hn =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN₁) hn)).2 hi)
  have hdis₂ : Disjoint V N₂ := Finset.disjoint_left.mpr (fun i hi hn =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN₂) hn)).2 hi)
  rw [secondPreColumn_union p hp hcop hg hpr Ψ₁ m r c d e k₁ H₁ V N₁ hdis₁,
    secondPreColumn_union p hp hcop hg hpr Ψ₂ m r c d e k₂ H₂ V N₂ hdis₂,
    star_mul]
  ring_nf

def secondChildEnergy (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (H : Finset ι → ℂ) (negative : Bool) : ℝ :=
  ∑ V ∈ F.powerset, ‖secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V‖ *
    ‖secondChildSum p hp hcop hg F V (if negative then Ψ₁ else Ψ₂)
      m r c d e (if negative then k₁ else k₂) H‖ ^ 2

theorem secondSeparatedPair_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (H₁ H₂ : Finset ι → ℂ) :
    ‖secondSeparatedPair p hp hcop hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ H₁ H₂‖ ≤
      Real.sqrt (secondChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ H₁ true) *
        Real.sqrt (secondChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ H₂ false) := by
  rw [secondSeparatedPair_eq_children p hp hcop hg hinj hpr]
  have h := DescentWeightedCauchy.weighted_cauchy F.powerset
    (secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂)
    (fun V => secondChildSum p hp hcop hg F V Ψ₂ m r c d e k₂ H₂)
    (fun V => secondChildSum p hp hcop hg F V Ψ₁ m r c d e k₁ H₁)
  simp only [secondChildEnergy, ite_true, Bool.false_eq_true, ite_false]
  convert h using 1
  · congr 2
    funext V
    ring
  · ring

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0116

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.RayCoefficients
Source SHA256: abdde869bced9a8cce51df7928ae25ebe4a952376f5c023fdbafdc89ec47f7ae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0117


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
