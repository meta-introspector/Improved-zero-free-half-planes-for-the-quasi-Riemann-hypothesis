        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=original_high_power (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · rw [energy_swap]
    have hh:=hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₂ W₁ hs₂ hs₁ X₂ X₁ hX₂ hX₁ hshort (by linarith) (by linarith)
    simpa only [mul_comm (sourceControl U W₂) (sourceControl U W₁)] using hh

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricIV

end

end OAI

end ExtendedModule12

/- BEGIN OAI.NumberTheory.DirichletL.Energy.LiveClippingDefect -/
section ExtendedModule13

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyLiveClippingDefectIV
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentRetainedEnergy
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

theorem rowTwistedSum_support_witness (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X : ℝ) (h : rowTwistedSum η m A z W t X ≠ 0) :
    ∃ I : Ideal O, I ≠ 0 ∧ W ((Ideal.absNorm I : ℝ) / X) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold rowTwistedSum
  calc
    _ = ∑' _I : Ideal O, (0 : ℂ) := by
      apply tsum_congr
      intro I
      by_cases hI : I = 0
      · subst I
        rw [idealCoeff_zero, zero_mul, zero_mul, zero_mul]
      · rw [hn I hI, mul_zero]
    _ = 0 := tsum_zero

theorem rowTwistedSum_support_scale (η : Character) (m A z : O)
    (W : ℝ → ℂ) (t X b : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b)
    (h : rowTwistedSum η m A z W t X ≠ 0) : 1 ≤ b * X := by
  obtain ⟨I, hI, hW⟩ := rowTwistedSum_support_witness η m A z W t X h
  have hn : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hn.trans ((div_le_iff₀ hX).mp (hs hW))

variable {ι : Type*} [Fintype ι]

theorem positiveSlotRow_support_scales (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (h : positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  have hp := left_ne_zero_of_mul (right_ne_zero_of_mul h)
  exact ⟨rowTwistedSum_support_scale η m A z W₁ t X₁ b hX₁ hs₁
      (left_ne_zero_of_mul hp),
    rowTwistedSum_support_scale η m A z W₂ t X₂ b hX₂ hs₂
      (right_ne_zero_of_mul hp)⟩

theorem positiveSlotRow_profiles_scales (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (h : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0) :
    1 ≤ b * X₁ ∧ 1 ≤ b * X₂ := by
  exact positiveSlotRow_support_scales η m A z _ _ S β P t X₁ X₂ b hX₁ hX₂
    (fun _ hx => (p.support 0 hx).2) (fun _ hx => (p.support 1 hx).2) h

theorem length_le_raw_add_endpoint (Z X b : ℝ) (hZ : 1 < Z) (hX : 0 < X)
    (hs : 1 ≤ b * X) : length Z X ≤ Real.logb Z X + Real.logb Z (max 1 b) := by
  have hB : 0 < max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  have hc : max 1 X ≤ max 1 b * X := by
    apply max_le
    · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le)
    · simpa using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) b) hX.le
  have hh := Real.logb_le_logb_of_le hZ
    (zero_lt_one.trans_le (le_max_left (1 : ℝ) X)) hc
  rw [Real.logb_mul hB.ne' hX.ne'] at hh
  simpa [length, add_comm] using hh

theorem total_clipping_defect (Z X₁ X₂ b : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hs₁ : 1 ≤ b * X₁) (hs₂ : 1 ≤ b * X₂) :
    length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
      2 * Real.logb Z (max 1 b) := by
  have h1 := length_le_raw_add_endpoint Z X₁ b hZ hX₁ hs₁
  have h2 := length_le_raw_add_endpoint Z X₂ b hZ hX₂ hs₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  linarith

theorem endpoint_threshold (b δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      2 * Real.logb Z (max 1 b) ≤ δ := by
  let Z₀ := Real.exp (1 + 2 * Real.log (max 1 b) / δ)
  have hb : 0 ≤ Real.log (max 1 b) := Real.log_nonneg (le_max_left _ _)
  have he : 0 < 1 + 2 * Real.log (max 1 b) / δ := by positivity
  have hZ₀ : 1 < Z₀ := Real.one_lt_exp_iff.mpr he
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZZ
  have hZ : 1 < Z := hZ₀.trans_le hZZ
  have hlog := Real.log_le_log (Real.exp_pos _) hZZ
  rw [Real.log_exp] at hlog
  have hbound : 2 * Real.log (max 1 b) ≤ δ * Real.log Z := by
    have hh : 2 * Real.log (max 1 b) / δ ≤ Real.log Z := by linarith
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm _ _)
  rw [Real.logb, ← mul_div_assoc]
  exact (div_le_iff₀ (Real.log_pos hZ)).mpr hbound

theorem profiles_uniform_defect (a b δ : ℝ) (hδ : 0 < δ) :
    ∃ Z₀ : ℝ, 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ∀ (η : Character) (m A z : O) (p : Profiles a b)
        (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
        positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ ≠ 0 →
        length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤ δ := by
  obtain ⟨Z₀, hZ₀, hh⟩ := endpoint_threshold b δ hδ
  refine ⟨Z₀, hZ₀, ?_⟩
  intro Z hZZ η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
  obtain ⟨h1, h2⟩ := positiveSlotRow_profiles_scales η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
  exact (total_clipping_defect Z X₁ X₂ b (hZ₀.trans_le hZZ) hX₁ hX₂ h1 h2).trans (hh Z hZZ)

theorem total_clipping_defect_nonneg (Z X₁ X₂ : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) := by
  have h1 := Real.logb_le_logb_of_le hZ hX₁ (le_max_right (1 : ℝ) X₁)
  have h2 := Real.logb_le_logb_of_le hZ hX₂ (le_max_right (1 : ℝ) X₂)
  rw [Real.logb_mul hX₁.ne' hX₂.ne']
  dsimp only [length]
  linarith

theorem positiveSlotRow_zero_or_defect (η : Character) (m A z : O)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ Z : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0 ∨
    (0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ∧
      length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
        2 * Real.logb Z (max 1 b)) := by
  by_cases hrow : positiveSlotRow η m A z (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0
  · exact Or.inl hrow
  · obtain ⟨h1, h2⟩ := positiveSlotRow_profiles_scales η m A z p S β P t X₁ X₂ hX₁ hX₂ hrow
    exact Or.inr ⟨total_clipping_defect_nonneg Z X₁ X₂ hZ hX₁ hX₂,
      total_clipping_defect Z X₁ X₂ b hZ hX₁ hX₂ h1 h2⟩

theorem energy_support_witness (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (h : CenteredMomentInductionEnergy.energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≠ 0) :
    ∃ z : O, keep z ∧ positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold CenteredMomentInductionEnergy.energy
  calc
    _ = ∑' _z : O, (0 : ℝ) := by
      apply tsum_congr
      intro z
      by_cases hk : keep z
      · simp only [ite_eq_left hk, hn z hk, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      · simp only [ite_eq_right hk]
    _ = 0 := tsum_zero

theorem energy_zero_or_defect (η : Character) (m A : O) (t : ℝ)
    {a b : ℝ} (p : Profiles a b) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ Z : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hZ : 1 < Z) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    CenteredMomentInductionEnergy.energy η m A t (p.profile 0) (p.profile 1)
        S β P X₁ X₂ keep Φ K = 0 ∨
    (0 ≤ length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ∧
      length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤
        2 * Real.logb Z (max 1 b)) := by
  by_cases h : CenteredMomentInductionEnergy.energy η m A t (p.profile 0) (p.profile 1)
      S β P X₁ X₂ keep Φ K = 0
  · exact Or.inl h
  · obtain ⟨z, _, hz⟩ := energy_support_witness η m A t _ _ S β P X₁ X₂ keep Φ K h
    exact Or.inr ((positiveSlotRow_zero_or_defect η m A z p S β P t X₁ X₂ Z hZ hX₁ hX₂).resolve_left hz)

theorem raw_gates_of_defect (Z M X₁ X₂ ell κ e : ℝ) (hZ : 1 < Z)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hdefect : length Z X₁ + length Z X₂ - Real.logb Z (X₁ * X₂) ≤ e)
    (hlarge : 5*M/6 ≤ length Z X₁ + length Z X₂ + ell)
    (hcap : length Z X₁ + length Z X₂ + 6*κ*ell ≤ M) :
    5*M/6-e ≤ Real.logb Z (X₁ * X₂)+ell ∧
      Real.logb Z (X₁ * X₂)+ell+(6*κ-1)*ell ≤ M := by
  have hnonneg := total_clipping_defect_nonneg Z X₁ X₂ hZ hX₁ hX₂
  constructor <;> nlinarith

theorem robust_slot_budgets (M total ell kappa defect : ℝ)
    (hell : 0 ≤ ell) (hk : 13/18 ≤ kappa)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M) :
    ell ≤ M/20+3*defect/10 ∧ (6*kappa-1)*ell ≤ M/6+defect := by
  have hkell : 10/3*ell ≤ (6*kappa-1)*ell :=
    mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem robust_defect_le_width (M xi defect : ℝ) (hM : 0 ≤ M) (hxi : 0 ≤ xi)
    (hreserve : xi+8*defect/5 ≤ M/15) : defect ≤ M := by
  linarith

theorem robust_balanced_long_nonneg (M total ell kappa xi defect : ℝ)
    (hM : 0 ≤ M) (hell : 0 ≤ ell) (hk : 13/18 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M)
    (hreserve : xi+8*defect/5 ≤ M/15) :
    8*M/15-13*defect/10 ≤ total-M/4 ∧ 0 ≤ total-M/4 := by
  obtain ⟨he, hb⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  constructor <;> linarith

theorem robust_reflected_low (M short along ell z kappa xi defect reflected : ℝ)
    (hM : 0 ≤ M) (_hs : 0 ≤ short) (hsM : short ≤ M/4)
    (_hell : 0 ≤ ell) (_hz : 0 ≤ z) (hze : z ≤ ell) (hk : 13/18 ≤ kappa)
    (he : ell ≤ M/20+3*defect/10)
    (hbudget : (6*kappa-1)*ell ≤ M/6+defect)
    (hxi : 0 ≤ xi) (hdefect : 0 ≤ defect) (hdefectM : defect ≤ M)
    (hhigh : 5*M/6 < short+max 0 along+z)
    (href : reflected ≤ max 0 (M-along+xi)) :
    0 < along ∧ reflected+short+z ≤ 23*M/30+xi+3*defect/5 ∧
      reflected+short+6*kappa*z ≤ 14*M/15+xi+8*defect/5 := by
  have haz : 0 < along := by
    by_contra hn
    have ha : along ≤ 0 := le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget : (6*kappa-1)*z ≤ M/6+defect :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap : z ≤ M/20+3*defect/10 := hze.trans he
  refine ⟨haz, ?_⟩
  by_cases hr : 0 ≤ M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem robust_reflected_low_admissible (M xi defect short reflected z kappa : ℝ)
    (hd : 0 ≤ defect) (hreserve : xi+8*defect/5 ≤ M/15)
    (ht : reflected+short+z ≤ 23*M/30+xi+3*defect/5)
    (hc : reflected+short+6*kappa*z ≤ 14*M/15+xi+8*defect/5) :
    reflected+short+z ≤ 5*M/6 ∧ reflected+short+6*kappa*z ≤ M := by
  constructor <;> linarith

theorem robust_deleted_cases (M total short along ell z kappa xi defect reflected : ℝ)
    (hM : 0 ≤ M) (hs : 0 ≤ short) (hsM : short ≤ M/4)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hk : 13/18 ≤ kappa)
    (hxi : 0 ≤ xi) (hd : 0 ≤ defect)
    (hreserve : xi+8*defect/5 ≤ M/15)
    (hlarge : 5*M/6-defect ≤ total+ell)
    (hcap : total+ell+(6*kappa-1)*ell ≤ M)
    (halong : max 0 along ≤ total-M/4)
    (href : reflected ≤ max 0 (M-along+xi)) :
    (short+max 0 along+z ≤ 5*M/6 ∧ short+max 0 along+6*kappa*z ≤ M) ∨
    (0 < along ∧ reflected+short+z ≤ 5*M/6 ∧
      reflected+short+6*kappa*z ≤ M) := by
  obtain ⟨he,hbudget⟩ := robust_slot_budgets M total ell kappa defect hell hk hlarge hcap
  by_cases hlo : short+max 0 along+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hzcap := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*kappa)
    nlinarith
  · obtain ⟨hapos, ht, hc⟩ := robust_reflected_low M short along ell z kappa xi defect reflected
      hM hs hsM hell hz hze hk he hbudget hxi hd
      (robust_defect_le_width M xi defect hM hxi hreserve) (lt_of_not_ge hlo) href
    exact Or.inr ⟨hapos, robust_reflected_low_admissible M xi defect short reflected z kappa hd hreserve ht hc⟩

theorem robust_fixed_slack (M₀ : ℝ) (hM₀ : 0 < M₀) :
    0 < M₀/56 ∧ ∀M : ℝ, M₀ ≤ M →
      M₀/56+8*(M₀/56)/5 ≤ M/15 := by
  constructor
  · positivity
  · intro M hM
    linarith

open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceDeletionCapacityIV

theorem robust_deleted_reference_cases (Z M X₁ X₂ ell z κ ξ e reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 13/18 ≤ κ)
    (hξ : 0 ≤ ξ) (he : 0 ≤ e) (hreserve : ξ+8*e/5 ≤ M/15)
    (hlarge : 5*M/6-e ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell ≤ M)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : ∀ I ∈ D₁, Prime I) (hD₂ : ∀ I ∈ D₂, Prime I)
    (href : reflected ≤ max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+ξ)) :
    let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
    let long := length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
    (short+long+z ≤ 5*M/6 ∧ short+long+6*κ*z ≤ M) ∨
    (0 < Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) ∧
      reflected+short+z ≤ 23*M/30+ξ+3*e/5 ∧
      reflected+short+6*κ*z ≤ 14*M/15+ξ+8*e/5) := by
  dsimp only
  have hb := robust_balanced_long_nonneg M (Real.logb Z (X₁*X₂)) ell κ ξ e
    hM hell hκ hξ hlarge hcap hreserve
  have hpos := comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hlog : Real.logb Z (comparisonSecond Z M X₁ X₂) = Real.logb Z (X₁*X₂)-M/4 := by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hY : 1 ≤ comparisonSecond Z M X₁ X₂ := by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
    exact Real.one_le_rpow hZ.le hb.2
  have hn₂ := product_norm_ge_one D₂ hD₂
  have hlongpos := div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort := deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0 := length_nonneg Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ)) hZ
  have hlong : length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ)) ≤
      Real.logb Z (X₁*X₂)-M/4 := by
    rw [← hlog]
    exact Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (le_max_left 1 _)) (max_le hY (div_le_self hpos.2.le hn₂))
  by_cases hlo : length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ))+
      length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6
  · refine Or.inl ⟨hlo, ?_⟩
    have hkc := mul_le_mul_of_nonneg_left hze (by linarith : 0 ≤ 6*κ)
    nlinarith
  · apply Or.inr
    obtain ⟨hellbound, hslot⟩ := robust_slot_budgets M (Real.logb Z (X₁*X₂)) ell κ e
      hell hκ hlarge hcap
    apply robust_reflected_low M _ _ ell z κ ξ e reflected hM hshort0 hshort hell hz hze hκ
      hellbound hslot hξ he (robust_defect_le_width M ξ e hM hξ hreserve) _ href
    rw [← CenteredMomentEnergyReferenceLowBranchGeometryIV.length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo

theorem robust_deleted_reference_window (Z M X₁ X₂ ell z κ ξ e : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hz : 0 ≤ z) (hze : z ≤ ell) (hκ : 13/18 ≤ κ)
    (hξ : 0 ≤ ξ) (he : 0 ≤ e) (hreserve : ξ+8*e/5 ≤ M/15)
    (hlarge : 5*M/6-e ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell ≤ M)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : ∀ I ∈ D₁, Prime I) (hD₂ : ∀ I ∈ D₂, Prime I) :
    let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
    let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+6*κ*z ≤ M) ∨
    (0 < along ∧ ∀ x ∈ Set.Icc 0 (max 0 (M-along+ξ)*Real.log Z),
      length Z (Real.exp x)+short+z ≤ 5*M/6 ∧
      length Z (Real.exp x)+short+6*κ*z ≤ M) := by
  dsimp only
  let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))
  rcases robust_deleted_reference_cases Z M X₁ X₂ ell z κ ξ e (max 0 (M-along+ξ))
    hZ hM hX₁ hX₂ hell hz hze hκ hξ he hreserve hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h.1, ?_⟩
    intro x hx
    have hh := CenteredMomentEnergyReferenceLowWindowIV.reflection_window_length Z
      (max 0 (M-along+ξ)) x hZ (le_max_left _ _) hx
    have hb := robust_reflected_low_admissible M ξ e _ (max 0 (M-along+ξ)) z κ
      he hreserve h.2.1 h.2.2
    constructor <;> linarith [hh.1]

theorem live_profiles_reference_window (a b M₀ : ℝ) (hM₀ : 0 < M₀) :
    ∃ e ξ Z₀ : ℝ, 0 < e ∧ 0 < ξ ∧ 1 < Z₀ ∧
      ∀ (Z M : ℝ), Z₀ ≤ Z → M₀ ≤ M →
      ∀ (η : Character) (m A u : O) (p : Profiles a b)
        (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
        (t X₁ X₂ ell z κ : ℝ), 0 < X₁ → 0 < X₂ → 0 ≤ ell →
        0 ≤ z → z ≤ ell → 13/18 ≤ κ →
        5*M/6 ≤ length Z X₁+length Z X₂+ell →
        length Z X₁+length Z X₂+6*κ*ell ≤ M →
      ∀ (D₁ D₂ : Finset (Ideal O)), (∀ I ∈ D₁, Prime I) → (∀ I ∈ D₂, Prime I) →
      positiveSlotRow η m A u (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0 ∨
      (let short := length Z (comparisonFirst Z M / ((∏ I ∈ D₁, I).absNorm : ℝ));
       let along := Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ));
       (short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+z ≤ 5*M/6 ∧
        short+length Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D₂, I).absNorm : ℝ))+6*κ*z ≤ M) ∨
       (0 < along ∧ ∀ x ∈ Set.Icc 0 (max 0 (M-along+ξ)*Real.log Z),
         length Z (Real.exp x)+short+z ≤ 5*M/6 ∧
         length Z (Real.exp x)+short+6*κ*z ≤ M)) := by
  have he : 0 < M₀/56 := by positivity
  obtain ⟨Z₀, hZ₀, hdefect⟩ := profiles_uniform_defect (ι := ι) a b (M₀/56) he
  refine ⟨M₀/56, M₀/56, Z₀, he, he, hZ₀, ?_⟩
  intro Z M hZZ hMM η m A u p S β P t X₁ X₂ ell z κ hX₁ hX₂ hell hz hze hκ hlarge hcap D₁ D₂ hD₁ hD₂
  by_cases hrow : positiveSlotRow η m A u (p.profile 0) (p.profile 1) S β P t X₁ X₂ = 0
  · exact Or.inl hrow
  · apply Or.inr
    have hZ := hZ₀.trans_le hZZ
    obtain ⟨hl, hc⟩ := raw_gates_of_defect Z M X₁ X₂ ell κ (M₀/56) hZ hX₁ hX₂
      (hdefect Z hZZ η m A u p S β P t X₁ X₂ hX₁ hX₂ hrow) hlarge hcap
    exact robust_deleted_reference_window Z M X₁ X₂ ell z κ (M₀/56) (M₀/56)
      hZ (hM₀.le.trans hMM) hX₁ hX₂ hell hz hze hκ he.le he.le
      ((robust_fixed_slack M₀ hM₀).2 M hMM) hl hc D₁ D₂ hD₁ hD₂

end SevenEighths.CenteredMomentEnergyLiveClippingDefectIV

end

end OAI

end ExtendedModule13

/- BEGIN OAI.NumberTheory.DirichletL.Energy.DeletedRobustGeometry -/
section ExtendedModule14

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyDeletedRobustGeometryIV
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceDivisorsIV
open CenteredMomentEnergyLiveClippingDefectIV
local notation "O" => HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(hB:0≤ Bmask)(Mcap L X₁ X₂ ell z κ xi e:ℝ)
    (hwidth:s.width≤ Mcap)(hL:Mcap+Bmask+xi≤ L)
    (hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hκ:13/18≤κ)(hxi:0≤ xi)(he:0≤ e)(hreserve:xi+8*e/5≤ s.width/15)
    (hlarge:5*s.width/6-e≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤ L ∧ along≤ L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤ L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤ s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤ s.width)):= by
  have hbase : 0 < Z := zero_lt_one.trans hZ
  have hb := robust_balanced_long_nonneg s.width (Real.logb Z (X₁*X₂)) ell κ xi e
    s.width_nonneg hell hκ hxi hlarge hcap hreserve
  have hy₁ : 1 ≤ comparisonFirst Z s.width :=
    Real.one_le_rpow hZ.le (by linarith [s.width_nonneg])
  have hy₂ : 1 ≤ comparisonSecond Z s.width X₁ X₂ := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂]
    exact Real.one_le_rpow hZ.le hb.2
  have hf : Real.logb Z (comparisonFirst Z s.width) = s.width/4 :=
    Real.logb_rpow hbase hZ.ne'
  have hl : Real.logb Z (comparisonSecond Z s.width X₁ X₂) = Real.logb Z (X₁*X₂)-s.width/4 := by
    rw [comparison_second_power Z s.width X₁ X₂ hZ hX₁ hX₂, Real.logb_rpow hbase hZ.ne']
  have hd₁ := divisor_reflection_range s hZ Mcap _ hwidth hy₁ D₁ hD₁
  have hd₂ := divisor_reflection_range s hZ Mcap _ hwidth hy₂ D₂ hD₂
  dsimp only at hd₁ hd₂
  rw [hf] at hd₁
  rw [hl] at hd₂
  have hn₁ := (divisor_norm s D₁ hD₁).1
  have hn₂ := (divisor_norm s D₂ hD₂).1
  have hlog₁ := Real.logb_nonneg hZ hn₁
  have hlog₂ := Real.logb_nonneg hZ hn₂
  have hMcap : 0 ≤ Mcap := s.width_nonneg.trans hwidth
  have hLc : 0 ≤ L := by linarith
  have hslot : 0 ≤ (6*κ-1)*ell := mul_nonneg (by linarith) hell
  dsimp only
  refine ⟨hd₁.2.2, hd₂.2.2, by linarith, by linarith [s.width_nonneg],
    by linarith, hd₂.2.1, max_le hLc (by linarith [hd₂.1]), ?_⟩
  have hp₁ : ∀ I ∈ D₁, Prime I := fun I hi =>
    CenteredMomentNaturalRowSource.support_prime s.puncture I (Finset.mem_powerset.mp hD₁ hi)
  have hp₂ : ∀ I ∈ D₂, Prime I := fun I hi =>
    CenteredMomentNaturalRowSource.support_prime s.puncture I (Finset.mem_powerset.mp hD₂ hi)
  let along := Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏ P ∈ D₂, P).absNorm : ℝ)
  have halong : Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏ P ∈ D₂, P).absNorm : ℝ)) = along := by
    rw [← hd₂.2.2]
    exact Real.logb_rpow hbase hZ.ne'
  rcases robust_deleted_reference_cases Z s.width X₁ X₂ ell z κ xi e (max 0 (s.width-along+xi))
    hZ s.width_nonneg hX₁ hX₂ hell hz hze hκ hxi he hreserve hlarge hcap D₁ D₂ hp₁ hp₂
    (by rw [halong]) with hc | hc
  · exact Or.inl (by simpa only [hd₁.2.2, hd₂.2.2] using hc)
  · apply Or.inr
    have hh := robust_reflected_low_admissible s.width xi e _ (max 0 (s.width-along+xi)) z κ
      he hreserve hc.2.1 hc.2.2
    simpa only [hd₁.2.2] using hh

end SevenEighths.CenteredMomentEnergyDeletedRobustGeometryIV

end

end OAI

end ExtendedModule14

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceRobustDeletedEnergy -/
section ExtendedModule15

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustDeletedEnergyIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyDeletedRobustGeometryIV CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem deleted_energy_from_low_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi defect saving Mcap Bmask L:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hdefect:0≤ defect)(hBmask:0≤ Bmask)(hL:Mcap+Bmask+xi≤ L)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap → xi+8*defect/5≤ s.width/15 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6-defect≤ Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤ s.width →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀F:Finset α,
      let β:=fun i I=> heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false W₁
          (comparisonFirst Z s.width/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (comparisonSecond Z s.width X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i)):=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low_with_error (α:=α) M H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap D₁ hD₁ D₂ hD₂ F
  dsimp only
  let short:=s.width/4-Real.logb Z ((∏I∈D₁,I).absNorm:ℝ)
  let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)
  have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ F) (fun i _ _=> hw i)
  have hg:=actual_deleted_gates s hZ.1 hBmask Mcap L X₁ X₂ (∑i,w i) (∑i∈F,w i) κ xi defect hs hL
    hX₁ hX₂ (Finset.sum_nonneg (fun i _=> hw i)) hsum hsumle hκ hxi.le hdefect hxiM hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤ L:=by linarith [s.width_nonneg]
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
    (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
    (fun i _ _=> Real.one_le_rpow hZ.1.le (hw i))
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=direct_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      s hQ hs W₁ W₂ hs₁ hs₂ (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask F (Finset.subset_univ F)
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs W₂ W₁ hs₂ hs₁ along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap: (fun z=> polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))) =
      (fun z=> polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · gcongr
      · exact hZ.1.le
      · exact hg.2.2.1

end SevenEighths.CenteredMomentEnergyReferenceRobustDeletedEnergyIV

end

end OAI

end ExtendedModule15

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceRobustOriginal -/
section ExtendedModule16

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustOriginalIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyDeletedRobustGeometryIV CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyReferenceRobustDeletedEnergyIV CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentInductionEnergy
theorem original_reference_from_low_robust
    (epsilonDelete:ℝ)(hepsilonDelete:0< epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi defect saving Mcap Bmask L:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hdefect:0≤ defect)(hBmask:0≤ Bmask)(hL:Mcap+Bmask+xi≤ L)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0< C ∧ 0< D ∧ 0< Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap → xi+8*defect/5≤ s.width/15 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6-defect≤ Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) :=by
  obtain ⟨Bslot,hBslot,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=α)
    (fun _=> bslot) (fun _=> Bslot) (fun _=> hBslot.le) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_energy_from_low_robust (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi defect saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hdefect hBmask hL B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  have hp:=comparison_positive Z s.width X₁ X₂ hZpos hX₁ hX₂
  apply hweight Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) _ 0
  · intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  · intro i
    exact Real.rpow_pos_of_pos hZpos _
  · intro i I hI
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
  · intro i I hI hn
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hp.1
  · exact hp.2
  · have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤ L:=by linarith [s.width_nonneg]
    have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Real.rpow_zero,mul_one] using hZ.2 Lslot ε κ η₀ Q K hK hlow
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hs hxiM
      W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap D₁ hD₁ D₂ hD₂ (Finset.univ\J)

end SevenEighths.CenteredMomentEnergyReferenceRobustOriginalIV

end

end OAI

end ExtendedModule16

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceRobustPower -/
section ExtendedModule17

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustPowerIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginalIV CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_reference_power_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6-rho/100≤ Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hscalar⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_reference_from_low_robust (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi (rho/100) saving Mcap Bmask L ha hlo hhi hbΦ hd hxi (by positivity) hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hxiM:xi+8*(rho/100)/5≤ s.width/15:=by linarith
  have hh:=hZ.2 Lslot d κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hg:=CenteredMomentEnergyLiveClippingDefectIV.robust_slot_budgets s.width
    (Real.logb Z (X₁*X₂)) (∑i,w i) κ (rho/100) hsum hκ hlarge hcap
  have hsumcap:(∑i,w i)≤ Mcap:=by linarith [s.width_nonneg]
  have hledger:=hscalar Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤ A:=by dsimp only [A];positivity
  have hE:0≤ E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤ E:=by
      calc
        _ = (1:ℝ)*diagonalControl s.radial.profile*A := by ring
        _ ≤ (K+1)*diagonalControl s.radial.profile*A :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤ L:=by linarith
  let P:=Z^(s.width+d)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+d)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤ P:=by dsimp only [P];positivity
  have hQmain:0≤ Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤ Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤ Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyReferenceRobustPowerIV

end

end OAI

end ExtendedModule17

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceLivePower -/
section ExtendedModule18

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLivePowerIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginalIV CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_reference_power_live
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀p:Profiles a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale = 0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=
    CenteredMomentEnergyReferenceRobustPowerIV.original_reference_power_robust
      (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefectIV.endpoint_threshold b (rho/100)
    (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  rcases CenteredMomentEnergyLiveClippingDefectIV.energy_zero_or_defect s.character s.mask 1 t p
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) X₁ X₂ Z s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · apply Or.inr
    have hg:=CenteredMomentEnergyLiveClippingDefectIV.raw_gates_of_defect
      Z s.width X₁ X₂ (∑i,w i) κ (rho/100) hZ.1 hX₁ hX₂
      (hdft.2.trans (hendpoint Z hZZ)) hlarge hcap
    exact hZ.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hg.1 hg.2

end SevenEighths.CenteredMomentEnergyReferenceLivePowerIV

end

end OAI

end ExtendedModule18

/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighSource -/
section ExtendedModule19

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePowerIV CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0< aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0< a)
variable (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)

def balancedInput:Input α:=
  CenteredMomentEnergyNaturalInputMatches.input M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
    hX₁ hX₂
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).1
    (comparison_positive Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one) hX₁ hX₂).2
    (comparison_same_product Z s.width X₁ X₂ (zero_lt_one.trans_le s.base_ge_one))

local notation "balancedSource"=> balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

omit [DecidableEq α] in
lemma balanced_matches:
    CenteredMomentAllocatedRayDictionary.Matches M H hH balancedSource η₀ θ w σ freq W bslot Z:=by
  constructor <;> intros <;> rfl

omit [DecidableEq α] in
lemma balanced_volume:
    CenteredMomentAmplificationChildInput.volume balancedSource=X₁*X₂*∏i,Z^(w i):=rfl

omit [DecidableEq α] in
lemma balanced_volume_bound (κ Mcap:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:13/18≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤ Mcap):
    CenteredMomentAmplificationChildInput.volume balancedSource≤ Z^Mcap:=by
  rw [balanced_volume]
  have hz:=zero_lt_one.trans hZ
  have hw0:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hx (X:ℝ):X≤ Z^(length Z X):=by
    rw [length,Real.rpow_logb hz hZ.ne' (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    exact le_max_right _ _
  calc
    _≤(Z^(length Z X₁)*Z^(length Z X₂))*(∏i,Z^(w i)):=by
      apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun _ _=> Real.rpow_nonneg hz.le _))
      exact mul_le_mul (hx X₁) (hx X₂) hX₂.le (Real.rpow_nonneg hz.le _)
    _=Z^(length Z X₁+length Z X₂+∑i,w i):=by
      rw [←Real.rpow_add hz,←Real.rpow_sum_of_pos hz,←Real.rpow_add hz]
    _≤ Z^Mcap:=Real.rpow_le_rpow_of_exponent_le hZ.le (by nlinarith)

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 13/18≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hstage⟩:=original_reference_power_live (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=α) bΦ hbΦ (fun _=> bslot) a b Mcap εdiag ξ saving (fun _=> hbslot) ha (by linarith) hM hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  rcases hz.2 Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hreference
  · exact Or.inl hzero
  · right
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (fun _=> le_rfl) s.puncture s.radial s.radial_support
      (balanced_volume_bound M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ κ Mcap hz.1 hw hκ hcap hs)
      (natural_inverse_scale s Mcap hM)
    have href':energy inp.η (fixedBadMask*idealGenerator s.puncture) 1 inp.t
        inp.W₁ inp.W₂ inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂
        s.radial.keep s.radial.profile s.radial.scale≤
        C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|+height)^J*Z^(s.width+ε):=hreference
    apply hphysical.trans
    have hh:=add_le_add_left (mul_le_mul_of_nonneg_left href' (by norm_num : (0:ℝ)≤2))
      (2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving)))
    convert hh using 1 <;> ring
end SevenEighths.CenteredMomentEnergyPositiveHighSourceIV

end

end OAI

end ExtendedModule19

/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighParameters -/
section ExtendedModule20

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveHighParametersIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePowerIV CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSourceIV CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetricIV
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0< aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0< a)
variable (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

lemma actual_width_le (hZ:1< Z):
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.width:=by
  have hn:0<(s.character.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.character.modulus_ne_bot)
  have hc:Real.logb Z (s.character.modulus.absNorm:ℝ)≤ s.characterWidth:=
    (Real.logb_le_iff_le_rpow hZ hn).mpr s.modulus_bound
  rw [s.scale_eq,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  exact add_le_add_right hc _

lemma actual_conductor_scale (hZ:1< Z):
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤ Z^s.width:=by
  rw [s.scale_eq,NaturalState.width,Real.rpow_add (zero_lt_one.trans hZ)]
  exact mul_le_mul_of_nonneg_left s.modulus_bound (Real.rpow_nonneg (by linarith) _)

omit [DecidableEq α] in
lemma balanced_log_volume (κ:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:13/18≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width):
    Real.logb Z (CenteredMomentAmplificationChildInput.volume balancedSource)≤ s.width:=by
  have hv:0< CenteredMomentAmplificationChildInput.volume balancedSource:=by
    rw [balanced_volume]
    exact mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun _ _=> Real.rpow_pos_of_pos (by linarith) _))
  exact (Real.logb_le_iff_le_rpow hZ hv).mpr
    (balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl)

omit [DecidableEq α] in
lemma balanced_actual_four_scales (hZ:1< Z)(hwidth:0< s.width)
    (hshort:s.width/4≤ min (length Z X₁) (length Z X₂)):
    let M0:=Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ);
    Z^(M0/4)≤(balancedSource).X₁ ∧ Z^(M0/4)≤(balancedSource).X₂ ∧
    Z^(M0/4)≤(balancedSource).Y₁ ∧ Z^(M0/4)≤(balancedSource).Y₂:=by
  have hf:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  have hm:=actual_width_le s hZ
  have hp:Z^((Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ))/4)≤
      Z^(s.width/4):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  exact ⟨hp.trans hf.1,hp.trans hf.2.1,hp.trans hf.2.2.1,hp.trans hf.2.2.2.1⟩

omit [DecidableEq α] in
lemma balanced_control (N:ℕ)(hN:Fintype.card α≤ N)(S:Finset (ℕ×ℕ)):
    (plainControl balancedSource (p.profile 0) (p.profile 1))^2≤
      (CenteredMomentEnergyNaturalInputMatches.profileBound W hW aslot bslot lo hi haslot hWs)^(2*N)*
        (p.control (insert (0,0) S))^2:=by
  apply plain_control_sq_le balancedSource p S N _
    (CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one W hW aslot bslot lo hi haslot hWs)
    hN (fun _=> le_rfl)

omit [DecidableEq α] in
lemma balanced_source_cost (N:ℕ)(hN:Fintype.card α≤ N)(hZ:1< Z):
    CenteredMomentFirstReferenceEnergy.sourceFactor balancedSource a a s.radial.scale≤
      (Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a))*Z^s.width:=by
  have hK:0< s.radial.scale:=by rw [s.scale_eq]; positivity
  have hc:=source_factor_le balancedSource N aslot a s.radial.scale haslot ha hK hN (fun _=> le_rfl)
  have hconst:0≤ Real.exp (Real.log 4)*CenteredMomentFirstPhysicalSource.fixedPresentationCost/
        ((min 1 aslot)^N*a*a):=by
    have hp:=CenteredMomentFirstPhysicalSource.fixedPresentationCost_pos
    positivity
  have he:(balancedSource).η=s.character:=rfl
  rw [he] at hc
  apply hc.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (actual_conductor_scale s hZ) hconst

end SevenEighths.CenteredMomentEnergyPositiveHighParametersIV

end

end OAI

end ExtendedModule20

/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveBalancedAdmission -/
section ExtendedModule21

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyPositiveBalancedAdmissionIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLivePowerIV CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyPositiveHighSourceIV CenteredMomentEnergyOriginalProfileControl
open CenteredMomentEnergyOriginalHighReflectionSymmetricIV
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0< aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0< a)
variable (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)

local notation "balancedSource" => balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂

open CenteredMomentEnergyPositiveHighParametersIV
open CenteredMomentEnergyNaturalInputMatches CenteredMomentAmplificationChildInput

theorem fixed_fields :
    (balancedSource).lower=aslot ∧ (balancedSource).upper=bslot ∧
    (balancedSource).b₁=b ∧ (balancedSource).b₂=b ∧
    (balancedSource).W₁=p.profile 0 ∧ (balancedSource).W₂=p.profile 1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧ (balancedSource).t=t ∧
    (∀i,(balancedSource).lo i=aslot) ∧ (∀i,(balancedSource).hi i=bslot) ∧
    (∀i,(balancedSource).M i=profileBound W hW aslot bslot lo hi haslot hWs) ∧
    (∀i,(balancedSource).P i=Z^(w i)) := by
  repeat' constructor
  all_goals intro i;rfl

theorem fixed_lower_product (N:ℕ)(hN:Fintype.card α≤ N) :
    0<(min 1 aslot)^N*a*a ∧
    (min 1 aslot)^N*a*a≤(∏i,(balancedSource).lo i)*a*a := by
  have hh:=CenteredMomentEnergyOriginalProfileControl.lower_product balancedSource N aslot haslot hN
    (fun _=> le_rfl)
  exact ⟨by positivity,mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ha.le) ha.le⟩

lemma exact_log_volume (hZ:1< Z) :
    Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+∑i,w i := by
  have hh:=CenteredMomentEnergyInputParentCapacity.input_volume_log balancedSource Z
  change Real.logb Z (volume balancedSource)=Real.logb Z X₁+Real.logb Z X₂+
    ∑i,Real.logb Z (Z^(w i)) at hh
  simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

theorem four_upper_scales (κ L:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:13/18≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤ L) :
    (balancedSource).X₁≤ Z^L ∧ (balancedSource).X₂≤ Z^L ∧
    (balancedSource).Y₁≤ Z^L ∧ (balancedSource).Y₂≤ Z^L := by
  have hp:0< Z:=zero_lt_one.trans hZ
  have hx:=CenteredMomentEnergyNaturalSourceAdmission.original_scale_caps w hZ hX₁ hX₂ hw
    (by linarith : (1/6:ℝ)≤κ) hcap hs
  have hv:=balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs
  have hprod:1≤∏i,Z^(w i):=by
    rw [←Real.rpow_sum_of_pos hp]
    exact Real.one_le_rpow hZ.le (Finset.sum_nonneg (fun i _=> hw i))
  have hxy:X₁*X₂≤ volume balancedSource:=by
    change X₁*X₂≤ X₁*X₂*(∏i,Z^(w i))
    exact le_mul_of_one_le_right (mul_pos hX₁ hX₂).le hprod
  have hY:1≤ comparisonFirst Z s.width:=Real.one_le_rpow hZ.le (div_nonneg s.width_nonneg (by norm_num))
  refine ⟨hx.1,hx.2,?_,?_⟩
  · change Z^(s.width/4)≤ Z^L
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [s.width_nonneg])
  · change X₁*X₂/comparisonFirst Z s.width≤ Z^L
    exact (div_le_self (mul_pos hX₁ hX₂).le hY).trans (hxy.trans hv)

theorem four_lower_scales (hZ:1< Z)(hwidth:0< s.width)
    (hshort:s.width/4≤ min (length Z X₁) (length Z X₂)) :
    Z^(s.width/4)≤(balancedSource).X₁ ∧ Z^(s.width/4)≤(balancedSource).X₂ ∧
    Z^(s.width/4)≤(balancedSource).Y₁ ∧ Z^(s.width/4)≤(balancedSource).Y₂ := by
  have hh:=balanced_four_scale_gates Z s.width X₁ X₂ hZ hwidth hX₁ hX₂ hshort
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

theorem state_capacity_packet (κ L:ℝ)(hZ:1< Z)(hw:∀i,0≤ w i)(hκ:13/18≤κ)
    (hcap:length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width)(hs:s.width≤ L) :
    1≤ s.radial.scale ∧ s.radial.scale⁻¹≤1 ∧
    (balancedSource).η=s.character ∧ (balancedSource).m=s.mask ∧
    length Z (balancedSource).X₁+length Z (balancedSource).X₂+6*κ*(∑i,w i)≤ s.width ∧
    Real.logb Z s.radial.scale+Real.logb Z ((balancedSource).η.modulus.absNorm:ℝ)≤ s.width ∧
    volume balancedSource≤ Z^s.width ∧ Real.logb Z (volume balancedSource)≤ s.width ∧
    volume balancedSource≤ Z^L ∧
    (s.puncture.absNorm:ℝ)≤ Z^Bmask := by
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  exact ⟨hr.1,hr.2.1,rfl,rfl,hcap,actual_width_le s hZ,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ s.width hZ hw hκ hcap le_rfl,
    balanced_log_volume M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ hZ hw hκ hcap,
    balanced_volume_bound M H hH η₀ θ W hW aslot bslot lo hi haslot hWs w σ freq hσ
      s p ha t X₁ X₂ hX₁ hX₂ κ L hZ hw hκ hcap hs,s.puncture_bound⟩

end SevenEighths.CenteredMomentEnergyPositiveBalancedAdmissionIV

end

end OAI

end ExtendedModule21

/- BEGIN OAI.NumberTheory.DirichletL.Energy.FirstSourceParameters -/
section ExtendedModule22

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentEnergyFirstSourceParametersIV
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstStageLossBudget CenteredMomentEnergyFirstActualFrequencyBudget
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentSectorLocalization

def sourceEpsilon (M A B ε:ℝ):ℝ:=reserve M B ε/(4*((A+1)+A+1))
def maskEpsilon (M B ε:ℝ):ℝ:=reserve M B ε/(B+B+1)
def columnLoss (M B ε:ℝ)(k:ℕ):ℝ:=
  stageLoss M B ε (k+1)-2*reserve M B ε-reserve M B ε/4

lemma source_cap_mono (es ds ts Bactual Bschedule sigma delta amp em child er θs θc κ mesh A saving:ℝ)
    (hB:Bactual≤ Bschedule)(ht:0≤ ts)(hem:0≤ em)(j:Fin 4):
    losses es ds ts Bactual j+
      lossVector sigma delta amp (sourcePaid Bactual em child er delta amp θs θc κ mesh) es A saving j≤
    losses es ds ts Bschedule j+
      lossVector sigma delta amp (sourcePaid Bschedule em child er delta amp θs θc κ mesh) es A saving j:=by
  fin_cases j <;>
    simp only [losses,lossVector,sourcePaid,Matrix.cons_val,Fin.reduceFinMk] <;>
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hB),mul_nonneg hem (sub_nonneg.mpr hB)]

theorem parameter_gates (M A B κ ε:ℝ)(hM:0≤ M)(hA:0≤ A)(hB:0≤ B)
    (hκ:(13/18:ℝ)≤κ)(hε:0<ε):
    let sigma:=amplification ε
    let r:=reserve M B ε
    0< sigma ∧ sigma≤1 ∧ 0< r/4 ∧ r/4≤ sigma/4 ∧ r/4≤1 ∧
      0< sourceEpsilon M A B ε ∧ sourceEpsilon M A B ε≤1 ∧
      0< maskEpsilon M B ε ∧ 0< mesh M B κ ε ∧
      mesh M B κ ε≤ sigma/12 ∧ 0≤ sigma/12 ∧ sigma/12< sigma/6 ∧
      0<2*sigma+1 ∧ 0≤ A+1:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have hb:=bounds M B κ ε hM hB hκ0 hε
  have hr:=hb.2.2.2.1
  have hrs:reserve M B ε≤ amplification ε/100:=min_le_left _ _
  have hm:=hb.2.2.2.2.2.1
  have hes:0< sourceEpsilon M A B ε:=by unfold sourceEpsilon;positivity
  have hesr:sourceEpsilon M A B ε≤ reserve M B ε:=by
    unfold sourceEpsilon
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hr.le hA]
  exact ⟨hb.1,hb.2.1,by positivity,by linarith,by linarith,
    hes,by linarith,by unfold maskEpsilon;positivity,hb.2.2.2.2.1,
    by linarith,by linarith [hb.1],by linarith [hb.1],by linarith [hb.1],by linarith⟩

lemma columnLoss_physical (M B ε:ℝ)(k:ℕ):
    columnLoss M B ε k+reserve M B ε/4=
      CenteredMomentEnergyStageMargins.physicalLoss M B ε k:=by
  unfold columnLoss CenteredMomentEnergyStageMargins.physicalLoss
  ring

theorem eventually_actual_four_fit (M A P B κ ε:ℝ)
    (hM:0≤ M)(hA:0≤ A)(_hP:0≤ P)(hB:0≤ B)(hready:readyBudget A P≤ B)
    (hκ:(13/18:ℝ)≤κ)(hε:0<ε):
    let r:=reserve M B ε
    ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(k:ℕ)(εchild:ℝ),εchild≤ stageLoss M B ε k→∀j:Fin 4,
        losses (sourceEpsilon M A B ε) (r/4) (r/4) (readyBudget A P) j+
          lossVector (amplification ε) (frequencyLoss Z 32 (r/4)) (r/4)
            ((readyBudget A P+readyBudget A P)*maskEpsilon M B ε+εchild+r/4+
              (frequencyLoss Z 32 (r/4)+r/4+r/4)/6+(r/4)/3+κ*mesh M B κ ε)
            (sourceEpsilon M A B ε) A (2*amplification ε+1) j+
          sourceEpsilon M A B ε*(A+1)+r/4≤ columnLoss M B ε k:=by
  dsimp only
  have hκ0:0≤κ:=by linarith
  have h:=actual_frequency_four_budget M A B (A+1) κ ε hM hA hB (by linarith) hκ0 hε
  obtain ⟨_,_,hem,_,_,hevent⟩:=h
  have hr:0< reserve M B ε:=(bounds M B κ ε hM hB hκ0 hε).2.2.2.1
  filter_upwards [hevent] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro k εchild hchild j
  have hfit:=hZ.2.2.2 k εchild (reserve M B ε) (reserve M B ε) hchild le_rfl le_rfl j
  have hmono:=source_cap_mono (sourceEpsilon M A B ε) (reserve M B ε/4) (reserve M B ε/4)
    (readyBudget A P) B (amplification ε) (frequencyLoss Z 32 (reserve M B ε/4))
    (reserve M B ε/4) (maskEpsilon M B ε) εchild (reserve M B ε/4)
    (reserve M B ε/4) (reserve M B ε/4) κ (mesh M B κ ε) A (2*amplification ε+1)
    hready (by positivity) hem.le j
  change losses (sourceEpsilon M A B ε) _ _ B j+
    lossVector _ _ _ (sourcePaid B (maskEpsilon M B ε) εchild _ _ _ _ _ _ _) _ _ _ j+
    sourceEpsilon M A B ε*(A+1)+_+_+_+_≤_ at hfit
  dsimp only [sourcePaid] at hmono hfit
  unfold columnLoss
  dsimp only [sourceEpsilon,maskEpsilon] at hmono hfit ⊢
  linarith only [hmono,hfit]

theorem ready_budget_final (M Bmask L ε A P:ℝ)(hM:0≤ M)(hB:0≤ Bmask)
    (hA:A≤2*CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε)+M+1)
    (hP:P≤ Bmask):
    readyBudget A P≤ CenteredMomentEnergyWidthRanges.finalSourceCap M Bmask L ε:=by
  have hn:1≤ count M ε:=by
    unfold count CenteredMomentFirstSecondLossParameters.depth
    omega
  have hm:=CenteredMomentEnergyWidthRanges.range_mono M Bmask L hM hB hn
  have hr:20≤ CenteredMomentEnergyWidthRanges.range M Bmask L (count M ε):=by
    simp only [CenteredMomentEnergyWidthRanges.range,CenteredMomentEnergyWidthRanges.step] at hm
    linarith [le_max_left (1:ℝ) L]
  unfold readyBudget CenteredMomentEnergyWidthRanges.finalSourceCap CenteredMomentEnergyWidthRanges.sourceCap
  linarith

end SevenEighths.CenteredMomentEnergyFirstSourceParametersIV

end

end OAI

end ExtendedModule22

/- BEGIN OAI.NumberTheory.DirichletL.Energy.NaturalLowPhysical -/
section ExtendedModule23

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowPhysicalIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyPositiveLowBandSource
open CenteredMomentEnergyNaturalSourceAdmission
open CenteredMomentEnergyPositiveHighParametersIV CenteredMomentEnergyPositiveBalancedAdmissionIV
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParametersIV
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_natural_low_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (_hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(13/18:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤ Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0< a0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0< lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0< r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLbase:0≤ max Lgoal Mparent:=hL.trans (le_max_left _ _)
  have hLphys:0≤2*max Lgoal Mparent+r/4:=by positivity
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalLowPhysical.actual_low_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (2*max Lgoal Mparent+r/4) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall hbeta hκbeta N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=> aslot) (fun _=> bslot) (fun _=> hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b),
    eventually_scale_admission b (max Lgoal Mparent) (r/4) hLbase hr]
    with Z hZZ hfit hclipPow hscale
  have hZ:1< Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0< max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlow
  let inp:=zeroSourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤ N:=Fintype.card_le_of_injective (fun i:T=> i.val) Subtype.val_injective
  have hm:=(both_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂).2
  have hu:=hscale.2 T M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ
    hw hκsmall (hstate.trans (le_max_right _ _)) hcapacity
  have hg:max Lgoal Mparent≤2*max Lgoal Mparent+r/4:=by linarith
  have hu1:inp.X₁≤ Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hu2:inp.X₂≤ Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hp:=lower_product_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hlowV:Real.logb Z (volume inp)≤5*state.width/6:=
    (low_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ hZ hlow).2
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=> le_rfl) (fun _=> le_rfl) (fun _=> rfl) (fun _=> rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu1 hu2 hu.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl hlowV (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  have hv0:volume inp = volume (sourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂):=rfl
  rw [ht,hv0] at hh
  simpa only [map_one,Nat.cast_one,div_one,mul_assoc] using hh

end SevenEighths.CenteredMomentEnergyNaturalLowPhysicalIV

end

end OAI

end ExtendedModule23

/- BEGIN OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionBounded -/
section ExtendedModule24

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionBoundedIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionOriginalIV CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_high_power
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      length Z X₁≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_high_from_low (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hxiM:xi≤ s.width/15:=by linarith
  have hh:=hZ.2 Lslot e κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hsumcap:(∑i,w i)≤ Mcap:=by
    have hlen₁:=length_nonneg Z X₁ hZ.1
    have hlen₂:=length_nonneg Z X₂ hZ.1
    have hk:=mul_le_mul_of_nonneg_right (show (1:ℝ)≤6*κ by linarith) hsum
    nlinarith
  have hledger:=hscalar e he Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤ A:=by dsimp only [A];positivity
  have hE:0≤ E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left hdiag (le_add_of_nonneg_left hK)) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤ L:=by linarith
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤ P:=by dsimp only [P];positivity
  have hQmain:0≤ Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤ Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤ Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionBoundedIV

end

end OAI

end ExtendedModule24

/- BEGIN OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetricBounded -/
section ExtendedModule25

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBoundedIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionBoundedIV
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyOriginalHighReflectionSymmetricIV

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_unbalanced_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      min (length Z X₁) (length Z X₂)≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_high_power (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  rcases min_le_iff.mp hshort with hshort|hshort
  · exact hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · rw [energy_swap]
    have hh:=hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs W₂ W₁ hs₂ hs₁ X₂ X₁ hX₂ hX₁ hshort (by linarith) (by linarith)
    simpa only [mul_comm (sourceControl U W₂) (sourceControl U W₁)] using hh

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBoundedIV

end

end OAI

end ExtendedModule25

/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighAssembly -/
section ExtendedModule26

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssemblyIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceIV CenteredMomentEnergyOriginalHighReflectionSymmetricIV
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

omit [Fintype α] [DecidableEq α] in
lemma low_restrict (W:ℝ→ℂ)(bslot a b bΦ Bmask L L' Lslot lo hi Mcap d d' κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hZ:1≤ Z)(hL:L'≤ L)(hd:d≤ d')(hC:0≤ C)
    (h:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap d κ Z η₀ Q degree S C):
    PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L' Lslot lo hi
      Mcap d' κ Z η₀ Q degree S C:=by
  intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
  have hscale:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs p X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale) hcap hlow
  apply hh.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
    (by have hh:=diagonalControl_nonneg s.radial.profile;positivity)

theorem actual_high_source_split
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d L:ℝ,0< d ∧ 0≤ L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃Ju Jr:ℕ,∃Uu Ur:Finset (ℕ×ℕ),∃Cu Cr:ℝ,0< Cu ∧ 0< Cr ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 13/18≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cu*(K+1)*diagonalControl s.radial.profile*(sourceControl Uu (p.profile 0)*sourceControl Uu (p.profile 1))^2*
          (1+|t|+height)^Ju*Z^(s.width+ε) ∨
      (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(sourceControl Ur (p.profile 0)*sourceControl Ur (p.profile 1))^2*
        (1+|t|+height)^Jr*Z^(s.width+ε) :=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuR,hLu,hustage⟩:=original_unbalanced_from_low (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirR,hLr,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrstage⟩:=
    actual_positive_source_entry (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨min du dr,max Lu Lr,lt_min hdu hdr,?_,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  · exact (show 0≤ Lu by linarith).trans (le_max_left _ _)
  intro degree S
  obtain ⟨Ju,Uu,Cu,hCu,hu⟩:=hustage degree S
  obtain ⟨Jr,Ur,Cr,hCr,hr⟩:=hrstage degree S
  refine ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,?_⟩
  filter_upwards [hu,hr] with Z hzu hzr
  refine ⟨hzu.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hlu:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lu
    Lslot lo hi Mcap (min du dr) du κ Z η₀ Q degree S K hzu.1.le (le_max_left _ _) (min_le_left _ _) hK hlow
  have hlr:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lr
    Lslot lo hi Mcap (min du dr) dr κ Z η₀ Q degree S K hzu.1.le (le_max_right _ _) (min_le_right _ _) hK hlow
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
  · left
    exact hzu.2 Lslot κ η₀ Q K hK hlu θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · have hfour:=balanced_four_scale_gates Z s.width X₁ X₂ hzu.1 (hrho.trans_le hslo)
      hX₁ hX₂ (le_of_lt (lt_of_not_ge hshort))
    rcases hzr.2 Lslot κ η₀ Q K hK hlr θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hsource
    · left
      rw [hzero]
      have hd:=diagonalControl_nonneg s.radial.profile
      have hz:=zero_lt_one.trans hzu.1
      positivity
    · exact Or.inr ⟨⟨hfour.1,hfour.2.1,hfour.2.2.1,hfour.2.2.2.1⟩,hsource⟩
end SevenEighths.CenteredMomentEnergyPositiveHighAssemblyIV

end

end OAI

end ExtendedModule26

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceRobustBounded -/
section ExtendedModule27

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceRobustBoundedIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginalIV CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyStageReserveBounded
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_reference_power_robust
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6-rho/100≤ Real.logb Z (X₁*X₂)+(∑i,w i) →
      Real.logb Z (X₁*X₂)+(∑i,w i)+(6*κ-1)*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hLupper,hscalar⟩:=
    exists_bounded_separated_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_reference_from_low_robust (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi (rho/100) saving Mcap Bmask L ha hlo hhi hbΦ hd hxi (by positivity) hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hxiM:xi+8*(rho/100)/5≤ s.width/15:=by linarith
  have hh:=hZ.2 Lslot e κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hg:=CenteredMomentEnergyLiveClippingDefectIV.robust_slot_budgets s.width
    (Real.logb Z (X₁*X₂)) (∑i,w i) κ (rho/100) hsum hκ hlarge hcap
  have hsumcap:(∑i,w i)≤ Mcap:=by linarith [s.width_nonneg]
  have hledger:=hscalar e he Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤ A:=by dsimp only [A];positivity
  have hE:0≤ E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤ E:=by
      calc
        _ = (1:ℝ)*diagonalControl s.radial.profile*A := by ring
        _ ≤ (K+1)*diagonalControl s.radial.profile*A :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤ L:=by linarith
  let P:=Z^(s.width+e)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+e)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤ P:=by dsimp only [P];positivity
  have hQmain:0≤ Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤ Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤ Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyReferenceRobustBoundedIV

end

end OAI

end ExtendedModule27

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceLiveBounded -/
section ExtendedModule28

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyReferenceLiveBoundedIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceRobustOriginalIV CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_reference_power_live
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e → 0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀p:Profiles a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale = 0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂)
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+e+ε) :=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=
    CenteredMomentEnergyReferenceRobustBoundedIV.original_reference_power_robust
      (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Z₀,hZ₀,hendpoint⟩:=CenteredMomentEnergyLiveClippingDefectIV.endpoint_threshold b (rho/100)
    (by positivity)
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop Z₀] with Z hZ hZZ
  refine ⟨hZ.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  rcases CenteredMomentEnergyLiveClippingDefectIV.energy_zero_or_defect s.character s.mask 1 t p
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) X₁ X₂ Z s.radial.keep s.radial.profile s.radial.scale hZ.1 hX₁ hX₂ with hz|hdft
  · exact Or.inl hz
  · apply Or.inr
    have hg:=CenteredMomentEnergyLiveClippingDefectIV.raw_gates_of_defect
      Z s.width X₁ X₂ (∑i,w i) κ (rho/100) hZ.1 hX₁ hX₂
      (hdft.2.trans (hendpoint Z hZZ)) hlarge hcap
    exact hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hg.1 hg.2

end SevenEighths.CenteredMomentEnergyReferenceLiveBoundedIV

end

end OAI

end ExtendedModule28

/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBounded -/
section ExtendedModule29

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBoundedIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLiveBoundedIV CenteredMomentEnergyOriginalSource
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyPhysicalEntry
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
variable (η₀:Character)(θ:α→ RayQuotient.Characters M H)
variable (W:ℝ→ ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)(haslot:0< aslot)
variable (hWs:Function.support W⊆Set.Icc aslot bslot)
variable (w σ freq:α→ ℝ)(hσ:∀i,σ i∈Set.Icc lo hi)
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0< a)
variable (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)

open CenteredMomentEnergyPositiveHighSourceIV

theorem actual_positive_source_entry
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e→ 0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 13/18≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale=0 ∨
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
        (1+|t|+height)^J*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,hstage⟩:=original_reference_power_live (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    (ι:=α) bΦ hbΦ (fun _=> bslot) a b Mcap εdiag ξ saving (fun _=> hbslot) ha (by linarith) hM hεdiag hξ
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  intro degree S
  obtain ⟨J,U,C,hC,hbound⟩:=hstage degree S
  refine ⟨J,U,C,hC,?_⟩
  filter_upwards [hbound,hred] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  rcases hz.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hreference
  · exact Or.inl hzero
  · right
    have hphysical:=hr.2 inp (p.profile 0) (p.profile 1) rfl rfl
      (p.support 0) (p.support 1) (fun _=> le_rfl) s.puncture s.radial s.radial_support
      (balanced_volume_bound M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂ κ Mcap hz.1 hw hκ hcap hs)
      (natural_inverse_scale s Mcap hM)
    have href':energy inp.η (fixedBadMask*idealGenerator s.puncture) 1 inp.t
        inp.W₁ inp.W₂ inp.slots inp.toData.coefficient inp.P inp.Y₁ inp.Y₂
        s.radial.keep s.radial.profile s.radial.scale≤
        C*(K+1)*diagonalControl s.radial.profile*(sourceControl U (p.profile 0)*sourceControl U (p.profile 1))^2*
          (1+|t|+height)^J*Z^(s.width+e+ε):=hreference
    apply hphysical.trans
    have hh:=add_le_add_left (mul_le_mul_of_nonneg_left href' (by norm_num : (0:ℝ)≤2))
      (2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving)))
    convert hh using 1 <;> ring
end SevenEighths.CenteredMomentEnergyPositiveHighSourceBoundedIV

end

end OAI

end ExtendedModule29

/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighAssemblyBounded -/
section ExtendedModule30

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighAssemblyBoundedIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceIV (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetricIV (balanced_four_scale_gates)
open CenteredMomentEnergyPositiveHighSourceBoundedIV CenteredMomentEnergyOriginalHighReflectionSymmetricBoundedIV
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyPositiveHighAssemblyIV (low_restrict)

theorem actual_high_source_split
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d L:ℝ,0< d ∧ 0≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃Ju Jr:ℕ,∃Uu Ur:Finset (ℕ×ℕ),∃Cu Cr:ℝ,0< Cu ∧ 0< Cr ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ e→ 0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 13/18≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cu*(K+1)*diagonalControl s.radial.profile*(sourceControl Uu (p.profile 0)*sourceControl Uu (p.profile 1))^2*
          (1+|t|+height)^Ju*Z^(s.width+e+ε) ∨
      (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(sourceControl Ur (p.profile 0)*sourceControl Ur (p.profile 1))^2*
        (1+|t|+height)^Jr*Z^(s.width+e+ε) :=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuR,hLu,hLuUpper,hustage⟩:=original_unbalanced_from_low (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirR,hLr,hLrUpper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrstage⟩:=
    actual_positive_source_entry (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨min du dr,max Lu Lr,lt_min hdu hdr,?_,max_le hLuUpper hLrUpper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  · exact (show 0≤ Lu by linarith).trans (le_max_left _ _)
  intro degree S
  obtain ⟨Ju,Uu,Cu,hCu,hu⟩:=hustage degree S
  obtain ⟨Jr,Ur,Cr,hCr,hr⟩:=hrstage degree S
  refine ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,?_⟩
  filter_upwards [hu,hr] with Z hzu hzr
  refine ⟨hzu.1,?_⟩
  intro e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hlu:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lu
    Lslot lo hi Mcap e e κ Z η₀ Q degree S K hzu.1.le (le_max_left _ _) le_rfl hK hlow
  have hlr:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lr
    Lslot lo hi Mcap e e κ Z η₀ Q degree S K hzu.1.le (le_max_right _ _) le_rfl hK hlow
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
  · left
    exact hzu.2 e Lslot κ η₀ Q K he hK hlu θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · have hfour:=balanced_four_scale_gates Z s.width X₁ X₂ hzu.1 (hrho.trans_le hslo)
      hX₁ hX₂ (le_of_lt (lt_of_not_ge hshort))
    rcases hzr.2 e Lslot κ η₀ Q K he hK hlr θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hsource
    · left
      rw [hzero]
      have hd:=diagonalControl_nonneg s.radial.profile
      have hz:=zero_lt_one.trans hzu.1
      positivity
    · exact Or.inr ⟨⟨hfour.1,hfour.2.1,hfour.2.2.1,hfour.2.2.2.1⟩,hsource⟩
end SevenEighths.CenteredMomentEnergyPositiveHighAssemblyBoundedIV

end

end OAI

end ExtendedModule30

/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighBound -/
section ExtendedModule31

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighBoundIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyPositiveHighSourceIV (balancedInput)
open CenteredMomentEnergyOriginalHighReflectionSymmetricIV (balanced_four_scale_gates)
open CenteredMomentEnergyPositiveHighSourceBoundedIV CenteredMomentEnergyOriginalHighReflectionSymmetricBoundedIV
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyPositiveHighAssemblyIV (low_restrict)

open CenteredMomentEnergyPositiveHighAssemblyBoundedIV CenteredMomentEnergyPositiveHighParametersIV
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyNaturalInputMatches

theorem actual_high_from_physical
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃L:ℝ,0≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0< Cfixed ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e emass efinal Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K Cmass:ℝ),
        0≤ e→0≤ K→0≤ Cmass→e+ε≤ efinal→emass≤ efinal→εdiag≤ efinal→-saving≤ efinal→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 13/18≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      ((Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) →
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp≤
          Cmass*(p.control Smass)^2*(1+|t|+height)^Jmass*Z^(s.width+emass)) →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|+height)^Jout*Z^(s.width+efinal) :=by
  obtain ⟨d,L,hd,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hstage⟩:=
    actual_high_source_split (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨L,hL,hLupper,Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,hbound⟩:=hstage degree S
  let U:Finset (ℕ×ℕ):=insert (0,0) (Smass∪Uu∪Ur)
  let Jout:ℕ:=Jmass+Ju+Jr
  let P:ℝ:=(profileBound Wslot hcSlot aslot bslot lo hi haslot hsSlot)^(2*Fintype.card α)
  let D:ℝ:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ctail*P*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤ P:=pow_nonneg (zero_le_one.trans
    (profileBound_ge_one Wslot hcSlot aslot bslot lo hi haslot hsSlot)) _
  have hD:0≤ D:=by dsimp [D];positivity
  have hT:0≤ T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0< Cfixed:=by dsimp [Cfixed];positivity
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Lslot κ η₀ Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hlarge hcap
  dsimp only
  intro hphysical
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hh:=hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi
    hheight hfreq hκ s hQ hwidthLo hwidth p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hscale:0≤ s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  let F:ℝ:=(p.control U)^2*(1+|t|+height)^Jout*Z^(s.width+efinal)
  have hF:0≤ F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤ Jout)(hej:ej≤ efinal):
      (p.control Sj)^2*(1+|t|+height)^jj*Z^(s.width+ej)≤ F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show s.width+ej≤ s.width+efinal by linarith)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤ Jout:=by dsimp [Jout];omega
  have hjr:Jr≤ Jout:=by dsimp [Jout];omega
  have hjm:Jmass≤ Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1)≤ Cfixed*(K+Cmass+1):=by
    dsimp [Cfixed]
    nlinarith only [hCr.le,hD,hT,hK,mul_nonneg hCr.le hK,mul_nonneg hD hK,mul_nonneg hT hK,
      mul_nonneg hCmass hCfixed.le]
  rcases hh with hunbalanced|⟨hfour,hsource⟩
  · change _≤ Cu*(K+1)*diagonalControl s.radial.profile*(p.control Uu)^2*
        (1+|t|+height)^Ju*Z^(s.width+e+ε) at hunbalanced
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤ Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hmass:=hphysical hfour
    have hmEnv:=henv Smass Jmass emass hm hjm hmassFinal
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        CenteredMomentAmplificationChildInput.volume inp≤ Cmass*F:=by
      apply hmass.trans
      convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤ P*(p.control U)^2:=by
      have hc:=balanced_control (α:=α) M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
        (Fintype.card α) le_rfl U
      have h00:(0,0)∈U:=Finset.mem_insert_self _ _
      simpa only [Finset.insert_eq_of_mem h00] using hc
    have hheight1:1≤(1+|t|+height)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤ efinal):s.radial.scale*Z^x≤ Z^(s.width+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by unfold NaturalState.width;linarith [s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤ c)(hA:0≤ A)(hx:x≤ efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤ c*P*A*F:=by
      calc
        _≤ c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
        _≤ c*(P*(p.control U)^2)*A*Z^(s.width+efinal):=by gcongr;exact hscalePower x hx
        _≤ c*P*A*F:=by
          calc
            _ = (c*P*A*(p.control U)^2*Z^(s.width+efinal))*1 := by ring
            _ ≤ (c*P*A*(p.control U)^2*Z^(s.width+efinal))*
                (1+|t|+height)^Jout := mul_le_mul_of_nonneg_left hheight1 (by positivity)
            _ = c*P*A*F := by dsimp [F]; ring
    have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) hdiagFinal
    have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) htailFinal
    have hrEnv:=henv Ur Jr (e+ε) hr hjr hefinal
    have href:=mul_le_mul_of_nonneg_left hrEnv (show 0≤2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
    have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
      (show 0≤2*diagonalControl s.radial.profile by positivity)
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤ Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu.le,hK,mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _≤ Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+|t|+height)^Jout*Z^(s.width+efinal)
    dsimp [D,T,F] at hsum href hfinish
    change _≤_ at hsum
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+|t|+height)^Jr*Z^(s.width+(e+ε)))≤_ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+|t|+height)^Jr*Z^(s.width+e+ε)≤_
    have hex:s.width+e+ε=s.width+(e+ε):=by ring
    rw [hex]
    nlinarith only [hsum,href,hfinish]

end SevenEighths.CenteredMomentEnergyPositiveHighBoundIV

end

end OAI

end ExtendedModule31

/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighSourceBound -/
section ExtendedModule32

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighSourceBoundIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentInductionEnergy CenteredMomentPrimeSlot
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceLowBands
open CenteredMomentFiniteProfileExceptional
open CenteredMomentFirstSourceReduction CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyPositiveHighSourceIV (balancedInput)
open CenteredMomentEnergyPositiveHighBoundIV CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyPositiveHighAssemblyIV (low_restrict)
def PhysicalHighAt (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (a b bΦ Bmask L Lslot rho Mcap κ ξ e Z:ℝ)(ha:0< a)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(η₀:Character)(Q:Ideal O)
    (S:Finset (ℕ×ℕ))(J:ℕ)(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ freq:T→ℝ)(t height:ℝ),
    (∀i,0≤ w i)→(∀i,w i≤ Lslot)→∀hσlo:∀i,lo≤σ i,∀hσhi:∀i,σ i≤ hi,
    0≤ height→(∀i,|freq i|≤ height)→
  ∀state:NaturalState Z Bmask bΦ,state.fixedModulus=internalQ Q η₀→ rho≤ state.width→state.width≤ Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,∀hX₁:0< X₁,∀hX₂:0< X₂,
    X₁≤ Z^L→X₂≤ Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ state.width→
    5*state.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
    let inp:=balancedInput M H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂;
    (Z^(state.width/4)≤ inp.X₁ ∧ Z^(state.width/4)≤ inp.X₂ ∧
      Z^(state.width/4)≤ inp.Y₁ ∧ Z^(state.width/4)≤ inp.Y₂)→
    physicalMass inp state.puncture 1 fixedBadMask 1 (Ψ T) state.radial.scale Z ξ/volume inp≤
      C*(p.control S)^2*(1+|t|+height)^J*Z^(state.width+e)

def PositiveHighAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi rho Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤ w i)→(∀i,w i≤ Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤ hi)→
    0≤ height→(∀i,|v i|≤ height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→ rho≤ s.width→s.width≤ Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0< X₁→0< X₂→X₁≤ Z^L→X₂≤ Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
    5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=> primePool M H bslot (Z^(w i)))
      (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=> Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

theorem actual_high_stage_from_physical
    (W:ℝ→ℂ)(hW:Continuous W)(aslot bslot lo hi a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)
    (hrho:0< rho)(hε:0<ε)(hMcap:0≤ Mcap)(hBmask:0≤ Bmask)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃Ψ:(T:Finset α)→𝓢(ℝ,ℂ),
      (∀T,Function.support (Ψ T:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1)) ∧
      (∀T x,0≤(Ψ T x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0< Cfixed ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀(L Lslot κ e emass efinal:ℝ)(η₀:Character)(Q:Ideal O)(K Cphysical:ℝ),
      13/18≤κ→0≤ e→0≤ K→0≤ Cphysical→e+ε≤ efinal→emass≤ efinal→εdiag≤ efinal→-saving≤ efinal→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask (Mcap+Bmask+rho/100)
        Lslot lo hi Mcap e κ Z η₀ Q degree S K→
      PhysicalHighAt (α:=α) M H hH W hW aslot bslot lo hi haslot hWs
        a b bΦ Bmask L Lslot rho Mcap κ ξ emass Z ha Ψ η₀ Q Smass Jmass Cphysical→
      PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho Mcap efinal κ Z η₀ Q
        Jout U (Cfixed*(K+Cphysical+1)):=by
  have hfixed (T:Finset α):=actual_high_from_physical (α:=T) M H hH W aslot bslot lo hi
    haslot hWs hW a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε
    hMcap hBmask hbslot hεdiag hξ
  choose Lj hLj hLjcap Ψ hΨs hΨn hj using hfixed
  refine ⟨Ψ,hΨs,hΨn,?_⟩
  intro degree S Jmass Smass
  have hall (T:Finset α):=hj T degree S Jmass Smass
  choose Jj Uj Cj hCj hbound using hall
  let Jout:ℕ:=∑T:Finset α,Jj T
  let U:Finset (ℕ×ℕ):=Finset.univ.biUnion Uj
  let Cfixed:ℝ:=1+∑T:Finset α,Cj T
  have hCfixed:0< Cfixed:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
    dsimp [Cfixed];linarith
  have hCC (T:Finset α):Cj T≤ Cfixed:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hCj T).le)
      (Finset.mem_univ T)
    dsimp [Cfixed];linarith
  have hJJ (T:Finset α):Jj T≤ Jout:=Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ T)
  have hUU (T:Finset α):Uj T⊆U:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ T,hx⟩
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  have hevent:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr hbound
  filter_upwards [hevent,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro L Lslot κ e emass efinal η₀ Q K Cphysical hκ he hK hCphysical hefinal hmassFinal
    hdiagFinal htailFinal hlow hmass
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hlowT:=CenteredMomentEnergyLowBandSubtype.positiveLowAt_subtype (α:=α) M H hH T
    W bslot a b bΦ Bmask (Mcap+Bmask+rho/100) Lslot lo hi Mcap e κ Z η₀ Q degree S K hlow
  have hlowLj:=low_restrict (α:=T) M H hH W bslot a b bΦ Bmask (Mcap+Bmask+rho/100)
    (Lj T) Lslot lo hi Mcap e e κ Z η₀ Q degree S K hZ1.le (hLjcap T) le_rfl hK hlowT
  have hphys:=hmass T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hwidthLo
    hwidth p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity hlarge
  have hh:=(hZ T).2 e emass efinal Lslot κ η₀ Q K Cphysical he hK hCphysical
    hefinal hmassFinal hdiagFinal htailFinal hlowLj θ w σ freq t height hw hwL hσlo hσhi
    hheight hfreq hκ state hQ hwidthLo hwidth p X₁ X₂ hX₁ hX₂ hlarge hcapacity hphys
  have hc:=hCC T
  have hp:=profile_control_mono p (hUU T)
  have hp0:=p.control_nonneg (Uj T)
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  have hpow:=pow_le_pow_right₀ hbase (hJJ T)
  have hd:=diagonalControl_nonneg state.radial.profile
  have hz:0≤ Z:=zero_le_one.trans hZ1.le
  apply hh.trans
  gcongr

omit [Fintype α] [DecidableEq α] in
theorem positive_from_stages
    (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi rho Mcap e κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(J:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hold:PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho e κ Z η₀ Q J S C)
    (hlow:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J S C)
    (hhigh:PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi rho Mcap e κ Z η₀ Q J S C):
    PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi Mcap e κ Z η₀ Q J S C:=by
  intro T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
    hX₁ hX₂ hcap₁ hcap₂ hcapacity
  by_cases hsmall:s.width≤ rho
  · exact hold T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hsmall p X₁ X₂
      hX₁ hX₂ hcap₁ hcap₂ hcapacity
  by_cases hl:length Z X₁+length Z X₂+(∑i,w i)≤5*s.width/6
  · exact hlow T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂
      hX₁ hX₂ hcap₁ hcap₂ hcapacity hl
  exact hhigh T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ (le_of_not_ge hsmall) hs
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity (le_of_not_ge hl)

end SevenEighths.CenteredMomentEnergyPositiveHighSourceBoundIV

end

end OAI

end ExtendedModule32

/- BEGIN OAI.NumberTheory.DirichletL.Energy.NaturalLowStage -/
section ExtendedModule33

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalLowStageIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyPositiveLowBandSource
open CenteredMomentEnergyNaturalSourceAdmission
open CenteredMomentEnergyPositiveHighParametersIV CenteredMomentEnergyPositiveBalancedAdmissionIV
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParametersIV
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyNaturalLowPhysicalIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyBandMonotonicity

theorem actual_low_from_bands
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)(hΦ:2≤ bΦ)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot κ ε:ℝ)(k:ℕ)
    (hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(13/18:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃Uout:Finset (ℕ×ℕ),∃Jout:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask Lgoal Lslot lo hi Mparent
        (physicalLoss Mglobal B ε k) κ Z η₀ Q Jout Uout (C*(C₀+C₁+1)) ∧
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask Lgoal Mparent
        (physicalLoss Mglobal B ε k) Z Jout Uout (C*(C₀+C₁+1)) :=by
  let r:=reserve Mglobal B ε
  have hκ0:0≤κ:=by linarith
  have hr:0< r:=(bounds Mglobal B κ ε hMg hB hκ0 hε).2.2.2.1
  have hmarg:=margins Mglobal B κ ε hMg hB hκ0 hε k
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hbΦ:0< bΦ:=by linarith
  obtain ⟨Ψ,hΨs,hΨn,Cfixed,hCfixed,hentry⟩:=
    CenteredMomentEnergyPositiveLowSourceControlled.actual_low_stages_from_physical (α:=α)
      M H hH W hW.continuous aslot bslot lo hi a b bΦ Mparent (r/4) (r/4)
      (2*amplification ε+1) haslot hWs hbslot ha hb hbΦ hMp (by positivity) (by positivity)
  obtain ⟨U,J,hphysical⟩:=actual_natural_low_physical (α:=α) M H hH W hW aslot bslot lo hi a b bΦ
    haslot hWs hbslot ha hb Mglobal A B Bmask Mparent Mchild Lgoal Lslot Mchild κ ε k
    hMg hA hB hBm hMp hMc hL hLs hMA hready hκ hbeta hκbeta hε hslot hdrop Ψ degree S
  let Umerge:=S∪U
  let Jmerge:=degree+J
  have hS:S⊆Umerge:=Finset.subset_union_left
  have hU:U⊆Umerge:=Finset.subset_union_right
  have hdeg:degree≤ Jmerge:=Nat.le_add_right _ _
  have hJ:J≤ Jmerge:=Nat.le_add_left _ _
  have halower:a/max 1 b≤ a:=by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
    nlinarith [le_max_left (1:ℝ) b]
  have hlen:Lgoal≤2*max Lgoal Mparent+r/4:=by
    have hh:=le_max_left Lgoal Mparent
    linarith
  refine ⟨insert (0,0) Umerge,Jmerge,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cp,hCp,hphys⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  let Cout:=Cfixed*(Cp+1)+1
  have hCout:0< Cout:=by dsimp [Cout];positivity
  refine ⟨Cout,hCout,?_⟩
  filter_upwards [hentry,hphys] with Z he hp
  refine ⟨hp.1,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
  have hzsmall:=zeroAt_transport (internalQ Q η₀)
    (a/max 1 b) b bΦ Bmask _ Mchild εchild Z
    (a/max 1 b) b 2 0 _ Mchild εchild degree degree S S C₀ C₀ hp.1.le
    le_rfl le_rfl hΦ hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₀ le_rfl hzero
  have hpsmall:=positiveAt_transport (α:=α) M H hH W bslot
    (a/max 1 b) b bΦ Bmask _ Lslot lo hi Mchild εchild κ Z
    (a/max 1 b) b 2 0 _ Mchild εchild η₀ Q degree degree S S C₁ C₁ hp.1.le
    le_rfl le_rfl hΦ hBm le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₁ le_rfl hpos
  have hold:=positiveAt_transport (α:=α) M H hH W bslot
    (a/max 1 b) b bΦ Bmask _ Lslot lo hi Mchild εchild κ Z
    a b bΦ Bmask Lgoal Mchild (physicalLoss Mglobal B ε k) η₀ Q
    degree Jmerge S Umerge C₁ C₁ hp.1.le halower le_rfl le_rfl le_rfl hlen le_rfl
    (hell.trans hmarg.2.1) hdeg hS hC₁ le_rfl hpos
  have hm:=hp.2 εchild C₀ C₁ hell hC₀ hC₁ hzsmall hpsmall
  have hm':PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
      a b bΦ Bmask Lgoal Lslot Mchild Mparent κ (r/4) (physicalLoss Mglobal B ε k)
      Z ha Ψ η₀ Q Umerge Jmerge (Cp*(C₀+C₁+1)):=by
    intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hh:=hm T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hs
      p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
    have hz:0≤ Z:=zero_le_one.trans hp.1.le
    have hcontrol:=profile_control_mono p hU
    have hc0:=p.control_nonneg U
    have hheight1:1≤1+|t|+height:=by linarith [abs_nonneg t]
    apply hh.trans
    gcongr
  have hsave:-(2*amplification ε+1)≤ physicalLoss Mglobal B ε k:=by
    have hs:0< amplification ε:=(bounds Mglobal B κ ε hMg hB hκ0 hε).1
    linarith [hmarg.1]
  have hout:=he.2 Bmask Lgoal Lslot Mchild κ (physicalLoss Mglobal B ε k) η₀ Q Umerge Jmerge
    (Cp*(C₀+C₁+1)) C₁ hκsmall (by positivity) hC₁ hmarg.2.2.1 hsave hold hm'
  have hC:Cfixed*(Cp*(C₀+C₁+1)+1)+C₁≤ Cout*(C₀+C₁+1):=by
    dsimp [Cout]
    nlinarith [mul_nonneg hCfixed.le hC₀,mul_nonneg hCfixed.le hC₁]
  constructor
  · exact CenteredMomentEnergyStageMonotonicity.positiveLowAt_transport (α:=α) M H hH W bslot
      a b bΦ Bmask Lgoal Lslot lo hi Mparent (physicalLoss Mglobal B ε k) κ Z
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) η₀ Q Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.1
  · exact CenteredMomentEnergyStageMonotonicity.zeroLowAt_transport (internalQ Q η₀)
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) Z
      a b bΦ Bmask Lgoal Mparent (physicalLoss Mglobal B ε k) Jmerge Jmerge
      (insert (0,0) Umerge) (insert (0,0) Umerge) _ _ hp.1.le
      le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      (by positivity) hC hout.2

end SevenEighths.CenteredMomentEnergyNaturalLowStageIV

end

end OAI

end ExtendedModule33

/- BEGIN OAI.NumberTheory.DirichletL.Energy.CappedLowStage -/
section ExtendedModule34

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedLowStageIV
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyCappedRequests CenteredMomentEnergySourceCapSchedule
open CenteredMomentNaturalFixedRaySource
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_capped_low
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hW:ContDiff ℝ ∞ W)(haslot:0< aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hbslot:0≤ bslot)
    (ha:0< a)(hb:0≤ b)(hrad:2≤ radial)(hmask:0≤ Bmask)(hMcap:0≤ Mcap)
    (hκ:(13/18:ℝ)≤κ)(hε:0<ε)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(k:ℕ)(hk:k< count Mcap ε)
    (hold:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε k):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀η₀:Character,∀Q:Ideal O,Q≤ M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤ Ideal.span {(72:O)}→
      ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
        PositiveLowAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q J U C ∧
        ZeroLowAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z J U C :=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Ag:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let Lreq:=requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1))
  have hBs:0≤ Bs:=sourceCap_nonneg Mcap Bmask L hMcap hmask _
  have hRange:=range_nonneg Mcap Bmask L hMcap hmask (count Mcap ε)
  have hAg:0≤ Ag:=by dsimp [Ag];positivity
  have hMp:0≤ Mp:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε (k+1)
  have hMc:0≤ Mc:=bandWidth_nonneg Mcap Bs ε hMcap hBs hε k
  have hMpCap:Mp≤ Mcap:=bandWidth_le Mcap Bs ε (k+1)
  have hMpAg:Mp≤ Ag:=by dsimp [Ag];linarith
  have hLnext:0≤ lengthAt Mcap Bmask L ε (k+1):=
    range_nonneg Mcap Bmask L hMcap hmask _
  have hLreq:0≤ Lreq:=(request_bounds Mcap Bmask _ hMcap hmask hLnext).1
  have hκ0:0≤κ:=by linarith
  have hbounds:=bounds Mcap Bs κ ε hMcap hBs hκ0 hε
  have hmesh:0≤ fineMesh Mcap Bmask L κ ε:=hbounds.2.2.2.2.1.le
  have hr:0< reserve Mcap Bs ε:=hbounds.2.2.2.1
  have hr4:reserve Mcap Bs ε/4≤1:=by
    have hh:reserve Mcap Bs ε≤ amplification ε/100:=min_le_left _ _
    have hs:=hbounds.2.1
    linarith
  have hready:CenteredMomentEnergyFirstLiveAdmission.readyBudget Ag Bmask≤ Bs:=
    readyBudget_le_schedule Mcap Bmask L ε Ag Bmask hMcap hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤ Mc:=parent_drop Mcap Bs ε hε k
  have hlength:2*max Lreq Mp+reserve Mcap Bs ε/4≤ lengthAt Mcap Bmask L ε k:=
    previous_admits Mcap Bmask L ε Mp (reserve Mcap Bs ε/4) hMcap hmask hMpCap hr4 k hk
  have hsupport:=child_support a b Mcap ε k hk
  obtain ⟨degree,S,hold⟩:=hold
  obtain ⟨U,J,hstage⟩:=CenteredMomentEnergyNaturalLowStageIV.actual_low_from_bands
    (α:=α) M H hH W hW aslot bslot lo hi (lowerAt a b Mcap ε (k+1)) b radial
    haslot hWs hbslot (lowerAt_pos a b Mcap ε ha (k+1)) hb hrad
    Mcap Ag Bs Bmask Mp Mc Lreq (fineMesh Mcap Bmask L κ ε) κ ε k
    hMcap hAg hBs hmask hMp hMc hLreq hmesh hMpAg hready hκ hbeta hκbeta hε
    le_rfl hdrop degree S
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cz,Cp,hCz,hCp,hold⟩:=hold η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cs,hCs,hstage⟩:=hstage η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cs*(Cz+Cp+1),by positivity,?_⟩
  filter_upwards [hold,hstage] with Z hold hs
  have hz:=hold.2.1
  have hp:=hold.2.2
  rw [hsupport] at hz hp
  have hz':ZeroAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) Mc (stageLoss Mcap Bs ε k) Z degree S Cz:=
    zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
      degree degree S S Cz Cz hold.1.le le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl
      le_rfl (Finset.Subset.refl _) hCz.le le_rfl hz
  have hp':PositiveAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)/max 1 b) b radial Bmask
      (2*max Lreq Mp+reserve Mcap Bs ε/4) (fineMesh Mcap Bmask L κ ε) lo hi Mc
      (stageLoss Mcap Bs ε k) κ Z η₀ Q degree S Cp:=
    positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
      _ _ _ _ _ _ _ η₀ Q degree degree S S Cp Cp hold.1.le
      le_rfl le_rfl le_rfl le_rfl hlength le_rfl le_rfl le_rfl (Finset.Subset.refl _)
      hCp.le le_rfl hp
  exact ⟨hs.1,hs.2 (stageLoss Mcap Bs ε k) Cz Cp le_rfl hCz.le hCp.le hz' hp'⟩

end SevenEighths.CenteredMomentEnergyCappedLowStageIV

end

end OAI

end ExtendedModule34

/- BEGIN OAI.NumberTheory.DirichletL.Energy.PositiveHighPhysical -/
section ExtendedModule35

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyPositiveHighPhysicalIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyPositiveHighSourceIV CenteredMomentEnergyPositiveHighSourceBoundIV
open CenteredMomentEnergyPositiveHighParametersIV CenteredMomentEnergyPositiveBalancedAdmissionIV
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParametersIV
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_positive_high_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (_hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(13/18:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalHighAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤ Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0< a0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0< lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0< r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLphys:0≤ max Lgoal Mparent:=hL.trans (le_max_left _ _)
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalHighPhysical.actual_high_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (max Lgoal Mparent) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall hbeta hκbeta N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=> aslot) (fun _=> bslot) (fun _=> hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b)]
    with Z hZZ hfit hclipPow
  have hZ:1< Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0< max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos
    T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlarge
  dsimp only
  intro hfour
  let inp:=balancedInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤ N:=Fintype.card_le_of_injective (fun i:T=> i.val) Subtype.val_injective
  have hm:=balanced_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hu:=four_upper_scales M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ κ (max Lgoal Mparent)
    hZ hw hκ hcapacity (hstate.trans (le_max_right _ _))
  have hp:=fixed_lower_product M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=> le_rfl) (fun _=> le_rfl) (fun _=> rfl) (fun _=> rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu.1 hu.2.1 hu.2.2.1 hu.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl le_rfl hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  rw [ht] at hh
  dsimp only [inp,r] at hh
  have hN1:((1:Ideal O).absNorm:ℝ)=1:=by norm_num
  simpa only [hN1,div_one,mul_assoc] using hh

end SevenEighths.CenteredMomentEnergyPositiveHighPhysicalIV

end

end OAI

end ExtendedModule35

/- BEGIN OAI.NumberTheory.DirichletL.Energy.NaturalHighStage -/
section ExtendedModule36

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalHighStageIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyPositiveHighSourceIV CenteredMomentEnergyPositiveHighSourceBoundIV
open CenteredMomentEnergyPositiveHighParametersIV CenteredMomentEnergyPositiveBalancedAdmissionIV
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins CenteredMomentEnergyFirstSourceParametersIV
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_high_stage
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hrho:0< rho)(hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(13/18:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(lowDegree:ℕ)(Slow:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁ Clow:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→0≤ Clow→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (max Lgoal Mparent)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      CenteredMomentEnergyReferenceLowBands.PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask
        (Mparent+Bmask+rho/100) Lslot lo hi Mparent (physicalLoss Mglobal B ε k) κ Z η₀ Q
        lowDegree Slow Clow→
      PositiveHighAt (α:=α) M H hH W bslot a b bΦ Bmask Lgoal Lslot lo hi rho Mparent
        (reflectedLoss Mglobal B ε k) κ Z η₀ Q J U (C*(C₀+C₁+Clow+1)) := by
  let r:=reserve Mglobal B ε
  have hκ0:0≤κ:=by linarith
  have hb:0≤ b:=zero_le_one.trans hhi
  have hr:0< r:=(bounds Mglobal B κ ε hMg hB hκ0 hε).2.2.2.1
  have hr4:0< r/4:=by positivity
  have hs:0< amplification ε:=(bounds Mglobal B κ ε hMg hB hκ0 hε).1
  obtain ⟨Ψ,hΨs,hΨn,hstage⟩:=actual_high_stage_from_physical (α:=α) M H hH
    W hW.continuous aslot bslot lo hi a b bΦ rho r Mparent Bmask (r/4) (r/4)
    (2*amplification ε+1) haslot hWs hbslot ha hlo hhi hbΦ hrho hr hMp hBm hr4 hr4
  obtain ⟨Up,Jp,hphysical⟩:=CenteredMomentEnergyPositiveHighPhysicalIV.actual_positive_high_physical
    (α:=α) M H hH W hW aslot bslot lo hi a b bΦ haslot hWs hbslot ha hb
    Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε k hMg hA hB hBm hMp hMc hL hLs
    hMA hready hκ hbeta hκbeta hε hslot hdrop Ψ degree S
  obtain ⟨J,U,Cf,hCf,hstageZ⟩:=hstage lowDegree Slow Jp Up
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cp,hCp,hphysZ⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cf*(Cp+1),by positivity,?_⟩
  filter_upwards [hstageZ,hphysZ] with Z hstageNow hphysicalNow
  refine ⟨hphysicalNow.1,?_⟩
  intro εchild C₀ C₁ Clow hchild hC₀ hC₁ hClow hzero hpos hlow
  have hp:=hphysicalNow.2 εchild C₀ C₁ hchild hC₀ hC₁ hzero hpos
  have hm:=margins Mglobal B κ ε hMg hB hκ0 hε k
  have hmass:0≤ Cp*(C₀+C₁+1):=by positivity
  have hh:=hstageNow.2 Lgoal Lslot κ (physicalLoss Mglobal B ε k)
    (physicalLoss Mglobal B ε k) (reflectedLoss Mglobal B ε k) η₀ Q
    Clow (Cp*(C₀+C₁+1)) hκ hm.1.le hClow hmass
    (by exact le_rfl) hm.2.2.2.1 (hm.2.2.1.trans hm.2.2.2.1)
    (by have hpos:=hm.1.le.trans hm.2.2.2.1;linarith only [hpos,hs]) hlow hp
  have hconst:Cf*(Clow+Cp*(C₀+C₁+1)+1)≤(Cf*(Cp+1))*(C₀+C₁+Clow+1):=by
    have hh:0≤ Cp*Clow:=mul_nonneg hCp.le hClow
    nlinarith only [mul_nonneg hCf.le hh,mul_nonneg hCf.le hC₀,mul_nonneg hCf.le hC₁]
  intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hslo hsupper
    p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂ hcapacity hlarge
  apply (hh T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hslo hsupper
    p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂ hcapacity hlarge).trans
  have hd:=diagonalControl_nonneg state.radial.profile
  have hp0:=p.control_nonneg U
  have hz:0≤ Z:=zero_le_one.trans hphysicalNow.1.le
  gcongr

end SevenEighths.CenteredMomentEnergyNaturalHighStageIV

end

end OAI

end ExtendedModule36

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ZeroGrowthPhysical -/
section ExtendedModule37

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalIV
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound CenteredMomentSecondHeightFamily
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentEnergyZeroGrowthPhysicalReindex CenteredMomentSourceInputReindex
open CenteredMomentEnergyZeroBalancedAdmission CenteredMomentEnergyZeroBalancedDictionary
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyFirstSourceParametersIV CenteredMomentEnergyFirstLiveAdmission
open CenteredMomentEnergyCanonicalHighPhysical CenteredMomentEnergyZeroGrowthSource
open CenteredMomentEnergyStageMargins CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyFirstGaussianProfileWeights CenteredMomentFirstAmplifiedFourCoefficients
open CenteredMomentSecondInputCapacitySource CenteredMomentFirstSourceReduction
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_growth_physical
    (Wslot:ℝ→ℂ)(aslot bslot Lslot lo hi κ a b bΦ Bmask Lgoal Lchild Mparent Mchild
      Mschedule Bschedule ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support Wslot⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ Wslot)(hLs:0≤ Lslot)(hκ:(13/18:ℝ)≤κ)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (ha:0< a)(hb:0≤ b)(hBmask:0≤ Bmask)(hLgoal:0≤ Lgoal)(hLchild:0≤ Lchild)
    (hMparent:0≤ Mparent)(hMchild:0≤ Mchild)(hMschedule:0≤ Mschedule)(hBschedule:0≤ Bschedule)
    (hε:0<ε)(hcap: max Mparent (2*Lgoal)≤ Lchild)
    (hready:readyBudget (max Mparent (2*Lgoal)) Bmask≤ Bschedule)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (Ψ:𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃Uprofile:Finset (ℕ×ℕ),∃Jheight:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∃Z₀:ℝ,1< Z₀ ∧ ∀Z:ℝ,Z₀≤ Z→
    ∀(k:ℕ)(εchild C₀ C₁ rho:ℝ),εchild≤ stageLoss Mschedule Bschedule ε k→
      0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 Lchild Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH Wslot bslot (a/max 1 b) b 2 0 Lchild Lslot lo hi
        Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalGrowthAt (internalQ Q η₀) a b bΦ Bmask Lgoal rho Mparent
        (reserve Mschedule Bschedule ε/4) (physicalLoss Mschedule Bschedule ε k)
        Z ha Ψ Uprofile Jheight (C*(C₀+C₁+1)):=by
  let A:=max Mparent (2*Lgoal)
  let r:=reserve Mschedule Bschedule ε
  have hA:0≤ A:=hMparent.trans (le_max_left _ _)
  obtain ⟨hsigma,hsigma1,hr,hxiSigma,hxi1,hes,hes1,hem,hmesh,hmeshEta,heta0,heta,hSaving,hSeed⟩:=
    parameter_gates Mschedule A Bschedule κ ε hMschedule hA hBschedule hκ hε
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have ha2:0< a^2:=sq_pos_of_pos ha
  obtain ⟨U,J,hphysical⟩:=actual_high_physical (α:=α) M H hH
    Wslot aslot bslot Mchild Lslot (r/4) lo hi κ a b 1
    (maskEpsilon Mschedule Bschedule ε) (by norm_num) hem ha hb
    Lchild hLchild degree S haslot hWs hW hMchild hLs hr hκsmall hbeta hκbeta
    0 1 1 (a^2) (r/4) (by norm_num) (by norm_num) ha2 hr
    (fun _=>1) (fun _=>1) (fun _=> by norm_num)
    (sourceEpsilon Mschedule A Bschedule ε) (r/4) (r/4) (A+1) (r/4)
    (2*amplification ε+1) hes hr hr hr
    (amplification ε) hsigma hxiSigma A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBmask heta hr hsigma1 hxi1 hr hes1 le_rfl (fun _=>Ψ) (r/4) (a*a)
    hr (mul_pos ha ha)
  have hfit:=eventually_actual_four_fit Mschedule A Bmask Bschedule κ ε
    hMschedule hA hBmask hBschedule hready hκ hε
  have hclip:∀ᶠZ:ℝ in atTop,1< Z ∧ Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    filter_upwards [eventually_gt_atTop (1:ℝ),
      (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<2*(r/4) by linarith)))
        (max 1 b*max 1 b)] with Z hZ hz
    exact ⟨hZ,(Real.logb_le_iff_le_rpow hZ (mul_pos
      (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _)))).mpr hz⟩
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Zbase,hZbase,hphysical⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Znum,hZnum⟩:=Filter.eventually_atTop.mp (hfit.and hclip)
  refine ⟨C,hC,max Zbase Znum,hZbase.trans_le (le_max_left _ _),?_⟩
  intro Z hZZ k εchild C₀ C₁ rho hchild hC₀ hC₁ hzero hpos
  have hZbaseLe:Zbase≤ Z:=(le_max_left _ _).trans hZZ
  have hn:=hZnum Z ((le_max_right _ _).trans hZZ)
  have hZ:1< Z:=hn.1.1
  intro s hQ hsLower hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂ hlarge
  dsimp only
  intro hfour
  let src:=emptyBalanced s p ha t X₁ X₂ hX₁ hX₂ α
  let θ:(∅:Finset α)→RayQuotient.Characters M H:=fun i=> isEmptyElim i
  have hmatch:CenteredMomentAllocatedRayDictionary.Matches M H hH src η₀ θ
      (fun _=>0) (fun _=>0) (fun _=>0) Wslot bslot Z:=by
    constructor <;> intro i <;> exact isEmptyElim i
  have hupper:=four_upper_scales s p ha t X₁ X₂ hX₁ hX₂ Mparent Lgoal hZ hLgoal hs hc₁ hc₂
  have hu:Z^A≤ Z^Lchild:=Real.rpow_le_rpow_of_exponent_le hZ.le hcap
  have hgate:=declared_capacity s p ha t X₁ X₂ hX₁ hX₂ hZ
  have hdecl:=declared_capacity_upper s X₁ X₂ Mparent Lgoal hZ hLgoal hs hc₁ hc₂
  have hK:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  have hbound:=hphysical ∅ θ Z hZbaseLe εchild C₀ C₁ hC₀ hC₁ hzero hpos
    (fun _=>0) (fun _=>0) (fun _=>0) 0 (mesh Mschedule Bschedule κ ε) hmesh.le
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i) (by norm_num)
    (fun i=> isEmptyElim i) src hmatch
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i)
    (fun i=> isEmptyElim i) (by simp) le_rfl le_rfl
    hb hb (le_max_right _ _) (le_max_right _ _) (by simp)
    s.puncture 1 s.puncture_ne_zero s.puncture_bound squarefree_one one_ne_zero
    s.radial.scale hK.1 p rfl rfl
    (hupper.1.trans hu) (hupper.2.1.trans hu) (hupper.2.2.1.trans hu) (hupper.2.2.2.trans hu)
    (max s.width (length Z X₁+length Z X₂)) s.width (r/4)
    (columnLoss Mschedule Bschedule ε k) hr.le hdecl
    (by
      change length Z X₁+length Z X₂+6*κ*(∑i:(∅:Finset α),(0:ℝ))≤_
      simpa only [Finset.sum_const_zero,mul_zero,add_zero] using
        le_max_right s.width (length Z X₁+length Z X₂))
    (hgate.2.1.trans (le_max_left _ _)) hgate.2.1 (by linarith)
    hn.2.2 (by simp [lowerFactor]) (le_max_left _ _)
    hfour.1 hfour.2.1 hfour.2.2.1 hfour.2.2.2 (hn.1.2 k εchild hchild)
  rw [show physicalMass src s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z (r/4)=
      physicalMass (CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂)
        s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z (r/4) from
        empty_balanced_mass s p ha t X₁ X₂ hX₁ hX₂ _ _ _ _ _ _ _ _] at hbound
  rw [show volume src=X₁*X₂ from empty_balanced_volume s p ha t X₁ X₂ hX₁ hX₂] at hbound
  have heq:max s.width (length Z X₁+length Z X₂)+columnLoss Mschedule Bschedule ε k+r/4=
      max s.width (length Z X₁+length Z X₂)+physicalLoss Mschedule Bschedule ε k:=by
    dsimp only [r]
    rw [add_assoc,columnLoss_physical]
  simpa only [map_one,Nat.cast_one,div_one,add_zero,
    show (src).t=t from rfl,heq] using hbound

end SevenEighths.CenteredMomentEnergyZeroGrowthPhysicalIV

end

end OAI

end ExtendedModule37

/- BEGIN OAI.NumberTheory.DirichletL.Energy.NaturalZeroStage -/
section ExtendedModule38

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyNaturalZeroStageIV
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyBandMonotonicity
open CenteredMomentEnergyStageMonotonicity CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentNaturalFixedRaySource
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_zero_stage
    (W:ℝ→ℂ)(aslot bslot Lslot lo hi κ a b bΦ Bmask Lgoal Mparent Mchild
      Mschedule Bschedule ε rho:ℝ)(k:ℕ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hLs:0≤ Lslot)(hκ:(13/18:ℝ)≤κ)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:2≤ bΦ)(hBmask:0≤ Bmask)(_hLgoal:0≤ Lgoal)
    (hMparent:0≤ Mparent)(hMchild:0≤ Mchild)(hMschedule:0≤ Mschedule)(hBschedule:0≤ Bschedule)
    (hε:0<ε)(hrho:0< rho)(hrhoChild:rho≤ Mchild)
    (hdrop:Mparent-amplification ε/2≤ Mchild):
    ∃d Lgrow Llow:ℝ,0< d ∧ d≤1 ∧ 0< Lgrow ∧ Lgoal≤ Lgrow ∧
      Lgrow=max Lgoal (Mparent+Bmask+2*d)+1 ∧
      Llow=max Lgrow (Mparent+Bmask+rho/100) ∧
      Llow≤ max Lgoal (Mparent+Bmask+rho/100+2)+1 ∧
    ∀Lchild:ℝ,0≤ Lchild→max Mparent (2*Lgrow)≤ Lchild→
      readyBudget (max Mparent (2*Lgrow)) Bmask≤ Bschedule→
    ∀degree degreeLow:ℕ,∀S Slow:Finset (ℕ×ℕ),∃J:ℕ,∃U:Finset (ℕ×ℕ),
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁ Clow:ℝ,εchild≤ stageLoss Mschedule Bschedule ε k→
      0≤ C₀→0≤ C₁→0≤ Clow→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b bΦ Bmask Lchild Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b bΦ Bmask Lchild Lslot lo hi
        Mchild εchild κ Z η₀ Q degree S C₁→
      ZeroLowAt (internalQ Q η₀) a b bΦ Bmask Llow Mparent
        (physicalLoss Mschedule Bschedule ε k) Z degreeLow Slow Clow→
      ZeroAt (internalQ Q η₀) a b bΦ Bmask Lgoal Mparent
        (stageLoss Mschedule Bschedule ε (k+1)) Z J U (C*(Clow+C₀+C₁+1)):=by
  let r:=reserve Mschedule Bschedule ε
  have hκ0:0≤κ:=by linarith
  have hr:0< r:=(bounds Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε).2.2.2.1
  have hb:0≤ b:=by linarith
  have hrad:0< bΦ:=by linarith
  obtain ⟨d,Lgrow,hd,hd1,hLg,hgoal,hLexact,hLupper,hsharp⟩:=
    CenteredMomentEnergyZeroGrowthContourBounded.zero_from_growth_additional_loss_bounded
      a b bΦ r Mparent Bmask Lgoal ha hlo hhi hrad hr hMparent hBmask
  let Llow:=max Lgrow (Mparent+Bmask+rho/100)
  refine ⟨d,Lgrow,Llow,hd,hd1,hLg,hgoal,hLexact,rfl,?_,?_⟩
  · apply max_le
    · apply hLupper.trans
      exact add_le_add (max_le_max (le_refl Lgoal)
        (show Mparent+Bmask+2≤ Mparent+Bmask+rho/100+2 by linarith only [hrho])) (le_refl (1:ℝ))
    · have hh:=le_max_right Lgoal (Mparent+Bmask+rho/100+2)
      linarith
  intro Lchild hLc hcap hready degree degreeLow S Slow
  obtain ⟨Ψ,hsΨ,hnΨ,hgrowth⟩:=
    CenteredMomentEnergyZeroGrowthSourceControlled.actual_growth_from_physical
      a b bΦ rho r Mparent Bmask (2*Lgrow) Lgrow (r/4) (r/4) (2*amplification ε+1)
      ha hlo hhi hrad hrho hr hMparent hBmask (by positivity) le_rfl (by positivity) (by positivity)
  obtain ⟨Smass,Jmass,hphysical⟩:=
    CenteredMomentEnergyZeroGrowthPhysicalIV.actual_growth_physical (α:=α) M H hH
      W aslot bslot Lslot lo hi κ a b bΦ Bmask Lgrow Lchild Mparent Mchild Mschedule Bschedule ε
      haslot hWs hW hLs hκ hbeta hκbeta ha hb hBmask hLg.le hLc hMparent hMchild
      hMschedule hBschedule hε hcap hready hdrop Ψ degree S
  obtain ⟨Jgrowth,Ugrowth,Cgrowth,hCg,hgrowth⟩:=hgrowth (degree+degreeLow) (S∪Slow) Jmass Smass
  obtain ⟨J,U,Csharp,hCs,hsharp⟩:=hsharp Ugrowth
  refine ⟨J,U,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cmass,hCm,Zmass,hZm,hmass⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  let C:=Csharp*(Cgrowth*(Cmass+2)+1)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  filter_upwards [eventually_ge_atTop Zmass,hgrowth,hsharp] with Z hZmZ hg hs
  have hZ:1< Z:=hZm.trans_le hZmZ
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ Clow hchild hC₀ hC₁ hClow hz hp hl
  have hmarg:=margins Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε k
  have hpLoss:0≤ physicalLoss Mschedule Bschedule ε k:=hmarg.1.le
  have hrLoss:0≤ reflectedLoss Mschedule Bschedule ε k:=hpLoss.trans hmarg.2.2.2.1
  have hlength:Lgrow≤ Lchild:=by linarith [le_max_right Mparent (2*Lgrow)]
  have hap:a/max 1 b≤ a:=div_le_self ha.le (le_max_left _ _)
  have hzero:=zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ 2 0 _ _ _
    degree degree S S C₀ C₀ hZ.le le_rfl le_rfl hbΦ hBmask le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) hC₀ le_rfl hz
  have hpositive:=positiveAt_transport (α:=α) M H hH W bslot _ _ _ _ _ _ _ _ _ _ κ Z
    _ _ 2 0 _ _ _ η₀ Q degree degree S S C₁ C₁ hZ.le
    le_rfl le_rfl hbΦ hBmask le_rfl le_rfl le_rfl le_rfl (Finset.Subset.refl _) hC₁ le_rfl hp
  have hmassNow:=hmass Z hZmZ k εchild C₀ C₁ rho hchild hC₀ hC₁ hzero hpositive
  have hprevious:=zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z a b bΦ Bmask Lgrow rho
    (reflectedLoss Mschedule Bschedule ε k) degree (degree+degreeLow) S (S∪Slow) C₀ C₀
    hZ.le hap le_rfl le_rfl le_rfl hlength hrhoChild
    (hchild.trans (hmarg.2.1.trans hmarg.2.2.2.1)) (Nat.le_add_right _ _)
    Finset.subset_union_left hC₀ le_rfl hz
  have hlow:=zeroLowAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    degreeLow (degree+degreeLow) Slow (S∪Slow) Clow Clow hZ.le
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (Nat.le_add_left _ _)
    Finset.subset_union_right hClow le_rfl hl
  have hgrowthNow:=hg.2 (physicalLoss Mschedule Bschedule ε k)
    (physicalLoss Mschedule Bschedule ε k) (reflectedLoss Mschedule Bschedule ε k)
    (internalQ Q η₀) Clow (Cmass*(C₀+C₁+1)) C₀ hpLoss hClow (by positivity) hC₀
    (by unfold reflectedLoss;exact le_rfl) hmarg.2.2.2.1
    (hmarg.2.2.1.trans hmarg.2.2.2.1)
    (by have hh:= (bounds Mschedule Bschedule κ ε hMschedule hBschedule hκ0 hε).1
        linarith only [hrLoss,hh]) hprevious hlow hmassNow
  have hfinal:=hs.2 (reflectedLoss Mschedule Bschedule ε k) (internalQ Q η₀) Jgrowth
    (Cgrowth*(Clow+Cmass*(C₀+C₁+1)+C₀+1)) hrLoss (by positivity) hgrowthNow
  rw [reflected_then_zero] at hfinal
  have hfront:Csharp*(Cgrowth*(Clow+Cmass*(C₀+C₁+1)+C₀+1)+1)≤ C*(Clow+C₀+C₁+1):=by
    have hinner:Clow+Cmass*(C₀+C₁+1)+C₀+1≤(Cmass+2)*(Clow+C₀+C₁+1):=by
      nlinarith [mul_nonneg hCm.le hClow]
    calc
      _≤ Csharp*(Cgrowth*((Cmass+2)*(Clow+C₀+C₁+1))+(Clow+C₀+C₁+1)):=by
        gcongr
        linarith
      _=_:=by dsimp [C];ring
  exact zeroAt_transport (internalQ Q η₀) _ _ _ _ _ _ _ Z _ _ _ _ _ _ _
    J J U U _ _ hZ.le le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl (Finset.Subset.refl _) (by positivity) hfront hfinal

end SevenEighths.CenteredMomentEnergyNaturalZeroStageIV

end

end OAI

end ExtendedModule38

/- BEGIN OAI.NumberTheory.DirichletL.Energy.CappedAnalyticSuccessor -/
section ExtendedModule39

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessorIV
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyPositiveHighBoundIV
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthInduction (remaining lowerAt lengthAt lowerAt_pos child_support child_length)
open CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyStageMonotonicity
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyCappedRequests
open CenteredMomentEnergySourceCapSchedule CenteredMomentNaturalFixedRaySource
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_successor
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hrad:2≤ radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ:(13/18:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκbeta:2*HeckeZeroSupremum.beta-1≤κ)
    (k:ℕ)(hk:k< count Mcap ε)
    (hold:CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (k+1):=by
  let Bs:=finalSourceCap Mcap Bmask L ε
  let Mp:=bandWidth Mcap Bs ε (k+1)
  let Mc:=bandWidth Mcap Bs ε k
  let ac:=lowerAt a b Mcap ε (k+1)
  let Lc:=lengthAt Mcap Bmask L ε (k+1)
  let Lp:=lengthAt Mcap Bmask L ε k
  let Lreq:=requestLength Mcap Bmask Lc
  let A:=2*range Mcap Bmask L (count Mcap ε)+Mcap+1
  let r:=reserve Mcap Bs ε
  have hBs:0≤ Bs:=sourceCap_nonneg Mcap Bmask L hMcap.le hmask _
  have hκ0:0≤κ:=by linarith
  have hb:0≤ b:=zero_le_one.trans hhi
  have hr:0< r:=(bounds Mcap Bs κ ε hMcap.le hBs hκ0 hε).2.2.2.1
  have hr1:r/4≤1:=by
    have hh:=bounds Mcap Bs κ ε hMcap.le hBs hκ0 hε
    have hrs:r≤ amplification ε/100:=min_le_left _ _
    linarith [hh.2.1]
  have hMp:0≤ Mp:=bandWidth_nonneg Mcap Bs ε hMcap.le hBs hε _
  have hMc:0< Mc:=band_positive Mcap Bs ε hMcap hBs hε k
  have hMpM:Mp≤ Mcap:=bandWidth_le _ _ _ _
  have hMcM:Mc≤ Mcap:=bandWidth_le _ _ _ _
  have hac:0< ac:=lowerAt_pos a b Mcap ε ha _
  have haca:ac≤ a:=CenteredMomentEnergyProfiles.lower_antitone a b ha (Nat.zero_le _)
  have haclo:ac≤1/4:=haca.trans hlo
  have hLc:0≤ Lc:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hLp:0≤ Lp:=range_nonneg Mcap Bmask L hMcap.le hmask _
  have hreq:=request_bounds Mcap Bmask Lc hMcap.le hmask hLc
  have hreqFinal:Lreq≤ range Mcap Bmask L (count Mcap ε):=
    request_le_final Mcap Bmask L ε hMcap.le hmask k hk
  have hRange:=range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)
  have hA:0≤ A:=by dsimp [A];positivity
  have hMA:Mp≤ A:=by dsimp [A];linarith [range_nonneg Mcap Bmask L hMcap.le hmask (count Mcap ε)]
  have hready:readyBudget A Bmask≤ Bs:=
    readyBudget_le_schedule Mcap Bmask L ε A Bmask hMcap.le hmask le_rfl le_rfl
  have hdrop:Mp-amplification ε/2≤ Mc:=parent_drop Mcap Bs ε hε k
  have hmesh:0≤ fineMesh Mcap Bmask L κ ε:=
    (fineMesh_pos Mcap Bmask L κ ε hMcap.le hmask hκ0 hε).le
  have hsupport:lowerAt a b Mcap ε k=ac/max 1 b:=child_support a b Mcap ε k hk
  have hrequest:2*max Lreq Mp+r/4≤ Lp:=previous_admits Mcap Bmask L ε Mp (r/4)
    hMcap.le hmask hMpM hr1 k hk
  have hhighL:max Lc Mp≤ Lp:=by
    have hh:max Lc Mp≤ Lreq:=max_le hreq.2.1 (hMpM.trans hreq.2.2)
    have hg:0≤ max Lreq Mp:=hreq.1.trans (le_max_left _ _)
    have hx:=le_max_left Lreq Mp
    linarith
  have href:Mp+Bmask+Mc/100≤ Lreq:=by
    have hh:=actual_contours Mcap Bmask Lc Mp Mc 0 hMcap.le hmask hMpM hMcM (by norm_num)
    exact (le_max_right _ _).trans hh
  obtain ⟨Jold,Sold,hprev⟩:=hold
  obtain ⟨Slow,Jlow,hlow⟩:=CenteredMomentEnergyCappedLowStageIV.actual_capped_low (α:=α) M H hH
    W aslot bslot a b radial Bmask L lo hi Mcap κ ε hW haslot hWs hbslot ha hb hrad
    hmask hMcap.le hκ hε hbeta hκbeta k hk ⟨Jold,Sold,hprev⟩
  obtain ⟨Uhigh,Jhigh,hhigh⟩:=CenteredMomentEnergyNaturalHighStageIV.actual_high_stage (α:=α) M H hH
    W hW aslot bslot lo hi ac b radial haslot hWs hbslot hac haclo hhi (by linarith)
    Mcap A Bs Bmask Mp Mc Lc (fineMesh Mcap Bmask L κ ε) Mc κ ε k hMc hMcap.le hA hBs hmask
    hMp hMc.le hLc hmesh hMA hready hκ hbeta hκbeta hε le_rfl hdrop Jold Sold Jlow Slow
  obtain ⟨d,Lgrow,Llow,hd,hd1,hLg,hgoal,hLexact,hLlow,hLupper,hzeroStage⟩:=
    CenteredMomentEnergyNaturalZeroStageIV.actual_zero_stage (α:=α) M H hH
      W aslot bslot (fineMesh Mcap Bmask L κ ε) lo hi κ ac b radial Bmask Lc Mp Mc Mcap Bs ε Mc k
      haslot hWs hW hmesh hκ hbeta hκbeta hac haclo hhi hrad hmask hLc hMp hMc.le hMcap.le hBs
      hε hMc le_rfl hdrop
  have hLlowReq:Llow≤ Lreq:=by
    rw [hLlow,hLexact]
    exact actual_contours Mcap Bmask Lc Mp Mc d hMcap.le hmask hMpM hMcM hd1
  have hLgrowLow:Lgrow≤ Llow:=by rw [hLlow];exact le_max_left _ _
  have hLgrowReq:Lgrow≤ Lreq:=hLgrowLow.trans hLlowReq
  have hzeroCap:max Mp (2*Lgrow)≤ Lp:=by
    have hm:Mp≤ Lreq:=hMpM.trans hreq.2.2
    have hh:=le_max_left Lreq Mp
    apply max_le <;> linarith
  have hzeroReady:readyBudget (max Mp (2*Lgrow)) Bmask≤ Bs:=by
    have hc:max Mp (2*Lgrow)≤ A:=by
      apply max_le
      · exact hMA
      · dsimp [A];linarith
    apply le_trans _ hready
    unfold readyBudget
    linarith
  obtain ⟨Jzero,Uzero,hzero⟩:=hzeroStage Lp hLp hzeroCap hzeroReady Jold Jlow Sold Slow
  have hmarg:=margins Mcap Bs κ ε hMcap.le hBs hκ0 hε k
  apply CenteredMomentEnergyCappedSuccessorPacking.certified_from_stages (α:=α) M H hH
    W bslot a b radial Bmask L lo hi Mcap κ ε ha hmask hMcap.le hκ0 hε k
    (stageLoss Mcap Bs ε (k+1)) (physicalLoss Mcap Bs ε k) (reflectedLoss Mcap Bs ε k)
    le_rfl (hmarg.2.2.2.1.trans hmarg.2.2.2.2) hmarg.2.2.2.2 ⟨Jold,Sold,hprev⟩
  · refine ⟨Jzero,Uzero,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Cz,hCz,hzeroZ⟩:=hzero η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Cz*(Clow+C₀+C₁+1),by positivity,?_⟩
    filter_upwards [hprevZ,hlowZ,hzeroZ] with Z hp hl hz
    have hzz:=hp.2.1
    have hpp:=hp.2.2
    rw [hsupport] at hzz hpp
    have hlowRestricted:=zeroLowAt_transport (internalQ Q η₀)
      ac b radial Bmask Lreq Mp (physicalLoss Mcap Bs ε k) Z
      ac b radial Bmask Llow Mp (physicalLoss Mcap Bs ε k) Jlow Jlow Slow Slow Clow Clow
      hp.1.le le_rfl le_rfl le_rfl le_rfl hLlowReq le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.2
    exact hz.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzz hpp hlowRestricted
  · refine ⟨Jlow,Slow,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Clow,hClow,?_⟩
    filter_upwards [hlowZ] with Z hl
    exact positiveLowAt_transport (α:=α) M H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
      ac b radial Bmask Lc Mp (physicalLoss Mcap Bs ε k) η₀ Q Jlow Jlow Slow Slow Clow Clow
      hl.1.le le_rfl le_rfl le_rfl le_rfl hreq.2.1 le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
  · refine ⟨Jhigh,Uhigh,?_⟩
    intro η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨C₀,C₁,hC₀,hC₁,hprevZ⟩:=hprev η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Clow,hClow,hlowZ⟩:=hlow η₀ Q hQM hQ0 hQt hQ72
    obtain ⟨Ch,hCh,hhighZ⟩:=hhigh η₀ Q hQM hQ0 hQt hQ72
    refine ⟨Ch*(C₀+C₁+Clow+1),by positivity,?_⟩
    filter_upwards [hprevZ,hlowZ,hhighZ] with Z hp hl hh
    have hzz:=hp.2.1
    have hpp:=hp.2.2
    rw [hsupport] at hzz hpp
    have hzSmall:=zeroAt_transport (internalQ Q η₀)
      (ac/max 1 b) b radial Bmask Lp Mc (stageLoss Mcap Bs ε k) Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k)
      Jold Jold Sold Sold C₀ C₀ hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC₀.le le_rfl hzz
    have hpSmall:=positiveAt_transport (α:=α) M H hH W bslot
      (ac/max 1 b) b radial Bmask Lp (fineMesh Mcap Bmask L κ ε) lo hi Mc (stageLoss Mcap Bs ε k) κ Z
      (ac/max 1 b) b 2 0 (max Lc Mp) Mc (stageLoss Mcap Bs ε k) η₀ Q
      Jold Jold Sold Sold C₁ C₁ hp.1.le le_rfl le_rfl hrad hmask hhighL le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hC₁.le le_rfl hpp
    have hlRestricted:=positiveLowAt_transport (α:=α) M H hH W bslot
      ac b radial Bmask Lreq (fineMesh Mcap Bmask L κ ε) lo hi Mp (physicalLoss Mcap Bs ε k) κ Z
      ac b radial Bmask (Mp+Bmask+Mc/100) Mp (physicalLoss Mcap Bs ε k) η₀ Q
      Jlow Jlow Slow Slow Clow Clow hp.1.le le_rfl le_rfl le_rfl le_rfl href le_rfl le_rfl le_rfl
      (Finset.Subset.refl _) hClow.le le_rfl hl.2.1
    exact hh.2 _ C₀ C₁ Clow le_rfl hC₀.le hC₁.le hClow.le hzSmall hpSmall hlRestricted

end SevenEighths.CenteredMomentEnergyCappedAnalyticSuccessorIV

end

end OAI

end ExtendedModule39

/- BEGIN OAI.NumberTheory.DirichletL.Energy.CertifiedExistence -/
section ExtendedModule40

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentEnergyCertifiedExistenceIV
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyCappedAnalyticSuccessorIV CenteredMomentEnergyCappedRadialTransport
open CenteredMomentEnergyWidthSchedule
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem certified_bands (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(haUpper:a≤1/4)(hb:1≤ b)(hrad:2≤ radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ0:(13/18:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∀k:ℕ,k≤ count Mcap ε→
      CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε k:=by
  intro k
  induction k with
  | zero =>
    intro _
    exact certified_floor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW ha (by linarith) (by linarith) hmask hMcap.le (by linarith) hε hbeta hκ
  | succ k ih =>
    intro hk
    have hprevious:=ih (Nat.le_of_succ_le hk)
    have hstep:k< count Mcap ε:=by omega
    exact actual_successor (α:=α) M H hH W aslot bslot a b radial Bmask L lo hi Mcap κ ε
      haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hκ0 hε hbeta hκ
      k hstep hprevious

theorem terminal_certificate (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (hbslot:0≤ bslot)(ha:0< a)(haUpper:a≤1/4)(hb:1≤ b)(_hrad:0< radial)
    (hmask:0≤ Bmask)(hMcap:0< Mcap)(hκ0:(13/18:ℝ)≤κ)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    CertifiedBand (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε (count Mcap ε):=by
  apply certified_from_max_two (α:=α) M H hH W bslot a b radial Bmask L lo hi Mcap κ ε
  exact certified_bands (α:=α) M H hH W aslot bslot a b (max 2 radial) Bmask L lo hi Mcap κ ε
    haslot hWs hW hbslot ha haUpper hb (le_max_left _ _) hmask hMcap hκ0 hε hbeta hκ _ le_rfl

end SevenEighths.CenteredMomentEnergyCertifiedExistenceIV

end

end OAI

end ExtendedModule40

#print axioms OAI.SevenEighths.CenteredMomentEnergyCertifiedExistenceIV.terminal_certificate

end PartIVBlock4

/- BEGIN consolidated variable_moments/PhysicalCount.lean -/
section PartIVBlock5
/-! Literal fixed-kappa same-witness crossing arithmetic; no analytic count premise. -/
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RHBootstrapCount
noncomputable section

def D (c u : ℝ) : ℝ := 3-(1+c)*u
def P (c u : ℝ) : ℝ := (2-c*u)*(1-u)
def rstar (c u t : ℝ) : ℝ := ((2-c*u)*t+(c/2-1)*u)/D c u
def invGain (u r : ℝ) : ℝ := u+(1-u)*r
def plainGain (c u t r : ℝ) : ℝ := 2*(t-r)+(c/2)*u*(1-2*(t-r))

lemma D_pos (c u : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (_hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) : 0 < D c u := by
  have hp := mul_nonneg (show 0 ≤ 1+c by linarith) (show 0 ≤ 1/2-u by linarith)
  unfold D
  nlinarith
lemma crossing (c u t : ℝ) (hd : D c u ≠ 0) :
    invGain u (rstar c u t) = plainGain c u t (rstar c u t) := by
  unfold invGain plainGain rstar
  field_simp [hd]
  unfold D
  ring
lemma rstar_lower_half (c u t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) (ht0 : 1 ≤ t) : 1/2 < rstar c u t := by
  have hd := D_pos c u hc0 hc1 hu0 hu1
  apply (lt_div_iff₀ hd).2
  have hcu1 := mul_nonneg hc0.le (show 0 ≤ 1/2-u by linarith)
  have hstep := mul_nonneg (show 0 ≤ 2-c*u by nlinarith) (show 0 ≤ t-1 by linarith)
  unfold D
  nlinarith
lemma rstar_upper_one (c u t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) (ht1 : t ≤ 3/2) : rstar c u t ≤ 1 := by
  have hd := D_pos c u hc0 hc1 hu0 hu1
  apply (div_le_iff₀ hd).2
  have hcu1 := mul_nonneg hc0.le (show 0 ≤ 1/2-u by linarith)
  have hstep := mul_nonneg (show 0 ≤ 2-c*u by nlinarith) (show 0 ≤ 3/2-t by linarith)
  unfold D
  nlinarith
lemma plain_length_bounds (c u t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) (ht0 : 1 ≤ t) (ht1 : t ≤ 3/2) :
    1/3 ≤ t-rstar c u t ∧ t-rstar c u t ≤ 1/2 := by
  have hd := D_pos c u hc0 hc1 hu0 hu1
  have hr : rstar c u t*D c u = (2-c*u)*t+(c/2-1)*u := by
    unfold rstar
    exact div_mul_cancel₀ _ (ne_of_gt hd)
  have hstep0 := mul_nonneg (show 0 ≤ 1-u by linarith) (show 0 ≤ t-1 by linarith)
  have hstep1 := mul_nonneg (show 0 ≤ 1-u by linarith) (show 0 ≤ 3/2-t by linarith)
  have hcu := mul_nonneg (show 0 ≤ 2-c by linarith) hu0
  constructor
  · apply (mul_le_mul_iff_left₀ hd).mp
    unfold D at *
    nlinarith
  · apply (mul_le_mul_iff_left₀ hd).mp
    unfold D at *
    nlinarith
lemma rstar_minimum (c u t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) (ht0 : 1 ≤ t) :
    (6-c)/(10-2*c) ≤ rstar c u t := by
  have hd := D_pos c u hc0 hc1 hu0 hu1
  have hk : 0 < 10-2*c := by linarith
  have hcu1 := mul_nonneg hc0.le (show 0 ≤ 1/2-u by linarith)
  have hstep := mul_nonneg (show 0 ≤ 2-c*u by nlinarith) (show 0 ≤ t-1 by linarith)
  have hh := mul_nonneg (show 0 ≤ 2-c by linarith) (show 0 ≤ 1-2*u by linarith)
  unfold rstar
  apply (div_le_div_iff₀ hk hd).2
  unfold D
  nlinarith
lemma capacity_bounds (c u t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) (ht0 : 1 ≤ t) (ht1 : t ≤ 3/2) :
    (1-rstar c u t)/2 < 1/5 ∧ (c/4)*(1-2*(t-rstar c u t)) < 1/5 := by
  have hr := rstar_minimum c u t hc0 hc1 hu0 hu1 ht0
  have hm := (plain_length_bounds c u t hc0 hc1 hu0 hu1 ht0 ht1).1
  have hk : 0 < 10-2*c := by linarith
  have hmin : (3/5 : ℝ) < (6-c)/(10-2*c) := by
    apply (lt_div_iff₀ hk).2
    linarith
  constructor
  · linarith
  · have hp := mul_nonneg hc0.le (show 0 ≤ t-rstar c u t-1/3 by linarith)
    nlinarith
lemma crossing_maximizes_min (c u t r : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) :
    min (invGain u r) (plainGain c u t r) ≤ invGain u (rstar c u t) := by
  have hd := D_pos c u hc0 hc1 hu0 hu1
  have he := crossing c u t (ne_of_gt hd)
  by_cases hr : r ≤ rstar c u t
  · have hm := mul_nonneg (show 0 ≤ 1-u by linarith) (sub_nonneg.mpr hr)
    exact (min_le_left _ _).trans (by unfold invGain at *; nlinarith)
  · have hcu := mul_nonneg hc0.le (show 0 ≤ 1/2-u by linarith)
    have hm := mul_nonneg (show 0 ≤ 2-c*u by nlinarith) (show 0 ≤ r-rstar c u t by linarith)
    apply (min_le_right _ _).trans
    rw [he]
    unfold plainGain
    nlinarith
lemma short_envelope_identity (c u t : ℝ) (hd : D c u ≠ 0) :
    invGain u (rstar c u t) = 1-P c u*(3/2-t)/D c u := by
  unfold invGain rstar P
  field_simp [hd]
  unfold D
  ring


def J (a c d u : ℝ) : ℝ := (a-d)*D c u+d*P c u
def tstar (a c d u : ℝ) : ℝ := 1+d*P c u/(2*J a c d u)
def countR (a c d u : ℝ) : ℝ := 1-d+(a-d)*d*P c u/(2*J a c d u)
def shortCount (c d u t : ℝ) : ℝ := 1-d+d*P c u*(3/2-t)/D c u
def longCount (a d t : ℝ) : ℝ := 1-a+(a-d)*t
lemma P_pos (c u : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (_hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) : 0 < P c u := by
  have hh := mul_nonneg hc0.le (show 0 ≤ 1/2-u by linarith)
  unfold P
  exact mul_pos (by nlinarith) (by linarith)
lemma J_pos (a c d u : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) (hd0 : 0 ≤ d) (hda : d < a) : 0 < J a c d u := by
  have hp := P_pos c u hc0 hc1 hu0 hu1
  have hD := D_pos c u hc0 hc1 hu0 hu1
  have hh := mul_pos (sub_pos.mpr hda) hD
  have hdp := mul_nonneg hd0 hp.le
  unfold J
  linarith
lemma tstar_range (a c d u : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) (hd0 : 0 ≤ d) (hda : d < a) :
    1 ≤ tstar a c d u ∧ tstar a c d u ≤ 3/2 := by
  have hj := J_pos a c d u hc0 hc1 hu0 hu1 hd0 hda
  have hp := P_pos c u hc0 hc1 hu0 hu1
  have hD := D_pos c u hc0 hc1 hu0 hu1
  have hdp := mul_nonneg hd0 hp.le
  have hratio : 0 ≤ d*P c u/(2*J a c d u) := div_nonneg hdp (by positivity)
  have hbound : d*P c u ≤ J a c d u := by
    have hh := mul_nonneg (sub_nonneg.mpr hda.le) hD.le
    unfold J
    linarith
  have hratio1 : d*P c u/(2*J a c d u) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*J a c d u)).2
    linarith
  unfold tstar
  constructor <;> linarith
lemma balance_identity (a c d u : ℝ) (hd : D c u ≠ 0) (hj : J a c d u ≠ 0) :
    shortCount c d u (tstar a c d u) = longCount a d (tstar a c d u) := by
  unfold shortCount longCount tstar
  field_simp [hd, hj]
  unfold J
  ring
lemma count_identity (a c d u : ℝ) (hj : J a c d u ≠ 0) :
    longCount a d (tstar a c d u) = countR a c d u := by
  unfold longCount tstar countR
  field_simp [hj]
  ring
lemma balance_minimizes_max (a c d u t : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) (hd0 : 0 ≤ d) (hda : d < a) :
    countR a c d u ≤ max (shortCount c d u t) (longCount a d t) := by
  have hD := D_pos c u hc0 hc1 hu0 hu1
  have hp := P_pos c u hc0 hc1 hu0 hu1
  have hj := J_pos a c d u hc0 hc1 hu0 hu1 hd0 hda
  have hb := balance_identity a c d u (ne_of_gt hD) (ne_of_gt hj)
  have hr := count_identity a c d u (ne_of_gt hj)
  by_cases ht : t ≤ tstar a c d u
  · have hs := mul_nonneg (div_nonneg (mul_nonneg hd0 hp.le) hD.le)
        (sub_nonneg.mpr ht)
    apply le_trans _ (le_max_left _ _)
    rw [← hr, ← hb]
    unfold shortCount
    simp only [div_eq_mul_inv] at hs ⊢
