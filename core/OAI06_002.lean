      (Ideal.absNorm χ.modulus : ℝ) ≤ Z^B →
      ∀ X : ℝ, ∀ hX : 0<X, ∀ hret : 1≤X*b, ∀ t : ℝ,
      volumeControl Q χ (CenteredMomentRetainedProfile.retainedProfile
        W a b ha hs (W.smooth ⊤) X hX hret t) ≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*Z^ε*(1+‖t‖)^n := by
  obtain ⟨n,S,hS,hbound⟩ := volumeControl_source_control a b ε B ha hε hB
  refine ⟨n,S,hS,?_⟩
  intro Q
  obtain ⟨C,hC,hCbound⟩ := hbound Q
  refine ⟨(max 1 b)^(pvSeminorms.sup Prod.snd)*C,by positivity,?_⟩
  intro W hs Z hZ χ hχ X hX hret t
  exact (CenteredMomentRetainedProfile.retained_volumeControl_le
    Q χ W a b ha hs (W.smooth ⊤) X hX hret t).trans
    ((mul_le_mul_of_nonneg_left (hCbound W hs Z hZ χ hχ t) (by positivity)).trans_eq (by ring))
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule1450

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalUnit
Source SHA256: 41425d0ccfd3908ca74318e20940dbf413fc739e8b00e0282f07c39c4a9f7b6e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1451


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeTwist
open CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => HeckeFamily.O

theorem rectangle_source_unit (a b ε B : ℝ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁≤1 →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂≤1 →
      ∀ Z : ℝ, 1≤Z → ∀ η χ ψ : Character,
      (Ideal.absNorm χ.modulus:ℝ)≤Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A z : O, ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀ n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0<L →
      L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
        twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
        C*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hvol⟩ := volumeControl_source_control a b ε B ha hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨D,hD,hDvol⟩ := hvol Q
  let V := 128*(b+b)
  have hV : 0≤V := by dsimp [V]; positivity
  refine ⟨1+8*D*V,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ hS₁ hS₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hbound₁ (y:ℝ) : ‖W₁ y‖≤1 :=
    (SchwartzMap.norm_le_seminorm ℝ W₁ y).trans
      ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans hS₁)
  have hbound₂ (y:ℝ) : ‖W₂ y‖≤1 :=
    (SchwartzMap.norm_le_seminorm ℝ W₂ y).trans
      ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans hS₂)
  have herr (W:𝓢(ℝ,ℂ)) (hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
      (hS':S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤1) :
      volumeControl Q χ (normPowerProfile W a b ha hs (W.smooth ⊤) t) ≤
        D*Z^ε*(1+‖t‖)^J := by
    apply (hDvol W hs Z hZ χ hnorm t).trans
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hS' hD.le) (Real.rpow_nonneg (by linarith) _))
        (show 0≤(1+‖t‖)^J by positivity)
  have hraw := actual_twisted_rectangle_saving η χ ψ Q hQ hQψ hind m A z hml hm2 hrow
    W₁ W₂ a b a b 1 1 ha ha hb hb zero_le_one zero_le_one hs₁ hs₂
    (W₁.smooth ⊤) (W₂.smooth ⊤) hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0<T := hpX ▸ mul_pos (hL.trans_le hX₁) (hL.trans_le hX₂)
  have hn := CenteredMoment.normalized_centered_saving _ T L V _ hT (by
    simpa only [mul_one] using hraw)
  have hE := add_le_add (herr W₁ hs₁ hS₁) (herr W₂ hs₂ hS₂)
  have hr : 0≤Real.sqrt T/L := div_nonneg (Real.sqrt_nonneg _) hL.le
  calc
    _ ≤ _ := hn
    _ ≤ 4*(D*Z^ε*(1+‖t‖)^J+D*Z^ε*(1+‖t‖)^J)*V*(Real.sqrt T/L) := by
      gcongr
    _ = (8*D*V)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by ring
    _ ≤ (1+8*D*V)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
      gcongr
      linarith
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule1451

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalNormalize
Source SHA256: 3a9731f3d3f6c45f6198f74599d3a5c09bfc751d40c1d306473b777fa68ff05a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1452


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

def sourceControl (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

def normalizedProfile (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  (sourceControl S W)⁻¹ • W

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤sourceControl S W := apply_nonneg _ _

theorem sourceControl_zero (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (W : 𝓢(ℝ,ℂ)) (hW : sourceControl S W=0) : W=0 := by
  ext x
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact (SchwartzMap.norm_le_seminorm ℝ W x).trans
    ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans_eq hW)

theorem normalizedProfile_control (S) (W : 𝓢(ℝ,ℂ)) :
    sourceControl S (normalizedProfile S W)≤1 := by
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((sourceControl S W)⁻¹ • W)≤1
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (sourceControl_nonneg S W))]
  change (sourceControl S W)⁻¹*sourceControl S W≤1
  by_cases h : sourceControl S W=0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem normalizedProfile_support (S) (W : 𝓢(ℝ,ℂ)) :
    Function.support (normalizedProfile S W:ℝ→ℂ)⊆Function.support (W:ℝ→ℂ) := by
  intro x hx hw
  apply hx
  simp [normalizedProfile,smul_apply,hw]

theorem normalizedProfile_reconstruct (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (W : 𝓢(ℝ,ℂ)) : sourceControl S W • normalizedProfile S W=W := by
  by_cases h : sourceControl S W=0
  · rw [sourceControl_zero S hS W h]
    simp [sourceControl,normalizedProfile]
  · simp [normalizedProfile,smul_smul,h]

theorem twistedIdealSum_profile_smul (χ : Character) (W : 𝓢(ℝ,ℂ))
    (c t X : ℝ) : twistedIdealSum χ (c • W : 𝓢(ℝ,ℂ)) t X = (c:ℂ)*twistedIdealSum χ W t X := by
  unfold twistedIdealSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro I
  change _ * ((c:ℂ) * W _) = (c:ℂ) * (_ * W _)
  ring

theorem twistedIdealSum_normalized (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (χ : Character) (W : 𝓢(ℝ,ℂ)) (t X : ℝ) :
    twistedIdealSum χ W t X = (sourceControl S W:ℂ)*
      twistedIdealSum χ (normalizedProfile S W) t X := by
  rw [←twistedIdealSum_profile_smul,normalizedProfile_reconstruct S hS W]
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule1452

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalRectangle
Source SHA256: da99e36a0e263e9d6d2dbbc04896ab22ecebf80afd722bb157d2a5e3bf98f45d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1453


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeTwist
open CenteredMomentHeckeCancellation CenteredMomentLattice
local notation "O" => HeckeFamily.O

theorem rectangle_source_control (a b ε B : ℝ)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hB : 0≤B) :
    ∃ J : ℕ, ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ Q : Ideal O, Q≠0 → ∃ C : ℝ, 0<C ∧
      ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀ Z : ℝ, 1≤Z → ∀ η χ ψ : Character,
      (Ideal.absNorm χ.modulus:ℝ)≤Z^B → Q≤ψ.modulus →
      CenteredExceptionalProfile.InducedBy χ ψ →
      ∀ m A z : O, ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      (∀ n,elementCoeff χ n=CanonicalRowCompletion.rowTwist
        (HeckeRowClosure.elementHom η) m 1 (A*z) n) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0<L →
      L≤X₁ → L≤X₂ → L≤Y₁ → L≤Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ‖(Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
        twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂)‖ ≤
        C*(sourceControl S W₁*sourceControl S W₂)*Z^ε*(1+‖t‖)^J*(Real.sqrt T/L) := by
  obtain ⟨J,S,hS,hunit⟩ := rectangle_source_unit a b ε B ha hb hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hbound⟩ := hunit Q hQ
  refine ⟨C,hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have h := hbound (normalizedProfile S W₁) (normalizedProfile S W₂)
    ((normalizedProfile_support S W₁).trans hs₁)
    ((normalizedProfile_support S W₂).trans hs₂)
    (normalizedProfile_control S W₁) (normalizedProfile_control S W₂)
    Z hZ η χ ψ hnorm hQψ hind m A z hml hm2 hrow
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have heq : (Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂-
      twistedIdealSum χ W₁ t Y₁*twistedIdealSum χ W₂ t Y₂) =
      ((sourceControl S W₁*sourceControl S W₂:ℝ):ℂ)*
      ((Real.sqrt T:ℂ)⁻¹*(twistedIdealSum χ (normalizedProfile S W₁) t X₁*
        twistedIdealSum χ (normalizedProfile S W₂) t X₂-
        twistedIdealSum χ (normalizedProfile S W₁) t Y₁*
        twistedIdealSum χ (normalizedProfile S W₂) t Y₂)) := by
    rw [twistedIdealSum_normalized S hS χ W₁ t X₁,
      twistedIdealSum_normalized S hS χ W₂ t X₂,
      twistedIdealSum_normalized S hS χ W₁ t Y₁,
      twistedIdealSum_normalized S hS χ W₂ t Y₂]
    push_cast
    ring
  rw [heq,norm_mul,Complex.norm_real,Real.norm_of_nonneg
    (mul_nonneg (sourceControl_nonneg S W₁) (sourceControl_nonneg S W₂))]
  exact (mul_le_mul_of_nonneg_left h
    (mul_nonneg (sourceControl_nonneg S W₁) (sourceControl_nonneg S W₂))).trans_eq (by ring)
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
end OAIOriginalModule1453

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RetainedEnergy
Source SHA256: eeb0dd6dafd5fac1b7aeb570bda344613d65c2208b172828212837a4beb89fe1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1454



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredMomentRetainedProfile
open CenteredMomentDivisorRawEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveSlotRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) : ℂ :=
  (Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹ *
    ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
      ∏ i,rowSlot η m A z (S i) (β i) t)

def retainedPositiveRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) : ℂ :=
  positiveSlotRow η m A z (dilated W₁ (clipDilation X₁)) (dilated W₂ (clipDilation X₂))
    S β P t (clippedScale X₁) (clippedScale X₂)

omit [DecidableEq ι] in
theorem retained_rectangle_raw_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ T : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hT : 0 < T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏ i,rowSlot η m A z (S i) (β i) t)‖^2 =
      (clippedScale X₁*clippedScale X₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  have hp : 0 < ∏ i,P i := Finset.prod_pos (fun i _ => hP i)
  have hc₁ : 0 < clippedScale X₁ := zero_lt_one.trans_le (clippedScale_ge_one _)
  have hc₂ : 0 < clippedScale X₂ := zero_lt_one.trans_le (clippedScale_ge_one _)
  unfold retainedPositiveRow positiveSlotRow
  rw [normalized_norm_sq _ (mul_pos hT hp),normalized_norm_sq _ (mul_pos (mul_pos hc₁ hc₂) hp),
    clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  field_simp [hp.ne',hT.ne',hc₁.ne',hc₂.ne']

omit [DecidableEq ι] in
theorem centered_to_retained_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T) :
    ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2 ≤
      2*(clippedScale X₁*clippedScale X₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2+
      2*(clippedScale Y₁*clippedScale Y₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2 := by
  let F (U V : ℝ) : ℂ := (Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
    ((rowTwistedSum η m A z W₁ t U*rowTwistedSum η m A z W₂ t V)*
      ∏ i,rowSlot η m A z (S i) (β i) t)
  have he : centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T=F X₁ X₂-F Y₁ Y₂ := by
    unfold centeredSlotRow F
    ring
  rw [he]
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (F X₁ X₂) (F Y₁ Y₂)) 2
  have hn : ‖F X₁ X₂-F Y₁ Y₂‖^2 ≤ 2*‖F X₁ X₂‖^2+2*‖F Y₁ Y₂‖^2 := by
    nlinarith [sq_nonneg (‖F X₁ X₂‖-‖F Y₁ Y₂‖)]
  have hx := retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t X₁ X₂ T hX₁ hX₂ hT
  have hy := retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t Y₁ Y₂ T hY₁ hY₂ hT
  change ‖F X₁ X₂‖^2=_ at hx
  change ‖F Y₁ Y₂‖^2=_ at hy
  rw [hx,hy] at hn
  convert hn using 1 ; ring

omit [DecidableEq ι] in
theorem centered_to_retained_weighted_energy (η : Character) (m A : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T)
    (rows : Finset O) (ω : O → ℝ) (hω : ∀ z∈rows,0 ≤ ω z) :
    (∑ z∈rows,ω z*‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2) ≤
      2*(clippedScale X₁*clippedScale X₂/T)*
        (∑ z∈rows,ω z*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2)+
      2*(clippedScale Y₁*clippedScale Y₂/T)*
        (∑ z∈rows,ω z*‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  have hh := mul_le_mul_of_nonneg_left
    (centered_to_retained_energy η m A z W₁ W₂ S β P hP t X₁ X₂ Y₁ Y₂ T
      hX₁ hX₂ hY₁ hY₂ hT) (hω z hz)
  convert hh using 1 ; ring

omit [DecidableEq ι] in
theorem retained_rectangle_uniform_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (b₁ b₂ t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 ≤
      (max 1 b₁*max 1 b₂)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  have hB : 0 ≤ max 1 b₁*max 1 b₂ := mul_nonneg
    (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left _ _))
  by_cases h₁ : X₁*b₁ < 1
  · unfold positiveSlotRow
    rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h₁,zero_mul,zero_mul,mul_zero,norm_zero,zero_pow (by decide)]
    exact mul_nonneg hB (sq_nonneg _)
  by_cases h₂ : X₂*b₂ < 1
  · unfold positiveSlotRow
    rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h₂,mul_zero,zero_mul,mul_zero,norm_zero,zero_pow (by decide)]
    exact mul_nonneg hB (sq_nonneg _)
  have hr : clippedScale X₁*clippedScale X₂/(X₁*X₂) ≤ max 1 b₁*max 1 b₂ := by
    have h := mul_le_mul (clipDilation_le b₁ X₁ hX₁ (le_of_not_gt h₁))
      (clipDilation_le b₂ X₂ hX₂ (le_of_not_gt h₂))
      (zero_le_one.trans (clipDilation_ge_one _ hX₂)) (zero_le_one.trans (le_max_left _ _))
    simpa only [clipDilation,div_mul_div_comm] using h
  unfold positiveSlotRow
  rw [retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t X₁ X₂ (X₁*X₂) hX₁ hX₂ (mul_pos hX₁ hX₂)]
  exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)

omit [DecidableEq ι] in
theorem centered_to_retained_uniform_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (b₁ b₂ t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2 ≤
      2*(max 1 b₁*max 1 b₂)*
        (‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2+
         ‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2) := by
  have he : centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T =
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂-
      positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂ := by
    unfold centeredSlotRow positiveSlotRow
    rw [hX,hY]
    ring
  rw [he]
  have hx := retained_rectangle_uniform_energy η m A z W₁ W₂ S β P hP b₁ b₂ t X₁ X₂ hX₁ hX₂ hs₁ hs₂
  have hy := retained_rectangle_uniform_energy η m A z W₁ W₂ S β P hP b₁ b₂ t Y₁ Y₂ hY₁ hY₂ hs₁ hs₂
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le
    (positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
    (positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂)) 2
  nlinarith [sq_nonneg (‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖-
    ‖positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂‖)]

end SevenEighths.CenteredMomentRetainedEnergy

end

end OAI
end OAIOriginalModule1454

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorRetained
Source SHA256: 9024fe3c9be0db0fe98c02b5781abbceae4de8e8c02a946feab11c98d711b7b1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1455



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allocatedPositiveRow (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  retainedPositiveRow η m A z W₁ W₂ (fun i : liveIndices D a => S i)
    (fun i : liveIndices D a => β i) (fun i : liveIndices D a => P i) t
    (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))

theorem allocated_to_retained_energy (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
         ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hx : (X₁/Ideal.absNorm (selectedPlain D a 0))*(X₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hX]; rfl
  have hy : (Y₁/Ideal.absNorm (selectedPlain D a 0))*(Y₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hY]; rfl
  have hr := allocated_raw_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hT
  have hc := centered_to_retained_uniform_energy η m A z W₁ W₂
    (fun i : liveIndices D a => S i) (fun i : liveIndices D a => β i)
    (fun i : liveIndices D a => P i) (fun i => hP i) b₁ b₂ t _ _ _ _ _
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))
    hx hy hW₁ hW₂
  have hF : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have hh := mul_le_mul_of_nonneg_left hc (div_nonneg (sq_nonneg (∏ i∈frozenIndices D a,M i)) hF.le)
  apply hr.trans
  convert hh using 1 <;> simp only [residualCenteredRow,allocatedPositiveRow] ; ring

theorem masked_raw_to_retained_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)),(∀ i,∀ I∈S i,Prime I) →
      ∀ (β : ι → Ideal O → ℂ) (M P : ι → ℝ),(∀ i,0 ≤ M i) → (∀ i,0 < P i) →
      (∀ i,∀ I∈S i,‖β i I‖ ≤ M i) → ∀ (D : Ideal O),Squarefree D →
      ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z∈rows,0 ≤ ω z) →
      (∑ z∈rows,ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
      C*(Ideal.absNorm D:ℝ)^ε*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
             ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  obtain ⟨C,hC,hbase⟩ := actual_allocated_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S hS β M P hM hP hβ D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY rows ω hω
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hh := hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows (fun z => ω z/(T*∏ i,P i))
    (fun z hz => div_nonneg (hω z hz) htotal.le)
  have he (z : O) (x : ℂ) : (ω z/(T*∏ i,P i))*‖x‖^2 =
      ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*x‖^2 := by
    rw [normalized_norm_sq _ htotal]
    ring
  simp_rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hb := mul_le_mul_of_nonneg_left
    (allocated_to_retained_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
      b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY) (hω z hz)
  convert hb using 1 ; ring

end SevenEighths.CenteredMomentDivisorRetained

end

end OAI
end OAIOriginalModule1455

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SlotRatios
Source SHA256: 4f815851713cffccfa3a3369fe221d610272780b9766c349763a7e2f88925fa4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1456


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

def logWindow (a b : ℝ) : ℝ := max |Real.log a| |Real.log b|

theorem logWindow_nonneg (a b : ℝ) : 0 ≤ logWindow a b :=
  (abs_nonneg _).trans (le_max_left _ _)

theorem slot_log_ratio_bound (W : ℝ → ℂ) (a b P Z : ℝ) (I : Ideal O)
    (ha : 0 < a) (hZ : 1 < Z)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hW : W ((Ideal.absNorm I:ℝ)/P) ≠ 0) :
    |Real.logb Z ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b/Real.log Z := by
  have hw := hs hW
  have hr : 0 < (Ideal.absNorm I:ℝ)/P := ha.trans_le hw.1
  have hlow := Real.log_le_log ha hw.1
  have hhigh := Real.log_le_log hr hw.2
  have habs : |Real.log ((Ideal.absNorm I:ℝ)/P)| ≤ logWindow a b := by
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le (Real.log a)
      have hm := le_max_left |Real.log a| |Real.log b|
      dsimp only [logWindow]
      linarith
    · exact hhigh.trans ((le_abs_self _).trans (le_max_right _ _))
  rw [Real.logb,abs_div,abs_of_pos (Real.log_pos hZ)]
  exact div_le_div_of_nonneg_right habs (Real.log_pos hZ).le

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
theorem frozen_subset_ratio_bound (entrance frozen : Finset ι) (hsub : frozen ⊆ entrance)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ frozen,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |∑ i ∈ frozen,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  calc
    _ ≤ ∑ i ∈ frozen,|Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ frozen,logWindow (a i) (b i)/Real.log Z :=
      Finset.sum_le_sum (fun i hi => slot_log_ratio_bound (W i) (a i) (b i) (P i) Z (v i)
        (ha i (hsub hi)) hZ (hs i (hsub hi)) (hW i hi))
    _ = (∑ i ∈ frozen,logWindow (a i) (b i))/Real.log Z := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => logWindow_nonneg (a i) (b i))) (Real.log_pos hZ).le

theorem disjoint_frozen_ratio_bound (entrance old fresh : Finset ι)
    (hold : old ⊆ entrance) (hfresh : fresh ⊆ entrance) (hdis : Disjoint old fresh)
    (W : ι → ℝ → ℂ) (a b P : ι → ℝ) (v : ι → Ideal O) (Z : ℝ) (hZ : 1 < Z)
    (ha : ∀ i ∈ entrance,0 < a i)
    (hs : ∀ i ∈ entrance,Function.support (W i) ⊆ Set.Icc (a i) (b i))
    (hW : ∀ i ∈ old ∪ fresh,W i ((Ideal.absNorm (v i):ℝ)/P i) ≠ 0) :
    |(∑ i ∈ old,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i))+
      (∑ i ∈ fresh,Real.logb Z ((Ideal.absNorm (v i):ℝ)/P i))| ≤
      (∑ i ∈ entrance,logWindow (a i) (b i))/Real.log Z := by
  rw [← Finset.sum_union hdis]
  exact frozen_subset_ratio_bound entrance (old ∪ fresh) (Finset.union_subset hold hfresh)
    W a b P v Z hZ ha hs hW

end SevenEighths.CenteredMomentSlotRatios

end

end OAI
end OAIOriginalModule1456

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorWitness
Source SHA256: 4b8ee71779cc145a32d7e21c5567cae4c1777cf6bfc101e9e045c417901dec56
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1457



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorWitness
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentHeckeExpansion
open CenteredMomentRectangle HeckeFamily IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_tsum_term {α : Type*} (f : α → ℂ) (h : (∑' x,f x) ≠ 0) :
    ∃ x,f x ≠ 0 := by
  by_contra hn
  push Not at hn
  exact h (by simp only [hn,tsum_zero])

theorem allocated_nonzero_witness (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    ∃ (v : (i : ι) → S i) (I J : Ideal O),
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a ≠ 0 ∧
      (∀ i,β i (v i) ≠ 0) ∧ idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J ≠ 0 := by
  obtain ⟨v,_,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hβ,ht⟩ := mul_ne_zero_iff.mp hv
  obtain ⟨I,hI⟩ := exists_tsum_term _ ht
  obtain ⟨J,hJ⟩ := exists_tsum_term _ hI
  have hh := mul_ne_zero_iff.mp hJ
  exact ⟨v,I,J,(mul_ne_zero_iff.mp hh.1).1,
    fun i => Finset.prod_ne_zero_iff.mp hβ i (Finset.mem_univ i),hh.2⟩

def actualExtracted (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) : Ideal O :=
  (selectedPlain D a 0*selectedPlain D a 1)*∏ i∈frozenIndices D a,v i

private theorem prime_dvd_selectedPlain (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) (P : primeSupport D)
    (hP : P ∈ selectedPrimes D Finset.univ a (Sum.inr j)) :
    (P : Ideal O) ∣ selectedPlain D a j := by
  exact Finset.dvd_prod_of_mem (fun q : primeSupport D => (q : Ideal O))
    (a := P) (s := selectedPrimes D Finset.univ a (Sum.inr j)) hP

theorem divisor_dvd_actualExtracted (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (I J : Ideal O)
    (hn : allocationTerm D Finset.univ (factorTuple v I J) a ≠ 0) :
    D ∣ actualExtracted D a v := by
  apply (squarefree_dvd_iff D _ hD).mpr
  intro P hP
  let PP : primeSupport D := ⟨P,hP⟩
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp (a PP).property).1
  have hmem : PP ∈ selectedPrimes D Finset.univ a i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ PP,hi⟩
  cases i with
  | inl i =>
      have hfr : i ∈ frozenIndices D a := Finset.mem_filter.mpr ⟨Finset.mem_univ i,⟨PP,hmem⟩⟩
      have hd : P∣v i := selected_divides_factor D Finset.univ (factorTuple v I J) a hn PP (Sum.inl i) hi
      exact dvd_mul_of_dvd_right (hd.trans (Finset.dvd_prod_of_mem v (a := i) (s := frozenIndices D a) hfr)) _
  | inr j =>
      have hd : P∣selectedPlain D a j := prime_dvd_selectedPlain D a j PP hmem
      fin_cases j
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _

theorem actualExtracted_ne_zero (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) : actualExtracted D a v ≠ 0 :=
  mul_ne_zero (mul_ne_zero (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hv i))

theorem actualExtracted_norm_boundary (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) (I J : Ideal O)
    (hn : allocationTerm D Finset.univ (factorTuple v I J) a ≠ 0) :
    (Ideal.absNorm D:ℝ) ≤ selectedNorm D a*∏ i∈frozenIndices D a,(Ideal.absNorm (v i):ℝ) := by
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (actualExtracted_ne_zero D a v hv))) (map_dvd Ideal.absNorm (divisor_dvd_actualExtracted D hD a v I J hn))
  simpa only [actualExtracted,map_mul,map_prod,Nat.cast_mul,Nat.cast_prod,selectedNorm] using
    (show (Ideal.absNorm D:ℝ) ≤ Ideal.absNorm (actualExtracted D a v) by exact_mod_cast h)

end SevenEighths.CenteredMomentDivisorWitness

end

end OAI
end OAIOriginalModule1457

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DivisorActualBoundary
Source SHA256: 97bc26355960afce8f27b7bd3b6e185900f07695b4c0daf5cc75e6bff38c5cf8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1458


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorActualBoundary
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentDivisorRaw CenteredMomentDivisorWitness CenteredMomentSlotRatios HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem selected_log_identity (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) (P : ι → ℝ) (hP : ∀ i,0 < P i) (Z : ℝ) :
    Real.logb Z (selectedNorm D a*∏ i∈frozenIndices D a,(Ideal.absNorm (v i:Ideal O):ℝ)) =
      Real.logb Z (formalReductionFactor D a P)+
        ∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i) := by
  have hn (i : ι) : (Ideal.absNorm (v i:Ideal O):ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hv i))
  unfold formalReductionFactor
  rw [Real.logb_mul (selectedNorm_pos D a).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)),
    Real.logb_mul (selectedNorm_pos D a).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => (hP i).ne')),
    Real.logb_prod _ _ (fun i _ => hn i),Real.logb_prod _ _ (fun i _ => (hP i).ne')]
  simp_rw [Real.logb_div (hn _) (hP _).ne']
  rw [Finset.sum_sub_distrib]
  ring

theorem nonzero_row_formal_boundary (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (hβW : ∀ i I,β i I ≠ 0 → W i ((Ideal.absNorm I:ℝ)/P i) ≠ 0)
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
  obtain ⟨v,I,J,ha,hβ,hrect⟩ := allocated_nonzero_witness η m A z t S β D a
    W₁ W₂ X₁ X₂ Y₁ Y₂ hne
  have hv (i : ι) : (v i:Ideal O) ≠ 0 := (hS i (v i) (v i).property).ne_zero
  have hb := actualExtracted_norm_boundary D hD a (fun i => v i) hv I J ha
  have hND : (0:ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hl := Real.logb_le_logb_of_le hZ hND hb
  rw [selected_log_identity D a (fun i => v i) hv P hP Z] at hl
  have hr : |∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i)| ≤
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
    apply frozen_subset_ratio_bound (ι := ι) Finset.univ (frozenIndices D a) (Finset.subset_univ _)
      W lo hi P (fun i => (v i:Ideal O)) Z hZ
    · intro i _
      exact hlo i
    · intro i _
      exact hW i
    · intro i _
      exact hβW i (v i) (hβ i)
  have hh := (le_abs_self (∑ i∈frozenIndices D a,Real.logb Z ((Ideal.absNorm (v i:Ideal O):ℝ)/P i))).trans hr
  linarith

theorem original_nonzero_row_formal_boundary (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hne : allocatedRectangle η m A z t S
      (fun i I => ν i I*W i ((Ideal.absNorm I:ℝ)/P i)) D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z :=
  nonzero_row_formal_boundary η m A z t S hS _ W lo hi P hlo hP hW
    (fun _i _I h => (mul_ne_zero_iff.mp h).2) D hD a W₁ W₂ X₁ X₂ Y₁ Y₂ Z hZ hne

end SevenEighths.CenteredMomentDivisorActualBoundary

end

end OAI
end OAIOriginalModule1458

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ActiveAllocation
Source SHA256: 017a5415a78dbedfe7a0d66731dd1a0900cb3e8534077892af92922fd3cd5956
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1459



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentActiveAllocation
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained
open CenteredMomentSlotRatios CenteredMomentDivisorActualBoundary CenteredMomentDivisorRectangle
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def activeAllocations (η:Character) (m A:O) (t:ℝ) (S:ι→Finset (Ideal O))
    (β:ι→Ideal O→ℂ) (D:Ideal O) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ) :
    Finset (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :=
  Finset.univ.filter (fun a=>∃z:O,allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂≠0)

theorem inactive_zero (η:Character) (m A:O) (t:ℝ) (S:ι→Finset (Ideal O))
    (β:ι→Ideal O→ℂ) (D:Ideal O) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (ha:a∉activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂) (z:O) :
    allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂=0 := by
  by_contra hn
  exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,z,hn⟩)

theorem masked_eq_active_allocations (η:Character) (m A z:O) (t:ℝ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (D:Ideal O) (hD:Squarefree D)
    (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂) :
    maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂=
      ∑a∈activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ := by
  unfold maskedRectangle
  rw [CenteredMomentDivisorFullMask.full_mask_eq_allocated_rectangles η m A z t S β D hD
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂]
  symm
  exact Finset.sum_subset (Finset.subset_univ _) (fun a _ ha=>inactive_zero η m A t S β D
    W₁ W₂ X₁ X₂ Y₁ Y₂ a ha z)

theorem active_allocated_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
      (D : Ideal O),Squarefree D → ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z ∈ rows,0 ≤ ω z) →
      (∑ z ∈ rows,ω z*‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a ∈ activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
            ∑ z ∈ rows,ω z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
  obtain ⟨C,hC,hbase⟩:=actual_allocated_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ rows ω hω
  apply (hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ rows ω hω).trans_eq
  congr 1
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a ha hn
  simp only [inactive_zero η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂ a hn,norm_zero,zero_pow (by norm_num:2≠0),mul_zero,Finset.sum_const_zero]

theorem active_raw_to_retained_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)),(∀ i,∀ I∈S i,Prime I) →
      ∀ (β : ι → Ideal O → ℂ) (M P : ι → ℝ),(∀ i,0 ≤ M i) → (∀ i,0 < P i) →
      (∀ i,∀ I∈S i,‖β i I‖ ≤ M i) → ∀ (D : Ideal O),Squarefree D →
      ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ∀ (rows : Finset O) (ω : O → ℝ),(∀ z∈rows,0 ≤ ω z) →
      (∑ z∈rows,ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
      C*(Ideal.absNorm D:ℝ)^ε*
        ∑ a ∈ activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P)*
          ∑ z∈rows,ω z*
            (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
             ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  obtain ⟨C,hC,hbase⟩ := active_allocated_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S hS β M P hM hP hβ D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY rows ω hω
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hh := hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows (fun z => ω z/(T*∏ i,P i))
    (fun z hz => div_nonneg (hω z hz) htotal.le)
  have he (z : O) (x : ℂ) : (ω z/(T*∏ i,P i))*‖x‖^2 =
      ω z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*x‖^2 := by
    rw [normalized_norm_sq _ htotal]
    ring
  simp_rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hb := mul_le_mul_of_nonneg_left
    (allocated_to_retained_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
      b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY) (hω z hz)
  convert hb using 1 ; ring

theorem active_formal_boundary (η : Character) (m A : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hactive : a∈activeAllocations η m A t S
      (fun i I => ν i I*W i ((Ideal.absNorm I:ℝ)/P i)) D W₁ W₂ X₁ X₂ Y₁ Y₂) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
  obtain ⟨z,hz⟩:=(Finset.mem_filter.mp hactive).2
  exact original_nonzero_row_formal_boundary η m A z t S hS ν W lo hi P hlo hP hW
    D hD a W₁ W₂ X₁ X₂ Y₁ Y₂ Z hZ hz

end SevenEighths.CenteredMomentActiveAllocation

end

end OAI
end OAIOriginalModule1459

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ActiveDivisorShell
Source SHA256: 585491404d857a603ec977f901d20c225cb2670b95990cfe702565eadcbbf0f9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1460



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentActiveDivisorShell
open HeckeFamily CenteredMomentActiveAllocation CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDivisorBoundary CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O

structure Source (ι:Type*) [Fintype ι] where
  η : Character
  m : O
  A : O
  t : ℝ
  slots : ι→Finset (Ideal O)
  prime : ∀i,∀I∈slots i,Prime I
  ν : ι→Ideal O→ℂ
  W : ι→ℝ→ℂ
  lo : ι→ℝ
  hi : ι→ℝ
  P : ι→ℝ
  lo_pos : ∀i,0<lo i
  P_pos : ∀i,0<P i
  support : ∀i,Function.support (W i)⊆Set.Icc (lo i) (hi i)
  W₁ : ℝ→ℂ
  W₂ : ℝ→ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Source.active (s:Source ι) (D:Ideal O) : Finset (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :=
  activeAllocations s.η s.m s.A s.t s.slots
    (fun i I=>s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)) D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

def Source.allowance (s:Source ι) (Z:ℝ) : ℝ :=
  (∑i,logWindow (s.lo i) (s.hi i))/Real.log Z

theorem Source.active_boundary (s:Source ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.active D) (Z:ℝ) (hZ:1<Z) :
    Real.logb Z (Ideal.absNorm D:ℝ)≤Real.logb Z (formalReductionFactor D a s.P)+s.allowance Z :=
  active_formal_boundary s.η s.m s.A s.t s.slots s.prime s.ν s.W s.lo s.hi s.P s.lo_pos s.P_pos
    s.support D hD a s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ Z hZ ha

theorem reciprocal_sqrt_log (Z x y:ℝ) (hZ:1<Z) (hx:0<x) (hy:0<y) :
    1/Real.sqrt (x*y)=Z^(-(Real.logb Z x+Real.logb Z y)/2) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  calc
    _=(x*y)^(-(1/2:ℝ)):=by rw [Real.sqrt_eq_rpow,one_div,Real.rpow_neg (mul_nonneg hx.le hy.le)]
    _=(Z^(Real.logb Z x+Real.logb Z y))^(-(1/2:ℝ)):=by
      rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hx,Real.rpow_logb hz hZ.ne' hy]
    _=_:=by rw [←Real.rpow_mul hz.le]; congr 1; ring

theorem Source.active_pair_weight {κ:Type*} [Fintype κ] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (ha:a∈s.active D) (hb:b∈v.active D) (Z:ℝ) (hZ:1<Z) :
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)≤
      Z^((s.allowance Z+v.allowance Z)/2)/(Ideal.absNorm D:ℝ) := by
  have hs:0<formalReductionFactor D a s.P:=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))
  have hv:0<formalReductionFactor D b v.P:=
    mul_pos (selectedNorm_pos D b) (Finset.prod_pos (fun i _=>v.P_pos i))
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  rw [reciprocal_sqrt_log Z _ _ hZ hs hv]
  have hl:=s.active_boundary D hD a ha Z hZ
  have hr:=v.active_boundary D hD b hb Z hZ
  have he:-(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P))/2≤
      (s.allowance Z+v.allowance Z)/2-Real.logb Z (Ideal.absNorm D:ℝ):=by linarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le he
  rwa [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn] at hp

theorem paired_active_divisor_shell {κ:Type*} [Fintype κ] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (Ds:Finset (Ideal O))
    (a:∀D:Ideal O,Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:∀D:Ideal O,Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (hD:∀D∈Ds,Squarefree D) (ha:∀D∈Ds,a D∈s.active D) (hb:∀D∈Ds,b D∈v.active D)
    (T Z:ℝ) (hT:1≤T) (hZ:1<Z)
    (hlo:∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) (hhi:∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) :
    (∑D∈Ds,1/Real.sqrt (formalReductionFactor D (a D) s.P*formalReductionFactor D (b D) v.P))≤
      256*Z^((s.allowance Z+v.allowance Z)/2) := by
  have hs (D:Ideal O):0<formalReductionFactor D (a D) s.P:=
    mul_pos (selectedNorm_pos D (a D)) (Finset.prod_pos (fun i _=>s.P_pos i))
  have hv (D:Ideal O):0<formalReductionFactor D (b D) v.P:=
    mul_pos (selectedNorm_pos D (b D)) (Finset.prod_pos (fun i _=>v.P_pos i))
  simp_rw [reciprocal_sqrt_log Z _ _ hZ (hs _) (hv _)]
  apply paired_raw_divisor_bound Ds T Z ((s.allowance Z+v.allowance Z)/2) hT hZ
    (fun D=>Real.logb Z (formalReductionFactor D (a D) s.P))
    (fun D=>Real.logb Z (formalReductionFactor D (b D) v.P))
    (fun _=>s.allowance Z) (fun _=>v.allowance Z)
    (fun D hd=>(hD D hd).ne_zero) hlo hhi
    (fun D hd=>s.active_boundary D (hD D hd) (a D) (ha D hd) Z hZ)
    (fun D hd=>v.active_boundary D (hD D hd) (b D) (hb D hd) Z hZ)
  intro D hd
  linarith

theorem paired_all_active_shell {κ:Type*} [Fintype κ] [DecidableEq κ]
    (N:ℕ) (hι:Fintype.card ι≤N) (hκ:Fintype.card κ≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Source ι) (v:Source κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤T → 1<Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2) := by
  obtain ⟨C₁,hC₁,hcard₁⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  obtain ⟨C₂,hC₂,hcard₂⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=κ⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨256*C₁*C₂,by positivity,?_⟩
  intro s v Ds hD T Z hT hZ hlo hhi
  have ht:0<T:=zero_lt_one.trans_le hT
  have hz:0<Z:=zero_lt_one.trans hZ
  let θ:ℝ:=(s.allowance Z+v.allowance Z)/2
  have hc₁ (D:Ideal O) (hd:D∈Ds):( (s.active D).card:ℝ)≤C₁*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((s.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₁ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hc₂ (D:Ideal O) (hd:D∈Ds):( (v.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((v.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (κ⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₂ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hp (D:Ideal O) (hd:D∈Ds):
      (∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
      (C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=by
    have hn:0<(Ideal.absNorm D:ℝ):=ht.trans_le (hlo D hd)
    have he:((Ideal.absNorm D:ℝ)^ε)*((Ideal.absNorm D:ℝ)^ε)=(Ideal.absNorm D:ℝ)^(2*ε):=by
      rw [←Real.rpow_add hn]; congr 1; ring
    have hpow:(Ideal.absNorm D:ℝ)^(2*ε)≤(2*T)^(2*ε):=
      Real.rpow_le_rpow hn.le (hhi D hd).le (by positivity)
    calc
      _≤∑_a∈s.active D,∑_b∈v.active D,Z^θ/(Ideal.absNorm D:ℝ):=
        Finset.sum_le_sum (fun a ha=>Finset.sum_le_sum (fun b hb=>s.active_pair_weight v D (hD D hd) a b ha hb Z hZ))
      _=((s.active D).card:ℝ)*((v.active D).card:ℝ)*(Z^θ/(Ideal.absNorm D:ℝ)):=by simp;ring
      _≤(C₁*(Ideal.absNorm D:ℝ)^ε)*(C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^θ/(Ideal.absNorm D:ℝ)):=
        mul_le_mul_of_nonneg_right (mul_le_mul (hc₁ D hd) (hc₂ D hd) (by positivity) (by positivity)) (by positivity)
      _=(C₁*C₂)*(Ideal.absNorm D:ℝ)^(2*ε)*(Z^θ/(Ideal.absNorm D:ℝ)):=by rw [←he];ring
      _≤(C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
          (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) ht (hlo D hd)) (by positivity) (by positivity)
  calc
    _≤∑_D∈Ds,(C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=Finset.sum_le_sum hp
    _=(Ds.card:ℝ)*((C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T)):=by simp
    _≤(256*T)*((C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T)):=
      mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT (fun D hd=>(hD D hd).ne_zero) hhi) (by positivity)
    _=(256*C₁*C₂)*(2*T)^(2*ε)*Z^θ:=by field_simp

end SevenEighths.CenteredMomentActiveDivisorShell

end

end OAI
end OAIOriginalModule1460

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Smooth
Source SHA256: 3ed97ce1f925a280163fe57aa4a0a7092d391ca1235746ee7763308c153a0dd7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1461



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentSmooth
open FourierBridge EisensteinSchwartzPoisson

def rootWindow (V : ℝ → ℂ) (u : ℝ) : ℂ := V u / (Real.sqrt (Real.exp u) : ℂ)

def wholeKernel (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (R ρ x u v : ℝ) : ℂ :=
  V 0 ρ * V 1 x * rootWindow (V 2) u * rootWindow (V 3) v *
    paperRadialFourier W (R * Real.exp (ρ + x - u - v))

def rowPhase (V : Fin 4 → ℝ → ℂ) (ρ x t : ℝ) : ℂ :=
  (V 0 ρ * logPhase t ρ) * (V 1 x * logPhase t x)

def columnPhase (V : ℝ → ℂ) (u t : ℝ) : ℂ :=
  rootWindow V u * logPhase t (-u)

def separatedKernel (V : Fin 4 → ℝ → ℂ) (ρ x u v t : ℝ) : ℂ :=
  rowPhase V ρ x t * columnPhase (V 2) u t * columnPhase (V 3) v t

theorem whole_kernel_separation (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
        ∫ t : ℝ, separatedKernel V ρ x u v t * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  let U : Fin 4 → ℝ → ℂ := ![V 0, V 1, rootWindow (V 2), rootWindow (V 3)]
  let a : Fin 4 → ℝ := ![1, 1, -1, -1]
  have hU : ∀ i y, U i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i
    · exact hV 0 y hy
    · exact hV 1 y hy
    · apply hV 2 y
      intro hz
      exact hy (by simp [U, rootWindow, hz])
    · apply hV 3 y
      intro hz
      exact hy (by simp [U, rootWindow, hz])
  obtain ⟨C, hC, hs⟩ := paperRadialFourier_log_separation_envelope W U a M hM hU A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  refine ⟨b, ?_, hi, hm, hp⟩
  intro ρ x u v
  have h := hb ![ρ, x, u, v]
  simpa [U, a, wholeKernel, separatedKernel, rowPhase, columnPhase,
    Fin.prod_univ_succ, Fin.sum_univ_succ, sub_eq_add_neg, mul_assoc, add_assoc] using h

lemma separated_integrable (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (ρ x u v : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ => c * separatedKernel V ρ x u v t * b t) := by
  let K : ℝ := ‖c‖ * ‖V 0 ρ‖ * ‖V 1 x‖ * ‖rootWindow (V 2) u‖ * ‖rootWindow (V 3) v‖
  apply (b.integrable.norm.const_mul K).mono'
  · have hρ := logPhase_continuous_left ρ
    have hx := logPhase_continuous_left x
    have hu := logPhase_continuous_left (-u)
    have hv := logPhase_continuous_left (-v)
    exact (by unfold separatedKernel rowPhase columnPhase; fun_prop : Continuous (fun t : ℝ =>
      c * separatedKernel V ρ x u v t * b t)).aestronglyMeasurable
  · filter_upwards [] with t
    simp only [separatedKernel, rowPhase, columnPhase, norm_mul, logPhase_norm, mul_one]
    dsimp only [K]
    ring_nf
    exact le_rfl

theorem finite_pair_separation {α β : Type*}
    (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (R : ℝ) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ ρ x u v : ℝ, wholeKernel W V R ρ x u v =
      ∫ t : ℝ, separatedKernel V ρ x u v t * b t)
    (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (ρ x : ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, (c i * star (d j)) * wholeKernel W V R ρ x (u i) (v j)) =
      ∫ t : ℝ, rowPhase V ρ x t *
        (∑ i ∈ S, c i * columnPhase (V 2) (u i) t) *
        (∑ j ∈ T, star (d j) * columnPhase (V 3) (v j) t) * b t := by
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∫ t : ℝ,
        (c i * star (d j)) * separatedKernel V ρ x (u i) (v j) t * b t := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsep, ← integral_const_mul]
      congr 1
      funext t
      ring
    _ = ∫ t : ℝ, ∑ i ∈ S, ∑ j ∈ T,
        (c i * star (d j)) * separatedKernel V ρ x (u i) (v j) t * b t := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum T
        (fun j _ => separated_integrable b V ρ x (u i) (v j) (c i * star (d j))))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum _ (fun j _ =>
        separated_integrable b V ρ x (u i) (v j) (c i * star (d j)))]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [Finset.sum_mul, Finset.mul_sum, separatedKernel]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem whole_product_pair_separation (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b : 𝓢(ℝ, ℂ),
      (∀ {α β : Type*} (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
        (u : α → ℝ) (v : β → ℝ) (ρ x : ℝ),
        (∑ i ∈ S, ∑ j ∈ T, (c i * star (d j)) * wholeKernel W V R ρ x (u i) (v j)) =
          ∫ t : ℝ, rowPhase V ρ x t *
            (∑ i ∈ S, c i * columnPhase (V 2) (u i) t) *
            (∑ j ∈ T, star (d j) * columnPhase (V 3) (v j) t) * b t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) ∧
      (1 + R) ^ A * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
      (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨C, hC, hs⟩ := whole_kernel_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  exact ⟨b, fun S T c d u v ρ x => finite_pair_separation W V R b hb S T c d u v ρ x,
    hi, hm, hp⟩

theorem logPhase_norm_ratio (q X θ : ℝ) (hq : 0 < q) (hX : 0 < X) :
    logPhase θ (-Real.log (q / X)) =
      logPhase θ (Real.log X) * (q : ℂ) ^ (Complex.I * (-(2 * Real.pi * θ))) := by
  have hlog : -Real.log (q / X) = Real.log X + -Real.log q := by
    rw [Real.log_div hq.ne' hX.ne']
    ring
  rw [hlog, logPhase_add]
  congr 1
  have hθ : (-(2 * Real.pi * θ)) / (2 * Real.pi) = -θ := by
    have hp := Real.pi_ne_zero
    field_simp
  have hn := CenteredMomentLattice.logPhase_eq_normPower (-(2 * Real.pi * θ)) q hq
  rw [hθ] at hn
  push_cast at hn
  rw [← hn]
  unfold logPhase
  congr 1
  push_cast
  ring

open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

theorem idealWeight_height_add (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R I : Ideal O) (hI : I ≠ 0) (t v : ℝ) :
    idealWeight c χ R (t + v) I =
      idealWeight c χ R t I * (Ideal.absNorm I : ℂ) ^ (Complex.I * v) := by
  have hn : (Ideal.absNorm I : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [idealWeight, Complex.ofReal_add, mul_add, Complex.cpow_add _ _ hn]
  ring

theorem idealWeight_whole_phase (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R I : Ideal O) (hI : I ≠ 0) (t θ X : ℝ) (hX : 0 < X) :
    idealWeight c χ R t I * logPhase θ (-Real.log ((Ideal.absNorm I : ℝ) / X)) =
      logPhase θ (Real.log X) * idealWeight c χ R (t - 2 * Real.pi * θ) I := by
  have hn : (0 : ℝ) < Ideal.absNorm I := by
    exact_mod_cast (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI))
  rw [logPhase_norm_ratio _ X θ hn hX, sub_eq_add_neg, idealWeight_height_add c χ R I hI]
  push_cast
  ring

theorem centered_whole_phase (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R Qslot I J : Ideal O) (hQslot : Qslot ≠ 0) (hI : I ≠ 0) (hJ : J ≠ 0)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ t θ X : ℝ) (hX : 0 < X) :
    (idealWeight c χ R t (Qslot * I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) *
      logPhase θ (-Real.log ((Ideal.absNorm (Qslot * I * J) : ℝ) / X)) =
      logPhase θ (Real.log X) *
        (idealWeight c χ R (t - 2 * Real.pi * θ) (Qslot * I * J) *
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) := by
  calc
    _ = (idealWeight c χ R t (Qslot * I * J) *
        logPhase θ (-Real.log ((Ideal.absNorm (Qslot * I * J) : ℝ) / X))) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J := by ring
    _ = _ := by
      rw [idealWeight_whole_phase c χ R (Qslot * I * J) (mul_ne_zero (mul_ne_zero hQslot hI) hJ) t θ X hX]
      ring

end SevenEighths.CenteredMomentSmooth
end

end OAI
end OAIOriginalModule1461

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Cauchy
Source SHA256: 8383bc0e47dacb25f88a86b6f843db6b43c9f175a89f635f268f416c2819eba9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1462


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentCauchy
open CenteredMomentSmooth FourierBridge

theorem bounded_row_cauchy {κ : Type*} (rows : Finset κ)
    (w A B : κ → ℂ) (hw : ∀ k ∈ rows, ‖w k‖ ≤ 1) :
    ‖∑ k ∈ rows, w k * A k * B k‖ ≤
      Real.sqrt (∑ k ∈ rows, ‖A k‖ ^ 2) * Real.sqrt (∑ k ∈ rows, ‖B k‖ ^ 2) := by
  calc
    _ ≤ ∑ k ∈ rows, ‖w k * A k * B k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ rows, ‖A k‖ * ‖B k‖ := Finset.sum_le_sum fun k hk => by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (norm_nonneg _) (hw k hk)) (norm_nonneg _)
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt rows _ _

def leftColumn {α : Type*} (S : Finset α) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, c i * columnPhase V (u i) t

def rightColumn {β : Type*} (T : Finset β) (d : β → ℂ)
    (V : ℝ → ℂ) (v : β → ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ T, star (d j) * columnPhase V (v j) t

lemma paired_columns_integrable {α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ) (ρ x : ℝ)
    (S : Finset α) (T : Finset β) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (z : ℂ) :
    Integrable (fun t : ℝ => z * (rowPhase V ρ x t *
      leftColumn S c (V 2) u t * rightColumn T d (V 3) v t * b t)) := by
  have hi := integrable_finsetSum S (fun i _ => integrable_finsetSum T
    (fun j _ => separated_integrable b V ρ x (u i) (v j) (z * c i * star (d j))))
  convert hi using 1
  funext t
  simp only [leftColumn, rightColumn, Finset.mul_sum, Finset.sum_mul, separatedKernel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem common_density_cauchy {κ α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (rows : Finset κ) (S : Finset α) (T : Finset β)
    (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
    (ρ x : κ → ℝ) (η : κ → ℂ)
    (hη : ∀ k ∈ rows, ‖η k‖ ≤ 1)
    (hV₀ : ∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) (hV₁ : ∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1)
    (E : ℝ) (_hE : 0 ≤ E) (J : ℕ)
    (henergy : ∀ t : ℝ,
      Real.sqrt (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn T (d k) (V 3) v t‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) :
    ‖∑ k ∈ rows, η k * ∫ t : ℝ, rowPhase V (ρ k) (x k) t *
      leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t‖ ≤
      E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
  have hrow (k : κ) (hk : k ∈ rows) (t : ℝ) : ‖η k * rowPhase V (ρ k) (x k) t‖ ≤ 1 := by
    rw [norm_mul, rowPhase, norm_mul, norm_mul, norm_mul, logPhase_norm, logPhase_norm, mul_one, mul_one]
    exact (mul_le_of_le_one_left (by positivity) (hη k hk)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hV₀ k hk)).trans (hV₁ k hk))
  have hpoint (t : ℝ) :
      ‖∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ ≤
        E * ((1 + ‖t‖) ^ J * ‖b t‖) := by
    have hs := bounded_row_cauchy rows (fun k => η k * rowPhase V (ρ k) (x k) t)
      (fun k => leftColumn S (c k) (V 2) u t) (fun k => rightColumn T (d k) (V 3) v t)
      (fun k hk => hrow k hk t)
    have he : (∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)) =
        (∑ k ∈ rows, (η k * rowPhase V (ρ k) (x k) t) *
          leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t) * b t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hs.trans (henergy t)) (norm_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) :=
    JointLogSeparation.weighted_schwartz_integrable b J
  calc
    _ = ‖∫ t : ℝ, ∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ := by
      congr 1
      rw [integral_finsetSum _ (fun k _ =>
        paired_columns_integrable b V (ρ k) (x k) S T (c k) (d k) u v (η k))]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul]
    _ ≤ ∫ t : ℝ, E * ((1 + ‖t‖) ^ J * ‖b t‖) :=
      norm_integral_le_of_norm_le (hi.const_mul E) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

theorem whole_kernel_row_estimate (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {κ α β : Type*} (rows : Finset κ) (S : Finset α) (T : Finset β)
        (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : κ → ℝ) (η : κ → ℂ),
      (∀ k ∈ rows, ‖η k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ, Real.sqrt (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ ^ 2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn T (d k) (V 3) v t‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) →
      (1 + R) ^ A * ‖∑ k ∈ rows, η k *
        (∑ i ∈ S, ∑ j ∈ T, (c k i * star (d k j)) *
          wholeKernel W V R (ρ k) (x k) (u i) (v j))‖ ≤ C * E := by
  obtain ⟨C, hC, hs⟩ := whole_product_pair_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR κ α β rows S T c d u v ρ x η hη hV₀ hV₁ E hE he
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  have hid (k : κ) := hb S T (c k) (d k) u v (ρ k) (x k)
  simp_rw [hid]
  have hcs := common_density_cauchy b V rows S T c d u v ρ x η hη hV₀ hV₁ E hE J he
  change (1 + R) ^ A * ‖∑ k ∈ rows, η k * ∫ t : ℝ,
    rowPhase V (ρ k) (x k) t * leftColumn S (c k) (V 2) u t *
      rightColumn T (d k) (V 3) v t * b t‖ ≤ _
  calc
    _ ≤ (1 + R) ^ A * (E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = E * ((1 + R) ^ A * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ ≤ E * C := mul_le_mul_of_nonneg_left hm hE
    _ = _ := mul_comm _ _

end SevenEighths.CenteredMomentCauchy
end

end OAI
end OAIOriginalModule1462

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowCauchy
Source SHA256: b1083c5a2939ccc901af12a2f3d337d6534c0fb69e73342217ea11e37226409d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1463



namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def lowNumeratorWeight (C : CalibrationData) (Ω : ℝ→ℂ) (X Y : ℝ) (m : O) (v : ℝ) : ℂ :=
  Ω (elementNorm m/lowPhysicalScale C X Y)*C.residueMonoid m*
    ((elementNorm m/lowPhysicalScale C X Y:ℝ):ℂ)^(-((v:ℂ)*Complex.I))

lemma lowOuterCutoff_norm (a b x : ℝ) : ‖lowOuterCutoff a b x‖≤1 := by
  rw [lowOuterCutoff,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _),abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

lemma lowNumeratorWeight_norm (C : CalibrationData) (Ω : ℝ→ℂ)
    (hΩ : ∀x,‖Ω x‖≤1) (hΩ0 : Ω 0=0) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (m : O) (v : ℝ) :
    ‖lowNumeratorWeight C Ω X Y m v‖≤1 := by
  by_cases hm : m=0
  · simp [lowNumeratorWeight,hm,elementNorm,hΩ0]
  have hmpos : 0<elementNorm m := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hm))
  have he : -((v:ℂ)*Complex.I)=((-v:ℝ):ℂ)*Complex.I := by simp
  rw [lowNumeratorWeight,norm_mul,norm_mul,he,
    low_mellin_phase_norm _ (-v) (div_pos hmpos (lowPhysicalScale_pos C X Y hX hY)),mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΩ _)).trans (C.residueMonoid_norm_le_one m)

lemma lowNumeratorWeight_common_support (C : CalibrationData) (Ω : ℝ→ℂ)
    (hΩ : HasCompactSupport Ω) (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset O,∀m∉R,∀v : ℝ,lowNumeratorWeight C Ω X Y m v=0 := by
  have hh := elementWindow_finite_support Ω hΩ _ (lowPhysicalScale_pos C X Y hX hY)
  refine ⟨hh.toFinset,?_⟩
  intro m hm v
  have hz : Ω (elementNorm m/lowPhysicalScale C X Y)=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hm
  simp [lowNumeratorWeight,hz]

theorem lowSeparatedIntegrand_cauchy (C : CalibrationData) (Ω : ℝ→ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ∀x,‖Ω x‖≤1) (hΩ0 : Ω 0=0)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    ∃R : Finset O,∀W0 W1 : ℝ→ℂ,∀B : RayRing→O→ℂ,∀v : ℝ,
      ‖lowSeparatedIntegrand C W0 W1 Ω X Y B v‖≤
        ‖mellin W0 ((v:ℂ)*Complex.I)‖*
          ∑σ : RayRing,Real.sqrt (∑m∈R,‖lowRayAmplitude C W1 Y σ m v‖^2)*
            Real.sqrt (∑m∈R,‖B σ m‖^2) := by
  obtain ⟨R,hR⟩ := lowNumeratorWeight_common_support C Ω hΩc X Y hX hY
  refine ⟨R,?_⟩
  intro W0 W1 B v
  have he : lowSeparatedIntegrand C W0 W1 Ω X Y B v=
      mellin W0 ((v:ℂ)*Complex.I)*
        ∑σ : RayRing,∑m∈R,lowNumeratorWeight C Ω X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m := by
    unfold lowSeparatedIntegrand
    change mellin W0 ((v:ℂ)*Complex.I)*
      (∑'m : O,lowNumeratorWeight C Ω X Y m v*∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m)=_
    rw [tsum_eq_sum (s:=R) (fun m hm=>by rw [hR m hm v,zero_mul])]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [he,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑σ : RayRing,‖∑m∈R,lowNumeratorWeight C Ω X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun σ _=>CenteredMomentCauchy.bounded_row_cauchy R
      (fun m=>lowNumeratorWeight C Ω X Y m v) (fun m=>lowRayAmplitude C W1 Y σ m v) (B σ)
      (fun m _=>lowNumeratorWeight_norm C Ω hΩ hΩ0 X Y hX hY m v))

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1463

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalKernel
Source SHA256: f44fcda3492abc1f3e2bb1c9ec8e3c16124a6035abb810f30cd66719d3b17605
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1464


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalKernel
open CenteredMomentSmooth CenteredMomentCauchy FourierBridge

theorem paired_row_triangle {κ : Type*} (rows : Finset κ)
    (w A B : κ → ℂ) (hw : ∀k∈rows,‖w k‖≤1) :
    ‖∑k∈rows,w k*A k*B k‖≤∑k∈rows,‖A k‖*‖B k‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro k hk
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) (hw k hk)) (norm_nonneg _)

theorem common_density_pair {κ α β : Type*}
    (b : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (rows : Finset κ) (S : Finset α) (T : Finset β)
    (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
    (ρ x : κ → ℝ) (η : κ → ℂ)
    (hη : ∀ k ∈ rows, ‖η k‖ ≤ 1)
    (hV₀ : ∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) (hV₁ : ∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1)
    (E : ℝ) (_hE : 0 ≤ E) (J : ℕ)
    (henergy : ∀ t : ℝ,
      (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ *
        ‖rightColumn T (d k) (V 3) v t‖) ≤ E * (1 + ‖t‖) ^ J) :
    ‖∑ k ∈ rows, η k * ∫ t : ℝ, rowPhase V (ρ k) (x k) t *
      leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t‖ ≤
      E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖ := by
  have hrow (k : κ) (hk : k ∈ rows) (t : ℝ) : ‖η k * rowPhase V (ρ k) (x k) t‖ ≤ 1 := by
    rw [norm_mul, rowPhase, norm_mul, norm_mul, norm_mul, logPhase_norm, logPhase_norm, mul_one, mul_one]
    exact (mul_le_of_le_one_left (by positivity) (hη k hk)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hV₀ k hk)).trans (hV₁ k hk))
  have hpoint (t : ℝ) :
      ‖∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ ≤
        E * ((1 + ‖t‖) ^ J * ‖b t‖) := by
    have hs := paired_row_triangle rows (fun k => η k * rowPhase V (ρ k) (x k) t)
      (fun k => leftColumn S (c k) (V 2) u t) (fun k => rightColumn T (d k) (V 3) v t)
      (fun k hk => hrow k hk t)
    have he : (∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)) =
        (∑ k ∈ rows, (η k * rowPhase V (ρ k) (x k) t) *
          leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t) * b t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [he, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hs.trans (henergy t)) (norm_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) :=
    JointLogSeparation.weighted_schwartz_integrable b J
  calc
    _ = ‖∫ t : ℝ, ∑ k ∈ rows, η k * (rowPhase V (ρ k) (x k) t *
        leftColumn S (c k) (V 2) u t * rightColumn T (d k) (V 3) v t * b t)‖ := by
      congr 1
      rw [integral_finsetSum _ (fun k _ =>
        paired_columns_integrable b V (ρ k) (x k) S T (c k) (d k) u v (η k))]
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_const_mul]
    _ ≤ ∫ t : ℝ, E * ((1 + ‖t‖) ^ J * ‖b t‖) :=
      norm_integral_le_of_norm_le (hi.const_mul E) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

theorem whole_kernel_paired_row_estimate (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {κ α β : Type*} (rows : Finset κ) (S : Finset α) (T : Finset β)
        (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : κ → ℝ) (η : κ → ℂ),
      (∀ k ∈ rows, ‖η k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ, (∑ k ∈ rows, ‖leftColumn S (c k) (V 2) u t‖ *
        ‖rightColumn T (d k) (V 3) v t‖) ≤ E * (1 + ‖t‖) ^ J) →
      (1 + R) ^ A * ‖∑ k ∈ rows, η k *
        (∑ i ∈ S, ∑ j ∈ T, (c k i * star (d k j)) *
          wholeKernel W V R (ρ k) (x k) (u i) (v j))‖ ≤ C * E := by
  obtain ⟨C, hC, hs⟩ := whole_product_pair_separation W V M hM hV A J
  refine ⟨C, hC, ?_⟩
  intro R hR κ α β rows S T c d u v ρ x η hη hV₀ hV₁ E hE he
  obtain ⟨b, hb, hi, hm, hp⟩ := hs R hR
  have hid (k : κ) := hb S T (c k) (d k) u v (ρ k) (x k)
  simp_rw [hid]
  have hcs := common_density_pair b V rows S T c d u v ρ x η hη hV₀ hV₁ E hE J he
  change (1 + R) ^ A * ‖∑ k ∈ rows, η k * ∫ t : ℝ,
    rowPhase V (ρ k) (x k) t * leftColumn S (c k) (V 2) u t *
      rightColumn T (d k) (V 3) v t * b t‖ ≤ _
  calc
    _ ≤ (1 + R) ^ A * (E * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = E * ((1 + R) ^ A * ∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) := by ring
    _ ≤ E * C := mul_le_mul_of_nonneg_left hm hE
    _ = _ := mul_comm _ _

end SevenEighths.CenteredMomentExceptionalKernel

end

end OAI
end OAIOriginalModule1464

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RowNorm
Source SHA256: ffd74c13888b96610cba8b7152f2d5e92c5715e2a4b3ee37192ea9ca10787aed
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1465



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentRowNorm
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

def pairResidue (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x : Residue (a * b)) : ℂ :=
  supportedModulusCharacter a ha (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (supportedModulusCharacter b hb
      (frequencyReduction b (a * b) (dvd_mul_left b a) x))

@[simp] theorem pairResidue_mk (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (z : O) :
    pairResidue a b ha hb (Ideal.Quotient.mk _ z) =
      idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b})) := by
  simp only [pairResidue, frequencyReduction_mk, supportedModulusCharacter_mk]

def pairFourier (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (h : O) : ℂ :=
  ∑' x : Residue (a * b), pairResidue a b ha hb x *
    quotientTrace (a * b) (mul_ne_zero (supported_element_ne_zero a ha)
      (supported_element_ne_zero b hb)) (Ideal.Quotient.mk _ h * x)

theorem row_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O =>
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) (pairResidue a b ha hb)
  simpa only [pairResidue_mk, scaledRadialTest_apply] using h

theorem row_pair_poisson (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O,
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖eisEmbedding z‖ ^ 2 / K)) =
    ((K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) : ℂ) *
      ∑' h : O, pairFourier a b ha hb h *
        paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (a * b)‖ ^ 2) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_radial_paper_poisson_trace W K hK (a * b)
    (mul_ne_zero (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))
    (pairResidue a b ha hb)
  simpa only [pairResidue_mk, pairFourier, quotientTrace, tsum_fintype, Complex.real_smul] using h

def rowPolynomial {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ) (z : O) : ℂ :=
  ∑ i ∈ S, c i * idealRowHom z (Ideal.span {a i})

def rowEnergy {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O, ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖eisEmbedding z‖ ^ 2 / K)

theorem rowPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ) (z : O) :
    ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (idealRowHom z (Ideal.span {a i}) * star (idealRowHom z (Ideal.span {a j}))) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [rowPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem rowEnergy_expand {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : O, (idealRowHom z (Ideal.span {a i}) *
          star (idealRowHom z (Ideal.span {a j}))) * W (‖eisEmbedding z‖ ^ 2 / K) := by
  have hs (i j : α) := (row_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [rowEnergy, rowPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)).summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp only [tsum_mul_left]

theorem rowEnergy_poisson {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (((K / ‖eisEmbedding (a i * a j)‖ ^ 2 : ℝ) : ℂ) *
          ∑' h : O, pairFourier (a i) (a j) (ha i) (ha j) h *
            paperRadialFourier W
              (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (a i * a j)‖ ^ 2)) := by
  rw [rowEnergy_expand S a c ha W K hK]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [row_pair_poisson (a i) (a j) (ha i) (ha j) W K hK]

end SevenEighths.CenteredMomentRowNorm

end

end OAI
end OAIOriginalModule1465

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ChildAssembly
Source SHA256: 4320a8957d0706d8cc4e92b896f0108269d9975d7975432353aebbe4bfc60d51
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1466




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildAssembly
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFixedRay CenteredMomentMobiusRegroup CenteredMomentRowNorm RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def divisorCoefficient {α : Type*} (L : Ideal O) (a : α → O) (c : α → ℂ)
    (χ : RayCharacter) (i : α) : ℂ :=
  if L ∣ Ideal.span {a i} then c i * rayCharacter χ (a i) else 0

theorem rayCharacter_inverse_star (χ : RayCharacter) (a : O) :
    star (rayCharacter (χ⁻¹) a) = rayCharacter χ a := by
  change star ((χ⁻¹) (Ideal.Quotient.mk _ a)) = χ (Ideal.Quotient.mk _ a)
  rw [MulChar.star_apply', inv_inv]

theorem divisor_pair_separation {α β : Type*} (L : Ideal O) (a : α → O) (b : β → O)
    (c : α → ℂ) (d : β → ℂ) (D E h : O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (i : α) (j : β) (K : ℂ) :
    (if L ∣ Ideal.span {a i} ∧ L ∣ Ideal.span {b j} then
      completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K else 0) =
      actualCorrelation D E hD hE h *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          pairCoeff (phaseTable D E) χ ξ *
            ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
              star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) * K := by
  by_cases hi : L ∣ Ideal.span {a i}
  · by_cases hj : L ∣ Ideal.span {b j}
    · simp only [hi,hj,and_self,ite_true,divisorCoefficient,star_mul,rayCharacter_inverse_star]
      rw [completeSupportExtension_separated D E h (a i) (b j) hD hE (ha i) (hb j)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro ξ _
      ring
    · simp only [hi,hj,and_false,ite_false,divisorCoefficient,ite_true,zero_mul,star_zero,
        mul_zero,Finset.sum_const_zero]
  · simp only [hi,false_and,ite_false,divisorCoefficient,zero_mul,Finset.sum_const_zero,mul_zero]

theorem pair_ray_fubini {α β γ δ : Type*} [Fintype γ] [Fintype δ]
    (S : Finset α) (T : Finset β) (A : γ → δ → ℂ)
    (L : α → γ → ℂ) (R : β → δ → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, ∑ χ : γ, ∑ ξ : δ, A χ ξ * (L i χ * R j ξ) * K i j) =
      ∑ χ : γ, ∑ ξ : δ, A χ ξ * ∑ i ∈ S, ∑ j ∈ T, (L i χ * R j ξ) * K i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := S)]
  simp_rw [Finset.sum_comm (s := S) (t := Finset.univ)]
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.sum_comm (s := T)]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem finite_correlation_children {α β : Type*} (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a i - 1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b j - 1)
    (hcopA : ∀ i, IsCoprime (D * E) (a i)) (hcopB : ∀ j, IsCoprime (D * E) (b j))
    (h : O) (c : α → ℂ) (d : β → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) * actualCorrelation D E hD hE h *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
            pairCoeff (phaseTable D E) χ ξ *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
                  star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) * K i j := by
  rw [finite_correlation_mobius S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB h c d K]
  apply Finset.sum_congr rfl
  intro L hL
  simp_rw [divisor_pair_separation L a b c d D E h hD hE ha hb]
  simp_rw [← Finset.mul_sum (s := T), ← Finset.mul_sum (s := S)]
  rw [pair_ray_fubini]
  ring

theorem separated_pair_rowPolynomials {α β : Type*} (S : Finset α) (T : Finset β)
    (L : Ideal O) (a : α → O) (b : β → O) (c : α → ℂ) (d : β → ℂ)
    (χ ξ : RayCharacter) (f : α → ℂ) (g : β → ℂ) (h : O) :
    (∑ i ∈ S, ∑ j ∈ T,
      ((divisorCoefficient L a c χ i * idealRowHom h (Ideal.span {a i})) *
        star (divisorCoefficient L b d (ξ⁻¹) j * idealRowHom (-h) (Ideal.span {b j}))) *
        (f i * star (g j))) =
      rowPolynomial S a (fun i => divisorCoefficient L a c χ i * f i) h *
        star (rowPolynomial T b (fun j => divisorCoefficient L b d (ξ⁻¹) j * g j) (-h)) := by
  simp only [rowPolynomial, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end SevenEighths.CenteredMomentChildAssembly

end

end OAI
end OAIOriginalModule1466

/-! Original module: OAI.NumberTheory.DirichletL.Moments.GaussEnergy
Source SHA256: e91c9f7a2ae35f14ce944534e8e2977833a023dc316f6e59c00a0b5d97a3b10e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1467


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentGaussEnergy
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentFourier CenteredMomentPoisson
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def gaussRow (a : O) (ha : Supported (Ideal.span {a})) (z : O) : ℂ :=
  ProbePhysical.sexticGauss a (supported_element_ne_zero a ha) z /
    (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)

theorem gaussRow_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => gaussRow a ha z * star (gaussRow b hb z) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  let P : Residue (a * b) → ℂ := fun x =>
    normalizedResidueGauss a (supported_element_ne_zero a ha)
      (supportedModulusCharacter a ha) (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (normalizedResidueGauss b (supported_element_ne_zero b hb)
      (supportedModulusCharacter b hb) (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) P
  simpa only [P, frequencyReduction_mk, normalizedResidueGauss,
    residueGauss_supported_mk, scaledRadialTest_apply, gaussRow] using hs

def gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : O) : ℂ :=
  ∑ i ∈ S, c i * gaussRow (a i) (ha i) z

def gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O, ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖eisEmbedding z‖ ^ 2 / K)

theorem gaussPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : O) :
    ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [gaussPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gaussEnergy_expand {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    gaussEnergy S a ha c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : O, (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) *
          W (‖eisEmbedding z‖ ^ 2 / K) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussEnergy, gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)).summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp only [tsum_mul_left]

theorem gaussEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖ ^ 2 / K)) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  exact (hasSum_sum (fun i _ =>
    (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

theorem finite_energy_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  have hs := Complex.hasSum_re (gaussEnergy_summable S a ha c W K hK).hasSum
  change HasSum _ (gaussEnergy S a ha c W K).re at hs
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hs
  calc
    _ ≤ ∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2 *
        (W (‖eisEmbedding z‖ ^ 2 / K)).re := by
      apply Finset.sum_le_sum
      intro z hz
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z)) hs

theorem gaussEnergy_poisson {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    gaussEnergy S a ha c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ) *
          (Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ) : ℂ))) *
          ∑' h : O, actualCorrelation (a i) (a j) (ha i) (ha j) (-h) *
            paperRadialFourier W
              (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (a i * a j)‖ ^ 2)) := by
  rw [gaussEnergy_expand S a ha c W K hK]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [gaussRow]
  rw [sextic_gauss_pair_poisson (a i) (a j) (ha i) (ha j) W K hK]

end SevenEighths.CenteredMomentGaussEnergy

end

end OAI
end OAIOriginalModule1467

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ChildEnergy
Source SHA256: 4a3d78b6f6b0a86792fb8d95cf27541bb59e795553ee6783c56d62ef2dd63071
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1468



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem leftColumn_eq_gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    leftColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      gaussPolynomial S a ha (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn gaussPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rightColumn_eq_star_gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    rightColumn S (fun i => c i * gaussRow (a i) (ha i) z) V u t =
      star (gaussPolynomial S a ha (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, gaussPolynomial, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem whole_kernel_gauss_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i, Supported (Ideal.span {a i}))
        (hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (gaussEnergy S a ha (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (gaussEnergy T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * gaussRow (a i) (ha i) z) * star (d j * gaussRow (b j) (hb j) z)) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * gaussRow (a i) (ha i) z)
    (fun z j => d j * gaussRow (b j) (hb j) z) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_gaussEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_energy_le_gaussEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial S a ha (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) z‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_gaussPolynomial, rightColumn_eq_star_gaussPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentChildEnergy

end

end OAI
end OAIOriginalModule1468

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PlainEnergy
Source SHA256: 6314ca7721d52278d3e88513d6a844835384dcf8195b205f31915c2723bf94e0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1469


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentPlainEnergy
open CanonicalQuadraticSieve CenteredMomentRowNorm ConcreteTraceCRT
open CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

theorem rowEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖rowPolynomial S a c z‖^2 : ℝ) : ℂ) *
      W (‖eisEmbedding z‖^2/K)) := by
  have hs (i j : α) := (row_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [rowPolynomial_norm_sq,Finset.sum_mul,mul_assoc]
  exact (hasSum_sum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

theorem finite_energy_le_rowEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c z‖^2) ≤ (rowEnergy S a c W K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c W K hK).hasSum
  change HasSum _ (rowEnergy S a c W K).re at hs
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hs
  calc
    _ ≤ ∑ z ∈ rows, ‖rowPolynomial S a c z‖^2*(W (‖eisEmbedding z‖^2/K)).re := by
      apply Finset.sum_le_sum
      intro z hz
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z)) hs

theorem finite_negative_energy_le_rowEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖eisEmbedding z‖^2/K)).re) :
    (∑ z ∈ rows, ‖rowPolynomial S a c (-z)‖^2) ≤ (rowEnergy S a c W K).re := by
  have he := finite_energy_le_rowEnergy S a ha c W K hK (rows.image Neg.neg) hW (by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    simpa only [map_neg,norm_neg] using hmajor w hw)
  rwa [Finset.sum_image (fun x hx y hy hxy => neg_injective hxy)] at he

end SevenEighths.CenteredMomentPlainEnergy

end

end OAI
end OAIOriginalModule1469

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PlainChildEnergy
Source SHA256: c03041b409b0ed173fa4b2b1ae00f6075b51d8f3dcc088e5e554a9a64008ea9b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1470



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentPlainChildEnergy
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm CenteredMomentPlainEnergy CenteredMomentCauchy
open CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem leftColumn_eq_rowPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    leftColumn S (fun i => c i * idealRowHom z (Ideal.span {a i})) V u t =
      rowPolynomial S a (fun i => c i * columnPhase V (u i) t) z := by
  unfold leftColumn rowPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rightColumn_eq_star_rowPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (z : O) (t : ℝ) :
    rightColumn S (fun i => c i * idealRowHom z (Ideal.span {a i})) V u t =
      star (rowPolynomial S a (fun i => c i * star (columnPhase V (u i) t)) z) := by
  simp only [rightColumn, rowPolynomial, star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem whole_kernel_plain_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (_ha : ∀ i, Supported (Ideal.span {a i}))
        (_hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (rowEnergy S a (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (rowEnergy T b (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * idealRowHom z (Ideal.span {a i})) * star (d j * idealRowHom (-z) (Ideal.span {b j}))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * idealRowHom z (Ideal.span {a i}))
    (fun z j => d j * idealRowHom (-z) (Ideal.span {b j})) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_rowEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_negative_energy_le_rowEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial S a (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖rowPolynomial T b (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_rowPolynomial, rightColumn_eq_star_rowPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentPlainChildEnergy

end

end OAI
end OAIOriginalModule1470

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectedChild
Source SHA256: 773dc16de3bf361d1d51593843a3843128433ef0fa14690e1b5f3659c29e9df1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1471


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentReflectedChild
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentCauchy
open CenteredMomentSmooth CenteredMomentChildEnergy
local notation "O" => ActualEisensteinCubic.O

theorem finite_reflected_energy_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c (-z)‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  have hh := finite_energy_le_gaussEnergy S a ha c W K hK (rows.image Neg.neg) hW
    (by intro z hz;obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa only [map_neg,norm_neg] using hmajor w hw)
  rw [Finset.sum_image] at hh
  · exact hh
  · intro x hx y hy hxy
    exact neg_injective hxy

theorem whole_kernel_reflected_gauss_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i, Supported (Ideal.span {a i}))
        (hb : ∀ j, Supported (Ideal.span {b j}))
        (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η : O → ℂ),
      (∀ z ∈ rows, ‖η z‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (gaussEnergy S a ha (fun i => c i * columnPhase (V 2) (u i) t) U K).re ≤
        (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (gaussEnergy T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) U K).re ≤
        (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ‖∑ z ∈ rows, η z *
        (∑ i ∈ S, ∑ j ∈ T,
          ((c i * gaussRow (a i) (ha i) z) * star (d j * gaussRow (b j) (hb j) (-z))) *
            wholeKernel W V R (ρ z) (x z) (u i) (v j))‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR α β rows S T a b ha hb c d u v ρ x η hη hV₀ hV₁ U K hK hU hmajor
    E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound R hR rows S T
    (fun z i => c i * gaussRow (a i) (ha i) z)
    (fun z j => d j * gaussRow (b j) (hb j) (-z)) u v ρ x η hη hV₀ hV₁
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL := (finite_energy_le_gaussEnergy S a ha
    (fun i => c i * columnPhase (V 2) (u i) t) U K hK rows hU hmajor).trans (hleft t)
  have hR' := (finite_reflected_energy_le_gaussEnergy T b hb
    (fun j => d j * star (columnPhase (V 3) (v j) t)) U K hK rows hU hmajor).trans (hright t)
  have hl : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial S a ha (fun i => c i * columnPhase (V 2) (u i) t) z‖ ^ 2) ≤
      E₁ * (1 + ‖t‖) ^ J₁ := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr : Real.sqrt (∑ z ∈ rows,
      ‖gaussPolynomial T b hb (fun j => d j * star (columnPhase (V 3) (v j) t)) (-z)‖ ^ 2) ≤
      E₂ * (1 + ‖t‖) ^ J₂ := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  simp only [leftColumn_eq_gaussPolynomial, rightColumn_eq_star_gaussPolynomial, norm_star]
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentReflectedChild

end

end OAI
end OAIOriginalModule1471

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGaussEnergy
Source SHA256: f0bd6e81c8f86abf32c5993333f9d9c424cefa790ab3b0bafc9b8fa5ae385c9d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1472



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGaussColumn (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) : ℂ :=
  if physicalIdealRay s=σ then
    (Y:ℂ)⁻¹*W1 ((Ideal.absNorm s.val:ℝ)/Y)*lowArithmeticCoefficient C s*
      (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)
  else 0

lemma lowGaussColumn_row (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) (m : O) :
    (if physicalIdealRay s=σ then lowAdditiveCoefficient C W1 Y s m v else 0)=
      lowGaussColumn C W1 Y σ v s*
        gaussRow (primaryGenerator s.val) ((supported_span_primaryGenerator_iff s.val).mpr s.property) (-m) := by
  have he := (primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1
  unfold lowGaussColumn gaussRow
  rw [congrArg Ideal.absNorm he]
  split_ifs
  · rw [lowAdditiveCoefficient_eq]
    simp only [div_eq_mul_inv]
    ring
  · simp

theorem lowRayAmplitude_gaussPolynomial (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀σ : RayRing,∀v : ℝ,∀m : O,
      lowRayAmplitude C W1 Y σ m v=
        gaussPolynomial F (fun s=>primaryGenerator s.val)
          (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
          (lowGaussColumn C W1 Y σ v) (-m) := by
  obtain ⟨F,hF⟩ := lowRayAmplitude_eq_finite C W1 hW1 Y hY
  refine ⟨F,?_⟩
  intro σ v m
  rw [hF σ m v]
  unfold gaussPolynomial
  apply Finset.sum_congr rfl
  intro s hs
  exact lowGaussColumn_row C W1 Y σ v s m

theorem lowRayAmplitude_energy (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    ∃F : Finset {I : Id // Supported I},∀σ : RayRing,∀v : ℝ,
      ∀U : SchwartzMap ℝ ℂ,∀Q : ℝ,0<Q→∀rows : Finset O,
      (∀z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/Q)).re)→
      (∀z∈rows,1≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/Q)).re)→
      (∑z∈rows,‖lowRayAmplitude C W1 Y σ z v‖^2)≤
        (gaussEnergy F (fun s=>primaryGenerator s.val)
          (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
          (lowGaussColumn C W1 Y σ v) U Q).re := by
  obtain ⟨F,hF⟩ := lowRayAmplitude_gaussPolynomial C W1 hW1 Y hY
  refine ⟨F,?_⟩
  intro σ v U Q hQ rows hU hmajor
  simp_rw [hF σ v]
  exact CenteredMomentReflectedChild.finite_reflected_energy_le_gaussEnergy F
    (fun s=>primaryGenerator s.val) (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
    (lowGaussColumn C W1 Y σ v) U Q hQ rows hU hmajor

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1472

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowColumnBounds
Source SHA256: 807aa1a67c730624d734dd6063c69b1e95329bbb9fab993687474c7c0e203766
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1473


namespace OAI

noncomputable section
open scoped Classical
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGaussColumns (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) :
    Finset {I : Id // Supported I} :=
  ((idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn).toFinset

lemma lowGaussColumns_mem (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y)
    (s : {I : Id // Supported I}) :
    s∈lowGaussColumns W1 hW1 Y hY ↔ W1 ((Ideal.absNorm s.val:ℝ)/Y)≠0 := by
  simp only [lowGaussColumns,Set.Finite.mem_toFinset,Set.mem_preimage,Function.mem_support]

lemma lowRayAmplitude_source_columns (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (m : O) :
    lowRayAmplitude C W1 Y σ m v=
      CenteredMomentGaussEnergy.gaussPolynomial (lowGaussColumns W1 hW1 Y hY)
        (fun s=>primaryGenerator s.val)
        (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
        (lowGaussColumn C W1 Y σ v) (-m) := by
  unfold lowRayAmplitude
  rw [tsum_eq_sum (s:=lowGaussColumns W1 hW1 Y hY) (fun s hs=>by
    have hz : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0 := by
      simpa only [lowGaussColumns_mem,not_not] using hs
    simp only [lowAdditiveCoefficient_outer_zero C W1 Y s m v hz,ite_self])]
  unfold CenteredMomentGaussEnergy.gaussPolynomial
  exact Finset.sum_congr rfl (fun s _=>lowGaussColumn_row C W1 Y σ v s m)

lemma lowGaussColumns_card (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 1≤Y)
    (a b : ℝ) (hW : Function.support W1⊆Set.Icc a b) :
    ((lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY)).card:ℝ)≤128*max 1 b*Y := by
  let F := lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY)
  have hH : 1≤max 1 b*Y := one_le_mul_of_one_le_of_one_le (le_max_left _ _) hY
  have hh := DescentFiberCost.finite_ideal_count_real (F.image Subtype.val) (max 1 b*Y) hH
    (by intro I hI;obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hI;exact s.property.1)
    (by
      intro I hI
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hI
      have hw := (hW ((lowGaussColumns_mem W1 hW1 Y _ s).mp hs)).2
      have hn : (Ideal.absNorm s.val:ℝ)≤b*Y := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hY)).mp hw
      exact hn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_trans zero_le_one hY)))
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hh
  simpa only [mul_assoc,F] using hh

lemma lowGaussColumn_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (W1 : ℝ→ℂ) (a b B : ℝ) (ha : 0<a) (hB : 0≤B)
    (hW : Function.support W1⊆Set.Icc a b) (hWB : ∀x,‖W1 x‖≤B)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) :
    ‖lowGaussColumn (calibrationForSet S hS) W1 Y σ v s‖≤
      B*a^(-(1/2:ℝ))/Y := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  by_cases hzero : W1 ((Ideal.absNorm s.val:ℝ)/Y)=0
  · simp only [lowGaussColumn,hzero,mul_zero,zero_mul,ite_self,norm_zero]
    positivity
  have hqa := (hW hzero).1
  have hp : ‖(((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)‖=
      ((Ideal.absNorm s.val:ℝ)/Y)^(-(1/2:ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hq hY)]
    congr 1
    simp
  have hr : ((Ideal.absNorm s.val:ℝ)/Y)^(-(1/2:ℝ))≤a^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha hqa (by norm_num)
  unfold lowGaussColumn
  split_ifs
  · rw [norm_mul,norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,hp]
    calc
      _ ≤ Y⁻¹*B*1*a^(-(1/2:ℝ)) := by
        gcongr
        · exact hWB _
        · exact lowArithmeticCoefficient_source_norm S hS s
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem lowGaussColumn_l2_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀hS : ∀P∈S,P.IsMaximal,
      ∀W1 : ℝ→ℂ,∀hW1 : HasCompactSupport W1,
      Function.support W1⊆Set.Icc a b → (∀x,‖W1 x‖≤B) →
      ∀Y : ℝ,∀hY : 1≤Y,∀σ : RayRing,∀v : ℝ,
      (∑s∈lowGaussColumns W1 hW1 Y (lt_of_lt_of_le zero_lt_one hY),
        ‖lowGaussColumn (calibrationForSet S hS) W1 Y σ v s‖^2)≤C/Y := by
  let C := 128*max 1 b*(B*a^(-(1/2:ℝ)))^2+1
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro S hS W1 hW1 hW hWB Y hY σ v
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have hcoef (s : {I : Id // Supported I}) := lowGaussColumn_norm_bound S hS W1 a b B ha hB hW hWB Y hy σ v s
  calc
    _ ≤ ∑_s∈lowGaussColumns W1 hW1 Y hy,(B*a^(-(1/2:ℝ))/Y)^2 := by
      apply Finset.sum_le_sum
      intro s hs
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoef s) 2
    _ = ((lowGaussColumns W1 hW1 Y hy).card:ℝ)*(B*a^(-(1/2:ℝ))/Y)^2 := by simp
    _ ≤ (128*max 1 b*Y)*(B*a^(-(1/2:ℝ))/Y)^2 :=
      mul_le_mul_of_nonneg_right (lowGaussColumns_card W1 hW1 Y hY a b hW) (sq_nonneg _)
    _ = (128*max 1 b*(B*a^(-(1/2:ℝ)))^2)/Y := by field_simp
    _ ≤ C/Y := div_le_div_of_nonneg_right (by dsimp only [C];linarith) hy.le

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1473

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowActualEnergies
Source SHA256: c7e3fb2a96e6a0875fd6be32ae9d17f6f6c18e18c8210459322834ecadd4ade6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1474



namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

def lowNumeratorRows (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q) : Finset O :=
  (elementWindow_finite_support (lowOuterCutoff a b) (lowOuterCutoff_compact a b ha hb) Q hQ).toFinset

lemma lowNumeratorRows_mem (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q) (m : O) :
    m∈lowNumeratorRows a b ha hb Q hQ ↔ lowOuterCutoff a b (elementNorm m/Q)≠0 := by
  simp only [lowNumeratorRows,Set.Finite.mem_toFinset,Function.mem_support]

def lowGaussMajorant (a b : ℝ) (ha : 0<a) (hb : 0<b) : SchwartzMap ℝ ℂ :=
  (lowOuterCutoff_compact (a/2) (2*b) (by positivity) (by positivity)).toSchwartzMap
    (lowOuterCutoff_smooth (a/2) (2*b))

lemma lowGaussMajorant_nonneg (a b : ℝ) (ha : 0<a) (hb : 0<b) (x : ℝ) :
    0≤(lowGaussMajorant a b ha hb x).re := by
  change 0≤(lowOuterCutoff (a/2) (2*b) x).re
  simp only [lowOuterCutoff,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma lowGaussMajorant_on_rows (a b : ℝ) (ha : 0<a) (hb : 0<b) (Q : ℝ) (hQ : 0<Q)
    (m : O) (hm : m∈lowNumeratorRows a b ha hb Q hQ) :
    lowGaussMajorant a b ha hb (‖ConcreteTraceCRT.eisEmbedding m‖^2/Q)=1 := by
  have hh := lowOuterCutoff_support a b ha hb ((lowNumeratorRows_mem a b ha hb Q hQ m).mp hm)
  change lowOuterCutoff (a/2) (2*b) (‖ConcreteTraceCRT.eisEmbedding m‖^2/Q)=1
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  exact lowOuterCutoff_one _ _ (by positivity) (by positivity) _ hh.1 hh.2

theorem lowRayAmplitude_actual_energy (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v Q : ℝ) (hQ : 0<Q) :
    (∑m∈lowNumeratorRows a b ha hb Q hQ,‖lowRayAmplitude C W1 Y σ m v‖^2)≤
      (gaussEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
        (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
        (lowGaussColumn C W1 Y σ v) (lowGaussMajorant a b ha hb) Q).re := by
  simp_rw [lowRayAmplitude_source_columns C W1 hW1 Y hY σ v]
  exact CenteredMomentReflectedChild.finite_reflected_energy_le_gaussEnergy _ _ _ _ _ Q hQ _
    (fun _=>lowGaussMajorant_nonneg a b ha hb _)
    (fun m hm=>by rw [lowGaussMajorant_on_rows a b ha hb Q hQ m hm];norm_num)

lemma lowSeparatedIntegrand_source_cauchy (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (X Y : ℝ) (hX : 0<X) (hY : 0<Y)
    (B : RayRing→O→ℂ) (v : ℝ) :
    ‖lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v‖≤
      ‖mellin W0 ((v:ℂ)*Complex.I)‖*
        ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY),
          ‖lowRayAmplitude C W1 Y σ m v‖^2)*
          Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY),‖B σ m‖^2) := by
  let R := lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY)
  have hR (m : O) (hm : m∉R) : lowNumeratorWeight C (lowOuterCutoff a b) X Y m v=0 := by
    have hz : lowOuterCutoff a b (elementNorm m/lowPhysicalScale C X Y)=0 := by
      simpa only [R,lowNumeratorRows_mem,not_not] using hm
    simp [lowNumeratorWeight,hz]
  have he : lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v=
      mellin W0 ((v:ℂ)*Complex.I)*
        ∑σ : RayRing,∑m∈R,lowNumeratorWeight C (lowOuterCutoff a b) X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m := by
    unfold lowSeparatedIntegrand
    change mellin W0 ((v:ℂ)*Complex.I)*
      (∑'m : O,lowNumeratorWeight C (lowOuterCutoff a b) X Y m v*∑σ : RayRing,lowRayAmplitude C W1 Y σ m v*B σ m)=_
    rw [tsum_eq_sum (s:=R) (fun m hm=>by rw [hR m hm,zero_mul])]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [he,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ∑σ : RayRing,‖∑m∈R,lowNumeratorWeight C (lowOuterCutoff a b) X Y m v*lowRayAmplitude C W1 Y σ m v*B σ m‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun σ _=>CenteredMomentCauchy.bounded_row_cauchy R
      (fun m=>lowNumeratorWeight C (lowOuterCutoff a b) X Y m v) (fun m=>lowRayAmplitude C W1 Y σ m v) (B σ)
      (fun m _=>lowNumeratorWeight_norm C _ (lowOuterCutoff_norm a b)
        (lowOuterCutoff_small a b ha 0 (by positivity)) X Y hX hY m v))

theorem lowSeparatedIntegrand_actual_energies (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) (v : ℝ) :
    ‖lowSeparatedIntegrand C W0 W1 (lowOuterCutoff a b) X Y B v‖≤
      ‖mellin W0 ((v:ℂ)*Complex.I)‖*
        ∑σ : RayRing,Real.sqrt ((gaussEnergy (lowGaussColumns W1 hW1 Y hY)
          (fun s=>primaryGenerator s.val) (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
          (lowGaussColumn C W1 Y σ v) (lowGaussMajorant a b ha hb) (lowPhysicalScale C X Y)).re)*
          Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY),‖B σ m‖^2) := by
  apply (lowSeparatedIntegrand_source_cauchy a b ha hb C W0 W1 X Y hX hY B v).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro σ hσ
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (lowRayAmplitude_actual_energy a b ha hb C W1 hW1 Y hY σ v
    (lowPhysicalScale C X Y) (lowPhysicalScale_pos C X Y hX hY))) (Real.sqrt_nonneg _)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1474

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGramProfile
Source SHA256: bba8c4d8d6a6fd68a0a653f1aac45f410fca089ddd58550081a0c0e24d8b48fb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1475


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramCoefficient (C : CalibrationData) (σ : RayRing)
    (s : {I : Id // Supported I}) : ℂ :=
  if physicalIdealRay s=σ then lowArithmeticCoefficient C s else 0

def lowGramProfile (W1 : ℝ→ℂ) (v r : ℝ) : ℂ :=
  W1 r*(r:ℂ)^(-1+(v:ℂ)*Complex.I)

def lowGramScale (Y : ℝ) : ℂ := (Y:ℂ)⁻¹*(Real.sqrt Y:ℂ)⁻¹

lemma lowGramCoefficient_source_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (s : {I : Id // Supported I}) :
    ‖lowGramCoefficient (calibrationForSet S hS) σ s‖≤1 := by
  unfold lowGramCoefficient
  split_ifs
  · exact lowArithmeticCoefficient_source_norm S hS s
  · simp

lemma lowGramProfile_norm (W1 : ℝ→ℂ) (v r : ℝ) (hr : 0<r) :
    ‖lowGramProfile W1 v r‖=‖W1 r‖/r := by
  rw [lowGramProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hr]
  simp only [Complex.add_re,Complex.neg_re,Complex.one_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero,
    Real.rpow_neg_one,div_eq_mul_inv]

lemma lowGramScale_cpow (Y : ℝ) (hY : 0<Y) : lowGramScale Y=(Y:ℂ)^(-(3/2:ℂ)) := by
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  rw [show -(3/2:ℂ)=(-1)+(-(1/2:ℂ)) by norm_num,Complex.cpow_add _ _ hy,
    Complex.cpow_neg_one,Complex.cpow_neg,ProbeEuler.cpow_half_eq_sqrt _ hY.le]
  rfl

lemma lowGramScale_mul_star (Y : ℝ) (hY : 0<Y) :
    lowGramScale Y*star (lowGramScale Y)=((Y^3:ℝ):ℂ)⁻¹ := by
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have hs : (Real.sqrt Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hY).ne'
  have hsquare : (Real.sqrt Y:ℂ)^2=(Y:ℂ) := by exact_mod_cast Real.sq_sqrt hY.le
  simp only [lowGramScale,map_mul,map_inv₀,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_pow]
  field_simp
  ring_nf
  rw [hsquare]

theorem lowGaussColumn_unnormalized (C : CalibrationData) (W1 : ℝ→ℂ)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (s : {I : Id // Supported I}) :
    lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)=
      lowGramScale Y*(lowGramCoefficient C σ s*
        lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y)) := by
  have hq : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  have hr : 0<(Ideal.absNorm s.val:ℝ)/Y := div_pos hq hY
  have hrc : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hsqrt : Real.sqrt (Ideal.absNorm s.val:ℝ)=
      Real.sqrt Y*Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y) := by
    rw [←Real.sqrt_mul hY.le,mul_div_cancel₀ _ hY.ne']
  have hp : (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
      (Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y):ℂ)⁻¹=
        (((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-1+(v:ℂ)*Complex.I) := by
    rw [←ProbeEuler.cpow_half_eq_sqrt _ hr.le,←Complex.cpow_neg,←Complex.cpow_add _ _ hrc]
    congr 1
    ring
  unfold lowGaussColumn lowGramCoefficient
  split_ifs
  · rw [hsqrt,Complex.ofReal_mul]
    simp only [div_eq_mul_inv,mul_inv_rev]
    calc
      _ = (Y:ℂ)⁻¹*(Real.sqrt Y:ℂ)⁻¹*(lowArithmeticCoefficient C s*W1 ((Ideal.absNorm s.val:ℝ)/Y))*
        ((((Ideal.absNorm s.val:ℝ)/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*
          (Real.sqrt ((Ideal.absNorm s.val:ℝ)/Y):ℂ)⁻¹) := by ring_nf
      _ = _ := by rw [hp];unfold lowGramScale lowGramProfile;ring_nf
  · simp

theorem lowRayAmplitude_unnormalized (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (m : O) :
    lowRayAmplitude C W1 Y σ m v=lowGramScale Y*
      ∑s∈lowGaussColumns W1 hW1 Y hY,
        lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y)*
          sexticGauss (primaryGenerator s.val) (supported_primaryGenerator_ne_zero s.val s.property) (-m) := by
  rw [lowRayAmplitude_source_columns C W1 hW1 Y hY σ v]
  unfold gaussPolynomial gaussRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have he := congrArg Ideal.absNorm ((primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1)
  rw [he]
  calc
    _ = (lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ))*
      sexticGauss (primaryGenerator s.val) (supported_primaryGenerator_ne_zero s.val s.property) (-m) := by ring
    _ = _ := by rw [lowGaussColumn_unnormalized C W1 Y hY σ v s];ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1475

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGramArithmetic
Source SHA256: bf0f768891c15321156627f4a4e1051e52818a7b36790e60c53fe76e47443b20
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1476



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcreteTraceCRT ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def gramPeriodicMonoid (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  conjugateMonoid C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported

lemma gramPeriodicMonoid_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (n : O) : ‖gramPeriodicMonoid C B D n‖≤1 := by
  rw [gramPeriodicMonoid,MonoidHom.mul_apply,norm_mul]
  change ‖star (C.residueMonoid n)‖*_≤1
  rw [norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one n)).trans (actualPeriodicRow_norm 1 (fun _=>by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported n)

lemma gramPeriodicMonoid_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (gramPeriodicMonoid C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=>rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change star (C.residueMonoid x)*_=star (C.residueMonoid y)*_
  congr 1
  · apply congrArg star
    apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left hxy)
  · exact hp x y (Ideal.mul_le_right hxy)

lemma gramPeriodicMonoid_zero (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (n : O) (hn : ¬IsCoprime B n) :
    gramPeriodicMonoid C B D n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hn]
  change star (C.residueMonoid n)*
    ((((1:O→*ℂ) n*coprimalityMask B n)*
      numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
      movingNumeratorRow D.numeratorGood D.numeratorSupported n)=0
  rw [hm]
  simp

lemma gramPeriodicMonoid_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    gramPeriodicMonoid C B D n=(C.residueMonoid n)⁻¹*idealRowHom C.generator (Ideal.span {n}) := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn] at he
  have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [ite_eq_left hc]
  simp only [MonoidHom.one_apply,hm,one_mul,one_pow] at he
  change star (C.residueMonoid n)*_=_
  rw [←he]
  congr 1
  let := finite_quotient_span C.generator_ne_zero
  let : Fintype (O⧸Ideal.span {C.generator}) := Fintype.ofFinite _
  change star (C.residue (Ideal.Quotient.mk _ n))=(C.residue (Ideal.Quotient.mk _ n))⁻¹
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']

theorem lowArithmeticCoefficient_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (s : {I : Id // Supported I}) :
    lowArithmeticCoefficient (calibrationForSet S hS) s=
      (calibrationForSet S hS).tau⁻¹*
        gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator
          (calibrationLowData S hS) (primaryGenerator s.val) := by
  let C := calibrationForSet S hS
  have hn := supported_primaryGenerator_ne_zero s.val s.property
  have he := (primaryGenerator_spec s.val hn).1
  have hp := (primaryGenerator_spec s.val hn).2
  have hsupp := (supported_span_primaryGenerator_iff s.val).mpr s.property
  have hb := calibration_generator_bad S hS hbad
  by_cases hc : IsCoprime C.generator (primaryGenerator s.val)
  · have hguard : ∀P∈C.excluded,¬P∣s.val := by
      rw [show C.excluded=S from calibrationForSet_excluded S hS,←he]
      exact (calibration_coprime_iff_excluded_span S hS _).mp hc
    rw [lowArithmeticCoefficient,ite_eq_left hguard,
      gramPeriodicMonoid_primary C C.generator (calibrationLowData S hS) hb.1 hb.2 _ hsupp hp hc,he]
    ring
  · have hguard : ¬∀P∈C.excluded,¬P∣s.val := by
      rw [show C.excluded=S from calibrationForSet_excluded S hS,←he]
      exact fun h=>hc ((calibration_coprime_iff_excluded_span S hS _).mpr h)
    rw [lowArithmeticCoefficient,ite_eq_right hguard,gramPeriodicMonoid_zero C C.generator (calibrationLowData S hS) _ hc,mul_zero]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1476

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGramFixedCoefficient
Source SHA256: e41627489e06ac66953e33821cf8c6e769a2eaa8371f63cca11ce1799ae58752
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1477


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gramFixedModulus (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  (Ideal.span {(calibrationForSet S hS).generator}*
    calibrationRowModulus (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS))*
      Ideal.span {(4:O)}

lemma gramFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : gramFixedModulus S hS≠0 := by
  unfold gramFixedModulus
  apply mul_ne_zero
  · exact mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (calibrationForSet S hS).generator_ne_zero)
      (calibrationRowModulus_ne_zero _ _ (calibrationForSet S hS).generator_ne_zero _)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

def gramCoefficientExtension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) : ℂ :=
  if physicalRay n=σ then (calibrationForSet S hS).tau⁻¹*
    gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS) n
  else 0

lemma gramCoefficientExtension_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) :
    ‖gramCoefficientExtension S hS σ n‖≤1 := by
  unfold gramCoefficientExtension
  split_ifs
  · rw [norm_mul,norm_inv,calibrationForSet_tau_norm,inv_one,one_mul]
    exact gramPeriodicMonoid_norm _ _ _ _
  · simp

lemma gramCoefficientExtension_zero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O)
    (hn : ¬IsCoprime (calibrationForSet S hS).generator n) : gramCoefficientExtension S hS σ n=0 := by
  unfold gramCoefficientExtension
  split_ifs
  · rw [gramPeriodicMonoid_zero _ _ _ _ hn,mul_zero]
  · rfl

theorem lowGramCoefficient_eq_extension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      gramCoefficientExtension S hS σ (primaryGenerator s.val) := by
  unfold lowGramCoefficient gramCoefficientExtension
  change (if physicalRay (primaryGenerator s.val)=σ then _ else 0)=_
  rw [lowArithmeticCoefficient_periodic S hS hbad s]

theorem gramCoefficientExtension_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (x y : O) (hxy : x-y∈gramFixedModulus S hS) :
    gramCoefficientExtension S hS σ x=gramCoefficientExtension S hS σ y := by
  have hr : physicalRay x=physicalRay y := Ideal.Quotient.eq.mpr (Ideal.mul_le_right hxy)
  have hm := gramPeriodicMonoid_periodic (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) x y (Ideal.mul_le_left hxy)
  simp only [gramCoefficientExtension,hr,hm]

lemma gramCoefficientExtension_scaled_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (d x y : O) (hxy : x-y∈gramFixedModulus S hS) :
    gramCoefficientExtension S hS σ (d*x)=gramCoefficientExtension S hS σ (d*y) := by
  apply gramCoefficientExtension_periodic
  rw [←mul_sub]
  exact (gramFixedModulus S hS).mul_mem_left d hxy

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1477

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramNumerator
Source SHA256: 72efa3c26c25e49179980f36ba00a21abd736b708f509ea32abbf2dc91f48510
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1478



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def numeratorExtension (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) : O→*ℂ :=
  numeratorBadTwist u a b r hr*movingNumeratorRow r hr

lemma numeratorExtension_norm (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n : O) :
    ‖numeratorExtension u a b r hr n‖≤1 := by
  rw [numeratorExtension,MonoidHom.mul_apply,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (numeratorBadTwist_norm _ _ _ _ _ _)).trans (movingNumeratorRow_norm _ _ _)

lemma numeratorExtension_periodic (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Ideal.span {(72:O)}*Ideal.span {r})
      (numeratorExtension u a b r hr) := by
  intro x y hxy
  change numeratorBadTwist u a b r hr x*movingNumeratorRow r hr x=
    numeratorBadTwist u a b r hr y*movingNumeratorRow r hr y
  rw [numeratorBadTwist_periodic _ _ _ _ _ x y (Ideal.mul_le_left hxy),
    movingNumeratorRow_periodic _ _ x y (Ideal.mul_le_right hxy)]

lemma numeratorExtension_primary (u : Oˣ) (a b : ℕ) (r k n : O)
    (hr : Supported (Ideal.span {r})) (hpr : λ₀^2∣r-1)
    (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) :
    numeratorExtension u a b r hr n=idealRowHom k (Ideal.span {n}) := by
  rw [hk]
  exact (idealRowHom_factor_numerator u a b r n hr hpr hn hpn).symm

lemma numeratorExtension_neg_primary (u : Oˣ) (a b : ℕ) (r k n : O)
    (hr : Supported (Ideal.span {r})) (hpr : λ₀^2∣r-1)
    (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) :
    numeratorExtension (-u) a b r hr n=idealRowHom (-k) (Ideal.span {n}) := by
  apply numeratorExtension_primary _ _ _ _ _ _ hr hpr _ hn hpn
  simp only [Units.val_neg,hk]
  ring

lemma numerator_good_norm_le (u : Oˣ) (a b : ℕ) (r k : O)
    (hk : k=u.val*λ₀^a*(2:O)^b*r) (hk0 : k≠0) :
    Ideal.absNorm (Ideal.span {r})≤Ideal.absNorm (Ideal.span {k}) := by
  apply Nat.le_of_dvd
  · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hk0))
  · apply map_dvd Ideal.absNorm
    rw [Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact ⟨u.val*λ₀^a*(2:O)^b,by rw [hk];ring⟩

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1478

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramJointFixed
Source SHA256: e7ca0544e169878f2b6d6aa030fe92af9440fb4077a1c5b79f57a799c78292e8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1479


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def primaryCoefficient (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) : ℂ :=
  if λ₀^2∣n-1 then gramCoefficientExtension S hS σ n else 0

lemma primaryCoefficient_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) :
    ‖primaryCoefficient S hS σ n‖≤1 := by
  unfold primaryCoefficient
  split_ifs
  · exact gramCoefficientExtension_norm _ _ _ _
  · simp

def jointFixedModulus (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  gramFixedModulus S hS*Ideal.span {λ₀^2}*Ideal.span {(72:O)}

lemma jointFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : jointFixedModulus S hS≠0 := by
  apply mul_ne_zero
  · apply mul_ne_zero (gramFixedModulus_nonzero S hS)
    exact Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero _ ConcretePrimeRowBridge.goodLambda_prime.ne_zero)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

lemma primaryCoefficient_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (x y : O) (hxy : x-y∈jointFixedModulus S hS) :
    primaryCoefficient S hS σ x=primaryCoefficient S hS σ y := by
  have hg := gramCoefficientExtension_periodic S hS σ x y (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hp : λ₀^2∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_right (Ideal.mul_le_left hxy))
  have hi : (λ₀^2∣x-1)↔(λ₀^2∣y-1) := by
    constructor
    · intro h
      convert dvd_sub h hp using 1 ; ring
    · intro h
      convert dvd_add hp h using 1 ; ring
  simp only [primaryCoefficient,hi,hg]

def jointFixed (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ : O) : ℂ :=
  primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
    numeratorBadTwist u a b r hr n₁*star (numeratorBadTwist (-u) a b r hr n₂)*
      sexticReciprocityPhase n₁ n₂

lemma jointFixed_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ : O) :
    ‖jointFixed S hS σ C u a b r hr n₁ n₂‖≤1 := by
  unfold jointFixed
  simp only [norm_mul,norm_star]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (sexticReciprocityPhase_norm _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (numeratorBadTwist_norm _ _ _ _ _ _)
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (numeratorBadTwist_norm _ _ _ _ _ _)
  exact (mul_le_of_le_one_left (norm_nonneg _) (primaryCoefficient_norm _ _ _ _)).trans (primaryCoefficient_norm _ _ _ _)

lemma jointFixed_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (n₁ n₂ m₁ m₂ : O)
    (h₁ : n₁-m₁∈jointFixedModulus S hS) (h₂ : n₂-m₂∈jointFixedModulus S hS) :
    jointFixed S hS σ C u a b r hr n₁ n₂=jointFixed S hS σ C u a b r hr m₁ m₂ := by
  have hc₁ := primaryCoefficient_periodic S hS σ (C*n₁) (C*m₁)
    (by rw [←mul_sub];exact (jointFixedModulus S hS).mul_mem_left C h₁)
  have hc₂ := primaryCoefficient_periodic S hS σ (C*n₂) (C*m₂)
    (by rw [←mul_sub];exact (jointFixedModulus S hS).mul_mem_left C h₂)
  have hb₁ := numeratorBadTwist_periodic u a b r hr n₁ m₁ (Ideal.mul_le_right h₁)
  have hb₂ := numeratorBadTwist_periodic (-u) a b r hr n₂ m₂ (Ideal.mul_le_right h₂)
  have hfour (x y : O) (h : x-y∈jointFixedModulus S hS) : (4:O)∣x-y :=
    (show (4:O)∣72 from ⟨18,by norm_num⟩).trans (Ideal.mem_span_singleton.mp (Ideal.mul_le_right h))
  have hp : sexticReciprocityPhase n₁ n₂=sexticReciprocityPhase m₁ m₂ := by
    unfold sexticReciprocityPhase
    rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub n₁ m₁ (hfour _ _ h₁),
      QuadraticGaussRay.residue_eq_of_four_dvd_sub n₂ m₂ (hfour _ _ h₂)]
  simp only [jointFixed,hc₁,hc₂,hb₁,hb₂,hp]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1479

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramJoint
Source SHA256: a30a7cb48f7bcf839267160dcf01536a74657043799cf4957195c8a79535a518
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1480


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

def jointExtension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (n₁ n₂ : O) : ℂ :=
  jointFixed S hS σ C u a b r hr n₁ n₂*
    (idealRowHom n₁ (Ideal.span {r})*star (idealRowHom n₂ (Ideal.span {r})))*
      globalExtension P hg c n₁ n₂ k

lemma jointExtension_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ) (hc : ∀i,1≤c i)
    (n₁ n₂ : O) : ‖jointExtension S hS σ C k u a b r hr P hg c n₁ n₂‖≤Ideal.absNorm (∏i,P i^c i) := by
  rw [jointExtension,norm_mul]
  have ha : ‖jointFixed S hS σ C u a b r hr n₁ n₂*
      (idealRowHom n₁ (Ideal.span {r})*star (idealRowHom n₂ (Ideal.span {r})))‖≤1 := by
    rw [norm_mul,norm_mul,norm_star]
    exact (mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (jointFixed_norm _ _ _ _ _ _ _ _ _ _ _)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans (idealRowHom_norm _ _))
  exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using globalExtension_norm P hg c hc n₁ n₂ k)

def jointPeriod (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (P : ι→Id) (r : O) : Id :=
  jointFixedModulus S hS*(∏i,P i)*Ideal.span {r}

lemma jointExtension_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (n₁ n₂ m₁ m₂ : O) (h₁ : n₁-m₁∈jointPeriod S hS P r) (h₂ : n₂-m₂∈jointPeriod S hS P r) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      jointExtension S hS σ C k u a b r hr P hg c m₁ m₂ := by
  have hf := jointFixed_periodic S hS σ C u a b r hr n₁ n₂ m₁ m₂
    (Ideal.mul_le_left (Ideal.mul_le_left h₁)) (Ideal.mul_le_left (Ideal.mul_le_left h₂))
  have hm₁ := idealRowHom_congr_mod (Ideal.span {r}) n₁ m₁ (Ideal.mul_le_right h₁)
  have hm₂ := idealRowHom_congr_mod (Ideal.span {r}) n₂ m₂ (Ideal.mul_le_right h₂)
  have he := globalExtension_periodic P hg c n₁ n₂ m₁ m₂ k k
    (Ideal.mul_le_right (Ideal.mul_le_left h₁)) (Ideal.mul_le_right (Ideal.mul_le_left h₂)) (by simp)
  simp only [jointExtension,hf,hm₁,hm₂,he]

lemma jointExtension_dilation_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (d n₁ n₂ m₁ m₂ : O) (h₁ : n₁-m₁∈jointPeriod S hS P r) (h₂ : n₂-m₂∈jointPeriod S hS P r) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)=
      jointExtension S hS σ C k u a b r hr P hg c (d*m₁) (d*m₂) := by
  apply jointExtension_periodic
  · rw [←mul_sub];exact (jointPeriod S hS P r).mul_mem_left d h₁
  · rw [←mul_sub];exact (jointPeriod S hS P r).mul_mem_left d h₂

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1480

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramJointSource
Source SHA256: a142826e225c4286b90f7abdbb7262ab87671364d5a4762cb98734c97d5e6356
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1481


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentSupportedCorrelation CenteredMomentCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

theorem jointExtension_source (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : Supported (Ideal.span {C}))
    (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (hpr : λ₀^2∣r-1) (hk : k=u.val*λ₀^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (hcop : Pairwise (Function.onFun IsCoprime P))
    (he : Ideal.span {C}=∏i,P i^c i)
    [Fintype (O⧸∏i,P i^c i)] [∀i,Fintype (O⧸P i^c i)]
    (n₁ n₂ : O) (h₁ : Supported (Ideal.span {n₁})) (h₂ : Supported (Ideal.span {n₂}))
    (hp₁ : λ₀^2∣n₁-1) (hp₂ : λ₀^2∣n₂-1) (hn : IsCoprime n₁ n₂) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      primaryCoefficient S hS σ (C*n₁)*star (primaryCoefficient S hS σ (C*n₂))*
        actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
          (supported_mul_elements C n₂ hC h₂) (C*k) := by
  rw [actual_common_lift C n₁ n₂ k hC h₁ h₂ hp₁ hp₂ hn,
    actualCommon_eq_globalExtension C hC P hg c hc hcop he n₁ n₂ k hn,
    ←numeratorExtension_primary u a b r k n₁ hr hpr hk h₁ hp₁,
    ←numeratorExtension_neg_primary u a b r k n₂ hr hpr hk h₂ hp₂]
  simp only [jointExtension,jointFixed,numeratorExtension,MonoidHom.mul_apply,
    movingNumeratorRow,MonoidHom.coe_mk,OneHom.coe_mk,star_mul]
  ring

lemma lowGramCoefficient_eq_primary (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      primaryCoefficient S hS σ (primaryGenerator s.val) := by
  have hp : λ₀^2∣primaryGenerator s.val-1 := (primaryGenerator_spec s.val
    (supported_primaryGenerator_ne_zero s.val s.property)).2
  rw [primaryCoefficient,ite_eq_left hp]
  exact lowGramCoefficient_eq_extension S hS hbad σ s

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1481

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramGcd
Source SHA256: 0b4ac98d07f67fd7a90a40ae660d2f393139a9791f3d338444b7cf44b46960dc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1482


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
abbrev SupportedIdeal := {I : Id // Supported I}

lemma gram_supported_divisor (I D : Id) (hI : Supported I) (hd : D∣I) : Supported D := by
  obtain ⟨J,rfl⟩ := hd
  exact (supported_mul_iff D J).mp hI |>.1

lemma gram_supported_quotient (I D : Id) (hI : Supported I) (hd : D∣I) :
    Supported (idealQuotient D I) := gram_supported_divisor I _ hI (idealQuotient_dvd hd)

def gcdCommon (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨gcd I.val J.val,gram_supported_divisor I.val _ I.property (gcd_dvd_left _ _)⟩

def gcdLeft (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨idealQuotient (gcdCommon I J).val I.val,
    gram_supported_quotient I.val _ I.property (gcd_dvd_left _ _)⟩

def gcdRight (I J : SupportedIdeal) : SupportedIdeal :=
  ⟨idealQuotient (gcdCommon I J).val J.val,
    gram_supported_quotient J.val _ J.property (gcd_dvd_right _ _)⟩

lemma gcd_residual_coprime (I J : SupportedIdeal) : IsCoprime (gcdLeft I J).val (gcdRight I J).val :=
  (gcd_eq_iff_quotient_coprime _ _ _ (gcdCommon I J).property.1
    (gcd_dvd_left _ _) (gcd_dvd_right _ _)).mp rfl

lemma gcd_common_left (I J : SupportedIdeal) : (gcdCommon I J).val*(gcdLeft I J).val=I.val :=
  idealQuotient_mul (gcd_dvd_left _ _)

lemma gcd_common_right (I J : SupportedIdeal) : (gcdCommon I J).val*(gcdRight I J).val=J.val :=
  idealQuotient_mul (gcd_dvd_right _ _)

abbrev CoprimeTriple := {t : SupportedIdeal×SupportedIdeal×SupportedIdeal // IsCoprime t.2.1.val t.2.2.val}

def gcdTriple (p : SupportedIdeal×SupportedIdeal) : CoprimeTriple :=
  ⟨(gcdCommon p.1 p.2,gcdLeft p.1 p.2,gcdRight p.1 p.2),gcd_residual_coprime p.1 p.2⟩

def multiplyTriple (t : CoprimeTriple) : SupportedIdeal×SupportedIdeal :=
  (⟨t.val.1.val*t.val.2.1.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.1.property⟩⟩,
   ⟨t.val.1.val*t.val.2.2.val,(supported_mul_iff _ _).mpr ⟨t.val.1.property,t.val.2.2.property⟩⟩)

lemma multiply_gcdTriple (p : SupportedIdeal×SupportedIdeal) : multiplyTriple (gcdTriple p)=p := by
  apply Prod.ext <;> apply Subtype.ext
  · exact gcd_common_left _ _
  · exact gcd_common_right _ _

lemma gcdTriple_multiply (t : CoprimeTriple) : gcdTriple (multiplyTriple t)=t := by
  have he : gcd (t.val.1.val*t.val.2.1.val) (t.val.1.val*t.val.2.2.val)=t.val.1.val := by
    rw [_root_.gcd_mul_left,normalize_eq,Ideal.isCoprime_iff_gcd.mp t.property,mul_one]
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext he
  · apply Prod.ext <;> apply Subtype.ext
    · change idealQuotient (gcd _ _) (t.val.1.val*t.val.2.1.val)=t.val.2.1.val
      dsimp only [multiplyTriple]
      rw [he]
      exact mul_left_cancel₀ t.val.1.property.1 (idealQuotient_mul (dvd_mul_right _ _))
    · change idealQuotient (gcd _ _) (t.val.1.val*t.val.2.2.val)=t.val.2.2.val
      dsimp only [multiplyTriple]
      rw [he]
      exact mul_left_cancel₀ t.val.1.property.1 (idealQuotient_mul (dvd_mul_right _ _))

def gcdPairEquiv : (SupportedIdeal×SupportedIdeal)≃CoprimeTriple where
  toFun := gcdTriple
  invFun := multiplyTriple
  left_inv := multiply_gcdTriple
  right_inv := gcdTriple_multiply

lemma gcdPair_tsum (f : SupportedIdeal×SupportedIdeal→ℂ) :
    (∑'p,f p)=∑'t : CoprimeTriple,f (multiplyTriple t) := by
  exact (gcdPairEquiv.symm.tsum_eq f).symm

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1482

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramFrequency
Source SHA256: 7380b7aebc0a7f87f659c5fba68576ce595f1a87b08343fb8d94d008e79825bb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1483


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

lemma actual_common_frequency_zero (C n₁ n₂ j : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (hj : ¬C∣j) :
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j=0 := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero C hC) (supported_element_ne_zero n₁ h₁))
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero C hC) (supported_element_ne_zero n₂ h₂))
  let : Fintype (O⧸Ideal.span {C*n₁}) := Fintype.ofFinite _
  let : Fintype (O⧸Ideal.span {C*n₂}) := Fintype.ofFinite _
  exact fullModulusCorrelation_eq_zero_of_common_not_dvd _ _ C j _ _
    (dvd_mul_right _ _) (dvd_mul_right _ _) hj

lemma tsum_element_divisible (C : O) (hC : C≠0) (f : O→ℂ) :
    (∑'j : O,if C∣j then f j else 0)=∑'k : O,f (C*k) := by
  have hinj : Function.Injective (fun k : O=>C*k) := fun _ _ h=>mul_left_cancel₀ hC h
  have hs : Function.support (fun j : O=>if C∣j then f j else 0)⊆Set.range (fun k : O=>C*k) := by
    intro j hj
    have hd : C∣j := by by_contra h;simp [h] at hj
    obtain ⟨k,rfl⟩ := hd
    exact ⟨k,rfl⟩
  have ht := hinj.tsum_eq hs
  calc
    _ = ∑'k : O,if C∣C*k then f (C*k) else 0 := ht.symm
    _ = _ := by simp only [dvd_mul_right,ite_true]

theorem actual_common_frequency_tsum (C n₁ n₂ : O)
    (hC : Supported (Ideal.span {C})) (h₁ : Supported (Ideal.span {n₁}))
    (h₂ : Supported (Ideal.span {n₂})) (W : O→ℂ) :
    (∑'j : O,actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j*W j)=
      ∑'k : O,actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
        (supported_mul_elements C n₂ hC h₂) (C*k)*W (C*k) := by
  rw [←tsum_element_divisible C (supported_element_ne_zero C hC) (fun j=>
    actualCorrelation (C*n₁) (C*n₂) (supported_mul_elements C n₁ hC h₁)
      (supported_mul_elements C n₂ hC h₂) j*W j)]
  apply tsum_congr
  intro j
  by_cases hj : C∣j
  · rw [ite_eq_left hj]
  · rw [ite_eq_right hj,actual_common_frequency_zero C n₁ n₂ j hC h₁ h₂ hj,zero_mul]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1483

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramIdealDilation
Source SHA256: bafa64cc4010869a50b843696ef9cf457602e3e791172166b520f998cd1faa5f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1484


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev DivisibleSupported (D : SupportedIdeal) := {I : SupportedIdeal // D.val∣I.val}

def supportedIdealProduct (D J : SupportedIdeal) : SupportedIdeal :=
  ⟨D.val*J.val,(supported_mul_iff _ _).mpr ⟨D.property,J.property⟩⟩

def supportedDilationEquiv (D : SupportedIdeal) : SupportedIdeal≃DivisibleSupported D where
  toFun J := ⟨supportedIdealProduct D J,dvd_mul_right _ _⟩
  invFun I := ⟨idealQuotient D.val I.val.val,gram_supported_quotient I.val.val D.val I.val.property I.property⟩
  left_inv J := by
    apply Subtype.ext
    exact mul_left_cancel₀ D.property.1 (idealQuotient_mul (dvd_mul_right D.val J.val))
  right_inv I := by
    apply Subtype.ext
    apply Subtype.ext
    exact idealQuotient_mul I.property

lemma supported_dilation_generator (D J : SupportedIdeal) :
    primaryGenerator (supportedIdealProduct D J).val=primaryGenerator D.val*primaryGenerator J.val :=
  primaryGenerator_mul _ _

lemma supported_dilation_norm (D J : SupportedIdeal) :
    Ideal.absNorm (supportedIdealProduct D J).val=Ideal.absNorm D.val*Ideal.absNorm J.val :=
  map_mul Ideal.absNorm _ _

theorem supported_divisor_tsum (D : SupportedIdeal) (f : SupportedIdeal→ℂ) :
    (∑'I : SupportedIdeal,if D.val∣I.val then f I else 0)=
      ∑'J : SupportedIdeal,f (supportedIdealProduct D J) := by
  change (∑'I : SupportedIdeal,({I : SupportedIdeal | D.val∣I.val}.indicator f) I)=_
  rw [←tsum_subtype (s:={I : SupportedIdeal | D.val∣I.val}) (f:=f)]
  exact (supportedDilationEquiv D).tsum_eq (fun I : DivisibleSupported D=>f I.val) |>.symm

theorem supported_divisor_pair_tsum (D : SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      if D.val∣I.val ∧ D.val∣J.val then f I J else 0)=
      ∑'I : SupportedIdeal,∑'J : SupportedIdeal,
        f (supportedIdealProduct D I) (supportedIdealProduct D J) := by
  have hinner (I : SupportedIdeal) : (∑'J : SupportedIdeal,if D.val∣I.val ∧ D.val∣J.val then f I J else 0)=
      if D.val∣I.val then ∑'J : SupportedIdeal,f I (supportedIdealProduct D J) else 0 := by
    by_cases hI : D.val∣I.val
    · simp only [hI,true_and,ite_true]
      exact supported_divisor_tsum D (f I)
    · simp [hI]
  simp_rw [hinner]
  exact supported_divisor_tsum D (fun I=>∑'J : SupportedIdeal,f I (supportedIdealProduct D J))

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1484

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramJointMean
Source SHA256: 8383d3b5cc28ef2f1788428257a3e11ef79326506126a40d2b176cc0056f9eaf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1485



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCorrelation
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

def jointRemainder (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J : Id) (n₁ n₂ : O) : ℂ :=
  jointFixed S hS σ C u a b r hr n₁ n₂*
    (idealRowHom n₁ J*star (idealRowHom n₂ (Ideal.span {r})))*globalExtension P hg c n₁ n₂ k

theorem jointExtension_local_factor (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J p : Id) [p.IsMaximal] (hgp : goodLambda∉p) (e : ℕ) (he : e≠0)
    (hfactor : Ideal.span {r}=J*p^e) (n₁ n₂ : O) :
    jointExtension S hS σ C k u a b r hr P hg c n₁ n₂=
      (actualSextic p hgp^e) (Ideal.Quotient.mk p n₁)*
        jointRemainder S hS σ C k u a b r hr P hg c J n₁ n₂ := by
  have hf : idealRowHom n₁ (Ideal.span {r})=
      idealRowHom n₁ J*(actualSextic p hgp^e) (Ideal.Quotient.mk p n₁) := by
    rw [hfactor,map_mul,map_pow,idealRowHom_prime n₁ p hgp,MulChar.pow_apply' _ he]
  rw [jointExtension,hf,jointRemainder]
  ring

lemma jointRemainder_periodic_first (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J : Id) (n m y : O) (h : n-m∈jointFixedModulus S hS*(∏i,P i)*J) :
    jointRemainder S hS σ C k u a b r hr P hg c J n y=
      jointRemainder S hS σ C k u a b r hr P hg c J m y := by
  have hf := jointFixed_periodic S hS σ C u a b r hr n y m y
    (Ideal.mul_le_left (Ideal.mul_le_left h)) (by simp)
  have hm := idealRowHom_congr_mod J n m (Ideal.mul_le_right h)
  have hg' := globalExtension_periodic P hg c n y m y k k
    (Ideal.mul_le_right (Ideal.mul_le_left h)) (by simp) (by simp)
  simp only [jointRemainder,hf,hm,hg']

theorem jointExtension_mean_zero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (J p : Id) [p.IsMaximal] (hgp : goodLambda∉p) (hchar : ringChar (O⧸p)≠2)
    (e : ℕ) (he : ¬6∣e) (hfactor : Ideal.span {r}=J*p^e)
    (hcop : IsCoprime (jointFixedModulus S hS*(∏i,P i)*J) (p^e))
    [Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J)] [Fintype (O⧸p^e)]
    [Fintype (O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e)] (d : O) :
    (∑x : O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e,
      ∑y : O⧸(jointFixedModulus S hS*(∏i,P i)*J)*p^e,
        jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out))=0 := by
  have he0 : e≠0 := by intro h;exact he (h ▸ dvd_zero 6)
  have he1 : 1≤e := Nat.one_le_iff_ne_zero.mpr he0
  simp_rw [jointExtension_local_factor S hS σ C k u a b r hr P hg c J p hgp e he0 hfactor]
  apply joint_mean_of_local_factor _ p hgp hchar e e he1 he hcop
    (fun x y=>jointRemainder S hS σ C k u a b r hr P hg c J (d*x) (d*y)) _ d
  intro x z y hxz
  apply jointRemainder_periodic_first
  rw [←mul_sub]
  exact (jointFixedModulus S hS*(∏i,P i)*J).mul_mem_left d hxz

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1485

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramJointPeriod
Source SHA256: 63c39693202d61945ffd6cd35dd5d4b3f0b50e8d3cb577b6d85ce788ad0c0853
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1486


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

lemma common_radical_norm_le (C : O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (∏i,P i)≤Ideal.absNorm (Ideal.span {C}) := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hC)))
  apply map_dvd Ideal.absNorm
  rw [he]
  exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))

lemma jointPeriod_norm_bound (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hk : k=u.val*λ₀^a*(2:O)^b*r) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) :
    Ideal.absNorm (jointPeriod S hS P r)≤
      Ideal.absNorm (jointFixedModulus S hS)*Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) := by
  rw [jointPeriod,map_mul,map_mul]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (common_radical_norm_le C hC P c hc he))
    (numerator_good_norm_le u a b r k hk hk0)

lemma jointPeriod_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (C : O) (hC : C≠0) (P : ι→Id) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (he : Ideal.span {C}=∏i,P i^c i) (r : O) (hr : r≠0) :
    jointPeriod S hS P r≠0 := by
  have hp : ∏i,P i≠(0:Id) := by
    intro hz
    have hd : (∏i,P i)∣Ideal.span {C} := by
      rw [he]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _=>dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp (hc i)))
    rw [hz,zero_dvd_iff] at hd
    exact hC (Ideal.span_singleton_eq_bot.mp hd)
  exact mul_ne_zero (mul_ne_zero (jointFixedModulus_nonzero S hS) hp)
    (Ideal.span_singleton_eq_bot.not.mpr hr)

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1486

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramMobiusPool
Source SHA256: 1e150d0e8e9ebb098b2a15c962b51d58b415aad1528504d7d0dc70311541585e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1487



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentMobiusRegroup
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma divisorPool_supported (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    Supported D := by
  obtain ⟨J,hJ,hd⟩ := Finset.mem_biUnion.mp hD
  exact gram_supported_divisor J.val D J.property ((mem_idealDivisors J.property.1).mp hd)

def poolDivisor (G : Finset SupportedIdeal) (D : Id) : SupportedIdeal :=
  if hD : D∈divisorPool G Subtype.val then ⟨D,divisorPool_supported G D hD⟩
  else ⟨1,by
    constructor
    · exact one_ne_zero
    · intro P hP
      change P∈normalizedFactors (1:Id) at hP
      rw [normalizedFactors_one] at hP
      simp at hP⟩

lemma poolDivisor_val (G : Finset SupportedIdeal) (D : Id) (hD : D∈divisorPool G Subtype.val) :
    (poolDivisor G D).val=D := by simp [poolDivisor,hD]

lemma finite_pair_eq_tsum (F G : Finset SupportedIdeal) (f : SupportedIdeal→SupportedIdeal→ℂ)
    (hf : ∀I J,I∉F ∨ J∉G→f I J=0) :
    (∑I∈F,∑J∈G,f I J)=∑'I : SupportedIdeal,∑'J : SupportedIdeal,f I J := by
  have hinner (I : SupportedIdeal) : (∑J∈G,f I J)=∑'J : SupportedIdeal,f I J :=
    (tsum_eq_sum (fun J hJ=>hf I J (Or.inr hJ))).symm
  simp_rw [hinner]
  symm
  apply tsum_eq_sum
  intro I hI
  simp only [hf I _ (Or.inl hI),tsum_zero]

theorem finite_pair_mobius_dilation (F G : Finset SupportedIdeal)
    (f : SupportedIdeal→SupportedIdeal→ℂ) (hf : ∀I J,I∉F ∨ J∉G→f I J=0) :
    (∑I∈F,∑J∈G,if IsCoprime I.val J.val then f I J else 0)=
      ∑D∈divisorPool G Subtype.val,(moebius D:ℂ)*
        ∑'I : SupportedIdeal,∑'J : SupportedIdeal,
          f (supportedIdealProduct (poolDivisor G D) I) (supportedIdealProduct (poolDivisor G D) J) := by
  rw [finite_pair_mobius F G Subtype.val Subtype.val (fun J _=>J.property.1) f]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hd := poolDivisor_val G D hD
  rw [finite_pair_eq_tsum F G (fun I J=>if D∣I.val ∧ D∣J.val then f I J else 0) (by
    intro I J h
    simp only [hf I J h,ite_self])]
  convert supported_divisor_pair_tsum (poolDivisor G D) f using 1
  rw [hd]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1487

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramPrimeSeparation
Source SHA256: 0b38dcd1c598364aae728a9ab21234b58603537637db351a07a75460151da233
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1488


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma maximal_coprime_of_not_dvd (p J : Id) [p.IsMaximal] (h : ¬p∣J) : IsCoprime J p := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra htop
  have he : p=J⊔p := Ideal.IsMaximal.eq_of_le inferInstance htop le_sup_right
  apply h
  apply Ideal.dvd_iff_le.mpr
  rw [he]
  exact le_sup_left

theorem exists_prime_separation (I p : Id) (hI : I≠0) [p.IsMaximal] (hp0 : p≠0) :
    ∃J : Id,I=J*p^((normalizedFactors I).count p) ∧ IsCoprime J p ∧ J≠0 := by
  have hp : Prime p := Ideal.prime_of_isPrime hp0 inferInstance
  obtain ⟨J,hJ,hnd⟩ := (FiniteMultiplicity.of_prime_left hp hI).exists_eq_pow_mul_and_not_dvd
  have he : multiplicity p I=(normalizedFactors I).count p := by
    simpa only [normalize_eq] using multiplicity_eq_count_normalizedFactors hp.irreducible hI
  refine ⟨J,?_,maximal_coprime_of_not_dvd p J hnd,?_⟩
  · rw [←he,mul_comm]
    exact hJ
  · intro hz
    rw [hz,mul_zero] at hJ
    exact hI hJ

theorem exists_nonexceptional_separation (L R I p : Id) (hI : I≠0)
    [p.IsMaximal] (hp0 : p≠0) (hL : ¬p∣L) (hR : ¬p∣R) :
    ∃J : Id,I=J*p^((normalizedFactors I).count p) ∧
      IsCoprime (L*R*J) (p^((normalizedFactors I).count p)) ∧ J≠0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_prime_separation I p hI hp0
  exact ⟨J,hJ,((maximal_coprime_of_not_dvd p L hL).mul_left
    (maximal_coprime_of_not_dvd p R hR)).mul_left hcop |>.pow_right,hJ0⟩

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1488

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramResidue
Source SHA256: 6e343efbdc68ed9d8472273b5549a67a39f2f36036a90541cfb720687ff264c9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1489


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]

theorem exists_nonexceptional_residue (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing)
    (C k : O) (hC : C≠0) (hk0 : k≠0) (u : Oˣ) (a b : ℕ) (r : O)
    (hr : Supported (Ideal.span {r})) (hk : k=u.val*goodLambda^a*(2:O)^b*r)
    (P : ι→Id) [∀i,(P i).IsMaximal] (hg : ∀i,goodLambda∉P i) (c : ι→ℕ)
    (hc : ∀i,1≤c i) (hfac : Ideal.span {C}=∏i,P i^c i)
    (p : Id) [p.IsMaximal] (hp0 : p≠0) (hgp : goodLambda∉p)
    (hchar : ringChar (O⧸p)≠2) (hfixed : ¬p∣jointFixedModulus S hS) (hcommon : ¬p∣∏i,P i)
    (he : ¬6∣(normalizedFactors (Ideal.span {r})).count p) :
    ∃(M : Id)(hM : M≠0),
      Ideal.absNorm M≤Ideal.absNorm (jointFixedModulus S hS)*
        Ideal.absNorm (Ideal.span {C})*Ideal.absNorm (Ideal.span {k}) ∧
      letI : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient hM
      letI : Fintype (O⧸M):=Fintype.ofFinite _
      ∀d : O,∃A : (O⧸M)→(O⧸M)→ℂ,
        (∀n₁ n₂,A (Ideal.Quotient.mk M n₁) (Ideal.Quotient.mk M n₂)=
          jointExtension S hS σ C k u a b r hr P hg c (d*n₁) (d*n₂)) ∧
        (∀x y,‖A x y‖≤Ideal.absNorm (Ideal.span {C})) ∧
        (∑x,∑y,A x y)=0 := by
  obtain ⟨J,hJ,hcop,hJ0⟩ := exists_nonexceptional_separation (jointFixedModulus S hS)
    (∏i,P i) (Ideal.span {r}) p hr.1 hp0 hfixed hcommon
  let e := (normalizedFactors (Ideal.span {r})).count p
  let M : Id := (jointFixedModulus S hS*(∏i,P i)*J)*p^e
  have hMperiod : M=jointPeriod S hS P r := by
    rw [jointPeriod,hJ]
    dsimp [M,e]
    ring
  have hM0 : M≠0 := hMperiod ▸ jointPeriod_nonzero S hS C hC P c hc hfac r
    (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr)
  refine ⟨M,hM0,?_,?_⟩
  · rw [hMperiod]
    exact jointPeriod_norm_bound S hS C k hC hk0 u a b r hk P c hc hfac
  · let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM0
    let : Fintype (O⧸M) := Fintype.ofFinite _
    let : Finite (O⧸jointFixedModulus S hS*(∏i,P i)*J) :=
      Ring.HasFiniteQuotients.finiteQuotient (left_ne_zero_of_mul hM0)
    let : Fintype (O⧸jointFixedModulus S hS*(∏i,P i)*J) := Fintype.ofFinite _
    let : Finite (O⧸p^e) := Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ hp0)
    let : Fintype (O⧸p^e) := Fintype.ofFinite _
    intro d
    let A : (O⧸M)→(O⧸M)→ℂ := fun x y=>
      jointExtension S hS σ C k u a b r hr P hg c (d*x.out) (d*y.out)
    refine ⟨A,?_,?_,?_⟩
    · intro n₁ n₂
      apply jointExtension_dilation_periodic
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₁))
      · rw [←hMperiod]
        exact Ideal.Quotient.eq.mp (Ideal.Quotient.mk_out (Ideal.Quotient.mk M n₂))
    · intro x y
      rw [hfac]
      exact jointExtension_norm S hS σ C k u a b r hr P hg c hc _ _
    · exact jointExtension_mean_zero S hS σ C k u a b r hr P hg c J p hgp hchar e he hJ hcop d

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1489

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramNonexceptionalBlock
Source SHA256: b0613a810151f4ce3362430bd59879cf9cd631643a252542476fec8679de7966
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1490



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open ConcretePrimeRowBridge UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "Joint" => ProbeGramPeriodicPoisson.Joint

theorem literal_nonexceptional_block (A : ℕ) (hA : 2<A) (a₀ b₀ : ℝ)
    (ha₀ : 0<a₀) (hab : a₀<b₀) :
    ∃H : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀{ι : Type*}[Fintype ι],∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C k : O)(_hC : C≠0)(_hk0 : k≠0)(u : Oˣ)(a b : ℕ)(r : O)
      (hr : Supported (Ideal.span {r})),k=u.val*goodLambda^a*(2:O)^b*r→
      ∀(P : ι→Id)[_hmax : ∀i,(P i).IsMaximal](hg : ∀i,goodLambda∉P i)(c : ι→ℕ),
      (∀i,1≤c i)→Ideal.span {C}=∏i,P i^c i→
      ∀(p : Id)[_hpmax : p.IsMaximal],p≠0→∀_hgp : goodLambda∉p,
      ringChar (O⧸p)≠2→(¬p∣jointFixedModulus S hS)→(¬p∣∏i,P i)→
      (¬6∣(normalizedFactors (Ideal.span {k})).count p)→
      ∀(W : SchwartzMap Joint ℂ),ProbeGramAnnularLattice.AnnularSupport a₀ b₀ W→
      ∀(d : O)(N : ℝ),0<N→
      Summable (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
      ‖∑'m : O×O,jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)‖≤
        K*ProbeGramLatticeDecay.sourceControl H W*(Ideal.absNorm (Ideal.span {C}):ℝ)*N^2*
          min 1 (((Ideal.absNorm (jointFixedModulus S hS):ℝ)*Ideal.absNorm (Ideal.span {C})*
            Ideal.absNorm (Ideal.span {k})/N)^A) := by
  obtain ⟨H,K,hK,hengine⟩ := ProbeGramPeriodicPoisson.ideal_annular_periodic_bound A hA a₀ b₀ ha₀ hab
  refine ⟨H,K,hK,?_⟩
  intro ι inst S hS σ C k hC hk0 u a b r hr hk P hmax hg c hc hfac p hpmax hp0 hgp hchar hfixed hcommon he W hW d N hN
  have hcount : (normalizedFactors (Ideal.span {k})).count p=
      (normalizedFactors (Ideal.span {r})).count p := by
    rw [hk]
    exact good_factor_count p hgp hchar u a b r hr
  have heR : ¬6∣(normalizedFactors (Ideal.span {r})).count p := hcount ▸ he
  obtain ⟨M,hM,hMN,hres⟩ := exists_nonexceptional_residue S hS σ C k hC hk0 u a b r hr hk
    P hg c hc hfac p hp0 hgp hchar hfixed hcommon heR
  let : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype (O⧸M) := Fintype.ofFinite _
  obtain ⟨f,hf,hfn,hfm⟩ := hres d
  have hmean : (∑'v : (O⧸M)×(O⧸M),f v.1 v.2)=0 := by
    rw [tsum_fintype,Fintype.sum_prod_type]
    exact hfm
  have hh := hengine W hW M hM (fun v=>f v.1 v.2) (Ideal.absNorm (Ideal.span {C}))
    (Nat.cast_nonneg _) (fun v=>hfn v.1 v.2) hmean N hN
  have hfun : (fun m : O×O=>f (ProbeGramPeriodicPoisson.idealQuotientPair M m).1
      (ProbeGramPeriodicPoisson.idealQuotientPair M m).2*W (ProbeGramLatticeDecay.physicalPoint N m))=
      (fun m : O×O=>jointExtension S hS σ C k u a b r hr P hg c (d*m.1) (d*m.2)*
        W (ProbeGramLatticeDecay.physicalPoint N m)) := by
    funext m
    rw [ProbeGramPeriodicPoisson.idealQuotientPair,hf]
  rw [hfun] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by unfold ProbeGramLatticeDecay.sourceControl;positivity)
  apply min_le_min_left
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ hN.le
  exact_mod_cast hMN

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1490

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGramHeight
Source SHA256: f308c1b0dccb35bda9354305aaf32901d739f93a0eca25b919a1d754f4c95f53
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1491


namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap Topology
open Filter Set CompletedHeight FourierBridge
namespace SevenEighths.ProbePhysical

def lowGramBaseWindow (W : ℝ→ℂ) (r : ℝ) : ℂ := W r/(r:ℂ)

lemma lowGramBaseWindow_support (W : ℝ→ℂ) :
    Function.support (lowGramBaseWindow W)⊆Function.support W := by
  intro r hr hz
  exact hr (by simp [lowGramBaseWindow,hz])

lemma lowGramBaseWindow_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (lowGramBaseWindow W) := by
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r=0
  · subst r
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ=>(0:ℂ)) 0).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds ha] with x hx
    have hz : W x=0 := by
      by_contra h
      exact (not_le.mpr hx) (hs h).1
    simp [lowGramBaseWindow,hz]
  · unfold lowGramBaseWindow
    simp only [div_eq_mul_inv]
    exact hW.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.fun_inv (Complex.ofReal_ne_zero.mpr hr))

lemma lowGramProfile_twist (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (v r : ℝ) :
    lowGramProfile W v r=normTwistedSource (lowGramBaseWindow W) (v/(2*Real.pi)) r := by
  by_cases hz : W r=0
  · simp [lowGramProfile,normTwistedSource,lowGramBaseWindow,hz]
  have hr : 0<r := ha.trans_le (hs hz).1
  have hrc : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hp : (r:ℂ)^((v:ℂ)*Complex.I)=logPhase (v/(2*Real.pi)) (Real.log r) := by
    rw [Complex.cpow_def_of_ne_zero hrc,←Complex.ofReal_log hr.le]
    unfold logPhase
    congr 1
    push_cast
    field_simp
  rw [lowGramProfile,Complex.cpow_add _ _ hrc,Complex.cpow_neg_one,hp]
  unfold normTwistedSource lowGramBaseWindow
  ring

def lowGramSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (v : ℝ) : SchwartzMap ℝ ℂ :=
  uniformTwistedSchwartz (lowGramBaseWindow W) a b ha
    ((lowGramBaseWindow_support W).trans hs) (lowGramBaseWindow_smooth W a b ha hs hW) (v/(2*Real.pi))

lemma lowGramSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (v r : ℝ) :
    lowGramSchwartz W a b ha hs hW v r=lowGramProfile W v r := by
  rw [lowGramSchwartz,uniformTwistedSchwartz_apply,lowGramProfile_twist W a b ha hs]

theorem lowGramProfile_uniform_degree (a b : ℝ) (ha : 0<a) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∀W : ℝ→ℂ,∀hs : Function.support W⊆Set.Icc a b,∀hW : ContDiff ℝ ∞ W,
      ∃C : ℝ,0<C ∧ ∀v : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (lowGramSchwartz W a b ha hs hW v)≤C*(1+‖v‖)^n := by
  obtain ⟨n,hn⟩ := normTwistedSource_uniform_degree a b ha S
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn (lowGramBaseWindow W) ((lowGramBaseWindow_support W).trans hs)
    (lowGramBaseWindow_smooth W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro v
  apply (hb (v/(2*Real.pi))).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply pow_le_pow_left₀ (by positivity)
  gcongr
  simp only [norm_div,Real.norm_eq_abs,abs_of_pos (show (0:ℝ)<2*Real.pi by positivity)]
  exact div_le_self (norm_nonneg v) (by linarith [Real.pi_gt_three])

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1491

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramShell
Source SHA256: 86c9d12bd6e9bc48949cf0745dcd36334a0f760ab7dfa83d5b3d07f57d3bd1c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1492



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical EisensteinSchwartzPoisson

def shellProfile (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ) : ℂ :=
  lowGramProfile W v x*star (lowGramProfile W v y)*paperRadialFourier U (T/(x*y))

lemma shellProfile_zero_left (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hx : W x=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hx]

lemma shellProfile_zero_right (W : ℝ→ℂ) (v : ℝ) (U : SchwartzMap ℝ ℂ) (T x y : ℝ)
    (hy : W y=0) : shellProfile W v U T x y=0 := by
  simp [shellProfile,lowGramProfile,hy]

theorem shellProfile_weighted_bound (a b B : ℝ) (ha : 0<a) (hB : 0≤B) (A : ℕ) :
    ∃s : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
      ∀(W : ℝ→ℂ),(Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤B)→
      ∀(U : SchwartzMap ℝ ℂ)(v T x y : ℝ),0≤T→
        (1+T)^A*‖shellProfile W v U T x y‖≤
          C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U := by
  obtain ⟨s,C,hC,hpaper⟩ := paperRadialFourier_euler_source_weighted_bound A 0
  refine ⟨s,(1+B/a)^2*(1+b^2)^A*C,by positivity,?_⟩
  intro W hs hW U v T x y hT
  by_cases hx : W x=0
  · rw [shellProfile_zero_left _ _ _ _ _ _ hx,norm_zero,mul_zero]
    positivity
  by_cases hy : W y=0
  · rw [shellProfile_zero_right _ _ _ _ _ _ hy,norm_zero,mul_zero]
    positivity
  have hxa := (hs hx).1
  have hya := (hs hy).1
  have hxb := (hs hx).2
  have hyb := (hs hy).2
  have hx0 := ha.trans_le hxa
  have hy0 := ha.trans_le hya
  have hxy : 0<x*y := mul_pos hx0 hy0
  have hxyb : x*y≤b^2 := by nlinarith [mul_le_mul hxb hyb hy0.le (hx0.le.trans hxb)]
  have ht : 0≤T/(x*y) := div_nonneg hT hxy.le
  have hp := hpaper U 0 (by omega) (T/(x*y)) ht
  simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hp
  have hscale : 1+T≤(1+b^2)*(1+T/(x*y)) := by
    have he : T=(x*y)*(T/(x*y)) := by field_simp
    have hbound := mul_le_mul_of_nonneg_right hxyb ht
    rw [←he] at hbound
    nlinarith [sq_nonneg b]
  have hp' : (1+T)^A*‖paperRadialFourier U (T/(x*y))‖≤
      (1+b^2)^A*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) := by
    calc
      _ ≤ ((1+b^2)*(1+T/(x*y)))^A*‖paperRadialFourier U (T/(x*y))‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hscale _) (norm_nonneg _)
      _ = (1+b^2)^A*((1+T/(x*y))^A*‖paperRadialFourier U (T/(x*y))‖) := by rw [mul_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have hwx : ‖lowGramProfile W v x‖≤1+B/a := by
    rw [lowGramProfile_norm W v x hx0]
    exact (div_le_div₀ hB (hW x) ha hxa).trans (by linarith)
  have hwy : ‖lowGramProfile W v y‖≤1+B/a := by
    rw [lowGramProfile_norm W v y hy0]
    exact (div_le_div₀ hB (hW y) ha hya).trans (by linarith)
  rw [shellProfile,norm_mul,norm_mul,norm_star]
  calc
    _ = (‖lowGramProfile W v x‖*‖lowGramProfile W v y‖)*
        ((1+T)^A*‖paperRadialFourier U (T/(x*y))‖) := by ring
    _ ≤ (1+B/a)^2*((1+b^2)^A*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      apply mul_le_mul _ hp' (by positivity) (by positivity)
      nlinarith [mul_le_mul hwx hwy (norm_nonneg _) (by positivity : 0≤1+B/a)]
    _ = _ := by ring

end SevenEighths.ProbeGramCommon
