    · exact (polynomial_nonzero_support χ W X sigma t b hX hs hn).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hX.le)
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 b) hX.le
  refine ⟨Real.logb_nonneg hZ (le_max_left _ _),?_⟩
  have hh:=Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 X)) hclip
  rw [Real.logb_mul hB.ne' hX.ne'] at hh
  linarith

lemma deleted_same_product (X₁ X₂ Y₁ Y₂ T d₁ d₂ : ℝ)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/d₁)*(X₂/d₂)=T/(d₁*d₂) ∧
      (Y₁/d₁)*(Y₂/d₂)=T/(d₁*d₂) := by
  constructor <;> rw [div_mul_div_comm]
  · rw [hX]
  · rw [hY]

theorem actual_deleted_capacity {α : Type*} [DecidableEq α]
    (F J : Finset α) (hJ : J⊆F) (P : α→ℝ) (hP : ∀i∈F,1≤P i)
    (χ : Character) (W₁ W₂ : ℝ→ℂ) (Z X₁ X₂ t₁ t₂ b₁ b₂ kappa M : ℝ)
    (D₁ D₂ : Ideal O) (hD₁ : D₁≠0) (hD₂ : D₂≠0)
    (hZ : 1<Z) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hk : 0≤kappa)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hn : polynomial χ false W₁ (X₁/(D₁.absNorm:ℝ)) 0 t₁ *
      polynomial χ false W₂ (X₂/(D₂.absNorm:ℝ)) 0 t₂≠0)
    (hcap : Real.logb Z (X₁*X₂)+6*kappa*(∑i∈F,Real.logb Z (P i))≤M) :
    let n₁:=Real.logb Z (max 1 (X₁/(D₁.absNorm:ℝ)))
    let n₂:=Real.logb Z (max 1 (X₂/(D₂.absNorm:ℝ)))
    0≤n₁ ∧ 0≤n₂ ∧ n₁+n₂+6*kappa*(∑i∈J,Real.logb Z (P i))≤
      M+Real.logb Z (max 1 b₁*max 1 b₂) := by
  have hd₁ : 1≤(D₁.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD₁)
  have hd₂ : 1≤(D₂.absNorm:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD₂)
  have hd₁p : 0<(D₁.absNorm:ℝ):=zero_lt_one.trans_le hd₁
  have hd₂p : 0<(D₂.absNorm:ℝ):=zero_lt_one.trans_le hd₂
  have hc₁:=actual_clipped_log χ W₁ Z _ 0 t₁ b₁ hZ (div_pos hX₁ hd₁p) hs₁ (mul_ne_zero_iff.mp hn).1
  have hc₂:=actual_clipped_log χ W₂ Z _ 0 t₂ b₂ hZ (div_pos hX₂ hd₂p) hs₂ (mul_ne_zero_iff.mp hn).2
  have hslots : (∑i∈J,Real.logb Z (P i))≤∑i∈F,Real.logb Z (P i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hJ (fun i hi _=>Real.logb_nonneg hZ (hP i hi))
  have hslots' := mul_le_mul_of_nonneg_left hslots (by positivity : 0≤6*kappa)
  have hlog₁:=Real.logb_nonneg hZ hd₁
  have hlog₂:=Real.logb_nonneg hZ hd₂
  rw [Real.logb_div hX₁.ne' hd₁p.ne'] at hc₁
  rw [Real.logb_div hX₂.ne' hd₂p.ne'] at hc₂
  rw [Real.logb_mul hX₁.ne' hX₂.ne'] at hcap
  have hb₁ : 0<max 1 b₁:=zero_lt_one.trans_le (le_max_left _ _)
  have hb₂ : 0<max 1 b₂:=zero_lt_one.trans_le (le_max_left _ _)
  dsimp only
  refine ⟨hc₁.1,hc₂.1,?_⟩
  rw [Real.logb_mul hb₁.ne' hb₂.ne']
  linarith [hc₁.2,hc₂.2]

lemma eventually_fixed_clipping_cost (b₁ b₂ delta : ℝ) (hdelta : 0<delta) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ Real.logb Z (max 1 b₁*max 1 b₂)≤delta := by
  have hc:=(tendsto_rpow_atTop hdelta).eventually (eventually_ge_atTop (max 1 b₁*max 1 b₂))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc] with Z hZ hC
  refine ⟨hZ,?_⟩
  exact (Real.logb_le_iff_le_rpow hZ (mul_pos
    (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _)))).mpr hC
end SevenEighths.CenteredMomentCommonMaskChildCapacity

end

end OAI
end OAIOriginalModule1998

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectionNegligible
Source SHA256: 7081015bb3bc5d7ef84192cf1ba0753d5b12ab96db544376bad6dbef28891d2c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1999


namespace OAI

noncomputable section
open scoped ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily EisensteinSchwartzPoisson

lemma normalized_power_eq (Y : ℝ) (hY : 0<Y) (B : ℕ) :
    Y^B/Real.sqrt Y=Y^((B:ℝ)-1/2) := by
  rw [Real.rpow_sub hY,Real.rpow_natCast,Real.sqrt_eq_rpow]

theorem actual_reflected_small_negligible (a b xi saving : ℝ) (ha : 0<a) (hxi : 0<xi) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y Z : ℝ),
      1≤Z → 0<Y → Y≤Z^(-xi) →
      ‖HeckeDyadic.polynomial η false
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) Y 0 0‖≤
        C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨B,hB⟩ := exists_nat_gt (max (2:ℝ) (saving/xi+1/2))
  have hB2 : 2≤B := by exact_mod_cast (le_of_lt ((le_max_left _ _).trans_lt hB))
  have hBp : 0≤(B:ℝ)-1/2 := by have := (le_max_left _ _).trans_lt hB;linarith
  have hsav : saving≤xi*((B:ℝ)-1/2) := by
    have hh := (le_max_right _ _).trans_lt hB
    have hh' : saving/xi≤(B:ℝ)-1/2 := by linarith
    exact (div_le_iff₀ hxi).mp hh' |>.trans_eq (mul_comm _ _)
  obtain ⟨n,hn⟩ := actual_reflected_absolute_bound a b ha B hB2
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hbound⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro η t Y Z hZ hY hYZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  apply (hbound η t Y hY).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [normalized_power_eq Y hY B]
  calc
    _≤(Z^(-xi))^((B:ℝ)-1/2) := Real.rpow_le_rpow hY.le hYZ hBp
    _=Z^((-xi)*((B:ℝ)-1/2)) := (Real.rpow_mul hz.le _ _).symm
    _≤Z^(-saving) := Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem actual_reflected_upper_negligible (a b xi saving L Cscale : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hCscale : 0<Cscale) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y Z : ℝ),
      1≤Z → 0<Y → Y≤Cscale*Z^L →
      ‖HeckeDyadic.polynomial η false
        (fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x) Y 0 0‖≤
        C*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((saving+L*(3/2))/(xi/2))
  have hsav : saving+L*(3/2)≤xi/2*(A:ℝ) := by
    have hh := (div_le_iff₀ (by linarith : 0<xi/2)).mp hA.le
    nlinarith
  obtain ⟨n,hn⟩ := actual_reflected_discarded_bound a b ha A 2 (by omega)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hbound⟩ := hn W hs hW
  refine ⟨C*Cscale^(3/2:ℝ),by positivity,?_⟩
  intro η t Y Z hZ hY hYZ
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hR : 0<Z^(xi/2) := Real.rpow_pos_of_pos hz _
  have hp : Y^2/Real.sqrt Y≤Cscale^(3/2:ℝ)*Z^(L*(3/2)) := by
    rw [normalized_power_eq Y hY 2]
    norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
    calc
      _≤(Cscale*Z^L)^(3/2:ℝ) := Real.rpow_le_rpow hY.le hYZ (by norm_num)
      _=_ := by rw [Real.mul_rpow hCscale.le (by positivity),←Real.rpow_mul hz.le]
  have hd : (Z^(xi/2))^A=Z^((xi/2)*(A:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  calc
    _≤C*(1+‖t‖)^n*(Y^2/Real.sqrt Y)/(Z^(xi/2))^A := hbound η t Y _ hY hR
    _≤C*(1+‖t‖)^n*(Cscale^(3/2:ℝ)*Z^(L*(3/2)))/(Z^(xi/2))^A :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _=(C*Cscale^(3/2:ℝ))*(1+‖t‖)^n*Z^(L*(3/2)-(xi/2)*(A:ℝ)) := by
      rw [hd,Real.rpow_sub hz]
      ring
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end OAIOriginalModule1999

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength
Source SHA256: 0a4d0ca94d0ae90e562034756662ed3af3b4236e2d863a51b8fbdb321018e980
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2000



namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentReflectionRetainedLength
open CenteredMomentComparisonReflection CenteredMomentReflectedTruncation
open CenteredMomentSectorLocalization

lemma retained_scale_lower (R Y : ℝ) (hY : 0<Y) (n : ℤ)
    (hn : n∈retainedAnnuli R Y hY) : 1≤dyadicScale n*Y := by
  obtain ⟨hr,q,hq,hne⟩ := (retainedAnnuli_mem R Y hY n).mp hn
  have hs := (dyadicWeight_support n hne).2.le
  have hh := mul_le_mul_of_nonneg_right (hq.trans hs) hY.le
  simpa only [inv_mul_cancel₀ hY.ne'] using hh

theorem eventually_actual_retained_length (C box xi : ℝ) (hC : 0<C)
    (hbox : 1≤box) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(M a Q R d h : ℝ),
      0<Q → 0<d → Q*R≤C*Z^M → d≤R → 1≤h →
      ∀n : ℤ,∀hY : 0<Q*d/(Z^a*h),
      n∈retainedAnnuli (Z^(xi/4)) (Q*d/(Z^a*h)) hY →
      1≤dyadicScale n*(Q*d/(Z^a*h)) ∧
      0≤Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h)))) ∧
      Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h))))≤M-a+xi := by
  have hc := (tendsto_rpow_atTop (show 0<xi/2 by linarith)).eventually
    (eventually_ge_atTop (box*C))
  have hfour := (tendsto_rpow_atTop (show 0<xi/4 by linarith)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc,hfour] with Z hZ hconst h4
  refine ⟨hZ,?_⟩
  intro M a Q R d h hQ hd hcap hdR hh n hY hn
  have hz : 0<Z := zero_lt_one.trans hZ
  have hs : dyadicScale n≤Z^(xi/2) := by
    calc
      _≤4*Z^(xi/4) := retained_scale_le _ n ((retainedAnnuli_mem _ _ hY n).mp hn).1
      _≤Z^(xi/4)*Z^(xi/4) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _=Z^(xi/2) := by rw [←Real.rpow_add hz];congr 1;ring
  have hlo := retained_scale_lower _ _ hY n hn
  have hraw := reflected_scale_bound Z M a xi C Q R d h (dyadicScale n)
    hZ hC.le hQ.le hd.le (dyadicScale_pos n).le hcap hdR hh hs
  have hb : 1≤box*(dyadicScale n*(Q*d/(Z^a*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤_ :=mul_le_mul hbox hlo zero_le_one (by linarith)
  refine ⟨hlo,Real.logb_nonneg hZ hb,?_⟩
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hb)).mpr
  calc
    _≤box*(C*Z^(M-a+xi/2)) := mul_le_mul_of_nonneg_left hraw (by linarith)
    _=(box*C)*Z^(M-a+xi/2) :=by ring
    _≤Z^(xi/2)*Z^(M-a+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
    _=Z^(M-a+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

lemma one_reflection_total_width (M A z b xi reflected : ℝ)
    (hb : b≤M/4) (hreflection : reflected≤M-(A-z-b)+xi) :
    reflected+b+z≤3*M/2-A+2*z+xi := by linarith

lemma positive_slot_width_drop (M A z xi kappa : ℝ)
    (hM : 0≤M) (hz : 0≤z) (hk : 3/4≤kappa)
    (hA : 5*M/6≤A) (hcap : A+(6*kappa-1)*z≤M) :
    3*M/2-A+2*z+xi≤23*M/30+xi ∧
    3*M/2-A+2*z+xi+(6*kappa-1)*z≤14*M/15+xi := by
  have hkz : 7/2*z≤(6*kappa-1)*z := mul_le_mul_of_nonneg_right (by linarith) hz
  have hsmall : z≤M/21 := by linarith
  constructor <;> nlinarith

end SevenEighths.CenteredMomentReflectionRetainedLength

end

end OAI
end OAIOriginalModule2000

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectionTailMass
Source SHA256: 1a3fedf5e78b254dc4fdf1582f7372efddd7ad9dd9761dd096e6a64620619c33
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2001



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectionTailMass
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma subset_norm_le (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S) :
    (Ideal.absNorm (∏P∈D,P):ℝ)≤(Ideal.absNorm (∏P∈S,P):ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS)))
    (map_dvd Ideal.absNorm (Finset.prod_dvd_prod_of_subset D S (fun P=>P) hD))

lemma restoration_norm_one (S : Finset (Ideal O)) (H : SmoothIdeal S) : 1≤norm H.val := by
  unfold CenteredMomentReflectionDeletion.norm
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr H.val.property))

lemma dual_scale_bounds (S D : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (hD : D⊆S)
    (H : SmoothIdeal S) (Q X U : ℝ) (hQ : 0<Q) (hX : 0<X)
    (hcap : Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤U*X) :
    0<Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val) ∧
    Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)≤U := by
  have hd := subset_product_norm_pos D (fun P hP=>hS P (hD hP))
  have hh := norm_pos H.val
  refine ⟨by positivity,?_⟩
  calc
    _≤Q*(Ideal.absNorm (∏P∈D,P):ℝ)/X :=
      div_le_div_of_nonneg_left (by positivity) hX
        (by nlinarith [restoration_norm_one S H])
    _≤Q*(Ideal.absNorm (∏P∈S,P):ℝ)/X :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (subset_norm_le S D hS hD) hQ.le) hX.le
    _≤U := (div_le_iff₀ hX).mpr hcap

theorem coefficient_column_bound (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
      (η ηi : Character)(f : Finset (Ideal O)→SmoothIdeal S→ℂ)(B : ℝ),0≤B →
      (∀D∈S.powerset,∀H,‖f D H‖≤B) →
      (∀D∈S.powerset,Summable (fun H=>coefficient η ηi S D H*f D H)) ∧
      ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*f D H‖≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*B := by
  obtain ⟨C,hC,hbound⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi f B hB hf
  have hs (D : Finset (Ideal O)) (hD : D∈S.powerset) :
      Summable (fun H : SmoothIdeal S=>‖coefficient η ηi S D H*f D H‖) := by
    apply ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B).of_nonneg_of_le
      (fun _=>norm_nonneg _)
    intro H
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
  refine ⟨fun D hD=>(hs D hD).of_norm,?_⟩
  calc
    _≤∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H*f D H‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun D hD=>norm_tsum_le_tsum_norm (hs D hD)))
    _≤∑D∈S.powerset,(∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)*B := by
      apply Finset.sum_le_sum
      intro D hD
      rw [←tsum_mul_right]
      apply (hs D hD).tsum_le_tsum _
        ((coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD)).mul_right B)
      intro H
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf D hD H) (norm_nonneg _)
    _≤_ := by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (hbound S hS η ηi).2 hB

theorem actual_deleted_discarded_negligible (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O))(_hS : ∀P∈S,Prime P)
        (η ηi χ : Character)(t Q X Z : ℝ),1≤Z → 0<Q → 0<X →
        Q*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X →
        let F := fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x
        (∀D∈S.powerset,Summable (fun H : SmoothIdeal S=>coefficient η ηi S D H*
          HeckeDyadic.polynomial χ false F
            (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0)) ∧
        ‖∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient η ηi S D H*
          HeckeDyadic.polynomial χ false F
            (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0‖≤
          C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨n,hn⟩ := actual_reflected_upper_negligible a b xi saving L Cscale ha hxi hscale
  obtain ⟨D,hD,hDb⟩ := coefficient_column_bound ε hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hCb⟩ := hn W hs hW
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro S hS η ηi χ t Q X Z hZ hQ hX hcap
  dsimp only
  have hh := hDb S hS η ηi
    (fun E H=>HeckeDyadic.polynomial χ false
      (fun x=>(CenteredMomentSectorLocalization.discardedWeight (Z^(xi/2)) x:ℂ)*
        paperRadialFourier (CompletedHeight.normTwistedSource W t) x)
      (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm H.val)) 0 0)
    (C*(1+‖t‖)^n*Z^(-saving)) (by positivity) (by
      intro E hE H
      have hy := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) H Q X (Cscale*Z^L) hQ hX hcap
      exact hCb χ t _ Z hZ hy.1 hy.2)
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  ring

end SevenEighths.CenteredMomentReflectionTailMass

end

end OAI
end OAIOriginalModule2001

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectionWeightedEnergy
Source SHA256: 3eb494a30c23a02076acdc038c9b79680fb6e54934d2d3893eeeb2b7ff7eea5c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2002



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionWeightedEnergy
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentReflectedAnnuli
local notation "O" => HeckeFamily.O

abbrev Index (S : Finset (Ideal O)) := (S.powerset × SmoothIdeal S) × ℤ

def baseIndex (S : Finset (Ideal O)) : Index S :=
  ((⟨∅,Finset.mem_powerset.mpr (Finset.empty_subset _)⟩,unitSmooth S),0)

def signedWeight (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ)
    (a : Index S) : ℂ :=
  coefficient η ηi S a.1.1.val a.1.2 * (annularMass B a.2 : ℂ)

lemma signedWeight_norm (η ηi : Character) (S : Finset (Ideal O))
    (B : ℕ) (a : Index S) :
    ‖signedWeight η ηi S B a‖ =
      ‖coefficient η ηi S a.1.1.val a.1.2‖ * annularMass B a.2 := by
  rw [signedWeight,norm_mul,Complex.norm_real,Real.norm_of_nonneg (annularMass_nonneg _ _)]

lemma annularMass_le_two (B : ℕ) (hB : 2≤B) (n : ℤ) :
    annularMass B n ≤ annularMass 2 n := by
  have hp := CenteredMomentSectorLocalization.dyadicScale_pos n
  unfold annularMass
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
    (pow_le_pow_right₀ (by linarith [CenteredMomentSectorLocalization.dyadicScale_pos n]) hB)

lemma coefficient_joint_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    Summable (fun a : S.powerset × SmoothIdeal S =>
      ‖coefficient η ηi S a.1.val a.2‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun D => coefficient_summable_norm η ηi S hS D.val
    (Finset.mem_powerset.mp D.property),(hasSum_fintype _).summable⟩

lemma coefficient_joint_mass (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) :
    (∑' a : S.powerset × SmoothIdeal S,‖coefficient η ηi S a.1.val a.2‖) =
      ∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖ := by
  rw [(coefficient_joint_summable η ηi S hS).tsum_prod,tsum_fintype]
  exact Finset.sum_coe_sort S.powerset (fun D => ∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖)

lemma signedWeight_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) := by
  simp_rw [signedWeight_norm]
  exact (coefficient_joint_summable η ηi S hS).mul_of_nonneg
    (annularMass_summable B hB) (fun _ => norm_nonneg _) (annularMass_nonneg B)

lemma signedWeight_mass (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B) :
    (∑'a : Index S,‖signedWeight η ηi S B a‖) =
      (∑D∈S.powerset,∑'H : SmoothIdeal S,‖coefficient η ηi S D H‖) *
        ∑'n : ℤ,annularMass B n := by
  rw [(signedWeight_summable_norm η ηi S hS B hB).tsum_prod]
  simp_rw [signedWeight_norm,tsum_mul_left]
  rw [tsum_mul_right,coefficient_joint_mass η ηi S hS]

lemma signed_series_reindex (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ)
    (f : Index S→ℂ) (hs : Summable (fun a=>‖signedWeight η ηi S B a*f a‖)) :
    (∑'a : Index S,signedWeight η ηi S B a*f a) =
      ∑D : S.powerset,∑'H : SmoothIdeal S,∑'n : ℤ,
        coefficient η ηi S D.val H*(annularMass B n:ℂ)*f ((D,H),n) := by
  rw [hs.of_norm.tsum_prod,hs.of_norm.prod.tsum_prod,tsum_fintype]
  rfl

lemma signedWeight_base (η ηi : Character) (S : Finset (Ideal O)) (B : ℕ) :
    signedWeight η ηi S B (baseIndex S)=(annularMass B 0:ℂ) := by
  simp only [signedWeight,baseIndex,coefficient_empty_unit,one_mul]

theorem signed_mass_subpower (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : Character)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε*(∑'n : ℤ,annularMass B n) := by
  obtain ⟨C,hC,hb⟩ := reflection_mass_subpower ε hε
  refine ⟨C,hC,?_⟩
  intro S hS η ηi B hB
  refine ⟨signedWeight_summable_norm η ηi S hS B hB,?_⟩
  rw [signedWeight_mass η ηi S hS B hB]
  exact mul_le_mul_of_nonneg_right (hb S hS η ηi).2 (tsum_nonneg (annularMass_nonneg B))

def annularConstant : ℝ := 1 + ∑'n : ℤ,annularMass 2 n

lemma annularConstant_pos : 0<annularConstant := by
  have h : 0≤∑'n : ℤ,annularMass 2 n := tsum_nonneg (annularMass_nonneg 2)
  dsimp [annularConstant]
  linarith

lemma annularMass_total_le (B : ℕ) (hB : 2≤B) :
    (∑'n : ℤ,annularMass B n) ≤ annularConstant := by
  apply ((annularMass_summable B hB).tsum_le_tsum (annularMass_le_two B hB)
    (annularMass_summable 2 le_rfl)).trans
  dsimp [annularConstant]
  linarith

theorem uniform_signed_mass (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)),(∀P∈S,Prime P) →
      ∀(η ηi : Character)(B : ℕ),2≤B →
      Summable (fun a : Index S => ‖signedWeight η ηi S B a‖) ∧
      (∑'a : Index S,‖signedWeight η ηi S B a‖) ≤
        C*(Ideal.absNorm (∏P∈S,P):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := signed_mass_subpower ε hε
  refine ⟨C*annularConstant,mul_pos hC annularConstant_pos,?_⟩
  intro S hS η ηi B hB
  refine ⟨(hb S hS η ηi B hB).1,(hb S hS η ηi B hB).2.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (annularMass_total_le B hB) (by positivity)).trans_eq (by ring)

lemma sum_iSup_le_of_selection {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (g : ∀i,α i→ℝ) (E : ℝ)
    (hselection : ∀a : ∀i,α i,(∑i,g i (a i))≤E) :
    (∑i,⨆a,g i a)≤E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/((Fintype.card ι:ℝ)+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  choose a ha using fun i => exists_lt_of_lt_ciSup
    (show (⨆a,g i a)-δ < (⨆a,g i a) by linarith)
  have hh : (∑i,⨆a,g i a) ≤ ∑i,(g i (a i)+δ) := by
    apply Finset.sum_le_sum
    intro i _
    linarith [ha i]
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
  have he : ((Fintype.card ι:ℝ)+1)*δ=ε := by
    dsimp [δ]
    field_simp
  have hn : (0:ℝ)≤Fintype.card ι := Nat.cast_nonneg _
  have hb := hselection a
  simp only [Finset.card_univ] at hh
  nlinarith

lemma selection_point_bound {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (f : ∀i,α i→ℂ) (E : ℝ)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) (i : ι) (a : α i) :
    ‖f i a‖^2≤E := by
  have hh := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun j=>‖f j (Function.update base i a j)‖^2)
    (fun j _=>sq_nonneg _) (Finset.mem_univ i)
  exact (by simpa using hh : ‖f i a‖^2≤∑j,‖f j (Function.update base i a j)‖^2).trans
    (hselection (Function.update base i a))

theorem weighted_selection_energy {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (w f : ∀i,α i→ℂ) (M E : ℝ) (_hM : 0≤M)
    (hs : ∀i,Summable (fun a=>‖w i a‖))
    (hm : ∀i,(∑'a,‖w i a‖)≤M)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) :
    (∀i,Summable (fun a=>‖w i a*f i a‖)) ∧
      (∑i,‖∑'a,w i a*f i a‖^2)≤M^2*E := by
  let (i : ι) : Nonempty (α i) := ⟨base i⟩
  let v (i : ι) : ℝ := ⨆a,‖f i a‖^2
  have hbd (i : ι) : BddAbove (Set.range (fun a=>‖f i a‖^2)) :=
    ⟨E,by rintro _ ⟨a,rfl⟩;exact selection_point_bound base f E hselection i a⟩
  have hv (i : ι) (a : α i) : ‖f i a‖^2≤v i := le_ciSup (hbd i) a
  have hv0 (i : ι) : 0≤v i := (sq_nonneg _).trans (hv i (base i))
  have hnorm (i : ι) (a : α i) : ‖f i a‖≤Real.sqrt (v i) :=
    (Real.le_sqrt (norm_nonneg _) (hv0 i)).mpr (hv i a)
  have hw (i : ι) : Summable (fun a=>‖w i a*f i a‖) := by
    apply ((hs i).mul_right (Real.sqrt (v i))).of_nonneg_of_le (fun _=>norm_nonneg _)
    intro a
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _)
  have hsum (i : ι) : ‖∑'a,w i a*f i a‖≤M*Real.sqrt (v i) := by
    apply (norm_tsum_le_tsum_norm (hw i)).trans
    apply ((hw i).tsum_le_tsum (fun a=>by
      rw [norm_mul];exact mul_le_mul_of_nonneg_left (hnorm i a) (norm_nonneg _))
      ((hs i).mul_right (Real.sqrt (v i)))).trans
    rw [tsum_mul_right]
    exact mul_le_mul_of_nonneg_right (hm i) (Real.sqrt_nonneg _)
  refine ⟨hw,?_⟩
  calc
    (∑i,‖∑'a,w i a*f i a‖^2) ≤ ∑i,(M*Real.sqrt (v i))^2 :=
      Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (hsum i) 2)
    _ = M^2*∑i,v i := by simp only [mul_pow,Real.sq_sqrt (hv0 _),Finset.mul_sum]
    _ ≤ M^2*E := mul_le_mul_of_nonneg_left
      (sum_iSup_le_of_selection base (fun i a=>‖f i a‖^2) E hselection) (sq_nonneg M)

theorem finite_weighted_selection_energy {ι : Type*} [Fintype ι] {α : ι→Type*}
    (base : ∀i,α i) (s : ∀i,Finset (α i)) (w f : ∀i,α i→ℂ)
    (M E : ℝ) (hM : 0≤M) (hm : ∀i,(∑a∈s i,‖w i a‖)≤M)
    (hselection : ∀a : ∀i,α i,(∑i,‖f i (a i)‖^2)≤E) :
    (∑i,‖∑a∈s i,w i a*f i a‖^2)≤M^2*E := by
  let w' (i : ι) (a : α i) : ℂ := if a∈s i then w i a else 0
  have hs (i : ι) : Summable (fun a=>‖w' i a‖) := by
    apply summable_of_ne_finset_zero (s:=s i)
    intro a ha
    simp [w',ha]
  have hmass (i : ι) : (∑'a,‖w' i a‖)≤M := by
    rw [tsum_eq_sum (s:=s i) (fun a ha=>by simp [w',ha])]
    calc
      (∑a∈s i,‖w' i a‖) = ∑a∈s i,‖w i a‖ := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [w',ha]
      _ ≤ M := hm i
  have hh := (weighted_selection_energy base w' f M E hM hs hmass hselection).2
  have he (i : ι) : (∑'a,w' i a*f i a)=∑a∈s i,w i a*f i a := by
    rw [tsum_eq_sum (s:=s i) (fun a ha=>by simp [w',ha])]
    apply Finset.sum_congr rfl
    intro a ha
    simp [w',ha]
  simpa only [he] using hh

lemma masked_signedWeight_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B)
    (mask : Index S→ℂ) (hm : ∀a,‖mask a‖≤1) :
    Summable (fun a=>‖mask a*signedWeight η ηi S B a‖) := by
  apply (signedWeight_summable_norm η ηi S hS B hB).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm a)

lemma masked_signedWeight_mass_le (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (B : ℕ) (hB : 2≤B)
    (mask : Index S→ℂ) (hm : ∀a,‖mask a‖≤1) :
    (∑'a,‖mask a*signedWeight η ηi S B a‖)≤∑'a,‖signedWeight η ηi S B a‖ := by
  apply (masked_signedWeight_summable_norm η ηi S hS B hB mask hm).tsum_le_tsum
    _ (signedWeight_summable_norm η ηi S hS B hB)
  intro a
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hm a)

theorem actual_masked_reflection_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi : ι→Character)(B : ι→ℕ),(∀i,2≤B i) →
      ∀(R E : ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀(mask f : ∀i,Index (S i)→ℂ),(∀i a,‖mask i a‖≤1) →
      (∀a : ∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖)) ∧
      (∑i,‖∑'a,(mask i a*signedWeight (η i) (ηi i) (S i) (B i) a)*f i a‖^2) ≤
        C*R^ε*E := by
  obtain ⟨C,hC,hb⟩ := uniform_signed_mass (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap mask f hmask hselection
  have hR0 : 0≤R := by linarith
  let M := C*R^(ε/2)
  have hM : 0≤M := by dsimp [M];positivity
  have hs (i : ι) := masked_signedWeight_summable_norm (η i) (ηi i) (S i)
    (hS i) (B i) (hB i) (mask i) (hmask i)
  have hm (i : ι) :
      (∑'a,‖mask i a*signedWeight (η i) (ηi i) (S i) (B i) a‖)≤M := by
    apply (masked_signedWeight_mass_le (η i) (ηi i) (S i) (hS i) (B i) (hB i)
      (mask i) (hmask i)).trans
    apply (hb (S i) (hS i) (η i) (ηi i) (B i) (hB i)).2.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hcap i) (by positivity : 0≤ε/2)) hC.le
  have hh := weighted_selection_energy (fun i=>baseIndex (S i))
    (fun i a=>mask i a*signedWeight (η i) (ηi i) (S i) (B i) a) f M E hM hs hm hselection
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  have hr : (R^(ε/2))^2=R^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hR0]
    congr 1
    ring
  dsimp [M]
  rw [mul_pow,hr]

theorem actual_reflection_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(S : ι→Finset (Ideal O)),(∀i P,P∈S i → Prime P) →
      ∀(η ηi : ι→Character)(B : ι→ℕ),(∀i,2≤B i) →
      ∀(R E : ℝ),1≤R → (∀i,(Ideal.absNorm (∏P∈S i,P):ℝ)≤R) →
      ∀f : ∀i,Index (S i)→ℂ,
      (∀a : ∀i,Index (S i),(∑i,‖f i (a i)‖^2)≤E) →
      (∀i,Summable (fun a=>‖signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖)) ∧
      (∑i,‖∑'a,signedWeight (η i) (ηi i) (S i) (B i) a*f i a‖^2)≤C*R^ε*E := by
  obtain ⟨C,hC,h⟩ := actual_masked_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ S hS η ηi B hB R E hR hcap f hselection
  simpa only [norm_one,one_mul] using
    h S hS η ηi B hB R E hR hcap (fun _ _=>1) f (by intro i a;simp) hselection

end SevenEighths.CenteredMomentReflectionWeightedEnergy

end

end OAI
end OAIOriginalModule2002

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SlotClassTransport
Source SHA256: 577d14af36cd608c2a0d8b7bcdfd6e90551dff74436bd082802de67e07907a33
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2003




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentSlotClassTransport
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentAllocatedNaturalSource CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem common_fixed_slot_coefficient (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C R : Ideal O) (B : actualAllocations s.pools C)
    (i : CenteredMomentCommonProfile.liveIndices B.val) (I : Ideal O) :
    (commonData (withHeight s τ v) C R B).coefficient i I=
      idealCoeff (ν i.val) I*s.W i.val ((I.absNorm:ℝ)/s.P i.val) := by
  change s.ν i.val I*s.W i.val ((I.absNorm:ℝ)/s.P i.val)=_
  rw [hν]

omit [DecidableEq ι] in
theorem commonSlots_fixed_coefficient (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C : Ideal O) (B : actualAllocations s.pools C)
    (i : CenteredMomentCommonProfile.liveIndices B.val) (I : Ideal O) :
    (commonSlots (withHeight s τ v) C B).coefficient i I=
      idealCoeff (ν i.val) I*s.W i.val ((I.absNorm:ℝ)/s.P i.val) := by
  change s.ν i.val I*s.W i.val ((I.absNorm:ℝ)/s.P i.val)=_
  rw [hν]

theorem allocated_fixed_character_gate (s : Input ι) (ν : ι→Character)
    (Q : Ideal O) (hQ : ∀i,Q≤(ν i).modulus)
    (τ : Character) (v : ℝ) (C R L : Ideal O) (B : actualAllocations s.pools C)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (i : CenteredMomentDivisorRaw.liveIndices L a) :
    Q≤(ν i.val.val).modulus ∧
    (commonData (withHeight s τ v) C R B).slots i.val=s.slots i.val.val ∧
    (commonData (withHeight s τ v) C R B).P i.val=s.P i.val.val ∧
    (commonData (withHeight s τ v) C R B).W i.val=s.W i.val.val :=
  ⟨hQ _,rfl,rfl,rfl⟩

theorem allocated_positive_fixed_characters (s : Input ι) (ν : ι→Character)
    (hν : ∀i I,s.ν i I=idealCoeff (ν i) I)
    (τ : Character) (v : ℝ) (C R L : Ideal O) (B : actualAllocations s.pools C)
    (a : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (z : O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) :
    let d:=commonData (withHeight s τ v) C R B
    allocatedPositiveRow d.η d.m d.A z d.t d.slots d.coefficient d.P L a W₁ W₂ X₁ X₂=
      retainedPositiveRow τ
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator (R*C))
        1 z W₁ W₂
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=>s.slots i.val.val)
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=>fun I=>
          idealCoeff (ν i.val.val) I*s.W i.val.val ((I.absNorm:ℝ)/s.P i.val.val))
        (fun i : CenteredMomentDivisorRaw.liveIndices L a=>s.P i.val.val) v
        (X₁/Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain L a 0))
        (X₂/Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain L a 1)) := by
  dsimp only
  unfold allocatedPositiveRow
  have he : (fun i : CenteredMomentDivisorRaw.liveIndices L a=>
      (commonData (withHeight s τ v) C R B).coefficient i.val)=
    (fun i : CenteredMomentDivisorRaw.liveIndices L a=>fun I=>
      idealCoeff (ν i.val.val) I*s.W i.val.val ((I.absNorm:ℝ)/s.P i.val.val)) := by
    funext i I
    exact common_fixed_slot_coefficient s ν hν τ v C R B i.val I
  rw [he]
  rfl

end SevenEighths.CenteredMomentSlotClassTransport

end

end OAI
end OAIOriginalModule2003

/-! Original module: OAI.NumberTheory.DirichletL.ThetaRegularity
Source SHA256: adf047348f003a9442f47729534ae0a2d02ddcf4e9044efaca6def27c96424c1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2004





namespace OAI

noncomputable section

open scoped BigOperators Classical Topology
open Filter Asymptotics

namespace SevenEighths.ThetaRegularity

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic ConcreteTraceCRT GaussianTheta

theorem norm_gaussian (a : ℝ) (z : ℂ) :
    ‖gaussian a z‖ = Real.exp (-Real.pi * a * ‖z‖ ^ 2) := by
  simp [gaussian, Complex.norm_exp, pow_two, Complex.mul_re, Complex.mul_im]

theorem lattice_gap (z : O) (hz : z ≠ 0) : 1 ≤ ‖eisEmbedding z‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {z}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hz)

theorem gaussian_le_inverse_square (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    ‖gaussian a z‖ ≤ ((1 + a * ‖z‖ ^ 2) ^ 2)⁻¹ := by
  let x := a * ‖z‖ ^ 2
  have hx : 0 ≤ x := mul_nonneg ha (sq_nonneg _)
  have h1 : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hs : (1 + x) ^ 2 ≤ Real.exp (Real.pi * x) := calc
    _ ≤ (Real.exp x) ^ 2 := by gcongr
    _ = Real.exp (2 * x) := by rw [pow_two, ← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right Real.two_le_pi hx)
  rw [norm_gaussian]
  have hexp : -Real.pi * a * ‖z‖ ^ 2 = -(Real.pi * x) := by dsimp [x]; ring
  rw [hexp]
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos _) (by positivity)).mpr hs

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

def decayRate : ℝ := Real.pi * parameter c 1

theorem decayRate_pos : 0 < decayRate c :=
  mul_pos Real.pi_pos (parameter_pos c 1 one_pos)

omit [NeZero c] in
theorem parameter_eq (t : ℝ) : parameter c t = parameter c 1 * t := by
  unfold parameter
  ring

omit [NeZero c] in
theorem norm_gaussian_parameter (t : ℝ) (z : ℂ) :
    ‖gaussian (parameter c t) z‖ = Real.exp (-decayRate c * t * ‖z‖ ^ 2) := by
  rw [norm_gaussian, parameter_eq]
  congr 1
  unfold decayRate
  ring

theorem coefficient_norm_le_one (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (r : O ⧸ Ideal.span {c}) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    have hu : ‖χ (u : O ⧸ Ideal.span {c})‖ = 1 := by
      simpa only [MulChar.coe_equivToUnitHom] using
        Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    exact hu.le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    norm_num

theorem term_norm_le (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (z : O) :
    ‖χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian (parameter c t) (eisEmbedding z)‖ ≤
        Real.exp (-decayRate c * t * ‖eisEmbedding z‖ ^ 2) := by
  rw [norm_mul, norm_gaussian_parameter]
  exact mul_le_of_le_one_left (Real.exp_nonneg _) (coefficient_norm_le_one c χ _)

theorem continuousOn_theta_above (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (δ : ℝ) (hδ : 0 < δ) : ContinuousOn (theta c χ) (Set.Ioi δ) := by
  apply continuousOn_tsum (u := fun z : O => ‖gaussian (parameter c δ) (eisEmbedding z)‖)
  · intro z
    unfold gaussian parameter
    fun_prop
  · exact (gaussian_summable _ (parameter_pos c δ hδ)).norm
  · intro z t ht
    apply (term_norm_le c χ t z).trans
    rw [norm_gaussian_parameter]
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ decayRate c * ‖eisEmbedding z‖ ^ 2 :=
      mul_nonneg (decayRate_pos c).le (sq_nonneg _)
    have htd : δ < t := ht
    nlinarith

theorem continuousAt_theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 0 < t) : ContinuousAt (theta c χ) t := by
  have h := continuousOn_theta_above c χ (t / 2) (half_pos ht)
  exact h.continuousAt (isOpen_Ioi.mem_nhds (show t / 2 < t by linarith))

theorem continuousOn_theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    ContinuousOn (theta c χ) (Set.Ioi 0) :=
  fun t ht => (continuousAt_theta c χ t ht).continuousWithinAt

theorem theta_locallyIntegrableOn (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    MeasureTheory.LocallyIntegrableOn (theta c χ) (Set.Ioi 0) :=
  (continuousOn_theta c χ).locallyIntegrableOn measurableSet_Ioi

def tailConstant : ℝ := ∑' z : O, ‖gaussian (parameter c (1 / 2)) (eisEmbedding z)‖

omit [NeZero c] in
theorem tailConstant_nonneg : 0 ≤ tailConstant c := tsum_nonneg (fun _z => norm_nonneg _)

theorem tailConstant_le_cauchy :
    tailConstant c ≤ 4 * (1 + Real.pi / Real.sqrt (parameter c (1 / 2))) ^ 2 := by
  have ha := parameter_pos c (1 / 2) (by norm_num)
  apply le_trans (Summable.tsum_le_tsum
    (fun z : O => gaussian_le_inverse_square _ ha.le (eisEmbedding z))
    (gaussian_summable _ ha).norm
    (EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_summable _ ha))
  exact EisensteinSchwartzPoisson.scaled_eisenstein_cauchy_bound _ ha

theorem tailConstant_le_linear :
    tailConstant c ≤ 8 * (1 + Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖) := by
  have ha := parameter_pos c (1 / 2) (by norm_num)
  have hs : (Real.pi / Real.sqrt (parameter c (1 / 2))) ^ 2 =
      Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖ := by
    rw [div_pow, Real.sq_sqrt ha.le]
    simp only [parameter]
    norm_num
    field_simp
  have h := tailConstant_le_cauchy c
  have hsq := sq_nonneg (1 - Real.pi / Real.sqrt (parameter c (1 / 2)))
  nlinarith

theorem tail_eq_tsum (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 0 < t) :
    theta c χ t - constantTerm c χ = ∑' z : O, if z = 0 then 0 else
      χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z) := by
  have h := (theta_summable c χ t ht).tsum_eq_add_tsum_ite (0 : O)
  rw [theta_zero_term c χ t] at h
  exact sub_eq_iff_eq_add.mpr (by simpa only [theta, add_comm] using h)

theorem tail_term_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 1 ≤ t) (z : O) :
    ‖if z = 0 then (0 : ℂ) else
      χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z)‖ ≤
      Real.exp (-decayRate c * t / 2) *
        ‖gaussian (parameter c (1 / 2)) (eisEmbedding z)‖ := by
  by_cases hz : z = 0
  · simp only [ite_eq_left hz, norm_zero]
    positivity
  · rw [ite_eq_right hz]
    apply (term_norm_le c χ t z).trans
    rw [norm_gaussian_parameter, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hn := lattice_gap z hz
    have hβ := decayRate_pos c
    have hprod : 0 ≤ (t - 1) * (‖eisEmbedding z‖ ^ 2 - 1) :=
      mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hn)
    have hineq : t / 2 + ‖eisEmbedding z‖ ^ 2 / 2 ≤ t * ‖eisEmbedding z‖ ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hineq hβ.le]

theorem theta_tail_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 1 ≤ t) :
    ‖theta c χ t - constantTerm c χ‖ ≤
      tailConstant c * Real.exp (-decayRate c * t / 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [tail_eq_tsum c χ t ht0]
  have hsum := (gaussian_summable _ (parameter_pos c (1 / 2) (by norm_num))).norm
  have hmajor := hsum.mul_left (Real.exp (-decayRate c * t / 2))
  have hnorm := Summable.of_nonneg_of_le (fun z => norm_nonneg _)
    (tail_term_bound c χ t ht) hmajor
  apply (norm_tsum_le_tsum_norm hnorm).trans
  have h := Summable.tsum_le_tsum (tail_term_bound c χ t ht) hnorm hmajor
  simpa only [tsum_mul_left, tailConstant, mul_comm] using h

theorem theta_tail_bound_conductor (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖theta c χ t - constantTerm c χ‖ ≤
      8 * (1 + Real.pi ^ 2 * Real.sqrt 3 * ‖eisEmbedding c‖) *
        Real.exp (-decayRate c * t / 2) :=
  (theta_tail_bound c χ t ht).trans
    (mul_le_mul_of_nonneg_right (tailConstant_le_linear c) (Real.exp_nonneg _))

theorem theta_tail_isBigO_exp (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    (fun t : ℝ => theta c χ t - constantTerm c χ) =O[atTop]
      (fun t : ℝ => Real.exp (-(decayRate c / 2) * t)) := by
  apply isBigO_iff.mpr
  refine ⟨tailConstant c, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have he : -(decayRate c / 2) * t = -decayRate c * t / 2 := by ring
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), he] using theta_tail_bound c χ t ht

theorem theta_tail_isBigO_rpow (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (r : ℝ) :
    (fun t : ℝ => theta c χ t - constantTerm c χ) =O[atTop] (fun t : ℝ => t ^ r) :=
  (theta_tail_isBigO_exp c χ).trans
    (isLittleO_exp_neg_mul_rpow_atTop (half_pos (decayRate_pos c)) r).isBigO

end SevenEighths.ThetaRegularity

end

end OAI
end OAIOriginalModule2004

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Strip
Source SHA256: b720580769968346ea6b92ef674fc411e7c61fc65ebd617eae9053bd7c8834b8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2005



namespace OAI

noncomputable section
open scoped Classical Topology
open Filter Asymptotics Set MeasureTheory

namespace SevenEighths.HeckeStrip

def gammaConstant : ℝ := Real.Gamma (11 / 10) / Real.Gamma (19 / 10)

theorem gammaConstant_pos : 0 < gammaConstant :=
  div_pos (Real.Gamma_pos_of_pos (by norm_num)) (Real.Gamma_pos_of_pos (by norm_num))

theorem gamma_ratio_left_bound (t : ℝ) :
    ‖Complex.Gamma (1 - ((-(1 / 10) : ℂ) + t * Complex.I)) /
      Complex.Gamma ((-(1 / 10) : ℂ) + t * Complex.I)‖ ≤
        gammaConstant * (3 + |t|) ^ 2 := by
  let s : ℂ := -(1 / 10) + t * Complex.I
  have hb := CubicReflectionKernel.Gamma_shifted_pair_bound
    (1 / 2) (3 / 5) (-t) 2 (by norm_num) (by norm_num)
  simp only [Complex.ofReal_neg] at hb
  have hnum : ((1 / 2 : ℝ) : ℂ) + ((3 / 5 : ℝ) + (-t) * Complex.I) = 1 - s := by
    dsimp [s]; push_cast; ring
  have hden : ((1 / 2 : ℝ) : ℂ) - ((3 / 5 : ℝ) + (-t) * Complex.I) + (2 : ℕ) = s + 2 := by
    dsimp [s]; push_cast; ring
  rw [hnum, hden] at hb
  norm_num only [show (1 / 2 : ℝ) + 3 / 5 = 11 / 10 by norm_num,
    show (1 / 2 : ℝ) - 3 / 5 + (2 : ℕ) = 19 / 10 by norm_num] at hb
  have heq : Complex.Gamma (1 - s) / Complex.Gamma s =
      (∏ k ∈ Finset.range 2, (s + k)) *
        (Complex.Gamma (1 - s) / Complex.Gamma (s + 2)) := by
    rw [div_eq_mul_inv, CubicReflectionKernel.inverse_Gamma_shift s 2]
    simp only [Nat.cast_ofNat, div_eq_mul_inv]
    ring
  have hs : ‖s‖ ≤ 1 / 10 + |t| := by
    simpa [s, norm_mul] using norm_add_le (-(1 / 10) : ℂ) ((t : ℂ) * Complex.I)
  have hf := CubicReflectionKernel.norm_Gamma_shift_factor s 2
  have hf' : ‖∏ k ∈ Finset.range 2, (s + k)‖ ≤ (3 + |t|) ^ 2 := by
    have hs2 : ‖s‖ + (2 : ℝ) ≤ 3 + |t| := by linarith
    exact hf.trans (pow_le_pow_left₀ (by positivity) hs2 2)
  change ‖Complex.Gamma (1 - s) / Complex.Gamma s‖ ≤ _
  rw [heq, norm_mul]
  exact (mul_le_mul hf' hb (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem gamma_ratio_left_bound_of_re (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖Complex.Gamma (1 - z) / Complex.Gamma z‖ ≤ gammaConstant * (3 + |z.im|) ^ 2 := by
  have he : (-(1 / 10) : ℂ) + z.im * Complex.I = z := by
    simpa only [hz, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using Complex.re_add_im z
  simpa only [he] using gamma_ratio_left_bound z.im

def completionScale (Q : ℝ) : ℝ := Real.sqrt (3 * Q) / (2 * Real.pi)

theorem completionScale_pos (Q : ℝ) (hQ : 0 < Q) : 0 < completionScale Q := by
  unfold completionScale
  positivity

theorem completionScale_left_power (Q : ℝ) (hQ : 0 < Q) :
    completionScale Q ^ (6 / 5 : ℝ) =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
  have he : completionScale Q = (Real.sqrt 3 / (2 * Real.pi)) * Real.sqrt Q := by
    unfold completionScale
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    ring
  rw [he, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _)]
  congr 1
  rw [Real.sqrt_eq_rpow Q, ← Real.rpow_mul hQ.le]
  norm_num

def leftConstant : ℝ :=
  (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * gammaConstant

theorem leftConstant_pos : 0 < leftConstant :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) gammaConstant_pos

theorem left_boundary_of_functional_equation (Q D : ℝ) (hQ : 0 < Q) (_hD : 0 ≤ D)
    (L Ldual : ℂ → ℂ) (ε : ℂ) (hε : ‖ε‖ = 1)
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z.re = -(1 / 10)) :
    ‖L z‖ ≤ leftConstant * D * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hscale : ‖(completionScale Q : ℂ) ^ (1 - 2 * z)‖ =
      (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (completionScale_pos Q hQ)]
    have hre : (1 - 2 * z).re = 6 / 5 := by simp [hz]; norm_num
    rw [hre, completionScale_left_power Q hQ]
  have hd : ‖Ldual (1 - z)‖ ≤ D := hdual _ (by simp [hz]; norm_num)
  rw [hfe z hz, norm_mul, norm_mul, norm_mul, hε, one_mul, hscale]
  have hg := gamma_ratio_left_bound_of_re z hz
  have hc := gammaConstant_pos
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left hg (by positivity)) hd (norm_nonneg _)
    (by positivity : 0 ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
      (gammaConstant * (3 + |z.im|) ^ 2))
  calc
    _ ≤ ((Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ) * Q ^ (3 / 5 : ℝ)) *
        (gammaConstant * (3 + |z.im|) ^ 2) * D := hm
    _ = _ := by unfold leftConstant; ring

def strip : Set ℂ := Complex.re ⁻¹' Ioo (-(1 / 10)) (11 / 10)
def closedStrip : Set ℂ := Complex.re ⁻¹' Icc (-(1 / 10)) (11 / 10)

theorem vertical_strip_of_exp_bound (F : ℂ → ℂ) (C : ℝ)
    (hF : DiffContOnCl ℂ F strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖F z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) → ‖F z‖ ≤ C)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖F z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) : ‖F z‖ ≤ C := by
  obtain ⟨A, B, hA, hB, hgrowth⟩ := hgrowth
  apply PhragmenLindelof.vertical_strip hF ?_ hleft hright hz.1 hz.2
  refine ⟨1, ?_, B, ?_⟩
  · apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 11 / 10 - -(1 / 10))).mpr
    linarith [Real.two_le_pi]
  · apply isBigO_iff.mpr
    refine ⟨A, eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)⟩
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (hgrowth z hz).trans
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    simp only [one_mul]
    exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp |z.im|]) hB

theorem closure_strip_subset : closure strip ⊆ closedStrip :=
  closure_minimal (fun _ hz => ⟨hz.1.le, hz.2.le⟩)
    (isClosed_Icc.preimage Complex.continuous_re)

theorem shift_norm_lower (z : ℂ) (hz : z ∈ closedStrip) : 1 ≤ ‖z + 2‖ := by
  have h := Complex.re_le_norm (z + 2)
  norm_num at h
  linarith [hz.1]

theorem shift_ne_zero (z : ℂ) (hz : z ∈ closedStrip) : z + 2 ≠ 0 := by
  have h := shift_norm_lower z hz
  intro hzero
  rw [hzero, norm_zero] at h
  norm_num at h

theorem height_le_shift_norm (z : ℂ) (hz : z ∈ closedStrip) :
    3 + |z.im| ≤ 3 * ‖z + 2‖ := by
  have hr := Complex.re_le_norm (z + 2)
  have hi := Complex.abs_im_le_norm (z + 2)
  norm_num at hr hi
  linarith [hz.1]

theorem shift_norm_le_height (z : ℂ) (hz : z ∈ closedStrip) :
    ‖z + 2‖ ≤ 2 * (3 + |z.im|) := by
  have hr : 0 ≤ z.re + 2 := by linarith [hz.1]
  have h := Complex.norm_le_abs_re_add_abs_im (z + 2)
  norm_num [abs_of_nonneg hr] at h
  linarith [hz.2, abs_nonneg z.im]

def normalized (Q : ℝ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  L z / (((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2)

theorem norm_normalized (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ) (z : ℂ) :
    ‖normalized Q L z‖ = ‖L z‖ / (Q ^ (3 / 5 : ℝ) * ‖z + 2‖ ^ 2) := by
  simp [normalized, norm_pow,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hQ _)]

theorem normalized_diffContOnCl (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hL : DiffContOnCl ℂ L strip) : DiffContOnCl ℂ (normalized Q L) strip := by
  have hqn : ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)).ne'
  have hd : Differentiable ℂ (fun z : ℂ => ((Q ^ (3 / 5 : ℝ) : ℝ) : ℂ) * (z + 2) ^ 2) := by
    fun_prop
  refine ⟨hL.differentiableOn.div hd.differentiableOn ?_, hL.continuousOn.div hd.continuous.continuousOn ?_⟩
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z ⟨hz.1.le, hz.2.le⟩))
  · intro z hz
    exact mul_ne_zero hqn (pow_ne_zero _ (shift_ne_zero z (closure_strip_subset hz)))

theorem normalized_exp_bound (Q : ℝ) (hQ : 0 < Q) (L : ℂ → ℂ)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖normalized Q L z‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨A, B, hA, hB, hg⟩ := hgrowth
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  refine ⟨A / Q ^ (3 / 5 : ℝ), B, div_nonneg hA hq.le, hB, ?_⟩
  intro z hz
  have hn := shift_norm_lower z ⟨hz.1.le, hz.2.le⟩
  have hn2 : 1 ≤ ‖z + 2‖ ^ 2 := by nlinarith
  rw [norm_normalized Q hQ]
  calc
    _ ≤ ‖L z‖ / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hq (by nlinarith)
    _ ≤ (A * Real.exp (B * |z.im|)) / Q ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_right (hg z hz) hq.le
    _ = _ := by ring

theorem normalized_boundary_bound (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (z : ℂ) (hz : z ∈ closedStrip)
    (hL : ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2) :
    ‖normalized Q L z‖ ≤ 9 * C := by
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hn : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  have hh := height_le_shift_norm z hz
  have hh2 : (3 + |z.im|) ^ 2 ≤ 9 * ‖z + 2‖ ^ 2 := by
    nlinarith [abs_nonneg z.im, norm_nonneg (z + 2)]
  rw [norm_normalized Q hQ]
  apply (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hn))).mpr
  apply hL.trans
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg hC hq.le)
  nlinarith

theorem uniform_strip_bound_of_edges (Q C : ℝ) (hQ : 0 < Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hn : ‖normalized Q L z‖ ≤ 9 * C := by
    apply vertical_strip_of_exp_bound _ _ (normalized_diffContOnCl Q hQ L hL)
      (normalized_exp_bound Q hQ L hgrowth) ?_ ?_ z hz
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw], by rw [hw]; norm_num⟩) (hleft w hw)
    · intro w hw
      apply normalized_boundary_bound Q C hQ hC L w
        (show w ∈ closedStrip from ⟨by rw [hw]; norm_num, by rw [hw]⟩) (hright w hw)
  have hq := Real.rpow_pos_of_pos hQ (3 / 5 : ℝ)
  have hnz : 0 < ‖z + 2‖ := lt_of_lt_of_le zero_lt_one (shift_norm_lower z hz)
  rw [norm_normalized Q hQ] at hn
  have hb := (div_le_iff₀ (mul_pos hq (sq_pos_of_pos hnz))).mp hn
  have hh := shift_norm_le_height z hz
  have hh2 : ‖z + 2‖ ^ 2 ≤ 4 * (3 + |z.im|) ^ 2 := by
    nlinarith [norm_nonneg (z + 2), abs_nonneg z.im]
  have h := mul_le_mul_of_nonneg_left hh2 (mul_nonneg (by positivity : 0 ≤ 9 * C) hq.le)
  nlinarith

theorem uniform_strip_bound (Q C : ℝ) (hQ : 1 ≤ Q) (hC : 0 ≤ C)
    (L : ℂ → ℂ) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hleft : ∀ z : ℂ, z.re = -(1 / 10) →
      ‖L z‖ ≤ C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2)
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ C)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * C * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  apply uniform_strip_bound_of_edges Q C (lt_of_lt_of_le zero_lt_one hQ) hC L hL
    hgrowth hleft ?_ z hz
  intro w hw
  apply (hright w hw).trans
  have hq : 1 ≤ Q ^ (3 / 5 : ℝ) := Real.one_le_rpow hQ (by norm_num)
  have hh : 1 ≤ (3 + |w.im|) ^ 2 := by nlinarith [abs_nonneg w.im]
  calc
    C ≤ C * Q ^ (3 / 5 : ℝ) := le_mul_of_one_le_right hC hq
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hC (le_trans zero_le_one hq)) hh

theorem uniform_strip_bound_of_functional_equation
    (Q D : ℝ) (hQ : 1 ≤ Q) (hD : 0 ≤ D) (L Ldual : ℂ → ℂ)
    (ε : ℂ) (hε : ‖ε‖ = 1) (hL : DiffContOnCl ℂ L strip)
    (hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ z ∈ strip, ‖L z‖ ≤ A * Real.exp (B * |z.im|))
    (hfe : ∀ z : ℂ, z.re = -(1 / 10) → L z =
      ε * (completionScale Q : ℂ) ^ (1 - 2 * z) *
        (Complex.Gamma (1 - z) / Complex.Gamma z) * Ldual (1 - z))
    (hright : ∀ z : ℂ, z.re = 11 / 10 → ‖L z‖ ≤ D)
    (hdual : ∀ z : ℂ, z.re = 11 / 10 → ‖Ldual z‖ ≤ D)
    (z : ℂ) (hz : z ∈ closedStrip) :
    ‖L z‖ ≤ 36 * ((1 + leftConstant) * D) * Q ^ (3 / 5 : ℝ) * (3 + |z.im|) ^ 2 := by
  have hQ0 := lt_of_lt_of_le zero_lt_one hQ
  have hc := leftConstant_pos
  apply uniform_strip_bound Q ((1 + leftConstant) * D) hQ (by positivity) L hL hgrowth ?_ ?_ z hz
  · intro w hw
    apply (left_boundary_of_functional_equation Q D hQ0 hD L Ldual ε hε hfe hdual w hw).trans
    have hbase : leftConstant * D ≤ (1 + leftConstant) * D := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg hQ0.le _)) (sq_nonneg _)
  · intro w hw
    apply (hright w hw).trans
    nlinarith

theorem uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (F : ℂ → ℂ)
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ closedStrip, ‖F z‖ ≤ C) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * F z‖ ≤
        A * Real.exp (B * |z.im|) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨G, hG, hg⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (-(1 / 10)) (11 / 10)
  let S : ℝ := a ^ (-(11 / 10) : ℝ) + a ^ (1 / 10 : ℝ)
  have hS : 0 ≤ S := add_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg ha.le _)
  refine ⟨S * G * C, Real.pi, by positivity, Real.pi_pos.le, ?_⟩
  intro z hz
  have hzc : z ∈ closedStrip := ⟨hz.1.le, hz.2.le⟩
  have haBound : ‖(a : ℂ) ^ (-z)‖ ≤ S := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re]
    exact VerticalContourShift.rpow_between_endpoints a (-(11 / 10)) (1 / 10) (-z.re)
      ha (by linarith [hz.2]) (by linarith [hz.1])
  rw [norm_mul, norm_mul]
  have hgamma := hg z hzc
  have hprod := mul_le_mul (mul_le_mul haBound hgamma (norm_nonneg _) hS)
    (hF z hzc) (norm_nonneg _) (mul_nonneg hS (mul_nonneg hG.le (Real.exp_nonneg _)))
  nlinarith

theorem mellin_uncompleted_exp_bound (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ)
    (hleft : MellinConvergent f (-(1 / 10) : ℂ))
    (hright : MellinConvergent f (11 / 10 : ℂ)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ strip,
      ‖(a : ℂ) ^ (-z) * (Complex.Gamma z)⁻¹ * mellin f z‖ ≤
        A * Real.exp (B * |z.im|) := by
  apply uncompleted_exp_bound a ha (mellin f)
  obtain ⟨C, hC, hb⟩ := VerticalContourShift.mellin_uniform_strip_bound f
    (-(1 / 10)) (11 / 10) (by simpa using hleft) (by simpa using hright)
  exact ⟨C, hC, fun z hz => hb z hz.1 hz.2⟩

end SevenEighths.HeckeStrip
end

end OAI
end OAIOriginalModule2005

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.StripActual
Source SHA256: 3c4e1debb9c1265a90079382fdcef5433cdde33035256873c993debcc5c2e579
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2006




namespace OAI

noncomputable section
open scoped Classical Topology BigOperators
open Set MeasureTheory
namespace SevenEighths.HeckeStripActual
open HeckeFamily HeckePrimitive

variable (c : O) [NeZero c]

private instance : Fintype (O ⧸ Ideal.span {c}) := by
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using NeZero.ne c)
  exact Fintype.ofFinite _

def conductor : ℝ := Ideal.absNorm (Ideal.span {c})

theorem conductor_ge_one : 1 ≤ conductor c := by
  unfold conductor
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {c}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact NeZero.ne c)

theorem completionScale_eq_inv :
    HeckeStrip.completionScale (conductor c) = (Real.pi * scale c)⁻¹ := by
  have hn : 0 < ‖ConcreteTraceCRT.eisEmbedding c‖ := by
    have h := ThetaRegularity.lattice_gap c (NeZero.ne c)
    nlinarith [norm_nonneg (ConcreteTraceCRT.eisEmbedding c)]
  unfold HeckeStrip.completionScale conductor scale GaussianTheta.parameter
  rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq (norm_nonneg _)]
  field_simp

theorem completionScale_cpow (s : ℂ) :
    (HeckeStrip.completionScale (conductor c) : ℂ)^s =
      (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) := by
  rw [completionScale_eq_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (mul_nonneg Real.pi_pos.le (scale_pos c).le),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (scale_pos c).le,
    mul_inv_rev]
  simp only [Complex.cpow_neg]

theorem completedL_eq_standard (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s =
      (HeckeStrip.completionScale (conductor c) : ℂ)^s * Complex.Gamma s *
        LFunction (character c χ hu) s := by
  rw [completedL_eq_gamma_mul_LFunction c χ hu hp h0 h1 hΓ, completionScale_cpow]

theorem LFunction_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖LFunction η s‖ ≤ HeckeReciprocalBound.bound σ := by
  have hs1 := hσ.trans_le hs
  rw [LFunction_eq_series η hs1, IdealEuler.series]
  have hsum := IdealEuler.weighted_summable_norm (idealCoeff η) (idealCoeff_norm_le_one η) s hs1
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply Summable.tsum_le_tsum _ hsum
    (CubicEisenstein.fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ))
  intro I
  change ‖idealCoeff η I * CubicEisenstein.fullIdealWeight s I‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I)).trans
    (HeckeReciprocalBound.normWeight_le_of_re_ge hs I)

theorem pair_strong (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) :
    IsStrongFEPair (pair c χ hu hp) := by
  constructor
  · exact HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal (character c χ hu) hχ
  · apply HeckeCharacterAnalytic.coefficients_zero_of_nonprincipal
      (character c χ⁻¹ (inverse_unit_trivial c χ hu))
    change χ⁻¹ ≠ 1
    simpa only [ne_eq, inv_eq_one] using hχ

theorem LFunction_eq_uncompleted (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) (s : ℂ) :
    LFunction (character c χ hu) s =
      (HeckeStrip.completionScale (conductor c) : ℂ)^(-s) * (Complex.Gamma s)⁻¹ *
        completedL c χ hu hp s := by
  let a := HeckeStrip.completionScale (conductor c)
  have ha : 0 < a := HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))
  have hL := LFunction_entire_nonprincipal (character c χ hu) hχ
  have hΛ : Differentiable ℂ (completedL c χ hu hp) :=
    (pair_strong c χ hu hp hχ).differentiable_Λ.div_const 6
  have hR : Differentiable ℂ (fun z : ℂ => (a : ℂ)^(-z) * (Complex.Gamma z)⁻¹ *
      completedL c χ hu hp z) :=
    (((differentiable_id.neg).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      Complex.differentiable_one_div_Gamma).mul hΛ
  have he : LFunction (character c χ hu) = fun z : ℂ => (a : ℂ)^(-z) *
      (Complex.Gamma z)⁻¹ * completedL c χ hu hp z := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hL).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hR) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have h0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have h1 : z ≠ 1 := by intro h; norm_num [h] at hz
    have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    rw [completedL_eq_standard c χ hu hp h0 h1 hΓ]
    have haz : (a : ℂ)^z ≠ 0 := (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [ha.ne'])
    change LFunction (character c χ hu) z = (a : ℂ)^(-z) * (Complex.Gamma z)⁻¹ *
      ((a : ℂ)^z * Complex.Gamma z * LFunction (character c χ hu) z)
    rw [Complex.cpow_neg]
    field_simp
  exact congr_fun he s

theorem functional_equation_left (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (hs : s.re = -(1/10)) :
    LFunction (character c χ hu) s = TraceCharacter.normalizedGauss c χ *
      (HeckeStrip.completionScale (conductor c) : ℂ)^(1-2*s) *
      (Complex.Gamma (1-s) / Complex.Gamma s) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s) := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hs0 : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hs1 : 1-s ≠ 1 := by intro h; apply h0; linear_combination -h
  have hΓdual : Complex.Gamma (1-s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs]; norm_num)
  have hΓ : Complex.Gamma s ≠ 0 := by
    have h := Complex.Gamma_ne_zero_of_re_pos (s := s+1) (by simp [hs]; norm_num)
    rw [Complex.Gamma_add_one s h0] at h
    exact (mul_ne_zero_iff.mp h).2
  have he := completedL_functional_equation c χ hu hp hs0 hs1
  rw [sub_sub_cancel] at he
  rw [completedL_eq_standard c χ hu hp h0 h1 hΓ,
    completedL_eq_standard c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv hs0 hs1 hΓdual] at he
  let a := HeckeStrip.completionScale (conductor c)
  have ha : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))).ne'
  have haz : (a : ℂ)^s ≠ 0 := (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [ha])
  have hpow : (a : ℂ)^(1-s) = (a : ℂ)^s * (a : ℂ)^(1-2*s) := by
    rw [← Complex.cpow_add _ _ ha]
    congr 1
    ring
  apply mul_left_cancel₀ (mul_ne_zero haz hΓ)
  calc
    _ = TraceCharacter.normalizedGauss c χ * ((a : ℂ)^(1-s) * Complex.Gamma (1-s) *
        LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)) (1-s)) := he
    _ = _ := by
      change _ = ((a : ℂ)^s * Complex.Gamma s) *
        (TraceCharacter.normalizedGauss c χ * (a : ℂ)^(1-2*s) *
          (Complex.Gamma (1-s)/Complex.Gamma s) * _)
      rw [hpow]
      field_simp

theorem LFunction_exp_growth (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ HeckeStrip.strip,
      ‖LFunction (character c χ hu) z‖ ≤ A * Real.exp (B * |z.im|) := by
  let f : ℝ → ℂ := fun t => (pair c χ hu hp).f t / 6
  have hP := pair_strong c χ hu hp hχ
  have hconv (s : ℂ) : MellinConvergent f s := (hP.hasMellin s).1.div_const 6
  have h := HeckeStrip.mellin_uncompleted_exp_bound
    (HeckeStrip.completionScale (conductor c))
    (HeckeStrip.completionScale_pos _ (lt_of_lt_of_le zero_lt_one (conductor_ge_one c))) f
    (hconv _) (hconv _)
  have heq (z : ℂ) :
      (HeckeStrip.completionScale (conductor c) : ℂ)^(-z) * (Complex.Gamma z)⁻¹ * mellin f z =
        LFunction (character c χ hu) z := by
    rw [LFunction_eq_uncompleted c χ hu hp hχ]
    congr 1
    change mellin (fun t => (pair c χ hu hp).f t / 6) z = (pair c χ hu hp).Λ z / 6
    rw [mellin_div_const, (hP.hasMellin z).2]
  simpa only [heq] using h

theorem uniform_strip_bound (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖LFunction (character c χ hu) z‖ ≤
      36 * ((1 + HeckeStrip.leftConstant) * HeckeReciprocalBound.bound (11/10)) *
        conductor c ^ (3/5 : ℝ) * (3 + |z.im|)^2 := by
  apply HeckeStrip.uniform_strip_bound_of_functional_equation
    (conductor c) (HeckeReciprocalBound.bound (11/10)) (conductor_ge_one c)
    (tsum_nonneg (fun _ => norm_nonneg _))
    (LFunction (character c χ hu))
    (LFunction (character c χ⁻¹ (inverse_unit_trivial c χ hu)))
    (TraceCharacter.normalizedGauss c χ) (TraceCharacter.normalizedGauss_norm c χ hp)
    (LFunction_entire_nonprincipal (character c χ hu) hχ).diffContOnCl
    (LFunction_exp_growth c χ hu hp hχ) (fun _ hs => functional_equation_left c χ hu hp hs)
    _ _ z hz
  · intro s hs
    exact LFunction_norm_le _ (by norm_num : (1 : ℝ) < 11/10) hs.ge
  · intro s hs
    exact LFunction_norm_le _ (by norm_num : (1 : ℝ) < 11/10) hs.ge

end SevenEighths.HeckeStripActual

end

end OAI
end OAIOriginalModule2006

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicMellin
Source SHA256: 7d39e81729715eeb072b352fc9298d47698ff2758364294508d33019ae442e82
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2007



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def twistedCoefficient (χ : Character) (inverse : Bool) (σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ inverse I.val * (norm I : ℂ)^(-shift σ freq)

theorem twisted_coefficient_summable (χ : Character) (inverse : Bool) (c σ freq : ℝ)
    (hc : 1 < c+σ) :
    Summable (fun I : NonzeroIdeal => ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c)) := by
  have hf := (CubicEisenstein.fullIdealWeight_summable_norm ((c+σ : ℝ) : ℂ)
    (by simpa using hc)).comp_injective (Subtype.val_injective : Function.Injective
      (fun I : NonzeroIdeal => I.val))
  apply hf.of_nonneg_of_le (fun I => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_pos I).le _))
  intro I
  have hI : I.val ≠ 0 := I.property
  change ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c) ≤
    ‖CubicEisenstein.fullIdealWeight ((c+σ : ℝ) : ℂ) I.val‖
  rw [CubicEisenstein.fullIdealWeight, ite_eq_right hI]
  change ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c) ≤
    ‖(norm I : ℂ)^(-((c+σ : ℝ) : ℂ))‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp only [Complex.neg_re, Complex.ofReal_re]
  unfold twistedCoefficient
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re, shift_re]
  calc
    _ = ‖coefficient χ inverse I.val‖ * (norm I)^(-(c+σ)) := by
      rw [mul_assoc, ← Real.rpow_add (norm_pos I)]
      congr 2
      ring
    _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg (norm_pos I).le _)
      (coefficient_norm_le χ inverse I.val)

theorem twisted_series_eq (χ : Character) (inverse : Bool) (σ freq : ℝ)
    {s : ℂ} (hs : 1 < (s+shift σ freq).re) :
    (∑' I : NonzeroIdeal, twistedCoefficient χ inverse σ freq I*(norm I : ℂ)^(-s)) =
      series χ inverse (s+shift σ freq) := by
  rw [series_eq_tsum χ inverse hs]
  apply tsum_congr
  intro I
  unfold twistedCoefficient
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_pos I).ne')]
  congr 2
  ring

theorem polynomial_eq_weighted (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0 < D) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(shift σ freq-(1/2 : ℂ)) *
        ∑' I : NonzeroIdeal, twistedCoefficient χ inverse σ freq I * W (norm I/D) := by
  have he (I : NonzeroIdeal) : summand χ inverse W D σ freq I =
      (D : ℂ)^(shift σ freq) * (twistedCoefficient χ inverse σ freq I * W (norm I/D)) := by
    unfold summand twistedCoefficient
    rw [CompletedGauss.positive_quotient_cpow_neg _ _ (norm_pos I) hD]
    ring
  unfold polynomial
  simp_rw [he]
  rw [tsum_mul_left, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 2
  ring

theorem polynomial_mellin (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hWs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (D c σ freq : ℝ) (hD : 0 < D) (hc : 1 < c+σ) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
      mellin W ((c : ℂ)+t*Complex.I) *
        (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) *
          series χ inverse (((c : ℂ)+t*Complex.I)+shift σ freq) := by
  rw [polynomial_eq_weighted χ inverse W D σ freq hD]
  rw [CompletedGauss.weightedMellin_inversion norm norm_pos
    (twistedCoefficient χ inverse σ freq) c (twisted_coefficient_summable χ inverse c σ freq hc)
    W a b ha hWs hW D hD]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [twisted_series_eq χ inverse σ freq (by simpa using hc)]
  have he : (D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I) =
      (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
    congr 1
    ring
  calc
    _ = mellin W ((c : ℂ)+t*Complex.I) *
        ((D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I)) *
          series χ inverse (((c : ℂ)+t*Complex.I)+shift σ freq) := by ring
    _ = _ := by rw [he]

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2007

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicContour
Source SHA256: e6b8fae8e52db0a45f050758ec3cbeea8a92e7e5ab13eac517320a0cd6644c6c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2008


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

def integrand (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+shift σ freq-(1/2 : ℂ)) *
    series χ inverse (s+shift σ freq)

theorem series_norm_le (χ : Character) (inverse : Bool) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤s.re) :
    ‖series χ inverse s‖ ≤ HeckeReciprocalBound.bound b := by
  cases inverse
  · exact HeckeStripActual.LFunction_norm_le χ hb hs
  · exact HeckeReciprocalBound.reciprocal_norm_le χ hb hs

theorem series_differentiableAt_right (χ : Character) (inverse : Bool) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hs) (Or.inl (by intro h; norm_num [h] at hs))
  · exact HeckeReciprocal.reciprocal_differentiableAt χ
      (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one hs)

theorem series_differentiableAt_nonprincipal (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) {s : ℂ} (hz : inverse=true → LFunction χ s≠0) :
    DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_entire_nonprincipal χ hχ s
  · have he : series χ true = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [series, HeckeReciprocal.reciprocal, hχ]
    rw [he]
    exact (LFunction_entire_nonprincipal χ hχ s).inv (hz rfl)

theorem integrand_differentiableAt (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (series χ inverse) (s+shift σ freq)) :
    DifferentiableAt ℂ (integrand χ inverse W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (shift σ freq))

theorem integrand_norm (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ inverse W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ inverse (s+shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem integrand_vertical_integrable (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (hc : 1<c+σ) :
    Integrable (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_right χ inverse (by simpa using hc))).continuousAt.comp
    fun_prop
  have hm := (CompletedGauss.compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*HeckeReciprocalBound.bound (c+σ))).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [integrand_norm χ inverse W D σ freq hD]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (series_norm_le χ inverse hc (by simp))
  positivity

theorem finite_rectangle (χ : Character) (hχ : χ.residue≠1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) := by
  have hhol : DifferentiableOn ℂ (integrand χ inverse W D σ freq)
      (uIcc l r ×ℂ uIcc (-T) T) := by
    intro s hs
    exact (integrand_differentiableAt χ inverse W a b ha hWs hW D σ freq hD
      (series_differentiableAt_nonprincipal χ hχ inverse (hz s hs))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand χ inverse W D σ freq) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem polynomial_finite_shift (χ : Character) (hχ : χ.residue≠1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1<r+σ) (hT : 0≤T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ inverse W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) = _
  rw [← integral_add_compl measurableSet_Icc
    (integrand_vertical_integrable χ inverse W a b ha hWs hW D r σ freq hD hr)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T≤T)]
  rw [finite_rectangle χ hχ inverse W a b ha hWs hW D σ freq l r T hD hz]

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2008

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicEstimates
Source SHA256: f77d6813d5a8b8e1a8ffe38ef5c8aab47a3e549879a34b10a26fe1935e0b0139
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2009


namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem rapid_tail_bound (F : ℝ → ℂ) (C T : ℝ) (n : ℕ) (hC : 0≤C) (hT : 0≤T)
    (hF : ∀ t : ℝ, (1+|t|)^(n+2)*‖F t‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, F t‖ ≤ C/(1+T)^n*Real.pi := by
  have hen (t : ℝ) (ht : t ∈ (Icc (-T) T)ᶜ) :
      ‖F t‖≤(C/(1+T)^n)*(1+t^2)⁻¹ := by
    have ht' : T≤|t| := by
      by_contra h
      have hab : |t|<T := lt_of_not_ge h
      exact ht ⟨(abs_lt.mp hab).1.le, (abs_lt.mp hab).2.le⟩
    have hp : (1+T)^n*(1+t^2)≤(1+|t|)^(n+2) := by
      rw [pow_add]
      apply mul_le_mul
      · exact pow_le_pow_left₀ (by linarith) (by linarith) n
      · nlinarith [sq_abs t, abs_nonneg t]
      · positivity
      · positivity
    have hh : ‖F t‖*((1+T)^n*(1+t^2))≤C :=
      (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (by simpa [mul_comm] using hF t)
    have hb := (le_div_iff₀ (by positivity : 0<(1+T)^n*(1+t^2))).mpr hh
    simpa [div_mul_eq_div_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hb
  have hint := (integrable_inv_one_add_sq.const_mul (C/(1+T)^n))
  calc
    _ ≤ ∫ t : ℝ in (Icc (-T) T)ᶜ, (C/(1+T)^n)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
      exact hen t ht
    _ ≤ ∫ t : ℝ, (C/(1+T)^n)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem absolute_tail_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D r σ freq C T : ℝ) (n : ℕ) (hD : 0<D) (hr : 1<r+σ) (hC : 0≤C) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖≤C) :
    ‖∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)‖ ≤
      (C*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi := by
  apply rapid_tail_bound _ _ T n
  · exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hD.le _))
      (tsum_nonneg (fun _ => norm_nonneg _))
  · exact hT
  · intro t
    rw [integrand_norm χ inverse W D σ freq hD]
    have hb := series_norm_le χ inverse hr (s := (r : ℂ)+t*I+shift σ freq) (by simp)
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
      sub_self, add_zero]
    calc
      _ = ((1+|t|)^(n+2)*‖mellin W ((r : ℂ)+t*I)‖)*D^(r+σ-1/2)*
        ‖series χ inverse ((r : ℂ)+t*I+shift σ freq)‖ := by ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right (hm t) (Real.rpow_nonneg hD.le _))
        hb (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hD.le _))

theorem central_segment_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D l σ freq C K T : ℝ) (hD : 0<D) (hC : 0≤C) (hK : 0≤K) (hT : 0≤T)
    (hm : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤C)
    (hs : ∀ t ∈ Icc (-T) T, ‖series χ inverse ((l : ℂ)+t*I+shift σ freq)‖≤K) :
    ‖∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)‖ ≤
      C*D^(l+σ-1/2)*K*Real.pi := by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint := integrable_inv_one_add_sq.const_mul (C*D^(l+σ-1/2)*K)
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ := by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ inverse W D σ freq hD]
      have hb := CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t (hm t)
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
        sub_self, add_zero]
      calc
        _ ≤ (C/(1+t^2))*D^(l+σ-1/2)*K :=
          mul_le_mul (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hD.le _))
            (hs t ⟨ht.1.le,ht.2⟩) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ ∫ t : ℝ, (C*D^(l+σ-1/2)*K)*(1+t^2)⁻¹ :=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2009

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.DyadicJoins
Source SHA256: d599abac4adc5bdc2a06338be16ad57f3be6197273b572c1e649941779878c15
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2010


namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem horizontal_join_bound (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq l r y C K : ℝ) (n : ℕ)
    (hD : 1≤D) (hlr : l≤r) (hC : 0≤C) (_hK : 0≤K)
    (hm : ∀ x ∈ Icc l r, (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤C)
    (hs : ∀ x ∈ Icc l r, ‖series χ inverse ((x : ℂ)+y*I+shift σ freq)‖≤K) :
    ‖∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+y*I)‖ ≤
      (C*D^(r+σ-1/2)*K/(1+|y|)^n)*|r-l| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  have hx' : x ∈ Icc l r := by simpa [uIcc_of_le hlr] using uIoc_subset_uIcc hx
  have hb : ‖mellin W ((x : ℂ)+y*I)‖≤C/(1+|y|)^n := by
    apply (le_div_iff₀ (by positivity : 0<(1+|y|)^n)).mpr
    simpa [mul_comm] using hm x hx'
  have hpow : D^(x+σ-1/2)≤D^(r+σ-1/2) :=
    Real.rpow_le_rpow_of_exponent_le hD (by linarith [hx'.2])
  rw [integrand_norm χ inverse W D σ freq (by linarith)]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  calc
    _ ≤ (C/(1+|y|)^n)*D^(r+σ-1/2)*K :=
      mul_le_mul (mul_le_mul hb hpow (by positivity) (by positivity))
        (hs x hx') (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem profile_strip_decay (a b : ℝ) (ha : 0<a) (l r : ℝ) (n : ℕ) :
    ∃ (S : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ → ℂ)⊆Icc a b →
      ∀ x ∈ Icc l r, ∀ y : ℝ,
      (1+|y|)^n*‖mellin W ((x : ℂ)+y*I)‖≤
        C*S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W :=
  CubicReflectionKernel.mellin_strip_source_bound a b ha l r n

end SevenEighths.HeckeDyadic

end

end OAI
end OAIOriginalModule2010

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationColumn
Source SHA256: 06c2bae203bb819f97d15138f6636da46e73236bbed44cc48461037a5388372c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2011



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_reciprocal_identity (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    {s : ℂ} (hs : 1<s.re) :
    series χ true s=(1-idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-s))*series ψ true s := by
  have hL : LFunction ψ s=LFunction χ s*(1-idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-s)) := by
    rw [LFunction_eq_series ψ hs,LFunction_eq_series χ hs,hm,
      IdealEuler.series_deletePrimes {P} (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs]
    simp only [Finset.prod_singleton]
    change IdealEuler.series (idealCoeff χ) s *
      (1-idealCoeff χ P.val*CubicEisenstein.fullIdealWeight s P.val)=_
    rw [CubicEisenstein.fullIdealWeight,ite_eq_right P.property.ne_zero]
  have h0 : s≠0 := by intro h; norm_num [h] at hs
  have h1 : s≠1 := by intro h; norm_num [h] at hs
  simp only [series,ite_true,HeckeReciprocal.reciprocal_eq_inv χ h0 h1,
    HeckeReciprocal.reciprocal_eq_inv ψ h0 h1]
  have hχ := LFunction_ne_zero_of_one_lt_re χ hs
  have hψ := LFunction_ne_zero_of_one_lt_re ψ hs
  apply (mul_right_cancel₀ hψ)
  rw [mul_assoc,inv_mul_cancel₀ hψ,mul_one,hL]
  rw [←mul_assoc,inv_mul_cancel₀ hχ,one_mul]

lemma rescaled_power (D N : ℝ) (hD : 0<D) (hN : 0<N) (w : ℂ) :
    (D : ℂ)^(w-(1/2 : ℂ))*(N : ℂ)^(-w)=
      (N : ℂ)^(-(1/2 : ℂ))*((D/N : ℝ) : ℂ)^(w-(1/2 : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hD hN).ne')]
  rw [←Complex.ofReal_log hD.le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log (div_pos hD hN).le,Real.log_div hD.ne' hN.ne']
  rw [←Complex.exp_add,←Complex.exp_add]
  congr 1
  push_cast
  ring

theorem prime_column_identity (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0<D) :
    polynomial χ true W D σ freq=polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*
        polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq := by
  let N : ℝ := P.val.absNorm
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc : 1<(2-σ)+σ := by linarith
  have he (t : ℝ) : integrand χ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I)=
      integrand ψ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I)-
      (idealCoeff χ P.val*(N : ℂ)^(-(1/2 : ℂ)))*
        integrand ψ true W (D/N) σ freq (((2-σ : ℝ) : ℂ)+t*I) := by
    let w : ℂ := (((2-σ : ℝ) : ℂ)+t*I)+shift σ freq
    have hw : 1<w.re := by dsimp [w]; simp
    have hr := prime_reciprocal_identity χ ψ P hm hw
    have hp := rescaled_power D N hD hN w
    unfold integrand
    change mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*series χ true w=_
    rw [hr]
    change mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*
      ((1-idealCoeff χ P.val*(N : ℂ)^(-w))*series ψ true w)=_
    calc
      _ = mellin W _*(D : ℂ)^(w-(1/2 : ℂ))*series ψ true w-
          idealCoeff χ P.val*mellin W _*((D : ℂ)^(w-(1/2 : ℂ))*(N : ℂ)^(-w))*series ψ true w := by ring
      _ = _ := by rw [hp]; ring
  have hI := integrand_vertical_integrable ψ true W a b ha hWs hW D (2-σ) σ freq hD hc
  have hJ := integrand_vertical_integrable ψ true W a b ha hWs hW (D/N) (2-σ) σ freq (div_pos hD hN) hc
  rw [polynomial_mellin χ true W a b ha hWs hW D (2-σ) σ freq hD hc,
    polynomial_mellin ψ true W a b ha hWs hW D (2-σ) σ freq hD hc,
    polynomial_mellin ψ true W a b ha hWs hW (D/(P.val.absNorm : ℝ)) (2-σ) σ freq (div_pos hD hN) hc]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I))=_
  simp_rw [he]
  rw [integral_sub hI (hJ.const_mul _),integral_const_mul]
  change _=(1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand ψ true W D σ freq (((2-σ : ℝ) : ℂ)+t*I))-
    idealCoeff χ P.val*(N : ℂ)^(-(1/2 : ℂ))*
      ((1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand ψ true W (D/N) σ freq (((2-σ : ℝ) : ℂ)+t*I)))
  ring

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2011

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationMask
Source SHA256: 54f61f71149f0d32b6fd9ad5a285197b2a329494d5460e3e4c8c18b638dc4d47
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2012


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CanonicalQuadraticSieve hiding O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem row_coeff_zero_unsupported (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) (J : Ideal O) (hJ : ¬Supported J) :
    idealCoeff χ J=0 := by
  by_cases hz : J=0
  · subst J
    exact map_zero _
  let n := ConcretePrimeRowBridge.idealGenerator J
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero J hz
  have hs : Ideal.span {n}=J := ConcretePrimeRowBridge.span_idealGenerator J
  rw [←hs,idealCoeff_span χ hn,heq]
  exact rowTwist_zero_of_not_supported (elementHom η) m f z n hmLam hm2 (hs ▸ hJ)

theorem prime_coprime_iff (P : SmoothMobiusCorrection.PrimeIdeal) (J : Ideal O) :
    IsCoprime J P.val ↔ ¬P.val∣J := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  rw [isCoprime_comm,Ideal.isCoprime_iff_codisjoint,
    ←(Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint,
    ←Ideal.dvd_iff_le]

theorem amplified_row_prime_mask (η χ ψ : Character) (m f z a : O)
    (P : SmoothMobiusCorrection.PrimeIdeal) (hspan : Ideal.span {a}=P.val)
    (hχ : ∀ n : O, elementCoeff χ n=rowTwist (elementHom η) m f z n)
    (hψ : ∀ n : O, elementCoeff ψ n=rowTwist (elementHom η) m f (z*a^6) n)
    (hmLam : λ₀∣m) (hm2 : (2 : O)∣m) :
    idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ) := by
  ext J
  rw [IdealEuler.deletePrimes_apply]
  simp only [Finset.mem_singleton,forall_eq]
  by_cases hs : Supported J
  · rw [idealCoeff_eq_row η ψ m f (z*a^6) hψ,
      show m^6*f^4*(z*a^6)=(m^6*f^4*z)*a^6 by ring,
      idealRowHom_argument_mul,idealRowHom_sixth_mask a J hs,hspan,prime_coprime_iff]
    by_cases hd : P.val∣J
    · simp [hd]
    · simp only [hd,not_false_eq_true,ite_true,mul_one]
      exact (idealCoeff_eq_row η χ m f z hχ J).symm
  · rw [row_coeff_zero_unsupported η ψ m f (z*a^6) hψ hmLam hm2 J hs,
      row_coeff_zero_unsupported η χ m f z hχ hmLam hm2 J hs]
    simp

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2012

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEnergy
Source SHA256: 34813bee6e142bd8452de0e19980e2aa7176e21d564919e28893b500b0d55c73
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2013


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem prime_column_energy (χ ψ : Character) (P : SmoothMobiusCorrection.PrimeIdeal)
    (hm : idealCoeff ψ=IdealEuler.deletePrimes {P} (idealCoeff χ))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b)
    (hW : ContDiff ℝ ∞ W) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ true W D σ freq‖^2≤
      2*(‖polynomial ψ true W D σ freq‖^2+
        ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖^2) := by
  have hN : (1 : ℝ)≤P.val.absNorm := by
    exact_mod_cast (show 1≤P.val.absNorm from (SmoothMobiusCorrection.prime_norm_two_le P).trans' (by norm_num))
  have hNp : (0 : ℝ)<P.val.absNorm := by linarith
  have hc : ‖idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
    rw [norm_mul]
    have hh : ‖(P.val.absNorm : ℂ)^(-(1/2 : ℂ))‖≤1 := by
      change ‖((P.val.absNorm : ℝ) : ℂ)^(-(1/2 : ℂ))‖≤1
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNp]
      norm_num
      exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (idealCoeff_norm_le_one χ P.val)).trans hh
  rw [prime_column_identity χ ψ P hm W a b ha hWs hW D σ freq hD]
  have hn := norm_sub_le (polynomial ψ true W D σ freq)
    (idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)
  rw [norm_mul] at hn
  have hb := mul_le_of_le_one_left
    (norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq)) hc
  nlinarith [norm_nonneg (polynomial ψ true W D σ freq),
    norm_nonneg (polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    norm_nonneg (polynomial ψ true W D σ freq-
      idealCoeff χ P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq),
    sq_nonneg (‖polynomial ψ true W D σ freq‖-
      ‖polynomial ψ true W (D/(P.val.absNorm : ℝ)) σ freq‖)]

theorem finite_amplification (rows : Finset FreeRow) (multipliers : Finset NonzeroIdeal)
    (target : Finset O) (F : FreeRow→ℝ) (E : O→ℝ) (K : ℝ)
    (hK : 0≤K) (hE : ∀ u, 0≤E u)
    (hmap : ∀ u∈rows, ∀ A∈multipliers, rowMap (u,A)∈target)
    (hamp : ∀ u∈rows, ∀ A∈multipliers, F u≤K*E (rowMap (u,A))) :
    (multipliers.card : ℝ)*(∑ u∈rows, F u)≤K*∑ v∈target, E v := by
  have hs : (multipliers.card : ℝ)*(∑ u∈rows, F u)=
      ∑ p∈rows×ˢmultipliers, F p.1 := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const,nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hs]
  calc
    _ ≤ ∑ p∈rows×ˢmultipliers, K*E (rowMap p) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hu,hA⟩ := Finset.mem_product.mp hp
      exact hamp p.1 hu p.2 hA
    _ = K*∑ v∈(rows×ˢmultipliers).image rowMap, E v := by
      rw [Finset.mul_sum,Finset.sum_image]
      exact fun p hp q hq h => rowMap_injective h
    _ ≤ K*∑ v∈target, E v := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro v hv
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨hu,hA⟩ := Finset.mem_product.mp hp
        exact hmap p.1 hu p.2 hA
      · intro v hv hn
        exact hE v

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2013

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
Source SHA256: 9d1af7a50e0dcdda149b234c790aea46581a971ebb54f46881086ee986a097f4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2014


namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeRowClosure
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
abbrev NonzeroElement := UnrestrictedIdealReindex.NonzeroElement

structure RowData where
  η : Character
  m : O
  f : O
  m_ne_zero : m≠0
  f_ne_zero : f≠0
  lambda_dvd : λ₀∣m
  two_dvd : (2 : O)∣m

def RowData.character (data : RowData) (u : NonzeroElement) : Character :=
  Classical.choose (exists_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd)

theorem RowData.character_spec (data : RowData) (u : NonzeroElement) (n : O) :
    elementCoeff (data.character u) n=
      CanonicalRowCompletion.rowTwist (elementHom data.η) data.m data.f u.val n :=
  Classical.choose_spec (exists_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd) n

def amplifiedElement (u : NonzeroElement) (A : NonzeroIdeal) : NonzeroElement :=
  ⟨u.val*(ConcretePrimeRowBridge.idealGenerator A.val)^6,
    mul_ne_zero u.property (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero A.val A.property))⟩

theorem RowData.amplified_prime_mask (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) :
    idealCoeff (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))=
      IdealEuler.deletePrimes {P} (idealCoeff (data.character u)) := by
  exact amplified_row_prime_mask data.η (data.character u)
    (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) data.m data.f u.val
    (ConcretePrimeRowBridge.idealGenerator P.val) P
    (ConcretePrimeRowBridge.span_idealGenerator P.val)
    (data.character_spec u) (data.character_spec (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))
    data.lambda_dvd data.two_dvd

theorem RowData.prime_column (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    polynomial (data.character u) true W D σ freq=
      polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq-
      idealCoeff (data.character u) P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*
        polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq :=
  prime_column_identity _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD

theorem RowData.prime_energy (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial (data.character u) true W D σ freq‖^2≤
      2*(‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq‖^2+
        ‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq‖^2) :=
  prime_column_energy _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD

end SevenEighths.HeckeInverseAmplification

end

end OAI
end OAIOriginalModule2014

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Presentation
Source SHA256: 6d3ab5d6b1fe51409d259d966a4031d0257ba0c488e535660efcd08af6b15b47
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2015



namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckePresentation
open HeckeFamily

def generator (η : Character) : O := ConcretePrimeRowBridge.idealGenerator η.modulus

instance (η : Character) : NeZero (generator η) :=
  ⟨ConcretePrimeRowBridge.idealGenerator_ne_zero η.modulus η.modulus_ne_bot⟩

theorem span_generator (η : Character) : Ideal.span {generator η} = η.modulus :=
  ConcretePrimeRowBridge.span_idealGenerator η.modulus

def quotientEquiv (η : Character) : (O ⧸ Ideal.span {generator η}) ≃+* (O ⧸ η.modulus) :=
  Ideal.quotEquivOfEq (span_generator η)

def principalResidue (η : Character) : MulChar (O ⧸ Ideal.span {generator η}) ℂ :=
  CharacterTransport.pullback (quotientEquiv η) η.residue

@[simp] theorem principalResidue_mk (η : Character) (z : O) :
    principalResidue η (Ideal.Quotient.mk (Ideal.span {generator η}) z) =
      elementCoeff η z := by
  simp only [principalResidue, CharacterTransport.pullback_apply, quotientEquiv,
    Ideal.quotEquivOfEq_mk, elementCoeff]

theorem principalResidue_unit (η : Character) (u : Oˣ) :
    principalResidue η (Ideal.Quotient.mk (Ideal.span {generator η}) (u : O)) = 1 := by
  rw [principalResidue_mk]
  exact η.unit_trivial u

def principalCharacter (η : Character) : Character :=
  HeckePrimitive.character (generator η) (principalResidue η) (principalResidue_unit η)

@[simp] theorem principalCharacter_elementCoeff (η : Character) (z : O) :
    elementCoeff (principalCharacter η) z = elementCoeff η z := principalResidue_mk η z

theorem principalResidue_primitive (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) :
    FiniteFourier.IsPrimitiveOnIdeals (principalResidue η) :=
  CharacterTransport.primitive_pullback (quotientEquiv η) η.residue hp

private theorem pullback_one {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    CharacterTransport.pullback e (1 : MulChar S ℂ) = 1 := by
  apply MulChar.ext'
  intro x
  rw [CharacterTransport.pullback_apply]
  by_cases hx : IsUnit x
  · have hxe : IsUnit (e x) := hx.map e.toMonoidHom
    rw [MulChar.one_apply hxe, MulChar.one_apply hx]
  · have he : ¬ IsUnit (e x) := by
      intro h
      apply hx
      simpa using h.map e.symm.toMonoidHom
    rw [MulChar.map_nonunit _ he, MulChar.map_nonunit _ hx]

theorem principalResidue_ne_one (η : Character) (hη : η.residue ≠ 1) :
    principalResidue η ≠ 1 := by
  intro h
  have he := congrArg (CharacterTransport.pullback (quotientEquiv η).symm) h
  rw [principalResidue, CharacterTransport.pullback_symm, pullback_one] at he
  exact hη he

theorem LFunction_principalCharacter (η : Character) (hη : η.residue ≠ 1) (s : ℂ) :
    LFunction (principalCharacter η) s = LFunction η s := by
  have hp : (principalCharacter η).residue ≠ 1 := principalResidue_ne_one η hη
  have ha := LFunction_entire_nonprincipal (principalCharacter η) hp
  have hb := LFunction_entire_nonprincipal η hη
  have he : LFunction (principalCharacter η) = LFunction η := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr ha).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hb) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    unfold LFunction
    congr 1
    apply continuedLattice_eq_of_elementCoeff_eq _ _ (principalCharacter_elementCoeff η)
      (by linarith) (by intro h; norm_num [h] at hz)
  exact congr_fun he s

theorem uniform_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (hη : η.residue ≠ 1)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖LFunction η z‖ ≤
      36 * ((1 + HeckeStrip.leftConstant) * HeckeReciprocalBound.bound (11/10)) *
        (η.modulus.absNorm : ℝ) ^ (3/5 : ℝ) * (3 + |z.im|)^2 := by
  have h := HeckeStripActual.uniform_strip_bound (generator η) (principalResidue η)
    (principalResidue_unit η) (principalResidue_primitive η hp) (principalResidue_ne_one η hη) z hz
  change ‖LFunction (principalCharacter η) z‖ ≤ _ at h
  rw [LFunction_principalCharacter η hη z] at h
  simpa only [HeckeStripActual.conductor, span_generator] using h

end SevenEighths.HeckePresentation

end

end OAI
end OAIOriginalModule2015

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeDyadic
Source SHA256: 4504481a089a7ea7650ce98cc15a574a4f354cf11aa5199b2611b595b84581b5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2016



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def coefficient (χ : Character) (I : Ideal O) : ℂ :=
  (IdealMangoldt.value I : ℂ) * idealCoeff χ I

@[simp] theorem coefficient_zero (χ : Character) : coefficient χ 0 = 0 := by
  unfold coefficient
  rw [IdealMangoldt.value_zero, Complex.ofReal_zero, zero_mul]

def series (χ : Character) (s : ℂ) : ℂ := -deriv (LFunction χ) s / LFunction χ s

theorem series_eq_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    series χ s = ∑' I : NonzeroIdeal, coefficient χ I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, (IdealMangoldt.value I.val : ℂ) *
      IdealEuler.weighted (idealCoeff χ) s I.val) =
      ∑' I : Ideal O, (IdealMangoldt.value I : ℂ) * IdealEuler.weighted (idealCoeff χ) s I := by
    apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => (IdealMangoldt.value I : ℂ) * IdealEuler.weighted (idealCoeff χ) s I)
    intro I hI hi
    subst I
    exact hI (by
      change (IdealMangoldt.value 0 : ℂ) * IdealEuler.weighted (idealCoeff χ) s 0 = 0
      rw [IdealMangoldt.value_zero, Complex.ofReal_zero, zero_mul])
  change -deriv (LFunction χ) s / LFunction χ s = _
  rw [← HeckeLogDerivative.coeff_LSeries_eq χ hs]
  change LSeries (IdealLogDerivative.coeff (idealCoeff χ)) s = _
  rw [← IdealLogDerivative.mangoldt_series_eq_LSeries _ (idealCoeff_norm_le_one χ) s hs, ← he]
  apply tsum_congr
  intro I
  simp only [coefficient, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight]
  rw [ite_eq_right_iff.mpr (fun h => (I.property h).elim)]
  simp only [HeckeDyadic.norm, Complex.ofReal_natCast, mul_assoc]

def twistedCoefficient (χ : Character) (σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ I.val * (norm I : ℂ)^(-shift σ freq)

theorem twisted_coefficient_summable (χ : Character) (c σ freq : ℝ)
    (hc : 1 < c+σ) :
    Summable (fun I : NonzeroIdeal => ‖twistedCoefficient χ σ freq I‖*(norm I)^(-c)) := by
  have hf := (IdealLogDerivative.mangoldt_weighted_summable_norm
    (idealCoeff χ) (idealCoeff_norm_le_one χ) ((c+σ : ℝ) : ℂ)
    (by simpa using hc)).comp_injective (Subtype.val_injective : Function.Injective
      (fun I : NonzeroIdeal => I.val))
  convert hf using 1
  ext I
  simp only [Function.comp_apply, twistedCoefficient, coefficient, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight,
    ite_eq_right_iff.mpr (fun h => (I.property h).elim), norm_mul]
  change (‖(IdealMangoldt.value I.val : ℂ)‖ * ‖idealCoeff χ I.val‖ *
      ‖(norm I : ℂ)^(-shift σ freq)‖) * (norm I)^(-c) =
    ‖(IdealMangoldt.value I.val : ℂ)‖ * (‖idealCoeff χ I.val‖ *
      ‖(norm I : ℂ)^(-((c+σ : ℝ) : ℂ))‖)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I),
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp only [Complex.neg_re, shift_re, Complex.ofReal_re]
  rw [mul_assoc, mul_assoc, ← Real.rpow_add (norm_pos I)]
  congr 3
  ring

def summand (χ : Character) (W : ℝ → ℂ) (D σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ I.val * W (norm I/D) * ((norm I/D : ℝ) : ℂ)^(-shift σ freq)

def polynomial (χ : Character) (W : ℝ → ℂ) (D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) * ∑' I : NonzeroIdeal, summand χ W D σ freq I

theorem twisted_series_eq (χ : Character) (σ freq : ℝ)
    {s : ℂ} (hs : 1 < (s+shift σ freq).re) :
    (∑' I : NonzeroIdeal, twistedCoefficient χ σ freq I*(norm I : ℂ)^(-s)) =
      series χ (s+shift σ freq) := by
  rw [series_eq_tsum χ hs]
  apply tsum_congr
  intro I
  unfold twistedCoefficient
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_pos I).ne')]
  congr 2
  ring

theorem polynomial_eq_weighted (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0 < D) :
    polynomial χ W D σ freq =
      (D : ℂ)^(shift σ freq-(1/2 : ℂ)) *
        ∑' I : NonzeroIdeal, twistedCoefficient χ σ freq I * W (norm I/D) := by
  have he (I : NonzeroIdeal) : summand χ W D σ freq I =
      (D : ℂ)^(shift σ freq) * (twistedCoefficient χ σ freq I * W (norm I/D)) := by
    unfold summand twistedCoefficient
    rw [CompletedGauss.positive_quotient_cpow_neg _ _ (norm_pos I) hD]
    ring
  unfold polynomial
  simp_rw [he]
  rw [tsum_mul_left, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 2
  ring

theorem polynomial_mellin (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hWs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (D c σ freq : ℝ) (hD : 0 < D) (hc : 1 < c+σ) :
    polynomial χ W D σ freq = (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
      mellin W ((c : ℂ)+t*Complex.I) *
        (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) *
          series χ (((c : ℂ)+t*Complex.I)+shift σ freq) := by
  rw [polynomial_eq_weighted χ W D σ freq hD]
  rw [CompletedGauss.weightedMellin_inversion norm norm_pos
    (twistedCoefficient χ σ freq) c (twisted_coefficient_summable χ c σ freq hc)
    W a b ha hWs hW D hD]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [twisted_series_eq χ σ freq (by simpa using hc)]
  have he : (D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I) =
      (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
    congr 1
    ring
  calc
    _ = mellin W ((c : ℂ)+t*Complex.I) *
        ((D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I)) *
          series χ (((c : ℂ)+t*Complex.I)+shift σ freq) := by ring
    _ = _ := by rw [he]

end SevenEighths.HeckePrimeDyadic

end

end OAI
end OAIOriginalModule2016

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicEuler
Source SHA256: 79ff926aaf930411e7e52b259fb004a2f4ac7736b3d8aabb417f6a9d3f4e96f1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2017


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def eulerBound (b : ℝ) : ℝ :=
  ∑' I : NonzeroIdeal, IdealMangoldt.value I.val * (norm I)^(-b)

theorem eulerBound_summable {b : ℝ} (hb : 1<b) :
    Summable (fun I : NonzeroIdeal => IdealMangoldt.value I.val * (norm I)^(-b)) := by
  have ha (I : Ideal O) : ‖IdealEuler.normWeight 0 I‖ ≤ 1 := by
    change ‖CubicEisenstein.fullIdealWeight 0 I‖ ≤ 1
    by_cases hI : I = 0
    · rw [CubicEisenstein.fullIdealWeight, ite_eq_left_iff.mpr (fun h => (h hI).elim), norm_zero]
      norm_num
    · rw [CubicEisenstein.fullIdealWeight, ite_eq_right_iff.mpr (fun h => (hI h).elim)]
      simp
  have hf := (IdealLogDerivative.mangoldt_weighted_summable_norm
    (IdealEuler.normWeight 0) ha (b : ℂ) (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NonzeroIdeal => I.val))
  convert hf using 1
  ext I
  simp only [Function.comp_apply, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight,
    ite_eq_right_iff.mpr (fun h => (I.property h).elim), neg_zero, Complex.cpow_zero, one_mul]
  change IdealMangoldt.value I.val * (norm I)^(-b) =
    ‖(IdealMangoldt.value I.val : ℂ) * (norm I : ℂ)^(-(b : ℂ))‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (IdealMangoldt.value_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp

theorem series_norm_le (χ : Character) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤s.re) : ‖series χ s‖ ≤ eulerBound b := by
  rw [series_eq_tsum χ (hb.trans_le hs)]
  have hbound (I : NonzeroIdeal) :
      ‖coefficient χ I.val * (norm I : ℂ)^(-s)‖ ≤
        IdealMangoldt.value I.val * (norm I)^(-b) := by
    rw [norm_mul]
    have hn : 1 ≤ norm I := by
      unfold HeckeDyadic.norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hc : ‖coefficient χ I.val‖ ≤ IdealMangoldt.value I.val := by
      rw [coefficient, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (IdealMangoldt.value_nonneg _)]
      exact mul_le_of_le_one_right (IdealMangoldt.value_nonneg _) (idealCoeff_norm_le_one χ _)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re]
    exact mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hs))
      (Real.rpow_nonneg (norm_pos I).le _) (IdealMangoldt.value_nonneg _)

  have hf := (eulerBound_summable hb).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact (norm_tsum_le_tsum_norm hf).trans (hf.tsum_le_tsum hbound (eulerBound_summable hb))

end SevenEighths.HeckePrimeDyadic

end

end OAI
end OAIOriginalModule2017

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeDyadicContour
Source SHA256: 432a545c71db0c300ae45bde06cbaf4ec9399d8fc5c577c3779727ddf5938be9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2018


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def integrand (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+HeckeDyadic.shift σ freq-(1/2 : ℂ)) *
    series χ (s+HeckeDyadic.shift σ freq)

theorem series_differentiableAt_nonprincipal (χ : Character) (hχ : χ.residue≠1)
    {s : ℂ} (hz : LFunction χ s≠0) : DifferentiableAt ℂ (series χ) s := by
  have h := (LFunction_entire_nonprincipal χ hχ).analyticAt s
  exact (h.deriv.neg.div h hz).differentiableAt

theorem series_differentiableAt_right (χ : Character) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ) s := by
  have ha : AnalyticAt ℂ (LFunction χ) s := by
    apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt 1)).2 ?_ s hs
    intro z hz
    exact (LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hz) (Or.inl (by intro h; norm_num [h] at hz))).differentiableWithinAt
  exact (ha.deriv.neg.div ha (LFunction_ne_zero_of_one_lt_re χ hs)).differentiableAt

theorem integrand_differentiableAt (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (series χ) (s+HeckeDyadic.shift σ freq)) :
    DifferentiableAt ℂ (integrand χ W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (HeckeDyadic.shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (HeckeDyadic.shift σ freq))

theorem integrand_norm (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ (s+HeckeDyadic.shift σ freq)‖ := by
  unfold integrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem integrand_vertical_integrable (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (hc : 1<c+σ) :
    Integrable (fun t : ℝ => integrand χ W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => integrand χ W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (integrand_differentiableAt χ W a b ha hWs hW D σ freq hD
      (series_differentiableAt_right χ (by simpa using hc))).continuousAt.comp
    fun_prop
  have hm := (CompletedGauss.compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*eulerBound (c+σ))).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [integrand_norm χ W D σ freq hD]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, zero_mul,
    sub_self, add_zero]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (series_norm_le χ hc (by simp))
  positivity

theorem finite_rectangle (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+HeckeDyadic.shift σ freq)≠0) :
    (∫ t : ℝ in -T..T, integrand χ W D σ freq ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I))) := by
  have hhol : DifferentiableOn ℂ (integrand χ W D σ freq)
      (uIcc l r ×ℂ uIcc (-T) T) := by
    intro s hs
    exact (integrand_differentiableAt χ W a b ha hWs hW D σ freq hD
      (series_differentiableAt_nonprincipal χ hχ (hz s hs))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand χ W D σ freq) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, integrand χ W D σ freq ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem polynomial_finite_shift (χ : Character) (hχ : χ.residue≠1)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1<r+σ) (hT : 0≤T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), LFunction χ (s+HeckeDyadic.shift σ freq)≠0) :
    polynomial χ W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, integrand χ W D σ freq ((r : ℂ)+t*I)) = _
  rw [← integral_add_compl measurableSet_Icc
    (integrand_vertical_integrable χ W a b ha hWs hW D r σ freq hD hr)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -T≤T)]
  rw [finite_rectangle χ hχ W a b ha hWs hW D σ freq l r T hD hz]

end SevenEighths.HeckePrimeDyadic

end

end OAI
end OAIOriginalModule2018

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimePowers
Source SHA256: 70c14f0e2aeb4f582ecd897b62b7f3cc39ef7d33fd8492d821c390fbf5a4248a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2019



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckePrimePowers
open HeckeFamily UniqueFactorizationMonoid

theorem nonprime_primePow_powerful {I : Ideal O} (hpow : IsPrimePow I) (hprime : ¬Prime I) :
    CompletedGauss.PowerfulIdeal I := by
  obtain ⟨P,k,hP,hk,rfl⟩ := hpow
  have hk2 : 2≤k := by
    by_contra h
    have hk1 : k=1 := by omega
    subst k
    exact hprime (by simpa using hP)
  refine ⟨pow_ne_zero _ hP.ne_zero,?_⟩
  intro Q hQ
  rw [hP.irreducible.normalizedFactors_pow] at hQ ⊢
  have hQP := (Multiset.mem_replicate.mp hQ).2
  subst Q
  simpa using hk2

def logWeight (I : Ideal O) : ℝ := IdealMangoldt.value I / Real.log (Ideal.absNorm I)

theorem logWeight_nonneg (I : Ideal O) : 0≤logWeight I :=
  div_nonneg (IdealMangoldt.value_nonneg _) (Real.log_natCast_nonneg _)

theorem logWeight_le_one (I : Ideal O) : logWeight I≤1 := by
  by_cases hlog : Real.log (Ideal.absNorm I)=0
  · simp [logWeight,hlog]
  · apply (div_le_one (lt_of_le_of_ne (Real.log_natCast_nonneg _) (Ne.symm hlog))).mpr
    exact IdealLogDerivative.value_le_log_norm I

theorem logWeight_prime {P : Ideal O} (hP : Prime P) : logWeight P=1 := by
  have hp2 : (2 : ℝ)≤P.absNorm := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
  have hp : 0<Real.log (P.absNorm : ℝ) := Real.log_pos (by linarith)
  rw [logWeight, PNT.IdealPrimeMass.value_prime hP, div_self hp.ne']

theorem logWeight_eq_zero {I : Ideal O} (hI : ¬IsPrimePow I) : logWeight I=0 := by
  simp only [logWeight, IdealMangoldt.value, ite_eq_right hI, zero_div]

theorem sum_prime_extraction (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ) :
    (∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
      (∑ I∈S.filter Prime, idealCoeff χ I*f I) =
      ∑ I∈S.filter (fun I => IsPrimePow I ∧ ¬Prime I),
        (logWeight I : ℂ)*idealCoeff χ I*f I := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hP : Prime I
  · simp only [hP, ite_true, not_true_eq_false, and_false, ite_false,
      logWeight_prime hP, Complex.ofReal_one, one_mul, sub_self]
  · by_cases hp : IsPrimePow I
    · simp [hP,hp]
    · simp [hP,hp,logWeight_eq_zero hp]

theorem prime_extraction_error (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character) (S : Finset (Ideal O)) (f : Ideal O→ℂ)
      (X B : ℝ), 1≤X → 0≤B →
      (∀ I∈S, (I.absNorm : ℝ)≤X) → (∀ I∈S, ‖f I‖≤B) →
      ‖(∑ I∈S, (logWeight I : ℂ)*idealCoeff χ I*f I) -
        (∑ I∈S.filter Prime, idealCoeff χ I*f I)‖ ≤ C*X^(1/2+ε)*B := by
  obtain ⟨C,hC,hcount⟩ := CompletedGauss.powerful_ideal_count ε hε
  refine ⟨C,hC,?_⟩
  intro χ S f X B hX hB hnorm hf
  rw [sum_prime_extraction]
  let A := S.filter (fun I => IsPrimePow I ∧ ¬Prime I)
  have hA : (A.card : ℝ)≤C*X^(1/2+ε) := by
    apply hcount A X hX
    intro I hI
    obtain ⟨hIS,hpow,hprime⟩ := Finset.mem_filter.mp hI
    exact ⟨nonprime_primePow_powerful hpow hprime,hnorm I hIS⟩
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _I∈A, B := by
      apply Finset.sum_le_sum
      intro I hI
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (logWeight_nonneg _)]
      have hcoeff : logWeight I*‖idealCoeff χ I‖≤1 :=
        (mul_le_of_le_one_right (logWeight_nonneg I) (idealCoeff_norm_le_one χ I)).trans
          (logWeight_le_one I)
      exact (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)).trans
        (by simpa using hf I (Finset.mem_filter.mp hI).1)
    _ = (A.card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hA hB

end SevenEighths.HeckePrimePowers

end

end OAI
end OAIOriginalModule2019

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrimeAnnular
Source SHA256: 3687ff362cecec75d4be082abc2fc2d2a2adf6494d04a332b8def77bc7b26709
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2020



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Set
namespace SevenEighths.HeckePrimeAnnular
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def annulusSet (b D : ℝ) : Finset (Ideal O) := idealsUpTo ⌊max 1 b*D⌋₊

def annularWeight (W : ℝ→ℂ) (D σ freq : ℝ) (I : Ideal O) : ℂ :=
  W ((I.absNorm : ℝ)/D)*(((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift σ freq)

def primePolynomial (χ : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ I∈(annulusSet b D).filter Prime,
    idealCoeff χ I*annularWeight W D σ freq I

theorem annular_support (W : ℝ→ℂ) (a b D : ℝ) (ha : 0<a) (hD : 0<D)
    (hWs : Function.support W⊆Icc a b) (I : Ideal O)
    (hw : W ((I.absNorm : ℝ)/D)≠0) : I∈annulusSet b D := by
  have hs := hWs hw
  apply mem_idealsUpTo.mpr
  constructor
  · have hnorm : 0<(I.absNorm : ℝ) := by
      have := (le_div_iff₀ hD).mp hs.1
      nlinarith
    exact_mod_cast hnorm
  · have hn := (div_le_iff₀ hD).mp hs.2
    exact Nat.le_floor (hn.trans (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le))

theorem log_polynomial_eq_finite (χ : Character) (W : ℝ→ℂ) (a b D σ freq : ℝ)
    (ha : 0<a) (hD : 0<D) (hWs : Function.support W⊆Icc a b)
    (hlarge : 2*(|Real.log a|+|Real.log b|)+1≤Real.log D) :
    HeckePrimeDyadic.polynomial χ (PrimeLogProfile.profile W (1/Real.log D)) D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑ I∈annulusSet b D,
        (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I := by
  rw [PrimeLogProfile.profile_eq_log_division W a b D ha hWs hD hlarge]
  unfold HeckePrimeDyadic.polynomial
  congr 1
  have he : (fun I : NonzeroIdeal => HeckePrimeDyadic.summand χ
      (fun y => W y/(Real.log (D*y) : ℂ)) D σ freq I) =
      fun I : NonzeroIdeal => (HeckePrimePowers.logWeight I.val : ℂ)*
        idealCoeff χ I.val*annularWeight W D σ freq I.val := by
    funext I
    unfold HeckePrimeDyadic.summand HeckePrimeDyadic.coefficient annularWeight
    dsimp only [HeckePrimePowers.logWeight, HeckeDyadic.norm]
    rw [mul_div_cancel₀ _ hD.ne']
    simp only [Complex.ofReal_div]
    ring
  rw [he]
  calc
    _ = ∑' I : Ideal O, (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I := by
      apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I≠0})
        (f := fun I : Ideal O => (HeckePrimePowers.logWeight I : ℂ)*idealCoeff χ I*annularWeight W D σ freq I)
      intro I hI hzero
      subst I
      exact hI (by simp [HeckePrimePowers.logWeight])
    _ = _ := by
      apply tsum_eq_sum
      intro I hI
      have hw : W ((I.absNorm : ℝ)/D)=0 := by
        by_contra hh
        exact hI (annular_support W a b D ha hD hWs I hh)
      simp [annularWeight,hw]

theorem fixed_profile_norm_bound (W : ℝ→ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0<a) :
    ∃ B : ℝ, 0<B ∧ ∀ σ∈Icc lo hi, ∀ y∈Icc a b, ‖W y‖*y^(-σ)≤B := by
  let K : Set (ℝ×ℝ) := Icc lo hi ×ˢ Icc a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℝ×ℝ => ‖W p.2‖*p.2^(-p.1)) K := by
    apply (hW.comp continuous_snd).norm.continuousOn.mul
    exact continuous_snd.continuousOn.rpow continuous_fst.neg.continuousOn
      (fun p hp => Or.inl (ne_of_gt (ha.trans_le hp.2.1)))
  obtain ⟨M,hM⟩ := hK.bddAbove_image hc
  refine ⟨|M|+1,by positivity,?_⟩
  intro σ hσ y hy
  exact (hM (Set.mem_image_of_mem _ (show (σ,y)∈K from ⟨hσ,hy⟩))).trans
    (by linarith [le_abs_self M])

theorem extraction_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character) (W : ℝ→ℂ) (a b D σ freq B : ℝ),
      0<a → 1≤D → Function.support W⊆Icc a b →
      2*(|Real.log a|+|Real.log b|)+1≤Real.log D → 0≤B →
      (∀ y∈Icc a b, ‖W y‖*y^(-σ)≤B) →
      ‖HeckePrimeDyadic.polynomial χ (PrimeLogProfile.profile W (1/Real.log D)) D σ freq -
        primePolynomial χ W b D σ freq‖≤
        C*(max 1 b)^((1/2 : ℝ)+ε)*D^ε*B := by
  obtain ⟨C,hC,herr⟩ := HeckePrimePowers.prime_extraction_error ε hε
  refine ⟨C,hC,?_⟩
  intro χ W a b D σ freq B ha hD hWs hlarge hB hWbound
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hX : 1≤max 1 b*D := hD.trans (le_mul_of_one_le_left hDp.le (le_max_left _ _))
  have hnorm (I : Ideal O) (hI : I∈annulusSet b D) : (I.absNorm : ℝ)≤max 1 b*D := by
    exact (Nat.cast_le.mpr (mem_idealsUpTo.mp hI).2).trans
      (Nat.floor_le (by positivity))
  have hw (I : Ideal O) (_hI : I∈annulusSet b D) : ‖annularWeight W D σ freq I‖≤B := by
    by_cases hz : W ((I.absNorm : ℝ)/D)=0
    · simpa [annularWeight,hz] using hB
    · have hs := hWs hz
      have hy : 0<(I.absNorm : ℝ)/D := ha.trans_le hs.1
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hy]
      simpa only [Complex.neg_re,shift_re] using hWbound _ hs
  have hb := herr χ (annulusSet b D) (annularWeight W D σ freq) (max 1 b*D) B
    hX hB hnorm hw
  have hn : ‖(D : ℂ)^(-(1/2 : ℂ))‖=D^(-(1/2 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hDp]
    norm_num
  rw [log_polynomial_eq_finite χ W a b D σ freq ha hDp hWs hlarge,
    primePolynomial,←mul_sub,norm_mul,hn]
  calc
    _ ≤ D^(-(1/2 : ℝ))*(C*(max 1 b*D)^(1/2+ε)*B) := by
      exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hDp.le _)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤max 1 b) hDp.le]
      have he : D^(-(1/2 : ℝ))*D^(1/2+ε)=D^ε := by
        rw [←Real.rpow_add hDp]
        congr 1
        ring
      calc
        _ = C*(max 1 b)^(1/2+ε)*(D^(-(1/2 : ℝ))*D^(1/2+ε))*B := by ring
        _ = _ := by rw [he]

end SevenEighths.HeckePrimeAnnular

end

end OAI
end OAIOriginalModule2020

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.PrincipalStrip
Source SHA256: 4fe8823fa427f804e1b281e9bd7d8f5ab15183431db496f612d5c6a19f82454b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2021



namespace OAI

noncomputable section
open scoped Classical Topology
open Set MeasureTheory
namespace SevenEighths.HeckePrincipalStrip
open HeckeFamily HeckeTheta

def normalized (η : Character) (s : ℂ) : ℂ := HeckeOrigin.poleRemoved η s / (s+2)

theorem normalized_diffContOnCl (η : Character) :
    DiffContOnCl ℂ (normalized η) HeckeStrip.strip := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  exact ((HeckeOrigin.poleRemoved_entire η z).div (differentiableAt_id.add_const 2)
    (HeckeStrip.shift_ne_zero z (HeckeStrip.closure_strip_subset hz))).differentiableWithinAt

theorem norm_sub_one_le_shift (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖z-1‖ ≤ ‖z+2‖ := by
  have h : ‖z+2‖^2 - ‖z-1‖^2 = 6*z.re+3 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  nlinarith [hz.1, norm_nonneg (z-1), norm_nonneg (z+2)]

theorem normalized_norm_le (η : Character) {z : ℂ} (hz : z ∈ HeckeStrip.closedStrip)
    (h0 : z ≠ 0) (h1 : z ≠ 1) : ‖normalized η z‖ ≤ ‖LFunction η z‖ := by
  unfold normalized
  rw [HeckeOrigin.poleRemoved_eq η h0 h1, norm_div, norm_mul]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (HeckeStrip.shift_norm_lower z hz))).mpr
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right (norm_sub_one_le_shift z hz)
    (norm_nonneg (LFunction η z))

private theorem norm_z_le_height (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖z‖ ≤ 3 + |z.im| := by
  apply (Complex.norm_le_abs_re_add_abs_im z).trans
  have hr : |z.re| ≤ 3 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  linarith

private theorem norm_sub_one_le_height (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖z-1‖ ≤ 3 + |z.im| := by
  apply (Complex.norm_le_abs_re_add_abs_im (z-1)).trans
  have hr : |z.re-1| ≤ 3 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  linarith

theorem regularized_completion_bound (η : Character) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ HeckeStrip.closedStrip,
      ‖HeckeMellinIdentity.regularized (pair (coefficients η)) z‖ ≤ C * (3+|z.im|)^2 := by
  let P := pair (coefficients η)
  have hstrong := P.isStrongFEPair_toStrongFEPair
  obtain ⟨C, hC, hbound⟩ := VerticalContourShift.mellin_uniform_strip_bound P.f_modif
    (-(1/10)) (11/10) (hstrong.hasMellin _).1 (hstrong.hasMellin _).1
  let D := C + ‖P.f₀‖ + ‖P.ε‖ * ‖P.g₀‖
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro z hz
  have hΛ : ‖P.Λ₀ z‖ ≤ C := hbound z hz.1 hz.2
  have hT : 1 ≤ 3+|z.im| := by linarith [abs_nonneg z.im]
  have hz0 := norm_z_le_height z hz
  have hz1 := norm_sub_one_le_height z hz
  unfold HeckeMellinIdentity.regularized
  change ‖z*(z-1)*P.Λ₀ z - (z-1)*P.f₀ + z*P.ε*P.g₀‖ ≤ _
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) (le_refl ‖z*P.ε*P.g₀‖)).trans
  simp only [norm_mul]
  calc
    _ ≤ ((3+|z.im|)*(3+|z.im|))*C + (3+|z.im|)*‖P.f₀‖ +
        (3+|z.im|)*‖P.ε‖*‖P.g₀‖ := by gcongr
    _ ≤ D*(3+|z.im|)^2 := by
      dsimp [D]
      have hf := norm_nonneg P.f₀
      have hg := mul_nonneg (norm_nonneg P.ε) (norm_nonneg P.g₀)
      have hsq : 3+|z.im| ≤ (3+|z.im|)^2 := by nlinarith
      nlinarith

theorem normalized_exp_growth (η : Character) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ HeckeStrip.strip,
      ‖normalized η z‖ ≤ A * Real.exp (B * |z.im|) := by
  obtain ⟨C, hC, hCbound⟩ := regularized_completion_bound η
  obtain ⟨G, hG, hGbound⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (9/10) (21/10)
  let S : ℝ := Real.pi ^ (-(1/10) : ℝ) + Real.pi ^ (11/10 : ℝ)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨9*S*G*C, Real.pi+2, by positivity, by positivity, ?_⟩
  intro z hz
  have hzc : z ∈ HeckeStrip.closedStrip := ⟨hz.1.le, hz.2.le⟩
  have hp : ‖(Real.pi : ℂ)^z‖ ≤ S := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact VerticalContourShift.rpow_between_endpoints Real.pi (-(1/10)) (11/10) z.re
      Real.pi_pos hzc.1 hzc.2
  have hg : ‖(Complex.Gamma (z+1))⁻¹‖ ≤ G*Real.exp (Real.pi*|z.im|) := by
    simpa using hGbound (z+1) (by constructor <;> simp only [Complex.add_re, Complex.one_re] <;>
      linarith [hzc.1, hzc.2])
  have ht : (3+|z.im|)^2 ≤ 9*Real.exp (2*|z.im|) := by
    have he := Real.add_one_le_exp |z.im|
    have ht0 := abs_nonneg z.im
    have hle : 3+|z.im| ≤ 3*Real.exp |z.im| := by linarith
    have hs := sq_le_sq₀ (by positivity : 0 ≤ 3+|z.im|) (by positivity : 0 ≤ 3*Real.exp |z.im|)
    have hsq := hs.mpr hle
    rw [mul_pow, ← Real.exp_nat_mul] at hsq
    norm_num at hsq ⊢
    exact hsq
  unfold normalized HeckeOrigin.poleRemoved
  simp only [norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  calc
    _ ≤ ‖(Real.pi : ℂ)^z‖ * ‖(Complex.Gamma (z+1))⁻¹‖ *
        ‖HeckeMellinIdentity.regularized (pair (coefficients η)) z‖ := by
      apply (div_le_self (by positivity) (HeckeStrip.shift_norm_lower z hzc)).trans
      exact div_le_self (by positivity) (by norm_num)
    _ ≤ S * (G*Real.exp (Real.pi*|z.im|)) * (C*(3+|z.im|)^2) := by
      gcongr
      exact hCbound z hzc
    _ ≤ S * (G*Real.exp (Real.pi*|z.im|)) * (C*(9*Real.exp (2*|z.im|))) := by gcongr
    _ = _ := by
      rw [show (Real.pi+2)*|z.im| = Real.pi*|z.im| + 2*|z.im| by ring, Real.exp_add]
      ring

theorem primitive_normalized_bound (c : O) [NeZero c]
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖normalized (HeckePrimitive.character c χ hu) z‖ ≤
      36 * ((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10)) *
        HeckeStripActual.conductor c ^ (3/5 : ℝ) * (3+|z.im|)^2 := by
  let η := HeckePrimitive.character c χ hu
  let D := HeckeReciprocalBound.bound (11/10)
  have hD : 0 ≤ D := tsum_nonneg (fun _ => norm_nonneg _)
  have hc := HeckeStrip.leftConstant_pos
  have hQ := HeckeStripActual.conductor_ge_one c
  apply HeckeStrip.uniform_strip_bound (HeckeStripActual.conductor c)
    ((1+HeckeStrip.leftConstant)*D) hQ (by positivity) (normalized η)
    (normalized_diffContOnCl η) (normalized_exp_growth η) ?_ ?_ z hz
  · intro w hw
    have hwc : w ∈ HeckeStrip.closedStrip := ⟨by rw [hw], by rw [hw]; norm_num⟩
    apply (normalized_norm_le η hwc (by intro h; simp [h] at hw)
      (by intro h; norm_num [h] at hw)).trans
    have hb := HeckeStrip.left_boundary_of_functional_equation
      (HeckeStripActual.conductor c) D (lt_of_lt_of_le zero_lt_one hQ) hD
      (LFunction η) (LFunction (HeckePrimitive.character c χ⁻¹
        (HeckePrimitive.inverse_unit_trivial c χ hu))) (TraceCharacter.normalizedGauss c χ)
      (TraceCharacter.normalizedGauss_norm c χ hp)
      (fun _ hs => HeckeStripActual.functional_equation_left c χ hu hp hs)
      (fun _ hs => HeckeStripActual.LFunction_norm_le _ (by norm_num : (1 : ℝ)<11/10) hs.ge) w hw
    apply hb.trans
    have hbase : HeckeStrip.leftConstant*D ≤ (1+HeckeStrip.leftConstant)*D := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbase (Real.rpow_nonneg (by linarith) _)) (sq_nonneg _)
  · intro w hw
    have hwc : w ∈ HeckeStrip.closedStrip := ⟨by rw [hw]; norm_num, by rw [hw]⟩
    apply (normalized_norm_le η hwc (by intro h; norm_num [h] at hw)
      (by intro h; norm_num [h] at hw)).trans
    apply (HeckeStripActual.LFunction_norm_le η (by norm_num : (1 : ℝ)<11/10) hw.ge).trans
    change D ≤ (1+HeckeStrip.leftConstant)*D
    nlinarith

theorem poleRemoved_principalCharacter (η : Character) (s : ℂ) :
    HeckeOrigin.poleRemoved (HeckePresentation.principalCharacter η) s =
      HeckeOrigin.poleRemoved η s := by
  have he : HeckeOrigin.poleRemoved (HeckePresentation.principalCharacter η) =
      HeckeOrigin.poleRemoved η := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeOrigin.poleRemoved_entire _)).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (HeckeOrigin.poleRemoved_entire _)) (z₀ := (2 : ℂ))
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds
      (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    have h0 : z ≠ 0 := by intro h; norm_num [h] at hz
    have h1 : z ≠ 1 := by intro h; norm_num [h] at hz
    rw [HeckeOrigin.poleRemoved_eq _ h0 h1, HeckeOrigin.poleRemoved_eq _ h0 h1]
    congr 1
    unfold LFunction
    congr 1
    exact continuedLattice_eq_of_elementCoeff_eq _ _
      (HeckePresentation.principalCharacter_elementCoeff η) (by linarith) h1
  exact congr_fun he s

theorem uniform_normalized_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖normalized η z‖ ≤
      36 * ((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10)) *
        (η.modulus.absNorm : ℝ) ^ (3/5 : ℝ) * (3+|z.im|)^2 := by
  have h := primitive_normalized_bound (HeckePresentation.generator η)
    (HeckePresentation.principalResidue η) (HeckePresentation.principalResidue_unit η)
    (HeckePresentation.principalResidue_primitive η hp) z hz
  change ‖normalized (HeckePresentation.principalCharacter η) z‖ ≤ _ at h
  unfold normalized at h ⊢
  rw [poleRemoved_principalCharacter] at h
  simpa only [HeckeStripActual.conductor, HeckePresentation.span_generator] using h

def sourceNormalized (η : Character) (s : ℂ) : ℂ :=
  HeckeOrigin.poleRemoved η s / (s+1)

theorem sourceNormalized_norm_le (η : Character) (z : ℂ)
    (hz : z ∈ HeckeStrip.closedStrip) :
    ‖sourceNormalized η z‖ ≤ 3 * ‖normalized η z‖ := by
  have hlow : (9/10 : ℝ) ≤ ‖z+1‖ := by
    have hre := Complex.re_le_norm (z+1)
    simp only [Complex.add_re, Complex.one_re] at hre
    linarith [hz.1]
  have hn1 : z+1 ≠ 0 := norm_pos_iff.mp (by linarith)
  have hn2 : z+2 ≠ 0 := HeckeStrip.shift_ne_zero z hz
  have hratio : ‖z+2‖ ≤ 3*‖z+1‖ := by
    have ht := norm_add_le (z+1) (1 : ℂ)
    rw [norm_one, show z+1+1=z+2 by ring] at ht
    linarith
  have heq : sourceNormalized η z = normalized η z * ((z+2)/(z+1)) := by
    unfold sourceNormalized normalized
    field_simp
  rw [heq, norm_mul, norm_div]
  have hd : ‖z+2‖ / ‖z+1‖ ≤ 3 := (div_le_iff₀ (norm_pos_iff.mpr hn1)).mpr hratio
  nlinarith [norm_nonneg (normalized η z)]

theorem uniform_source_normalized_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue)
    (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) :
    ‖sourceNormalized η z‖ ≤
      108 * ((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10)) *
        (η.modulus.absNorm : ℝ) ^ (3/5 : ℝ) * (3+|z.im|)^2 := by
  apply (sourceNormalized_norm_le η z hz).trans
  have h := mul_le_mul_of_nonneg_left (uniform_normalized_strip_bound η hp z hz) (by norm_num : (0 : ℝ) ≤ 3)
  convert h using 1 ; ring

end SevenEighths.HeckePrincipalStrip

end

end OAI
end OAIOriginalModule2021

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput
Source SHA256: e210ffe3239034cc9011145ced17576d67ae0c77cd00855add998311a3efcf7d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2022


namespace OAI

noncomputable section
open scoped Classical Topology
open Set
namespace SevenEighths.HeckeLogarithmicInput
open HeckeFamily

def regular (η : Character) (s : ℂ) : ℂ :=
  if η.residue = 1 then HeckePrincipalStrip.sourceNormalized η s else LFunction η s

theorem regular_eq_nonprincipal (η : Character) (hη : η.residue ≠ 1) :
    regular η = LFunction η := by funext s; simp [regular, hη]

theorem regular_differentiableAt (η : Character) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (regular η) s := by
  have hplus : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  by_cases hη : η.residue = 1
  · have he : regular η = HeckePrincipalStrip.sourceNormalized η := by
      funext z; simp [regular, hη]
    rw [he]
    exact (HeckeOrigin.poleRemoved_entire η s).div (differentiableAt_id.add_const 1) hplus
  · rw [regular_eq_nonprincipal η hη]
    exact LFunction_entire_nonprincipal η hη s

theorem regular_ne_zero (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) : regular η s ≠ 0 := by
  have hs0 : 0 < s.re := by linarith [HeckeZeroSupremum.half_le_beta]
  have h0 : s ≠ 0 := by intro h; simp [h] at hs0
  have hplus : s+1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
    linarith
  by_cases hη : η.residue = 1
  · simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized]
    apply div_ne_zero _ hplus
    by_cases h1 : s = 1
    · subst s; exact HeckeOrigin.poleRemoved_one_ne_zero η hη
    · rw [HeckeOrigin.poleRemoved_eq η h0 h1]
      exact mul_ne_zero (sub_ne_zero.mpr h1)
        (HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inl h1))
  · rw [regular_eq_nonprincipal η hη]
    exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inr hη)

theorem regular_inverse_differentiableAt (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) :
    DifferentiableAt ℂ (fun z => (regular η z)⁻¹) s :=
  (regular_differentiableAt η (by linarith [HeckeZeroSupremum.half_le_beta])).inv
    (regular_ne_zero η hs)

theorem principal_regular_factor_bound {s : ℂ} (hs : 0 ≤ s.re) :
    ‖s-1‖ ≤ ‖s+1‖ := by
  have he : ‖s+1‖^2 - ‖s-1‖^2 = 4*s.re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  nlinarith [norm_nonneg (s-1), norm_nonneg (s+1)]

theorem regular_norm_le (η : Character) {σ : ℝ} (hσ : 1 < σ)
    {s : ℂ} (hs : σ ≤ s.re) : ‖regular η s‖ ≤ HeckeReciprocalBound.bound σ := by
  by_cases hη : η.residue = 1
  · have h0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
    have h1 : s ≠ 1 := by intro h; simp [h] at hs; linarith
    have hp : 0 < ‖s+1‖ := by
      have hr := Complex.re_le_norm (s+1)
      simp only [Complex.add_re, Complex.one_re] at hr
      linarith
    simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized,
      HeckeOrigin.poleRemoved_eq η h0 h1, norm_div, norm_mul]
    apply le_trans _ (HeckeStripActual.LFunction_norm_le η hσ hs)
    apply (div_le_iff₀ hp).mpr
    nlinarith [principal_regular_factor_bound (s := s) (by linarith), norm_nonneg (LFunction η s)]
  · rw [regular_eq_nonprincipal η hη]
    exact HeckeStripActual.LFunction_norm_le η hσ hs

theorem regular_inverse_norm_le (η : Character) {s : ℂ} (hs : (3/2 : ℝ) ≤ s.re) :
    ‖(regular η s)⁻¹‖ ≤ 5 * HeckeReciprocalBound.bound (3/2) := by
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hL := HeckeReciprocalBound.reciprocal_norm_le η (by norm_num : (1 : ℝ)<3/2) hs
  rw [HeckeReciprocal.reciprocal_eq_inv η h0 h1] at hL
  have hB : 0 ≤ HeckeReciprocalBound.bound (3/2) := tsum_nonneg (fun _ => norm_nonneg _)
  by_cases hη : η.residue = 1
  · have hlow : (1/2 : ℝ) ≤ ‖s-1‖ := by
      have hr := Complex.re_le_norm (s-1)
      simp only [Complex.sub_re, Complex.one_re] at hr
      linarith
    have hratio : ‖s+1‖ / ‖s-1‖ ≤ 5 := by
      apply (div_le_iff₀ (by linarith : 0 < ‖s-1‖)).mpr
      have hr := norm_add_le (s-1) (2 : ℂ)
      norm_num only [Complex.norm_ofNat] at hr
      rw [show s-1+2=s+1 by ring] at hr
      linarith
    simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized,
      HeckeOrigin.poleRemoved_eq η h0 h1, inv_div, norm_div, norm_mul]
    calc
      _ = (‖s+1‖ / ‖s-1‖) * ‖(LFunction η s)⁻¹‖ := by rw [norm_inv]; ring
      _ ≤ _ := mul_le_mul hratio hL (norm_nonneg _) (by norm_num)
  · rw [regular_eq_nonprincipal η hη]
    linarith

def uniformConstant : ℝ :=
  108*((1+HeckeStrip.leftConstant)*HeckeReciprocalBound.bound (11/10))

theorem uniformConstant_nonneg : 0 ≤ uniformConstant := by
  have hc := HeckeStrip.leftConstant_pos
  have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
  unfold uniformConstant
  positivity

theorem modulus_norm_ge_one (η : Character) : 1 ≤ (η.modulus.absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)

theorem regular_strip_bound (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (z : ℂ)
    (hz : z ∈ HeckeStrip.closedStrip) :
    ‖regular η z‖ ≤ uniformConstant * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|z.im|)^2 := by
  by_cases hη : η.residue = 1
  · simpa only [regular, ite_eq_left hη, uniformConstant] using
      HeckePrincipalStrip.uniform_source_normalized_strip_bound η hp z hz
  · rw [regular_eq_nonprincipal η hη]
    apply (HeckePresentation.uniform_strip_bound η hp hη z hz).trans
    have hc := HeckeStrip.leftConstant_pos
    have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
    unfold uniformConstant
    gcongr ; norm_num

theorem regular_right_growth (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) {z : ℂ}
    (hz : -(1/10 : ℝ) ≤ z.re) :
    ‖regular η z‖ ≤ uniformConstant * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|z.im|)^2 := by
  by_cases hright : z.re ≤ 11/10
  · exact regular_strip_bound η hp z ⟨hz, hright⟩
  · apply (regular_norm_le η (by norm_num : (1 : ℝ)<11/10) (le_of_not_ge hright)).trans
    have hD : 0 ≤ HeckeReciprocalBound.bound (11/10) := tsum_nonneg (fun _ => norm_nonneg _)
    have hc := HeckeStrip.leftConstant_pos
    have hC : HeckeReciprocalBound.bound (11/10) ≤ uniformConstant := by
      unfold uniformConstant; nlinarith
    have hQ : 1 ≤ (η.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
      Real.one_le_rpow (modulus_norm_ge_one η) (by norm_num)
    have hT : 1 ≤ (3+|z.im|)^2 := by nlinarith [abs_nonneg z.im]
    exact hC.trans ((le_mul_of_one_le_right uniformConstant_nonneg hQ).trans
      (le_mul_of_one_le_right (mul_nonneg uniformConstant_nonneg (by linarith : 0 ≤ (η.modulus.absNorm : ℝ)^(3/5 : ℝ))) hT))

theorem regular_ne_zero_on_disk (η : Character) (a e t : ℝ)
    (ha : HeckeZeroSupremum.beta ≤ a) (he : 0 < e) {z : ℂ}
    (hz : z ∈ Metric.ball ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    regular η z ≠ 0 := by
  apply regular_ne_zero η
  have hn : ‖z-((2 : ℂ)+t*Complex.I)‖ < 2-a-2*e := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z-((2 : ℂ)+t*Complex.I))
  have hrl := neg_abs_le (z-((2 : ℂ)+t*Complex.I)).re
  norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re] at hr hrl
  linarith

theorem reciprocal_norm_le_regular_inverse (η : Character) {s : ℂ}
    (hs : HeckeZeroSupremum.beta < s.re) :
    ‖HeckeReciprocal.reciprocal η s‖ ≤ ‖(regular η s)⁻¹‖ := by
  have hs0 : 0 < s.re := by linarith [HeckeZeroSupremum.half_le_beta]
  have h0 : s ≠ 0 := by intro h; simp [h] at hs0
  by_cases hη : η.residue = 1
  · by_cases h1 : s = 1
    · subst s
      rw [HeckeReciprocal.reciprocal_principal_one η hη, norm_zero]
      exact norm_nonneg _
    have hp : s+1 ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at he
      linarith
    have hL := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt η hs (Or.inl h1)
    have he : HeckeReciprocal.reciprocal η s =
        ((s-1)/(s+1))*(regular η s)⁻¹ := by
      rw [HeckeReciprocal.reciprocal_eq_inv η h0 h1]
      simp only [regular, ite_eq_left hη, HeckePrincipalStrip.sourceNormalized,
        HeckeOrigin.poleRemoved_eq η h0 h1]
      field_simp
    rw [he, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hp)).mpr (principal_regular_factor_bound hs0.le)
  · simp only [HeckeReciprocal.reciprocal, regular, ite_eq_right hη, le_refl]

theorem regular_disk_growth (η : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals η.residue) (a e t : ℝ)
    (ha : (1/2 : ℝ) ≤ a) (he : 0 ≤ e) {z : ℂ}
    (hz : z ∈ Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    ‖regular η z‖ ≤ (4*uniformConstant) * (η.modulus.absNorm : ℝ)^(3/5 : ℝ) *
      (3+|t|)^2 := by
  have hn : ‖z-((2 : ℂ)+t*Complex.I)‖ ≤ 2-a-2*e := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hr := Complex.abs_re_le_norm (z-((2 : ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (z-((2 : ℂ)+t*Complex.I))
  norm_num [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.sub_im, Complex.add_im, Complex.mul_im] at hr hi
  have hzre : -(1/10 : ℝ) ≤ z.re := by
    have hh := neg_abs_le (z.re-2)
    linarith
  have hheight : 3+|z.im| ≤ 2*(3+|t|) := by
    have hab := abs_add_le (z.im-t) t
    rw [sub_add_cancel] at hab
    linarith [abs_nonneg t]
  apply (regular_right_growth η hp hzre).trans
  have hsq : (3+|z.im|)^2 ≤ 4*(3+|t|)^2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 3+|z.im|)
      (by positivity : 0 ≤ 2*(3+|t|))).mpr hheight
    nlinarith
  calc
    _ ≤ uniformConstant*(η.modulus.absNorm : ℝ)^(3/5 : ℝ)*(4*(3+|t|)^2) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg uniformConstant_nonneg (Real.rpow_nonneg (by positivity) _))
    _ = _ := by ring

end SevenEighths.HeckeLogarithmicInput

end

end OAI
end OAIOriginalModule2022

/-! Original module: OAI.NumberTheory.DirichletL.GammaZeroDetector
Source SHA256: 3ec3bab7d9c8bd0e3a0d4b94738147d6f002b405a539547df172d1751489f60b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2023






namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex

namespace SevenEighths.GammaZeroDetector

theorem gamma_shift (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    Gamma (z + n) = Gamma z * ∏ k ∈ Finset.range n, (z + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : z + n ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp only [add_im, natCast_im, add_zero, zero_im] at this
      exact hz this
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one _ hn, ih, Finset.prod_range_succ]
    ring

theorem gamma_shift_norm_lower (z : ℂ) (n : ℕ) :
    |z.im| ^ n ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ := by
  rw [norm_prod]
  calc
    _ = ∏ _k ∈ Finset.range n, |z.im| := by simp
    _ ≤ _ := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro k _
      simpa using Complex.abs_im_le_norm (z + k)

theorem gamma_power_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      |z.im| ^ n * ‖Gamma z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := CubicGammaExponential.real_Gamma_compact_bound
    (a + n) (b + n) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro z hza hzb hzi
  have hzne : z.im ≠ 0 := by intro h; norm_num [h] at hzi
  have hzre : 0 < (z + n).re := by simp only [add_re, natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) n]
  calc
    _ ≤ ‖∏ k ∈ Finset.range n, (z + k)‖ * ‖Gamma z‖ :=
      mul_le_mul_of_nonneg_right (gamma_shift_norm_lower z n) (norm_nonneg _)
    _ = ‖Gamma (z + n)‖ := by rw [gamma_shift z hzne n, norm_mul, mul_comm]
    _ ≤ Real.Gamma (z + n).re := CubicGammaExponential.norm_Gamma_le_real _ hzre
    _ ≤ C := hbound _ (by simp only [add_re, natCast_re]; constructor <;> linarith)

theorem gamma_rapid_bound (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (1 + |z.im|) ^ n * ‖Gamma z‖ ≤ C := by
  obtain ⟨C₁, hC₁, hlarge⟩ := gamma_power_bound a b ha n
  obtain ⟨C₀, hC₀, hsmall⟩ := CubicGammaExponential.real_Gamma_compact_bound a b ha
  refine ⟨2 ^ n * (C₀ + C₁), by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · have hp : (1 + |z.im|) ^ n ≤ 2 ^ n * |z.im| ^ n := by
      rw [← mul_pow]
      gcongr
      linarith
    calc
      _ ≤ (2 ^ n * |z.im| ^ n) * ‖Gamma z‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ n * C₁ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hlarge z hza hzb ht) (by positivity)
      _ ≤ _ := by gcongr; linarith
  · have hg : ‖Gamma z‖ ≤ C₀ :=
      (CubicGammaExponential.norm_Gamma_le_real z (ha.trans_le hza)).trans (hsmall z.re ⟨hza,hzb⟩)
    have hp : (1 + |z.im|) ^ n ≤ (2 : ℝ) ^ n := by gcongr; linarith
    calc
      _ ≤ 2 ^ n * C₀ := mul_le_mul hp hg (norm_nonneg _) (by positivity)
      _ ≤ _ := by gcongr; linarith

theorem gamma_differentiableAt_right {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n hn
  have h := congrArg Complex.re hn
  simp only [neg_re, natCast_re] at h
  linarith [Nat.cast_nonneg (α := ℝ) n]

def cancelledKernel (f g : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (Y : ℂ) ^ z * Gamma (z + 1) * dslope f 0 z * g z

def literalKernel (f g : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (Y : ℂ) ^ z * Gamma z * f z * g z

theorem cancelledKernel_eq_literal {f g : ℂ → ℂ} {Y : ℝ} (hf0 : f 0 = 0)
    {z : ℂ} (hz : z ≠ 0) : cancelledKernel f g Y z = literalKernel f g Y z := by
  unfold cancelledKernel literalKernel
  rw [Gamma_add_one z hz, dslope_of_ne f hz]
  simp only [slope, sub_zero, hf0, smul_eq_mul, vsub_eq_sub]
  field_simp

theorem cancelledKernel_at_zero (f g : ℂ → ℂ) (Y : ℝ) :
    cancelledKernel f g Y 0 = deriv f 0 * g 0 := by
  simp [cancelledKernel, Complex.cpow_zero, Complex.Gamma_one]

theorem dslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope f 0) := by
  apply differentiableOn_univ.mp
  exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).mpr hf.differentiableOn

theorem cancelledKernel_differentiableAt {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) {Y : ℝ} (hY : 0 < Y) {z : ℂ} (hz : -1 < z.re) :
    DifferentiableAt ℂ (cancelledKernel f g Y) z := by
  exact ((((differentiableAt_id.const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hY.ne'))).mul
    ((gamma_differentiableAt_right (by change 0 < z.re + 1; linarith)).comp z
      (differentiableAt_id.add_const 1))).mul (dslope_entire hf z)).mul (hg z))

theorem literalKernel_norm (f g : ℂ → ℂ) {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    ‖literalKernel f g Y z‖ = Y ^ z.re * ‖Gamma z‖ * ‖f z‖ * ‖g z‖ := by
  simp only [literalKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]

theorem cancelledKernel_large_height_bound {f g : ℂ → ℂ} (hf0 : f 0 = 0)
    {Y a b A B G : ℝ} (hY : 1 ≤ Y) (_ha : -1 < a) (n : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hG : 0 ≤ G)
    (hgamma : ∀ z : ℂ, a + 1 ≤ z.re → z.re ≤ b + 1 →
      (1 + |z.im|) ^ (n + 2) * ‖Gamma z‖ ≤ G)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hg : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) (hzi : 1 ≤ |z.im|) :
    ‖cancelledKernel f g Y z‖ ≤ (Y ^ b * G * A * B) / (1 + z.im ^ 2) := by
  have hY0 : 0 < Y := by linarith
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzi
  have hnorm : 1 ≤ ‖z‖ := hzi.trans (Complex.abs_im_le_norm z)
  have hΓ : ‖Gamma z‖ ≤ ‖Gamma (z + 1)‖ := by
    rw [Gamma_add_one z hz0, norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hnorm
  have hga := hgamma (z + 1) (by simpa using hza) (by simpa using hzb)
  simp only [add_im, one_im, add_zero] at hga
  have hweighted : (1 + z.im ^ 2) * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) ≤ G := by
    calc
      _ ≤ (1 + |z.im|) ^ 2 * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) := by
        gcongr
        nlinarith [sq_abs z.im, abs_nonneg z.im]
      _ = (1 + |z.im|) ^ (n + 2) * ‖Gamma (z + 1)‖ := by rw [pow_add]; ring
      _ ≤ _ := hga
  have hgdiv : ‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n ≤ G / (1 + z.im ^ 2) :=
    (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using hweighted)
  rw [cancelledKernel_eq_literal hf0 hz0, literalKernel_norm f g hY0]
  calc
    _ ≤ Y ^ b * ‖Gamma (z + 1)‖ * (A * (1 + |z.im|) ^ n) * B := by
      gcongr
      · exact hf z hza hzb
      · exact hg z hza hzb
    _ = (Y ^ b * A * B) * (‖Gamma (z + 1)‖ * (1 + |z.im|) ^ n) := by ring
    _ ≤ (Y ^ b * A * B) * (G / (1 + z.im ^ 2)) :=
      mul_le_mul_of_nonneg_left hgdiv (by positivity)
    _ = _ := by ring

theorem cancelledKernel_strip_bound {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y a b A B : ℝ}
    (hY : 1 ≤ Y) (ha : -1 < a) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖cancelledKernel f g Y z‖ ≤ C / (1 + z.im ^ 2) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨G,hG,hgamma⟩ := gamma_rapid_bound (a+1) (b+1) (by linarith) (n+2)
  let S : Set ℂ := Icc a b ×ℂ Icc (-1 : ℝ) 1
  have hc : ContinuousOn (cancelledKernel f g Y) S := by
    intro z hz
    exact (cancelledKernel_differentiableAt hf hg hY0 (ha.trans_le hz.1.1)).continuousAt.continuousWithinAt
  have hw : ContinuousOn (fun z : ℂ => (1 + z.im ^ 2) * ‖cancelledKernel f g Y z‖) S :=
    (continuous_const.add (continuous_im.pow 2)).continuousOn.mul hc.norm
  obtain ⟨K,hK⟩ := (isCompact_Icc.reProdIm isCompact_Icc : IsCompact S).bddAbove_image hw
  refine ⟨|K| + Y ^ b * G * A * B + 1, by positivity, ?_⟩
  intro z hza hzb
  by_cases ht : 1 ≤ |z.im|
  · apply (cancelledKernel_large_height_bound hf0 hY ha n hA hB hG.le hgamma
      hfbound hgbound hza hzb ht).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [abs_nonneg K]
  · have hzS : z ∈ S := ⟨⟨hza,hzb⟩, abs_le.mp (le_of_lt (lt_of_not_ge ht))⟩
    have hb := hK (Set.mem_image_of_mem _ hzS)
    apply (le_div_iff₀ (by positivity : 0 < 1 + z.im ^ 2)).mpr
    have hnonneg : 0 ≤ Y ^ b * G * A * B := by positivity
    nlinarith [le_abs_self K]

theorem cancelledKernel_vertical_integrable {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {Y a b C x : ℝ}
    (hY : 0 < Y) (ha : -1 < a) (hx : x ∈ Icc a b)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖cancelledKernel f g Y z‖ ≤ C / (1 + z.im ^ 2)) :
    Integrable (fun t : ℝ => cancelledKernel f g Y ((x : ℂ) + t * I)) := by
  have hc : Continuous (fun t : ℝ => cancelledKernel f g Y ((x : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (cancelledKernel_differentiableAt hf hg hY (by simpa using ha.trans_le hx.1)).continuousAt.comp
    fun_prop
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro t
  simpa [div_eq_mul_inv] using hbound ((x : ℂ) + t * I) (by simpa using hx.1) (by simpa using hx.2)

theorem cancelledKernel_contour_shift {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y a b A B : ℝ}
    (hY : 1 ≤ Y) (ha : -1 < a) (hab : a ≤ b) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ B) :
    (∫ t : ℝ, cancelledKernel f g Y ((a : ℂ) + t * I)) =
      ∫ t : ℝ, cancelledKernel f g Y ((b : ℂ) + t * I) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨C,_,hbnd⟩ := cancelledKernel_strip_bound hf hg hf0 hY ha n hA hB hfbound hgbound
  apply VerticalContourShift.integral_eq_of_strip_decay _ a b C hab
    (fun z hz _ => cancelledKernel_differentiableAt hf hg hY0 (ha.trans_le hz))
    (cancelledKernel_vertical_integrable hf hg hY0 ha ⟨le_rfl,hab⟩ hbnd)
    (cancelledKernel_vertical_integrable hf hg hY0 ha ⟨hab,le_rfl⟩ hbnd)
  intro x hx t
  simpa using hbnd ((x : ℂ) + t * I) (by simpa using hx.1) (by simpa using hx.2)

theorem literal_contour_shift {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf0 : f 0 = 0) {Y A B : ℝ}
    (hY : 1 ≤ Y) (n : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfbound : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ A * (1 + |z.im|) ^ n)
    (hgbound : ∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ B) :
    (∫ t : ℝ, literalKernel f g Y ((2 : ℂ) + t * I)) =
      ∫ t : ℝ, literalKernel f g Y ((-(1/4) : ℂ) + t * I) := by
  have h := cancelledKernel_contour_shift hf hg hf0 hY (by norm_num : (-1 : ℝ) < -(1/4))
    (by norm_num : (-(1/4) : ℝ)≤2) n hA hB hfbound hgbound
  have he (x : ℝ) (hx : x ≠ 0) (t : ℝ) :
      cancelledKernel f g Y ((x : ℂ) + t * I) = literalKernel f g Y ((x : ℂ) + t * I) := by
    apply cancelledKernel_eq_literal hf0
    intro hz
    apply hx
    simpa using congrArg Complex.re hz
  simp only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] at h
  have h2 (t : ℝ) := he 2 (by norm_num) t
  have hq (t : ℝ) := he (-(1/4)) (by norm_num) t
  norm_num only [Complex.ofReal_ofNat, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one] at h2 hq
  simpa only [h2, hq] using h.symm

theorem gamma_negative_quarter_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ t : ℝ,
      (1 + t ^ 2) * (1 + |t|) ^ n * ‖Gamma ((-(1/4) : ℂ) + t * I)‖ ≤ G := by
  obtain ⟨C,hC,hgamma⟩ := gamma_rapid_bound (3/4) (3/4) (by norm_num) (n+2)
  refine ⟨4*C, by positivity, ?_⟩
  intro t
  let z : ℂ := (-(1/4) : ℂ) + t * I
  have hzre : z.re = -(1/4) := by simp [z]
  have hzim : z.im = t := by simp [z]
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzre
  have hn : (1/4 : ℝ) ≤ ‖z‖ := by simpa only [hzre, abs_neg, abs_of_pos (by norm_num : (0 : ℝ)<1/4)] using Complex.abs_re_le_norm z
  have hΓ : ‖Gamma z‖ ≤ 4 * ‖Gamma (z+1)‖ := by
    rw [Gamma_add_one z hz0, norm_mul]
    nlinarith [norm_nonneg (Gamma z)]
  have hbound := hgamma (z+1) (by norm_num [hzre]) (by norm_num [hzre])
  simp only [add_im, one_im, add_zero, hzim] at hbound
  have hp : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t, abs_nonneg t]
  change (1+t^2)*(1+|t|)^n*‖Gamma z‖ ≤ 4*C
  calc
    _ ≤ (1+|t|)^2*(1+|t|)^n*(4*‖Gamma (z+1)‖) := by gcongr
    _ = 4*((1+|t|)^(n+2)*‖Gamma (z+1)‖) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by norm_num)

theorem literal_shifted_integral_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ (f g : ℂ → ℂ) (Y A B : ℝ),
      0 < Y → 0 ≤ A → 0 ≤ B →
      (∀ t : ℝ, ‖f ((-(1/4) : ℂ)+t*I)‖ ≤ A*(1+|t|)^n) →
      (∀ t : ℝ, ‖g ((-(1/4) : ℂ)+t*I)‖ ≤ B) →
      ‖∫ t : ℝ, literalKernel f g Y ((-(1/4) : ℂ)+t*I)‖ ≤
        Real.pi * G * A * B * Y ^ (-(1/4 : ℝ)) := by
  obtain ⟨G,hG,hgamma⟩ := gamma_negative_quarter_bound n
  refine ⟨G,hG,?_⟩
  intro f g Y A B hY hA hB hf hg
  have hbound (t : ℝ) :
      ‖literalKernel f g Y ((-(1/4) : ℂ)+t*I)‖ ≤
        (G*A*B*Y^(-(1/4 : ℝ)))*(1+t^2)⁻¹ := by
    have hga : (1+|t|)^n*‖Gamma ((-(1/4) : ℂ)+t*I)‖ ≤ G/(1+t^2) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [hgamma t])
    rw [literalKernel_norm f g hY]
    have hzre : (((-(1/4) : ℂ)+t*I).re) = (-(1/4) : ℝ) := by norm_num
    rw [hzre]
    change Y^(-(1/4 : ℝ))*‖Gamma ((-(1/4) : ℂ)+t*I)‖*
      ‖f ((-(1/4) : ℂ)+t*I)‖*‖g ((-(1/4) : ℂ)+t*I)‖ ≤ _
    calc
      _ ≤ Y^(-(1/4 : ℝ))*‖Gamma ((-(1/4) : ℂ)+t*I)‖*(A*(1+|t|)^n)*B := by gcongr; exact hf t; exact hg t
      _ = (A*B*Y^(-(1/4 : ℝ)))*((1+|t|)^n*‖Gamma ((-(1/4) : ℂ)+t*I)‖) := by ring
      _ ≤ (A*B*Y^(-(1/4 : ℝ)))*(G/(1+t^2)) := mul_le_mul_of_nonneg_left hga (by positivity)
      _ = _ := by ring
  have hint := norm_integral_le_of_norm_le
    (integrable_inv_one_add_sq.const_mul (G*A*B*Y^(-(1/4 : ℝ)))) (ae_of_all _ hbound)
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at hint
  convert hint using 1; ring

theorem literal_detector_bound (n : ℕ) :
    ∃ G : ℝ, 0 < G ∧ ∀ (f g : ℂ → ℂ) (Y A B : ℝ),
      Differentiable ℂ f → Differentiable ℂ g → f 0 = 0 →
      1 ≤ Y → 0 ≤ A → 0 ≤ B →
      (∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖f z‖ ≤ A*(1+|z.im|)^n) →
      (∀ z : ℂ, -(1/4 : ℝ) ≤ z.re → z.re ≤ 2 → ‖g z‖ ≤ B) →
      ‖∫ t : ℝ, literalKernel f g Y ((2 : ℂ)+t*I)‖ ≤
        Real.pi * G * A * B * Y ^ (-(1/4 : ℝ)) := by
  obtain ⟨G,hG,hbound⟩ := literal_shifted_integral_bound n
  refine ⟨G,hG,?_⟩
  intro f g Y A B hf hg hf0 hY hA hB hfb hgb
  rw [literal_contour_shift hf hg hf0 hY n hA hB hfb hgb]
  apply hbound f g Y A B (by linarith) hA hB
  · intro t; simpa using hfb ((-(1/4) : ℂ)+t*I) (by norm_num) (by norm_num)
  · intro t; exact hgb _ (by norm_num) (by norm_num)

open HeckeFamily

def cutoffSet (D : ℝ) : Finset (Ideal O) :=
  ConcretePrimeRowBridge.idealsUpTo ⌊2*D⌋₊

theorem mem_cutoffSet {D : ℝ} (hD : 0 ≤ D) {J : Ideal O} :
    J ∈ cutoffSet D ↔ J ≠ 0 ∧ (J.absNorm : ℝ) ≤ 2*D := by
  rw [cutoffSet, ConcretePrimeRowBridge.mem_idealsUpTo]
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨?_, ?_⟩
    · intro h; simp [h] at hp
    · exact (by exact_mod_cast hb : (J.absNorm : ℝ) ≤ ⌊2*D⌋₊).trans
        (Nat.floor_le (by positivity))
  · rintro ⟨hp, hb⟩
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp),
      Nat.le_floor hb⟩

def cutoffTerm (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) (s : ℂ) : ℂ :=
  HeckeDyadic.coefficient χ true J * V ((J.absNorm : ℝ)/D) *
    CubicEisenstein.fullIdealWeight s J

def cutoff (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) : ℂ :=
  ∑ J ∈ cutoffSet D, cutoffTerm χ V D J s

@[simp] theorem cutoffTerm_zero (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) :
    cutoffTerm χ V D 0 s = 0 := by
  simp [cutoffTerm, CubicEisenstein.fullIdealWeight]

theorem cutoffTerm_eq (χ : Character) (V : ℝ → ℂ) (D : ℝ) {J : Ideal O}
    (hJ : J ≠ 0) (s : ℂ) :
    cutoffTerm χ V D J s = (UniqueFactorizationMonoid.moebius J : ℂ) *
      idealCoeff χ J * V ((J.absNorm : ℝ)/D) * (J.absNorm : ℂ)^(-s) := by
  rw [cutoffTerm, CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
  rfl

theorem cutoff_eq_tsum (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 0 < D)
    (hV : ∀ x : ℝ, 2 ≤ x → V x = 0) (s : ℂ) :
    cutoff χ V D s = ∑' J : Ideal O, cutoffTerm χ V D J s := by
  symm
  apply tsum_eq_sum
  intro J hJ
  by_cases hzero : J = 0
  · subst J; exact cutoffTerm_zero χ V D s
  · have hn : 2*D < (J.absNorm : ℝ) := by
      by_contra h
      exact hJ ((mem_cutoffSet hD.le).mpr ⟨hzero, le_of_not_gt h⟩)
    have hv := hV ((J.absNorm : ℝ)/D) ((le_div_iff₀ hD).mpr hn.le)
    simp [cutoffTerm, hv]

theorem cutoffTerm_entire (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) :
    Differentiable ℂ (cutoffTerm χ V D J) := by
  by_cases hJ : J = 0
  · subst J
    have he : cutoffTerm χ V D 0 = fun _ : ℂ => 0 := funext (cutoffTerm_zero χ V D)
    rw [he]
    exact differentiable_const 0
  · have hn : (J.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hJ
    unfold cutoffTerm
    simp only [CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
    exact (differentiable_id.neg.const_cpow (Or.inl hn)).const_mul _

theorem cutoff_entire (χ : Character) (V : ℝ → ℂ) (D : ℝ) :
    Differentiable ℂ (cutoff χ V D) := by
  exact Differentiable.fun_sum fun J _ => cutoffTerm_entire χ V D J

theorem cutoffTerm_norm_le (χ : Character) (V : ℝ → ℂ) (D : ℝ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) (J : Ideal O) :
    ‖cutoffTerm χ V D J s‖ ≤ 1 := by
  by_cases hJ : J = 0
  · subst J
    rw [cutoffTerm_zero, norm_zero]
    norm_num
  · have hnorm : 1 ≤ (J.absNorm : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
    have hw : ‖CubicEisenstein.fullIdealWeight s J‖ ≤ 1 := by
      rw [CubicEisenstein.fullIdealWeight, ite_eq_right hJ]
      have hn : 0 < (J.absNorm : ℝ) := by linarith
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn, neg_re]
      exact (Real.rpow_le_rpow_of_exponent_le hnorm (neg_nonpos.mpr hs)).trans_eq (Real.rpow_zero _)
    rw [cutoffTerm, norm_mul, norm_mul]
    calc
      _ ≤ (1 : ℝ)*1*1 := by gcongr; exact HeckeDyadic.coefficient_norm_le χ true J; exact hV _
      _ = 1 := by norm_num

theorem cutoff_norm_le (χ : Character) (V : ℝ → ℂ) {D : ℝ} (hD : 1 ≤ D)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖cutoff χ V D s‖ ≤ 256*D := by
  have hcount := DescentFiberCost.finite_ideal_count_real (cutoffSet D) (2*D) (by linarith)
    (fun J hJ => ((mem_cutoffSet (by linarith : 0 ≤ D)).mp hJ).1)
    (fun J hJ => ((mem_cutoffSet (by linarith : 0 ≤ D)).mp hJ).2)
  calc
    _ ≤ ∑ J ∈ cutoffSet D, ‖cutoffTerm χ V D J s‖ := norm_sum_le _ _
    _ ≤ ∑ _J ∈ cutoffSet D, (1 : ℝ) := Finset.sum_le_sum (fun J _ => cutoffTerm_norm_le χ V D hV hs J)
    _ = ((cutoffSet D).card : ℝ) := by simp
    _ ≤ 256*D := by linarith

theorem original_right_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ s : ℂ,
      (1/4 : ℝ) ≤ s.re → ‖LFunction χ s‖ ≤
        C*(χ.modulus.absNorm : ℝ)^2*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hdel⟩ := HeckeDeletionBounds.factors_subpower_bound
    (1/4) 1 (by norm_num) (by norm_num)
  let Cp := HeckeLogarithmicInput.uniformConstant
  have hCp : 0 ≤ Cp := HeckeLogarithmicInput.uniformConstant_nonneg
  refine ⟨(1+Cp)*Cd, by positivity, ?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue ≠ 1 := fun h => hχ
    ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hL := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10 : ℝ) ≤ s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hL
  have hnorm : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
  have hqp : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ) ≤ χ.modulus.absNorm := by
    apply le_trans _ hnorm
    simpa using Real.rpow_le_rpow_of_exponent_le
      (HeckeLogarithmicInput.modulus_norm_ge_one ψ) (by norm_num : (3/5 : ℝ) ≤ 1)
  have hLd : ‖LFunction ψ s‖ ≤ (1+Cp)*(χ.modulus.absNorm : ℝ)*(3+|s.im|)^2 := by
    apply hL.trans
    change Cp * _ * _ ≤ _
    gcongr
    linarith
  have hd := hdel χ.modulus χ.modulus_ne_bot ψ s hs
  rw [Real.rpow_one] at hd
  have hd' : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖ ≤ Cd*(χ.modulus.absNorm : ℝ) := by
    linarith [norm_nonneg ((HeckeFiniteDeletion.factors χ.modulus ψ s)⁻¹)]
  rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ (by linarith), norm_mul]
  calc
    _ ≤ ((1+Cp)*(χ.modulus.absNorm : ℝ)*(3+|s.im|)^2) *
        (Cd*(χ.modulus.absNorm : ℝ)) := mul_le_mul hLd hd' (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem shifted_original_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ (ρ z : ℂ),
      (51/100 : ℝ) ≤ ρ.re → -(1/4 : ℝ) ≤ z.re →
      ‖LFunction χ (ρ+z)‖ ≤
        (C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2)*(1+|z.im|)^2 := by
  obtain ⟨C,hC,hbound⟩ := original_right_growth
  refine ⟨C,hC,?_⟩
  intro χ hχ ρ z hρ hz
  have hb := hbound χ hχ (ρ+z) (by simp only [add_re]; linarith)
  have hh : 3+|(ρ+z).im| ≤ (3+|ρ.im|)*(1+|z.im|) := by
    simp only [add_im]
    have hab := abs_add_le ρ.im z.im
    nlinarith [abs_nonneg ρ.im, abs_nonneg z.im]
  calc
    _ ≤ C*(χ.modulus.absNorm : ℝ)^2*((3+|ρ.im|)*(1+|z.im|))^2 := by
      apply hb.trans; gcongr
    _ = _ := by ring

def detectorIntegrand (χ : Character) (V : ℝ → ℂ) (D Y : ℝ) (ρ z : ℂ) : ℂ :=
  (Y : ℂ)^z * Gamma z * LFunction χ (ρ+z) * cutoff χ V D (ρ+z)

def detectorIntegral (χ : Character) (V : ℝ → ℂ) (D Y : ℝ) (ρ : ℂ) : ℂ :=
  ((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)

theorem detector_contour_shift (χ : Character) (hχ : χ.residue ≠ 1)
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {D Y : ℝ}
    (hD : 1 ≤ D) (hY : 1 ≤ Y) {ρ : ℂ} (hρ : (51/100 : ℝ) ≤ ρ.re)
    (hzero : LFunction χ ρ = 0) :
    (∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)) =
      ∫ t : ℝ, detectorIntegrand χ V D Y ρ (-(1/4)+t*I) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth
  apply literal_contour_shift (A := C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (B := 256*D)
    ((LFunction_entire_nonprincipal χ hχ).comp (differentiable_const ρ |>.add differentiable_id))
    ((cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id))
    (by simpa using hzero) hY 2 (by positivity) (by positivity : 0 ≤ 256*D)
  · intro z hz _
    exact hgrowth χ hχ ρ z hρ hz
  · intro z hz _
    exact cutoff_norm_le χ V hD hV (s := ρ+z) (by simp only [add_re]; linarith)

theorem detector_integral_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (χ : Character), χ.residue ≠ 1 →
      ∀ (V : ℝ → ℂ), (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ (D Y : ℝ),
      1 ≤ D → 1 ≤ Y → ∀ ρ : ℂ, (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 →
      ‖detectorIntegral χ V D Y ρ‖ ≤
        K*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2*D*Y^(-(1/4 : ℝ)) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth
  obtain ⟨G,hG,hgamma⟩ := literal_detector_bound 2
  refine ⟨128*G*C, by positivity, ?_⟩
  intro χ hχ V hV D Y hD hY ρ hρ hzero
  have hb := hgamma (fun z => LFunction χ (ρ+z)) (fun z => cutoff χ V D (ρ+z))
    Y (C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (256*D)
    ((LFunction_entire_nonprincipal χ hχ).comp (differentiable_const ρ |>.add differentiable_id))
    ((cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id))
    (by simpa using hzero) hY (by positivity) (by positivity)
    (fun z hz _ => hgrowth χ hχ ρ z hρ hz)
    (fun z hz _ => cutoff_norm_le χ V hD hV (by simp only [add_re]; linarith))
  change ‖∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)‖ ≤ _ at hb
  rw [detectorIntegral, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (by positivity))).trans_eq
  field_simp
  ring

theorem detector_integrable (χ : Character) (hχ : χ.residue ≠ 1)
    (V : ℝ → ℂ) (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) {D Y : ℝ}
    (hD : 1 ≤ D) (hY : 1 ≤ Y) {ρ : ℂ} (hρ : (51/100 : ℝ) ≤ ρ.re)
    (hzero : LFunction χ ρ = 0) {x : ℝ} (hx : x ∈ Icc (-(1/4)) 2) (hx0 : x ≠ 0) :
    Integrable (fun t : ℝ => detectorIntegrand χ V D Y ρ ((x : ℂ)+t*I)) := by
  obtain ⟨C,hC,hgrowth⟩ := shifted_original_growth
  let f : ℂ → ℂ := fun z => LFunction χ (ρ+z)
  let g : ℂ → ℂ := fun z => cutoff χ V D (ρ+z)
  have hf : Differentiable ℂ f :=
    (LFunction_entire_nonprincipal χ hχ).comp (differentiable_const ρ |>.add differentiable_id)
  have hg : Differentiable ℂ g :=
    (cutoff_entire χ V D).comp (differentiable_const ρ |>.add differentiable_id)
  have hf0 : f 0 = 0 := by simpa [f] using hzero
  obtain ⟨B,_,hb⟩ := cancelledKernel_strip_bound (b := 2) hf hg hf0 hY
    (by norm_num : (-1 : ℝ) < -(1/4)) 2
    (A := C*(χ.modulus.absNorm : ℝ)^2*(3+|ρ.im|)^2) (B := 256*D)
    (by positivity) (by positivity)
    (fun z hz _ => hgrowth χ hχ ρ z hρ hz)
    (fun z hz _ => cutoff_norm_le χ V hD hV (s := ρ+z) (by simp only [add_re]; linarith))
  have hi := cancelledKernel_vertical_integrable hf hg (by linarith : 0 < Y)
    (by norm_num : (-1 : ℝ) < -(1/4)) hx hb
  apply hi.congr
  filter_upwards [] with t
  apply cancelledKernel_eq_literal hf0
  intro hz
  apply hx0
  simpa using congrArg Complex.re hz

theorem detectorIntegral_contour_normalization (χ : Character) (V : ℝ → ℂ)
    (D Y : ℝ) (ρ : ℂ) :
    detectorIntegral χ V D Y ρ = ((2*Real.pi : ℂ)*I)⁻¹ *
      ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)*I := by
  rw [MeasureTheory.integral_mul_const, mul_inv_rev]
  simp only [detectorIntegral, ofReal_mul, ofReal_ofNat]
  have hi : I⁻¹*I = 1 := inv_mul_cancel₀ I_ne_zero
  calc
    _ = (I⁻¹*I)*(((2*Real.pi : ℂ))⁻¹ * ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)) := by rw [hi, one_mul]
    _ = _ := by ring

theorem detector_power_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (R θ : ℝ), 0 ≤ R → 0 ≤ θ →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ (U D : ℝ), 1 ≤ U →
      1 ≤ D → D ≤ U^(3/2 : ℝ) → (χ.modulus.absNorm : ℝ) ≤ R*U →
      ∀ ρ : ℂ, (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ‖detectorIntegral χ V D (U^20) ρ‖ ≤ (K*R^2)*U^(-(3/2 : ℝ)+2*θ) := by
  obtain ⟨K,hK,hbound⟩ := detector_integral_bound
  refine ⟨16*K, by positivity, ?_⟩
  intro R θ hR hθ χ hχ V hV U D hU hD hDU hQ ρ hρ hzero ht
  have hU0 : 0 < U := by linarith
  have huθ : 1 ≤ U^θ := Real.one_le_rpow hU hθ
  have hheight : 3+|ρ.im| ≤ 4*U^θ := by linarith
  have hY : 1 ≤ U^20 := one_le_pow₀ hU
  have he : (U^20)^(-(1/4 : ℝ)) = U^(-5 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    norm_num
  have hb := hbound χ hχ V hV D (U^20) hD hY ρ hρ hzero
  rw [he] at hb
  calc
    _ ≤ K*(R*U)^2*(4*U^θ)^2*U^(3/2 : ℝ)*U^(-5 : ℝ) := by
      apply hb.trans; gcongr
    _ = (16*K*R^2)*(U^(2 : ℝ)*(U^θ)^2*U^(3/2 : ℝ)*U^(-5 : ℝ)) := by
      rw [Real.rpow_two]; ring
    _ = _ := by
      rw [← Real.rpow_mul_natCast hU0.le, ← Real.rpow_add hU0,
        ← Real.rpow_add hU0, ← Real.rpow_add hU0]
      congr 2
      ring

theorem detector_uniform_small (R θ ε : ℝ) (hR : 0 ≤ R)
    (hθ : 0 ≤ θ) (hθ' : θ < 3/4) (hε : 0 < ε) :
    ∃ U₀ : ℝ, ∀ U : ℝ, U₀ ≤ U → 1 ≤ U →
      ∀ (χ : Character), χ.residue ≠ 1 → ∀ (V : ℝ → ℂ),
      (∀ x : ℝ, ‖V x‖ ≤ 1) → ∀ D : ℝ, 1 ≤ D → D ≤ U^(3/2 : ℝ) →
      (χ.modulus.absNorm : ℝ) ≤ R*U → ∀ ρ : ℂ,
      (51/100 : ℝ) ≤ ρ.re → LFunction χ ρ = 0 → |ρ.im| ≤ U^θ →
      ‖detectorIntegral χ V D (U^20) ρ‖ < ε := by
  obtain ⟨K,hK,hbound⟩ := detector_power_bound
  have ht : Tendsto (fun U : ℝ => (K*R^2)*U^(-(3/2 : ℝ)+2*θ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < (3/2 : ℝ)-2*θ)).const_mul (K*R^2)
    simpa [neg_sub, sub_eq_add_neg, add_comm] using h
  obtain ⟨U₀,hU₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  refine ⟨U₀,?_⟩
  intro U hU₀' hU χ hχ V hV D hD hDU hQ ρ hρ hzero ht
  exact (hbound R θ hR hθ χ hχ V hV U D hU hD hDU hQ ρ hρ hzero ht).trans_lt (hU₀ U hU₀')

end SevenEighths.GammaZeroDetector

end

end OAI
end OAIOriginalModule2023

/-! Original module: OAI.NumberTheory.DirichletL.GammaDetectorExpansion
Source SHA256: f1e455f9752c9573a43abc59eee148dcd5bf21577eb4603dc2eeb1c5599fd9f6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2024




namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex
namespace SevenEighths.GammaDetectorExpansion
open GammaZeroDetector HeckeFamily

def line (t : ℝ) : ℂ := 2+t*I

@[simp] theorem line_re (t : ℝ) : (line t).re = 2 := by simp [line]
@[simp] theorem line_im (t : ℝ) : (line t).im = t := by simp [line]

theorem gamma_line_integrable : Integrable (fun t : ℝ => Gamma (line t)) := by
  obtain ⟨C,hC,hbound⟩ := gamma_rapid_bound 2 2 (by norm_num) 2
  apply (integrable_inv_one_add_sq.const_mul C).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.mpr
    exact fun t => (gamma_differentiableAt_right (by simp : 0 < (line t).re)).continuousAt.comp
      (by unfold line; fun_prop)
  · filter_upwards [] with t
    have hb := hbound (line t) (by simp) (by simp)
    simp only [line_im] at hb
    have hp : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t, abs_nonneg t]
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [norm_nonneg (Gamma (line t))]

theorem gamma_mellin_inverse {x : ℝ} (hx : 0 < x) :
    ((2*Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t : ℝ, (x : ℂ)^(-line t)*Gamma (line t)) = Complex.exp (-(x : ℂ)) := by
  let f : ℝ → ℂ := fun x => (Real.exp (-x) : ℂ)
  have hm (s : ℂ) (hs : 0 < s.re) : mellin f s = Gamma s := by
    rw [Gamma_eq_integral hs, GammaIntegral_eq_mellin]
  have hf : MellinConvergent f (2 : ℂ) := by
