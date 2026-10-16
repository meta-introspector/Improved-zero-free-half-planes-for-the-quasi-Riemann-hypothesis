      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (windows : Fin 7→ℝ→ℂ) (C Cd Ct Tmax Γ E oldHeight B M H U A₀ Vmax : ℝ) (N J Ntail : ℕ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤C → 0≤Cd → 0≤Ct → 0≤Tmax → 0≤Γ → 1≤E → 1≤U → 1≤B → 0≤H →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B) →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail≤Tmax →
      (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 →
      (∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail side≤
        canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A₀ Vmax*
          Γ*(((X/B^3)*(Real.exp 1*B)^3)*F)*U^(deltaLoss+8*ε)*E*(1+‖oldHeight‖)^(2*J) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_below_rank deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks side
    windows C Cd Ct Tmax Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hCd hCt hTmax hΓ hE hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ htail hterminal ih
  have hb := hbound p hp hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate
    pool blocks side windows C Cd Ct Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hΓ (zero_le_one.trans hE) hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ ih
  have hX:=hstate.column_pos
  have hF : 0≤F:=zero_le_one.trans hstate.label_ge_one
  have hP : 0≤((X/B^3)*(Real.exp 1*B)^3)*F := by positivity
  have hs := canonicalBudgetScalar_bound C Cd Ct Tmax Clo Chi A₀ Vmax Γ
    (((X/B^3)*(Real.exp 1*B)^3)*F) E oldHeight (Real.exp 1*B) U deltaLoss ε
    (globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail)
    ((Ksrc/Z^η)/Z^(η*(N:ℝ))) J hC hCd hCt hTmax hClo.le hChi.le hΓ hP hE
    (by positivity) hBU hU hδ.le hε.le htail hterminal
  apply hb.trans
  convert hs using 1 ; ring

end

def reopeningScaleConstant (A M : ℝ) : ℝ := 1+Real.exp (A+1)+Real.exp M

def reopeningAuxiliaryScale (A M κ Z : ℝ) : ℝ := reopeningScaleConstant A M*Z^(κ+3)

lemma reopeningScaleConstant_one (A M : ℝ) : 1≤reopeningScaleConstant A M := by
  unfold reopeningScaleConstant
  linarith [Real.exp_pos (A+1),Real.exp_pos M]

lemma reopeningScaleConstant_exp (A M : ℝ) : Real.exp A≤reopeningScaleConstant A M := by
  have h : Real.exp A≤Real.exp (A+1) := Real.exp_le_exp.mpr (by linarith)
  unfold reopeningScaleConstant
  linarith [Real.exp_pos M]

theorem globalFirstRowCap_reopening (Z η X F Ksrc B : ℝ)
    (hZ : 0<Z) (hK : 0<Ksrc) (hB : 0<B) :
    globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F =
      (Real.exp 1)^8*X^2*F^2*Z^η/Ksrc := by
  unfold globalFirstRowCap
  field_simp

theorem globalFirstRowCap_reopening_bound (Z η X F Ksrc B : ℝ)
    (hZ : 1≤Z) (_hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) :
    globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F ≤ (Real.exp 1)^8*Z^13 := by
  rw [globalFirstRowCap_reopening Z η X F Ksrc B (by linarith) (by linarith) (by linarith)]
  have hηZ : Z^η≤Z := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ hη1
  calc
    _ ≤ (Real.exp 1)^8*X^2*F^2*Z^η := div_le_self (by positivity) hK
    _ ≤ (Real.exp 1)^8*(Z^3)^2*(Z^3)^2*Z := by gcongr
    _ = _ := by ring

theorem globalFirstRowCap_reopening_small_power (Z η X F Ksrc B deltaLoss : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) (hδ : 0≤deltaLoss) :
    (max 1 (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F))^deltaLoss ≤
      ((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss) := by
  have he : 1≤Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hb := globalFirstRowCap_reopening_bound Z η X F Ksrc B hZ hη hη1 hX hXZ hF hFZ hK hB
  have hmax : max 1 (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)≤(Real.exp 1)^8*Z^13 :=
    max_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ he) (one_le_pow₀ hZ)) hb
  apply (Real.rpow_le_rpow (by positivity) hmax hδ).trans_eq
  rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
  norm_num

theorem reopeningAuxiliaryScale_bounds (A M κ Z η X F Ksrc B : ℝ)
    (hκ : 0≤κ) (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (_hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    let U := reopeningAuxiliaryScale A M κ Z
    1≤U ∧ Ksrc/Z^η≤U ∧ X/B^3≤U ∧ Real.exp 1*B≤U ∧ F≤U ∧ Z^κ≤U ∧
      Real.exp M≤U ∧ (X/B^3)*Real.exp M≤U ∧ (X/B^3)⁻¹≤U := by
  let C := reopeningScaleConstant A M
  have hC : 1≤C := reopeningScaleConstant_one A M
  have hCZ : C≤C*Z^(κ+3) := le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hZ (by linarith))
  have hZ3 : Z^3≤Z^(κ+3) := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num; linarith)
  have hZκ : Z^κ≤Z^(κ+3) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hbase : Z^(κ+3)≤C*Z^(κ+3) := le_mul_of_one_le_left (by positivity) hC
  have hKcut : Ksrc/Z^η≤Z^3 :=
    (div_le_self (by linarith) (Real.one_le_rpow hZ hη)).trans hKZ
  have hell : X/B^3≤X := div_le_self (by linarith) (one_le_pow₀ hB)
  have hB3 : B≤B^3 := by nlinarith [sq_nonneg (B-1)]
  have hBsup : Real.exp 1*B≤Real.exp (A+1)*Z^3 := by
    calc
      _ ≤ Real.exp 1*B^3 := mul_le_mul_of_nonneg_left hB3 (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*X) := mul_le_mul_of_nonneg_left hactive (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
      _ = _ := by rw [Real.exp_add]; ring
  have hCA : Real.exp (A+1)≤C := by dsimp [C,reopeningScaleConstant]; linarith [Real.exp_pos M]
  have hCM : Real.exp M≤C := by dsimp [C,reopeningScaleConstant]; linarith [Real.exp_pos (A+1)]
  have hinv : (X/B^3)⁻¹≤Real.exp A := by
    rw [inv_div]
    exact (div_le_iff₀ (by linarith : 0<X)).mpr hactive
  change 1≤C*Z^(κ+3) ∧ _
  refine ⟨hC.trans hCZ,hKcut.trans (hZ3.trans hbase),
    (hell.trans hXZ).trans (hZ3.trans hbase),?_,hFZ.trans (hZ3.trans hbase),
    hZκ.trans hbase,hCM.trans hCZ,?_,hinv.trans ((reopeningScaleConstant_exp A M).trans hCZ)⟩
  · exact hBsup.trans (mul_le_mul hCA hZ3 (by positivity) (by linarith))
  · calc
      _ ≤ Z^3*Real.exp M := mul_le_mul_of_nonneg_right (hell.trans hXZ) (Real.exp_pos _).le
      _ ≤ Z^(κ+3)*C := mul_le_mul hZ3 hCM (Real.exp_pos _).le (by positivity)
      _ = _ := mul_comm _ _

theorem globalFirstTailFactor_envelope (K ell B F U H : ℝ) (N : ℕ)
    (hK : 0≤K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F)
    (hU : 1≤U) (hH : 0≤H) (hKU : K≤U) (hiell : ell⁻¹≤U) :
    globalFirstTailFactor K ell B F U H N≤4096*U^20/(1+H)^N := by
  have hBi : B⁻¹≤1 := inv_le_one_of_one_le₀ hB
  have hFi : F⁻¹≤1 := inv_le_one_of_one_le₀ hF
  have hratio : K*U^2/(ell^2*B^2*F^2)≤U^5 := by
    calc
      _ = K*U^2*(ell⁻¹)^2*(B⁻¹)^2*(F⁻¹)^2 := by field_simp
      _ ≤ U*U^2*U^2*1^2*1^2 := by gcongr
      _ = _ := by ring
  have hone : 1+U≤2*U := by linarith
  have hinner : 1+(1+U)^3*(K*U^2/(ell^2*B^2*F^2))≤16*U^8 := by
    calc
      _ ≤ 1+(2*U)^3*U^5 := by gcongr
      _ = 1+8*U^8 := by ring
      _ ≤ _ := by have hh : 1≤U^8 := one_le_pow₀ hU; linarith
  unfold globalFirstTailFactor
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (2*U)^4*(16*U^8)^2 := by gcongr
    _ = _ := by ring

theorem globalFirstTailFactor_reopening_power (A M κ Z η X F Ksrc B : ℝ) (N : ℕ)
    (hκ : 0≤κ) (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (reopeningAuxiliaryScale A M κ Z) (Z^κ) N ≤
      (4096*(reopeningScaleConstant A M)^20)*Z^(20*(κ+3)-κ*N) := by
  have hZ0 : 0<Z := by linarith
  have hB0 : 0<B := by linarith
  have hX0 : 0<X := by linarith
  have hs := reopeningAuxiliaryScale_bounds A M κ Z η X F Ksrc B hκ hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  have hBsup : 1≤Real.exp 1*B := one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hbound := globalFirstTailFactor_envelope (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
    (reopeningAuxiliaryScale A M κ Z) (Z^κ) N (by positivity) (by positivity) hBsup hF hs.1
    (by positivity) hs.2.1 hs.2.2.2.2.2.2.2.2
  apply hbound.trans
  have hden : (Z^κ)^N≤(1+Z^κ)^N := pow_le_pow_left₀ (by positivity) (by linarith [Real.rpow_pos_of_pos hZ0 κ]) N
  calc
    _ ≤ 4096*(reopeningAuxiliaryScale A M κ Z)^20/(Z^κ)^N :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      unfold reopeningAuxiliaryScale
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_mul_natCast hZ0.le,
        Real.rpow_sub hZ0]
      ring_nf

theorem globalFirstTailFactor_reopening_arbitrary_decay (A M κ R : ℝ) (hκ : 0<κ) :
    ∃N : ℕ,0<N ∧ ∀Z η X F Ksrc B : ℝ,
      1≤Z → 0≤η → 1≤X → X≤Z^3 → 1≤F → F≤Z^3 →
      1≤Ksrc → Ksrc≤Z^3 → 1≤B → B^3≤Real.exp A*X →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
        (reopeningAuxiliaryScale A M κ Z) (Z^κ) N ≤
        (4096*(reopeningScaleConstant A M)^20)*Z^(-R) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((20*(κ+3)+R)/κ))
  have hN0 : 0<N := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hN
  have hNR : (20*(κ+3)+R)/κ<(N:ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hexp : 20*(κ+3)-κ*(N:ℝ)≤-R := by
    have hm := (div_lt_iff₀ hκ).mp hNR
    nlinarith
  refine ⟨N,hN0,?_⟩
  intro Z η X F Ksrc B hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  exact (globalFirstTailFactor_reopening_power A M κ Z η X F Ksrc B N hκ.le hZ hη
    hX hXZ hF hFZ hK hKZ hB hactive).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (by positivity))

theorem globalFirstTailFactor_reopening_nat_decay (A M Z η X F Ksrc B : ℝ) (R : ℕ)
    (hZ : 1≤Z) (hη : 0≤η)
    (hX : 1≤X) (hXZ : X≤Z^3) (hF : 1≤F) (hFZ : F≤Z^3)
    (hK : 1≤Ksrc) (hKZ : Ksrc≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (reopeningScaleConstant A M*Z^4) Z (R+80) ≤
      (4096*(reopeningScaleConstant A M)^20)*Z^(-(R:ℝ)) := by
  have h := globalFirstTailFactor_reopening_power A M 1 Z η X F Ksrc B (R+80)
    (by norm_num) hZ hη hX hXZ hF hFZ hK hKZ hB hactive
  have hpow : 20*((1:ℝ)+3)-1*((R+80:ℕ):ℝ)=-(R:ℝ) := by push_cast; ring
  rw [hpow] at h
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at h ⊢
  exact h

lemma reopening_cutoff_ratio (Z η Ksrc : ℝ) (hZ : 0<Z) (hK : 0<Ksrc) :
    Ksrc/(Ksrc/Z^η)=Z^η := by field_simp

lemma globalFirstRowCap_reopening_rpow (Z η X F Ksrc B deltaLoss : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B) (hδ : 0≤deltaLoss) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss ≤
      ((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss) := by
  have hcap : 0≤globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F := by
    unfold globalFirstRowCap
    positivity
  exact (Real.rpow_le_rpow hcap (le_max_right 1 _) hδ).trans
    (globalFirstRowCap_reopening_small_power Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ)

lemma reopening_cube_bound (A M Z X B : ℝ) (hZ : 1≤Z) (_hX : 1≤X)
    (hXZ : X≤Z^3) (hB : 1≤B) (hactive : B^3≤Real.exp A*X) :
    Real.exp 1*B≤reopeningScaleConstant A M*Z^3 := by
  have hB3 : B≤B^3 := by nlinarith [sq_nonneg (B-1)]
  have hC : Real.exp (A+1)≤reopeningScaleConstant A M := by
    unfold reopeningScaleConstant
    linarith [Real.exp_pos M]
  calc
    _ ≤ Real.exp 1*B^3 := mul_le_mul_of_nonneg_left hB3 (Real.exp_pos _).le
    _ ≤ Real.exp 1*(Real.exp A*X) := mul_le_mul_of_nonneg_left hactive (Real.exp_pos _).le
    _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
    _ = Real.exp (A+1)*Z^3 := by rw [Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (by positivity)

theorem reopening_diagonal_monomial (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hactive : B^3≤Real.exp A*X) (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      ((Real.exp 1*B)*(reopeningScaleConstant A M*Z^4))^ε ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M^2)^ε)*Z^(13*deltaLoss+7*ε) := by
  let C := reopeningScaleConstant A M
  have hC : 1≤C := reopeningScaleConstant_one A M
  have hb := reopening_cube_bound A M Z X B hZ hX hXZ hB hactive
  have hprod : (Real.exp 1*B)*(C*Z^4)≤C^2*Z^7 := by
    calc
      _ ≤ (C*Z^3)*(C*Z^4) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
  have hpow : ((Real.exp 1*B)*(C*Z^4))^ε≤(C^2)^ε*Z^(7*ε) := by
    apply (Real.rpow_le_rpow (by positivity) hprod hε).trans_eq
    rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
    norm_num
  have hcap := globalFirstRowCap_reopening_rpow Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ
  calc
    _ ≤ (((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss))*((C^2)^ε*Z^(7*ε)) :=
      mul_le_mul hcap hpow (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = _ := by rw [Real.rpow_add (by linarith : 0<Z)]; dsimp [C]; ring

theorem reopening_recursive_monomial (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hδ : 0≤deltaLoss) (_hε : 0≤ε) :
    (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M)^(deltaLoss+8*ε))*Z^(17*deltaLoss+32*ε) := by
  have hC : 0<reopeningScaleConstant A M := lt_of_lt_of_le zero_lt_one (reopeningScaleConstant_one A M)
  have he : (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε)=
      reopeningScaleConstant A M^(deltaLoss+8*ε)*Z^(4*deltaLoss+32*ε) := by
    rw [Real.mul_rpow hC.le (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
    congr 2
    ring
  rw [he]
  have hcap := globalFirstRowCap_reopening_rpow Z η X F Ksrc B deltaLoss hZ hη hη1 hX hXZ hF hFZ hK hB hδ
  calc
    _ ≤ (((Real.exp 1)^8)^deltaLoss*Z^(13*deltaLoss))*
      (reopeningScaleConstant A M^(deltaLoss+8*ε)*Z^(4*deltaLoss+32*ε)) :=
      mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = _ := by
      have hh : 17*deltaLoss+32*ε=13*deltaLoss+(4*deltaLoss+32*ε) := by ring
      rw [hh]
      simp only [Real.rpow_add (by linarith : 0<Z)]
      ring

theorem reopening_diagonal_with_ratio (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hactive : B^3≤Real.exp A*X) (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (Ksrc/(Ksrc/Z^η))*((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      ((Real.exp 1*B)*(reopeningScaleConstant A M*Z^4))^ε) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M^2)^ε)*Z^(η+13*deltaLoss+7*ε) := by
  rw [reopening_cutoff_ratio Z η Ksrc (by linarith) (by linarith)]
  apply (mul_le_mul_of_nonneg_left (reopening_diagonal_monomial A M Z η X F Ksrc B deltaLoss ε
    hZ hη hη1 hX hXZ hF hFZ hK hB hactive hδ hε) (by positivity)).trans_eq
  rw [show η+13*deltaLoss+7*ε=η+(13*deltaLoss+7*ε) by ring]
  simp only [Real.rpow_add (by linarith : 0<Z)]
  ring

theorem reopening_recursive_with_ratio (A M Z η X F Ksrc B deltaLoss ε : ℝ)
    (hZ : 1≤Z) (hη : 0≤η) (hη1 : η≤1) (hX : 1≤X) (hXZ : X≤Z^3)
    (hF : 1≤F) (hFZ : F≤Z^3) (hK : 1≤Ksrc) (hB : 1≤B)
    (hδ : 0≤deltaLoss) (hε : 0≤ε) :
    (Ksrc/(Ksrc/Z^η))*((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss *
      (reopeningScaleConstant A M*Z^4)^(deltaLoss+8*ε)) ≤
      (((Real.exp 1)^8)^deltaLoss*(reopeningScaleConstant A M)^(deltaLoss+8*ε))*Z^(η+17*deltaLoss+32*ε) := by
  rw [reopening_cutoff_ratio Z η Ksrc (by linarith) (by linarith)]
  apply (mul_le_mul_of_nonneg_left (reopening_recursive_monomial A M Z η X F Ksrc B deltaLoss ε
    hZ hη hη1 hX hXZ hF hFZ hK hB hδ hε) (by positivity)).trans_eq
  rw [show η+17*deltaLoss+32*ε=η+(17*deltaLoss+32*ε) by ring]
  simp only [Real.rpow_add (by linarith : 0<Z)]
  ring

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0242

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.ClosedRecursion
Source SHA256: caa7fc4fd36c3e1b3031ca71705320aff9c7c31a02d88538eeb029a680f37e72
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0243



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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

private theorem two_windows_bound (windows : Fin 7→ℝ→ℂ)
    (hc : ∀i,HasCompactSupport (windows i)) (hs : ∀i,Continuous (windows i)) :
    ∃Vmax : ℝ,0≤Vmax ∧ (∀t,‖windows 5 t‖≤Vmax) ∧ (∀t,‖windows 6 t‖≤Vmax) := by
  have hb (i : Fin 7) : ∃B : ℝ,0≤B ∧ ∀t,‖windows i t‖≤B := by
    obtain ⟨B,hB⟩ := ((hc i).isCompact_range (hs i)).bddAbove_image continuous_norm.continuousOn
    have he (t : ℝ) : ‖windows i t‖≤B := hB ⟨windows i t,⟨t,rfl⟩,rfl⟩
    exact ⟨B,(norm_nonneg _).trans (he 0),he⟩
  obtain ⟨B₅,h₅,hb₅⟩ := hb 5
  obtain ⟨B₆,h₆,hb₆⟩ := hb 6
  exact ⟨B₅+B₆,by linarith,fun t=>(hb₅ t).trans (by linarith),fun t=>(hb₆ t).trans (by linarith)⟩

theorem reopenedCanonicalRow_state_step
    (g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (N J Ntail : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ)
      (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ Clo Chi Vmax₁ Vmax₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧ 0<Clo ∧ 0<Chi ∧
      0≤Vmax₁ ∧ 0≤Vmax₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B H U Tmax E : ℝ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤Γ → 1≤E → 1≤U → 1≤B → 0≤H → 0≤Tmax →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      (X/B^3)*Real.exp M≤U → Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail≤Tmax →
      (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
      let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
           (ConcretePrimeRowBridge.idealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re≤
      B*(‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
      (Real.exp 5*Cfirst*Real.sqrt D₁*Real.sqrt D₂)*Γ^2*(X*F)^2*
        (Ksrc/(Ksrc/Z^η))*(globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss*
        U^(deltaLoss+8*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,htransfer⟩ :=
    reopenedCanonicalRow_nonzero_twoPassage g V M Nv hM hNv hgM hV hWin ε deltaLoss hε hδ (N+1) (2*J) Ntail
  obtain ⟨Clo,Chi,hClo,hChi,hbudget⟩ := globalFirstQuantitativeBudget_bounded deltaLoss hδ ε hε
  obtain ⟨Vmax₁,hVmax₁,hw₁₅,hw₁₆⟩ := two_windows_bound w₁ hwc₁ (fun i=>(hws₁ i).continuous)
  obtain ⟨Vmax₂,hVmax₂,hw₂₅,hw₂₆⟩ := two_windows_bound w₂ hwc₂ (fun i=>(hws₂ i).continuous)
  have hwb₁' : ∀i t,w₁ i t≠0→|t|≤M+7 := by convert hwb₁ using 1 ; ring_nf
  have hwb₂' : ∀i t,w₂ i t≠0→|t|≤M+7 := by convert hwb₂ using 1 ; ring_nf
  refine ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,Clo,Chi,Vmax₁,Vmax₂,
    hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,hClo,hChi,hVmax₁,hVmax₂,
    hwc₁,hws₁,hwb₁',hwc₂,hws₂,hwb₂',?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool Q β
    Γ t B H U Tmax E hbase hpbad hZ hZbig hη hηsmall hΓ hE hU hB hH hTmax hKU hellU hBU hHU heU
    hMU hprogress hβ hQ hQB htail hterminal ih
  dsimp only
  have hX:=hstate.column_pos
  have hF0 : 0<F:=zero_lt_one.trans_le hstate.label_ge_one
  have hK0 : 0<Ksrc:=zero_lt_one.trans_le hstate.row_ge_one
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hell : 0<X/B^3:=div_pos hX (pow_pos hB0 _)
  have hKcut : 0<Ksrc/Z^η:=div_pos hK0 (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  have hBsup : 1≤Real.exp 1*B:=one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hΨ : ∀u,‖Ψ u‖≤1:=fun u=>hstate.coefficient.norm_le hbase u
  have he := htransfer p hp hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc (Ksrc/Z^η)
    (X/B^3) (Real.exp 1*B) F H U hΓ hK0 hKcut hell hBsup hF0 hH hU hMU hΨ hβ hQ hQB
    (fun I hI=>(hstate.label_bounds I hI).2.1) (fun I hI=>(hstate.label_bounds I hI).2.2.2)
  let blocks:=canonicalSourceBlocks pool (reopenedCubeFamily Q)
  have hb₁ : ∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B:=
    fun b hb=>(canonicalSourceBlocks_cube_norms p pool (reopenedCubeFamily Q) (Real.exp 1*B)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).1)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).2) b hb).1
  have hb₂ : ∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B:=
    fun b hb=>(canonicalSourceBlocks_cube_norms p pool (reopenedCubeFamily Q) (Real.exp 1*B)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).1)
      (fun c hc=>(reopenedCubeFamily_cube_norms p Q _ hQB c hc).2) b hb).2
  have hbL:=hbudget p hp hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks true w₁
    C₁ Cd₁ Ct₁ Tmax (Γ^2) E t B M H U (M+7) Vmax₁ N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC₁ hCd₁.le hCt₁.le hTmax (sq_nonneg Γ) hE hU hB hH
    hKU hellU hBU hHU heU hprogress (by linarith) hVmax₁ hw₁₅ hw₁₆ (hwb₁' 5) (hwb₁' 6)
    hb₁ hb₂ htail hterminal (ih true)
  have hbR:=hbudget p hp hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks false w₂
    C₂ Cd₂ Ct₂ Tmax (Γ^2) E t B M H U (M+7) Vmax₂ N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC₂ hCd₂.le hCt₂.le hTmax (sq_nonneg Γ) hE hU hB hH
    hKU hellU hBU hHU heU hprogress (by linarith) hVmax₂ hw₂₅ hw₂₆ (hwb₂' 5) (hwb₂' 6)
    hb₁ hb₂ htail hterminal (ih false)
  let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
  let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
  have hD₁ : 0≤D₁:=canonicalBudgetCoefficient_nonneg _ _ _ _ _ _ _ _ hC₁ hCd₁.le hCt₁.le hTmax hClo.le hChi.le
  have hD₂ : 0≤D₂:=canonicalBudgetCoefficient_nonneg _ _ _ _ _ _ _ _ hC₂ hCd₂.le hCt₂.le hTmax hClo.le hChi.le
  have hpairs:=canonicalPairBudget_normalized X F B Ksrc (Ksrc/Z^η) Cf
    ((globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss) U (deltaLoss+8*ε) E t
    (D₁*Γ^2) (D₂*Γ^2) _ _ J hX hF0.le hB0 hK0.le hKcut hCf
    (Real.rpow_nonneg (globalFirstRowCap_pos _ _ _ _ hKcut hell (zero_lt_one.trans_le hBsup) hF0).le _)
    (zero_le_one.trans hU) (zero_le_one.trans hE) (mul_nonneg hD₁ (sq_nonneg Γ)) (mul_nonneg hD₂ (sq_nonneg Γ))
    (by simpa only [mul_assoc] using hbL) (by simpa only [mul_assoc] using hbR)
  have hsqrt : Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)=Real.sqrt D₁*Real.sqrt D₂*Γ^2 := by
    rw [Real.sqrt_mul hD₁,Real.sqrt_mul hD₂,Real.sqrt_sq_eq_abs]
    calc
      _ = Real.sqrt D₁*Real.sqrt D₂*(|Γ|^2) := by ring
      _ = _ := by rw [sq_abs]
  have hscaled:=mul_le_mul_of_nonneg_left he hB0.le
  calc
    _ ≤ B*(‖canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
        (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (X/B^3)‖+
       ‖canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
        (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
       B*((X/B^3)*(Real.exp 1*B)^2*F*(Ksrc/(Ksrc/Z^η))*Cf*
         (globalFirstRowCap (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F)^deltaLoss*
         Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ t) m w₁
           C₁ Cd₁ Ct₁ (Γ^2) ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail true)*
         Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ t) m w₂
           C₂ Cd₂ Ct₂ (Γ^2) ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail false)) :=
      hscaled.trans_eq (by ring)
    _ ≤ _ := by
      apply (add_le_add le_rfl hpairs).trans_eq
      calc
        _ = _ := by rw [show Real.exp 5*Cf*Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)=
            Real.exp 5*Cf*(Real.sqrt (D₁*Γ^2)*Real.sqrt (D₂*Γ^2)) by ring,hsqrt];ring

theorem reopenedCanonicalRow_polynomial_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0≤C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B E : ℝ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 →
      0≤Γ → 1≤E → 1≤B → B^3≤Real.exp A*X →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
           (ConcretePrimeRowBridge.idealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re≤
      B*(‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)+
      C*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨N,hN,hterminal⟩ := reopening_terminal_order η 0 hη
  obtain ⟨w₁,w₂,Cf,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,Clo,Chi,Vmax₁,Vmax₂,
    hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,hClo,hChi,hV₁,hV₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_state_step g V M Nv hM hNv hgM hV hWin ε deltaLoss hε hδ N J 80
  let Cs:=reopeningScaleConstant A M
  let Tmax:=4096*Cs^20
  have hCs : 1≤Cs:=reopeningScaleConstant_one A M
  have hTmax : 0≤Tmax:=by dsimp [Tmax]; positivity
  let D₁:=canonicalBudgetCoefficient C₁ Cd₁ Ct₁ Tmax Clo Chi (M+7) Vmax₁
  let D₂:=canonicalBudgetCoefficient C₂ Cd₂ Ct₂ Tmax Clo Chi (M+7) Vmax₂
  let Cbase:=Real.exp 5*Cf*Real.sqrt D₁*Real.sqrt D₂
  let Cpow:=((Real.exp 1)^8)^deltaLoss*Cs^(deltaLoss+8*ε)
  have hCbase : 0≤Cbase:=by dsimp [Cbase]; positivity
  have hCpow : 0≤Cpow:=by dsimp [Cpow]; positivity
  refine ⟨w₁,w₂,Cbase*Cpow,mul_nonneg hCbase hCpow,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B E hbase hpbad hZ hZbig hX hXZ hFZ hΓ hE hB hactive hprogress hβ hQ hQB ih
  have hs:=reopeningAuxiliaryScale_bounds A M 1 Z η X F Ksrc B (by norm_num) hZ.le hη.le
    hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at hs
  obtain ⟨hU,hKU,hellU,hBU,hFU,hHU,heU,hMU,hiU⟩:=hs
  have htail : globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F
      (Cs*Z^4) Z 80≤Tmax := by
    have hh:=globalFirstTailFactor_reopening_nat_decay A M Z η X F Ksrc B 0
      hZ.le hη.le hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
    simpa only [Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one,zero_add] using hh
  have ht : (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 := by
    simpa only [neg_zero,Real.rpow_zero] using hterminal Z Ksrc hZ.le
      (zero_le_one.trans hstate.row_ge_one) hstate.row_le_global
  have hb:=hstep p hp hcop hg hc hinj hpr base bad Z η Ψ m labels X F Ksrc hstate pool Q β
    Γ t B Z (Cs*Z^(4:ℕ)) Tmax E hbase hpbad hZ hZbig hη.le hηsmall hΓ hE hU hB
    (zero_le_one.trans hZ.le) hTmax hKU hellU hBU hHU heU hMU hprogress hβ hQ hQB htail ht ih
  dsimp only at hb ⊢
  have hm:=reopening_recursive_with_ratio A M Z η X F Ksrc B deltaLoss ε hZ.le hη.le
    (by linarith) hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hB hδ.le hε.le
  have hx := mul_le_mul_of_nonneg_left hm
    (show 0≤Cbase*Γ^2*(X*F)^2*E*(1+‖t‖)^(2*J) by positivity)
  apply hb.trans
  apply add_le_add le_rfl
  convert hx using 1 <;> dsimp [Cbase,Cpow,D₁,D₂,Cs] <;> ring

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

theorem reopenedCanonicalFirstErrors_power
    (g : 𝓢(ℝ,ℂ)) (A M : ℝ) (hgM : ∀t,g t≠0→|t|≤M)
    (ε η : ℝ) (hε : 0<ε) (hη : 0<η) (hbudget : 3000*η≤(1:ℝ)/40) :
    ∃C : ℝ,0≤C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B : ℝ),
      (∀u,‖base u‖≤1) → 1≤Z → 1≤X → X≤Z^3 → F≤Z^3 →
      0≤Γ → 1≤B → B^3≤Real.exp A*X →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      B*(‖canonicalSourceZero p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (X/B^3)‖+
         ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖)≤
      C*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
  obtain ⟨N,hN,horder⟩:=canonicalFirstTail_reopening_order η ε ((1:ℝ)/40) hη hε.le
  obtain ⟨Cz,Ct,hCz,hCt,herrors⟩:=reopenedCanonicalFirstErrors g M hgM ε hε N
  let Cs:=reopeningScaleConstant A M
  have hCs : 1≤Cs:=reopeningScaleConstant_one A M
  let Cz':=Cz*(Real.exp 1)^(1+ε)*Cs^ε
  let Ct':=4*Ct*(Real.exp (2*M))^N*Cs^(25+ε)
  have hCz' : 0≤Cz':=by dsimp [Cz']; positivity
  have hCt' : 0≤Ct':=by dsimp [Ct']; positivity
  refine ⟨Cz'+Ct',add_nonneg hCz' hCt',?_⟩
  intro ι _ p hp _ hcop hg hinj hc base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B hbase hZ hX hXZ hFZ hΓ hB hactive hβ hQB
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hX0 : 0<X:=zero_lt_one.trans_le hX
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hK0 : 0<Ksrc:=zero_lt_one.trans_le hstate.row_ge_one
  have hF0 : 0<F:=zero_lt_one.trans_le hstate.label_ge_one
  have hs:=reopeningAuxiliaryScale_bounds A M 1 Z η X F Ksrc B (by norm_num) hZ hη.le
    hX hXZ hstate.label_ge_one hFZ hstate.row_ge_one hstate.row_le_global hB hactive
  norm_num [reopeningAuxiliaryScale,Real.rpow_natCast] at hs
  obtain ⟨hU,hKU,hellU,hBU,hFU,hHU,heU,hMU,hiU⟩:=hs
  let U:=Cs*Z^(4:ℕ)
  have hBsup : 1≤Real.exp 1*B:=one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hB
  have hB0U : B≤U := (le_mul_of_one_le_left hB0.le (Real.one_le_exp (by norm_num))).trans hBU
  have hKsrcU : Ksrc≤U := by
    calc
      _ ≤ Z^3:=hstate.row_le_global
      _ ≤ Z^4:=by nlinarith [sq_nonneg Z,show 0≤Z^2*(Z-1)^2 by positivity]
      _ ≤ U:=le_mul_of_one_le_left (by positivity) hCs
  have herr:=herrors p hp hcop hg hinj hc pool Q labels β Ψ m Γ t Ksrc (Ksrc/Z^η)
    (X/B^3) (Real.exp 1*B) F U hΓ hK0 (by positivity) (by positivity) hBsup
    hstate.label_ge_one hU hMU (fun u=>hstate.coefficient.norm_le hbase u) hβ hQB
    (fun I hI=>(hstate.label_bounds I hI).1) (fun I hI=>(hstate.label_bounds I hI).2.2.2)
  dsimp only at herr ⊢
  have hzero:=canonicalFirstZero_normalization Cz Γ X F Ksrc B Z ε hCz hX0 hF0.le hK0.le hB
    (hstate.row_bound hZ hη.le hbudget)
  have hBpow : B^ε≤Cs^ε*Z^(3*ε) := by
    have hh : B≤Cs*Z^3 := (le_mul_of_one_le_left hB0.le (Real.one_le_exp (by norm_num))).trans
      (reopening_cube_bound A M Z X B hZ hX hXZ hB hactive)
    apply (Real.rpow_le_rpow hB0.le hh hε.le).trans_eq
    rw [Real.mul_rpow (by linarith) (by positivity),←Real.rpow_natCast_mul hZ0.le]
    norm_num
  have hz : B*‖canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (X/B^3)‖≤
      Cz'*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
    apply ((mul_le_mul_of_nonneg_left herr.1 hB0.le).trans hzero).trans
    calc
      _ ≤ (Cz*(Real.exp 1)^(1+ε))*(Cs^ε*Z^(3*ε))*Γ^2*(X*F)^2*Z^(-((1:ℝ)/40)) := by gcongr
      _ = _ := by rw [show 3*ε-(1:ℝ)/40=3*ε+(-((1:ℝ)/40)) by ring,Real.rpow_add hZ0]; dsimp [Cz']; ring
  have ht0:=horder Cs Ct Γ B (Real.exp 1*B) U F Ksrc Z M hCs hCt hB0.le
    (by positivity) (by positivity) hF0.le hstate.row_ge_one hZ hB0U hBU le_rfl hFU hKsrcU
  have ht : B*‖canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc (Ksrc/Z^η) (X/B^3)‖≤
      Ct'*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40) := by
    have hpow : Z^(-((1:ℝ)/40))≤Z^(3*ε-(1:ℝ)/40):=
      Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    have hXF : 1≤(X*F)^2:=one_le_pow₀ (one_le_mul_of_one_le_of_one_le hX hstate.label_ge_one)
    apply ((mul_le_mul_of_nonneg_left herr.2 hB0.le).trans ht0).trans
    calc
      _ = Ct'*Γ^2*Z^(-((1:ℝ)/40)):=by dsimp [Ct']; ring
      _ ≤ Ct'*Γ^2*((X*F)^2*Z^(3*ε-(1:ℝ)/40)):=by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCt' (sq_nonneg Γ))
        exact hpow.trans (le_mul_of_one_le_left (by positivity) hXF)
      _ = _:=by ring
  rw [mul_add]
  exact (add_le_add hz ht).trans_eq (by ring)

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

theorem reopenedCanonicalRow_closed_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η) (hηsmall : η≤(1:ℝ)/1000)
    (hbudget : 3000*η≤(1:ℝ)/40) (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0≤C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hpr : ∀i,lambda^2∣p i-1)
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ)
      (Γ t B E : ℝ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 →
      0≤Γ → 1≤E → 1≤B → B^3≤Real.exp A*X →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B) →
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      B*(∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
           (ConcretePrimeRowBridge.idealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p (X/B^3) S))) Ksrc).re≤
      C*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖t‖)^(2*J) := by
  obtain ⟨w₁,w₂,Cp,hCp,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_polynomial_step g V A M Nv hM hNv hgM hV hWin ε deltaLoss η hε hδ hη hηsmall J
  obtain ⟨Ce,hCe,herrors⟩:=reopenedCanonicalFirstErrors_power g A M hgM ε η hε hη hbudget
  refine ⟨w₁,w₂,Ce+Cp,add_nonneg hCe hCp,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hcop hg hc hinj hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B E hbase hpbad hZ hZbig hX hXZ hFZ hΓ hE hB hactive hprogress hβ hQ hQB ih
  have hpstep:=hstep p hp hcop hg hc hinj hpr base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B E hbase hpbad hZ hZbig hX hXZ hFZ hΓ hE hB hactive hprogress hβ hQ hQB ih
  have herr:=herrors p hp hcop hg hinj hc base bad Z Ψ m labels X F Ksrc hstate pool Q β
    Γ t B hbase hZ.le hX hXZ hFZ hΓ hB hactive hβ hQB
  dsimp only at hpstep herr
  have hpow : Z^(3*ε-(1:ℝ)/40)≤Z^(η+17*deltaLoss+32*ε):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hEH : 1≤E*(1+‖t‖)^(2*J):=
    one_le_mul_of_one_le_of_one_le hE (one_le_pow₀ (by linarith [norm_nonneg t]))
  have he : Ce*Γ^2*(X*F)^2*Z^(3*ε-(1:ℝ)/40)≤
      Ce*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖t‖)^(2*J) := by
    calc
      _ ≤ Ce*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε):=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (Ce*Γ^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε))*(E*(1+‖t‖)^(2*J)):=
        le_mul_of_one_le_right (by positivity) hEH
      _ = _:=by ring
  apply hpstep.trans
  exact (add_le_add (herr.trans he) le_rfl).trans_eq (by ring)

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CompletedGauss
open ActualEisensteinCubic UniqueFactorizationMonoid

theorem nonresidual_count_eq_on_fiber (I J Q P : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    (normalizedFactors I).count P=(normalizedFactors J).count P := by
  have ha := congrArg (fun A : Ideal ActualEisensteinCubic.O=>(normalizedFactors A).count P) hA
  simp only [normalizedFactors_rowPowerfulPart,Multiset.count_filter] at ha
  have ht := congrArg (fun A : Ideal ActualEisensteinCubic.O=>(normalizedFactors A).count P) hT
  simp only [rowMaskPart,normalizedFactors_squarefreeMaskPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at ht
  have hr0 : (normalizedFactors (rowResidualPart I Q)).count P=0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp hm).2
  simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at hr0
  by_cases hpq : P∣Q
  · simp only [hpq,ite_true] at ht
    by_cases hi : 2≤(normalizedFactors I).count P <;>
      by_cases hj : 2≤(normalizedFactors J).count P <;> simp only [hi,hj,ite_true,ite_false,not_true_eq_false,not_false_eq_true] at ha ht <;> omega
  · have hpi : P∣I := (hP.dvd_mul.mp hpool).resolve_right hpq
    have hci : 0<(normalizedFactors I).count P :=
      Multiset.count_pos.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hpi⟩)
    simp only [hpq,not_false_eq_true,ite_true] at hr0
    by_cases hi : 2≤(normalizedFactors I).count P <;>
      by_cases hj : 2≤(normalizedFactors J).count P <;> simp only [hi,hj,ite_true,ite_false,not_true_eq_false,not_false_eq_true] at ha hr0 <;> omega

theorem nonresidual_prime_transport (I J F Q P : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hJ : J≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    P∣J*Q ∧ ¬P∣rowResidualPart J Q ∧ completedLocalExponent I F P=completedLocalExponent J F P := by
  have hc := nonresidual_count_eq_on_fiber I J Q P hI hP hA hT hpool hr
  have hpoolJ : P∣J*Q := by
    rcases hP.dvd_mul.mp hpool with hi|hq
    · have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hi⟩
      have hcj : 0<(normalizedFactors J).count P := hc ▸ Multiset.count_pos.mpr hm
      exact dvd_mul_of_dvd_left ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hJ).mp (Multiset.count_pos.mp hcj)).2 Q
    · exact dvd_mul_of_dvd_right hq J
  have hrc : (normalizedFactors (rowResidualPart I Q)).count P=
      (normalizedFactors (rowResidualPart J Q)).count P := by
    simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
      normalizedFactors_rowSimplePart,Multiset.count_filter,hc]
  refine ⟨hpoolJ,?_,?_⟩
  · intro hd
    have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart J) Q)).mpr ⟨hP,hd⟩
    have hp : 0<(normalizedFactors (rowResidualPart I Q)).count P := hrc.symm ▸ Multiset.count_pos.mpr hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp
      (Multiset.count_pos.mp hp)).2
  · simp only [completedLocalExponent,hc]

lemma completedResidualScale_eq_on_fiber (K : ℝ) (I J Q : Ideal ActualEisensteinCubic.O)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q) :
    completedResidualScale K I Q=completedResidualScale K J Q := by
  simp only [completedResidualScale,hA,hT]

end CompletedGauss

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace E] in
lemma compact_estimate_prod_antilipschitz (T : E→L[ℂ]F) (K : E→L[ℂ]G) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    ∃D : NNReal,AntilipschitzWith D (T.prod K) := by
  let R := max A 0+max B 0
  have hR : 0≤R := add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨⟨Real.sqrt R,Real.sqrt_nonneg _⟩,(T.prod K).antilipschitz_of_bound (fun u => ?_)⟩
  have hT : ‖T u‖^2≤‖(T.prod K) u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_fst_le (T u,K u))
  have hK : ‖K u‖^2≤‖(T.prod K) u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_snd_le (T u,K u))
  have hh : ‖u‖^2≤R*‖(T.prod K) u‖^2 := calc
    _ ≤A*‖T u‖^2+B*‖K u‖^2 := hest u
    _ ≤max A 0*‖T u‖^2+max B 0*‖K u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    _ ≤max A 0*‖(T.prod K) u‖^2+max B 0*‖(T.prod K) u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hT (le_max_right _ _))
        (mul_le_mul_of_nonneg_left hK (le_max_right _ _))
    _ = _ := by dsimp only [R]; ring
  change ‖u‖≤Real.sqrt R*‖(T.prod K) u‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow,Real.sq_sqrt hR] using hh

lemma finiteDimensional_ker_of_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    FiniteDimensional ℂ T.ker := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  have hc : IsCompactOperator (K.comp T.ker.subtypeL) := hK.comp_clm T.ker.subtypeL
  have hid : IsCompactOperator (ContinuousLinearMap.id ℂ T.ker) := by
    apply compact_of_norm_le_compact _ _ hc
    refine ⟨Real.sqrt (max B 0),fun u => ?_⟩
    have ht : T (u:E)=0 := u.2
    have hh := hest (u:E)
    rw [ht,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_add] at hh
    have hh' : ‖u‖^2≤max B 0*‖K (u:E)‖^2 :=
      hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    change ‖u‖≤Real.sqrt (max B 0)*‖K (u:E)‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow,Real.sq_sqrt (le_max_right B 0)] using hh'
  exact FiniteDimensional.of_isCompactOperator_id hid

lemma antilipschitz_of_injective_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) (hT : Function.Injective T) :
    ∃D : NNReal,AntilipschitzWith D T := by
  by_contra hanti
  have hex (ε : ℝ) (hε : 0<ε) : ∃u : E,‖u‖=1 ∧ ‖T u‖<ε := by
    by_contra! hn
    apply hanti
    refine ⟨⟨ε⁻¹,inv_nonneg.mpr hε.le⟩,antilipschitz_of_bound_of_norm_one T (fun u hu => ?_)⟩
    change 1≤ε⁻¹*‖T u‖
    have hh := mul_le_mul_of_nonneg_left (hn u hu) (inv_nonneg.mpr hε.le)
    simpa only [inv_mul_cancel₀ hε.ne'] using hh
  obtain ⟨eps,hepsAnti,hepsPos,heps⟩ := exists_seq_strictAnti_tendsto (0:ℝ)
  choose u hunorm huT using fun n : ℕ => hex (eps n) (hepsPos n)
  have huTlim : Tendsto (fun n => T (u n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (huT n).le) heps
  obtain ⟨S,hS,hsub⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨k,hk,seq,hseq,hklim⟩ := hS.tendsto_subseq
    (fun n => hsub ⟨u n,by simp only [Metric.mem_closedBall,dist_zero_right,hunorm,le_refl],rfl⟩)
  let P := T.prod K
  obtain ⟨D,hD⟩ := compact_estimate_prod_antilipschitz T K A B hest
  have hlim : Tendsto (fun n => P (u (seq n))) atTop (𝓝 (0,k)) :=
    (huTlim.comp hseq.tendsto_atTop).prodMk_nhds hklim
  have hmem : (0,k)∈Set.range P :=
    (hD.isClosed_range P.uniformContinuous).mem_of_tendsto hlim
      (Eventually.of_forall (fun n => ⟨u (seq n),rfl⟩))
  obtain ⟨v,hv⟩ := hmem
  have hvlim : Tendsto (fun n => u (seq n)) atTop (𝓝 v) := by
    apply (hD.isInducing P.continuous).tendsto_nhds_iff.mpr
    change Tendsto (fun n => P (u (seq n))) atTop (𝓝 (P v))
    rw [hv]
    exact hlim
  have hvzero : v=0 := hT (by
    have hh := congrArg Prod.fst hv
    change T v=0 at hh
    simpa only [map_zero] using hh)
  have hnorm : ‖v‖=1 := tendsto_nhds_unique hvlim.norm (by simpa only [hunorm] using tendsto_const_nhds)
  rw [hvzero,norm_zero] at hnorm
  norm_num at hnorm

end CubicEisenstein

end

end OAI
end OAIOriginalModule0243

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.FredholmAlternative
Source SHA256: f21621cb451f18d949dcd949897df2fbd30ea2552b894293aa60a78fb0bc36f7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0244


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

section

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace E] in
lemma ker_orthogonal_restriction_injective (T : E→L[ℂ]F) :
    Function.Injective (T.domRestrict T.kerᗮ) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  apply Subtype.ext
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  exact T.ker.inner_right_of_mem_orthogonal hu u.2

lemma ker_orthogonal_restriction_range (T : E→L[ℂ]F) :
    Set.range (T.domRestrict T.kerᗮ)=Set.range T := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  apply Set.Subset.antisymm
  · rintro _ ⟨u,rfl⟩
    exact ⟨u.1,rfl⟩
  · rintro _ ⟨u,rfl⟩
    refine ⟨⟨u-T.ker.starProjection u,T.ker.sub_starProjection_mem_orthogonal u⟩,?_⟩
    change T (u-T.ker.starProjection u)=T u
    rw [map_sub]
    have hz : T (T.ker.starProjection u)=0 := T.ker.starProjection_apply_mem u
    rw [hz,sub_zero]

lemma ker_orthogonal_restriction_antilipschitz (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    ∃D : NNReal,AntilipschitzWith D (T.domRestrict T.kerᗮ) := by
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  apply antilipschitz_of_injective_compact_estimate (T.domRestrict T.kerᗮ)
    (K.domRestrict T.kerᗮ) (hK.comp_clm T.kerᗮ.subtypeL) A B
      (fun u => hest u) (ker_orthogonal_restriction_injective T)

lemma closed_range_of_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) : IsClosed (Set.range T) := by
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  rw [←ker_orthogonal_restriction_range T]
  exact hD.isClosed_range (T.domRestrict T.kerᗮ).uniformContinuous

lemma selfAdjoint_range_eq_ker_orthogonal (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (hrange : IsClosed (Set.range T)) : T.range=T.kerᗮ := by
  have hh := T.orthogonal_ker
  rw [hT.adjoint_eq] at hh
  rw [hrange.submodule_topologicalClosure_eq] at hh
  exact hh.symm

end

section
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

lemma selfAdjoint_fredholm_of_compact_estimate (T : E→L[ℂ]E) (hT : IsSelfAdjoint T)
    (K : E→L[ℂ]G) (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) : T.IsFredholm := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  let : FiniteDimensional ℂ T.ker := finiteDimensional_ker_of_compact_estimate T K hK A B hest
  let : T.kerᗮ.CoFG :=
    (T.kerᗮ.quotientEquivOfIsCompl T.ker T.ker.isCompl_orthogonal.symm).symm.finiteDimensional
  have hrange := closed_range_of_compact_estimate T K hK A B hest
  have heq := selfAdjoint_range_eq_ker_orthogonal T hT hrange
  let : T.range.CoFG := heq.symm ▸ (inferInstance : T.kerᗮ.CoFG)
  obtain ⟨D,hD⟩ := ker_orthogonal_restriction_antilipschitz T K hK A B hest
  let : CompleteSpace T.kerᗮ := T.ker.isClosed_orthogonal.completeSpace_coe
  have hf : (T.domRestrict T.kerᗮ).IsFredholm := by
    apply (hD.isClosedEmbedding (T.domRestrict T.kerᗮ).uniformContinuous).isFredholm
    have he : (T.domRestrict T.kerᗮ).range=T.range := by
      apply SetLike.coe_injective
      exact ker_orthogonal_restriction_range T
    rw [he]
    infer_instance
  exact (ContinuousLinearMap.isFredholm_domRestrict_iff T.ker.isClosed_orthogonal).mp hf

end

def kernelSpectralFormOperator (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  ContinuousLinearMap.id ℂ KernelEnergyGraph-
    (z+1)•(kernelEnergyMass.adjoint.comp kernelEnergyMass)

lemma kernelSpectralFormOperator_inner (z : ℂ) (u : KernelEnergyGraph) :
    inner ℂ u (kernelSpectralFormOperator z u)=
      ((‖kernelEnergyGradient u‖^2:ℝ):ℂ)-z*((‖kernelEnergyMass u‖^2:ℝ):ℂ) := by
  change inner ℂ u (u-(z+1)•kernelEnergyMass.adjoint (kernelEnergyMass u))=_
  rw [inner_sub_right,inner_smul_right u (kernelEnergyMass.adjoint (kernelEnergyMass u)) (z + 1),kernelEnergyMass.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelEnergyGraph_norm_sq,Complex.ofReal_add]
  ring

lemma kernelSpectralFormOperator_selfAdjoint (spectralParam : ℝ) :
    IsSelfAdjoint (kernelSpectralFormOperator (spectralParam:ℂ)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  apply (LinearMap.isSymmetric_iff_inner_map_self_real _).mpr
  intro u
  have hh := kernelSpectralFormOperator_inner (spectralParam:ℂ) u
  have hr : inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u=
      (((‖kernelEnergyGradient u‖^2-spectralParam*‖kernelEnergyMass u‖^2):ℝ):ℂ) := by
    rw [←inner_conj_symm,kernelSpectralFormOperator_inner]
    simp only [map_sub,map_mul,Complex.conj_ofReal,Complex.ofReal_sub,Complex.ofReal_mul]
  change (starRingEnd ℂ) (inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u)=
    inner ℂ (kernelSpectralFormOperator (spectralParam:ℂ) u) u
  rw [hr,Complex.conj_ofReal]

lemma scalar_compact_energy_estimate (m g n t k spectralParam C : ℝ)
    (_hn : 0≤n) (_ht : 0≤t) (hspectralParam : 0≤spectralParam) (hspectralParamone : spectralParam<1) (hC : 0≤C)
    (hspace : n^2=m^2+g^2) (hcore : m^2≤g^2+C*k^2)
    (hform : g^2-spectralParam*m^2≤n*t) :
    n^2≤(4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2 := by
  have hd : 0<1-spectralParam := sub_pos.mpr hspectralParamone
  have hlow : (1-spectralParam)/2*n^2≤n*t+C*k^2 := by
    nlinarith [mul_nonneg (show 0≤1+spectralParam by linarith) (sub_nonneg.mpr hcore),
      mul_nonneg hd.le (mul_nonneg hC (sq_nonneg k))]
  have hlow' := mul_le_mul_of_nonneg_left hlow (show 0≤4*(1-spectralParam) by positivity)
  have hsq : (1-spectralParam)^2*n^2≤4*t^2+4*(1-spectralParam)*C*k^2 := by
    nlinarith [sq_nonneg ((1-spectralParam)*n-2*t)]
  have he : (4/(1-spectralParam)^2)*t^2+(4*C/(1-spectralParam))*k^2=
      (4*t^2+4*(1-spectralParam)*C*k^2)/(1-spectralParam)^2 := by
    field_simp [hd.ne']
  rw [he]
  exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr (by nlinarith [hsq])

lemma kernelSpectralFormOperator_compact_estimate
    (K : Set KernelQuotient) (hK : MeasurableSet K) (C : ℝ) (hC : 0≤C)
    (hcore : ∀u : KernelEnergyGraph,‖kernelEnergyMass u‖^2≤‖kernelEnergyGradient u‖^2+
      C*‖kernelEnergyMassRestriction K hK u‖^2)
    (spectralParam : ℝ) (hspectralParam : 0≤spectralParam) (hspectralParamone : spectralParam<1) (u : KernelEnergyGraph) :
    ‖u‖^2≤(4/(1-spectralParam)^2)*‖kernelSpectralFormOperator (spectralParam:ℂ) u‖^2+
      (4*C/(1-spectralParam))*‖kernelEnergyMassRestriction K hK u‖^2 := by
  apply scalar_compact_energy_estimate ‖kernelEnergyMass u‖ ‖kernelEnergyGradient u‖
    ‖u‖ ‖kernelSpectralFormOperator (spectralParam:ℂ) u‖ ‖kernelEnergyMassRestriction K hK u‖ spectralParam C
    (norm_nonneg _) (norm_nonneg _) hspectralParam hspectralParamone hC (kernelEnergyGraph_norm_sq u) (hcore u)
  have hh := re_inner_le_norm (𝕜 := ℂ) u (kernelSpectralFormOperator (spectralParam:ℂ) u)
  rw [kernelSpectralFormOperator_inner] at hh
  simpa only [RCLike.re_to_complex,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero] using hh

lemma kernelSpectralFormOperator_solution_graph (z : ℂ) (F : KernelQuotientL2)
    (v : KernelEnergyGraph) (hv : kernelSpectralFormOperator z v=kernelVariationalSolution F) :
    (kernelEnergyMass v,F+z•kernelEnergyMass v)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  have hh : v-(z+1)•kernelEnergyMass.adjoint (kernelEnergyMass v)=kernelEnergyMass.adjoint F := hv
  have hv' : kernelEnergyMass.adjoint (F+(z+1)•kernelEnergyMass v)=v := by
    rw [map_add,map_smul]
    exact (sub_eq_iff_eq_add.mp hh).symm
  have he : kernelEnergyMass v+(F+z•kernelEnergyMass v)=F+(z+1)•kernelEnergyMass v := by
    rw [add_smul,one_smul]
    abel
  rw [he]
  change kernelEnergyMass (kernelEnergyMass.adjoint (F+(z+1)•kernelEnergyMass v))=kernelEnergyMass v
  rw [hv']

lemma kernelSpectralFormOperator_of_domain (z : ℂ) (u : kernelEnergyLaplacian.domain) :
    kernelSpectralFormOperator z (kernelVariationalSolution (kernelEnergyLaplacian u+u))=
      kernelVariationalSolution (kernelEnergyLaplacian u-z•(u:KernelQuotientL2)) := by
  have hu : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  change kernelVariationalSolution (kernelEnergyLaplacian u+u)-
    (z+1)•kernelVariationalSolution (kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u)))=_
  rw [hu,←map_smul,←map_sub]
  congr 1
  rw [add_smul,one_smul]
  abel

theorem kernelSpectralFormOperator_isFredholm (spectralParam : ℝ)
    (hzero : 0≤spectralParam) (hone : spectralParam<1) :
    (kernelSpectralFormOperator (spectralParam:ℂ)).IsFredholm := by
  obtain ⟨K,hK,C,hC,hcompact,hcoercive⟩ := kernel_global_exterior_coercivity
  exact selfAdjoint_fredholm_of_compact_estimate _
    (kernelSpectralFormOperator_selfAdjoint spectralParam)
    (kernelEnergyMassRestriction K hK.measurableSet) hcompact
    (4/(1-spectralParam)^2) (4*C/(1-spectralParam))
    (kernelSpectralFormOperator_compact_estimate K hK.measurableSet C hC hcoercive spectralParam hzero hone)

theorem kernel_theta_spectral_fredholm :
    (kernelSpectralFormOperator (8/9:ℂ)).IsFredholm := by
  convert kernelSpectralFormOperator_isFredholm (8/9) (by norm_num) (by norm_num) using 1
  norm_num

end CubicEisenstein

namespace CanonicalRowCompletion
open SecondPassArithmetic

theorem cubeLogRange_sq_small_power (b ε : ℝ) (_hb : 0≤b) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀X Z : ℝ,0≤X → 1≤Z → X≤Z^3 →
      ((cubeLogRange b X).card:ℝ)^2≤C*Z^ε := by
  let B:=max 1 b
  let deltaLoss:=ε/2
  let C₀:=1+Real.log B+3/deltaLoss
  have hB : 1≤B:=le_max_left _ _
  have hB0 : 0<B:=zero_lt_one.trans_le hB
  have hδ : 0<deltaLoss:=by dsimp [deltaLoss];positivity
  have hlogB : 0≤Real.log B:=Real.log_nonneg hB
  have hC₀ : 0<C₀:=by dsimp [C₀];positivity
  refine ⟨C₀^2,by positivity,?_⟩
  intro X Z hX hZ hXZ
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hZ3 : 1≤Z^3:=one_le_pow₀ hZ
  have hY : 1≤B*Z^3:=one_le_mul_of_one_le_of_one_le hB hZ3
  have hxY : max 1 (b*X)≤B*Z^3 := by
    apply max_le hY
    calc
      b*X ≤ B*X:=mul_le_mul_of_nonneg_right (le_max_right _ _) hX
      _ ≤ B*Z^3:=mul_le_mul_of_nonneg_left hXZ hB0.le
  have hcard : ((cubeLogRange b X).card:ℝ)≤1+Real.log B+3*Real.log Z := by
    rw [cubeLogRange_card,Nat.cast_add,Nat.cast_one]
    have hlog:=normLogBin_le_log_upper (max 1 (b*X)) (B*Z^3)
      (zero_lt_one.trans_le (le_max_left _ _)) hxY hY
    rw [Real.log_mul hB0.ne' (pow_pos hZ0 3).ne',Real.log_pow] at hlog
    norm_num at hlog
    linarith
  have hr : 1≤Z^deltaLoss:=Real.one_le_rpow hZ hδ.le
  have hl : Real.log Z≤Z^deltaLoss/deltaLoss:=Real.log_le_rpow_div hZ0.le hδ
  have hc : 1+Real.log B+3*Real.log Z≤C₀*Z^deltaLoss := by
    calc
      _ ≤ (1+Real.log B)*Z^deltaLoss+3*(Z^deltaLoss/deltaLoss) := by
        gcongr
        exact le_mul_of_one_le_right (by linarith) hr
      _ = _:=by dsimp [C₀];ring
  calc
    _ ≤ (C₀*Z^deltaLoss)^2:=pow_le_pow_left₀ (Nat.cast_nonneg _) (hcard.trans hc) 2
    _ = C₀^2*Z^ε:=by
      rw [mul_pow,←Real.rpow_natCast (Z^deltaLoss) 2,←Real.rpow_mul hZ0.le]
      congr 1
      dsimp [deltaLoss]
      congr 1
      ring

end CanonicalRowCompletion

namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

theorem halfCanonicalPadding_budget (ε C : ℝ) (hε : 0<ε) (hC : 0≤C) :
    0<canonicalPadding ε C/2 ∧ canonicalPadding ε C/2≤(1:ℝ)/1000 ∧
    3000*(canonicalPadding ε C/2)≤(1:ℝ)/80 ∧
    3001*C*(canonicalPadding ε C/2)≤ε/2 := by
  have h:=canonicalPadding_budget ε C hε hC
  refine ⟨by linarith,by linarith,by linarith,?_⟩
  have hceta : 0≤3001*C*canonicalPadding ε C :=
    mul_nonneg (mul_nonneg (by norm_num) hC) h.1.le
  nlinarith [h.2.2.2.2.1]

theorem canonicalRankMargin_strict_reserve (η : ℝ) (hη : 0≤η)
    (hbudget : 3000*η≤(1:ℝ)/80) (r : ℕ) :
    (3:ℝ)/80≤canonicalRankMargin ((1:ℝ)/20) η r :=
  (by linarith : (3:ℝ)/80≤(1:ℝ)/20-3000*η).trans
    (canonicalRankMargin_lower _ η hη r)

theorem CanonicalStateCondition.fixed_factor_margin
    {base : ActualEisensteinCubic.O→*ℂ} {bad : Ideal ActualEisensteinCubic.O} {Z η : ℝ} {Ψ : ActualEisensteinCubic.O→*ℂ} {m : ActualEisensteinCubic.O}
    {labels : Finset (Ideal ActualEisensteinCubic.O)} {X F K : ℝ}
    (h : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hη : 0≤η) (hbudget : 3000*η≤(1:ℝ)/80)
    (C : ℝ) (hC : 0≤C) (hCZ : C≤Z^((1:ℝ)/80)) :
    C*K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((1:ℝ)/40)) := by
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hXF : 0≤X*F:=mul_nonneg h.column_pos.le (zero_le_one.trans h.label_ge_one)
  have hm := canonicalRankMargin_strict_reserve η hη hbudget (fixedDepthRank Z K)
  have hi : K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((3:ℝ)/80)) := by
    apply h.invariant.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (neg_le_neg hm)) hXF
  calc
    C*K*‖eisEmbedding m‖^2 = C*(K*‖eisEmbedding m‖^2) := by ring
    _ ≤ C*((X*F)*Z^(-((3:ℝ)/80))) := mul_le_mul_of_nonneg_left hi hC
    _ ≤ Z^((1:ℝ)/80)*((X*F)*Z^(-((3:ℝ)/80))) :=
      mul_le_mul_of_nonneg_right hCZ (mul_nonneg hXF (Real.rpow_nonneg hZ0.le _))
    _ = (X*F)*(Z^((1:ℝ)/80)*Z^(-((3:ℝ)/80))) := by ring
    _ = _ := by rw [←Real.rpow_add hZ0];norm_num

end SecondPassArithmetic

namespace CanonicalRowCompletion

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open FirstPassCubeLabels (columnLog)

private theorem height_sum_bound (a b : ℝ) (J : ℕ) :
    (1+|a+b|)^(2*J)≤(1+|a|)^(2*J)*(1+|b|)^(2*J) := by
  have h : 1+|a+b|≤(1+|a|)*(1+|b|) := by
    have := abs_add_le a b
    nlinarith [abs_nonneg a,abs_nonneg b]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0≤1+|a+b|) h (2*J)

theorem progressingCanonicalBin_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀u,|u|≤columnWindowRadius a b→V u=1)
    (B ell X H₀ K E oldHeight : ℝ) (J : ℕ)
    (hB : 0<B) (hell : 0<ell) (hX : X=B^3*ell) (hK : 0<K) (hE : 0≤E)
    (hn : ∀v∈Q,B≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))
    (hn' : ∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*B) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let Q':=progressingCubes S D H₀ Q
    let β:=fun I v=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    (∀ξ : ℝ,B*rowFamilyEnergy labels (fun I z=>
      reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ Q' (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (idealGenerator I) (fun T=>frequencyTwist V (oldHeight+ξ) (columnLog (poolPrimary F) ell T)) z) K≤
      E*(1+|oldHeight+ξ|)^(2*J)) →
    X*rowFamilyEnergy labels (fun I z=>
      outsideCanonicalBin S D hbad Q (normHeightTwist Ψ oldHeight) m (idealGenerator I) z W X H₀) K≤
      E*(1+|oldHeight|)^(2*J)*
        (∫ξ : ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^J)^2 := by
  dsimp only
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let Q':=progressingCubes S D H₀ Q
  let β:=fun I v=>reopenedCubeCoefficient H₀
    (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
  let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  intro hsource
  have hX0 : 0<X := by rw [hX];positivity
  have hQsub : Q'⊆Q := Finset.filter_subset _ _
  have heq : (fun I z=>outsideCanonicalBin S D hbad Q (normHeightTwist Ψ oldHeight) m (idealGenerator I) z W X H₀)=
      (fun I z=>outsideCanonicalBin S D hbad Q' (normHeightTwist Ψ oldHeight) m (idealGenerator I) z W X H₀) := by
    funext I z
    exact outsideCanonicalBin_filter S D hbad Q _ m _ z W X H₀
  rw [heq]
  have he := outsideCanonicalBin_energy S D hbad Q' labels (normHeightTwist Ψ oldHeight) m W
    a b ha hs hW V hV B ell X H₀ K ((E/B)*(1+|oldHeight|)^(2*J)) J hB hell hX hK
    (by positivity) (fun v hv=>hn v (hQsub hv)) (fun v hv=>hn' v (hQsub hv))
  have hpnt : ∀ξ : ℝ,rowFamilyEnergy labels (fun I z=>
      reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ Q' (separatedCubeCoefficient (β I) n B ξ)
        (normHeightTwist Ψ oldHeight) m (idealGenerator I)
        (fun T=>frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K≤
      ((E/B)*(1+|oldHeight|)^(2*J))*(1+|ξ|)^(2*J) := by
    intro ξ
    change (∑I∈labels,nonzeroRowMajorantSum _ K).re≤_
    rw [reopenedCanonicalEnergy_two_heights (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q' labels
      (fun I=>separatedCubeCoefficient (β I) n B ξ) Ψ m V ell K oldHeight ξ hell]
    change rowFamilyEnergy labels _ K≤_
    have ht := (le_div_iff₀ hB).mpr (by simpa only [mul_comm] using hsource ξ)
    calc
      _ ≤ E*(1+|oldHeight+ξ|)^(2*J)/B := by simpa only [Nat.mul_comm J 2] using ht
      _ ≤ E*((1+|oldHeight|)^(2*J)*(1+|ξ|)^(2*J))/B :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (height_sum_bound oldHeight ξ J) hE) hB.le
      _ = _ := by ring
  have hf:=he hpnt
  have hh:=mul_le_mul_of_nonneg_left hf hX0.le
  apply hh.trans_eq
  rw [hX]
  field_simp

end CanonicalRowCompletion

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss
open ActualEisensteinCubic

theorem shortCompletedSum_nonpos (Ψ : ActualEisensteinCubic.O→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (hH : H₀≤0) :
    shortCompletedSum Ψ W X H₀=0 := by
  unfold shortCompletedSum
  calc
    _ = ∑'I : Ideal ActualEisensteinCubic.O,(0:ℂ) := tsum_congr (fun I=>ite_eq_right (not_lt_of_ge (hH.trans (Nat.cast_nonneg (Ideal.absNorm I)))))
    _ = 0 := tsum_zero

end CompletedGauss
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalLabels_subset_idealRange
    (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hbad : ∀P∈fixedBadPrimes,P∣bad) : labels⊆idealRange F := by
  intro I hI
  have hb:=hstate.label_bounds I hI
  exact mem_idealRange.mpr ⟨admissible_of_squarefree_coprime_bad I bad hb.2.1 hb.2.2.1 hbad,hb.2.2.2⟩

theorem rowFamilyEnergy_le_rectangle (labels : Finset (Ideal ActualEisensteinCubic.O)) (F K : ℝ)
    (hK : 0<K) (hlabels : labels⊆idealRange F) (P : Ideal ActualEisensteinCubic.O→ActualEisensteinCubic.O→ℂ) :
    rowFamilyEnergy labels P K≤SchwartzMap.seminorm ℝ 0 0 rowMajorant*
      ∑f : idealRange F,∑z∈(firstFrequencyDisk (2*K)).erase 0,‖P f.val z‖^2 := by
  rw [rowFamilyEnergy_eq_sum labels P K hK]
  have hM : 0≤SchwartzMap.seminorm ℝ 0 0 rowMajorant:=apply_nonneg _ _
  calc
    _ ≤ ∑I∈labels,∑z∈(firstFrequencyDisk (2*K)).erase 0,
        SchwartzMap.seminorm ℝ 0 0 rowMajorant*‖P I z‖^2 := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_right
        ((Complex.re_le_norm _).trans (SchwartzMap.norm_le_seminorm ℝ rowMajorant _)) (sq_nonneg _)
    _ = SchwartzMap.seminorm ℝ 0 0 rowMajorant*
        ∑I∈labels,∑z∈(firstFrequencyDisk (2*K)).erase 0,‖P I z‖^2 := by
      simp only [Finset.mul_sum]
    _ ≤ SchwartzMap.seminorm ℝ 0 0 rowMajorant*
        ∑I∈idealRange F,∑z∈(firstFrequencyDisk (2*K)).erase 0,‖P I z‖^2 := by
      apply mul_le_mul_of_nonneg_left _ hM
      exact Finset.sum_le_sum_of_subset_of_nonneg hlabels (fun I _ _=>Finset.sum_nonneg (fun z hz=>sq_nonneg _))
    _ = _ := by
      congr 1
      exact (Finset.sum_coe_sort (s:=idealRange F)
        (f:=fun I=>∑z∈(firstFrequencyDisk (2*K)).erase 0,‖P I z‖^2)).symm

theorem canonicalShortEnergy_uniform_twist
    (a b : ℝ) (ha : 0<a) (ε ρ q levelBound : ℝ)
    (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃d : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^((1:ℝ)/1000) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∀(labels : Finset (Ideal ActualEisensteinCubic.O)),labels⊆idealRange F →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),(∀x,‖Ψ x‖≤1) → ∀(mask : ActualEisensteinCubic.O) (lengthScale : ℂ),
      (∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        HasExactCompletedDyadicModels rays (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ) (CompletedUnitRows.unitRowFamily Ψ mask u f) lengthScale) →
      rowFamilyEnergy labels (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ)
        mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000))) K≤
      (C*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*((2*K)*(Ideal.absNorm G:ℝ)*F)^ε*(K*F)*Z^ε := by
  obtain ⟨d,hbound⟩:=CompletedUnitRows.short_completed_elements_uniform_twist a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨C,hC,h⟩:=hbound W hs hW
  refine ⟨2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*C,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin labels hlabels Ψ hΨ mask lengthScale hmodels
  have hK0 : 0<K:=zero_lt_one.trans_le hK
  have hF0 : 0<F:=zero_lt_one.trans_le hF
  have hT : ∀z∈(firstFrequencyDisk (2*K)).erase 0,
      z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤2*K := by
    intro z hz
    refine ⟨(Finset.mem_erase.mp hz).1,?_⟩
    rw [←eisEmbedding_norm_sq_eq_absNorm_span]
    exact (mem_firstFrequencyDisk (2*K) z).mp (Finset.mem_erase.mp hz).2
  have hshort:=h θ rays Z (2*K) X F hZ (by linarith) hF hFZ G hG hbad hmargin
    ((firstFrequencyDisk (2*K)).erase 0) hT Ψ hΨ mask lengthScale hmodels
  have hsum := (div_le_iff₀ hF0).mp hshort
  have hrect:=rowFamilyEnergy_le_rectangle labels F K hK0 hlabels
    (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ) mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000)))
  exact hrect.trans ((mul_le_mul_of_nonneg_left hsum (apply_nonneg _ _)).trans_eq (by ring))

end CanonicalRowCompletion

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open FirstPassCubeLabels (columnLog)

theorem progressingCanonicalFamily_energy
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0≤b)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀u,|u|≤columnWindowRadius a b→V u=1)
    (X H₀ K E oldHeight : ℝ) (J : ℕ)
    (hX : 0<X) (hK : 0<K) (hE : 0≤E) (hD : b*X≤D) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β:=fun I v=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    (∀j∈cubeLogRange b X,
      let B:=normLogScale j
      let Q':=progressingCubes S D H₀ (activeCubeLogBin S D b X j)
      Q'.Nonempty → ∀ξ : ℝ,B*rowFamilyEnergy labels (fun I z=>
        reopenedCanonicalRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
          (poolPrimary_good F hF) Finset.univ Q' (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I)
          (fun T=>frequencyTwist V (oldHeight+ξ) (columnLog (poolPrimary F) (X/B^3) T)) z) K≤
        E*(1+|oldHeight+ξ|)^(2*J)) →
    rowFamilyEnergy labels (fun I z=>outsideCanonicalRow S D hbad (normHeightTwist Ψ oldHeight)
      m (idealGenerator I) z W X) K≤
    2*X*rowFamilyEnergy labels (fun I z=>
      shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K+
    2*((cubeLogRange b X).card:ℝ)^2*E*(1+|oldHeight|)^(2*J)*
      (∫ξ : ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^J)^2 := by
  dsimp only
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  intro hsource
  let T:=E*(1+|oldHeight|)^(2*J)*(∫ξ : ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^J)^2
  have hT : 0≤T := by dsimp only [T];positivity
  let binEnergy:=fun j=>rowFamilyEnergy labels (fun I z=>
    outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) (normHeightTwist Ψ oldHeight)
      m (idealGenerator I) z W X H₀) K
  have hbin (j : ℕ) (hj : j∈cubeLogRange b X) : X*binEnergy j≤T := by
    by_cases hnon : (progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty
    · apply progressingCanonicalBin_energy S D hbad (activeCubeLogBin S D b X j) labels Ψ m W
        a b ha hs hW V hV (normLogScale j) (X/(normLogScale j)^3) X H₀ K E oldHeight J
        (normLogScale_pos j) (div_pos hX (pow_pos (normLogScale_pos j) _))
        (by field_simp [(normLogScale_pos j).ne']) hK hE
        (fun v hv=>(activeCubeLogBin_norms S D b X j v hv).1)
        (fun v hv=>(activeCubeLogBin_norms S D b X j v hv).2)
      exact hsource j hj hnon
    · have hempty:=Finset.not_nonempty_iff_eq_empty.mp hnon
      have heq : (fun I z=>outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j)
          (normHeightTwist Ψ oldHeight) m (idealGenerator I) z W X H₀)=(fun _ _=>0) := by
        funext I z
        exact outsideCanonicalBin_zero_of_empty_filter S D hbad _ _ m _ z W X H₀ hempty
      dsimp only [binEnergy]
      rw [heq]
      simpa only [rowFamilyEnergy,nonzeroRowMajorantSum,norm_zero,zero_pow (by decide : (2:ℕ)≠0),
        Complex.ofReal_zero,mul_zero,ite_self,tsum_zero,Finset.sum_const_zero,Complex.zero_re] using hT
  have hsum : X*∑j∈cubeLogRange b X,binEnergy j≤((cubeLogRange b X).card:ℝ)*T := by
    simpa only [Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hbin
  have hwhole:=outsideCanonicalRow_family_binned_energy S D hbad hSp (normHeightTwist Ψ oldHeight)
    m labels W hWc b X H₀ K hb hX hK (fun x hx=>(hs hx).2) hD
  calc
    _ ≤ 2*X*(rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,binEnergy j) := hwhole
    _ = 2*X*rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K+
        (2*((cubeLogRange b X).card:ℝ))*(X*∑j∈cubeLogRange b X,binEnergy j) := by ring
    _ ≤ 2*X*rowFamilyEnergy labels (fun I z=>
        shortCompletedSum (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) z) W X H₀) K+
        (2*((cubeLogRange b X).card:ℝ))*(((cubeLogRange b X).card:ℝ)*T) := by gcongr
    _ = _ := by dsimp only [T];ring

end CanonicalRowCompletion

end

end OAI
end OAIOriginalModule0244

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.MeromorphicResolvent
Source SHA256: 3cff92549cd07c861846e4a28df2202f794eee3ef9fed52ab5157144b2b48645
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0245


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped Topology

lemma kernelSpectralFormOperator_analyticAt (z : ℂ) :
    AnalyticAt ℂ kernelSpectralFormOperator z := by
  let S : KernelEnergyGraph→L[ℂ]KernelEnergyGraph := kernelEnergyMass.adjoint.comp kernelEnergyMass
  have hc : AnalyticAt ℂ (fun w : ℂ => w • S) (z+1) := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply] using!
      (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
        (F := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) S) (z+1))
  have hz : AnalyticAt ℂ (fun w : ℂ => w+1) z := analyticAt_id.add analyticAt_const
  exact analyticAt_const.sub (hc.comp_of_eq hz rfl)

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelMassGram : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  kernelEnergyMass.adjoint.comp kernelEnergyMass

private lemma selfAdjoint_adjoint_comp {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) : IsSelfAdjoint (A.adjoint.comp A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

lemma kernelMassGram_selfAdjoint : IsSelfAdjoint kernelMassGram :=
  selfAdjoint_adjoint_comp kernelEnergyMass

def kernelThetaNull : Submodule ℂ KernelEnergyGraph :=
  (kernelSpectralFormOperator (8/9:ℂ)).ker

def kernelThetaRegular : Submodule ℂ KernelEnergyGraph := kernelThetaNullᗮ

instance kernelThetaNull_complete : CompleteSpace kernelThetaNull :=
  (kernelSpectralFormOperator (8/9:ℂ)).isClosed_ker.completeSpace_coe

instance kernelThetaRegular_complete : CompleteSpace kernelThetaRegular :=
  kernelThetaNull.isClosed_orthogonal.completeSpace_coe

instance kernelThetaNull_finiteDimensional : FiniteDimensional ℂ kernelThetaNull :=
  kernel_theta_spectral_fredholm.finite_ker

lemma kernelThetaNull_gram_eq (u : KernelEnergyGraph) (hu : u∈kernelThetaNull) :
    kernelMassGram u=(9/17:ℂ)•u := by
  have hh : u-(8/9+1:ℂ)•kernelMassGram u=0 := hu
  have he : u=(17/9:ℂ)•kernelMassGram u := by
    simpa only [show (8/9+1:ℂ)=17/9 by norm_num] using sub_eq_zero.mp hh
  calc
    _ = (9/17:ℂ)•((17/9:ℂ)•kernelMassGram u) := by rw [smul_smul]; norm_num
    _ = _ := by rw [←he]

lemma kernelThetaNull_spectral_eq (z : ℂ) (u : KernelEnergyGraph) (hu : u∈kernelThetaNull) :
    kernelSpectralFormOperator z u=((8/9-z)*(9/17):ℂ)•u := by
  change u-(z+1)•kernelMassGram u=_
  rw [kernelThetaNull_gram_eq u hu,smul_smul]
  calc
    u-((z+1)*(9/17):ℂ)•u=(1-(z+1)*(9/17):ℂ)•u := by rw [sub_smul,one_smul]
    _ = _ := by congr 1; ring

lemma kernelMassGram_preserves_regular (u : KernelEnergyGraph) (hu : u∈kernelThetaRegular) :
    kernelMassGram u∈kernelThetaRegular := by
  apply (kernelThetaNull.mem_orthogonal _).mpr
  intro v hv
  have he : inner ℂ v (kernelMassGram u)=inner ℂ (kernelMassGram v) u := by
    simpa only [ContinuousLinearMap.coe_coe] using (kernelMassGram_selfAdjoint.isSymmetric v u).symm
  rw [he,kernelThetaNull_gram_eq v hv,inner_smul_left (𝕜 := ℂ) v u (9/17:ℂ)]
  rw [kernelThetaNull.inner_right_of_mem_orthogonal hv hu,mul_zero]

lemma kernelSpectralFormOperator_preserves_regular (z : ℂ)
    (u : KernelEnergyGraph) (hu : u∈kernelThetaRegular) :
    kernelSpectralFormOperator z u∈kernelThetaRegular :=
  kernelThetaRegular.sub_mem hu (kernelThetaRegular.smul_mem _ (kernelMassGram_preserves_regular u hu))

def kernelRegularGram : kernelThetaRegular→L[ℂ]kernelThetaRegular :=
  kernelMassGram.restrict kernelMassGram_preserves_regular

def kernelRegularPencil (z : ℂ) : kernelThetaRegular→L[ℂ]kernelThetaRegular :=
  ContinuousLinearMap.id ℂ kernelThetaRegular-(z+1)•kernelRegularGram

lemma kernelRegularPencil_apply (z : ℂ) (u : kernelThetaRegular) :
    (kernelRegularPencil z u:KernelEnergyGraph)=kernelSpectralFormOperator z u := rfl

lemma kernelRegularPencil_center_isUnit : IsUnit (kernelRegularPencil (8/9:ℂ)) := by
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := kernelThetaRegular)).mpr
  constructor
  · intro u v huv
    apply ker_orthogonal_restriction_injective (kernelSpectralFormOperator (8/9:ℂ))
    exact congrArg (fun w : kernelThetaRegular => (w:KernelEnergyGraph)) huv
  · intro v
    have he : (kernelSpectralFormOperator (8/9:ℂ)).range=kernelThetaRegular := by
      exact selfAdjoint_range_eq_ker_orthogonal _
        (by convert kernelSpectralFormOperator_selfAdjoint (8/9) using 1 ; norm_num)
        kernel_theta_spectral_fredholm.isClosed_range
    have hv : (v:KernelEnergyGraph)∈(kernelSpectralFormOperator (8/9:ℂ)).range := by
      rw [he]
      exact v.2
    obtain ⟨u,hu⟩ := hv
    change kernelSpectralFormOperator (8/9:ℂ) u=(v:KernelEnergyGraph) at hu
    let w : kernelThetaRegular := ⟨u-kernelThetaNull.starProjection u,kernelThetaNull.sub_starProjection_mem_orthogonal u⟩
    refine ⟨w,Subtype.ext ?_⟩
    rw [kernelRegularPencil_apply]
    change kernelSpectralFormOperator (8/9:ℂ) (u-kernelThetaNull.starProjection u)=v
    rw [map_sub,hu]
    have hz : kernelSpectralFormOperator (8/9:ℂ) (kernelThetaNull.starProjection u)=0 :=
      kernelThetaNull.starProjection_apply_mem u
    rw [hz,sub_zero]

private abbrev endomorphismNormedSpace (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] : NormedSpace ℂ (E →L[ℂ] E) := inferInstance

local instance : NormedSpace ℂ (kernelThetaRegular →L[ℂ] kernelThetaRegular) :=
  endomorphismNormedSpace kernelThetaRegular

lemma kernelRegularPencil_analyticAt (z : ℂ) :
    AnalyticAt ℂ kernelRegularPencil z := by
  have hc : AnalyticAt ℂ (fun w : ℂ => w • kernelRegularGram) (z+1) := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply] using!
      (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
        (F := kernelThetaRegular→L[ℂ]kernelThetaRegular)
        (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) kernelRegularGram) (z+1))
  have hz : AnalyticAt ℂ (fun w : ℂ => w+1) z := analyticAt_id.add analyticAt_const
  exact analyticAt_const.sub (hc.comp_of_eq hz rfl)

lemma kernelRegularPencil_eventually_isUnit :
    ∀ᶠ z : ℂ in 𝓝 (8/9:ℂ), IsUnit (kernelRegularPencil z) :=
  (kernelRegularPencil_analyticAt (8/9)).continuousAt.eventually
    ((Units.isOpen (R := kernelThetaRegular→L[ℂ]kernelThetaRegular)).mem_nhds
      (show kernelRegularPencil (8/9)∈{x : kernelThetaRegular→L[ℂ]kernelThetaRegular | IsUnit x} from
        kernelRegularPencil_center_isUnit))

lemma kernelRegularInverse_analyticAt :
    AnalyticAt ℂ (fun z : ℂ => Ring.inverse (kernelRegularPencil z)) (8/9:ℂ) := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ)
    (A := kernelThetaRegular→L[ℂ]kernelThetaRegular))
    (kernelRegularPencil (8/9)) kernelRegularPencil_center_isUnit
  exact hi.comp_of_eq (kernelRegularPencil_analyticAt (8/9)) rfl

private def continuousLinearSandwich {H G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : H →L[ℂ] G) (B : G →L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (G →L[ℂ] G) :=
  (ContinuousLinearMap.compL ℂ G H G A).comp
    ((ContinuousLinearMap.compL ℂ G H H).flip B)

def kernelRegularLiftCLM :
    (kernelThetaRegular→L[ℂ]kernelThetaRegular)→L[ℂ](KernelEnergyGraph→L[ℂ]KernelEnergyGraph) :=
  continuousLinearSandwich (H := kernelThetaRegular) (G := KernelEnergyGraph)
    kernelThetaRegular.subtypeL
    kernelThetaRegular.orthogonalProjectionOnto

def kernelRegularInverseLift (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  kernelRegularLiftCLM (Ring.inverse (kernelRegularPencil z))

lemma kernelRegularInverseLift_apply (z : ℂ) (u : KernelEnergyGraph) :
    kernelRegularInverseLift z u =
      (Ring.inverse (kernelRegularPencil z) (kernelThetaRegular.orthogonalProjectionOnto u) :
        KernelEnergyGraph) := rfl

lemma kernelRegularInverseLift_analyticAt :
    AnalyticAt ℂ kernelRegularInverseLift (8/9:ℂ) := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := kernelThetaRegular→L[ℂ]kernelThetaRegular)
    (F := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    kernelRegularLiftCLM (Ring.inverse (kernelRegularPencil (8/9)))).comp_of_eq
      kernelRegularInverse_analyticAt rfl

def kernelLocalEnergyResolvent (z : ℂ) : KernelEnergyGraph→L[ℂ]KernelEnergyGraph :=
  ((17/9)/(8/9-z):ℂ) • kernelThetaNull.starProjection + kernelRegularInverseLift z

lemma kernelLocalEnergyResolvent_meromorphicAt :
    MeromorphicAt kernelLocalEnergyResolvent (8/9:ℂ) := by
  have hs : MeromorphicAt (fun z : ℂ => (17/9)/(8/9-z)) (8/9:ℂ) := by fun_prop
  have hp : MeromorphicAt (fun z : ℂ => ((17/9)/(8/9-z):ℂ) • kernelThetaNull.starProjection) (8/9:ℂ) := by
    obtain ⟨n,hn⟩ := hs
    refine ⟨n,?_⟩
    let A := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) kernelThetaNull.starProjection
    have ha := ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := ℂ)
      (F := KernelEnergyGraph→L[ℂ]KernelEnergyGraph) A
      (((8/9:ℂ)-(8/9))^n*((17/9)/(8/9-(8/9))))
    convert ha.comp_of_eq hn rfl using 1 ;
      simp [A,Function.comp_def,smul_smul,smul_eq_mul]
  exact hp.add kernelRegularInverseLift_analyticAt.meromorphicAt

lemma kernelSpectralFormOperator_regularInverseLift (z : ℂ)
    (hz : IsUnit (kernelRegularPencil z)) (u : KernelEnergyGraph) :
    kernelSpectralFormOperator z (kernelRegularInverseLift z u)=
      kernelThetaRegular.starProjection u := by
  rw [kernelRegularInverseLift_apply,←kernelRegularPencil_apply]
  have he := congrArg (fun A : kernelThetaRegular→L[ℂ]kernelThetaRegular =>
    A (kernelThetaRegular.orthogonalProjectionOnto u))
      (Ring.mul_inverse_cancel (kernelRegularPencil z) hz)
  exact congrArg (fun v : kernelThetaRegular => (v:KernelEnergyGraph)) he

lemma kernelLocalEnergyResolvent_right_inverse (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) (u : KernelEnergyGraph) :
    kernelSpectralFormOperator z (kernelLocalEnergyResolvent z u)=u := by
  change kernelSpectralFormOperator z
    (((17/9)/(8/9-z):ℂ) • kernelThetaNull.starProjection u + kernelRegularInverseLift z u)=u
  rw [map_add,map_smul,kernelThetaNull_spectral_eq z _
    (kernelThetaNull.starProjection_apply_mem u),smul_smul]
  have hc : ((17/9)/(8/9-z):ℂ)*((8/9-z)*(9/17))=1 := by
    calc
      _ = (((17/9)/(8/9-z):ℂ)*(8/9-z))*(9/17) := by ring
      _ = (17/9:ℂ)*(9/17) := by rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hne.symm)]
      _ = 1 := by norm_num
  rw [hc,one_smul,kernelSpectralFormOperator_regularInverseLift z hz]
  exact kernelThetaNull.starProjection_add_starProjection_orthogonal u

lemma selfAdjoint_one_sub_smul_normal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : H→L[ℂ]H)
    (hS : IsSelfAdjoint S) (z : ℂ) : IsStarNormal (1-z•S) := by
  let : IsStarNormal S := hS.isStarNormal
  infer_instance

lemma kernelSpectralFormOperator_normal (z : ℂ) : IsStarNormal (kernelSpectralFormOperator z) := by
  exact selfAdjoint_one_sub_smul_normal kernelMassGram kernelMassGram_selfAdjoint (z+1)

lemma kernelSpectralFormOperator_isUnit_near (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) : IsUnit (kernelSpectralFormOperator z) := by
  have hsur : Function.Surjective (kernelSpectralFormOperator z) := fun u =>
    ⟨kernelLocalEnergyResolvent z u,kernelLocalEnergyResolvent_right_inverse z hne hz u⟩
  apply (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mpr
  refine ⟨?_,hsur⟩
  change Function.Injective (kernelSpectralFormOperator z).toLinearMap
  apply LinearMap.ker_eq_bot.mp
  rw [←ContinuousLinearMap.IsStarNormal.orthogonal_range (kernelSpectralFormOperator_normal z)]
  have hr : (kernelSpectralFormOperator z).range=⊤ := LinearMap.range_eq_top.mpr hsur
  rw [hr,Submodule.top_orthogonal_eq_bot]

lemma kernelLocalEnergyResolvent_left_inverse (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) (u : KernelEnergyGraph) :
    kernelLocalEnergyResolvent z (kernelSpectralFormOperator z u)=u := by
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mp
    (kernelSpectralFormOperator_isUnit_near z hne hz)
  exact hinj.1 (kernelLocalEnergyResolvent_right_inverse z hne hz _)

lemma kernelLocalEnergyResolvent_eq_inverse (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) :
    kernelLocalEnergyResolvent z = Ring.inverse (kernelSpectralFormOperator z) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ((ContinuousLinearMap.isUnit_iff_bijective (𝕜 := ℂ) (E := KernelEnergyGraph)).mp
    (kernelSpectralFormOperator_isUnit_near z hne hz)).1
  rw [kernelLocalEnergyResolvent_right_inverse z hne hz]
  have hi := congrArg (fun A : KernelEnergyGraph→L[ℂ]KernelEnergyGraph => A u)
    (Ring.mul_inverse_cancel (kernelSpectralFormOperator z) (kernelSpectralFormOperator_isUnit_near z hne hz))
  exact hi.symm

lemma kernelSpectralFormInverse_meromorphicAt :
    MeromorphicAt (fun z : ℂ => Ring.inverse (kernelSpectralFormOperator z)) (8/9:ℂ) := by
  apply kernelLocalEnergyResolvent_meromorphicAt.congr
  filter_upwards [kernelRegularPencil_eventually_isUnit.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hne
  exact kernelLocalEnergyResolvent_eq_inverse z hne hz

end

open scoped Topology

lemma meromorphicAt_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (A : E→L[ℂ]F) {f : ℂ→E} {z : ℂ}
    (hf : MeromorphicAt f z) : MeromorphicAt (fun w => A (f w)) z := by
  obtain ⟨n,hn⟩ := hf
  refine ⟨n,?_⟩
  have hh := (A.analyticAt ((z-z)^n•f z)).comp_of_eq hn rfl
  simpa only [Function.comp_def,map_smul] using hh

lemma meromorphicAt_bilinear {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (B : E→L[ℂ]F→L[ℂ]G) {f : ℂ→E} {g : ℂ→F} {z : ℂ}
    (hf : MeromorphicAt f z) (hg : MeromorphicAt g z) :
    MeromorphicAt (fun w => B (f w) (g w)) z := by
  obtain ⟨m,hm⟩ := hf
  obtain ⟨n,hn⟩ := hg
  refine ⟨m+n,?_⟩
  have hh := (B.analyticAt_bilinear (((z-z)^m•f z),((z-z)^n•g z))).comp₂ hm hn
  simpa only [map_smul,_root_.smul_apply,smul_smul,pow_add,mul_comm] using hh

lemma meromorphicAt_clm_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A : ℂ→E→L[ℂ]F} {f : ℂ→E} {z : ℂ}
    (hA : MeromorphicAt A z) (hf : MeromorphicAt f z) :
    MeromorphicAt (fun w => A w (f w)) z :=
  meromorphicAt_bilinear (ContinuousLinearMap.apply ℂ F) hf hA

lemma selfAdjoint_pencil_isUnit_nonreal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : H→L[ℂ]H)
    (hS : IsSelfAdjoint S) (z : ℂ) (hz : z.im≠0) : IsUnit (1-z•S) := by
  have hne : z≠0 := fun h => hz (by rw [h]; rfl)
  have hi : z⁻¹.im≠0 := by
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr hz) (mt Complex.normSq_eq_zero.mp hne)
  have hout : z⁻¹∉spectrum ℂ S := fun h => hi (hS.im_eq_zero_of_mem_spectrum h)
  have hu := (spectrum.notMem_iff (R := ℂ) (A := H→L[ℂ]H)).mp hout
  have hv := hu.smul (Units.mk0 z hne)
  simpa only [Units.smul_def,Units.val_mk0,Algebra.algebraMap_eq_smul_one,
    smul_sub,smul_smul,mul_inv_cancel₀ hne,one_smul] using hv

lemma kernelSpectralFormOperator_isUnit_nonreal (z : ℂ) (hz : z.im≠0) :
    IsUnit (kernelSpectralFormOperator z) := by
  exact selfAdjoint_pencil_isUnit_nonreal kernelMassGram kernelMassGram_selfAdjoint (z+1)
    (by simpa using hz)

lemma kernelSpectralFormInverse_analyticAt_of_isUnit (z : ℂ)
    (hz : IsUnit (kernelSpectralFormOperator z)) :
    AnalyticAt ℂ (fun w => Ring.inverse (kernelSpectralFormOperator w)) z := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ)
    (A := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)) (kernelSpectralFormOperator z) hz
  exact hi.comp_of_eq (kernelSpectralFormOperator_analyticAt z) rfl

lemma kernelSpectralFormInverse_analyticAt_nonreal (z : ℂ) (hz : z.im≠0) :
    AnalyticAt ℂ (fun w => Ring.inverse (kernelSpectralFormOperator w)) z :=
  kernelSpectralFormInverse_analyticAt_of_isUnit z (kernelSpectralFormOperator_isUnit_nonreal z hz)

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelL2SandwichCLM : (KernelEnergyGraph→L[ℂ]KernelEnergyGraph)→L[ℂ]
    (KernelQuotientL2→L[ℂ]KernelQuotientL2) :=
  continuousLinearSandwich kernelEnergyMass kernelEnergyMass.adjoint

def kernelSpectralResolvent (z : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM (Ring.inverse (kernelSpectralFormOperator z))

lemma kernelSpectralResolvent_apply (z : ℂ) (F : KernelQuotientL2) :
    kernelSpectralResolvent z F=
      kernelEnergyMass (Ring.inverse (kernelSpectralFormOperator z) (kernelVariationalSolution F)) := rfl

private lemma meromorphicAt_operator_clm {H G : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : (H →L[ℂ] H) →L[ℂ] (G →L[ℂ] G))
    {f : ℂ → (H →L[ℂ] H)} {z : ℂ} (hf : MeromorphicAt f z) :
    MeromorphicAt (fun w => A (f w)) z :=
  meromorphicAt_clm A hf

lemma kernelSpectralResolvent_meromorphicAt :
    MeromorphicAt kernelSpectralResolvent (8/9:ℂ) := by
  exact meromorphicAt_operator_clm
    (H := KernelEnergyGraph) (G := KernelQuotientL2)
    (f := fun z : ℂ => Ring.inverse (kernelSpectralFormOperator z))
    kernelL2SandwichCLM kernelSpectralFormInverse_meromorphicAt

lemma kernelSpectralResolvent_analyticAt_nonreal (z : ℂ) (hz : z.im≠0) :
    AnalyticAt ℂ kernelSpectralResolvent z := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (Ring.inverse (kernelSpectralFormOperator z))).comp_of_eq
    (kernelSpectralFormInverse_analyticAt_nonreal z hz) rfl

lemma kernelSpectralResolvent_graph (z : ℂ) (hz : IsUnit (kernelSpectralFormOperator z))
    (F : KernelQuotientL2) :
    (kernelSpectralResolvent z F,F+z•kernelSpectralResolvent z F)∈kernelEnergyLaplacian.graph := by
  apply kernelSpectralFormOperator_solution_graph z F
  have hi := congrArg (fun A : KernelEnergyGraph→L[ℂ]KernelEnergyGraph =>
    A (kernelVariationalSolution F)) (Ring.mul_inverse_cancel (kernelSpectralFormOperator z) hz)
  exact hi

lemma kernelSpectralResolvent_left_inverse (z : ℂ) (hz : IsUnit (kernelSpectralFormOperator z))
    (u : kernelEnergyLaplacian.domain) :
    kernelSpectralResolvent z (kernelEnergyLaplacian u-z•(u:KernelQuotientL2))=u := by
  rw [kernelSpectralResolvent_apply,←kernelSpectralFormOperator_of_domain z u]
  have hi := congrArg (fun A : KernelEnergyGraph→L[ℂ]KernelEnergyGraph =>
    A (kernelVariationalSolution (kernelEnergyLaplacian u+u)))
      (Ring.inverse_mul_cancel (kernelSpectralFormOperator z) hz)
  change Ring.inverse (kernelSpectralFormOperator z)
    (kernelSpectralFormOperator z (kernelVariationalSolution (kernelEnergyLaplacian u+u)))=
      kernelVariationalSolution (kernelEnergyLaplacian u+u) at hi
  rw [hi]
  exact kernelEnergyLaplacian_resolvent_relation u

lemma kernelSpectralResolvent_unique (z : ℂ) (hz : IsUnit (kernelSpectralFormOperator z))
    (u F : KernelQuotientL2) (hu : (u,F+z•u)∈kernelEnergyLaplacian.graph) :
    kernelSpectralResolvent z F=u := by
  let v : kernelEnergyLaplacian.domain := ⟨u,LinearPMap.mem_domain_of_mem_graph hu⟩
  have hv : kernelEnergyLaplacian v=F+z•u :=
    kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph v) hu rfl
  have hh := kernelSpectralResolvent_left_inverse z hz v
  rw [hv] at hh
  simpa only [v,add_sub_cancel_right] using hh

def kernelEisensteinSpectralParameter (s : ℂ) : ℂ := s*(2-s)

def kernelEisensteinResolvent (s : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelSpectralResolvent (kernelEisensteinSpectralParameter s)

lemma kernelEisensteinSpectralParameter_center :
    kernelEisensteinSpectralParameter (4/3)=8/9 := by
  norm_num [kernelEisensteinSpectralParameter]

lemma kernelEisensteinResolvent_meromorphicAt :
    MeromorphicAt kernelEisensteinResolvent (4/3:ℂ) := by
  have hh : MeromorphicAt kernelSpectralResolvent (kernelEisensteinSpectralParameter (4/3)) := by
    rw [kernelEisensteinSpectralParameter_center]
    exact kernelSpectralResolvent_meromorphicAt
  exact hh.comp_analyticAt (by unfold kernelEisensteinSpectralParameter; fun_prop)

lemma kernelEisensteinSpectralParameter_nonreal (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    (kernelEisensteinSpectralParameter s).im≠0 := by
  have he : (kernelEisensteinSpectralParameter s).im=2*(1-s.re)*s.im := by
    simp only [kernelEisensteinSpectralParameter,Complex.mul_im,Complex.sub_re,Complex.sub_im]
    norm_num
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hs.symm)) hi

lemma kernelEisensteinResolvent_analyticAt_nonreal (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ kernelEisensteinResolvent s := by
  exact (kernelSpectralResolvent_analyticAt_nonreal _
    (kernelEisensteinSpectralParameter_nonreal s hs hi)).comp_of_eq
      (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl

lemma kernelEisensteinResolvent_forcing_meromorphicAt
    (F : ℂ→KernelQuotientL2) (hF : MeromorphicAt F (4/3:ℂ)) :
    MeromorphicAt (fun s => kernelEisensteinResolvent s (F s)) (4/3:ℂ) :=
  meromorphicAt_clm_apply kernelEisensteinResolvent_meromorphicAt hF

lemma kernelEisensteinPencil_eventually_isUnit :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ), IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s)) := by
  have hc : ContinuousAt kernelEisensteinSpectralParameter (4/3:ℂ) := by
    unfold kernelEisensteinSpectralParameter
    fun_prop
  have hp : ∀ᶠ s : ℂ in 𝓝 (4/3:ℂ), IsUnit (kernelRegularPencil (kernelEisensteinSpectralParameter s)) := by
    have hh : ∀ᶠ z : ℂ in 𝓝 (kernelEisensteinSpectralParameter (4/3)), IsUnit (kernelRegularPencil z) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularPencil_eventually_isUnit
    exact hc.eventually hh
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds,
    eventually_ne_nhdsWithin (show (4/3:ℂ)≠2/3 by norm_num),self_mem_nhdsWithin] with s hs htwo hfour
  apply kernelSpectralFormOperator_isUnit_near _ _ hs
  intro he
  have hzero : (s-4/3)*(s-2/3)=0 := by
    have hid : (s-4/3)*(s-2/3)=(8/9:ℂ)-kernelEisensteinSpectralParameter s := by
      unfold kernelEisensteinSpectralParameter
      ring
    rw [hid,he,sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact hfour (sub_eq_zero.mp h)
  · exact htwo (sub_eq_zero.mp h)

def kernelEisensteinL2Correction (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    KernelQuotientL2 :=
  kernelEisensteinResolvent s (kernelL2Defect a b ha hab s)

lemma kernelEisensteinL2Correction_meromorphicAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelEisensteinL2Correction a b ha hab) (4/3:ℂ) :=
  kernelEisensteinResolvent_forcing_meromorphicAt _
    ((kernelL2Defect_entire a b ha hab).analyticAt (4/3)).meromorphicAt

lemma kernelEisensteinL2Correction_analyticAt_nonreal
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelEisensteinL2Correction a b ha hab) s := by
  exact ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
    (kernelL2Defect a b ha hab s,kernelEisensteinResolvent s)).comp₂
      ((kernelL2Defect_entire a b ha hab).analyticAt s)
      (kernelEisensteinResolvent_analyticAt_nonreal s hs hi)

lemma kernelEisensteinL2Correction_graph (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    (kernelEisensteinL2Correction a b ha hab s,
      kernelL2Defect a b ha hab s + kernelEisensteinSpectralParameter s •
        kernelEisensteinL2Correction a b ha hab s)∈kernelEnergyLaplacian.graph :=
  kernelSpectralResolvent_graph _ hs _

lemma kernelEisensteinL2Correction_graph_nonreal (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    (kernelEisensteinL2Correction a b ha hab s,
      kernelL2Defect a b ha hab s + kernelEisensteinSpectralParameter s •
        kernelEisensteinL2Correction a b ha hab s)∈kernelEnergyLaplacian.graph :=
  kernelEisensteinL2Correction_graph a b ha hab s
    (kernelSpectralFormOperator_isUnit_nonreal _ (kernelEisensteinSpectralParameter_nonreal s hs hi))

lemma kernelEisensteinL2Correction_graph_eventually (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ),
    (kernelEisensteinL2Correction a b ha hab s,
      kernelL2Defect a b ha hab s + kernelEisensteinSpectralParameter s •
        kernelEisensteinL2Correction a b ha hab s)∈kernelEnergyLaplacian.graph := by
  filter_upwards [kernelEisensteinPencil_eventually_isUnit] with s hs
  exact kernelEisensteinL2Correction_graph a b ha hab s hs

lemma kernelEisensteinL2Correction_unique (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s)))
    (u : KernelQuotientL2)
    (hu : (u,kernelL2Defect a b ha hab s+kernelEisensteinSpectralParameter s•u)∈kernelEnergyLaplacian.graph) :
    kernelEisensteinL2Correction a b ha hab s=u :=
  kernelSpectralResolvent_unique _ hs _ _ hu

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelThetaMassProjection : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM kernelThetaNull.starProjection

def kernelRegularL2Resolvent (z : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM (kernelRegularInverseLift z)

lemma kernelRegularL2Resolvent_analyticAt :
    AnalyticAt ℂ kernelRegularL2Resolvent (8/9:ℂ) := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (kernelRegularInverseLift (8/9))).comp_of_eq kernelRegularInverseLift_analyticAt rfl

lemma kernelSpectralResolvent_decomposition (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) (F : KernelQuotientL2) :
    kernelSpectralResolvent z F=((17/9)/(8/9-z):ℂ)•kernelThetaMassProjection F+
      kernelRegularL2Resolvent z F := by
  unfold kernelSpectralResolvent
  rw [←kernelLocalEnergyResolvent_eq_inverse z hne hz]
  simp only [kernelLocalEnergyResolvent,map_add,map_smul,_root_.add_apply,
    _root_.smul_apply,kernelThetaMassProjection,kernelRegularL2Resolvent]

def kernelEisensteinCorrectionNumerator (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    KernelQuotientL2 :=
  ((17/9)/(s-2/3):ℂ)•kernelThetaMassProjection (kernelL2Defect a b ha hab s)+
    (s-4/3)•kernelRegularL2Resolvent (kernelEisensteinSpectralParameter s)
      (kernelL2Defect a b ha hab s)

def kernelEisensteinResidueVector (a b : ℝ) (ha : 0<a) (hab : a<b) : KernelQuotientL2 :=
  (17/6:ℂ)•kernelThetaMassProjection (kernelL2Defect a b ha hab (4/3))

lemma kernelEisensteinCorrectionNumerator_center (a b : ℝ) (ha : 0<a) (hab : a<b) :
    kernelEisensteinCorrectionNumerator a b ha hab (4/3)=kernelEisensteinResidueVector a b ha hab := by
  simp only [kernelEisensteinCorrectionNumerator,kernelEisensteinResidueVector,sub_self,zero_smul,add_zero]
  congr 1
  norm_num

lemma kernelEisensteinCorrectionNumerator_analyticAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    AnalyticAt ℂ (kernelEisensteinCorrectionNumerator a b ha hab) (4/3:ℂ) := by
  have hf := (kernelL2Defect_entire a b ha hab).analyticAt (4/3:ℂ)
  have hp := (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2)
    (F := KernelQuotientL2) kernelThetaMassProjection (kernelL2Defect a b ha hab (4/3))).comp_of_eq hf rfl
  have hr : AnalyticAt ℂ (fun s => kernelRegularL2Resolvent (kernelEisensteinSpectralParameter s)) (4/3:ℂ) := by
    have hreg : AnalyticAt ℂ kernelRegularL2Resolvent (kernelEisensteinSpectralParameter (4/3)) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularL2Resolvent_analyticAt
    exact hreg.comp_of_eq (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl
  have happ := ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
    (kernelL2Defect a b ha hab (4/3),kernelRegularL2Resolvent (kernelEisensteinSpectralParameter (4/3)))).comp₂ hf hr
  have hscalar : AnalyticAt ℂ (fun s : ℂ => (17/9)/(s-2/3)) (4/3:ℂ) := by
    apply AnalyticAt.div analyticAt_const (analyticAt_id.sub analyticAt_const)
    norm_num
  exact (hscalar.smul hp).add ((analyticAt_id.sub analyticAt_const).smul happ)

lemma kernelEisensteinCorrectionNumerator_eventually (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ),
      (s-4/3)•kernelEisensteinL2Correction a b ha hab s=
        kernelEisensteinCorrectionNumerator a b ha hab s := by
  have hc : ContinuousAt kernelEisensteinSpectralParameter (4/3:ℂ) := by
    unfold kernelEisensteinSpectralParameter
    fun_prop
  have hp : ∀ᶠ s : ℂ in 𝓝 (4/3:ℂ), IsUnit (kernelRegularPencil (kernelEisensteinSpectralParameter s)) := by
    have hh : ∀ᶠ z : ℂ in 𝓝 (kernelEisensteinSpectralParameter (4/3)), IsUnit (kernelRegularPencil z) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularPencil_eventually_isUnit
    exact hc.eventually hh
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds,
    eventually_ne_nhdsWithin (show (4/3:ℂ)≠2/3 by norm_num),self_mem_nhdsWithin] with s hs htwo hfour
  have hfactor : (8/9:ℂ)-kernelEisensteinSpectralParameter s=(s-4/3)*(s-2/3) := by
    unfold kernelEisensteinSpectralParameter
    ring
  have hne : kernelEisensteinSpectralParameter s≠8/9 := by
    intro he
    have hh := mul_ne_zero (sub_ne_zero.mpr hfour) (sub_ne_zero.mpr htwo)
    rw [←hfactor,he,sub_self] at hh
    exact hh rfl
  change (s-4/3)•kernelSpectralResolvent (kernelEisensteinSpectralParameter s)
    (kernelL2Defect a b ha hab s)=_
  rw [kernelSpectralResolvent_decomposition _ hne hs,smul_add,smul_smul]
  have hscalar : (s-4/3)*((17/9)/(8/9-kernelEisensteinSpectralParameter s))=(17/9)/(s-2/3) := by
    rw [hfactor]
    have hcancel (x y c : ℂ) (hx : x≠0) : x*(c/(x*y))=c/y := by
      rw [div_eq_mul_inv,mul_inv_rev]
      calc
        _ = (x*x⁻¹)*(c*y⁻¹) := by ring
        _ = c/y := by rw [mul_inv_cancel₀ hx,one_mul,div_eq_mul_inv]
    exact hcancel _ _ _ (sub_ne_zero.mpr hfour)
  rw [hscalar]
  rfl

lemma kernelEisensteinResidueVector_limit (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)•kernelEisensteinL2Correction a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelEisensteinResidueVector a b ha hab)) := by
  apply (tendsto_congr' (kernelEisensteinCorrectionNumerator_eventually a b ha hab)).mpr
  rw [←kernelEisensteinCorrectionNumerator_center a b ha hab]
  exact (kernelEisensteinCorrectionNumerator_analyticAt a b ha hab).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

instance kernelThetaMassProjection_range_finiteDimensional :
    FiniteDimensional ℂ kernelThetaMassProjection.range := by
  let B : kernelThetaNull→L[ℂ]KernelQuotientL2 := kernelEnergyMass.comp kernelThetaNull.subtypeL
  have : FiniteDimensional ℂ B.range := LinearMap.finiteDimensional_range B.toLinearMap
  apply Submodule.finiteDimensional_of_le (S₂ := B.range)
  rintro y ⟨x,rfl⟩
  exact ⟨kernelThetaNull.orthogonalProjectionOnto (kernelEnergyMass.adjoint x),rfl⟩

lemma kernelEisensteinResidueVector_graph (a b : ℝ) (ha : 0<a) (hab : a<b) :
    (kernelEisensteinResidueVector a b ha hab,(8/9:ℂ)•kernelEisensteinResidueVector a b ha hab)
      ∈kernelEnergyLaplacian.graph := by
  let v : KernelEnergyGraph := (17/6:ℂ)•kernelThetaNull.starProjection
    (kernelVariationalSolution (kernelL2Defect a b ha hab (4/3)))
  have hv : kernelSpectralFormOperator (8/9) v=kernelVariationalSolution 0 := by
    change kernelSpectralFormOperator (8/9) ((17/6:ℂ)•kernelThetaNull.starProjection _)=_
    rw [map_smul]
    have hz : kernelSpectralFormOperator (8/9) (kernelThetaNull.starProjection
        (kernelVariationalSolution (kernelL2Defect a b ha hab (4/3))))=0 :=
      kernelThetaNull.starProjection_apply_mem _
    rw [hz,smul_zero,map_zero]
  have hh := kernelSpectralFormOperator_solution_graph (8/9) 0 v hv
  simpa only [v,map_smul,zero_add,kernelEisensteinResidueVector,kernelThetaMassProjection,
    kernelL2SandwichCLM,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,kernelVariationalSolution] using! hh

end CubicEisenstein

end

end OAI
end OAIOriginalModule0245

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.UnitNormalization
Source SHA256: d6e2c448f97f60cced629e1f7a390dfca1f6007537b1db256b9532206710c062
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0246


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CanonicalRowCompletion
open ConcreteTraceCRT (eisEmbedding)
open UniqueFactorizationMonoid

lemma good_prime_norm_mod_six (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) : Ideal.absNorm P%6=1 := by
  let : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  let : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  obtain ⟨χ,hχ⟩ : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,orderOf χ=6 := ⟨_,sexticChar_order P hg hc⟩
  have hdiv:=χ.orderOf_dvd_card_sub_one
  rw [hχ] at hdiv
  have hcard : 1<Fintype.card (ActualEisensteinCubic.O⧸P):=Fintype.one_lt_card
  have hn : Ideal.absNorm P=Fintype.card (ActualEisensteinCubic.O⧸P) := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  rw [hn]
  omega

lemma unit_sixth_exponent_mul (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (ha : a%6=1) (hb : b%6=1) :
    u.val^((a*b-1)/6)=u.val^((a-1)/6)*u.val^((b-1)/6) := by
  have ha' : a=6*(a/6)+1:=by omega
  have hb' : b=6*(b/6)+1:=by omega
  have hab : a*b=6*(a/6+b/6+6*((a/6)*(b/6)))+1 := by
    calc
      a*b=(6*(a/6)+1)*(6*(b/6)+1):=congrArg₂ (·*·) ha' hb'
      _ = _ := by ring
  have hab' : (a*b-1)/6=a/6+b/6+6*((a/6)*(b/6)):=by omega
  have hda : (a-1)/6=a/6:=by omega
  have hdb : (b-1)/6=b/6:=by omega
  rw [hab',hda,hdb,pow_add,pow_add,pow_mul,unit_pow_six,one_pow,mul_one]

private lemma multiset_unit_norm (u : ActualEisensteinCubic.Oˣ) (s : Multiset (Ideal ActualEisensteinCubic.O))
    (hs : ∀P∈s,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    (s.map (localRowValue u.val)).prod =
      eisEmbedding (u.val^(((s.map Ideal.absNorm).prod-1)/6)) ∧
      (s.map Ideal.absNorm).prod%6=1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons P s ih =>
    have hp:=hs P (Multiset.mem_cons_self _ _)
    let : P.IsMaximal:=hp.1
    have htail : ∀Q∈s,Q.IsMaximal ∧ lambda∉Q ∧ ringChar (ActualEisensteinCubic.O⧸Q)≠2:=
      fun Q hQ=>hs Q (Multiset.mem_cons_of_mem hQ)
    obtain ⟨hv,hn⟩:=ih htail
    have hP:=good_prime_norm_mod_six P hp.2.1 hp.2.2
    simp only [Multiset.map_cons,Multiset.prod_cons]
    refine ⟨?_,by rw [Nat.mul_mod,hP,hn]⟩
    rw [localRowValue_good _ P hp.2.1,actualSextic_unit_euler P hp.2.1 hp.2.2,hv]
    have hcard : Nat.card (ActualEisensteinCubic.O⧸P)=Ideal.absNorm P := by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
    rw [hcard,unit_sixth_exponent_mul u _ _ hP hn,map_mul]

theorem idealRowHom_unit_norm (u : ActualEisensteinCubic.Oˣ) (I : Ideal ActualEisensteinCubic.O) (hI : I≠0)
    (hgood : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    idealRowHom u.val I=eisEmbedding (u.val^((Ideal.absNorm I-1)/6)) := by
  have hn (s : Multiset (Ideal ActualEisensteinCubic.O)) : (s.map Ideal.absNorm).prod=Ideal.absNorm s.prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih => simp only [Multiset.map_cons,Multiset.prod_cons,map_mul,ih]
  have hh:=(multiset_unit_norm u (normalizedFactors I) hgood).1
  rw [hn,Ideal.prod_normalizedFactors_eq_self hI] at hh
  change (if I=0 then 0 else _) = _
  rwa [ite_eq_right hI]

lemma ideal_norm_mod_six_of_good (I : Ideal ActualEisensteinCubic.O) (hI : I≠0)
    (hgood : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    Ideal.absNorm I%6=1 := by
  have hn (s : Multiset (Ideal ActualEisensteinCubic.O)) : (s.map Ideal.absNorm).prod=Ideal.absNorm s.prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih => simp only [Multiset.map_cons,Multiset.prod_cons,map_mul,ih]
  have hh:=(multiset_unit_norm (1:ActualEisensteinCubic.Oˣ) (normalizedFactors I) hgood).2
  rwa [hn,Ideal.prod_normalizedFactors_eq_self hI] at hh

theorem idealRowHom_unit_eq_of_norm_mod_thirty_six (u : ActualEisensteinCubic.Oˣ) (I J : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hJ : J≠0)
    (hgI : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (hgJ : ∀P∈normalizedFactors J,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (hmod : Ideal.absNorm I%36=Ideal.absNorm J%36) :
    idealRowHom u.val I=idealRowHom u.val J := by
  rw [idealRowHom_unit_norm u I hI hgI,idealRowHom_unit_norm u J hJ hgJ]
  have hmi:=ideal_norm_mod_six_of_good I hI hgI
  have hmj:=ideal_norm_mod_six_of_good J hJ hgJ
  have hm : (Ideal.absNorm I-1)/6 ≡ (Ideal.absNorm J-1)/6 [MOD 6] := by
    dsimp [Nat.ModEq]
    omega
  exact congrArg eisEmbedding (pow_eq_pow_of_modEq hm (unit_pow_six u))

theorem rowTwist_unit_norm (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z n : ActualEisensteinCubic.O) (u : ActualEisensteinCubic.Oˣ)
    (hn : n≠0)
    (hgood : ∀P∈normalizedFactors (Ideal.span {n}),
      P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    rowTwist Ψ m f (u.val*z) n = rowTwist Ψ m f z n *
      eisEmbedding (u.val^((Ideal.absNorm (Ideal.span {n})-1)/6)) := by
  change Ψ n*idealRowHom (m^6*f^4*(u.val*z)) (Ideal.span {n}) =
    (Ψ n*idealRowHom (m^6*f^4*z) (Ideal.span {n}))*_
  rw [show m^6*f^4*(u.val*z)=u.val*(m^6*f^4*z) by ring,
    idealRowHom_argument_mul,
    idealRowHom_unit_norm u _ (Ideal.span_singleton_eq_bot.not.mpr hn) hgood]
  ring

end CanonicalUnitEuler

namespace CompletedGauss
open ActualEisensteinCubic CompletedDyadic

theorem normalized_cusp_coefficient (d ζ : ℂ) (m n b : ℝ) (hn : 0<n) (hb : 0<b) :
    ζ*(d/((Real.sqrt ((3:ℝ)^m*n*b^3):ℝ):ℂ)) =
      (4/3:ℂ)*(81*ζ)*(normalizedCuspAmplitude d m b /
        ((4*(3:ℝ)^(m/3)*Real.sqrt n*b:ℝ):ℂ)) := by
  have ha : (3:ℝ)^(m/6)*Real.sqrt b≠0:=by positivity
  have hs : Real.sqrt ((3:ℝ)^m*n*b^3)≠0:=by positivity
  have hr : (3:ℝ)^(m/3)*Real.sqrt n*b≠0:=by positivity
  have hid:=cusp_coefficient_normalization m n b hn hb
  have hcross : ((3:ℝ)^(m/6)*Real.sqrt b)*((3:ℝ)^(m/3)*Real.sqrt n*b)=
      Real.sqrt ((3:ℝ)^m*n*b^3) := by
    have hh:=(div_eq_div_iff hs hr).mp hid
    simpa only [one_mul] using hh
  have hc := congrArg (fun x:ℝ=>(x:ℂ)) hcross
  push_cast at hc
  unfold normalizedCuspAmplitude
  have hsa : (((3:ℝ)^(m/6):ℝ):ℂ)≠0:=by exact_mod_cast (Real.rpow_pos_of_pos (by norm_num) (m/6)).ne'
  have hsb : ((Real.sqrt b:ℝ):ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hb).ne'
  have hsr : (((3:ℝ)^(m/3):ℝ):ℂ)≠0:=by exact_mod_cast (Real.rpow_pos_of_pos (by norm_num) (m/3)).ne'
  have hsn : ((Real.sqrt n:ℝ):ℂ)≠0:=by exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
  have hbc : (b:ℂ)≠0:=by exact_mod_cast hb.ne'
  rw [←hc]
  push_cast
  field_simp
  ; ring

theorem normalized_reflection_weight (ζ : ℂ) (hζ : ‖ζ‖≤(1:ℝ)/81) :
    ‖(81:ℂ)*ζ‖≤1 := by
  rw [norm_mul]
  norm_num
  linarith

theorem normalized_cusp_coefficient_nat (d ζ : ℂ) (m : ℕ) (n b : ℝ)
    (hn : 0<n) (hb : 0<b) :
    ζ*(d/((Real.sqrt ((3:ℝ)^((m:ℝ)-4)*n*b^3):ℝ):ℂ)) =
      (4/3:ℂ)*(81*ζ)*(normalizedCuspAmplitude d ((m:ℝ)-4) b /
        ((4*ramifiedScale completedRamifiedInitial completedRamifiedStep m*Real.sqrt n*b:ℝ):ℂ)) := by
  rw [actual_ramified_scale]
  exact normalized_cusp_coefficient d ζ ((m:ℝ)-4) n b hn hb

theorem reflection_kernel_scale (X r c0 C K U B k n b D E : ℝ)
    (hX : 0<X) (hc0 : 0<c0) (hC : 0<C) (hK : 0<K) (hU : 0<U) (hB : 0<B)
    (hk : 0<k) (hn : 0<n) (hb : 0<b) (hD : 0<D) (hE : 0<E) :
    ((K^2*C^2/((X/c0^2)*D*E^3))⁻¹*r^3*B^3*U)*
      Real.exp (-2*Real.log (k/K)+Real.log (n/U)+3*Real.log (b/B)) =
      r^3*(D*n)*(E*b)^3*X/(k^2*(c0*C)^2) := by
  rw [positive_log_scale_identity k n b K U B _ hk hn hb hK hU hB]
  field_simp

theorem completed_branch_kernel_argument {ι : Type*} [Fintype ι]
    (P : ι→Ideal ActualEisensteinCubic.O) (hP : ∀i,P i≠0) (e : ι→Fin 3)
    (K X c0 r U B : ℝ) (I F Q H N V : Ideal ActualEisensteinCubic.O)
    (hX : 0<X) (hc0 : 0<c0) (hK : 0<completedResidualScale K I Q)
    (hU : 0<U) (hB : 0<B) (hH : H≠0) (hN : N≠0) (hV : V≠0) :
    ((completedBranchScale K (X/c0^2) I F Q P e)⁻¹*r^3*B^3*U)*
      Real.exp (-2*Real.log ((Ideal.absNorm H:ℝ)/completedResidualScale K I Q)+
        Real.log ((Ideal.absNorm N:ℝ)/U)+3*Real.log ((Ideal.absNorm V:ℝ)/B)) =
      r^3*(Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1*N):ℝ)*
        (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2*V):ℝ)^3*X/
        ((Ideal.absNorm H:ℝ)^2*(c0*(Ideal.absNorm (∏i,P i):ℝ))^2) := by
  have hnorm (J : Ideal ActualEisensteinCubic.O) (hj : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz=>hj (Ideal.absNorm_eq_zero_iff.mp hz))
  have hp : (∏i,P i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hP i)
  have hD:=reflectionExtractedDivisor_ne_zero P hP (fun i=>completedLocalExponent I F (P i)) e 1
  have hE:=reflectionExtractedDivisor_ne_zero P hP (fun i=>completedLocalExponent I F (P i)) e 2
  simpa only [completedBranchScale,map_mul,Nat.cast_mul] using
    reflection_kernel_scale X r c0 (Ideal.absNorm (∏i,P i):ℝ) (completedResidualScale K I Q) U B
      (Ideal.absNorm H:ℝ) (Ideal.absNorm N:ℝ) (Ideal.absNorm V:ℝ)
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 1):ℝ)
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i=>completedLocalExponent I F (P i)) e 2):ℝ)
      hX hc0 (hnorm _ hp) hK hU hB (hnorm _ hH) (hnorm _ hN) (hnorm _ hV) (hnorm _ hD) (hnorm _ hE)

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem shortEnergy_scalar_normalization (C H R Z K X F G ε : ℝ)
    (hC : 0≤C) (hH : 0≤H) (hR : 0≤R) (hZ : 1≤Z) (hK : 0≤K)
    (hX : 0<X) (hF : 0≤F) (hG : 1≤G) (hε : 0≤ε)
    (hFZ : F≤Z^3) (hmass : X*F≤Z^3)
    (hmargin : (2*K)*G≤X*F*Z^(-((1:ℝ)/40))) :
    2*X*((C*H)*R*((2*K)*G*F)^ε*(K*F)*Z^ε)≤
      (C*H)*R*(X*F)^2*Z^(7*ε-(1:ℝ)/40) := by
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hs : Z^(-((1:ℝ)/40))≤1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hZ (by norm_num : -((1:ℝ)/40)≤0)
  have hp : (2*K)*G*F≤Z^6 := by
    calc
      _ ≤ (X*F*Z^(-((1:ℝ)/40)))*F:=mul_le_mul_of_nonneg_right hmargin hF
      _ ≤ (X*F)*F:=mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (mul_one _)) hF
      _ ≤ (Z^3)*(Z^3):=mul_le_mul hmass hFZ hF (by positivity)
      _ = _:=by ring
  have hpow : ((2*K)*G*F)^ε≤Z^(6*ε) := by
    apply (Real.rpow_le_rpow (by positivity) hp hε).trans_eq
    rw [←Real.rpow_natCast_mul hZ0.le]
    norm_num
  have hrow : 2*K≤X*F*Z^(-((1:ℝ)/40)) :=
    (le_mul_of_one_le_right (by positivity) hG).trans hmargin
  have hnorm : 2*X*(K*F)≤(X*F)^2*Z^(-((1:ℝ)/40)) := by
    calc
      _ = (X*F)*(2*K):=by ring
      _ ≤ (X*F)*(X*F*Z^(-((1:ℝ)/40))):=mul_le_mul_of_nonneg_left hrow (by positivity)
      _ = _:=by ring
  calc
    _ = (C*H)*R*((2*K)*G*F)^ε*(2*X*(K*F))*Z^ε:=by ring
    _ ≤ (C*H)*R*Z^(6*ε)*((X*F)^2*Z^(-((1:ℝ)/40)))*Z^ε:=by gcongr
    _ = _:=by
      rw [show 7*ε-(1:ℝ)/40=6*ε+(-((1:ℝ)/40))+ε by ring,
        Real.rpow_add hZ0,Real.rpow_add hZ0]
      ring

theorem canonicalShortEnergy_normalized_uniform_twist
    (a b : ℝ) (ha : 0<a) (ε ρ q levelBound : ℝ)
    (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃d : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^((1:ℝ)/1000) → 0<X → X*F≤Z^3 →
    ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∀(labels : Finset (Ideal ActualEisensteinCubic.O)),labels⊆idealRange F →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),(∀x,‖Ψ x‖≤1) → ∀(mask : ActualEisensteinCubic.O) (lengthScale : ℂ),
      (∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        HasExactCompletedDyadicModels rays (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ) (CompletedUnitRows.unitRowFamily Ψ mask u f) lengthScale) →
      2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ)
        mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000))) K≤
      (C*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*(X*F)^2*Z^(7*ε-(1:ℝ)/40) := by
  obtain ⟨d,hbound⟩:=canonicalShortEnergy_uniform_twist a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩:=hbound W hs hW
  refine ⟨C,hC,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ hX hmass G hG hbad hmargin labels hlabels Ψ hΨ mask lengthScale hmodels
  have he:=hb θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin labels hlabels Ψ hΨ mask lengthScale hmodels
  have hFZ' : F≤Z^3 := by
    apply hFZ.trans
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
  have hGN : 1≤(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz=>hG (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscalar:=shortEnergy_scalar_normalization C ((1+‖θ‖)^d) ((rays:ℝ)^2*‖lengthScale‖^2)
    Z K X F (Ideal.absNorm G:ℝ) ε hC (by positivity) (by positivity) hZ
    (zero_le_one.trans hK) hX (zero_le_one.trans hF) hGN hε.le hFZ' hmass hmargin
  apply (mul_le_mul_of_nonneg_left he (by positivity : 0≤2*X)).trans
  convert hscalar using 1 <;> ring

end CanonicalRowCompletion

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma rowCoordinates_zero : rowCoordinates (0 : Fin 2 → ActualEisensteinCubic.O)=0 := by
  apply norm_le_zero_iff.mp
  have h := coordinates_norm_bound (0 : Fin 2 → ActualEisensteinCubic.O)
  have he : (fun i : Fin 2 => eisEmbedding ((0 : Fin 2 → ActualEisensteinCubic.O) i))=0 := by
    funext i
    exact map_zero _
  rw [he,norm_zero,mul_zero] at h
  exact h

lemma rowCoordinates_norm_pos {u : Fin 2 → ActualEisensteinCubic.O} (hu : u≠0) :
    0<‖rowCoordinates u‖ := by
  apply norm_pos_iff.mpr
  intro h
  exact hu (rowCoordinates_injective (h.trans rowCoordinates_zero.symm))

lemma rowCoordinates_le_horizontal (u : Fin 2 → ActualEisensteinCubic.O) (z : ℂ) (hz : ‖z‖≤1) :
    ‖rowCoordinates u‖≤2*(‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖+
      ‖eisEmbedding (u 0)‖) := by
  apply (coordinates_norm_bound u).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · simp only [Fin.zero_eta]
    linarith [norm_nonneg (eisEmbedding (u 0)*z+eisEmbedding (u 1))]
  · have h : ‖eisEmbedding (u 1)‖≤
        ‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖+‖eisEmbedding (u 0)*z‖ := by
      simpa only [add_sub_cancel_left] using
        norm_sub_le (eisEmbedding (u 0)*z+eisEmbedding (u 1)) (eisEmbedding (u 0)*z)
    rw [norm_mul] at h
    have hm := mul_le_mul_of_nonneg_left hz (norm_nonneg (eisEmbedding (u 0)))
    rw [mul_one] at hm
    exact h.trans (add_le_add_right hm _)

lemma height_times_coordinate_bound (A c v N : ℝ)
    (_hA : 0≤A) (hc : 1≤c) (hv : 1/2≤v) (hN : N≤2*(A+c)) :
    N*v≤5*(A^2+c^2*v^2) := by
  have hv0 : 0≤v := by linarith
  have hcv : v≤c*v := by nlinarith
  have hcv0 : 1/2≤c*v := by linarith
  have hv2 : v^2≤(c*v)^2 := by nlinarith
  have hcross : 2*v*A≤A^2+c^2*v^2 := by nlinarith [sq_nonneg (A-v)]
  have hlin : 2*c*v≤4*(c*v)^2 := by nlinarith
  have hNv := mul_le_mul_of_nonneg_right hN hv0
  nlinarith [sq_nonneg A]

lemma rowHeight_times_coordinates (u : Fin 2 → ActualEisensteinCubic.O) (hu : u 0≠0)
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) :
    (v/(‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖^2+
       ‖eisEmbedding (u 0)‖^2*v^2))*‖rowCoordinates u‖≤5 := by
  have hc : 1≤‖eisEmbedding (u 0)‖ := by
    have hh := one_le_normSq_embedding (u 0) hu
    rw [Complex.normSq_eq_norm_sq] at hh
    nlinarith [norm_nonneg (eisEmbedding (u 0))]
  have hden : 0<‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖^2+
      ‖eisEmbedding (u 0)‖^2*v^2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  simpa only [mul_comm v] using
    height_times_coordinate_bound _ _ _ _ (norm_nonneg _) hc hv
      (rowCoordinates_le_horizontal u z hz)

lemma positive_rpow_of_product_bound (h N C σ : ℝ)
    (hh : 0≤h) (hN : 0<N) (hC : 0≤C) (hσ : 0≤σ) (hb : h*N≤C) :
    h^σ≤C^σ*N^(-σ) := by
  have hdiv : h≤C/N := (le_div_iff₀ hN).mpr hb
  have hr := Real.rpow_le_rpow hh hdiv hσ
  rw [Real.div_rpow hC hN.le,div_eq_mul_inv] at hr
  simpa only [Real.rpow_neg hN.le] using hr

def cuspRemainderProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  positiveHeightPower s v-cuspSeedProfile a b s v

lemma cuspRemainderProfile_norm_le (a b : ℝ) (s : ℂ) (v : ℝ) (hv : 0<v) :
    ‖cuspRemainderProfile a b s v‖≤v^s.re := by
  have hnon : 0≤1-cuspTransition a b v := sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hle : 1-cuspTransition a b v≤1 := by
    have := Real.smoothTransition.nonneg ((v-a)/(b-a))
    change 0≤cuspTransition a b v at this
    linarith
  have he : cuspRemainderProfile a b s v=
      ((1-cuspTransition a b v:ℝ):ℂ)*positiveHeightPower s v := by
    simp only [cuspRemainderProfile,cuspSeedProfile,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  rw [he,norm_mul,Complex.norm_of_nonneg hnon,positiveHeightPower_eq_cpow s v hv,
    Complex.norm_cpow_eq_rpow_re_of_pos hv]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hv.le _) hle

lemma cuspRemainderProfile_zero (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hv : 0<v) (hbv : b≤v) : cuspRemainderProfile a b s v=0 := by
  rw [cuspRemainderProfile,cuspSeedProfile_incoming a b s v hab hbv hv,
    positiveHeightPower_eq_cpow s v hv,sub_self]

lemma cuspRemainderProfile_norm_le_bound (a b : ℝ) (s : ℂ) (v : ℝ)
    (hab : a<b) (hb : 0≤b) (hv : 0<v) (hs : 0≤s.re) :
    ‖cuspRemainderProfile a b s v‖≤b^s.re := by
  by_cases h : b≤v
  · rw [cuspRemainderProfile_zero a b s v hab hv h,norm_zero]
    exact Real.rpow_nonneg hb _
  · exact (cuspRemainderProfile_norm_le a b s v hv).trans
      (Real.rpow_le_rpow hv.le (le_of_not_ge h) hs)

end

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_row_embedding_ne_zero {u : Fin 2 → ActualEisensteinCubic.O} (hu : u≠0) :
    (eisEmbedding ∘ u)≠0 := by
  intro h
  apply hu
  funext i
  apply eisEmbedding_injective
  simpa only [Function.comp_apply,Pi.zero_apply,map_zero] using congrFun h i

lemma coprime_row_ne_zero {u : Fin 2 → ActualEisensteinCubic.O} (h : IsCoprime (u 0) (u 1)) : u≠0 := by
  intro hz
  have hh : (0 : ActualEisensteinCubic.O)=1 := by
    simpa only [hz,Pi.zero_apply,isCoprime_zero_left,isUnit_zero_iff] using h
  exact zero_ne_one hh

theorem cuspRemainderProfile_row_bound (a b : ℝ) (s : ℂ)
    (hab : a<b) (hb : 0≤b) (hs : 0≤s.re)
    (u : Fin 2 → ActualEisensteinCubic.O) (hcop : IsCoprime (u 0) (u 1))
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) :
    ‖cuspRemainderProfile a b s (transformedHeight z v (eisEmbedding ∘ u))‖≤
      (max 5 (2*b))^s.re*‖rowCoordinates u‖^(-s.re) := by
  have hu := coprime_row_ne_zero hcop
  have hN := rowCoordinates_norm_pos hu
  have hv0 : 0<v := by linarith
  have hh : 0<transformedHeight z v (eisEmbedding ∘ u) :=
    div_pos hv0 (heightDenominator_pos z v hv0 _ (integral_row_embedding_ne_zero hu))
  have hC : 0≤max 5 (2*b) := (by norm_num : (0:ℝ)≤5).trans (le_max_left _ _)
  by_cases hc : u 0=0
  · have hunit : IsUnit (u 1) := by simpa only [hc,isCoprime_zero_left] using hcop
    obtain ⟨d,hd⟩ := hunit
    have hdnorm : ‖eisEmbedding (u 1)‖=1 := by
      rw [←hd]
      exact GaussGeneratorTransport.norm_eisEmbedding_unit d
    have hn : ‖rowCoordinates u‖≤2 := by
      apply (coordinates_norm_bound u).trans
      have hm : ‖fun i => eisEmbedding (u i)‖≤1 := by
        apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro i
        fin_cases i
        · change ‖eisEmbedding (u 0)‖≤1
          simp only [hc,map_zero,norm_zero,zero_le_one]
        · exact hdnorm.le
      nlinarith
    apply (cuspRemainderProfile_norm_le_bound a b s _ hab hb hh hs).trans
    exact positive_rpow_of_product_bound b _ _ _ hb hN hC hs
      (by nlinarith [mul_le_mul_of_nonneg_left hn hb,le_max_right (5 : ℝ) (2*b)])
  · apply (cuspRemainderProfile_norm_le a b s _ hh).trans
    apply positive_rpow_of_product_bound _ _ _ _ hh.le hN hC hs
    exact (rowHeight_times_coordinates u hc z hz v hv).trans (le_max_left _ _)

def translatedCuspRow (M : SL(2,ActualEisensteinCubic.O)) (r : CuspCosets) : Fin 2 → ActualEisensteinCubic.O :=
  Matrix.vecMul (cosetRow r) (M : Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O)

lemma translatedCuspRow_injective (M : SL(2,ActualEisensteinCubic.O)) : Function.Injective (translatedCuspRow M) := by
  intro r t h
  apply cosetRow_injective
  have hh := congrArg (fun u : Fin 2 → ActualEisensteinCubic.O => Matrix.vecMul u
    ((M⁻¹ : SL(2,ActualEisensteinCubic.O)) : Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O)) h
  simpa only [translatedCuspRow,Matrix.vecMul_vecMul,←Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.vecMul_one] using hh

lemma integral_bottom_coprime (M : SL(2,ActualEisensteinCubic.O)) : IsCoprime (M 1 0) (M 1 1) := by
  have hd : M 0 0*M 1 1-M 0 1*M 1 0=1 := by
    simpa only [Matrix.det_fin_two] using M.property
  refine ⟨-M 0 1,M 0 0,?_⟩
  linear_combination hd

lemma translatedCuspRow_coprime (M : SL(2,ActualEisensteinCubic.O)) (r : CuspCosets) :
    IsCoprime (translatedCuspRow M r 0) (translatedCuspRow M r 1) := by
  induction r using Quotient.inductionOn with
  | _ N =>
    change IsCoprime (translatedCuspRow M (cosetOf N) 0) (translatedCuspRow M (cosetOf N) 1)
    simpa only [translatedCuspRow,cosetRow_cosetOf,row,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Matrix.vecMul,dotProduct] using integral_bottom_coprime ((N : SL(2,ActualEisensteinCubic.O))*M)

lemma cosetHeight_integral_chart (M : SL(2,ActualEisensteinCubic.O)) (r : CuspCosets)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    cosetHeight r (integralComplexMatrix M • upperPoint z v hv)=
      transformedHeight z v (eisEmbedding ∘ translatedCuspRow M r) := by
  induction r using Quotient.inductionOn with
  | _ N =>
    change cosetHeight (cosetOf N) (integralComplexMatrix M • upperPoint z v hv)=
      transformedHeight z v (eisEmbedding ∘ translatedCuspRow M (cosetOf N))
    rw [cosetHeight_cosetOf,←integralComplexMatrix_levelThree,
      ←mul_smul,←map_mul,hyperbolicHeight_action_upperPoint]
    simp only [integralComplexMatrix_apply,transformedHeight,heightDenominator,
      Function.comp_apply,translatedCuspRow,cosetRow_cosetOf,row,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Matrix.vecMul,dotProduct]

lemma translated_remainder_majorant (a b : ℝ) (s : ℂ)
    (hab : a<b) (hb : 0≤b) (hs : 0≤s.re)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v)
    (hv0 : 0<v) (r : CuspCosets) :
    ‖(cosetCharacter r)⁻¹*cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖≤
      (max 5 (2*b))^s.re*‖rowCoordinates (translatedCuspRow M r)‖^(-s.re) := by
  rw [norm_mul,norm_inv,norm_cosetCharacter,inv_one,one_mul,cosetHeight_integral_chart]
  exact cuspRemainderProfile_row_bound a b s hab hb hs _
    (translatedCuspRow_coprime M r) z hz v hv

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff MatrixGroups

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma cuspCutoffTerm_eq_seedProfile (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (r : CuspCosets) (w : HyperbolicSpace) :
    cuspCutoffTerm 1 (cuspSeedProfile a b s) r w=
      (cosetCharacter r)⁻¹*cuspSeedProfile a b s (cosetHeight r w) := by
  unfold cuspCutoffTerm
  split_ifs with h
  · rfl
  · rw [cuspSeedProfile_zero a b s _ hab ((le_of_not_gt h).trans ha),mul_zero]

lemma cusp_seed_profile_summable (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (w : HyperbolicSpace) :
    Summable (fun r : CuspCosets => (cosetCharacter r)⁻¹*
      cuspSeedProfile a b s (cosetHeight r w)) :=
  (cuspCutoffTerm_summable 1 le_rfl _ w).congr
    (fun r => cuspCutoffTerm_eq_seedProfile a b ha hab s r w)

theorem eisenstein_sub_seed_eq_series (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (w : HyperbolicSpace) :
    hyperbolicEisenstein s w-smoothCuspSeed a b s w=
      ∑'r : CuspCosets,(cosetCharacter r)⁻¹*
        cuspRemainderProfile a b s (cosetHeight r w) := by
  have hE := (height_series_summable_norm s hs w).of_norm
  have hS := cusp_seed_profile_summable a b ha hab s w
  have heq : smoothCuspSeed a b s w=∑'r : CuspCosets,
      (cosetCharacter r)⁻¹*cuspSeedProfile a b s (cosetHeight r w) := by
    unfold smoothCuspSeed cuspCutoffCorrection
    exact tsum_congr (fun r => cuspCutoffTerm_eq_seedProfile a b ha hab s r w)
  rw [hyperbolicEisenstein_eq_height_series,heq,←hE.tsum_sub hS]
  apply tsum_congr
  intro r
  rw [cuspRemainderProfile,positiveHeightPower_eq_cpow s _ (cosetHeight_pos r w)]
  ring

def eisensteinRemainderBound (b : ℝ) (s : ℂ) : ℝ :=
  (max 5 (2*b))^s.re * ∑'n : (Fin 2×Fin 2)→ℤ,‖n‖^(-s.re)

lemma eisensteinRemainderBound_nonneg (b : ℝ) (s : ℂ) :
    0≤eisensteinRemainderBound b s :=
  mul_nonneg (Real.rpow_nonneg ((by norm_num : (0:ℝ)≤5).trans (le_max_left _ _)) _)
    (tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _))

theorem eisenstein_sub_seed_chart_bound (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (M : SL(2,ActualEisensteinCubic.O))
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) (hv0 : 0<v) :
    ‖hyperbolicEisenstein s (integralComplexMatrix M • upperPoint z v hv0)-
      smoothCuspSeed a b s (integralComplexMatrix M • upperPoint z v hv0)‖≤
      eisensteinRemainderBound b s := by
  let G : ((Fin 2×Fin 2)→ℤ)→ℝ := fun n => (max 5 (2*b))^s.re*‖n‖^(-s.re)
  let f : CuspCosets→(Fin 2×Fin 2)→ℤ := fun r => rowCoordinates (translatedCuspRow M r)
  let R : CuspCosets→ℂ := fun r => (cosetCharacter r)⁻¹*cuspRemainderProfile a b s
    (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))
  have hg : Summable G := (summable_integer_four_rpow s.re hs).mul_left _
  have hi : Function.Injective f := rowCoordinates_injective.comp (translatedCuspRow_injective M)
  have hb : ∀r,‖R r‖≤G (f r) :=
    translated_remainder_majorant a b s hab (by linarith) (by linarith) M z hz v hv hv0
  have hr : Summable (fun r => ‖R r‖) :=
    (hg.comp_injective hi).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  rw [eisenstein_sub_seed_eq_series a b ha hab s (by linarith)]
  change ‖∑'r,R r‖≤eisensteinRemainderBound b s
  apply (norm_tsum_le_tsum_norm hr).trans
  have hsum : (∑'r,‖R r‖)≤∑'n,G n :=
    Summable.tsum_le_tsum_of_inj f hi (fun _ _ => by dsimp [G]; positivity) hb hr hg
  simpa only [G,tsum_mul_left,eisensteinRemainderBound] using hsum

theorem eisenstein_sub_seed_bounded (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) (w : HyperbolicSpace) :
    ‖hyperbolicEisenstein s w-smoothCuspSeed a b s w‖≤eisensteinRemainderBound b s := by
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  have hz1 : ‖z‖≤1 := by
    rw [Complex.normSq_eq_norm_sq] at hz
    nlinarith [norm_nonneg z]
  have hv1 : 1/2≤v := by
    have hh := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hh0 := Real.sqrt_nonneg (2/3 : ℝ)
    nlinarith
  have hw : w=integralComplexMatrix M⁻¹ • upperPoint z v hv := by
    rw [←hMw,map_inv,inv_smul_smul]
  rw [hw]
  exact eisenstein_sub_seed_chart_bound a b ha hab s hs M⁻¹ z hz1 v hv1 hv

lemma cuspRemainderProfile_measurable (a b : ℝ) (s : ℂ) :
    Measurable (cuspRemainderProfile a b s) := by
  unfold cuspRemainderProfile cuspSeedProfile positiveHeightPower logRatioPower cuspTransition
  fun_prop

lemma eisenstein_sub_seed_measurable (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) :
    Measurable (fun w => hyperbolicEisenstein s w-smoothCuspSeed a b s w) := by
  simp_rw [eisenstein_sub_seed_eq_series a b ha hab s hs]
  apply Measurable.tsum
  intro r
  exact measurable_const.mul ((cuspRemainderProfile_measurable a b s).comp
    (cosetHeight_continuous r).measurable)

theorem kernel_eisenstein_sub_seed_memLp (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4<s.re) :
    MemLp (fun q => kernelQuotientEisenstein s (by linarith) q-
      kernelQuotientSeed a b s q) 2 (integralQuotientVolume globalKubotaKernel) := by
  have hmeas : Measurable (fun q => kernelQuotientEisenstein s (by linarith) q-
      kernelQuotientSeed a b s q) :=
    measurable_from_quotient.mpr (eisenstein_sub_seed_measurable a b ha hab s (by linarith))
  apply MemLp.of_bound hmeas.aestronglyMeasurable (eisensteinRemainderBound b s)
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact eisenstein_sub_seed_bounded a b ha hab s hs w

end CubicEisenstein

end

end OAI
end OAIOriginalModule0246

/-! Original module: OAI.NumberTheory.DirichletL.RowCompletion.CompletedEnergy
Source SHA256: 85c10fcf824fc7f06e7b408b575d4a9cb40803596839a147e9d6e1a2052c6d64
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0247


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCoefficientClass (IsBaseRayTwist)

def outsideLogEnergy (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O)) (V : ℝ→ℂ) (X K : ℝ) : ℝ :=
  let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
  let hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
    (poolPrimary_good P hP) Finset.univ Ψ m labels V X K

theorem outsideLogEnergy_eq_completed
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (V : ℝ→ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) (X K : ℝ) (hX : 0<X) :
    outsideLogEnergy S D hbad Ψ m labels V X K=
      rowFamilyEnergy labels (fun I z=>outsideCanonicalRow S D hbad Ψ m (idealGenerator I) z
        (radialFromLog V hVs A hV) X) K := by
  exact canonicalLogEnergy_eq_completed_rows S D hbad Ψ m labels V hVs A hV X K hX

def HasCanonicalThetaModels (S : Finset (Ideal ActualEisensteinCubic.O)) (base : ActualEisensteinCubic.O→*ℂ)
    (ρ q levelBound : ℝ) : Prop :=
  ∀(A : ℝ),0≤A → ∀(W : ℝ→ℂ),
    Function.support W⊆Set.Icc (Real.exp (-A)) (Real.exp A) → ContDiff ℝ ∞ W →
    ∀κ : ℝ,0<κ → ∃C : ℝ,0≤C ∧
    ∀(Z K X F θ : ℝ),1≤Z → 1≤K → 0<X → 1≤F → F≤Z^((1:ℝ)/1000) →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),IsBaseRayTwist base Ψ → ∀m : ActualEisensteinCubic.O,m≠0 →
    let G : Ideal ActualEisensteinCubic.O:=Ideal.span {m*excludedGenerator S}
    (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∃(rays : ℕ) (lengthScale : ℂ),(rays:ℝ)^2*‖lengthScale‖^2≤C*Z^κ ∧
      ∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        HasExactCompletedDyadicModels rays
          (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ)
          (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) lengthScale

theorem outsideLogEnergy_terminal_constant
    (V : ℝ→ℂ) (hVs : ContDiff ℝ ∞ V) (A : ℝ)
    (hV : ∀s,V s≠0→|s|≤A) :
    ∃C : ℝ,0≤C ∧ ∀(S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
      (base : ActualEisensteinCubic.O→*ℂ) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (X F K t : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      (∀u,‖base u‖≤1) → 1<Z → 0≤η → 3000*η≤(1:ℝ)/40 →
      (fixedDepthRank Z K=0 ∨ X≤1) →
      outsideLogEnergy S D hbad (normHeightTwist Ψ t) m labels V X K≤C*(X*F)^2 := by
  have hVc : HasCompactSupport V :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (fun s hs=>abs_le.mp (hV s hs))
  let v : 𝓢(ℝ,ℂ):=hVc.toSchwartzMap hVs
  let M:=SchwartzMap.seminorm ℝ 0 0 v
  refine ⟨canonicalTerminalConstant A M,canonicalTerminalConstant_nonneg A M,?_⟩
  intro S D hbad base Z η Ψ m labels X F K t hstate hbase hZ hη hbudget hstop
  let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  have hinj : Function.Injective (fun i:primePool P=>Ideal.span {poolPrimary P i}) := by
    intro i j he
    exact Subtype.ext (by simpa only [poolPrimary_span P hP] using he)
  exact CanonicalStateCondition.terminal_energy (poolPrimary P) (poolPrimary_ne_zero P hP)
    (poolPrimary_coprime P hP) (poolPrimary_good P hP) (poolPrimary_odd P hP) hinj
    Finset.univ base (∏Q∈S,Q) Z η Ψ m labels X F K hstate hbase hZ hη hbudget
    V A M t (apply_nonneg _ _) (fun s=>SchwartzMap.norm_le_seminorm ℝ v s) hV hstop

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

def fractionalThetaPoint (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  eisEmbedding u.val * eisEmbedding lambda^((m:ℤ)-4) * eisEmbedding n * eisEmbedding b^3

lemma embedding_lambda_ne_zero : eisEmbedding lambda≠0 :=
  by
    intro hz
    apply PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero
    apply ConcreteTraceCRT.eisEmbedding_injective
    simpa only [map_zero] using hz

theorem fractionalThetaPoint_clear (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    eisEmbedding lambda^4*fractionalThetaPoint u m n b=
      eisEmbedding (u.val*lambda^m*(n*b^3)) := by
  unfold fractionalThetaPoint
  rw [zpow_sub₀ embedding_lambda_ne_zero]
  simp only [zpow_natCast,map_mul,map_pow]
  field_simp [embedding_lambda_ne_zero]

lemma embedding_lambda_norm_sq : ‖eisEmbedding lambda‖^2=(3:ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,CubicEisenstein.absNorm_span_lambda]
  norm_num

theorem fractionalThetaPoint_norm_sq (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    ‖fractionalThetaPoint u m n b‖^2=
      (3:ℝ)^((m:ℝ)-4)*‖eisEmbedding n‖^2*(‖eisEmbedding b‖^2)^3 := by
  have hp : (‖eisEmbedding lambda‖^((m:ℤ)-4))^2=(3:ℝ)^((m:ℝ)-4) := by
    calc
      _ = (‖eisEmbedding lambda‖^2)^((m:ℤ)-4) := by
        calc
          _ = ‖eisEmbedding lambda‖^(((m:ℤ)-4)*2):=by rw [zpow_mul]; norm_num
          _ = ‖eisEmbedding lambda‖^((2:ℤ)*((m:ℤ)-4)):=by congr 1; ring
          _ = _:=by rw [zpow_mul]; norm_num
      _ = (3:ℝ)^((m:ℤ)-4):=by rw [embedding_lambda_norm_sq]
      _ = _:=by rw [←Real.rpow_intCast]; norm_num
  simp only [fractionalThetaPoint,norm_mul,norm_zpow,norm_pow,
    GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul,mul_pow,hp]
  ring

theorem fractionalThetaPoint_ne_zero (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O)
    (hn : n≠0) (hb : b≠0) : fractionalThetaPoint u m n b≠0 := by
  unfold fractionalThetaPoint
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero ((u.isUnit.map eisEmbedding).ne_zero) (zpow_ne_zero _ embedding_lambda_ne_zero)
    · intro hz
      apply hn
      apply ConcreteTraceCRT.eisEmbedding_injective
      simpa only [map_zero] using hz
  · apply pow_ne_zero
    intro hz
    apply hb
    apply ConcreteTraceCRT.eisEmbedding_injective
    simpa only [map_zero] using hz

end

section
open ActualEisensteinCubic CompletedDyadic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)

theorem fractional_cusp_coefficient (d ζ : ℂ) (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O)
    (hn : n≠0) (hb : b≠0) :
    ζ*(d/((‖fractionalThetaPoint u m n b‖:ℝ):ℂ)) =
      (4/3:ℂ)*(81*ζ)*(normalizedCuspAmplitude d ((m:ℝ)-4) (‖eisEmbedding b‖^2) /
        ((4*ramifiedScale completedRamifiedInitial completedRamifiedStep m*
          ‖eisEmbedding n‖*‖eisEmbedding b‖^2:ℝ):ℂ)) := by
  have hn0 : 0<‖eisEmbedding n‖:=norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hn)
  have hb0 : 0<‖eisEmbedding b‖:=norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hb)
  have hh:=normalized_cusp_coefficient_nat d ζ m (‖eisEmbedding n‖^2) (‖eisEmbedding b‖^2)
    (sq_pos_of_pos hn0) (sq_pos_of_pos hb0)
  rw [←fractionalThetaPoint_norm_sq u m n b,Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at hh
  exact hh

def normalizedThetaAmplitude (d : ℂ→ℂ) (vartheta : ActualEisensteinCubic.O→ℂ)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  normalizedCuspAmplitude (d (fractionalThetaPoint u m n b)) ((m:ℝ)-4) (‖eisEmbedding b‖^2) *
    (fractionalThetaPoint u m n b/(‖fractionalThetaPoint u m n b‖:ℂ)) *
    vartheta (u.val*lambda^m*(n*b^3))

theorem normalizedThetaAmplitude_norm (d : ℂ→ℂ) (vartheta : ActualEisensteinCubic.O→ℂ)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) (hn : n≠0) (hb : b≠0)
    (hd : ‖d (fractionalThetaPoint u m n b)‖≤
      27*(3:ℝ)^(((m:ℝ)-4)/6)*‖eisEmbedding b‖)
    (hv : ‖vartheta (u.val*lambda^m*(n*b^3))‖≤1) :
    ‖normalizedThetaAmplitude d vartheta u m n b‖≤1 := by
  have hb0 : 0<‖eisEmbedding b‖:=norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hb)
  have hμ : fractionalThetaPoint u m n b≠0:=fractionalThetaPoint_ne_zero u m n b hn hb
  have ha:=normalizedCuspAmplitude_norm (d (fractionalThetaPoint u m n b)) ((m:ℝ)-4)
    (‖eisEmbedding b‖^2) (sq_pos_of_pos hb0) (by simpa only [Real.sqrt_sq (norm_nonneg _)] using hd)
  have hu : ‖fractionalThetaPoint u m n b/(‖fractionalThetaPoint u m n b‖:ℂ)‖=1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self]
    exact norm_ne_zero_iff.mpr hμ
  simp only [normalizedThetaAmplitude,norm_mul,hu,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans hv

theorem cusp_summand_eq_local_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal ActualEisensteinCubic.O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i) (j : ι→ℕ)
    (d : ℂ→ℂ) (vartheta : ActualEisensteinCubic.O→ℂ) (ζ : ℂ)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) (hn : n≠0) (hb : b≠0) :
    (ζ*(d (fractionalThetaPoint u m n b)/(‖fractionalThetaPoint u m n b‖:ℂ)))*
      (fractionalThetaPoint u m n b/(‖fractionalThetaPoint u m n b‖:ℂ))*
      vartheta (u.val*lambda^m*(n*b^3))*
      (∏i,bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (u.val*lambda^m*(n*b^3)))) =
    (4/3:ℂ)*(81*ζ)*ramifiedBranchPhase P hg j u m*
      ∑e : ι→Fin 3,
        (normalizedThetaAmplitude d vartheta u m n b*reflectedBranch P hg j e n b)/
          ((4*ramifiedScale completedRamifiedInitial completedRamifiedStep m*
            ‖eisEmbedding n‖*‖eisEmbedding b‖^2:ℝ):ℂ) := by
  rw [fractional_cusp_coefficient (d (fractionalThetaPoint u m n b)) ζ u m n b hn hb,
    ramified_bracket_full_expansion]
  simp only [normalizedThetaAmplitude,Finset.mul_sum,]
  apply Finset.sum_congr rfl
  intro e he
  ring

end

open ActualEisensteinCubic LocalReflectionBrackets
open ConcreteTraceCRT (eisEmbedding)

def paperLambda : ActualEisensteinCubic.O := 1+2*omega

def paperLambdaUnit : ActualEisensteinCubic.Oˣ where
  val := -omega
  inv := -omega^2
  val_inv := by
    calc
      (-omega)*(-omega^2)=omega^3:=by ring
      _=1:=omega_primitive.pow_eq_one
  inv_val := by
    calc
      (-omega^2)*(-omega)=omega^3:=by ring
      _=1:=omega_primitive.pow_eq_one

lemma paperLambdaUnit_six : (paperLambdaUnit.val:ActualEisensteinCubic.O)^6=1 := by
  change (-omega)^6=1
  calc
    (-omega)^6=(omega^3)^2:=by ring
    _=1:=by rw [omega_primitive.pow_eq_one,one_pow]

lemma paperLambda_eq : paperLambda=paperLambdaUnit.val*lambda := by
  change 1+2*omega=(-omega)*lambda
  change (1+2*omega:ActualEisensteinCubic.O)=(-omega)*(omega-1)
  have hw:=omega_primitive.geom_sum_eq_zero (by decide : 1<(3:ℕ))
  norm_num [Finset.sum_range_succ] at hw
  linear_combination hw

lemma paperLambda_embedding_ne_zero : eisEmbedding paperLambda≠0 := by
  rw [paperLambda_eq,map_mul]
  exact mul_ne_zero ((paperLambdaUnit.isUnit.map eisEmbedding).ne_zero) embedding_lambda_ne_zero

def paperFractionalThetaPoint (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) : ℂ :=
  eisEmbedding u.val*eisEmbedding paperLambda^((m:ℤ)-4)*eisEmbedding n*eisEmbedding b^3

def paperUnitReindex (m : ℕ) : ActualEisensteinCubic.Oˣ ≃ ActualEisensteinCubic.Oˣ := Equiv.mulRight (paperLambdaUnit^(m+2))

lemma paperUnitReindex_apply (m : ℕ) (u : ActualEisensteinCubic.Oˣ) :
    paperUnitReindex m u=u*paperLambdaUnit^(m+2):=rfl

theorem paperFractionalThetaPoint_eq (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    paperFractionalThetaPoint u m n b=
      fractionalThetaPoint (paperUnitReindex m u) m n b := by
  have ht : eisEmbedding paperLambdaUnit.val≠0:=(paperLambdaUnit.isUnit.map eisEmbedding).ne_zero
  have ht6 : eisEmbedding paperLambdaUnit.val^6=1:=by
    rw [←map_pow,paperLambdaUnit_six,map_one]
  have hp : eisEmbedding paperLambdaUnit.val^((m:ℤ)-4)=eisEmbedding paperLambdaUnit.val^(m+2) := by
    rw [show (m:ℤ)-4=((m+2:ℕ):ℤ)-6 by omega,zpow_sub₀ ht]
    norm_num only [zpow_natCast,zpow_ofNat,ht6,div_one]
  simp only [paperFractionalThetaPoint,fractionalThetaPoint,paperUnitReindex_apply,
    Units.val_mul,Units.val_pow_eq_pow_val,map_mul,map_pow,paperLambda_eq,mul_zpow,hp]
  ring

theorem paperFractionalThetaPoint_clear (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    eisEmbedding paperLambda^4*paperFractionalThetaPoint u m n b=
      eisEmbedding (u.val*paperLambda^m*(n*b^3)) := by
  unfold paperFractionalThetaPoint
  rw [zpow_sub₀ paperLambda_embedding_ne_zero]
  simp only [zpow_natCast,map_mul,map_pow]
  field_simp [paperLambda_embedding_ne_zero]

theorem paperFractionalThetaPoint_norm_sq (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    ‖paperFractionalThetaPoint u m n b‖^2=
      (3:ℝ)^((m:ℝ)-4)*‖eisEmbedding n‖^2*(‖eisEmbedding b‖^2)^3 := by
  rw [paperFractionalThetaPoint_eq,fractionalThetaPoint_norm_sq]

theorem paperIntegralArgument_eq (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    u.val*paperLambda^m*(n*b^3)=paperLambdaUnit.val^4*
      ((paperUnitReindex m u).val*lambda^m*(n*b^3)) := by
  apply ConcreteTraceCRT.eisEmbedding_injective
  rw [←paperFractionalThetaPoint_clear,paperFractionalThetaPoint_eq,
    paperLambda_eq,map_mul,mul_pow]
  rw [map_mul,map_pow,←fractionalThetaPoint_clear]
  ring

theorem paperBracket_transport (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P)
    (j : ℕ) (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    bracket (actualSextic P hg) j (Ideal.Quotient.mk P (u.val*paperLambda^m*(n*b^3))) =
      unitArgumentFactor (actualSextic P hg) j (Ideal.Quotient.mk P (paperLambdaUnit.val^4))*
      bracket (actualSextic P hg) j
        (Ideal.Quotient.mk P ((paperUnitReindex m u).val*lambda^m*(n*b^3))) := by
  rw [paperIntegralArgument_eq,map_mul]
  apply bracket_mul_unit
  exact ((paperLambdaUnit.isUnit.pow 4).map (Ideal.Quotient.mk P)).ne_zero

lemma paperLambdaUnit_four : paperLambdaUnit.val^4=omega := by
  change (-omega)^4=omega
  calc
    _=omega^3*omega:=by ring
    _=omega:=by rw [omega_primitive.pow_eq_one,one_mul]

theorem paperBracket_one_transport (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] (hg : lambda∉P)
    (u : ActualEisensteinCubic.Oˣ) (m : ℕ) (n b : ActualEisensteinCubic.O) :
    bracket (actualSextic P hg) 1 (Ideal.Quotient.mk P (u.val*paperLambda^m*(n*b^3))) =
      bracket (actualSextic P hg) 1
        (Ideal.Quotient.mk P ((paperUnitReindex m u).val*lambda^m*(n*b^3))) := by
  rw [paperBracket_transport,paperLambdaUnit_four]
  have hv : (actualSextic P hg (Ideal.Quotient.mk P omega))^3=1 := by
    rw [←map_pow,←map_pow,omega_primitive.pow_eq_one,map_one,map_one]
  have hf : unitArgumentFactor (actualSextic P hg) 1 (Ideal.Quotient.mk P omega)=1 := by
    simp only [unitArgumentFactor,show (1:ℕ)≠4 by decide,ite_false]
    rw [show (1:ℕ)+2=3 by rfl,MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (3:ℕ)≠0),hv,inv_one]
  rw [hf,one_mul]

end CompletedGauss

open scoped BigOperators Classical SchwartzMap ContDiff
namespace CanonicalCubeSeparation

lemma columnWindowRadius_exp (A : ℝ) (hA : 0≤A) :
    columnWindowRadius (Real.exp (-A)) (Real.exp A)=2*A+3 := by
  rw [columnWindowRadius,Real.log_exp,Real.log_exp,abs_neg,abs_of_nonneg hA]
  ring

theorem fixed_reopening_profiles (A : ℝ) (hA : 0≤A) :
    ∃g V : 𝓢(ℝ,ℂ), HasCompactSupport (g:ℝ→ℂ) ∧ HasCompactSupport (V:ℝ→ℂ) ∧
      (∀u,|u|≤columnWindowRadius (Real.exp (-A)) (Real.exp A)→g u=1) ∧
      (∀u,g u≠0→|u|≤2*A+4) ∧
      (∀u,g u≠0→V u=1) ∧
      (∀u,V u≠0→|u|≤2*A+5) := by
  obtain ⟨g,hgc,hgs,hgone,hgsupp,hgzero⟩:=FourierBridge.exists_complex_smooth_cutoff (2*A+3) (by linarith)
  obtain ⟨v,hvc,hvs,hvone,hvsupp,hvzero⟩:=FourierBridge.exists_complex_smooth_cutoff (2*A+4) (by linarith)
  let gs : 𝓢(ℝ,ℂ):=hgc.toSchwartzMap hgs
  let vs : 𝓢(ℝ,ℂ):=hvc.toSchwartzMap hvs
  have hgbound : ∀u,g u≠0→|u|≤2*A+4 := by
    intro u hu
    have hh:=abs_le.mpr (hgsupp (subset_tsupport g hu))
    linarith
  refine ⟨gs,vs,hgc,hvc,?_,hgbound,?_,?_⟩
  · intro u hu
    exact hgone u (by simpa only [columnWindowRadius_exp A hA] using hu)
  · intro u hu
    exact hvone u (hgbound u hu)
  · intro u hu
    have hh:=abs_le.mpr (hvsupp (subset_tsupport v hu))
    linarith

lemma fixed_reopening_child_radius (A : ℝ) : (2*A+4)+7=2*A+11 := by ring

end CanonicalCubeSeparation

namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalShortState_geometry (S : Finset (Ideal ActualEisensteinCubic.O))
    (hSp : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (base : ActualEisensteinCubic.O→*ℂ) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K)
    (hZ : 1≤Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η)
    (hbudget : 3000*η≤(1:ℝ)/80)
    (hfixed : 2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80)) :
    let G:=Ideal.span {m*excludedGenerator S}
    G≠0 ∧ (∀P∈fixedBadPrimes,P∣G) ∧ labels⊆idealRange F ∧
      X*F≤Z^3 ∧ (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) := by
  have hprod : (∏P∈S,P)≠0:=Finset.prod_ne_zero_iff.mpr (fun P hP=>(hSp P hP).ne_zero)
  have he : excludedGenerator S≠0:=idealGenerator_ne_zero _ hprod
  have hG : (Ideal.span {m*excludedGenerator S}:Ideal ActualEisensteinCubic.O)≠0:=
    Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero hstate.mask_ne_zero he)
  have hpG : ∀P∈fixedBadPrimes,P∣Ideal.span {m*excludedGenerator S} := by
    intro P hP
    apply Ideal.dvd_iff_le.mpr
    apply Ideal.span_le.mpr
    exact Set.singleton_subset_iff.mpr (P.mul_mem_left m (excludedGenerator_mem S (hbad hP)))
  have hlabels : labels⊆idealRange F:=canonicalLabels_subset_idealRange base (∏P∈S,P) Z η Ψ m labels X F K hstate
    (fun P hP=>Finset.dvd_prod_of_mem (fun Q:Ideal ActualEisensteinCubic.O=>Q) (hbad hP))
  have hmass : X*F≤Z^3:=hstate.mass_le.trans (canonicalRankMass_global Z hZbig _)
  refine ⟨hG,hpG,hlabels,hmass,?_⟩
  have hZ0 : 0<Z:=zero_lt_one.trans_le hZ
  have hXF : 0≤X*F:=mul_nonneg hstate.column_pos.le (zero_le_one.trans hstate.label_ge_one)
  have hm : (3:ℝ)/80≤canonicalRankMargin ((1:ℝ)/20) η (fixedDepthRank Z K) :=
    (by linarith : (3:ℝ)/80≤(1:ℝ)/20-3000*η).trans (canonicalRankMargin_lower _ η hη _)
  have hi : K*‖eisEmbedding m‖^2≤(X*F)*Z^(-((3:ℝ)/80)):=
    hstate.invariant.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (neg_le_neg hm)) hXF)
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,map_mul,norm_mul,mul_pow]
  calc
    (2*K)*(‖eisEmbedding m‖^2*‖eisEmbedding (excludedGenerator S)‖^2)=
        (2*‖eisEmbedding (excludedGenerator S)‖^2)*(K*‖eisEmbedding m‖^2):=by ring
    _ ≤ Z^((1:ℝ)/80)*((X*F)*Z^(-((3:ℝ)/80))):=
      mul_le_mul hfixed hi (mul_nonneg (zero_le_one.trans hstate.row_ge_one) (sq_nonneg _)) (by positivity)
    _ = (X*F)*(Z^((1:ℝ)/80)*Z^(-((3:ℝ)/80))):=by ring
    _ = _:=by rw [←Real.rpow_add hZ0]; norm_num

theorem canonicalShortState_uniform_twist
    (a b : ℝ) (ha : 0<a) (ε ρ q levelBound : ℝ)
    (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃d : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ : ℝ) (rays : ℕ) (S : Finset (Ideal ActualEisensteinCubic.O)),
    (∀P∈S,Prime P) → fixedBadPrimes⊆S →
    ∀(base : ActualEisensteinCubic.O→*ℂ) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ),
    CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
    (∀x,‖base x‖≤1) → 1≤Z → Real.exp 9000≤Z → 0≤η → 3000*η≤(1:ℝ)/80 →
    2*‖eisEmbedding (excludedGenerator S)‖^2≤Z^((1:ℝ)/80) → ∀lengthScale : ℂ,
    (F<Z^((1:ℝ)/1000) → ∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
      HasExactCompletedDyadicModels rays (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
        (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val ((Ideal.span {m*excludedGenerator S})*f.val)
        (CompletedHeight.normTwistedSource W θ)
        (CompletedUnitRows.unitRowFamily Ψ (m*excludedGenerator S) u f) lengthScale) →
    2*X*rowFamilyEnergy labels (fun I z=>shortCompletedSum
      (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z)
      W X (if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0)) K≤
    (C*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*(X*F)^2*Z^(7*ε-(1:ℝ)/40) := by
  obtain ⟨d,hbound⟩:=canonicalShortEnergy_normalized_uniform_twist a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩:=hbound W hs hW
  refine ⟨C,hC,?_⟩
  intro θ rays S hSp hbad base Z η Ψ m labels X F K hstate hbase hZ hZbig hη hbudget hfixed lengthScale hmodels
  by_cases hF : F<Z^((1:ℝ)/1000)
  · rw [ite_eq_left hF]
    obtain ⟨hG,hpG,hlabels,hmass,hmargin⟩:=canonicalShortState_geometry S hSp hbad base Z η Ψ m labels X F K
      hstate hZ hZbig hη hbudget hfixed
    exact hb θ rays Z K X F hZ hstate.row_ge_one hstate.label_ge_one hF.le hstate.column_pos hmass
      (Ideal.span {m*excludedGenerator S}) hG hpG hmargin labels hlabels Ψ
      (fun x=>hstate.coefficient.norm_le hbase x) (m*excludedGenerator S) lengthScale (hmodels hF)
  · rw [ite_eq_right hF,rowFamilyEnergy_eq_sum labels _ K (zero_lt_one.trans_le hstate.row_ge_one)]
    have hz (I : Ideal ActualEisensteinCubic.O) (z : ActualEisensteinCubic.O) : shortCompletedSum
        (rowTwist (normHeightTwist Ψ θ) (m*excludedGenerator S) (idealGenerator I) z) W X 0=0:=
      shortCompletedSum_nonpos _ _ _ _ le_rfl
    simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero,Finset.sum_const_zero]
    positivity

end CanonicalRowCompletion

namespace CanonicalCubeSeparation

def radiusIter (A : ℝ) : ℕ→ℝ
  | 0=>A
  | n+1=>radiusIter (2*A+11) n

@[simp] theorem radiusIter_zero (A : ℝ) : radiusIter A 0=A:=rfl
@[simp] theorem radiusIter_succ (A : ℝ) (n : ℕ) :
    radiusIter A (n+1)=radiusIter (2*A+11) n:=rfl

theorem radiusIter_mono_base (n : ℕ) : Monotone (fun A:ℝ=>radiusIter A n) := by
  induction n with
  | zero=>intro A B h;exact h
  | succ n ih=>intro A B h;exact ih (by linarith : 2*A+11≤2*B+11)

theorem radiusIter_nonneg (A : ℝ) (hA : 0≤A) (n : ℕ) : 0≤radiusIter A n := by
  induction n generalizing A with
  | zero=>exact hA
  | succ n ih=>exact ih (2*A+11) (by linarith)

theorem radiusIter_mono_depth (A : ℝ) (hA : 0≤A) : Monotone (radiusIter A) := by
  apply monotone_nat_of_le_succ
  intro n
  exact radiusIter_mono_base n (by linarith : A≤2*A+11)

theorem le_radiusIter (A : ℝ) (hA : 0≤A) (n : ℕ) : A≤radiusIter A n :=
  radiusIter_mono_depth A hA (Nat.zero_le n)

theorem radiusIter_child_le (A : ℝ) (hA : 0≤A) (s r : ℕ) (hs : s<r) :
    radiusIter (2*A+11) s≤radiusIter A r :=
  radiusIter_mono_depth A hA (Nat.succ_le_of_lt hs)

theorem common_pool_parent (A Z X D : ℝ) (r : ℕ) (hA : 0≤A)
    (_hZ : 0≤Z) (hX : 0≤X) (hXZ : X≤Z^3)
    (hD : Real.exp (radiusIter A r)*Z^3≤D) : Real.exp A*X≤D := by
  exact (mul_le_mul (Real.exp_le_exp.mpr (le_radiusIter A hA r)) hXZ hX
    (Real.exp_pos _).le).trans hD

theorem common_pool_child (A Z D : ℝ) (s r : ℕ) (hA : 0≤A)
    (hZ : 0≤Z) (hs : s<r) (hD : Real.exp (radiusIter A r)*Z^3≤D) :
    Real.exp (radiusIter (2*A+11) s)*Z^3≤D :=
  (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (radiusIter_child_le A hA s r hs))
    (pow_nonneg hZ _)).trans hD

end CanonicalCubeSeparation

open scoped BigOperators Classical
namespace QuadraticAllOddCRT
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisTraceModChar finite_quotient_span)
open FiniteGaussPhase hiding O

def character (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal] : MulChar (ActualEisensteinCubic.O⧸P) ℂ := by
  letI : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  letI : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  exact (quadraticChar (ActualEisensteinCubic.O⧸P)).ringHomComp (Int.castRingHom ℂ)

theorem normalized_prime_eq_square_sum (p : ActualEisensteinCubic.O) (hp : p≠0)
    [(Ideal.span {p}).IsMaximal] (hc : ringChar (ActualEisensteinCubic.O⧸Ideal.span {p})≠2) :
    ConcreteBreveE.normalizedTraceGauss p hp (character (Ideal.span {p}))=
      quadraticGammaO p hp := by
  let : Field (ActualEisensteinCubic.O⧸Ideal.span {p}):=Ideal.Quotient.field _
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {p}):=Fintype.ofFinite _
  let ψ:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates p hp
  have hψ:ψ≠1:=by
    have hprim:=GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
    simpa only [AddChar.mulShift_one] using hprim (a:=1) one_ne_zero
  change gaussSum (character (Ideal.span {p})) ψ/(‖eisEmbedding p‖:ℂ)=
    (∑x:ActualEisensteinCubic.O⧸Ideal.span {p},ψ (x^2))/(‖eisEmbedding p‖:ℂ)
  congr 1
  exact ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase ψ hc hψ

theorem normalized_product_eq_square_sum {ι : Type*} [Fintype ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2) :
    normalizedProductTraceGauss p hp hcop (fun i=>character (Ideal.span {p i}))=
      quadraticGammaO (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)) := by
  let c:=∏i,p i
  have hc0:c≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {c}):=finite_quotient_span hc0
  let : Fintype (ActualEisensteinCubic.O⧸Ideal.span {c}):=Fintype.ofFinite _
  let (i:ι) : Fintype (ActualEisensteinCubic.O⧸Ideal.span {p i}):=Fintype.ofFinite _
  let (i:ι) : Field (ActualEisensteinCubic.O⧸Ideal.span {p i}):=Ideal.Quotient.field _
  let e:=productElementCRT p hcop
  let ψ:=eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0
  change (∑x:ActualEisensteinCubic.O⧸Ideal.span {c},(∏i,character (Ideal.span {p i}) (e x i))*ψ x)/(‖eisEmbedding c‖:ℂ)=
    (∑x:ActualEisensteinCubic.O⧸Ideal.span {c},ψ (x^2))/(‖eisEmbedding c‖:ℂ)
  congr 1
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i=>ActualEisensteinCubic.O⧸Ideal.span {p i}) e ψ (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0) hc

theorem quadraticGamma_product {ι : Type*} [Fintype ι]
    (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2) :
    quadraticGammaO (∏i,p i) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))=
      ∏i,character (Ideal.span {p i}) (Ideal.Quotient.mk (Ideal.span {p i}) (cofactor p i))*
        quadraticGammaO (p i) (hp i) := by
  rw [←normalized_product_eq_square_sum p hp hcop hc,normalizedProductTraceGauss_crt]
  apply Finset.prod_congr rfl
  intro i hi
  rw [normalized_prime_eq_square_sum _ _ (hc i)]

end QuadraticAllOddCRT

end

end OAI
end OAIOriginalModule0247

/-! Original module: OAI.NumberTheory.DirichletL.RowCompletion.CubicReopening
Source SHA256: 574e90f9f9586d9c7a4d7393824a7867bf88dfea2495a63a1fdbe63d994e0aa2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0248


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalRowCompletion

section
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

theorem outside_pool_coprime_excluded
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (hSp : ∀P∈S,Prime P)
    (i : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)) :
    IsCoprime (Ideal.span {poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D) i})
      (∏P∈S,P) := by
  rw [poolPrimary_span _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)]
  apply Ideal.isCoprime_iff_codisjoint.mpr
  apply (Ideal.isMaximal_def.mp (inferInstance : i.val.IsMaximal)).not_le_iff_codisjoint.mp
  intro hle
  apply excludedGenerator_not_mem_pool S D hSp i
  apply hle
  have hm : excludedGenerator S ∈ Ideal.span {excludedGenerator S} :=
    Ideal.subset_span (by simp)
  simpa only [excludedGenerator,span_idealGenerator] using hm

theorem cubeIdeal_eq_primeProduct_span (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,Admissible I) (v : primePool F→₀ℕ) :
    Ideal.span {primeProduct (poolPrimary F) v.support v}=cubeIdeal F v := by
  rw [primeProduct,FiniteGaussPhase.span_finset_prod]
  simp only [←Ideal.span_singleton_pow,poolPrimary_span F hF]
  unfold cubeIdeal
  apply Finset.prod_subset (Finset.subset_univ v.support)
  intro i hi hni
  rw [Finsupp.notMem_support_iff.mp hni,pow_zero]

theorem cubeIdeal_primeProduct_norm (F : Finset (Ideal ActualEisensteinCubic.O))
    (hF : ∀I∈F,Admissible I) (v : primePool F→₀ℕ) :
    ‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2=
      (Ideal.absNorm (cubeIdeal F v):ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,cubeIdeal_eq_primeProduct_span F hF]

theorem progressingActiveBin_cube_bound
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (b X H₀ : ℝ) (j : ℕ)
    (hQ : (progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty) :
    (normLogScale j)^3≤b*X := by
  obtain ⟨v,hv⟩:=hQ
  have hbin := (Finset.mem_filter.mp hv).1
  have hactive := (Finset.mem_filter.mp hbin).1
  have hnorm := (activeCubeLogBin_norms S D b X j v hbin).1
  exact (pow_le_pow_left₀ (normLogScale_pos j).le hnorm 3).trans
    (Finset.mem_filter.mp hactive).2

end

open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open CanonicalCubeSeparation JointLogSeparation
open FirstPassCubeLabels (columnLog)

theorem progressingCanonicalBin_closed_step
    (g V : 𝓢(ℝ,ℂ)) (A M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss η : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (hη : 0<η)
    (hηsmall : η≤(1:ℝ)/1000) (hbudget : 3000*η≤(1:ℝ)/40) (J : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (C : ℝ), 0≤C ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+7) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+7) ∧
      ∀(S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
      (base : ActualEisensteinCubic.O→*ℂ) (Z : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O) (labels : Finset (Ideal ActualEisensteinCubic.O))
      (X F K E oldHeight : ℝ),
      CanonicalStateCondition base (∏P∈S,P) Z η Ψ m labels X F K →
      (∀u,‖base u‖≤1) → 1<Z → Real.exp 9000≤Z → 1≤X → X≤Z^3 → F≤Z^3 → 1≤E →
      let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
      letI : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
        fun i=>by rw [poolPrimary_span P hP i];infer_instance
      (∀side : Bool, let windows:=if side then windows₁ else windows₂
        ∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base (∏Q∈S,Q) Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z K → ∀s : ℝ,
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      ∀j∈cubeLogRange (Real.exp A) X,
      let B:=normLogScale j
      let H₀:=if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0
      let Q':=progressingCubes S D H₀ (activeCubeLogBin S D (Real.exp A) X j)
      Q'.Nonempty → ∀ξ : ℝ,
      B*rowFamilyEnergy labels (fun I z=>
        reopenedCanonicalRow (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
          (poolPrimary_good P hP) Finset.univ Q'
          (separatedCubeCoefficient
            (fun v=>reopenedCubeCoefficient H₀
              (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1)
              (cubeIdeal P v))
            (fun v=>(Ideal.absNorm (cubeIdeal P v):ℝ)) B ξ)
          Ψ m (idealGenerator I)
          (fun T=>frequencyTwist g (oldHeight+ξ) (columnLog (poolPrimary P) (X/B^3) T)) z) K≤
        C*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E*(1+|oldHeight+ξ|)^(2*J) := by
  obtain ⟨w₁,w₂,C₀,hC₀,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,hstep⟩ :=
    reopenedCanonicalRow_closed_step g V A M Nv hM hNv hgM hV hWin
      ε deltaLoss η hε hδ hη hηsmall hbudget J
  obtain ⟨Cβ,hCβ,hβbound⟩:=outside_separated_cube_coefficient_bound ε hε
  let Cg:=Cβ*(Real.exp (A+1))^ε
  refine ⟨w₁,w₂,C₀*Cg^2,by positivity,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro S D hbad hSp base Z Ψ m labels X F K E oldHeight hstate hbase hZ hZbig hX hXZ hFZ hE
  dsimp only
  let P:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hP:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i : primePool P,(Ideal.span {poolPrimary P i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span P hP i];infer_instance
  intro ih j hj hQ ξ
  let B:=normLogScale j
  let H₀:=if F<Z^((1:ℝ)/1000) then Z^((1:ℝ)/1000) else 0
  let Q':=progressingCubes S D H₀ (activeCubeLogBin S D (Real.exp A) X j)
  let β:=fun I v=>separatedCubeCoefficient
    (fun u=>reopenedCubeCoefficient H₀
      (rowTwist (normHeightTwist Ψ oldHeight) (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal P u))
    (fun u=>(Ideal.absNorm (cubeIdeal P u):ℝ)) B ξ v
  have hB : 1≤B:=normLogScale_ge_one j
  have hBp : 0<B:=normLogScale_pos j
  have hactive : B^3≤Real.exp A*X:=progressingActiveBin_cube_bound S D (Real.exp A) X H₀ j hQ
  have hBscale : Real.exp 1*B≤Real.exp (A+1)*Z^3 := by
    calc
      _ ≤ Real.exp 1*(Real.exp A*X) :=
        mul_le_mul_of_nonneg_left ((le_self_pow₀ hB (by decide : (3:ℕ)≠0)).trans hactive) (Real.exp_pos _).le
      _ ≤ Real.exp 1*(Real.exp A*Z^3) := by gcongr
      _ = _ := by rw [Real.exp_add];ring
  have hbgrowth : (Real.exp 1*B)^ε≤(Real.exp (A+1))^ε*Z^(3*ε) := by
    calc
      _ ≤ (Real.exp (A+1)*Z^3)^ε :=
        Real.rpow_le_rpow (by positivity) hBscale hε.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast_mul (by linarith : 0≤Z)]
        norm_num
  have hΨ : ∀u,‖normHeightTwist Ψ oldHeight u‖≤1 :=
    fun u=>(normHeightTwist_norm_le Ψ oldHeight u).trans (hstate.coefficient.norm_le hbase u)
  have hcoeff : ∀I∈labels,∀v∈Q',‖β I v‖≤Cg*Z^(3*ε) := by
    intro I hI v hv
    have hvbin: v∈activeCubeLogBin S D (Real.exp A) X j:=(Finset.mem_filter.mp hv).1
    obtain ⟨hlo,hhi⟩:=activeCubeLogBin_norms S D (Real.exp A) X j v hvbin
    exact (hβbound S D _ hΨ m (idealGenerator I) H₀ B ξ v hBp hlo hhi).trans
      ((mul_le_mul_of_nonneg_left hbgrowth hCβ.le).trans_eq (by dsimp only [Cg];ring))
  have hinj : Function.Injective (fun i:primePool P=>Ideal.span {poolPrimary P i}) := by
    intro i k he
    exact Subtype.ext (by simpa only [poolPrimary_span P hP] using he)
  have hpr (i : primePool P) : lambda^2∣poolPrimary P i-1 :=
    (primaryPrime_spec i.val (poolPrimary_ne_zero P hP i)).2.2.2
  have hn : ∀v∈Q',‖ConcreteTraceCRT.eisEmbedding
      (FirstPassCubeLabels.primeProduct (poolPrimary P) v.support v)‖^2≤Real.exp 1*B := by
    intro v hv
    rw [cubeIdeal_primeProduct_norm P hP]
    exact (activeCubeLogBin_norms S D (Real.exp A) X j v (Finset.mem_filter.mp hv).1).2
  have hp := hstep (poolPrimary P) (poolPrimary_ne_zero P hP) (poolPrimary_coprime P hP)
    (poolPrimary_good P hP) (poolPrimary_odd P hP) hinj hpr base (∏Q∈S,Q) Z Ψ m labels
    X F K hstate Finset.univ Q' β (Cg*Z^(3*ε)) (oldHeight+ξ) B E hbase
    (outside_pool_coprime_excluded S D hbad hSp) hZ hZbig hX hXZ hFZ
    (by dsimp only [Cg];positivity) hE hB hactive
    (progressingActiveBin_progress S D (Real.exp A) X Z F j hstate.label_ge_one hQ)
    hcoeff (fun v hv=>Finset.subset_univ _) hn ih
  have hpower : (Z^(3*ε))^2*Z^(η+17*deltaLoss+32*ε)=Z^(η+17*deltaLoss+38*ε) := by
    rw [←Real.rpow_mul_natCast (by linarith : 0≤Z),←Real.rpow_add (by linarith : 0<Z)]
    congr 1
    norm_num
    ring
  have heq : C₀*(Cg*Z^(3*ε))^2*(X*F)^2*Z^(η+17*deltaLoss+32*ε)*E*(1+‖oldHeight+ξ‖)^(2*J)=
      (C₀*Cg^2)*(X*F)^2*Z^(η+17*deltaLoss+38*ε)*E*(1+|oldHeight+ξ|)^(2*J) := by
    rw [Real.norm_eq_abs]
    calc
      _ = (C₀*Cg^2)*(X*F)^2*((Z^(3*ε))^2*Z^(η+17*deltaLoss+32*ε))*E*(1+|oldHeight+ξ|)^(2*J) := by ring
      _ = _ := by rw [hpower]
  exact (show _≤_ from hp).trans_eq heq

end CanonicalRowCompletion

open scoped BigOperators Classical
namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CanonicalRowCompletion
open CanonicalQuadraticSieve hiding O
open UniqueFactorizationMonoid
open ActualEisensteinCoordinates (eval coords eval_coords)
open ShortDraftLatticeCount (qNat qO_nonneg coords_eval)

def unitSupplement (u : ActualEisensteinCubic.Oˣ) : ActualEisensteinCubic.O→*ℂ where
  toFun n:=if Supported (Ideal.span {n}) then idealRowHom u.val (Ideal.span {n}) else 0
  map_one' := by
    have hs : Supported (1:Ideal ActualEisensteinCubic.O):=⟨one_ne_zero,by
      intro P hP
      rw [normalizedFactors_one] at hP
      exact False.elim (Multiset.notMem_zero P hP)⟩
    rw [show Ideal.span {(1:ActualEisensteinCubic.O)}=(1:Ideal ActualEisensteinCubic.O) by simp only [Ideal.span_singleton_one,Ideal.one_eq_top],ite_eq_left hs,map_one]
  map_mul' x y := by
    rw [←Ideal.span_singleton_mul_span_singleton, supported_mul_iff,map_mul]
    by_cases hx:Supported (Ideal.span {x}) <;> by_cases hy:Supported (Ideal.span {y}) <;> simp [hx,hy]

private lemma supported_good (I : Ideal ActualEisensteinCubic.O) (hI : Supported I) :
    ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2 := by
  intro P hP
  have hp:=prime_of_normalized_factor P hP
  exact ⟨(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero,hI.2 P hP⟩

lemma unitSupplement_norm (u : ActualEisensteinCubic.Oˣ) (n : ActualEisensteinCubic.O) : ‖unitSupplement u n‖≤1 := by
  change ‖if _ then _ else _‖≤_
  split_ifs
  · exact idealRowHom_norm _ _
  · simp

private lemma norm_eval_residue (m : ℕ) (a b : ℤ) :
    (Ideal.absNorm (Ideal.span {eval a b}) : ZMod m)=
      (a : ZMod m)^2-(a : ZMod m)*(b : ZMod m)+(b : ZMod m)^2 := by
  have hi : (Ideal.absNorm (Ideal.span {eval a b}) : ℤ)=a^2-a*b+b^2 := by
    rw [←qNat_eq_absNorm_span]
    change ((ShortDraftLatticeCount.q (coords (eval a b))).toNat : ℤ)=_
    rw [Int.toNat_of_nonneg (qO_nonneg _),coords_eval]
    rfl
  have hz := congrArg (fun k : ℤ => (k : ZMod m)) hi
  push_cast at hz
  exact hz

lemma norm_residue_congruent (m : ℕ) (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈(Ideal.span {(m:ActualEisensteinCubic.O)} : Ideal ActualEisensteinCubic.O)) :
    Ideal.absNorm (Ideal.span {x})%m=Ideal.absNorm (Ideal.span {y})%m := by
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  let c:=(coords y).1
  let d:=(coords y).2
  let e:=(coords z).1
  let f:=(coords z).2
  have hy : y=eval c d:=(eval_coords y).symm
  have hx : x=eval (c+(m:ℤ)*e) (d+(m:ℤ)*f) := by
    calc
      x=y+(m:ActualEisensteinCubic.O)*z:=by linear_combination hz
      _=eval (c+(m:ℤ)*e) (d+(m:ℤ)*f):=by
        rw [hy,←eval_coords z]
        dsimp [eval,c,d,e,f]
        push_cast
        ring
  apply (ZMod.natCast_eq_natCast_iff' _ _ m).mp
  rw [hx,hy,norm_eval_residue,norm_eval_residue]
  simp

lemma supported_span_congruent_mod_thirty_six (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈(Ideal.span {(36:ActualEisensteinCubic.O)} : Ideal ActualEisensteinCubic.O)) :
    Supported (Ideal.span {x})↔Supported (Ideal.span {y}) := by
  have h36:(36:ActualEisensteinCubic.O)∣x-y:=Ideal.mem_span_singleton.mp hxy
  have hlam : lambda∣(36:ActualEisensteinCubic.O):=
    ((dvd_pow_self lambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three).trans ⟨12,by norm_num⟩
  have htwo : (2:ActualEisensteinCubic.O)∣(36:ActualEisensteinCubic.O):=⟨18,by norm_num⟩
  have he (a : ActualEisensteinCubic.O) (ha : a∣x-y) : a∣x↔a∣y := by
    constructor
    · intro hx
      convert dvd_sub hx ha using 1 ; ring
    · intro hy
      convert dvd_add ha hy using 1 ; ring
  rw [supported_span_iff,supported_span_iff,he lambda (hlam.trans h36),he 2 (htwo.trans h36)]

theorem unitSupplement_periodic (u : ActualEisensteinCubic.Oˣ) (x y : ActualEisensteinCubic.O)
    (hxy : x-y∈(Ideal.span {(36:ActualEisensteinCubic.O)} : Ideal ActualEisensteinCubic.O)) :
    unitSupplement u x=unitSupplement u y := by
  have hs:=supported_span_congruent_mod_thirty_six x y hxy
  change (if _ then _ else _)=(if _ then _ else _)
  by_cases hx:Supported (Ideal.span {x})
  · have hy:=hs.mp hx
    rw [ite_eq_left hx,ite_eq_left hy]
    exact idealRowHom_unit_eq_of_norm_mod_thirty_six u _ _ hx.1 hy.1
      (supported_good _ hx) (supported_good _ hy) (norm_residue_congruent 36 x y hxy)
  · rw [ite_eq_right hx,ite_eq_right (fun hy=>hx (hs.mpr hy))]

private lemma rowTwist_zero_of_common_prime (Ψ : ActualEisensteinCubic.O→*ℂ) (m f z n : ActualEisensteinCubic.O)
    (P : Ideal ActualEisensteinCubic.O) (hp : Prime P) (hm : m∈P) (hn : n∈P) :
    rowTwist Ψ m f z n=0 := by
  have hPI:P∣Ideal.span {n}:=Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hn))
  have hm6:m^6∈P:=by
    rw [show m^6=m^5*m by ring]
