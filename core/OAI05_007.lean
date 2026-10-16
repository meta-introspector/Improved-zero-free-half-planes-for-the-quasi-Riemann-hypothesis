        ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) Q₀))\B,
          if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
          ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*
        mixedReflectedValue (C h B T) (G h).shape
          (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_ne_zero
          (G h).denominator_ne_zero
          (((poolPrimeFamily R (Ideal.span {m}*F) Q₀).restrict B).reflected K hK (S.restrict T)).generator_good
          (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val))
          (slotIndices B (PrimeIndex K) T) W X := by
  have hP : Pairwise (Function.onFun IsCoprime (Pall).ideal) :=
    joined_free_pairwise D.movingIdeal Q₀ D.movingSupported S hS hdis
  have hodd : ∀ i, ringChar (Eis⧸(Pall).ideal i)≠2 := by
    intro i
    cases i with
    | inl P => exact (supported_factors_good D.movingIdeal D.movingSupported P.val.val
        (Multiset.mem_toFinset.mp P.val.property)).2.2
    | inr t => exact hSodd t
  have hj : ∀ i, Jall i<6 := by
    intro i
    cases i with
    | inl P => exact Nat.mod_lt _ (by norm_num)
    | inr t => norm_num
  have hchoose := exists_original_controlled_source D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    S c G N hN hNp hP C
  choose CC hCC using hchoose
  rw [(Pall).marked_reflected_source_of_controlled hP hodd Jall hj markedSumSlots φ hφnorm Q₀ hQ₀ hφperiod
    c hc hcQ G N hN CC W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  exact original_controlled_source_sum D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    S hSodd (C h) (CC h) (hCC h) (G h).shape (G h).denominator_ne_zero W X
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1064

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ActualSelected
Source SHA256: 9504f9ab1fc6802ef7ae01f334bb1079f74624624f284447134724d3f7f2653e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1065



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (S : PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad
local notation "Pall" => PrimeFamily.sum (freePrimeFamily D.movingIdeal (Q*Ideal.span {(72:Eis)}) D.movingSupported) S
local notation "Jall" => Sum.elim (fun P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}) =>
  Multiset.count (Subtype.val (Subtype.val P)) (UniqueFactorizationMonoid.normalizedFactors D.movingIdeal)%6) (fun _ : σ => 0)

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem actual_marked_selected_reflection
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hSodd : ∀ i, ringChar (Eis⧸S.ideal i)≠2)
    (hdis : ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}), ∀ i, S.ideal i≠P.val.val)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n, ‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c}, FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h, (9:Eis)*(G h).c0∣N)
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((Pall).ideal i))
    (C : ∀ h : Eis⧸Ideal.span {c}, ∀ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ, ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict B).reflected K hK (S.restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i, if S.ideal i∣A then (1:ℂ) else 0)=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c}, fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h *
      ∑ B : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})), ∑ T : Finset σ,
        ((∏ b∈(Finset.univ:Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})))\B,
          if completedLocalExponent R F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0)*
          ∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (S.ideal t):ℂ)⁻¹)*
        mixedReflectedValue (C h B T) (G h).shape
          (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict B).reflected K hK (S.restrict T)).generator_ne_zero
          (G h).denominator_ne_zero
          (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict B).reflected K hK (S.restrict T)).generator_good
          (reflectedExponent (fun b : B => completedLocalExponent R F b.val.val))
          (slotIndices B (PrimeIndex K) T) W X := by
  have hQ0 : (Q*Ideal.span {(72:Eis)})≠0 := by
    apply mul_ne_zero hQ
    simp only [ne_eq,Ideal.zero_eq_bot,Ideal.span_singleton_eq_bot]
    norm_num
  exact (actual_marked_row_eq_joined D S Ψ Q hmLam hm2 W X).trans
    (original_selected_reflected_expansion D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask S
      hS hSodd hdis (D.fixedFactor Ψ Q) (D.fixedFactor_norm Ψ Q hΨnorm) hQ0
      (D.fixedFactor_periodic Ψ Q hΨperiod) c hc hcQ G N hN hNp C W hWcompact lo hi hlo hsupp hW X hX)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1065

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalWeights
Source SHA256: eb1d36955dee816d28cd7e9a9df70acddf6a471629464b985452a00c314bd75c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1066


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def frozenInactiveWeight (J F Q Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J Q Q₀)) : ℂ :=
  ∏ b∈(Finset.univ:Finset (FreeReflection.pool J Q Q₀))\A,
    if completedLocalExponent J F b.val=0 then 1-(Ideal.absNorm b.val:ℂ)⁻¹ else 0

lemma one_sub_inverse_norm_le_one (I : Ideal Eis) (hI : I≠0) :
    ‖1-(Ideal.absNorm I:ℂ)⁻¹‖≤1 := by
  have hn : (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hi : (Ideal.absNorm I:ℝ)⁻¹≤1 := inv_le_one_of_one_le₀ hn
  have he : (1-(Ideal.absNorm I:ℂ)⁻¹)=((1-(Ideal.absNorm I:ℝ)⁻¹):ℝ) := by push_cast;rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  have hp : 0≤(Ideal.absNorm I:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  linarith

lemma frozenInactiveWeight_norm (J F Q Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J Q Q₀)) :
    ‖frozenInactiveWeight J F Q Q₀ A‖≤1 := by
  unfold frozenInactiveWeight
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro b hb
    exact norm_nonneg _
  · intro b hb
    split_ifs
    · exact one_sub_inverse_norm_le_one b.val
        (NeZero.ne ((poolPrimeFamily J Q Q₀).ideal b))
    · simp

lemma original_fourier_frozen_weight_norm {m f z : Eis} (D : GoodMaskRowData m f z)
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : ∀ n,‖Ψ n‖≤1)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})] (h : Eis⧸Ideal.span {c})
    (J F Q₀ : Ideal Eis) (A : Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)) :
    ‖fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ A‖≤1 := by
  rw [norm_mul]
  exact (mul_le_mul (D.fixedCoefficient_norm Ψ Q hΨ c hc h)
    (frozenInactiveWeight_norm J F (Ideal.span {m}*F) Q₀ A) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1066

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalAggregation
Source SHA256: 4fe4f8851e609bc42527e55e8a1654c9751dba68017cf4e24fee1c8b3632293a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1067



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma bounded_row_multiplier_energy {κ : Type*} (rows : Finset κ) (r f : κ→ℂ)
    (hr : ∀ k∈rows,‖r k‖≤1) :
    (∑ k∈rows,‖r k*f k‖^2)≤∑ k∈rows,‖f k‖^2 := by
  apply Finset.sum_le_sum
  intro k hk
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hr k hk)

theorem original_frozen_source_energy {κ σ : Type*} [Fintype σ]
    (rows : Finset κ) {m f : Eis} (z : κ→Eis) (D : ∀ k,GoodMaskRowData m f (z k))
    (Ψ : Eis→*ℂ) (Q : Ideal Eis) (hΨ : ∀ n,‖Ψ n‖≤1)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (J F Q₀ : Ideal Eis)
    (g : (Eis⧸Ideal.span {c})→Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)→Finset σ→κ→ℂ)
    (E : ℝ) (hg : ∀ h A T,(∑ k∈rows,‖g h A T k‖^2)≤E) :
    (∑ k∈rows,‖thetaDerivativeScalar⁻¹*
      ∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc ((D k).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀),
          frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ A*∑ T : Finset σ,g h A T k‖^2)≤
    ‖thetaDerivativeScalar⁻¹‖^2*
      (Fintype.card ((Eis⧸Ideal.span {c})×(Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)×Finset σ)):ℝ)^2*E := by
  let B := (Eis⧸Ideal.span {c})×(Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀)×Finset σ)
  let v := fun (b : B) k => (fixedThetaRowCoeff c hc ((D k).fixedFactor Ψ Q) b.1*
    frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ b.2.1)*g b.1 b.2.1 b.2.2 k
  have hv (b : B) : (∑ k∈rows,‖v b k‖^2)≤E := by
    apply (bounded_row_multiplier_energy rows _ _ (fun k hk =>
      original_fourier_frozen_weight_norm (D k) Ψ Q hΨ c hc b.1 J F Q₀ b.2.1)).trans
    exact hg b.1 b.2.1 b.2.2
  have he := weighted_finite_row_energy_uniform (Finset.univ : Finset B) rows (fun _ => (1:ℂ)) v E (fun b hb => hv b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at he
  have hid (k : κ) : (∑ b : B,v b k)=
      ∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc ((D k).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) Q₀),
          frozenInactiveWeight J F (Ideal.span {m}*F) Q₀ A*∑ T : Finset σ,g h A T k := by
    simp only [B,v,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  simp_rw [←hid]
  simp only [norm_mul,mul_pow,←Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq (by ring)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1067

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SourceCost
Source SHA256: ba8413a5b6db65c79db905b1b13d16036eaf27fe5849d381e7b88e4efc880706
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1068



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma pool_subset_choices_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 →
      (Fintype.card (Finset (FreeReflection.pool J Q Q₀)):ℝ)^2≤C*(Ideal.absNorm (J*Q):ℝ)^ε := by
  obtain ⟨C,hC,hb⟩ := original_pool_choice_count ε hε
  refine ⟨C,hC,?_⟩
  intro J Q Q₀ hJ hQ
  apply le_trans _ (hb J Q Q₀ hJ hQ)
  simp only [Fintype.card_finset,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) (by norm_num) _) _

theorem original_source_cost {χ : Type*} [Fintype χ] (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
    ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 →
      (Fintype.card (χ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)):ℝ)^2*
        (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤
      C*(Ideal.absNorm (J*Q):ℝ)^ε*(∏ i,H i)^ε := by
  obtain ⟨Cp,hCp,hp⟩ := pool_subset_choices_small_power ε hε
  obtain ⟨Ch,hCh,hh⟩ := harmonic_product_small_power rmax ε hε
  let C := ((Fintype.card χ:ℝ)^2+1)*(2:ℝ)^(2*rmax)*Cp*Ch
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro σ _ H hcard hH J Q Q₀ hJ hQ
  have hs : (Fintype.card (Finset σ):ℝ)^2≤(2:ℝ)^(2*rmax) := by
    simp only [Fintype.card_finset,Nat.cast_pow,Nat.cast_ofNat,←pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hcf : (Fintype.card χ:ℝ)^2≤(Fintype.card χ:ℝ)^2+1 := by linarith
  have hprod : 0≤(∏ i,H i)^ε := Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) _
  have hnp : 0≤(Ideal.absNorm (J*Q):ℝ)^ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ = (Fintype.card χ:ℝ)^2*(Fintype.card (Finset (FreeReflection.pool J Q Q₀)):ℝ)^2*
        (Fintype.card (Finset σ):ℝ)^2*(∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2 := by
      simp only [Fintype.card_prod,Nat.cast_mul,mul_pow];ring
    _ ≤ ((Fintype.card χ:ℝ)^2+1)*(Cp*(Ideal.absNorm (J*Q):ℝ)^ε)*
        (2:ℝ)^(2*rmax)*(Ch*(∏ i,H i)^ε) := by
      gcongr
      · exact hp J Q Q₀ hJ hQ
      · exact hh H hcard hH
    _ = _ := by dsimp [C];ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1068

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SourceBudget
Source SHA256: 7e8e129ddc6652bde1f39a879f924b1c17ec21f4dccb800b22359fa1454b284c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1069


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem original_source_cost_budget {χ : Type*} [Fintype χ]
    (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] (H : σ→ℝ),
      Fintype.card σ≤rmax → (∀ i,1≤H i) →
    ∀ (J Q Q₀ : Ideal Eis),J≠0 → Q≠0 → ∀ (Z Lpool Lslot loss : ℝ),1<Z →
      (Ideal.absNorm (J*Q):ℝ)≤Z^Lpool → (∏ i,H i)≤Z^Lslot → ε*(Lpool+Lslot)≤loss →
      (Fintype.card (χ×(Finset (FreeReflection.pool J Q Q₀)×Finset σ)):ℝ)^2*
        (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2≤C*Z^loss := by
  obtain ⟨C,hC,hb⟩ := original_source_cost (χ:=χ) rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ _ H hcard hH J Q Q₀ hJ hQ Z Lpool Lslot loss hZ hpool hslot hloss
  have hz : 0<Z := lt_trans zero_lt_one hZ
  apply (hb H hcard hH J Q Q₀ hJ hQ).trans
  calc
    _ ≤ C*(Z^Lpool)^ε*(Z^Lslot)^ε := by
      have hp := Real.rpow_le_rpow (Nat.cast_nonneg (Ideal.absNorm (J*Q))) hpool hε.le
      have hs := Real.rpow_le_rpow (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) hslot hε.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) hs
        (Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hH i))) _) (by positivity)
    _ = C*Z^(ε*(Lpool+Lslot)) := by
      rw [←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,mul_assoc,←Real.rpow_add hz]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le hloss) hC.le
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1069

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.DyadBudget
Source SHA256: 432fa77b6f96339b5f6942a99c2b405772c5d16454ef1c8873168b789e22df3c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1070


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
noncomputable section

lemma columnDyadicLength_mono_pos {A B : ℝ} (hA : 0<A) (hAB : A≤B) :
    columnDyadicLength A≤columnDyadicLength B := by
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_right (Real.log_le_log hA hAB) (Real.log_nonneg (by norm_num))

theorem actual_dyad_count_budget (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z Hrow Hslot : ℝ,1≤Z → 0<Hrow → 0<Hslot →
      Hrow≤Z^L → Hslot≤Z^L →
      (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2≤C*Z^ε := by
  let a := ε/(3*(L+1))
  have ha : 0<a := div_pos hε (by positivity)
  let B := 2+1/(a*Real.log 2)
  have hB : 0<B := by dsimp only [B];have := Real.log_pos (by norm_num : (1:ℝ)<2);positivity
  refine ⟨B^3,by positivity,?_⟩
  intro Z Hrow Hslot hZ hR hS hRc hSc
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hnorm := Real.one_le_rpow hZ hL
  have hcount := columnDyadicLength_small_power a ha (Z^L) hnorm
  have hr : (columnDyadicLength Hrow+1:ℝ)≤B*(Z^L)^a := by
    have hle : (columnDyadicLength Hrow+1:ℝ)≤(columnDyadicLength (Z^L)+1:ℝ) := by
      exact_mod_cast Nat.add_le_add_right (columnDyadicLength_mono_pos hR hRc) 1
    exact hle.trans hcount
  have hs : (columnDyadicLength Hslot+1:ℝ)≤B*(Z^L)^a := by
    have hle : (columnDyadicLength Hslot+1:ℝ)≤(columnDyadicLength (Z^L)+1:ℝ) := by
      exact_mod_cast Nat.add_le_add_right (columnDyadicLength_mono_pos hS hSc) 1
    exact hle.trans hcount
  have hexp : L*a*3≤ε := by
    have he : a*(3*(L+1))=ε := by dsimp [a];field_simp
    have hh : 0≤a := ha.le
    nlinarith
  calc
    _ ≤ (B*(Z^L)^a)*(B*(Z^L)^a)^2 := by gcongr
    _ = B^3*((Z^L)^a)^3 := by ring
    _ = B^3*Z^(L*a*3) := by
      rw [←Real.rpow_mul hz.le]
      have he := Real.rpow_mul_natCast hz.le (L*a) 3
      norm_num only [Nat.cast_ofNat] at he
      rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexp) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1070

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SurvivingGate
Source SHA256: 00fa12362473bf0d71f3311d583805ec7ca97285ba4c40003efb2b9e53a0d45e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1071




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic CompletedGauss ActualEisensteinCubic CubicEisenstein CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u
variable {a c : Eis} {mode : Bool}

theorem actual_surviving_retained_gates
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ],
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ→ℕ) (A : Ideal Eis→Ideal Eis→ℂ) (e : φ→Fin 3)
      (Z X QK QP δ : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<X → 0<QK → 0<QP →
      i∈retainedDyads (familyRawScale F s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches F jF A (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))
      0≤v ∧ 0≤ell ∧ -η≤InverseTerminalWidths.ramifiedWidth Z i.1 ∧
      v+3*ell+InverseTerminalWidths.ramifiedWidth Z i.1≤
        InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP)) (Real.logb Z X)
          F.ideal jF e+δ+η := by
  obtain ⟨Z₁,hZ₁,hwidth⟩ := actual_retained_width_uniform s hc kK kP 1 1 η hkK hkP (by norm_num) (by norm_num) hη
  obtain ⟨Z₂,hZ₂,hram⟩ := InverseTerminalWidths.ramified_width_threshold η hη
  refine ⟨max Z₁ Z₂,lt_of_lt_of_le hZ₁ (le_max_left _ _),?_⟩
  intro φ _ F hF jF A e Z X QK QP δ i hZ hX hQK hQP hi he
  have hz1 := (le_max_left Z₁ Z₂).trans hZ
  have hz2 := (le_max_right Z₁ Z₂).trans hZ
  have hz := lt_of_lt_of_le hZ₁ hz1
  have hnorm := surviving_forced_norms F hF jF A (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
    ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
    (fun n hn => ⟨(reflectedNDyad_bounds _ n hn).1.2,(reflectedNDyad_bounds _ n hn).2.2⟩)
    (fun b hb => ⟨(reflectedBDyad_bounds _ b hb).1,(reflectedBDyad_bounds _ b hb).2.2⟩) e he
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  refine ⟨Real.logb_nonneg hz ((one_le_div (hp 1)).mpr hnorm.1),
    Real.logb_nonneg hz ((one_le_div (hp 2)).mpr hnorm.2),hram Z hz2 i.1,?_⟩
  simpa only [one_mul] using hwidth F jF e Z X QK QP δ i hz1 hX hQK hQP hi
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1071

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowExponent
Source SHA256: b8cc04e4b29696f52681680fb29b8fff946e7079fd05cab7b1e80c48111d2f08
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1072





namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_low_exponent
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hη : 0<η) :
    ∃ Z₀ : ℝ,1<Z₀ ∧
    ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀)) (e : A→Fin 3) (column : Ideal Eis→Ideal Eis→ℂ)
      (Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → 0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))
      InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
        (normWidth Z (frozenExtracted G j e 2)) za v ell (ramifiedWidth Z i.1)
        (terminalDualWidth Z H za Nstar G.ideal j e)+ε*(H+v+ell+za)+η/2+O₀/2≤
      (5/6-2*d)+200*η+π := by
  obtain ⟨Z₀,hZ₀,hgates⟩ := actual_surviving_retained_gates s hc₀ kK kP η hkK hkP hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro J I F Q Q₀ hJ hI hQ hpower hmask A e column
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hK hP hIn hPow hRow hlog hPowUpper hQwidth hd hd1 hell0 hO hza hshift
    hNs heH heza heN hδ hδη hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscale hret hsurv
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  obtain ⟨hv,hell,hel,hwidth⟩ := hgates G hpair j column e Z X QK QP δ i hZ hX hK hP hret hsurv
  rw [←heH,←heza,←heN] at hwidth
  have hH := physical_residual_width I Q hI Z (5/6-2*d) O₀ H Ck CO CH hz hCk hCO hCH hIn hPow hRow
  have hA := original_optional_powerful_width J I Q Q₀ hJ hI hQ hpower hmask A Z hz
  have hN0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 1)
  have hS0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 0)
  have hB0 := normWidth_nonneg Z hz _ (frozenExtracted_ne_zero G j e 2)
  have hNA := frozenExtracted_width_le G j e 1 Z hz
  have ht := ProbeLowReflected.compensated_reflected_exponent_with_length d ell0 O₀ H
    (normWidth Z (∏ b,G.ideal b)) (normWidth Z (frozenExtracted G j e 1))
    (normWidth Z (frozenExtracted G j e 0)) (normWidth Z (frozenExtracted G j e 2)) za
    (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
    (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
    (ramifiedWidth Z i.1) shift (5*η)
    hd hd1 (by positivity) (by linarith) (by linarith) (by linarith)
    hN0 hNA hS0 hB0 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (hshift.trans (by linarith)) ?_
  · have hb := retained_extracted_log_budget (familyRawScale G s X QK QP) Z δ Lscale Lrow Lslot η
      (kK*QK) (kP*QP) (familyRawScale_pos G s hc₀ X QK QP hX hK hP) hz
      (mul_pos hkK hK) (mul_pos hkP hP) hscale hconst hrowcap hslotcap i hret
      (frozenExtracted G j e 1) (frozenExtracted G j e 2)
      (frozenExtracted_ne_zero G j e 1) (frozenExtracted_ne_zero G j e 2)
    rw [←heH,←heza] at hb
    have hb' := mul_le_mul_of_nonneg_left hb hε
    have hTd : terminalDualWidth Z H za Nstar G.ideal j e=
        2*H+2*normWidth Z (∏ b,G.ideal b)+2*za-1-ell0-shift-
          normWidth Z (frozenExtracted G j e 1)-3*normWidth Z (frozenExtracted G j e 2) := by
      unfold terminalDualWidth
      rw [hNs,←frozenExtracted_eq_ideal,←frozenExtracted_eq_ideal]
      ring
    change InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
      (normWidth Z (frozenExtracted G j e 2)) za _ _ _ _+_+_+_≤_
    rw [hTd]
    unfold InverseTerminalWidths.reflectedExponent at ht ⊢
    linarith
  · dsimp only [terminalDualWidth] at hwidth
    rw [hNs,←frozenExtracted_eq_ideal,←frozenExtracted_eq_ideal] at hwidth
    linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1072

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowBranchSum
Source SHA256: 375f53ce006acaa55fc5aea985804beaa9abe61868ad2978f59ebe5755380ced
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1073




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_low_energy_sum
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (ρ : ℝ) (hρ : 0<ρ) (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ C : ℝ, 1<Z₀ ∧ 0<C ∧
    ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot : ℝ) (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → 0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      ((branches.card:ℝ)*∑ e∈branches,
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))≤
        C*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^((5/6-2*d)+200*η+π-O₀/2) := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_low_exponent s hc₀ kK kP η hkK hkP hηpos
  obtain ⟨C,hC,hcount⟩ := surviving_branch_count_small_power ρ hρ
  refine ⟨Z₀,C,hZ₀,hC,?_⟩
  intro J I F Q Q₀ hJ hI hQ hpower hmask A column
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ hδη hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hcbr := hcount G ((poolPrimeFamily J Q Q₀).restrict_pairwise
    (poolPrimeFamily_pairwise J Q Q₀) A) j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hb (e : A→Fin 3) (he : e∈branches) := hsave J I F Q Q₀ hJ hI hQ hpower hmask A e column
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ hδη hε hrowcap hslotcap hconst hbudget hscap hret he
  calc
    _ ≤ (branches.card:ℝ)*∑ _e∈branches,Z^((5/6-2*d)+200*η+π-O₀/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he
      apply Real.rpow_le_rpow_of_exponent_le hz'.le
      have hh := hb e he
      dsimp only at hh
      linarith
    _ = ((branches.card:ℝ)^2)*Z^((5/6-2*d)+200*η+π-O₀/2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcbr (Real.rpow_nonneg (lt_trans zero_lt_one hz').le _)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1073

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalSaving
Source SHA256: fc192a454261456733c46efceeb9ca5f4c9bfd08101fa64c989717999007ab57
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1074



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_terminal_saving
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧
    ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (e : A→Fin 3)
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))
      InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
        (normWidth Z (frozenExtracted G j e 2)) za v ell (ramifiedWidth Z i.1)
        (terminalDualWidth Z H za Nstar G.ideal j e)+O₀/2+π≤F₀-cstar/4 := by
  obtain ⟨Z₀,hZ₀,hgates⟩ := actual_surviving_retained_gates s hc₀ kK kP η hkK hkP hηpos
  refine ⟨Z₀,hZ₀,?_⟩
  intro J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ
  dsimp only
  intro hret hsurv
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hG := (poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A
  obtain ⟨hv,hell,hel,hwidth⟩ := hgates G hG j column e Z X QK QP δ i hZ hX hQK hQP hret hsurv
  rw [←heH,←heza,←heN] at hwidth
  exact original_optional_terminal_saving J I F B R Q₀ hJ hI hF hB hR hpower hmask A e
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat
    (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
    (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
    (ramifiedWidth Z i.1) d η (δ+η) π Ck CO CH Cf
    (lt_of_lt_of_le hZ₀ hZ) hCk hCO hCH hCf hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    hM hO hz hzcap hv hell hel (by simpa only [add_assoc] using hwidth)
    hc hmargin hd hη hτ hπ
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1074

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalExponent
Source SHA256: f1256a54a08c1c2d0f090aad85d00481a703bcf29dc7de8259bde403ebe49faf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1075



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_energy_exponent
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧
    ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (e : A→Fin 3)
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      e∈survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) →
      let v := Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))
      let ell := Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))
      InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
        (normWidth Z (frozenExtracted G j e 2)) za v ell (ramifiedWidth Z i.1)
        (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+v+ell+za)+η/2+O₀/2≤F₀-cstar/4 := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_terminal_saving s hc₀ kK kP η hkK hkP hηpos
  refine ⟨Z₀,hZ₀,?_⟩
  intro J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret hsurv
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hs := hsave J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hret hsurv
  have hb := retained_extracted_log_budget (familyRawScale G s X QK QP) Z δ Lscale Lrow Lslot η
    (kK*QK) (kP*QP) (familyRawScale_pos G s hc₀ X QK QP hX hQK hQP)
    (lt_of_lt_of_le hZ₀ hZ) (mul_pos hkK hQK) (mul_pos hkP hQP) hscap hconst hrowcap hslotcap i hret
    (frozenExtracted G j e 1) (frozenExtracted G j e 2)
    (frozenExtracted_ne_zero G j e 1) (frozenExtracted_ne_zero G j e 2)
  rw [←heH,←heza] at hb
  have he := mul_le_mul_of_nonneg_left hb hε
  dsimp only [G,j] at hs hb he
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1075

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalBranchSum
Source SHA256: eccf5f6dd531ec629b11c7002d300b09468ab439399eae844cce92d6afd4adc7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1076




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {a c₀ : Eis} {mode : Bool}

theorem original_surviving_energy_sum
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (ρ : ℝ) (hρ : 0<ρ) (kK kP η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hηpos : 0<η) :
    ∃ Z₀ C : ℝ, 1<Z₀ ∧ 0<C ∧
    ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (column : Ideal Eis→Ideal Eis→ℂ)
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z (kK*QK) → za=Real.logb Z (kP*QP) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      0≤ε → (kK*QK)≤Z^Lrow → (kP*QP)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
      let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      ((branches.card:ℝ)*∑ e∈branches,
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))≤
        C*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨Z₀,hZ₀,hsave⟩ := original_surviving_energy_exponent s hc₀ kK kP η hkK hkP hηpos
  obtain ⟨C,hC,hcount⟩ := surviving_branch_count_small_power ρ hρ
  refine ⟨Z₀,C,hZ₀,hC,?_⟩
  intro J I F B R Q₀ hJ hI hF hB hR hpower hmask A column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let branches := survivingFrozenBranches G j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hcbr := hcount G ((poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise
    (poolPrimeFamily_pairwise J (B*F*R) Q₀) A) j column (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hb (e : A→Fin 3) (he : e∈branches) := hsave J I F B R Q₀ hJ hI hF hB hR hpower hmask A e column
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε hrowcap hslotcap hconst hbudget hscap hret he
  calc
    _ ≤ (branches.card:ℝ)*∑ _e∈branches,Z^(F₀-cstar/4-O₀/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro e he
      apply Real.rpow_le_rpow_of_exponent_le hz'.le
      have hh := hb e he
      dsimp only at hh
      linarith
    _ = ((branches.card:ℝ)^2)*Z^(F₀-cstar/4-O₀/2) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcbr (Real.rpow_nonneg (lt_trans zero_lt_one hz').le _)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1076

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.TupleMasks
Source SHA256: d8c545dd3bbd142563509bb5b432cea1d05da4527761a261f08359d380d37835
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1077



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
lemma slot_choice_fixed_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val) (F : φ→Ideal Eis) :
    (∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j) ↔
      (∀ j,∀ i : T,(a i).val≠F j) ∧ (∀ j,∀ i : {i // i∉T},(b i).val≠F j) := by
  constructor
  · intro h
    constructor
    · intro j i
      simpa only [slotChoiceSplit_active] using h j i.val
    · intro j i
      simpa only [slotChoiceSplit_inactive] using h j i.val
  · rintro ⟨ha,hb⟩ j i
    by_cases hi : i∈T
    · rw [slotChoiceSplit_active L T a b ⟨i,hi⟩]
      exact ha j ⟨i,hi⟩
    · rw [slotChoiceSplit_inactive L T a b ⟨i,hi⟩]
      exact hb j ⟨i,hi⟩

lemma slot_choice_mask_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val)
    (F : φ→Ideal Eis) (K : Ideal Eis) :
    (IsCoprime K (∏ i,((slotChoiceSplit L T).symm (a,b) i).val) ∧
      ∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j) ↔
    (IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j,∀ i : {i // i∉T},(b i).val≠F j) ∧
      (IsCoprime K (∏ i : T,(a i).val) ∧ ∀ j,∀ i : T,(a i).val≠F j) := by
  rw [slot_choice_coprime_split,slot_choice_fixed_split]
  tauto

def fixedTupleWeight (F : φ→Ideal Eis) (a : σ→Ideal Eis) (w : ℂ) : ℂ :=
  if ∀ j i,a i≠F j then w else 0

omit [Fintype σ] [DecidableEq σ] in
lemma fixedTupleWeight_norm (F : φ→Ideal Eis) (a : σ→Ideal Eis) (w : ℂ) :
    ‖fixedTupleWeight F a w‖≤‖w‖ := by
  unfold fixedTupleWeight
  split
  · exact le_rfl
  · simp

lemma split_masked_column (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val)
    (F : φ→Ideal Eis) (K : Ideal Eis) (w v : ℂ) :
    (if IsCoprime K (∏ i,((slotChoiceSplit L T).symm (a,b) i).val) ∧
      ∀ j i,((slotChoiceSplit L T).symm (a,b) i).val≠F j then w*v else 0)=
    if IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j,∀ i : {i // i∉T},(b i).val≠F j then
      (if IsCoprime K (∏ i : T,(a i).val) then fixedTupleWeight F (fun i : T => (a i).val) w*v else 0)
    else 0 := by
  simp only [slot_choice_mask_split]
  simp only [fixedTupleWeight]
  split_ifs <;> simp_all
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1077

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SupportedChoices
Source SHA256: 6c48a1a729fccbacc190c710722fa7305c460e7a39d0cbf87e798809ad3b4f0c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1078


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def supportedSlotChoices (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :=
  {p : ∀ i,L i // IsCoprime K (∏ i,(p i).val) ∧ ∀ j i,(p i).val≠F j}

instance supportedSlotChoices_fintype (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :
    Fintype (supportedSlotChoices L F K) := inferInstanceAs (Fintype {_p : ∀ i,L i // _})

def supportedSlotSplit (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis) (K : Ideal Eis) :
    supportedSlotChoices L F K ≃
      supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K ×
        supportedSlotChoices (fun i : T => L i.val) F K where
  toFun p :=
    let q := slotChoiceSplit L T p.val
    have h := (slot_choice_mask_split L T q.1 q.2 F K).mp (by simpa only [q,Prod.mk.eta,Equiv.symm_apply_apply] using p.property)
    (⟨q.2,h.1⟩,⟨q.1,h.2⟩)
  invFun q := ⟨(slotChoiceSplit L T).symm (q.2.val,q.1.val),
    (slot_choice_mask_split L T q.2.val q.1.val F K).mpr ⟨q.1.property,q.2.property⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact (slotChoiceSplit L T).symm_apply_apply p.val
  right_inv q := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.snd ((slotChoiceSplit L T).apply_symm_apply (q.2.val,q.1.val))
    · exact congrArg Prod.fst ((slotChoiceSplit L T).apply_symm_apply (q.2.val,q.1.val))

theorem sum_supported_slot_choices (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (F : φ→Ideal Eis) (K : Ideal Eis) (H : supportedSlotChoices L F K→ℂ) :
    (∑ p : supportedSlotChoices L F K,
      (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p.val i).val:ℂ)⁻¹)*H p)=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K,
      (∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*
        ∑ a : supportedSlotChoices (fun i : T => L i.val) F K,
          H ((supportedSlotSplit L T F K).symm (b,a)) := by
  rw [←(supportedSlotSplit L T F K).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  change (∏ i∈(Finset.univ:Finset σ)\T,
    (Ideal.absNorm (((slotChoiceSplit L T).symm (a.val,b.val)) i).val:ℂ)⁻¹)=_
  rw [slot_choice_inactive_weight,Equiv.apply_symm_apply]
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1078

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SlotCoefficients
Source SHA256: deeadcd6ff8005715027b2e5a18fd41c80a3ac4766bf12ff38ecb9dcd3aa43c6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1079



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma PrimeFamily.eq_of_ideal_eq {ι : Type*} (P Q : PrimeFamily ι) (h : P.ideal=Q.ideal) : P=Q := by
  cases P
  cases Q
  cases h
  rfl

def slotChoiceFamily (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (p : ∀ i,L i) : PrimeFamily σ where
  ideal i := (p i).val
  maximal i := hmax i _ (p i).property
  good i := hgood i _ (p i).property

omit [Fintype σ] in
lemma slotChoiceFamily_active (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (T : Finset σ) (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val) :
    (slotChoiceFamily L hmax hgood ((slotChoiceSplit L T).symm (a,b))).restrict T=
      slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) a := by
  apply PrimeFamily.eq_of_ideal_eq
  funext i
  exact congrArg Subtype.val (slotChoiceSplit_active L T a b i)

lemma slot_coefficient_split (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (w : ∀ i,L i→ℂ) (a : ∀ i : T,L i.val) (b : ∀ i : {i // i∉T},L i.val) :
    (∏ i,w i ((slotChoiceSplit L T).symm (a,b) i))=
      (∏ i : T,w i.val (a i))*(∏ i : {i // i∉T},w i.val (b i)) := by
  have he := Fintype.prod_subtype_mul_prod_subtype (fun i : σ => i∈T)
    (fun i => w i ((slotChoiceSplit L T).symm (a,b) i))
  simp only [slotChoiceSplit_active,slotChoiceSplit_inactive] at he
  refine he.symm.trans ?_
  congr 1
  apply Finset.prod_congr (by ext; simp only [Finset.mem_univ])
  intro i hi
  rfl

omit [DecidableEq σ] in
lemma slot_coefficient_norm (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (p : ∀ i,L i) : ‖∏ i,w i (p i)‖≤1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hw i (p i))
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1079

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CubeSlots
Source SHA256: eeff4c247ffdf8e554c75d1913cf4573a8579ec1cb714b003eb76c15b72bfffb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1080



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma prime_dvd_cube_mul (P H A : Ideal Eis) (hP : Prime P) :
    P∣H^3*A ↔ P∣H ∨ P∣A := by
  constructor
  · intro h
    rcases hP.dvd_mul.mp h with h|h
    · exact Or.inl (hP.dvd_of_dvd_pow h)
    · exact Or.inr h
  · rintro (h|h)
    · exact dvd_mul_of_dvd_left (dvd_pow h (by decide : (3:ℕ)≠0)) A
    · exact dvd_mul_of_dvd_right h _

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def cubeActiveSlots (H : Ideal Eis) (S : PrimeFamily σ) : Finset σ :=
  Finset.univ.filter (fun i => ¬S.ideal i∣H)

omit [DecidableEq σ] in
lemma cube_shifted_mark (H A : Ideal Eis) (S : PrimeFamily σ) :
    (∏ i,if S.ideal i∣H^3*A then (1:ℂ) else 0)=
      ∏ i∈cubeActiveSlots H S,if S.ideal i∣A then (1:ℂ) else 0 := by
  rw [cubeActiveSlots,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  have hp : Prime (S.ideal i) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  rw [prime_dvd_cube_mul _ H A hp]
  by_cases hh : S.ideal i∣H
  · simp only [hh,true_or,ite_true,not_true_eq_false,ite_false]
  · simp only [hh,false_or,not_false_eq_true,ite_true]

omit [DecidableEq σ] in
lemma cube_shifted_mark_restrict (H A : Ideal Eis) (S : PrimeFamily σ) :
    (∏ i,if S.ideal i∣H^3*A then (1:ℂ) else 0)=
      ∏ i : cubeActiveSlots H S,if (S.restrict (cubeActiveSlots H S)).ideal i∣A then (1:ℂ) else 0 := by
  rw [cube_shifted_mark]
  symm
  exact Finset.prod_coe_sort (cubeActiveSlots H S) (fun i => if S.ideal i∣A then (1:ℂ) else 0)

omit [DecidableEq σ] in
theorem markedCompletedT_cube_shift (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ)
    (H : Ideal Eis) (S : PrimeFamily σ) :
    markedCompletedT Ψ W X (fun A => ∏ i,if S.ideal i∣H^3*A then (1:ℂ) else 0)=
      markedCompletedT Ψ W X
        (fun A => ∏ i : cubeActiveSlots H S,if (S.restrict (cubeActiveSlots H S)).ideal i∣A then (1:ℂ) else 0) := by
  congr 1
  funext A
  exact cube_shifted_mark_restrict H A S

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1080

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CubeSlotChoices
Source SHA256: 0df5cc8a920a428e703ce361442efbc01a27e21618c6c834b9b5f7eb7701c554
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1081


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

 def cubeDivList (H : Ideal Eis) (L : Finset (Ideal Eis)) : Finset (Ideal Eis) := L.filter (fun P => P∣H)
 def cubeAwayList (H : Ideal Eis) (L : Finset (Ideal Eis)) : Finset (Ideal Eis) := L.filter (fun P => ¬P∣H)
 def cubeChoiceActive (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (p : ∀ i,L i) : Finset σ :=
  Finset.univ.filter (fun i => ¬(p i).val∣H)

abbrev CubeSlotChoices (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :=
  Σ T : Finset σ,(∀ i : {i // i∉T},cubeDivList H (L i.val))×(∀ i : T,cubeAwayList H (L i.val))

def cubeChoicesJoin (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (x : CubeSlotChoices H L) : ∀ i,L i :=
  (slotChoiceSplit L x.1).symm
    (fun i => ⟨(x.2.2 i).val,(Finset.mem_filter.mp (x.2.2 i).property).1⟩,
     fun i => ⟨(x.2.1 i).val,(Finset.mem_filter.mp (x.2.1 i).property).1⟩)

lemma cubeChoicesJoin_label (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) (x : CubeSlotChoices H L) :
    cubeChoiceActive H L (cubeChoicesJoin H L x)=x.1 := by
  rcases x with ⟨T,b,a⟩
  ext i
  simp only [cubeChoiceActive,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hi : i∈T
  · have ha := (Finset.mem_filter.mp (a ⟨i,hi⟩).property).2
    have he := slotChoiceSplit_active L T
      (fun j => ⟨(a j).val,(Finset.mem_filter.mp (a j).property).1⟩)
      (fun j => ⟨(b j).val,(Finset.mem_filter.mp (b j).property).1⟩) ⟨i,hi⟩
    dsimp only [cubeChoicesJoin]
    rw [he]
    exact iff_of_true ha hi
  · have hb := (Finset.mem_filter.mp (b ⟨i,hi⟩).property).2
    have he := slotChoiceSplit_inactive L T
      (fun j => ⟨(a j).val,(Finset.mem_filter.mp (a j).property).1⟩)
      (fun j => ⟨(b j).val,(Finset.mem_filter.mp (b j).property).1⟩) ⟨i,hi⟩
    dsimp only [cubeChoicesJoin]
    rw [he]
    exact iff_of_false (not_not_intro hb) hi

lemma cubeChoicesJoin_injective (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    Function.Injective (cubeChoicesJoin H L) := by
  rintro ⟨T,b,a⟩ ⟨U,d,c⟩ he
  have ht := congrArg (cubeChoiceActive H L) he
  rw [cubeChoicesJoin_label,cubeChoicesJoin_label] at ht
  dsimp only at ht
  subst U
  apply congrArg (fun q => (⟨T,q⟩ : CubeSlotChoices H L))
  have hx := congrArg (slotChoiceSplit L T) he
  simp only [cubeChoicesJoin,Equiv.apply_symm_apply] at hx
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact congrArg (fun q => (q.2 i).val) hx
  · funext i
    apply Subtype.ext
    exact congrArg (fun q => (q.1 i).val) hx

lemma cubeChoicesJoin_surjective (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    Function.Surjective (cubeChoicesJoin H L) := by
  intro p
  let T := cubeChoiceActive H L p
  let a : ∀ i : T,cubeAwayList H (L i.val) := fun i =>
    ⟨(p i.val).val,Finset.mem_filter.mpr ⟨(p i.val).property,(Finset.mem_filter.mp i.property).2⟩⟩
  have hd (i : {i // i∉T}) : (p i.val).val∣H := by
    by_contra hi
    exact i.property (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  let b : ∀ i : {i // i∉T},cubeDivList H (L i.val) := fun i =>
    ⟨(p i.val).val,Finset.mem_filter.mpr ⟨(p i.val).property,hd i⟩⟩
  refine ⟨⟨T,b,a⟩,?_⟩
  apply (slotChoiceSplit L T).injective
  simp only [cubeChoicesJoin,Equiv.apply_symm_apply]
  apply Prod.ext <;> funext i <;> apply Subtype.ext <;> rfl

def cubeSlotChoiceEquiv (H : Ideal Eis) (L : σ→Finset (Ideal Eis)) :
    CubeSlotChoices H L ≃ (∀ i,L i) :=
  Equiv.ofBijective (cubeChoicesJoin H L) ⟨cubeChoicesJoin_injective H L,cubeChoicesJoin_surjective H L⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1081

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CubeSlotSource
Source SHA256: 27a444721e40e117289c98705877ee138826a3a68ffbb7861ac2a4165ca10cf5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1082


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (H : Ideal Eis) (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

include hmax hgood in
lemma cubeJoined_mark (x : CubeSlotChoices H L) (A : Ideal Eis) :
    (∏ i,if (cubeChoicesJoin H L x i).val∣H^3*A then (1:ℂ) else 0)=
      ∏ i : x.1,if (x.2.2 i).val∣A then (1:ℂ) else 0 := by
  have hs := cube_shifted_mark H A (slotChoiceFamily L hmax hgood (cubeChoicesJoin H L x))
  have hl : cubeActiveSlots H (slotChoiceFamily L hmax hgood (cubeChoicesJoin H L x))=x.1 :=
    cubeChoicesJoin_label H L x
  rw [hl] at hs
  apply hs.trans
  rw [←Finset.prod_coe_sort x.1]
  apply Finset.prod_congr rfl
  intro i hi
  have he := slotChoiceSplit_active L x.1
    (fun i => ⟨(x.2.2 i).val,(Finset.mem_filter.mp (x.2.2 i).property).1⟩)
    (fun i => ⟨(x.2.1 i).val,(Finset.mem_filter.mp (x.2.1 i).property).1⟩) i
  change (if ((slotChoiceSplit L x.1).symm _ i.val).val∣A then (1:ℂ) else 0)=_
  rw [he]

include hmax hgood in
lemma cubeJoined_completed (x : CubeSlotChoices H L) (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT Ψ W X
      (fun A => ∏ i,if (cubeChoicesJoin H L x i).val∣H^3*A then (1:ℂ) else 0)=
    markedCompletedT Ψ W X
      (fun A => ∏ i : x.1,if (x.2.2 i).val∣A then (1:ℂ) else 0) := by
  congr 1
  funext A
  exact cubeJoined_mark H L hmax hgood x A

lemma cubeJoined_coefficient (x : CubeSlotChoices H L) (w : ∀ i,L i→ℂ) :
    (∏ i,w i (cubeChoicesJoin H L x i))=
      (∏ i : {i // i∉x.1},w i.val ⟨(x.2.1 i).val,(Finset.mem_filter.mp (x.2.1 i).property).1⟩)*
      (∏ i : x.1,w i.val ⟨(x.2.2 i).val,(Finset.mem_filter.mp (x.2.2 i).property).1⟩) := by
  exact (slot_coefficient_split L x.1 w _ _).trans (mul_comm _ _)

def cubeAbsorbedCoefficient (w : ∀ i,L i→ℂ) (T : Finset σ) : ℂ :=
  ∑ b : ∀ i : {i // i∉T},cubeDivList H (L i.val),
    ∏ i : {i // i∉T},w i.val ⟨(b i).val,(Finset.mem_filter.mp (b i).property).1⟩

lemma cubeAbsorbedCoefficient_product (w : ∀ i,L i→ℂ) (T : Finset σ) :
    cubeAbsorbedCoefficient H L w T=
      ∏ i : {i // i∉T},∑ P : cubeDivList H (L i.val),w i.val ⟨P.val,(Finset.mem_filter.mp P.property).1⟩ :=
  (Fintype.prod_sum (fun (i : {i // i∉T}) (P : cubeDivList H (L i.val)) =>
    w i.val ⟨P.val,(Finset.mem_filter.mp P.property).1⟩)).symm

include hmax hgood

theorem original_cube_shifted_tuple_source (w : ∀ i,L i→ℂ)
    (Ψ : Eis→*ℂ) (W : ℝ→ℂ) (X : ℝ) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT Ψ W X
      (fun A => ∏ i,if (p i).val∣H^3*A then (1:ℂ) else 0))=
    ∑ T : Finset σ,cubeAbsorbedCoefficient H L w T*
      ∑ a : ∀ i : T,cubeAwayList H (L i.val),
        (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
          markedCompletedT Ψ W X (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0) := by
  rw [←(cubeSlotChoiceEquiv H L).sum_comp]
  change (∑ x : CubeSlotChoices H L,(∏ i,w i (cubeChoicesJoin H L x i))*
    markedCompletedT Ψ W X (fun A => ∏ i,if (cubeChoicesJoin H L x i).val∣H^3*A then (1:ℂ) else 0))=_
  simp_rw [cubeJoined_completed H L hmax hgood,cubeJoined_coefficient]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Fintype.sum_prod_type]
  simp only [cubeAbsorbedCoefficient,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1082

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CubeSlotBounds
Source SHA256: a7b420f75fc4a2fdadd7341e5e997f617802e019c4b112fa8c20e2c1b0e915b7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1083


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
open IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma cubeDivList_card (H : Ideal Eis) (hH : H≠0) (L : Finset (Ideal Eis)) :
    (cubeDivList H L).card≤(idealDivisors H).card := by
  apply Finset.card_le_card
  intro P hP
  exact (mem_idealDivisors hH).mpr (Finset.mem_filter.mp hP).2

lemma cube_divisor_card_one (H : Ideal Eis) (hH : H≠0) :
    (1:ℝ)≤(idealDivisors H).card := by
  exact_mod_cast Finset.card_pos.mpr ⟨1,(mem_idealDivisors hH).mpr (one_dvd H)⟩

lemma cubeAbsorbedCoefficient_norm (H : Ideal Eis) (hH : H≠0)
    (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (T : Finset σ) (rmax : ℕ)
    (hr : Fintype.card σ≤rmax) :
    ‖cubeAbsorbedCoefficient H L w T‖≤((idealDivisors H).card:ℝ)^rmax := by
  rw [cubeAbsorbedCoefficient_product,norm_prod]
  calc
    _ ≤ ∏ i : {i // i∉T},((idealDivisors H).card:ℝ) := by
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i hi
      calc
        _ ≤ ∑ P : cubeDivList H (L i.val),‖w i.val ⟨P.val,(Finset.mem_filter.mp P.property).1⟩‖ := norm_sum_le _ _
        _ ≤ ∑ _P : cubeDivList H (L i.val),(1:ℝ) := Finset.sum_le_sum (fun P _ => hw _ _)
        _ = ((cubeDivList H (L i.val)).card:ℝ) := by simp
        _ ≤ _ := Nat.cast_le.mpr (cubeDivList_card H hH _)
    _ = ((idealDivisors H).card:ℝ)^(Fintype.card {i // i∉T}) := by simp
    _ ≤ _ := pow_le_pow_right₀ (cube_divisor_card_one H hH)
      ((Fintype.card_subtype_le _).trans hr)

lemma cubeAbsorbedCoefficient_mass (H : Ideal Eis) (hH : H≠0)
    (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (rmax : ℕ) (hr : Fintype.card σ≤rmax) :
    (∑ T : Finset σ,‖cubeAbsorbedCoefficient H L w T‖)≤
      (2:ℝ)^rmax*((idealDivisors H).card:ℝ)^rmax := by
  calc
    _ ≤ ∑ _T : Finset σ,((idealDivisors H).card:ℝ)^rmax :=
      Finset.sum_le_sum (fun T _ => cubeAbsorbedCoefficient_norm H hH L w hw T rmax hr)
    _ = (2:ℝ)^(Fintype.card σ)*((idealDivisors H).card:ℝ)^rmax := by
      simp [Fintype.card_finset]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hr) (by positivity)

theorem cubeAbsorbedCoefficient_small_power (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      (H : Ideal Eis),H≠0 → ∀ (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ),
      (∀ i P,‖w i P‖≤1) → Fintype.card σ≤rmax →
      (∑ T : Finset σ,‖cubeAbsorbedCoefficient H L w T‖)^2≤C*(Ideal.absNorm H:ℝ)^ε := by
  let δ : ℝ := ε/(2*rmax+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨D,hD,hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨((2:ℝ)^rmax*D^rmax)^2,by positivity,?_⟩
  intro σ _ _ H hH L w hw hr
  have hn : (1:ℝ)≤Ideal.absNorm H := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hH (Ideal.absNorm_eq_zero_iff.mp h))
  have hn0 : 0<(Ideal.absNorm H:ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hde : δ*(rmax:ℝ)*2≤ε := by
    dsimp [δ]
    have hp : (0:ℝ)<2*rmax+1 := by positivity
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  calc
    _ ≤ ((2:ℝ)^rmax*((idealDivisors H).card:ℝ)^rmax)^2 := by
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
        (cubeAbsorbedCoefficient_mass H hH L w hw rmax hr) 2
    _ ≤ ((2:ℝ)^rmax*(D*(Ideal.absNorm H:ℝ)^δ)^rmax)^2 := by gcongr; exact hd H hH
    _ = ((2:ℝ)^rmax*D^rmax)^2*(Ideal.absNorm H:ℝ)^(δ*(rmax:ℝ)*2) := by
      have he := Real.rpow_mul_natCast hn0.le (δ*(rmax:ℝ)) 2
      norm_num only [Nat.cast_ofNat] at he
      rw [he,Real.rpow_mul_natCast hn0.le δ rmax]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hde) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1083

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CubeSlotEnergy
Source SHA256: 93e2d4789ed6fc3eae430232043f3c327a7550cd9a87d292441194159b3450f4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1084



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem original_cube_shifted_tuple_energy (rmax : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {σ κ : Type*} [Fintype σ] [DecidableEq σ]
      (H : Ideal Eis),H≠0 → ∀ (L : σ→Finset (Ideal Eis))
      (_hmax : ∀ i,∀ P∈L i,P.IsMaximal)
      (_hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
      (w : ∀ i,L i→ℂ), (∀ i P,‖w i P‖≤1) → Fintype.card σ≤rmax →
    ∀ (rows : Finset κ) (Ψ : κ→(Eis→*ℂ)) (W : ℝ→ℂ) (X E : ℝ),0≤E →
      (∀ T : Finset σ,
        (∑ k∈rows,‖∑ a : ∀ i : T,cubeAwayList H (L i.val),
          (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
            markedCompletedT (Ψ k) W X (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0)‖^2)≤E) →
      (∑ k∈rows,‖∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (Ψ k) W X
        (fun A => ∏ i,if (p i).val∣H^3*A then (1:ℂ) else 0)‖^2)≤
      C*(Ideal.absNorm H:ℝ)^ε*E := by
  obtain ⟨C,hC,hb⟩ := cubeAbsorbedCoefficient_small_power rmax ε hε
  refine ⟨C,hC,?_⟩
  intro σ κ _ _ H hH L hmax hgood w hw hr rows Ψ W X E hE he
  simp_rw [original_cube_shifted_tuple_source H L hmax hgood w]
  apply (weighted_finite_row_energy_uniform Finset.univ rows (cubeAbsorbedCoefficient H L w)
    (fun T k => ∑ a : ∀ i : T,cubeAwayList H (L i.val),
      (∏ i : T,w i.val ⟨(a i).val,(Finset.mem_filter.mp (a i).property).1⟩)*
        markedCompletedT (Ψ k) W X (fun A => ∏ i : T,if (a i).val∣A then (1:ℂ) else 0)) E
    (fun T _ => he T)).trans
  exact mul_le_mul_of_nonneg_right (hb H hH L w hw hr) hE
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1084

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.InactiveRows
Source SHA256: 930dc38ffbfb89e55066a653e1639b5dc122bf36f2913aee4661b3775ecbbd6a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1085



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def inactiveRowSet (rows : Finset (Ideal Eis)) (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (F : φ→Ideal Eis) (b : ∀ i : {i // i∉T},L i.val) : Finset (Ideal Eis) :=
  rows.filter fun K => IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠F j

lemma subtype_zero_extension_energy {κ : Type*} [DecidableEq κ]
    (rows small : Finset κ) (hs : small⊆rows) (f : small→ℂ) :
    (∑ k∈rows,‖if hk:k∈small then f ⟨k,hk⟩ else 0‖^2)=∑ k : small,‖f k‖^2 := by
  have he : (∑ k∈rows,‖if hk:k∈small then f ⟨k,hk⟩ else 0‖^2)=
      ∑ k∈small,‖if hk:k∈small then f ⟨k,hk⟩ else 0‖^2 := by
    symm
    apply Finset.sum_subset hs
    intro k hk hks
    simp only [dite_eq_right hks,norm_zero,zero_pow (by decide : (2:ℕ)≠0)]
  rw [he,←Finset.sum_coe_sort small]
  apply Finset.sum_congr rfl
  intro k hk
  rw [dite_eq_left k.property]

theorem original_inactive_restricted_energy
    (rows : Finset (Ideal Eis)) (L : σ→Finset (Ideal Eis)) (T : Finset σ)
    (F : φ→Ideal Eis) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (w : ∀ i,L i→ℂ) (hw : ∀ i P,‖w i P‖≤1)
    (f : ∀ b : ∀ i : {i // i∉T},L i.val,inactiveRowSet rows L T F b→ℂ)
    (E : ℝ) (hE : 0≤E)
    (hf : ∀ b,(∑ k : inactiveRowSet rows L T F b,‖f b k‖^2)≤E) :
    (∑ k∈rows,‖∑ b : ∀ i : {i // i∉T},L i.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
        (if hk:k∈inactiveRowSet rows L T F b then f b ⟨k,hk⟩ else 0)‖^2)≤
    (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*E := by
  let wt := fun b : ∀ i : {i // i∉T},L i.val =>
    (∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i))
  let g := fun (b : ∀ i : {i // i∉T},L i.val) k =>
    if hk:k∈inactiveRowSet rows L T F b then f b ⟨k,hk⟩ else 0
  have hg (b) : (∑ k∈rows,‖g b k‖^2)≤E := by
    rw [show (∑ k∈rows,‖g b k‖^2)=∑ k : inactiveRowSet rows L T F b,‖f b k‖^2 from
      subtype_zero_extension_energy rows _ (Finset.filter_subset _ _) (f b)]
    exact hf b
  have hm : (∑ b,‖wt b‖)≤∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ) := by
    apply (Finset.sum_le_sum (fun b hb => ?_)).trans (inactive_choices_mass_bound L T H hzero hH)
    change ‖_*_‖≤_
    rw [norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact slot_coefficient_norm (fun i : {i // i∉T} => L i.val) (fun i => w i.val) (fun i => hw i.val) b
  apply (weighted_finite_row_energy_uniform Finset.univ rows wt g E (fun b hb => hg b)).trans
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun b _ => norm_nonneg _)) hm 2) hE
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1085

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalSlotSupport
Source SHA256: c5661139f81ef3d6d08e156a23eb349d8d3f9ed04602cedfeb537f9ab87e13f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1086



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

abbrev originalSlotChoices :=
  {p : ∀ i,L i // ∀ P : FreePrimeIndex D.movingIdeal Q₀,∀ i,(p i).val≠P.val.val}

def originalSlotSupportEquiv :
    originalSlotChoices D Q₀ L ≃ supportedSlotChoices L ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) where
  toFun p := ⟨p.val,(original_slot_mask_iff D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    (slotChoiceFamily L hmax hgood p.val)).mp p.property⟩
  invFun p := ⟨p.val,(original_slot_mask_iff D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    (slotChoiceFamily L hmax hgood p.val)).mpr p.property⟩
  left_inv _p := rfl
  right_inv _p := rfl

def originalSlotSplit (T : Finset σ) : originalSlotChoices D Q₀ L ≃
    supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) ×
      supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) :=
  (originalSlotSupportEquiv D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood).trans
    (supportedSlotSplit L T ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)))

lemma originalSlotSplit_symm_val (T : Finset σ)
    (b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)))
    (a : supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F))) :
    ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)).val=
      (slotChoiceSplit L T).symm (a.val,b.val) := rfl

theorem original_supported_slot_sum (T : Finset σ)
    (w : ∀ i,L i→ℂ) (H : originalSlotChoices D Q₀ L→ℂ) :
    (∑ p : originalSlotChoices D Q₀ L,
      (∏ i∈(Finset.univ:Finset σ)\T,(Ideal.absNorm (p.val i).val:ℂ)⁻¹)*
        (∏ i,w i (p.val i))*H p)=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
      ∑ a : supportedSlotChoices (fun i : T => L i.val) ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
        (∏ i : T,w i.val (a.val i))*
        H ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)) := by
  rw [←(originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [originalSlotSplit_symm_val,slot_choice_inactive_weight,Equiv.apply_symm_apply,slot_coefficient_split]
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1086

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalChoiceControl
Source SHA256: a3d7751b87971184d09f917165cabff681f9f2fcfca9d670ddfa28bdb3ad1bc7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1087



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

lemma originalSplit_active_family (T : Finset σ) (p : originalSlotChoices D Q₀ L) :
    (slotChoiceFamily L hmax hgood p.val).restrict T=
      slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val)
        ((originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).2.val) := by
  let e := originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T
  calc
    _ = (slotChoiceFamily L hmax hgood (e.symm (e p)).val).restrict T :=
      congrArg (fun q : originalSlotChoices D Q₀ L => (slotChoiceFamily L hmax hgood q.val).restrict T) (e.symm_apply_apply p).symm
    _ = _ := by
      rw [originalSlotSplit_symm_val,slotChoiceFamily_active]

variable {τ : Type*} [Fintype τ] (Frozen : PrimeFamily τ) {N a c : Eis} {mode : Bool}
variable (T : Finset σ)
    (C : ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
        (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode)

def originalSplitControlled (p : originalSlotChoices D Q₀ L) :
    ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
      (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
      ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator N a c mode :=
  castControlled (congrArg (fun S => (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
    (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) S).generator)
    (originalSplit_active_family D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).symm)
    (C (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).1
      (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p).2)

lemma originalSplitControlled_value (p : originalSlotChoices D Q₀ L)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue
      (originalSplitControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood Frozen T C p) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X=
    let q := originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p
    mixedReflectedValue (C q.1 q.2) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X := by
  exact mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1087

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalChoicePhysical
Source SHA256: 1d0454ee6f7945d02d6bf009e7b71943e23f474f1f50e148fd45a67fa2a2ccd9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1088


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q₀ : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime Q₀ (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))

variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

variable {τ : Type*} [Fintype τ] (Frozen : PrimeFamily τ) {N a c : Eis} {mode : Bool}
variable (T : Finset σ)
    (C : ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F))
        (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode)

def originalSplitPhysical
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ)
    (q : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
      ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F)) ×
      supportedSlotChoices (fun i : T => L i.val)
      ((poolPrimeFamily R (Ideal.span {m}*F) Q₀).ideal) (rowResidualPart I (Ideal.span {m}*F))) : ℂ :=
  mixedReflectedValue (C q.1 q.2) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) q.2.val)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X
lemma originalSplitControlled_physical (p : originalSlotChoices D Q₀ L)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue
      (originalSplitControlled D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood Frozen T C p) s
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero hc
      (Frozen.reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
        ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X=
    originalSplitPhysical R I F Q₀ hbad L hmax hgood Frozen T C s hc jF W X
      (originalSlotSplit D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T p) := by
  exact originalSplitControlled_value D R I F Q₀ hR hI hF hm hf hz hbad hcop hpow hmask
    L hmax hgood Frozen T C p s hc jF W X

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1088

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.UniformNormalized
Source SHA256: b1d94294ed5ad8852de8e9f50959cbaccb05d75ea8178b1e0ce9f21ebbbdc586
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1089



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v
variable {N a c : Eis} {mode : Bool}

theorem actual_physical_shape_uniform_type_uniform
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ {φ : Type u} [Fintype φ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3) (m : ℕ)
      (T QK QP Qn Qb A C ε : ℝ), 0<T → 0<QK → 0<QP → 0<Qn → 0<Qb → 0≤C →
    let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
    let r := ramifiedScale 1 completedRamifiedStep m
    let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
    let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
    (A/(r*Real.sqrt Qn*Qb)*smallScalar R)^2*(frozenBranchScale F jF e)^2*
      (C*((kK*QK)*U*B*(kP*QP))^ε*((kK*QK)+U*B)*B*
        (U+(kP*QP)+(U*(kP*QP))^(2/3:ℝ))) ≤
    (A*Real.sqrt kn*kb)^2*(6*C)*Z^(
      InverseTerminalWidths.reflectedExponent 0 (Real.logb Z (kK*QK))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
        (Real.logb Z (kP*QP)) (Real.logb Z U) (Real.logb Z B)
        (InverseTerminalWidths.ramifiedWidth Z m)
        (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK))
          (Real.logb Z (kP*QP)) (Real.logb Z T) F.ideal jF e) +
      ε*(Real.logb Z (kK*QK)+Real.logb Z U+Real.logb Z B+Real.logb Z (kP*QP))+η/2) := by
  let Cf := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c}):ℝ)^2*kn*kb^3/(kK^2*kP^2)
  have hcn : (0:ℝ)<Ideal.absNorm (Ideal.span {c}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hc))
  have htau := sourceCuspScale_pos s.index
  have hCf : 0<Cf := by dsimp only [Cf]; positivity
  obtain ⟨Z₀,hZ₀,he⟩ := literal_threshold_error_uniform Cf η hCf hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro φ _ Z hZ F jF e m T QK QP Qn Qb A C ε hT hK hP hn hb hC
  let R := kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb
  let r := ramifiedScale 1 completedRamifiedStep m
  let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
  let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hr : 0<r := ramifiedScale_pos _ _ (by norm_num)
    (lt_trans zero_lt_one completedRamifiedStep_gt_one) _
  have hR : 0<R := by
    have hcc := actualKernelCoefficient_pos F s hc m T hT
    dsimp only [R,kernelCenter]
    positivity
  have hh := physical_scalar_hybrid_shape F jF e Z r Qn Qb kn kb R A C (kK*QK) (kP*QP) ε
    hz hr hn hb hkn hkb hR hC (mul_pos hkK hK) (mul_pos hkP hP)
  dsimp only at hh ⊢
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) hC))
  apply Real.rpow_le_rpow_of_exponent_le hz.le
  have hthreshold := actual_kernel_upper_threshold F jF e s hc m Z T QK QP Qn Qb kK kP kn kb
    hT hK hP hn hb hkK hkP hkn hkb
  have hexp := he Z hZ m 0 (Real.logb Z (kK*QK))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
    (Real.logb Z (kP*QP)) (Real.logb Z U) (Real.logb Z B)
    (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z (kK*QK)) (Real.logb Z (kP*QP))
      (Real.logb Z T) F.ideal jF e)
  change Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R = _ at hthreshold
  rw [hthreshold]
  linarith

theorem normalized_surviving_physical_source_energy_type_uniform
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ (degree : ℕ) (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
      X=kK*QK → Y=kn*Qn → B=kb*Qb → L=kP*QP →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
        ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property).1 (S P.val)).generator N a c mode)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K P hp, (D K P hp).fixedFactor=D0.fixedFactor) →
      (∀ K P hp u m n b, actualCuspColumn (D K P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      ((branches.card:ℝ)*∑ e∈branches,
        let U := Y/Ideal.absNorm (frozenExtracted F jF e 1)
        let Bb := B/Ideal.absNorm (frozenExtracted F jF e 2)
        (Real.exp (M 2/2+M 3)*Real.sqrt kn*kb)^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z L) (Real.logb Z U) (Real.logb Z Bb)
            (InverseTerminalWidths.ramifiedWidth Z m)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z X) (Real.logb Z L) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z X+Real.logb Z U+Real.logb Z Bb+Real.logb Z L)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,C₀,C,hC₀,hC,hsource⟩ := surviving_physical_source_energy_type_uniform
    (N := N) (a := a) (c := c) (mode := mode)
    ε hε a₀ b₀ ha₀ windows M hM hwindowNorm hwindows W hWsupport hW
  obtain ⟨Z₀,hZ₀,hshape⟩ := actual_physical_shape_uniform_type_uniform s hc
    kK kP kn kb η hkK hkP hkn hkb hη
  refine ⟨degree,C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ X Y B L hX hY hB hL F jF hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb hsX hsY hsB hsL
    rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  have hh := hsource X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
  let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*
    smallScalar (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb)
  dsimp only at hh ⊢
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [mul_left_comm (scalar^2) (branches.card:ℝ)]
  rw [Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨heY,heB⟩ := surviving_extracted_scales F hF jF (actualCuspColumn D0 s hc u m)
    nset bset Y B (fun n h => ⟨(hn n h).1.2,(hn n h).2⟩) hb e he
  rw [heY,heB]
  have hee := hshape Z hZ F jF e m T QK QP Qn Qb (Real.exp (M 2/2+M 3)) C ε hT hQK hQP hQn hQb hC.le
  dsimp only at hee
  rw [hsX,hsY,hsB,hsL]
  convert hee using 1 ; ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1089

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SectorNormalized
Source SHA256: 9d26113f7fe9010fcdfb82ac61da91c7068a459ec25637d48341e6cd3c92f8d5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1090



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v
variable {N a c : Eis} {mode : Bool}

theorem sector_normalized_physical_energy
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ (degree : ℕ) (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
      X=kK*QK → Y=kn*Qn → B=kb*Qb → L=kP*QP →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (E : SectorArithmetic (N:=N) F rows Pset S (fun K hK => (hrows K hK).1) s hc)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn E.referenceArithmetic s hc u m) nset bset
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (E.completion K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      ((branches.card:ℝ)*∑ e∈branches,
        let U := Y/Ideal.absNorm (frozenExtracted F jF e 1)
        let Bb := B/Ideal.absNorm (frozenExtracted F jF e 2)
        (Real.exp (M 2/2+M 3)*Real.sqrt kn*kb)^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z L) (Real.logb Z U) (Real.logb Z Bb)
            (InverseTerminalWidths.ramifiedWidth Z m)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z X) (Real.logb Z L) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z X+Real.logb Z U+Real.logb Z Bb+Real.logb Z L)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,C₀,C,Z₀,hC₀,hC,hZ₀,hsource⟩ := normalized_surviving_physical_source_energy_type_uniform
    (N:=N) (a:=a) (c:=c) (mode:=mode) ε hε a₀ b₀ ha₀ windows M hM hwindowNorm hwindows
    W hWsupport hW s hc kK kP kn kb η hkK hkP hkn hkb hη
  refine ⟨degree,C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ X Y B L hX hY hB hL F jF hN hbase hac hF hNF hcharF hj
    u m T θ QK QP Qn Qb hT hQK hQP hQn hQb hsX hsY hsB hsL
    rows nset bset Pset S hrows E r₀ aw₀ w₀ hrowcop hproducts hScop hSN hSchar hn hb hP hr₀ haw₀ hw₀
  exact hsource Z hZ X Y B L hX hY hB hL F jF hN hbase hac hF hNF hcharF hj
    E.referencePrimes E.referenceArithmetic u m T θ QK QP Qn Qb hT hQK hQP hQn hQb hsX hsY hsB hsL
    rows nset bset Pset S hrows E.completion r₀ aw₀ w₀ hrowcop hproducts hScop hSN hSchar hn hb hP
    E.fixedFactor_eq E.cuspColumn_eq hr₀ haw₀ hw₀
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1090

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LiteralNormalized
Source SHA256: eacf521bded18bea14e12b805e5d7efcbfce79be95398602f4cd5d99afb1acb9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1091



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v
variable {N a c : Eis} {mode : Bool}

theorem sector_normalized_literal_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (η : ℝ) (hη : 0<η) :
    ∃ (degree : ℕ) (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c∣N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f,jF f<6) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=N) F rows Pset S hrows s hc),
      (∀ K∈rows,(∀ f,IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ j,IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal j)) →
      (∀ P∈Pset,∀ j,ringChar (Eis⧸(F.sum (S P)).ideal j)≠2) →
    ∀ (u : Eisˣ) (i : ℕ×ℕ×ℕ) (T θ QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<T → 1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn E.referenceArithmetic s hc u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      (∑ K : rows,‖literalDyadicRow F K.val (hrows K.val K.property) S jF Pset
        (E.completion K) s hc u i W θ T r aw‖^2)≤
      ((branches.card:ℝ)*∑ e∈branches,
        (Real.exp (Real.log 2/2+Real.log 2))^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z QK)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z (QP/2))
            (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1)))
            (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2)))
            (InverseTerminalWidths.ramifiedWidth Z i.1)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z QK) (Real.logb Z (QP/2)) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z QK+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))+Real.logb Z (QP/2))+η/2))*
        (C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,C₀,C,Z₀,hC₀,hC,hZ₀,henergy⟩ := sector_normalized_physical_energy
    (N:=N) (a:=a) (c:=c) (mode:=mode) ε hε lo hi hlo
    (fun _ => completedShellWindow) (fun _ => Real.log 2)
    (fun _ => Real.log_nonneg (by norm_num)) (fun _ => completedShellWindow_norm)
    (fun _ => completedShellWindow_support) W hWs hW s hc 1 (1/2) 1 1 η
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hη
  refine ⟨degree,C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ F jF hN hbase hac hF hNF hcharF hj rows Pset S hrows E
    hrowcop hprod hScop hSN hSchar u i T θ QK QP r aw hT hQK hQP hKr hPr hr haw
  have hkp : 0<QK := lt_of_lt_of_le zero_lt_one hQK
  have hpp : 0<QP := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hQP
  have hp : ∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*(QP/2) := by
    intro P hP
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using hPr P hP
  have hh := henergy Z hZ QK ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) (QP/2)
    hQK (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) (by linarith)
    F jF hN hbase hac hF hNF hcharF hj u i.1 T θ QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
    hT hkp hpp (by positivity) (by positivity) (by ring) (by ring) (by ring) (by ring)
    rows (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) Pset S
    (fun K hK => ⟨hrows K hK,(hKr K hK).2⟩) E r aw (fun _ _ => 1)
    hrowcop hprod hScop hSN hSchar
    (fun n hn => ⟨(reflectedNDyad_bounds _ n hn).1,(reflectedNDyad_bounds _ n hn).2.2⟩)
    (fun b hb => ⟨(reflectedBDyad_bounds _ b hb).1,(reflectedBDyad_bounds _ b hb).2.2⟩)
    hp hr haw (fun _ _ => by simp)
  dsimp only at hh ⊢
  have he : (∑ K : rows,‖literalDyadicRow F K.val (hrows K.val K.property) S jF Pset
      (E.completion K) s hc u i W θ T r aw‖^2)=
      ∑ K : rows,‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property) S jF Pset
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) (E.completion K) s hc u i.1
        (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ T r aw (fun _ _ => 1)‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    rw [literalDyadicRow_eq_physical F K.val (hrows K.val K.property) S jF Pset
      (E.completion K) s hc u i QK QP hkp hpp (hKr K.val K.property) hprod
      (fun P hP => (hPr P hP).2) W θ T r aw]
  rw [he]
  simpa only [Real.sqrt_one,mul_one] using hh
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1091

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowSector
Source SHA256: f2e33ab2c7627f3d8c59ff129b0eda04cf8d509f420e3d548fc94ce1bf51e7bf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1092



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_sector_literal_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (u : Eisˣ) (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalDyadicRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^((5/6-2*d)+200*η+π-O₀/2) := by
  obtain ⟨degree,C₀,Cs,Zs,hC₀,hCs,hZs,henergy⟩ := sector_normalized_literal_energy
    (N:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ η hηpos
  obtain ⟨Zb,Cb,hZb,hCb,hbranch⟩ := original_surviving_low_energy_sum s hc₀ ρ hρ 1 (1/2) η
    (by norm_num) (by norm_num) hηpos
  let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
  have hKc : 0<Kc := by dsimp [Kc];positivity
  refine ⟨degree*2,Kc*Cb*C₀^2+1,max Zs Zb,by positivity,lt_of_lt_of_le hZs (le_max_left _ _),?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP Lscale Lrow Lslot i
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar u θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZs ((le_max_left _ _).trans hZ))
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
  have hs := henergy Z ((le_max_left _ _).trans hZ) G j hNlevel hbase hac hpair hGN hGchar hj
    rows Pset S hrows E hrowcop hprod hScop hSN hSchar u i X θ QK QP r aw hX hqk hqp hKr hPr hr haw
  have hb := hbranch J I F Q Q₀ hJ hI hQ hpower hmask A (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP ε Lscale Lrow Lslot i
    ((le_max_right _ _).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift hNs
    (by simpa only [one_mul] using heH) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using heza)
    heN hδ hδη hε.le
    (by simpa only [one_mul] using hrowcap) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hslotcap)
    hconst hbudget hscap hret
  dsimp only at hs hb
  rw [←heH,←heza,←heN] at hs
  simp_rw [←Finset.mul_sum] at hs
  apply hs.trans
  calc
    _ = Kc*((survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)).card*
      ∑ e∈survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1),
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by dsimp [Kc,G,j];ring
    _ ≤ Kc*(Cb*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^((5/6-2*d)+200*η+π-O₀/2))*(C₀*(1+‖θ‖)^degree)^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKc.le) (sq_nonneg _)
    _ = (Kc*Cb*C₀^2)*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^((5/6-2*d)+200*η+π-O₀/2) := by rw [mul_pow,←pow_mul];ring
    _ ≤ _ := by gcongr;linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1092

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowRetained
Source SHA256: b3f20434fcc87452fa309242939476dddff72e2c79aba07f5657513df5939fb4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1093



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_sector_retained_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP Lscale Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*((retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)).card:ℝ)^2*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^((5/6-2*d)+200*η+π-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_sector_literal_energy
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
  refine ⟨degree,36*C,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let Dset := retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)
  let src := fun (ui : Eisˣ×(ℕ×ℕ×ℕ)) (K : rows) =>
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ ui.1 ui.2 W θ X r aw
  have hb (ui : Eisˣ×(ℕ×ℕ×ℕ)) (hui : ui∈(Finset.univ:Finset Eisˣ)×ˢDset) :=
    henergy J I F Q Q₀ hJ hI hQ hpower hmask A
      Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP Lscale Lrow Lslot ui.2
      hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
      hNs heH heza heN hδ hδη hrowcap hslotcap hconst hbudget hscap
      (Finset.mem_product.mp hui).2 rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
      ui.1 θ r aw hqk hqp hKr hPr hr haw
  have hh := weighted_finite_row_energy_uniform ((Finset.univ:Finset Eisˣ)×ˢDset) (Finset.univ:Finset rows)
    (fun _ => (1:ℂ)) src _ hb
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  simp only [src,one_mul,norm_one,Finset.sum_const,nsmul_eq_mul,mul_one,
    Finset.card_product,Finset.card_univ,hcard,Finset.sum_product,tsum_fintype] at hh ⊢
  apply hh.trans_eq
  push_cast
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1093

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowRetainedBudget
Source SHA256: 3e1ae97732f7abcda593c77e2042c0fc9de68bad7a90a680f75a1bb26fb6a6be
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1094



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_sector_retained_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤Lpool) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_sector_retained_energy
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨degree,C*Cd,Z₀,mul_pos hC hCd,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have hs := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift δ π Ck CO CH X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have hd := hcount Z (familyRawScale G s X QK QP) hz'.le hscap
  have hp : (Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ≤Z^(Lpool*ρ) := by
    rw [Real.rpow_mul hzpos.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpool hρ.le
  apply hs.trans
  calc
    _ ≤ C*(Cd*Z^κ)*(1+‖θ‖)^degree*Z^(Lpool*ρ)*Z^((5/6-2*d)+200*η+π-O₀/2) := by gcongr
    _ = (C*Cd)*(1+‖θ‖)^degree*Z^(κ+Lpool*ρ+((5/6-2*d)+200*η+π-O₀/2)) := by
      rw [Real.rpow_add hzpos,Real.rpow_add hzpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz'.le (by nlinarith)) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1094

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalSector
Source SHA256: 2658bf9a8caf3ad083cb84b799b1dd5906df5faad6b9fff52481975c75fd8f29
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1095



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_literal_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (u : Eisˣ) (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalDyadicRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨degree,C₀,Cs,Zs,hC₀,hCs,hZs,henergy⟩ := sector_normalized_literal_energy
    (N:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ η hηpos
  obtain ⟨Zb,Cb,hZb,hCb,hbranch⟩ := original_surviving_energy_sum s hc₀ ρ hρ 1 (1/2) η
    (by norm_num) (by norm_num) hηpos
  let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
  have hKc : 0<Kc := by dsimp [Kc];positivity
  refine ⟨degree*2,Kc*Cb*C₀^2+1,max Zs Zb,by positivity,lt_of_lt_of_le hZs (le_max_left _ _),?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar u θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZs ((le_max_left _ _).trans hZ))
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A
  have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
  have hs := henergy Z ((le_max_left _ _).trans hZ) G j hNlevel hbase hac hpair hGN hGchar hj
    rows Pset S hrows E hrowcop hprod hScop hSN hSchar u i X θ QK QP r aw hX hqk hqp hKr hPr hr haw
  have hb := hbranch J I F B R Q₀ hJ hI hF hB hR hpower hmask A (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    ((le_max_right _ _).trans hZ) hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    (by simpa only [one_mul] using heH) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using heza)
    heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε.le
    (by simpa only [one_mul] using hrowcap) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hslotcap)
    hconst hbudget hscap hret
  dsimp only at hs hb
  rw [←heH,←heza,←heN] at hs
  simp_rw [←Finset.mul_sum] at hs
  apply hs.trans
  calc
    _ = Kc*((survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)).card*
      ∑ e∈survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1),
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by dsimp [Kc,G,j];ring
    _ ≤ Kc*(Cb*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2))*(C₀*(1+‖θ‖)^degree)^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKc.le) (sq_nonneg _)
    _ = (Kc*Cb*C₀^2)*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by rw [mul_pow,←pow_mul];ring
    _ ≤ _ := by gcongr;linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1095

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalRetained
Source SHA256: a3a5739231322f96c9a17077a4aed0559fcff57c7c679569c2c5d944d1793c0e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1096



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_retained_energy
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*((retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)).card:ℝ)^2*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_sector_literal_energy
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
  refine ⟨degree,36*C,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let Dset := retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)
  let src := fun (ui : Eisˣ×(ℕ×ℕ×ℕ)) (K : rows) =>
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ ui.1 ui.2 W θ X r aw
  have hb (ui : Eisˣ×(ℕ×ℕ×ℕ)) (hui : ui∈(Finset.univ:Finset Eisˣ)×ˢDset) :=
    henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
      Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot ui.2
      hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
      heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
      (Finset.mem_product.mp hui).2 rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
      ui.1 θ r aw hqk hqp hKr hPr hr haw
  have hh := weighted_finite_row_energy_uniform ((Finset.univ:Finset Eisˣ)×ˢDset) (Finset.univ:Finset rows)
    (fun _ => (1:ℂ)) src _ hb
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  simp only [src,one_mul,norm_one,Finset.sum_const,nsmul_eq_mul,mul_one,
    Finset.card_product,Finset.card_univ,hcard,Finset.sum_product,tsum_fintype] at hh ⊢
  apply hh.trans_eq
  push_cast
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1096

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.RetainedBudget
Source SHA256: 5e9f966619e8254ce71eafe0b04eb49164ee00d3df8afcad286f1f25887b4bc5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1097



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_retained_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤Lpool) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_sector_retained_energy
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨degree,C*Cd,Z₀,mul_pos hC hCd,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have hs := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have hd := hcount Z (familyRawScale G s X QK QP) hz'.le hscap
  have hp : (Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ≤Z^(Lpool*ρ) := by
    rw [Real.rpow_mul hzpos.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpool hρ.le
  apply hs.trans
  calc
    _ ≤ C*(Cd*Z^κ)*(1+‖θ‖)^degree*Z^(Lpool*ρ)*Z^(F₀-cstar/4-O₀/2) := by gcongr
    _ = (C*Cd)*(1+‖θ‖)^degree*Z^(κ+Lpool*ρ+(F₀-cstar/4-O₀/2)) := by
      rw [Real.rpow_add hzpos,Real.rpow_add hzpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz'.le (by nlinarith only [hsmall])) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1097

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.UniformNormalizedUniformDegree
Source SHA256: ea151529b3e69ad3b7c8fb226414c975a42146f8fc496586df7b19589358ff4a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1098



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v

theorem normalized_surviving_physical_source_energy_type_uniform_uniform_degree
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ (degree : ℕ), ∀ {N a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
    ∃ (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
      X=kK*QK → Y=kn*Qn → B=kb*Qb → L=kP*QP →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (D : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
        ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property).1 (S P.val)).generator N a c mode)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K P hp, (D K P hp).fixedFactor=D0.fixedFactor) →
      (∀ K P hp u m n b, actualCuspColumn (D K P hp) s hc u m n b=actualCuspColumn D0 s hc u m n b) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (D K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      ((branches.card:ℝ)*∑ e∈branches,
        let U := Y/Ideal.absNorm (frozenExtracted F jF e 1)
        let Bb := B/Ideal.absNorm (frozenExtracted F jF e 2)
        (Real.exp (M 2/2+M 3)*Real.sqrt kn*kb)^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z L) (Real.logb Z U) (Real.logb Z Bb)
            (InverseTerminalWidths.ramifiedWidth Z m)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z X) (Real.logb Z L) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z X+Real.logb Z U+Real.logb Z Bb+Real.logb Z L)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,huniform⟩ := surviving_physical_source_energy_type_uniform_uniform_degree
    ε hε a₀ b₀ ha₀ windows M hM hwindowNorm hwindows W hWsupport hW
  refine ⟨degree,?_⟩
  intro N a c mode s hc
  obtain ⟨C₀,C,hC₀,hC,hsource⟩ := huniform (N:=N) (a:=a) (c:=c) (mode:=mode)
  obtain ⟨Z₀,hZ₀,hshape⟩ := actual_physical_shape_uniform_type_uniform s hc
    kK kP kn kb η hkK hkP hkn hkb hη
  refine ⟨C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ X Y B L hX hY hB hL F jF hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb hsX hsY hsB hsL
    rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  have hh := hsource X Y B L hX hY hB hL F jF s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m T θ QK QP Qn Qb hT hQK hQP hQn hQb rows nset bset Pset S hrows D r₀ aw₀ w₀
    hrowcop hproducts hScop hSN hSchar hn hb hP hκ hA hr₀ haw₀ hw₀
  let branches := survivingFrozenBranches F jF (actualCuspColumn D0 s hc u m) nset bset
  let scalar := Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*
    smallScalar (kernelCenter (actualKernelCoefficient F s m T) QK QP Qn Qb)
  dsimp only at hh ⊢
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  rw [mul_left_comm (scalar^2) (branches.card:ℝ)]
  rw [Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨heY,heB⟩ := surviving_extracted_scales F hF jF (actualCuspColumn D0 s hc u m)
    nset bset Y B (fun n h => ⟨(hn n h).1.2,(hn n h).2⟩) hb e he
  rw [heY,heB]
  have hee := hshape Z hZ F jF e m T QK QP Qn Qb (Real.exp (M 2/2+M 3)) C ε hT hQK hQP hQn hQb hC.le
  dsimp only at hee
  rw [hsX,hsY,hsB,hsL]
  convert hee using 1 ; ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1098

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SectorNormalizedUniformDegree
Source SHA256: 6860292f318fa610672d892f825c05a8df28c17dfad5324d5d10c97b7afbb1c1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1099



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform CompletedDyadic
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v

theorem sector_normalized_physical_energy_uniform_degree
    (ε : ℝ) (hε : 0<ε) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindowNorm : ∀ i y, ‖windows i y‖≤1)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (kK kP kn kb η : ℝ) (hkK : 0<kK) (hkP : 0<kP) (hkn : 0<kn) (hkb : 0<kb) (hη : 0<η) :
    ∃ (degree : ℕ), ∀ {N a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
    ∃ (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (X Y B L : ℝ), 1≤X → 1≤Y → 1≤B → 1≤L →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c ∣ N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f, jF f<6) →
    ∀ (u : Eisˣ) (m : ℕ) (T θ QK QP Qn Qb : ℝ),
      0<T → 0<QK → 0<QP → 0<Qn → 0<Qb →
      X=kK*QK → Y=kn*Qn → B=kb*Qb → L=kP*QP →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ)≤X)
      (E : SectorArithmetic (N:=N) F rows Pset S (fun K hK => (hrows K hK).1) s hc)
      (r₀ aw₀ : Ideal Eis→ℂ) (w₀ : Ideal Eis→Ideal Eis→ℂ),
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i)=P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis⧸(F.sum (S P)).ideal i)≠2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ)≤Y) →
      (∀ b ∈ bset, primaryGenerator b≠0 ∧ (Ideal.absNorm b:ℝ)≤B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*L) →
      (∀ K ∈ rows, ‖r₀ K‖≤1) → (∀ P ∈ Pset, ‖aw₀ P‖≤1) → (∀ n b, ‖w₀ n b‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn E.referenceArithmetic s hc u m) nset bset
      (∑ K : rows, ‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property).1 S jF Pset nset bset
        (E.completion K) s hc u m windows QK QP Qn Qb W θ T r₀ aw₀ w₀‖^2) ≤
      ((branches.card:ℝ)*∑ e∈branches,
        let U := Y/Ideal.absNorm (frozenExtracted F jF e 1)
        let Bb := B/Ideal.absNorm (frozenExtracted F jF e 2)
        (Real.exp (M 2/2+M 3)*Real.sqrt kn*kb)^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z L) (Real.logb Z U) (Real.logb Z Bb)
            (InverseTerminalWidths.ramifiedWidth Z m)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z X) (Real.logb Z L) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z X+Real.logb Z U+Real.logb Z Bb+Real.logb Z L)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,huniform⟩ := normalized_surviving_physical_source_energy_type_uniform_uniform_degree
    ε hε a₀ b₀ ha₀ windows M hM hwindowNorm hwindows
    W hWsupport hW kK kP kn kb η hkK hkP hkn hkb hη
  refine ⟨degree,?_⟩
  intro N a c mode s hc
  obtain ⟨C₀,C,Z₀,hC₀,hC,hZ₀,hsource⟩ := huniform (N:=N) (a:=a) (c:=c) (mode:=mode) s hc
  refine ⟨C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ X Y B L hX hY hB hL F jF hN hbase hac hF hNF hcharF hj
    u m T θ QK QP Qn Qb hT hQK hQP hQn hQb hsX hsY hsB hsL
    rows nset bset Pset S hrows E r₀ aw₀ w₀ hrowcop hproducts hScop hSN hSchar hn hb hP hr₀ haw₀ hw₀
  exact hsource Z hZ X Y B L hX hY hB hL F jF hN hbase hac hF hNF hcharF hj
    E.referencePrimes E.referenceArithmetic u m T θ QK QP Qn Qb hT hQK hQP hQn hQb hsX hsY hsB hsL
    rows nset bset Pset S hrows E.completion r₀ aw₀ w₀ hrowcop hproducts hScop hSN hSchar hn hb hP
    E.fixedFactor_eq E.cuspColumn_eq hr₀ haw₀ hw₀
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1099

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LiteralNormalizedUniformDegree
Source SHA256: 79d44474f7c29bf2da825a317836cf50ee732445f5595fcef955f320aa676241
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1100



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
universe u v

theorem sector_normalized_literal_energy_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (η : ℝ) (hη : 0<η) :
    ∃ (degree : ℕ), ∀ {N a c : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
    ∃ (C₀ C Z₀ : ℝ), 0≤C₀ ∧ 0<C ∧ 1<Z₀ ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ], ∀ Z : ℝ, Z₀≤Z →
    ∀ (F : PrimeFamily φ) (jF : φ→ℕ),
      (9:Eis)*c∣N → (if mode then λ₀^2∣a-1 else λ₀^2∣c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis⧸F.ideal f)≠2) → (∀ f,jF f<6) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=N) F rows Pset S hrows s hc),
      (∀ K∈rows,(∀ f,IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ j,IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal j)) →
      (∀ P∈Pset,∀ j,ringChar (Eis⧸(F.sum (S P)).ideal j)≠2) →
    ∀ (u : Eisˣ) (i : ℕ×ℕ×ℕ) (T θ QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<T → 1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      let branches := survivingFrozenBranches F jF (actualCuspColumn E.referenceArithmetic s hc u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)
      (∑ K : rows,‖literalDyadicRow F K.val (hrows K.val K.property) S jF Pset
        (E.completion K) s hc u i W θ T r aw‖^2)≤
      ((branches.card:ℝ)*∑ e∈branches,
        (Real.exp (Real.log 2/2+Real.log 2))^2*(6*C)*Z^(
          InverseTerminalWidths.reflectedExponent 0 (Real.logb Z QK)
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
            (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
            (Real.logb Z (QP/2))
            (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1)))
            (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2)))
            (InverseTerminalWidths.ramifiedWidth Z i.1)
            (InverseTerminalWidths.terminalDualWidth Z (Real.logb Z QK) (Real.logb Z (QP/2)) (Real.logb Z T) F.ideal jF e)+
          ε*(Real.logb Z QK+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted F jF e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted F jF e 2))+Real.logb Z (QP/2))+η/2))*
        (C₀*(1+‖θ‖)^degree)^2 := by
  obtain ⟨degree,huniform⟩ := sector_normalized_physical_energy_uniform_degree
    ε hε lo hi hlo
    (fun _ => completedShellWindow) (fun _ => Real.log 2)
    (fun _ => Real.log_nonneg (by norm_num)) (fun _ => completedShellWindow_norm)
    (fun _ => completedShellWindow_support) W hWs hW 1 (1/2) 1 1 η
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hη
  refine ⟨degree,?_⟩
  intro N a c mode s hc
  obtain ⟨C₀,C,Z₀,hC₀,hC,hZ₀,henergy⟩ := huniform (N:=N) (a:=a) (c:=c) (mode:=mode) s hc
  refine ⟨C₀,C,Z₀,hC₀,hC,hZ₀,?_⟩
  intro φ σ _ _ Z hZ F jF hN hbase hac hF hNF hcharF hj rows Pset S hrows E
    hrowcop hprod hScop hSN hSchar u i T θ QK QP r aw hT hQK hQP hKr hPr hr haw
  have hkp : 0<QK := lt_of_lt_of_le zero_lt_one hQK
  have hpp : 0<QP := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hQP
  have hp : ∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤2*(QP/2) := by
    intro P hP
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using hPr P hP
  have hh := henergy Z hZ QK ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) (QP/2)
    hQK (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) (by linarith)
    F jF hN hbase hac hF hNF hcharF hj u i.1 T θ QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
    hT hkp hpp (by positivity) (by positivity) (by ring) (by ring) (by ring) (by ring)
    rows (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) Pset S
    (fun K hK => ⟨hrows K hK,(hKr K hK).2⟩) E r aw (fun _ _ => 1)
    hrowcop hprod hScop hSN hSchar
    (fun n hn => ⟨(reflectedNDyad_bounds _ n hn).1,(reflectedNDyad_bounds _ n hn).2.2⟩)
    (fun b hb => ⟨(reflectedBDyad_bounds _ b hb).1,(reflectedBDyad_bounds _ b hb).2.2⟩)
    hp hr haw (fun _ _ => by simp)
  dsimp only at hh ⊢
  have he : (∑ K : rows,‖literalDyadicRow F K.val (hrows K.val K.property) S jF Pset
      (E.completion K) s hc u i W θ T r aw‖^2)=
      ∑ K : rows,‖weightedFinitePhysicalKernelRow F K.val (hrows K.val K.property) S jF Pset
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1) (E.completion K) s hc u i.1
        (fun _ => completedShellWindow) QK QP ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1) W θ T r aw (fun _ _ => 1)‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    rw [literalDyadicRow_eq_physical F K.val (hrows K.val K.property) S jF Pset
      (E.completion K) s hc u i QK QP hkp hpp (hKr K.val K.property) hprod
      (fun P hP => (hPr P hP).2) W θ T r aw]
  rw [he]
  simpa only [Real.sqrt_one,mul_one] using hh
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1100

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalSectorUniformDegree
Source SHA256: e4929e09d57d0669c89fe739525402d1d7cb5e90fb529762e0ff7fe5c6451a9c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1101



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem original_sector_literal_energy_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ), ∀ {Nlevel a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (_hNlevel : (9:Eis)*c₀∣Nlevel)
    (_hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (_hac : IsCoprime a c₀),
    ∃ (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot : ℝ)
      (i : ℕ×ℕ×ℕ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ) →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (u : Eisˣ) (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalDyadicRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨degree,huniform⟩ := sector_normalized_literal_energy_uniform_degree ε hε lo hi hlo W hWs hW η hηpos
  refine ⟨degree*2,?_⟩
  intro Nlevel a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨C₀,Cs,Zs,hC₀,hCs,hZs,henergy⟩ := huniform (N:=Nlevel) (a:=a) (c:=c₀) (mode:=mode) s hc₀
  obtain ⟨Zb,Cb,hZb,hCb,hbranch⟩ := original_surviving_energy_sum s hc₀ ρ hρ 1 (1/2) η
    (by norm_num) (by norm_num) hηpos
  let Kc := (Real.exp (Real.log 2/2+Real.log 2))^2*(6*Cs)
  have hKc : 0<Kc := by dsimp [Kc];positivity
  refine ⟨Kc*Cb*C₀^2+1,max Zs Zb,by positivity,lt_of_lt_of_le hZs (le_max_left _ _),?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot i
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hret rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar u θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZs ((le_max_left _ _).trans hZ))
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A
  have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
  have hs := henergy Z ((le_max_left _ _).trans hZ) G j hNlevel hbase hac hpair hGN hGchar hj
    rows Pset S hrows E hrowcop hprod hScop hSN hSchar u i X θ QK QP r aw hX hqk hqp hKr hPr hr haw
  have hb := hbranch J I F B R Q₀ hJ hI hF hB hR hpower hmask A (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP ε Lscale Lrow Lslot i
    ((le_max_right _ _).trans hZ) hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    (by simpa only [one_mul] using heH) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using heza)
    heN hM hO hz hzcap hc hmargin hd hη hτ hπ hε.le
    (by simpa only [one_mul] using hrowcap) (by simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hslotcap)
    hconst hbudget hscap hret
  dsimp only at hs hb
  rw [←heH,←heza,←heN] at hs
  simp_rw [←Finset.mul_sum] at hs
  apply hs.trans
  calc
    _ = Kc*((survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1)).card*
      ∑ e∈survivingFrozenBranches G j (actualCuspColumn E.referenceArithmetic s hc₀ u i.1)
        (reflectedNDyad i.2.2) (reflectedBDyad i.2.1),
        Z^(InverseTerminalWidths.reflectedExponent 0 H (normWidth Z (frozenExtracted G j e 0))
          (normWidth Z (frozenExtracted G j e 2)) za
          (Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1)))
          (Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2)))
          (ramifiedWidth Z i.1) (terminalDualWidth Z H za Nstar G.ideal j e)+
          ε*(H+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm (frozenExtracted G j e 1))+
            Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm (frozenExtracted G j e 2))+za)+η/2))*(C₀*(1+‖θ‖)^degree)^2 := by dsimp [Kc,G,j];ring
    _ ≤ Kc*(Cb*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2))*(C₀*(1+‖θ‖)^degree)^2 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hKc.le) (sq_nonneg _)
    _ = (Kc*Cb*C₀^2)*(1+‖θ‖)^(degree*2)*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by rw [mul_pow,←pow_mul];ring
    _ ≤ _ := by gcongr;linarith
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1101

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalRetainedUniformDegree
Source SHA256: 623d9ab1038a2dc38e14a212432777e82d1af3a5f4a3c41cb13ee5e05bfa0ea9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1102



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem original_sector_retained_energy_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η) :
    ∃ (degree : ℕ), ∀ {Nlevel a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (_hNlevel : (9:Eis)*c₀∣Nlevel)
    (_hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (_hac : IsCoprime a c₀),
    ∃ (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*((retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)).card:ℝ)^2*(1+‖θ‖)^degree*(Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ*Z^(F₀-cstar/4-O₀/2) := by
  obtain ⟨degree,huniform⟩ := original_sector_literal_energy_uniform_degree ε hε lo hi hlo W hWs hW ρ hρ η hηpos
  refine ⟨degree,?_⟩
  intro Nlevel a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩ := huniform (Nlevel:=Nlevel) (a:=a) (c₀:=c₀) (mode:=mode) s hc₀ hNlevel hbase hac
  refine ⟨36*C,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let Dset := retainedDyads (familyRawScale G s X QK QP) (16*Z^δ)
  let src := fun (ui : Eisˣ×(ℕ×ℕ×ℕ)) (K : rows) =>
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ ui.1 ui.2 W θ X r aw
  have hb (ui : Eisˣ×(ℕ×ℕ×ℕ)) (hui : ui∈(Finset.univ:Finset Eisˣ)×ˢDset) :=
    henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
      Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot ui.2
      hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
      heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
      (Finset.mem_product.mp hui).2 rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar
      ui.1 θ r aw hqk hqp hKr hPr hr haw
  have hh := weighted_finite_row_energy_uniform ((Finset.univ:Finset Eisˣ)×ˢDset) (Finset.univ:Finset rows)
    (fun _ => (1:ℂ)) src _ hb
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  simp only [src,one_mul,norm_one,Finset.sum_const,nsmul_eq_mul,mul_one,
    Finset.card_product,Finset.card_univ,hcard,Finset.sum_product,tsum_fintype] at hh ⊢
  apply hh.trans_eq
  push_cast
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1102

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.RetainedBudgetUniformDegree
Source SHA256: 003d5264d77d87c6c5ac768d7c99704584708572781a987b20aa62fc38f1f058
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1103



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem original_sector_retained_budget_uniform_degree
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (_hLpool : 0≤Lpool) :
    ∃ (degree : ℕ), ∀ {Nlevel a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (_hNlevel : (9:Eis)*c₀∣Nlevel)
    (_hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (_hac : IsCoprime a c₀),
    ∃ (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
        literalDyadicRow G K.val (hrows K.val K.property) S j Pset
          (E.completion K) s hc₀ u i W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨degree,huniform⟩ := original_sector_retained_energy_uniform_degree ε hε lo hi hlo W hWs hW ρ hρ η hηpos
  refine ⟨degree,?_⟩
  intro Nlevel a c₀ mode s hc₀ hNlevel hbase hac
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩ := huniform (Nlevel:=Nlevel) (a:=a) (c₀:=c₀) (mode:=mode) s hc₀ hNlevel hbase hac
  obtain ⟨Cd,hCd,hcount⟩ := retained_count_budget κ δ Lscale hκ hδL
  refine ⟨C*Cd,Z₀,mul_pos hC hCd,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have hs := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d δ π Ck CO CH Cf X QK QP Lscale Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have hd := hcount Z (familyRawScale G s X QK QP) hz'.le hscap
  have hp : (Ideal.absNorm (∏ b,G.ideal b):ℝ)^ρ≤Z^(Lpool*ρ) := by
    rw [Real.rpow_mul hzpos.le]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hpool hρ.le
  apply hs.trans
  calc
    _ ≤ C*(Cd*Z^κ)*(1+‖θ‖)^degree*Z^(Lpool*ρ)*Z^(F₀-cstar/4-O₀/2) := by gcongr
    _ = (C*Cd)*(1+‖θ‖)^degree*Z^(κ+Lpool*ρ+(F₀-cstar/4-O₀/2)) := by
      rw [Real.rpow_add hzpos,Real.rpow_add hzpos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz'.le (by nlinarith only [hsmall])) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1103

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.WholeRow
Source SHA256: 17a8523f814f48db5cd40a09ddb553a99ecd2d3416f22d1c55a4d04a29a9d0f1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1104



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def literalWholeRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) : ℂ :=
  ∑ P : {P : Pset // IsCoprime K P.val}, r K*aw P.val.val*
    mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
      (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X

lemma sum_tsum_tsum_finite_middle {α β γ : Type*} [Fintype β]
    (L : Finset α) (f : α→β→γ→ℂ) (hf : ∀ p∈L, ∀ u, Summable (f p u)) :
    (∑ p∈L,∑' u,∑' i,f p u i)=∑' u,∑' i,∑ p∈L,f p u i := by
  simp only [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact (Summable.tsum_finsetSum (fun p hp => hf p hp u)).symm

theorem literalWholeRow_eq_dyadic (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hchar : ∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2)
    (hj : ∀ i,jF i<6) (hprod : ∀ P∈Pset,(∏ j,(S P).ideal j)=P)
    (W : ℝ→ℂ) (lo hi : ℝ) (hlo : 0<lo) (hWs : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (θ X : ℝ) (hX : 0<X) (r aw : Ideal Eis→ℂ) :
    literalWholeRow F K hK S jF Pset D s hc W θ X r aw=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X
            (fun K => r K*shapeArgument (primaryGenerator K))
            (fun P => aw P*shapeArgument (primaryGenerator P)) := by
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hts := (CompletedHeight.normTwistedSource_support W θ).trans hWs
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) u i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let wt := fun P : L => (r K*shapeArgument (primaryGenerator K))*(aw P.val.val*shapeArgument (primaryGenerator P.val.val))
  have hs (P : L) (u : Eisˣ) : Summable (fun i => wt P*block P u i) :=
    (literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX u).mul_left _
  have hp (P : L) : r K*aw P.val.val*
      mixedReflectedValue (D P.val P.property) s (F.reflected K hK (S P.val.val)).generator_ne_zero hc
        (F.reflected K hK (S P.val.val)).generator_good (reflectedExponent jF)
        (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X=
      (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
        ∑' u : Eisˣ,∑' i : ℕ×ℕ×ℕ,wt P*block P u i := by
    rw [mixedReflectedValue_eq_dyadic (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo hts htw X hX,
      actual_shape_separation,hprod P.val.val P.val.property]
    simp only [tsum_mul_left]
    dsimp only [wt,block]
    ring
  unfold literalWholeRow
  simp_rw [hp]
  rw [←Finset.mul_sum,sum_tsum_tsum_finite_middle Finset.univ (fun P u i => wt P*block P u i) (fun P _ u => hs P u)]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1104

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.RowTail
Source SHA256: b676e4bcf7efd83358f4d06cba5cbc96aa4b4e0e4d656b00db7a43611f37db31
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1105



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma finite_weighted_truncation {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (w : α→ℂ) (J : Finset β)
    (hf : ∀ p, Summable (f p)) :
    (∑' i,∑ p,w p*f p i)-(∑ i∈J,∑ p,w p*f p i)=
      ∑ p,w p*((∑' i,f p i)-∑ i∈J,f p i) := by
  rw [Summable.tsum_finsetSum (fun p _ => (hf p).mul_left (w p)),Finset.sum_comm]
  simp only [tsum_mul_left,←Finset.mul_sum,mul_sub,Finset.sum_sub_distrib]

lemma finite_weighted_truncation_norm {α β : Type*} [Fintype α]
    (f : α→β→ℂ) (w : α→ℂ) (J : Finset β) (E : ℝ)
    (hf : ∀ p, Summable (f p)) (hw : ∀ p,‖w p‖≤1)
    (he : ∀ p, ‖(∑' i,f p i)-∑ i∈J,f p i‖≤E) :
    ‖(∑' i,∑ p,w p*f p i)-(∑ i∈J,∑ p,w p*f p i)‖≤Fintype.card α*E := by
  rw [finite_weighted_truncation f w J hf]
  calc
    _ ≤ ∑ p,‖w p*((∑' i,f p i)-∑ i∈J,f p i)‖ := norm_sum_le _ _
    _ ≤ ∑ _p : α,E := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw p) (norm_nonneg _)).trans (by simpa using he p)
    _ = _ := by simp

theorem original_family_row_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
    ∀ (u : Eisˣ) (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖(∑' i : ℕ×ℕ×ℕ,literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw)-
        ∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw‖≤
        Pset.card*(C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := original_family_dyadic_tail
    (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod u θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  have hs (P : L) : Summable (block P) :=
    literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo
      ((CompletedHeight.normTwistedSource_support W θ).trans hWs) htw X hX u
  have he (P : L) : ‖(∑' i,block P i)-∑ i∈J,block P i‖≤
      C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
    rw [tsum_sub_finset_eq_tail (block P) (hs P) J]
    have hh := hbound F K hK (S P.val.val) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) jF hj u θ X T QK QP hX hT hQK hQP hKr
      (by rw [hprod P.val.val P.val.property]; exact hPr P.val.val P.val.property)
    apply le_trans ?_ hh
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : i∈J <;> simp [J] at hi ⊢ <;> simp [hi,block]
  have hw (P : L) : ‖r K*aw P.val.val‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul hr (haw P.val.val P.val.property) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hh := finite_weighted_truncation_norm block (fun P : L => r K*aw P.val.val) J _ hs hw he
  change ‖(∑' i,∑ P : L,r K*aw P.val.val*block P i)-∑ i∈J,∑ P : L,r K*aw P.val.val*block P i‖≤_
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Fintype.card_subtype_le (fun P : Pset => IsCoprime K P.val)).trans_eq (Fintype.card_coe Pset)
  · positivity
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1105

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.RowTailUniformDegree
Source SHA256: f3a145c38aff88c1d4aaaa9f2a270ac7dc6361efc3d16bbd30ff378893ed0ae1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1106



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v

theorem original_family_row_tail_uniform_degree (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {N a c : Eis} {mode : Bool}, ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
    ∀ (u : Eisˣ) (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖(∑' i : ℕ×ℕ×ℕ,literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw)-
        ∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
          literalDyadicRow F K hK S jF Pset D s hc u i W θ X r aw‖≤
        Pset.card*(C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
          T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := original_family_dyadic_tail_uniform_degree lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro N a c mode φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod u θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let L := {P : Pset // IsCoprime K P.val}
  let block := fun (P : L) i => literalDyadicBlock (F.reflected K hK (S P.val.val))
    (D P.val P.property) s hc (reflectedExponent jF) (slotIndices φ (PrimeIndex K) σ)
    (CompletedHeight.normTwistedSource W θ) X u i
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  have htw : ContDiff ℝ ∞ (CompletedHeight.normTwistedSource W θ) := by
    have he : (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ:ℝ→ℂ)=
        CompletedHeight.normTwistedSource W θ := by
      funext x
      exact CompletedHeight.uniformTwistedSchwartz_apply W lo hi hlo hWs hW θ x
    rw [←he]
    exact (CompletedHeight.uniformTwistedSchwartz W lo hi hlo hWs hW θ).smooth ⊤
  have hj' : ∀ i : φ ⊕ (PrimeIndex K ⊕ σ), reflectedExponent jF i<6 := by
    intro i
    rcases i with f | k | p
    · exact hj f
    · norm_num [reflectedExponent]
    · norm_num [reflectedExponent]
  have hs (P : L) : Summable (block P) :=
    literalDyadicBlock_summable (F.reflected K hK (S P.val.val)) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) (reflectedExponent jF) hj' (slotIndices φ (PrimeIndex K) σ)
      (CompletedHeight.normTwistedSource W θ) lo hi hlo
      ((CompletedHeight.normTwistedSource_support W θ).trans hWs) htw X hX u
  have he (P : L) : ‖(∑' i,block P i)-∑ i∈J,block P i‖≤
      C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
        T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹ := by
    rw [tsum_sub_finset_eq_tail (block P) (hs P) J]
    have hh := hbound F K hK (S P.val.val) (D P.val P.property) s hc hN hbase
      (hchar P.val.val P.val.property) jF hj u θ X T QK QP hX hT hQK hQP hKr
      (by rw [hprod P.val.val P.val.property]; exact hPr P.val.val P.val.property)
    apply le_trans ?_ hh
    apply le_of_eq
    congr 1
    apply tsum_congr
    intro i
    by_cases hi : i∈J <;> simp [J] at hi ⊢ <;> simp [hi,block]
  have hw (P : L) : ‖r K*aw P.val.val‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul hr (haw P.val.val P.val.property) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hh := finite_weighted_truncation_norm block (fun P : L => r K*aw P.val.val) J _ hs hw he
  change ‖(∑' i,∑ P : L,r K*aw P.val.val*block P i)-∑ i∈J,∑ P : L,r K*aw P.val.val*block P i‖≤_
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast (Fintype.card_subtype_le (fun P : Pset => IsCoprime K P.val)).trans_eq (Fintype.card_coe Pset)
  · positivity
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1106

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.WholePair
Source SHA256: f1a10c6413dc7d53145debda427ce89e6e955aaeed357d45926dfd6e4e959964
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1107



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma sum_subtype_dite {α : Type*} [Fintype α] (p : α→Prop) (f : ∀ x,p x→ℂ) :
    (∑ x : {x // p x},f x.val x.property)=∑ x,if h:p x then f x h else 0 := by
  have hh := Fintype.sum_subtype_add_sum_subtype p (fun x => if h:p x then f x h else 0)
  have hz : (∑ x : {x // ¬p x},if h:p x.val then f x.val h else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dite_eq_right x.property
  rw [hz,add_zero] at hh
  simpa only [Subtype.property,dite_eq_left] using hh

def literalPairEntry (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K P : Ideal Eis) : ℂ :=
  if hK:K∈rows then if hP:P∈Pset then if hp:IsCoprime K P then
    r K*aw P*mixedReflectedValue (D ⟨K,hK⟩ ⟨P,hP⟩ hp) s
      (F.reflected K (hrows K hK) (S P)).generator_ne_zero hc
      (F.reflected K (hrows K hK) (S P)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X
  else 0 else 0 else 0

lemma literalWholeRow_eq_pairs (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K : rows) :
    literalWholeRow F K.val (hrows K.val K.property) S jF Pset (D K) s hc W θ X r aw=
      ∑ P∈Pset,literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K.val P := by
  let f := fun (P : Pset) (hp : IsCoprime K.val P.val) => r K.val*aw P.val*
    mixedReflectedValue (D K P hp) s (F.reflected K.val (hrows K.val K.property) (S P.val)).generator_ne_zero hc
      (F.reflected K.val (hrows K.val K.property) (S P.val)).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X
  change (∑ P : {P : Pset // IsCoprime K.val P.val},f P.val P.property)=_
  rw [sum_subtype_dite (fun P : Pset => IsCoprime K.val P.val) f,
    ←Finset.sum_coe_sort Pset (literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K.val)]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [literalPairEntry,dite_eq_left K.property,dite_eq_left P.property,f]

lemma literalPairEntry_restrict (F : PrimeFamily φ) (rows Pset rows' Pset' : Finset (Ideal Eis))
    (hrow : rows'⊆rows) (hP : Pset'⊆Pset) (S : Ideal Eis→PrimeFamily σ)
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (E : SectorArithmetic (N:=N) F rows' Pset' S (fun K hK => hrows K (hrow hK)) s hc)
    (hE : ∀ (K : rows') (P : Pset') hp,E.completion K P hp=D ⟨K.val,hrow K.property⟩ ⟨P.val,hP P.property⟩ hp)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (K P : Ideal Eis) (hK : K∈rows') (hp : P∈Pset') :
    literalPairEntry F rows' Pset' S (fun K hK => hrows K (hrow hK)) jF E.completion s hc W θ X r aw K P=
      literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw K P := by
  simp only [literalPairEntry,dite_eq_left hK,dite_eq_left hp,dite_eq_left (hrow hK),dite_eq_left (hP hp)]
  by_cases hcop : IsCoprime K P
  · simp only [dite_eq_left hcop,hE]
  · simp only [dite_eq_right hcop]
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1107

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ActiveProducts
Source SHA256: 4dbf992772413c4c7db790c5a13eca079652277bce42bf867db850893cccf14d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1108



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma slotProductCoefficient_norm (tuples : Finset (σ→Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (aw : (σ→Ideal Eis)→ℂ) (haw : ∀ p∈tuples,‖aw p‖≤1)
    (P : Ideal Eis) (hP : P∈tuples.image slotTupleProduct) :
    ‖slotProductCoefficient tuples aw P‖≤1 := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
  rw [slotProductCoefficient_at_product tuples hinj aw p hp]
  exact haw p hp

def activeTupleReflectedRow
    (F : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : tuples.image slotTupleProduct,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) (K : rows) : ℂ :=
    ∑ p : tuples,if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue
        (D K ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) X else 0

theorem literalWholeRow_eq_active_tuples
    (F : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : tuples.image slotTupleProduct,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) (K : rows) :
    literalWholeRow F K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood)
      jF (tuples.image slotTupleProduct) (D K) s hc W θ X r (slotProductCoefficient tuples aw)=
    ∑ p : tuples,if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue
        (D K ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
        (F.reflected K.val (hrows K.val K.property) (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) X else 0 := by
  rw [literalWholeRow_eq_pairs F rows _ _ hrows jF D s hc W θ X r _ K,Finset.sum_image hinj]
  rw [←Finset.sum_coe_sort tuples]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [literalPairEntry,dite_eq_left K.property,
    dite_eq_left (Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩),
    slotProductCoefficient_at_product tuples hinj aw p.val p.property]
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1108

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.FixedTuples
Source SHA256: 960abc7cd14c547bfbd32ba10e8cc1fd9d4500a22473edd06a624332fc2f4ca2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1109



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def fixedSlotTupleSet (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) : Finset (σ→Ideal Eis) :=
  (Fintype.piFinset L).filter fun p => ∀ j i,p i≠F j

lemma mem_fixedSlotTupleSet (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (p : σ→Ideal Eis) :
    p∈fixedSlotTupleSet L F ↔ (∀ i,p i∈L i) ∧ ∀ j i,p i≠F j := by
  simp only [fixedSlotTupleSet,Finset.mem_filter,Fintype.mem_piFinset]

lemma fixedSlotTupleSet_product_injective (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P) :
    Set.InjOn slotTupleProduct (↑(fixedSlotTupleSet L F) : Set (σ→Ideal Eis)) :=
  (slotTupleProduct_injective_on L hL hprime).mono (fun p hp => (mem_fixedSlotTupleSet L F p).mp hp |>.1)

def supportedSlotTupleEquiv (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :
    supportedSlotChoices L F K ≃ {p : fixedSlotTupleSet L F // IsCoprime K (slotTupleProduct p.val)} where
  toFun p := ⟨⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩⟩,p.property.1⟩
  invFun p := ⟨fun i => ⟨p.val.val i,((mem_fixedSlotTupleSet L F _).mp p.val.property).1 i⟩,
    ⟨p.property,((mem_fixedSlotTupleSet L F _).mp p.val.property).2⟩⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    rfl
  right_inv p := rfl

def supportedSlotProductEquiv (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (K : Ideal Eis) :
    supportedSlotChoices L F K ≃
      {P : (fixedSlotTupleSet L F).image slotTupleProduct // IsCoprime K P.val} := by
  let f := fun p : supportedSlotChoices L F K =>
    (⟨⟨slotTupleProduct (fun i => (p.val i).val),Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩,p.property.1⟩ :
      {P : (fixedSlotTupleSet L F).image slotTupleProduct // IsCoprime K P.val})
  apply Equiv.ofBijective f
  constructor
  · intro p q he
    have hv := congrArg (fun P => P.val.val) he
    have hh := fixedSlotTupleSet_product_injective L F hL hprime
      ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩)
      ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (q.val i).property,q.property.2⟩) hv
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun hh i)
  · intro P
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp P.val.property
    let q : supportedSlotChoices L F K := ⟨fun i => ⟨p i,((mem_fixedSlotTupleSet L F p).mp hp).1 i⟩,
      ⟨by change IsCoprime K (slotTupleProduct p);rw [he];exact P.property,((mem_fixedSlotTupleSet L F p).mp hp).2⟩⟩
    refine ⟨q,?_⟩
    apply Subtype.ext
    exact Subtype.ext he

lemma supportedSlotProductEquiv_apply (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (K : Ideal Eis) (p : supportedSlotChoices L F K) :
    ((supportedSlotProductEquiv L F hL hprime K) p).val.val=∏ i,(p.val i).val := rfl
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1109

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ChoiceTransport
Source SHA256: cc70193c4fbdf86265d9c39d701193506a6a6e188c03a1f796328fff8e68e70d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1110



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

def fixedTupleFamily (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P) (P : Ideal Eis) : PrimeFamily σ :=
  tuplePrimeFamily (fixedSlotTupleSet L F) hne
    (fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i))
    (fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)) P

lemma fixedTupleFamily_at_choice (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (p : ∀ i,L i) (hp : ∀ j i,(p i).val≠F j) :
    fixedTupleFamily L F hne hmax hgood (∏ i,(p i).val)=slotChoiceFamily L hmax hgood p := by
  apply PrimeFamily.eq_of_ideal_eq
  exact tuplePrimeFamily_at_product (fixedSlotTupleSet L F) hne _ _
    (fixedSlotTupleSet_product_injective L F hL hprime) (fun i => (p i).val)
    ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p i).property,hp⟩)

def fixedTupleCoefficient (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ) (p : σ→Ideal Eis) : ℂ :=
  if hp:∀ i,p i∈L i then ∏ i,w i ⟨p i,hp i⟩ else 0

omit [DecidableEq σ] in
lemma fixedTupleCoefficient_at (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ) (p : ∀ i,L i) :
    fixedTupleCoefficient L w (fun i => (p i).val)=∏ i,w i (p i) := by
  simp only [fixedTupleCoefficient,dite_eq_left (show ∀ i,(p i).val∈L i from fun i => (p i).property)]

omit [DecidableEq σ] in
lemma fixedTupleCoefficient_norm (L : σ→Finset (Ideal Eis)) (w : ∀ i,L i→ℂ)
    (hw : ∀ i P,‖w i P‖≤1) (p : σ→Ideal Eis) : ‖fixedTupleCoefficient L w p‖≤1 := by
  unfold fixedTupleCoefficient
  split
  · exact slot_coefficient_norm L w hw _
  · simp
