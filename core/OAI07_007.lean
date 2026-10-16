    ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths ≤
      (max 1 b)^N/(Ideal.absNorm C:ℝ)*(frozenControl B.val M)^2 := by
  have hB := (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1
  have hR := rawReduction_pos B.val hB D.lengths hP
  have hN := CenteredMomentFirstScale.norm_pos C hC
  by_cases hz : frozenCoefficient B.val C D.R D.nu D.slot D.lengths=0
  · rw [hz,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    positivity
  · have hm := frozen_norm_bound D C B M hM hν hWnorm
    have hh := (actual_reduction_norm B.val hB C D.R
      (Finset.mem_filter.mp B.property).2 D.nu D.slot D.lengths hP a b ha hW hz).2
    have he : (max 1 b)^Fintype.card ι≤(max 1 b)^N :=
      pow_le_pow_right₀ (le_max_left _ _) hcard
    have hi : (1:ℝ)/rawReduction B.val D.lengths ≤ (max 1 b)^N/(Ideal.absNorm C:ℝ) := by
      apply (div_le_div_iff₀ hR hN).mpr
      simpa only [one_mul] using hh.trans (mul_le_mul_of_nonneg_right he hR.le)
    calc
      _ ≤ (frozenControl B.val M)^2/rawReduction B.val D.lengths :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm _) hR.le
      _ = (frozenControl B.val M)^2*(1/rawReduction B.val D.lengths) := by ring
      _ ≤ (frozenControl B.val M)^2*((max 1 b)^N/(Ideal.absNorm C:ℝ)) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = _ := by ring

theorem normalized_common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        (‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2/rawReduction B.val D.lengths) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  have hV := rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP
  have he := div_le_div_of_nonneg_right
    (common_energy_allocation D hS hp C hC hseed τ t L W K hK hW) hV.le
  apply he.trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ => ((actualAllocations D.S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hR := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
  field_simp

theorem normalized_common_energy_bound (N : ℕ) (a b : ℝ) (ha : 0<a)
    (D : OriginalData ι) (hcard : Fintype.card ι≤N)
    (hS : ∀ i,∀ I∈D.S i,I≠0) (hp : ∀ i,∀ I∈D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) (M : ι → ℝ) (hM : ∀ i,0≤M i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hWnorm : ∀ i x,‖D.slot i x‖≤M i)
    (hslot : ∀ i,Function.support (D.slot i)⊆Set.Icc a b) :
    commonEnergy D C hC τ t L W K / rawVolume D ≤
      (max 1 b)^N * ((actualAllocations D.S C).card:ℝ)/(Ideal.absNorm C:ℝ) *
        ∑ B : actualAllocations D.S C, (frozenControl B.val M)^2 *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  apply (normalized_common_energy_allocation D hS hp C hC hseed τ t L W K hK hW
    hX₁ hX₂ hB₁ hB₂ hP).trans
  calc
    _ ≤ ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ((max 1 b)^N/(Ideal.absNorm C:ℝ)*(frozenControl B.val M)^2) *
          (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      have hVa : 0<rawVolume (allocatedData D C L B) := by
        rw [allocated_rawVolume D C L B hB₁ hB₂ hP]
        exact div_pos (rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP)
          (rawReduction_pos B.val (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP)
      exact mul_le_mul_of_nonneg_right
        (frozen_normalized_bound N a b ha D hcard C hC.1 B M hM hP hν hWnorm hslot)
        (div_nonneg (allocated_nonneg D C L B τ t W K hK hW) hVa.le)
    _ = _ := by
      simp only [mul_assoc,← Finset.mul_sum]
      ring

theorem normalized_common_as_tsum (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hV : 0<rawVolume D) :
    (∑' z : O, ‖(Real.sqrt (rawVolume D):ℂ)⁻¹ * commonGauss D C hC τ t L z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) =
      commonEnergy D C hC τ t L W K/rawVolume D := by
  have hn (z : O) : ‖(Real.sqrt (rawVolume D):ℂ)⁻¹ * commonGauss D C hC τ t L z‖^2 =
      ‖commonGauss D C hC τ t L z‖^2/rawVolume D := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow,inv_pow,Real.sq_sqrt hV.le]
    ring
  simp_rw [hn,div_mul_eq_mul_div]
  exact tsum_div_const

theorem allocated_sum_hasSum (D : OriginalData ι) (C L : Ideal O)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ∑ B : actualAllocations D.S C,
      ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
        (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
        (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re))
      (∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K) := by
  exact hasSum_sum (fun B _ => (allocated_hasSum D C L B τ t W K hK).mul_left _)

theorem original_radial_bound (N : ℕ) (a b : ℝ) (ha : 0<a) :
    ∃ F : ℝ,0<F ∧ ∀ {κ : Type*} [Fintype κ],∀ D : OriginalData κ,
      Fintype.card κ≤N →
      (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
      ∀ (C : Ideal O) (hC : Supported C), D.s∣C →
      ∀ (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K T : ℝ),
      0<K → (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      0<D.X₁ → 0<D.X₂ → D.B₁≠0 → D.B₂≠0 →
      (∀ i,0<D.lengths i) → D.X₁*D.X₂=T → D.Y₁*D.Y₂=T →
      ∀ M : κ → ℝ,(∀ i,0≤M i) → (∀ i I,‖D.nu i I‖≤1) →
      (∀ i x,‖D.slot i x‖≤M i) →
      (∀ i,Function.support (D.slot i)⊆Set.Icc a b) →
      (∑' z : O,
        ‖(Real.sqrt ((T/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i):ℂ)⁻¹ *
          commonGauss D C hC τ t L z‖^2 * (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) ≤
        F*((actualAllocations D.S C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          ∑ B : actualAllocations D.S C,(frozenControl B.val M)^2 *
            (allocatedEnergy D C L B τ t W K/rawVolume (allocatedData D C L B)) := by
  refine ⟨(max 1 b)^N,pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _,?_⟩
  intro κ _ D hcard hS hp C hC hseed τ t L W K T hK hW hX₁ hX₂ hB₁ hB₂ hP hX hY M hM hν hWnorm hslot
  rw [← (rawVolume_both D T hX hY).1,
    normalized_common_as_tsum D C hC τ t L W K (rawVolume_pos D hX₁ hX₂ hB₁ hB₂ hP)]
  exact normalized_common_energy_bound N a b ha D hcard hS hp C hC hseed τ t L W K hK hW
    hX₁ hX₂ hB₁ hB₂ hP M hM hν hWnorm hslot

end SevenEighths.CenteredMomentFirstAllocationGaussEnergy

end

end OAI
end OAIOriginalModule2162

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceAllocationControl
Source SHA256: 4edef3cf37908d762c93dac08124cc435ec1df9b870dba093e2d6bf50f4552bd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2163




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceMass
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance firstAllocationControlDecidableEq {κ : Type*} : DecidableEq κ := Classical.decEq _

lemma frozen_live_control (B : Tuple ι) (M : ι→ℝ) :
    frozenControl B M * (∏i : liveIndices B,M i.val) = ∏i,M i := by
  rw [Finset.prod_coe_sort (liveIndices B) M]
  unfold frozenControl liveIndices
  rw [mul_comm]
  exact Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i=>B (Sum.inl i)=1) M

lemma frozen_child_control (s : Input ι) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : HeckeFamily.Character) (t : ℝ) :
    (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2 = (∏i,s.M i)^2 := by
  rw [←mul_pow]
  exact congrArg (fun x:ℝ=>x^2) (frozen_live_control B.val s.M)

lemma allocated_control_sum (s : Input ι) (C R : Ideal O)
    (τ : HeckeFamily.Character) (t : ℝ) :
    (∑B : actualAllocations s.pools C,
      (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) =
      ((actualAllocations s.pools C).card:ℝ) * (∏i,s.M i)^2 := by
  simp only [frozen_child_control,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
    nsmul_eq_mul]

theorem allocated_control_mass (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀{κ : Type*}[Fintype κ],Fintype.card κ≤N →
      ∀(s : Input κ)(C R : Ideal O),C≠0 →
      ∀(τ : HeckeFamily.Character)(t : ℝ),
        ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
          (∑B : actualAllocations s.pools C,
            (frozenControl B.val s.M)^2 * (∏i,(child s C R B τ t).M i)^2) ≤
          D*(Ideal.absNorm C:ℝ)^(ε-1)*(∏i,s.M i)^2 := by
  obtain ⟨D,hD,hcard⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (ε/2) (half_pos hε)
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro κ _ hn s C R hC τ t
  have hN : (0:ℝ)<Ideal.absNorm C := CenteredMomentFirstScale.norm_pos C hC
  have hh := hcard (ι:=κ⊕Fin 2) (by simp only [Fintype.card_sum,Fintype.card_fin];omega)
    s.pools C hC
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (actualAllocations s.pools C).card) hh 2
  rw [mul_pow,←Real.rpow_mul_natCast hN.le,show ε/2*(2:ℕ)=ε by norm_num] at hs
  rw [allocated_control_sum]
  calc
    _ = (((actualAllocations s.pools C).card:ℝ)^2/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 := by ring
    _ ≤ (D^2*(Ideal.absNorm C:ℝ)^ε/(Ideal.absNorm C:ℝ)) * (∏i,s.M i)^2 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs hN.le) (sq_nonneg _)
    _ = _ := by rw [Real.rpow_sub hN,Real.rpow_one];ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2163

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalColumn
Source SHA256: 6a564e07ff7d81bf2cba2f19cfbe28dcc163bc65590bd2ae0c77b89ff7a8cad3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2164



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentSecondSectorColumns CenteredMomentFirstSectorTransform IdealMobiusDivisorSum
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors CenteredMomentLiveDomain
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentChildAssembly
local notation "O"=>ActualEisensteinCubic.O

theorem columns_gauss_polynomial (C:Ideal O)(hC:Supported C)(S:Finset (Ideal O))
    (f:Ideal O→ℂ)(z:O):
    gaussPolynomial Finset.univ (element C C hC.1 S) (element_supported C C hC.1 S)
      (fun a=>f a) z=
    gaussPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
      (sourceGenerator_supported _) (fun I=>if IsCoprime C (I:Ideal O) then f I else 0) z:=by
  rw [source_gaussPolynomial (residualPool C hC.1 S)
    (fun I=>if IsCoprime C I then f I else 0) z,supported_residualPool C hC S]
  have he (a:columns C C hC.1 S):
      gaussRow (element C C hC.1 S a) (element_supported C C hC.1 S a) z=
        primaryGaussRow a z:=by
    rw [primaryGaussRow,dite_eq_left (column_supported C C hC.1 S a)]
    rfl
  simp only [gaussPolynomial,he]
  rw [Finset.sum_coe_sort (columns C C hC.1 S) (fun I=>f I*primaryGaussRow I z)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

theorem columns_gauss_polynomial_filter (Q C:Ideal O)(hC:Supported C)(S:Finset (Ideal O))
    (f:Ideal O→ℂ)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 S) (element_supported Q C hC.1 S)
      (fun a=>f a) z=
    gaussPolynomial Finset.univ (sourceGenerator (residualPool C hC.1 S))
      (sourceGenerator_supported _) (fun I=>if IsCoprime Q (I:Ideal O) then f I else 0) z:=by
  rw [source_gaussPolynomial (residualPool C hC.1 S)
    (fun I=>if IsCoprime Q I then f I else 0) z,supported_residualPool C hC S]
  have he (a:columns Q C hC.1 S):
      gaussRow (element Q C hC.1 S a) (element_supported Q C hC.1 S a) z=
        primaryGaussRow a z:=by
    rw [primaryGaussRow,dite_eq_left (column_supported Q C hC.1 S a)]
    rfl
  simp only [gaussPolynomial,he]
  rw [Finset.sum_coe_sort (columns Q C hC.1 S) (fun I=>f I*primaryGaussRow I z)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs <;> simp

variable {ι:Type*}[Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem first_column_original_data (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)
    (a:columns C C hC.1 D.columns→ℂ)
    (ha:∀I:columns C C hC.1 D.columns,
      a I=(if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element C C hC.1 D.columns)
      (element_supported C C hC.1 D.columns) a z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask t T) z:=by
  rw [funext ha,columns_gauss_polynomial C hC D.columns
    (fun I=>(if L∣I then D.beta (C*I) else 0)*heightCoeff τ t I) z]
  have he:(fun I:supportedColumns (residualPool C hC.1 D.columns)=>
      if IsCoprime C (I:Ideal O) then
        (if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I:supportedColumns (residualPool C hC.1 D.columns)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I):=by
    funext I
    by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]
  rw [he]
  exact normalized_common_gauss_allocation D hS hp C hC hseed τ t T L z

theorem first_column_original_data_filter (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)
    (a:columns Q C hC.1 D.columns→ℂ)
    (ha:∀I:columns Q C hC.1 D.columns,
      a I=(if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 D.columns)
      (element_supported Q C hC.1 D.columns) a z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask t T) z:=by
  rw [funext ha,columns_gauss_polynomial_filter Q C hC D.columns
    (fun I=>(if L∣I then D.beta (C*I) else 0)*heightCoeff τ t I) z]
  have he:(fun I:supportedColumns (residualPool C hC.1 D.columns)=>
      if IsCoprime Q (I:Ideal O) then
        (if L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I else 0)=
      (fun I:supportedColumns (residualPool C hC.1 D.columns)=>
        (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I):=by
    funext I
    rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
    by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]
  rw [he]
  exact normalized_common_gauss_allocation D hS hp C hC hseed τ t T L z

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2164

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceCanonicalData
Source SHA256: d71e86055f953f46bf2c902649c7bafd151bed09f7cdc7fbaac8505f3f8ad96e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2165


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport
open CenteredMomentGaussEnergy CenteredMomentFirstColumns CenteredMomentChildAssembly
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily
open RayFourExpansion IdealMobiusDivisorSum ActualEisensteinCubic CenteredMomentHeckeExpansion
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstCanonicalDataDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def allocatedPolynomial (s:OriginalData ι)(C L:Ideal O)(τ:Character)(t T:ℝ)(z:O):ℂ:=
  ∑B:actualAllocations s.S C,frozenCoefficient B.val C s.R s.nu s.slot s.lengths*
    gaussPolynomial Finset.univ (sourceGenerator (allocatedData s C L B).columns)
      (sourceGenerator_supported (allocatedData s C L B).columns)
      ((allocatedData s C L B).coefficient τ fixedBadMask t T) z

def leftChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C C hC.1 s.columns) (element_supported C C hC.1 s.columns)
    (divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta C a*leftCoefficient e r ρ (element C C hC.1 s.columns a)) χ) z

def rightChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C D hD.1 s.columns) (element_supported C D hD.1 s.columns)
    (divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta D a*rightCoefficient e r ρ (element C D hD.1 s.columns a)) χ) z

theorem actual_canonical_original_data (η:Character)(m:O)(hm:m≠0)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let M:=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*activeConductor C D};
    ∃τ₁ τ₂:Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      ∀s:OriginalData ι,(∀i,∀I∈s.S i,I≠0)→(∀i,∀I∈s.S (Sum.inl i),Prime I)→
      s.s∣C→s.s∣D→∀t T:ℝ,∀L:Ideal O,∀z:O,
        (Real.sqrt T:ℂ)⁻¹*leftChild s η m t C D hC E ξ₁ L z=
          allocatedPolynomial s C L τ₁ t T z ∧
        (Real.sqrt T:ℂ)⁻¹*rightChild s η m t C D hC hD E ξ₂ L (-z)=
          allocatedPolynomial s D L τ₂ t T (-z):=by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩:=actual_child_family η m hm hmLam hm2 C D hC hD E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_⟩
  intro s hS hp hsC hsD t T L z
  constructor
  · exact first_column_original_data s hS hp C hC hsC τ₁ t T L _
      (h₁ s.columns s.beta t L) z
  · exact first_column_original_data_filter s hS hp C D hC.1 hD hCD hsD τ₂ t T L _
      (h₂ s.columns s.beta t L) (-z)

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2165

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindow
Source SHA256: 069f905cb97b7bc204a2ff526e84d56c13a8727964c240fcf15d9c8a18552123
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2166



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentSmooth
open FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma generator_span (S:Finset (Ideal O))(I:supportedColumns S):
    Ideal.span {sourceGenerator S I}=(I:Ideal O):=
  primary_span_supported I (Finset.mem_filter.mp I.property).2

def commonWindow (D:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)
    (t θ X:ℝ)(V:ℝ→ℂ)(L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 D.columns
  gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then D.beta (C*I) else 0)*heightCoeff τ t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z

theorem common_window_original_integral (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*commonWindow D C hC τ t θ X V L z=
      ∫w:ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
          gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported (allocatedData D C L B).columns)
            ((allocatedData D C L B).coefficient τ fixedBadMask
              (t+2*Real.pi*(w-θ)) T) z:=by
  let Q:=residualPool C hC.1 D.columns
  let β:=fun I:supportedColumns Q=>if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
    then D.beta (C*I) else 0
  have hh:=gauss_column_integral Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    β τ t θ X hX V hVc hVs z
  simp only [generator_span] at hh
  change commonWindow D C hC τ t θ X V L z=
    ∫w:ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      commonGauss D C hC τ (t+2*Real.pi*(w-θ)) L z at hh
  rw [hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  have he:=normalized_common_gauss_allocation D hS hp C hC hseed τ
    (t+2*Real.pi*(w-θ)) T L z
  rw [←he]
  ring

theorem common_window_original_integrable (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)(z:O):
    Integrable (fun w:ℝ=>columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask (t+2*Real.pi*(w-θ)) T) z):=by
  let Q:=residualPool C hC.1 D.columns
  let β:=fun I:supportedColumns Q=>if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
    then D.beta (C*I) else 0
  have hh:=(CenteredMomentHeckeWindowEnergy.gauss_column_integrable Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) β τ t θ X hX V hVc hVs z).const_mul
      ((Real.sqrt T:ℂ)⁻¹)
  simp only [generator_span] at hh
  convert hh using 1
  funext w
  rw [←normalized_common_gauss_allocation D hS hp C hC hseed τ (t+2*Real.pi*(w-θ)) T L z]
  change _=(Real.sqrt T:ℂ)⁻¹*(columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
    commonGauss D C hC τ (t+2*Real.pi*(w-θ)) L z)
  ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2166

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowColumns
Source SHA256: cc8c4a87408333941f15426151dc0de5821cee12b1b5092c7556a92b8ee74886
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2167




namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum
open FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowColumnsDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma element_norm (Q C:Ideal O)(hC:C≠0)(S:Finset (Ideal O))(I:columns Q C hC S):
    ‖eisEmbedding (element Q C hC S I)‖^2=(Ideal.absNorm (I:Ideal O):ℝ):=by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,element_span]

theorem column_window_common (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(V:ℝ→ℂ)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) z=
        commonWindow s C hC τ t θ X V L z:=by
  simp only [ha,element_norm]
  rw [columns_gauss_polynomial_filter Q C hC s.columns
    (fun I=>(if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I*
      columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ) z]
  unfold commonWindow
  congr 1
  funext I
  rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]

theorem column_window_original_integral (s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:s.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) z=
      ∫w:ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        allocatedPolynomial s C L τ (t+2*Real.pi*(w-θ)) T z:=by
  rw [column_window_common s Q C hQ hC hQC τ t θ X V L a ha z]
  exact common_window_original_integral s hS hp C hC hseed τ t T θ X hX V hVc hVs L z

theorem column_star_window_original_integral (s:OriginalData ι)
    (hS:∀i,∀I∈s.S i,I≠0)(hp:∀i,∀I∈s.S (Sum.inl i),Prime I)
    (Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)(hQC:primeSupport Q=primeSupport C)
    (hseed:s.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)(z:O):
    (Real.sqrt T:ℂ)⁻¹*gaussPolynomial Finset.univ (element Q C hC.1 s.columns)
      (element_supported Q C hC.1 s.columns)
      (fun I=>a I*star (columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ)) (-z)=
      ∫w:ℝ,columnDensity (fun x=>star (V x)) (conjugate_compact V hVc)
        (conjugate_smooth V hVs) w*logPhase (-θ-w) (Real.log X)*
        allocatedPolynomial s C L τ (t+2*Real.pi*(w-(-θ))) T (-z):=by
  simp only [star_columnPhase]
  exact column_window_original_integral s hS hp Q C hQ hC hQC hseed τ t T (-θ) X hX
    (fun x=>star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) L a ha (-z)

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2167

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowCanonical
Source SHA256: 5c31e2e5368e00678b3c271aadbae56539b3783406eeec59bfbe43fda2735e5e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2168


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum
open FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowCanonicalDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def leftWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C C hC.1 s.columns) (element_supported C C hC.1 s.columns)
    (fun I=>divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta C a*leftCoefficient e r ρ (element C C hC.1 s.columns a)) χ I*
      columnPhase V (Real.log (‖eisEmbedding (element C C hC.1 s.columns I)‖^2/X)) θ) z

def rightWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C D hD.1 s.columns) (element_supported C D hD.1 s.columns)
    (fun I=>divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta D a*rightCoefficient e r ρ (element C D hD.1 s.columns a)) χ I*
      star (columnPhase V (Real.log (‖eisEmbedding (element C D hD.1 s.columns I)‖^2/X)) θ)) z

theorem actual_canonical_window_integrals (η:Character)(m:O)(hm:m≠0)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let M:=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*activeConductor C D};
    ∃τ₁ τ₂:Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      ∀s:OriginalData ι,(∀i,∀I∈s.S i,I≠0)→(∀i,∀I∈s.S (Sum.inl i),Prime I)→
      s.s∣C→s.s∣D→∀t T θ X Y:ℝ,0<X→0<Y→
      ∀V₁:ℝ→ℂ,∀hV₁c:HasCompactSupport V₁,∀hV₁s:ContDiff ℝ ∞ V₁,
      ∀V₂:ℝ→ℂ,∀hV₂c:HasCompactSupport V₂,∀hV₂s:ContDiff ℝ ∞ V₂,
      ∀L:Ideal O,∀z:O,
        (Real.sqrt T:ℂ)⁻¹*leftWindowChild s η m t C D hC E ξ₁ L θ X V₁ z=
          (∫w:ℝ,columnDensity V₁ hV₁c hV₁s w*logPhase (θ-w) (Real.log X)*
            allocatedPolynomial s C L τ₁ (t+2*Real.pi*(w-θ)) T z) ∧
        (Real.sqrt T:ℂ)⁻¹*rightWindowChild s η m t C D hC hD E ξ₂ L θ Y V₂ (-z)=
          (∫w:ℝ,columnDensity (fun x=>star (V₂ x)) (conjugate_compact V₂ hV₂c)
            (conjugate_smooth V₂ hV₂s) w*logPhase (-θ-w) (Real.log Y)*
            allocatedPolynomial s D L τ₂ (t+2*Real.pi*(w-(-θ))) T (-z)):=by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩:=actual_child_family η m hm hmLam hm2 C D hC hD E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_⟩
  intro s hS hp hsC hsD t T θ X Y hX hY V₁ hV₁c hV₁s V₂ hV₂c hV₂s L z
  constructor
  · exact column_window_original_integral s hS hp C C hC.1 hC rfl hsC τ₁ t T θ X hX
      V₁ hV₁c hV₁s L _ (h₁ s.columns s.beta t L) z
  · exact column_star_window_original_integral s hS hp C D hC.1 hD hCD hsD τ₂ t T θ Y hY
      V₂ hV₂c hV₂s L _ (h₂ s.columns s.beta t L) z

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2168

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowEnergy
Source SHA256: 74989b2b9d69232c9735c02730c73427e826d19c0f3c85021d9a942a5b10d8d5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2169



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowEnergyDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def commonEnergy (s:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)
    (t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):ℂ:=
  let Q:=residualPool C hC.1 s.columns
  gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then s.beta (C*I) else 0)*heightCoeff τ t I) U K

lemma column_unwindowed_common (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):
    gaussPolynomial Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I) z=
      commonGauss s C hC τ t L z:=by
  rw [columns_gauss_polynomial_filter Q C hC s.columns
    (fun I=>(if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I) z]
  unfold commonGauss
  congr 1
  funext I
  rw [coprime_of_same_support Q C I hQ hC.1 (Finset.mem_filter.mp I.property).2.1 hQC]
  by_cases hc:IsCoprime C (I:Ideal O) <;> by_cases hl:L∣(I:Ideal O) <;> simp [hc,hl]

theorem column_unwindowed_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t:ℝ)(L:Ideal O)(U:𝓢(ℝ,ℂ))(K:ℝ):
    gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I) U K=
      commonEnergy s C hC τ t L U K:=by
  unfold gaussEnergy commonEnergy
  apply tsum_congr
  intro z
  rw [column_unwindowed_common s Q C hQ hC hQC τ t L z]
  rfl

theorem column_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫w:ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2:=by
  have hh:=smoothed_window_energy_from_height V hVc hVs J Finset.univ
    (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
    (fun I:columns Q C hC.1 s.columns=>if L∣(I:Ideal O) then s.beta (C*I) else 0)
    τ t θ X hX U K hK hU E hE (fun v=>by
      simp only [element_span]
      rw [column_unwindowed_energy s Q C hQ hC hQC]
      exact henergy v)
  simpa only [ha,element_span,element_norm] using hh

theorem column_star_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*star (columnPhase V
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ)) U K).re≤
      (E*heightCost t (-θ)^(2*J))*(∫w:ℝ,(1+‖w‖)^J*
        ‖columnDensity (fun x=>star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) w‖)^2:=by
  simp only [star_columnPhase]
  exact column_window_energy s Q C hQ hC hQC τ t (-θ) X hX
    (fun x=>star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs)
    L a ha U K hK hU J E hE henergy

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2169

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceDyadicWindowEnergy
Source SHA256: 15c3e17d888f548602b6f5cc229727f075846fdb4c649a124f420dd7e622fb5c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2170



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentLogDyadic CenteredMomentSecondWindowSource CenteredMomentSecondWindowBudget
open IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

theorem column_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*columnPhase logAnnulus
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  exact (column_window_energy s Q C hQ hC hQC τ t θ X hX
    logAnnulus logAnnulus_compact logAnnulus_smooth L a ha U K hK hU J E hE henergy).trans
      (shifted_window_budget J t θ E hE)

theorem column_star_dyadic_window_energy (s:OriginalData ι)(Q C:Ideal O)(hQ:Q≠0)(hC:Supported C)
    (hQC:primeSupport Q=primeSupport C)(τ:Character)(t θ X:ℝ)(hX:0<X)(L:Ideal O)
    (a:columns Q C hC.1 s.columns→ℂ)
    (ha:∀I:columns Q C hC.1 s.columns,
      a I=(if L∣(I:Ideal O) then s.beta (C*I) else 0)*heightCoeff τ t I)
    (U:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(hU:∀z:O,0≤(U (‖eisEmbedding z‖^2/K)).re)
    (J:ℕ)(E:ℝ)(hE:0≤E)
    (henergy:∀v:ℝ,(commonEnergy s C hC τ v L U K).re≤E*(1+‖v‖)^(2*J)):
    (gaussEnergy Finset.univ (element Q C hC.1 s.columns) (element_supported Q C hC.1 s.columns)
      (fun I=>a I*star (columnPhase logAnnulus
        (Real.log (‖eisEmbedding (element Q C hC.1 s.columns I)‖^2/X)) θ)) U K).re≤
      (windowBudget J t E*(1+‖θ‖)^J)^2:=by
  simpa only [star_logAnnulus_column,norm_neg] using
    column_dyadic_window_energy s Q C hQ hC hQC τ t (-θ) X hX L a ha U K hK hU J E hE henergy

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2170

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePresentation
Source SHA256: 6dc9f46236908d9cfdd0e0cf4325dbc58b73ba0ca7229797cfa80559646ed35a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2171


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalFamily
local notation "O"=>ActualEisensteinCubic.O

def fixedPresentationCost : ℝ:=
  (Ideal.absNorm (Ideal.span {fixedBadMask}):ℝ)*Ideal.absNorm (Ideal.span {(72:O)})

theorem fixedPresentationCost_pos : 0<fixedPresentationCost:=by
  apply mul_pos
  · exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using fixedBadMask_ne_zero))
  · exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simp))

theorem fixed_presentation_norm (η τ:Character)(C D:Ideal O)(E:Finset (CommonIndex C D))
    (hM:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (τ.modulus.absNorm:ℝ)=fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=by
  rw [hM,←Ideal.span_singleton_mul_span_singleton]
  simp only [map_mul,Nat.cast_mul,eisEmbedding_norm_sq_eq_absNorm_span,fixedPresentationCost]
  ring

theorem fixed_pair_presentation_caps (η τ₁ τ₂:Character)(C D:Ideal O)
    (E:Finset (CommonIndex C D))
    (hM₁:τ₁.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (hM₂:τ₂.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (τ₁.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2 ∧
    (τ₂.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=
  ⟨(fixed_presentation_norm η τ₁ C D E hM₁).le,(fixed_presentation_norm η τ₂ C D E hM₂).le⟩

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2171

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceFixedFamily
Source SHA256: 007f3348acf5ce8d0968961d025b7289a63066e44c9e471beb1c64cd3cc36107
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2172




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentFirstMaskedFamily CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceProfileMass CenteredMomentSupportedZeroEnergy CenteredMomentCommonSupport
open CenteredMomentChildAssembly CenteredMomentAddedZeroUniform RayFourExpansion CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

structure FixedPair (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter) where
  left : Character
  right : Character
  left_modulus : left.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}
  right_modulus : right.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}
  left_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff left t I=rowWeight η fixedBadMask 1 1 t I*
      (leftCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))
  right_height : ∀I:Ideal O,Supported I→∀t:ℝ,
    heightCoeff right t I=rowWeight η fixedBadMask 1 1 t I*
      (rightCoefficient (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC)
          (activeExponent C D)) (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))

def fixedPair (η:Character)(C D:Ideal O)(hC:Supported C)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):FixedPair η C D hC E ξ₁ ξ₂:=
  Classical.choice (by
    obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,_,_⟩:=exists_canonical_masked_pair η C D hC E ξ₁ ξ₂
    exact ⟨⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩⟩)

theorem FixedPair.conductor_caps {η:Character}{C D:Ideal O}{hC:Supported C}
    {E:Finset (CommonIndex C D)}{ξ₁ ξ₂:RayCharacter}(F:FixedPair η C D hC E ξ₁ ξ₂):
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2 ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=
  fixed_pair_presentation_caps η F.left F.right C D E F.left_modulus F.right_modulus

variable {ι:Type*}[Fintype ι]
local instance firstFixedFamilyDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem beta_coprime (s:OriginalData ι)(I:Ideal O)(h:s.beta I≠0):IsCoprime I s.R:=by
  obtain ⟨v,hv,hv0,he⟩:=finiteColumnCoefficient_witness (Fintype.piFinset s.S) s.profile I h
  rw [←he]
  by_contra hn
  apply hv0
  simp only [OriginalData.profile,profileCoefficient,hn,ite_false,mul_zero,zero_mul]

lemma extracted_mask_redundant (s:OriginalData ι)(C:Ideal O):
    maskedSource (idealGenerator s.R) (fun I=>s.beta (C*I))=(fun I=>s.beta (C*I)):=by
  apply maskedSource_eq_of_live
  intro I hI
  rw [span_idealGenerator]
  exact (beta_coprime s (C*I) hI).of_mul_left_right

theorem fixed_divisor_column (s:OriginalData ι)(η τ:Character)(C:Ideal O)
    (F:O→ℂ)(ξ:RayCharacter)
    (hτ:∀I:Ideal O,Supported I→∀t:ℝ,heightCoeff τ t I=
      rowWeight η fixedBadMask 1 1 t I*(F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (L I:Ideal O)(hI:Supported I)(t:ℝ):
    divisorCoefficient L (fun J:Ideal O=>primaryGenerator J)
      (fun J=>s.beta (C*J)*rowWeight η (fixedBadMask*idealGenerator s.R) 1 1 t J*
        F (primaryGenerator J)) ξ I=
      (if L∣I then s.beta (C*I) else 0)*heightCoeff τ t I:=by
  have hh:=divisor_column_masked η τ F ξ hτ (idealGenerator s.R) L I hI (fun J=>s.beta (C*J)) t
  rw [extracted_mask_redundant] at hh
  exact hh

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2172

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps
Source SHA256: 77b53e68d974610c87d6a2a00f8290f171bad457df04eca52b9af21a4421e770
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2173




namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentFirstSourceConductorCaps
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSecondHeightFamily
local notation "O"=>ActualEisensteinCubic.O

lemma divisor_norm_le (I C : Ideal O) (hC : C≠0) (h : I∣C) :
    (I.absNorm:ℝ)≤C.absNorm := by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC))
    (map_dvd Ideal.absNorm h)

lemma original_factor_caps (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) :
    ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2≤C.absNorm ∧
    ‖eisEmbedding (activeConductor C D)‖^2≤C.absNorm := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span,eisEmbedding_norm_sq_eq_absNorm_span]
  exact ⟨divisor_norm_le _ C hC.1 ((subsetGenerator_span_dvd C D E).trans (commonPart_dvd C D hC.1)),
    divisor_norm_le _ C hC.1 ((activeConductor_span_dvd C D).trans (commonPart_dvd C D hC.1))⟩

theorem fixed_pair_caps (η : Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) :
    (F.left.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 ∧
    (F.right.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
  have h:=original_factor_caps C D hC E
  have hb : fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2≤
      fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
    have hf:=fixedPresentationCost_pos.le
    nlinarith [mul_le_mul h.1 h.2 (sq_nonneg _) (Nat.cast_nonneg C.absNorm),
      mul_nonneg hf (Nat.cast_nonneg η.modulus.absNorm)]
  exact ⟨F.conductor_caps.1.trans hb,F.conductor_caps.2.trans hb⟩

def rayCost : ℝ := (Ideal.span {(12:O)}).absNorm*fixedPresentationCost

lemma rayCost_nonneg : 0≤rayCost :=
  mul_nonneg (Nat.cast_nonneg _) fixedPresentationCost_pos.le

theorem radical_once_cap (ρ υ : Character) (χ : RayCharacter) (p : O) (hp : p≠0) (k : ℕ)
    (hυ : υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p k) :
    (υ.modulus.absNorm:ℝ)≤rayCost*(ρ.modulus.absNorm:ℝ)*(Ideal.span {p}).absNorm := by
  have hP : (1:ℕ)≤(Ideal.span {p}).absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp))
  have ht : (if k=0 then 1 else (Ideal.span {p}).absNorm)≤(Ideal.span {p}).absNorm := by
    split_ifs <;> omega
  have hr:=CenteredMomentSecondRadicalBudget.child_modulus_bound ρ χ
  have hn : υ.modulus.absNorm≤
      (ρ.modulus.absNorm*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*(Ideal.span {p}).absNorm := by
    apply hυ.trans
    unfold radicalBound
    gcongr
  have hh : (υ.modulus.absNorm:ℝ)≤
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*(Ideal.span {p}).absNorm := by
    exact_mod_cast hn
  convert hh using 1 ; unfold rayCost fixedPresentationCost ; ring

theorem fixed_error_cap (η : Character) (C D : Ideal O) (hC : Supported C)
    (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter)
    (F : FixedPair η C D hC E ξ₁ ξ₂) (ρ υ : Character)
    (hρ : ρ=F.left ∨ ρ=F.right) (χ : RayCharacter) (p : O) (hp : p≠0) (k : ℕ)
    (hυ : υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p k) :
    (υ.modulus.absNorm:ℝ)≤(rayCost*fixedPresentationCost)*
      (η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2*(Ideal.span {p}).absNorm := by
  have hf:=fixed_pair_caps η C D hC E ξ₁ ξ₂ F
  have hr : (ρ.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2 := by
    rcases hρ with rfl|rfl
    · exact hf.1
    · exact hf.2
  apply (radical_once_cap ρ υ χ p hp k hυ).trans
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr rayCost_nonneg)
    (Nat.cast_nonneg (Ideal.span {p}).absNorm)
  convert hh using 1 ; ring

theorem eventually_caps (ε : ℝ) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀η:Character,∀(C D:Ideal O)(hC:Supported C),
    ∀(E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter)(F:FixedPair η C D hC E ξ₁ ξ₂),
    ∀q B:ℝ,(η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^B→
    (F.left.modulus.absNorm:ℝ)≤Z^(q+2*B+ε) ∧
    (F.right.modulus.absNorm:ℝ)≤Z^(q+2*B+ε) ∧
    ∀(ρ υ:Character), (ρ=F.left∨ρ=F.right)→∀(χ:RayCharacter)(p:O),p≠0→
    ∀(k:ℕ)(r:ℝ),υ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p k→
    ((Ideal.span {p}).absNorm:ℝ)≤Z^r→(υ.modulus.absNorm:ℝ)≤Z^(q+2*B+r+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε))
    (max fixedPresentationCost (rayCost*fixedPresentationCost))
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with Z hconst hZ
  refine ⟨hZ,?_⟩
  intro η C D hC E ξ₁ ξ₂ F q B hη hCcap
  have hz : 0<Z:=zero_lt_one.trans hZ
  have hm:=fixed_pair_caps η C D hC E ξ₁ ξ₂ F
  have hb : fixedPresentationCost*(η.modulus.absNorm:ℝ)*(C.absNorm:ℝ)^2≤Z^(q+2*B+ε) := by
    calc
      _≤Z^ε*Z^q*(Z^B)^2 := by
        gcongr
        exact (le_max_left _ _).trans hconst
      _=_ := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
  refine ⟨hm.1.trans hb,hm.2.trans hb,?_⟩
  intro ρ υ hρ χ p hp k r hυ hP
  apply (fixed_error_cap η C D hC E ξ₁ ξ₂ F ρ υ hρ χ p hp k hυ).trans
  calc
    _≤Z^ε*Z^q*(Z^B)^2*Z^r := by
      gcongr
      exact (le_max_right _ _).trans hconst
    _=_ := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring

end SevenEighths.CenteredMomentFirstSourceConductorCaps

end

end OAI
end OAIOriginalModule2173

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PlainGlobalBound
Source SHA256: 11166ba9fbebac6446435a10d79255483e5251654fa21c0d41be0b153c84335f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2174


namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
namespace SevenEighths.CenteredMomentPlainGlobalBound
open HeckeFamily HeckeDyadic

 theorem weighted_central (χ:Character)(W:ℝ→ℂ)(D freq C K T:ℝ)
    (hD:0<D)(hC:0≤C)(hK:0≤K)(hT:0≤T)
    (hm:∀t:ℝ,(1+|t|)^4*‖mellin W (((1/2:ℝ):ℂ)+t*I)‖≤C)
    (hs:∀t∈Icc (-T) T,‖series χ false (((1/2:ℝ):ℂ)+t*I+shift 0 freq)‖≤K*(1+|t|)^2):
    ‖∫t:ℝ in -T..T,integrand χ false W D 0 freq (((1/2:ℝ):ℂ)+t*I)‖≤C*K*Real.pi:=by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤T)]
  have hint:=integrable_inv_one_add_sq.const_mul (C*K)
  calc
    _≤∫t:ℝ in Ioc (-T) T,(C*K)*(1+t^2)⁻¹:=by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ false W D 0 freq hD]
      have hm':(1+|t|)^2*(‖mellin W (((1/2:ℝ):ℂ)+t*I)‖*(1+|t|)^2)≤C:=by
        nlinarith only [hm t]
      have hb:=CubicReflectionKernel.weighted_two_to_cauchy
        (mul_nonneg (norm_nonneg _) (sq_nonneg _)) t hm'
      have hh:=mul_le_mul_of_nonneg_left (hs t ⟨ht.1.le,ht.2⟩)
        (norm_nonneg (mellin W (((1/2:ℝ):ℂ)+t*I)))
      have hbK:=mul_le_mul_of_nonneg_right hb hK
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,zero_mul,
        sub_self,add_zero]
      norm_num only [add_zero,sub_self,Real.rpow_zero,mul_one]
      apply hh.trans
      convert hbK using 1 <;> ring
    _≤∫t:ℝ,(C*K)*(1+t^2)⁻¹:=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _=_:=by rw [integral_const_mul,integral_univ_inv_one_add_sq]

 theorem finite_strip_bound (χ:Character)(hχ:χ.residue≠1)(W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hWs:Function.support W⊆Icc a b)(hW:ContDiff ℝ ∞ W)
    (D freq C K:ℝ)(hD:1≤D)(hC:0≤C)(hK:0≤K)
    (hm:∀x∈Icc (1/2:ℝ) 2,∀t:ℝ,(1+|t|)^6*‖mellin W ((x:ℂ)+t*I)‖≤C)
    (hs:∀x∈Icc (1/2:ℝ) 2,∀t:ℝ,
      ‖series χ false ((x:ℂ)+t*I+shift 0 freq)‖≤K*(1+|t|)^2):
    ‖polynomial χ false W D 0 freq‖≤(1/(2*Real.pi))*
      (C*K*Real.pi+3*C*K+C*HeckeReciprocalBound.bound 2*Real.pi):=by
  have hD0:0<D:=zero_lt_one.trans_le hD
  have hm4 (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(t:ℝ):
      (1+|t|)^4*‖mellin W ((x:ℂ)+t*I)‖≤C:=by
    apply le_trans _ (hm x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · norm_num
  have hcent:=weighted_central χ W D freq C K D hD0 hC hK hD0.le
    (hm4 _ (by norm_num)) (fun t _=>hs _ (by norm_num) t)
  have hg (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(y:ℝ)(hy:|y|=D):
      ‖series χ false ((x:ℂ)+y*I+shift 0 freq)‖≤K*(1+D)^2:=by
    simpa only [hy] using hs x hx y
  have hlo:=horizontal_join_bound χ false W D 0 freq (1/2) 2 (-D) C (K*(1+D)^2) 4
    hD (by norm_num) hC (by positivity) (fun x hx=>hm4 x hx (-D))
    (fun x hx=>hg x hx (-D) (by simp [abs_of_nonneg hD0.le]))
  have hhi:=horizontal_join_bound χ false W D 0 freq (1/2) 2 D C (K*(1+D)^2) 4
    hD (by norm_num) hC (by positivity) (fun x hx=>hm4 x hx D)
    (fun x hx=>hg x hx D (abs_of_nonneg hD0.le))
  have htail:=absolute_tail_bound χ false W D 2 0 freq C D 4 hD0 (by norm_num) hC hD0.le
    (hm _ (by norm_num))
  have hpower:D^(3/2:ℝ)≤(1+D)^2:=by
    have hp:D^(3/2:ℝ)≤D^(2:ℝ):=Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
    rw [Real.rpow_two] at hp
    nlinarith
  have hratio:D^(3/2:ℝ)/(1+D)^2≤1:=(div_le_one (by positivity)).mpr hpower
  have hratio4:D^(3/2:ℝ)/(1+D)^4≤1:=by
    apply (div_le_one (by positivity)).mpr
    apply hpower.trans
    exact pow_le_pow_right₀ (by linarith : 1≤1+D) (by norm_num : 2≤4)
  have hj:(C*D^(3/2:ℝ)*(K*(1+D)^2)/(1+D)^4)*(3/2)≤(3/2)*C*K:=by
    have he:(C*D^(3/2:ℝ)*(K*(1+D)^2)/(1+D)^4)*(3/2)=
        ((3/2)*C*K)*(D^(3/2:ℝ)/(1+D)^2):=by field_simp
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hratio
  have ht:(C*D^(3/2:ℝ)*HeckeReciprocalBound.bound 2)/(1+D)^4*Real.pi≤
      C*HeckeReciprocalBound.bound 2*Real.pi:=by
    have hb:0≤HeckeReciprocalBound.bound 2:=tsum_nonneg (fun _=>norm_nonneg _)
    have he:(C*D^(3/2:ℝ)*HeckeReciprocalBound.bound 2)/(1+D)^4*Real.pi=
        (C*HeckeReciprocalBound.bound 2*Real.pi)*(D^(3/2:ℝ)/(1+D)^4):=by ring
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hratio4
  norm_num only [add_zero,show (2:ℝ)-1/2=3/2 by norm_num,show |(2:ℝ)-1/2|=3/2 by norm_num,
    abs_neg,abs_of_nonneg hD0.le] at hlo hhi htail
  rw [polynomial_finite_shift χ hχ false W a b ha hWs hW D 0 freq (1/2) 2 D hD0
    (by norm_num) hD0.le (by intro s hs h; cases h),norm_mul]
  have hnorm:‖(1/(2*Real.pi):ℂ)‖=(1/(2*Real.pi):ℝ):=by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left ((norm_four_sides _ _ _ _).trans ?_) (by positivity)
  simp only [ofReal_neg] at hlo
  linarith [hlo.trans hj,hhi.trans hj,htail.trans ht]

end SevenEighths.CenteredMomentPlainGlobalBound

end

end OAI
end OAIOriginalModule2174

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PlainGlobalActual
Source SHA256: 2303be8a4fe4fc71cc96f76445d16263616e03dce34ef54e952f2b4aa6c1788f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2175



namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace SevenEighths.CenteredMomentPlainGlobalActual
open HeckeFamily HeckeDyadic CenteredMomentPlainGlobalBound

 theorem global_polynomial_bound (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀W:SchwartzMap ℝ ℂ,Function.support (W:ℝ→ℂ)⊆Icc a b→
    ∀χ:Character,χ.residue≠1→∀D freq:ℝ,1≤D→
      ‖polynomial χ false W D 0 freq‖≤
        C*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (χ.modulus.absNorm:ℝ)*(3+|freq|)^2:=by
  obtain ⟨S,Cm,hCm,hm⟩:=profile_strip_decay a b ha (1/2) 2 6
  obtain ⟨Cg,hCg,hg⟩:=original_upper_strip (3/10) (by norm_num)
  let E:=HeckeReciprocalBound.bound 2
  have hE:0≤E:=tsum_nonneg (fun _=>norm_nonneg _)
  let C:ℝ:=Cm*(Cg*(Real.pi+3)+E*Real.pi)/(2*Real.pi)
  have hC:0<C:=div_pos (mul_pos hCm (add_pos_of_pos_of_nonneg
    (mul_pos hCg (by positivity)) (mul_nonneg hE Real.pi_pos.le))) (by positivity)
  refine ⟨S,C,hC,?_⟩
  intro W hWs χ hχ D freq hD
  let Q:ℝ:=χ.modulus.absNorm
  let V:ℝ:=3+|freq|
  let B:ℝ:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB:0≤B:=apply_nonneg _ _
  have hQ:1≤Q:=by
    dsimp [Q]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hV:1≤V:=by dsimp [V]; linarith [abs_nonneg freq]
  have hQ0:0≤Q:=zero_le_one.trans hQ
  have hrad:((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)≤Q:=radical_norm_le_modulus χ
  have hrad0:0≤((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ):=Nat.cast_nonneg _
  have hcost:Q^(3/5:ℝ)*((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)^((1/10+(3/10)):ℝ)≤Q:=by
    calc
      _≤Q^(3/5:ℝ)*Q^((1/10+(3/10)):ℝ):=mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hrad0 hrad (by norm_num)) (Real.rpow_nonneg hQ0 _)
      _=Q:=by rw [←Real.rpow_add (zero_lt_one.trans_le hQ)]; norm_num
  have hgrowth (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(t:ℝ):
      ‖series χ false ((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)‖≤(Cg*Q*V^2)*(1+|t|)^2:=by
    have hs:-(1/10:ℝ)≤(((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)).re:=by simp [HeckeDyadic.shift]; linarith [hx.1]
    have hh:=hg χ hχ _ hs
    have him:(((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)).im=t-freq:=by simp [HeckeDyadic.shift,sub_eq_add_neg]
    rw [him] at hh
    have ht:3+|t-freq|≤V*(1+|t|):=by
      dsimp [V]
      have hab:=abs_sub t freq
      nlinarith [abs_nonneg t,abs_nonneg freq,mul_nonneg (abs_nonneg t) (abs_nonneg freq)]
    apply hh.trans
    change Cg*Q^(3/5:ℝ)*((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)^((1/10+(3/10)):ℝ)*
      (3+|t-freq|)^2≤_
    have hc:=mul_le_mul (mul_le_mul_of_nonneg_left hcost hCg.le)
      (pow_le_pow_left₀ (by positivity) ht 2) (by positivity) (mul_nonneg hCg.le hQ0)
    convert hc using 1 <;> ring
  have hb:=finite_strip_bound χ hχ W a b ha hWs (W.smooth ⊤) D freq (Cm*B) (Cg*Q*V^2)
    hD (mul_nonneg hCm.le hB) (by positivity) (hm W hWs) hgrowth
  have hQV:1≤Q*V^2:=one_le_mul_of_one_le_of_one_le hQ (one_le_pow₀ hV)
  have he:E≤E*(Q*V^2):=le_mul_of_one_le_right hE hQV
  apply hb.trans
  dsimp only [C]
  change _≤Cm*(Cg*(Real.pi+3)+E*Real.pi)/(2*Real.pi)*B*Q*V^2
  have hCe: Cm*B*E*Real.pi≤Cm*B*(E*(Q*V^2))*Real.pi:=by gcongr
  dsimp only [E] at hCe ⊢
  calc
    _≤(1/(2*Real.pi))*
      (Cm*B*(Cg*Q*V^2)*Real.pi+3*(Cm*B)*(Cg*Q*V^2)+
       Cm*B*(HeckeReciprocalBound.bound 2*(Q*V^2))*Real.pi):=
      mul_le_mul_of_nonneg_left (add_le_add_right hCe _) (by positivity)
    _=_:=by ring

end SevenEighths.CenteredMomentPlainGlobalActual

end

end OAI
end OAIOriginalModule2175

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimeGlobal
Source SHA256: 0a68a36818ffd0823cee6c3e48c322c6e652a3fa4e386a4c9300dfb467ae02e3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2176



namespace OAI

noncomputable section
open scoped Classical ContDiff
open Set
namespace SevenEighths.CenteredMomentPrimeGlobal
open HeckeFamily HeckePrimeRay HeckeZeroSupremum

lemma zeroMaximum_le_beta {ι : Type*} [Fintype ι]
    (χ : ι→Character) (hχ : ∀i,(χ i).residue≠1) (T : ℝ)
    (hbeta : (51/100:ℝ)≤beta) :
    HeckeDetectorZeros.zeroMaximum χ hχ T≤beta := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl|hx
  · exact hbeta
  · obtain ⟨⟨i,s⟩,hs,rfl⟩ := Finset.mem_image.mp hx
    have hz := (HeckeDetectorZeros.mem_familyZeros χ hχ T i s).mp hs
    exact zero_re_le_beta (χ i) (by linarith [hz.1]) (Or.inr (hχ i)) hz.2.2.2

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem ray_prime_global_squared (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmax τ ε e slack η σmin σmax κ : ℝ)
    (hR : 0≤R) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε) (he : 0<e)
    (he' : e<1/1000) (hslack : 0<slack) (hη : 0≤η)
    (hbudget : 8*e*R+slack≤ε) (hbeta : (51/100:ℝ)≤beta)
    (hκ : 2*beta-1≤κ) :
    ∃ C : ℝ,0<C ∧ ∀ Z d : ℝ,1≤Z → 0≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀ (χ : Character) (_hn : ∀θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (i : ℕ),
    ∀ r σ freq : ℝ,0≤r → r≤R → σmin≤σ → σ≤σmax →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log ((Z^d)^r) →
      (∀θ : RayQuotient.Characters M H,
        (twistedFamily M H hH χ θ).modulus.absNorm≤Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ →
      (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
      ‖rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq‖^2≤
        C*(Z^d)^(κ*r+2*ε) := by
  obtain ⟨C,hC,hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    R dmax τ ε e slack η σmin σmax hR hdmax hτ hε he he' hslack hη hbudget
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro Z d hZ hd hdmax hU hT χ hn i r σ freq hr hrR hσ hσmax hlarge hQ hf ht
  have hmax := zeroMaximum_le_beta (twistedFamily M H hH χ) hn
    (3*(i+1:ℕ)*Z^τ) hbeta
  have hb := hbound Z d hZ hd hdmax hU hT χ hn beta i hbeta beta_le_one
    (by linarith) r σ freq hr hrR hσ hσmax hlarge hQ hf ht
  have hUp : 0<Z^d := by linarith
  have hp : ((Z^d)^((beta-1/2)*r+ε))^2 = (Z^d)^(2*((beta-1/2)*r+ε)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hUp.le]
    congr 1
    ring
  calc
    _≤(C*(Z^d)^((beta-1/2)*r+ε))^2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _=C^2*(Z^d)^(2*((beta-1/2)*r+ε)) := by rw [mul_pow,hp]
    _≤C^2*(Z^d)^(κ*r+2*ε) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤Z^d)
        (by nlinarith [mul_le_mul_of_nonneg_right hκ hr])) (sq_nonneg _)

end SevenEighths.CenteredMomentPrimeGlobal

end

end OAI
end OAIOriginalModule2176

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimeHeight
Source SHA256: f3a8dc33493a7b9950a2de66835cf13b57de0e86f7e893487c1c0a9c941fb0cc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2177



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.CenteredMomentPrimeHeight
open HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDyadic HeckeZeroSupremum
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem ray_prime_bounded_scale (W : ℝ→ℂ) (A B lo hi D : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : Continuous W) (_hD : 1≤D) :
    ∃C : ℝ,0<C ∧ ∀(χ : Character)(P σ freq : ℝ),1≤P → P≤D → lo≤σ → σ≤hi →
      ‖rayPrimePolynomial M H χ W B P σ freq‖≤C := by
  obtain ⟨Cw,hCw,hprofile⟩ := fixed_profile_norm_bound W hW A B lo hi hA
  let S := annulusSet B D
  refine ⟨((S.card:ℝ)+1)*Cw,by positivity,?_⟩
  intro χ P σ freq hP hPD hσ hσhi
  have hp : 0<P := zero_lt_one.trans_le hP
  have hsub : (annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H)⊆S := by
    intro I hI
    have hi := ConcretePrimeRowBridge.mem_idealsUpTo.mp (Finset.mem_filter.mp hI).1
    apply ConcretePrimeRowBridge.mem_idealsUpTo.mpr
    exact ⟨hi.1,hi.2.trans (Nat.floor_mono (mul_le_mul_of_nonneg_left hPD (le_trans zero_le_one (le_max_left _ _))))⟩
  have hn (I : Ideal O) : ‖idealCoeff χ I*annularWeight W P σ freq I‖≤Cw := by
    have hc := idealCoeff_norm_le_one χ I
    apply (show ‖idealCoeff χ I*annularWeight W P σ freq I‖≤‖annularWeight W P σ freq I‖ by
      rw [norm_mul];exact mul_le_of_le_one_left (norm_nonneg _) hc).trans
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simp [annularWeight,hz,hCw.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hA.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσ,hσhi⟩ _ hs
  have hpow : ‖(P:ℂ)^(-(1/2:ℂ))‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    norm_num only [Complex.neg_re,show ((1/2:ℂ).re)=1/2 by norm_num]
    exact Real.rpow_le_one_of_one_le_of_nonpos hP (by norm_num)
  unfold rayPrimePolynomial
  rw [norm_mul]
  calc
    _ ≤ ‖∑ I∈(annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H),
        idealCoeff χ I*annularWeight W P σ freq I‖ := mul_le_of_le_one_left (norm_nonneg _) hpow
    _ ≤ ∑ I∈(annulusSet B P).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H),Cw :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun I _=>hn I))
    _ ≤ ∑ _I∈S,Cw := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>hCw.le)
    _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul];nlinarith

lemma lifted_scale_power (Z T D P κ loss : ℝ) (hZ : 0<Z) (hT : 0<T) (hD : D≠0)
    (hU : 1<(Z*T)^D) (hP : 0<P) :
    ((Z*T)^D)^(κ*Real.logb ((Z*T)^D) P+2*(loss/(2*D)))=
      P^κ*Z^loss*T^loss := by
  have hu : 0<(Z*T)^D := zero_lt_one.trans hU
  rw [Real.rpow_add hu]
  have hs : ((Z*T)^D)^(κ*Real.logb ((Z*T)^D) P)=P^κ := by
    rw [mul_comm κ,Real.rpow_mul hu.le,Real.rpow_logb hu (ne_of_gt hU) hP]
  rw [hs,←Real.rpow_mul (mul_pos hZ hT).le]
  have he : D*(2*(loss/(2*D)))=loss := by field_simp
  rw [he,Real.mul_rpow hZ.le hT.le]
  ring

theorem ray_prime_all_height_large (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (_hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧ ∀ Z P : ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀χ : Character,(χ.modulus.absNorm:ℝ)≤Z^Lmod →
      (∀θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).residue≠1) →
    ∀σ freq : ℝ,lo≤σ → σ≤hi →
      2*(|Real.log A|+|Real.log B|)+1≤Real.log P →
      ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C*P^κ*Z^loss*(3+|freq|)^loss := by
  let d := max Lmod Lslot+2
  have hd : 0<d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hd1 : 1≤d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hmd : Lmod+1≤d := by dsimp [d];have := le_max_left Lmod Lslot;linarith
  have hsd : Lslot≤d := by dsimp [d];have := le_max_right Lmod Lslot;linarith
  let eps := loss/(2*d)
  have heps : 0<eps := by dsimp [eps];positivity
  let e := min (eps/32) (1/2000)
  have he : 0<e := lt_min (by positivity) (by norm_num)
  have he' : e<1/1000 := (min_le_right _ _).trans_lt (by norm_num)
  have hbudget : 8*e*1+eps/2≤eps := by have := min_le_left (eps/32) (1/2000);dsimp [e];linarith
  obtain ⟨C,hC,hbound⟩ := CenteredMomentPrimeGlobal.ray_prime_global_squared M H hH W A B hA hWs hW
    1 d 1 eps e (eps/2) (4/d) lo hi κ (by norm_num) hd.le (by norm_num) heps he he'
    (by positivity) (by positivity) hbudget hbeta hκ
  let Z₀ := max 2 (M.absNorm:ℝ)
  refine ⟨C,Z₀,hC,lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_left _ _),?_⟩
  intro Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi hlarge
  have hz2 : 2≤Z := (le_max_left _ _).trans hZ
  have hz : 0<Z := by linarith
  have hz1 : 1≤Z := by linarith
  have hMZ : (M.absNorm:ℝ)≤Z := (le_max_right _ _).trans hZ
  let T := 3+|freq|
  let Zt := Z*T
  let U := Zt^d
  have hT3 : 3≤T := by dsimp [T];linarith [abs_nonneg freq]
  have hT : 0<T := by linarith
  have hzt6 : 6≤Zt := by dsimp [Zt];nlinarith
  have hzt : 0<Zt := by linarith
  have hzt1 : 1≤Zt := by linarith
  have hZzt : Z≤Zt := by dsimp [Zt];nlinarith
  have hTzt : T≤Zt := by dsimp [Zt];nlinarith
  have hztU : Zt≤U := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hzt1 hd1
  have hU : 1<U := by linarith
  have hUp : 0<U := by linarith
  have hPU : P≤U := hPcap.trans ((Real.rpow_le_rpow_of_exponent_le hz1 hsd).trans
    (Real.rpow_le_rpow hz.le hZzt hd.le))
  let r := Real.logb U P
  have hr : 0≤r := Real.logb_nonneg hU hP
  have hr1 : r≤1 := (Real.logb_le_iff_le_rpow hU (zero_lt_one.trans_le hP)).mpr
    (by simpa only [Real.rpow_one] using hPU)
  have hPr : U^r=P := Real.rpow_logb hUp (ne_of_gt hU) (zero_lt_one.trans_le hP)
  have hQ (θ : RayQuotient.Characters M H) : ((twistedFamily M H hH χ θ).modulus.absNorm:ℝ)≤U := by
    have ht : ((twistedFamily M H hH χ θ).modulus.absNorm:ℝ)≤(χ.modulus.absNorm:ℝ)*M.absNorm := by
      exact_mod_cast HeckePrimeScale.twisted_modulus_bound M H hH χ θ
    apply ht.trans
    calc
      _ ≤ Z^Lmod*Z := mul_le_mul hχ hMZ (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
      _ = Z^(Lmod+1) := by rw [Real.rpow_add hz,Real.rpow_one]
      _ ≤ Z^d := Real.rpow_le_rpow_of_exponent_le hz1 hmd
      _ ≤ U := Real.rpow_le_rpow hz.le hZzt hd.le
  have hheight : (3+2*Zt)^2≤U^(4/d) := by
    have heq : U^(4/d)=Zt^(4:ℝ) := by
      dsimp [U]
      rw [←Real.rpow_mul hzt.le]
      congr 1
      field_simp
    rw [heq,Real.rpow_ofNat]
    have hb : 3+2*Zt≤Zt^2 := by nlinarith
    calc
      _ ≤ (Zt^2)^2 := pow_le_pow_left₀ (by positivity) hb 2
      _ = _ := by ring
  have hb := hbound Zt d hzt1 hd.le le_rfl (by linarith : 2≤Zt^d)
    (by simpa only [Real.rpow_one] using (show (2:ℝ)<Zt by linarith)) χ hn 0 r σ freq hr hr1 hσ hσhi
    (by change _≤Real.log (U^r);rw [hPr];exact hlarge) hQ
    (by norm_num only [Nat.mul_zero,Nat.zero_add,Nat.cast_ofNat,Real.rpow_one];dsimp [T] at hTzt;linarith)
    (by simpa only [Nat.mul_zero,Nat.zero_add,Nat.cast_ofNat,Real.rpow_one] using hheight)
  change ‖rayPrimePolynomial M H χ W B (U^r) σ freq‖^2≤C*U^(κ*r+2*eps) at hb
  rw [hPr] at hb
  apply hb.trans_eq
  dsimp only [U,Zt,r,eps,T]
  rw [lifted_scale_power Z (3+|freq|) d P κ loss hz hT hd.ne' hU (zero_lt_one.trans_le hP)]
  ring

theorem ray_prime_all_height_squared (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧ ∀ Z P : ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀χ : Character,(χ.modulus.absNorm:ℝ)≤Z^Lmod →
      (∀θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).residue≠1) →
    ∀σ freq : ℝ,lo≤σ → σ≤hi →
      ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C*(1+|freq|)^degree*Z^loss*P^κ := by
  obtain ⟨Cbig,Z₀,hCbig,hZ₀,hbig⟩ := ray_prime_all_height_large M H hH W A B hA hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  let K := 2*(|Real.log A|+|Real.log B|)+1
  have hK : 0≤K := by dsimp [K];positivity
  obtain ⟨Csmall,hCs,hsmall⟩ := ray_prime_bounded_scale M H W A B lo hi (Real.exp K) hA hWs hW.continuous
    (Real.one_le_exp hK)
  let degree := ⌈loss⌉₊
  let C0 := Cbig+Csmall^2
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0*(3:ℝ)^degree,Z₀,by positivity,hZ₀,?_⟩
  intro Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi
  have hz1 : 1≤Z := hZ₀.le.trans hZ
  have hκ0 : 0≤κ := by linarith
  have hpκ : 1≤P^κ := Real.one_le_rpow hP hκ0
  have hzloss : 1≤Z^loss := Real.one_le_rpow hz1 hloss.le
  have htbase : 1≤3+|freq| := by linarith [abs_nonneg freq]
  have htloss : 1≤(3+|freq|)^loss := Real.one_le_rpow htbase hloss.le
  have hbase : ‖rayPrimePolynomial M H χ W B P σ freq‖^2≤C0*P^κ*Z^loss*(3+|freq|)^loss := by
    by_cases hlarge : K≤Real.log P
    · exact (hbig Z P hZ hP hPcap χ hχ hn σ freq hσ hσhi hlarge).trans
        (by dsimp [C0];gcongr; nlinarith [sq_nonneg Csmall])
    · have hPD : P≤Real.exp K := by
        have he := Real.exp_le_exp.mpr (le_of_not_ge hlarge)
        simpa only [Real.exp_log (zero_lt_one.trans_le hP)] using he
      have hb := pow_le_pow_left₀ (norm_nonneg _) (hsmall χ P σ freq hP hPD hσ hσhi) 2
      apply hb.trans
      calc
        Csmall^2 ≤ C0 := by dsimp [C0];linarith
        _ ≤ C0*P^κ := le_mul_of_one_le_right hC0.le hpκ
        _ ≤ C0*P^κ*Z^loss := le_mul_of_one_le_right (by positivity) hzloss
        _ ≤ _ := le_mul_of_one_le_right (by positivity) htloss
  have hheight : (3+|freq|)^loss≤(3:ℝ)^degree*(1+|freq|)^degree := by
    calc
      _ ≤ (3+|freq|)^(degree:ℝ) := Real.rpow_le_rpow_of_exponent_le htbase (Nat.le_ceil loss)
      _ = (3+|freq|)^degree := Real.rpow_natCast _ _
      _ ≤ (3*(1+|freq|))^degree := pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg freq]) _
      _ = _ := mul_pow _ _ _
  apply hbase.trans
  calc
    _ ≤ C0*P^κ*Z^loss*((3:ℝ)^degree*(1+|freq|)^degree) :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentPrimeHeight
end

end OAI
end OAIOriginalModule2177

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RayNonprincipal
Source SHA256: 087a295b1eb697b449ab398e2254fd295ff23392e813fe545980712cf213df47
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2178




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRayNonprincipal
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion HeckePrimeRay
local notation "O" => HeckeFamily.O

theorem product_principal_descent (χ θ:Character)
    (hp:(χ.product θ).residue=1) :
    FiniteConductor.FactorsThroughIdeal χ.residue
      (θ.modulus.map (Ideal.Quotient.mk χ.modulus)) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  rw [FiniteConductor.factorsThroughIdeal_iff]
  intro u hu
  obtain ⟨q,hq,hqu⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk χ.modulus) Ideal.Quotient.mk_surjective).mp hu
  let a:O := 1+q
  have ha:Ideal.Quotient.mk χ.modulus a=(u:O⧸χ.modulus) := by
    dsimp [a]; rw [map_add,map_one,hqu]; ring
  have hθa:Ideal.Quotient.mk θ.modulus a=1 := by
    simp only [a,map_add,map_one,Ideal.Quotient.eq_zero_iff_mem.mpr hq,add_zero]
  have hcχ:IsCoprime (Ideal.span {a}) χ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (ha ▸ u.isUnit)
  have hcθ:IsCoprime (Ideal.span {a}) θ.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (hθa ▸ isUnit_one)
  have hcp:IsCoprime (Ideal.span {a}) (χ.product θ).modulus :=
    (hcχ.mul_right hcθ).of_isCoprime_of_dvd_right
      (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)
  have hv:elementCoeff (χ.product θ) a=1 := by
    change (χ.product θ).residue _=1
    rw [hp]
    exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hcp)
  rw [elementCoeff_product] at hv
  change χ.residue (Ideal.Quotient.mk χ.modulus a)*
    θ.residue (Ideal.Quotient.mk θ.modulus a)=1 at hv
  simpa only [ha,hθa,map_one,mul_one] using hv

theorem product_principal_inducing (χ θ:Character)
    (hp:(χ.product θ).residue=1) :
    ∃ψ:Character, FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      θ.modulus≤ψ.modulus ∧ InducedBy χ ψ :=
  HeckeMaskDescent.exists_primitive_above χ θ.modulus
    (product_principal_descent χ θ hp)

theorem actual_row_twist_nonprincipal (η χ θ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hQ:Q≤θ.modulus) (hex:¬FixedInducingRow η Q m A z) :
    (χ.product θ).residue≠1 := by
  intro hp
  obtain ⟨ψ,hψ,hmod,hind⟩ := product_principal_inducing χ θ hp
  exact hex ⟨χ,ψ,hψ,hind,hQ.trans hmod,hrow⟩

variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

theorem all_ray_twists_nonprincipal (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hQ:Q≤M) (hex:¬FixedInducingRow η Q m A z) :
    ∀θ:RayQuotient.Characters M H, (twistedFamily M H hH χ θ).residue≠1 := by
  intro θ
  exact actual_row_twist_nonprincipal η χ (HeckeRayQuotient.character M H hH θ)
    Q m A z hrow hQ hex

end SevenEighths.CenteredMomentRayNonprincipal

end

end OAI
end OAIOriginalModule2178

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectedProfileMeasure
Source SHA256: 5f90497567035bbdc06fa40e714c310507947e909ab73f591544443f52e54bf6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2179





namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedProfileMeasure
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem actual_profile_separation (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀y : ℝ,V y*paperRadialFourier (CompletedHeight.normTwistedSource W t)
          (s*Real.exp y)=∫v : ℝ,(V y*logPhase v y)*density v) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*(1+‖t‖)^n ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*(1+‖t‖)^n) := by
  obtain ⟨C,hC,hsep⟩ := LocalLogFourier.coupled_positive_log_separation_linear_constant
    (fun _ : Unit=>V) (fun _=>1) (fun _=>M) (fun _=>hM) (fun _=>hV) A J
  obtain ⟨n,hn⟩ := CenteredMomentComparisonReflection.reflected_profile_height_control
    a b ha A (J+(volume : Measure ℝ).integrablePower)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨(C+1)*D,by positivity,?_⟩
  intro t s hs0
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have hF : ContDiffOn ℝ ∞ (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (Set.Ioi 0) := by
    rw [←he]
    exact paperRadialFourier_contDiffOn _
  obtain ⟨density,hid,hi,hm,hp⟩ := hsep _ hF (D*(1+‖t‖)^n) (by positivity)
    (fun j hj x hx=>hDb t j hj x hx.le) s hs0
  refine ⟨density,?_,hi,hm.trans ?_,fun v=>(hp v).trans ?_⟩
  · intro y
    simpa using hid (fun _ : Unit=>y)
  · nlinarith [pow_nonneg (show 0≤1+‖t‖ by positivity) n]
  · nlinarith [pow_nonneg (show 0≤1+‖t‖ by positivity) n]

theorem row_density_energy {ι : Type*} [Fintype ι]
    (density φ : ι→ℝ→ℂ) (rho : ℝ→ℝ) (w : ℝ→ℝ)
    (hrho : ∀v,0<rho v) (hw : ∀v,0<w v)
    (hpoint : ∀i v,‖density i v‖≤rho v)
    (hint : ∀i,Integrable (fun v=>density i v*φ i v))
    (hmeasure : Integrable (fun v=>rho v*w v))
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀v,(∑i,‖φ i v‖^2)≤E*(w v)^2) :
    (∑i,‖∫v : ℝ,density i v*φ i v‖^2)≤E*(∫v : ℝ,rho v*w v)^2 := by
  let B (v : ℝ) : ℂ := (rho v*w v:ℝ)
  let F (i : ι) (v : ℝ) : ℂ := density i v/B v*φ i v
  have hB0 (v : ℝ) : B v≠0 := Complex.ofReal_ne_zero.mpr (mul_pos (hrho v) (hw v)).ne'
  have hBn (v : ℝ) : ‖B v‖=rho v*w v := by
    exact Complex.norm_of_nonneg (mul_pos (hrho v) (hw v)).le
  have he (i : ι) (v : ℝ) : B v*F i v=density i v*φ i v := by
    dsimp only [F]
    field_simp [hB0 v]
  have hFn (i : ι) (v : ℝ) : ‖F i v‖≤‖φ i v‖/w v := by
    dsimp only [F]
    rw [norm_mul,norm_div,hBn]
    calc
      _≤(rho v/(rho v*w v))*‖φ i v‖ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hpoint i v) (mul_pos (hrho v) (hw v)).le) (norm_nonneg _)
      _=_ := by field_simp [(hrho v).ne', (hw v).ne']
  have hb (v : ℝ) : (∑i,‖F i v‖^2)≤E := by
    calc
      _≤∑i,(‖φ i v‖/w v)^2 := Finset.sum_le_sum (fun i _=>
        pow_le_pow_left₀ (norm_nonneg _) (hFn i v) 2)
      _=(∑i,‖φ i v‖^2)/(w v)^2 := by simp only [div_pow,Finset.sum_div]
      _≤E := (div_le_iff₀ (sq_pos_of_pos (hw v))).mpr (henergy v)
  have hh := CompletedGauss.finite_integral_energy_bound B F E hE
    (by simpa only [hBn] using hmeasure) (fun i=>by simpa only [he] using hint i) hb
  simpa only [he,hBn] using hh

theorem row_density_energy_two {ι : Type*} [Fintype ι]
    (b₁ b₂ : ι→ℝ→ℂ) (φ : ι→ℝ→ℝ→ℂ) (rho₁ rho₂ w₁ w₂ : ℝ→ℝ)
    (hr₁ : ∀v,0<rho₁ v) (hr₂ : ∀v,0<rho₂ v)
    (hw₁ : ∀v,0<w₁ v) (hw₂ : ∀v,0<w₂ v)
    (hp₁ : ∀i v,‖b₁ i v‖≤rho₁ v) (hp₂ : ∀i v,‖b₂ i v‖≤rho₂ v)
    (hi₁ : ∀i,Integrable (fun x=>b₁ i x*(∫y : ℝ,b₂ i y*φ i x y)))
    (hi₂ : ∀i x,Integrable (fun y=>b₂ i y*φ i x y))
    (hm₁ : Integrable (fun x=>rho₁ x*w₁ x))
    (hm₂ : Integrable (fun y=>rho₂ y*w₂ y))
    (E : ℝ) (hE : 0≤E)
    (hb : ∀x y,(∑i,‖φ i x y‖^2)≤E*(w₁ x)^2*(w₂ y)^2) :
    (∑i,‖∫x : ℝ,b₁ i x*(∫y : ℝ,b₂ i y*φ i x y)‖^2)≤
      E*(∫x : ℝ,rho₁ x*w₁ x)^2*(∫y : ℝ,rho₂ y*w₂ y)^2 := by
  have hh := row_density_energy b₁ (fun i x=>∫y : ℝ,b₂ i y*φ i x y)
    rho₁ w₁ hr₁ hw₁ hp₁ hi₁ hm₁ (E*(∫y : ℝ,rho₂ y*w₂ y)^2) (by positivity) (by
      intro x
      have ht := row_density_energy b₂ (fun i y=>φ i x y) rho₂ w₂ hr₂ hw₂
        hp₂ (fun i=>hi₂ i x) hm₂ (E*(w₁ x)^2) (by positivity) (hb x)
      exact ht.trans_eq (by ring))
  exact hh.trans_eq (by ring)

def logWindow (V : ℝ→ℂ) (x : ℝ) : ℂ := if 0<x then V (Real.log x) else 0

theorem finite_annular_separation (V F : ℝ→ℂ) (s X : ℝ) (hX : 0<X)
    (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v)
    (η : Character) (S : Finset (Ideal O))
    (hS : ∀I∈S,I≠0)
    (hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S) :
    HeckeDyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  have hnorm (I : Ideal O) (hI : I∈S) : 0<(I.absNorm:ℝ)/X := by
    apply div_pos _ hX
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
  have hi (I : Ideal O) : Integrable (fun v : ℝ=>
      density v*(HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    have ht := ((density.integrable (μ:=volume)).mul_bdd
      (logPhase_continuous_left (Real.log ((I.absNorm:ℝ)/X))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun v=>le_of_eq (logPhase_norm v _)))).mul_const
        (HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X))
    apply ht.congr
    filter_upwards [] with v
    ring
  have hp (v : ℝ) : HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
  rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 0 S
    (fun I hI h=>hc I hI (mul_ne_zero_iff.mp h).1)]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_self,neg_zero,
    Complex.cpow_zero,mul_one]
  simp_rw [hp]
  have he : (fun v : ℝ=>density v*((X:ℂ)^(-(1/2:ℂ))*
      ∑I∈S,HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) =
      (fun v=>(X:ℂ)^(-(1/2:ℂ))*∑I∈S,density v*(HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    funext v
    rw [←Finset.mul_sum]
    ring
  rw [he,integral_const_mul,integral_finsetSum S (fun I _=>hi I)]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hh := hsep (Real.log ((I.absNorm:ℝ)/X))
  rw [Real.exp_log (hnorm I hI)] at hh
  simp only [logWindow,ite_eq_left (hnorm I hI)]
  rw [hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  ring

lemma logWindow_support (V : ℝ→ℂ) (M : ℝ)
    (hV : ∀y,V y≠0 → |y|≤M) :
    Function.support (logWindow V)⊆Set.Icc (Real.exp (-M)) (Real.exp M) := by
  intro x hx
  change logWindow V x≠0 at hx
  by_cases hxp : 0<x
  · have hv : V (Real.log x)≠0 := by simpa only [logWindow,ite_eq_left hxp] using hx
    have hh := abs_le.mp (hV _ hv)
    constructor
    · simpa only [Real.exp_log hxp] using Real.exp_le_exp.mpr hh.1
    · simpa only [Real.exp_log hxp] using Real.exp_le_exp.mpr hh.2
  · exact False.elim (hx (by simp only [logWindow,ite_eq_right hxp]))

theorem plain_annular_separation (V F : ℝ→ℂ) (M s X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v) (η : Character) :
    HeckeDyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  exact finite_annular_separation V F s X hX density hsep η S hs hc

theorem actual_plain_profile_measure (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀hs : Function.support W⊆Set.Icc a b,
      ∀hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t s : ℝ,0<s →
      ∃density : 𝓢(ℝ,ℂ),
        (∀(η : Character)(X : ℝ),0<X →
          HeckeDyadic.polynomial η false (fun x=>logWindow V x*
            paperRadialFourier (CompletedHeight.normTwistedSource W t) (s*x)) X 0 0 =
          ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
        Integrable (fun v : ℝ=>(1+‖v‖)^J*‖density v‖) ∧
        (1+s)^A*(∫v : ℝ,(1+‖v‖)^J*‖density v‖)≤C*(1+‖t‖)^n ∧
        (∀v : ℝ,(1+s)^A*(1+‖v‖)^J*‖density v‖≤C*(1+‖t‖)^n) := by
  obtain ⟨n,hn⟩ := actual_profile_separation V M a b hM hV ha A J
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro t s hs0
  obtain ⟨density,hsep,hi,hm,hp⟩ := hb t s hs0
  exact ⟨density,(fun η X hX=>plain_annular_separation V _ M s X hX hV density hsep η),hi,hm,hp⟩

end SevenEighths.CenteredMomentReflectedProfileMeasure

end

end OAI
end OAIOriginalModule2179

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectedPairEnergy
Source SHA256: 6441ba108ab49e9e276d70eae5ee5a9f310ca5a37b0b28b88e236c497ba0148b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2180


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedPairEnergy
open HeckeFamily FourierBridge CenteredMomentReflectedProfileMeasure
local notation "O" => HeckeFamily.O

lemma plain_frequency_control (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) :
    Continuous (fun v : ℝ=>HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
    ∃K : ℝ,∀v : ℝ,‖HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)‖≤K := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  have he (v : ℝ) : HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hs I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
  constructor
  · simp_rw [he]
    exact continuous_const.mul (continuous_finsetSum S (fun I _=>
      continuous_const.mul (logPhase_continuous_left _)))
  · refine ⟨‖(X:ℂ)^(-(1/2:ℂ))‖*∑I∈S,
      ‖HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)‖,?_⟩
    intro v
    rw [he,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul,logPhase_norm,mul_one]

lemma plain_density_integrable (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) (density : 𝓢(ℝ,ℂ)) :
    Integrable (fun v : ℝ=>density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) := by
  obtain ⟨hc,K,hK⟩ := plain_frequency_control V M X hX hV η
  exact (density.integrable (μ:=volume)).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hK)

theorem paired_profile_energy {ι : Type*} [Fintype ι]
    (χ ψ : ι→Character) (P : ι→ℂ) (V₁ V₂ : ℝ→ℂ) (M₁ M₂ : ℝ)
    (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁) (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (F₁ F₂ : ι→ℝ→ℂ) (s₁ s₂ X₁ X₂ : ι→ℝ)
    (hX₁ : ∀i,0<X₁ i) (hX₂ : ∀i,0<X₂ i)
    (b₁ b₂ : ι→𝓢(ℝ,ℂ))
    (hsep₁ : ∀i y,V₁ y*F₁ i (s₁ i*Real.exp y)=
      ∫v : ℝ,(V₁ y*logPhase v y)*b₁ i v)
    (hsep₂ : ∀i y,V₂ y*F₂ i (s₂ i*Real.exp y)=
      ∫v : ℝ,(V₂ y*logPhase v y)*b₂ i v)
    (rho₁ rho₂ w₁ w₂ : ℝ→ℝ)
    (hr₁ : ∀v,0<rho₁ v) (hr₂ : ∀v,0<rho₂ v)
    (hw₁ : ∀v,0<w₁ v) (hw₂ : ∀v,0<w₂ v)
    (hp₁ : ∀i v,‖b₁ i v‖≤rho₁ v) (hp₂ : ∀i v,‖b₂ i v‖≤rho₂ v)
    (hm₁ : Integrable (fun x=>rho₁ x*w₁ x))
    (hm₂ : Integrable (fun y=>rho₂ y*w₂ y))
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀x y,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)*
      HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)*P i‖^2)≤
        E*(w₁ x)^2*(w₂ y)^2) :
    (∑i,‖HeckeDyadic.polynomial (χ i) false (fun x=>logWindow V₁ x*F₁ i (s₁ i*x)) (X₁ i) 0 0 *
      HeckeDyadic.polynomial (ψ i) false (fun x=>logWindow V₂ x*F₂ i (s₂ i*x)) (X₂ i) 0 0 * P i‖^2)≤
      E*(∫x : ℝ,rho₁ x*w₁ x)^2*(∫y : ℝ,rho₂ y*w₂ y)^2 := by
  let T₁ (i : ι) (x : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)
  let T₂ (i : ι) (y : ℝ) := HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)
  let φ (i : ι) (x y : ℝ) := T₁ i x*T₂ i y*P i
  have hi₂ (i : ι) (x : ℝ) : Integrable (fun y=>b₂ i y*φ i x y) := by
    have hi := (plain_density_integrable V₂ M₂ (X₂ i) (hX₂ i) hV₂ (ψ i) (b₂ i)).const_mul (T₁ i x*P i)
    apply hi.congr
    filter_upwards [] with y
    dsimp [φ,T₂]
    ring
  have he₂ (i : ι) (x : ℝ) : (∫y : ℝ,b₂ i y*φ i x y)=
      T₁ i x*(∫y : ℝ,b₂ i y*T₂ i y)*P i := by
    rw [←integral_const_mul,←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [φ]
    ring
  have hi₁ (i : ι) : Integrable (fun x=>b₁ i x*(∫y : ℝ,b₂ i y*φ i x y)) := by
    simp_rw [he₂]
    have hi := (plain_density_integrable V₁ M₁ (X₁ i) (hX₁ i) hV₁ (χ i) (b₁ i)).mul_const
      ((∫y : ℝ,b₂ i y*T₂ i y)*P i)
    apply hi.congr
    filter_upwards [] with x
    dsimp [T₁]
    ring
  have hh := row_density_energy_two (fun i=>(b₁ i:ℝ→ℂ)) (fun i=>(b₂ i:ℝ→ℂ)) φ
    rho₁ rho₂ w₁ w₂ hr₁ hr₂ hw₁ hw₂ hp₁ hp₂ hi₁ hi₂ hm₁ hm₂ E hE henergy
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [plain_annular_separation V₁ (F₁ i) M₁ (s₁ i) (X₁ i) (hX₁ i) hV₁ (b₁ i) (hsep₁ i) (χ i),
      plain_annular_separation V₂ (F₂ i) M₂ (s₂ i) (X₂ i) (hX₂ i) hV₂ (b₂ i) (hsep₂ i) (ψ i)]
  simp_rw [he₂]
  congr 1
  rw [←integral_mul_const,←integral_mul_const]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [T₁,T₂]
  ring

end SevenEighths.CenteredMomentReflectedPairEnergy

end

end OAI
end OAIOriginalModule2180

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectedUniformPair
Source SHA256: cc7bb17c701f40c0f21690789c69ab8058e81e1eedbfc747b8a55c25bcf997ce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2181


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedUniformPair
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
open CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy

def heightScale (A n : ℕ) (s t : ℝ) : ℝ := (1+s)^A/(1+‖t‖)^n

def normalizedReflected (V W : ℝ→ℂ) (A n : ℕ) (s t x : ℝ) : ℂ :=
  logWindow V x*((heightScale A n s t:ℝ):ℂ)*
    paperRadialFourier (CompletedHeight.normTwistedSource W t) (s*x)

def envelope (C : ℝ) (J : ℕ) (v : ℝ) : ℝ := C/(1+v^2)/(1+‖v‖)^J

lemma heightScale_pos (A n : ℕ) (s t : ℝ) (hs : 0<s) : 0<heightScale A n s t := by
  unfold heightScale
  positivity

lemma envelope_pos (C : ℝ) (hC : 0<C) (J : ℕ) (v : ℝ) : 0<envelope C J v := by
  unfold envelope
  positivity

lemma envelope_weight (C : ℝ) (J : ℕ) (v : ℝ) :
    envelope C J v*(1+‖v‖)^J=C/(1+v^2) := by
  unfold envelope
  field_simp

lemma envelope_integrable (C : ℝ) (J : ℕ) :
    Integrable (fun v : ℝ=>envelope C J v*(1+‖v‖)^J) := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  exact integrable_inv_one_add_sq.const_mul C

lemma envelope_integral (C : ℝ) (J : ℕ) :
    (∫v : ℝ,envelope C J v*(1+‖v‖)^J)=C*Real.pi := by
  simp_rw [envelope_weight,div_eq_mul_inv]
  rw [integral_const_mul,integral_univ_inv_one_add_sq]

lemma normalized_density_bound (A n J : ℕ) (s t C : ℝ) (hs : 0<s)
    (b : 𝓢(ℝ,ℂ))
    (hp : ∀v : ℝ,(1+s)^A*(1+‖v‖)^(J+2)*‖b v‖≤C*(1+‖t‖)^n) :
    ∀v : ℝ,‖(((heightScale A n s t:ℝ):ℂ) • b) v‖≤envelope C J v := by
  intro v
  have ht : 0<(1+‖t‖)^n := by positivity
  have hv : 0<(1+‖v‖)^J := by positivity
  have hh : (1+‖v‖)^2*((1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖)≤C := by
    rw [smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (heightScale_pos A n s t hs).le]
    unfold heightScale
    have hh := (div_le_iff₀ ht).mpr (hp v)
    convert hh using 1 ; rw [pow_add] ; ring
  have hnorm : 0≤(1+‖v‖)^J*‖(((heightScale A n s t:ℝ):ℂ) • b) v‖ := by positivity
  have hb := CubicReflectionKernel.weighted_two_to_cauchy hnorm v hh
  apply (le_div_iff₀ hv).mpr
  simpa only [envelope,mul_comm] using hb

theorem actual_pair_uniform (V₁ V₂ : ℝ→ℂ) (M₁ M₂ a₁ b₁ a₂ b₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁) (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (ha₁ : 0<a₁) (ha₂ : 0<a₂) (A J₁ J₂ : ℕ) :
    ∃n₁ n₂ : ℕ,∀W₁ W₂ : ℝ→ℂ,
      Function.support W₁⊆Set.Icc a₁ b₁ → ContDiff ℝ ∞ W₁ →
      Function.support W₂⊆Set.Icc a₂ b₂ → ContDiff ℝ ∞ W₂ →
      ∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)
        (s₁ s₂ t₁ t₂ X₁ X₂ : ι→ℝ),
        (∀i,0<s₁ i) → (∀i,0<s₂ i) → (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      ∀E : ℝ,0≤E →
      (∀x y,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V₁) (X₁ i) 0 (2*Real.pi*x)*
        HeckeDyadic.polynomial (ψ i) false (logWindow V₂) (X₂ i) 0 (2*Real.pi*y)*P i‖^2)≤
          E*((1+‖x‖)^J₁)^2*((1+‖y‖)^J₂)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false (normalizedReflected V₁ W₁ A n₁ (s₁ i) (t₁ i)) (X₁ i) 0 0 *
        HeckeDyadic.polynomial (ψ i) false (normalizedReflected V₂ W₂ A n₂ (s₂ i) (t₂ i)) (X₂ i) 0 0 * P i‖^2)≤C*E := by
  obtain ⟨n₁,h₁⟩ := actual_profile_separation V₁ M₁ a₁ b₁ hM₁ hV₁ ha₁ A (J₁+2)
  obtain ⟨n₂,h₂⟩ := actual_profile_separation V₂ M₂ a₂ b₂ hM₂ hV₂ ha₂ A (J₂+2)
  refine ⟨n₁,n₂,?_⟩
  intro W₁ W₂ hs₁ hW₁ hs₂ hW₂
  obtain ⟨C₁,hC₁,hb₁⟩ := h₁ W₁ hs₁ hW₁
  obtain ⟨C₂,hC₂,hb₂⟩ := h₂ W₂ hs₂ hW₂
  refine ⟨(C₁*Real.pi)^2*(C₂*Real.pi)^2,by positivity,?_⟩
  intro ι _ χ ψ P s₁ s₂ t₁ t₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ E hE henergy
  choose d₁ hid₁ hi₁ hm₁ hp₁ using fun i=>hb₁ (t₁ i) (s₁ i) (hs₁ i)
  choose d₂ hid₂ hi₂ hm₂ hp₂ using fun i=>hb₂ (t₂ i) (s₂ i) (hs₂ i)
  let e₁ (i : ι) : ℂ := heightScale A n₁ (s₁ i) (t₁ i)
  let e₂ (i : ι) : ℂ := heightScale A n₂ (s₂ i) (t₂ i)
  let F₁ (i : ι) (x : ℝ) := e₁ i*paperRadialFourier (CompletedHeight.normTwistedSource W₁ (t₁ i)) x
  let F₂ (i : ι) (x : ℝ) := e₂ i*paperRadialFourier (CompletedHeight.normTwistedSource W₂ (t₂ i)) x
  have hsep₁ (i : ι) (y : ℝ) : V₁ y*F₁ i (s₁ i*Real.exp y)=
      ∫v : ℝ,(V₁ y*logPhase v y)*(e₁ i • d₁ i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V₁ y*logPhase v y)*(e₁ i*d₁ i v))=
        (fun v=>e₁ i*((V₁ y*logPhase v y)*d₁ i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid₁ i y]
    dsimp [F₁]
    ring
  have hsep₂ (i : ι) (y : ℝ) : V₂ y*F₂ i (s₂ i*Real.exp y)=
      ∫v : ℝ,(V₂ y*logPhase v y)*(e₂ i • d₂ i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V₂ y*logPhase v y)*(e₂ i*d₂ i v))=
        (fun v=>e₂ i*((V₂ y*logPhase v y)*d₂ i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid₂ i y]
    dsimp [F₂]
    ring
  have hh := paired_profile_energy χ ψ P V₁ V₂ M₁ M₂ hV₁ hV₂ F₁ F₂ s₁ s₂ X₁ X₂ hX₁ hX₂
    (fun i=>e₁ i • d₁ i) (fun i=>e₂ i • d₂ i) hsep₁ hsep₂
    (envelope C₁ J₁) (envelope C₂ J₂) (fun x=>(1+‖x‖)^J₁) (fun y=>(1+‖y‖)^J₂)
    (envelope_pos C₁ hC₁ J₁) (envelope_pos C₂ hC₂ J₂) (by intro x;positivity) (by intro y;positivity)
    (fun i=>normalized_density_bound A n₁ J₁ (s₁ i) (t₁ i) C₁ (hs₁ i) (d₁ i) (hp₁ i))
    (fun i=>normalized_density_bound A n₂ J₂ (s₂ i) (t₂ i) C₂ (hs₂ i) (d₂ i) (hp₂ i))
    (envelope_integrable C₁ J₁) (envelope_integrable C₂ J₂) E hE henergy
  rw [envelope_integral,envelope_integral] at hh
  have heq : E*(C₁*Real.pi)^2*(C₂*Real.pi)^2=((C₁*Real.pi)^2*(C₂*Real.pi)^2)*E := by ring
  rw [heq] at hh
  have hf₁ (i : ι) : normalizedReflected V₁ W₁ A n₁ (s₁ i) (t₁ i)=
      (fun x=>logWindow V₁ x*F₁ i (s₁ i*x)) := by
    funext x
    dsimp [normalizedReflected,F₁,e₁]
    ring
  have hf₂ (i : ι) : normalizedReflected V₂ W₂ A n₂ (s₂ i) (t₂ i)=
      (fun x=>logWindow V₂ x*F₂ i (s₂ i*x)) := by
    funext x
    dsimp [normalizedReflected,F₂,e₂]
    ring
  simp_rw [hf₁,hf₂]
  exact hh

end SevenEighths.CenteredMomentReflectedUniformPair

end

end OAI
end OAIOriginalModule2181

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ScaleSupremum
Source SHA256: f33b661fde8707624ece210028118bfc09570a562225715c6901c39b61a22b73
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2182


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)
def scaleSum (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ inv J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleSum_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (scaleSum χ inv W S) := by
  unfold scaleSum
  fun_prop

theorem scaleSum_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (scaleSum χ inv W S) (scaleSum χ inv (scaleProfile W) S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => coefficient χ inv J*W ((J.absNorm : ℝ)*Real.exp (-t)))
        (coefficient χ inv J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul (coefficient χ inv J) using 1
    · rfl
    · change coefficient χ inv J*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        coefficient χ inv J*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [scaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [scaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

theorem scaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ) (S : Finset (Ideal O))
    (l : ℝ) (hc : ∀ J : Ideal O, J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    scaleSum χ inv W S l=polynomial χ inv W (Real.exp l) 0 0 := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 0 S hc,scale_normalization]
  simp only [HeckeDyadic.shift,ofReal_zero,zero_mul,sub_self,neg_zero,Complex.cpow_zero,mul_one]
  unfold scaleSum
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Real.exp_neg,div_eq_mul_inv]

def scaleTest (W : ℝ→ℂ) (j : Fin 2) : ℝ→ℂ :=
  if j=0 then W else scaleProfile W

lemma scaleTest_continuous (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (j : Fin 2) :
    Continuous (scaleTest W j) := by
  unfold scaleTest
  split
  · exact hW.continuous
  · exact scaleProfile_continuous W hW

lemma scaleTest_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) (j : Fin 2) :
    Function.support (scaleTest W j)⊆Icc a b := by
  unfold scaleTest
  split
  · exact hs
  · exact scaleProfile_support W a b hs

theorem paired_rowwise_scales {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high) (lx ly : ι→ℝ)
    (hlx : ∀ i∈rows,lx i∈Icc lo hi) (hly : ∀ i∈rows,ly i∈Icc low high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 0 *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 0 * P i‖^2≤E) :
    ∑ i∈rows,‖polynomial (χ i) false W (Real.exp (lx i)) 0 0 *
      polynomial (ψ i) false V (Real.exp (ly i)) 0 0 * P i‖^2≤
      (1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (j k : Fin 2) (i : ι) (x y : ℝ) :=
    scaleSum (χ i) false (scaleTest W j) S x *
      scaleSum (ψ i) false (scaleTest V k) T y * P i
  have eqW (i : ι) (j : Fin 2) (x : ℝ) (hx : x∈Icc lo hi) :=
    scaleSum_eq_polynomial (χ i) false (scaleTest W j) S x
      (scaleSupport_cover _ a b hi x hb (scaleTest_support W a b hWs j) hx.2)
  have eqV (i : ι) (k : Fin 2) (y : ℝ) (hy : y∈Icc low high) :=
    scaleSum_eq_polynomial (ψ i) false (scaleTest V k) T y
      (scaleSupport_cover _ c d high y hd (scaleTest_support V c d hVs k) hy.2)
  have hc (j k : Fin 2) (i : ι) : Continuous (Function.uncurry (F j k i)) := by
    exact (((scaleSum_continuous (χ i) false _ S (scaleTest_continuous W hW j)).comp
      continuous_fst).mul ((scaleSum_continuous (ψ i) false _ T
      (scaleTest_continuous V hV k)).comp continuous_snd)).mul continuous_const
  have hx (k : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (fun u=>F 0 k i u y) (F 1 k i x y) x := by
    simpa [F,scaleTest] using
      (scaleSum_deriv (χ i) false W S (hW.differentiable (by simp)) x).mul_const
        (scaleSum (ψ i) false (scaleTest V k) T y) |>.mul_const (P i)
  have hy (j : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    simpa [F,scaleTest] using
      ((scaleSum_deriv (ψ i) false V T (hV.differentiable (by simp)) y).const_mul
        (scaleSum (χ i) false (scaleTest W j) S x)).mul_const (P i)
  have hh := rowwise_energy_two rows F (fun j k i _=>hc j k i)
    (fun k i _ x y=>hx k i x y) (fun j i _ x y=>hy j i x y)
    lo hi low high E hlh hlw lx ly hlx hly (by
      intro j k x hx y hy
      simpa only [F,eqW _ j x hx,eqV _ k y hy] using henergy j k x hx y hy)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [F]
  rw [eqW i 0 (lx i) (hlx i hi),eqV i 0 (ly i) (hly i hi)]
  simp only [scaleTest,ite_true]

theorem exists_paired_scale_majorant {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 0 *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 0 * P i‖^2≤E) :
    ∃ B : ι→ℝ,(∀i,0≤B i) ∧
      (∀i,∀ x∈Icc lo hi,∀ y∈Icc low high,
        ‖polynomial (χ i) false W (Real.exp x) 0 0 *
          polynomial (ψ i) false V (Real.exp y) 0 0 * P i‖^2≤B i) ∧
      (∑ i∈rows,B i)≤(1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (i : ι) (p : ℝ×ℝ) :=
    scaleSum (χ i) false W S p.1 * scaleSum (ψ i) false V T p.2 * P i
  have hc (i : ι) : Continuous (F i) :=
    (((scaleSum_continuous (χ i) false W S hW.continuous).comp continuous_fst).mul
      ((scaleSum_continuous (ψ i) false V T hV.continuous).comp continuous_snd)).mul continuous_const
  have heq (i : ι) (x y : ℝ) (hx : x∈Icc lo hi) (hy : y∈Icc low high) :
      F i (x,y)=polynomial (χ i) false W (Real.exp x) 0 0 *
        polynomial (ψ i) false V (Real.exp y) 0 0 * P i := by
    dsimp only [F]
    rw [scaleSum_eq_polynomial (χ i) false W S x
      (scaleSupport_cover W a b hi x hb hWs hx.2),
      scaleSum_eq_polynomial (ψ i) false V T y
      (scaleSupport_cover V c d high y hd hVs hy.2)]
  have hm (i : ι) : ∃p∈(Icc lo hi)×ˢ(Icc low high),
      ∀q∈(Icc lo hi)×ˢ(Icc low high),‖F i q‖^2≤‖F i p‖^2 := by
    exact (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
      ((nonempty_Icc.mpr hlh).prod (nonempty_Icc.mpr hlw)) ((hc i).norm.pow 2).continuousOn
  choose p hp hmax using hm
  refine ⟨fun i=>‖F i (p i)‖^2,fun i=>sq_nonneg _,?_,?_⟩
  · intro i x hx y hy
    have hh := hmax i (x,y) ⟨hx,hy⟩
    rwa [heq i x y hx hy] at hh
  · have hh := paired_rowwise_scales rows χ ψ P W V a b c d hb hd hWs hVs hW hV
      lo hi low high E hlh hlw (fun i=>(p i).1) (fun i=>(p i).2)
      (fun i _=>(hp i).1) (fun i _=>(hp i).2) henergy
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [←heq i (p i).1 (p i).2 (hp i).1 (hp i).2]

end SevenEighths.CenteredMomentScaleSupremum

end

end OAI
end OAIOriginalModule2182

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum
Source SHA256: 53e319f9d263bd549b043e0301180a92a46045c09085a1480288bd5b88c40f49
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2183


namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentFrequencyScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge FourierBridge
open CenteredMomentScaleSupremum (scaleTest scaleTest_continuous scaleTest_support)
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)
def frequencyScaleSum (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem frequencyScaleSum_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (frequencyScaleSum χ inv W freq S) := by
  unfold frequencyScaleSum
  fun_prop

theorem frequencyScaleSum_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (frequencyScaleSum χ inv W freq S) (frequencyScaleSum χ inv (scaleProfile W) freq S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*W ((J.absNorm : ℝ)*Real.exp (-t)))
        ((coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul ((coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))) using 1
    · rfl
    · change (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
      rw [Complex.real_smul]
      push_cast
      ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  · ext t
    simp only [frequencyScaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [frequencyScaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

lemma ratio_frequency_phase (x l freq : ℝ) (hx : 0<x) :
    (((x/Real.exp l : ℝ):ℂ)^(-shift 0 freq))=
      logPhase (freq/(2*Real.pi)) (-l)*logPhase (freq/(2*Real.pi)) (Real.log x) := by
  have ht : 2*Real.pi*(freq/(2*Real.pi))=freq := by field_simp
  have hh := norm_phase x (Real.exp l) hx (Real.exp_pos l) 0 (freq/(2*Real.pi))
  rw [ht] at hh
  simp only [neg_zero,Complex.cpow_zero,one_mul,zero_re,zero_im,sub_zero] at hh
  rw [←hh,Real.log_div hx.ne' (Real.exp_pos l).ne',Real.log_exp]
  rw [show Real.log x-l=(-l)+Real.log x by ring,logPhase_add]

theorem frequencyScaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    polynomial χ inv W (Real.exp l) 0 freq=
      logPhase (freq/(2*Real.pi)) (-l)*frequencyScaleSum χ inv W freq S l := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 freq S hc,scale_normalization]
  unfold frequencyScaleSum
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h0 : J=0
  · subst J
    simp only [coefficient_zero,zero_mul,mul_zero]
  have hpos : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h0)
  rw [ratio_frequency_phase _ l freq hpos,Real.exp_neg,div_eq_mul_inv]
  ring

theorem frequencyScaleSum_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    ‖frequencyScaleSum χ inv W freq S l‖=‖polynomial χ inv W (Real.exp l) 0 freq‖ := by
  rw [frequencyScaleSum_eq_polynomial χ inv W freq S l hc,norm_mul,logPhase_norm,one_mul]

theorem paired_rowwise_scales {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (freq₁ freq₂ : ι→ℝ) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high) (lx ly : ι→ℝ)
    (hlx : ∀ i∈rows,lx i∈Icc lo hi) (hly : ∀ i∈rows,ly i∈Icc low high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 (freq₂ i) * P i‖^2≤E) :
    ∑ i∈rows,‖polynomial (χ i) false W (Real.exp (lx i)) 0 (freq₁ i) *
      polynomial (ψ i) false V (Real.exp (ly i)) 0 (freq₂ i) * P i‖^2≤
      (1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (j k : Fin 2) (i : ι) (x y : ℝ) :=
    frequencyScaleSum (χ i) false (scaleTest W j) (freq₁ i) S x *
      frequencyScaleSum (ψ i) false (scaleTest V k) (freq₂ i) T y * P i
  have eqW (i : ι) (j : Fin 2) (x : ℝ) (hx : x∈Icc lo hi) :=
    frequencyScaleSum_norm (χ i) false (scaleTest W j) (freq₁ i) S x
      (scaleSupport_cover _ a b hi x hb (scaleTest_support W a b hWs j) hx.2)
  have eqV (i : ι) (k : Fin 2) (y : ℝ) (hy : y∈Icc low high) :=
    frequencyScaleSum_norm (ψ i) false (scaleTest V k) (freq₂ i) T y
      (scaleSupport_cover _ c d high y hd (scaleTest_support V c d hVs k) hy.2)
  have hc (j k : Fin 2) (i : ι) : Continuous (Function.uncurry (F j k i)) := by
    exact (((frequencyScaleSum_continuous (χ i) false _ (freq₁ i) S (scaleTest_continuous W hW j)).comp
      continuous_fst).mul ((frequencyScaleSum_continuous (ψ i) false _ (freq₂ i) T
      (scaleTest_continuous V hV k)).comp continuous_snd)).mul continuous_const
  have hx (k : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (fun u=>F 0 k i u y) (F 1 k i x y) x := by
    simpa [F,scaleTest] using
      (frequencyScaleSum_deriv (χ i) false W (freq₁ i) S (hW.differentiable (by simp)) x).mul_const
        (frequencyScaleSum (ψ i) false (scaleTest V k) (freq₂ i) T y) |>.mul_const (P i)
  have hy (j : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    simpa [F,scaleTest] using
      ((frequencyScaleSum_deriv (ψ i) false V (freq₂ i) T (hV.differentiable (by simp)) y).const_mul
        (frequencyScaleSum (χ i) false (scaleTest W j) (freq₁ i) S x)).mul_const (P i)
  have hh := rowwise_energy_two rows F (fun j k i _=>hc j k i)
    (fun k i _ x y=>hx k i x y) (fun j i _ x y=>hy j i x y)
    lo hi low high E hlh hlw lx ly hlx hly (by
      intro j k x hx y hy
      simpa only [F,norm_mul,eqW _ j x hx,eqV _ k y hy] using henergy j k x hx y hy)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [F]
  simp only [norm_mul]
  rw [eqW i 0 (lx i) (hlx i hi),eqV i 0 (ly i) (hly i hi)]
  simp only [scaleTest,ite_true]

theorem exists_paired_scale_majorant {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (freq₁ freq₂ : ι→ℝ) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤b) (hd : 0≤d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤hi) (hlw : low≤high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 (freq₂ i) * P i‖^2≤E) :
    ∃ B : ι→ℝ,(∀i,0≤B i) ∧
      (∀i,∀ x∈Icc lo hi,∀ y∈Icc low high,
        ‖polynomial (χ i) false W (Real.exp x) 0 (freq₁ i) *
          polynomial (ψ i) false V (Real.exp y) 0 (freq₂ i) * P i‖^2≤B i) ∧
      (∑ i∈rows,B i)≤(1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (i : ι) (p : ℝ×ℝ) :=
    frequencyScaleSum (χ i) false W (freq₁ i) S p.1 * frequencyScaleSum (ψ i) false V (freq₂ i) T p.2 * P i
  have hc (i : ι) : Continuous (F i) :=
    (((frequencyScaleSum_continuous (χ i) false W (freq₁ i) S hW.continuous).comp continuous_fst).mul
      ((frequencyScaleSum_continuous (ψ i) false V (freq₂ i) T hV.continuous).comp continuous_snd)).mul continuous_const
  have heq (i : ι) (x y : ℝ) (hx : x∈Icc lo hi) (hy : y∈Icc low high) :
      ‖F i (x,y)‖^2=‖polynomial (χ i) false W (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false V (Real.exp y) 0 (freq₂ i) * P i‖^2 := by
    dsimp only [F]
    simp only [norm_mul]
    rw [frequencyScaleSum_norm (χ i) false W (freq₁ i) S x
      (scaleSupport_cover W a b hi x hb hWs hx.2),
      frequencyScaleSum_norm (ψ i) false V (freq₂ i) T y
      (scaleSupport_cover V c d high y hd hVs hy.2)]
  have hm (i : ι) : ∃p∈(Icc lo hi)×ˢ(Icc low high),
      ∀q∈(Icc lo hi)×ˢ(Icc low high),‖F i q‖^2≤‖F i p‖^2 := by
    exact (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
      ((nonempty_Icc.mpr hlh).prod (nonempty_Icc.mpr hlw)) ((hc i).norm.pow 2).continuousOn
  choose p hp hmax using hm
  refine ⟨fun i=>‖F i (p i)‖^2,fun i=>sq_nonneg _,?_,?_⟩
  · intro i x hx y hy
    have hh := hmax i (x,y) ⟨hx,hy⟩
    rwa [heq i x y hx hy] at hh
  · have hh := paired_rowwise_scales rows χ ψ freq₁ freq₂ P W V a b c d hb hd hWs hVs hW hV
      lo hi low high E hlh hlw (fun i=>(p i).1) (fun i=>(p i).2)
      (fun i _=>(hp i).1) (fun i _=>(hp i).2) henergy
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [←heq i (p i).1 (p i).2 (hp i).1 (hp i).2]

end SevenEighths.CenteredMomentFrequencyScaleSupremum

end

end OAI
end OAIOriginalModule2183

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RadialPolynomialEnergy
Source SHA256: 267d2a22f9ff59f852f4b77f3c50b3f1ae2b2e44fd302691bf92a4a59b738541
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2184



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentRadialPolynomialEnergy
open HeckeFamily HeckeDyadic CenteredMomentFrequencyScaleSupremum
open CenteredMomentPositiveSummability ConcreteTraceCRT
open HeckeInverseAmplification
local notation "O" => HeckeFamily.O

lemma polynomial_bounded (W : ℝ→ℂ) (a b X : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃B : ℝ,0≤B ∧ ∀χ : Character,∀t : ℝ,‖polynomial χ false W X 0 t‖≤B := by
  let l:=Real.log X
  let S:=scaleSupport l b
  have hx : Real.exp l=X := Real.exp_log hX
  have hc : ∀I : Ideal O,I≠0 → W ((I.absNorm:ℝ)/Real.exp l)≠0 → I∈S :=
    scaleSupport_cover W a b l l hb hs le_rfl
  let B:=‖Complex.exp (-(l:ℂ)/2)‖*∑I∈S,‖W ((I.absNorm:ℝ)*Real.exp (-l))‖
  refine ⟨B,by dsimp [B];positivity,?_⟩
  intro χ t
  rw [←hx,frequencyScaleSum_eq_polynomial χ false W t S l hc,norm_mul,
    FourierBridge.logPhase_norm,one_mul]
  unfold frequencyScaleSum
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul,norm_mul,FourierBridge.logPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (coefficient_norm_le χ false I)

lemma pair_radial_summable (χ : O→Character) (P : O→ℂ) (t omega : O→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a b c d X Y Pbound : ℝ)
    (hb : 0≤b) (hd : 0≤d) (hX : 0<X) (hY : 0<Y)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc c d)
    (hP : ∀z,‖P z‖≤Pbound) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z:O=>if keep z then
      ‖polynomial (χ z) false W₁ X 0 (t z)*polynomial (χ z) false W₂ Y 0 (omega z)*P z‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B₁,hB₁,h₁⟩:=polynomial_bounded W₁ a b X hb hX hs₁
  obtain ⟨B₂,hB₂,h₂⟩:=polynomial_bounded W₂ c d Y hd hY hs₂
  apply bounded_radial_summable _ (B₁*B₂*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul (h₁ _ _) (h₂ _ _) (norm_nonneg _) hB₁)
    (hP z) (norm_nonneg _) (mul_nonneg hB₁ hB₂)

lemma single_radial_summable (χ : O→Character) (P : O→ℂ) (t : O→ℝ)
    (W : ℝ→ℂ) (a b X Pbound : ℝ) (hb : 0≤b) (hX : 0<X)
    (hs : Function.support W⊆Set.Icc a b) (hP : ∀z,‖P z‖≤Pbound)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z:O=>if keep z then ‖polynomial (χ z) false W X 0 (t z)*P z‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  obtain ⟨B,hB,hh⟩:=polynomial_bounded W a b X hb hX hs
  apply bounded_radial_summable _ (B*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul]
  exact mul_le_mul (hh _ _) (hP z) (norm_nonneg _) hB

end SevenEighths.CenteredMomentRadialPolynomialEnergy

end

end OAI
end OAIOriginalModule2184

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SlotRemoval
Source SHA256: bb31cc639692cc79356f61ce83fc44366b14a6630f340b375ab1d15efb5369a3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2185


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentSlotRemoval

theorem whole_slot_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      (∑ i ∈ R, length i) ≤ min (∑ i ∈ s, length i) (F/(6*κ)+η) ∧
      (R=s ∨ F ≤ 6*κ*(∑ i ∈ R, length i)) := by
  have hthreshold : 0 ≤ F/(6*κ) := div_nonneg hF (by positivity)
  by_cases htotal : (∑ i ∈ s, length i) ≤ F/(6*κ)
  · refine ⟨s,Finset.Subset.refl _,le_min le_rfl ?_,Or.inl rfl⟩
    linarith
  · have htarget : 0 ≤ (∑ i ∈ s, length i)-F/(6*κ) := by linarith
    obtain ⟨T,hTs,hTupper,hTlower⟩ := HeckeDetectorSlotSelection.whole_slots
      s length (fun _ => 1) 1 η (by norm_num) hη hL hmesh
      (by intros; norm_num) (by intros; norm_num) 1
      ((∑ i ∈ s, length i)-F/(6*κ)) (by norm_num) (by norm_num)
      htarget (by linarith) (by simp)
    simp only [one_mul,mul_one] at hTlower
    have hsum : (∑ i ∈ s, length i)=(∑ i ∈ s\T, length i)+(∑ i ∈ T, length i) :=
      (Finset.sum_sdiff hTs).symm
    have hTnonneg : 0 ≤ ∑ i ∈ T, length i := Finset.sum_nonneg (fun i hi => hL i (hTs hi))
    refine ⟨s\T,Finset.sdiff_subset,le_min (by linarith) (by linarith),Or.inr ?_⟩
    have hremove : F/(6*κ) ≤ ∑ i ∈ s\T, length i := by linarith
    exact (div_le_iff₀ (by positivity : 0 < 6*κ)).mp hremove |>.trans_eq (mul_comm _ _)

theorem removal_cost {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧
      κ*(∑ i ∈ R, length i) ≤ F/6+κ*η ∧
      (R=s ∨ F-6*κ*(∑ i ∈ R, length i) ≤ 0) := by
  obtain ⟨R,hRs,hR,hpay⟩ := whole_slot_removal s length η κ F hη hκ hF hL hmesh
  refine ⟨R,hRs,?_,hpay.imp_right sub_nonpos.mpr⟩
  have hh := mul_le_mul_of_nonneg_left (hR.trans (min_le_right _ _)) hκ.le
  have he : κ*(F/(6*κ)+η)=F/6+κ*η := by field_simp
  rwa [he] at hh

theorem actual_product_removal {α : Type*} (s : Finset α) (length : α → ℝ)
    (η κ F : ℝ) (hη : 0 ≤ η) (hκ : 0 < κ) (hF : 0 ≤ F)
    (hL : ∀ i ∈ s, 0 ≤ length i) (hmesh : ∀ i ∈ s, length i ≤ η) :
    ∃ R : Finset α, R ⊆ s ∧ (R=s ∨ F-6*κ*(∑ i ∈ R, length i) ≤ 0) ∧
      ∀ (Z : ℝ), 1 ≤ Z → ∀ (C : α → ℝ), (∀ i ∈ s, 0 ≤ C i) →
      ∀ (Q : α → ℂ), (∀ i ∈ s, ‖Q i‖^2 ≤ C i*Z^(κ*length i)) →
      ‖∏ i ∈ s, Q i‖^2 ≤
        (∏ i ∈ R, C i)*Z^(F/6+κ*η)*‖∏ i ∈ s\R, Q i‖^2 := by
  obtain ⟨R,hRs,hcost,hpay⟩ := removal_cost s length η κ F hη hκ hF hL hmesh
  refine ⟨R,hRs,hpay,?_⟩
  intro Z hZ C hC Q hQ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hremoved : ‖∏ i ∈ R, Q i‖^2 ≤ (∏ i ∈ R, C i)*Z^(F/6+κ*η) := by
    rw [norm_prod,← Finset.prod_pow]
    calc
      _ ≤ ∏ i ∈ R, C i*Z^(κ*length i) :=
        Finset.prod_le_prod₀ (fun i hi => sq_nonneg _) (fun i hi => hQ i (hRs hi))
      _ = (∏ i ∈ R, C i)*Z^(κ*(∑ i ∈ R, length i)) := by
        rw [Finset.prod_mul_distrib,Finset.mul_sum,Real.rpow_sum_of_pos hZpos]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ hcost) (Finset.prod_nonneg (fun i hi => hC i (hRs hi)))
  have he : (∏ i ∈ s, Q i)=(∏ i ∈ s\R, Q i)*(∏ i ∈ R, Q i) :=
    (Finset.prod_sdiff hRs).symm
  rw [he,norm_mul,mul_pow,mul_comm (‖∏ i ∈ s\R, Q i‖^2)]
  exact mul_le_mul_of_nonneg_right hremoved (sq_nonneg _)

end SevenEighths.CenteredMomentSlotRemoval

end

end OAI
end OAIOriginalModule2185

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
Source SHA256: aefabbfb58e7aa8c0d270fcd660efe611728f4248bb8a2aae9a36149c9b74f8c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2186



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSourceInputReindex
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstAmplificationChoice CenteredMomentOriginalChildEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {α β : Type*} [Fintype α] [Fintype β]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _
local instance : DecidableEq (β⊕Fin 2) := Classical.decEq _

def reindex (e : α≃β) (s : Input α) : Input β where
  η := s.η
  m := s.m
  A := s.A
  t := s.t
  slots := fun i=>s.slots (e.symm i)
  prime := fun i=>s.prime (e.symm i)
  ν := fun i=>s.ν (e.symm i)
  W := fun i=>s.W (e.symm i)
  lo := fun i=>s.lo (e.symm i)
  hi := fun i=>s.hi (e.symm i)
  P := fun i=>s.P (e.symm i)
  lo_pos := fun i=>s.lo_pos (e.symm i)
  P_pos := fun i=>s.P_pos (e.symm i)
  support := fun i=>s.support (e.symm i)
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  M := fun i=>s.M (e.symm i)
  M_ge_one := fun i=>s.M_ge_one (e.symm i)
  coefficient_bound := fun i=>s.coefficient_bound (e.symm i)
  b₁ := s.b₁
  b₂ := s.b₂
  support₁ := s.support₁
  support₂ := s.support₂
  X₁_pos := s.X₁_pos
  X₂_pos := s.X₂_pos
  Y₁_pos := s.Y₁_pos
  Y₂_pos := s.Y₂_pos
  same_product := s.same_product
  rows := s.rows
  weight := s.weight
  weight_nonneg := s.weight_nonneg
  plain₁ := s.plain₁
  plain₂ := s.plain₂
  plain₁_ne := s.plain₁_ne
  plain₂_ne := s.plain₂_ne
  coverage₁ := s.coverage₁
  coverage₂ := s.coverage₂
  ν_bound := fun i=>s.ν_bound (e.symm i)
  W_bound := fun i=>s.W_bound (e.symm i)
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=>s.lower_le (e.symm i)
  upper_ge := fun i=>s.upper_ge (e.symm i)

def tupleMap (e : α≃β) : Tuple α≃Tuple β :=
  (e.sumCongr (Equiv.refl (Fin 2))).arrowCongr (Equiv.refl (Ideal O))

omit [Fintype α] [Fintype β] in
lemma tupleMap_apply (e : α≃β) (v : Tuple α) (j : β⊕Fin 2) :
    tupleMap e v j = v ((e.sumCongr (Equiv.refl (Fin 2))).symm j) := rfl

lemma tupleMap_product (e : α≃β) (v : Tuple α) :
    finiteTupleProduct (tupleMap e v)=finiteTupleProduct v :=
  (e.sumCongr (Equiv.refl (Fin 2))).symm.prod_comp v

lemma pools_map (e : α≃β) (s : Input α) :
    (Fintype.piFinset s.pools).image (tupleMap e) = Fintype.piFinset (reindex e s).pools := by
  ext v
  simp only [Finset.mem_image,Fintype.mem_piFinset]
  constructor
  · rintro ⟨w,hw,rfl⟩ j
    cases j with
    | inl i => exact hw (Sum.inl (e.symm i))
    | inr i => exact hw (Sum.inr i)
  · intro hv
    refine ⟨(tupleMap e).symm v,?_,(tupleMap e).apply_symm_apply v⟩
    intro j
    cases j with
    | inl i => simpa [tupleMap,Input.pools,reindex] using hv (Sum.inl (e i))
    | inr i => exact hv (Sum.inr i)

lemma profile_map (e : α≃β) (s : Input α) (R seed : Ideal O) (v : Tuple α) :
    (original (reindex e s) R seed).profile (tupleMap e v) =
      (original s R seed).profile v := by
  simp only [OriginalData.profile,original,reindex,profileCoefficient,tupleMap_product,
    tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Equiv.refl_symm,
    Equiv.refl_apply,Sum.map_inl,Sum.map_inr]
  congr 3
  exact e.symm.prod_comp (fun i=>s.ν i (v (Sum.inl i))*
    s.W i ((Ideal.absNorm (v (Sum.inl i)):ℝ)/s.P i))

lemma columns_map (e : α≃β) (s : Input α) (R seed : Ideal O) :
    (original (reindex e s) R seed).columns=(original s R seed).columns := by
  unfold OriginalData.columns
  change finiteColumns (Fintype.piFinset (reindex e s).pools)=finiteColumns (Fintype.piFinset s.pools)
  rw [←pools_map,finiteColumns,Finset.image_image]
  congr 1
  funext v
  exact tupleMap_product e v

lemma coefficient_map (e : α≃β) (s : Input α) (R seed : Ideal O) :
    (original (reindex e s) R seed).beta=(original s R seed).beta := by
  funext I
  unfold OriginalData.beta finiteColumnCoefficient
  change (∑v∈(Fintype.piFinset (reindex e s).pools).filter (fun v=>finiteTupleProduct v=I),
    (original (reindex e s) R seed).profile v)=_
  rw [←pools_map,Finset.filter_image]
  rw [Finset.sum_image (fun v _ w _ h => (tupleMap e).injective h)]
  simp only [tupleMap_product,profile_map]
  rfl

lemma volume_map (e : α≃β) (s : Input α) : volume (reindex e s)=volume s := by
  simp only [volume,reindex,e.symm.prod_comp]

lemma controls_map (e : α≃β) (s : Input α) :
    (∏i,(reindex e s).M i)=(∏i,s.M i) ∧
    (∏i,(reindex e s).lo i)=(∏i,s.lo i) ∧
    (∏i,(reindex e s).hi i)=(∏i,s.hi i) := by
  simp only [reindex,e.symm.prod_comp,and_self]

lemma sourceRadius_map (e : α≃β) (s : Input α) :
    CenteredMomentOriginalCommonHarmonic.sourceRadius (reindex e s)=
      CenteredMomentOriginalCommonHarmonic.sourceRadius s := by
  simp only [CenteredMomentOriginalCommonHarmonic.sourceRadius,reindex,e.symm.prod_comp]

theorem normalizedGaussSource_map (e : α≃β) (s : Input α) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (reindex e s) R seed W K=normalizedGaussSource s R seed W K := by
  unfold normalizedGaussSource
  rw [columns_map,coefficient_map,volume_map]
  rfl

def imageInput (e : α↪β) (T : Finset α) (s : Input T) : Input (T.map e) :=
  reindex (Finset.equivMap e T) s

omit [Fintype α] [Fintype β] in
lemma imageInput_lo (e : α↪β) (T : Finset α) (s : Input T) (i : T) :
    (imageInput e T s).lo ((Finset.equivMap e T) i)=s.lo i := by
  simp only [imageInput,reindex,Equiv.symm_apply_apply]

omit [Fintype α] [Fintype β] in
lemma imageInput_hi (e : α↪β) (T : Finset α) (s : Input T) (i : T) :
    (imageInput e T s).hi ((Finset.equivMap e T) i)=s.hi i := by
  simp only [imageInput,reindex,Equiv.symm_apply_apply]

omit [Fintype α] [Fintype β] in
lemma imageInput_normalized (e : α↪β) (T : Finset α) (s : Input T)
    (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (imageInput e T s) R seed W K=normalizedGaussSource s R seed W K :=
  normalizedGaussSource_map (Finset.equivMap e T) s R seed W K

def allocatedImage (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Input ((liveIndices B.val).map e) :=
  imageInput e (liveIndices B.val) (child s C R B τ t)

omit [Fintype β] in
lemma allocatedImage_ranges (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (lo hi : β→ℝ) (hlo : ∀i,s.lo i=lo (e i)) (hhi : ∀i,s.hi i=hi (e i)) :
    (∀j,(allocatedImage e s C R B τ t).lo j=lo j.val) ∧
    (∀j,(allocatedImage e s C R B τ t).hi j=hi j.val) := by
  constructor
  · intro j
    obtain ⟨i,rfl⟩:=(Finset.equivMap e (liveIndices B.val)).surjective j
    rw [allocatedImage,imageInput_lo]
    exact hlo i.val
  · intro j
    obtain ⟨i,rfl⟩:=(Finset.equivMap e (liveIndices B.val)).surjective j
    rw [allocatedImage,imageInput_hi]
    exact hhi i.val

omit [Fintype β] in
theorem allocatedImage_normalized (e : α↪β) (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (allocatedImage e s C R B τ t) (R*C) seed W K =
      childNormalizedGaussSource s C R seed B τ t W K :=
  imageInput_normalized e (liveIndices B.val) (child s C R B τ t) (R*C) seed W K

end SevenEighths.CenteredMomentSourceInputReindex

end

end OAI
end OAIOriginalModule2186

/-! Original module: OAI.NumberTheory.DirichletL.Moments.TwistedReflection
Source SHA256: d360d4588e06e592b5384b3c5912dfe2aaec4aacbe85180a06dd39308e1a4b55
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2187



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentTwistedReflection
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentNaturalReflection
open CenteredMomentReflectionDeletion EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

lemma polynomial_twisted_source (χ : Character) (W : ℝ→ℂ) (X t : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)=
      HeckeDyadic.polynomial χ false (CompletedHeight.normTwistedSource W t) X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  have hm := HeckeDetectorDyadicBridge.norm_phase (I.val.absNorm:ℝ) X (HeckeDyadic.norm_pos I) hX 0 t
  simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  simp only [Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,CompletedHeight.normTwistedSource]
  simp only [HeckeDyadic.norm,HeckeDyadic.shift] at hm ⊢
  rw [hm]
  simp only [Complex.ofReal_zero]
  ring

theorem actual_original_twisted_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : ℝ→ℂ)(a b : ℝ)(_ha : 0<a)(_hs : Function.support W⊆Set.Icc a b)
        (_hW : ContDiff ℝ ∞ W)(omega X : ℝ),0<X →
        HeckeDyadic.polynomial χ false W X 0 omega=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*idealCoeff ψ (∏P∈D,P)*
              idealCoeff ψ.inverse H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              HeckeDyadic.polynomial χ.inverse false
                (paperRadialFourier (CompletedHeight.normTwistedSource W (omega/(2*Real.pi))))
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hp,hnp,hG,hcap,hreflect⟩ := original_inverse_reflection χ hn
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro W a b ha hs hW omega X hX
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (omega/(2*Real.pi)) : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W (omega/(2*Real.pi)) := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW _ x
  have hh := hreflect (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (omega/(2*Real.pi))) X hX
  rw [he] at hh
  have ht : 2*Real.pi*(omega/(2*Real.pi))=omega := by field_simp
  rw [←ht,polynomial_twisted_source χ W X (omega/(2*Real.pi)) hX]
  simpa only [ht] using hh

end SevenEighths.CenteredMomentTwistedReflection

end

end OAI
end OAIOriginalModule2187

/-! Original module: OAI.NumberTheory.DirichletL.Moments.OneReflectionEnergy
Source SHA256: 5207dcc99784ef63830a04aa317314a4eac96c18fce7ac741c3411e8e0b41ba9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2188



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionEnergy
open HeckeFamily CenteredMomentReflectedProfileMeasure CenteredMomentReflectedPairEnergy
open CenteredMomentReflectedUniformPair CenteredMomentComparisonReflection
open EisensteinSchwartzPoisson

lemma polynomial_inverse_plain (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ.inverse false W X 0 0=
      conj (HeckeDyadic.polynomial χ false (fun x=>conj (W x)) X 0 0) := by
  rw [polynomial_plain _ _ _ hX,polynomial_plain _ _ _ hX,map_mul,map_inv₀,
    Complex.conj_ofReal,Complex.conj_tsum]
  congr 1
  apply tsum_congr
  intro I
  rw [map_mul,idealCoeff_inverse_conj,Complex.conj_conj]

lemma polynomial_inverse_norm (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    ‖HeckeDyadic.polynomial χ.inverse false W X 0 0‖=
      ‖HeckeDyadic.polynomial χ false (fun x=>conj (W x)) X 0 0‖ := by
  rw [polynomial_inverse_plain χ W X hX,Complex.norm_conj]

theorem actual_one_uniform (V : ℝ→ℂ) (M a b : ℝ) (hM : 0≤M)
    (hV : ∀y,V y≠0 → |y|≤M) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀{ι : Type} [Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)
        (s t X Y omega : ι→ℝ)(Wshort : ℝ→ℂ),
        (∀i,0<s i) → (∀i,0<X i) →
      ∀E : ℝ,0≤E →
      (∀v,(∑i,‖HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*
        HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i‖^2)≤E*((1+‖v‖)^J)^2) →
      (∑i,‖HeckeDyadic.polynomial (χ i) false (normalizedReflected V W A n (s i) (t i)) (X i) 0 0 *
        HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i‖^2)≤C*E := by
  obtain ⟨n,hn⟩ := actual_profile_separation V M a b hM hV ha A (J+2)
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨(C*Real.pi)^2,by positivity,?_⟩
  intro ι _ χ ψ P s t X Y omega Wshort hs hX E hE henergy
  choose d hid hi hm hp using fun i=>hb (t i) (s i) (hs i)
  let e (i : ι) : ℂ := heightScale A n (s i) (t i)
  let F (i : ι) (x : ℝ) := e i*paperRadialFourier (CompletedHeight.normTwistedSource W (t i)) x
  let Q (i : ι) := HeckeDyadic.polynomial (ψ i) false Wshort (Y i) 0 (omega i)*P i
  let φ (i : ι) (v : ℝ) := HeckeDyadic.polynomial (χ i) false (logWindow V) (X i) 0 (2*Real.pi*v)*Q i
  have hsep (i : ι) (y : ℝ) : V y*F i (s i*Real.exp y)=
      ∫v : ℝ,(V y*FourierBridge.logPhase v y)*(e i • d i) v := by
    simp only [smul_apply,smul_eq_mul]
    have he : (fun v : ℝ=>(V y*FourierBridge.logPhase v y)*(e i*d i v))=
        (fun v=>e i*((V y*FourierBridge.logPhase v y)*d i v)) := by funext v;ring
    rw [he,integral_const_mul,←hid i y]
    dsimp [F]
    ring
  have hsource (i : ι) : HeckeDyadic.polynomial (χ i) false
      (normalizedReflected V W A n (s i) (t i)) (X i) 0 0*Q i=
      ∫v : ℝ,(e i • d i) v*φ i v := by
    have hf : normalizedReflected V W A n (s i) (t i)=
        (fun x=>logWindow V x*F i (s i*x)) := by
      funext x
      dsimp [normalizedReflected,F,e]
      ring
    rw [hf,plain_annular_separation V (F i) M (s i) (X i) (hX i) hV (e i • d i) (hsep i),
      ←integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hint (i : ι) : Integrable (fun v : ℝ=>(e i • d i) v*φ i v) := by
    have hh := (plain_density_integrable V M (X i) (hX i) hV (χ i) (e i • d i)).mul_const (Q i)
    apply hh.congr
    filter_upwards [] with v
    dsimp [φ]
    ring
  have hh := row_density_energy (fun i=>(e i • d i:𝓢(ℝ,ℂ))) φ (envelope C J)
    (fun v=>(1+‖v‖)^J) (envelope_pos C hC J) (by intro v;positivity)
    (fun i=>normalized_density_bound A n J (s i) (t i) C (hs i) (d i) (hp i)) hint
    (envelope_integrable C J) E hE (by
      intro v
      simpa only [φ,Q,mul_assoc] using henergy v)
  rw [envelope_integral] at hh
  simp_rw [←hsource] at hh
  simpa only [Q,mul_assoc,mul_comm E] using hh

end SevenEighths.CenteredMomentOneReflectionEnergy

end

end OAI
end OAIOriginalModule2188

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization
Source SHA256: 9444eec77d9397ac5da68747ceac85a157daad9a87dd5f4d1e44f91af0b9975f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2189



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentReflectedNormalization
open HeckeFamily CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson

lemma actual_log_window :
    CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow=
      (fun x : ℝ=>(annulus x:ℂ)) := by
  funext x
  unfold CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow
  split_ifs with hx
  · rw [Real.exp_log hx]
  · rw [annulus_zero_low x (by linarith)]
    rfl

lemma polynomial_const (χ : Character) (W : ℝ→ℂ) (X : ℝ) (c : ℂ) :
    HeckeDyadic.polynomial χ false (fun x=>c*W x) X 0 0=
      c*HeckeDyadic.polynomial χ false W X 0 0 := by
  unfold HeckeDyadic.polynomial
  have he (I : HeckeDyadic.NonzeroIdeal) :
      HeckeDyadic.summand χ false (fun x=>c*W x) X 0 0 I=
        c*HeckeDyadic.summand χ false W X 0 0 I := by
    unfold HeckeDyadic.summand
    ring
  simp_rw [he,tsum_mul_left]
  ring

lemma normalized_profile_actual (W : ℝ→ℂ) (B n : ℕ) (s t x : ℝ) :
    normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n s t x=
      (heightScale B n s t:ℂ)*CenteredMomentReflectedAnnuli.annularProfile
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) s x := by
  unfold normalizedReflected
  rw [actual_log_window]
  unfold CenteredMomentReflectedAnnuli.annularProfile
  ring

theorem actual_annular_normalization (χ : Character) (W : ℝ→ℂ) (B n : ℕ)
    (k : ℤ) (t Y : ℝ) :
    (Real.sqrt (dyadicScale k):ℂ)*HeckeDyadic.polynomial χ false
      (CenteredMomentReflectedAnnuli.annularProfile
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (dyadicScale k))
      (dyadicScale k*Y) 0 0=
      (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
        HeckeDyadic.polynomial χ false
          (normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale k) t)
          (dyadicScale k*Y) 0 0 := by
  have hf : normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale k) t=
      (fun x=>(heightScale B n (dyadicScale k) t:ℂ)*
        CenteredMomentReflectedAnnuli.annularProfile
          (paperRadialFourier (CompletedHeight.normTwistedSource W t)) (dyadicScale k) x) :=
    funext (normalized_profile_actual W B n (dyadicScale k) t)
  rw [hf,polynomial_const]
  have hh : (1+‖t‖)^n*CenteredMomentReflectedAnnuli.annularMass B k*
      heightScale B n (dyadicScale k) t=Real.sqrt (dyadicScale k) := by
    unfold CenteredMomentReflectedAnnuli.annularMass heightScale
    have ht : (1+‖t‖)^n≠0 := ne_of_gt (by positivity)
    have hs : (1+dyadicScale k)^B≠0 := ne_of_gt (by have := dyadicScale_pos k;positivity)
    field_simp
  have hc : (((1+‖t‖)^n:ℝ):ℂ)*(CenteredMomentReflectedAnnuli.annularMass B k:ℂ)*
      (heightScale B n (dyadicScale k) t:ℂ)=(Real.sqrt (dyadicScale k):ℂ) := by
    rw [←Complex.ofReal_mul,←Complex.ofReal_mul,hh]
  rw [←mul_assoc _ (heightScale B n (dyadicScale k) t:ℂ),hc]

end SevenEighths.CenteredMomentReflectedNormalization

end

end OAI
end OAIOriginalModule2189

/-! Original module: OAI.NumberTheory.DirichletL.Moments.OneReflectionScaleEnergy
Source SHA256: 48093c6739e095ac4e31ff11ca2b8b340a78e897770ae94f327798ae290b4fd3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2190




namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionScaleEnergy
open HeckeFamily HeckeDyadic CenteredMomentSectorLocalization
open CenteredMomentReflectedUniformPair CenteredMomentReflectedNormalization
open CenteredMomentScaleSupremum (scaleTest)

lemma annulus_complex_support :
    Function.support (fun x : ℝ=>(annulus x:ℂ))⊆Icc (1/4) 1 := by
  intro x hx
  have hn : annulus x≠0 := by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

lemma annulus_complex_smooth : ContDiff ℝ ∞ (fun x : ℝ=>(annulus x:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

lemma annular_inverse_frequency_norm (χ : Character) (X v : ℝ) (hX : 0<X) :
    ‖polynomial χ.inverse false
      (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
      X 0 (2*Real.pi*v)‖=
    ‖polynomial χ false (fun x : ℝ=>(annulus x:ℂ)) X 0 (-2*Real.pi*v)‖ := by
  rw [actual_log_window]
  have hh := HeckeInverseAmplification.polynomial_inverse_norm χ false
    (fun x : ℝ=>(annulus x:ℂ)) X 0 (-2*Real.pi*v) hX
  simpa only [Complex.conj_ofReal,neg_mul,neg_neg] using hh

theorem actual_one_rowwise_scales (a b : ℝ) (ha : 0<a) (A J : ℕ) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀(χ : ι→Character)(P : ι→ℂ)
      (s t lx ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high E : ℝ),
      0≤d → Function.support Wshort⊆Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,lx i∈Icc lo hi) → (∀i,ly i∈Icc low high) →
      (∀i,0<s i) → 0≤E →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Icc lo hi,∀y∈Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i).inverse false
        (normalizedReflected CenteredMomentReflectedAnnuli.logWindow Wlong A n (s i) (t i))
        (Real.exp (lx i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hwindow : ∀y,CenteredMomentReflectedAnnuli.logWindow y≠0 → |y|≤Real.log 4 := by
    intro y hy
    have hh := CenteredMomentReflectedAnnuli.logWindow_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans hlog⟩
  obtain ⟨n,hn⟩ := CenteredMomentOneReflectionEnergy.actual_one_uniform
    CenteredMomentReflectedAnnuli.logWindow (Real.log 4) a b hlog hwindow ha A J
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hbound⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  intro ι _ χ P s t lx ly omega Wshort c d lo hi low high E hd hshort hshortsmooth
    hlh hlw hlx hly hspos hE henergy
  have hdx : 0≤1+2*(hi-lo) := by linarith
  have hdy : 0≤1+2*(high-low) := by linarith
  have hfixed (v : ℝ) :
      (∑i,‖polynomial (χ i).inverse false
        (CenteredMomentReflectedProfileMeasure.logWindow CenteredMomentReflectedAnnuli.logWindow)
        (Real.exp (lx i)) 0 (2*Real.pi*v)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
      ((1+2*(hi-lo))*((1+2*(high-low))*E))*((1+‖v‖)^J)^2 := by
    have hh := CenteredMomentFrequencyScaleSupremum.paired_rowwise_scales Finset.univ
      χ χ (fun _=>-2*Real.pi*v) omega P (fun z : ℝ=>(annulus z:ℂ)) Wshort
      (1/4) 1 c d (by norm_num) hd annulus_complex_support hshort annulus_complex_smooth hshortsmooth
      lo hi low high (E*(1+‖v‖)^(2*J)) hlh hlw lx ly
      (fun i _=>hlx i) (fun i _=>hly i) (henergy v)
    have hp : ((1+‖v‖)^J)^2=(1+‖v‖)^(2*J) := by
      rw [←pow_mul,Nat.mul_comm J 2]
    calc
      _ = ∑i,‖polynomial (χ i) false (fun z : ℝ=>(annulus z:ℂ))
        (Real.exp (lx i)) 0 (-2*Real.pi*v)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [norm_mul,annular_inverse_frequency_norm (χ i) _ v (Real.exp_pos _)]
      _ ≤ (1+2*(hi-lo))*((1+2*(high-low))*(E*(1+‖v‖)^(2*J))) := hh
      _ = _ := by rw [hp];ring
  have hh := hbound (fun i=>(χ i).inverse) χ P s t (fun i=>Real.exp (lx i))
    (fun i=>Real.exp (ly i)) omega Wshort hspos (fun i=>Real.exp_pos _)
    ((1+2*(hi-lo))*((1+2*(high-low))*E)) (mul_nonneg hdx (mul_nonneg hdy hE)) hfixed
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentOneReflectionScaleEnergy

end

end OAI
end OAIOriginalModule2190

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectedChoiceEnergy
Source SHA256: c2685baf06e8d7b05c526635896345e743fa1dfda65c5a216eb7ae106dbb3ba0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2191





namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentReflectedChoiceEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentReflectionDeletion CenteredMomentReflectionTailMass
open CenteredMomentNaturalPrimitive CenteredMomentReflectionRetainedLength
open Filter

local notation "O" => HeckeFamily.O

theorem actual_independent_profile_choices (a b : ℝ) (ha : 0<a) (B J : ℕ) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀{α : ι→Type},
      ∀(χ : ι→Character)(P : ι→ℂ)(s X : ∀i,α i→ℝ)(keep : ∀i,α i→Prop)
        (t ly omega : ι→ℝ)(Wshort : ℝ→ℂ)(c d lo hi low high E : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i u,0<s i u) → (∀i u,keep i u → 0<X i u ∧ Real.log (X i u)∈Set.Icc lo hi) → 0≤E →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      ∀u : ∀i,α i,
      (∑i,‖if keep i (u i) then polynomial (χ i).inverse false
        (normalizedReflected CenteredMomentReflectedAnnuli.logWindow Wlong B n (s i (u i)) (t i))
        (X i (u i)) 0 0*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i else 0‖^2)≤
        C*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨n,hn⟩ := CenteredMomentOneReflectionScaleEnergy.actual_one_rowwise_scales a b ha B J
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hb⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  intro ι _ α χ P s X keep t ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hly hspos hgeom hE henergy u
  let lx (i : ι) := if keep i (u i) then Real.log (X i (u i)) else lo
  let P' (i : ι) := if keep i (u i) then P i else 0
  have hlx (i : ι) : lx i∈Set.Icc lo hi := by
    dsimp [lx]
    split_ifs with hk
    · exact (hgeom i (u i) hk).2
    · exact ⟨le_rfl,hlh⟩
  have he (v : ℝ) (j k : Fin 2) (x : ℝ) (hx : x∈Set.Icc lo hi)
      (y : ℝ) (hy : y∈Set.Icc low high) :
      (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
        (Real.exp x) 0 (-2*Real.pi*v)*
        polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P' i‖^2)
        ≤E*(1+‖v‖)^(2*J) := by
    apply (Finset.sum_le_sum (fun i _=>?_)).trans (henergy v j k x hx y hy)
    dsimp only [P']
    split_ifs
    · exact le_rfl
    · simp only [mul_zero,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
      exact sq_nonneg _
  have hh := hb χ P' (fun i=>s i (u i)) t lx ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hlx hly (fun i=>hspos i (u i)) hE he
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [lx,P']
  split_ifs with hk
  · rw [Real.exp_log (hgeom i (u i) hk).1]
  · simp

theorem eventually_natural_choice_geometry (C xi : ℝ) (hC : 0<C) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(χ ψ : Character)(M a : ℝ),
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm →
      (χ.modulus.absNorm:ℝ)≤C*Z^M →
      let S := redundantSet χ.modulus ψ.modulus
      ∀u : Index S,
      let Y := (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈u.1.1.val,P):ℝ)/(Z^a*CenteredMomentReflectionDeletion.norm u.1.2.val)
      ∀hY : 0<Y,u.2∈retainedAnnuli (Z^(xi/4)) Y hY →
      1≤dyadicScale u.2*Y ∧
      0≤Real.log (dyadicScale u.2*Y) ∧
      Real.log (dyadicScale u.2*Y)≤(M-a+xi)*Real.log Z := by
  filter_upwards [eventually_actual_retained_length C 1 xi hC le_rfl hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ ψ M a hcap hmod
  dsimp only
  intro u hY hu
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hD := subset_product_norm_pos u.1.1.val
    (fun P hP=>hS P ((Finset.mem_powerset.mp u.1.1.property) hP))
  have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤C*Z^M := by
    have hh : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by exact_mod_cast hcap
    exact hh.trans hmod
  have hh := hZ.2 M a _ _ _ _ hQ hD hc
    (subset_norm_le _ _ hS (Finset.mem_powerset.mp u.1.1.property))
    (restoration_norm_one _ u.1.2) u.2 hY hu
  simp only [one_mul] at hh
  refine ⟨hh.1,Real.log_nonneg hh.1,?_⟩
  have hz : 0<Real.log Z := Real.log_pos hZ.1
  have hlog := hh.2.2
  rw [Real.logb] at hlog
  exact (div_le_iff₀ hz).mp hlog

end SevenEighths.CenteredMomentReflectedChoiceEnergy

end

end OAI
end OAIOriginalModule2191

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RetainedReflection
Source SHA256: b96a97b0a57902c2013eb42a63c27f3552dd89088ddc147f2c544459e86b9641
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2192




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentRetainedReflection
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive CenteredMomentNaturalReflection
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma masked_decayTwo (F : ℝ→ℂ) (hF : DecayTwo F) (w : ℝ→ℝ)
    (hw : ∀x,0≤w x ∧ w x≤1) : DecayTwo (fun x=>(w x:ℂ)*F x) := by
  obtain ⟨D,hD,hb⟩ := hF
  refine ⟨D,hD,?_⟩
  intro x hx
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw x).1]
  apply (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (norm_nonneg _) (hw x).2) (sq_nonneg x)).trans (hb x hx)

lemma column_retained_discarded (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) :
    HeckeDyadic.polynomial η false F Y 0 0=
      HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0+
      HeckeDyadic.polynomial η false (fun x=>(discardedWeight R x:ℂ)*F x) Y 0 0 := by
  have hr := plain_summable η _ (masked_decayTwo F hF _ (retainedWeight_bounds R)) Y hY
  have hd := plain_summable η _ (masked_decayTwo F hF _ (discardedWeight_bounds R)) Y hY
  simp only [CenteredMomentReflectionDeletion.norm] at hr hd
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ hY,polynomial_plain _ _ _ hY,
    ←mul_add,←hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro I
  have hp := retained_add_discarded R (norm I/Y) (div_pos (norm_pos I) hY)
  simp only [CenteredMomentReflectionDeletion.norm] at hp ⊢
  rw [←mul_add,←add_mul,←Complex.ofReal_add,hp,Complex.ofReal_one,one_mul]

lemma bounded_columns (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F) :
    ∃C : ℝ,0≤C ∧ ∀Y U : ℝ,0<Y → Y≤U →
      ‖HeckeDyadic.polynomial η false F Y 0 0‖≤C*U^(3/2:ℝ) := by
  obtain ⟨D,hD,hF⟩ := hF
  obtain ⟨C,hC,hb⟩ := plain_rapid_bound 2 (by omega)
  refine ⟨C*D,by positivity,?_⟩
  intro Y U hY hYU
  apply (hb η F D Y hD hY hF).trans
  rw [normalized_power_eq Y hY 2]
  norm_num only [Nat.cast_ofNat,show (2:ℝ)-1/2=3/2 by norm_num]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hY.le hYU (by norm_num)) (by positivity)

lemma reflected_column_summable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η ηi χ : Character) (F : ℝ→ℂ) (hF : DecayTwo F) (Q X : ℝ)
    (hQ : 0<Q) (hX : 0<X) (D : Finset (Ideal O)) (hD : D∈S.powerset) :
    Summable (fun H : SmoothIdeal S=>coefficient η ηi S D H*
      HeckeDyadic.polynomial χ false F
        (Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0) := by
  obtain ⟨C,hC,hb⟩ := bounded_columns χ F hF
  obtain ⟨K,hK,hKb⟩ := coefficient_column_bound 1 (by norm_num)
  let U := Q*(Ideal.absNorm (∏P∈S,P):ℝ)/X
  have hu : 0<U := div_pos (mul_pos hQ (subset_product_norm_pos S hS)) hX
  exact (hKb S hS η ηi (fun E H=>HeckeDyadic.polynomial χ false F
    (Q*(Ideal.absNorm (∏P∈E,P):ℝ)/(X*norm H.val)) 0 0)
    (C*U^(3/2:ℝ)) (by positivity) (by
      intro E hE H
      have hscale := dual_scale_bounds S E hS (Finset.mem_powerset.mp hE) H Q X U hQ hX (by
        dsimp [U]
        rw [div_mul_cancel₀ _ hX.ne'])
      exact hb _ U hscale.1 hscale.2)).1 D hD

theorem original_retained_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : 𝓢(ℝ,ℂ))(X R : ℝ)(_hX : 0<X),
        let Q := (ψ.modulus.absNorm:ℝ)
        let Y := fun (D : Finset (Ideal O))(H : SmoothIdeal S)=>Q*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)
        HeckeDyadic.polynomial χ false W X 0 0=
          G*((∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
            HeckeDyadic.polynomial χ.inverse false
              (fun x=>(retainedWeight R x:ℂ)*paperRadialFourier W x) (Y D H) 0 0)+
            ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
            HeckeDyadic.polynomial χ.inverse false
              (fun x=>(discardedWeight R x:ℂ)*paperRadialFourier W x) (Y D H) 0 0) := by
  obtain ⟨ψ,G,hp,hnp,hG,hcap,heq⟩ := original_inverse_reflection χ hn
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro W X R hX
  dsimp only
  rw [heq W X hX]
  congr 1
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  have hS := redundantSet_prime χ.modulus ψ.modulus
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hF := reflected_decayTwo W
  have hr := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (retainedWeight_bounds R)) _ X hQ hX D hD
  have hd := reflected_column_summable _ hS ψ ψ.inverse χ.inverse _
    (masked_decayTwo _ hF _ (discardedWeight_bounds R)) _ X hQ hX D hD
  rw [←hr.tsum_add hd]
  apply tsum_congr
  intro H
  have hY := (dual_scale_bounds _ D hS (Finset.mem_powerset.mp hD) H
    (ψ.modulus.absNorm:ℝ) X ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈redundantSet χ.modulus ψ.modulus,P):ℝ)/X)
    hQ hX (by rw [div_mul_cancel₀ _ hX.ne'])).1
  change coefficient ψ ψ.inverse _ D H*HeckeDyadic.polynomial χ.inverse false
    (paperRadialFourier W) _ 0 0=_
  rw [column_retained_discarded χ.inverse _ hF R _ hY,mul_add]

end SevenEighths.CenteredMomentRetainedReflection

end

end OAI
end OAIOriginalModule2192

/-! Original module: OAI.NumberTheory.DirichletL.Moments.OriginalReflectionApproximation
Source SHA256: d14a4f2c3d03a7dfdb9a2b12464c42ec310d45b6a4a8d5171421b704f027156d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2193



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionApproximation
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open CenteredMomentComparisonReflection CenteredMomentReflectionTailMass
open CenteredMomentSectorLocalization CenteredMomentReflectedTruncation
open CenteredMomentReflectedAnnuli CenteredMomentNaturalPrimitive
open CenteredMomentRetainedReflection CenteredMomentTwistedReflection
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

def finiteAnnularColumn (η : Character) (F : ℝ→ℂ) (R Y : ℝ) : ℂ :=
  if hY : 0<Y then ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
    HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0

lemma finiteAnnularColumn_eq (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) : finiteAnnularColumn η F R Y=
      HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0 := by
  rw [finiteAnnularColumn,dite_eq_left hY]
  exact (retained_finite_series η F hF R Y hY).symm

def retainedOriginal (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) : ℂ :=
  let S := redundantSet χ.modulus ψ.modulus
  ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
    finiteAnnularColumn χ.inverse
      (paperRadialFourier (CompletedHeight.normTwistedSource W t)) R
      ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val))

lemma radical_le_original (χ ψ : Character)
    (hcap : ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm) :
    (Ideal.absNorm (redundantIdeal χ.modulus ψ.modulus):ℝ)≤(χ.modulus.absNorm:ℝ) := by
  have hp : 1≤ψ.modulus.absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  exact_mod_cast (show (redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm by
    nlinarith)

theorem actual_original_retained_approximation (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀(χ : Character),χ.residue≠1 →
        ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
        ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
        ∀(X t Z : ℝ),0<X → 1≤Z → (χ.modulus.absNorm:ℝ)≤Cscale*Z^L*X →
          ‖HeckeDyadic.polynomial χ false W X 0 (2*Real.pi*t)-
            G*retainedOriginal χ ψ W X (Z^(xi/2)) t‖≤
            C*(χ.modulus.absNorm:ℝ)^ε*(1+‖t‖)^n*Z^(-saving) := by
  obtain ⟨n,hn⟩ := actual_deleted_discarded_negligible a b xi saving L Cscale ε ha hxi hscale hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hCb⟩ := hn W hs hW
  refine ⟨C,hC,?_⟩
  intro χ hχ
  obtain ⟨ψ,G,hp,hnp,hG,hcap,heq⟩ := original_retained_reflection χ hχ
  refine ⟨ψ,G,hp,hnp,hG,hcap,?_⟩
  intro X t Z hX hZ hmod
  let S := redundantSet χ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hcap' : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤Cscale*Z^L*X := by
    have hc : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤(χ.modulus.absNorm:ℝ) := by
      exact_mod_cast hcap
    exact hc.trans hmod
  let Wt := CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t
  have heWt : (Wt : ℝ→ℂ)=CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  have hF : DecayTwo (paperRadialFourier (CompletedHeight.normTwistedSource W t)) := by
    rw [←heWt]
    exact reflected_decayTwo Wt
  have hret : retainedOriginal χ ψ W X (Z^(xi/2)) t=
      ∑D∈S.powerset,∑'H : SmoothIdeal S,coefficient ψ ψ.inverse S D H*
        HeckeDyadic.polynomial χ.inverse false
          (fun x=>(retainedWeight (Z^(xi/2)) x:ℂ)*
            paperRadialFourier (CompletedHeight.normTwistedSource W t) x)
          ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
    unfold retainedOriginal
    apply Finset.sum_congr rfl
    intro D hD
    apply tsum_congr
    intro H
    rw [finiteAnnularColumn_eq _ _ hF _ _
      (dual_scale_bounds S D hS (Finset.mem_powerset.mp hD) H _ X _ hQ hX hcap').1]
  have hsource := heq Wt X (Z^(xi/2)) hX
  dsimp only at hsource
  rw [heWt] at hsource
  rw [polynomial_twisted_source χ W X t hX,hsource,←hret]
  rw [mul_add,add_sub_cancel_left,norm_mul,hG,one_mul]
  have hb := (hCb S hS ψ ψ.inverse χ.inverse t _ X Z hZ hQ hX hcap').2
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (radical_le_original χ ψ hcap) hε.le

end SevenEighths.CenteredMomentOriginalReflectionApproximation

end

end OAI
end OAIOriginalModule2193

/-! Original module: OAI.NumberTheory.DirichletL.Moments.OriginalReflectionEnergy
Source SHA256: 4a62c123c1f47b8bafc77859dc8c1923e125c6faa7f312451d069f76ee43b190
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2194


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentOriginalReflectionEnergy
open HeckeFamily CenteredMomentOriginalReflectionApproximation CenteredMomentNaturalPrimitive

lemma norm_sq_comparison (a b : ℂ) : ‖a‖^2≤2*‖b‖^2+2*‖a-b‖^2 := by
  have he : a=b+(a-b) := by ring
  have hh : ‖a‖≤‖b‖+‖a-b‖ := by nth_rw 1 [he];exact norm_add_le _ _
  nlinarith [norm_nonneg a,norm_nonneg b,norm_nonneg (a-b),sq_nonneg (‖b‖-‖a-b‖)]

theorem actual_original_energy_to_retained (a b xi saving L Cscale ε : ℝ)
    (ha : 0<a) (hxi : 0<xi) (hscale : 0<Cscale) (hε : 0<ε) :
    ∃n : ℕ,∀(W : ℝ→ℂ),Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],∀χ : ι→Character,
        (∀i,(χ i).residue≠1) →
        ∃ψ : ι→Character,
        (∀i,FiniteFourier.IsPrimitiveOnIdeals (ψ i).residue ∧ (ψ i).residue≠1 ∧
          (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) ∧
        ∀(X t : ι→ℝ)(P : ι→ℂ)(T Z Rcap : ℝ),0≤T → 1≤Z → 1≤Rcap →
          (∀i,0<X i) → (∀i,‖t i‖≤T) → (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
          (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*X i) →
          (∑i,‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i‖^2)≤
            2*(∑i,‖retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)*P i‖^2)+
            C*Rcap^(2*ε)*(1+T)^(2*n)*Z^(-2*saving)*(∑i,‖P i‖^2) := by
  obtain ⟨n,hn⟩ := actual_original_retained_approximation a b xi saving L Cscale ε ha hxi hscale hε
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨C,hC,hb⟩ := hn W hs hW
  refine ⟨2*C^2,by positivity,?_⟩
  intro ι _ χ hχ
  choose ψ G hp hnψ hG hcap happrox using fun i=>hb (χ i) (hχ i)
  refine ⟨ψ,fun i=>⟨hp i,hnψ i,hcap i⟩,?_⟩
  intro X t P T Z Rcap hT hZ hR hX ht hmod hsource
  let B := C*Rcap^ε*(1+T)^n*Z^(-saving)
  have hB : 0≤B := by dsimp [B];positivity
  have herr (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)-
        G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)‖≤B := by
    apply (happrox i (X i) (t i) Z (hX i) hZ (hsource i)).trans
    dsimp [B]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hmod i) hε.le) hC.le)
      (pow_le_pow_left₀ (by positivity) (by simpa only [Real.norm_eq_abs,add_comm] using add_le_add_left (ht i) 1) n) (by positivity) (by positivity)
  have hpoint (i : ι) :
      ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i‖^2≤
      2*‖retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i)*P i‖^2+B^2*(2*‖P i‖^2) := by
    have hh := norm_sq_comparison
      (HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i)
      ((G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i))*P i)
    have he : ‖HeckeDyadic.polynomial (χ i) false W (X i) 0 (2*Real.pi*t i)*P i-
        (G i*retainedOriginal (χ i) (ψ i) W (X i) (Z^(xi/2)) (t i))*P i‖≤B*‖P i‖ := by
      rw [←sub_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (herr i) (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) he 2
    simp only [norm_mul,hG,one_mul] at hh
    simp only [mul_pow] at hs
    simp only [norm_mul]
    nlinarith
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset ι))=>hpoint i)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hBeq : B^2*2=(2*C^2)*Rcap^(2*ε)*(1+T)^(2*n)*Z^(-2*saving) := by
    have hr0 : 0≤Rcap := by linarith
    have hz0 : 0≤Z := by linarith
    have hr : (Rcap^ε)^2=Rcap^(2*ε) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hr0];congr 1;ring
    have hz : (Z^(-saving))^2=Z^(-2*saving) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hz0];congr 1;ring
    dsimp [B]
    rw [mul_pow,mul_pow,mul_pow,hr,hz,←pow_mul]
    rw [Nat.mul_comm n 2]
    ring
  convert hh using 1
  rw [←mul_assoc,hBeq]

end SevenEighths.CenteredMomentOriginalReflectionEnergy

end

end OAI
end OAIOriginalModule2194

/-! Original module: OAI.NumberTheory.DirichletL.Moments.OriginalReflectionErrorMass
Source SHA256: 3c92642c9c77b6279fead5073a4b99afa1fcb88d992a1214aa4dc8e2ba74e549
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2195






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentOriginalReflectionErrorMass
open HeckeFamily HeckeDyadic HeckePrimeAnnular HeckePrimeRay
open CenteredMomentCounting CenteredMomentAbsoluteEnergy CenteredMomentComparisonReflection
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O

lemma annularWeight_zero_norm (W : ℝ→ℂ) (D freq : ℝ) (hD : 0<D)
    (I : Ideal O) (hI : I≠0) :
    ‖annularWeight W D 0 freq I‖=‖W ((I.absNorm:ℝ)/D)‖ := by
  have hn : 0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hn hD)]
  simp only [Complex.neg_re,shift_re,neg_zero,Real.rpow_zero,mul_one]

lemma actual_coefficient_norm (χ : Character) (W : ℝ→ℂ) (D freq B : ℝ)
    (hD : 0<D) (hB : 0≤B) (hW : ∀x,‖W x‖≤B) (I : Ideal O) :
    ‖idealCoeff χ I*annularWeight W D 0 freq I‖≤B := by
  by_cases hI:I=0
  · subst I
    simpa only [idealCoeff_zero,zero_mul,norm_zero] using hB
  rw [norm_mul,annularWeight_zero_norm W D freq hD I hI]
  exact (mul_le_mul (idealCoeff_norm_le_one χ I) (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)

lemma actual_coefficient_support (χ : Character) (W : ℝ→ℂ) (b D freq : ℝ)
    (hD : 0<D) (hs : Function.support W⊆Set.Iic b) (I : Ideal O)
    (hne : idealCoeff χ I*annularWeight W D 0 freq I≠0) :
    (I.absNorm:ℝ)≤max 1 b*D := by
  have hw : W ((I.absNorm:ℝ)/D)≠0:=by
    intro hz
    exact hne (by simp only [annularWeight,hz,zero_mul,mul_zero])
  exact ((div_le_iff₀ hD).mp (hs hw)).trans
    (mul_le_mul_of_nonneg_right (le_max_right 1 b) hD.le)

lemma polynomial_all_ideals (χ : Character) (W : ℝ→ℂ) (D freq : ℝ) :
    polynomial χ false W D 0 freq=
      (D:ℂ)^(-(1/2:ℂ))*∑'I:Ideal O,idealCoeff χ I*annularWeight W D 0 freq I := by
  unfold polynomial
  congr 1
  have he:(∑'I:NonzeroIdeal,idealCoeff χ I.val*annularWeight W D 0 freq I.val)=
      ∑'I:Ideal O,idealCoeff χ I*annularWeight W D 0 freq I:=by
    apply tsum_subtype_eq_of_support_subset (s:={I:Ideal O|I≠0})
      (f:=fun I:Ideal O=>idealCoeff χ I*annularWeight W D 0 freq I)
    intro I hI hz
    subst I
    exact hI (by simp only [idealCoeff_zero,zero_mul])
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,
    annularWeight,mul_assoc] using he

lemma normalized_linear_bound (D c : ℝ) (hD : 0<D) (v : ℂ)
    (hv : ‖v‖≤c*D) : ‖(D:ℂ)^(-(1/2:ℂ))*v‖≤c*Real.sqrt D := by
  rw [inverse_half_power D hD.le,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg D)]
  have hs:Real.sqrt D≠0:=(Real.sqrt_pos.mpr hD).ne'
  have hd:D/Real.sqrt D=Real.sqrt D:=by
    apply (div_eq_iff hs).mpr
    simpa only [pow_two] using (Real.sq_sqrt hD.le).symm
  calc
    _ ≤ (Real.sqrt D)⁻¹*(c*D):=mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr (Real.sqrt_nonneg D))
    _ = c*(D/Real.sqrt D):=by ring
    _ = _:=by rw [hd]

theorem plain_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖polynomial χ false W D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  rw [polynomial_all_ideals]
  apply normalized_linear_bound D _ hD
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>idealCoeff χ I*annularWeight W D 0 freq I)
    (max 1 b*D) B (by positivity) hB (by
      change idealCoeff χ (0:Ideal O)*_ = 0
      rw [idealCoeff_zero,zero_mul])
    (actual_coefficient_norm χ W D freq B hD hB hW)
    (actual_coefficient_support χ W b D freq hD hs)
  convert hh using 1; ring

theorem finite_polynomial_bound (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) (S : Finset (Ideal O)) :
    ‖(D:ℂ)^(-(1/2:ℂ))*∑I∈S,idealCoeff χ I*annularWeight W D 0 freq I‖≤
      (128*max 1 b*B)*Real.sqrt D := by
  apply normalized_linear_bound D _ hD
  let f : Ideal O→ℂ:=fun I=>if I∈S then idealCoeff χ I*annularWeight W D 0 freq I else 0
  have he:(∑'I:Ideal O,f I)=∑I∈S,idealCoeff χ I*annularWeight W D 0 freq I:=by
    rw [tsum_eq_sum (s:=S) (fun I hI=>by simp only [f,ite_eq_right hI])]
    exact Finset.sum_congr rfl (fun I hI=>by simp only [f,ite_eq_left hI])
  have hh:=norm_tsum_ideal_ball f (max 1 b*D) B (by positivity) hB
    (by
      change f (0:Ideal O)=0
      simp only [f,idealCoeff_zero,zero_mul,ite_self])
    (by intro I;dsimp only [f];split_ifs;exact actual_coefficient_norm χ W D freq B hD hB hW I;simpa using hB)
    (by
      intro I hI
      have hm:I∈S:=by by_contra hn;exact hI (by simp only [f,ite_eq_right hn])
      exact actual_coefficient_support χ W b D freq hD hs I (by simpa only [f,ite_eq_left hm] using hI))
  rw [he] at hh
  convert hh using 1; ring

theorem ray_prime_polynomial_bound (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (χ : Character) (W : ℝ→ℂ) (b B D freq : ℝ)
    (hB : 0≤B) (hD : 0<D) (hW : ∀x,‖W x‖≤B)
    (hs : Function.support W⊆Set.Iic b) :
    ‖rayPrimePolynomial M H χ W b D 0 freq‖≤(128*max 1 b*B)*Real.sqrt D := by
  exact finite_polynomial_bound χ W b B D freq hB hD hW hs _

def remainingMultiplier {α : Type*} (J : Finset α)
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (χ : Character) (χslot : α→Character) (Wshort : ℝ→ℂ) (Wslot : α→ℝ→ℂ)
    (b D : α→ℝ) (Xshort omega : ℝ) (freq : α→ℝ) : ℂ :=
  polynomial χ false Wshort Xshort 0 omega*
    ∏j∈J,rayPrimePolynomial M H (χslot j) (Wslot j) (b j) (D j) 0 (freq j)

def errorConstant {α : Type*} (F : Finset α) (bshort Bshort : ℝ) (b B : α→ℝ) : ℝ :=
  (1+(128*max 1 bshort*Bshort)^2)*∏j∈F,max 1 ((128*max 1 (b j)*B j)^2)

lemma errorConstant_pos {α : Type*} (F : Finset α) (bshort Bshort : ℝ) (b B : α→ℝ) :
    0<errorConstant F bshort Bshort b B := by
  apply mul_pos
  · positivity
  · exact Finset.prod_pos (fun j _=>zero_lt_one.trans_le (le_max_left _ _))

theorem remainingMultiplier_sq_bound {α : Type*} (F J : Finset α) (hJ : J⊆F)
    (Wshort : ℝ→ℂ) (Wslot : α→ℝ→ℂ) (bshort Bshort : ℝ) (b B : α→ℝ)
    (hBshort : 0≤Bshort) (hB : ∀j∈F,0≤B j)
    (hWshort : ∀x,‖Wshort x‖≤Bshort) (hWslot : ∀j∈F,∀x,‖Wslot j x‖≤B j)
    (hsshort : Function.support Wshort⊆Set.Iic bshort)
    (hsslot : ∀j∈F,Function.support (Wslot j)⊆Set.Iic (b j))
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (χ : Character) (χslot : α→Character) (D : α→ℝ) (Xshort omega : ℝ) (freq : α→ℝ)
    (hX : 0<Xshort) (hD : ∀j∈J,0<D j) :
    ‖remainingMultiplier J M H χ χslot Wshort Wslot b D Xshort omega freq‖^2≤
      errorConstant F bshort Bshort b B*Xshort*∏j∈J,D j := by
  have hs:=pow_le_pow_left₀ (norm_nonneg _)
    (plain_polynomial_bound χ Wshort bshort Bshort Xshort omega hBshort hX hWshort hsshort) 2
  rw [mul_pow,Real.sq_sqrt hX.le] at hs
  have hj (j:α) (hj:j∈J):
      ‖rayPrimePolynomial M H (χslot j) (Wslot j) (b j) (D j) 0 (freq j)‖^2≤
        (128*max 1 (b j)*B j)^2*D j := by
    have hh:=pow_le_pow_left₀ (norm_nonneg _)
      (ray_prime_polynomial_bound M H (χslot j) (Wslot j) (b j) (B j) (D j) (freq j)
        (hB j (hJ hj)) (hD j hj) (hWslot j (hJ hj)) (hsslot j (hJ hj))) 2
    simpa only [mul_pow,Real.sq_sqrt (hD j hj).le] using hh
  have hc : (128*max 1 bshort*Bshort)^2*(∏j∈J,(128*max 1 (b j)*B j)^2)≤
      errorConstant F bshort Bshort b B := by
    have hp : (∏j∈J,(128*max 1 (b j)*B j)^2)≤∏j∈F,max 1 ((128*max 1 (b j)*B j)^2) :=
      (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) (fun j _=>le_max_right 1 _)).trans
        (Finset.prod_le_prod_of_subset_of_one_le₀ hJ (fun j _=>by positivity)
          (fun j _ _=>le_max_left 1 _))
    exact mul_le_mul (by linarith [sq_nonneg (128*max 1 bshort*Bshort)]) hp
      (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
  calc
    _ = ‖polynomial χ false Wshort Xshort 0 omega‖^2*
      ∏j∈J,‖rayPrimePolynomial M H (χslot j) (Wslot j) (b j) (D j) 0 (freq j)‖^2 := by
        simp only [remainingMultiplier,norm_mul,mul_pow,norm_prod,Finset.prod_pow]
    _ ≤ ((128*max 1 bshort*Bshort)^2*Xshort)*∏j∈J,(128*max 1 (b j)*B j)^2*D j :=
      mul_le_mul hs (Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) hj)
        (Finset.prod_nonneg (fun j _=>sq_nonneg _)) (by positivity)
    _ = ((128*max 1 bshort*Bshort)^2*(∏j∈J,(128*max 1 (b j)*B j)^2))*(Xshort*∏j∈J,D j) := by
      rw [Finset.prod_mul_distrib];ring
    _ ≤ errorConstant F bshort Bshort b B*(Xshort*∏j∈J,D j) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hX.le (Finset.prod_nonneg (fun j hj=>(hD j hj).le)))
    _ = _ := by ring

theorem uniform_radial_error_mass {α : Type*} (F : Finset α)
    (Wshort : ℝ→ℂ) (Wslot : α→ℝ→ℂ) (bshort Bshort : ℝ) (b B : α→ℝ)
    (hBshort : 0≤Bshort) (hB : ∀j∈F,0≤B j)
    (hWshort : ∀x,‖Wshort x‖≤Bshort) (hWslot : ∀j∈F,∀x,‖Wslot j x‖≤B j)
    (hsshort : Function.support Wshort⊆Set.Iic bshort)
    (hsslot : ∀j∈F,Function.support (Wslot j)⊆Set.Iic (b j)) :
    ∃C:ℝ,0<C ∧ ∀J:Finset α,J⊆F →
      ∀(M:Ideal O) [NeZero M] (H:Subgroup (O⧸M)ˣ)
        (χ:O→Character) (χslot:α→O→Character) (omega:O→ℝ) (freq:α→O→ℝ)
        (D:α→ℝ) (Xshort K:ℝ) (Φ:𝓢(ℝ,ℂ)),
        0<Xshort → (∀j∈J,0<D j) → 0<K →
        let P:=fun z:O=>remainingMultiplier J M H (χ z) (fun j=>χslot j z)
          Wshort Wslot b D Xshort (omega z) (fun j=>freq j z)
        Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2) ∧
        (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2)≤
          C*diagonalControl Φ*max 1 K*Xshort*(∏j∈J,D j) ∧
        ∀E:Finset O,(∑z∈E,‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2)≤
          C*diagonalControl Φ*max 1 K*Xshort*(∏j∈J,D j) := by
  let C:=errorConstant F bshort Bshort b B
  have hC:0<C:=errorConstant_pos F bshort Bshort b B
  refine ⟨C,hC,?_⟩
  intro J hJ M _ H χ χslot omega freq D Xshort K Φ hX hD hK P
  let A:=C*Xshort*∏j∈J,D j
  have hA:0≤A:=mul_nonneg (mul_nonneg hC.le hX.le) (Finset.prod_nonneg (fun j hj=>(hD j hj).le))
  have hp (z:O):‖P z‖^2≤A:=remainingMultiplier_sq_bound F J hJ Wshort Wslot
    bshort Bshort b B hBshort hB hWshort hWslot hsshort hsslot M H (χ z) (fun j=>χslot j z)
    D Xshort (omega z) (fun j=>freq j z) hX hD
  have hs:Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2):=
    Summable.of_nonneg_of_le (fun z=>mul_nonneg (norm_nonneg _) (sq_nonneg _))
      (fun z=>mul_le_mul_of_nonneg_left (hp z) (norm_nonneg _))
      ((radial_norm_summable Φ K hK).mul_right A)
  have hb:(∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2)≤
      C*diagonalControl Φ*max 1 K*Xshort*(∏j∈J,D j):=by
    calc
      _ ≤ ∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*A:=
        hs.tsum_le_tsum (fun z=>mul_le_mul_of_nonneg_left (hp z) (norm_nonneg _))
          ((radial_norm_summable Φ K hK).mul_right A)
      _ = (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖)*A:=tsum_mul_right
      _ ≤ (diagonalControl Φ*max 1 K)*A:=
        mul_le_mul_of_nonneg_right (radial_weight_lattice_bound_all Φ K hK) hA
      _ = _:=by dsimp [A];ring
  refine ⟨hs,hb,?_⟩
  intro E
  exact (sum_le_hasSum E (fun z _=>mul_nonneg (norm_nonneg _) (sq_nonneg _)) hs.hasSum).trans hb

lemma compact_norm_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃B:ℝ,0<B ∧ ∀x,‖W x‖≤B := by
  obtain ⟨B,hB,hbound⟩:=fixed_profile_norm_bound W hW a b 0 0 ha
  refine ⟨B,hB,?_⟩
  intro x
  by_cases hx:W x=0
  · simpa only [hx,norm_zero] using hB.le
  · simpa using hbound 0 (by simp) x (hs hx)

theorem smooth_radial_error_mass {α : Type*} (F : Finset α)
    (Wshort : ℝ→ℂ) (Wslot : α→ℝ→ℂ) (ashort bshort : ℝ) (a b : α→ℝ)
    (hashort : 0<ashort) (ha : ∀j∈F,0<a j)
    (hsshort : Function.support Wshort⊆Set.Icc ashort bshort)
    (hsslot : ∀j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWshort : ContDiff ℝ ∞ Wshort) (hWslot : ∀j∈F,ContDiff ℝ ∞ (Wslot j)) :
    ∃C:ℝ,0<C ∧ ∀J:Finset α,J⊆F →
      ∀(M:Ideal O) [NeZero M] (H:Subgroup (O⧸M)ˣ)
        (χ:O→Character) (χslot:α→O→Character) (omega:O→ℝ) (freq:α→O→ℝ)
        (D:α→ℝ) (Xshort K:ℝ) (Φ:𝓢(ℝ,ℂ)),
        0<Xshort → (∀j∈J,0<D j) → 0<K →
        let P:=fun z:O=>remainingMultiplier J M H (χ z) (fun j=>χslot j z)
          Wshort Wslot b D Xshort (omega z) (fun j=>freq j z)
        Summable (fun z:O=>‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2) ∧
        (∑'z:O,‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2)≤
          C*diagonalControl Φ*max 1 K*Xshort*(∏j∈J,D j) ∧
        ∀E:Finset O,(∑z∈E,‖Φ (‖eisEmbedding z‖^2/K)‖*‖P z‖^2)≤
          C*diagonalControl Φ*max 1 K*Xshort*(∏j∈J,D j) := by
  obtain ⟨Bshort,hBshort,hshort⟩:=compact_norm_bound Wshort ashort bshort hashort hsshort hWshort.continuous
  have hex (j:α):∃B:ℝ,0≤B ∧ (j∈F → ∀x,‖Wslot j x‖≤B):=by
    by_cases hj:j∈F
    · obtain ⟨B,hB,hbound⟩:=compact_norm_bound (Wslot j) (a j) (b j) (ha j hj) (hsslot j hj) (hWslot j hj).continuous
      exact ⟨B,hB.le,fun _=>hbound⟩
    · exact ⟨0,le_rfl,fun h=>False.elim (hj h)⟩
  choose B hB hbound using hex
  exact uniform_radial_error_mass F Wshort Wslot bshort Bshort b B hBshort.le
    (fun j _=>hB j) hshort hbound (fun x hx=>(hsshort hx).2)
    (fun j hj x hx=>(hsslot j hj hx).2)

