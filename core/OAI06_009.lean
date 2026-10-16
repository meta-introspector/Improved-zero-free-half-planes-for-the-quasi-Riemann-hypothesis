  simp only [hi, Finset.notMem_empty] at h

theorem assignedTuples_card_of_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι]
    (L : ι → Finset (Ideal O)) : (assignedTuples L).card = 1 := by
  simp [assignedTuples]

end SevenEighths.DetectorDictionaryInverseAssignedCount

end

end OAI
end OAIOriginalModule1696

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceProfileMass
Source SHA256: 6bc7a7f76d8ccb7dd9d6ba6e7b49f72810afd83285f58cb3de5a90a4f6d95275
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1697


namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceProfileMass
open ActualEisensteinCubic CenteredMomentPrimary CenteredMomentRectangle
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
local notation "O" => ActualEisensteinCubic.O

 theorem primary_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (I : Ideal O) :
    primaryIdealCharacter 1 χ I=1 := by
  rw [primaryIdealCharacter_apply]
  have he : Ideal.Quotient.mk (Ideal.span {(1:O)}) (CompletedGauss.primaryGenerator I)=1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(1:O)}))]
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.span_singleton_one]
    trivial
  rw [he,map_one]

 theorem idealWeight_mod_one (χ : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) (R I : Ideal O) :
    CenteredMomentRectangle.idealWeight 1 χ R 0 I=(if IsCoprime I R then 1 else 0) := by
  simp only [idealWeight,primary_mod_one,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]

def profileCoefficient {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))*
    (if s∣finiteTupleProduct v then 1 else 0)

 theorem profileCoefficient_eq_original {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      originalFiniteCoefficient 1 (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  rw [originalFiniteCoefficient,idealWeight_mod_one]
  rfl

theorem profile_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Ideal O) (ν : ι → Ideal O → ℂ),
      (∀ j I,‖ν j I‖≤1) → ∀ (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ S : Finset (Tuple ι),
      (∑ v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
        C*(T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j,P j) := by
  obtain ⟨C,hC,ht⟩ := smooth_finite_source_mass_uniform Wslot W₁ W₂ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  simp_rw [profileCoefficient_eq_original]
  exact ht 1 one_ne_zero 1 R 0 ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S

end SevenEighths.CenteredMomentSourceProfileMass

end

end OAI
end OAIOriginalModule1697

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AbsoluteEnergy
Source SHA256: 36cfa538becc649184d1f4b312b01c23008d7c84c5aa1540c9212a40f32de49a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1698



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentAbsoluteEnergy
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion
open CenteredMomentHeckeExpansion CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one_all (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) : ‖rowWeight η m A z t I‖ ≤ 1 := by
  by_cases hI : I=0
  · subst I
    rw [map_zero,norm_zero]
    norm_num
  · exact CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η m A z t I hI

theorem radial_norm_summable (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖Φ (‖eisEmbedding z‖^2/K)‖) := by
  simpa only [scaledRadialTest_apply] using
    actual_eisenstein_summable_norm (scaledRadialTest Φ K hK)

theorem radial_weight_lattice_bound_all (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑' z : O, ‖Φ (‖eisEmbedding z‖^2/K)‖) ≤ diagonalControl Φ*max 1 K := by
  by_cases hlarge : 1≤K
  · simpa only [max_eq_right hlarge] using radial_weight_lattice_bound Φ K hlarge
  have hsmall : K≤1 := (not_le.mp hlarge).le
  let B := 4*(Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have hB : 0≤B := by dsimp [B]; positivity
  have hp (z : O) : ‖Φ (‖eisEmbedding z‖^2/K)‖ ≤
      B*((1+1*‖eisEmbedding z‖^2)^2)⁻¹ := by
    have hq : 0≤‖eisEmbedding z‖^2/K := div_nonneg (sq_nonneg _) hK.le
    have hh := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (2,0)) (k := 2) (n := 0) le_rfl le_rfl Φ (‖eisEmbedding z‖^2/K)
    simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hq] at hh
    norm_num only [show (2:ℝ)^2=4 by norm_num] at hh
    change (1+‖eisEmbedding z‖^2/K)^2*‖Φ (‖eisEmbedding z‖^2/K)‖≤B at hh
    have hq' : ‖eisEmbedding z‖^2≤‖eisEmbedding z‖^2/K := by
      apply (le_div_iff₀ hK).mpr
      exact mul_le_of_le_one_right (sq_nonneg _) hsmall
    have hden : (1+1*‖eisEmbedding z‖^2)^2≤(1+‖eisEmbedding z‖^2/K)^2 := by
      simp only [one_mul]
      gcongr
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hden (norm_nonneg _)).trans hh
  have hb := (radial_norm_summable Φ K hK).tsum_le_tsum hp
    ((scaled_eisenstein_cauchy_summable 1 (by norm_num)).mul_left B)
  rw [tsum_mul_left] at hb
  have hc := scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
  simp only [one_mul] at hc hb
  have ht := hb.trans (mul_le_mul_of_nonneg_left hc hB)
  rw [max_eq_left hsmall,mul_one]
  dsimp only [B] at ht
  unfold diagonalControl
  nlinarith

theorem finite_hecke_polynomial_norm (η : Character) (m A z : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    ‖∑ I∈S,c I*rowWeight η m A z t I‖ ≤ ∑ I∈S,‖c I‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)

theorem finite_hecke_energy_summable (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
      Φ (‖eisEmbedding z‖^2/K)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (f := fun z : O => (∑ I∈S,‖c I‖)^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
      (norm_nonneg _)
  · exact (radial_norm_summable Φ K hK).mul_left _

theorem finite_hecke_energy_absolute (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    ‖finiteHeckeEnergy η m A t S c Φ K‖ ≤
      diagonalControl Φ*max 1 K*(∑ I∈S,‖c I‖)^2 := by
  have hs := (finite_hecke_energy_summable η m A t S c Φ K hK).norm
  calc
    _ ≤ ∑' z : O, ‖((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
        Φ (‖eisEmbedding z‖^2/K)‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' z : O,(∑ I∈S,‖c I‖)^2*‖Φ (‖eisEmbedding z‖^2/K)‖ := by
      apply hs.tsum_le_tsum _ ((radial_norm_summable Φ K hK).mul_left _)
      intro z
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (finite_hecke_polynomial_norm η m A z t S c) 2)
        (norm_nonneg _)
    _ = (∑ I∈S,‖c I‖)^2*(∑' z : O,‖Φ (‖eisEmbedding z‖^2/K)‖) := tsum_mul_left
    _ ≤ (∑ I∈S,‖c I‖)^2*(diagonalControl Φ*max 1 K) :=
      mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) (sq_nonneg _)
    _ = _ := by ring

theorem smooth_subset_source_absolute_energy {α : Type*} (F : Finset α)
    (Wslot : α → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (a b : α → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j∈F,0<a j) (hb : ∀ j∈F,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j∈F,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hWslot : ∀ j∈F,ContDiff ℝ ∞ (Wslot j)) (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂) :
    ∃ C : ℝ,0<C ∧ ∀ J : Finset α,J⊆F →
      ∀ (η : Character) (m A : O) (t : ℝ) (R : Ideal O) (ν : α → Ideal O → ℂ),
      (∀ j∈J,∀ I,‖ν j I‖≤1) →
      ∀ (P : α → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j∈J,0<P j) → 0<X₁ → 0<X₂ → 0<Y₁ → 0<Y₂ → B₁≠0 → B₂≠0 →
      X₁*X₂=T → Y₁*Y₂=T → ∀ (S : Finset (Tuple J)) (K : ℝ),0<K →
      let H := (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏ j∈J,P j)
      let E := finiteHeckeEnergy η m A t (finiteColumns S)
        (finiteColumnCoefficient S (profileCoefficient R (fun j : J => ν j.val)
          (fun j : J => Wslot j.val) (fun j : J => P j.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)) Φ K
      ‖E‖≤C*max 1 K*H^2 ∧ ‖E‖/H≤C*max 1 K*H := by
  obtain ⟨D,hD,hm⟩ := smooth_subset_source_mass_uniform F Wslot W₁ W₂ a b a₁ b₁ a₂ b₂
    ha hb ha₁ hb₁ ha₂ hb₂ hsSlot hs₁ hs₂ hWslot hW₁ hW₂
  let C := (diagonalControl Φ+1)*D^2
  have hd := diagonalControl_nonneg Φ
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro J hJ η m A t R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S K hK H E
  have hmass := (hm J hJ 1 one_ne_zero 1 R 0 ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S).2
  have hmass' : (∑ I∈finiteColumns S,‖finiteColumnCoefficient S
      (profileCoefficient R (fun j : J => ν j.val) (fun j : J => Wslot j.val)
        (fun j : J => P j.val) W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I‖)≤D*H := by
    simpa only [finiteColumnCoefficient,profileCoefficient_eq_original,H,mul_assoc] using hmass
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hNB₁ : 0<(Ideal.absNorm B₁:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₁)
  have hNB₂ : 0<(Ideal.absNorm B₂:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB₂)
  have hprod : 0<∏ j∈J,P j := Finset.prod_pos hP
  have hH : 0<H := by dsimp only [H]; positivity
  have hmax : 0≤max 1 K := le_trans zero_le_one (le_max_left _ _)
  have he : ‖E‖≤C*max 1 K*H^2 := by
    apply (finite_hecke_energy_absolute η m A t (finiteColumns S) _ Φ K hK).trans
    calc
      _ ≤ diagonalControl Φ*max 1 K*(D*H)^2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass' 2)
          (mul_nonneg hd hmax)
      _ ≤ (diagonalControl Φ+1)*max 1 K*(D*H)^2 := by gcongr; linarith
      _ = C*max 1 K*H^2 := by dsimp only [C]; ring
  refine ⟨he,?_⟩
  apply (div_le_iff₀ hH).mpr
  convert he using 1; ring

end SevenEighths.CenteredMomentAbsoluteEnergy

end

end OAI
end OAIOriginalModule1698

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonProfile
Source SHA256: f18b6eea1fe2ba9e9482f8d0d0b511f1aa29775e944c75ed84d9bc233a09ad3a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1699



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonProfile
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonPrimeSlots CenteredMomentCommonAllocationBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def liveIndices (B : Tuple ι) : Finset ι := Finset.univ.filter (fun i => B (Sum.inl i)=1)

def remainingTuple (B u : Tuple ι) : Tuple (liveIndices B) :=
  Sum.elim (fun i => u (Sum.inl i.val)) (fun j => u (Sum.inr j))

@[simp] theorem remainingTuple_slot (B u : Tuple ι) (i : liveIndices B) :
    remainingTuple B u (Sum.inl i)=u (Sum.inl i.val) := rfl

@[simp] theorem remainingTuple_plain (B u : Tuple ι) (j : Fin 2) :
    remainingTuple B u (Sum.inr j)=u (Sum.inr j) := rfl

theorem remaining_product (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    finiteTupleProduct u=finiteTupleProduct (remainingTuple B u) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,remainingTuple,
    Sum.elim_inl,Sum.elim_inr]
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => u (Sum.inl i))]
  congr 1
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  apply hf i
  intro hBi
  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBi⟩)

theorem slot_profiles_split (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (β : ι → Ideal O → ℂ) :
    (∏ i,β i (B (Sum.inl i)*u (Sum.inl i)))=
      (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),β i (B (Sum.inl i)))*
        ∏ i : liveIndices B,β i.val (u (Sum.inl i.val)) := by
  rw [Finset.prod_coe_sort (liveIndices B) (fun i => β i (u (Sum.inl i)))]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1)
    (fun i => β i (B (Sum.inl i)*u (Sum.inl i))),mul_comm]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hf i (Finset.mem_filter.mp hi).2,mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2,one_mul]

theorem profile_common_allocation (B u : Tuple ι) (C R s : Ideal O)
    (hB : finiteTupleProduct B=C) (hsC : s∣C)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
        profileCoefficient R (fun i : liveIndices B => ν i.val) (fun i => Wslot i.val) (fun i => P i.val)
          W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 (remainingTuple B u) := by
  have hprod : finiteTupleProduct (fun i => B i*u i)=C*finiteTupleProduct (remainingTuple B u) := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct u=_
    rw [hB,remaining_product B u hf]
  have hdiv : s∣C*finiteTupleProduct (remainingTuple B u) := dvd_mul_of_dvd_left hsC _
  unfold profileCoefficient
  rw [slot_profiles_split B u hf (fun i I => ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)),hprod]
  simp only [hdiv,ite_true,one_dvd,mul_one,remainingTuple_slot,remainingTuple_plain,
    IsCoprime.mul_left_iff]
  rw [mul_assoc B₁,mul_assoc B₂]
  by_cases hC : IsCoprime C R <;>
    by_cases hu : IsCoprime (finiteTupleProduct (remainingTuple B u)) R <;>
    simp_all only [true_and,false_and,ite_true,ite_false,mul_zero,zero_mul,mul_one]
  ring

theorem actual_frozen_slots (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : Tuple ι) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,IdealMobiusDivisorSum.primeSupport (B i)⊆IdealMobiusDivisorSum.primeSupport C)
    (u : Tuple ι) (hu : u∈residualBoxes S C B hB)
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) :
    ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 := by
  intro i hi
  rcases prime_coordinate_cases S hS C hC B hB hBs u hu (Sum.inl i) (hp i) with h|h
  · exact False.elim (hi h.1)
  · exact h.1

end SevenEighths.CenteredMomentCommonProfile

end

end OAI
end OAIOriginalModule1699

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonPuncture
Source SHA256: 0a0626cf48c4fad5d299bf98147e00c2c5708285a29318144c94633750a7549a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1700


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonPuncture
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O

 theorem residualBoxes_filter {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0) :
    residualBoxes S C B hB=
      (Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i))).filter
        (fun u => IsCoprime C (∏ i,u i)) := by
  ext u
  simp only [residualBoxes,Fintype.mem_piFinset,Finset.mem_filter,
    IsCoprime.prod_right_iff,Finset.mem_univ,forall_const]
  exact forall_and

theorem residualBoxes_sum {ι : Type*} [Fintype ι]
    (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (F : (ι → Ideal O) → ℂ) :
    (∑ u∈residualBoxes S C B hB,F u)=
      ∑ u∈Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i)),
        (if IsCoprime C (∏ i,u i) then 1 else 0)*F u := by
  rw [residualBoxes_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  split_ifs <;> simp

theorem profileCoefficient_puncture {ι : Type*} [Fintype ι]
    (C R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    (if IsCoprime C (finiteTupleProduct v) then 1 else 0)*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v := by
  unfold profileCoefficient
  rw [IsCoprime.mul_right_iff,show IsCoprime C (finiteTupleProduct v) ↔ IsCoprime (finiteTupleProduct v) C from isCoprime_comm]
  by_cases hC : IsCoprime (finiteTupleProduct v) C <;>
    by_cases hR : IsCoprime (finiteTupleProduct v) R <;> simp [hC,hR]

theorem residual_profile_sum {ι : Type*} [Fintype ι]
    (S : (ι ⊕ Fin 2) → Finset (Ideal O)) (C : Ideal O) (B : Tuple ι) (hB : ∀ i,B i≠0)
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (F : Tuple ι → ℂ) :
    (∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u*F u)=
      ∑ u∈Fintype.piFinset (fun i => residualPool (B i) (hB i) (S i)),
        profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u*F u := by
  have he (u : Tuple ι) :
      (if IsCoprime C (∏ i,u i) then 1 else 0)*
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u=
        profileCoefficient (R*C) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u :=
    profileCoefficient_puncture C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s u
  rw [residualBoxes_sum]
  simp_rw [← mul_assoc,he]
  apply Finset.sum_congr
  · ext u
    simp only [Fintype.mem_piFinset]
  · intro u hu
    rfl

end SevenEighths.CenteredMomentCommonPuncture

end

end OAI
end OAIOriginalModule1700

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PositiveSummability
Source SHA256: 5e9c587aa2b23ffa17600f0c50cd207d058dfb80d39175900ba835778d9d43e5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1701



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentPositiveSummability
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceMass
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile CenteredMomentDivisorRetained
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction CenteredMomentDivisorAllocation
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O

lemma plain_finite_norm (η:Character) (m A z:O) (t:ℝ) (W:ℝ→ℂ) (b X:ℝ)
    (hs:Function.support W⊆Set.Iic b) (hX:0<X) :
    ‖rowTwistedSum η m A z W t X‖≤∑I∈idealBall (b*X),‖W ((Ideal.absNorm I:ℝ)/X)‖ := by
  rw [rowTwistedSum_eq_weight,tsum_eq_sum (s:=idealBall (b*X)) ?_]
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)
  · intro I hI
    by_cases h0:I=0
    · subst I
      simp only [map_zero,zero_mul]
    · have hw:W ((Ideal.absNorm I:ℝ)/X)=0 := by
        by_contra hn
        have hh:=hs hn
        have hbound:(Ideal.absNorm I:ℝ)≤b*X:=(div_le_iff₀ hX).mp hh
        exact hI ((mem_idealBall _ _).mpr ⟨h0,hbound⟩)
      rw [hw,mul_zero]

lemma slot_finite_norm (η:Character) (m A z:O) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) :
    ‖rowSlot η m A z S β t‖≤∑I∈S,‖β I‖ := by
  rw [rowSlot_eq_weight]
  exact finite_hecke_polynomial_norm η m A z t S β

lemma bounded_radial_summable (F:O→ℂ) (B:ℝ) (hF:∀z,‖F z‖≤B)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (f:=fun z:O=>B^2*‖Φ (‖eisEmbedding z‖^2/K)‖)
  · intro z
    split_ifs
    · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hF z) 2)
        (Complex.abs_re_le_norm _) (abs_nonneg _) (sq_nonneg _)
    · simp only [norm_zero]
      positivity
  · exact (radial_norm_summable Φ K hK).mul_left _

lemma product_bounded {ι:Type*} [Fintype ι]
    (η:Character) (m A:O) (t:ℝ) (c:ℂ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) :
    ∃B:ℝ,∀z:O,‖c*((rowTwistedSum η m A z W₁ t X₁*
      rowTwistedSum η m A z W₂ t X₂)*∏i,rowSlot η m A z (S i) (β i) t)‖≤B := by
  refine ⟨‖c‖*((∑I∈idealBall (b₁*X₁),‖W₁ ((Ideal.absNorm I:ℝ)/X₁)‖)*
    (∑I∈idealBall (b₂*X₂),‖W₂ ((Ideal.absNorm I:ℝ)/X₂)‖)*
    ∏i,∑I∈S i,‖β i I‖),?_⟩
  intro z
  rw [norm_mul,norm_mul,norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul
  · exact mul_le_mul (plain_finite_norm η m A z t W₁ b₁ X₁ hs₁ hX₁)
      (plain_finite_norm η m A z t W₂ b₂ X₂ hs₂ hX₂) (norm_nonneg _) (by positivity)
  · exact Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _) (fun i _=>slot_finite_norm η m A z t (S i) (β i))
  · positivity
  · positivity

 theorem retained_positive_summable {ι:Type*} [Fintype ι]
    (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  unfold retainedPositiveRow positiveSlotRow
  simp_rw [←clipped_rowTwistedSum η m A _ W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A _ W₂ t X₂ hX₂]
  obtain ⟨B,hB⟩:=product_bounded η m A t
    (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem allocated_positive_summable {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (D:Ideal O) (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    Summable (fun z:O=>if keep z then ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0) := by
  have hN (j:Fin 2):(0:ℝ)<Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedPositiveRow
  exact retained_positive_summable η m A t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) _ _ _ keep Φ K hK

end SevenEighths.CenteredMomentPositiveSummability

end

end OAI
end OAIOriginalModule1701

/-! Original module: OAI.NumberTheory.DirichletL.Moments.InductionEnergy
Source SHA256: 010e75c398c3a7a7a50399baa3b293371367ec45a6fd7b81f9662be6e787ce44
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1702


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentInductionEnergy
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentPositiveSummability
open CenteredMomentCounting CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def energy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ) (X₁ X₂:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
    (Φ (‖eisEmbedding z‖^2/K)).re else 0

lemma plain_absolute (η:Character) (m A z:O) (t:ℝ) (W:ℝ→ℂ) (b B X:ℝ)
    (hb:0≤b) (hB:0≤B) (hX:0<X) (hs:Function.support W⊆Set.Iic b)
    (hW:∀x,‖W x‖≤B) : ‖rowTwistedSum η m A z W t X‖≤(128*b*B)*X := by
  rw [rowTwistedSum_eq_weight]
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=>rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X))
    (b*X) B (mul_nonneg hb hX.le) hB (by change rowWeight η m A z t (0:Ideal O)*_=0; rw [map_zero,zero_mul])
    (fun I=>by rw [norm_mul]; exact (mul_le_mul (rowWeight_norm_le_one_all η m A z t I)
      (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    (fun I hi=>(div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hi)))
  convert hh using 1 ; ring

omit [DecidableEq ι] in
lemma positive_squared_absolute (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤
      ((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i) := by
  let L:ℝ:=(128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i)
  let T:ℝ:=X₁*X₂*∏i,P i
  have hL:0≤L:=mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (Finset.prod_nonneg (fun i _=>mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hB i)))
  have hT:0<T:=mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=>hP i))
  have hsum:‖(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
      ∏i,rowSlot η m A z (S i) (β i) t‖≤L*T := by
    rw [norm_mul,norm_mul,norm_prod]
    have hp:=Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _=>norm_nonneg (rowSlot η m A z (S i) (β i) t))
      (fun i _=>rowSlot_bound η m A z (S i) (β i) t (b i*P i) (B i)
        (mul_nonneg (hb i) (hP i).le) (hB i) (hβ i) (hN i))
    have hq:=mul_le_mul
      (mul_le_mul (plain_absolute η m A z t W₁ b₁ B₁ X₁ hb₁ hB₁ hX₁ hs₁ hW₁)
        (plain_absolute η m A z t W₂ b₂ B₂ X₂ hb₂ hB₂ hX₂ hs₂ hW₂) (norm_nonneg _) (by positivity))
      hp (by positivity) (by positivity)
    apply hq.trans_eq
    simp only [mul_left_comm (B _) (b _),mul_assoc,Finset.prod_mul_distrib]
    dsimp [L,T]
    simp only [Finset.prod_mul_distrib]
    ring
  unfold positiveSlotRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hT]
  calc
    _≤(L*T)^2/T:=div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsum 2) hT.le
    _=L^2*T:=by field_simp

omit [DecidableEq ι] in
theorem energy_absolute (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K≤
      diagonalControl Φ*max 1 K*
        (((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)) := by
  let E:ℝ:=((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)
  have hE:0≤E:=mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hX₁.le hX₂.le)
    (Finset.prod_nonneg (fun i _=>(hP i).le)))
  have hp (z:O):‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤E:=
    positive_squared_absolute η m A z t W₁ W₂ b₁ b₂ B₁ B₂ X₁ X₂ hb₁ hb₂ hB₁ hB₂
      hX₁ hX₂ hs₁ hs₂ hW₁ hW₂ S β P b B hP hb hB hβ hN
  have hs:=bounded_radial_summable
    (fun z:O=>positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂) (Real.sqrt E)
    (fun z=>Real.le_sqrt_of_sq_le (hp z)) keep Φ K hK
  have hbnd:=hs.tsum_le_tsum (g:=fun z:O=>E*‖Φ (‖eisEmbedding z‖^2/K)‖) (fun z=>by
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hp z) (norm_nonneg _))
    · positivity) ((radial_norm_summable Φ K hK).mul_left E)
  rw [tsum_mul_left] at hbnd
  exact hbnd.trans ((mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) hE).trans_eq (mul_comm _ _))

end SevenEighths.CenteredMomentInductionEnergy

end

end OAI
end OAIOriginalModule1702

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RadialEligibleEnergy
Source SHA256: 97229b52aab2de72235465a510f4990bb864f2e4af88961fc7811809827476e9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1703



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentPositiveSummability
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

structure Radial where
  keep : O→Prop
  profile : 𝓢(ℝ,ℂ)
  scale : ℝ
  scale_pos : 0<scale
  nonneg : ∀z:O,0≤(profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/scale)).re

def Radial.weight (r:Radial) (z:O) : ℝ :=
  if r.keep z then (r.profile (‖ConcreteTraceCRT.eisEmbedding z‖^2/r.scale)).re else 0

lemma Radial.weight_nonneg (r:Radial) (z:O) : 0≤r.weight z := by
  unfold Radial.weight
  split_ifs
  · exact r.nonneg z
  · rfl

def finiteData (s:Data ι) (r:Radial) (S:Finset O) : Data ι :=
  {s with rows:=S,weight:=r.weight,weight_nonneg:=fun z _=>r.weight_nonneg z}

def energy (s:Data ι) (r:Radial) (D:Ideal O) : ℝ :=
  ∑'z:O,r.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    CenteredMomentDivisorRowEnergy.maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def childEnergy (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑'z:O,r.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

lemma child_summable (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :
    Summable (fun z:O=>r.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)) := by
  have hX:=allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.slots s.coefficient s.P D a
    r.keep r.profile r.scale r.scale_pos
  have hY:=allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.Y₁_pos s.Y₂_pos s.slots s.coefficient s.P D a
    r.keep r.profile r.scale r.scale_pos
  convert hX.add hY using 1
  funext z
  unfold Radial.weight
  split_ifs <;> ring

lemma finite_child_le (s:Data ι) (r:Radial) (S:Finset O) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :
    (finiteData s r S).childEnergy D a≤childEnergy s r D a := by
  exact sum_le_hasSum S (fun z _=>mul_nonneg (r.weight_nonneg z)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))) (child_summable s r D a).hasSum

lemma energy_nonneg (s:Data ι) (r:Radial) (D:Ideal O) : 0≤energy s r D :=
  tsum_nonneg (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))

lemma child_nonneg (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0≤childEnergy s r D a :=
  tsum_nonneg (fun z=>mul_nonneg (r.weight_nonneg z) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial),∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentEligibleEnergy.actual_source_from_children N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD E hE hchild
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))
  intro S
  exact hbound (finiteData s r S) D hD E hE
    (fun a ha=>(finite_child_le s r S D a).trans (hchild a ha))

 theorem actual_source_root_from_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial),∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      Real.sqrt (energy s r D)≤C*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)*Real.sqrt (s.profileFactor*E)*
        ∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P) := by
  obtain ⟨C,hC,hbase⟩:=actual_source_from_children (ι:=ι) N hslots ε hε
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro s r D hD E hE hc
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he:0≤s.profileFactor*E:=mul_nonneg s.profile_nonneg hE
  have hs:=sqrt_sum_le (s.toSource.active D) (fun a=>1/formalReductionFactor D a s.P)
    (fun a _=>div_nonneg zero_le_one (s.reduction_pos D a).le)
  simp_rw [sqrt_reciprocal _ (s.reduction_pos D _)] at hs
  have hh:=Real.sqrt_le_sqrt (hbase s r D hD E hE hc)
  have hrew:C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)=
      (C*(Ideal.absNorm D:ℝ)^ε*(s.profileFactor*E))*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P):=by ring
  rw [hrew,Real.sqrt_mul (mul_nonneg (mul_nonneg hC.le hp) he),
    Real.sqrt_mul (mul_nonneg hC.le hp),Real.sqrt_mul hC.le] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end SevenEighths.CenteredMomentRadialEligibleEnergy

end

end OAI
end OAIOriginalModule1703

/-! Original module: OAI.NumberTheory.DirichletL.Moments.BottomStage
Source SHA256: daca85093d88bf17cbab0b0d483b6f988b68d71971b1846efd44bdd6a27bb4cb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1704




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentBottomStage
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentInductionEnergy CenteredMomentAbsoluteEnergy QuadraticInitialBound
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι]

 def positiveEnergy (s:Data ι) (r:Radial) : ℝ :=
  CenteredMomentInductionEnergy.energy s.η s.m s.A s.t s.W₁ s.W₂ s.slots s.coefficient s.P
    s.X₁ s.X₂ r.keep r.profile r.scale

 def profileMass (s:Data ι) (B₁ B₂:ℝ) : ℝ :=
  ((128*max 0 s.b₁*B₁)*(128*max 0 s.b₂*B₂)*(∏i,128*max 0 (s.hi i)*s.M i))^2

 theorem actual_absolute (s:Data ι) (r:Radial) (B₁ B₂:ℝ) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hW₁:∀x,‖s.W₁ x‖≤B₁) (hW₂:∀x,‖s.W₂ x‖≤B₂) :
    positiveEnergy s r≤diagonalControl r.profile*max 1 r.scale*profileMass s B₁ B₂*
      (s.X₁*s.X₂*∏i,s.P i) := by
  have hs₁:Function.support s.W₁⊆Set.Iic (max 0 s.b₁):=
    by
      intro x hx
      change x≤max 0 s.b₁
      have hs:x≤s.b₁:=s.support₁ hx
      exact hs.trans (le_max_right 0 s.b₁)
  have hs₂:Function.support s.W₂⊆Set.Iic (max 0 s.b₂):=
    by
      intro x hx
      change x≤max 0 s.b₂
      have hs:x≤s.b₂:=s.support₂ hx
      exact hs.trans (le_max_right 0 s.b₂)
  have hN:∀i,∀I∈s.slots i,s.coefficient i I≠0 →
      (Ideal.absNorm I:ℝ)≤max 0 (s.hi i)*s.P i:=by
    intro i I hI hn
    have hw:s.W i ((Ideal.absNorm I:ℝ)/s.P i)≠0:=by
      intro hw
      apply hn
      simp only [Data.coefficient,hw,mul_zero]
    have hs:=s.support i hw
    exact (div_le_iff₀ (s.P_pos i)).mp (hs.2.trans (le_max_right _ _))
  have hh:=energy_absolute s.η s.m s.A s.t s.W₁ s.W₂
    (max 0 s.b₁) (max 0 s.b₂) B₁ B₂ s.X₁ s.X₂ (le_max_left _ _) (le_max_left _ _) hB₁ hB₂
    s.X₁_pos s.X₂_pos hs₁ hs₂ hW₁ hW₂
    s.slots s.coefficient s.P (fun i=>max 0 (s.hi i)) s.M s.P_pos
    (fun i=>le_max_left _ _) (fun i=>zero_le_one.trans (s.M_ge_one i)) s.coefficient_bound
    hN r.keep r.profile r.scale r.scale_pos
  exact hh.trans_eq (by unfold profileMass;ring)

 theorem actual_bottom_band (s:Data ι) (r:Radial) (B₁ B₂:ℝ) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hW₁:∀x,‖s.W₁ x‖≤B₁) (hW₂:∀x,‖s.W₂ x‖≤B₂)
    (Z m M σ:ℝ) (hZ:1<Z) (hK:1≤r.scale) (hm:m≤σ)
    (hrow:r.scale≤Z^m) (hsource:s.X₁*s.X₂*∏i,s.P i≤Z^M) :
    positiveEnergy s r≤(diagonalControl r.profile*profileMass s B₁ B₂)*Z^(M+σ) := by
  have hh:=actual_absolute s r B₁ B₂ hB₁ hB₂ hW₁ hW₂
  rw [max_eq_right hK] at hh
  have hp:0≤profileMass s B₁ B₂:=sq_nonneg _
  have hd:0≤diagonalControl r.profile:=diagonalControl_nonneg _
  have hs:0≤s.X₁*s.X₂*∏i,s.P i:=(mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))).le
  have hpow:r.scale*(s.X₁*s.X₂*∏i,s.P i)≤Z^(M+σ):=by
    apply (mul_le_mul hrow hsource hs (Real.rpow_nonneg (by linarith) _)).trans
    rw [←Real.rpow_add (zero_lt_one.trans hZ)]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply hh.trans
  calc
    _=(diagonalControl r.profile*profileMass s B₁ B₂)*(r.scale*(s.X₁*s.X₂*∏i,s.P i)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hpow (mul_nonneg hd hp)

end SevenEighths.CenteredMomentBottomStage

end

end OAI
end OAIOriginalModule1704

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CoreFloor
Source SHA256: 1188d36e5d356fc2c0dc9ad25320b485b145d4f451fe85f45716f1866d2e5df4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1705


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCoreFloor
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentPositiveSummability
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O" => HeckeFamily.O

 def zeroRow (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ):ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)

 def zeroEnergy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):ℝ :=
  ∑'z:O,if r.keep z then ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2*
    (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0

 theorem zero_energy_eq (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r=
    energy η m A t W₁ W₂ (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      X₁ X₂ r.keep r.profile r.scale:=by
  simp [zeroEnergy,energy,zeroRow,positiveSlotRow]

 theorem zero_absolute (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁)(hb₂:0≤b₂)(hB₁:0≤B₁)(hB₂:0≤B₂)
    (hX₁:0<X₁)(hX₂:0<X₂)(hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂)(hW₁:∀x,‖W₁ x‖≤B₁)(hW₂:∀x,‖W₂ x‖≤B₂)
    (r:Radial):
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r≤
      diagonalControl r.profile*max 1 r.scale*((128*b₁*B₁)*(128*b₂*B₂))^2*(X₁*X₂):=by
  rw [zero_energy_eq]
  have h:=energy_absolute (ι:=Fin 0) η m A t W₁ W₂ b₁ b₂ B₁ B₂ X₁ X₂
    hb₁ hb₂ hB₁ hB₂ hX₁ hX₂ hs₁ hs₂ hW₁ hW₂
    (fun _=>∅) (fun _=>0) (fun _=>1) (fun _=>1) (fun _=>1)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    r.keep r.profile r.scale r.scale_pos
  simpa only [Fin.prod_univ_zero,mul_one,mul_assoc] using h

 theorem zero_padded_core (η:Character) (mask A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂:ℝ) (hb₁:0≤b₁)(hb₂:0≤b₂)(hB₁:0≤B₁)(hB₂:0≤B₂)
    (hs₁:Function.support W₁⊆Set.Iic b₁)(hs₂:Function.support W₂⊆Set.Iic b₂)
    (hW₁:∀x,‖W₁ x‖≤B₁)(hW₂:∀x,‖W₂ x‖≤B₂)
    (r:Radial)(Z m q n₁ n₂ ρ δ:ℝ)(hZ:1<Z)(hm:0≤m)(hq:0≤q)
    (hscale:r.scale=Z^m)(hfloor:m+q≤ρ)(hcore:n₁+n₂≤m+q+δ):
    zeroEnergy η mask A t W₁ W₂ (Z^n₁) (Z^n₂) r≤
      (diagonalControl r.profile*((128*b₁*B₁)*(128*b₂*B₂))^2)*Z^(m+q+ρ+δ):=by
  have hZ0:0<Z:=zero_lt_one.trans hZ
  have h:=zero_absolute η mask A t W₁ W₂ b₁ b₂ B₁ B₂ (Z^n₁) (Z^n₂)
    hb₁ hb₂ hB₁ hB₂ (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    hs₁ hs₂ hW₁ hW₂ r
  rw [hscale,max_eq_right (Real.one_le_rpow hZ.le hm)] at h
  have hp:Z^m*(Z^n₁*Z^n₂)≤Z^(m+q+ρ+δ):=by
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply h.trans
  calc
    _=(diagonalControl r.profile*((128*b₁*B₁)*(128*b₂*B₂))^2)*(Z^m*(Z^n₁*Z^n₂)):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hp (mul_nonneg (diagonalControl_nonneg _) (sq_nonneg _))

 theorem whole_slot_norm {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:Character)(m A z:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
    (S:ι→Finset (Ideal O))(β:ι→Ideal O→ℂ)(P:ι→ℝ)(hP:∀i,0<P i):
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2=
      ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2 *
        (∏i,‖rowSlot η m A z (S i) (β i) t‖^2/P i):=by
  have hp:0<∏i,P i:=Finset.prod_pos (fun i _=>hP i)
  unfold positiveSlotRow zeroRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ (mul_pos (mul_pos hX₁ hX₂) hp),
    CenteredMomentDivisorRawEnergy.normalized_norm_sq _ (mul_pos hX₁ hX₂)]
  rw [norm_mul,norm_prod,mul_pow,Finset.prod_div_distrib,Finset.prod_pow]
  ring

 theorem slot_energy_reduction {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:Character)(m A:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)(b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁)(hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0<X₁)(hX₂:0<X₂)(S:ι→Finset (Ideal O))(β:ι→Ideal O→ℂ)
    (P:ι→ℝ)(hP:∀i,0<P i)(r:Radial)(E:ℝ)
    (hslots:∀z,r.keep z→(∏i,‖rowSlot η m A z (S i) (β i) t‖^2/P i)≤E):
    energy η m A t W₁ W₂ S β P X₁ X₂ r.keep r.profile r.scale≤
      E*zeroEnergy η m A t W₁ W₂ X₁ X₂ r:=by
  obtain ⟨B,hB⟩:=product_bounded (ι:=Fin 0) η m A t (Real.sqrt (X₁*X₂):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ (fun _=>∅) (fun _=>0)
  have hz:∀z,‖zeroRow η m A z t W₁ W₂ X₁ X₂‖≤B:=by
    simpa [zeroRow] using hB
  have hsum:=bounded_radial_summable _ B hz r.keep r.profile r.scale r.scale_pos
  obtain ⟨B',hB'⟩:=product_bounded η m A t (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  have hspos:=bounded_radial_summable _ B' hB' r.keep r.profile r.scale r.scale_pos
  change Summable (fun z:O=>if r.keep z then
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0) at hspos
  unfold energy zeroEnergy
  rw [←tsum_mul_left]
  apply hspos.tsum_le_tsum _ (hsum.mul_left E)
  intro z
  by_cases hk:r.keep z
  · simp only [ite_eq_left hk]
    rw [whole_slot_norm η m A z t W₁ W₂ X₁ X₂ hX₁ hX₂ S β P hP]
    have hb:=mul_le_mul_of_nonneg_left (hslots z hk)
      (sq_nonneg ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖)
    have hh:=mul_le_mul_of_nonneg_right hb (r.nonneg z)
    nlinarith only [hh]
  · simp [hk]

end SevenEighths.CenteredMomentCoreFloor

end

end OAI
end OAIOriginalModule1705

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RadialCenteredEnergy
Source SHA256: 575c11deacbab31e6460e0b1dadd1af099c8350731a0bdd41f9abbc1cc18ce86
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1706



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentRadialCenteredEnergy
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentDivisorExtraction CenteredMomentDivisorRowEnergy CenteredMomentDivisorRectangle
open CenteredMomentHeckeSlots CenteredMomentPositiveSummability CenteredMomentActiveAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def centeredChildEnergy (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):ℝ:=
  ∑'z:O,r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
    s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2

lemma centered_child_summable (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):
    Summable (fun z:O=>r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2):=by
  have hN (j:Fin 2):(0:ℝ)<Ideal.absNorm (selectedPlain D a j):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  let c:ℂ:=(Real.sqrt ((s.X₁*s.X₂/selectedNorm D a)*∏i:liveIndices D a,s.P i):ℂ)⁻¹
  obtain ⟨BX,hBX⟩:=product_bounded s.η s.m s.A s.t c s.W₁ s.W₂ s.b₁ s.b₂
    (s.X₁/Ideal.absNorm (selectedPlain D a 0)) (s.X₂/Ideal.absNorm (selectedPlain D a 1))
    s.support₁ s.support₂ (div_pos s.X₁_pos (hN 0)) (div_pos s.X₂_pos (hN 1))
    (fun i:liveIndices D a=>s.slots i) (fun i:liveIndices D a=>s.coefficient i)
  obtain ⟨BY,hBY⟩:=product_bounded s.η s.m s.A s.t c s.W₁ s.W₂ s.b₁ s.b₂
    (s.Y₁/Ideal.absNorm (selectedPlain D a 0)) (s.Y₂/Ideal.absNorm (selectedPlain D a 1))
    s.support₁ s.support₂ (div_pos s.Y₁_pos (hN 0)) (div_pos s.Y₂_pos (hN 1))
    (fun i:liveIndices D a=>s.slots i) (fun i:liveIndices D a=>s.coefficient i)
  have hF (z:O):‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖≤BX+BY:=by
    unfold residualCenteredRow centeredSlotRow
    change ‖c*((_ - _)*_)‖≤_
    rw [sub_mul,mul_sub]
    exact (norm_sub_le _ _).trans (add_le_add (hBX z) (hBY z))
  have hs:=bounded_radial_summable _ (BX+BY) hF r.keep r.profile r.scale r.scale_pos
  convert hs using 1
  funext z
  unfold Radial.weight
  split_ifs <;> ring

lemma centered_child_nonneg (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))):0≤centeredChildEnergy s r D a:=
  tsum_nonneg (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))

def restrict (r:Radial) (p:O→Prop):Radial:={r with keep:=fun z=>r.keep z ∧ p z}

 theorem centered_child_split (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (p:O→Prop):
    centeredChildEnergy s r D a=centeredChildEnergy s (restrict r p) D a+
      centeredChildEnergy s (restrict r (fun z=>¬p z)) D a:=by
  unfold centeredChildEnergy
  rw [←Summable.tsum_add (centered_child_summable s (restrict r p) D a)
    (centered_child_summable s (restrict r (fun z=>¬p z)) D a)]
  apply tsum_congr
  intro z
  by_cases hk:r.keep z <;> by_cases hp:p z <;> simp [Radial.weight,restrict,hk,hp]

 theorem actual_source_centered (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*
        ∑a∈s.toSource.active D,((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
          centeredChildEnergy s r D a:=by
  obtain ⟨C,hC,hbase⟩:=active_allocated_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD
  have hraw:0<s.X₁*s.X₂*∏i,s.P i:=mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _))
  intro rows
  have hb:=hbase s.η s.m s.A s.t s.slots s.coefficient D hD s.W₁ s.W₂ s.b₁ s.b₂
    s.X₁ s.X₂ s.Y₁ s.Y₂ s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos
    rows (fun z=>r.weight z/(s.X₁*s.X₂*∏i,s.P i)) (fun z _=>div_nonneg (r.weight_nonneg z) hraw.le)
  have he (z:O) (x:ℂ):(r.weight z/(s.X₁*s.X₂*∏i,s.P i))*‖x‖^2=
      r.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*x‖^2:=by
    rw [normalized_norm_sq _ hraw];ring
  simp_rw [he] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  have hf:0≤(∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P:=
    div_nonneg (sq_nonneg _) (mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>s.P_pos i))).le
  calc
    _≤∑z∈rows,r.weight z*((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
      ‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=by
      apply Finset.sum_le_sum
      intro z hz
      have hh:=mul_le_mul_of_nonneg_left
        (allocated_raw_energy s.η s.m s.A z s.t s.slots s.prime s.coefficient s.M s.P
          (fun i=>(zero_le_one.trans (s.M_ge_one i))) s.P_pos s.coefficient_bound D a s.W₁ s.W₂
          s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
          s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos (mul_pos s.X₁_pos s.X₂_pos)) (r.weight_nonneg z)
      convert hh using 1 ; ring
    _=((∏i∈frozenIndices D a,s.M i)^2/formalReductionFactor D a s.P)*
      ∑z∈rows,r.weight z*‖residualCenteredRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)‖^2:=by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intros;ring
    _≤_:=mul_le_mul_of_nonneg_left (sum_le_hasSum rows
      (fun z _=>mul_nonneg (r.weight_nonneg z) (sq_nonneg _)) (centered_child_summable s r D a).hasSum) hf

 theorem actual_source_from_centered_children (N:ℕ) (hslots:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D → ∀E:ℝ,0≤E →
      (∀a∈s.toSource.active D,centeredChildEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P:=by
  obtain ⟨C,hC,hbound⟩:=actual_source_centered N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD E hE hchild
  apply (hbound s r D hD).trans
  calc
    _≤C*(Ideal.absNorm D:ℝ)^ε*∑a∈s.toSource.active D,
        (s.profileFactor/formalReductionFactor D a s.P)*E:=by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      apply Finset.sum_le_sum
      intro a ha
      have hp:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
        Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
          (fun i _=>zero_le_one.trans (s.M_ge_one i)) (fun i _ _=>s.M_ge_one i)
      have hsq:(∏i∈frozenIndices D a,s.M i)^2≤s.profileFactor:=by
        have hh:=pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.M_ge_one i))) hp 2
        have hf:1≤2*(max 1 s.b₁*max 1 s.b₂):=by
          have ht:=one_le_mul_of_one_le_of_one_le (le_max_left 1 s.b₁) (le_max_left 1 s.b₂)
          linarith
        exact hh.trans (le_mul_of_one_le_left (sq_nonneg _) hf)
      exact mul_le_mul (div_le_div_of_nonneg_right hsq (s.reduction_pos D a).le)
        (hchild a ha) (centered_child_nonneg s r D a) (div_nonneg s.profile_nonneg (s.reduction_pos D a).le)
    _=_:=by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

end SevenEighths.CenteredMomentRadialCenteredEnergy

end

end OAI
end OAIOriginalModule1706

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RadialPointwiseEnergy
Source SHA256: eb3ea2a640a69eeb2db9de78fe5c59cd1996150f3afe4c6c6820bd223c378bf8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1707


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseEnergy
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentSlotRatios CenteredMomentUniformDivisorShell
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

lemma inverse_reduction (s:Data ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.toSource.active D)
    (Z:ℝ) (hZ:1<Z) :
    1/formalReductionFactor D a s.P≤Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ) := by
  have hh:=s.toSource.active_pair_weight s.toSource D hD a a ha ha Z hZ
  rw [show formalReductionFactor D a s.P*formalReductionFactor D a s.P=
    (formalReductionFactor D a s.P)^2 by ring,Real.sqrt_sq (s.reduction_pos D a).le] at hh
  convert hh using 1
  congr 2
  ring

 theorem actual_pointwise_divisor (N:ℕ) (hι:Fintype.card ι≤N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0<C ∧ ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
      ∀E Z:ℝ,0≤E → 1<Z → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
        (s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  obtain ⟨C₁,hC₁,henergy⟩:=CenteredMomentRadialEligibleEnergy.actual_source_from_children N hι ε hε
  obtain ⟨C₂,hC₂,hcard⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨C₁*C₂,by positivity,?_⟩
  intro s r D hD E Z hE hZ hc
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
  have hsz:((s.toSource.active D).card:ℝ)≤C₂*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((s.toSource.active D).card:ℝ)≤Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard D hD.ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hs:(∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)≤
      (C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by
    calc
      _≤∑a∈s.toSource.active D,Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ):=
        Finset.sum_le_sum (fun a ha=>inverse_reduction s D hD a ha Z hZ)
      _=((s.toSource.active D).card:ℝ)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ)):=by simp
      _≤_:=mul_le_mul_of_nonneg_right hsz (div_nonneg (Real.rpow_nonneg (by linarith) _) hn.le)
  apply (henergy s r D hD E hE hc).trans
  calc
    _≤C₁*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ((C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^(s.toSource.allowance Z)/(Ideal.absNorm D:ℝ))):=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg (mul_nonneg hC₁.le hp) s.profile_nonneg) hE)
    _=_:=by
      have he:(Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε=(Ideal.absNorm D:ℝ)^(2*ε):=by
        rw [←Real.rpow_add hn];congr 1;ring
      calc
        _=(C₁*C₂)*((Ideal.absNorm D:ℝ)^ε*(Ideal.absNorm D:ℝ)^ε)*
          Z^(s.toSource.allowance Z)*(s.profileFactor*E)/(Ideal.absNorm D:ℝ):=by ring
        _=_:=by rw [he]

end SevenEighths.CenteredMomentRadialPointwiseEnergy

end

end OAI
end OAIOriginalModule1707

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RadialPointwiseUniform
Source SHA256: 4e107a1e9f20f92539c65ea3bca114beabca99a2b3f35fc60c63f3024bc5d525
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1708


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentRadialPointwiseUniform
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentRadialPointwiseEnergy CenteredMomentUniformDivisorShell
open CenteredMomentSlotRatios
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Bound (ι:Type*) [Fintype ι] [DecidableEq ι] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (r:Radial) (D:Ideal O),Squarefree D →
    ∀E Z:ℝ,0≤E → 1<Z → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
    energy s r D≤C*(Ideal.absNorm D:ℝ)^(2*ε)*Z^(s.toSource.allowance Z)*
      (s.profileFactor*E)/(Ideal.absNorm D:ℝ)

 theorem uniform_subset (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0<C ∧ ∀J:Finset ι,Bound J C ε := by
  have he (J:Finset ι):∃C:ℝ,0<C ∧ Bound J C ε:=
    actual_pointwise_divisor (Fintype.card ι) (by simpa using Finset.card_le_univ J) ε hε
  choose C hC hb using he
  let D:ℝ:=1+∑J:Finset ι,C J
  have hs:0≤∑J:Finset ι,C J:=Finset.sum_nonneg (fun J _=>(hC J).le)
  refine ⟨D,by dsimp [D];linarith,?_⟩
  intro J s r I hI E Z hE hZ hc
  have hd:C J≤D:=by
    have hh:=Finset.single_le_sum (fun J _=>(hC J).le) (Finset.mem_univ J)
    dsimp [D];linarith
  apply (hb J s r I hI E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (Nat.cast_nonneg _) _)

 theorem actual_uniform_divisor (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀(J:Finset ι) (s:Data J),(∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      ∀(r:Radial) (D:Ideal O),Squarefree D → ∀E Z:ℝ,0≤E → 1<Z →
      (Ideal.absNorm D:ℝ)≤Z^B → (∀a∈s.toSource.active D,childEnergy s r D a≤E) →
      energy s r D≤C*Z^δ*(s.profileFactor*E)/(Ideal.absNorm D:ℝ) := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  obtain ⟨C,hC,hbound⟩:=uniform_subset (ι:=ι) ε hε
  let A:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*A,by dsimp [A];positivity,?_⟩
  intro J s hlo hhi r D hD E Z hE hZ hN hc
  have hz:0<Z:=zero_lt_one.trans hZ
  have ha:Z^(s.toSource.allowance Z)≤A:=by
    dsimp [A]
    rw [←numerical_allowance Z _ hZ]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (subset_allowance J s.toSource lo hi hlo hhi Z hZ)
  have hp:(Ideal.absNorm D:ℝ)^(2*ε)≤Z^δ:=by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hN (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have he:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  apply (hbound J s r D hD E Z hE hZ hc).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg s.profile_nonneg hE)
  calc
    _≤C*Z^δ*A:=mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le) ha
      (Real.rpow_nonneg hz.le _) (by positivity)
    _=_:=by ring

end SevenEighths.CenteredMomentRadialPointwiseUniform

end

end OAI
end OAIOriginalModule1708

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RemainingBox
Source SHA256: 2527c5d68819298a89be08d9f904362748785e5f930ed84c7756f99bccb8cf8f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1709


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def restoreTuple (B : Tuple ι) (v : Tuple (liveIndices B)) : Tuple ι :=
  Sum.elim (fun i => if h : i∈liveIndices B then v (Sum.inl ⟨i,h⟩) else 1)
    (fun j => v (Sum.inr j))

@[simp] theorem remaining_restore (B : Tuple ι) (v : Tuple (liveIndices B)) :
    remainingTuple B (restoreTuple B v)=v := by
  funext i
  rcases i with i|j
  · simp [remainingTuple,restoreTuple]
  · rfl

theorem restore_remaining (B u : Tuple ι)
    (hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1) :
    restoreTuple B (remainingTuple B u)=u := by
  funext i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · rfl
    · exact (hf i (by simpa [liveIndices] using hi)).symm
  · rfl

def remainingSets (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O)) :
    (liveIndices B ⊕ Fin 2) → Finset (Ideal O) :=
  Sum.elim (fun i => S (Sum.inl i.val)) (fun j => S (Sum.inr j))

theorem remaining_mem (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (u : Tuple ι) (hu : u∈Fintype.piFinset S) :
    remainingTuple B u∈Fintype.piFinset (remainingSets B S) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · exact Fintype.mem_piFinset.mp hu (Sum.inl i.val)
  · exact Fintype.mem_piFinset.mp hu (Sum.inr j)

theorem restore_mem (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i))
    (v : Tuple (liveIndices B)) (hv : v∈Fintype.piFinset (remainingSets B S)) :
    restoreTuple B v∈Fintype.piFinset S := by
  apply Fintype.mem_piFinset.mpr
  intro i
  rcases i with i|j
  · simp only [restoreTuple,Sum.elim_inl]
    split_ifs with hi
    · exact Fintype.mem_piFinset.mp hv (Sum.inl ⟨i,hi⟩)
    · exact hg i (by simpa [liveIndices] using hi)
  · exact Fintype.mem_piFinset.mp hv (Sum.inr j)

theorem remaining_box_sum (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1)
    (hg : ∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i))
    (F : Tuple ι → ℂ) :
    (∑ u∈Fintype.piFinset S,F u)=
      ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) := by
  apply Finset.sum_bij (fun u _ => remainingTuple B u)
  · exact fun u hu => remaining_mem B S u hu
  · intro u hu v hv he
    have hu' := restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))
    have hv' := restore_remaining B v (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hv _))
    rw [← hu',← hv',he]
  · intro v hv
    exact ⟨restoreTuple B v,restore_mem B S hg v hv,remaining_restore B v⟩
  · intro u hu
    rw [restore_remaining B u (fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _))]

theorem remaining_box_sum_gate (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hf : ∀ i,B (Sum.inl i)≠1 → ∀ I∈S (Sum.inl i),I=1)
    (F : Tuple ι → ℂ) :
    (∑ u∈Fintype.piFinset S,F u)=
      if (∀ i,B (Sum.inl i)≠1 → (1 : Ideal O)∈S (Sum.inl i)) then
        ∑ v∈Fintype.piFinset (remainingSets B S),F (restoreTuple B v) else 0 := by
  split_ifs with hg
  · exact remaining_box_sum B S hf hg F
  · have he : Fintype.piFinset S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      apply hg
      intro i hi
      have hui := Fintype.mem_piFinset.mp hu (Sum.inl i)
      rwa [hf i hi _ hui] at hui
    rw [he,Finset.sum_empty]

end SevenEighths.CenteredMomentRemainingBox

end

end OAI
end OAIOriginalModule1709

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceCommonMask
Source SHA256: 196c3afb2447ed13561dcef7aac09b6a19a101d9d7f925c7d0beedf3de9ad5c9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1710



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceCommonMask
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentCompleteCommon
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem profile_nonzero_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι)
    (hne : profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v≠0) :
    IsCoprime (finiteTupleProduct v) R ∧ s∣finiteTupleProduct v := by
  constructor
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero,zero_mul])
  · by_contra hn
    exact hne (by simp only [profileCoefficient,hn,ite_false,mul_zero])

theorem column_nonzero_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O)
    (S : Finset (Tuple ι)) (I : Ideal O)
    (hne : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0) :
    IsCoprime I R ∧ s∣I := by
  obtain ⟨v,hv,hvne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have he := (Finset.mem_filter.mp hv).2
  have hm := profile_nonzero_masks R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v hvne
  rwa [he] at hm

theorem pair_common_masks
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (hs : Squarefree s)
    (S : Finset (Tuple ι)) (I J : Ideal O) (hI : I≠0) (hJ : J≠0)
    (hi : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I≠0)
    (hj : finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) J≠0) :
    s∣commonPart I J ∧ s∣commonPart J I ∧
      IsCoprime (commonPart I J) R ∧ IsCoprime (commonPart J I) R := by
  have hmi := column_nonzero_masks R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s S I hi
  have hmj := column_nonzero_masks R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s S J hj
  have hd := squarefree_mask_survives s I J hs hI hJ hmi.2 hmj.2
  exact ⟨hd.2.1,hd.2.2.1,
    hmi.1.of_isCoprime_of_dvd_left (commonPart_dvd I J hI),
    hmj.1.of_isCoprime_of_dvd_left (commonPart_dvd J I hJ)⟩

end SevenEighths.CenteredMomentSourceCommonMask

end

end OAI
end OAIOriginalModule1710

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceLiveAllocation
Source SHA256: 184906477cd86d7305b00e27db8842b4d565ff846e96fdbd9b480a0b35b2fa50
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1711



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceLiveAllocation
open CenteredMomentRemainingBox CenteredMomentCommonProfile CenteredMomentCommonPuncture
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationBox CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem prime_residual_frozen (B : Tuple ι) (hB : ∀ i,B i≠0)
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) :
    ∀ i,B (Sum.inl i)≠1 → ∀ I∈residualPool (B (Sum.inl i)) (hB _) (S (Sum.inl i)),I=1 := by
  intro i hi I hI
  have hprime := hp i _ ((mem_residualPool _ _ _ _).mp hI)
  rcases hprime.irreducible.isUnit_or_isUnit rfl with h|h
  · exact False.elim (hi (by simpa only [Ideal.isUnit_iff,Ideal.one_eq_top] using h))
  · simpa only [Ideal.isUnit_iff,Ideal.one_eq_top] using h

theorem allocation_frozen_gate (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) (C : Ideal O) (B : Tuple ι)
    (hB : B∈CenteredMomentCommonAllocationSum.allocationLabels S C) :
    ∀ i,B (Sum.inl i)≠1 → B (Sum.inl i)∈S (Sum.inl i) := by
  classical
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp hB
  intro i hi
  have hvi : v (Sum.inl i)∈S (Sum.inl i) := by
    have hh := hv
    simp only [Fintype.mem_piFinset] at hh
    exact hh (Sum.inl i)
  have he := congrFun hvB (Sum.inl i)
  change CenteredMomentSupport.supportExtract (v (Sum.inl i))
    (IdealMobiusDivisorSum.primeSupport C)=B (Sum.inl i) at he
  rw [CenteredMomentSupport.supportExtract_prime _ (hp i _ hvi)] at he
  split_ifs at he with hm
  · rwa [he] at hvi
  · exact False.elim (hi he.symm)

theorem live_residual_pool (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (B : Tuple ι) (hB : ∀ i,B i≠0) (i : liveIndices B) :
    residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val))=S (Sum.inl i.val) := by
  ext I
  rw [mem_residualPool,(Finset.mem_filter.mp i.property).2,one_mul]

theorem residual_source_profile (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s : Ideal O)
    (hprod : finiteTupleProduct B=C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (F : Tuple (liveIndices B) → ℂ) :
    (∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)*
        F (remainingTuple B u))=
      ((∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0))*
      (if (∀ i,B (Sum.inl i)≠1 → B (Sum.inl i)∈S (Sum.inl i)) then
        ∑ v∈Fintype.piFinset (remainingSets B (fun i => residualPool (B i) (hB i) (S i))),
          profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
            (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
            (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v*F v else 0) := by
  let T := fun i => residualPool (B i) (hB i) (S i)
  have hf := prime_residual_frozen B hB S hp
  let A := (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
          ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
        (if IsCoprime C R then 1 else 0)
  let G := fun v : Tuple (liveIndices B) =>
    profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
      (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
      (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v*F v
  rw [residualBoxes_sum]
  calc
    _ = ∑ u∈Fintype.piFinset T,A*G (remainingTuple B u) := by
      apply Finset.sum_congr
      · ext u;simp only [Fintype.mem_piFinset];rfl
      · intro u hu
        have hfu : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 :=
          fun i hi => hf i hi _ (Fintype.mem_piFinset.mp hu _)
        rw [profile_common_allocation B u C R s hprod hsC hfu]
        change (if IsCoprime C (finiteTupleProduct u) then 1 else 0)*
          (A*_ * F (remainingTuple B u))=_
        rw [remaining_product B u hfu]
        dsimp only [G]
        rw [← profileCoefficient_puncture C R]
        ring
    _ = A*(∑ u∈Fintype.piFinset T,G (remainingTuple B u)) := by rw [Finset.mul_sum]
    _ = _ := by
      rw [remaining_box_sum_gate B T hf]
      simp only [remaining_restore,T,mem_residualPool,mul_one]
      rfl

end SevenEighths.CenteredMomentSourceLiveAllocation

end

end OAI
end OAIOriginalModule1711

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceLiveColumn
Source SHA256: aec066f684433cf9a258023b9102d49023bc15a1738668c0149a7413a2ffab18
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1712


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceLiveColumn
open CenteredMomentSourceLiveAllocation CenteredMomentRemainingBox CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationBox CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def frozenCoefficient (B : Tuple ι) (C R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) : ℂ :=
  (∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),
    ν i (B (Sum.inl i))*Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i))*
    (if IsCoprime C R then 1 else 0)

def liveBox (S : (ι ⊕ Fin 2) → Finset (Ideal O)) (B : Tuple ι) (hB : ∀ i,B i≠0) :
    Finset (Tuple (liveIndices B)) :=
  Fintype.piFinset (remainingSets B (fun i => residualPool (B i) (hB i) (S i)))

def liveProfile (B : Tuple ι) (C R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    Tuple (liveIndices B) → ℂ :=
  profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1

theorem residual_source_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s a : Ideal O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (∑ u∈residualBoxes S C B hB,if finiteTupleProduct u=a then
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i) else 0)=
      frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B hB)
          (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  have hh := residual_source_profile S hp B hB C R s hprod hsC ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (fun v => if finiteTupleProduct v=a then 1 else 0)
  rw [ite_eq_left (allocation_frozen_gate S hp C B hlabel)] at hh
  calc
    _ = ∑ u∈residualBoxes S C B hB,
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s (fun i => B i*u i)*
        (if finiteTupleProduct (remainingTuple B u)=a then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      have hf : ∀ i,B (Sum.inl i)≠1 → u (Sum.inl i)=1 := by
        intro i hi
        have hui := hu
        simp only [residualBoxes,Fintype.mem_piFinset] at hui
        exact prime_residual_frozen B hB S hp i hi _
          (Finset.mem_filter.mp (hui (Sum.inl i))).1
      rw [remaining_product B u hf]
      split_ifs <;> simp
    _ = _ := hh.trans (by
      unfold frozenCoefficient finiteColumnCoefficient liveBox liveProfile
      rw [Finset.sum_filter]
      congr 1
      apply Finset.sum_congr
      · ext v;simp only [Fintype.mem_piFinset]
      intro v hv
      split_ifs <;> simp)

theorem original_source_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s a : Ideal O) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*a)=
      ∑ B : actualAllocations S C,
        frozenCoefficient B C R ν Wslot P*
          finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
            (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a := by
  simp only [finiteColumnCoefficient, Finset.sum_filter]
  have halloc := original_coefficient_allocated S hS C a hC ha hCa
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  change (∑ v ∈ Fintype.piFinset S, if finiteTupleProduct v = C * a then
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v else 0) = _ at halloc
  rw [halloc]
  apply Finset.sum_congr rfl
  intro B hB
  have h := residual_source_column S hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R s a
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2 hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  simp only [finiteColumnCoefficient, Finset.sum_filter] at h
  exact h

end SevenEighths.CenteredMomentSourceLiveColumn

end

end OAI
end OAIOriginalModule1712

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AllocationCost
Source SHA256: ec70f62f31931f15f5720da98226bc9ebf481aeeda452378de21926de7f35dc9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1713


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAllocationCost
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O

 theorem actualAllocations_uniform_small_power (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ D : ℝ,0<D ∧ ∀ {ι : Type*} [Fintype ι],Fintype.card ι≤N →
      ∀ (S : ι → Finset (Ideal O)) (C : Ideal O),C≠0 →
        ((actualAllocations S C).card:ℝ)≤D*(Ideal.absNorm C:ℝ)^ε := by
  let δ := ε/(N+1:ℕ)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(1+D)^(N+1),by positivity,?_⟩
  intro ι _ hn S C hC
  have hNC : (1:ℝ)≤Ideal.absNorm C := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hb : 1≤(1+D)*(Ideal.absNorm C:ℝ)^δ := by
    nlinarith [Real.one_le_rpow hNC hδ.le]
  have hd : δ*(N+1:ℕ)=ε := by
    dsimp only [δ]
    field_simp
  calc
    _ ≤ ((IdealMobiusDivisorSum.idealDivisors C).card:ℝ)^Fintype.card ι := by
      exact_mod_cast actualAllocations_card S C hC
    _ ≤ ((1+D)*(Ideal.absNorm C:ℝ)^δ)^Fintype.card ι := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ _
      exact (hdiv C hC).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    _ ≤ ((1+D)*(Ideal.absNorm C:ℝ)^δ)^(N+1) := pow_le_pow_right₀ hb (by omega)
    _ = _ := by rw [mul_pow,←Real.rpow_mul_natCast (Nat.cast_nonneg _),hd]

 theorem frozenCoefficient_norm {ι : Type*} [Fintype ι]
    (B : Tuple ι) (C R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ)
    (hν : ∀ i I,‖ν i I‖≤1) (hW : ∀ i x,‖Wslot i x‖≤M i)
    (hM : ∀ i,1≤M i) :
    ‖frozenCoefficient B C R ν Wslot P‖≤∏ i,M i := by
  unfold frozenCoefficient
  rw [norm_mul]
  have hc : ‖(if IsCoprime C R then (1:ℂ) else 0)‖≤1 := by split_ifs <;> simp
  apply (mul_le_of_le_one_right (norm_nonneg _) hc).trans
  rw [norm_prod]
  calc
    _ ≤ ∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),M i := by
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i hi
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hν i _)).trans (hW i _)
    _ ≤ ∏ i,M i := Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _ => zero_le_one.trans (hM i)) (fun i _ _ => hM i)

end SevenEighths.CenteredMomentAllocationCost

end

end OAI
end OAIOriginalModule1713

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonRawScale
Source SHA256: 2e712f33027130b0b1533618407cbbcbb5814c1bc85141a12d7caa59035a7459
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1714


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def frozenScale (B : Tuple ι) (P : ι → ℝ) (i : ι) : ℝ :=
  if B (Sum.inl i)=1 then 1 else P i

def plainNorm (B : Tuple ι) : ℝ :=
  (Ideal.absNorm (B (Sum.inr 0)):ℝ)*Ideal.absNorm (B (Sum.inr 1))

def rawReduction (B : Tuple ι) (P : ι → ℝ) : ℝ := plainNorm B*∏ i,frozenScale B P i

def remainingRaw (B : Tuple ι) (T : ℝ) (P : ι → ℝ) : ℝ :=
  (T/plainNorm B)*∏ i : liveIndices B,P i

omit [Fintype ι] in
theorem plainNorm_pos (B : Tuple ι) (hB : ∀ i,B i≠0) : 0<plainNorm B := by
  unfold plainNorm
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB _))

omit [Fintype ι] in
theorem frozenScale_pos (B : Tuple ι) (P : ι → ℝ) (hP : ∀ i,0<P i) (i : ι) :
    0<frozenScale B P i := by
  unfold frozenScale
  split_ifs
  · exact zero_lt_one
  · exact hP i

theorem rawReduction_pos (B : Tuple ι) (hB : ∀ i,B i≠0) (P : ι → ℝ) (hP : ∀ i,0<P i) :
    0<rawReduction B P := mul_pos (plainNorm_pos B hB) (Finset.prod_pos (fun i _ => frozenScale_pos B P hP i))

theorem slot_scale_split (B : Tuple ι) (P : ι → ℝ) :
    (∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)=∏ i,P i := by
  rw [Finset.prod_coe_sort (liveIndices B) P]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1) P]
  unfold frozenScale liveIndices
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  ring

theorem raw_scale_identity (B : Tuple ι) (hB : ∀ i,B i≠0) (T : ℝ) (P : ι → ℝ) :
    remainingRaw B T P*rawReduction B P=T*∏ i,P i := by
  unfold remainingRaw rawReduction
  have h := slot_scale_split B P
  calc
    _ = T*((∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)) := by
      field_simp [(plainNorm_pos B hB).ne']
    _ = _ := by rw [h]

theorem remainingRaw_source (B : Tuple ι) (_hB : ∀ i,B i≠0)
    (B₁ B₂ : Ideal O) (_hB₁ : B₁≠0) (_hB₂ : B₂≠0) (T : ℝ) (P : ι → ℝ) :
    remainingRaw B (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)) P=
      (T/((Ideal.absNorm (B₁*B (Sum.inr 0)):ℝ)*Ideal.absNorm (B₂*B (Sum.inr 1))))*
        ∏ i : liveIndices B,P i := by
  unfold remainingRaw plainNorm
  simp only [map_mul,Nat.cast_mul]
  ring

theorem product_norm (B : Tuple ι) :
    (Ideal.absNorm (finiteTupleProduct B):ℝ)=plainNorm B*∏ i,(Ideal.absNorm (B (Sum.inl i)):ℝ) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,map_mul,map_prod,
    Nat.cast_mul,Nat.cast_prod,plainNorm]
  ring

theorem frozen_window_ne_zero (B : Tuple ι) (C R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (hne : frozenCoefficient B C R ν Wslot P≠0) (i : ι) (hi : B (Sum.inl i)≠1) :
    Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i)≠0 := by
  have hp := (mul_ne_zero_iff.mp hne).1
  have hx := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  exact (mul_ne_zero_iff.mp hx).2

theorem actual_reduction_norm (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O)
    (hprod : finiteTupleProduct B=C) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (hP : ∀ i,0<P i)
    (a b : ℝ) (ha : 0<a) (hW : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (hne : frozenCoefficient B C R ν Wslot P≠0) :
    (min 1 a)^Fintype.card ι*rawReduction B P≤(Ideal.absNorm C:ℝ) ∧
      (Ideal.absNorm C:ℝ)≤(max 1 b)^Fintype.card ι*rawReduction B P := by
  have hi (i : ι) : min 1 a*frozenScale B P i≤(Ideal.absNorm (B (Sum.inl i)):ℝ) ∧
      (Ideal.absNorm (B (Sum.inl i)):ℝ)≤max 1 b*frozenScale B P i := by
    by_cases h : B (Sum.inl i)=1
    · simp only [frozenScale,h,ite_true,map_one,Nat.cast_one,mul_one]
      exact ⟨min_le_left _ _,le_max_left _ _⟩
    · have hs := hW i (frozen_window_ne_zero B C R ν Wslot P hne i h)
      rw [frozenScale,ite_eq_right h]
      exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (hP i).le)
          ((le_div_iff₀ (hP i)).mp hs.1),
        le_trans ((div_le_iff₀ (hP i)).mp hs.2)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (hP i).le)⟩
  rw [←hprod,product_norm]
  constructor
  · have hh := Finset.prod_le_prod₀ (s:=Finset.univ)
      (fun i _ => mul_nonneg (le_of_lt (lt_min zero_lt_one ha)) (frozenScale_pos B P hP i).le)
      (fun i _ => (hi i).1)
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (plainNorm_pos B hB).le
    simpa only [rawReduction,mul_left_comm,mul_assoc] using hh'
  · have hh := Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _ => Nat.cast_nonneg (Ideal.absNorm (B (Sum.inl i))))
      (fun i _ => (hi i).2)
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (plainNorm_pos B hB).le
    simpa only [rawReduction,mul_left_comm,mul_assoc] using hh'

end SevenEighths.CenteredMomentCommonRawScale

end

end OAI
end OAIOriginalModule1714

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonRawCost
Source SHA256: 65b5e4b8485badb4e4885eeff03b84fa94c8fe69713359d6e09acd1d0e01fa57
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1715


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonRawCost
open CenteredMomentCommonRawScale CenteredMomentAllocationCost CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem frozen_normalized_cost (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : C≠0)
    (hprod : finiteTupleProduct B=C) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ) (hP : ∀ i,0<P i)
    (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤M i) (hM : ∀ i,1≤M i)
    (a b : ℝ) (ha : 0<a) (hW : ∀ i,Function.support (Wslot i)⊆Set.Icc a b) :
    ‖frozenCoefficient B C R ν Wslot P‖^2/rawReduction B P≤
      ((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ) := by
  have hN : (0:ℝ)<Ideal.absNorm C := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hR := rawReduction_pos B hB P hP
  by_cases hz : frozenCoefficient B C R ν Wslot P=0
  · rw [hz,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)) hN.le
  · have hm := frozenCoefficient_norm B C R ν Wslot P M hν hWnorm hM
    have hh := (actual_reduction_norm B hB C R hprod ν Wslot P hP a b ha hW hz).2
    have hi : (1:ℝ)/rawReduction B P≤(max 1 b)^Fintype.card ι/(Ideal.absNorm C:ℝ) := by
      apply (div_le_div_iff₀ hR hN).mpr
      simpa only [one_mul] using hh
    calc
      _ ≤ (∏ i,M i)^2/rawReduction B P :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm _) hR.le
      _ = (∏ i,M i)^2*(1/rawReduction B P) := by ring
      _ ≤ (∏ i,M i)^2*((max 1 b)^Fintype.card ι/(Ideal.absNorm C:ℝ)) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = _ := by ring

end SevenEighths.CenteredMomentCommonRawCost

end

end OAI
end OAIOriginalModule1715

/-! Original module: OAI.NumberTheory.DirichletL.Moments.LiveSupport
Source SHA256: fc59bf94629f91c1c643335b4fca2e2d0e39dc54939e1d22870bb6a77e6d1cba
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1716



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentLiveSupport
open CenteredMomentSourceLiveColumn CenteredMomentSourceLiveAllocation CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum CenteredMomentFirstSectors CenteredMomentSourceCommonMask
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem restore_frozen (B : Tuple ι) (v : Tuple (liveIndices B)) :
    ∀ i,B (Sum.inl i)≠1 → restoreTuple B v (Sum.inl i)=1 := by
  intro i hi
  simp only [restoreTuple,Sum.elim_inl]
  rw [dite_eq_right (by simpa [liveIndices] using hi)]

theorem restore_product (B : Tuple ι) (v : Tuple (liveIndices B)) :
    finiteTupleProduct (restoreTuple B v)=finiteTupleProduct v := by
  rw [remaining_product B _ (restore_frozen B v),remaining_restore]

theorem restored_original_mem (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I) (C : Ideal O)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (hlabel : B∈allocationLabels S C)
    (v : Tuple (liveIndices B)) (hv : v∈liveBox S B hB) :
    (fun i => B i*restoreTuple B v i)∈Fintype.piFinset S := by
  have hg : ∀ i,B (Sum.inl i)≠1 →
      (1:Ideal O)∈residualPool (B (Sum.inl i)) (hB _) (S (Sum.inl i)) := by
    intro i hi
    rw [mem_residualPool,mul_one]
    exact allocation_frozen_gate S hp C B hlabel i hi
  have hu := restore_mem B (fun i => residualPool (B i) (hB i) (S i)) hg v (by simpa only [liveBox,Fintype.mem_piFinset] using hv)
  apply Fintype.mem_piFinset.mpr
  intro i
  simp only [Fintype.mem_piFinset] at hu
  exact (mem_residualPool _ _ _ _).mp (hu i)

theorem live_column_original_support (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R a : Ideal O)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (hne : finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) a≠0) :
    C*a∈finiteColumns (Fintype.piFinset S) ∧ a≠0 ∧ IsCoprime C a := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hv,ha⟩ := Finset.mem_filter.mp hv
  have hm := profile_nonzero_masks (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) 1 v hvn
  rw [ha,IsCoprime.mul_right_iff] at hm
  have hsrc := restored_original_mem S hp C B hB hlabel v hv
  have he : finiteTupleProduct (fun i => B i*restoreTuple B v i)=C*a := by
    rw [finiteTupleProduct,Finset.prod_mul_distrib]
    change finiteTupleProduct B*finiteTupleProduct (restoreTuple B v)=_
    rw [hprod,restore_product,ha]
  have hn : C*a≠0 := by
    rw [← he,finiteTupleProduct]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hS i _ (Fintype.mem_piFinset.mp hsrc i))
  exact ⟨Finset.mem_image.mpr ⟨_,hsrc,he⟩,right_ne_zero_of_mul hn,hm.1.2.symm⟩

end SevenEighths.CenteredMomentLiveSupport

end

end OAI
end OAIOriginalModule1716

/-! Original module: OAI.NumberTheory.DirichletL.Moments.LiveDomain
Source SHA256: 9bdeb219b4021cfad192c1294008d31d5e604fec2f23ea1e2d62cb2f1c4606f9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1717




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentLiveDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

 theorem finite_column_mem {ι : Type*} [Fintype ι] (S : Finset (Tuple ι))
    (β : Tuple ι → ℂ) (a : Ideal O) (ha : finiteColumnCoefficient S β a≠0) : a∈finiteColumns S := by
  obtain ⟨v,hv,hvn⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
  exact Finset.mem_image.mpr ⟨v,hv,he⟩

 theorem sum_same_support (S T : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (hST : ∀ I∈S,c I≠0 → I∈T) (hTS : ∀ I∈T,c I≠0 → I∈S) :
    (∑ I∈S,c I*f I)=∑ I∈T,c I*f I := by
  have hs : (∑ I∈S∩T,c I*f I)=∑ I∈S,c I*f I := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro I hI hn
    have hc : c I=0 := by
      by_contra h
      exact hn (Finset.mem_inter.mpr ⟨hI,hST I hI h⟩)
    rw [hc,zero_mul]
  have ht : (∑ I∈S∩T,c I*f I)=∑ I∈T,c I*f I := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro I hI hn
    have hc : c I=0 := by
      by_contra h
      exact hn (Finset.mem_inter.mpr ⟨hTS I hI h,hI⟩)
    rw [hc,zero_mul]
  exact hs.symm.trans ht

 theorem supported_residualPool (C : Ideal O) (hC : Supported C) (S : Finset (Ideal O)) :
    supportedColumns (residualPool C hC.1 S)=residualPool C hC.1 (supportedColumns S) := by
  ext I
  simp only [supportedColumns,Finset.mem_filter,mem_residualPool]
  rw [supported_mul_iff]
  tauto

def primaryGaussRow (I : Ideal O) (z : O) : ℂ :=
  if hI : Supported I then
    gaussRow (CompletedGauss.primaryGenerator I)
      (by rw [primary_span_supported I hI];exact hI) z else 0

theorem source_gaussPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator S) (sourceGenerator_supported S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*primaryGaussRow I z := by
  unfold gaussPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*primaryGaussRow I z)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [primaryGaussRow,dite_eq_left (Finset.mem_filter.mp I.property).2]
  rfl

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem live_column_sum (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    (∑ I∈supportedColumns (residualPool C hC.1 (finiteColumns (Fintype.piFinset S))),c I*f I)=
      ∑ I∈supportedColumns (finiteColumns (liveBox S B hB)),c I*f I := by
  dsimp only
  apply sum_same_support
  · intro I hI hn
    exact Finset.mem_filter.mpr ⟨finite_column_mem _ _ I hn,(Finset.mem_filter.mp hI).2⟩
  · intro I hI hn
    have hh := live_column_original_support S hS hp B hB C R I hlabel hprod
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn
    exact Finset.mem_filter.mpr ⟨(mem_residualPool C hC.1 _ I).mpr hh.1,(Finset.mem_filter.mp hI).2⟩

theorem live_gaussPolynomial (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (z : O) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) z=
      gaussPolynomial Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) z := by
  let c := finiteColumnCoefficient (liveBox S B hB)
    (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let T := finiteColumns (liveBox S B hB)
  change gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I : supportedColumns Q => c I*f I) z=_
  refine (source_gaussPolynomial Q (fun I => c I*f I) z).trans ?_
  refine Eq.trans ?_ (source_gaussPolynomial T (fun I => c I*f I) z).symm
  simpa only [mul_assoc] using live_column_sum S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => f I*primaryGaussRow I z)

theorem live_gaussEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) W K=
      gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  unfold gaussEnergy
  apply tsum_congr
  intro z
  exact congrArg (fun x : ℂ => ((‖x‖^2:ℝ):ℂ)*W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K))
    (live_gaussPolynomial S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ f z)

end SevenEighths.CenteredMomentLiveDomain

end

end OAI
end OAIOriginalModule1717

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RestrictedDomain
Source SHA256: 858b59af3e7814ef82790be9d11f50d9abd81d9b1c33e08c2ace28d73e496a9e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1718



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentLiveSupport CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFirstSectors CenteredMomentSourceRow CanonicalQuadraticSieve
open CenteredMomentRowNorm CenteredMomentRestrictedEnergy CenteredMomentLiveDomain
local notation "O" => ActualEisensteinCubic.O

theorem source_rowPolynomial (S : Finset (Ideal O)) (c : Ideal O → ℂ) (z : O) :
    rowPolynomial Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I) z=
      ∑ I∈supportedColumns S,c I*CanonicalRowCompletion.idealRowHom z I := by
  unfold rowPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*CanonicalRowCompletion.idealRowHom z I)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2]

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem live_rowPolynomial (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (z : O) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    rowPolynomial Finset.univ (sourceGenerator Q)
      (fun I : supportedColumns Q => c I*f I) z=
      rowPolynomial Finset.univ (sourceGenerator T)
        (fun I : supportedColumns T => c I*f I) z := by
  let c := finiteColumnCoefficient (liveBox S B hB)
    (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let T := finiteColumns (liveBox S B hB)
  change rowPolynomial Finset.univ (sourceGenerator Q)
    (fun I : supportedColumns Q => c I*f I) z=_
  refine (source_rowPolynomial Q (fun I => c I*f I) z).trans ?_
  refine Eq.trans ?_ (source_rowPolynomial T (fun I => c I*f I) z).symm
  simpa only [mul_assoc] using live_column_sum S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => f I*CanonicalRowCompletion.idealRowHom z I)

theorem live_restrictedEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    restrictedEnergy keep Finset.univ (sourceGenerator Q)
      (fun I : supportedColumns Q => c I*f I) W K=
      restrictedEnergy keep Finset.univ (sourceGenerator T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  unfold restrictedEnergy
  apply tsum_congr
  intro z
  exact congrArg (fun x : ℂ => if keep z then ‖x‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)
    (live_rowPolynomial S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂ f z)

end SevenEighths.CenteredMomentRestrictedDomain

end

end OAI
end OAIOriginalModule1718

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceAllocationEnergy
Source SHA256: 95127b9042a0689fb7095f3e338b58eac6d0d9503758f5f3ace89593e6c2e8c2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1719



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceAllocationEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O

 theorem gaussPolynomial_allocation {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ) (z : O) :
    gaussPolynomial S a ha (fun i => ∑ B,b B*d B i) z=
      ∑ B,b B*gaussPolynomial S a ha (d B) z := by
  simp only [gaussPolynomial,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

theorem finite_allocation_energy {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑ z∈rows,‖gaussPolynomial S a ha (fun i => ∑ B,b B*d B i) z‖^2)≤
      (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*(gaussEnergy S a ha (d B) W K).re := by
  calc
    _ ≤ ∑ z∈rows,(Fintype.card γ:ℝ)*∑ B,‖b B‖^2*‖gaussPolynomial S a ha (d B) z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      rw [gaussPolynomial_allocation]
      simpa only [Finset.card_univ,norm_mul,mul_pow] using
        CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B => b B*gaussPolynomial S a ha (d B) z)
    _ = (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*∑ z∈rows,‖gaussPolynomial S a ha (d B) z‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_energy_le_gaussEnergy S a ha (d B) W K hK rows hW hmajor) (sq_nonneg _)

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_source_allocation_energy {α : Type*}
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : C≠0) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (A : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hCJ : ∀ i,IsCoprime C (Ideal.span {a i}))
    (f : α → ℂ) (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑ z∈rows,‖gaussPolynomial A a ha (fun i =>
      finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*Ideal.span {a i})*f i) z‖^2)≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (gaussEnergy A a ha (fun i =>
            finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (Ideal.span {a i})*f i) W K).re := by
  have hc (i : α) := original_source_column S hS hp C R s (Ideal.span {a i}) hC (ha i).1 (hCJ i) hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  simp_rw [hc,Finset.sum_mul,mul_assoc]
  simpa only [Fintype.card_coe] using finite_allocation_energy A a ha
    (fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P)
    (fun B i => finiteColumnCoefficient
      (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (Ideal.span {a i})*f i)
    rows W K hK hW hmajor

end SevenEighths.CenteredMomentSourceAllocationEnergy

end

end OAI
end OAIOriginalModule1719

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceProfileMassUniform
Source SHA256: f3fcf86cfe16e6e62ad314547b2126989a9d002be127015f770d92111085f6e7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1720


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap

namespace SevenEighths.CenteredMomentSourceProfileMassUniform
open ActualEisensteinCubic CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceProfileMass
local notation "O" => ActualEisensteinCubic.O

theorem profile_mass_explicit {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (W₁ W₂ : ℝ → ℂ)
    (b D : ι → ℝ) (b₁ b₂ D₁ D₂ : ℝ)
    (hb : ∀ j,0≤b j) (hb₁ : 0≤b₁) (hb₂ : 0≤b₂)
    (hD : ∀ j,0≤D j) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂)
    (hzSlot : ∀ j,Wslot j 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hsSlot : ∀ j x,Wslot j x≠0→x≤b j)
    (hs₁ : ∀ x,W₁ x≠0→x≤b₁) (hs₂ : ∀ x,W₂ x≠0→x≤b₂)
    (hbound : ∀ j x,‖Wslot j x‖≤D j)
    (hbound₁ : ∀ x,‖W₁ x‖≤D₁) (hbound₂ : ∀ x,‖W₂ x‖≤D₂)
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (hν : ∀ j I,‖ν j I‖≤1)
    (P : ι → ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O)
    (hP : ∀ j,0<P j) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (S : Finset (Tuple ι)) :
    (∑v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
      (2*128^(Fintype.card ι+2)*(∏j,D j)*D₁*D₂*(∏j,b j)*b₁*b₂)*
        (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by
  let e := Fintype.equivFin ι
  have hzero : ∀ i,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i 0=0 := by
    simpa only [Fin.forall_fin_add,sourceProfiles,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hzSlot (e.symm j)) (And.intro hz₁ hz₂)
  have hs : ∀ i x,sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x≠0→
      x≤sourceBounds (fun j => b (e.symm j)) b₁ b₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hsSlot (e.symm j)) (And.intro hs₁ hs₂)
  have hbound' : ∀ i x,‖sourceProfiles (fun j => Wslot (e.symm j)) W₁ W₂ i x‖≤
      sourceBounds (fun j => D (e.symm j)) D₁ D₂ i := by
    simpa only [Fin.forall_fin_add,sourceProfiles,sourceBounds,Fin.append_left,Fin.append_right,
      Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
      using And.intro (fun j => hbound (e.symm j)) (And.intro hbound₁ hbound₂)
  have hm := originalCoefficient_mass (Fintype.card ι) 1 one_ne_zero
    (1 : MulChar (O ⧸ Ideal.span {(1:O)}) ℂ) R 0 (fun j => ν (e.symm j))
    (fun j I => hν _ I) (fun j => Wslot (e.symm j)) (fun j => P (e.symm j))
    (fun j => b (e.symm j)) (fun j => D (e.symm j)) W₁ W₂
    b₁ b₂ D₁ D₂ X₁ X₂ Y₁ Y₂ T B₁ B₂ s
    (fun j => hb _) hb₁ hb₂ (fun j => hD _) hD₁ hD₂
    (fun j => hP _) hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY hzero hs hbound'
    (S.image (tupleEquiv e))
  rw [finite_original_mass_reindex] at hm
  simp_rw [profileCoefficient_eq_original]
  simpa only [sourceMassConstant,e.symm.prod_comp D,e.symm.prod_comp b,e.symm.prod_comp P] using hm

theorem profile_mass_uniform {ι : Type*} [Fintype ι]
    (Wslot : ι → ℝ → ℂ) (a b : ι → ℝ) (a₁ b₁ a₂ b₂ : ℝ)
    (ha : ∀ j,0<a j) (hb : ∀ j,0≤b j)
    (ha₁ : 0<a₁) (hb₁ : 0≤b₁) (ha₂ : 0<a₂) (hb₂ : 0≤b₂)
    (hsSlot : ∀ j,Function.support (Wslot j)⊆Set.Icc (a j) (b j))
    (hWslot : ∀ j,ContDiff ℝ ∞ (Wslot j)) :
    ∃ C : ℝ,0<C ∧ ∀ W₁ W₂ : 𝓢(ℝ,ℂ),
      Function.support (W₁ : ℝ→ℂ)⊆Set.Icc a₁ b₁ →
      Function.support (W₂ : ℝ→ℂ)⊆Set.Icc a₂ b₂ →
      ∀ (R : Ideal O) (ν : ι→Ideal O→ℂ),(∀ j I,‖ν j I‖≤1)→
      ∀ (P : ι→ℝ) (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ s : Ideal O),
      (∀ j,0<P j)→0<X₁→0<X₂→0<Y₁→0<Y₂→B₁≠0→B₂≠0→
      X₁*X₂=T→Y₁*Y₂=T→∀ S : Finset (Tuple ι),
      (∑v∈S,‖profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v‖)≤
        (C*SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂)*
          (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by
  choose D hD hbound hz hs using fun j =>
    smooth_annular_bound (Wslot j) (a j) (b j) (ha j) (hsSlot j) (hWslot j)
  let C₀ := 2*128^(Fintype.card ι+2)*(∏j,D j)*(∏j,b j)*b₁*b₂
  have hprodD : 0≤∏j,D j := Finset.prod_nonneg (fun j _ => hD j)
  have hprodb : 0≤∏j,b j := Finset.prod_nonneg (fun j _ => hb j)
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  refine ⟨1+C₀,by positivity,?_⟩
  intro W₁ W₂ hs₁ hs₂ R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hzW (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
      (hs : Function.support (W : ℝ→ℂ)⊆Set.Icc a b) : W 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs hn).1
  have hm := profile_mass_explicit Wslot W₁ W₂ b D b₁ b₂
    (SchwartzMap.seminorm ℝ 0 0 W₁) (SchwartzMap.seminorm ℝ 0 0 W₂)
    hb hb₁ hb₂ hD (apply_nonneg _ _) (apply_nonneg _ _) hz
    (hzW W₁ a₁ b₁ ha₁ hs₁) (hzW W₂ a₂ b₂ ha₂ hs₂) hs
    (fun x hx => (hs₁ hx).2) (fun x hx => (hs₂ hx).2) hbound
    (SchwartzMap.norm_le_seminorm ℝ W₁) (SchwartzMap.norm_le_seminorm ℝ W₂)
    R ν hν P X₁ X₂ Y₁ Y₂ T B₁ B₂ s hP hX₁ hX₂ hY₁ hY₂ hB₁ hB₂ hX hY S
  have hT : 0<T := hX ▸ mul_pos hX₁ hX₂
  have hprodP : 0≤∏j,P j := Finset.prod_nonneg (fun j _ => (hP j).le)
  have hpos : 0≤SchwartzMap.seminorm ℝ 0 0 W₁*SchwartzMap.seminorm ℝ 0 0 W₂*
      (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂))*(∏j,P j) := by positivity
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_right (show C₀≤1+C₀ by linarith) hpos
  dsimp only [C₀] at hh
  nlinarith only [hh]
end SevenEighths.CenteredMomentSourceProfileMassUniform

end

end OAI
end OAIOriginalModule1720

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceRectangle
Source SHA256: acd85c381e6006addb0d4f1322f7b5c21a488eebf0043436ee1caa16501acb9e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1721





namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRectangle
open ActualEisensteinCubic HeckeFamily CenteredMomentHeckeExpansion CenteredMomentRectangle
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentExtraction CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentRemainingBox
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def tuplePools (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O)) :
    (ι⊕Fin 2)→Finset (Ideal O) := Sum.elim slots (fun j=>if j=0 then S₁ else S₂)

def tuplePool (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O)) : Finset (Tuple ι) :=
  Fintype.piFinset (tuplePools slots S₁ S₂)

def pack (v : ι→Ideal O) (I J : Ideal O) : Tuple ι :=
  Sum.elim v (fun j=>if j=0 then I else J)

omit [Fintype ι] in
@[simp] theorem pack_slot (v : ι→Ideal O) (I J : Ideal O) (i : ι) :
    pack v I J (Sum.inl i)=v i := rfl
omit [Fintype ι] in
@[simp] theorem pack_left (v : ι→Ideal O) (I J : Ideal O) :
    pack v I J (Sum.inr 0)=I := by simp [pack]
omit [Fintype ι] in
@[simp] theorem pack_right (v : ι→Ideal O) (I J : Ideal O) :
    pack v I J (Sum.inr 1)=J := by simp [pack]

theorem pack_product (v : ι→Ideal O) (I J : Ideal O) :
    finiteTupleProduct (pack v I J)=(∏ i,v i)*I*J := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,pack_slot,Fin.prod_univ_two,
    pack_left,pack_right,mul_assoc]

def tuplePoolEquiv (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O)) :
    tuplePool slots S₁ S₂ ≃ ((∀ i,slots i)×S₁×S₂) where
  toFun v := ((fun i=>⟨v.val (Sum.inl i),Fintype.mem_piFinset.mp v.property (Sum.inl i)⟩),
    ⟨v.val (Sum.inr 0),by simpa [tuplePools] using Fintype.mem_piFinset.mp v.property (Sum.inr 0)⟩,
    ⟨v.val (Sum.inr 1),by simpa [tuplePools] using Fintype.mem_piFinset.mp v.property (Sum.inr 1)⟩)
  invFun v := ⟨pack (fun i=>v.1 i) v.2.1 v.2.2,by
    apply Fintype.mem_piFinset.mpr
    intro i
    cases i with
    | inl i => exact (v.1 i).property
    | inr j => fin_cases j <;> simp [pack,tuplePools]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i => rfl
    | inr j => fin_cases j <;> rfl
  right_inv v := rfl

theorem sum_tuplePool (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (f : Tuple ι→ℂ) :
    (∑ v∈tuplePool slots S₁ S₂,f v)=
      ∑ v : (∀ i,slots i),∑ I : S₁,∑ J : S₂,f (pack (fun i=>v i) I J) := by
  rw [← Finset.sum_coe_sort (tuplePool slots S₁ S₂) f]
  have he := (tuplePoolEquiv slots S₁ S₂).symm.sum_comp (fun v : tuplePool slots S₁ S₂=>f v)
  change (∑ x : ((∀ i,slots i)×S₁×S₂),f (pack (fun i=>x.1 i) x.2.1 x.2.2))=
    (∑ v : tuplePool slots S₁ S₂,f v) at he
  simpa only [Fintype.sum_prod_type] using he.symm

theorem finite_column_regroup (S : Finset (Tuple ι)) (β : Tuple ι→ℂ) (w : Ideal O→ℂ) :
    (∑ I∈finiteColumns S,finiteColumnCoefficient S β I*w I)=
      ∑ v∈S,β v*w (finiteTupleProduct v) := by
  simp only [finiteColumnCoefficient,Finset.sum_mul]
  calc
    _ = ∑ I∈finiteColumns S,∑ v∈S.filter (fun v=>finiteTupleProduct v=I),
        β v*w (finiteTupleProduct v) := by
      apply Finset.sum_congr rfl
      intro I hI
      apply Finset.sum_congr rfl
      intro v hv
      rw [(Finset.mem_filter.mp hv).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun v hv=>Finset.mem_image.mpr ⟨v,hv,rfl⟩) _

def PlainCoverage (S : Finset (Ideal O)) (W : ℝ→ℂ) (B : Ideal O) (X Y : ℝ) : Prop :=
  ∀ I, W ((Ideal.absNorm (B*I):ℝ)/X)≠0 ∨ W ((Ideal.absNorm (B*I):ℝ)/Y)≠0 → I∈S

theorem rectangle_zero_left (S₁ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (I J : Ideal O) (hI : I∉S₁) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)=0 := by
  have hx : W₁ ((Ideal.absNorm (B₁*I):ℝ)/X₁)=0 := by
    by_contra hn;exact hI (h I (Or.inl hn))
  have hy : W₁ ((Ideal.absNorm (B₁*I):ℝ)/Y₁)=0 := by
    by_contra hn;exact hI (h I (Or.inr hn))
  simp only [idealRectangle,hx,hy,zero_mul,sub_self]

theorem rectangle_zero_right (S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h : PlainCoverage S₂ W₂ B₂ X₂ Y₂) (I J : Ideal O) (hJ : J∉S₂) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)=0 := by
  have hx : W₂ ((Ideal.absNorm (B₂*J):ℝ)/X₂)=0 := by
    by_contra hn;exact hJ (h J (Or.inl hn))
  have hy : W₂ ((Ideal.absNorm (B₂*J):ℝ)/Y₂)=0 := by
    by_contra hn;exact hJ (h J (Or.inr hn))
  simp only [idealRectangle,hx,hy,mul_zero,sub_self]

theorem finite_plain_rectangle (S₁ S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ)
    (B₁ B₂ : Ideal O) (X₁ X₂ Y₁ Y₂ : ℝ)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂)
    (f : Ideal O→Ideal O→ℂ) :
    (∑ I : S₁,∑ J : S₂,f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J))=
      ∑' I : Ideal O,∑' J : Ideal O,f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J) := by
  symm
  rw [tsum_eq_sum (s := S₁)]
  · rw [← Finset.sum_coe_sort S₁ (fun I=>∑' J : Ideal O,
      f I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J))]
    apply Finset.sum_congr rfl
    intro I hI
    rw [tsum_eq_sum (s := S₂)]
    · exact (Finset.sum_coe_sort S₂ _).symm
    · intro J hJ
      rw [rectangle_zero_right S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₂ I J hJ,mul_zero]
  · intro I hI
    simp only [rectangle_zero_left S₁ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ I _ hI,mul_zero,tsum_zero]

def fullMaskedRectangle (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) : ℂ :=
  ∑ v : (∀ i,slots i),(∏ i,ν i (v i)*Wslot i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      (if IsCoprime ((∏ i,(v i:Ideal O))*I*J) R then (1:ℂ) else 0)*
      (if L∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
      rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
      idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*I) (B₂*J)

theorem source_polynomial_eq_full_masked_rectangle (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (tuplePool slots S₁ S₂),
      finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      fullMaskedRectangle η m A z t slots ν (fun i I=>Wslot i ((Ideal.absNorm I:ℝ)/P i))
        R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ := by
  rw [finite_column_regroup,sum_tuplePool]
  unfold fullMaskedRectangle
  apply Finset.sum_congr rfl
  intro v hv
  rw [← finite_plain_rectangle S₁ S₂ W₁ W₂ B₁ B₂ X₁ X₂ Y₁ Y₂ h₁ h₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [profileCoefficient,pack_product,pack_slot,pack_left,pack_right]
  ring

theorem fullMaskedRectangle_pullback (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ =
      fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) 1 1 := by
  unfold fullMaskedRectangle
  simp only [one_mul,idealRectangle_extract]

theorem pullback_same_product (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    (X₁/Ideal.absNorm B₁)*(X₂/Ideal.absNorm B₂)=T/(Ideal.absNorm B₁*Ideal.absNorm B₂:ℝ) ∧
    (Y₁/Ideal.absNorm B₁)*(Y₂/Ideal.absNorm B₂)=T/(Ideal.absNorm B₁*Ideal.absNorm B₂:ℝ) :=
  extracted_product_scale X₁ X₂ Y₁ Y₂ T B₁ B₂ hX hY

theorem fullMaskedRectangle_modulus_one [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot 1 L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ =
      CenteredMomentDivisorRowEnergy.maskedRectangle η m A z t slots
        (fun i I=>ν i I*Wslot i I) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) := by
  simp only [fullMaskedRectangle,CenteredMomentDivisorRowEnergy.maskedRectangle,
    isCoprime_one_right,ite_true,one_mul,idealRectangle_extract]
  apply Finset.sum_congr (by ext; simp)
  intro v hv
  rfl

theorem source_polynomial_eq_maskedRectangle [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (tuplePool slots S₁ S₂),
      finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (profileCoefficient 1 ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      CenteredMomentDivisorRowEnergy.maskedRectangle η m A z t slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) :=
  (source_polynomial_eq_full_masked_rectangle η m A z t slots S₁ S₂ 1 L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂).trans
    (fullMaskedRectangle_modulus_one η m A z t slots ν _ L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)

theorem plainCoverage_residualPool (S : Finset (Ideal O)) (W : ℝ→ℂ)
    (B C : Ideal O) (hC : C≠0) (X Y : ℝ) (h : PlainCoverage S W B X Y) :
    PlainCoverage (residualPool C hC S) W (B*C) X Y := by
  intro I hi
  apply (mem_residualPool C hC S I).mpr
  apply h (C*I)
  simpa only [mul_assoc] using hi

def plainSupportPool (b X Y : ℝ) : Finset (Ideal O) := idealBall (b*X)∪idealBall (b*Y)

theorem plainSupportPool_coverage (W : ℝ→ℂ) (b X Y : ℝ)
    (hW₀ : W 0=0) (hs : Function.support W⊆Set.Iic b) (hX : 0<X) (hY : 0<Y) :
    PlainCoverage (plainSupportPool b X Y) W 1 X Y := by
  intro I hi
  simp only [one_mul] at hi
  have cover (Q : ℝ) (hQ : 0<Q) (hne : W ((Ideal.absNorm I:ℝ)/Q)≠0) :
      I∈idealBall (b*Q) := by
    apply (mem_idealBall _ _).mpr
    constructor
    · intro hI
      subst I
      apply hne
      simp only [map_zero,Nat.cast_zero,zero_div,hW₀]
    · exact (div_le_iff₀ hQ).mp (hs hne)
  obtain hi|hi := hi
  · exact Finset.mem_union_left _ (cover X hX hi)
  · exact Finset.mem_union_right _ (cover Y hY hi)

theorem extracted_plainSupportPool_coverage (W : ℝ→ℂ) (B : Ideal O) (hB : B≠0)
    (b X Y : ℝ) (hW₀ : W 0=0) (hs : Function.support W⊆Set.Iic b)
    (hX : 0<X) (hY : 0<Y) :
    PlainCoverage (residualPool B hB (plainSupportPool b X Y)) W B X Y := by
  simpa only [one_mul] using plainCoverage_residualPool (plainSupportPool b X Y)
    W 1 B hB X Y (plainSupportPool_coverage W b X Y hW₀ hs hX hY)

theorem supported_source_polynomial_eq_full_rectangle
    (η : Character) (m A z : O) (t : ℝ)
    (slots : ι→Finset (Ideal O)) (R L : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (hB₁ : B₁≠0) (hB₂ : B₂≠0) (hw₁ : W₁ 0=0) (hw₂ : W₂ 0=0)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) :
    let T := tuplePool slots
      (residualPool B₁ hB₁ (plainSupportPool b₁ X₁ Y₁))
      (residualPool B₂ hB₂ (plainSupportPool b₂ X₂ Y₂))
    (∑ I∈finiteColumns T,finiteColumnCoefficient T
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I*rowWeight η m A z t I)=
      fullMaskedRectangle η m A z t slots ν (fun i I=>Wslot i ((Ideal.absNorm I:ℝ)/P i))
        R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ :=
  source_polynomial_eq_full_masked_rectangle η m A z t slots _ _ R L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
    (extracted_plainSupportPool_coverage W₁ B₁ hB₁ b₁ X₁ Y₁ hw₁ hs₁ hX₁ hY₁)
    (extracted_plainSupportPool_coverage W₂ B₂ hB₂ b₂ X₂ Y₂ hw₂ hs₂ hX₂ hY₂)

theorem liveBox_eq_tuplePool (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι)
    (hB : ∀ i,B i≠0) :
    liveBox S B hB = tuplePool
      (fun i : liveIndices B=>residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val)))
      (residualPool (B (Sum.inr 0)) (hB _) (S (Sum.inr 0)))
      (residualPool (B (Sum.inr 1)) (hB _) (S (Sum.inr 1))) := by
  ext v
  simp only [liveBox,tuplePool,Fintype.mem_piFinset]
  constructor <;> intro h i
  all_goals
    cases i with
    | inl i => exact h (Sum.inl i)
    | inr j =>
      fin_cases j
      · exact h (Sum.inr 0)
      · exact h (Sum.inr 1)

theorem live_source_polynomial_eq_full_rectangle
    (η : Character) (m A z : O) (t : ℝ)
    (S : (ι⊕Fin 2)→Finset (Ideal O)) (B : Tuple ι) (hB : ∀ i,B i≠0)
    (C R : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage (S (Sum.inr 0)) W₁ B₁ X₁ Y₁)
    (h₂ : PlainCoverage (S (Sum.inr 1)) W₂ B₂ X₂ Y₂) :
    (∑ I∈finiteColumns (liveBox S B hB),finiteColumnCoefficient (liveBox S B hB)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I * rowWeight η m A z t I)=
      fullMaskedRectangle η m A z t
        (fun i : liveIndices B=>residualPool (B (Sum.inl i.val)) (hB _) (S (Sum.inl i.val)))
        (fun i=>ν i.val) (fun i I=>Wslot i.val ((Ideal.absNorm I:ℝ)/P i.val))
        (R*C) 1 W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) := by
  rw [liveBox_eq_tuplePool]
  exact source_polynomial_eq_full_masked_rectangle η m A z t _ _ _ (R*C) 1
    (fun i : liveIndices B=>ν i.val) (fun i=>Wslot i.val) (fun i=>P i.val)
    W₁ W₂ X₁ X₂ Y₁ Y₂ _ _
    (plainCoverage_residualPool _ W₁ B₁ _ (hB _) X₁ Y₁ h₁)
    (plainCoverage_residualPool _ W₂ B₂ _ (hB _) X₂ Y₂ h₂)

end SevenEighths.CenteredMomentSourceRectangle

end

end OAI
end OAIOriginalModule1721

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask
Source SHA256: 84c74c8e4f557c9709a986a4a44c7e1f98d0799a2ed1b4ba1b995346d39eb6db
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1722



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSourceRectangleMask
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentSourceRectangle
open CenteredMomentDivisorRowEnergy CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_ideal_mask (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (R I : Ideal O) :
    (if IsCoprime I R then (1:ℂ) else 0)*rowWeight η m A z t I=
      rowWeight η (m*idealGenerator R) A z t I := by
  by_cases hI : Supported I
  · have hm : (m*idealGenerator R)^6*(A*z)=(idealGenerator R)^6*(m^6*(A*z)) := by ring
    change (if IsCoprime I R then (1:ℂ) else 0)*
      ((idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))=
      (idealCoeff η I*idealRowHom ((m*idealGenerator R)^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)
    rw [hm,idealRowHom_argument_mul ((idealGenerator R)^6) (m^6*(A*z)) I,
      idealRowHom_sixth_mask (idealGenerator R) I hI,span_idealGenerator]
    ring
  · rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hI,
      rowWeight_zero_of_not_supported η (m*idealGenerator R) A z t
        (hmLam.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) I hI,mul_zero]

theorem ideal_mask_nonzero (m : O) (hm : m≠0) (R : Ideal O) (hR : R≠0) :
    m*idealGenerator R≠0 := mul_ne_zero hm (idealGenerator_ne_zero R hR)

theorem fullMaskedRectangle_eq_maskedRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (ν Wslot : ι→Ideal O→ℂ)
    (R L : Ideal O) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    fullMaskedRectangle η m A z t slots ν Wslot R L W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂=
      maskedRectangle η (m*idealGenerator R) A z t slots
        (fun i I=>ν i I*Wslot i I) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) := by
  unfold fullMaskedRectangle maskedRectangle
  apply Finset.sum_congr (by ext;simp)
  intro v hv
  congr 1
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [idealRectangle_extract]
  rw [mul_right_comm (if IsCoprime _ R then (1:ℂ) else 0) _,rowWeight_ideal_mask η m A z t hmLam hm2]
  ring

theorem source_polynomial_eq_maskedRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (slots : ι→Finset (Ideal O)) (S₁ S₂ : Finset (Ideal O))
    (R L : Ideal O) (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (h₁ : PlainCoverage S₁ W₁ B₁ X₁ Y₁) (h₂ : PlainCoverage S₂ W₂ B₂ X₂ Y₂) :
    (∑ I∈CenteredMomentSourceMass.finiteColumns (tuplePool slots S₁ S₂),
      CenteredMomentSourceMass.finiteColumnCoefficient (tuplePool slots S₁ S₂)
        (CenteredMomentSourceProfileMass.profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ L) I * rowWeight η m A z t I)=
      maskedRectangle η (m*idealGenerator R) A z t slots
        (fun i I=>ν i I*Wslot i ((Ideal.absNorm I:ℝ)/P i)) L W₁ W₂
        (X₁/Ideal.absNorm B₁) (X₂/Ideal.absNorm B₂)
        (Y₁/Ideal.absNorm B₁) (Y₂/Ideal.absNorm B₂) :=
  (source_polynomial_eq_full_masked_rectangle η m A z t slots S₁ S₂ R L ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ h₁ h₂).trans
    (fullMaskedRectangle_eq_maskedRectangle η m A z t hmLam hm2 slots ν _ R L W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂)

end SevenEighths.CenteredMomentSourceRectangleMask

end

end OAI
end OAIOriginalModule1722

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceSmoothedAllocation
Source SHA256: 81eeeb0c9b96a742b4e0db9b95fce0693a2e01abf0fae61e77e2ea3aaf84c649
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1723



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceSmoothedAllocation
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentSourceAllocationEnergy CenteredMomentSourceLiveColumn
open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O

theorem smoothed_allocation_energy {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (gaussEnergy S a ha (fun i => ∑ B,b B*d B i) W K).re≤
      (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*(gaussEnergy S a ha (d B) W K).re := by
  have hs := gaussEnergy_hasSum_re S a ha (fun i => ∑ B,b B*d B i) W K hK
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hW z))
  intro rows
  calc
    _ ≤ ∑ z∈rows,(Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        (‖gaussPolynomial S a ha (d B) z‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B => b B*gaussPolynomial S a ha (d B) z)) (hW z)
      rw [gaussPolynomial_allocation]
      simpa only [Finset.card_univ,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using h
    _ = (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        ∑ z∈rows,‖gaussPolynomial S a ha (d B) z‖^2*(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_weighted_le_gaussEnergy S a ha (d B) W K hK hW rows) (sq_nonneg _)

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_source_smoothed_allocation_energy {α : Type*}
    (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : C≠0) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (A : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (hCJ : ∀ i,IsCoprime C (Ideal.span {a i}))
    (f : α → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    :
    (gaussEnergy A a ha (fun i =>
      finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*Ideal.span {a i})*f i) W K).re≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (gaussEnergy A a ha (fun i =>
            finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (Ideal.span {a i})*f i) W K).re := by
  have hc (i : α) := original_source_column S hS hp C R s (Ideal.span {a i}) hC (ha i).1 (hCJ i) hsC
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  simp_rw [hc,Finset.sum_mul,mul_assoc]
  simpa only [Fintype.card_coe] using smoothed_allocation_energy A a ha
    (fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P)
    (fun B i => finiteColumnCoefficient
      (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) (Ideal.span {a i})*f i)
    W K hK hW

end SevenEighths.CenteredMomentSourceSmoothedAllocation

end

end OAI
end OAIOriginalModule1723

/-! Original module: OAI.NumberTheory.DirichletL.Moments.OriginalChildEnergy
Source SHA256: a8a78f6ccd2f0f96990938c6fde56ae1dfb2643b5a5cea34fe2539f08b4de26c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1724



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentOriginalChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentLiveSupport CenteredMomentLiveDomain CenteredMomentSourceSmoothedAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_source_punctured_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s I : Ideal O) (hC : C≠0) (hI : I≠0) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)=
      ∑ B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I := by
  by_cases hc : IsCoprime C I
  · rw [ite_eq_left hc]
    exact original_source_column S hS hp C R s I hC hI hc hsC ν Wslot P W₁ W₂
      X₁ X₂ Y₁ Y₂ B₁ B₂
  · rw [ite_eq_right hc]
    symm
    apply Finset.sum_eq_zero
    intro B hB
    have hz : finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
        (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I=0 := by
      by_contra hn
      exact hc (live_column_original_support S hS hp B
        (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R I
        (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
        ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hn).2.2
    rw [hz,mul_zero]

def sourceGaussEnergy (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I : supportedColumns Q => c I*f I) W K

theorem original_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K).re≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let b := fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P
  let d := fun (B : actualAllocations S C) (I : supportedColumns Q) =>
    finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime C (I:Ideal O) then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)*f I=
      ∑ B,b B*d B I := by
    rw [original_source_punctured_column S hS hp C R s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hsC ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂,Finset.sum_mul]
    simp only [b,d,mul_assoc]
  have h := smoothed_allocation_energy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  have he' := funext he
  change (gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re≤_
  rw [he']
  apply h.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  simpa only [b,d,sourceGaussEnergy] using
    congrArg (fun x : ℂ => ‖frozenCoefficient B C R ν Wslot P‖^2*x.re)
    (live_gaussEnergy S hS hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f W K)

end SevenEighths.CenteredMomentOriginalChildEnergy

end

end OAI
end OAIOriginalModule1724

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationLiveMask
Source SHA256: a58d419c41d00fc96376020b59a93e4cfab0f0f88209835cb6cb346271c2fcbd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1725


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationLiveMask
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentOriginalChildEnergy CenteredMomentRemainingBox CenteredMomentCommonProfile
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

 theorem profile_mask (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s v=
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1 v*
        (if s∣finiteTupleProduct v then 1 else 0) := by
  simp only [profileCoefficient,one_dvd,ite_true,mul_one]

theorem column_mask (S : Finset (Tuple ι)) (R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s I : Ideal O) :
    finiteColumnCoefficient S
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) I=
      finiteColumnCoefficient S
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ 1) I*
          (if s∣I then 1 else 0) := by
  unfold finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [profile_mask,(Finset.mem_filter.mp hv).2]

 def maskedLiveProfile (B : Tuple ι) (C R s : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    Tuple (liveIndices B) → ℂ :=
  profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) s

theorem original_masked_live_column (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s I : Ideal O) (hC : C≠0) (hI : I≠0) (hsc : IsCoprime s C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    (if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
      (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)=
      ∑ B : actualAllocations S C,frozenCoefficient B C R ν Wslot P*
        finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I := by
  have he := original_source_punctured_column S hS hp C R 1 I hC hI (one_dvd C)
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
  rw [column_mask,hsc.dvd_mul_left_iff]
  have hh := congrArg (fun z : ℂ => z*(if s∣I then 1 else 0)) he
  rw [Finset.sum_mul] at hh
  convert hh using 1
  · split_ifs <;> simp
  · apply Finset.sum_congr rfl
    intro B hB
    rw [maskedLiveProfile,column_mask]
    dsimp only [liveProfile]
    ring

end SevenEighths.CenteredMomentAmplificationLiveMask

end

end OAI
end OAIOriginalModule1725

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationCost
Source SHA256: 78a671a4bea09b39346891c88cea4be793ff7f93f0ab1ed0fdb9332359bdf1fb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1726


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocationCost
open CenteredMomentCommonAllocationSum CenteredMomentSupport IdealMobiusDivisorSum
open CenteredMomentAddedZeroUniform CenteredMomentCommonSectors
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

 theorem allocation_slot_one (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (i : ι) : B.val (Sum.inl i)=1 := by
  obtain ⟨v,hv,hvB⟩ := Finset.mem_image.mp (Finset.mem_filter.mp B.property).1
  have hi := Fintype.mem_piFinset.mp hv (Sum.inl i)
  have hd := hslot i (v (Sum.inl i)) hi
  have he := congrFun hvB (Sum.inl i)
  have hc : IsCoprime (P^k) (v (Sum.inl i)) := hd.2.pow_left
  have hh := supportExtract_of_disjoint (v (Sum.inl i)) (primeSupport (P^k))
    ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff (pow_ne_zero k hP) hd.1).mpr hc).symm
  exact he.symm.trans hh

 theorem allocation_plain_product (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : B.val (Sum.inr 0)*B.val (Sum.inr 1)=P^k := by
  have he := (Finset.mem_filter.mp B.property).2
  rw [Fintype.prod_sum_type,show (∏ i : ι,B.val (Sum.inl i))=1 by
    simp only [allocation_slot_one S P hP k hslot B,Finset.prod_const_one],one_mul,
    Fin.prod_univ_two] at he
  exact he

 theorem allocation_plain_injective (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    Function.Injective (fun B : actualAllocations S (P^k) => B.val (Sum.inr 0)) := by
  intro B D he
  have hb := allocation_plain_product S P hP k hslot B
  have hd := allocation_plain_product S P hP k hslot D
  have hb0 := (allocation_data S (P^k) B (Finset.mem_filter.mp B.property).1).1 (Sum.inr 0)
  have he1 : B.val (Sum.inr 1)=D.val (Sum.inr 1) := by
    apply mul_left_cancel₀ hb0
    exact (hb.trans hd.symm).trans (congrArg (fun x => x*D.val (Sum.inr 1)) he.symm)
  apply Subtype.ext
  funext i
  cases i with
  | inl i => rw [allocation_slot_one S P hP k hslot B,allocation_slot_one S P hP k hslot D]
  | inr i => fin_cases i <;> assumption

 theorem idealDivisors_prime_power_card (P : Ideal O) (hP : Prime P) (k : ℕ) :
    (idealDivisors (P^k)).card≤k+1 := by
  have hs : idealDivisors (P^k)⊆(Finset.range (k+1)).image (fun j => P^j) := by
    intro I hI
    obtain ⟨j,hj,he⟩ := (dvd_prime_pow hP k).mp ((mem_idealDivisors (pow_ne_zero k hP.ne_zero)).mp hI)
    have heq : I=P^j := dvd_antisymm he.dvd he.symm.dvd
    exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),heq.symm⟩
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans_eq (Finset.card_range (k+1)))

theorem actual_amplification_allocations_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : Prime P) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    (actualAllocations S (P^k)).card≤k+1 := by
  let f : actualAllocations S (P^k) → idealDivisors (P^k) := fun B =>
    ⟨B.val (Sum.inr 0),(mem_idealDivisors (pow_ne_zero k hP.ne_zero)).mpr
      ⟨B.val (Sum.inr 1),(allocation_plain_product S P hP.ne_zero k hslot B).symm⟩⟩
  have hf : Function.Injective f := by
    intro B D he
    exact allocation_plain_injective S P hP.ne_zero k hslot (congrArg Subtype.val he)
  have hh := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hh
  exact hh.trans (idealDivisors_prime_power_card P hP k)

 theorem actual_error_allocations_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : Prime P) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I) :
    (actualAllocations S (P^k)).card≤8 := by
  have hh := actual_amplification_allocations_card S P hP k hslot
  rcases hk with rfl|rfl|rfl <;> omega

end SevenEighths.CenteredMomentAmplificationAllocationCost

end

end OAI
end OAIOriginalModule1726

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationAllocationScale
Source SHA256: b8e5462cf12b0921bc8b14fc180c2a8cc6825b12144eb79fe53eb159c29d145b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1727



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationAllocationCost CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale
open CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem all_slots_live (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : liveIndices (B : Tuple ι)=Finset.univ := by
  apply Finset.filter_eq_self.mpr
  intro i hi
  exact allocation_slot_one S P hP k hslot B i

 theorem frozenCoefficient_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (scale : ι → ℝ) :
    frozenCoefficient B (P^k) R ν Wslot scale=(if IsCoprime (P^k) R then 1 else 0) := by
  unfold frozenCoefficient
  have he : Finset.univ.filter (fun i => B.val (Sum.inl i)≠1)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i hi
    exact not_not_intro (allocation_slot_one S P hP k hslot B i)
  rw [he,Finset.prod_empty,one_mul]

 theorem frozenCoefficient_norm_le (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (R : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (scale : ι → ℝ) :
    ‖frozenCoefficient B (P^k) R ν Wslot scale‖≤1 := by
  rw [frozenCoefficient_exact S P hP k hslot B R ν Wslot scale]
  split_ifs <;> simp

 theorem rawReduction_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (scale : ι → ℝ) :
    rawReduction B scale=(Ideal.absNorm P:ℝ)^k := by
  unfold rawReduction plainNorm frozenScale
  simp only [allocation_slot_one S P hP k hslot B,ite_true,Finset.prod_const_one,mul_one]
  rw [← Nat.cast_mul,← map_mul,allocation_plain_product S P hP k hslot B,map_pow,Nat.cast_pow]

 theorem live_slot_card (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) : Fintype.card (liveIndices (B : Tuple ι))=Fintype.card ι := by
  rw [Fintype.card_coe,all_slots_live S P hP k hslot B,Finset.card_univ]

theorem remainingRaw_exact (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (P : Ideal O) (hP : P≠0) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime P I)
    (B : actualAllocations S (P^k)) (scale : ι → ℝ) (Traw : ℝ) :
    remainingRaw B Traw scale=(Traw*∏ i,scale i)/(Ideal.absNorm P:ℝ)^k := by
  have hb := (allocation_data S (P^k) B (Finset.mem_filter.mp B.property).1).1
  have he := raw_scale_identity B hb Traw scale
  rw [rawReduction_exact S P hP k hslot B scale] at he
  have hn : (Ideal.absNorm P:ℝ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hP
  exact (eq_div_iff (pow_ne_zero k hn)).mpr he

end SevenEighths.CenteredMomentAmplificationAllocationScale

end

end OAI
end OAIOriginalModule1727

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationLiveEnergy
Source SHA256: daa0ca1a5d1b2f0f607c77a12b44ecfeae355b7789d4b5af96876a1c67a1d1fc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1728


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationLiveEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentLiveSupport CenteredMomentLiveDomain CenteredMomentSourceSmoothedAllocation
open CenteredMomentOriginalChildEnergy CenteredMomentAmplificationLiveMask
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

 theorem masked_live_gaussEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) W K=
      gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  have he (I : Ideal O) : finiteColumnCoefficient (liveBox S B hB)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I=
      finiteColumnCoefficient (liveBox S B hB)
        (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*
          (if s∣I then 1 else 0) := column_mask _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp_rw [he,mul_assoc]
  exact live_gaussEnergy S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I => (if s∣I then 1 else 0)*f I) W K

theorem original_masked_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsc : IsCoprime s C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K).re≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let b := fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P
  let d := fun (B : actualAllocations S C) (I : supportedColumns Q) =>
    finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime C (I:Ideal O) then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)*f I=
      ∑ B,b B*d B I := by
    rw [original_masked_live_column S hS hp C R s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂,Finset.sum_mul]
    simp only [b,d,mul_assoc]
  have h := smoothed_allocation_energy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  have he' := funext he
  change (gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re≤_
  rw [he']
  apply h.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  simpa only [b,d,sourceGaussEnergy] using
    congrArg (fun x : ℂ => ‖frozenCoefficient B C R ν Wslot P‖^2*x.re)
    (masked_live_gaussEnergy S hS hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R s hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f W K)

end SevenEighths.CenteredMomentAmplificationLiveEnergy

end

end OAI
end OAIOriginalModule1728

/-! Original module: OAI.NumberTheory.DirichletL.Moments.GaussNormalization
Source SHA256: a9548a0397bb3a9687534631d26d933fe2cd3bc2aa14ea51e1450b772bebbc73
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1729



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentGaussNormalization
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentDivisorRawEnergy CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

theorem gaussPolynomial_const_mul {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ) (d : ℂ) (z : O) :
    gaussPolynomial S a ha (fun i => d*c i) z=d*gaussPolynomial S a ha c z := by
  simp only [gaussPolynomial,Finset.mul_sum,mul_assoc]

theorem gaussEnergy_const_mul {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ) (d : ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    gaussEnergy S a ha (fun i => d*c i) W K=((‖d‖^2:ℝ):ℂ)*gaussEnergy S a ha c W K := by
  simp only [gaussEnergy,gaussPolynomial_const_mul,norm_mul,mul_pow,Complex.ofReal_mul,mul_assoc,tsum_mul_left]

theorem gaussEnergy_central {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (T : ℝ) (hT : 0<T) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (gaussEnergy S a ha (fun i => (Real.sqrt T:ℂ)⁻¹*c i) W K).re=
      (gaussEnergy S a ha c W K).re/T := by
  rw [gaussEnergy_const_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt hT.le]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,div_eq_mul_inv,mul_comm]

theorem sourceGaussEnergy_central (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (T : ℝ) (hT : 0<T) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy Q (fun I => (Real.sqrt T:ℂ)⁻¹*c I) f W K).re=
      (sourceGaussEnergy Q c f W K).re/T := by
  unfold sourceGaussEnergy
  simp only [mul_assoc]
  exact gaussEnergy_central Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I : supportedColumns Q => c I*f I) T hT W K

theorem sourceGaussEnergy_nonneg (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤(sourceGaussEnergy Q c f W K).re := by
  have hs := CenteredMomentSmoothedWindowEnergy.gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) (fun I : supportedColumns Q => c I*f I) W K hK
  change 0≤(gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) _ W K).re
  rw [←hs.tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hW z))

end SevenEighths.CenteredMomentGaussNormalization

end

end OAI
end OAIOriginalModule1729

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationChildEnergy
Source SHA256: 88ab81c1bc30919ffcc1cd44bfa11c8059a73aadc92c857ed6a15ece9941cbb6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1730




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationChildEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy CenteredMomentAmplificationLiveMask
open CenteredMomentAmplificationLiveEnergy CenteredMomentAmplificationAllocationScale
open CenteredMomentAmplificationAllocationCost CenteredMomentGaussNormalization
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem actual_amplification_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (Q R s : Ideal O) (hQ : Prime Q) (hQs : Supported Q) (k : ℕ)
    (hslot : ∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime Q I)
    (hsc : IsCoprime s (Q^k))
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool (Q^k) (pow_ne_zero k hQ.ne_zero) (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime (Q^k) I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) ((Q^k)*I) else 0) f W K).re≤
      (k+1:ℝ)*∑ B : actualAllocations S (Q^k),
        (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B (Q^k) R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
  have hsPow : ∀ n : ℕ,Supported (Q^n) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero] using CenteredMomentAddedZero.supported_one_ideal
    | succ n ih => rw [pow_succ,supported_mul_iff];exact ⟨ih,hQs⟩
  have hC := hsPow k
  have he := original_masked_child_energy S hS hp (Q^k) R s hC hsc ν Wslot P
    W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f W K hK hW
  let E : actualAllocations S (Q^k) → ℝ := fun B =>
    (sourceGaussEnergy
      (finiteColumns (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1))
      (finiteColumnCoefficient
        (liveBox S B (allocation_data S (Q^k) B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B (Q^k) R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re
  have hE (B : actualAllocations S (Q^k)) : 0≤E B := sourceGaussEnergy_nonneg _ _ _ W K hK hW
  have hc : ((actualAllocations S (Q^k)).card:ℝ)≤(k+1:ℝ) := by
    exact_mod_cast actual_amplification_allocations_card S Q hQ k hslot
  have hf (B : actualAllocations S (Q^k)) :
      ‖frozenCoefficient B (Q^k) R ν Wslot P‖^2≤1 := by
    have hh := frozenCoefficient_norm_le S Q hQ.ne_zero k hslot B R ν Wslot P
    nlinarith [norm_nonneg (frozenCoefficient B (Q^k) R ν Wslot P)]
  exact he.trans (mul_le_mul (by exact hc)
    (Finset.sum_le_sum (fun B _ => mul_le_of_le_one_left (hE B) (hf B)))
    (Finset.sum_nonneg (fun B _ => mul_nonneg (sq_nonneg _) (hE B))) (by positivity))

end SevenEighths.CenteredMomentAmplificationChildEnergy

end

end OAI
end OAIOriginalModule1730

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RestrictedSource
Source SHA256: 4917a704ba366169900d7b835d9a0ca78c0b9ab3fef38359efd84e176e628da3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1731



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedSource
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentRestrictedDomain
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentOriginalChildEnergy
local notation "O" => ActualEisensteinCubic.O

theorem rowPolynomial_allocation {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (b : γ → ℂ) (d : γ → α → ℂ) (z : O) :
    rowPolynomial S a (fun i => ∑ B,b B*d B i) z=
      ∑ B,b B*rowPolynomial S a (d B) z := by
  simp only [rowPolynomial,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

def sourceRestrictedEnergy (keep : O → Prop) (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  restrictedEnergy keep Finset.univ (sourceGenerator Q)
    (fun I : supportedColumns Q => c I*f I) W K

theorem smoothed_restricted_allocation {α γ : Type*} [Fintype γ] (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (restrictedEnergy keep S a (fun i => ∑ B,b B*d B i) W K)≤
      (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*(restrictedEnergy keep S a (d B) W K) := by
  let u := fun z : O => if keep z then (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hu (z : O) : 0≤u z := by dsimp only [u];split_ifs;exact hW z;exact le_rfl
  have hs := restricted_hasSum_weighted keep S a ha (fun i => ∑ B,b B*d B i) W K hK
  rw [← hs.tsum_eq]
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hu z))
  intro rows
  calc
    _ ≤ ∑ z∈rows,(Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        (‖rowPolynomial S a (d B) z‖^2*u z) := by
      apply Finset.sum_le_sum
      intro z hz
      have h := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B => b B*rowPolynomial S a (d B) z)) (hu z)
      rw [rowPolynomial_allocation]
      simpa only [Finset.card_univ,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using h
    _ = (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*
        ∑ z∈rows,‖rowPolynomial S a (d B) z‖^2*u z := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_weighted_le_restricted keep S a ha (d B) W K hK hW rows) (sq_nonneg _)

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_restricted_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K) := by
  let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
  let b := fun B : actualAllocations S C => frozenCoefficient B C R ν Wslot P
  let d := fun (B : actualAllocations S C) (I : supportedColumns Q) =>
    finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime C (I:Ideal O) then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)*f I=
      ∑ B,b B*d B I := by
    rw [original_source_punctured_column S hS hp C R s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hsC ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂,Finset.sum_mul]
    simp only [b,d,mul_assoc]
  have h := smoothed_restricted_allocation keep Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q) b d W K hK hW
  have he' := funext he
  change (restrictedEnergy keep Finset.univ (sourceGenerator Q) _ W K)≤_
  rw [he']
  apply h.trans_eq
  rw [Fintype.card_coe]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  simpa only [b,d,sourceRestrictedEnergy] using
    congrArg (fun x : ℝ => ‖frozenCoefficient B C R ν Wslot P‖^2*x)
    (live_restrictedEnergy S hS hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f keep W K)

end SevenEighths.CenteredMomentRestrictedSource

end

end OAI
end OAIOriginalModule1731

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RestrictedSourceNormalization
Source SHA256: 99244d1662cc762800d8e55d73aa537eb47a18a4c6b34102cd6c2ce6aeb69c68
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1732



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentRestrictedSourceNormalization
open CanonicalQuadraticSieve CenteredMomentSourceRow CenteredMomentRestrictedSource
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost CenteredMomentRestrictedEnergy
local notation "O" => ActualEisensteinCubic.O

theorem sourceRestrictedEnergy_nonneg (keep : O → Prop) (Q : Finset (Ideal O)) (c f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (_hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤sourceRestrictedEnergy keep Q c f W K := by
  unfold sourceRestrictedEnergy restrictedEnergy
  apply tsum_nonneg
  intro z
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (hW z)
  · exact le_rfl

variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem normalized_restricted_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        (‖frozenCoefficient B C R ν Wslot P‖^2/rawReduction B P)*
          ((sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K)/remainingRaw B Traw P) := by
  have h := original_restricted_child_energy S hS hp C R s hC hsC ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ f keep W K hK hW
  have htotal : 0<Traw*∏ i,P i := mul_pos hTraw (Finset.prod_pos (fun i _ => hP i))
  apply (div_le_div_of_nonneg_right h htotal.le).trans_eq
  rw [mul_div_assoc,Finset.sum_div]
  apply congrArg (fun x : ℝ => ((actualAllocations S C).card:ℝ)*x)
  apply Finset.sum_congr rfl
  intro B hB
  have hb := (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
  have hr := raw_scale_identity B hb Traw P
  have hpR := rawReduction_pos B hb P hP
  have hpL : 0<remainingRaw B Traw P := by
    apply (mul_pos_iff_of_pos_right hpR).mp
    exact hr.symm ▸ htotal
  have alg (d e n r l : ℝ) (hr : 0<r) (hl : 0<l) (hn : l*r=n) :
      d*e/n=(d/r)*(e/l) := by
    rw [←hn]
    field_simp [hr.ne',hl.ne']
  exact alg _ _ _ _ _ hpR hpL hr

theorem restricted_child_common_saving (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsC : s∣C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (Traw : ℝ) (hTraw : 0<Traw) (hP : ∀ i,0<P i)
    (M : ι → ℝ) (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤M i)
    (hM : ∀ i,1≤M i) (a b : ℝ) (ha : 0<a)
    (hslot : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (f : Ideal O → ℂ) (keep : O → Prop) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceRestrictedEnergy keep (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I => if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K)/(Traw*∏ i,P i)≤
      ((actualAllocations S C).card:ℝ)*
        (((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ))*
          ∑ B : actualAllocations S C, ((sourceRestrictedEnergy keep
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K)/remainingRaw B Traw P) := by
  have h := normalized_restricted_child_energy S hS hp C R s hC hsC ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ Traw hTraw hP f keep W K hK hW
  apply h.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B hB
  have hb := (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
  have hprod : finiteTupleProduct (B : Tuple ι)=C := (Finset.mem_filter.mp B.property).2
  have hc := frozen_normalized_cost (ι:=ι) (B : Tuple ι) hb C R hC.1 hprod ν Wslot P M hP hν hWnorm hM a b ha hslot
  apply mul_le_mul_of_nonneg_right hc
  have hr := raw_scale_identity B hb Traw P
  have hpR := rawReduction_pos B hb P hP
  have htotal : 0<Traw*∏ i,P i := mul_pos hTraw (Finset.prod_pos (fun i _ => hP i))
  have hpL : 0<remainingRaw B Traw P := (mul_pos_iff_of_pos_right hpR).mp (hr.symm ▸ htotal)
  exact div_nonneg (sourceRestrictedEnergy_nonneg keep _ _ f W K hK hW) hpL.le

end SevenEighths.CenteredMomentRestrictedSourceNormalization

end

end OAI
end OAIOriginalModule1732

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSourceEnergy
Source SHA256: 1828f5356c3ee48438f1f776043909e4a7aa16527f72a134aad5373b2ffb976e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1733




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourceEnergy
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors CenteredMomentCommonSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def secondSourceKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' h : O,(primaryGaussRow I h*star (primaryGaussRow J h))*
    W (‖ConcreteTraceCRT.eisEmbedding h‖^2/K)

theorem heightCoeff_mul (τ : Character) (t : ℝ) (I J : Ideal O) :
    heightCoeff τ t (I*J)=heightCoeff τ t I*heightCoeff τ t J := by
  have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t)=
      (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg
      (Nat.cast_nonneg (Ideal.absNorm I):(0:ℝ)≤Ideal.absNorm I)
      (Nat.cast_nonneg (Ideal.absNorm J):(0:ℝ)≤Ideal.absNorm J) (Complex.I*t)
  simp only [heightCoeff,map_mul,Nat.cast_mul,hpow]
  ring

theorem source_energy_common_sectors (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    sourceGaussEnergy S β (heightCoeff τ t) W K=
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((β q.1*heightCoeff τ t q.1)*star (β q.2*heightCoeff τ t q.2))*
            secondSourceKernel q.1 q.2 W K := by
  rw [sourceGaussEnergy,gaussEnergy_expand _ _ _ _ W K hK]
  have hk (I J : supportedColumns S) :
      (∑' h : O,(gaussRow (sourceGenerator S I) (sourceGenerator_supported S I) h*
        star (gaussRow (sourceGenerator S J) (sourceGenerator_supported S J) h))*
          W (‖ConcreteTraceCRT.eisEmbedding h‖^2/K))=secondSourceKernel I J W K := by
    unfold secondSourceKernel
    apply tsum_congr
    intro h
    simp only [primaryGaussRow,dite_eq_left (Finset.mem_filter.mp I.property).2,
      dite_eq_left (Finset.mem_filter.mp J.property).2,sourceGenerator]
  simp_rw [hk]
  let F := fun I J : Ideal O =>
    ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*secondSourceKernel I J W K
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,F I J)=_
  have he (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort (supportedColumns S) (F I)
  simp_rw [he]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ _

theorem source_sector_independent_columns (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((β q.1*heightCoeff τ t q.1)*star (β q.2*heightCoeff τ t q.2))*secondSourceKernel q.1 q.2 W K)=
      heightCoeff τ t C*star (heightCoeff τ t D)*
        ∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
          if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
            ((β (C*a)*heightCoeff τ t a)*star (β (D*b)*heightCoeff τ t b))*
              secondSourceKernel (C*a) (D*b) W K else 0 := by
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I J => ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*secondSourceKernel I J W K),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [heightCoeff_mul,star_mul,mul_zero]
  ring

end SevenEighths.CenteredMomentSecondSourceEnergy

end

end OAI
end OAIOriginalModule1733

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSourcePoisson
Source SHA256: 2415598acfbc57eaa314587597b3e4d6d3eaaa172daeb860169a23f321462764
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1734


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSourcePoisson
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentLiveDomain
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFourier CenteredMomentPoisson
open CenteredMomentSecondSourceEnergy CenteredMomentSupportedCorrelation CenteredMomentRowNorm
local notation "O" => ActualEisensteinCubic.O

theorem secondSourceKernel_poisson (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    secondSourceKernel I J W K=
      (K:ℂ)/((Real.sqrt (Ideal.absNorm I:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm J:ℝ):ℂ))*
        ∑' h : O,actualCorrelation (primaryGenerator I) (primaryGenerator J)
          (by rw [primary_span_supported I hI];exact hI)
          (by rw [primary_span_supported J hJ];exact hJ) (-h)*
          paperRadialFourier W (K*‖eisEmbedding h‖^2/
            ‖eisEmbedding (primaryGenerator I*primaryGenerator J)‖^2) := by
  unfold secondSourceKernel
  simp only [primaryGaussRow,dite_eq_left hI,dite_eq_left hJ,gaussRow]
  rw [sextic_gauss_pair_poisson _ _ ((supported_span_primaryGenerator_iff I).mpr hI)
    ((supported_span_primaryGenerator_iff J).mpr hJ) W K hK]
  simp only [primary_span_supported I hI,primary_span_supported J hJ]

theorem sourceGaussEnergy_poisson (τ : Character) (t : ℝ)
    (S : Finset (Ideal O)) (β : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    sourceGaussEnergy S β (heightCoeff τ t) W K=
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((β I*heightCoeff τ t I)*star (β J*heightCoeff τ t J))*
          ((K:ℂ)/((Real.sqrt (Ideal.absNorm (I:Ideal O):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (J:Ideal O):ℝ):ℂ)))*
            ∑' h : O,actualCorrelation (sourceGenerator S I) (sourceGenerator S J)
              (sourceGenerator_supported S I) (sourceGenerator_supported S J) (-h)*
              paperRadialFourier W (K*‖eisEmbedding h‖^2/
                ‖eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2) := by
  rw [sourceGaussEnergy,gaussEnergy_poisson _ _ _ _ W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2]
  ring

end SevenEighths.CenteredMomentSecondSourcePoisson

end

end OAI
end OAIOriginalModule1734

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondSectorColumns
Source SHA256: e68433440a4791d396c15ba9ffa78f1748681025e42cf59f7a68fe44726235a0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1735




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondSectorColumns
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentSecondSourceEnergy
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentCommonSectors
open CenteredMomentSecondScaled CenteredMomentSupportedCorrelation CenteredMomentChildAssembly
open CenteredMomentFixedRay CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def sectorPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) : Finset (Ideal O) :=
  (residualPool C hC (supportedColumns S)).filter (IsCoprime C)

theorem sectorPool_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (a:Ideal O) :=
  residualPool_supported C hC S ⟨a,(Finset.mem_filter.mp a.property).1⟩

def sectorElement (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : O := primaryGenerator a

theorem sectorElement_span (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Ideal.span {sectorElement C hC S a}=a :=
  primary_span_supported a (sectorPool_supported C hC S a)

theorem sectorElement_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : Supported (Ideal.span {sectorElement C hC S a}) := by
  rw [sectorElement_span]
  exact sectorPool_supported C hC S a

theorem sectorElement_primary (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : sectorPool C hC S) : ConcretePrimeRowBridge.goodLambda^2∣sectorElement C hC S a-1 :=
  (primaryGenerator_spec a (supported_primaryGenerator_ne_zero a (sectorPool_supported C hC S a))).2

theorem coprime_of_same_support (C D a : Ideal O) (hC : C≠0) (hD : D≠0) (ha : a≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) :
    IsCoprime C a ↔ IsCoprime D a := by
  change IdealMobiusDivisorSum.primeSupport C=IdealMobiusDivisorSum.primeSupport D at hCD
  rw [←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC ha,
    ←IdealCoprimeSieveOperator.primeSupport_disjoint_iff hD ha,hCD]

theorem sectorElement_coprime (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (S : Finset (Ideal O)) (a : sectorPool C hC.1 S) :
    IsCoprime (primaryGenerator C*primaryGenerator D) (sectorElement C hC.1 S a) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [←Ideal.span_singleton_mul_span_singleton,primary_span_supported C hC,
    primary_span_supported D hD,sectorElement_span]
  have hc := (Finset.mem_filter.mp a.property).2
  exact hc.mul_left ((coprime_of_same_support C D a hC.1 hD.1
    (sectorPool_supported C hC.1 S a).1 hCD).mp hc)

theorem independent_sector_pools (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (S : Finset (Ideal O)) (F : Ideal O → Ideal O → ℂ) :
    (∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
      if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then F a b else 0)=
    ∑ a : sectorPool C hC S,∑ b : sectorPool D hD S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then F a b else 0 := by
  have he (a : Ideal O) :
      (∑ b : sectorPool D hD S,if IsCoprime a (b:Ideal O) then F a b else 0)=
      ∑ b∈sectorPool D hD S,if IsCoprime a b then F a b else 0 :=
    Finset.sum_coe_sort (sectorPool D hD S) (fun b : Ideal O => if IsCoprime a b then F a b else 0)
  simp_rw [he]
  rw [Finset.sum_coe_sort (sectorPool C hC S)
    (fun a => ∑ b∈sectorPool D hD S,if IsCoprime a b then F a b else 0)]
  simp only [sectorPool,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hCa : IsCoprime C a
  · simp only [hCa,ite_true,true_and]
    apply Finset.sum_congr rfl
    intro b hb
    have hcb := coprime_of_same_support C D b hC hD
      (residualPool_supported D hD S ⟨b,hb⟩).1 hCD
    by_cases hDb : IsCoprime D b <;> simp [hcb,hDb]
  · simp only [hCa,ite_false,false_and,Finset.sum_const_zero]

end SevenEighths.CenteredMomentSecondSectorColumns

end

end OAI
