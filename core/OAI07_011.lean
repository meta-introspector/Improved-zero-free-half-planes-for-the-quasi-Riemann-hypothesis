
lemma original_rawVolume (s : Input ι) (R seed : Ideal O) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (original s R seed)=volume s := by
  simp [CenteredMomentFirstAllocationGaussEnergy.rawVolume,original,volume]

lemma allocated_input_columns (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    (allocatedData (original s R seed) C L B).columns=
      (original (child s C R B τ t) (R*C) L).columns ∧
    (allocatedData (original s R seed) C L B).beta=
      (original (child s C R B τ t) (R*C) L).beta := by
  have hh := child_columns s C R L B τ t
  simpa only [OriginalData.columns,OriginalData.beta,allocated_pools,allocated_profile,original] using hh

lemma allocated_input_volume (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      volume (child s C R B τ t) := by
  simp only [CenteredMomentFirstAllocationGaussEnergy.rawVolume,allocatedData,original,
    volume,child,commonData,one_mul,div_mul_div_comm]

lemma allocated_input_energy (s : Input ι) (C R seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)=
      childNormalizedGaussSource s C R L B τ t W K := by
  obtain ⟨hc,hb⟩ := allocated_input_columns s C R seed L B τ t
  unfold CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy
  rw [hc,hb,allocated_input_volume s C R seed L B τ t]
  rfl

theorem common_energy_allocated_inputs (N : ℕ) (a b : ℝ) (ha : 0<a)
    (s : Input ι) (hcard : Fintype.card ι≤N) (haS : a≤s.lower) (hbS : s.upper≤b)
    (C R seed : Ideal O) (hC : Supported C) (hseed : seed∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (commonEnergy (original s R seed) C hC τ t L W K).re / volume s ≤
      (max 1 b)^N * ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
        ∑B : actualAllocations s.pools C,
          (CenteredMomentFirstAllocationGaussEnergy.frozenControl B.val s.M)^2 *
            childNormalizedGaussSource s C R L B τ t W K := by
  have hh := CenteredMomentFirstAllocationGaussEnergy.normalized_common_energy_bound N a b ha
    (original s R seed) hcard s.pools_ne s.prime C hC hseed τ t L W K hK hW
    s.X₁_pos s.X₂_pos one_ne_zero one_ne_zero s.P_pos s.M
    (fun i=>zero_le_one.trans (s.M_ge_one i)) s.ν_bound s.W_bound
    (fun i x hx=>⟨haS.trans (s.slot_support i hx).1,(s.slot_support i hx).2.trans hbS⟩)
  rw [← commonEnergy_real _ _ _ _ _ _ _ _ hK,original_rawVolume] at hh
  change (commonEnergy (original s R seed) C hC τ t L W K).re / volume s ≤
    (max 1 b)^N * ((actualAllocations s.pools C).card:ℝ)/(Ideal.absNorm C:ℝ) *
      ∑B : actualAllocations s.pools C,
        (CenteredMomentFirstAllocationGaussEnergy.frozenControl B.val s.M)^2 *
          (CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s R seed) C L B τ t W K /
            CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s R seed) C L B)) at hh
  simpa only [allocated_input_energy] using hh

lemma allocated_input_masked_energy (s : Input ι) (C R T seed L : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentFirstAllocationGaussEnergy.allocatedEnergy (original s (R*T) seed) C L B τ t W K /
      CenteredMomentFirstAllocationGaussEnergy.rawVolume (allocatedData (original s (R*T) seed) C L B)=
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) L).columns
      (CenteredMomentFirstMaskedFamily.maskedSource (idealGenerator T)
        (original (child s C R B τ t) (R*C) L).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) := by
  rw [allocated_input_energy,CenteredMomentFirstMaskedInput.normalized_child_mask]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2313

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstCommonSourceBudget
Source SHA256: 918971dc0018b2ee621314d645e72860bfeb5d8735caf644344132915ee2df45
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2314



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonSourceBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn CenteredMomentFirstAllocationGaussEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

lemma child_nonneg (s:Input ι)(C R seed:Ideal O)(B:actualAllocations s.pools C)
    (τ:Character)(t:ℝ)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)
    (hW:∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re):
    0≤childNormalizedGaussSource s C R seed B τ t W K:=by
  rw [←allocated_input_energy s C R seed seed B τ t W K]
  apply div_nonneg
  · exact allocated_nonneg (original s R seed) C seed B τ t W K hK hW
  · rw [allocated_input_volume s C R seed seed B τ t]
    exact (CenteredMomentAmplificationChildInput.volume_pos _).le

theorem common_energy_live_allocations (N:ℕ)(a b:ℝ)(ha:0<a)
    (s:Input ι)(hcard:Fintype.card ι≤N)(haS:a≤s.lower)(hbS:s.upper≤b)
    (C R seed:Ideal O)(hC:Supported C)(hseed:seed∣C)
    (τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)
    (hW:∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re):
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
    (max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)*
      ∑B:actualAllocations s.pools C,
        if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
          (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K
        else 0:=by
  have hh:=normalized_common_energy_allocation (original s R seed) s.pools_ne s.prime C hC hseed
    τ t L W K hK hW s.X₁_pos s.X₂_pos one_ne_zero one_ne_zero s.P_pos
  rw [←commonEnergy_real _ _ _ _ _ _ _ _ hK,original_rawVolume] at hh
  change _ ≤ ((actualAllocations s.pools C).card:ℝ)*
    ∑B:actualAllocations s.pools C,
      (‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
        (allocatedEnergy (original s R seed) C L B τ t W K/
          rawVolume (allocatedData (original s R seed) C L B)) at hh
  simp_rw [allocated_input_energy s C R seed L _ τ t W K] at hh
  apply hh.trans
  calc
    _≤((actualAllocations s.pools C).card:ℝ)*
      ∑B:actualAllocations s.pools C,
        ((max 1 b)^N/(C.absNorm:ℝ))*
          (if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
            (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K
          else 0):=by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      by_cases hz:frozenCoefficient B.val C R s.ν s.W s.P=0
      · simp only [hz,ne_eq,not_true_eq_false,ite_false,norm_zero,zero_pow (by decide:2≠0),zero_div,zero_mul,mul_zero]
        exact le_rfl
      · rw [ite_eq_left hz]
        have hf:=frozen_normalized_bound N a b ha (original s R seed) hcard C hC.1 B s.M
          (fun i=>zero_le_one.trans (s.M_ge_one i)) s.P_pos s.ν_bound s.W_bound
          (fun i x hx=>⟨haS.trans (s.slot_support i hx).1,(s.slot_support i hx).2.trans hbS⟩)
        have hn:=child_nonneg s C R L B τ t W K hK hW
        change ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P≤
          (max 1 b)^N/(C.absNorm:ℝ)*(frozenControl B.val s.M)^2 at hf
        convert mul_le_mul_of_nonneg_right hf hn using 1 ; ring
    _=_:=by rw [←Finset.mul_sum];ring

theorem common_energy_from_live_children (N:ℕ)(a b ε:ℝ)(ha:0<a)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{κ:Type*}[Fintype κ],∀s:Input κ,
    Fintype.card κ≤N → a≤s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K E:ℝ),0<K → 0≤E →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤E*(∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*E*(∏i,s.M i)^2:=by
  obtain ⟨D,hD,hmass⟩:=allocated_control_mass N ε hε
  refine ⟨(max 1 b)^N*D,mul_pos (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _) hD,?_⟩
  intro κ _ s hcard haS hbS C R seed hC hseed τ t L W K E hK hE hW hchild
  have hh:=common_energy_live_allocations N a b ha s hcard haS hbS C R seed hC hseed τ t L W K hK hW
  apply hh.trans
  have hc:0≤(max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ):=by positivity
  have hs:(∑B:actualAllocations s.pools C,
      if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
        (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K else 0)≤
      E*∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2:=by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro B hB
    split_ifs with hb
    · convert mul_le_mul_of_nonneg_left (hchild B hb) (sq_nonneg (frozenControl B.val s.M)) using 1 ; ring
    · positivity
  have hm:=hmass hcard s C R hC.1 τ t
  calc
    _≤((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ))*
        (E*∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2):=
      mul_le_mul_of_nonneg_left hs hc
    _=((max 1 b)^N*E)*(((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)*
        ∑B:actualAllocations s.pools C,(frozenControl B.val s.M)^2*(∏i,(child s C R B τ t).M i)^2):=by ring
    _≤((max 1 b)^N*E)*(D*(C.absNorm:ℝ)^(ε-1)*(∏i,s.M i)^2):=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (by positivity) hE)
    _=_:=by ring

end SevenEighths.CenteredMomentFirstCommonSourceBudget

end

end OAI
end OAIOriginalModule2314

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstCommonSourcePowerBudget
Source SHA256: 70f57bc1b23cf733130caca630d46749a6ad6ef5a0deb1b8b359b94948b71e0f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2315



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonSourcePowerBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstCommonSourceBudget
local notation "O"=>ActualEisensteinCubic.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

theorem common_energy_power_budget (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → a≤s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ),0<K →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(CenteredMomentAmplificationChildInput.volume (child s C R B τ t))^(α j))*
          (∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-1)*
          (∑j,E j*(b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))^(α j))*
            (∏i,s.M i)^2:=by
  obtain ⟨Cbound,hCbound,hbound⟩:=common_energy_from_live_children N a b ε ha hε
  refine ⟨Cbound,hCbound,?_⟩
  intro ι _ s hcard haS hbS C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hv:=CenteredMomentAmplificationChildInput.volume_pos s
  have hn:=CenteredMomentFirstScale.norm_pos C hC.1
  apply hbound s hcard haS hbS C R seed hC hseed τ t L W K _ hK
    (Finset.sum_nonneg (fun j _=>mul_nonneg (hE j) (Real.rpow_nonneg (by positivity) _))) hW
  intro B hB
  apply (hchild B hB).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (hE j)
  exact Real.rpow_le_rpow (CenteredMomentAmplificationChildInput.volume_pos _).le
    (CenteredMomentAmplificationChildSourceCaps.common_volume_le N b hb s hcard hbS C R B τ t hB) (hα j)

theorem common_energy_linear_volume (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cbound:ℝ,0<Cbound ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → a≤s.lower → s.upper≤b →
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C →
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K E:ℝ),0<K → 0≤E →
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      childNormalizedGaussSource s C R L B τ t W K≤
        E*CenteredMomentAmplificationChildInput.volume (child s C R B τ t)*
          (∏i,(child s C R B τ t).M i)^2)→
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
        Cbound*(C.absNorm:ℝ)^(ε-2)*CenteredMomentAmplificationChildInput.volume s*E*(∏i,s.M i)^2:=by
  obtain ⟨Cbound,hCbound,hbound⟩:=common_energy_from_live_children N a b ε ha hε
  refine ⟨Cbound*b^N,mul_pos hCbound (pow_pos (zero_lt_one.trans_le hb) _),?_⟩
  intro ι _ s hcard haS hbS C R seed hC hseed τ t L W K E hK hE hW hchild
  have hv:=CenteredMomentAmplificationChildInput.volume_pos s
  have hn:=CenteredMomentFirstScale.norm_pos C hC.1
  have hh:=hbound s hcard haS hbS C R seed hC hseed τ t L W K
    (E*(b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ))) hK
    (mul_nonneg hE (by positivity)) hW (fun B hB=>by
      apply (hchild B hB).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (CenteredMomentAmplificationChildSourceCaps.common_volume_le N b hb s hcard hbS C R B τ t hB) hE)
        (sq_nonneg _))
  apply hh.trans_eq
  have hp:(C.absNorm:ℝ)^(ε-2)=(C.absNorm:ℝ)^(ε-1)/(C.absNorm:ℝ):=by
    rw [show ε-2=(ε-1)-1 by ring,Real.rpow_sub hn,Real.rpow_one]
  rw [hp]
  ring

end SevenEighths.CenteredMomentFirstCommonSourcePowerBudget

end

end OAI
end OAIOriginalModule2315

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstCommonReferencePower
Source SHA256: 6e4df380f9fce104640b0a4ae257beed0dfab7c143a3bb14dda8958271e07caf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2316



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstCommonReferencePower
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstCommonSourceBudget
open CenteredMomentFirstCommonSourcePowerBudget
local notation "O"=>HeckeFamily.O
local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

def normalizedPower (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ):ℝ:=
  C^ε*(b^N)^α*E/q*(V/C)^(α-1)*Z^(-allowance)

lemma normalizedPower_nonneg (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ)
    (hb:0≤b)(hV:0≤V)(hC:0≤C)(hq:0≤q)(hZ:0≤Z)(hE:0≤E):
    0≤normalizedPower b V C q Z allowance ε E N α:=by
  unfold normalizedPower
  positivity

lemma reference_power_identity (b V C q Z allowance ε E:ℝ)(N:ℕ)(α:ℝ)
    (hb:0<b)(hV:0<V)(hC:0<C)(hq:0<q)(hZ:0<Z):
    (q*(V/C)^2*Z^allowance)*normalizedPower b V C q Z allowance ε E N α=
      C^(ε-1)*V*E*(b^N*V/C)^α:=by
  have hx:0<V/C:=div_pos hV hC
  have hbN:0<b^N:=pow_pos hb N
  have hprod:Z^allowance*Z^(-allowance)=1:=by
    rw [←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero]
  unfold normalizedPower
  rw [Real.rpow_sub hx,Real.rpow_one,Real.rpow_sub hC,Real.rpow_one,
    show b^N*V/C=b^N*(V/C) by ring,Real.mul_rpow hbN.le hx.le]
  field_simp
  calc
    _ = E*(Z^allowance*Z^(-allowance)):=by ring
    _ = E:=by rw [hprod,mul_one]

theorem common_energy_reference_powers (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N→a≤s.lower→s.upper≤b→
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C→
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K Z allowance:ℝ),0<K→0<Z→
    (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
    ∀(n:ℕ)(E α:Fin n→ℝ),(∀j,0≤E j)→(∀j,0≤α j)→
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      childNormalizedGaussSource s C R L B τ t W K≤
        (∑j,E j*(volume (child s C R B τ t))^(α j))*(∏i,(child s C R B τ t).M i)^2)→
    (commonEnergy (original s R seed) C hC τ t L W K).re≤
      ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
        (Cb*(∏i,s.M i)^2*∑j,normalizedPower b (volume s) (C.absNorm:ℝ)
          (τ.modulus.absNorm:ℝ) Z allowance ε (E j) N (α j)):=by
  obtain ⟨Cb,hCb,hbound⟩:=common_energy_power_budget N a b ε ha hb hε
  refine ⟨Cb,hCb,?_⟩
  intro ι _ s hc hlo hhi C R seed hC hseed τ t L W K Z allowance hK hZ hW n E α hE hα hchild
  have hV:=volume_pos s
  have hNC:=CenteredMomentFirstScale.norm_pos C hC.1
  have hq:=CenteredMomentFirstScale.norm_pos τ.modulus τ.modulus_ne_bot
  have hh:=hbound s hc hlo hhi C R seed hC hseed τ t L W K hK hW n E α hE hα hchild
  have hh':=(div_le_iff₀ hV).mp hh
  apply hh'.trans_eq
  calc
    _ = Cb*(∏i,s.M i)^2*∑j,(C.absNorm:ℝ)^(ε-1)*volume s*E j*
        (b^N*volume s/(C.absNorm:ℝ))^(α j):=by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = Cb*(∏i,s.M i)^2*∑j,
        ((τ.modulus.absNorm:ℝ)*(volume s/(C.absNorm:ℝ))^2*Z^allowance)*
          normalizedPower b (volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
            Z allowance ε (E j) N (α j):=by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      exact (reference_power_identity b (volume s) (C.absNorm:ℝ) (τ.modulus.absNorm:ℝ)
        Z allowance ε (E j) N (α j) (zero_lt_one.trans_le hb) hV hNC hq hZ).symm
    _ = _:=by rw [←Finset.mul_sum];ring

end SevenEighths.CenteredMomentFirstCommonReferencePower

end

end OAI
end OAIOriginalModule2316

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceCommonBound
Source SHA256: b8fad867982e95680592c8c7de066297a5bc1868f36a831d6c6648e853d13ab9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2317




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSecondIdealBlockBound
local notation "O"=>ActualEisensteinCubic.O
universe u

theorem fixed_log_block_from_common_energy (W:𝓢(ℝ,ℂ))(decay J₁ J₂:ℕ):
    ∃Cbound:ℝ,0≤Cbound ∧ ∀{ι:Type u}[Fintype ι],∀η:Character,∀s:OriginalData ι,
    ∀t:ℝ,∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(E:Finset (CommonIndex C D))(rows:Finset O),(∀h∈rows,h≠0)→
    ∀K K₀ H₀ A₀ B₀:ℝ,0<K→0<K₀→0<H₀→0<A₀→0<B₀→
    ∀(U:𝓢(ℝ,ℂ))(H:ℝ),0<H→
    (∀h:O,0≤(U (‖eisEmbedding h‖^2/H)).re)→
    (∀h∈rows,1≤(U (‖eisEmbedding h‖^2/H)).re)→
    ∀E₁ E₂:Ideal O→ℝ,
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),0≤E₁ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),0≤E₂ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L U H).re≤E₁ L*(1+‖v‖)^(2*J₁))→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}),∀χ:RayCharacter,∀v:ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L U H).re≤E₂ L*(1+‖v‖)^(2*J₂))→
    (1+K₀*H₀/(A₀*B₀))^decay*
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K K₀ H₀ A₀ B₀‖≤
      ‖scalar C D hC E K A₀ B₀‖*Cbound*
        ∑L∈divisorPool (Finset.univ:Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)):=by
  obtain ⟨Cb,hCb,hbound⟩:=physical_block_child_bound W (fun _=>logAnnulus) (fun _=>Real.log 4)
    (fun _=>Real.log_nonneg (by norm_num)) (fun _ _ hn=>logAnnulus_enclosure _ hn) decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
    U H hH hU hmajor E₁ E₂ hE₁ hE₂ hleft hright
  apply hbound η (fixedBadMask*idealGenerator s.R) t s.columns s.beta C D hC hD hCD E rows hrows
    K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
    (fun _ _=>logAnnulus_norm _) (fun _ _=>logAnnulus_norm _) U H hH hU hmajor
    (fun L=>windowBudget J₁ t (E₁ L)) (fun L=>windowBudget J₂ t (E₂ L))
    (fun L _=>windowBudget_nonneg _ _ _) (fun L _=>windowBudget_nonneg _ _ _)
  · intro L hL χ θ
    exact (fixedPair η C D hC E χ χ).left_window_energy s t θ A₀ hA₀ L U H hH hU J₁ (E₁ L)
      (hE₁ L hL) (hleft L hL χ)
  · intro L hL χ θ
    exact (fixedPair η C D hC E χ χ).right_window_energy hD hCD s t θ B₀ hB₀ L U H hH hU J₂ (E₂ L)
      (hE₂ L hL) (hright L hL χ)

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2317

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalAnnularCommonBound
Source SHA256: 77e400002f3cbe68b558f7ed3db9ec13b984241953e8bc415393b082ddbc8bd7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2318




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalAnnularCommonBound
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
universe u

theorem actual_annular_block_from_common_energy (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ E₁ E₂ : Ideal O→ℝ,
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), 0≤E₁ L) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), 0≤E₂ L) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ E₁ L*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ E₂ L*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        ∑ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (windowBudget J₁ t (E₁ L)*windowBudget J₂ t (E₂ L)) := by
  obtain ⟨Cb,hCb,hbound⟩:=fixed_log_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n E₁ E₂ hE₁ hE₂ hleft hright
  rw [block_activeRows η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta
    C D hC hD E rows W K n]
  exact hbound η s t C D hC hD hCD E (activeRows rows n)
    (activeRows_nonzero rows n) K (dyadicScale (n 0)) (dyadicScale (n 1))
    (dyadicScale (n 2)) (dyadicScale (n 3)) hK
    (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _) (dyadicScale_pos _)
    CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1)) (dyadicScale_pos _) (fun _=>CenteredMomentFirstAnnularMajorant.profile_nonneg _)
    (fun h hh=>by
      have hn:=activeRows_norm rows n h hh
      have hm:=CenteredMomentFirstAnnularMajorant.scaled_majorant
        (dyadicScale (n 1)) (normValue h) (dyadicScale_pos _) hn.2.1.le hn.2.2.le
      simpa only [normValue_eq_embedding] using hm.ge)
    E₁ E₂ hE₁ hE₂ hleft hright

end SevenEighths.CenteredMomentFirstPhysicalAnnularCommonBound

end

end OAI
end OAIOriginalModule2318

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
Source SHA256: 2fcbc7b8aa9904099aa04b89cc26e5729db519a4fb062690c3d84e5f9dd960c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2319



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondInputGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
local instance {α:Type*}:DecidableEq α:=Classical.decEq _

def exponent (A D P q ε ξ:ℝ):ℝ:=
  max (A+ε) (max (2*A+D+ε+ξ/2) (max (A+P+ε) q))

structure Ready {ι:Type*}[Fintype ι](s:Input ι)(R:Ideal O)(K Z ξ B:ℝ):Prop where
  puncture_ne : R≠0
  scale_pos : 0<K
  volume_cap : volume s≤Z^B
  source_nonneg : 0≤sourceRadius s
  source_cap : sourceRadius s≤Z^B
  conductor_cap : (s.η.modulus.absNorm:ℝ)≤Z^B
  puncture_cap : (R.absNorm:ℝ)≤Z^B
  nominal_pos : 0<nominal s K
  nominal_cap : nominal s K≤Z^B
  frequency_pos : 0<frequencyRadius (nominal s K) Z ξ
  frequency_cap : frequencyRadius (nominal s K) Z ξ≤Z^B

theorem normalized_zero {ι:Type*}[Fintype ι](s:Input ι)(R seed:Ideal O)
    (hz:∀I:Ideal O,(original s R seed).beta I=0)(W:𝓢(ℝ,ℂ))(K:ℝ):
    normalizedGaussSource s R seed W K=0:=by
  simp [normalizedGaussSource,sourceGaussEnergy,gaussEnergy,gaussPolynomial,hz]

theorem eventually_twice_ready (N:ℕ)(b b₁ b₂ ε:ℝ)
    (hb:1≤b)(hb₁:1≤b₁)(hb₂:1≤b₂)(hε:0<ε):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R seed:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)→
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:Character)(v K A D P q ξ:ℝ),
    0<K → 0≤ξ → s.W₁ 0=0 → s.W₂ 0=0 →
    volume s≤Z^A → K⁻¹≤Z^D → (R.absNorm:ℝ)≤Z^P → (υ.modulus.absNorm:ℝ)≤Z^q →
    (∃I:Ideal O,(original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0)→
    Ready (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) K Z ξ (exponent A D P q ε ξ):=by
  filter_upwards [eventual_twice_caps N b b₁ b₂ ε hb hb₁ hb₂ hε,
    eventual_live_puncture N b b₁ b₂ ε hb hb₁ hb₂ hε] with Z hc hp
  refine ⟨hc.1,?_⟩
  intro ι _ s hs he C R seed B τ t hR hB Q hQ k hslot Bp υ v K A D P q ξ
    hK hξ hz₁ hz₂ hV hKi hRN hυ hlive
  have hh:=hc.2 s hs he C R B τ t hB Q hQ k hslot Bp υ v K A D ξ hK hV hKi
  have hr:=hp.2 s hs he C R seed B τ t hB Q hQ k hslot Bp υ v A P hz₁ hz₂ hV hRN hlive
  have h₁:A+ε≤exponent A D P q ε ξ:=le_max_left _ _
  have h₂:2*A+D+ε+ξ/2≤exponent A D P q ε ξ:=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃:A+P+ε≤exponent A D P q ε ξ:=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄:q≤exponent A D P q ε ξ:=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y:ℝ}(h:x≤y):Z^x≤Z^y:=Real.rpow_le_rpow_of_exponent_le hc.1.le h
  refine ⟨mul_ne_zero (mul_ne_zero hR (allocation_ne s C B)) (pow_ne_zero k hQ),hK,
    hh.1.trans (hpow h₁),hh.2.1,hh.2.2.1.trans (hpow h₁),
    hυ.trans (hpow h₄),hr.trans (hpow h₃),hh.2.2.2.1,
    hh.2.2.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.trans (hpow h₂)⟩

end SevenEighths.CenteredMomentFirstSecondInputGates

end

end OAI
end OAIOriginalModule2319

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSecondActiveErrorGates
Source SHA256: af55991af09be9a66e62883aaa15dfed71c355105f2559f6ed880991b4498a37
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2320



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondActiveErrorGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentFirstSecondInputGates CenteredMomentFirstAnnularInput
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type*} [Fintype ι]

def errorInput (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) : Input (liveIndices Bp.val) :=
  child (activeInput (child s C R B τ t)) (Q^k) (R*C) Bp υ v

lemma active_endpoints (s : Input ι) (b b₁ b₂ : ℝ) (he : Endpoints b b₁ b₂ s) :
    Endpoints b b₁ b₂ (activeInput s) := he

theorem error_caps (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I)
    (Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
    (υ : Character) (v : ℝ) :
    let d := errorInput s C R B τ t Q k Bp υ v;
    let H := volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k);
    0<H ∧ 0≤sourceRadius d ∧ volume d≤geometry N b b₁ b₂*H ∧
      sourceRadius d≤geometry N b b₁ b₂*H := by
  dsimp only
  have hC := norm_ge_one C (allocation_ne s C B)
  have hNp : 0<(Q.absNorm:ℝ)^k := pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k
  have hH : 0<volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k) :=
    div_pos (volume_pos s) (mul_pos (zero_lt_one.trans_le hC) hNp)
  have hv : volume (errorInput s C R B τ t Q k Bp υ v)≤
      b^N*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
    rw [errorInput,child_volume _ Q hQ k hslot,active_volume]
    exact (div_le_div_of_nonneg_right (common_volume_le N b hb s hc he.1 C R B τ t hne)
      hNp.le).trans_eq (by ring)
  have hc1 := (live_card_le B.val).trans hc
  have hc2 := (live_card_le Bp.val).trans hc1
  have hep := endpoints_child b b₁ b₂ _
    (active_endpoints _ b b₁ b₂ (endpoints_child b b₁ b₂ s he C R B τ t))
    (Q^k) (R*C) Bp υ v
  have hr := radius_bound N b b₁ b₂ hb h₁ h₂ _ hc2 hep
  have hpow : b^N≤geometry N b b₁ b₂ := by
    have hp : 1≤b^N := one_le_pow₀ hb
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    have hh : 1≤b₁*b₂ := by nlinarith
    nlinarith
  refine ⟨hH,hr.1,hv.trans (mul_le_mul_of_nonneg_right hpow hH.le),?_⟩
  exact hr.2.trans ((mul_le_mul_of_nonneg_left hv (show 0≤b^N*b₁*b₂ by positivity)).trans_eq (by
    unfold geometry;rw [show 2*N=N+N by omega,pow_add];ring))

theorem eventually_active_error_ready (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type*}[Fintype ι],∀s : Input ι,
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R seed : Ideal O)(B : actualAllocations s.pools C)(τ : Character)(t : ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q : Ideal O),Q≠0 → ∀k : ℕ,
    (∀i,∀I∈(activeInput (child s C R B τ t)).slots i,IsCoprime Q I) →
    ∀(Bp : actualAllocations (activeInput (child s C R B τ t)).pools (Q^k))
      (υ : Character)(v K A D P q ξ : ℝ),
    0<K → 0≤ξ → s.W₁ 0=0 → s.W₂ 0=0 →
    volume s≤Z^A → K⁻¹≤Z^D → (R.absNorm:ℝ)≤Z^P → (υ.modulus.absNorm:ℝ)≤Z^q →
    (∃I : Ideal O,(original (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) →
    Ready (errorInput s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) K Z ξ
      (exponent A D P q ε ξ) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε
    (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R seed B τ t hR hB Q hQ k hslot Bp υ v K A D P q ξ
    hK hξ hz₁ hz₂ hVp hKi hRN hυ hlive
  let d := errorInput s C R B τ t Q k Bp υ v
  let G := geometry N b b₁ b₂
  have hg : 1≤G := geometry_ge_one N b b₁ b₂ hb h₁ h₂
  have hcap := error_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hB Q hQ k hslot Bp υ v
  have hd : 0<(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := mul_pos
    (zero_lt_one.trans_le (norm_ge_one C (allocation_ne s C B)))
    (pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k)
  have hd1 : 1≤(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
    have hc := norm_ge_one C (allocation_ne s C B)
    have hq : 1 ≤ (Q.absNorm : ℝ)^k := one_le_pow₀ (norm_ge_one Q hQ)
    nlinarith
  have hHV : volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)≤volume s :=
    div_le_self (volume_pos s).le hd1
  have hm := mul_le_mul_of_nonneg_left hHV (zero_le_one.trans hg)
  have hpoly := polynomial_caps G (volume s) (volume d) (sourceRadius d) K Z A D ε ξ
    hg hZ.1 hZ.2.2 (volume_pos s) (volume_pos d) hcap.2.1 hK
    (hcap.2.2.1.trans hm) (hcap.2.2.2.trans hm) hVp hKi
  obtain ⟨I,hI⟩ := hlive
  have hi := child_column_norm (activeInput (child s C R B τ t)) (Q^k) (R*C) seed Bp υ v hz₁ hz₂ I hI
  have hone : 1≤G*(volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) :=
    (norm_ge_one I hi.1).trans (hi.2.2.trans hcap.2.2.2)
  rw [←mul_div_assoc] at hone
  have hprod : (C.absNorm:ℝ)*(Q.absNorm:ℝ)^k≤G*volume s := by
    simpa only [one_mul] using (le_div_iff₀ hd).mp hone
  have hpunct : (((R*C)*(Q^k)).absNorm:ℝ)≤Z^(A+P+ε) := by
    rw [puncture_norm]
    calc
      _≤(R.absNorm:ℝ)*(G*volume s) := by nlinarith [mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg R.absNorm)]
      _≤Z^P*(Z^ε*Z^A) := mul_le_mul hRN
        (mul_le_mul hZ.2.1 hVp (volume_pos s).le (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _))
        (mul_nonneg (zero_le_one.trans hg) (volume_pos s).le)
        (Real.rpow_nonneg (zero_lt_one.trans hZ.1).le _)
      _=Z^(A+P+ε) := by rw [←Real.rpow_add (zero_lt_one.trans hZ.1),←Real.rpow_add (zero_lt_one.trans hZ.1)];congr 1;ring
  have h₁ : A+ε≤exponent A D P q ε ξ := le_max_left _ _
  have h₂ : 2*A+D+ε+ξ/2≤exponent A D P q ε ξ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : A+P+ε≤exponent A D P q ε ξ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄ : q≤exponent A D P q ε ξ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y : ℝ} (h : x≤y) : Z^x≤Z^y := Real.rpow_le_rpow_of_exponent_le hZ.1.le h
  exact ⟨mul_ne_zero (mul_ne_zero hR (allocation_ne s C B)) (pow_ne_zero k hQ),hK,
    hpoly.1.trans (hpow h₁),hcap.2.1,hpoly.2.1.trans (hpow h₁),
    hυ.trans (hpow h₄),hpunct.trans (hpow h₃),nominal_pos d K hK,
    hpoly.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hpoly.2.2.2.1,hpoly.2.2.2.2.trans (hpow h₂)⟩

end SevenEighths.CenteredMomentFirstSecondActiveErrorGates

end

end OAI
end OAIOriginalModule2320

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSecondCommonGates
Source SHA256: d652f792fecb32a7f1908295880b3d9b1eae4397f3f596643f332618dae9a5eb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2321


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentFirstSecondInputGates
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum CenteredMomentOriginalCommonHarmonic
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O
local instance {α:Type*}:DecidableEq α:=Classical.decEq _

def commonExponent (A D P C q ε ξ:ℝ):ℝ:=
  max (A+ε) (max (2*A+D+ε+ξ/2) (max (P+C) q))

theorem eventually_common_ready (N:ℕ)(b b₁ b₂ ε:ℝ)
    (hb:1≤b)(hb₁:1≤b₁)(hb₂:1≤b₂)(hε:0<ε):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    R≠0 → frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀K A D P Ccap q ξ:ℝ,0<K → 0≤ξ → volume s≤Z^A → K⁻¹≤Z^D →
    (R.absNorm:ℝ)≤Z^P → (C.absNorm:ℝ)≤Z^Ccap → (τ.modulus.absNorm:ℝ)≤Z^q →
    Ready (child s C R B τ t) (R*C) K Z ξ (commonExponent A D P Ccap q ε ξ):=by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε
    (geometry_ge_one N b b₁ b₂ hb hb₁ hb₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hs he C R B τ t hR hB K A D P Ccap q ξ hK hξ hV hKi hRN hCN hτ
  have hC:=allocation_ne s C B
  have hNc:=norm_ge_one C hC
  have hv:=volume_pos s
  have hbN:0≤b^N:=pow_nonneg (zero_le_one.trans hb) _
  have hcv:volume (child s C R B τ t)≤b^N*volume s:=
    (common_volume_le N b hb s hs he.1 C R B τ t hB).trans
      (div_le_self (mul_nonneg hbN hv.le) hNc)
  have hr:=radius_bound N b b₁ b₂ hb hb₁ hb₂ (child s C R B τ t)
    ((live_card_le B.val).trans hs) (endpoints_child b b₁ b₂ s he C R B τ t)
  have hVg:volume (child s C R B τ t)≤geometry N b b₁ b₂*volume s:=by
    apply hcv.trans
    apply mul_le_mul_of_nonneg_right _ hv.le
    apply (pow_le_pow_right₀ hb (show N≤2*N by omega)).trans
    unfold geometry
    exact (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hb) _) hb₁).trans
      (le_mul_of_one_le_right (by positivity) hb₂)
  have hHg:sourceRadius (child s C R B τ t)≤geometry N b b₁ b₂*volume s:=by
    apply hr.2.trans
    apply (mul_le_mul_of_nonneg_left hcv (show 0≤b^N*b₁*b₂ by positivity)).trans_eq
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    ring
  have hc:=polynomial_caps (geometry N b b₁ b₂) (volume s)
    (volume (child s C R B τ t)) (sourceRadius (child s C R B τ t)) K Z A D ε ξ
    (geometry_ge_one N b b₁ b₂ hb hb₁ hb₂) hZ.1 hZ.2.2 hv (volume_pos _) hr.1 hK
    hVg hHg hV hKi
  have h₁:A+ε≤commonExponent A D P Ccap q ε ξ:=le_max_left _ _
  have h₂:2*A+D+ε+ξ/2≤commonExponent A D P Ccap q ε ξ:=
    (le_max_left _ _).trans (le_max_right _ _)
  have h₃:P+Ccap≤commonExponent A D P Ccap q ε ξ:=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h₄:q≤commonExponent A D P Ccap q ε ξ:=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hpow {x y:ℝ}(h:x≤y):Z^x≤Z^y:=Real.rpow_le_rpow_of_exponent_le hZ.1.le h
  have hRC:((R*C).absNorm:ℝ)≤Z^(P+Ccap):=by
    rw [map_mul,Nat.cast_mul,Real.rpow_add (zero_lt_one.trans hZ.1)]
    exact mul_le_mul hRN hCN (Nat.cast_nonneg _) (Real.rpow_nonneg (zero_le_one.trans hZ.1.le) P)
  refine ⟨mul_ne_zero hR hC,hK,hc.1.trans (hpow h₁),hr.1,hc.2.1.trans (hpow h₁),
    hτ.trans (hpow h₄),hRC.trans (hpow h₃),nominal_pos _ K hK,
    hc.2.2.1.trans (hpow ((by linarith : 2*A+D+ε≤2*A+D+ε+ξ/2).trans h₂)),
    hc.2.2.2.1,hc.2.2.2.2.trans (hpow h₂)⟩

end SevenEighths.CenteredMomentFirstSecondInputGates

end

end OAI
end OAIOriginalModule2321

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstWindowBudgets
Source SHA256: 1e7ee603a0c52c9a86413c7a52c97dfd75ecb1229ecdb8bf9301c825b0664310
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2322


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstWindowBudgets
open CenteredMomentSecondWindowBudget

lemma sqrt_sum_le {α:Type*}(s:Finset α)(E:α→ℝ)(hE:∀i∈s,0≤E i):
    Real.sqrt (∑i∈s,E i)≤∑i∈s,Real.sqrt (E i):=by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have he:0≤E a:=hE a (Finset.mem_insert_self _ _)
    have hs:0≤∑i∈s,E i:=Finset.sum_nonneg (fun i hi=>hE i (Finset.mem_insert_of_mem hi))
    have hadd:Real.sqrt (E a+∑i∈s,E i)≤Real.sqrt (E a)+Real.sqrt (∑i∈s,E i):=by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt he,Real.sq_sqrt hs,
          mul_nonneg (Real.sqrt_nonneg (E a)) (Real.sqrt_nonneg (∑i∈s,E i))]
    exact hadd.trans (add_le_add le_rfl (ih (fun i hi=>hE i (Finset.mem_insert_of_mem hi))))

lemma windowBudget_sum {α:Type*}(s:Finset α)(E:α→ℝ)(hE:∀i∈s,0≤E i)
    (J:ℕ)(t:ℝ):
    windowBudget J t (∑i∈s,E i)≤∑i∈s,windowBudget J t (E i):=by
  unfold windowBudget
  rw [←Finset.sum_mul,←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (sqrt_sum_le s E hE) (pow_nonneg (heightEnvelope_pos t).le _))
    (profileMoment_nonneg J)

theorem windowBudget_pair_sum {α β:Type*}(s:Finset α)(u:Finset β)
    (E:α→ℝ)(F:β→ℝ)(hE:∀i∈s,0≤E i)(hF:∀j∈u,0≤F j)
    (J₁ J₂:ℕ)(t:ℝ):
    windowBudget J₁ t (∑i∈s,E i)*windowBudget J₂ t (∑j∈u,F j)≤
      ∑i∈s,∑j∈u,windowBudget J₁ t (E i)*windowBudget J₂ t (F j):=by
  have hh:=mul_le_mul (windowBudget_sum s E hE J₁ t) (windowBudget_sum u F hF J₂ t)
    (windowBudget_nonneg J₂ t _) (Finset.sum_nonneg (fun i _=>windowBudget_nonneg J₁ t (E i)))
  apply hh.trans_eq
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicRows
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentCanonicalFirst CenteredMomentCommonSupport CenteredMomentGaussEnergy
open CenteredMomentLogDyadic CenteredMomentSecondWindowBudget RayFourExpansion CompletedGauss
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
universe u

theorem actual_annular_block_from_four_budgets (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cbound : ℝ, 0≤Cbound ∧ ∀ {ι : Type u} [Fintype ι],
    ∀ (η : Character) (s : OriginalData ι) (t : ℝ)
      (C D : Ideal O) (hC : Supported C) (hD : Supported D),
    primeSupport C=primeSupport D → ∀ (E : Finset (CommonIndex C D))
      (rows : Finset O) (K : ℝ), 0<K → ∀ n : Fin 4→ℤ,
    ∀ E₁ E₂ : Ideal O→Fin 4→ℝ,
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ i,0≤E₁ L i) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ i,0≤E₂ L i) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s C hC (fixedPair η C D hC E χ χ).left v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (∑i,E₁ L i)*(1+‖v‖)^(2*J₁)) →
    (∀ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
      (fun b=>Ideal.span {element C D hD.1 s.columns b}), ∀ χ : RayCharacter, ∀ v : ℝ,
      (commonEnergy s D hD (fixedPair η C D hC E χ χ).right v L
        CenteredMomentFirstAnnularMajorant.profile (dyadicScale (n 1))).re ≤ (∑i,E₂ L i)*(1+‖v‖)^(2*J₂)) →
    (1+dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))^decay *
      ‖block η (fixedBadMask*idealGenerator s.R) 1 t s.columns s.beta C D hC hD E rows W
        (fun _=>logAnnulus) K (dyadicScale (n 0)) (dyadicScale (n 1))
          (dyadicScale (n 2)) (dyadicScale (n 3))‖ ≤
      ‖scalar C D hC E K (dyadicScale (n 2)) (dyadicScale (n 3))‖*Cbound*
        ∑ L∈divisorPool (Finset.univ : Finset (columns C D hD.1 s.columns))
          (fun b=>Ideal.span {element C D hD.1 s.columns b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*
            (∑i:Fin 4,∑j:Fin 4,windowBudget J₁ t (E₁ L i)*windowBudget J₂ t (E₂ L j)) := by
  obtain ⟨Cb,hCb,hbound⟩:=CenteredMomentFirstPhysicalAnnularCommonBound.actual_annular_block_from_common_energy W decay J₁ J₂
  refine ⟨Cb,hCb,?_⟩
  intro ι inst η s t C D hC hD hCD E rows K hK n E₁ E₂ hE₁ hE₂ hleft hright
  have hh:=hbound η s t C D hC hD hCD E rows K hK n
    (fun L=>∑i,E₁ L i) (fun L=>∑i,E₂ L i)
    (fun L hL=>Finset.sum_nonneg (fun i _=>hE₁ L hL i))
    (fun L hL=>Finset.sum_nonneg (fun i _=>hE₂ L hL i)) hleft hright
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) hCb)
  apply Finset.sum_le_sum
  intro L hL
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact windowBudget_pair_sum Finset.univ Finset.univ (E₁ L) (E₂ L)
    (fun i _=>hE₁ L hL i) (fun i _=>hE₂ L hL i) J₁ J₂ t

end SevenEighths.CenteredMomentFirstWindowBudgets

end

end OAI
end OAIOriginalModule2322

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedWindow
Source SHA256: 349212a0ddb54397437f9aa743dcd4854a1e964e88b479709c2c0a0bb67b6166
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2323



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMixedWindow
open CenteredMomentFirstMixedRoot CenteredMomentFirstMixedAllowance CenteredMomentSecondWindowBudget
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstNonexceptionalPrefactor
local notation "O"=>HeckeFamily.O

theorem original_four_budget_reference {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(R seed:Ideal O)(a₁ a₂:ℝ)(ha₁:0<a₁)(ha₂:0<a₂)
    (hs₁:∀x,s.W₁ x≠0→a₁≤x)(hs₂:∀x,s.W₂ x≠0→a₂≤x)
    (m A:O)(t:ℝ)(S:Finset (Ideal O))(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayFourExpansion.RayCharacter)
    (F:FixedPair s.η C D hC E ξ₁ ξ₂)
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(U:Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z:ℝ)(EL ER:Fin 4→ℝ)(JL JR:ℕ)(height:ℝ)(hK:0<K)(hA:0<A₀)(hB:0<B₀)(hZ:1<Z)
    (hEL:∀i,0≤EL i)(hER:∀i,0≤ER i)(hwin:∀i y,U i y≠0→|y|≤M)
    (hn:block s.η m A t S (CenteredMomentOriginalCommonHarmonic.coefficient s R seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0):
    let V:=volume s.toData;
    ‖scalar C D hC E K A₀ B₀‖/V*
      (∑i:Fin 4,∑j:Fin 4,
        windowBudget JL height ((F.left.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i)*
        windowBudget JR height ((F.right.modulus.absNorm:ℝ)*(V/(D.absNorm:ℝ))^2*Z^(allowance D C Z)*ER j))≤
      (‖inactiveWeight C D E‖*(Real.exp M/((∏i,s.lo i)*a₁*a₂))*fixedPresentationCost*K*
        (s.η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm)*
        (∑i:Fin 4,∑j:Fin 4,windowBudget JL height (EL i)*windowBudget JR height (ER j)) :=by
  dsimp only
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hh:=original_fixed_reference_pair s R seed a₁ a₂ ha₁ ha₂ hs₁ hs₂
    m A t S C D hC hD hCD E ξ₁ ξ₂ F rows W U K K₀ H₀ A₀ B₀ M Z
    (EL i) (ER j) hK hA hB hZ (hEL i) (hER j) hwin hn
  have hqL:0<(F.left.modulus.absNorm:ℝ):=norm_pos _ F.left.modulus_ne_bot
  have hqR:0<(F.right.modulus.absNorm:ℝ):=norm_pos _ F.right.modulus_ne_bot
  have hCpos:=norm_pos C hC.1
  have hDpos:=norm_pos D hD.1
  have hV:=volume_pos s.toData
  have hz:0<Z:=zero_lt_one.trans hZ
  have hei:=hEL i
  have herj:=hER j
  have hh':=mul_le_mul_of_nonneg_right hh
    (mul_nonneg (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JL)
      (profileMoment_nonneg JL)) (mul_nonneg (pow_nonneg (heightEnvelope_pos height).le JR)
      (profileMoment_nonneg JR)))
  simp only [Real.sqrt_mul (by positivity : 0≤
    (F.left.modulus.absNorm:ℝ)*(volume s.toData/(C.absNorm:ℝ))^2*Z^(allowance C D Z)*EL i),
    Real.sqrt_mul (hEL i)] at hh'
  unfold windowBudget
  nlinarith only [hh']

end SevenEighths.CenteredMomentFirstMixedWindow

end

end OAI
end OAIOriginalModule2323

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceInternal
Source SHA256: ceb3cb424caeb79f840031156695189f88ff1db3ab88b170caf07a33382b2e79
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2324



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily CenteredExceptionalProfile CenteredExceptionalCount
open HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def internalQ (Q : Ideal O) (η₀ : Character) : Ideal O := Q⊓η₀.modulus

lemma internalQ_ne_zero (Q : Ideal O) (hQ : Q≠0) (η₀ : Character) : internalQ Q η₀≠0 :=
  Ideal.inf_ne_bot_of_ne_bot hQ η₀.modulus_ne_bot

lemma internalQ_ne_top (Q : Ideal O) (hQ : Q≠⊤) (η₀ : Character) : internalQ Q η₀≠⊤ := by
  intro h
  exact hQ (top_le_iff.mp (h ▸ (inf_le_left : internalQ Q η₀≤Q)))

lemma internalQ_coprime (Q P : Ideal O) (η₀ : Character)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η₀.modulus P) : IsCoprime (internalQ Q η₀) P :=
  (hQP.mul_left hηP).of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)

lemma natural_nonzero_base {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O)
    (h : idealCoeff F.character I≠0) : idealCoeff η I≠0 := by
  rw [F.ideal] at h
  exact left_ne_zero_of_mul h

lemma coefficient_forcing_coprime (η₀ : Character) (e : O) (he : elementCoeff η₀ e≠0)
    (Q P : Ideal O) (hQP : IsCoprime Q P) (hPe : P∣Ideal.span {e}) :
    IsCoprime (internalQ Q η₀) P :=
  internalQ_coprime Q P η₀ hQP (CenteredMomentChildRows.old_coefficient_prime_coprime η₀ e he P hPe)

theorem energy_split (η η₀ : Character) (Q : Ideal O) (m A : O)
    (rows : Finset O) (f : O→ℂ) :
    (∑z∈rows,‖f z‖^2)=
      (∑z∈rows.filter (fun z=>¬FixedInducingRow η (internalQ Q η₀) m A z),‖f z‖^2)+
      ∑z∈rows.filter (fun z=>FixedInducingRow η (internalQ Q η₀) m A z),‖f z‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun z=>¬FixedInducingRow η (internalQ Q η₀) m A z)
      (fun z=>‖f z‖^2)).symm

theorem internal_exceptional_count (η η₀ : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (m A : O) (hm : m≠0) (hA : A≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀P∈normalizedFactors D,goodLambda∉P ∧ (2:O)∉P ∧
      IsCoprime Q P ∧ IsCoprime η₀.modulus P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P%6=2)
    (Z C M F : ℝ) (hZ : 0<Z) (hC : 0≤C)
    (hDnorm : Z^(F/2)≤(D.absNorm:ℝ))
    (hN : ∀z∈rows,((Ideal.span {z}).absNorm:ℝ)≤C*Z^M) :
    ((rows.filter (fun z=>FixedInducingRow η (internalQ Q η₀) m A z)).card:ℝ)≤
      768*(6:ℝ)^(normalizedFactors (internalQ Q η₀)).toFinset.card*C^(1/6:ℝ)*Z^((M-2*F)/6) := by
  apply fixed_support_exceptional_count η (internalQ Q η₀) (internalQ_ne_zero Q hQ0 η₀)
    (internalQ_ne_top Q hQ η₀) (inf_le_left.trans hQ72) m A hm hA hmLam hm2
    (rows.filter (fun z=>FixedInducingRow η (internalQ Q η₀) m A z))
    (fun z hz=>hrows z (Finset.mem_filter.mp hz).1)
    (fun z hz=>(Finset.mem_filter.mp hz).2) D hD ?_ Z C M F hZ hC hDnorm
    (fun z hz=>hN z (Finset.mem_filter.mp hz).1)
  intro P hP
  obtain ⟨hLam,h2,hQP,hη₀,hη,hv⟩:=hgood P hP
  exact ⟨hLam,h2,internalQ_coprime Q P η₀ hQP hη₀,hη,hv⟩

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem internal_sector_nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (Q R : Ideal O)
    (hQM : Q≤M) (hR : R≠0) (hz : z≠0)
    (hex : ¬FixedInducingRow η (internalQ Q η₀) (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 z) :
    (F.character.product (relativeCharacter M H hH η₀ θ)).residue≠1 :=
  sector_nonprincipal M H hH F η₀ θ (internalQ Q η₀) R
    (inf_le_left.trans hQM) inf_le_right hR hz hex

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2324

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSlots
Source SHA256: c96953f7c9237f65c58a37367360c80a3617ca5f0103a081cbf56e893fc0bbf2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2325


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeRay HeckePrimeAnnular ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

lemma averaged_sector_coefficient (χ η₀ : Character) (R : Ideal O) (hR : R≠0)
    (θ : RayQuotient.Characters M H) (I : Ideal O) :
    idealCoeff (twistedFamily M H hH ((excluded χ R).product η₀.inverse) θ) I=
      idealCoeff (excluded (χ.product (relativeCharacter M H hH η₀ θ)) R) I := by
  simp only [twistedFamily,relativeCharacter,idealCoeff_product,excluded_ideal _ R hR]
  split_ifs <;> ring

lemma averaged_sector_polynomial (χ η₀ : Character) (R : Ideal O) (hR : R≠0)
    (θ : RayQuotient.Characters M H) (W : ℝ→ℂ) (b D σ t : ℝ) :
    primePolynomial (twistedFamily M H hH ((excluded χ R).product η₀.inverse) θ) W b D σ t=
      primePolynomial (excluded (χ.product (relativeCharacter M H hH η₀ θ)) R) W b D σ t := by
  unfold primePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [averaged_sector_coefficient M H hH χ η₀ R hR θ I]

theorem natural_relative_slot {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W : ℝ→ℂ) (b D σ t v : ℝ) (hD : 0<D) :
    normalizedSlot η (fixedBadMask*idealGenerator R) 1 z (primePool M H b D)
      (fun I=>idealCoeff η₀.inverse I*annularWeight W D σ v I) t D=
      (D:ℂ)^(Complex.I*t)*((RayQuotient.classNumber M H:ℂ)⁻¹*
        ∑θ : RayQuotient.Characters M H,
          primePolynomial (excluded (F.character.product (relativeCharacter M H hH η₀ θ)) R)
            W b D σ (t+v)) := by
  rw [relative_normalizedSlot_eq_ray M H η (excluded F.character R) η₀.inverse
    (fixedBadMask*idealGenerator R) 1 z
    (by simpa only [one_mul] using F.masked_element R hR) W b D σ t v hD,
    rayPrimePolynomial_eq_average M H hH]
  congr 2
  exact Finset.sum_congr rfl (fun θ _=>averaged_sector_polynomial M H hH F.character η₀ R hR θ W b D σ (t+v))

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2325

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceProduct
Source SHA256: c06ebd5d3b18c12e2c201c072db4709865158271d49db5697a2a4c9595ef6995
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2326



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeAnnular ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot CenteredMomentSlotNormalization
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def averageWeight : ℂ := (RayQuotient.classNumber M H:ℂ)⁻¹^(Fintype.card ι)

def sectorValue (χ η₀ : Character) (R : Ideal O) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P σ v : ι→ℝ) (t X₁ X₂ : ℝ)
    (θ : ι→RayQuotient.Characters M H) : ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (twistedIdealSum (excluded χ R) W₁ t X₁*twistedIdealSum (excluded χ R) W₂ t X₂)*
      ∏i,(P i:ℂ)^(Complex.I*t)*
        primePolynomial (excluded (χ.product (relativeCharacter M H hH η₀ (θ i))) R)
          (V i) (b i) (P i) (σ i) (t+v i)

theorem natural_relative_product {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P σ v : ι→ℝ) (t X₁ X₂ : ℝ)
    (hX : 0≤X₁*X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂
      (fun i=>primePool M H (b i) (P i))
      (fun i I=>idealCoeff η₀.inverse I*annularWeight (V i) (P i) (σ i) (v i) I) P t X₁ X₂=
      averageWeight (ι:=ι) M H*∑θ : ι→RayQuotient.Characters M H,
        sectorValue M H hH F.character η₀ R W₁ W₂ V b P σ v t X₁ X₂ θ := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ hX (fun i=>(hP i).le)]
  unfold selectedProduct
  simp_rw [F.masked_plain R hR]
  simp_rw [natural_relative_slot M H hH F η₀ R hR _ _ _ _ _ _ (hP _)]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.prod_sum,
    sectorValue,averageWeight]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  ring

theorem averageWeight_mass :
    ∑_θ : ι→RayQuotient.Characters M H,‖averageWeight (ι:=ι) M H‖=1 := by
  have hc : Fintype.card (RayQuotient.Characters M H)=RayQuotient.classNumber M H :=
    RayOrthogonality.card_characters H
  have hn : (RayQuotient.classNumber M H:ℝ)≠0 := by
    exact_mod_cast (RayQuotient.classNumber_pos M H).ne'
  simp only [averageWeight,Finset.sum_const,Finset.card_univ,Fintype.card_fun,hc,
    norm_pow,norm_inv,Complex.norm_natCast,nsmul_eq_mul,Nat.cast_pow]
  rw [inv_pow,mul_inv_cancel₀ (pow_ne_zero _ hn)]

theorem sector_average_energy (f : (ι→RayQuotient.Characters M H)→ℂ) :
    ‖averageWeight (ι:=ι) M H*∑θ,f θ‖^2≤
      ∑θ,‖averageWeight (ι:=ι) M H‖*‖f θ‖^2 := by
  have hm:=averageWeight_mass (ι:=ι) M H
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hm
  have he:=CubicEisenstein.norm_sum_sq_le_card Finset.univ f
  rw [norm_mul,mul_pow]
  apply (mul_le_mul_of_nonneg_left he (sq_nonneg _)).trans_eq
  rw [←Finset.mul_sum]
  change ‖averageWeight (ι:=ι) M H‖^2*
    ((Fintype.card (ι→RayQuotient.Characters M H):ℝ)*∑θ,‖f θ‖^2)=_
  calc
    _=‖averageWeight (ι:=ι) M H‖*((Fintype.card (ι→RayQuotient.Characters M H):ℝ)*
      ‖averageWeight (ι:=ι) M H‖)*(∑θ,‖f θ‖^2) := by ring
    _= _ := by rw [hm,mul_one]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2326

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePhysical
Source SHA256: b4fcb6c8e724c95c87bfe9bdaa21c39d4ebd1bf91250621c188e7933cb6f8f08
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2327


namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeAnnular ConcretePrimeRowBridge
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots CenteredMomentPrimeSlot
open CenteredMomentDetectorDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem natural_physical_product {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ) (t X₁ X₂ : ℝ)
    (hX : 0≤X₁*X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η₀ (V i) (P i) (external i)) P t X₁ X₂=
      averageWeight (ι:=ι) M H*∑θ : ι→RayQuotient.Characters M H,
        sectorValue M H hH F.character η₀ R W₁ W₂ (fun i x=>conj (V i x)) b P
          (fun i=>1-(external i).re) (fun i=>-(external i).im) t X₁ X₂ θ := by
  have hslot (i : ι) : rowSlot η (fixedBadMask*idealGenerator R) 1 z
      (primePool M H (b i) (P i)) (physicalSlotCoefficient η₀ (V i) (P i) (external i)) t=
      rowSlot η (fixedBadMask*idealGenerator R) 1 z (primePool M H (b i) (P i))
        (fun I=>idealCoeff η₀.inverse I*annularWeight (fun x=>conj (V i x))
          (P i) (1-(external i).re) (-(external i).im) I) t := by
    unfold rowSlot
    apply Finset.sum_congr rfl
    intro I hI
    rw [physicalSlotCoefficient_annular η₀ (V i) (P i) (external i) I
      (Finset.mem_filter.mp hI).2.1.ne_zero (hP i)]
  simpa only [positiveSlotRow,hslot] using natural_relative_product M H hH F η₀ R hR W₁ W₂
    (fun i x=>conj (V i x)) b P (fun i=>1-(external i).re) (fun i=>-(external i).im)
    t X₁ X₂ hX hP

theorem natural_physical_energy {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (R : Ideal O) (hR : R≠0) (W₁ W₂ : ℝ→ℂ)
    (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ) (t X₁ X₂ : ℝ)
    (hX : 0≤X₁*X₂) (hP : ∀i,0<P i) :
    ‖positiveSlotRow η (fixedBadMask*idealGenerator R) 1 z W₁ W₂
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η₀ (V i) (P i) (external i)) P t X₁ X₂‖^2≤
      ∑θ : ι→RayQuotient.Characters M H,‖averageWeight (ι:=ι) M H‖*
        ‖sectorValue M H hH F.character η₀ R W₁ W₂ (fun i x=>conj (V i x)) b P
          (fun i=>1-(external i).re) (fun i=>-(external i).im) t X₁ X₂ θ‖^2 := by
  rw [natural_physical_product M H hH F η₀ R hR W₁ W₂ V b P external t X₁ X₂ hX hP]
  exact sector_average_energy M H _

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2327

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PlainGlobalEnergy
Source SHA256: 57fd327c348fdc6d27d08b0ec13d2ea27657eb119acfb67918e147e476f4383e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2328




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentPlainGlobalEnergy
open HeckeFamily HeckeDyadic CenteredMomentCoreFloor
open CenteredMomentPlainGlobalActual CenteredMomentPositiveSummability
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentHeckeTwist CenteredMomentTwist CenteredMomentDetectorDictionary
open HeckeInverseAmplification CompletedHeight CenteredMomentHeckeHeight
open CenteredMomentLattice CenteredMomentHeckeCancellation CenteredMomentAbsoluteEnergy
local notation "O"=>HeckeFamily.O

 theorem plain_height_norm (χ:Character)(W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(t X:ℝ)(hX:0<X):
    ‖(Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W t X‖=
      ‖polynomial χ false W X 0 t‖:=by
  have hp:(normPowerProfile W a b ha hs hW t:ℝ→ℂ)=twistProfile W 0 t:=by
    funext x
    rw [normPowerProfile_apply]
    unfold twistProfile HeckeDyadic.shift
    simp only [Complex.ofReal_zero,zero_sub,neg_neg]
    rw [mul_comm (Complex.I) (t:ℂ)]
    ring
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX]
  have hi:idealSum χ (normPowerProfile W a b ha hs hW t) X=
      twistedIdealSum χ (normPowerProfile W a b ha hs hW t) 0 X:=by
    simp [idealSum,twistedIdealSum]
  rw [hi]
  have he:(Real.sqrt X:ℂ)⁻¹*((X:ℂ)^(Complex.I*t)*
      twistedIdealSum χ (normPowerProfile W a b ha hs hW t) 0 X)=
      (X:ℂ)^(Complex.I*t)*polynomial χ false W X 0 t:=by
    rw [←polynomial_twistProfile,←hp,plain_zero_height _ _ X hX]
    ring
  rw [he,norm_mul,norm_real_imaginary_power X t hX,one_mul]

 theorem zero_row_norm (η χ:Character)(mask A z:O)
    (hrow:∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) mask 1 (A*z) n)
    (W₁ W₂:ℝ→ℂ)(a b:ℝ)(ha:0<a)(hs₁:Function.support W₁⊆Set.Icc a b)
    (hs₂:Function.support W₂⊆Set.Icc a b)(hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    ‖zeroRow η mask A z t W₁ W₂ X₁ X₂‖=
      ‖polynomial χ false W₁ X₁ 0 t‖*‖polynomial χ false W₂ X₂ 0 t‖:=by
  unfold zeroRow
  rw [rowTwistedSum_eq η χ mask A z hrow,rowTwistedSum_eq η χ mask A z hrow,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  have he:(Real.sqrt X₂:ℂ)⁻¹*(Real.sqrt X₁:ℂ)⁻¹*
      (twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂)=
      ((Real.sqrt X₁:ℂ)⁻¹*twistedIdealSum χ W₁ t X₁)*
      ((Real.sqrt X₂:ℂ)⁻¹*twistedIdealSum χ W₂ t X₂):=by ring
  rw [he,norm_mul,plain_height_norm χ W₁ a b ha hs₁ hW₁ t X₁ hX₁,
    plain_height_norm χ W₂ a b ha hs₂ hW₂ t X₂ hX₂]

 theorem radial_bound_on_keep (F:O→ℂ)(r:Radial)(B:ℝ)(hB:0≤B)
    (hF:∀z,r.keep z→‖F z‖≤B):
    (∑'z:O,if r.keep z then ‖F z‖^2*(r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0)≤
      diagonalControl r.profile*max 1 r.scale*B^2:=by
  have hb:∀z,‖(if r.keep z then F z else 0)‖≤B:=by
    intro z
    by_cases h:r.keep z
    · simpa only [ite_eq_left h] using hF z h
    · simpa only [ite_eq_right h,norm_zero] using hB
  have hs:=bounded_radial_summable _ B hb r.keep r.profile r.scale r.scale_pos
  have heq:(fun z:O=>if r.keep z then
      ‖(if r.keep z then F z else 0)‖^2*(r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0)=
      (fun z:O=>if r.keep z then ‖F z‖^2*(r.profile (‖eisEmbedding z‖^2/r.scale)).re else 0):=by
    funext z
    split_ifs <;> rfl
  rw [heq] at hs
  have hh:=hs.tsum_le_tsum (g:=fun z:O=>B^2*‖r.profile (‖eisEmbedding z‖^2/r.scale)‖) (fun z=>by
    split_ifs with hk
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hF z hk) 2) (norm_nonneg _))
    · positivity) ((radial_norm_summable r.profile r.scale r.scale_pos).mul_left (B^2))
  rw [tsum_mul_left] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (radial_weight_lattice_bound_all r.profile r.scale r.scale_pos) (sq_nonneg B)).trans_eq (by ring))

 theorem zero_all_lengths_floor (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(η:Character)(mask A:O)(r:Radial)(χ:O→Character),
      (∀z,r.keep z→(χ z).residue≠1)→
      (∀z,r.keep z→∀n,elementCoeff (χ z) n=
        CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) mask 1 (A*z) n)→
    ∀(Z m q ρ Cscale t X₁ X₂:ℝ),1≤Z→0≤m→0≤q→0≤Cscale→
      r.scale=Z^m→m+q≤ρ→1≤X₁→1≤X₂→
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤Cscale*Z^(m+q))→
    zeroEnergy η mask A t W₁ W₂ X₁ X₂ r≤
      C*Cscale^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(3+|t|)^8*Z^(m+q+4*ρ):=by
  obtain ⟨S,C,hC,hpoly⟩:=global_polynomial_bound a b ha
  refine ⟨S,C^4,pow_pos hC _,?_⟩
  intro W₁ W₂ hs₁ hs₂ η mask A r χ hχ hrow Z m q ρ Cscale t X₁ X₂ hZ hm hq hCs hscale hfloor hX₁ hX₂ hmod
  let B₁:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁:0≤B₁:=apply_nonneg _ _
  have hB₂:0≤B₂:=apply_nonneg _ _
  let V:=3+|t|
  let Q:=Cscale*Z^(m+q)
  have hQ:0≤Q:=mul_nonneg hCs (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  let B:=C^2*(B₁*B₂)*Q^2*V^4
  have hB:0≤B:=by dsimp [B]; positivity
  have hpoint (z:O)(hz:r.keep z):‖zeroRow η mask A z t W₁ W₂ X₁ X₂‖≤B:=by
    rw [zero_row_norm η (χ z) mask A z (hrow z hz) W₁ W₂ a b ha hs₁ hs₂
      (W₁.smooth ⊤) (W₂.smooth ⊤) t X₁ X₂ (zero_lt_one.trans_le hX₁) (zero_lt_one.trans_le hX₂)]
    have hb₁:=hpoly W₁ hs₁ (χ z) (hχ z hz) X₁ t hX₁
    have hb₂:=hpoly W₂ hs₂ (χ z) (hχ z hz) X₂ t hX₂
    have h₁:‖polynomial (χ z) false W₁ X₁ 0 t‖≤C*B₁*Q*V^2:=
      hb₁.trans (by dsimp [V]; gcongr; exact hmod z hz)
    have h₂:‖polynomial (χ z) false W₂ X₂ 0 t‖≤C*B₂*Q*V^2:=
      hb₂.trans (by dsimp [V]; gcongr; exact hmod z hz)
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq (by dsimp [B];ring)
  have hb:=radial_bound_on_keep (fun z=>zeroRow η mask A z t W₁ W₂ X₁ X₂) r B hB hpoint
  change zeroEnergy η mask A t W₁ W₂ X₁ X₂ r≤_ at hb
  rw [hscale,max_eq_right (Real.one_le_rpow hZ hm)] at hb
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hp:Z^m*(Z^(m+q))^4≤Z^(m+q+4*ρ):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  have hd:=diagonalControl_nonneg r.profile
  apply hb.trans
  calc
    _=(C^4*Cscale^4*diagonalControl r.profile*(B₁*B₂)^2*V^8)*(Z^m*(Z^(m+q))^4):=by
      dsimp [B,Q]; ring
    _≤_:=mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentPlainGlobalEnergy

end

end OAI
end OAIOriginalModule2328

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalCoreFloor
Source SHA256: 646f514c99a2e7f89835d34e47fecdf25fa8208ef8fa1e3007d5260c6a0d712e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2329



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentNaturalCoreFloor
open HeckeFamily HeckeRowClosure CenteredMomentCoreFloor CenteredMomentPlainGlobalEnergy
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

 theorem natural_zero_all_lengths_floor (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(η:Character)(Q:Ideal O)(r:Radial)(bΦ:ℝ),0≤bΦ→
      (Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ)→
      (∀z,r.keep z→z≠0)→
      (∀z,r.keep z→¬FixedInducingRow η Q fixedBadMask 1 z)→
    ∀(Z m q ρ t X₁ X₂:ℝ),1≤Z→0≤m→0≤q→
      r.scale=Z^m→m+q≤ρ→1≤X₁→1≤X₂→
      (η.modulus.absNorm:ℝ)≤Z^q→
    zeroEnergy η fixedBadMask 1 t W₁ W₂ X₁ X₂ r≤
      C*bΦ^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(3+|t|)^8*Z^(m+q+4*ρ):=by
  obtain ⟨S,C,hC,hfloor⟩:=zero_all_lengths_floor a b ha
  let F:ℝ:=fixedConductorFactor
  have hF:0<F:=by
    unfold F fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨S,C*F^4,mul_pos hC (pow_pos hF _),?_⟩
  intro W₁ W₂ hs₁ hs₂ η Q r bΦ hbΦ hΦsupp hz hex Z m q ρ t X₁ X₂ hZ hm hq hscale hwidth hX₁ hX₂ hη
  let r':Radial:={r with keep:=fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  let χ:O→Character:=fun z=>if hz:z≠0 then (naturalRow η z hz).character else η
  have hrow (z:O)(h:r'.keep z):∀n,elementCoeff (χ z) n=
      CanonicalRowCompletion.rowTwist (elementHom η) fixedBadMask 1 (1*z) n:=by
    have hz0:=hz z h.1
    simpa only [χ,dite_eq_left hz0,one_mul] using (naturalRow η z hz0).element
  have hnon (z:O)(h:r'.keep z):(χ z).residue≠1:=
    CenteredMomentNonprincipalGate.actual_row_nonprincipal η (χ z) Q fixedBadMask 1 z
      (hrow z h) (hex z h.1)
  have hmod (z:O)(h:r'.keep z):((χ z).modulus.absNorm:ℝ)≤(F*bΦ)*Z^(m+q):=by
    have hz0:=hz z h.1
    have hs:‖eisEmbedding z‖^2/r.scale≤bΦ:=hΦsupp h.2
    have hn:((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m:=by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      rw [←hscale]
      exact (div_le_iff₀ r.scale_pos).mp hs
    have hh:=(naturalRow η z hz0).modulus_power_bound Z q m bΦ
      (zero_lt_one.trans_le hZ) hbΦ hη hn
    simpa only [χ,dite_eq_left hz0,add_comm q m] using hh
  have he:=hfloor W₁ W₂ hs₁ hs₂ η fixedBadMask 1 r' χ hnon hrow
    Z m q ρ (F*bΦ) t X₁ X₂ hZ hm hq (mul_nonneg hF.le hbΦ) hscale hwidth hX₁ hX₂ hmod
  have heq:zeroEnergy η fixedBadMask 1 t W₁ W₂ X₁ X₂ r=
      zeroEnergy η fixedBadMask 1 t W₁ W₂ X₁ X₂ r':=by
    unfold zeroEnergy
    apply tsum_congr
    intro z
    by_cases hk:r.keep z
    · by_cases hp:r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · simp [r',hk,hp]
    · simp [r',hk]
  rw [heq]
  exact he.trans_eq (by dsimp [r'];ring)

end SevenEighths.CenteredMomentNaturalCoreFloor

end

end OAI
end OAIOriginalModule2329

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PlainPositiveScale
Source SHA256: b0d5a465a1920466257c365f7a8a2f66051b8fbd9d1ee224fc2be9d0cf5b88d9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2330


namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentPlainPositiveScale
open HeckeFamily HeckeDyadic CenteredMomentPlainGlobalActual CenteredMomentPlainGlobalEnergy
open CenteredMomentHeckeTwist CenteredMomentDetectorDictionary

 theorem small_polynomial (χ:Character)(W:SchwartzMap ℝ ℂ)(a b:ℝ)(ha:0<a)
    (hWs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)(D freq:ℝ)(hD:0<D)(hD1:D≤1):
    ‖polynomial χ false W D 0 freq‖≤
      (128*max 0 b)*(SchwartzMap.seminorm ℝ 0 0 W):=by
  let B:=SchwartzMap.seminorm ℝ 0 0 W
  have hB:0≤B:=apply_nonneg _ _
  have hWs':Function.support (W:ℝ→ℂ)⊆Set.Icc a (max 0 b):=by
    intro x hx
    exact ⟨(hWs hx).1,(hWs hx).2.trans (le_max_right _ _)⟩
  have hs:=twistedIdealSum_absolute χ W a (max 0 b) B ha (le_max_left _ _) hB hWs' (W.smooth ⊤)
    (fun x=>SchwartzMap.norm_le_seminorm ℝ W x) freq D hD
  rw [←plain_height_norm χ W a b ha hWs (W.smooth ⊤) freq D hD,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
  have hsq:(Real.sqrt D)^2=D:=Real.sq_sqrt hD.le
  have hroot:0<Real.sqrt D:=Real.sqrt_pos.mpr hD
  have hle:Real.sqrt D≤1:=by exact (Real.sqrt_le_one).mpr hD1
  have he:(Real.sqrt D)⁻¹*((128*max 0 b*B)*D)=(128*max 0 b*B)*Real.sqrt D:=by
    calc
      _=(128*max 0 b*B)*((Real.sqrt D)⁻¹*(Real.sqrt D*Real.sqrt D)):=by rw [←pow_two,hsq];ring
      _=_:=by rw [inv_mul_cancel_left₀ hroot.ne']
  rw [he]
  exact mul_le_of_le_one_right (by positivity) hle

 theorem global_positive_scale (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀W:SchwartzMap ℝ ℂ,Function.support (W:ℝ→ℂ)⊆Set.Icc a b→
    ∀χ:Character,χ.residue≠1→∀D freq:ℝ,0<D→
      ‖polynomial χ false W D 0 freq‖≤
        C*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (χ.modulus.absNorm:ℝ)*(3+|freq|)^2:=by
  obtain ⟨S,C,hC,hg⟩:=global_polynomial_bound a b ha
  let S':Finset (ℕ×ℕ):=insert (0,0) S
  let C':ℝ:=C+128*max 0 b
  have hC':0<C':=add_pos_of_pos_of_nonneg hC (by positivity)
  refine ⟨S',C',hC',?_⟩
  intro W hWs χ hχ D freq hD
  have hB:0≤S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=apply_nonneg _ _
  have hsup:S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) W
  have hzero:SchwartzMap.seminorm ℝ 0 0 W≤S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=
    Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) (s:=S') (i:=(0,0)) (x:=W) (Finset.mem_insert_self (0,0) S)
  have hQ:1≤(χ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hV:1≤(3+|freq|)^2:=one_le_pow₀ (by linarith [abs_nonneg freq])
  by_cases hD1:1≤D
  · apply (hg W hWs χ hχ D freq hD1).trans
    gcongr
    dsimp [C']; linarith [le_max_left (0:ℝ) b]
  · have hh:=small_polynomial χ W a b ha hWs D freq hD (le_of_lt (lt_of_not_ge hD1))
    apply hh.trans
    calc
      _≤C'*(S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W):=by
        apply mul_le_mul _ hzero (apply_nonneg _ _) hC'.le
        dsimp [C'];linarith
      _≤(C'*(S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W))*
          ((χ.modulus.absNorm:ℝ)*(3+|freq|)^2):=
        le_mul_of_one_le_right (mul_nonneg hC'.le hB) (one_le_mul_of_one_le_of_one_le hQ hV)
      _=_:=by ring

end SevenEighths.CenteredMomentPlainPositiveScale

end

end OAI
end OAIOriginalModule2330

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PlainPositiveEnergy
Source SHA256: bd057b382981779d05ae9a6164efeae620e7672e9965c9eb7bab2ef0c72c9189
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2331



namespace OAI

noncomputable section
open scoped Classical SchwartzMap BigOperators
namespace SevenEighths.CenteredMomentPlainPositiveEnergy
open HeckeFamily HeckeDyadic CenteredMomentPlainPositiveScale CenteredMomentPlainGlobalEnergy
open CenteredMomentOriginalRadialComparison
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound ConcreteTraceCRT
local notation "O"=>HeckeFamily.O

 theorem actual_radial_pair_bound (a b:ℝ)(ha:0<a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(χ:O→Character)(r:Radial)(R X₁ X₂ freq₁ freq₂:ℝ),0≤R→0<X₁→0<X₂→
      (∀z,r.keep z→(χ z).residue≠1)→
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤R)→
    radialEnergy (fun z=>polynomial (χ z) false W₁ X₁ 0 freq₁*
      polynomial (χ z) false W₂ X₂ 0 freq₂) r.keep r.profile r.scale≤
      C*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*R^4*
        (3+|freq₁|)^4*(3+|freq₂|)^4:=by
  obtain ⟨S,C,hC,hg⟩:=global_positive_scale a b ha
  refine ⟨S,C^4,pow_pos hC _,?_⟩
  intro W₁ W₂ hs₁ hs₂ χ r R X₁ X₂ freq₁ freq₂ hR hX₁ hX₂ hχ hmod
  let B₁:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁:0≤B₁:=apply_nonneg _ _
  have hB₂:0≤B₂:=apply_nonneg _ _
  let B:=C^2*(B₁*B₂)*R^2*(3+|freq₁|)^2*(3+|freq₂|)^2
  have hB:0≤B:=by dsimp [B];positivity
  have hp (z:O)(hz:r.keep z):
      ‖polynomial (χ z) false W₁ X₁ 0 freq₁*polynomial (χ z) false W₂ X₂ 0 freq₂‖≤B:=by
    rw [norm_mul]
    have h₁:‖polynomial (χ z) false W₁ X₁ 0 freq₁‖≤C*B₁*R*(3+|freq₁|)^2:=
      (hg W₁ hs₁ (χ z) (hχ z hz) X₁ freq₁ hX₁).trans (by gcongr;exact hmod z hz)
    have h₂:‖polynomial (χ z) false W₂ X₂ 0 freq₂‖≤C*B₂*R*(3+|freq₂|)^2:=
      (hg W₂ hs₂ (χ z) (hχ z hz) X₂ freq₂ hX₂).trans (by gcongr;exact hmod z hz)
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq (by dsimp [B];ring)
  have hh:=radial_bound_on_keep _ r B hB hp
  exact hh.trans_eq (by dsimp [B];ring)

end SevenEighths.CenteredMomentPlainPositiveEnergy

end

end OAI
end OAIOriginalModule2331

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectedSource
Source SHA256: 81e1c25f49295e0a58465642f1bf73c115b06eff3dc83210dee5639b64dd983f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2332






namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentReflectedSource
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CanonicalUnitEuler
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonLinearSource CenteredMomentCommonPairedSource
open CenteredMomentFirstSectors CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondHeightFamily CenteredMomentSourceRow
local notation "O" => HeckeFamily.O
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def reflected (η:Character):Character:=η.product (HeckeUnitRows.character (-1:Oˣ))

theorem unit_ideal (I:Ideal O)(hI:Supported I):
    idealCoeff (HeckeUnitRows.character (-1:Oˣ)) I=idealRowHom (-1) I:=by
  rw [←ConcretePrimeRowBridge.span_idealGenerator I,
    idealCoeff_span _ (ConcretePrimeRowBridge.idealGenerator_ne_zero I hI.1),
    HeckeUnitRows.elementCoeff_character]
  change (if Supported (Ideal.span {ConcretePrimeRowBridge.idealGenerator I}) then _ else 0)=_
  rw [ConcretePrimeRowBridge.span_idealGenerator,ite_eq_left hI]
  rfl

theorem reflected_height (η:Character)(t:ℝ)(I:Ideal O)(hI:Supported I):
    heightCoeff (reflected η) t I=heightCoeff η t I*idealRowHom (-1) I:=by
  rw [heightCoeff,reflected,idealCoeff_product,unit_ideal I hI,heightCoeff]
  ring

theorem polynomial_neg {α:Type*}(S:Finset α)(a:α→O)
    (ha:∀i,Supported (Ideal.span {a i}))(c:α→ℂ)(η:Character)(t:ℝ)(z:O):
    rowPolynomial S a (fun i=>c i*heightCoeff η t (Ideal.span {a i})) (-z)=
      rowPolynomial S a (fun i=>c i*heightCoeff (reflected η) t (Ideal.span {a i})) z:=by
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only
  rw [reflected_height η t _ (ha i),show -z=(-1)*z by ring,idealRowHom_argument_mul]
  ring

theorem sourceColumn_neg {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):
    sourceColumn s C hC R seed L (-z)=
      sourceColumn (withHeight s (reflected s.η) s.t) C hC R seed L z:=by
  let Q:=residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))
  let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  have h:=polynomial_neg Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then β (C*I) else 0)
    s.η s.t z
  have hspan (I:supportedColumns Q):Ideal.span {sourceGenerator Q I}=(I:Ideal O):=
    primary_span_supported I (Finset.mem_filter.mp I.property).2
  simp only [hspan] at h
  dsimp only [sourceColumn, withHeight, Input.pools, Q, β] at h ⊢
  convert h using 1
  rfl

theorem normalizedColumn_neg {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(z:O):
    normalizedColumn s C hC R seed L (-z)=
      normalizedColumn (withHeight s (reflected s.η) s.t) C hC R seed L z:=by
  unfold normalizedColumn
  rw [sourceColumn_neg]
  simp only [withHeight,CenteredMomentExceptionalAmplitudePair.volume]

theorem reflected_row (η:Character)(m A z n:O)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m):
    rowTwist (HeckeRowClosure.elementHom η) m 1 (A*(-z)) n=
      rowTwist (HeckeRowClosure.elementHom (reflected η)) m 1 (A*z) n:=by
  by_cases hn:Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask _ m 1 _ n hn,rowTwist_extract_sixth_mask _ m 1 _ n hn]
    simp only [one_pow,one_mul]
    change elementCoeff η n*coprimalityMask m n*idealRowHom (A*(-z)) (Ideal.span {n})=
      elementCoeff (reflected η) n*coprimalityMask m n*idealRowHom (A*z) (Ideal.span {n})
    rw [reflected,elementCoeff_product,HeckeUnitRows.elementCoeff_character]
    have hu:unitSupplement (-1:Oˣ) n=idealRowHom (-1) (Ideal.span {n}):=by
      change (if Supported (Ideal.span {n}) then idealRowHom (-1) (Ideal.span {n}) else 0)=_
      rw [ite_eq_left hn]
    rw [hu,show A*(-z)=(-1)*(A*z) by ring,idealRowHom_argument_mul]
    ring
  · rw [CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn,
      CanonicalRowCompletion.rowTwist_zero_of_not_supported _ _ _ _ _ hmLam hm2 hn]

theorem reflected_inducing (η:Character)(Q:Ideal O)(m A z:O)
    (hmLam:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m):
    CenteredExceptionalProfile.FixedInducingRow η Q m A (-z) ↔
      CenteredExceptionalProfile.FixedInducingRow (reflected η) Q m A z:=by
  unfold CenteredExceptionalProfile.FixedInducingRow
  simp_rw [←reflected_row η m A z _ hmLam hm2]

end SevenEighths.CenteredMomentReflectedSource

end

end OAI
end OAIOriginalModule2332

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonSectorWindow
Source SHA256: db5f358caeb851c8cf8c5179359a0f1e6cf1828be4c6add1c1e222ad3ac59eb6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2333





namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonSectorWindow
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentSecondMaskedWindow CenteredMomentSecondSectorEnergy CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentExceptionalWholeWindow CenteredMomentSmooth CenteredMomentSecondWindowSource
open RayFourExpansion CenteredMomentLogDyadic
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [DecidableEq ι] in
theorem actual_sector_window (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t θ X:ℝ)(V:ℝ→ℂ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
        columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z=
      windowColumn s C hC R seed L τ t θ X V z:=by
  dsimp only
  simp_rw [masked_divisor_coefficient η τ χ A C hC hτ]
  rw [sector_rowPolynomial _ (fun I=>(if L∣I then finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)*
      heightCoeff τ t I*columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ) C hC z]
  unfold windowColumn
  rw [←rowPolynomial_factor]
  apply congrArg (fun c=>rowPolynomial Finset.univ (sourceGenerator (columns s C hC)) c z)
  funext I
  dsimp only [coefficient]
  split_ifs <;> simp_all ; ring

omit [DecidableEq ι] in
theorem window_neg (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t θ X:ℝ)(V:ℝ→ℂ)(z:O):
    windowColumn s C hC R seed L η t θ X V (-z)=
      windowColumn s C hC R seed L (reflected η) t θ X V z:=by
  unfold windowColumn rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  dsimp only
  rw [reflected_height η t I (Finset.mem_filter.mp I.property).2,
    show -z=(-1)*z by ring,idealRowHom_argument_mul,sourceGenerator_span]
  ring

omit [DecidableEq ι] in
theorem actual_reflected_sector_window (s:Input ι)(η τ:Character)(χ:RayCharacter)(A:O)
    (C:Ideal O)(hC:Supported C)(R seed L:Ideal O)(t θ X:ℝ)(z:O)
    (hτ:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
    rowPolynomial Finset.univ (sectorElement C hC.1 S)
      (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
        star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ)) (-z)=
      windowColumn s C hC R seed L (reflected τ) t (-θ) X logAnnulus z:=by
  dsimp only
  simp only [star_logAnnulus_column]
  rw [actual_sector_window s η τ χ A C hC R seed L t (-θ) X logAnnulus (-z) hτ,window_neg]

end SevenEighths.CenteredMomentCommonSectorWindow

end

end OAI
end OAIOriginalModule2333

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalAggregate
Source SHA256: fb64ba47415fddfed73269beb1c039a688847fc4a2f29becdbf641f633044abc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2334




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondExceptionalAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass CenteredMomentSecondBlockRadicalHarmonicMass
open CenteredMomentFirstSectors CenteredMomentSourceRow RayFourExpansion
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma live_radical_sum_le (η:Character)(S:Finset (Ideal O))(β:Ideal O→ℂ)(K R H:ℝ):
    (∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
      ∑_n:SourceBlocks p.val.1 p.val.2 U K R H,radicalWeight p.val.1 p.val.2)≤
    ∑q:ActiveBlocks S β K R H,radicalWeight q.1.1.val.1 q.1.1.val.2:=by
  rw [CenteredMomentSecondBlockRadicalHarmonicMass.active_blocks_sum_eq]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun p _ _=>Finset.sum_nonneg (fun U _=>mul_nonneg (Nat.cast_nonneg _) (radicalWeight_nonneg _ _)))

theorem part_energy_radical_bound (exceptional:Bool)(η:Character)(χ:RayCharacter)
    (Q:Ideal O)(m:O)(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))
    (K Tsec Z ξ H V E:ℝ)(hV:0<V)(hE:0≤E)
    (hb:∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*radicalWeight p.val.1 p.val.2):
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤
      E*(∑q:ActiveBlocks S β K (frequencyRadius Tsec Z ξ) H,
        radicalWeight q.1.1.val.1 q.1.1.val.2):=by
  apply (div_le_div_of_nonneg_right
    (partEnergy_norm_le exceptional η χ Q m t S β W K Tsec Z ξ H) hV.le).trans
  simp only [Finset.sum_div]
  calc
    _≤∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          E*radicalWeight p.val.1 p.val.2:=by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro U hU
      apply Finset.sum_le_sum
      intro n hn
      exact hb p hp U n
    _=E*(∑p∈liveLabels η S β,∑U:Finset (CommonIndex p.val.1 p.val.2),
        ∑_n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
          radicalWeight p.val.1 p.val.2):=by simp only [Finset.mul_sum]
    _≤_:=mul_le_mul_of_nonneg_left (live_radical_sum_le η S β K (frequencyRadius Tsec Z ξ) H) hE

theorem source_part_radical_bound (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)
    (hCr:0<Cr)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
    ∀(seed:Ideal O),Squarefree seed → seed≠0 →
    ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
    (∀I∈S,β I≠0→seed∣I) → (∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B) →
    ∀(exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)(W:𝓢(ℝ,ℂ))
      (K Tsec ξ H V E:ℝ),0<K → frequencyRadius Tsec Z ξ≤Cr*Z^L → H≤Z^B → 0<V → 0≤E →
    (∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*radicalWeight p.val.1 p.val.2) →
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤E*(C*Z^ε/(seed.absNorm:ℝ)):=by
  obtain ⟨C,hC,hmass⟩:=actual_block_radical_mass B L Cr ε hB hL hCr hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hmass] with Z hZ
  intro seed hs hs0 S β hmask hnorm exceptional η χ Q m t W K Tsec ξ H V E hK hR hH hV hE hb
  exact (part_energy_radical_bound exceptional η χ Q m t S β W K Tsec Z ξ H V E hV hE hb).trans
    (mul_le_mul_of_nonneg_left (hZ seed hs hs0 S β hmask hnorm K
      (frequencyRadius Tsec Z ξ) H hK hR hH) hE)

end SevenEighths.CenteredMomentSecondExceptionalAggregate

end

end OAI
end OAIOriginalModule2334

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
Source SHA256: 125db37041979feb43ef85e1b111faa4ab0dbb387e5d33380106d203c5b8af7e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2335





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentPartitionNorm
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget CenteredMomentSecondRetainedWidth
open CenteredMomentSecondSixthReduction CenteredMomentSecondSixthSource CenteredMomentSecondRadicalColumns
open CenteredMomentSecondReducedPredicate CenteredMomentSecondLiveBlock CenteredMomentSecondBlockSupport
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentRestrictedEnergy CenteredMomentSectorLocalization RayFourExpansion
open CenteredExceptionalProfile CenteredMomentReflectedSource
local notation "O" => HeckeFamily.O

theorem span_thirty_six_norm : (Ideal.span {(36:O)}).absNorm=1296 := by
  have h := ActualEisensteinCubic.rational_modulus_card 36 (by norm_num)
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
  exact h

theorem reflected_modulus_bound (τ:Character) :
    (reflected τ).modulus.absNorm≤1296*τ.modulus.absNorm := by
  have h := HeckePrimeScale.product_modulus_bound τ (HeckeUnitRows.character (-1:Oˣ))
  change (reflected τ).modulus.absNorm≤τ.modulus.absNorm*(Ideal.span {(36:O)}).absNorm at h
  simpa only [span_thirty_six_norm,mul_comm] using h

theorem common_subproduct_dvd_left (C D:Ideal O) (hC:Supported C)
    (hCD:primeSupport C=primeSupport D) (S:Finset (CommonIndex C D)) :
    (∏P∈S,P.val)∣C := by
  have h₁ := Finset.prod_dvd_prod_of_subset S Finset.univ
    (fun P:CommonIndex C D=>P.val) (Finset.subset_univ S)
  have h₂ : (∏P:CommonIndex C D,P.val)∣
      ∏P:CommonIndex C D,Ideal.span {commonPrime C D P}^leftExponent C D P := by
    apply Finset.prod_dvd_prod_of_dvd
    intro P _
    rw [commonPrime_span C D hC]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt (leftExponent_pos C D P))
  rw [left_ideal_product C D hC hCD] at h₂
  exact h₁.trans h₂

theorem common_subproduct_dvd_right (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (S:Finset (CommonIndex C D)) :
    (∏P∈S,P.val)∣D := by
  have h₁ := Finset.prod_dvd_prod_of_subset S Finset.univ
    (fun P:CommonIndex C D=>P.val) (Finset.subset_univ S)
  have h₂ : (∏P:CommonIndex C D,P.val)∣
      ∏P:CommonIndex C D,Ideal.span {commonPrime C D P}^rightExponent C D P := by
    apply Finset.prod_dvd_prod_of_dvd
    intro P _
    rw [commonPrime_span C D hC]
    exact dvd_pow_self _ (Nat.ne_zero_of_lt (rightExponent_pos C D P))
  rw [right_ideal_product C D hC hD hCD] at h₂
  exact h₁.trans h₂

theorem selected_nonunit_product (C D:Ideal O) (hC:Supported C)
    (U:Finset (CommonIndex C D)) :
    (∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}=
      ∏P∈U∪nonunitPartitionSet C D U,P.val := by
  have hd : Disjoint U (nonunitPartitionSet C D U) := by
    apply Finset.disjoint_left.mpr
    intro P hP hV
    exact (Finset.mem_sdiff.mp hV).2 hP
  rw [Finset.prod_union hd,nonunitFrequencyGenerator_span]
  simp only [unitIdeal,commonPrime_span C D hC]

theorem selected_nonunit_dvd (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D)) :
    ((∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}∣C) ∧
    ((∏P∈U,P.val)*Ideal.span {nonunitFrequencyGenerator C D U}∣D) := by
  rw [selected_nonunit_product C D hC]
  exact ⟨common_subproduct_dvd_left C D hC hCD _,
    common_subproduct_dvd_right C D hC hD hCD _⟩

theorem selected_nonunit_norm (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (hCD:primeSupport C=primeSupport D) (U:Finset (CommonIndex C D)) :
    (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm≤C.absNorm ∧
    (∏P∈U,P.val).absNorm*(Ideal.span {nonunitFrequencyGenerator C D U}).absNorm≤D.absNorm := by
  obtain ⟨h₁,h₂⟩ := selected_nonunit_dvd C D hC hD hCD U
  constructor
  · simpa only [map_mul] using Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)) (map_dvd Ideal.absNorm h₁)
  · simpa only [map_mul] using Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)) (map_dvd Ideal.absNorm h₂)

structure Family (η:Character) (C D:Ideal O) (hC:Supported C) (hD:Supported D)
    (U:Finset (CommonIndex C D)) (τ:RayCharacter→Character) : Prop where
  element_eq : ∀χ n,elementCoeff (τ χ) n=
    rowTwist (HeckeRowClosure.elementHom (childCharacter η χ))
      fixedBadMask 1 (reducedNumerator C D U) n
  height_eq : ∀χ I,Supported I→(IsCoprime C I ∨ IsCoprime D I)→∀t,
    heightCoeff (τ χ) t I=heightCoeff η t I*
      idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
      rayCharacter χ (primaryGenerator I)
  physical_budget : ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U R rows W K n≠0→∀χ,
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm ∧
    ∀Z:ℝ,1<Z→∀z∈liveRows C D U R rows,
      Real.logb Z (normValue z)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
        Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (4*(fixedFactor:ℝ))

theorem exists_exceptional_family (η:Character) (C D:Ideal O)
    (hC:Supported C) (hD:Supported D) (hCD:primeSupport C=primeSupport D)
    (U:Finset (CommonIndex C D)) : ∃τ,Family η C D hC hD U τ := by
  choose τ he ht hrest using fun χ:RayCharacter=>exists_retained_width_family η χ C D hC U
  refine ⟨τ,he,?_,?_⟩
  · intro χ I hI hi t
    rw [ht χ I hI t]
    rcases hi with hi|hi
    · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
    · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]
  · intro t S β R rows W K hK n hne χ
    have hne':physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n≠0:=by
      rwa [←physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
    obtain ⟨w,_,hwc⟩:=physicalBlock_nonzero_common η t S β C D hC hD hCD U R
      (liveRows C D U R rows) (fun z hz=>(liveRows_geometry C D U R rows z hz).2.1)
      W K hK n hne'
    obtain ⟨hN,hwidth⟩:=hrest χ hD hCD (nonunitFrequencyGenerator C D U*w) hwc
    refine ⟨hN,?_⟩
    intro Z hZ z hz
    exact (hwidth Z R hZ z (liveRows_weight C D U R rows z hz)).2.2.2.2.2

namespace Family
variable {η:Character} {C D:Ideal O} {hC:Supported C} {hD:Supported D}
  {U:Finset (CommonIndex C D)} {τ:RayCharacter→Character}

theorem nonexceptional_iff (h:Family η C D hC hD U τ) (χ:RayCharacter)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    nonexceptional η χ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      z≠0 ∧ ¬FixedInducingRow (τ χ) Q fixedBadMask 1 z :=
  actual_nonexceptional_iff η (τ χ) χ C D hC U (h.element_eq χ) Q m z hm hml hm2

theorem inducing_iff (h:Family η C D hC hD U τ) (χ:RayCharacter)
    (Q:Ideal O) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z ↔
      FixedInducingRow (τ χ) Q fixedBadMask 1 z :=
  actual_reduced_inducing_iff η (τ χ) χ C D hC U (h.element_eq χ) Q m z hm hz hml hm2

theorem paired_inducing_iff (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O) (hQ:Q≤Ideal.span {(72:O)}) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ↔
      FixedInducingRow (τ ξ) Q fixedBadMask 1 (-z) :=
  (h.inducing_iff χ Q m z hm hz hml hm2).symm.trans
    ((CenteredMomentExceptionalReflection.fixedInducingRow_reflection_iff η χ ξ Q hQ m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z hml hm2).trans
      (h.inducing_iff ξ Q m (-z) hm (neg_ne_zero.mpr hz) hml hm2))

theorem both_inducing (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O) (hQ:Q≤Ideal.span {(72:O)}) (m z:O) (hm:m≠0) (hz:z≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m) (hm2:(2:O)∣m)
    (hex:FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) :
    FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (reflected (τ ξ)) Q fixedBadMask 1 z := by
  have hleft := (h.inducing_iff χ Q m z hm hz hml hm2).mp hex
  refine ⟨hleft,?_⟩
  exact (reflected_inducing (τ ξ) Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp
    ((h.paired_inducing_iff χ ξ Q hQ m z hm hz hml hm2).mp hleft)

theorem reflected_height_eq (h:Family η C D hC hD U τ) (ξ:RayCharacter)
    (I:Ideal O)(hI:Supported I)(hi:IsCoprime C I ∨ IsCoprime D I)(t:ℝ) :
    heightCoeff (reflected (τ ξ)) t I=heightCoeff η t I*
      idealRowHom (-(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) I*
      rayCharacter ξ (primaryGenerator I) := by
  have hneg : idealRowHom (-(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)) I=
      idealRowHom (-1) I*idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I := by
    rw [show -(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U)=
      (-1)*(commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) by ring]
    exact idealRowHom_argument_mul _ _ _
  rw [reflected_height _ _ _ hI,h.height_eq ξ I hI hi t,hneg]
  ring

theorem live_both_inducing (h:Family η C D hC hD U τ) (χ ξ:RayCharacter)
    (Q:Ideal O)(hQ:Q≤Ideal.span {(72:O)})(m z:O)(hm:m≠0)
    (hml:ConcretePrimeRowBridge.goodLambda∣m)(hm2:(2:O)∣m)
    (radius:ℝ)(rows:Finset O)(hz:z∈liveRows C D U radius rows)
    (hex:FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) :
    z≠0 ∧ FixedInducingRow (τ χ) Q fixedBadMask 1 z ∧
      FixedInducingRow (reflected (τ ξ)) Q fixedBadMask 1 z := by
  have hz0 := (liveRows_geometry C D U radius rows z hz).2.1
  exact ⟨hz0,h.both_inducing χ ξ Q hQ m z hm hz0 hml hm2 hex⟩

theorem physical_conductor_bounds (h:Family η C D hC hD U τ)
    (hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)(χ:RayCharacter) :
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*C.absNorm ∧
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*D.absNorm := by
  have hN := (h.physical_budget t S β R rows W K hK n hne χ).1
  obtain ⟨h₁,h₂⟩ := selected_nonunit_norm C D hC hD hCD U
  constructor
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₁)
  · exact hN.trans <| by
      simpa only [mul_assoc] using (Nat.mul_le_mul_left (η.modulus.absNorm*fixedFactor) h₂)

end Family

def expandedConductor (τ:Character)(R C:Ideal O)(z:O):ℕ :=
  τ.modulus.absNorm*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm

def expandedFactor (η:Character):ℕ :=
  1296*η.modulus.absNorm*fixedFactor*(Ideal.span {fixedBadMask}).absNorm*
    (Ideal.span {(72:O)}).absNorm

theorem expanded_conductor_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O) :
    expandedConductor (τ χ) R C z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm ∧
    expandedConductor (reflected (τ ξ)) R D z≤
      expandedFactor η*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm := by
  have hl := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne χ).2
  have hr := (h.physical_conductor_bounds hCD t S β radius rows W K hK n hne ξ).1
  have hl' : (τ χ).modulus.absNorm≤1296*(η.modulus.absNorm*fixedFactor*D.absNorm) := by
    exact hl.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  have hr' := (reflected_modulus_bound (τ ξ)).trans (Nat.mul_le_mul_left 1296 hr)
  constructor
  · calc
      expandedConductor (τ χ) R C z≤
        (1296*(η.modulus.absNorm*fixedFactor*D.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring
  · calc
      expandedConductor (reflected (τ ξ)) R D z≤
        (1296*(η.modulus.absNorm*fixedFactor*C.absNorm))*
          (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm*
          (R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm := by
            unfold expandedConductor
            gcongr
      _=_ := by unfold expandedFactor;ring

theorem eventually_expanded_conductor_caps (η:Character)(ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(z:O)(c d r m:ℝ),
    (C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→(R.absNorm:ℝ)≤Z^r→normValue z≤Z^m→
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (expandedFactor η:ℝ)
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.1 he
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R z c d r m hCN hDN hRN hzn
  have hZpos : 0<Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have hconstant := hZ₀ Z ((le_max_right _ _).trans hZ)
  have hproduct : (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm≤
      Z^(c+d+r+m+ε) := by
    calc
      _≤Z^ε*Z^r*Z^c*Z^d*Z^m := by
        change (Ideal.absNorm (Ideal.span {z}):ℝ)≤_ at hzn
        gcongr
      _=Z^(c+d+r+m+ε) := by
        rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
        congr 1
        ring
  obtain ⟨hl,hr⟩ := expanded_conductor_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  constructor
  · exact (show (expandedConductor (τ χ) R C z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hl).trans hproduct
  · exact (show (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*(Ideal.span {z}).absNorm by
        exact_mod_cast hr).trans hproduct

theorem live_norm_le_four_radius (C D:Ideal O)(U:Finset (CommonIndex C D))
    (radius:ℝ)(rows:Finset O)(z:O)(hz:z∈liveRows C D U radius rows) :
    normValue z≤4*radius := by
  obtain ⟨hr,hg,hv,_,_,hn,_⟩ := retained_geometry radius
    (commonFrequencyGenerator C D) (nonunitFrequencyGenerator C D U) z
    (liveRows_weight C D U radius rows z hz)
  have hG := normValue_ge_one _ hg
  have hV := normValue_ge_one _ hv
  have hprod : 1≤normValue (commonFrequencyGenerator C D)*normValue (nonunitFrequencyGenerator C D U) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hG) (sub_nonneg.mpr hV)]
  exact hn.trans (div_le_self (by positivity) hprod)

theorem eventually_live_expanded_conductor_caps (η:Character)(ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m:ℝ),
    (C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→(R.absNorm:ℝ)≤Z^r→ radius≤Z^m→
    ∀z∈liveRows C D U radius rows,z≠0 ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+ε) := by
  obtain ⟨Z₁,hZ₁,h₁⟩ := eventually_expanded_conductor_caps η (ε/2) (by positivity)
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<ε/2 by positivity))) (4:ℝ)
  obtain ⟨Z₂,h₂⟩ := Filter.eventually_atTop.1 he
  refine ⟨max Z₁ Z₂,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro Z hZ C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R c d r m hCN hDN hRN hrad z hz
  have hZpos : 0<Z := zero_lt_one.trans (hZ₁.trans_le ((le_max_left _ _).trans hZ))
  have hfour := h₂ Z ((le_max_right _ _).trans hZ)
  have hfreq : normValue z≤Z^(m+ε/2) := by
    calc
      _≤4*radius := live_norm_le_four_radius C D U radius rows z hz
      _≤Z^(ε/2)*Z^m := mul_le_mul hfour hrad
        (liveRows_geometry C D U radius rows z hz).1.le (Real.rpow_nonneg hZpos.le _)
      _=Z^(m+ε/2) := by rw [←Real.rpow_add hZpos,add_comm]
  have hc := h₁ Z ((le_max_left _ _).trans hZ) C D hC hD hCD U τ h t S β radius rows W K hK
    n hne χ ξ R z c d r (m+ε/2) hCN hDN hRN hfreq
  have hexp : c+d+r+(m+ε/2)+ε/2=c+d+r+m+ε := by ring
  rw [hexp] at hc
  exact ⟨(liveRows_geometry C D U radius rows z hz).2.1,hc⟩

end SevenEighths.CenteredMomentSecondExceptionalFamily

end

end OAI
end OAIOriginalModule2335

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondChildRadialWidth
Source SHA256: f77e9340e2f881c350255e3015e88b32a791dc328bd972e23163e7735719f9bb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2336




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentSecondChildRadialWidth
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondDyadicRowSupport CenteredMomentSectorLocalization
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRadicalBudget
open CenteredMomentSecondActualWidth CenteredMomentSecondWidthDrop
local notation "O" => HeckeFamily.O

theorem physicalBlock_live_dyadic_witness (η:Character)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (U:Finset (CommonIndex C D))(R:ℝ)(rows:Finset O)(W:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0) :
    ∃z:O,z∈liveRows C D U R rows ∧ z∈dyadicRows rows n ∧
      z≠0 ∧ dyadicScale (n 1)<4*normValue z := by
  rw [physicalBlock_live_dyadic_rows η t S β C D hC hD U R rows W K n] at hne
  unfold physicalBlock at hne
  obtain ⟨z,hz,_⟩:=Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hl,hd⟩:=(mem_dyadicRows _ n z).mp hz
  have hz':z∈dyadicRows rows n:=(mem_dyadicRows rows n z).mpr
    ⟨(Finset.mem_filter.mp hl).1,hd⟩
  exact ⟨z,hl,hz',dyadicRows_nonzero rows n z hz',by
    have hh:=(dyadicRows_norm rows n z hz').1
    linarith⟩

section Family
variable {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
  {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
  (h:Family η C D hC hD U τ)
  (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
  (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
  (hne:physicalBlock η t S β C D hC hD U R rows W K n≠0)

include h hK hne

theorem dyadic_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter) :
    Real.logb Z (dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*(fixedFactor:ℝ)) := by
  obtain ⟨z,hzl,_,hz0,hscale⟩:=physicalBlock_live_dyadic_witness η t S β C D hC hD U R rows W K n hne
  have hw:=(h.physical_budget t S β R rows W K hK n hne χ).2 Z hZ z hzl
  have hh:=Real.logb_le_logb_of_le hZ (dyadicScale_pos (n 1)) hscale.le
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) (normValue_pos z hz0).ne'] at hh
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*(fixedFactor:ℝ))=
      Real.logb Z (4:ℝ)+Real.logb Z (4*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul (by norm_num : (4:ℝ)≠0) (by positivity : 4*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

omit h hK hne in

theorem radial_support_bound (Φ:ℝ→ℂ)(b:ℝ)
    (hs:Function.support Φ⊆Set.Iic b)(y:O)
    (hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y≤b*dyadicScale (n 1) :=
  (div_le_iff₀ (dyadicScale_pos (n 1))).mp (hs hy)

theorem radial_radius_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hh:=dyadic_log_budget h t S β R rows W K hK n hne Z hZ χ
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*(fixedFactor:ℝ))=
      Real.logb Z b+Real.logb Z (16*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hb.ne' (by positivity : 16*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [Real.logb_mul hb.ne' (dyadicScale_pos (n 1)).ne',hf]
  linarith

theorem radial_point_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (normValue y)+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hl:=Real.logb_le_logb_of_le hZ (normValue_pos y hy0)
    (radial_support_bound n Φ b hs y hy)
  have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb
  linarith

theorem declared_radial_log_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  exact radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb

theorem whole_radial_norm_budget (Z:ℝ)(hZ:1<Z)(χ:RayCharacter)
    (Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+Real.logb Z (16*b*(fixedFactor:ℝ))) := by
  have hτ:(0:ℝ)<(τ χ).modulus.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (τ χ).modulus_ne_bot)
  have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ χ b hb
  rw [←Real.logb_mul (mul_pos hb (dyadicScale_pos (n 1))).ne' hτ.ne'] at hh
  exact (mul_le_mul_of_nonneg_right (radial_support_bound n Φ b hs y hy) hτ.le).trans
    ((Real.logb_le_iff_le_rpow hZ (mul_pos (mul_pos hb (dyadicScale_pos (n 1))) hτ)).mp hh)

end Family

theorem fixed_radial_cost_eventually (b ε:ℝ)(hb:0<b)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→Real.logb Z (16*b*(fixedFactor:ℝ))≤ε := by
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (16*b*(fixedFactor:ℝ))
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (he.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ
  obtain ⟨hc,hZ1⟩:=hZ₀ Z ((le_max_right _ _).trans hZ)
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  exact (Real.logb_le_iff_le_rpow hZ1 (by positivity)).mpr hc

theorem eventually_whole_radial_width (b ε:ℝ)(hb:0<b)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→
    ∀(η:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
      (U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(R:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U R rows W K n≠0→
    ∀(χ:RayCharacter)(Φ:ℝ→ℂ),Function.support Φ⊆Set.Iic b→
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
        Real.logb Z (normValue (commonFrequencyGenerator C D))+
        Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε ∧
    ∀y:O,Φ (normValue y/dyadicScale (n 1))≠0→
      normValue y*((τ χ).modulus.absNorm:ℝ)≤
        Z^(Real.logb Z R+Real.logb Z (η.modulus.absNorm:ℝ)-
          Real.logb Z (normValue (commonFrequencyGenerator C D))+
          Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ε) := by
  obtain ⟨Z₀,hZ₀,hcost⟩:=fixed_radial_cost_eventually b ε hb hε
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ η C D hC hD U τ h t S β R rows W K hK n hne χ Φ hs
  have hZ1:=hZ₀.trans_le hZ
  have hc:=hcost Z hZ
  constructor
  · have hh:=radial_radius_log_budget h t S β R rows W K hK n hne Z hZ1 χ b hb
    linarith
  · intro y hy
    exact (whole_radial_norm_budget h t S β R rows W K hK n hne Z hZ1 χ Φ b hb hs y hy).trans
      (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))

theorem physical_declared_radial_width_drop {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H K Tsec Csec ξ M σ g:ℝ)(hZ:1<Z)(hH:0<H)(hK:0<K)
    (hT:0<Tsec)(hCs:0<Csec)
    (hg:amplificationIncrement η Z H K M σ≤g)
    (hscale:Tsec≤Csec*(H^2/(K*Z^g))) (n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ)
      rows W (K*Z^g) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      M-σ+ξ/2+Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hKg:0<K*Z^g:=mul_pos hK (Real.rpow_pos_of_pos hz _)
  have hw:=declared_radial_log_budget h t S β (frequencyRadius Tsec Z ξ) rows W
    (K*Z^g) hKg n hne Z hZ χ Φ b hb hs y hy0 hy
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hn:nominalLength Z H K g+Real.logb Z (η.modulus.absNorm:ℝ)≤M-σ := by
    have hnom:=actual_nominal_drop η Z H K M σ
    unfold nominalLength at hnom ⊢
    linarith
  rw [physical_frequency_scale Z H K g hZ hH hK] at hscale
  have hl:=Real.logb_le_logb_of_le hZ hT hscale
  rw [Real.logb_mul hCs.ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.logb_rpow hz hZ.ne'] at hl
  have hr:Real.logb Z (frequencyRadius Tsec Z ξ)≤
      nominalLength Z H K g+ξ/2+Real.logb Z Csec := by
    rw [frequencyRadius,Real.logb_mul hT.ne' (Real.rpow_pos_of_pos hz _).ne',
      Real.logb_rpow hz hZ.ne']
    linarith
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*Csec*(fixedFactor:ℝ))=
      Real.logb Z Csec+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hCs.ne' (by positivity : 16*b*(fixedFactor:ℝ)≠0)]
    congr 1
    ring
  rw [hf]
  linarith

end SevenEighths.CenteredMomentSecondChildRadialWidth

end

end OAI
end OAIOriginalModule2336

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplifiedChildWidth
Source SHA256: 1d9abea4ca98c7266e72b50c7e3ec32b98d2a70ad21e36af6a66763457749581
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2337





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedChildWidth
open ActualEisensteinCubic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CenteredMomentSecondRadicalBudget
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondChildRadialWidth
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondActualWidth CenteredMomentSecondWidthDrop
open CenteredMomentSecondCanonical CenteredMomentSecondHeightFamily
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

theorem modulus_pos (η:Character) : 0<(η.modulus.absNorm:ℝ) :=
  norm_pos _ η.modulus_ne_bot
theorem span_pos (m:O)(hm:m≠0) : 0<((Ideal.span {m}).absNorm:ℝ) :=
  norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hm)

theorem canonical_modulus_log (η ρ:Character)(m:O)(hm:m≠0)
    (I J:Ideal O)(A:Finset (CommonIndex I J))(Z:ℝ)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    Real.logb Z (ρ.modulus.absNorm:ℝ)=
      Real.logb Z (η.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((∏P∈A,P.val).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ) := by
  have he:0<((∏P∈A,P.val).absNorm:ℝ) := by
    apply norm_pos
    exact Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [hmod,first_displayed_norm]
  push_cast
  rw [Real.logb_mul (mul_pos (mul_pos (modulus_pos η) (span_pos m hm))
      (span_pos 72 (by norm_num))).ne' (mul_pos he (active_norm_pos I J)).ne',
    Real.logb_mul (mul_pos (modulus_pos η) (span_pos m hm)).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (modulus_pos η).ne' (span_pos m hm).ne',
    Real.logb_mul he.ne' (active_norm_pos I J).ne']
  ring

theorem radical_error_log_bound (ρ η:Character)(χ:RayCharacter)(m p:O)
    (hm:m≠0)(hp:p≠0)(Z:ℝ)(hZ:1<Z)(n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:η.modulus.absNorm≤radicalBound (childCharacter ρ χ) m p (errorMovingExponent n)) :
    Real.logb Z (η.modulus.absNorm:ℝ)≤
      Real.logb Z (ρ.modulus.absNorm:ℝ)+Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+errorMoving p Z (n+1) := by
  have hmpos:=span_pos m hm
  have h12:=span_pos 12 (by norm_num)
  have h72:=span_pos 72 (by norm_num)
  have hρ:=modulus_pos ρ
  have hray:( (childCharacter ρ χ).modulus.absNorm:ℝ)≤
      (ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm := by
    exact_mod_cast child_modulus_bound ρ χ
  have hb:(η.modulus.absNorm:ℝ)≤
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*Z^(errorMoving p Z (n+1)) := by
    have hh:(η.modulus.absNorm:ℝ)≤(radicalBound (childCharacter ρ χ) m p (errorMovingExponent n):ℝ):=by exact_mod_cast hN
    rw [radicalBound_error_power _ m p hp Z hZ n hn] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hray (by positivity))
        (by positivity)) (by positivity))
  have hh:=Real.logb_le_logb_of_le hZ (modulus_pos η) hb
  rw [Real.logb_mul (by positivity : (0:ℝ)<
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
      (Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm).ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
    Real.logb_mul (by positivity : (0:ℝ)<
      ((ρ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*(Ideal.span {m}).absNorm).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (mul_pos (modulus_pos ρ) (span_pos 12 (by norm_num))).ne' (span_pos m hm).ne',
    Real.logb_mul (modulus_pos ρ).ne' (span_pos 12 (by norm_num)).ne',
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  linarith

theorem common_nominal_identity (A c d R E m q w wo σ δ reserve branch:ℝ) :
    2*(A-c-w)-(2*A-c-d+R+E-m+
      max (d-c-2*w+wo) 0+branch*σ+δ+reserve)+(q+R+E+wo)=
    m+q+(d-c-2*w+wo-max (d-c-2*w+wo) 0)-branch*σ-δ-reserve := by ring

theorem common_nominal_le (A c d R E m q w wo σ δ reserve branch:ℝ) :
    2*(A-c-w)-(2*A-c-d+R+E-m+
      max (d-c-2*w+wo) 0+branch*σ+δ+reserve)+(q+R+E+wo)≤
    m+q-branch*σ-δ-reserve := by
  rw [common_nominal_identity]
  linarith [le_max_left (d-c-2*w+wo) (0:ℝ)]

theorem shortened_log (I J:Ideal O)(X Z:ℝ)(hX:0<X)(p:O)(hp:p≠0)(k:ℕ) :
    Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^k))=
      Real.logb Z X-Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)-errorRemoval p Z k := by
  rw [Real.logb_div hX.ne' (mul_pos (norm_pos _ (commonPart_ne_zero I J))
    (pow_pos (normValue_pos p hp) k)).ne',
    Real.logb_mul (norm_pos _ (commonPart_ne_zero I J)).ne' (pow_pos (normValue_pos p hp) k).ne',
    Real.logb_pow]
  unfold errorRemoval
  ring

theorem main_nominal_bound (η ρ:Character)(m:O)(hm:m≠0)(I J:Ideal O)
    (A:Finset (CommonIndex I J))(K X Z σ δ reserve:ℝ)
    (hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J}) :
    2*Real.logb Z (X/(commonPart I J).absNorm)-
      Real.logb Z (mainCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve)+
      Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m}).absNorm:ℝ)+Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)-
      2*σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  rw [Real.logb_div hX.ne' (norm_pos _ (commonPart_ne_zero I J)).ne',
    mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',
    nominalLog,CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX,
    canonical_modulus_log η ρ m hm I J A Z hmod]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) (0:ℝ)]

theorem error_nominal_bound (η ρ θ:Character)(χ:RayCharacter)(m₀ m₁ p:O)
    (hm₀:m₀≠0)(hm₁:m₁≠0)(hp:p≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
    (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
    (hmod:ρ.modulus=η.modulus*Ideal.span {m₀}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})
    (n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ) m₁ p (errorMovingExponent n)) :
    2*Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^(n+1)))-
      Real.logb Z (errorCommonRadius Z (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ))
        (nominalLog I J (∏P∈A,P.val) K X Z) (Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)) σ δ reserve p (n+1))+
      Real.logb Z (θ.modulus.absNorm:ℝ)≤
      Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z ((Ideal.span {m₀}).absNorm:ℝ)+Real.logb Z ((Ideal.span {m₁}).absNorm:ℝ)+
      2*Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)-σ-δ-reserve := by
  have he:(∏P∈A,P.val)≠0 := Finset.prod_ne_zero_iff.mpr (fun P _=>(IdealMobiusDivisorSum.support_prime (Finset.mem_inter.mp P.property).1).ne_zero)
  have hq:=radical_error_log_bound ρ θ χ m₁ p hm₁ hp Z hZ n hn hN
  rw [canonical_modulus_log η ρ m₀ hm₀ I J A Z hmod] at hq
  rw [shortened_log I J X Z hX p hp (n+1),errorCommonRadius,
    Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne',nominalLog,
    CenteredMomentFirstPhysicalLedger.nominal_log I J _ he Z K X hK hX]
  linarith [le_max_left (Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)-
    Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)-2*errorRemoval p Z (n+1)+errorMoving p Z (n+1)) (0:ℝ)]

theorem physical_radial_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(b:ℝ)(hb:0<b) :
    Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)-
      Real.logb Z (normValue (commonFrequencyGenerator C D))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hw:=radial_radius_log_budget h t S β (frequencyRadius Tsec Z ξ) rows W L hL n hne Z hZ χ b hb
  have hl:=Real.logb_le_logb_of_le hZ hT hscale
  rw [Real.logb_mul hCs.ne' (div_pos (sq_pos_of_pos hH) hL).ne',
    Real.logb_div (sq_pos_of_pos hH).ne' hL.ne',Real.logb_pow] at hl
  have hr:Real.logb Z (frequencyRadius Tsec Z ξ)≤
      2*Real.logb Z H-Real.logb Z L+ξ/2+Real.logb Z Csec := by
    rw [frequencyRadius,Real.logb_mul hT.ne'
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).ne',
      Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
    push_cast at hl
    linarith
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  have hf:Real.logb Z (16*b*Csec*(fixedFactor:ℝ))=
      Real.logb Z Csec+Real.logb Z (16*b*(fixedFactor:ℝ)) := by
    rw [←Real.logb_mul hCs.ne' (by positivity : (16:ℝ)*b*fixedFactor≠0)]
    congr 1
    ring
  rw [hf]
  linarith

theorem physical_declared_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by
  have hh:=physical_radial_budget h t S β rows W Z H L Tsec Csec ξ hZ hH hL hT hCs hscale n hne χ b hb
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hbH:1≤b*dyadicScale (n 1):=(normValue_ge_one y hy0).trans
    (radial_support_bound n Φ b hs y hy)
  rw [max_eq_right hbH]
  linarith

theorem physical_whole_budget {η:Character}{C D:Ideal O}
    {hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family η C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Z H L Tsec Csec ξ:ℝ)(hZ:1<Z)(hH:0<H)(hL:0<L)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*(H^2/L))(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W L n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
        Real.logb Z (16*b*Csec*(fixedFactor:ℝ))) := by
  have hh:=physical_radial_budget h t S β rows W Z H L Tsec Csec ξ hZ hH hL hT hCs hscale n hne χ b hb
  have hc:=actual_common_log_ge_unit C D hC U Z hZ
  have hb':Real.logb Z (b*dyadicScale (n 1))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      2*Real.logb Z H-Real.logb Z L+Real.logb Z (η.modulus.absNorm:ℝ)+ξ/2+
        Real.logb Z (16*b*Csec*(fixedFactor:ℝ)) := by linarith
  rw [←Real.logb_mul (mul_pos hb (dyadicScale_pos (n 1))).ne' (modulus_pos (τ χ)).ne'] at hb'
  exact (mul_le_mul_of_nonneg_right (radial_support_bound n Φ b hs y hy)
    (modulus_pos (τ χ)).le).trans
    ((Real.logb_le_iff_le_rpow hZ (mul_pos (mul_pos hb (dyadicScale_pos (n 1)))
      (modulus_pos (τ χ)))).mp hb')

theorem original_coefficient_fixed_mask {ι:Type*}[Fintype ι]
    (D:OriginalData ι)(ρ:Character)(t T:ℝ) :
    D.coefficient ρ fixedBadMask t T=
      fun I:supportedColumns D.columns => (Real.sqrt T:ℂ)⁻¹*(D.beta I*heightCoeff ρ t I) := by
  funext I
  rw [OriginalData.coefficient,←heightCoeff_eq_fixed_rowWeight ρ t I
    (Finset.mem_filter.mp I.property).2]

def presentationFactor : ℝ :=
  ((Ideal.span {(72:O)}).absNorm:ℝ)*(fixedFactor:ℝ)

theorem presentationFactor_pos : 0<presentationFactor :=
  mul_pos (span_pos 72 (by norm_num)) (by exact_mod_cast fixedFactor_pos)

theorem presentationFactor_log (Z:ℝ) : Real.logb Z presentationFactor=
    2*Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {(12:O)}).absNorm:ℝ)+
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ) := by
  unfold presentationFactor fixedFactor
  push_cast
  rw [Real.logb_mul (span_pos 72 (by norm_num)).ne'
      (mul_pos (mul_pos (span_pos 12 (by norm_num)) (span_pos fixedBadMask fixedBadMask_ne_zero))
        (span_pos 72 (by norm_num))).ne',
    Real.logb_mul (mul_pos (span_pos 12 (by norm_num)) (span_pos fixedBadMask fixedBadMask_ne_zero)).ne'
      (span_pos 72 (by norm_num)).ne',
    Real.logb_mul (span_pos 12 (by norm_num)).ne' (span_pos fixedBadMask fixedBadMask_ne_zero).ne']
  ring

theorem first_fixed_log_le (Z:ℝ)(hZ:1<Z) :
    Real.logb Z ((Ideal.span {(72:O)}).absNorm:ℝ)≤Real.logb Z presentationFactor := by
  apply Real.logb_le_logb_of_le hZ (span_pos 72 (by norm_num))
  have hf:(1:ℝ)≤fixedFactor:=by exact_mod_cast fixedFactor_pos
  exact le_mul_of_one_le_right (span_pos 72 (by norm_num)).le hf

theorem exists_fixed_width_threshold (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→∀ξ:ℝ,ξ≤σ/4→
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)<σ/2 := by
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  let C:ℝ:=((Ideal.span {fixedBadMask}).absNorm:ℝ)*(16*b*Csec*(fixedFactor:ℝ)*presentationFactor)
  have hCp:0<C:=mul_pos (span_pos fixedBadMask fixedBadMask_ne_zero)
    (mul_pos (by positivity : (0:ℝ)<16*b*Csec*fixedFactor) presentationFactor_pos)
  have he:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop (show 0<σ/4 by linarith))) C
  obtain ⟨Z₀,hZ₀⟩:=Filter.eventually_atTop.1 (he.and (Filter.eventually_gt_atTop (1:ℝ)))
  refine ⟨max 2 Z₀,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ ξ hξ
  obtain ⟨hCZ,hZ1⟩:=hZ₀ Z ((le_max_right _ _).trans hZ)
  have hh:Real.logb Z C≤σ/4:=(Real.logb_le_iff_le_rpow hZ1 hCp).mpr hCZ
  dsimp [C] at hh
  rw [Real.logb_mul (span_pos fixedBadMask fixedBadMask_ne_zero).ne'
    (mul_pos (by positivity : (0:ℝ)<16*b*Csec*fixedFactor) presentationFactor_pos).ne'] at hh
  linarith

def fixedWidthThreshold (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) : ℝ :=
  (exists_fixed_width_threshold b Csec σ hb hCs hσ).choose

theorem fixedWidthThreshold_spec (b Csec σ:ℝ)(hb:0<b)(hCs:0<Csec)(hσ:0<σ) :
    1<fixedWidthThreshold b Csec σ hb hCs hσ ∧
    ∀Z:ℝ,fixedWidthThreshold b Csec σ hb hCs hσ≤Z→∀ξ:ℝ,ξ≤σ/4→
      Real.logb Z ((Ideal.span {fixedBadMask}).absNorm:ℝ)+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)<σ/2 :=
  (exists_fixed_width_threshold b Csec σ hb hCs hσ).choose_spec

section ActualSource
variable (η ρ:Character)(m:O)(hm:m≠0)(I J:Ideal O)(A:Finset (CommonIndex I J))
  (K X Z σ δ reserve:ℝ)(hK:0<K)(hX:0<X)(hZ:1<Z)
  (hmod:ρ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun P:CommonIndex I J=>P.val) A*activeConductor I J})

local notation "cc" => Real.logb Z (Ideal.absNorm (commonPart I J):ℝ)
local notation "dd" => Real.logb Z (Ideal.absNorm (commonPart J I):ℝ)
local notation "kk" => nominalLog I J (∏P∈A,Subtype.val P) K X Z
local notation "Lm" => mainCommonRadius Z dd kk cc σ δ reserve
local notation "Hx" => X/Ideal.absNorm (commonPart I J)
local notation "parentWidth" => Real.logb Z K+Real.logb Z (Ideal.absNorm (Character.modulus η):ℝ)+Real.logb Z (Ideal.absNorm (Ideal.span (Singleton.singleton m)):ℝ)
include σ δ reserve hm hK hX hZ hmod

theorem main_nominal_fixed :
    2*Real.logb Z Hx-Real.logb Z Lm+Real.logb Z (ρ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-2*σ-δ-reserve := by
  have hh:=main_nominal_bound η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  linarith [first_fixed_log_le Z hZ]

theorem error_nominal_fixed (θ:Character)(χ:RayCharacter)(p:O)(hp:p≠0)
    (n:ℕ)(hn:n=0∨n=5∨n=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ) fixedBadMask p (errorMovingExponent n)) :
    2*Real.logb Z (X/((commonPart I J).absNorm*(normValue p)^(n+1)))-
      Real.logb Z (errorCommonRadius Z dd kk cc σ δ reserve p (n+1))+
      Real.logb Z (θ.modulus.absNorm:ℝ)≤
      parentWidth+Real.logb Z presentationFactor-σ-δ-reserve := by
  have hh:=error_nominal_bound η ρ θ χ m fixedBadMask p hm fixedBadMask_ne_zero hp
    I J A K X Z σ δ reserve hK hX hZ hmod n hn hN
  rw [presentationFactor_log]
  linarith

theorem main_declared_width {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-2*σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<Hx:=div_pos hX (norm_pos _ (commonPart_ne_zero I J))
  have hL:0<Lm:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z Hx Lm Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=main_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem error_declared_width (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)≤
      parentWidth-σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor) := by
  have hHx:0<X/((commonPart I J).absNorm*(normValue p)^(k+1)):=
    div_pos hX (mul_pos (norm_pos _ (commonPart_ne_zero I J)) (pow_pos (normValue_pos p hp) _))
  have hL:0<errorCommonRadius Z dd kk cc σ δ reserve p (k+1):=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_declared_budget h t S β rows W Z _ _ Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hnom:=error_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem main_whole_width {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(parentWidth-2*σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)) := by
  have hHx:0<Hx:=div_pos hX (norm_pos _ (commonPart_ne_zero I J))
  have hL:0<Lm:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_whole_budget h t S β rows W Z Hx Lm Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy
  have hnom:=main_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  apply hw.trans
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem error_whole_width (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy:Φ (normValue y/dyadicScale (n 1))≠0) :
    normValue y*((τ χ).modulus.absNorm:ℝ)≤
      Z^(parentWidth-σ-δ-reserve+ξ/2+
      Real.logb Z (16*b*Csec*(fixedFactor:ℝ)*presentationFactor)) := by
  have hHx:0<X/((commonPart I J).absNorm*(normValue p)^(k+1)):=
    div_pos hX (mul_pos (norm_pos _ (commonPart_ne_zero I J)) (pow_pos (normValue_pos p hp) _))
  have hL:0<errorCommonRadius Z dd kk cc σ δ reserve p (k+1):=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hw:=physical_whole_budget h t S β rows W Z _ _ Tsec Csec ξ hZ hHx hL hT hCs hscale n hne χ Φ b hb hs y hy
  have hnom:=error_nominal_fixed η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN
  have hF:(0:ℝ)<fixedFactor:=by exact_mod_cast fixedFactor_pos
  apply hw.trans
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  rw [Real.logb_mul (by positivity : (0:ℝ)<16*b*Csec*fixedFactor).ne' presentationFactor_pos.ne']
  linarith

theorem main_declared_width_drop {C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}(h:Family ρ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)(hscale:Tsec≤Csec*(Hx^2/Lm))
    (n:Fin 4→ℤ)
    (hne:physicalBlock ρ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W Lm n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=main_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith

theorem error_declared_width_drop (θ:Character)(χ₀:RayCharacter)(p:O)(hp:p≠0)
    (k:ℕ)(hk:k=0∨k=5∨k=6)
    (hN:θ.modulus.absNorm≤radicalBound (childCharacter ρ χ₀) fixedBadMask p (errorMovingExponent k))
    {C D:Ideal O}{hC:Supported C}{hD:Supported D}{U:Finset (CommonIndex C D)}
    {τ:RayCharacter→Character}(h:Family θ C D hC hD U τ)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(rows:Finset O)(W:𝓢(ℝ,ℂ))
    (Tsec Csec ξ:ℝ)(hT:0<Tsec)(hCs:0<Csec)
    (hscale:Tsec≤Csec*((X/((commonPart I J).absNorm*(normValue p)^(k+1)))^2/
      errorCommonRadius Z dd kk cc σ δ reserve p (k+1)))
    (n:Fin 4→ℤ)
    (hne:physicalBlock θ t S β C D hC hD U (frequencyRadius Tsec Z ξ) rows W
      (errorCommonRadius Z dd kk cc σ δ reserve p (k+1)) n≠0)
    (χ:RayCharacter)(Φ:ℝ→ℂ)(b:ℝ)(hb:0<b)(hs:Function.support Φ⊆Set.Iic b)
    (y:O)(hy0:y≠0)(hy:Φ (normValue y/dyadicScale (n 1))≠0)
    (hmask:m=fixedBadMask)(q:ℝ)(hcap:(η.modulus.absNorm:ℝ)≤Z^q)
    (hσ:0<σ)(hδ:0≤δ)(hr:0≤reserve)(hξ:ξ≤σ/4)
    (hlarge:fixedWidthThreshold b Csec σ hb hCs hσ≤Z) :
    Real.logb Z (max 1 (b*dyadicScale (n 1)))+Real.logb Z ((τ χ).modulus.absNorm:ℝ)<
      Real.logb Z K+q-σ/2 := by
  have hw:=error_declared_width η ρ m hm I J A K X Z σ δ reserve hK hX hZ hmod θ χ₀ p hp k hk hN h t S β rows W Tsec Csec ξ hT hCs hscale n hne χ Φ b hb hs y hy0 hy
  have hq:Real.logb Z (η.modulus.absNorm:ℝ)≤q:=
    (Real.logb_le_iff_le_rpow hZ (modulus_pos η)).mpr hcap
  have hc:=(fixedWidthThreshold_spec b Csec σ hb hCs hσ).2 Z hlarge ξ hξ
  rw [hmask] at hw
  linarith

end ActualSource
end SevenEighths.CenteredMomentAmplifiedChildWidth

end

end OAI
end OAIOriginalModule2337

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamilyUniform
Source SHA256: 8855774942d25ba08214194d99cf55af40990fb128cda7085513529bd6f16699
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2338


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology

namespace SevenEighths.CenteredMomentSecondExceptionalFamilyUniform
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondHeightFamily
open CenteredMomentSecondRadicalBudget CenteredMomentSecondLiveBlock
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentReflectedSource CenteredMomentSecondExceptionalFamily
local notation "O" => HeckeFamily.O

def fixedExpandedCost : ℝ :=
  1296*(fixedFactor:ℝ)*(Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm

theorem fixedExpandedCost_pos : 0<fixedExpandedCost := by
  have hb : (0:ℝ)<(Ideal.span {fixedBadMask}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h72 : (0:ℝ)<(Ideal.span {(72:O)}).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (show (72:O)≠0 by norm_num)))
  have hf : (0:ℝ)<fixedFactor := by exact_mod_cast fixedFactor_pos
  unfold fixedExpandedCost
  positivity

theorem expandedFactor_real (η:Character) :
    (expandedFactor η:ℝ)=fixedExpandedCost*(η.modulus.absNorm:ℝ) := by
  unfold expandedFactor fixedExpandedCost
  push_cast
  ring

theorem expanded_real_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O) :
    (expandedConductor (τ χ) R C z:ℝ)≤
      fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z := by
  obtain ⟨hl,hr⟩ := expanded_conductor_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  have hl' : (expandedConductor (τ χ) R C z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*normValue z := by
    dsimp only [normValue]
    exact_mod_cast hl
  have hr' : (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (expandedFactor η:ℝ)*R.absNorm*C.absNorm*D.absNorm*normValue z := by
    dsimp only [normValue]
    exact_mod_cast hr
  rw [expandedFactor_real] at hl' hr'
  exact ⟨hl',hr'⟩

theorem live_expanded_real_bounds {η:Character}{C D:Ideal O}{hC:Supported C}{hD:Supported D}
    {U:Finset (CommonIndex C D)}{τ:RayCharacter→Character}
    (h:Family η C D hC hD U τ)(hCD:primeSupport C=primeSupport D)
    (t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
    (W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)(n:Fin 4→ℤ)
    (hne:physicalBlock η t S β C D hC hD U radius rows W K n≠0)
    (χ ξ:RayCharacter)(R:Ideal O)(z:O)(hz:z∈liveRows C D U radius rows) :
    0<radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius := by
  obtain ⟨hR,hz0,hz1,_⟩ := liveRows_geometry C D U radius rows z hz
  obtain ⟨hl,hr⟩ := expanded_real_bounds h hCD t S β radius rows W K hK n hne χ ξ R z
  have hf := fixedExpandedCost_pos
  have hbound : fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*normValue z≤
      (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius := by
    calc
      _≤fixedExpandedCost*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*(4*radius) :=
        mul_le_mul_of_nonneg_left (live_norm_le_four_radius C D U radius rows z hz)
          (by positivity)
      _=_ := by ring
  exact ⟨hR,hz0,hz1,hl.trans hbound,hr.trans hbound⟩

theorem eventually_uniform_live_caps (ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀Z:ℝ,Z₀≤Z→∀η:Character,
    ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(U:Finset (CommonIndex C D))(τ:RayCharacter→Character),Family η C D hC hD U τ→
    ∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m q:ℝ),
    (η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→
    (R.absNorm:ℝ)≤Z^r→ radius≤Z^m→∀z∈liveRows C D U radius rows,
    0<radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+q+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+q+ε) := by
  have he := (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (4*fixedExpandedCost)
  obtain ⟨Z₁,hZ₁⟩ := Filter.eventually_atTop.1 he
  refine ⟨max 2 Z₁,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro Z hZ η C D hC hD hCD U τ h t S β radius rows W K hK n hne χ ξ R c d r m q hη hCN hDN hRN hrad z hz
  have hZpos : 0<Z := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hZ)
  have hconstant := hZ₁ Z ((le_max_right _ _).trans hZ)
  obtain ⟨hR,hz0,hz1,hl,hr⟩ := live_expanded_real_bounds h hCD t S β radius rows W K hK n hne χ ξ R z hz
  have hbound : (4*fixedExpandedCost)*η.modulus.absNorm*R.absNorm*C.absNorm*D.absNorm*radius≤
      Z^(c+d+r+m+q+ε) := by
    calc
      _≤Z^ε*Z^q*Z^r*Z^c*Z^d*Z^m := by gcongr
      _=Z^(c+d+r+m+q+ε) := by
        rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,
          ←Real.rpow_add hZpos,←Real.rpow_add hZpos]
        congr 1
        ring
  exact ⟨hR,hz0,hz1,hl.trans hbound,hr.trans hbound⟩

theorem exists_uniform_exceptional_family (ε:ℝ)(hε:0<ε) :
    ∃Z₀:ℝ,1<Z₀ ∧ ∀(η:Character)(C D:Ideal O)(hC:Supported C)(hD:Supported D),
    primeSupport C=primeSupport D→∀U:Finset (CommonIndex C D),
    ∃τ:RayCharacter→Character,Family η C D hC hD U τ ∧
    ∀Z:ℝ,Z₀≤Z→∀(t:ℝ)(S:Finset (Ideal O))(β:Ideal O→ℂ)(radius:ℝ)(rows:Finset O)
      (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→∀n:Fin 4→ℤ,
    physicalBlock η t S β C D hC hD U radius rows W K n≠0→
    ∀(χ ξ:RayCharacter)(R:Ideal O)(c d r m q:ℝ),
    (η.modulus.absNorm:ℝ)≤Z^q→(C.absNorm:ℝ)≤Z^c→(D.absNorm:ℝ)≤Z^d→
    (R.absNorm:ℝ)≤Z^r→ radius≤Z^m→∀z∈liveRows C D U radius rows,
    0<radius ∧ z≠0 ∧ 1≤normValue z ∧
    (expandedConductor (τ χ) R C z:ℝ)≤Z^(c+d+r+m+q+ε) ∧
    (expandedConductor (reflected (τ ξ)) R D z:ℝ)≤Z^(c+d+r+m+q+ε) := by
  obtain ⟨Z₀,hZ₀,hcaps⟩ := eventually_uniform_live_caps ε hε
  refine ⟨Z₀,hZ₀,?_⟩
  intro η C D hC hD hCD U
  obtain ⟨τ,hτ⟩ := exists_exceptional_family η C D hC hD hCD U
  refine ⟨τ,hτ,?_⟩
  intro Z hZ
  exact hcaps Z hZ η C D hC hD hCD U τ hτ

end SevenEighths.CenteredMomentSecondExceptionalFamilyUniform

end

end OAI
end OAIOriginalModule2338

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairDictionary
Source SHA256: 821259e00d2fe36384f3152ddf507da641b660f80c0b3c0d5158442385e51bc2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2339


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondExceptionalPairDictionary
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma raw_pair (V:ℝ)(hV:0<V)(a b:ℂ):
    ‖a‖*‖b‖=V*‖(Real.sqrt V:ℂ)⁻¹*a‖*‖(Real.sqrt V:ℂ)⁻¹*b‖:=by
  have hs:0<Real.sqrt V:=Real.sqrt_pos.mpr hV
  simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  field_simp
  rw [Real.sq_sqrt hV.le]

omit [DecidableEq ι] in
theorem original_pair (s:Input ι)(η τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y:ℝ)(Ds:Finset (Ideal O))(rows:Finset O)
    (hτ₁:∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
      heightCoeff τ₁ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (hτ₂:∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
      heightCoeff τ₂ v I=heightCoeff η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)):
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) w) z‖*
      ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*
          star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) w)) (-z)‖)=
      volume s.toData*(∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
        ‖windowColumn s C hC R seed L τ₁ t w X logAnnulus z‖*
        ‖windowColumn s D hD R seed L (reflected τ₂) t (-w) Y logAnnulus z‖):=by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro L hL
  rw [mul_left_comm (volume s.toData) ‖(moebius L:ℂ)‖]
  apply congrArg (fun a:ℝ=>‖(moebius L:ℂ)‖*a)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [raw_pair (volume s.toData) (volume_pos s.toData)]
  rw [actual_sector_window s η τ₁ χ A C hC R seed L t w X logAnnulus z hτ₁,
    actual_reflected_sector_window s η τ₂ ξ A D hD R seed L t w Y z hτ₂]
  ring

end SevenEighths.CenteredMomentSecondExceptionalPairDictionary

end

end OAI
end OAIOriginalModule2339

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPairBound
Source SHA256: 346bea31018789d3e9f22a1215e99ba273d329192eb00a3460a4dd3f1f0b4cdc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2340




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentSecondExceptionalPairBound
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonExceptionalWindow CenteredMomentExceptionalWindowHeight
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def originalPair (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y:ℝ)(Ds:Finset (Ideal O))(rows:Finset O):ℝ:=
    let S:=finiteColumns (Fintype.piFinset s.pools)
    let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖rowPolynomial Finset.univ (sectorElement C hC.1 S)
        (fun I=>divisorCoefficient L (sectorElement C hC.1 S)
          (movingCoefficient A (sectorElement C hC.1 S)
            (fun I:sectorPool C hC.1 S=>β (C*I)*heightCoeff η t I)) χ I*
          columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) w) z‖*
      ‖rowPolynomial Finset.univ (sectorElement D hD.1 S)
        (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
          (movingCoefficient A (sectorElement D hD.1 S)
            (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*
          star (columnPhase logAnnulus (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) w)) (-z)‖)

omit [DecidableEq ι] in
lemma window_withHeight (s:Input ι)(τ η:Character)(v t θ X:ℝ)(C:Ideal O)(hC:Supported C)
    (R seed L:Ideal O)(V:ℝ→ℂ)(z:O):
    windowColumn (withHeight s τ v) C hC R seed L η t θ X V z=
      windowColumn s C hC R seed L η t θ X V z:=rfl

theorem actual_original_pair (lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Tests),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(rows.card:ℝ)*Z^(2*ε+δ-max (r-Real.logb Z (C.absNorm:ℝ)) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,hJ⟩:=actual_common_window lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase s s p p w J
  let F:=volume s.toData*(K*(rows.card:ℝ)*Z^(2*ε+δ-max (r-Real.logb Z (C.absNorm:ℝ)) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentSecondExceptionalPairBound

end

end OAI
end OAIOriginalModule2340

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQPair
Source SHA256: a48703cfe93eb9ebbb97f802a8f7a7b0e90a4ac339e6a53dd18de764d3e55565
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2341







namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary CenteredMomentSecondExceptionalPairBound
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_original_pair (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ₀:RayCharacter)(U:Finset (CommonIndex C D)),
      idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ₀) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_common_window wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ η₀ χ₀ U hη m hm hml hm2 hex Cr M hCr hN X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ η₀ χ₀ U hη m hm hml hm2 hex Cr M hCr hN w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [CenteredMomentCommonExceptionalSymmetry.same_raw_better_cap] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase Sprofile s s p p w J
  let F:=volume s.toData*(K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass Sprofile s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,CenteredMomentFiniteProfileExceptionalCommon.mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end OAIOriginalModule2341

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalPair
Source SHA256: bab554cd708a43ece00d82611b5ec9683da2d74138db178e375c5e57382cdd1b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2342







namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairDictionary CenteredMomentSecondExceptionalPairBound
open CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_canonical_original_pair (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(ε δ θ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} → ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O),R≠0 → seed∣C → seed∣D →
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀(τ₁ τ₂:Character)(χ ξ:RayCharacter)(A:O),
      (∀I:Ideal O,Supported I → IsCoprime C I → ∀v:ℝ,
        heightCoeff τ₁ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      (∀I:Ideal O,Supported I → IsCoprime D I → ∀v:ℝ,
        heightCoeff τ₂ v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter ξ (primaryGenerator I)) →
      ∀rows:Finset O,(∀z∈rows,z≠0) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₁ Q fixedBadMask 1 z) →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow τ₂ Q fixedBadMask 1 (-z)) →
      (∀z∈rows,(τ₁.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀z∈rows,((reflected τ₂).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀(η₀:Character)(χ₀:RayCharacter)(U:Finset (CommonIndex C D)),
      IsCoprime Q C → idealCoeff η₀ C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter η₀ χ₀) Q m
        (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀(X Y:ℝ),0<X → 0<Y → ∀Ds:Finset (Ideal O),
      (∀L∈Ds,(moebius L:ℂ)≠0 → (L.absNorm:ℝ)≤Z^Lbound) → ∀w:ℝ,
      originalPair s s.η χ ξ A C D hC hD R seed s.t w X Y Ds rows≤
        (K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
          ((C.absNorm:ℝ)*D.absNorm)^θ*
          ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
            frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
          (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2)*
          (1+‖w‖)^(2*J):=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_common_window wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  refine ⟨J,Sprofile,hSprofile,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R seed hR hsC hsD r hX₁ hX₂ hY₁ hY₂
    τ₁ τ₂ χ ξ A hτ₁ hτ₂ rows hn hex₁ hex₂ hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY Ds hDs w
  have hex₂':∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (reflected τ₂) Q fixedBadMask 1 z:=by
    intro z hz
    exact (reflected_inducing τ₂ Q fixedBadMask 1 z (dvd_mul_right _ _) (dvd_mul_left _ _)).mp (hex₂ z hz)
  have hb:=hZ.2 (withHeight s τ₁ s.t) (withHeight s (reflected τ₂) s.t) p p hlo hhi hlo hhi
    hP hP hW₁ hW₂ hW₁ hW₂ C D hC hD R seed hR hsC hsD r r
    hX₁ hX₂ hY₁ hY₂ hX₁ hX₂ hY₁ hY₂ rows hn hex₁ hex₂' hcond₁ hcond₂ η₀ χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN w (-w) X Y hX hY Ds hDs
  simp only [window_withHeight] at hb
  rw [CenteredMomentCommonExceptionalSymmetry.same_raw_better_cap] at hb
  rw [originalPair,original_pair s s.η τ₁ τ₂ χ ξ A C D hC hD R seed s.t w X Y Ds rows hτ₁ hτ₂]
  apply (mul_le_mul_of_nonneg_left hb (volume_pos s.toData).le).trans
  have hm:=mass_phase Sprofile s s p p w J
  let F:=volume s.toData*(K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
            (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
            2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*(frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm)))*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2
  have hz:0<Z:=zero_lt_one.trans hZ.1
  have hF:0≤F:=by
    dsimp only [F]
    exact mul_nonneg (mul_nonneg (volume_pos s.toData).le
      (mul_nonneg (by positivity) (div_nonneg (mul_nonneg (frozenProfile_nonneg s) (frozenProfile_nonneg s))
        (by positivity)))) (sq_nonneg _)
  calc
    _=F*mass Sprofile s s p p s.t s.t w (-w) J:=by
      dsimp only [F,frozenProfile,withHeight,CenteredMomentFiniteProfileExceptionalCommon.mass,
        CenteredMomentAllocatedDetectorAmplitude.slotControl,CenteredMomentExceptionalAmplitudePair.volume]
      ring
    _≤F*((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*(1+‖w‖)^(2*J)):=
      mul_le_mul_of_nonneg_left hm hF
    _=_:=by dsimp only [F];ring

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end OAIOriginalModule2342

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondDivisorSupport
Source SHA256: d08f1a4168785e953e853795ba6ecb047687711af09bd352311dee1a22cde0c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2343


namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSecondDivisorSupport
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondScaled CenteredMomentChildAssembly
open CenteredMomentRowNorm CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondExceptionalPairBound RayFourExpansion
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _

theorem live_right_divisor_norm (D I L:Ideal O)(hD:D≠0)(hI:I≠0)
    (β:Ideal O→ℂ)(H:ℝ)(hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)
    (hne:β (D*I)≠0)(hLI:L∣I):
    (L.absNorm:ℝ)≤H/(D.absNorm:ℝ):=by
  have hDpos:(0:ℝ)<D.absNorm:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hnorm:(L.absNorm:ℝ)≤I.absNorm:=by
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)) (map_dvd Ideal.absNorm hLI)
  have hb:=hβ (D*I) hne
  rw [map_mul,Nat.cast_mul] at hb
  apply hnorm.trans
  apply (le_div_iff₀ hDpos).mpr
  simpa only [mul_comm] using hb

theorem right_divisor_coefficient_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)<L.absNorm)
    (η:Character)(t:ℝ)(A:O)(ξ:RayCharacter)(I:sectorPool D hD.1 S):
    divisorCoefficient L (sectorElement D hD.1 S)
      (movingCoefficient A (sectorElement D hD.1 S)
        (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I=0:=by
  unfold divisorCoefficient
  rw [sectorElement_span]
  split_ifs with hd
  · have hz:β (D*I)=0:=by
      by_contra hn
      exact (not_le_of_gt hL) (live_right_divisor_norm D I L hD.1
        (sectorPool_supported D hD.1 S I).1 β H hβ hn hd)
    simp only [movingCoefficient,hz,zero_mul]
  · rfl

theorem right_divisor_row_zero
    (D:Ideal O)(hD:Supported D)(S:Finset (Ideal O))(β:Ideal O→ℂ)(H:ℝ)
    (hβ:∀J,β J≠0→(J.absNorm:ℝ)≤H)(L:Ideal O)(hL:H/(D.absNorm:ℝ)<L.absNorm)
    (η:Character)(t:ℝ)(A:O)(ξ:RayCharacter)(v:sectorPool D hD.1 S→ℂ)(z:O):
    rowPolynomial Finset.univ (sectorElement D hD.1 S)
      (fun I=>divisorCoefficient L (sectorElement D hD.1 S)
        (movingCoefficient A (sectorElement D hD.1 S)
          (fun I:sectorPool D hD.1 S=>β (D*I)*heightCoeff η t I)) ξ I*v I) z=0:=by
  unfold rowPolynomial
  apply Finset.sum_eq_zero
  intro I hI
  exact mul_eq_zero_of_left
    (mul_eq_zero_of_left (right_divisor_coefficient_zero D hD S β H hβ L hL η t A ξ I) _) _

theorem originalPair_filter_right {ι:Type*}[Fintype ι][DecidableEq ι]
    (s:Input ι)(η:Character)(χ ξ:RayCharacter)(A:O)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(R seed:Ideal O)
    (t w X Y H:ℝ)(Ds:Finset (Ideal O))(rows:Finset O)
    (hβ:∀I:Ideal O,finiteColumnCoefficient (Fintype.piFinset s.pools)
      (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) I≠0→
      (I.absNorm:ℝ)≤H):
    originalPair s η χ ξ A C D hC hD R seed t w X Y Ds rows=
      originalPair s η χ ξ A C D hC hD R seed t w X Y
        (Ds.filter (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ))) rows:=by
  unfold originalPair
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro L hLD
  by_cases hL:(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)
  · rw [ite_eq_left hL]
  · rw [ite_eq_right hL]
    have hz:=right_divisor_row_zero D hD (finiteColumns (Fintype.piFinset s.pools))
      (finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed))
      H hβ L (lt_of_not_ge hL) η t A ξ
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro z hzr
    apply mul_eq_zero_of_right
    exact norm_eq_zero.mpr (hz _ _)

end SevenEighths.CenteredMomentSecondDivisorSupport

end

end OAI
end OAIOriginalModule2343

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalPhysicalBlock
Source SHA256: cb71d12400cf53bb33ac5923ed3d8db388cd00226caab2b43bc87b9194a5983e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2344




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

def sourceBudget {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ):ℝ:=
  K*(768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
    Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D=>P.val)
      (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6+
      2*ε+δ-max (r-min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))) 0)*
    ((C.absNorm:ℝ)*D.absNorm)^θ*
    ((1+2*Real.pi)^(4*J)*profileMass Sprofile s.toData s.toData p p J*
      frozenProfile s*frozenProfile s/((C.absNorm:ℝ)*D.absNorm))*volume s.toData*
    (∫u:ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth u‖)^2

lemma sourceBudget_nonneg {wlo whi:ℝ} (Sprofile:Finset (ℕ×ℕ)) (s:Input ι)(p:Profiles wlo whi)(J:ℕ)(Q C D:Ideal O)(U:Finset (CommonIndex C D))
    (K Z ε δ θ r Cr M:ℝ)(hK:0≤K)(hZ:0≤Z)(hCr:0≤Cr):
    0≤sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  have hp:=profileMass_nonneg Sprofile s.toData s.toData p p J
  have hf:=frozenProfile_nonneg s
  have hv:0≤volume s.toData:=(volume_pos s.toData).le
  unfold sourceBudget
  positivity

theorem actual_original_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,IsCoprime Q C → idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀X Y:ℝ,0<X → 0<Y →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R:ℝ)(ρ x:O→ℝ)(rK:ℝ),0<rK →
      (1+rK)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff s.η s.t I)*star (β (D*J)*heightCoeff s.η s.t J))*
              wholeKernel W (fun _=>logAnnulus) rK (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_original_pair wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ck,hCk,hkernel⟩:=actual_exceptional_block_bound W decay (2*J)
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hcop hη
    m hm hml hm2 hex Cr M hCr hN X Y hX hY H hβ hHD R ρ x rK hrK
  apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R rows ρ x
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) Q m χ₀ hQ72 hml hm2 hex
    (sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M)
    (sourceBudget_nonneg Sprofile s p J Q C D U K Z ε δ θ r Cr M hK.le (zero_lt_one.trans hZ.1).le hCr)
  intro χ ξ _ _ w
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
    hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
    (fun I hI hc v=>hτ χ I hI (Or.inl hc) v)
    (fun I hI hc v=>hτ (ξ⁻¹) I hI (Or.inr hc) v)
    rows hn (hex₁ χ) (hex₂ (ξ⁻¹)) (hcond₁ χ) (hcond₂ (ξ⁻¹))
    s.η χ₀ U hcop hη m hm hml hm2 hex Cr M hCr hN X Y hX hY
    ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
      (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)))
    (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
  change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y
    (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) rows≤_
  rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y H _ rows hβ]
  exact hp

end SevenEighths.CenteredMomentFiniteProfileExceptionalPhysical

end

end OAI
end OAIOriginalModule2344

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQBlock
Source SHA256: 484b710fb98ffd6a5b6af77513cc03cb2a355ae9414b90fe4b30eb632ca3da21
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2345





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter MeasureTheory

namespace SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss UniqueFactorizationMonoid
open CenteredMomentCommonRadialData CenteredMomentCommonWindowColumn CenteredMomentReflectedSource
open CenteredMomentCommonSectorWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondScaled CenteredMomentChildAssembly CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentExceptionalAmplitudePair
open CenteredMomentLogDyadic RayFourExpansion CenteredMomentSmooth
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonExceptionalCost
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalHeight CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalPairBound
open CenteredMomentFiniteProfileExceptional CenteredMomentFiniteProfileExceptionalCommon
open CenteredMomentFiniteProfileExceptionalPhysical
open CenteredMomentSecondExceptionalKernel CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentForcing CenteredMomentChildRows
open ConcretePrimeRowBridge CenteredMomentMobiusRegroup CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentSecondCanonicalScalar CenteredMomentSecondDivisorSupport
local notation "O" => HeckeFamily.O
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
universe u
variable {ι:Type u}[Fintype ι][DecidableEq ι]

theorem actual_original_exceptional_block (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)(lo hi:ι→ℝ)(W:𝓢(ℝ,ℂ))(decay:ℕ)
    (ε δ θ B Lbound:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∃Sprofile:Finset (ℕ×ℕ),(0,0)∈Sprofile ∧ ∃Ck:ℝ,0≤Ck ∧ ∀Q:Ideal O,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃K:ℝ,0<K ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(p:Profiles wlo whi),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      (∀i,1≤s.P i) → s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C D:Ideal O)(hC:Supported C)(hD:Supported D)(R0 seed:Ideal O),R0≠0 → seed∣C → seed∣D →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀r:ℝ,Z^r≤s.X₁ → Z^r≤s.X₂ → Z^r≤s.Y₁ → Z^r≤s.Y₂ →
      ∀τ:RayCharacter→Character,
      (∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
        heightCoeff (τ χ) v I=heightCoeff s.η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) →
      ∀(rows:Finset O),(∀z∈rows,z≠0) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 z) →
      (∀χ:RayCharacter,∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (τ χ) Q fixedBadMask 1 (-z)) →
      (∀χ:RayCharacter,∀z∈rows,((τ χ).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      (∀χ:RayCharacter,∀z∈rows,((reflected (τ χ)).modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R0.absNorm*D.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^B) →
      ∀χ₀:RayCharacter,idealCoeff s.η C≠0 →
      ∀m:O,m≠0 → goodLambda∣m → (2:O)∣m →
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow (childCharacter s.η χ₀) Q m A z) →
      ∀Cr M:ℝ,0≤Cr → (∀z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Cr*Z^M) →
      ∀X Y:ℝ,0<X → 0<Y →
      ∀H:ℝ,(∀I:Ideal O,β I≠0 → (I.absNorm:ℝ)≤H) → H/(D.absNorm:ℝ)≤Z^Lbound →
      ∀(R:ℝ)(ρ x:O→ℝ)(rK:ℝ),0<rK →
      (1+rK)^decay*‖∑z∈rows,retainedScalar C D U R z*
        ∑I:sectorPool C hC.1 S,∑J:sectorPool D hD.1 S,
          (if IsCoprime (I:Ideal O) (J:Ideal O) then
            idealCorrelation (C*I) (D*J)
              ((supported_mul_iff _ _).mpr ⟨hC,sectorPool_supported C hC.1 S I⟩)
              ((supported_mul_iff _ _).mpr ⟨hD,sectorPool_supported D hD.1 S J⟩) (A*z) else 0)*
            ((β (C*I)*heightCoeff s.η s.t I)*star (β (D*J)*heightCoeff s.η s.t J))*
              wholeKernel W (fun _=>logAnnulus) rK (ρ z) (x z)
                (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
                (Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y))‖≤
        Ck*sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M:=by
  obtain ⟨J,Sprofile,hSprofile,hJ⟩:=actual_canonical_original_pair wlo whi hwlo hwhi lo hi ε δ θ B Lbound hε hδ hθ hB hL
  obtain ⟨Ck,hCk,hkernel⟩:=actual_exceptional_block_bound W decay (2*J)
  refine ⟨J,Sprofile,hSprofile,Ck,hCk,?_⟩
  intro Q hQ hQtop hQ72
  obtain ⟨K,hK,hbound⟩:=hJ Q hQ hQtop hQ72
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD hCD U A S β
    r hX₁ hX₂ hY₁ hY₂ τ hτ rows hn hex₁ hex₂ hcond₁ hcond₂ χ₀ hη
    m hm hml hm2 hex Cr M hCr hN X Y hX hY H hβ hHD R ρ x rK hrK
  apply hkernel rK hrK s.η s.t S β C D hC hD hCD U R rows ρ x
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
    (fun I=>Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/Y)) Q m χ₀ hQ72 hml hm2 hex
    (sourceBudget Sprofile s p J Q C D U K Z ε δ θ r Cr M)
    (sourceBudget_nonneg Sprofile s p J Q C D U K Z ε δ θ r Cr M hK.le (zero_lt_one.trans hZ.1).le hCr)
  intro χ ξ _ _ w
  have hp:=hZ.2 s p hlo hhi hP hW₁ hW₂ C D hC hD R0 seed hR hsC hsD r
    hX₁ hX₂ hY₁ hY₂ (τ χ) (τ (ξ⁻¹)) χ (ξ⁻¹) A
    (fun I hI hc v=>hτ χ I hI (Or.inl hc) v)
    (fun I hI hc v=>hτ (ξ⁻¹) I hI (Or.inr hc) v)
    rows hn (hex₁ χ) (hex₂ (ξ⁻¹)) (hcond₁ χ) (hcond₂ (ξ⁻¹))
    s.η χ₀ U hη m hm hml hm2 hex Cr M hCr hN X Y hX hY
    ((divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))).filter
      (fun L=>(L.absNorm:ℝ)≤H/(D.absNorm:ℝ)))
    (fun L hL _=>(Finset.mem_filter.mp hL).2.trans hHD) w
  change originalPair s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y
    (divisorPool Finset.univ (fun I:sectorPool D hD.1 S=>(I:Ideal O))) rows≤_
  rw [originalPair_filter_right s s.η χ (ξ⁻¹) A C D hC hD R0 seed s.t w X Y H _ rows hβ]
  exact hp

end SevenEighths.CenteredMomentFiniteProfileExceptionalFixedQ

end

end OAI
end OAIOriginalModule2345

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalFixedQRows
Source SHA256: 52f28ec48d3706d657636ce2e97ccd47aad4f8897c0f0f5a09983dbc359d166c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2346


