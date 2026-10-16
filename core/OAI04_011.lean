    (lists:σ→Finset ι)(a:σ→ι→ℂ)(labels:Finset (Ideal Eis))(rows:Finset Eis)
    (d:Ideal Eis→ℝ)(w:ℝ→ℂ){Z:ℝ}(hZ:0<Z)(N h F:ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows d
      (childLogTest w h) (Z^N) Z F =
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows d
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z F := by
  unfold normalizedColumnEnergy
  simp_rw [norm_mul, canonical_row_clipping_norm p hp hcop hg pool Ψ m _ _
    slots lists a w hZ N h]

theorem initial_scalar_identity (m D B _v θ η δ π ε:ℝ) :
    prefactorCenter m D B θ+3*η+(D-B+θ+δ)+(B-θ+2*η)+π+
      ((D-B+θ+δ)+ε)=m+5*η+2*δ+π+ε := by
  unfold prefactorCenter
  ring

theorem initial_scalar_le (m D B v θ η δ π ε:ℝ)(hδ:δ≤3*η) :
    prefactorCenter m D B θ+3*η+(D-B+θ+δ)+(B-θ+2*η)+π+
      ((D-B+θ+δ)+ε)≤m+11*η+π+ε := by
  rw [initial_scalar_identity m D B v θ η δ π ε]
  linarith

end SevenEighths.InverseInitialEnergyCallerClipping

end

end OAI
end OAIOriginalModule0650

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalReassembly
Source SHA256: 4d02cad9a4c3eacbca11464807eae015a151e54a7e3b25ca3f5c0b43f3c5b98e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0651


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialPhysicalReassembly
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem initialColumn_zero_common (Ψ:O→*ℂ)(j d h:O)(H:Finset ι→ℂ)
    (G U:Finset ι)(hd:¬Disjoint G U):
    initialColumn p hp hcop hg Ψ j (∏i∈G,p i) d h H U=0:=by
  obtain ⟨i,hiG,hiU⟩:=Finset.not_disjoint_iff.mp hd
  have hm:rowCoprimeMask (fun i=>Ideal.span {p i}) U (j*∏i∈G,p i)=0:=by
    have hh:∃i∈U,j*∏k∈G,p k∈Ideal.span {p i}:=
      ⟨i,hiU,Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiG) j)⟩
    simp only [rowCoprimeMask,ite_eq_left hh]
  simp only [initialColumn,hm,mul_zero,zero_mul]

theorem physicalTerm_zero_left_common (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(G E V N M:Finset ι)(h:O)(ρ:SecondRayIndex)
    (hd:¬Disjoint G (V∪N)):
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ=0:=by
  simp only [physicalTerm,initialColumn_zero_common p hp hcop hg _ _ _ _ _ _ _ hd,
    star_zero,mul_zero,zero_mul]

theorem physicalTerm_zero_right_common (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(G E V N M:Finset ι)(h:O)(ρ:SecondRayIndex)
    (hd:¬Disjoint G (V∪M)):
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ=0:=by
  simp only [physicalTerm,initialColumn_zero_common p hp hcop hg _ _ _ _ _ _ _ hd,
    mul_zero,zero_mul]

private theorem missing_residual_common (pool G V N:Finset ι)
    (hN:N∈(pool\V).powerset)(hn:N∉((pool\G)\V).powerset):¬Disjoint G (V∪N):=by
  intro hd
  apply hn
  apply Finset.mem_powerset.mpr
  intro i hi
  have hh:=Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hi)
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hh.1,
    fun hG=>Finset.disjoint_left.mp hd hG (Finset.mem_union_right V hi)⟩,hh.2⟩

theorem rectangle_restore_common
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m:ℝ)(pool G E V:Finset ι)(h:O):
    (∑N∈((pool\G)\V).powerset,∑M∈((pool\G)\V).powerset,∑ρ:SecondRayIndex,
      physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ)=
    ∑N∈(pool\V).powerset,∑M∈(pool\V).powerset,∑ρ:SecondRayIndex,
      physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ:=by
  have hs:((pool\G)\V).powerset⊆(pool\V).powerset:=
    Finset.powerset_mono.mpr (Finset.sdiff_subset_sdiff Finset.sdiff_subset (Finset.Subset.refl _))
  calc
    _=∑N∈(pool\V).powerset,∑M∈((pool\G)\V).powerset,∑ρ:SecondRayIndex,
        physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m ⟨G,E,V,N,M,h⟩ ρ:=by
      apply Finset.sum_subset hs
      intro N hN hn
      apply Finset.sum_eq_zero
      intro M hM
      apply Finset.sum_eq_zero
      intro ρ hρ
      exact physicalTerm_zero_left_common p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m G E V N M h ρ
        (missing_residual_common pool G V N hN hn)
    _=_:=by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_subset hs
      intro M hM hm
      apply Finset.sum_eq_zero
      intro ρ hρ
      exact physicalTerm_zero_right_common p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m G E V N M h ρ
        (missing_residual_common pool G V M hM hm)

def sourceCodes (pool:Finset ι)(T:Finset O):
    Finset (Σ _G:Finset ι,Σ _E:Finset ι,Finset ι×O):=
  pool.powerset.sigma (fun G=>G.powerset.sigma (fun _E=>(pool\G).powerset×ˢT))

def sourceOfCode (x:Σ _G:Finset ι,Σ _E:Finset ι,Finset ι×O):Source (ι:=ι) 0 where
  common:=x.1
  divisor:=x.2.1
  overlap:=x.2.2.1
  frequency:=x.2.2.2
  assigned:=Fin.elim0

omit [DecidableEq ι] in
theorem sourceOfCode_injective:Function.Injective (sourceOfCode (ι:=ι)):=by
  rintro ⟨G,E,V,h⟩ ⟨G',E',V',h'⟩ he
  have hG:=congrArg Source.common he
  have hE:=congrArg Source.divisor he
  have hV:=congrArg Source.overlap he
  have hh:=congrArg Source.frequency he
  dsimp only [sourceOfCode] at hG hE hV hh
  subst G';subst E';subst V';subst h'
  rfl

def finiteSource (pool:Finset ι)(T:Finset O):Finset (Source (ι:=ι) 0):=
  (sourceCodes pool T).image sourceOfCode

theorem finiteSource_sum {A:Type*}[AddCommMonoid A]
    (pool:Finset ι)(T:Finset O)(f:Source (ι:=ι) 0→A):
    (∑x∈finiteSource pool T,f x)=
      ∑G∈pool.powerset,∑E∈G.powerset,∑V∈(pool\G).powerset,∑h∈T,
        f ⟨G,E,V,h,Fin.elim0⟩:=by
  rw [finiteSource,Finset.sum_image (fun _ _ _ _ he=>sourceOfCode_injective he)]
  simp only [sourceCodes,Finset.sum_sigma,Finset.sum_product,sourceOfCode]

theorem mem_finiteSource (pool:Finset ι)(T:Finset O)(x:Source (ι:=ι) 0):
    x∈finiteSource pool T ↔ x.common⊆pool ∧ x.divisor⊆x.common ∧
      x.overlap⊆pool\x.common ∧ x.frequency∈T:=by
  constructor
  · intro hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    simpa only [sourceCodes,Finset.mem_sigma,Finset.mem_product,Finset.mem_powerset,
      sourceOfCode,and_assoc] using ha
  · rintro ⟨hG,hE,hV,hh⟩
    refine Finset.mem_image.mpr ⟨⟨x.common,x.divisor,x.overlap,x.frequency⟩,?_,?_⟩
    · simpa only [sourceCodes,Finset.mem_sigma,Finset.mem_product,Finset.mem_powerset]
        using And.intro hG (And.intro hE (And.intro hV hh))
    · apply Source.ext <;> try rfl
      funext i
      exact Fin.elim0 i

theorem finiteSource_divisor (pool:Finset ι)(T:Finset O):
    ∀x∈finiteSource pool T,x.divisor⊆x.common:=by
  intro x hx
  exact (mem_finiteSource pool T x).mp hx |>.2.1

theorem finiteSource_nonzero (pool:Finset ι)(T:Finset O)(hT:(0:O)∉T):
    ∀x∈finiteSource pool T,x.frequency≠0:=by
  intro x hx he
  exact hT (he ▸ ((mem_finiteSource pool T x).mp hx).2.2.2)

theorem finite_physical_reassembly
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool:Finset ι)(freqT:Finset O)(Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
      if Disjoint U T then ∑E∈G.powerset,∑h∈freqT,
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0)=
    physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
      (fun _=>1) Ψ j σ (fun x=>star (W x)) W Φ Z D m:=by
  unfold physicalBlock
  rw [pointSource_sum,finiteSource_sum]
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro G hG
  have hif (U T:Finset ι):
      (if Disjoint U T then ∑E∈G.powerset,∑h∈freqT,
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0)=
      ∑E∈G.powerset,∑h∈freqT,if Disjoint U T then
        initialPhysicalMode p hp hcop hg Ψ j σ W Φ Z D m G U T E h else 0:=by
    split_ifs <;> simp
  simp_rw [hif,Finset.sum_comm (s:=(pool\G).powerset) (t:=G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  simp_rw [Finset.sum_comm (s:=(pool\G).powerset) (t:=freqT)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [original_ray_common_insertion p hp hcop hg hinj]
  apply Finset.sum_congr rfl
  intro V hV
  exact rectangle_restore_common p hp hcop hg Ψ j σ (fun x=>star (W x)) W Φ Z D m pool G E V h

end SevenEighths.InverseInitialPhysicalReassembly

end

end OAI
end OAIOriginalModule0651

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalLimit
Source SHA256: 857fb5ad01429b0d61de212c092d3f6bfa7a1334d9cb2b8a3f17338acd4ca686
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0652




namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialPhysicalLimit
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialRayAttachment InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialPhysicalReassembly
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def physicalFrequency (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(h:O):ℂ:=
  ∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
    if Disjoint U T then ∑E∈G.powerset,
      initialPhysicalMode p hp hcop hg Ψ j marks W Φ Z D m G U T E h else 0

theorem physicalFrequency_finite
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool:Finset ι)(freqT:Finset O)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ):
    (∑h∈freqT,physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h)=
    physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
      (fun _=>1) Ψ j marks (fun x=>star (W x)) W Φ Z D m:=by
  rw [←finite_physical_reassembly p hp hcop hg hinj]
  unfold physicalFrequency
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd:Disjoint U T
  · simp only [hd,ite_true]
    exact Finset.sum_comm
  · simp only [hd,ite_false,Finset.sum_const_zero]

theorem physicalFrequency_hasSum
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:0<Z):
    HasSum (physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m)
      (∑G∈pool.powerset,∑U∈(pool\G).powerset,∑T∈(pool\G).powerset,
        if Disjoint U T then ∑E∈G.powerset,∑'h:O,
          initialPhysicalMode p hp hcop hg Ψ j marks W Φ Z D m G U T E h else 0):=by
  unfold physicalFrequency
  apply hasSum_sum
  intro G hG
  apply hasSum_sum
  intro U hU
  apply hasSum_sum
  intro T hT
  by_cases hd:Disjoint U T
  · simp only [hd,ite_true]
    apply hasSum_sum
    intro E hE
    exact (initialPhysicalMode_summable p hp hcop hg hinj hc hpr Ψ j marks W Φ hZ D m
      G U T E
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hU) Finset.disjoint_sdiff)
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) Finset.disjoint_sdiff) hd).hasSum
  · simpa only [hd,ite_false] using (hasSum_zero : HasSum (fun _ : O=>(0:ℂ)) 0)

theorem original_input_zero_nonzero
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:0<Z):
    (∑'u:O,Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg pool Ψ j 1 1
        (initialTest p marks W Z D) u‖^2:ℝ))=
    physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m 0+
      ∑'h:O,if h=0 then 0 else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h:=by
  rw [initial_input_physical p hp hcop hg hinj hc hpr pool Ψ j marks W Φ hZ D m]
  have hs:=physicalFrequency_hasSum p hp hcop hg hinj hc hpr pool Ψ j marks W Φ Z D m hZ
  rw [←hs.tsum_eq]
  exact hs.summable.tsum_eq_add_tsum_ite 0

theorem nonzero_frequency_norm_le
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(marks:Finset ι→ℂ)
    (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m B:ℝ)(hZ:0<Z)
    (hfinite:∀freqT:Finset O,(0:O)∉freqT→
      ‖physicalBlock p hp hcop hg (pointSource pool (finiteSource pool freqT))
        (fun _=>1) Ψ j marks (fun x=>star (W x)) W Φ Z D m‖≤B):
    ‖∑'h:O,if h=0 then 0 else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h‖≤B:=by
  have hs:=physicalFrequency_hasSum p hp hcop hg hinj hc hpr pool Ψ j marks W Φ Z D m hZ
  have hs0:Summable (fun h:O=>if h=0 then (0:ℂ) else
      physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h):=by
    apply (hs.summable.indicator {h:O|h≠0}).congr
    intro h
    by_cases he:h=0 <;> simp [Set.indicator,he]
  apply InverseInitialHighFrequencyTail.norm_tsum_of_finite_bound _ hs0
  intro T
  let freqT:=T.filter (fun h:O=>h≠0)
  have hzero:(0:O)∉freqT:=by simp [freqT]
  have he:(∑h∈T,if h=0 then (0:ℂ) else physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h)=
      ∑h∈freqT,physicalFrequency p hp hcop hg pool Ψ j marks W Φ Z D m h:=by
    simp only [freqT,Finset.sum_filter,ite_not]
  rw [he,physicalFrequency_finite p hp hcop hg hinj]
  exact hfinite freqT hzero

end SevenEighths.InverseInitialPhysicalLimit

end

end OAI
end OAIOriginalModule0652

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialRetainedSupport
Source SHA256: ee9f53d0c5774535e1f95261cc2c5ffacddda6db2bddfed0ac4dd6604a4de083
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0653


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialRetainedSupport
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT CompletedGauss
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialKernelBridge SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,goodLambda∉Ideal.span {p i})

theorem live_cutoffs (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m:ℝ)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    W₁ (coordinates p x 0*coordinates p x 2*coordinates p x 4/Z^D)≠0 ∧
    W₂ (coordinates p x 0*coordinates p x 2*coordinates p x 5/Z^D)≠0 := by
  rw [physicalTerm_extracted p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ] at hne
  have hk:= (mul_ne_zero_iff.mp hne).2
  unfold physicalKernel at hk
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).1).2,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hk).1).2⟩

theorem live_whole_columns (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0<Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0*coordinates p x 2*coordinates p x 4≤b*Z^D ∧
    coordinates p x 0*coordinates p x 2*coordinates p x 5≤b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_cutoffs p hp hcop hg hpr Ψ j σ W₁ W₂ Φ Z D m x hx ρ hne
  exact ⟨(div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₁ h₁),
    (div_le_iff₀ (Real.rpow_pos_of_pos hZ D)).mp (hs₂ h₂)⟩

include hp in
omit [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in
theorem ideal_coordinates_one (x:Point ι):
    1≤coordinates p x 0 ∧ 1≤coordinates p x 1 ∧ 1≤coordinates p x 2 ∧
    1≤coordinates p x 4 ∧ 1≤coordinates p x 5 := by
  have hi (S:Finset ι):(1:ℝ)≤((sourceIdeal p S).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp S))
  exact ⟨hi _,hi _,hi _,hi _,hi _⟩

theorem live_ideal_caps (hpr:∀i,goodLambda^2∣p i-1)
    (Ψ:O→*ℂ)(j:O)(σ:Finset ι→ℂ)(W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (Z D m b:ℝ)(hZ:0<Z)(hs₁:Function.support W₁⊆Set.Iic b)
    (hs₂:Function.support W₂⊆Set.Iic b)(x:Point ι)(hx:Valid x)(ρ:SecondRayIndex)
    (hne:physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ≠0):
    coordinates p x 0≤b*Z^D ∧ coordinates p x 1≤b*Z^D ∧
    coordinates p x 2≤b*Z^D ∧ coordinates p x 4≤b*Z^D ∧
    coordinates p x 5≤b*Z^D := by
  obtain ⟨h₁,h₂⟩:=live_whole_columns p hp hcop hg hpr Ψ j σ W₁ W₂ Φ
    Z D m b hZ hs₁ hs₂ x hx ρ hne
  obtain ⟨hC,hd,hs,hn₁,hn₂⟩:=ideal_coordinates_one p hp x
  have hpair:1≤coordinates p x 0*coordinates p x 2:=by nlinarith
  have hcp:coordinates p x 0≤coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_right (by linarith) hs
  have hsp:coordinates p x 2≤coordinates p x 0*coordinates p x 2:=
    le_mul_of_one_le_left (by linarith) hC
  have hbig:coordinates p x 0*coordinates p x 2≤b*Z^D:=
    (le_mul_of_one_le_right (by positivity) hn₁).trans h₁
  have hdiv:coordinates p x 1≤coordinates p x 0:=by
    change ((sourceIdeal p x.divisor).absNorm:ℝ)≤(sourceIdeal p x.common).absNorm
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (sourceIdeal_ne_zero p hp _)))
      (map_dvd Ideal.absNorm (sourceIdeal_dvd p _ _ hx.divisor_subset))
  exact ⟨hcp.trans hbig,hdiv.trans (hcp.trans hbig),hsp.trans hbig,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₁,
    (le_mul_of_one_le_left (by linarith) hpair).trans h₂⟩

end SevenEighths.InverseInitialRetainedSupport

end

end OAI
end OAIOriginalModule0653

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.SecondPrincipalCaller
Source SHA256: d57b2ab59cecdc4dba9bc65ed3e6e71c0dddd7dd42109d8336c87133058ec232
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0654



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseSecondPrincipalCaller
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight
open InverseMoment InversePrincipalEnergy RayFourExpansion
local notation "Eis" => ActualEisensteinCubic.O

def principalWindow (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t)
  else uniformTwistedSchwartz om a b ha hs (om.smooth ⊤) t

theorem principalWindow_apply (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    principalWindow om a b ha hs negative t x =
      if negative then normTwistedSource (fun y => star (om y)) (-t) x
      else normTwistedSource om t x := by
  cases negative <;> simp only [principalWindow,Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,
    star_mul,logPhase_conjugate,mul_comm]

theorem principalWindow_norm (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t x : ℝ) :
    ‖principalWindow om a b ha hs negative t x‖=‖om x‖ := by
  rw [principalWindow_apply]
  cases negative <;> simp [normTwistedSource,logPhase_norm]

theorem principalWindow_support (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    Function.support (principalWindow om a b ha hs negative t) = Function.support om := by
  ext x
  change (_≠0) ↔ (_≠0)
  rw [←norm_ne_zero_iff,principalWindow_norm,norm_ne_zero_iff]

theorem principalWindow_seminorm_zero (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (negative : Bool) (t : ℝ) :
    SchwartzMap.seminorm ℝ 0 0 (principalWindow om a b ha hs negative t)=
      SchwartzMap.seminorm ℝ 0 0 om := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ om x
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (apply_nonneg _ _)
    intro x
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero,principalWindow_norm]
      using SchwartzMap.norm_le_seminorm ℝ (principalWindow om a b ha hs negative t) x

theorem principalWindow_upper (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs : Function.support om ⊆ Set.Icc a b) (M : ℝ) (hb : b≤Real.exp M)
    (negative : Bool) (t x : ℝ) (hx : principalWindow om a b ha hs negative t x≠0) :
    x≤Real.exp M := by
  have hmem : x∈Function.support om := by
    rw [←principalWindow_support om a b ha hs negative t]
    exact hx
  exact (hs hmem).2.trans hb

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) (hp : ∀ i,p i≠0)

include hp in

theorem whole_columnLog (D U : Finset ι) (hDU : Disjoint D U) (X : ℝ) :
    columnLog p (primeProductNorm p D*X) (D∪U)=Real.log (primeProductNorm p U/X) := by
  unfold columnLog
  rw [primeProductNorm_union p D U hDU,
    mul_div_mul_left _ _ (primeProductNorm_pos p hp D).ne']

omit [DecidableEq σ] in

theorem primeMark_union_of_lists_disjoint (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D) :
    primeMark slots lists coeff (D∪U)=primeMark slots lists coeff U := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  have hh := Finset.disjoint_left.mp (hD i hi) hk
  simp only [Finset.mem_union,hh,false_or]

include hp in

theorem firstCoreTest_markedRadial (slots : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (D U : Finset ι) (hDU : Disjoint D U)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) :
    firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D U =
    markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X U := by
  have ht : ∀ y : ℝ,logPhase (-t) (-y)=logPhase t y := by
    intro y
    unfold logPhase
    congr 1
    push_cast
    ring
  simp only [firstCoreTest,primeMark_union_of_lists_disjoint slots lists coeff D U hD,
    whole_columnLog p hp D U hDU X,ht,
    Real.exp_log (div_pos (primeProductNorm_pos p hp U) hX),
    markedRadial,Finset.empty_union,principalWindow]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    conjugateProfile_apply,uniformTwistedSchwartz_apply,normTwistedSource,star_mul] <;> ring

variable [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem secondInputCoefficient_overlap_zero
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (D U : Finset ι)
    (hDU : ¬Disjoint D U) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d H U=0 := by
  rw [secondInputCoefficient_fixed_mask (p := p) (hg := hg),commonProduct_mask p hg hinj]
  split_ifs with h
  · exact (hDU h.symm).elim
  · exact zero_mul _

include hp in

theorem firstCoreTest_coefficient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ) (D U : Finset ι)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (negative : Bool) (X t : ℝ) (hX : 0<X) (Ψ : Eis→*ℂ) (m c d : Eis) :
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) U =
    secondInputCoefficient p hg Ψ (m*∏ i∈D,p i) c d
      (markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X) U := by
  by_cases hd : Disjoint D U
  · unfold secondInputCoefficient
    rw [firstCoreTest_markedRadial p hp slots lists coeff D U hd hD om a b ha hs negative X t hX]
  · rw [secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd,
      secondInputCoefficient_overlap_zero p hg hinj Ψ m c d _ D U hd]

omit [DecidableEq ι] in

theorem input_diagonal (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (U : Finset ι) :
    (‖secondInputCoefficient p hg Ψ m c d (fun _=>1) U‖^2 : ℝ) * star (H U) * H U =
      ((‖secondInputCoefficient p hg Ψ m c d H U‖^2 : ℝ) : ℂ) := by
  have he : secondInputCoefficient p hg Ψ m c d H U =
      secondInputCoefficient p hg Ψ m c d (fun _=>1) U * H U := by
    simp only [secondInputCoefficient,mul_one]
  have hh : star (H U)*H U=((‖H U‖^2 : ℝ):ℂ) := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  rw [he,norm_mul,mul_pow,Complex.ofReal_mul,mul_assoc,hh]

omit [DecidableEq ι] in
theorem input_norm_product (Ψ : Eis→*ℂ) (m c d : Eis) (H : Finset ι→ℂ) (U : Finset ι) :
    (‖secondInputCoefficient p hg Ψ m c d (fun _=>1) U‖^2 : ℝ) * ‖H U‖^2 =
      ‖secondInputCoefficient p hg Ψ m c d H U‖^2 := by
  simp only [secondInputCoefficient,mul_one,norm_mul,mul_pow]

omit [DecidableEq ι] in

theorem zero_congr_input (F : Finset ι) (Ψ : Eis→*ℂ) (m c d : Eis)
    (H₁ H₂ : Finset ι→ℂ)
    (he : ∀ U,secondInputCoefficient p hg Ψ m c d H₁ U=
      secondInputCoefficient p hg Ψ m c d H₂ U)
    (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (K : Finset ι→Finset ι→Finset Eis) :
    truncatedSecondZero p hg F Ψ m c d H₁ W Y K=
      truncatedSecondZero p hg F Ψ m c d H₂ W Y K := by
  simp only [truncatedSecondZero,input_diagonal,he]

include hp in

theorem restoration_congr_input
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (Ψ : Eis→*ℂ) (m c d : Eis) (H₁ H₂ : Finset ι→ℂ)
    (he : ∀ U,secondInputCoefficient p hg Ψ m c d H₁ U=
      secondInputCoefficient p hg Ψ m c d H₂ U)
    (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (θ : Finset ι→Finset ι→Eis→ℂ) :
    principalRestoration p hg hinj hp F Ψ m c d H₁ W Y θ=
      principalRestoration p hg hinj hp F Ψ m c d H₂ W Y θ := by
  unfold principalRestoration
  apply Finset.sum_congr rfl
  intro G hG
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro k
  congr 1
  simp only [restorationTerm_eq,←Complex.ofReal_mul,input_norm_product,he]

include hp in

theorem firstCoreInputRow_principal_test
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t : ℝ) (hX : 0<X) (c d : Eis) (r : FirstCoreIndex) (z : Eis) :
    firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m (primeMark slots lists coeff)
      (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z =
    inputConjugateRow p hg F (firstCoreTwist negative χ Ψ r)
      ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i) (c*jLabel p B v ε₁ ε₂) d
      (markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X)
      (if negative then -z else z) := by
  rw [firstCoreInputRow_fixed_pool p hg hinj]
  unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
  apply Finset.sum_congr rfl
  intro U hU
  rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]

include hp in

theorem firstFreshSecondPoisson_markedRadial
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (c d : Eis) (r : FirstCoreIndex) :
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    let Ψ₀ := firstCoreTwist negative χ Ψ r
    let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
    let c₀ := c*jLabel p B v ε₁ ε₂
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (primeMark slots lists coeff) om X c d r t Y =
      ∑ G∈F.powerset,∑ U∈(F\G).powerset,∑ V∈(F\G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ₀ m₀ c₀ d H₀ G U V *
          maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0 := by
  intro H₀ Ψ₀ m₀ c₀
  let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) negative (-t) D
  have he (z : Eis) : inputConjugateRow p hg F Ψ₀ m₀ c₀ d H z=
      inputConjugateRow p hg F Ψ₀ m₀ c₀ d H₀ z := by
    unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
    apply Finset.sum_congr rfl
    intro U hU
    rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]
  calc
    _ = ∑' z : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/Y)*
        (‖inputConjugateRow p hg F Ψ₀ m₀ c₀ d H z‖^2 : ℝ) := by
      rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
        (primeMark slots lists coeff) om X c d r t Y hY]
      exact (inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H
        rowMajorant Y hY).symm
    _ = ∑' z : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/Y)*
        (‖inputConjugateRow p hg F Ψ₀ m₀ c₀ d H₀ z‖^2 : ℝ) := by simp_rw [he]
    _ = _ := inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H₀
      rowMajorant Y hY

theorem residual_lists_pairwise (slots J : Finset σ) (lists : σ→Finset ι) (A D : Finset ι)
    (h : (slots : Set σ).PairwiseDisjoint lists) :
    ((slots\J : Finset σ) : Set σ).PairwiseDisjoint (fun i=>lists i\(A∪D)) := by
  intro i hi j hj hij
  simp only [Finset.mem_coe,Finset.mem_sdiff] at hi hj
  exact (h hi.1 hj.1 hij).mono
    Finset.sdiff_subset Finset.sdiff_subset

omit [DecidableEq σ] in
theorem residual_lists_avoid (lists : σ→Finset ι) (A D : Finset ι) (i : σ) :
    Disjoint (lists i\(A∪D)) D := by
  apply Finset.disjoint_left.mpr
  intro k hk hkd
  exact (Finset.mem_sdiff.mp hk).2 (Finset.mem_union_right A hkd)

theorem residual_coeff_bound (slots J : Finset σ) (lists : σ→Finset ι)
    (coeff : σ→ι→ℂ) (A D : Finset ι)
    (h : ∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) :
    ∀ i∈slots\J,∀ k∈lists i\(A∪D),‖coeff i k‖≤1 := by
  intro i hi k hk
  exact h i (Finset.mem_sdiff.mp hi).1 k (Finset.mem_sdiff.mp hk).1

end Arithmetic

theorem firstCore_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈slots,Disjoint (lists i) D) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y R : ℝ),b≤Real.exp M → 0<X → 1≤Y → 0≤R →
      let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (secondPhysicalMask p d R)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := physical_child_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists coeff hslots hcoeff F D B v ε₁ ε₂ hD
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR H Ψ₀ m₀ c₀
  let V := principalWindow om a b ha hs negative t
  let H₀ := markedRadial p slots lists coeff ∅ V X
  have he (U : Finset ι) : secondInputCoefficient p hg Ψ₀ m₀ c₀ d H U=
      secondInputCoefficient p hg Ψ₀ m₀ c₀ d H₀ U :=
    firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX Ψ₀
      (m*b0Label p B v ε₁ ε₂) c₀ d
  rw [zero_congr_input p hg F Ψ₀ m₀ c₀ d H H₀ he,
    restoration_congr_input p hp hg hinj F Ψ₀ m₀ c₀ d H H₀ he]
  have hbnd := hbound p hp hg hinj hcop slots lists coeff hslots hcoeff ∅ F Ψ₀
    (fun z=>(firstCoreTwist_norm_le negative χ Ψ r z).trans (hΨ z)) m₀ c₀ d hd V W X M Y R
    hX hY hR (principalWindow_upper om a b ha hs M hb negative t)
  simpa only [H₀,V,Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero] using hbnd

theorem priority_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots J : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B A : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y R : ℝ),b≤Real.exp M → 0<X → 1≤Y → 0≤R →
      let H := firstCoreTest (primeMark (slots\J) (fun i=>lists i\(A∪D)) coeff)
        (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (secondPhysicalCutoff p d R)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (secondPhysicalMask p d R)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := firstCore_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots J lists coeff hslots hcoeff F D B A v ε₁ ε₂
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR
  exact hbound p hp hg hinj hcop (slots\J) (fun i=>lists i\(A∪D)) coeff
    (residual_lists_pairwise slots J lists A D hslots)
    (residual_coeff_bound slots J lists coeff A D hcoeff) F D B v ε₁ ε₂
    (fun i _=>residual_lists_avoid lists A D i) negative χ Ψ hΨ m c d hd r om W a b ha hs
    M t X Y R hb hX hY hR

end SevenEighths.InverseSecondPrincipalCaller

end

end OAI
end OAIOriginalModule0654

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondMarkedTail
Source SHA256: 0d7714df94e0738fe782d42e90131b0219eff84ee9d2fad7a6ad2f4e02424d87
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0655



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InversePrincipalEnergy InverseSecondPrincipalCaller
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem marked_radial_uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → O) (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A : Finset ι) (V : 𝓢(ℝ,ℂ)) (X M : ℝ), 0 < X →
      (∀ u, V u ≠ 0 → u ≤ Real.exp M) →
      ∀ U, ‖markedRadial p slots lists a A V X U‖ ≤
        (2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * SchwartzMap.seminorm ℝ 0 0 V := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_extracted_bound ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha A V X M hX hV U
  by_cases hz : V (primeProductNorm p U/X) = 0
  · simp only [markedRadial,hz,mul_zero,norm_zero]
    positivity
  · have hn : primeProductNorm p U ≤ X*Real.exp M := by
      simpa only [mul_comm] using (div_le_iff₀ hX).mp (hV _ hz)
    have hn0 : 0 ≤ primeProductNorm p U := (primeProductNorm_pos p hp U).le
    rw [markedRadial,norm_mul]
    apply (mul_le_mul (hmark p hp hcop slots lists a hslots ha A U)
      (V.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)).trans
    gcongr

theorem full_marked_second_tail (ε : ℝ) (hε : 0 < ε) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct Cm : ℝ), 0 < Ct ∧ 0 < Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0)
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, ∀ k ∈ lists i, ‖a i k‖ ≤ 1) →
      ∀ (A : Finset ι) (V W : 𝓢(ℝ,ℂ)) (X M Y H R : ℝ),
      0 < X → 0 < Y → 0 ≤ H → 1 ≤ X*Real.exp M →
      (∀ u, V u ≠ 0 → u ≤ Real.exp M) →
      wholeSecondRadius d (X*Real.exp M) Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d (markedRadial p slots lists a A V X) W Y
        (fun _ E => childFrequencyBall (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*(X*Real.exp M))^4 *
          (((2:ℝ)^A.card * Cm * (X*Real.exp M)^ε * SchwartzMap.seminorm ℝ 0 0 V)^2 *
            (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
              (1+(X*Real.exp M)^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_whole_column_tail order
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F Ψ hΨ m c d hd slots lists a hslots ha A V W X M Y H R hX hY hH hL hV hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d hd (markedRadial p slots lists a A V X) W
    _ Y H (X*Real.exp M) R (by positivity) hY hH hL
  · exact hmark p hp hcop slots lists a hslots ha A V X M hX hV
  · exact markedRadial_support p slots lists a A V X M hX hV
  · exact hR

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0655

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.SecondProfileUniform
Source SHA256: a0ba1c87f05fa70e796c2a06a9e5cbfecfa7eb2ef97fbc3e939c268e430982f1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0656



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment
open SevenEighths.InverseInitialProfile
open SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseSecondProfileUniform

def rooted (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  InverseClippingProfiles.rootSchwartz g M 0 1 0 a 0 zero_lt_one (by simp) hg

@[simp] theorem rooted_apply (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (y : ℝ) :
    rooted g M a hg y = (Real.exp (a*y) : ℂ)*g y := by
  simp [rooted, InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]

theorem rooted_support (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) :
    Function.support (rooted g M a hg) ⊆ Set.Icc (-M) M := by
  intro y hy
  exact hg (by simpa using hy)

def translated (g : 𝓢(ℝ, ℂ)) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ (-ρ) g

@[simp] theorem translated_apply (g : 𝓢(ℝ, ℂ)) (ρ y : ℝ) :
    translated g ρ y = g (y+ρ) := by simp [translated]

theorem fourier_translated (g : 𝓢(ℝ, ℂ)) (ρ t : ℝ) :
    (𝓕 (translated g ρ)) t = logPhase t ρ * (𝓕 g) t := by
  rw [SchwartzMap.fourier_coe]
  have he : (translated g ρ : ℝ → ℂ) = fun y => g (y+ρ) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translate, ← SchwartzMap.fourier_coe]

def normalization (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) : ℝ :=
  Real.exp (-6*L - ∑ i, InverseClippingProfiles.secondBalancedSlope i*ρ i +
    (Real.log c₁+Real.log c₂)/2)

def density (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    fullProfileDensity (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem density_formula (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) :
    density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p =
      (normalization ρ c₁ c₂ L : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 * (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) *
        (∏ i, logPhase (p.2 i) (ρ i) * (𝓕 (g i)) (p.2 i)) := by
  simp only [density, fullProfileDensity, tripleCoefficient, coordinateDensity,
    fourier_translated, fourier_clippedTwist]
  ring

private theorem fourier_twist (g : 𝓢(ℝ, ℂ)) (θ t : ℝ) :
    (𝓕 (frequencyTwist g θ)) t = (𝓕 g) (t-θ) := by
  rw [SchwartzMap.fourier_coe]
  have he : (frequencyTwist g θ : ℝ → ℂ) = fun y => logPhase θ y * g y := by
    ext y
    exact frequencyTwist_apply g θ y
  rw [he, InverseClippingProfiles.fourier_phase_shift, ← SchwartzMap.fourier_coe]

theorem density_norm (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) :
    ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖ = normalization ρ c₁ c₂ L *
      ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖ := by
  rw [density_formula]
  simp only [norm_mul, norm_prod, sourceDensity_norm, logPhase_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, normalization,
    abs_of_pos (Real.exp_pos _), twistedFullDensity, fullProfileDensity,
    tripleCoefficient, coordinateDensity, fourier_twist]
  ring

theorem density_joint_measurable (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun z : ((Fin 6 → ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × ℝ) × Ambient (Fin 6) =>
      density g g₁ g₂ b₃ z.1.1 z.1.2.1.1 z.1.2.1.2 z.1.2.2.1.1 z.1.2.2.1.2 z.1.2.2.2 z.2) := by
  simp_rw [density_formula]
  apply Measurable.stronglyMeasurable
  unfold normalization sourceDensity logPhase
  have h1 := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 := b₃.continuous.measurable
  have hu (i : Fin 6) := (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have he := Complex.continuous_exp.measurable
  fun_prop

theorem normalization_bound (B : Fin 6 → ℝ) (b : ℝ)
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (hρ : ∀ i, |ρ i| ≤ B i)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁b : c₁ ≤ b) (hc₂b : c₂ ≤ b) (hL : 0 ≤ L) :
    normalization ρ c₁ c₂ L ≤
      Real.exp ((∑ i, |InverseClippingProfiles.secondBalancedSlope i| *B i)+Real.log b) := by
  unfold normalization
  apply Real.exp_le_exp.mpr
  have hs : -(∑ i, InverseClippingProfiles.secondBalancedSlope i*ρ i) ≤
      ∑ i, |InverseClippingProfiles.secondBalancedSlope i| *B i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |InverseClippingProfiles.secondBalancedSlope i*ρ i| := neg_le_abs _
      _ = |InverseClippingProfiles.secondBalancedSlope i| *|ρ i| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hρ i) (abs_nonneg _)
  have h1 := Real.log_le_log hc₁ hc₁b
  have h2 := Real.log_le_log hc₂ hc₂b
  linarith

theorem density_weighted_integrable (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) := by
  simp_rw [density_norm]
  convert (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable g
    (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ J).const_mul
      (normalization ρ c₁ c₂ L) using 1
  funext p
  unfold twistedFullDensity
  ring

private theorem radial_common_box (Φ : 𝓢(ℝ, ℂ)) (M : Fin 6 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (V : Fin 6 → ℝ → ℂ), (∀ i y, V i y ≠ 0 → |y| ≤ M i) →
        ∀ y : Fin 6 → ℝ,
        (∏ i, V i (y i))*paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)) =
          ∫ t : ℝ, (∏ i, V i (y i)*logPhase t (secondKernelSlope i*y i))*b₃ t) ∧
      (1+R)^A * (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) ≤ C := by
  let box : Fin 6 → ℝ → ℂ := fun i y => if |y| ≤ M i then 1 else 0
  have hb : ∀ i y, box i y ≠ 0 → |y| ≤ M i := by
    intro i y h
    simpa [box] using h
  obtain ⟨C,hC,hs⟩ := paperRadialFourier_log_separation_envelope Φ box
    secondKernelSlope M hM hb A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,he,_,hm,_⟩ := hs R hR
  refine ⟨b₃,?_,hm⟩
  intro V hV y
  simp only [Finset.prod_mul_distrib]
  by_cases hz : (∏ i, V i (y i)) = 0
  · simp [hz]
  · have hall (i : Fin 6) : V i (y i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
    have hbox (i : Fin 6) : box i (y i) = 1 := by simp [box, hV i _ (hall i)]
    have h := he y
    simp only [hbox, one_mul, Finset.prod_const_one] at h
    rw [h, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring

theorem translated_box (g : 𝓢(ℝ, ℂ)) (M B ρ : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (hρ : |ρ| ≤ B)
    {y : ℝ} (hy : translated g ρ y ≠ 0) : |y| ≤ M+B := by
  have h := hg (show g (y+ρ) ≠ 0 from by simpa only [translated_apply] using hy)
  have hr := abs_le.mp hρ
  apply abs_le.mpr
  constructor <;> linarith [h.1,h.2,hr.1,hr.2]

theorem density_weighted_integral (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Ambient (Fin 6), ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) = normalization ρ c₁ c₂ L *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₁ θ₁)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₂ θ₂)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
        (∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖) := by
  simp_rw [density_norm]
  have he (p : Ambient (Fin 6)) :
      ambientWeight J p * (normalization ρ c₁ c₂ L *
        ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖) =
      normalization ρ c₁ c₂ L * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (frequencyTwist g₁ θ₁))
          (𝓕 (frequencyTwist g₂ θ₂)) b₃ p‖) := by
    unfold ambientWeight tripleHeight coordinateHeight twistedFullDensity
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  ring

def profile (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    ((∏ i, translated (g i) (ρ i) (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

def requiredOuterOrder (J : ℕ) : ℕ := J+2*InverseClippingProfiles.momentOrder J

theorem common_measure (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hg : ∀ i, Function.support (g i) ⊆ Set.Icc (-M i) (M i)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 0 < c₁ → 0 < c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 6 → ℝ, profile g g₁ g₂ Φ ρ c₁ c₂ θ₁ θ₂ R L y =
        ∫ p : Ambient (Fin 6), density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 6), ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  obtain ⟨C₃,hC₃,hsep⟩ := radial_common_box Φ (fun i => M i+B i)
    (fun i => add_nonneg (hM i) (hB i)) A J
  obtain ⟨C₁,hC₁,h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂,hC₂,h₂⟩ := frequencyTwist_fourier_moment J g₂
  let D := ∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖
  let E := Real.exp ((∑ i, |InverseClippingProfiles.secondBalancedSlope i| * B i)+Real.log b)
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun _ => by positivity))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨E*C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃,he,hm⟩ := hsep R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  refine ⟨?_, density_weighted_integrable _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hb : ∀ i z, translated (g i) (ρ i) z ≠ 0 → |z| ≤ M i+B i :=
      fun i z hz => translated_box (g i) (M i) (B i) (ρ i) (hg i) (hρ i) hz
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (fun i => translated (g i) (ρ i)) secondLeftSlope secondRightSlope secondKernelSlope
      R b₃ (he _ hb) y
    have habs := profile_integral_coordinate_absorption (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      secondLeftSlope secondRightSlope secondKernelSlope y
    simp only [profileMode] at habs
    unfold profile
    rw [hid, habs, ← full_density_mode_fubini, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold density
    ring
  · rw [density_weighted_integral]
    have h12 := mul_le_mul (h₁ θ₁) (h₂ θ₂)
      (integral_nonneg (fun _ => by positivity)) (by positivity)
    have h123 := mul_le_mul h12 hm (by positivity) (by positivity)
    have hd := mul_le_mul_of_nonneg_right h123 hD
    have hn := normalization_bound B b ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
    have hh := mul_le_mul hn hd (by positivity) hE
    convert hh using 1 <;>
      (dsimp only [InverseClippingProfiles.momentOrder, E, D]; ring)

theorem balanced_exponential_identity (ρ y : Fin 6 → ℝ) (c₁ c₂ L : ℝ) :
    normalization ρ c₁ c₂ L *
      (∏ i, Real.exp (InverseClippingProfiles.secondBalancedSlope i*(y i+ρ i))) *
      Real.exp (-(1/2:ℝ)*((∑ i, secondLeftSlope i*y i)+Real.log c₁)) *
      Real.exp (-(1/2:ℝ)*((∑ i, secondRightSlope i*y i)+Real.log c₂)) =
      Real.exp (-6*L)*Real.exp (InverseClippingProfiles.secondRootExponent y) := by
  rw [normalization, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [InverseClippingProfiles.secondBalancedSlope,
    InverseClippingProfiles.secondRootExponent, secondLeftSlope, secondRightSlope,
    Fin.sum_univ_succ]
  ring

def positiveSource (g : 𝓢(ℝ, ℂ)) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x)*g (Real.log x+Real.log c)

theorem positiveSource_logSchwartz (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (θ : ℝ) :
    positiveSource (CubicReflectionKernel.logSchwartz W a b ha hs hW) c θ x =
      clippedSource W c θ x := by
  simp only [positiveSource, CubicReflectionKernel.logSchwartz_apply,
    Real.exp_add, Real.exp_log hc, Real.exp_log hx, clippedSource]
  rw [mul_comm x c]

theorem balanced_profile_identity
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M : Fin 6 → ℝ) (m₁ m₂ : ℝ)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂)
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) :
    profile (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
      (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
      Φ ρ c₁ c₂ θ₁ θ₂ R L y =
      (Real.exp (-6*L) : ℂ) * secondPoissonProfile
        (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
        Φ (fun i y => U i (y+ρ i)) R y := by
  have he := congrArg (fun x : ℝ => (x : ℂ)) (balanced_exponential_identity ρ y c₁ c₂ L)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at he
  unfold profile secondPoissonProfile
  rw [InverseClippingProfiles.secondRootWindows_prod]
  simp only [translated_apply, clippedTwist_apply, rooted_apply, positiveSource, Real.log_exp,
    Finset.prod_mul_distrib]
  linear_combination
    (∏ i, U i (y i+ρ i)) * logPhase θ₁ (∑ i, secondLeftSlope i*y i) *
    g₁ ((∑ i, secondLeftSlope i*y i)+Real.log c₁) *
    logPhase θ₂ (∑ i, secondRightSlope i*y i) *
    g₂ ((∑ i, secondRightSlope i*y i)+Real.log c₂) *
    paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)) * he

theorem second_profile_common_measure
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 6 → ℝ,
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 6) => ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 6), ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := common_measure
    (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
    (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂) Φ M B b hM hB
    (fun i => rooted_support _ _ _ _) A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,hb₃⟩ := hs R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ (zero_lt_one.trans_le hc₁)
    (zero_lt_one.trans_le hc₂) hc₁b hc₂b hL
  refine ⟨?_,h.2⟩
  intro y
  rw [← balanced_profile_identity U g₁ g₂ Φ M m₁ m₂ hU h₁ h₂]
  exact h.1 y

def densityTower {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (z : Ambient ι × Ambient (Fin 6)) : ℂ :=
  fullProfileDensity outer b₁ b₂ b₃ z.1 *
    density g g₁ g₂ c₃ ρ c₁ c₂ (inheritedLeft i z.1) (inheritedRight j z.1) L z.2

theorem densityTower_joint_measurable {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) :
    StronglyMeasurable (densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L) := by
  unfold densityTower
  apply StronglyMeasurable.mul
  · exact ((InverseAmbientProfileTower.fullProfileDensity_continuous outer b₁ b₂ b₃).comp
      continuous_fst).stronglyMeasurable
  · have hm : Measurable (fun z : Ambient ι × Ambient (Fin 6) =>
        ((ρ,(c₁,c₂),(inheritedLeft i z.1,inheritedRight j z.1),L),z.2)) := by
      unfold inheritedLeft inheritedRight
      fun_prop
    exact (density_joint_measurable g g₁ g₂ c₃).comp_measurable hm

theorem densityTower_norm {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (z : Ambient ι × Ambient (Fin 6)) :
    ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖ =
      normalization ρ c₁ c₂ L *
        ‖InverseAmbientProfileTower.towerDensity i j outer b₁ b₂ b₃ g g₁ g₂ c₃ z‖ := by
  simp only [densityTower, InverseAmbientProfileTower.towerDensity, norm_mul, density_norm]
  ring

theorem densityTower_weighted_integrable {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) (J : ℕ) :
    Integrable (fun z : Ambient ι × Ambient (Fin 6) =>
      ambientWeight J z.1 * ambientWeight J z.2 *
        ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖) := by
  obtain ⟨C,hC,h⟩ := InverseAmbientProfileTower.towerDensity_weighted (ι := ι) J g g₁ g₂ c₃
  convert (h i j outer b₁ b₂ b₃).1.const_mul (normalization ρ c₁ c₂ L) using 1
  funext z
  rw [densityTower_norm]
  ring

private theorem tower_bound_from_inner {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L C R : ℝ) (hC : 0 ≤ C) (_hR : 0 < R) (A J : ℕ)
    (hb : ∀ θ₁ θ₂ : ℝ, (1+R)^A * (∫ q : Ambient (Fin 6), ambientWeight J q *
        ‖density g g₁ g₂ c₃ ρ c₁ c₂ θ₁ θ₂ L q‖) ≤
      C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
        (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J))) :
    (1+R)^A * (∫ z : Ambient ι × Ambient (Fin 6),
      ambientWeight J z.1 * ambientWeight J z.2 *
        ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖) ≤
      C * (∫ p : Ambient ι, ambientWeight (requiredOuterOrder J) p *
        ‖fullProfileDensity outer b₁ b₂ b₃ p‖) := by
  let f := fun z : Ambient ι × Ambient (Fin 6) =>
    ambientWeight J z.1 * ambientWeight J z.2 *
      ‖densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z‖
  have hi : Integrable f := densityTower_weighted_integrable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L J
  have hi' : Integrable (fun z : Ambient ι × Ambient (Fin 6) => (1+R)^A*f z) := hi.const_mul _
  have hout := (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable
    outer b₁ b₂ b₃ (requiredOuterOrder J)).const_mul C
  change (1+R)^A*(∫ z, f z) ≤ _
  rw [← integral_const_mul]
  rw [show (∫ z : Ambient ι × Ambient (Fin 6), (1+R)^A*f z) =
      ∫ p : Ambient ι, ∫ q : Ambient (Fin 6), (1+R)^A*f (p,q) by
    simpa only [Measure.volume_eq_prod] using integral_prod _ hi']
  rw [← integral_const_mul]
  have hip : Integrable (fun z : Ambient ι × Ambient (Fin 6) => (1+R)^A*f z) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hi'
  apply integral_mono hip.integral_prod_left hout
  intro p
  dsimp only
  have he : (∫ q : Ambient (Fin 6), (1+R)^A*f (p,q)) =
      ambientWeight J p * ‖fullProfileDensity outer b₁ b₂ b₃ p‖ *
        ((1+R)^A * ∫ q : Ambient (Fin 6), ambientWeight J q *
          ‖density g g₁ g₂ c₃ ρ c₁ c₂ (inheritedLeft i p) (inheritedRight j p) L q‖) := by
    simp only [f, densityTower, norm_mul]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with q
    ring
  rw [he]
  have hw := inherited_pair_weight_bound i j J (InverseClippingProfiles.momentOrder J) p
  have hp : 0 ≤ ambientWeight J p := zero_le_one.trans (ambientWeight_one_le J p)
  calc
    _ ≤ (ambientWeight J p * ‖fullProfileDensity outer b₁ b₂ b₃ p‖) *
        (C*((1+‖inheritedLeft i p‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖inheritedRight j p‖)^(InverseClippingProfiles.momentOrder J))) :=
      mul_le_mul_of_nonneg_left (hb _ _) (mul_nonneg hp (norm_nonneg _))
    _ = (C*‖fullProfileDensity outer b₁ b₂ b₃ p‖) *
        (ambientWeight J p * ((1+‖inheritedLeft i p‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖inheritedRight j p‖)^(InverseClippingProfiles.momentOrder J))) := by ring
    _ ≤ (C*‖fullProfileDensity outer b₁ b₂ b₃ p‖) * ambientWeight (requiredOuterOrder J) p :=
      mul_le_mul_of_nonneg_left hw (mul_nonneg hC (norm_nonneg _))
    _ = _ := by ring

theorem second_profile_tower_uniform {ι : Type*} [Fintype ι]
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ (θ₁ θ₂ : ℝ) (y : Fin 6 → ℝ),
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ c₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      (∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
        Integrable (fun z : Ambient ι × Ambient (Fin 6) =>
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖densityTower i j outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ∧
        (1+R)^A * (∫ z : Ambient ι × Ambient (Fin 6),
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖densityTower i j outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ≤
          C * (∫ p : Ambient ι, ambientWeight (requiredOuterOrder J) p *
            ‖fullProfileDensity outer b₁ b₂ b₃ p‖)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := second_profile_common_measure U g₁ g₂ Φ M B m₁ m₂ b hM hB hU h₁ h₂ A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨c₃,hc₃⟩ := hs R hR
  refine ⟨c₃,?_⟩
  intro ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  refine ⟨fun θ₁ θ₂ => (hc₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL).1, ?_⟩
  intro i j outer b₁ b₂ b₃
  refine ⟨densityTower_weighted_integrable i j outer b₁ b₂ b₃ _ _ _ c₃ ρ c₁ c₂ L J, ?_⟩
  exact tower_bound_from_inner i j outer b₁ b₂ b₃ _ _ _ c₃ ρ c₁ c₂ L C R hC hR A J
    (fun θ₁ θ₂ => (hc₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL).2.2)

theorem densityTower_fubini {ι : Type*} [Fintype ι] (i j : ι)
    (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ)
    (F : Ambient ι × Ambient (Fin 6) → ℂ) (hF : StronglyMeasurable F) (J : ℕ)
    (hbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L z * F z) =
      ∫ p, ∫ q, densityTower i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L (p,q) * F (p,q) :=
  density_test_fubini _ F
    (densityTower_joint_measurable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L) hF J
    (densityTower_weighted_integrable i j outer b₁ b₂ b₃ g g₁ g₂ c₃ ρ c₁ c₂ L J) hbound

theorem actual_child_height_weight_bound (J K : ℕ) (p : Ambient (Fin 6)) :
    ambientWeight J p *
      ((1+‖profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 4‖)^K *
       (1+‖profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 5‖)^K) ≤
      ambientWeight (J+2*K) p := by
  simpa only [second_inherited_left_eq, second_inherited_right_eq, norm_neg] using
    inherited_pair_weight_bound (4 : Fin 6) 5 J K p

theorem normalization_eta_log (Z η : ℝ) (hZ : 0 < Z) :
    Real.exp (-6*(η*Real.log Z)) = Z^(-6*η) := by
  rw [Real.rpow_def_of_pos hZ]
  congr 1
  ring

theorem fresh_physical_profile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (ω₁ ω₂ : ℝ → ℂ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hω₁ : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) ≠ 0 → ω₁ (q 4/X₀) = 1)
    (hω₂ : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) ≠ 0 → ω₂ (q 5/X₀) = 1)
    (hcut : ω₁ (q 4/X₀) ≠ 0 → ω₂ (q 5/X₀) ≠ 0 →
      ∀ i, V i (secondRelativeLog q G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L) : ℂ) * secondNormProfile
      (fun x => W₁ (x/(G₀*V₀*X₀))) (fun x => W₂ (x/(G₀*V₀*X₀)))
      Φ (fun _ _ => 1) Y q =
      ((E₀*V₀*X₀ : ℝ) : ℂ)⁻¹ * (ω₁ (q 4/X₀)*ω₂ (q 5/X₀)) *
        ((Real.exp (-6*L) : ℂ)*secondPoissonProfile W₁ W₂ Φ V
          (Y*K₀/(E₀*V₀^2*X₀^2)) (secondRelativeLog q G₀ E₀ V₀ K₀ X₀)) := by
  by_cases hw₁ : ω₁ (q 4/X₀) = 0
  · have hW : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      exact zero_ne_one (hw₁.symm.trans (hω₁ hn))
    simp only [secondNormProfile,hW,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 5/X₀) = 0
  · have hW : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0 := by
      by_contra hn
      exact zero_ne_one (hw₂.symm.trans (hω₂ hn))
    simp only [secondNormProfile,hW,hw₂,mul_zero,zero_mul,zero_div]
  have hm : secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q =
    (ω₁ (q 4/X₀)*ω₂ (q 5/X₀))*secondNormProfile (fun x => W₁ (x/(G₀*V₀*X₀)))
      (fun x => W₂ (x/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y q := by
    by_cases h1 : W₁ (q 0*q 2*q 4/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 0*q 2*q 5/(G₀*V₀*X₀)) = 0
    · simp only [secondNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  rw [hm, secondNormProfile_nominal W₁ W₂ Φ G₀ E₀ V₀ K₀ X₀ Y hG hE hV hK hX q hq]
  change _*( _*(_*secondNormProfile W₁ W₂ Φ (fun _ _ => 1) _
    (secondRelativeNorm q G₀ E₀ V₀ K₀ X₀))) = _
  rw [secondNormProfile_eq_full_of_windows W₁ W₂ Φ V _ _
    (secondRelativeNorm_pos q hq G₀ E₀ V₀ K₀ X₀ hG hE hV hK hX) (hcut hw₁ hw₂)]
  ring_nf
  rfl

theorem retained_clipping_parameter (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) (hret : w (q/Z^N) ≠ 0) :
    let c := Z^(max 0 N-N)
    1 ≤ c ∧ c ≤ b ∧ |Real.log c| ≤ Real.log b ∧
      Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b := by
  dsimp only
  have hc := InverseClippingProfiles.retained_clipped_column w Z N q a b hZ hq ha hb hw hret
  refine ⟨hc.1,hc.2.1,?_,hc.2.2.1⟩
  rw [abs_of_nonneg (Real.log_nonneg hc.1)]
  exact Real.log_le_log (zero_lt_one.trans_le hc.1) hc.2.1

theorem first_second_tower_uniform
    (W₁ W₂ : ℝ → ℂ) (a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (hsW₁ : Function.support W₁ ⊆ Set.Icc a₀ b₀)
    (hsW₂ : Function.support W₂ ⊆ Set.Icc a₀ b₀)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ₁ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (MV : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hVS : ∀ i, HasCompactSupport (V i))
    (hMV : ∀ i, 0 ≤ MV i) (hVbox : ∀ i y, V i y ≠ 0 → |y| ≤ MV i)
    (U : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ₂ : 𝓢(ℝ, ℂ))
    (M B : Fin 6 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A₁ A₂ J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    let outer := firstRootSchwartz V hV hVS
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ → ∃ b₃ c₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ₁ V R₁ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 9 → ℝ,
          fullProfileDensity outer b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      ∀ (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ (θ₁ θ₂ : ℝ) (y : Fin 6 → ℝ),
        (Real.exp (-6*L) : ℂ) * secondPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ₂ (fun i y => U i (y+ρ i)) R₂ y =
        ∫ p : Ambient (Fin 6), density G f₁ f₂ c₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun z : Ambient (Fin 9) × Ambient (Fin 6) =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ∧
      (1+R₁)^A₁ * (1+R₂)^A₂ * (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 outer b₁ b₂ b₃ G f₁ f₂ c₃ ρ c₁ c₂ L z‖) ≤ C := by
  dsimp only
  obtain ⟨C₂,hC₂,hsecond⟩ := second_profile_tower_uniform (ι := Fin 9)
    U g₁ g₂ Φ₂ M B m₁ m₂ b hM hB hU h₁ h₂ A₂ J
  obtain ⟨b₁,b₂,C₁,hC₁,hfirst⟩ := first_full_profile_common_measure
    W₁ W₂ a₀ b₀ ha₀ hsW₁ hsW₂ hW₁ hW₂ Φ₁ V MV hV hVS hMV hVbox A₁ (requiredOuterOrder J)
  refine ⟨b₁,b₂,C₂*C₁,mul_nonneg hC₂ hC₁,?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₃,he₁,_,hb₁⟩ := hfirst R₁ hR₁
  obtain ⟨c₃,hc₃⟩ := hsecond R₂ hR₂
  refine ⟨b₃,c₃,he₁,?_⟩
  intro ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hc₃ ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have ht := h.2 7 8 (firstRootSchwartz V hV hVS) b₁ b₂ b₃
  refine ⟨h.1,ht.1,?_⟩
  have hh := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (1+R₁)^A₁ by positivity)
  have hh' := mul_le_mul_of_nonneg_left hb₁ hC₂
  calc
    _ = (1+R₁)^A₁ * ((1+R₂)^A₂ * (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖densityTower 7 8 (firstRootSchwartz V hV hVS) b₁ b₂ b₃
            (fun i => rooted (U i) (M i) (InverseClippingProfiles.secondBalancedSlope i) (hU i))
            (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
            c₃ ρ c₁ c₂ L z‖)) := by ring
    _ ≤ (1+R₁)^A₁ * (C₂ * (∫ p : Ambient (Fin 9), ambientWeight (requiredOuterOrder J) p *
        ‖fullProfileDensity (firstRootSchwartz V hV hVS) b₁ b₂ b₃ p‖)) := hh
    _ ≤ C₂*C₁ := by
      simpa only [ambientWeight, tripleHeight, coordinateHeight, mul_assoc,
        mul_left_comm, mul_comm] using hh'

end SevenEighths.InverseSecondProfileUniform

end

end OAI
end OAIOriginalModule0656

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstProfileUniform
Source SHA256: 7893896dea0ea13e517ba952e13afe0cebd887b21de11fa32acbeb99926780a9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0657


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment
open SevenEighths.InverseInitialProfile
open SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseMomentFirstProfileUniform

def rooted (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  InverseClippingProfiles.rootSchwartz g M 0 1 0 a 0 zero_lt_one (by simp) hg

@[simp] theorem rooted_apply (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (y : ℝ) :
    rooted g M a hg y = (Real.exp (a*y) : ℂ)*g y := by
  simp [rooted, InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]

theorem rooted_support (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) :
    Function.support (rooted g M a hg) ⊆ Set.Icc (-M) M := by
  intro y hy
  exact hg (by simpa using hy)

def translated (g : 𝓢(ℝ, ℂ)) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ (-ρ) g

@[simp] theorem translated_apply (g : 𝓢(ℝ, ℂ)) (ρ y : ℝ) :
    translated g ρ y = g (y+ρ) := by simp [translated]

theorem fourier_translated (g : 𝓢(ℝ, ℂ)) (ρ t : ℝ) :
    (𝓕 (translated g ρ)) t = logPhase t ρ * (𝓕 g) t := by
  rw [SchwartzMap.fourier_coe]
  have he : (translated g ρ : ℝ → ℂ) = fun y => g (y+ρ) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translate, ← SchwartzMap.fourier_coe]

def normalization (ρ : Fin 9 → ℝ) (c₁ c₂ L : ℝ) : ℝ :=
  Real.exp (-(9/2:ℝ)*L - ∑ i, InverseClippingProfiles.firstBalancedSlope i*ρ i +
    (Real.log c₁+Real.log c₂)/2)

def density (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    fullProfileDensity (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem density_formula (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) :
    density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p =
      (normalization ρ c₁ c₂ L : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 * (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) *
        (∏ i, logPhase (p.2 i) (ρ i) * (𝓕 (g i)) (p.2 i)) := by
  simp only [density, fullProfileDensity, tripleCoefficient, coordinateDensity,
    fourier_translated, fourier_clippedTwist]
  ring

private theorem fourier_twist (g : 𝓢(ℝ, ℂ)) (θ t : ℝ) :
    (𝓕 (frequencyTwist g θ)) t = (𝓕 g) (t-θ) := by
  rw [SchwartzMap.fourier_coe]
  have he : (frequencyTwist g θ : ℝ → ℂ) = fun y => logPhase θ y * g y := by
    ext y
    exact frequencyTwist_apply g θ y
  rw [he, InverseClippingProfiles.fourier_phase_shift, ← SchwartzMap.fourier_coe]

theorem density_norm (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) :
    ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖ = normalization ρ c₁ c₂ L *
      ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖ := by
  rw [density_formula]
  simp only [norm_mul, norm_prod, sourceDensity_norm, logPhase_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, normalization,
    abs_of_pos (Real.exp_pos _), twistedFullDensity, fullProfileDensity,
    tripleCoefficient, coordinateDensity, fourier_twist]
  ring

theorem density_joint_measurable (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun z : ((Fin 9 → ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × ℝ) × Ambient (Fin 9) =>
      density g g₁ g₂ b₃ z.1.1 z.1.2.1.1 z.1.2.1.2 z.1.2.2.1.1 z.1.2.2.1.2 z.1.2.2.2 z.2) := by
  simp_rw [density_formula]
  apply Measurable.stronglyMeasurable
  unfold normalization sourceDensity logPhase
  have h1 := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 := b₃.continuous.measurable
  have hu (i : Fin 9) := (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have he := Complex.continuous_exp.measurable
  fun_prop

theorem normalization_bound (B : Fin 9 → ℝ) (b : ℝ)
    (ρ : Fin 9 → ℝ) (c₁ c₂ L : ℝ) (hρ : ∀ i, |ρ i| ≤ B i)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁b : c₁ ≤ b) (hc₂b : c₂ ≤ b) (hL : 0 ≤ L) :
    normalization ρ c₁ c₂ L ≤
      Real.exp ((∑ i, |InverseClippingProfiles.firstBalancedSlope i| *B i)+Real.log b) := by
  unfold normalization
  apply Real.exp_le_exp.mpr
  have hs : -(∑ i, InverseClippingProfiles.firstBalancedSlope i*ρ i) ≤
      ∑ i, |InverseClippingProfiles.firstBalancedSlope i| *B i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |InverseClippingProfiles.firstBalancedSlope i*ρ i| := neg_le_abs _
      _ = |InverseClippingProfiles.firstBalancedSlope i| *|ρ i| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hρ i) (abs_nonneg _)
  have h1 := Real.log_le_log hc₁ hc₁b
  have h2 := Real.log_le_log hc₂ hc₂b
  linarith

theorem density_weighted_integrable (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) := by
  simp_rw [density_norm]
  convert (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable g
    (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ J).const_mul
      (normalization ρ c₁ c₂ L) using 1
  funext p
  unfold twistedFullDensity
  ring

private theorem radial_common_box (Φ : 𝓢(ℝ, ℂ)) (M : Fin 9 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (V : Fin 9 → ℝ → ℂ), (∀ i y, V i y ≠ 0 → |y| ≤ M i) →
        ∀ y : Fin 9 → ℝ,
        (∏ i, V i (y i))*paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)) =
          ∫ t : ℝ, (∏ i, V i (y i)*logPhase t (firstKernelSlope i*y i))*b₃ t) ∧
      (1+R)^A * (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) ≤ C := by
  let box : Fin 9 → ℝ → ℂ := fun i y => if |y| ≤ M i then 1 else 0
  have hb : ∀ i y, box i y ≠ 0 → |y| ≤ M i := by
    intro i y h
    simpa [box] using h
  obtain ⟨C,hC,hs⟩ := paperRadialFourier_log_separation_envelope Φ box
    firstKernelSlope M hM hb A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,he,_,hm,_⟩ := hs R hR
  refine ⟨b₃,?_,hm⟩
  intro V hV y
  simp only [Finset.prod_mul_distrib]
  by_cases hz : (∏ i, V i (y i)) = 0
  · simp [hz]
  · have hall (i : Fin 9) : V i (y i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
    have hbox (i : Fin 9) : box i (y i) = 1 := by simp [box, hV i _ (hall i)]
    have h := he y
    simp only [hbox, one_mul, Finset.prod_const_one] at h
    rw [h, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring

theorem translated_box (g : 𝓢(ℝ, ℂ)) (M B ρ : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (hρ : |ρ| ≤ B)
    {y : ℝ} (hy : translated g ρ y ≠ 0) : |y| ≤ M+B := by
  have h := hg (show g (y+ρ) ≠ 0 from by simpa only [translated_apply] using hy)
  have hr := abs_le.mp hρ
  apply abs_le.mpr
  constructor <;> linarith [h.1,h.2,hr.1,hr.2]

theorem density_weighted_integral (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Ambient (Fin 9), ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) = normalization ρ c₁ c₂ L *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₁ θ₁)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₂ θ₂)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
        (∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖) := by
  simp_rw [density_norm]
  have he (p : Ambient (Fin 9)) :
      ambientWeight J p * (normalization ρ c₁ c₂ L *
        ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖) =
      normalization ρ c₁ c₂ L * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (frequencyTwist g₁ θ₁))
          (𝓕 (frequencyTwist g₂ θ₂)) b₃ p‖) := by
    unfold ambientWeight tripleHeight coordinateHeight twistedFullDensity
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  ring

def profile (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 9 → ℝ) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    ((∏ i, translated (g i) (ρ i) (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, firstLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, firstRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)))

def requiredOuterOrder (J : ℕ) : ℕ := J+2*InverseClippingProfiles.momentOrder J

theorem common_measure (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 9 → ℝ) (b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hg : ∀ i, Function.support (g i) ⊆ Set.Icc (-M i) (M i)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 0 < c₁ → 0 < c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 9 → ℝ, profile g g₁ g₂ Φ ρ c₁ c₂ θ₁ θ₂ R L y =
        ∫ p : Ambient (Fin 9), density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 9), ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  obtain ⟨C₃,hC₃,hsep⟩ := radial_common_box Φ (fun i => M i+B i)
    (fun i => add_nonneg (hM i) (hB i)) A J
  obtain ⟨C₁,hC₁,h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂,hC₂,h₂⟩ := frequencyTwist_fourier_moment J g₂
  let D := ∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖
  let E := Real.exp ((∑ i, |InverseClippingProfiles.firstBalancedSlope i| * B i)+Real.log b)
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun _ => by positivity))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨E*C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃,he,hm⟩ := hsep R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  refine ⟨?_, density_weighted_integrable _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hb : ∀ i z, translated (g i) (ρ i) z ≠ 0 → |z| ≤ M i+B i :=
      fun i z hz => translated_box (g i) (M i) (B i) (ρ i) (hg i) (hρ i) hz
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (fun i => translated (g i) (ρ i)) firstLeftSlope firstRightSlope firstKernelSlope
      R b₃ (he _ hb) y
    have habs := profile_integral_coordinate_absorption (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      firstLeftSlope firstRightSlope firstKernelSlope y
    simp only [profileMode] at habs
    unfold profile
    rw [hid, habs, ← full_density_mode_fubini, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold density
    ring
  · rw [density_weighted_integral]
    have h12 := mul_le_mul (h₁ θ₁) (h₂ θ₂)
      (integral_nonneg (fun _ => by positivity)) (by positivity)
    have h123 := mul_le_mul h12 hm (by positivity) (by positivity)
    have hd := mul_le_mul_of_nonneg_right h123 hD
    have hn := normalization_bound B b ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
    have hh := mul_le_mul hn hd (by positivity) hE
    convert hh using 1 <;>
      (dsimp only [InverseClippingProfiles.momentOrder, E, D]; ring)

theorem balanced_exponential_identity (ρ y : Fin 9 → ℝ) (c₁ c₂ L : ℝ) :
    normalization ρ c₁ c₂ L *
      (∏ i, Real.exp (InverseClippingProfiles.firstBalancedSlope i*(y i+ρ i))) *
      Real.exp (-(1/2:ℝ)*((∑ i, firstLeftSlope i*y i)+Real.log c₁)) *
      Real.exp (-(1/2:ℝ)*((∑ i, firstRightSlope i*y i)+Real.log c₂)) =
      Real.exp (-(9/2:ℝ)*L)*Real.exp (InverseClippingProfiles.firstRootExponent y) := by
  rw [normalization, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [InverseClippingProfiles.firstBalancedSlope,
    InverseClippingProfiles.firstRootExponent, firstLeftSlope, firstRightSlope,
    Fin.sum_univ_succ]
  ring

def positiveSource (g : 𝓢(ℝ, ℂ)) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x)*g (Real.log x+Real.log c)

theorem positiveSource_logSchwartz (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (θ : ℝ) :
    positiveSource (CubicReflectionKernel.logSchwartz W a b ha hs hW) c θ x =
      clippedSource W c θ x := by
  simp only [positiveSource, CubicReflectionKernel.logSchwartz_apply,
    Real.exp_add, Real.exp_log hc, Real.exp_log hx, clippedSource]
  rw [mul_comm x c]

theorem balanced_profile_identity
    (U : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M : Fin 9 → ℝ) (m₁ m₂ : ℝ)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂)
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 9 → ℝ) :
    profile (fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i))
      (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
      Φ ρ c₁ c₂ θ₁ θ₂ R L y =
      (Real.exp (-(9/2:ℝ)*L) : ℂ) * firstPoissonProfile
        (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
        Φ (fun i y => U i (y+ρ i)) R y := by
  have he := congrArg (fun x : ℝ => (x : ℂ)) (balanced_exponential_identity ρ y c₁ c₂ L)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at he
  unfold profile firstPoissonProfile
  rw [InverseClippingProfiles.firstRootWindows_prod]
  simp only [translated_apply, clippedTwist_apply, rooted_apply, positiveSource, Real.log_exp,
    Finset.prod_mul_distrib]
  linear_combination
    (∏ i, U i (y i+ρ i)) * logPhase θ₁ (∑ i, firstLeftSlope i*y i) *
    g₁ ((∑ i, firstLeftSlope i*y i)+Real.log c₁) *
    logPhase θ₂ (∑ i, firstRightSlope i*y i) *
    g₂ ((∑ i, firstRightSlope i*y i)+Real.log c₂) *
    paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)) * he

theorem first_profile_common_measure
    (U : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 9 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 9 → ℝ,
        (Real.exp (-(9/2:ℝ)*L) : ℂ) * firstPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 9), density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 9), ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := common_measure
    (fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i))
    (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂) Φ M B b hM hB
    (fun i => rooted_support _ _ _ _) A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,hb₃⟩ := hs R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ (zero_lt_one.trans_le hc₁)
    (zero_lt_one.trans_le hc₂) hc₁b hc₂b hL
  refine ⟨?_,h.2⟩
  intro y
  rw [← balanced_profile_identity U g₁ g₂ Φ M m₁ m₂ hU h₁ h₂]
  exact h.1 y

end SevenEighths.InverseMomentFirstProfileUniform

end

end OAI
end OAIOriginalModule0657

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstBalancedSource
Source SHA256: e52996f81ab61a5fecbe9a0fed6b4f0e4ffb5f48706daa73422aca3abe91508d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0658



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open JointLogSeparation MeasureTheory
noncomputable section

theorem first_fresh_physical_profile
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (s q : Fin 9 → ℝ) (hspos : ∀ i, 0 < s i) (hq : ∀ i, 0 < q i) (K : ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (normalization : ℂ)
    (he : ∀ y : Fin 9 → ℝ, normalization * firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) ≠ 0 → ω₁ (q 7/s 7) = 1)
    (hω₂ : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) ≠ 0 → ω₂ (q 8/s 8) = 1)
    (hcut : ω₁ (q 7/s 7) ≠ 0 → ω₂ (q 8/s 8) ≠ 0 → ∀ i, V i (firstRelativeLog q s i) = 1) :
    normalization * firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
    (firstRootScale s:ℂ)⁻¹*(ω₁ (q 7/s 7)*ω₂ (q 8/s 8))*
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
  by_cases hw₁ : ω₁ (q 7/s 7) = 0
  · have hh : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0 := by
      by_contra hn
      have := hω₁ hn
      simp only [hw₁,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₁,mul_zero,zero_mul,zero_div]
  by_cases hw₂ : ω₂ (q 8/s 8) = 0
  · have hh : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0 := by
      by_contra hn
      have := hω₂ hn
      simp only [hw₂,zero_ne_one] at this
    simp only [firstNormProfile,hh,hw₂,mul_zero,zero_mul,zero_div]
  have hcut' := hcut hw₁ hw₂
  have hnom := firstNormProfile_nominal W₁ W₂ Φ (fun _ _ => 1) s q hspos hq K
  have hfull : normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) =
      ∫ z : Frequency × (Fin 9 → ℝ), density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope (firstRelativeLog q s) z.1 z.2 := by
    have hp := firstPoissonProfile_log W₁ W₂ Φ V
      (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i)
      (fun i => div_pos (hq i) (hspos i))
    have hc : firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (firstRelativeLog q s) =
        firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i) := by
      unfold firstRelativeLog
      rw [hp]
      simp only [firstRelativeLog] at hcut'
      simp only [firstNormProfile,hcut',Finset.prod_const_one]
    rw [← hc]
    exact he (firstRelativeLog q s)
  have hm : firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q =
      (ω₁ (q 7/s 7)*ω₂ (q 8/s 8)) *
      firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
        (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ (fun _ _ => 1) K q := by
    by_cases h1 : W₁ (q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7)) = 0
    · simp only [firstNormProfile,h1,mul_zero,zero_mul,zero_div]
    by_cases h2 : W₂ (q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8)) = 0
    · simp only [firstNormProfile,h2,mul_zero,zero_mul,zero_div]
    simp only [hω₁ h1,hω₂ h2,one_mul]
  calc
    _ = (firstRootScale s:ℂ)⁻¹*(ω₁ (q 7/s 7)*ω₂ (q 8/s 8))*
        (normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1)
          (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) (fun i => q i/s i)) := by
      conv_lhs => rw [hm,hnom]
      ring
    _ = _ := by rw [hfull]

theorem first_balanced_density_integrable (g : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) :
    Integrable (InverseMomentFirstProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L) := by
  exact (full_density_integrable _ _ _ _).const_mul _

open ActualEisensteinCubic FirstPassCubeLabels
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem firstCommonNorms_pos (A₁ A₂ C R : ℝ) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (hC : 0 < C) (hR : 0 < R) (d h : Eis) (hd : d ≠ 0) (hh : h ≠ 0)
    (j : FirstCommonIndex ι) : ∀ i,0 < firstCommonNorms p A₁ A₂ C R d h j i := by
  intro i
  fin_cases i <;> simp only [firstCommonNorms]
  · exact hA₁
  · exact hA₂
  · exact hC
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hd))
  · exact hR
  · exact primeProductNorm_pos p hp _
  · exact sq_pos_of_pos (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hh))
  · exact primeProductNorm_pos p hp _
  · exact primeProductNorm_pos p hp _

include hp in

theorem actual_first_balanced_block (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (A₁ A₂ C R K L : ℝ)
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hC : 0 < C) (hR : 0 < R)
    (d h : Eis) (hd : d ≠ 0) (hh : h ≠ 0) (s : Fin 9 → ℝ) (hs : ∀ i,0 < s i)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z *
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      W₁ (A₁*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (hω₂ : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      W₂ (A₂*C*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ j ∈ firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s i) = 1) :
    (Real.exp (-(9/2:ℝ)*L):ℂ)*firstBlockedPhysicalRows p hg F selector C₁ C₂
      (fun x => W₁ (x/(s 0*s 2*s 5*s 7))) (fun x => W₂ (x/(s 1*s 2*s 5*s 8)))
      Φ A₁ A₂ C R K d h =
    (firstRootScale s:ℂ)⁻¹*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z := by
  apply first_block_normalized_density p hg F selector C₁ C₂ _ _ ω₁ ω₂ Φ A₁ A₂ C R K d h s density hDensity
  intro j hj hn
  exact first_fresh_physical_profile W₁ W₂ ω₁ ω₂ Φ V s
    (firstCommonNorms p A₁ A₂ C R d h j) hs
    (firstCommonNorms_pos p hp A₁ A₂ C R hA₁ hA₂ hC hR d h hd hh j) K density
    (Real.exp (-(9/2:ℝ)*L):ℂ) hsep
    (by simpa [firstCommonNorms] using hω₁ j hj hn)
    (by simpa [firstCommonNorms] using hω₂ j hj hn)
    (by simpa [firstCommonNorms] using hcut j hj hn)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0658

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstFamilySource
Source SHA256: 91aacfb4f983017f7b2a42b88de0a224937e563b57c3f519814561de83f83d98
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0659



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem integrable_first_block_density (F : Finset ι) (selector C₁ C₂ : Finset ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density) :
    Integrable (fun z : Frequency × (Fin 9 → ℝ) => density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z) := by
  let coef (j : FirstCommonIndex ι) :=
    (selector j.2.1*firstCommonWeight p hg C₁ C₂ h j)*
      (ω₁ (primeProductNorm p j.2.2.1/s 7)*ω₂ (primeProductNorm p j.2.2.2/s 8))
  have he : (fun z : Frequency × (Fin 9 → ℝ) => density z*
      firstBlockedSeparatedRow p hg F selector C₁ C₂ ω₁ ω₂ A₁ A₂ C R d h s z) =
      fun z => ∑ j∈firstCommonIndices F,coef j*(density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
          (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) := by
    funext z
    rw [←first_block_modes_eq_columns]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [coef]
    ring
  rw [he]
  exact integrable_finsetSum _ (fun j hj => (integrable_density_mode density hDensity
    firstLeftSlope firstRightSlope firstKernelSlope
    (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s)).const_mul (coef j))

theorem first_family_density_sum (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density) :
    (∑ x∈source,w x*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstBlockedSeparatedRow p hg F (selector x) (C₁ x) (C₂ x) ω₁ ω₂
        (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s z) =
    ∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z := by
  simp only [←integral_const_mul]
  rw [←integral_finsetSum source (fun x hx =>
    (integrable_first_block_density p hg F (selector x) (C₁ x) (C₂ x) ω₁ ω₂
      (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s density hDensity).const_mul (w x))]
  apply integral_congr_ae
  filter_upwards with z
  simp only [firstFamilySeparatedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def firstFamilyPhysicalRows (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R : κ → ℝ) (K : ℝ)
    (d h : κ → Eis) (s : Fin 9 → ℝ) : ℂ :=
  ∑ x∈source,w x*firstBlockedPhysicalRows p hg F (selector x) (C₁ x) (C₂ x)
    (fun y => W₁ (y/(s 0*s 2*s 5*s 7))) (fun y => W₂ (y/(s 1*s 2*s 5*s 8)))
    Φ (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x)

theorem actual_first_balanced_family (hp : ∀ i,p i ≠ 0)
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (hs : ∀ i,0 < s i) (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i) = 1) :
    (Real.exp (-(9/2:ℝ)*L):ℂ)*firstFamilyPhysicalRows p hg source F selector C₁ C₂ w
      W₁ W₂ Φ A₁ A₂ C R K d h s =
    (firstRootScale s:ℂ)⁻¹*∫ z : Frequency × (Fin 9 → ℝ),density z*
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z := by
  have hb (x : κ) (hx : x∈source) := actual_first_balanced_block p hp hg F (selector x) (C₁ x) (C₂ x)
    W₁ W₂ ω₁ ω₂ Φ V (A₁ x) (A₂ x) (C x) (R x) K L
    (hpos x hx).1 (hpos x hx).2.1 (hpos x hx).2.2.1 (hpos x hx).2.2.2.1
    (d x) (h x) (hpos x hx).2.2.2.2.1 (hpos x hx).2.2.2.2.2 s hs density hDensity hsep
    (hω₁ x hx) (hω₂ x hx) (hcut x hx)
  rw [←first_family_density_sum p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s density hDensity]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    _ = w x*((Real.exp (-(9/2:ℝ)*L):ℂ)*firstBlockedPhysicalRows p hg F (selector x) (C₁ x) (C₂ x)
      (fun y => W₁ (y/(s 0*s 2*s 5*s 7))) (fun y => W₂ (y/(s 1*s 2*s 5*s 8)))
      Φ (A₁ x) (A₂ x) (C x) (R x) K (d x) (h x)) := by ring
    _ = _ := by rw [hb x hx]; ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0659

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstPhysicalFamily
Source SHA256: 721e42add540dbc76f7a741cd14c45cb7bcd2a97df6b1201965ad6af5120bc77
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0660



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCanonicalCoefficient (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) : Finset ι→ℂ :=
  firstBareCubeCoefficient p hp hg hcop b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit negative
    (canonicalCubeResidual p hg b C negative Ψ m (ConcretePrimeRowBridge.idealGenerator x.1) H) d

theorem firstCanonicalCoefficient_old (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O) :
    firstCanonicalCoefficient p hp hcop hg b C negative Ψ m d H x =
      firstOldLabelCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p Ψ m
          (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)))
        (∏i∈C,p i) d x.1 := rfl

lemma first_unblocked_physical (F : Finset ι) (C₁ C₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstBlockedPhysicalRows p hg F (fun _=>1) C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed]
  simp only [firstBlockedPhysicalRows,one_mul]

theorem retained_first_physical_family (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ d : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (source : Finset (Ideal O×O)) (a : Ideal O×O→ℂ)
    (s : Fin 9→ℝ) (hs : ∀ i,0<s i) :
    (∑ x∈source,a x*canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)*
      firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)
        H₁ H₂ W₁ W₂ Φ K d x.2) =
    (K:ℂ)*firstFamilyPhysicalRows p hg source (pool\(b.support∪C)) (fun _ _=>1)
      (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁)
      (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂)
      (retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a)
      (fun x=>star (W₁ ((s 0*s 2*s 5*s 7)*x)))
      (fun x=>W₂ ((s 1*s 2*s 5*s 8)*x)) Φ
      (fun _=>‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
      (fun _=>‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
      (fun _=>primeProductNorm p C)
      (fun _=>primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit))
      K (fun _=>d) Prod.snd s := by
  have hscale₁ : s 0*s 2*s 5*s 7≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hs 0).ne' (hs 2).ne') (hs 5).ne') (hs 7).ne'
  have hscale₂ : s 1*s 2*s 5*s 8≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (hs 1).ne' (hs 2).ne') (hs 5).ne') (hs 8).ne'
  have hw₁ : (fun y=>star (W₁ ((s 0*s 2*s 5*s 7)*(y/(s 0*s 2*s 5*s 7))))) =
      fun y=>star (W₁ y) := by
    funext y
    rw [mul_div_cancel₀ _ hscale₁]
  have hw₂ : (fun y=>W₂ ((s 1*s 2*s 5*s 8)*(y/(s 1*s 2*s 5*s 8)))) = W₂ := by
    funext y
    rw [mul_div_cancel₀ _ hscale₂]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum,hw₁,hw₂]
  apply Finset.sum_congr rfl
  intro x hx
  rw [first_unblocked_physical p hg]
  simp only [firstCubePhysicalMode,retainedCubeWeight,firstCanonicalCoefficient,
    firstBareCubeCoefficient,Bool.false_eq_true,ite_false,ite_true]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0660

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceSupport
Source SHA256: 554a1680bb82ef9e1c025d30f86da89f59207b797e403cc42865ff017abc3771
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0661


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma first_squarefree_row_zero_mem (U : Finset ι) (i : ι) (hi : i∈U) (n : O)
    (hn : n∈Ideal.span {p i}) : finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg U n=0 := by
  unfold finiteSquarefreeRow
  apply Finset.prod_eq_zero hi
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn,MulChar.map_zero]

lemma canonicalCubeResidual_zero_overlap (b : CubeCoordinates ι) (C U : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ)
    (hn : ¬Disjoint U (b.support∪C)) : canonicalCubeResidual p hg b C negative Ψ m f H U=0 := by
  obtain ⟨i,hi,hib⟩ := Finset.not_disjoint_iff.mp hn
  rcases Finset.mem_union.mp hib with hib|hiC
  · have hm : cubeRadical p b.support∈Ideal.span {p i} :=
      Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hib)
    have hz : rowCoprimeMask (fun i=>Ideal.span {p i}) U (cubeRadical p b.support)=0 := by
      simp only [rowCoprimeMask,ite_eq_left_iff]
      intro hh
      exact False.elim (hh ⟨i,hi,hm⟩)
    simp only [canonicalCubeResidual,originalLabelColumn,hz,mul_zero,zero_mul]
  · have hm : aLabel p b.support (if negative then b.rightBit else b.leftBit)*(∏j∈C,p j)∈Ideal.span {p i} :=
      Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiC) _)
    have hz := first_squarefree_row_zero_mem p hg U i hi _ hm
    simp only [canonicalCubeResidual,originalLabelColumn,hz,zero_pow (by norm_num : 4≠0),mul_zero,zero_mul]

lemma firstCanonicalCoefficient_zero_overlap (b : CubeCoordinates ι) (C U : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O)
    (hn : ¬Disjoint U (b.support∪C)) : firstCanonicalCoefficient p hp hcop hg b C negative Ψ m d H x U=0 := by
  have hz := canonicalCubeResidual_zero_overlap p hg b C U negative Ψ m
    (ConcretePrimeRowBridge.idealGenerator x.1) H hn
  cases negative <;>
    simp only [firstCanonicalCoefficient,firstBareCubeCoefficient,Bool.false_eq_true,ite_false,ite_true,
      cubeMinusCoefficient,cubePlusCoefficient,firstPassColumnMinus,firstPassColumnPlus,hz,mul_zero]

lemma firstCommonIndices_membership (F : Finset ι) (j : FirstCommonIndex ι) :
    j∈firstCommonIndices F ↔ j.2.1⊆F ∧ j.2.2.1⊆F\j.2.1 ∧ j.2.2.2⊆F\j.2.1 := by
  simp [firstCommonIndices]

lemma firstCommonIndices_mono {F G : Finset ι} (h : F⊆G) : firstCommonIndices F⊆firstCommonIndices G := by
  intro j hj
  rcases (firstCommonIndices_membership F j).mp hj with ⟨hd,hu,hv⟩
  exact (firstCommonIndices_membership G j).mpr ⟨hd.trans h,
    hu.trans (Finset.sdiff_subset_sdiff h le_rfl),hv.trans (Finset.sdiff_subset_sdiff h le_rfl)⟩

lemma firstCommonWeight_zero_outside (F G : Finset ι) (C₁ C₂ : Finset ι→ℂ) (h : O)
    (hC₁ : ∀U,U⊆G → ¬U⊆F → C₁ U=0) (hC₂ : ∀U,U⊆G → ¬U⊆F → C₂ U=0)
    (j : FirstCommonIndex ι) (hj : j∈firstCommonIndices G) (hjF : j∉firstCommonIndices F) :
    firstCommonWeight p hg C₁ C₂ h j=0 := by
  rcases (firstCommonIndices_membership G j).mp hj with ⟨hd,hu,hv⟩
  by_cases hleft : j.2.1∪j.2.2.1⊆F
  · have hright : ¬j.2.1∪j.2.2.2⊆F := by
      intro hr
      apply hjF
      apply (firstCommonIndices_membership F j).mpr
      refine ⟨Finset.Subset.trans Finset.subset_union_left hleft,?_,?_⟩
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨hleft (Finset.mem_union_right _ hi),(Finset.mem_sdiff.mp (hu hi)).2⟩
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨hr (Finset.mem_union_right _ hi),(Finset.mem_sdiff.mp (hv hi)).2⟩
    have hz := hC₂ _ (Finset.union_subset hd (hv.trans Finset.sdiff_subset)) hright
    simp only [firstCommonWeight,firstCommonCoefficient,hz,mul_zero,zero_mul]
  · have hz := hC₁ _ (Finset.union_subset hd (hu.trans Finset.sdiff_subset)) hleft
    simp only [firstCommonWeight,firstCommonCoefficient,hz,mul_zero,zero_mul,star_zero]

theorem firstPhysicalCommonRows_fixed_pool (F G : Finset ι) (hFG : F⊆G)
    (C₁ C₂ : Finset ι→ℂ) (hC₁ : ∀U,U⊆G → ¬U⊆F → C₁ U=0)
    (hC₂ : ∀U,U⊆G → ¬U⊆F → C₂ U=0)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h=
      firstPhysicalCommonRows p hg G C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed,firstPhysicalCommonRows_indexed]
  exact Finset.sum_subset (firstCommonIndices_mono hFG) (fun j hj hn=>by
    rw [firstCommonWeight_zero_outside p hg F G C₁ C₂ h hC₁ hC₂ j hj hn,zero_mul])

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0661

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstRetainedFamily
Source SHA256: d3e85ec3240fa6d5e622bed773da8261fa72301964166580230669f7bf07c44a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0662


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def firstRetainedSource (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ) :
    Finset (Ideal O×O) :=
  labels.biUnion (fun f=> (nonzeroChildFrequencyBall
    (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y).image
      (fun h=>(f,h)))

theorem mem_firstRetainedSource (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ)
    (x : Ideal O×O) :
    x∈firstRetainedSource p labels b Y ↔ x.1∈labels ∧ x.2∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y := by
  rcases x with ⟨f,h⟩
  simp [firstRetainedSource]

theorem sum_firstRetainedSource {A : Type*} [AddCommMonoid A]
    (p : ι→O) (labels : Finset (Ideal O)) (b : CubeCoordinates ι) (Y : ℝ) (H : Ideal O×O→A) :
    ∑ x∈firstRetainedSource p labels b Y,H x =
    ∑ f∈labels,∑ h∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) Y,H (f,h) := by
  unfold firstRetainedSource
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro f hf
    exact Finset.sum_image (fun h hh k hk he=>congrArg Prod.snd he)
  · intro f hf g hg hfg
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k,hk,he⟩ := Finset.mem_image.mp hy
    exact hfg (congrArg Prod.fst he).symm

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_retained_label_family
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (labels : Finset (Ideal O)) (a : Ideal O→ℂ) (R : Finset ι→ℝ) :
    (∑ f∈labels,a f*canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator f)
      (fun U=>H₁ U*W₁ (primeProductNorm p U)) (fun U=>H₂ U*W₂ (primeProductNorm p U)) Φ K
      (fun D=>childFrequencyBall
        (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R D))) =
    ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*
      ∑ x∈firstRetainedSource p labels b (R D),a x.1*
        canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)*
        firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)
          H₁ H₂ W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) x.2 := by
  simp_rw [canonical_retained_physical p hp hcop hg hinj hc hpr pool b hb C hC]
  simp only [Finset.mul_sum,sum_firstRetainedSource,nonzeroChildFrequencyBall]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro h hh
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0662

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstActualSecondEnergy
Source SHA256: f2067ddb45f96d138f68d0ac9b7ac032e85b4d07a0fa7ff914dc9d6d9f8be217
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0663



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCanonicalSecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (H selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  (32*512)*∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
        (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)) ω X (∏i∈C,p i) d core t Y).re

theorem firstCanonicalSecondEnergy_nonneg (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (H selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    0≤firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d H selector ω X t Y := by
  unfold firstCanonicalSecondEnergy
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro D hD
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro core hcore
  apply mul_nonneg (norm_nonneg _)
  rw [first_fresh_real_energy p hp hg hinj hc F D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m _ ω X (∏i∈C,p i) d core t Y hY]
  exact Finset.sum_nonneg (fun z hz=>mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _))

theorem first_retained_actual_second_energy (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ d : O) (labels : Finset (Ideal O)) (a : Ideal O×O→ℂ) (Γ Y : ℝ),0≤Γ → 0<Y →
      (∀ f∈labels,Squarefree f) → (∀ f∈labels,f≠0) → (∀ x∈firstRetainedSource p labels b Y,‖a x‖≤Γ) →
      ∀ (negative : Bool) (H selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t : ℝ),0<X →
      firstFamilyEnergy p hg (firstRetainedSource p labels b Y) F (fun _=>selector)
        (firstCanonicalCoefficient p hp hcop hg b C negative
          (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H)
        (retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a) negative ω X t Prod.snd ≤
      Γ*K*Y^ε * firstCanonicalSecondEnergy p hp hg hinj F b C negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H selector ω X t Y := by
  obtain ⟨K,hK,hstep⟩ := retained_cube_energy_to_second ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d labels a Γ Y hΓ hY
    hlabels hn ha negative H selector ω X t hX
  have he := hstep p hp hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a
    (firstRetainedSource p labels b Y) Γ Y hΓ hY
    (fun x hx=>hlabels x.1 ((mem_firstRetainedSource p labels b Y x).mp hx).1)
    (fun x hx=>hn x.1 ((mem_firstRetainedSource p labels b Y x).mp hx).1) ha
    (fun x hx=>((mem_firstRetainedSource p labels b Y x).mp hx).2)
    negative H selector ω X t hX
  have hcoef : firstCanonicalCoefficient p hp hcop hg b C negative
      (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) d H =
      fun x=>firstOldLabelCoefficient p hp hcop hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
        (multiplicativeCoreColumn p (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂)
          (fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)))
        (∏i∈C,p i) d x.1 := by
    funext x
    exact firstCanonicalCoefficient_old p hp hcop hg b C negative _ _ d H x
  rw [hcoef]
  exact he

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0663

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstActualPriorityEnergy
Source SHA256: a7825f1b398e352d687584a3d7c5f2d6049174f9581d5e00b1ea955f428b7611
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0664


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstPrioritySecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  let A := (if negative then b.rightDivisor else b.leftDivisor)∪C
  (32*512)*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
        (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
          (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U)
          ω X (∏i∈C,p i) d core t Y).re

theorem first_actual_second_prime_priority
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d
      (primeMark slots lists a) selector ω X t Y ≤
    firstPrioritySecondEnergy p hp hg hinj F b C negative Ψ m d slots lists a selector ω X t Y := by
  let A := (if negative then b.rightDivisor else b.leftDivisor)∪C
  have hb (r : RayCharacter×RayCharacter) (D : Finset ι) (core : FirstCoreIndex) :=
    first_fresh_priority_energy p hp hg hinj hc F D b.support A
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
      (if negative then r.1 else r.2) Ψ m slots lists a (fun _=>1)
      ω X (∏i∈C,p i) d core t Y hY
  simp only [mul_one] at hb
  unfold firstCanonicalSecondEnergy firstPrioritySecondEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro core hcore
  have h := mul_le_mul_of_nonneg_left (hb r D core)
    (show 0≤(32*512:ℝ)*(‖crossCoeff r.1 r.2‖*‖selector D‖)*
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖ from by positivity)
  convert h using 1
  · dsimp only [A]
    ring
  · simp only [A,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0664

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstGlobalPush
Source SHA256: 0bff2771fd76e30578c9eb22e597f747c1541de574d180a80c11f9346c301029
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0665


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι κ:Type*} [DecidableEq ι] [DecidableEq κ]

def firstGlobalRetainedSource (p:ι→Eis) (outer:Finset κ)
    (labels:κ→Finset (Ideal Eis)) (cube:κ→CubeCoordinates ι) (Y:ℝ):
    Finset (Σ _ : κ,Ideal Eis×Eis):=
  outer.sigma (fun k=>firstRetainedSource p (labels k) (cube k) Y)

omit [DecidableEq κ] in
theorem first_global_retained_push (ε:ℝ)(hε:0<ε):
    ∃ K:ℝ,0<K ∧ ∀ (p:ι→Eis)(hp:∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F:Finset ι)(outer:Finset κ)(cube:κ→CubeCoordinates ι)(common:κ→Finset ι)
    (Ψ₁ Ψ₂:Eis→*ℂ)(m₁ m₂:Eis)(d:κ→Eis)
    (labels:κ→Finset (Ideal Eis))(a:κ→Ideal Eis×Eis→ℂ)(Γ Y:ℝ),
    (∀u,‖Ψ₁ u‖≤1)→(∀u,‖Ψ₂ u‖≤1)→0≤Γ→0<Y→
    (∀k∈outer,∀f∈labels k,Squarefree f)→(∀k∈outer,∀f∈labels k,f≠0)→
    (∀k∈outer,∀x∈firstRetainedSource p (labels k) (cube k) Y,‖a k x‖≤Γ)→
    ∀(negative:Bool)(H selector:κ→Finset ι→ℂ)(ω:ℝ→ℂ)(X t:ℝ),0<X→
    firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels cube Y) F
      (fun x=>selector x.1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg (cube x.1) (common x.1) negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d x.1) (H x.1) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg (cube x.1) (common x.1) Ψ₁ Ψ₂ m₁ m₂
        (d x.1) (a x.1) x.2)
      negative ω X t (fun x=>x.2.2) ≤
    Γ*K*Y^ε*∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (cube k) (common k)
      negative (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d k)
      (H k) (selector k) ω X t Y := by
  obtain ⟨K,hK,hpush⟩:=first_retained_actual_second_energy ε hε
  refine ⟨K,hK,?_⟩
  intro p hp _ hinj hcop hg hc hpr F outer cube common Ψ₁ Ψ₂ m₁ m₂ d labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hs hn ha negative H selector ω X t hX
  simp only [firstFamilyEnergy,firstGlobalRetainedSource,Finset.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact hpush p hp hinj hcop hg hc hpr F (cube k) (common k) Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂
    (d k) (labels k) (a k) Γ Y hΓ hY (hs k hk) (hn k hk) (ha k hk)
    negative (H k) (selector k) ω X t hX

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0665

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceIndex
Source SHA256: 401de52f63a4d36127a87cce6cda53a0c216cf92eac998e3b3d0863d20e239d0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0666



namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

abbrev FirstOriginalOuter (ι : Type*) := Σ _ : CubeCoordinates ι,Σ _ : Finset ι,Finset ι

def firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) : Finset (FirstOriginalOuter ι) :=
  (reopenedCubeFamily Q).sigma (fun b=>(pool\b.support).powerset.sigma
    (fun C=>(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset))

lemma mem_firstOriginalOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : FirstOriginalOuter ι) :
    k∈firstOriginalOuter pool Q ↔ k.1∈reopenedCubeFamily Q ∧ k.2.1∈(pool\k.1.support).powerset ∧
      k.2.2∈(k.2.1∪cubePrincipalSupport k.1.support k.1.leftExponent k.1.rightExponent k.1.leftBit k.1.rightBit).powerset := by
  simp [firstOriginalOuter]

lemma retained_cutoff_enlargement (E : O) (hE : E≠0) (R Y : ℝ) (hRY : R≤Y) (f : O→ℂ) :
    (∑h∈(childFrequencyBall E R).erase 0,f h)=
      ∑h∈nonzeroChildFrequencyBall E Y,(if h∈childFrequencyBall E R then (1:ℂ) else 0)*f h := by
  have hsub : (childFrequencyBall E R).erase 0⊆nonzeroChildFrequencyBall E Y := by
    intro h hh
    rcases Finset.mem_erase.mp hh with ⟨hn,hm⟩
    exact Finset.mem_erase.mpr ⟨hn,(mem_childFrequencyBall E hE Y h).mpr
      (((mem_childFrequencyBall E hE R h).mp hm).trans hRY)⟩
  calc
    _=∑h∈(childFrequencyBall E R).erase 0,(if h∈childFrequencyBall E R then (1:ℂ) else 0)*f h := by
      apply Finset.sum_congr rfl
      intro h hh
      simp [(Finset.mem_erase.mp hh).2]
    _=_ := Finset.sum_subset hsub (by
      intro h hh hn
      have hne := (Finset.mem_erase.mp hh).1
      have hout : h∉childFrequencyBall E R := fun hm=>hn (Finset.mem_erase.mpr ⟨hne,hm⟩)
      simp [hout])

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstOriginalWeight (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (k : FirstOriginalOuter ι) (x : Ideal O×O) : ℂ :=
  reopenedPairCoefficient β k.1 k.2.1 x.1 *
    (UniqueFactorizationMonoid.moebius (∏i∈k.2.2,Ideal.span {p i}):ℂ) *
    (if x.2∈reopenedPhysicalCutoff p k.1 x.1 (R k.1 k.2.1 x.1) k.2.2 then 1 else 0)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma firstOriginalWeight_norm_le (β : Ideal O→(ι→₀ℕ)→ℂ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (k : FirstOriginalOuter ι) (x : Ideal O×O) :
    ‖firstOriginalWeight p β R k x‖≤‖reopenedPairCoefficient β k.1 k.2.1 x.1‖ := by
  unfold firstOriginalWeight
  split_ifs
  · simp only [mul_one,norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (CubicEisenstein.norm_ideal_moebius_le_one _)
  · simp

theorem original_retained_global_index
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y) :
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I mark W Φ K (R b C I)) =
    ∑x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y,
      firstOriginalWeight p β R x.1 x.2 *
      canonicalCubeOuter p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator x.2.1)*
      firstCubePhysicalMode p hp hcop hg pool x.1.1 x.1.2.1 Ψ Ψ m m
        (ConcretePrimeRowBridge.idealGenerator x.2.1) (mark x.1.1.rightExponent) (mark x.1.1.leftExponent)
        W W Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) x.2.2 := by
  simp only [firstGlobalRetainedSource,firstOriginalOuter,Finset.sum_sigma,sum_firstRetainedSource]
  unfold reopenedPhysicalSourceSum reopenedPhysicalRetained
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro C hC
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro f hf
  have hE := firstPhysicalMultiplier_ne_zero p hp b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit f (hlabels f hf)
  have hRY' := hRY ⟨b,⟨C,D⟩⟩ ((mem_firstOriginalOuter pool Q _).mpr ⟨hb,hC,hD⟩) f hf
  rw [show reopenedPhysicalCutoff p b f (R b C f) D=
    childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R b C f D) from rfl]
  rw [retained_cutoff_enlargement _ hE _ Y hRY']
  apply Finset.sum_congr rfl
  intro h hh
  simp only [firstOriginalWeight,reopenedPhysicalCutoff]
  ac_rfl

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0666

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourcePhysical
Source SHA256: 7b50289bb9abda83087c356a739f13ca18e0983f931b2bfe53e4a9a439e34ca6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0667



namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem firstCubePhysicalMode_fixed_pool (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ d : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (x : Ideal O×O) :
    firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator x.1) H₁ H₂ W₁ W₂ Φ K d x.2=
    (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d x.2 *
      firstPhysicalCommonRows p hg pool
        (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁ x)
        (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂ x)
        (fun y=>star (W₁ y)) W₂ Φ
        (‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
        (‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
        (primeProductNorm p C)
        (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d x.2 := by
  change _*firstPhysicalCommonRows p hg (pool\(b.support∪C))
      (firstCanonicalCoefficient p hp hcop hg b C true Ψ₁ m₁ d H₁ x)
      (firstCanonicalCoefficient p hp hcop hg b C false Ψ₂ m₂ d H₂ x) _ _ _ _ _ _ _ _ _ _ = _
  apply congrArg (fun z : ℂ =>
    (K : ℂ) * cubeBaseFactor p hp hg b.support
      (fun i => b.leftExponent i + b.rightExponent i) b.leftBit b.rightBit d x.2 * z)
  apply firstPhysicalCommonRows_fixed_pool p hg _ pool Finset.sdiff_subset
  · intro U hU hn
    apply firstCanonicalCoefficient_zero_overlap p hp hcop hg
    intro hd
    apply hn
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi,fun he=>Finset.disjoint_left.mp hd hi he⟩
  · intro U hU hn
    apply firstCanonicalCoefficient_zero_overlap p hp hcop hg
    intro hd
    apply hn
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hU hi,fun he=>Finset.disjoint_left.mp hd hi he⟩

theorem original_retained_global_family
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I mark W Φ K (R b C I)) =
    (K:ℂ)*firstFamilyPhysicalRows p hg
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y) pool
      (fun _ _=>1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 true Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.rightExponent) x.2)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 false Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.leftExponent) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (firstOriginalWeight p β R x.1) x.2)
      (fun y=>star (W ((s 0*s 2*s 5*s 7)*y))) (fun y=>W ((s 1*s 2*s 5*s 8)*y)) Φ
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.rightBit)‖^2)
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.leftBit)‖^2)
      (fun x=>primeProductNorm p x.1.2.1)
      (fun x=>primeProductNorm p (cubeActiveSupport x.1.1.support
        (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)) K
      (fun x=>primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (fun x=>x.2.2) s := by
  rw [original_retained_global_index p hp hcop hg pool Q labels hlabels β Ψ m mark W Φ K Y R hRY]
  have hleft : s 0*s 2*s 5*s 7≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (hs 0)) (ne_of_gt (hs 2))) (ne_of_gt (hs 5))) (ne_of_gt (hs 7))
  have hright : s 1*s 2*s 5*s 8≠0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt (hs 1)) (ne_of_gt (hs 2))) (ne_of_gt (hs 5))) (ne_of_gt (hs 8))
  have hw₁ : (fun y=>star (W ((s 0*s 2*s 5*s 7)*(y/(s 0*s 2*s 5*s 7)))))=fun y=>star (W y) := by
    funext y
    rw [mul_div_cancel₀ _ hleft]
  have hw₂ : (fun y=>W ((s 1*s 2*s 5*s 8)*(y/(s 1*s 2*s 5*s 8))))=W := by
    funext y
    rw [mul_div_cancel₀ _ hright]
  simp only [firstFamilyPhysicalRows,Finset.mul_sum,hw₁,hw₂]
  apply Finset.sum_congr rfl
  intro x hx
  rw [first_unblocked_physical,firstCubePhysicalMode_fixed_pool p hp hcop hg]
  unfold retainedCubeWeight
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0667

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstGlobalSourceEnergy
Source SHA256: dc6e8537b86f1a5082d6cb62bea5dcd3a5ecfb021c416e76cf4195fd57035822
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0668



namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def originalRetainedFamily
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ) (s : Fin 9→ℝ) : ℂ :=
  firstFamilyPhysicalRows p hg
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun k=>k.1) Y) pool
      (fun _ _=>1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 true Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.rightExponent) x.2)
      (fun x=>firstCanonicalCoefficient p hp hcop hg x.1.1 x.1.2.1 false Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (mark x.1.1.leftExponent) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg x.1.1 x.1.2.1 Ψ Ψ m m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (firstOriginalWeight p β R x.1) x.2)
      (fun y=>star (W ((s 0*s 2*s 5*s 7)*y))) (fun y=>W ((s 1*s 2*s 5*s 8)*y)) Φ
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.rightBit)‖^2)
      (fun x=>‖eisEmbedding (aLabel p x.1.1.support x.1.1.leftBit)‖^2)
      (fun x=>primeProductNorm p x.1.2.1)
      (fun x=>primeProductNorm p (cubeActiveSupport x.1.1.support
        (fun i=>x.1.1.leftExponent i+x.1.1.rightExponent i) x.1.1.leftBit x.1.1.rightBit)) K
      (fun x=>primeSubsetGenerator (fun i=>Ideal.span {p i}) x.1.2.2) (fun x=>x.2.2) s

theorem original_global_physical_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (K Y : ℝ) (hK : 0<K)
    (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D)
    (hRY : ∀k∈firstOriginalOuter pool Q,∀f∈labels,R k.1 k.2.1 f k.2.2≤Y)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark v U*W (primeProductNorm p U)) z) K ≤
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark b.leftExponent U*W (primeProductNorm p U)) rowMajorant K)‖ +
    K*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W rowMajorant K Y R s‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark b.leftExponent U*W (primeProductNorm p U)) rowMajorant K
        (reopenedPhysicalCutoff p b I (R b C I)))‖ := by
  have he := original_reopened_physical_energy p hp hcop hg hinj hc hpr pool Q hQ labels hlabels
    β Ψ m (fun _=>mark) W K hK R hR
  rw [original_retained_global_family p hp hcop hg pool Q labels hlabels β Ψ m mark W rowMajorant K Y R hRY s hs] at he
  simpa only [originalRetainedFamily,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hK] using he

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0668

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstUnequalPhysicalEnergy
Source SHA256: 4d937c2c6c6519b445dd2d0ad81646fc032225804aa269c0291a9322cfa121ba
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0669



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_first_family_two_energies (hp : ∀ i,p i ≠ 0)
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 9 → ℝ → ℂ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (hs : ∀ i,0 < s i) (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 9 → ℝ,
      (Real.exp (-(9/2:ℝ)*L):ℂ)*firstPoissonProfile W₁ W₂ Φ V
        (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) y =
      ∫ z : Frequency × (Fin 9 → ℝ),density z*
        pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y z.1 z.2)
    (hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₁ (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      W₂ (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,V i (firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i) = 1)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hWeighted : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w W₁ W₂ Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
  have he := actual_first_balanced_family p hg hp source F selector C₁ C₂ w
    W₁ W₂ ω₁ ω₂ Φ V A₁ A₂ C R K L d h s hpos hs density hDensity hsep hω₁ hω₂ hcut
  have hb := first_family_integral_of_two_energies p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s
    density J B₁ B₂ hB₁ hB₂ hWeighted hleft hright
  have hn := congrArg norm he
  conv_lhs at hn => rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  conv_rhs at hn => rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (firstRootScale_pos s hs)]
  have hexp : Real.exp ((9/2:ℝ)*L)*Real.exp (-(9/2:ℝ)*L) = 1 := by
    rw [←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hn' := congrArg (fun a : ℝ => Real.exp ((9/2:ℝ)*L)*a) hn
  rw [←mul_assoc,hexp,one_mul] at hn'
  rw [←mul_assoc,←div_eq_mul_inv] at hn'
  rw [hn']
  exact mul_le_mul_of_nonneg_left hb (by have := firstRootScale_pos s hs; positivity)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0669

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileUniform
Source SHA256: bbd8159319b6dca98b7b7014c793a51fdbd7f496769c708a65e2079c85616b37
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0670



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_moving_family_two_energies_uniform
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile : ℝ,0 ≤ Cprofile ∧ ∀ {ι κ : Type*} [DecidableEq ι] (p : ι → Eis) (_hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (_hK : 0 < K) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (_hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (_hs : ∀ i,0 < s i)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hmeasure⟩ := InverseMomentFirstProfileUniform.first_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨Cprofile,hCprofile,?_⟩
  intro ι κ _ p hp _ hg source F selector C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK d h s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hRad : 0 < K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8) := by
    exact div_pos (mul_pos hK (hs 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (hs 3) (hs 4)) (sq_pos_of_pos (hs 5))) (hs 7)) (hs 8))
  obtain ⟨b₃,hb₃⟩ := hmeasure (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := first_balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_first_family_two_energies p hg hp source F selector C₁ C₂ w
    (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) ω₁ ω₂ Φ (fun i y => U₀ i (y+ρ i))
    A₁ A₂ C R K L d h s hpos hs den hden hsep hω₁ hω₂ hcut
    J B₁ B₂ hB₁ hB₂ hWeighted hleft hright
  have hd : (∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖den z‖) ≤
      Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker := by
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) Aker)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (by have := firstRootScale_pos s hs; positivity))

theorem first_global_retained_push_uniform (ε:ℝ)(hε:0<ε):
    ∃ K:ℝ,0<K ∧ ∀ {ι κ:Type*} [DecidableEq ι] [DecidableEq κ] (p:ι→Eis)(hp:∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F:Finset ι)(outer:Finset κ)(cube:κ→CubeCoordinates ι)(common:κ→Finset ι)
    (Ψ₁ Ψ₂:Eis→*ℂ)(m₁ m₂:Eis)(d:κ→Eis)
    (labels:κ→Finset (Ideal Eis))(a:κ→Ideal Eis×Eis→ℂ)(Γ Y:ℝ),
    (∀u,‖Ψ₁ u‖≤1)→(∀u,‖Ψ₂ u‖≤1)→0≤Γ→0<Y→
    (∀k∈outer,∀f∈labels k,Squarefree f)→(∀k∈outer,∀f∈labels k,f≠0)→
    (∀k∈outer,∀x∈firstRetainedSource p (labels k) (cube k) Y,‖a k x‖≤Γ)→
    ∀(negative:Bool)(H selector:κ→Finset ι→ℂ)(ω:ℝ→ℂ)(X t:ℝ),0<X→
    firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels cube Y) F
      (fun x=>selector x.1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg (cube x.1) (common x.1) negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d x.1) (H x.1) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg (cube x.1) (common x.1) Ψ₁ Ψ₂ m₁ m₂
        (d x.1) (a x.1) x.2)
      negative ω X t (fun x=>x.2.2) ≤
    Γ*K*Y^ε*∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (cube k) (common k)
      negative (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d k)
      (H k) (selector k) ω X t Y := by
  obtain ⟨K,hK,hpush⟩:=first_retained_actual_second_energy ε hε
  refine ⟨K,hK,?_⟩
  intro ι κ _ _ p hp _ hinj hcop hg hc hpr F outer cube common Ψ₁ Ψ₂ m₁ m₂ d labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hs hn ha negative H selector ω X t hX
  simp only [firstFamilyEnergy,firstGlobalRetainedSource,Finset.sum_sigma]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  exact hpush p hp hinj hcop hg hc hpr F (cube k) (common k) Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂
    (d k) (labels k) (a k) Γ Y hΓ hY (hs k hk) (hn k hk) (ha k hk)
    negative (H k) (selector k) ω X t hX

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0670

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileFiltered
Source SHA256: 146052f21a0ed35e717aa9d95ca468cb2a1f1f5719281e2c54ceac16a798723e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0671



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_original_subset_two_energies (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (outer:Finset κ) (b : κ→SecondPassArithmetic.CubeCoordinates ι) (common : κ→Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright : Eis) (dd:κ→Eis) (H₁ H₂ selector : κ→Finset ι→ℂ)
    (labels : κ→Finset (Ideal Eis)) (a : κ→Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀k∈outer,∀ f∈labels k,Squarefree f) (_hn : ∀k∈outer,∀ f∈labels k,f≠0)
    (_ha : ∀k∈outer,∀ x∈firstRetainedSource p (labels k) (b k) Y,‖a k x‖≤Γ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : (Σ _ : κ,Ideal Eis×Eis) → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i)
    (selected : Finset (Σ _ : κ,Ideal Eis×Eis))
    (_hselected : selected⊆firstGlobalRetainedSource p outer labels b Y),
    let source := selected
    let C₁ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) true Ψ₁ mleft (dd x.1) (H₁ x.1) x.2
    let C₂ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) false Ψ₂ mright (dd x.1) (H₂ x.1) x.2
    let w := fun x : (Σ _ : κ,Ideal Eis×Eis) => retainedCubeWeight p hp hcop hg (b x.1) (common x.1) Ψ₁ Ψ₂ mleft mright (dd x.1) (a x.1) x.2
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd x.1≠0 ∧ x.2.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (dd x.1) x.2.2 j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) true Ψ₁ mleft (dd k) (H₁ k) (selector k) ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y) ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) false Ψ₂ mright (dd k) (H₂ k) (selector k) ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y) ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F (fun x=>selector x.1) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun x=>dd x.1) (fun x=>x.2.2) s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂))*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hprofile⟩ := actual_first_moving_family_two_energies_uniform
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Kpush,hKpush,hpush⟩ := first_global_retained_push_uniform ε hε
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro ι κ _ _ p hp _ hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hweight : 0≤Γ*Kpush*Y^ε := by positivity
  have hroot:Real.sqrt (Γ*Kpush*Y^ε*B₁)*Real.sqrt (Γ*Kpush*Y^ε*B₂)=Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂):=by
    rw [Real.sqrt_mul hweight,Real.sqrt_mul hweight]
    calc
      _=(Real.sqrt (Γ*Kpush*Y^ε))^2*(Real.sqrt B₁*Real.sqrt B₂):=by ring
      _= _:=by rw [Real.sq_sqrt hweight]
  rw [←hroot]
  apply hprofile p hp hg source F (fun x=>selector x.1) C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK (fun x=>dd x.1) (fun x=>x.2.2) s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut (Γ*Kpush*Y^ε*B₁) (Γ*Kpush*Y^ε*B₂) (mul_nonneg hweight hB₁) (mul_nonneg hweight hB₂)
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd
      labels a Γ Y hΨ₁ hΨ₂ hΓ hY hlabels hn ha true H₁ selector ω₁ (s 7)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (hs 7)
    simp only [ite_true,] at he
    have hm1 : firstFamilyEnergy p hg source F (fun x=>selector x.1) C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (fun x=>x.2.2) ≤
        firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels b Y) F
        (fun x=>selector x.1) C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (fun x=>x.2.2) := by
      unfold firstFamilyEnergy
      exact Finset.sum_le_sum_of_subset_of_nonneg hselected (fun x hx hn=>
        mul_nonneg (norm_nonneg _) (firstBlockEnergy_nonneg p hg _ _ _ _ _ _ _ _))
    apply (hm1.trans he).trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hleft z) hweight
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd
      labels a Γ Y hΨ₁ hΨ₂ hΓ hY hlabels hn ha false H₂ selector ω₂ (s 8)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (hs 8)
    simp only [ite_false,Bool.false_eq_true] at he
    have hm2 : firstFamilyEnergy p hg source F (fun x=>selector x.1) C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (fun x=>x.2.2) ≤
        firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels b Y) F
        (fun x=>selector x.1) C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (fun x=>x.2.2) := by
      unfold firstFamilyEnergy
      exact Finset.sum_le_sum_of_subset_of_nonneg hselected (fun x hx hn=>
        mul_nonneg (norm_nonneg _) (firstBlockEnergy_nonneg p hg _ _ _ _ _ _ _ _))
    apply (hm2.trans he).trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hright z) hweight

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0671

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstUnequalMovingEnergy
Source SHA256: 2f82ceab07d281116aee6e22c84affb3a6216263ae64a1176d70c1e6a7df48ca
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0672


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
variable {ι κ : Type*} [DecidableEq ι]
theorem actual_first_moving_family_two_energies
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile : ℝ,0 ≤ Cprofile ∧ ∀ (p : ι → Eis) (_hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (source : Finset κ) (F : Finset ι) (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : κ → ℝ) (K L : ℝ) (_hK : 0 < K) (d h : κ → Eis) (s : Fin 9 → ℝ)
    (_hpos : ∀ x∈source,0 < A₁ x ∧ 0 < A₂ x ∧ 0 < C x ∧ 0 < R x ∧ d x ≠ 0 ∧ h x ≠ 0)
    (_hs : ∀ i,0 < s i)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) (h x) j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F selector C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K d h s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Real.sqrt B₁*Real.sqrt B₂)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hmeasure⟩ := InverseMomentFirstProfileUniform.first_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨Cprofile,hCprofile,?_⟩
  intro p hp _ hg source F selector C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK d h s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hRad : 0 < K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8) := by
    exact div_pos (mul_pos hK (hs 6))
      (mul_pos (mul_pos (mul_pos (mul_pos (hs 3) (hs 4)) (sq_pos_of_pos (hs 5))) (hs 7)) (hs 8))
  obtain ⟨b₃,hb₃⟩ := hmeasure (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := first_balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_first_family_two_energies p hg hp source F selector C₁ C₂ w
    (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) ω₁ ω₂ Φ (fun i y => U₀ i (y+ρ i))
    A₁ A₂ C R K L d h s hpos hs den hden hsep hω₁ hω₂ hcut
    J B₁ B₂ hB₁ hB₂ hWeighted hleft hright
  have hd : (∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖den z‖) ≤
      Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker := by
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < 1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8)) Aker)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    (by have := firstRootScale_pos s hs; positivity))

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0672

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstUnequalRetainedEnergy
Source SHA256: e2a85f879a30cca4d0faaddf8761550810601de936fb6ded307a5d457280fe53
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0673



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
variable {ι : Type*} [DecidableEq ι]
theorem actual_first_retained_two_energies (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (b : SecondPassArithmetic.CubeCoordinates ι) (common : Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright dd : Eis) (H₁ H₂ selector : Finset ι→ℂ)
    (labels : Finset (Ideal Eis)) (a : Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀ f∈labels,Squarefree f) (_hn : ∀ f∈labels,f≠0)
    (_ha : ∀ x∈firstRetainedSource p labels b Y,‖a x‖≤Γ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : Ideal Eis×Eis → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i),
    let source := firstRetainedSource p labels b Y
    let C₁ := firstCanonicalCoefficient p hp hcop hg b common true Ψ₁ mleft dd H₁
    let C₂ := firstCanonicalCoefficient p hp hcop hg b common false Ψ₂ mright dd H₂
    let w := retainedCubeWeight p hp hcop hg b common Ψ₁ Ψ₂ mleft mright dd a
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd≠0 ∧ x.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2 j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) dd x.2 j) s i)+ρ i) = 1)
    (B₁ B₂ : ℝ) (_hB₁ : 0 ≤ B₁) (_hB₂ : 0 ≤ B₂)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstCanonicalSecondEnergy p hp hg hinj F b common true Ψ₁ mleft dd H₁ selector ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstCanonicalSecondEnergy p hp hg hinj F b common false Ψ₂ mright dd H₂ selector ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)),
    ‖firstFamilyPhysicalRows p hg source F (fun _=>selector) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun _=>dd) Prod.snd s‖ ≤
      (Real.exp ((9/2:ℝ)*L)/firstRootScale s)*
        ((Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂))*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,hCprofile,hprofile⟩ := actual_first_moving_family_two_energies (ι := ι) (κ := Ideal Eis×Eis)
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Kpush,hKpush,hpush⟩ := first_retained_actual_second_energy ε hε
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro p hp _ hg hinj hcop hc hpr F b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut B₁ B₂ hB₁ hB₂ hleft hright
  have hweight : 0≤Γ*Kpush*Y^ε := by positivity
  have hroot:Real.sqrt (Γ*Kpush*Y^ε*B₁)*Real.sqrt (Γ*Kpush*Y^ε*B₂)=Γ*Kpush*Y^ε*(Real.sqrt B₁*Real.sqrt B₂):=by
    rw [Real.sqrt_mul hweight,Real.sqrt_mul hweight]
    calc
      _=(Real.sqrt (Γ*Kpush*Y^ε))^2*(Real.sqrt B₁*Real.sqrt B₂):=by ring
      _= _:=by rw [Real.sq_sqrt hweight]
  rw [←hroot]
  apply hprofile p hp hg source F (fun _=>selector) C₁ C₂ w ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂
    A₁ A₂ C R K L hK (fun _=>dd) Prod.snd s hpos hs hρ hc₁ hc₂ hc₁b hc₂b hL
    hω₁ hω₂ hcut (Γ*Kpush*Y^ε*B₁) (Γ*Kpush*Y^ε*B₂) (mul_nonneg hweight hB₁) (mul_nonneg hweight hB₂)
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F b common Ψ₁ Ψ₂ hΨ₁ hΨ₂ mleft mright dd
      labels a Γ Y hΓ hY hlabels hn ha true H₁ selector ω₁ (s 7)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) (hs 7)
    apply he.trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hleft z) hweight
  · intro z
    have he := hpush p hp hinj hcop hg hc hpr F b common Ψ₁ Ψ₂ hΨ₁ hΨ₂ mleft mright dd
      labels a Γ Y hΓ hY hlabels hn ha false H₂ selector ω₂ (s 8)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) (hs 8)
    apply he.trans
    simpa only [mul_assoc,ite_true,ite_false,Bool.false_eq_true] using mul_le_mul_of_nonneg_left (hright z) hweight

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0673

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstHeightBudget
Source SHA256: dd80a982fb46ef45eb012101b02bd82352d2f094064ebfe6c4111e125b6d6c03
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0674


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open JointLogSeparation InverseAmbientProfileTower

theorem first_left_height_budget (J:ℕ)(p:Ambient (Fin 9)):
    (1+‖profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 7‖)^J≤
      tripleHeight J p.1*coordinateHeight J p.2:=by
  have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedLeft 7 p‖) (inheritedLeft_bound 7 p) J
  rw [←ambientWeight_eq_pow] at h
  simpa only [first_inherited_left_eq,ambientWeight,tripleHeight,coordinateHeight] using h

theorem first_right_height_budget (J:ℕ)(p:Ambient (Fin 9)):
    (1+‖profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 8‖)^J≤
      tripleHeight J p.1*coordinateHeight J p.2:=by
  have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedRight 8 p‖) (inheritedRight_bound 8 p) J
  rw [←ambientWeight_eq_pow] at h
  simpa only [first_inherited_right_eq,norm_neg,ambientWeight,tripleHeight,coordinateHeight] using h

theorem first_unequal_prefactor (Z:ℝ)(hZ:0<Z)
    (M r ell V delta A₁ A₂ B R t h eta:ℝ):
    (Z^(-r-2*ell-V)*Z^M/firstRootScale
      (fun i=>Z^(![A₁,A₂,B,delta,R,t,h,r-A₁-B-t,r-A₂-B-t] i)))*
      Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (Real.sqrt ((Z^(firstKappa M r ell V delta A₁ B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))⁻¹)*
       Real.sqrt ((Z^(firstKappa M r ell V delta A₂ B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))⁻¹))=1:=by
  rw [first_physical_scalar Z hZ]
  have he:Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^((9/2:ℝ)*eta):=by
    rw [Real.rpow_def_of_pos hZ];congr 1;ring
  rw [he,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  rw [←Real.rpow_neg hZ.le,←Real.rpow_neg hZ.le,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  convert Real.rpow_zero Z using 1
  congr 1
  ring
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0674

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfilePhysical
Source SHA256: 16e718b51b774b8bbdb1af7c0321189cf7b21724ab7342b0ddbfda5a471ce4a1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0675



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseMomentFirstProfileUniform InverseAmbientProfileTower
theorem actual_first_original_subset_physical_budget (ε : ℝ) (hε : 0<ε)
    (U₀ : Fin 9 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 9 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ Cprofile Kpush : ℝ,0 ≤ Cprofile ∧ 0<Kpush ∧ ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (_hc : ∀ i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F : Finset ι) (outer:Finset κ) (b : κ→SecondPassArithmetic.CubeCoordinates ι) (common : κ→Finset ι)
    (Ψ₁ Ψ₂ : Eis→*ℂ) (mleft mright : Eis) (dd:κ→Eis) (H₁ H₂ selector : κ→Finset ι→ℂ)
    (labels : κ→Finset (Ideal Eis)) (a : κ→Ideal Eis×Eis→ℂ) (Γ Y : ℝ)
    (_hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (_hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (_hΓ : 0≤Γ) (_hY : 0<Y)
    (_hlabels : ∀k∈outer,∀ f∈labels k,Squarefree f) (_hn : ∀k∈outer,∀ f∈labels k,f≠0)
    (_ha : ∀k∈outer,∀ x∈firstRetainedSource p (labels k) (b k) Y,‖a k x‖≤Γ)
    (ω₁ ω₂ : ℝ → ℂ) (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
    (A₁ A₂ C R : (Σ _ : κ,Ideal Eis×Eis) → ℝ) (K L : ℝ) (_hK : 0<K) (s : Fin 9→ℝ)
    (_hs : ∀ i,0<s i)
    (selected : Finset (Σ _ : κ,Ideal Eis×Eis))
    (_hselected : selected⊆firstGlobalRetainedSource p outer labels b Y),
    let source := selected
    let C₁ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) true Ψ₁ mleft (dd x.1) (H₁ x.1) x.2
    let C₂ := fun x : (Σ _ : κ,Ideal Eis×Eis) => firstCanonicalCoefficient p hp hcop hg (b x.1) (common x.1) false Ψ₂ mright (dd x.1) (H₂ x.1) x.2
    let w := fun x : (Σ _ : κ,Ideal Eis×Eis) => retainedCubeWeight p hp hcop hg (b x.1) (common x.1) Ψ₁ Ψ₂ mleft mright (dd x.1) (a x.1) x.2
    ∀ (_hpos : ∀ x∈source,0<A₁ x ∧ 0<A₂ x ∧ 0<C x ∧ 0<R x ∧ dd x.1≠0 ∧ x.2.2≠0)
    (_hρ : ∀ i,|ρ i| ≤ B₀ i) (_hc₁ : 1 ≤ c₁) (_hc₂ : 1 ≤ c₂)
    (_hc₁b : c₁ ≤ bcap) (_hc₂b : c₂ ≤ bcap) (_hL : 0 ≤ L)
    (_hω₁ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₁ c₁ θ₁) (A₁ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.1/(s 0*s 2*s 5*s 7)) ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) = 1)
    (_hω₂ : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      (positiveSource g₂ c₂ θ₂) (A₂ x*C x*primeProductNorm p j.2.1*primeProductNorm p j.2.2.2/(s 1*s 2*s 5*s 8)) ≠ 0 →
      ω₂ (primeProductNorm p j.2.2.2/s 8) = 1)
    (_hcut : ∀ x∈source,∀ j∈firstCommonIndices F,
      selector x.1 j.2.1*firstCommonWeight p hg (C₁ x) (C₂ x) x.2.2 j ≠ 0 →
      ω₁ (primeProductNorm p j.2.2.1/s 7) ≠ 0 → ω₂ (primeProductNorm p j.2.2.2/s 8) ≠ 0 →
      ∀ i,U₀ i ((firstRelativeLog (firstCommonNorms p (A₁ x) (A₂ x) (C x) (R x) (dd x.1) x.2.2 j) s i)+ρ i) = 1)
    (Benergy : ℝ) (_hBenergy : 0 ≤ Benergy)
    (Z M r ell V delta aa₁ aa₂ bb rr tq hh eta:ℝ) (_hZ:0<Z)
    (_hscale:s=fun i=>Z^(![aa₁,aa₂,bb,delta,rr,tq,hh,r-aa₁-bb-tq,r-aa₂-bb-tq] i))
    (_hLe:L=eta*Real.log Z)
    (_hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      (Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) true Ψ₁ mleft (dd k) (H₁ k) (selector k) ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y) ≤
        Benergy*(tripleHeight J z.1*coordinateHeight J z.2))
    (_hright : ∀ z : Frequency × (Fin 9 → ℝ),
      (Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (b k) (common k) false Ψ₂ mright (dd k) (H₂ k) (selector k) ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y) ≤
        Benergy*(tripleHeight J z.1*coordinateHeight J z.2)),
    (Z^(-r-2*ell-V)*Z^M)*‖firstFamilyPhysicalRows p hg source F (fun x=>selector x.1) C₁ C₂ w (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂) Φ A₁ A₂ C R K (fun x=>dd x.1) (fun x=>x.2.2) s‖ ≤
      ((Γ*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)) := by
  obtain ⟨Cprofile,Kpush,hCprofile,hKpush,he⟩:=actual_first_original_subset_two_energies ε hε
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨Cprofile,Kpush,hCprofile,hKpush,?_⟩
  intro ι κ _ _ p hp _ hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    source C₁ C₂ w hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut Benergy hBenergy
    Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hZ hscale hLe hleft hright
  let P₁:=Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let P₂:=Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  have hp₁:0<P₁:=by dsimp [P₁];positivity
  have hp₂:0<P₂:=by dsimp [P₂];positivity
  have hb:=he p hp hg hinj hcop hc hpr F outer b common Ψ₁ Ψ₂ mleft mright dd H₁ H₂ selector labels a Γ Y
    hΨ₁ hΨ₂ hΓ hY hlabels hn ha ω₁ ω₂ ρ c₁ c₂ θ₁ θ₂ A₁ A₂ C R K L hK s hs selected hselected
    hpos hρ hc₁ hc₂ hc₁b hc₂b hL hω₁ hω₂ hcut (Benergy/P₁) (Benergy/P₂) (by positivity) (by positivity)
    (by intro z;rw [div_mul_eq_mul_div];apply (le_div_iff₀ hp₁).mpr;convert hleft z using 1 ; dsimp only [P₁] ; ring)
    (by intro z;rw [div_mul_eq_mul_div];apply (le_div_iff₀ hp₂).mpr;convert hright z using 1 ; dsimp only [P₂] ; ring)
  have hroot:Real.sqrt (Benergy/P₁)*Real.sqrt (Benergy/P₂)=Benergy*(Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹):=by
    simp only [div_eq_mul_inv,Real.sqrt_mul hBenergy]
    calc
      _=(Real.sqrt Benergy)^2*(Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹):=by ring
      _= _:=by rw [Real.sq_sqrt hBenergy]
  rw [hroot] at hb
  have hcancel:(Z^(-r-2*ell-V)*Z^M/firstRootScale s)*Real.exp ((9/2:ℝ)*L)*
      (Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹)=1:=by
    rw [hscale,hLe]
    exact first_unequal_prefactor Z hZ M r ell V delta aa₁ aa₂ bb rr tq hh eta
  have hnorm:0≤Z^(-r-2*ell-V)*Z^M:=by positivity
  apply (mul_le_mul_of_nonneg_left hb hnorm).trans_eq
  calc
    _=((Z^(-r-2*ell-V)*Z^M/firstRootScale s)*Real.exp ((9/2:ℝ)*L)*
      (Real.sqrt P₁⁻¹*Real.sqrt P₂⁻¹))*
      ((Γ*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))^Aker)):=by ring
    _= _:=by rw [hcancel,one_mul]
end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0675

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstWholeCubePriority
Source SHA256: eaa7b7d49ab530cccb2dca21bb85683fc3b12c42ecfdb6cc351d764cf67484f7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0676


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstWholePrioritySecondEnergy (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) : ℝ :=
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card * ∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
      ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
        (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m
          (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U)
          ω X (∏i∈C,p i) d core t Y).re

theorem first_actual_second_whole_cube_priority
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (F : Finset ι) (b : CubeCoordinates ι) (C extra : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    firstCanonicalSecondEnergy p hp hg hinj F b C negative Ψ m d
      (fun U=>primeMark slots lists a (extra∪U)) selector ω X t Y ≤
    firstWholePrioritySecondEnergy p hp hg hinj F b C extra negative Ψ m d slots lists a selector ω X t Y := by
  let A := extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have hb (r : RayCharacter×RayCharacter) (D : Finset ι) (core : FirstCoreIndex) :=
    first_fresh_priority_energy p hp hg hinj hc F D b.support A
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
      (if negative then r.1 else r.2) Ψ m slots lists a (fun _=>1)
      ω X (∏i∈C,p i) d core t Y hY
  simp only [mul_one] at hb
  unfold firstCanonicalSecondEnergy firstWholePrioritySecondEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro core hcore
  have h := mul_le_mul_of_nonneg_left (hb r D core)
    (show 0≤(32*512:ℝ)*(‖crossCoeff r.1 r.2‖*‖selector D‖)*
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖ from by positivity)
  convert h using 1
  · dsimp only [A]
    simp only [Finset.union_assoc]
    ring
  · simp only [A,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro J hJ
    ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0676

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondBalancedSource
Source SHA256: 7b0bd075db0d9df492059b1f8b9e5d76293d9b28bc5fc0f7ed724c5a52dd21c9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0677



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem balanced_density_integrable (g : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) :
    Integrable (InverseSecondProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L) := by
  exact (full_density_integrable _ _ _ _).const_mul _

theorem balanced_density_weighted_integrable (g : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ,ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun t : Frequency × (Fin 6 → ℝ) => tripleHeight J t.1*coordinateHeight J t.2*
      ‖InverseSecondProfileUniform.density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L t‖) :=
  InverseSecondProfileUniform.density_weighted_integrable g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L J

variable {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_source (source : Finset κ) (F : Finset ι)
    (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6 → ℝ → ℂ)
    (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 6 → ℝ,
      (Real.exp (-6*L):ℂ) * secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ V
        (Y*K₀/(E₀*V₀^2*X₀^2)) y =
      ∫ t : Frequency × (Fin 6 → ℝ), density t *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2)
    (hn : ∀ j ∈ source,(x j).divisor ≠ 0 ∧ (x j).frequency ≠ 0)
    (hω₁ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₁ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₁ (primeProductNorm p N/X₀) = 1)
    (hω₂ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₂ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₂ (primeProductNorm p N/X₀) = 1)
    (hcut : ∀ j ∈ secondProfileIndices source F x,
      ω₁ (primeProductNorm p j.2.1/X₀) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L):ℂ) * (∑ j ∈ source,w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
    ((E₀*V₀*X₀:ℝ):ℂ)⁻¹ * ∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ j ∈ source,w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t := by
  apply actualSecondFreshRows_normalized_density p hp hcop hg source F x w
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ Y G₀ E₀ V₀ K₀ X₀ density hDensity
  intro j hj
  obtain ⟨hjS,hN,hM⟩ := (mem_secondProfileIndices source F x j).mp hj
  have h1 : star (W₁ (primeProductNorm p (x j.1).common*primeProductNorm p (x j.1).overlap*
      primeProductNorm p j.2.1/(G₀*V₀*X₀))) ≠ 0 → star (ω₁ (primeProductNorm p j.2.1/X₀)) = 1 := by
    intro hh
    rw [hω₁ j.1 hjS j.2.1 hN (star_ne_zero.mp hh),star_one]
  have h2 := hω₂ j.1 hjS j.2.2 hM
  have h3 : star (ω₁ (primeProductNorm p j.2.1/X₀)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1 :=
    fun ha hb => hcut j hj (star_ne_zero.mp ha) hb
  have he := InverseSecondProfileUniform.fresh_physical_profile
    (fun x => star (W₁ x)) W₂ Φ V G₀ E₀ V₀ K₀ X₀ Y L hG hE hV hK hX
    (fun x => star (ω₁ x)) ω₂ (secondActualNorms p (x j.1) j.2.1 j.2.2)
    (secondActualNorms_pos p hp (x j.1) (hn j.1 hjS).1 (hn j.1 hjS).2 j.2.1 j.2.2)
    (by simpa [secondActualNorms] using h1)
    (by simpa [secondActualNorms] using h2)
    (by simpa [secondActualNorms] using h3)
  rw [hsep] at he
  simpa [secondActualNorms] using he

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0677

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondBalancedPhysical
Source SHA256: 2bf85c4ff98de91d70633555109323ba7cc122c65e671b5c6095fd5a2f694956
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0678



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondBalancedPhysicalUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
universe u₁ u₂
variable {ι : Type u₁} {σ : Type u₂} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_profile_children
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      0 < G → 0 < E → 0 < V → 0 < B → 0 < X → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*X^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₁ (primeProductNorm p N/X) = 1) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₂ (primeProductNorm p N/X) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/X) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B X i) = 1) →
      (Real.exp (-6*L):ℂ) * ((Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*X))) =
      ((Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹) *
        ∫ t : Frequency × (Fin 6 → ℝ),density t *
          ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,
            (w x*actualSecondSignedWeight p hp hcop hg Ψ
              (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
            ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
              secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
                ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := actual_second_modes_common_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
  have hn : ∀ x ∈ source,(secondInheritedProfile p x Ψ m z).divisor ≠ 0 ∧
      (secondInheritedProfile p x Ψ m z).frequency ≠ 0 := by
    intro x hx
    refine ⟨primeSubsetGenerator_ne_zero _ _,?_⟩
    have hh := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) R _).mp (hrows x hx)
    intro he
    change x.second.frequency = 0 at he
    simp only [he,mul_zero,map_zero,norm_zero,zero_pow (by omega : 2 ≠ 0),lt_self_iff_false] at hh
    exact hh.1
  have he := actual_second_balanced_source p hp hcop hg source pool
    (fun x : MarkedSecondSource ι Jo 0 => secondInheritedProfile p x Ψ m z)
    (fun x : MarkedSecondSource ι Jo 0 => w x*actualSecondSignedWeight p hp hcop hg Ψ
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ U G E V B X Y L
    hG hE hV hB hX density hDensity hsep hn hω₁ hω₂ hcut
  calc
    _ = ((Y:ℂ)*secondRayCoefficient z) * ((Real.exp (-6*L):ℂ)*
        ∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*X)) := by ring
    _ = _ := by
      rw [he]
      rw [←mul_assoc]
      apply congrArg (fun a : ℂ => ((Y:ℂ)*secondRayCoefficient z*((E*V*X:ℝ):ℂ)⁻¹)*a)
      apply integral_congr_ae
      filter_upwards with t
      apply congrArg (fun a : ℂ => density t*a)
      exact hsector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t _

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0678

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondPhysicalEnergy
Source SHA256: 771f16ef5dfd1bbde0919b95dac766cd553354187ccc97785d28027ec657e9e4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0679




namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondPhysicalEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_physical_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K J : ℕ) (A : ℝ),
      0 < G → 0 < E → 0 < V → 0 < B → 0 < X → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*X^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₁ (primeProductNorm p N/X) = 1) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₂ (primeProductNorm p N/X) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/X) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B X i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*X))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
  obtain ⟨sector,hsector⟩ := actual_second_balanced_profile_children p hp hcop hg hpr (σ:=σ) source hs
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w labels K J A hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have he := hsector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
  have hb := actual_second_all_modes_integral p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R labels hlabels hrows
    K ho hslots₁ hslots₂ w hw A hA J density hWeighted hleft hright
