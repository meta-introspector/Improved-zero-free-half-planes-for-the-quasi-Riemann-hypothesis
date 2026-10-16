          (gaussRow (a i) (ha i) h*star (gaussRow (b l) (hb l) (-h)))*K i l) := by
    by_cases hab : IsCoprime (a i) (b l)
    · simp only [hab,ite_true]
      rw [show dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h=_ from
        normalized_dilated_frequency P hcop hg hchar j hj0 hj6 e (a i) (b l) (ha i) (hb l)
          (hab.mul_right (har i)) (hbr l) k h]
      dsimp only [F,r,ρ]
      simp only [Complex.star_def,map_div₀,Complex.conj_ofReal]
      ring
    · simp [hab]
  simp_rw [ht,← Finset.mul_sum]
  rw [finite_first_children S T a b ha hb hpa hpb
    (fun i => c i/(‖eisEmbedding (a i)‖:ℂ)) (fun l => d l/(‖eisEmbedding (b l)‖:ℂ)) e r ρ
    (finiteSexticRow_mul P hg j) h K]

end SevenEighths.CenteredMomentFirstFrequency

end

end OAI
end OAIOriginalModule1533

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstScale
Source SHA256: dfb796bc931c984c2345a239276d4e12e16eee39fc07256090a5de85f163f192
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1534



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def firstNominalScale (I J E : Ideal O) (K X : ℝ) : ℝ :=
  (Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*X^2 /
    (K*(Ideal.absNorm (commonPart I J):ℝ)*(Ideal.absNorm (commonPart J I):ℝ))

theorem norm_pos (I : Ideal O) (hI : I≠0) : 0<(Ideal.absNorm I:ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem active_norm_pos (I J : Ideal O) :
    0<(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ) := by
  apply norm_pos
  exact Ideal.span_singleton_eq_bot.not.mpr (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)

theorem firstNominalScale_pos (I J E : Ideal O) (hE : E≠0) (K X : ℝ)
    (hK : 0<K) (hX : 0<X) : 0<firstNominalScale I J E K X := by
  unfold firstNominalScale
  exact div_pos (mul_pos (mul_pos (norm_pos E hE) (active_norm_pos I J)) (sq_pos_of_pos hX))
    (mul_pos (mul_pos hK (norm_pos _ (commonPart_ne_zero I J))) (norm_pos _ (commonPart_ne_zero J I)))

theorem first_kernel_ratio (I J E : Ideal O) (hI : I≠0) (hJ : J≠0) (hE : E≠0)
    (K X H : ℝ) (hK : 0<K) (hX : 0<X) :
    K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
      (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) =
      (H/firstNominalScale I J E K X)*(X^2/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) := by
  have hc := norm_pos _ (commonPart_ne_zero I J)
  have hd := norm_pos _ (commonPart_ne_zero J I)
  have he := norm_pos E hE
  have hr := active_norm_pos I J
  have ha := norm_pos _ (residualPart_ne_zero I J)
  have hb := norm_pos _ (residualPart_ne_zero J I)
  have hi : (Ideal.absNorm I:ℝ)=(Ideal.absNorm (commonPart I J):ℝ)*(Ideal.absNorm (residualPart I J):ℝ) := by
    exact_mod_cast absNorm_reconstruct I J hI
  have hj : (Ideal.absNorm J:ℝ)=(Ideal.absNorm (commonPart J I):ℝ)*(Ideal.absNorm (residualPart J I):ℝ) := by
    exact_mod_cast absNorm_reconstruct J I hJ
  rw [hi,hj]
  unfold firstNominalScale
  field_simp

theorem first_kernel_lower (I J E : Ideal O) (hI : I≠0) (hJ : J≠0) (hE : E≠0)
    (K X H HN : ℝ) (hK : 0<K) (hX : 0<X) (hH : 0≤H)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp HN*X)
    (hj : (Ideal.absNorm J:ℝ)≤Real.exp HN*X) :
    H/(Real.exp (2*HN)*firstNominalScale I J E K X) ≤
      K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  rw [first_kernel_ratio I J E hI hJ hE K X H hK hX]
  have hnI := norm_pos I hI
  have hnJ := norm_pos J hJ
  have hT := firstNominalScale_pos I J E hE K X hK hX
  have hh : (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)≤Real.exp (2*HN)*X^2 := by
    calc
      _ ≤ (Real.exp HN*X)*(Real.exp HN*X) := mul_le_mul hi hj hnJ.le (by positivity)
      _ = _ := by rw [show 2*HN=HN+HN by ring,Real.exp_add];ring
  have hr : 1/Real.exp (2*HN) ≤ X^2/((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
    apply (div_le_div_iff₀ (Real.exp_pos _) (mul_pos hnI hnJ)).mpr
    simpa only [one_mul,mul_comm] using hh
  calc
    _ = (H/firstNominalScale I J E K X)*(1/Real.exp (2*HN)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (div_nonneg hH hT.le)

theorem first_kernel_sector_lower (I J E : Ideal O) (hI : I≠0) (hJ : J≠0) (hE : E≠0)
    (K X H HN Tsec : ℝ) (hK : 0<K) (hX : 0<X) (hH : 0≤H)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp HN*X)
    (hj : (Ideal.absNorm J:ℝ)≤Real.exp HN*X)
    (hsec : firstNominalScale I J E K X≤Tsec) :
    (Real.exp (-2*HN)/Tsec)*H ≤
      K*H/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  have hT := firstNominalScale_pos I J E hE K X hK hX
  calc
    _ = H/(Real.exp (2*HN)*Tsec) := by rw [show -2*HN=-(2*HN) by ring,Real.exp_neg];ring
    _ ≤ H/(Real.exp (2*HN)*firstNominalScale I J E K X) :=
      div_le_div_of_nonneg_left hH (mul_pos (Real.exp_pos _) hT)
        (mul_le_mul_of_nonneg_left hsec (Real.exp_pos _).le)
    _ ≤ _ := first_kernel_lower I J E hI hJ hE K X H HN hK hX hH hi hj

end SevenEighths.CenteredMomentFirstScale

end

end OAI
end OAIOriginalModule1534

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactor
Source SHA256: b5e775ec8dd733a0528443488c6f64c11e9f406108ce72978586fce52d27addb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1535



namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon

lemma exceptional_core_nominal (K V E R C D A : ℝ)
    (hK:0<K)(hV:0<V)(hE:0<E)(hR:0<R)(hC:0<C)(hD:0<D)(hA:0<A):
    K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*A^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      (A/(E*R*V^2/(K*C*D)))^((5:ℝ)/6) := by
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi]; positivity
  · simp only [Set.mem_Ioi]; positivity
  · simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_rpow,
      Real.log_sqrt,Real.log_pow]
    ring

lemma amplified_nominal_ratio (Z T j g : ℝ)(hZ:1<Z)(hT:0<T):
    (Z^(j+g)/T)^((5:ℝ)/6)=Z^(5*(j-Real.logb Z T+g)/6) := by
  have hz:0<Z:=zero_lt_one.trans hZ
  rw [show j-Real.logb Z T+g=j+g-Real.logb Z T by ring]
  rw [show 5*(j+g-Real.logb Z T)/6=(j+g-Real.logb Z T)*((5:ℝ)/6) by ring,
    Real.rpow_mul hz.le,Real.rpow_sub hz,Real.rpow_logb hz (ne_of_gt hZ) hT]

theorem exceptional_core_log (K V E R C D Z j g : ℝ)
    (hK:0<K)(hV:0<V)(hE:0<E)(hR:0<R)(hC:0<C)(hD:0<D)(hZ:1<Z):
    K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (E*R*V^2/(K*C*D))+g)/6) := by
  rw [exceptional_core_nominal K V E R C D (Z^(j+g)) hK hV hE hR hC hD
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)]
  rw [amplified_nominal_ratio Z _ j g hZ (by positivity)]

theorem scalar_exceptional_bound (s μ H K V E R C D Z j g : ℝ)
    (hK:0<K)(hV:0<V)(hE:0<E)(hR:0<R)(hC:0<C)(hD:0<D)(hZ:1<Z)
    (hs:s*V≤μ*H*K*Real.sqrt (C*D)/(E*Real.sqrt R)):
    s/V*(V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) ≤
    μ*H*(V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(E^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (E*R*V^2/(K*C*D))+g)/6)) := by
  have hdiv:=div_le_div_of_nonneg_right hs (sq_nonneg V)
  have he:s*V/V^2=s/V:=by field_simp
  rw [he] at hdiv
  calc
    _≤(μ*H*K*Real.sqrt (C*D)/(E*Real.sqrt R)/V^2)*
        (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6):=by
      gcongr
    _=μ*H*(K*Real.sqrt (C*D)/(E*Real.sqrt R*V^2)*
        (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)):=by ring
    _=_:=by rw [exceptional_core_log K V E R C D Z j g hK hV hE hR hC hD hZ]

theorem actual_nominal_cancellation
    (I J E : Ideal ActualEisensteinCubic.O) (hE:E≠0)
    (K V Z j g : ℝ)(hK:0<K)(hV:0<V)(hZ:1<Z):
    let C : ℝ := (commonPart I J).absNorm;
    let D : ℝ := (commonPart J I).absNorm;
    let N : ℝ := E.absNorm;
    let R : ℝ := (Ideal.span {activeConductor I J}).absNorm;
    K*Real.sqrt (C*D)/(N*Real.sqrt R*V^2)*
      (V/C)^((2:ℝ)/3)*(V/D)^((2:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6) =
    V*K^((1:ℝ)/6)*R^((1:ℝ)/3)/(N^((1:ℝ)/6)*C*D)*
      Z^(5*(j-Real.logb Z (firstNominalScale I J E K V)+g)/6) := by
  exact exceptional_core_log K V _ _ _ _ Z j g hK hV (norm_pos E hE)
    (active_norm_pos I J) (norm_pos _ (commonPart_ne_zero I J))
    (norm_pos _ (commonPart_ne_zero J I)) hZ

end SevenEighths.CenteredMomentFirstExceptionalPrefactor

end

end OAI
end OAIOriginalModule1535

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSectors
Source SHA256: a981e8a977db16c32fee8d270536ff8bab7862166a9263913852925f21ac0141
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1536


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstSectors
open CenteredMomentCompleteCommon CenteredMomentCommonSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def residualPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) : Finset (Ideal O) :=
  S.preimage (fun a => C*a) (by intro a ha b hb he;exact mul_left_cancel₀ hC he)

@[simp] theorem mem_residualPool (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O)) (a : Ideal O) :
    a∈residualPool C hC S ↔ C*a∈S := Finset.mem_preimage

def pairSector (C D : Ideal O) (S T : Finset (Ideal O)) : Finset (Ideal O × Ideal O) :=
  (S.product T).filter (fun p => commonPart p.1 p.2=C ∧ commonPart p.2 p.1=D)

def residualPairDomain (C D : Ideal O) (hC : C≠0) (hD : D≠0) (S T : Finset (Ideal O)) :
    Finset (Ideal O × Ideal O) :=
  ((residualPool C hC S).product (residualPool D hD T)).filter
    (fun p => IsCoprime C p.1 ∧ IsCoprime C p.2 ∧ IsCoprime p.1 p.2)

theorem residualPair_image (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (S T : Finset (Ideal O))
    (hS : ∀ I∈S,I≠0) (hT : ∀ J∈T,J≠0) :
    (residualPairDomain C D hC hD S T).image (fun p => (C*p.1,D*p.2))=pairSector C D S T := by
  ext p
  rcases p with ⟨I,J⟩
  constructor
  · intro hp
    obtain ⟨⟨a,b⟩,hab,he⟩ := Finset.mem_image.mp hp
    simp only [Prod.mk.injEq] at he
    rcases he with ⟨rfl,rfl⟩
    obtain ⟨hpools,hCa,hCb,hab⟩ := Finset.mem_filter.mp hab
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hpools
    have has : C*a∈S := (mem_residualPool C hC S a).mp ha
    have hbs : D*b∈T := (mem_residualPool D hD T b).mp hb
    have ha0 : a≠0 := right_ne_zero_of_mul (hS _ has)
    have hb0 : b≠0 := right_ne_zero_of_mul (hT _ hbs)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨has,hbs⟩,
      reconstructed_commonParts C D a b hC hD ha0 hb0 hCD hCa hCb hab⟩
  · intro hp
    obtain ⟨hpools,hCI,hDJ⟩ := Finset.mem_filter.mp hp
    obtain ⟨hIS,hJT⟩ := Finset.mem_product.mp hpools
    have hi : C*residualPart I J=I := by rw [← hCI];exact (reconstruct I J (hS I hIS)).symm
    have hj : D*residualPart J I=J := by rw [← hDJ];exact (reconstruct J I (hT J hJT)).symm
    refine Finset.mem_image.mpr ⟨(residualPart I J,residualPart J I),?_,Prod.ext hi hj⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_,?_,residualParts_coprime I J⟩
    · exact (mem_residualPool C hC S _).mpr (by dsimp only;rw [hi];exact hIS)
    · exact (mem_residualPool D hD T _).mpr (by dsimp only;rw [hj];exact hJT)
    · rw [← hCI]
      exact commonPart_own_residual_coprime I J
    · rw [← hCI]
      exact commonPart_residualPart_coprime I J

theorem pairSector_sum (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (S T : Finset (Ideal O))
    (hS : ∀ I∈S,I≠0) (hT : ∀ J∈T,J≠0) (F : Ideal O → Ideal O → ℂ) :
    (∑ p∈pairSector C D S T,F p.1 p.2)=
      ∑ p∈residualPairDomain C D hC hD S T,F (C*p.1) (D*p.2) := by
  rw [← residualPair_image C D hC hD hCD S T hS hT,Finset.sum_image]
  intro p hp q hq he
  exact Prod.ext (mul_left_cancel₀ hC (congrArg Prod.fst he))
    (mul_left_cancel₀ hD (congrArg Prod.snd he))

theorem pairSector_double_sum (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (S T : Finset (Ideal O))
    (hS : ∀ I∈S,I≠0) (hT : ∀ J∈T,J≠0) (F : Ideal O → Ideal O → ℂ) :
    (∑ p∈pairSector C D S T,F p.1 p.2)=
      ∑ a∈residualPool C hC S,∑ b∈residualPool D hD T,
        if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then F (C*a) (D*b) else 0 := by
  rw [pairSector_sum C D hC hD hCD S T hS hT,residualPairDomain,Finset.sum_filter]
  exact Finset.sum_product _ _ _

def commonLabels (S T : Finset (Ideal O)) : Finset (Ideal O × Ideal O) :=
  (S.product T).image (fun p => (commonPart p.1 p.2,commonPart p.2 p.1))

theorem commonLabels_data (S T : Finset (Ideal O)) (C D : Ideal O)
    (h : (C,D)∈commonLabels S T) :
    C≠0 ∧ D≠0 ∧ primeSupport C=primeSupport D := by
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp h
  rcases Prod.mk.inj he with ⟨rfl,rfl⟩
  exact ⟨commonPart_ne_zero _ _,commonPart_ne_zero _ _,commonParts_equal_support _ _⟩

theorem sum_common_sectors (S T : Finset (Ideal O)) (F : Ideal O → Ideal O → ℂ) :
    (∑ I∈S,∑ J∈T,F I J)=
      ∑ p∈commonLabels S T,∑ q∈pairSector p.1 p.2 S T,F q.1 q.2 := by
  have hh := Finset.sum_fiberwise_of_maps_to
    (s:=S.product T) (t:=commonLabels S T)
    (g:=fun p : Ideal O × Ideal O => (commonPart p.1 p.2,commonPart p.2 p.1))
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    (fun p : Ideal O × Ideal O => F p.1 p.2)
  symm
  convert hh using 1
  · apply Finset.sum_congr rfl
    intro p hp
    rcases p with ⟨C,D⟩
    congr 1
    ext q
    simp only [pairSector,Finset.mem_filter,Prod.mk.injEq]
  · exact (Finset.sum_product S T (fun p : Ideal O × Ideal O => F p.1 p.2)).symm

end SevenEighths.CenteredMomentFirstSectors

end

end OAI
end OAIOriginalModule1536

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonAllocationBox
Source SHA256: ac3cad6b0398b8cb1856ed218f76e8dbe0623d2bddc1752fb633917e6279ab2d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1537



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationBox
open CenteredMomentCommonAllocation CenteredMomentSupport CenteredMomentCommonSectors
open CenteredMomentFirstSectors IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def sourceFiber (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O) :
    Finset (ι → Ideal O) :=
  (Fintype.piFinset S).filter (fun v => ∀ i,supportExtract (v i) (primeSupport C)=B i)

def residualBoxes (S : ι → Finset (Ideal O)) (C : Ideal O) (B : ι → Ideal O)
    (hB : ∀ i,B i≠0) : Finset (ι → Ideal O) :=
  Fintype.piFinset (fun i => (residualPool (B i) (hB i) (S i)).filter (IsCoprime C))

theorem residualBoxes_image (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) :
    (residualBoxes S C B hB).image (fun v i => B i*v i)=sourceFiber S C B := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    have hui := Fintype.mem_piFinset.mp hu
    apply Finset.mem_filter.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact (mem_residualPool (B i) (hB i) (S i) _).mp (Finset.mem_filter.mp (hui i)).1
    · intro i
      have hp := Finset.mem_filter.mp (hui i)
      have hsrc := (mem_residualPool (B i) (hB i) (S i) _).mp hp.1
      have hu0 : u i≠0 := right_ne_zero_of_mul (hS i _ hsrc)
      rw [supportExtract_mul _ _ (hB i) hu0,supportExtract_of_subset _ (hB i) _ (hBs i),
        supportExtract_of_disjoint _ _ ((IdealCoprimeSieveOperator.primeSupport_disjoint_iff hC hu0).mpr hp.2).symm,mul_one]
  · intro hv
    obtain ⟨hv,hvB⟩ := Finset.mem_filter.mp hv
    have hvi := Fintype.mem_piFinset.mp hv
    let u := fun i => supportResidual (v i) (primeSupport C)
    have hi (i : ι) : B i*u i=v i := by
      rw [← hvB i]
      exact support_reconstruct _ (hS i _ (hvi i)) _
    refine Finset.mem_image.mpr ⟨u,?_,funext hi⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_filter.mpr
    constructor
    · apply (mem_residualPool (B i) (hB i) (S i) _).mpr
      rw [hi]
      exact hvi i
    · exact residual_factor_coprime C (v i) hC

theorem sourceFiber_sum (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈sourceFiber S C B,F v)=
      ∑ u∈residualBoxes S C B hB,F (fun i => B i*u i) := by
  rw [← residualBoxes_image S hS C hC B hB hBs,Finset.sum_image]
  intro u hu v hv he
  funext i
  exact mul_left_cancel₀ (hB i) (congrFun he i)

theorem sourceFiber_product_sum (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C) (hprod : ∏ i,B i=C)
    (a : Ideal O) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0)=
      ∑ u∈residualBoxes S C B hB,if (∏ i,u i)=a then F (fun i => B i*u i) else 0 := by
  rw [sourceFiber_sum S hS C hC B hB hBs]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [Finset.prod_mul_distrib,hprod,mul_right_inj' hC]

end SevenEighths.CenteredMomentCommonAllocationBox

end

end OAI
end OAIOriginalModule1537

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonAllocationSum
Source SHA256: 3715eafaf13bc6503c36c3624de106647a520ddc6681af4e9e776611fbab62fc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1538


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocation CenteredMomentCommonAllocationBox CenteredMomentSupport
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def allocationLabels (S : ι → Finset (Ideal O)) (C : Ideal O) : Finset (ι → Ideal O) :=
  (Fintype.piFinset S).image (fun v i => supportExtract (v i) (primeSupport C))

def actualAllocations (S : ι → Finset (Ideal O)) (C : Ideal O) : Finset (ι → Ideal O) :=
  (allocationLabels S C).filter (fun B => ∏ i,B i=C)

theorem allocation_data (S : ι → Finset (Ideal O)) (C : Ideal O)
    (B : ι → Ideal O) (hB : B∈allocationLabels S C) :
    (∀ i,B i≠0) ∧ (∀ i,primeSupport (B i)⊆primeSupport C) := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hB
  refine ⟨fun i => supportExtract_ne_zero _ _,?_⟩
  intro i
  rw [supportExtract_support]
  exact Finset.inter_subset_right

 theorem sum_source_fibers (S : ι → Finset (Ideal O)) (C : Ideal O)
    (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,F v)=∑ B∈allocationLabels S C,∑ v∈sourceFiber S C B,F v := by
  have hh := Finset.sum_fiberwise_of_maps_to (s:=Fintype.piFinset S) (t:=allocationLabels S C)
    (g:=fun v i => supportExtract (v i) (primeSupport C))
    (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩) F
  symm
  convert hh using 1
  apply Finset.sum_congr rfl
  intro B hB
  congr 1
  ext v
  simp only [sourceFiber,Finset.mem_filter,funext_iff]

theorem sum_actual_allocations (S : ι → Finset (Ideal O))
    (C a : Ideal O) (hC : C≠0) (ha : a≠0) (hCa : IsCoprime C a)
    (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,if (∏ i,v i)=C*a then F v else 0)=
      ∑ B∈actualAllocations S C,
        ∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0 := by
  rw [sum_source_fibers S C]
  symm
  apply Finset.sum_filter_of_ne
  intro B hB hn
  obtain ⟨v,hv,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hp : (∏ i,v i)=C*a := by
    by_contra hh
    exact hne (ite_eq_right hh)
  have he := (tuple_products v C a hC ha hCa hp).1
  have hb := (Finset.mem_filter.mp hv).2
  simpa only [hb] using he

theorem original_coefficient_allocated (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C a : Ideal O) (hC : C≠0) (ha : a≠0)
    (hCa : IsCoprime C a) (F : (ι → Ideal O) → ℂ) :
    (∑ v∈Fintype.piFinset S,if (∏ i,v i)=C*a then F v else 0)=
      ∑ B : actualAllocations S C,
        ∑ u∈residualBoxes S C B
          (allocation_data S C B (Finset.mem_filter.mp B.property).1).1,
          if (∏ i,u i)=a then F (fun i => B.val i*u i) else 0 := by
  rw [sum_actual_allocations S C a hC ha hCa F]
  rw [← Finset.sum_coe_sort (actualAllocations S C)
    (fun B => ∑ v∈sourceFiber S C B,if (∏ i,v i)=C*a then F v else 0)]
  apply Finset.sum_congr rfl
  intro B hB
  exact sourceFiber_product_sum S hS C hC B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).2
    (Finset.mem_filter.mp B.property).2 a F

theorem actualAllocations_card (S : ι → Finset (Ideal O)) (C : Ideal O) (hC : C≠0) :
    (actualAllocations S C).card≤(idealDivisors C).card^(Fintype.card ι) := by
  let f (B : actualAllocations S C) : ι → idealDivisors C := fun i => ⟨B.val i,by
    apply (mem_idealDivisors hC).mpr
    have hh := Finset.dvd_prod_of_mem B.val (Finset.mem_univ i)
    rw [(Finset.mem_filter.mp B.property).2] at hh
    exact hh⟩
  have hf : Function.Injective f := by
    intro B D he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  simpa only [Fintype.card_coe,Fintype.card_fun] using Fintype.card_le_of_injective f hf

theorem actualAllocations_small_power [Nonempty ι] (ε : ℝ) (hε : 0<ε) :
    ∃ D : ℝ,0<D ∧ ∀ (S : ι → Finset (Ideal O)) (C : Ideal O),C≠0 →
      ((actualAllocations S C).card:ℝ)≤D*(Ideal.absNorm C:ℝ)^ε := by
  have hr : (0:ℝ)<Fintype.card ι := by exact_mod_cast Fintype.card_pos
  let δ := ε/(Fintype.card ι:ℝ)
  have hδ : 0<δ := div_pos hε hr
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨D^(Fintype.card ι),pow_pos hD _,?_⟩
  intro S C hC
  have hd : δ*(Fintype.card ι:ℝ)=ε := by dsimp only [δ];field_simp
  calc
    _ ≤ ((idealDivisors C).card:ℝ)^(Fintype.card ι) := by exact_mod_cast actualAllocations_card S C hC
    _ ≤ (D*(Ideal.absNorm C:ℝ)^δ)^(Fintype.card ι) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv C hC) _
    _ = _ := by rw [mul_pow,← Real.rpow_mul_natCast (Nat.cast_nonneg _),hd]

end SevenEighths.CenteredMomentCommonAllocationSum

end

end OAI
end OAIOriginalModule1538

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonPrimeSlots
Source SHA256: 5e4be055c4fe5ae02b5830194641fc8ebccae9856888e4c8de825022e20a521a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1539


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonPrimeSlots
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSupport IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

 theorem residual_original_mem (S : ι → Finset (Ideal O)) (C : Ideal O)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0) (u : ι → Ideal O)
    (hu : u∈residualBoxes S C B hB) (i : ι) : B i*u i∈S i :=
  (CenteredMomentFirstSectors.mem_residualPool _ _ _ _).mp
    (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hu i)).1

theorem prime_coordinate_cases (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C)
    (u : ι → Ideal O) (hu : u∈residualBoxes S C B hB)
    (i : ι) (hp : ∀ I∈S i,Prime I) :
    (B i=1 ∧ Prime (u i)) ∨ (u i=1 ∧ Prime (B i)) := by
  have hsrc := residual_original_mem S C B hB u hu i
  have hprime := hp _ hsrc
  by_cases hBi : B i=1
  · exact Or.inl ⟨hBi,by simpa only [hBi,one_mul] using hprime⟩
  · have hv : (fun j => B j*u j)∈sourceFiber S C B := by
      rw [← residualBoxes_image S hS C hC B hB hBs]
      exact Finset.mem_image.mpr ⟨u,hu,rfl⟩
    have he := (Finset.mem_filter.mp hv).2 i
    rw [supportExtract_prime _ hprime] at he
    have hmem : B i*u i∈primeSupport C := by
      by_contra hn
      rw [ite_eq_right hn] at he
      exact hBi he.symm
    rw [ite_eq_left hmem] at he
    have hu1 : u i=1 := mul_left_cancel₀ (hB i) (he.trans (mul_one (B i)).symm)
    exact Or.inr ⟨hu1,by simpa only [hu1,mul_one] using hprime⟩

def liveSlots (T : Finset ι) (B : ι → Ideal O) : Finset ι := T.filter (fun i => B i=1)
def frozenSlots (T : Finset ι) (B : ι → Ideal O) : Finset ι := T.filter (fun i => B i≠1)

theorem slot_coefficient_product (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C)
    (u : ι → Ideal O) (hu : u∈residualBoxes S C B hB)
    (T : Finset ι) (hp : ∀ i∈T,∀ I∈S i,Prime I) (β : ι → Ideal O → ℂ) :
    (∏ i∈T,β i (B i*u i))=
      (∏ i∈frozenSlots T B,β i (B i))*(∏ i∈liveSlots T B,β i (u i)) := by
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => B i=1) (fun i => β i (B i*u i)),mul_comm]
  apply congrArg₂ (·*·)
  · apply Finset.prod_congr rfl
    intro i hi
    have hTi := (Finset.mem_filter.mp hi).1
    have hBi := (Finset.mem_filter.mp hi).2
    have hu1 : u i=1 := by
      rcases prime_coordinate_cases S hS C hC B hB hBs u hu i (hp i hTi) with h|h
      · exact False.elim (hBi h.1)
      · exact h.1
    rw [hu1,mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2,one_mul]

theorem slot_residual_product (S : ι → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (C : Ideal O) (hC : C≠0)
    (B : ι → Ideal O) (hB : ∀ i,B i≠0)
    (hBs : ∀ i,primeSupport (B i)⊆primeSupport C)
    (u : ι → Ideal O) (hu : u∈residualBoxes S C B hB)
    (T : Finset ι) (hp : ∀ i∈T,∀ I∈S i,Prime I) :
    (∏ i∈T,u i)=∏ i∈liveSlots T B,u i := by
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hBi : B i≠1 := by
    intro he
    exact hnot (Finset.mem_filter.mpr ⟨hi,he⟩)
  rcases prime_coordinate_cases S hS C hC B hB hBs u hu i (hp i hi) with h|h
  · exact False.elim (hBi h.1)
  · exact h.1

end SevenEighths.CenteredMomentCommonPrimeSlots

end

end OAI
end OAIOriginalModule1539

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstWholeKernel
Source SHA256: 585a5686923f9350be93e71e24a6a7aecf366b10260773764ccd716f4e893ceb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1540



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstWholeKernel
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve EisensteinSchwartzPoisson
open CenteredMomentFirstFrequency CenteredMomentFirstColumns CenteredMomentGaussEnergy CenteredMomentFirstAssembly
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentPrimitive CenteredMomentScale CenteredMomentSmooth CenteredMomentFirstReduced
local notation "O" => ActualEisensteinCubic.O

def windows (V : Fin 4 → ℝ → ℂ) (K H A B K₀ H₀ A₀ B₀ : ℝ) : ℂ :=
  V 0 (Real.log (K/K₀))*V 1 (Real.log (H/H₀))*
    V 2 (Real.log (A/A₀))*V 3 (Real.log (B/B₀))

theorem dilated_frequency_whole_kernel {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (e a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (k : ℝ) (hk : 0<k) (h : O) (hh : h≠0)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let r := finitePrimeModulus P
    let ρ := finiteSexticRow P hg j
    let kr := k/‖eisEmbedding r‖^2
    dilatedFrequency P hcop hg j e a b ha hb k h *
      windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding a‖^2) (‖eisEmbedding b‖^2) K₀ H₀ A₀ B₀ *
      paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2)=
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/
        ((‖eisEmbedding r‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*
        star (ρ h)*originalPhase e r ρ a b *
        (gaussRow a ha h*star (gaussRow b hb (-h)))*
        wholeKernel W V (K₀*H₀/(A₀*B₀))
          (Real.log (kr/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
          (Real.log (‖eisEmbedding a‖^2/A₀)) (Real.log (‖eisEmbedding b‖^2/B₀)) := by
  dsimp only
  have haN : 0<‖eisEmbedding a‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha))
  have hbN : 0<‖eisEmbedding b‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero b hb))
  have hrN : 0<‖eisEmbedding (finitePrimeModulus P)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  have hhN : 0<‖eisEmbedding h‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hh)
  have hk' : 0<k/‖eisEmbedding (finitePrimeModulus P)‖^2 := div_pos hk (sq_pos_of_pos hrN)
  rw [show dilatedFrequency P hcop hg j e a b ha hb k h=_ from
    normalized_dilated_frequency P hcop hg hchar j hj0 hj6 e a b ha hb har hbr k h]
  rw [wholeKernel_actual W V _ _ _ _ K₀ H₀ A₀ B₀ hk' (sq_pos_of_pos hhN)
    (sq_pos_of_pos haN) (sq_pos_of_pos hbN) hK₀ hH₀ hA₀ hB₀]
  have harg : k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*finitePrimeModulus P))‖^2=
      (k/‖eisEmbedding (finitePrimeModulus P)‖^2)*‖eisEmbedding h‖^2/
        (‖eisEmbedding a‖^2*‖eisEmbedding b‖^2) := by
    simp only [map_mul,norm_mul]
    ring
  rw [harg]
  simp only [windows,Real.sqrt_sq haN.le,Real.sqrt_sq hbN.le,
    Complex.star_def,map_div₀,Complex.conj_ofReal]
  have hA : (Real.sqrt A₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hA₀).ne'
  have hB : (Real.sqrt B₀:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB₀).ne'
  have hr : (‖eisEmbedding (finitePrimeModulus P)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hrN.ne'
  have ha' : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr haN.ne'
  have hb' : (‖eisEmbedding b‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hbN.ne'
  have alg (c r a b A B x y u v : ℂ) (hr : r≠0) (ha : a≠0) (hb : b≠0)
      (hA : A≠0) (hB : B≠0) :
      (c/r*x*(u/a*(v/b)))*y=c/(r*A*B)*x*(u*v)*((A*B/(a*b))*y) := by
    field_simp
  convert alg ((k:ℂ)*canonicalNormalizedGauss P hcop hg j)
    (‖eisEmbedding (finitePrimeModulus P)‖:ℂ) (‖eisEmbedding a‖:ℂ) (‖eisEmbedding b‖:ℂ)
    (Real.sqrt A₀:ℂ) (Real.sqrt B₀:ℂ)
    (star (finiteSexticRow P hg j h)*originalPhase e (finitePrimeModulus P) (finiteSexticRow P hg j) a b)
    (windows V (k/‖eisEmbedding (finitePrimeModulus P)‖^2) (‖eisEmbedding h‖^2)
      (‖eisEmbedding a‖^2) (‖eisEmbedding b‖^2) K₀ H₀ A₀ B₀*
      paperRadialFourier W ((k/‖eisEmbedding (finitePrimeModulus P)‖^2)*‖eisEmbedding h‖^2/
        (‖eisEmbedding a‖^2*‖eisEmbedding b‖^2)))
    (gaussRow a ha h) (star (gaussRow b hb (-h))) hr ha' hb' hA hB using 1 <;>
    simp only [windows,Complex.star_def] <;> ring

end SevenEighths.CenteredMomentFirstWholeKernel

end

end OAI
end OAIOriginalModule1540

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstWholeAssembly
Source SHA256: 95c1de55452cd88256c2f105b94767fe7a57bce40341c2322f6c4a50393f1342
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1541


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstWholeAssembly
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve EisensteinSchwartzPoisson
open CenteredMomentFirstFrequency CenteredMomentFirstColumns CenteredMomentGaussEnergy
open CenteredMomentFirstAssembly CenteredMomentCommonSupport CenteredMomentFirstReduced
open CenteredMomentPrimitive CenteredMomentScale CenteredMomentSmooth CenteredMomentFirstWholeKernel
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

 theorem finite_whole_children {ι α β : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (S : Finset α) (T : Finset β) (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ l,Supported (Ideal.span {b l}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ l,ConcretePrimeRowBridge.goodLambda^2∣b l-1)
    (har : ∀ i,IsCoprime (a i) (finitePrimeModulus P))
    (hbr : ∀ l,IsCoprime (b l) (finitePrimeModulus P))
    (c : α → ℂ) (d : β → ℂ) (e : O) (k : ℝ) (hk : 0<k) (h : O) (hh : h≠0)
    (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (K₀ H₀ A₀ B₀ : ℝ)
    (hK₀ : 0<K₀) (hH₀ : 0<H₀) (hA₀ : 0<A₀) (hB₀ : 0<B₀) :
    let r := finitePrimeModulus P
    let ρ := finiteSexticRow P hg j
    let kr := k/‖eisEmbedding r‖^2
    (∑ i∈S,∑ l∈T,
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
        (c i*star (d l))*
        windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding (a i)‖^2) (‖eisEmbedding (b l)‖^2) K₀ H₀ A₀ B₀*
        paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a i*(b l*r))‖^2)) =
      ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/
        ((‖eisEmbedding r‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*star (ρ h)*
        ∑ L∈divisorPool T (fun l => Ideal.span {b l}),
          (UniqueFactorizationMonoid.moebius L:ℂ)*ρ e*
            ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
              ∑ i∈S,∑ l∈T,
                ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*
                    gaussRow (a i) (ha i) h)*
                  star (divisorCoefficient L b (fun l => d l*rightCoefficient e r ρ (b l)) (ξ⁻¹) l*
                    gaussRow (b l) (hb l) (-h)))*
                wholeKernel W V (K₀*H₀/(A₀*B₀))
                  (Real.log (kr/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
                  (Real.log (‖eisEmbedding (a i)‖^2/A₀)) (Real.log (‖eisEmbedding (b l)‖^2/B₀)) := by
  dsimp only
  let r := finitePrimeModulus P
  let ρ := finiteSexticRow P hg j
  let kr := k/‖eisEmbedding r‖^2
  let F := ((k:ℂ)*canonicalNormalizedGauss P hcop hg j/
    ((‖eisEmbedding r‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))*star (ρ h)
  let KK := fun i l => wholeKernel W V (K₀*H₀/(A₀*B₀))
    (Real.log (kr/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
    (Real.log (‖eisEmbedding (a i)‖^2/A₀)) (Real.log (‖eisEmbedding (b l)‖^2/B₀))
  have ht (i : α) (l : β) :
      (if IsCoprime (a i) (b l) then dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h else 0)*
        (c i*star (d l))*
        windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding (a i)‖^2) (‖eisEmbedding (b l)‖^2) K₀ H₀ A₀ B₀*
        paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a i*(b l*r))‖^2) =
      F*((if IsCoprime (a i) (b l) then originalPhase e r ρ (a i) (b l) else 0)*(c i*star (d l)))*
        (gaussRow (a i) (ha i) h*star (gaussRow (b l) (hb l) (-h)))*KK i l := by
    by_cases hab : IsCoprime (a i) (b l)
    · simp only [hab,ite_true]
      have hh' := dilated_frequency_whole_kernel P hcop hg hchar j hj0 hj6 e
        (a i) (b l) (ha i) (hb l) (hab.mul_right (har i)) (hbr l) k hk h hh
        W V K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
      dsimp only at hh'
      calc
        _ = (c i*star (d l))*(dilatedFrequency P hcop hg j e (a i) (b l) (ha i) (hb l) k h*
          windows V kr (‖eisEmbedding h‖^2) (‖eisEmbedding (a i)‖^2) (‖eisEmbedding (b l)‖^2) K₀ H₀ A₀ B₀*
          paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a i*(b l*r))‖^2)) := by ring
        _ = _ := by rw [hh'];dsimp only [F,KK,kr,r,ρ];ring
    · simp [hab]
  calc
    _ = F*(∑ i∈S,∑ l∈T,
      ((if IsCoprime (a i) (b l) then originalPhase e r ρ (a i) (b l) else 0)*(c i*star (d l)))*
        (gaussRow (a i) (ha i) h*star (gaussRow (b l) (hb l) (-h)))*KK i l) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro l hl
      simpa only [mul_assoc] using ht i l
    _ = _ := congrArg (fun z => F*z)
      (finite_first_children S T a b ha hb hpa hpb c d e r ρ (finiteSexticRow_mul P hg j) h KK)

end SevenEighths.CenteredMomentFirstWholeAssembly

end

end OAI
end OAIOriginalModule1541

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstChildBound
Source SHA256: 9380d9bde59006a69ba38ccfb8fcde63e8950df89c1cc2f34c687cf44f6dab9a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1542



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstChildBound
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentFirstAssembly
open CenteredMomentFirstColumns CenteredMomentGaussEnergy CenteredMomentReflectedChild
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentSmooth RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

private theorem weighted_norm_sum {α : Type*} (S : Finset α) (a f : α → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (B : α → ℝ)
    (hB : ∀ i ∈ S, r*‖f i‖ ≤ B i) :
    r*‖∑ i ∈ S, a i*f i‖ ≤ ∑ i ∈ S, ‖a i‖*B i := by
  calc
    _ ≤ r*∑ i ∈ S, ‖a i*f i‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hr
    _ = ∑ i ∈ S, ‖a i‖*(r*‖f i‖) := by simp only [Finset.mul_sum,norm_mul]; congr 1; funext i; ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hB i hi) (norm_nonneg _))

theorem finite_first_ray_divisor_bound (L : Finset (Ideal O))
    (F : Ideal O → RayCharacter → RayCharacter → ℂ)
    (r C : ℝ) (hr : 0 ≤ r) (hC : 0 ≤ C) (B₁ B₂ : Ideal O → ℝ)
    (hB₁ : ∀ I ∈ L, 0 ≤ B₁ I) (hB₂ : ∀ I ∈ L, 0 ≤ B₂ I)
    (hF : ∀ I ∈ L, ∀ χ ξ, r*‖F I χ ξ‖ ≤ C*(B₁ I*B₂ I)) :
    r*‖∑ I ∈ L, (UniqueFactorizationMonoid.moebius I : ℂ)*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ * F I χ ξ‖ ≤
      (256*C)*∑ I ∈ L, ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖*(B₁ I*B₂ I) := by
  have he (I : Ideal O) (hI : I ∈ L) :
      r*‖∑ χ : RayCharacter, ∑ ξ : RayCharacter,
        pairCoeff (firstPhaseTable) χ ξ*F I χ ξ‖ ≤ (256*C)*(B₁ I*B₂ I) := by
    calc
      _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          ‖pairCoeff (firstPhaseTable) χ ξ‖*(C*(B₁ I*B₂ I)) := by
        have h := weighted_norm_sum Finset.univ (fun _ : RayCharacter => (1 : ℂ))
          (fun χ => ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ*F I χ ξ) r hr
          (fun χ => ∑ ξ : RayCharacter, ‖pairCoeff (firstPhaseTable) χ ξ‖*(C*(B₁ I*B₂ I)))
          (fun χ _ => weighted_norm_sum Finset.univ _ _ r hr _ (fun ξ _ => hF I hI χ ξ))
        simpa only [one_mul,norm_one] using h
      _ = (∑ χ : RayCharacter, ∑ ξ : RayCharacter, ‖pairCoeff (firstPhaseTable) χ ξ‖)*
          (C*(B₁ I*B₂ I)) := by simp only [Finset.sum_mul]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right (firstPhaseTable_mass)
          (mul_nonneg hC (mul_nonneg (hB₁ I hI) (hB₂ I hI)))
        convert h using 1 ; ring
  have h := weighted_norm_sum L (fun I => (UniqueFactorizationMonoid.moebius I : ℂ))
    (fun I => ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (firstPhaseTable) χ ξ*F I χ ξ)
    r hr (fun I => (256*C)*(B₁ I*B₂ I)) he
  convert h using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  ring

theorem first_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (a : α → O) (b : β → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j}))
    (hpa : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1)
    (hpb : ∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1)
    (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ)
    (hρ : ∀ x y,ρ (x*y)=ρ x*ρ y) (q : O → ℂ) (K : O → α → β → ℂ) :
    (∑ z∈rows,q z*∑ i∈S,∑ j∈T,
      ((if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*(c i*star (d j)))*
        (gaussRow (a i) (ha i) z*star (gaussRow (b j) (hb j) (-z)))*K z i j)=
      ∑ L∈divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L:ℂ)*
          ∑ χ : RayCharacter,∑ ξ : RayCharacter,pairCoeff firstPhaseTable χ ξ*
            ∑ z∈rows,(q z*ρ e)*∑ i∈S,∑ j∈T,
              ((divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*gaussRow (a i) (ha i) z)*
                star (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹) j*
                  gaussRow (b j) (hb j) (-z)))*K z i j := by
  simp_rw [finite_first_children S T a b ha hb hpa hpb c d e r ρ hρ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s:=rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem whole_kernel_first_child_bound (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i,0≤M i)
    (hV : ∀ i y,V i y≠0 → |y|≤M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ R : ℝ,0<R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (ha : ∀ i,Supported (Ideal.span {a i})) (hb : ∀ j,Supported (Ideal.span {b j})),
      (∀ i,ConcretePrimeRowBridge.goodLambda^2∣a i-1) →
      (∀ j,ConcretePrimeRowBridge.goodLambda^2∣b j-1) →
      ∀ (c : α → ℂ) (d : β → ℂ) (e r : O) (ρ : O → ℂ),
      (∀ x y,ρ (x*y)=ρ x*ρ y) → ‖ρ e‖≤1 →
      ∀ (q : O → ℂ) (u : α → ℝ) (v : β → ℝ) (ρ₀ x : O → ℝ),
      (∀ z∈rows,‖q z‖≤1) →
      (∀ z∈rows,‖V 0 (ρ₀ z)‖≤1) → (∀ z∈rows,‖V 1 (x z)‖≤1) →
      ∀ (U : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),0≤B₁ L) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),0≤B₂ L) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),∀ χ : RayCharacter,∀ t : ℝ,
        (gaussEnergy S a ha (fun i =>
          divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ i*
            columnPhase (V 2) (u i) t) U K).re≤(B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L∈divisorPool T (fun j => Ideal.span {b j}),∀ ξ : RayCharacter,∀ t : ℝ,
        (gaussEnergy T b hb (fun j =>
          divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) ξ j*
            star (columnPhase (V 3) (v j) t)) U K).re≤(B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A*‖∑ z∈rows,q z*∑ i∈S,∑ j∈T,
        ((if IsCoprime (a i) (b j) then originalPhase e r ρ (a i) (b j) else 0)*(c i*star (d j)))*
          (gaussRow (a i) (ha i) z*star (gaussRow (b j) (hb j) (-z)))*
            wholeKernel W V R (ρ₀ z) (x z) (u i) (v j)‖≤
        C*∑ L∈divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_reflected_gauss_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T a b ha hb hpa hpb c d e r ρ hρ hρe q u v ρ₀ x hq hV₀ hV₁ U K hK hU hmajor
    B₁ B₂ hB₁ hB₂ hleft hright
  rw [first_row_children rows S T a b ha hb hpa hpb c d e r ρ hρ]
  apply finite_first_ray_divisor_bound _ _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (fun i => c i*leftCoefficient e r ρ (a i)) χ)
    (divisorCoefficient L b (fun j => d j*rightCoefficient e r ρ (b j)) (ξ⁻¹))
    u v ρ₀ x (fun z => q z*ρ e)
    (fun z hz => by rw [norm_mul];exact (mul_le_of_le_one_left (norm_nonneg _) (hq z hz)).trans hρe)
    hV₀ hV₁ U K hK hU hmajor (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL)
    (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentFirstChildBound

end

end OAI
end OAIOriginalModule1542

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RankinLabels
Source SHA256: 21fbe092bfe4c40f973a05674e1367038066b34fac77bc2af17d73f6b7dabbfb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1543



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinLabels
open IdealMobiusDivisorSum CenteredMomentRankinRadical CenteredMomentRankinSubset
local notation "O" => ActualEisensteinCubic.O

theorem common_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Ideal O),Squarefree s → s ≠ 0 →
      ∀ S : Finset (Ideal O × Ideal O),
      (∀ v ∈ S,v.1 ≠ 0 ∧ v.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1=primeSupport v.2) →
      (∀ v ∈ S,s ∣ v.1 ∧ s ∣ v.2) →
      ∀ X₁ X₂ Y : ℝ,0 < X₁ → 0 < X₂ → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1:ℝ) ≤ X₁ ∧ (Ideal.absNorm v.2:ℝ) ≤ X₂) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1 v.2):ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X₁^a*X₂^a*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := supported_power_pair_count a ε ha hε
  refine ⟨128*C,by positivity,?_⟩
  intro s hs hs0 S hS heq hdiv X₁ X₂ Y hX₁ hX₂ hY hN hR
  let rad : Ideal O × Ideal O → Ideal O := fun v => commonRadical v.1 v.2
  have hfiber (R : Ideal O) (hRmem : R ∈ S.image rad) :
      ((S.filter (fun v => rad v=R)).card:ℝ) ≤ C*X₁^a*X₂^a*Y^ε := by
    obtain ⟨v,hv,hvR⟩ := Finset.mem_image.mp hRmem
    have hR0 : R ≠ 0 := hvR ▸ commonRadical_ne_zero v.1 v.2
    have hRN : (Ideal.absNorm R:ℝ) ≤ Y := hvR ▸ hR v hv
    have hb := hcount R hR0 (S.filter (fun v => rad v=R))
      (fun v hv => hS v (Finset.mem_filter.mp hv).1)
      (by
        intro w hw
        obtain ⟨hw,hwr⟩ := Finset.mem_filter.mp hw
        have he : primeSupport R=primeSupport w.1 := by
          rw [← hwr,commonRadical_support,← heq w hw,Finset.inter_self]
        rw [he,heq w hw]
        exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩)
      X₁ X₂ hX₁ hX₂ (fun w hw => hN w (Finset.mem_filter.mp hw).1)
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hRN hε.le) (by positivity))
  have hrad := old_mask_radical_count S Prod.fst Prod.snd s hs hs0
    (fun v hv => (hS v hv).1) (fun v hv => (hS v hv).2)
    (fun v hv => (hdiv v hv).1) (fun v hv => (hdiv v hv).2) Y hY.le hR
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem rad hv)
  calc
    _ = ∑ R ∈ S.image rad,((S.filter (fun v => rad v=R)).card:ℝ) := by exact_mod_cast he
    _ ≤ ∑ _R ∈ S.image rad,C*X₁^a*X₂^a*Y^ε := Finset.sum_le_sum hfiber
    _ = ((S.image rad).card:ℝ)*(C*X₁^a*X₂^a*Y^ε) := by simp
    _ ≤ (128*Y/(Ideal.absNorm s:ℝ))*(C*X₁^a*X₂^a*Y^ε) :=
      mul_le_mul_of_nonneg_right hrad (by positivity)
    _ = _ := by rw [Real.rpow_add hY,Real.rpow_one]; ring

theorem partitioned_common_pair_count (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (s : Ideal O),Squarefree s → s ≠ 0 →
      ∀ S : Finset ((Ideal O × Ideal O) × Finset (Ideal O)),
      (∀ v ∈ S,v.1.1 ≠ 0 ∧ v.1.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1.1=primeSupport v.1.2) →
      (∀ v ∈ S,s ∣ v.1.1 ∧ s ∣ v.1.2) →
      (∀ v ∈ S,v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)) →
      ∀ X₁ X₂ Y : ℝ,0 < X₁ → 0 < X₂ → 0 < Y →
      (∀ v ∈ S,(Ideal.absNorm v.1.1:ℝ) ≤ X₁ ∧ (Ideal.absNorm v.1.2:ℝ) ≤ X₂) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ≤ Y) →
      (S.card:ℝ) ≤ C*X₁^a*X₂^a*Y^(1+ε)/(Ideal.absNorm s:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := common_pair_count a (ε/2) ha (by positivity)
  obtain ⟨D,hD,hpow⟩ := SquarefreeDivisorBound.prime_support_subsets_bound (ε/2) (by positivity)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro s hs hs0 S hS heq hdiv hpart X₁ X₂ Y hX₁ hX₂ hY hN hR
  have hpairs := hcount s hs hs0 (S.image Prod.fst)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hS w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact heq w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hdiv w hw)
    X₁ X₂ Y hX₁ hX₂ hY
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hN w hw)
    (by intro v hv; obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv; exact hR w hw)
  have hfiber (v : Ideal O × Ideal O) (hv : v ∈ S.image Prod.fst) :
      ((S.filter (fun w => w.1=v)).card:ℝ) ≤ D*Y^(ε/2) := by
    have hin : (S.filter (fun w => w.1=v)).image Prod.snd ⊆
        (primeSupport (commonRadical v.1 v.2)).powerset := by
      intro A hA
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨hw,hwe⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_powerset.mpr (hwe ▸ hpart w hw)
    have hinj : Set.InjOn (fun w : (Ideal O × Ideal O) × Finset (Ideal O) => w.2)
        (↑(S.filter (fun w => w.1=v)) : Set ((Ideal O × Ideal O) × Finset (Ideal O))) := by
      intro w hw z hz he
      exact Prod.ext ((Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hz).2.symm) he
    have hc : ((S.filter (fun w => w.1=v)).card:ℝ) ≤
        (2:ℝ)^(primeSupport (commonRadical v.1 v.2)).card := by
      have hb := Finset.card_le_card hin
      rw [Finset.card_image_of_injOn hinj,Finset.card_powerset] at hb
      exact_mod_cast hb
    obtain ⟨w,hw,hwe⟩ := Finset.mem_image.mp hv
    have hb := hpow (commonRadical v.1 v.2) (commonRadical_ne_zero _ _)
    have hn : (Ideal.absNorm (commonRadical v.1 v.2):ℝ) ≤ Y := hwe ▸ hR w hw
    exact hc.trans (hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hn (by positivity)) hD.le))
  have he := Finset.card_eq_sum_card_fiberwise
    (fun v (hv : v ∈ S) => Finset.mem_image_of_mem Prod.fst hv)
  calc
    _ = ∑ v ∈ S.image Prod.fst,((S.filter (fun w => w.1=v)).card:ℝ) := by exact_mod_cast he
    _ ≤ ∑ _v ∈ S.image Prod.fst,D*Y^(ε/2) := Finset.sum_le_sum hfiber
    _ = ((S.image Prod.fst).card:ℝ)*(D*Y^(ε/2)) := by simp
    _ ≤ (C*X₁^a*X₂^a*Y^(1+ε/2)/(Ideal.absNorm s:ℝ))*(D*Y^(ε/2)) :=
      mul_le_mul_of_nonneg_right hpairs (by positivity)
    _ = (C*D)*X₁^a*X₂^a*(Y^(1+ε/2)*Y^(ε/2))/(Ideal.absNorm s:ℝ) := by ring
    _ = _ := by rw [← Real.rpow_add hY]; congr 3; ring

end SevenEighths.CenteredMomentRankinLabels

end

end OAI
end OAIOriginalModule1543

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RankinScale
Source SHA256: 508fa216509a90764aa69866980f316ffc966b35a4e9338b9fcdee25d06fd4d0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1544


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinScale
open IdealMobiusDivisorSum CenteredMomentRankinRadical CenteredMomentRankinLabels
local notation "O" => ActualEisensteinCubic.O

theorem source_partition_count (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ,0 < C ∧ ∀ (Z p s₀ : ℝ),1 ≤ Z → 0 ≤ p → p ≤ B →
      ∀ (s : Ideal O),Squarefree s → s ≠ 0 → Z^s₀ ≤ (Ideal.absNorm s:ℝ) →
      ∀ S : Finset ((Ideal O × Ideal O) × Finset (Ideal O)),
      (∀ v ∈ S,v.1.1 ≠ 0 ∧ v.1.2 ≠ 0) →
      (∀ v ∈ S,primeSupport v.1.1=primeSupport v.1.2) →
      (∀ v ∈ S,s ∣ v.1.1 ∧ s ∣ v.1.2) →
      (∀ v ∈ S,v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)) →
      (∀ v ∈ S,(Ideal.absNorm v.1.1:ℝ) ≤ Z^B ∧ (Ideal.absNorm v.1.2:ℝ) ≤ Z^B) →
      (∀ v ∈ S,(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ) ≤ Z^p) →
      (S.card:ℝ) ≤ C*Z^(p-s₀+δ) := by
  let a : ℝ := δ/(3*(B+1))
  have ha : 0 < a := div_pos hδ (by positivity)
  obtain ⟨C,hC,hcount⟩ := partitioned_common_pair_count a a ha ha
  refine ⟨C,hC,?_⟩
  intro Z p s₀ hZ hp hpB s hs hs0 hNs S hS heq hdiv hpart hN hR
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hb := hcount s hs hs0 S hS heq hdiv hpart (Z^B) (Z^B) (Z^p)
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    (Real.rpow_pos_of_pos hZ0 _) hN hR
  have hpower : B*a+B*a+p*(1+a) ≤ p+δ := by
    have he : a*(3*(B+1))=δ := by dsimp only [a]; field_simp
    have hpa := mul_le_mul_of_nonneg_right hpB ha.le
    nlinarith
  calc
    _ ≤ C*(Z^B)^a*(Z^B)^a*(Z^p)^(1+a)/(Ideal.absNorm s:ℝ) := hb
    _ ≤ C*(Z^B)^a*(Z^B)^a*(Z^p)^(1+a)/(Z^s₀) :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hZ0 _) hNs
    _ = C*Z^(B*a+B*a+p*(1+a)-s₀) := by
      rw [← Real.rpow_mul hZ0.le,← Real.rpow_mul hZ0.le]
      rw [div_eq_mul_inv,← Real.rpow_neg hZ0.le]
      simp only [sub_eq_add_neg]
      rw [Real.rpow_add hZ0,Real.rpow_add hZ0,Real.rpow_add hZ0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hC.le

end SevenEighths.CenteredMomentRankinScale

end

end OAI
end OAIOriginalModule1544

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SourceRow
Source SHA256: 5d697f02e352e1ba102adb2400a9eb0d3fd019cf411f5214d7646fbf4b6fcbee
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1545



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentRowNorm HeckeFamily CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_split (η : Character) (m A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I = rowWeight η m A 1 t I*idealRowHom z I := by
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) =
    ((idealCoeff η I*idealRowHom (m^6*(A*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*idealRowHom z I
  rw [mul_one,← mul_assoc,idealRowHom_argument_mul]
  ring

theorem rowWeight_zero_of_not_supported (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m) (I : Ideal O) (hI : ¬Supported I) :
    rowWeight η m A z t I=0 := by
  by_cases h0 : I=0
  · rw [h0,map_zero]
  let n := idealGenerator I
  have hn : n ≠ 0 := idealGenerator_ne_zero I h0
  have hs : Ideal.span {n}=I := span_idealGenerator I
  have hz := rowTwist_zero_of_not_supported (HeckeRowClosure.elementHom η) m 1 (A*z) n
    hmLam hm2 (hs ▸ hI)
  have he : rowTwist (HeckeRowClosure.elementHom η) m 1 (A*z) n =
      idealCoeff η I*idealRowHom (m^6*(A*z)) I := by
    change elementCoeff η n*idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n})=_
    rw [one_pow,mul_one,hs,← idealCoeff_span η hn,hs]
  rw [he] at hz
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=0
  rw [hz,zero_mul]

def supportedColumns (S : Finset (Ideal O)) : Finset (Ideal O) := S.filter Supported

theorem primary_span_supported (I : Ideal O) (hI : Supported I) : Ideal.span {primaryGenerator I}=I := by
  have hn : primaryGenerator I ≠ 0 := by
    have hs : Supported (Ideal.span {idealGenerator I}) := by rw [span_idealGenerator]; exact hI
    have hg := (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff (idealGenerator I)).mpr
      ((supported_span_iff _).mp hs).1
    simpa only [span_idealGenerator] using hg
  exact (primaryGenerator_spec I hn).1

def sourceGenerator (S : Finset (Ideal O)) (I : supportedColumns S) : O := primaryGenerator I

theorem sourceGenerator_supported (S : Finset (Ideal O)) (I : supportedColumns S) :
    Supported (Ideal.span {sourceGenerator S I}) := by
  have hI := (Finset.mem_filter.mp I.property).2
  rw [sourceGenerator,primary_span_supported I hI]
  exact hI

theorem finite_hecke_sum_eq_rowPolynomial (η : Character) (m A z : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    (∑ I∈S,c I*rowWeight η m A z t I) =
      rowPolynomial Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) z := by
  have he : (∑ I∈S,c I*rowWeight η m A z t I) =
      ∑ I∈supportedColumns S,c I*rowWeight η m A z t I := by
    symm
    apply Finset.sum_filter_of_ne
    intro I hI hn
    by_contra hs
    exact hn (by rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hs,mul_zero])
  rw [he,← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*rowWeight η m A z t I)]
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,rowWeight_split]
  ring

def finiteHeckeEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O,((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
    W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)

theorem finiteHeckeEnergy_eq (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy η m A t S c W K =
      rowEnergy Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) W K := by
  unfold finiteHeckeEnergy rowEnergy
  simp_rw [finite_hecke_sum_eq_rowPolynomial η m A _ t hmLam hm2 S c]

theorem finiteHeckeEnergy_poisson (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          (((K/‖ConcreteTraceCRT.eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2:ℝ):ℂ)*
            ∑' h : O,pairFourier (sourceGenerator S I) (sourceGenerator S J)
              (sourceGenerator_supported S I) (sourceGenerator_supported S J) h*
              EisensteinSchwartzPoisson.paperRadialFourier W
                (K*‖ConcreteTraceCRT.eisEmbedding h‖^2/
                  ‖ConcreteTraceCRT.eisEmbedding (sourceGenerator S I*sourceGenerator S J)‖^2)) := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K]
  exact rowEnergy_poisson Finset.univ (sourceGenerator S)
    (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
    (sourceGenerator_supported S) W K hK

end SevenEighths.CenteredMomentSourceRow

end

end OAI
end OAIOriginalModule1545

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstEnergy
Source SHA256: b1f198845756e185113a9be9a9bd53f2acae0fe64cde707c19fdce9ae1f31bc5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1546



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstEnergy
open CenteredMomentCanonicalFirst CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentHeckeExpansion HeckeFamily ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem finiteHeckeEnergy_reduced_poisson (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          reducedFirstSum I J (Finset.mem_filter.mp I.property).2
            (Finset.mem_filter.mp J.property).2 W K := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K,
    rowEnergy_expand Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
      (sourceGenerator_supported S) W K hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [sourceGenerator,sourceGenerator,
    primary_span_supported I (Finset.mem_filter.mp I.property).2,
    primary_span_supported J (Finset.mem_filter.mp J.property).2,
    canonical_pair_reduced_poisson]
  exact hK

end SevenEighths.CenteredMomentFirstEnergy

end

end OAI
end OAIOriginalModule1546

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstIdealFamily
Source SHA256: 7e5b59e01bbb802e9025b0204b396e6694f7debf03b0506a841428b457280314
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1547



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstIdealFamily
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentFirstColumns
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_one_primary (η : Character) (m : O) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    rowWeight η m 1 1 t I=elementCoeff η (CompletedGauss.primaryGenerator I)*
      coprimalityMask m (CompletedGauss.primaryGenerator I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have he : idealCoeff η I=elementCoeff η (CompletedGauss.primaryGenerator I) := by
    have hh := idealCoeff_span η hn
    rw [hs] at hh
    exact hh
  have hm : idealRowHom (m^6) I=coprimalityMask m (CompletedGauss.primaryGenerator I) := by
    have hh := idealRowHom_sixth_eq_mask m _ (hs.symm ▸ hI)
    rw [hs] at hh
    exact hh
  change (idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
  rw [mul_one,mul_one,he,hm]

theorem ideal_height_of_primary (η τ : Character) (m : O) (F : O → ℂ)
    (hτ : ∀ n : O,Supported (Ideal.span {n}) → goodLambda^2∣n-1 →
      elementCoeff τ n=elementCoeff η n*coprimalityMask m n*F n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
      rowWeight η m 1 1 t I*F (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := CompletedGauss.primaryGenerator_spec I hn
  have he := hτ (CompletedGauss.primaryGenerator I) (hs.1.symm ▸ hI) hs.2
  rw [← idealCoeff_span τ hn,hs.1] at he
  rw [he,rowWeight_one_primary η m t I hI]
  ring

theorem exists_first_ideal_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O,Supported I → ∀ t : ℝ,
        idealCoeff τ₁ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
          rowWeight η m 1 1 t I*
            (leftCoefficient e r ρ (CompletedGauss.primaryGenerator I)*
              rayCharacter ξ₁ (CompletedGauss.primaryGenerator I))) ∧
      (∀ I : Ideal O,Supported I → ∀ t : ℝ,
        idealCoeff τ₂ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
          rowWeight η m 1 1 t I*
            (rightCoefficient e r ρ (CompletedGauss.primaryGenerator I)*
              rayCharacter ξ₂ (CompletedGauss.primaryGenerator I))) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_canonical_first_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro I hI t
    apply ideal_height_of_primary η τ₁ m
      (fun n => leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*rayCharacter ξ₁ n) _ I hI t
    intro n hn hp
    rw [h₁ n hn hp]
    ring
  · intro I hI t
    apply ideal_height_of_primary η τ₂ m
      (fun n => rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
        (activeConductor C D) (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n*rayCharacter ξ₂ n) _ I hI t
    intro n hn hp
    rw [h₂ n hn hp]
    ring

end SevenEighths.CenteredMomentFirstIdealFamily

end

end OAI
end OAIOriginalModule1547

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSectorEnergy
Source SHA256: bf3c46c3195ad19f8130dc8ad8efed67347c5310a7690d5a940515ecdb13ba26
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1548



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorEnergy
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalRowCompletion CanonicalQuadraticSieve HeckeFamily
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentCommonSectors CenteredMomentCompleteCommon
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport CenteredMomentActive CenteredMomentFourier IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def originalKernel (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O,(idealRowHom z I*star (idealRowHom z J))*W (‖eisEmbedding z‖^2/K)

theorem energy_common_sectors (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ p∈commonLabels (supportedColumns S) (supportedColumns S),
        ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
          ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*
            originalKernel q.1 q.2 W K := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K,
    rowEnergy_expand Finset.univ (sourceGenerator S)
      (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
      (sourceGenerator_supported S) W K hK]
  have hspan (I : supportedColumns S) : Ideal.span {sourceGenerator S I} = I :=
    primary_span_supported I (Finset.mem_filter.mp I.property).2
  simp_rw [hspan]
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K)=_
  let F := fun I J : Ideal O =>
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K
  have he (I : Ideal O) : (∑ J : supportedColumns S,F I J)=∑ J∈supportedColumns S,F I J :=
    Finset.sum_coe_sort (supportedColumns S) (F I)
  change (∑ I : supportedColumns S,∑ J : supportedColumns S,F I J)=_
  simp_rw [he]
  rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ∑ J∈supportedColumns S,F I J)]
  exact sum_common_sectors _ _ _

theorem sector_independent_columns (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (C D : Ideal O)
    (hC : C≠0) (hD : D≠0) (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*originalKernel q.1 q.2 W K) =
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        ∑ a∈residualPool C hC (supportedColumns S),∑ b∈residualPool D hD (supportedColumns S),
          if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
            ((c (C*a)*rowWeight η m A 1 t a)*star (c (D*b)*rowWeight η m A 1 t b))*
              originalKernel (C*a) (D*b) W K else 0 := by
  rw [pairSector_double_sum C D hC hD hCD _ _
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I hI => (Finset.mem_filter.mp hI).2.1)
    (fun I J => ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*originalKernel I J W K),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  split_ifs <;> simp only [map_mul,star_mul,mul_zero]
  ring

theorem fixed_common_parts (C D : Ideal O) (hC : C≠0) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) : commonPart C D=C ∧ commonPart D C=D := by
  simpa only [mul_one] using reconstructed_commonParts C D 1 1 hC hD one_ne_zero one_ne_zero
    hCD (isCoprime_one_right) (isCoprime_one_right) (isCoprime_one_left)

def fixedFirstSum (C D : Ideal O) (hC : Supported C) (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E ∈ (principalSupport (Finset.univ : Finset (CommonIndex C D)) (leftExponent C D) (rightExponent C D)).powerset,
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let k := K/‖eisEmbedding e‖^2
    let r := activeConductor C D
    (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow a b r (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC) e*
      (((k/‖eisEmbedding (a*(b*r))‖^2:ℝ):ℂ)*∑' h : O,
        tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter a ha)
          (supportedModulusCharacter b hb)⁻¹ (activeFunction C D hC) h*
          paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (a*(b*r))‖^2))

theorem originalKernel_fixed_first (C D : Ideal O) (hC : Supported C) (hD : D≠0)
    (hCD : primeSupport C=primeSupport D) (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    originalKernel (C*Ideal.span {a}) (D*Ideal.span {b}) W K=fixedFirstSum C D hC a b ha hb W K := by
  let := finite_quotient_span (supported_element_ne_zero b hb)
  obtain ⟨h₁,h₂⟩ := fixed_common_parts C D hC.1 hD hCD
  have he := common_residual_reduced_poisson (fun P : CommonIndex C D => P.val) Subtype.val_injective
    (common_good C D hC) (common_odd C D hC) Finset.univ (leftExponent C D) (rightExponent C D)
    (fun P _ => ne_of_gt (leftExponent_pos C D P)) (fun P _ => ne_of_gt (rightExponent_pos C D P))
    a b (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
    (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ W K hK
  change _=fixedFirstSum C D hC a b ha hb W K at he
  rw [← he]
  unfold originalKernel
  apply tsum_congr
  intro z
  rw [← MulChar.star_apply',supportedModulusCharacter_mk,supportedModulusCharacter_mk,
    ← commonPart_left_product,← commonPart_right_product,h₁,h₂]
  simp only [map_mul,star_mul]
  ring

end SevenEighths.CenteredMomentFirstSectorEnergy

end

end OAI
end OAIOriginalModule1548

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSectorTransform
Source SHA256: c0db0a3c60605dd37439fcea2075bc01feffcdb3f17e54c1f32714a14147852a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1549



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorTransform
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve HeckeFamily CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentSupportedCorrelation IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem residualPool_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Supported (a:Ideal O) := by
  have ha := (Finset.mem_filter.mp ((mem_residualPool C hC (supportedColumns S) a).mp a.property)).2
  exact ((supported_mul_iff C a).mp ha).2

def residualElement (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : O := CompletedGauss.primaryGenerator a

theorem residualElement_span (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Ideal.span {residualElement C hC S a}=a :=
  primary_span_supported a (residualPool_supported C hC S a)

theorem residualElement_supported (C : Ideal O) (hC : C≠0) (S : Finset (Ideal O))
    (a : residualPool C hC (supportedColumns S)) : Supported (Ideal.span {residualElement C hC S a}) := by
  rw [residualElement_span]
  exact residualPool_supported C hC S a

def sectorFixedTransform (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ a : residualPool C hC.1 (supportedColumns S),
    ∑ b : residualPool D hD.1 (supportedColumns S),
      if IsCoprime C (a:Ideal O) ∧ IsCoprime C (b:Ideal O) ∧ IsCoprime (a:Ideal O) (b:Ideal O) then
        ((c (C*a)*rowWeight η m A 1 t a)*star (c (D*b)*rowWeight η m A 1 t b))*
          fixedFirstSum C D hC (residualElement C hC.1 S a) (residualElement D hD.1 S b)
            (residualElement_supported C hC.1 S a) (residualElement_supported D hD.1 S b) W K
      else 0

theorem sector_fixed_transform (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    (∑ q∈pairSector C D (supportedColumns S) (supportedColumns S),
      ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*originalKernel q.1 q.2 W K) =
      rowWeight η m A 1 t C*star (rowWeight η m A 1 t D)*
        sectorFixedTransform η m A t S c C D hC hD W K := by
  rw [sector_independent_columns η m A t S c C D hC.1 hD.1 hCD W K]
  congr 1
  unfold sectorFixedTransform
  let F := fun a b : Ideal O =>
    if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then
      ((c (C*a)*rowWeight η m A 1 t a)*star (c (D*b)*rowWeight η m A 1 t b))*originalKernel (C*a) (D*b) W K else 0
  change (∑ a∈residualPool C hC.1 (supportedColumns S),∑ b∈residualPool D hD.1 (supportedColumns S),F a b)=_
  rw [← Finset.sum_coe_sort _ (fun a => ∑ b∈residualPool D hD.1 (supportedColumns S),F a b)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_coe_sort _ (F a)]
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only [F]
  split_ifs
  · have hh := originalKernel_fixed_first C D hC hD.1 hCD
      (residualElement C hC.1 S a) (residualElement D hD.1 S b)
      (residualElement_supported C hC.1 S a) (residualElement_supported D hD.1 S b) W K hK
    rw [residualElement_span,residualElement_span] at hh
    rw [hh]
  · rfl

theorem commonLabels_supported (S : Finset (Ideal O))
    (p : commonLabels (supportedColumns S) (supportedColumns S)) :
    Supported p.val.1 ∧ Supported p.val.2 := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp p.property
  have hq₁ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
  have hq₂ := (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).2
  rw [← he]
  exact ⟨commonPart_supported _ _ hq₁,commonPart_supported _ _ hq₂⟩

theorem energy_fixed_transforms (η : Character) (m A : O) (t : ℝ)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      ∑ p : commonLabels (supportedColumns S) (supportedColumns S),
        rowWeight η m A 1 t p.val.1*star (rowWeight η m A 1 t p.val.2)*
          sectorFixedTransform η m A t S c p.val.1 p.val.2
            (commonLabels_supported S p).1 (commonLabels_supported S p).2 W K := by
  rw [energy_common_sectors η m A t hmLam hm2 S c W K hK]
  rw [← Finset.sum_coe_sort _ (fun p : Ideal O × Ideal O => ∑ q∈pairSector p.1 p.2 (supportedColumns S) (supportedColumns S),
    ((c q.1*rowWeight η m A 1 t q.1)*star (c q.2*rowWeight η m A 1 t q.2))*originalKernel q.1 q.2 W K)]
  apply Finset.sum_congr rfl
  intro p hp
  exact sector_fixed_transform η m A t S c p.val.1 p.val.2
    (commonLabels_supported S p).1 (commonLabels_supported S p).2
    (commonLabels_data _ _ p.val.1 p.val.2 p.property).2.2 W K hK

end SevenEighths.CenteredMomentFirstSectorTransform

end

end OAI
end OAIOriginalModule1549

/-! Original module: OAI.NumberTheory.DirichletL.Moments.HeckeColumnWindow
Source SHA256: 0ea6c407b7748b6c6abce234c9831803ed61cec1a8487883e0538586b13d0fb8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1550



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeColumnWindow
open FourierBridge HeckeFamily CenteredMomentSmooth CenteredMomentGaussEnergy
open CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

def heightCoeff (τ : Character) (t : ℝ) (I : Ideal O) : ℂ :=
  idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)

theorem heightCoeff_add (τ : Character) (I : Ideal O) (hI : I≠0) (t v : ℝ) :
    heightCoeff τ (t+v) I=heightCoeff τ t I*(Ideal.absNorm I:ℂ)^(Complex.I*v) := by
  have hn : (Ideal.absNorm I:ℂ)≠0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [heightCoeff,Complex.ofReal_add,mul_add,Complex.cpow_add _ _ hn]
  ring

theorem heightCoeff_phase (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    heightCoeff τ t I*logPhase θ (-Real.log ((Ideal.absNorm I:ℝ)/X))=
      logPhase θ (Real.log X)*heightCoeff τ (t-2*Real.pi*θ) I := by
  have hn : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [logPhase_norm_ratio _ X θ hn hX,sub_eq_add_neg,heightCoeff_add τ I hI]
  push_cast
  ring

def rootProfile (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) : 𝓢(ℝ,ℂ) :=
  (hVc.mul_right (f':=fun u : ℝ => (Real.exp (-u/2):ℂ))).toSchwartzMap
    (hVs.mul (Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2))))

theorem rootProfile_apply (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (u : ℝ) :
    rootProfile V hVc hVs u=rootWindow V u := by
  change V u*(Real.exp (-u/2):ℂ)=_
  rw [rootWindow,← Real.exp_half,show -u/2=-(u/2) by ring,Real.exp_neg,
    Complex.ofReal_inv,div_eq_mul_inv]
  ring

def columnDensity (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) : 𝓢(ℝ,ℂ) :=
  𝓕 (rootProfile V hVc hVs)

theorem columnDensity_moments (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (J : ℕ) :
    Integrable (fun w : ℝ => (1+‖w‖)^J*‖columnDensity V hVc hVs w‖) :=
  JointLogSeparation.weighted_schwartz_integrable _ J

theorem rootWindow_integral (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (u : ℝ) :
    rootWindow V u=∫ w : ℝ,logPhase w u*columnDensity V hVc hVs w := by
  rw [← rootProfile_apply V hVc hVs u,schwartz_log_inversion]
  apply integral_congr_ae
  filter_upwards [] with w
  congr 2
  simp only [Real.inner_apply]
  push_cast
  ring

theorem phase_combine (w θ u : ℝ) :
    logPhase w u*logPhase θ (-u)=logPhase (θ-w) (-u) := by
  unfold logPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem height_column_integral (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    heightCoeff τ t I*columnPhase V (Real.log ((Ideal.absNorm I:ℝ)/X)) θ=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) I := by
  rw [columnPhase,rootWindow_integral V hVc hVs,← mul_assoc,← integral_const_mul,← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with w
  calc
    _ = columnDensity V hVc hVs w*(heightCoeff τ t I*
      (logPhase w (Real.log ((Ideal.absNorm I:ℝ)/X))*
        logPhase θ (-Real.log ((Ideal.absNorm I:ℝ)/X)))) := by ring
    _ = _ := by
      rw [phase_combine,heightCoeff_phase τ I hI t (θ-w) X hX,
        show t-2*Real.pi*(θ-w)=t+2*Real.pi*(w-θ) by ring]
      ring

theorem height_column_integrable (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (τ : Character) (I : Ideal O) (hI : I≠0)
    (t θ X : ℝ) (hX : 0<X) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      heightCoeff τ (t+2*Real.pi*(w-θ)) I) := by
  have he (w : ℝ) : logPhase (θ-w) (Real.log X)*heightCoeff τ (t+2*Real.pi*(w-θ)) I=
      heightCoeff τ t I*logPhase (θ-w) (-Real.log ((Ideal.absNorm I:ℝ)/X)) := by
    rw [heightCoeff_phase τ I hI t (θ-w) X hX]
    congr 2
    ring
  have hfun : (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      heightCoeff τ (t+2*Real.pi*(w-θ)) I) =
      (fun w : ℝ => columnDensity V hVc hVs w*(heightCoeff τ t I*
        logPhase (θ-w) (-Real.log ((Ideal.absNorm I:ℝ)/X)))) := by
    funext w
    rw [mul_assoc,he w]
  rw [hfun]
  apply ((columnDensity V hVc hVs).integrable.norm.const_mul ‖heightCoeff τ t I‖).mono'
  · have hp := (logPhase_continuous_left (-Real.log ((Ideal.absNorm I:ℝ)/X))).comp
      (show Continuous (fun w : ℝ => θ-w) from continuous_const.sub continuous_id)
    exact ((columnDensity V hVc hVs).continuous.mul (hp.const_mul _)).aestronglyMeasurable
  · filter_upwards [] with w
    simp only [norm_mul,logPhase_norm,mul_one]
    exact le_of_eq (mul_comm _ _)

theorem gauss_column_integral {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    gaussPolynomial S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z := by
  have hi (i : α) : Integrable (fun w : ℝ => β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*gaussRow (a i) (ha i) z) :=
    ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul _).mul_const _
  unfold gaussPolynomial
  calc
    _ = ∑ i∈S,∫ w : ℝ,β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*gaussRow (a i) (ha i) z := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_const,integral_const_mul,← height_column_integral V hVc hVs τ _ (ha i).1 t θ X hX]
      ring
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => hi i)]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

end SevenEighths.CenteredMomentHeckeColumnWindow

end

end OAI
end OAIOriginalModule1550

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ConjugateWindow
Source SHA256: c20652c3cb5db5ed9e349a2481ef32beee5eb3f229cce272eb50f99dff73828f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1551


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentConjugateWindow
open FourierBridge CenteredMomentSmooth

theorem star_logPhase (t u : ℝ) : star (logPhase t u)=logPhase (-t) u := by
  simp only [logPhase,Complex.star_def,← Complex.exp_conj,map_mul,
    Complex.conj_ofReal,Complex.conj_I]
  congr 1
  push_cast
  ring

theorem star_columnPhase (V : ℝ → ℂ) (u t : ℝ) :
    star (columnPhase V u t)=columnPhase (fun x => star (V x)) u (-t) := by
  rw [columnPhase,star_mul,star_logPhase,columnPhase,mul_comm]
  congr 1
  simp only [rootWindow,Complex.star_def,map_div₀,Complex.conj_ofReal]

theorem conjugate_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (fun x => star (V x)) := by
  apply hV.comp_left
  simp

theorem conjugate_smooth (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun x => star (V x)) := by
  exact Complex.conjCLE.contDiff.comp hV

end SevenEighths.CenteredMomentConjugateWindow

end

end OAI
end OAIOriginalModule1551

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstChildProfile
Source SHA256: 2fb869a4de0569a44fd0aec5da10435c08f946621282741f429581783b35d31b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1552


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFirstChildProfile
open HeckeFamily CenteredMomentFirstIdealFamily CenteredMomentHeckeColumnWindow
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst CenteredMomentHeckeExpansion
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentSourceRow
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem divisor_column_of_family (η τ : Character) (m : O) (F : O → ℂ) (ξ : RayCharacter)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η m 1 1 t I*(F (CompletedGauss.primaryGenerator I)*
        rayCharacter ξ (CompletedGauss.primaryGenerator I)))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => CompletedGauss.primaryGenerator J)
      (fun J => β J*rowWeight η m 1 1 t J*F (CompletedGauss.primaryGenerator J)) ξ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring

theorem exists_first_divisor_pair (η : Character) (m : O) (hm : m≠0)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ L I : Ideal O,Supported I → ∀ β : Ideal O → ℂ,∀ t : ℝ,
        divisorCoefficient L (fun J : Ideal O => CompletedGauss.primaryGenerator J)
          (fun J => β J*rowWeight η m 1 1 t J*leftCoefficient e r ρ (CompletedGauss.primaryGenerator J)) ξ₁ I=
          (if L∣I then β I else 0)*heightCoeff τ₁ t I) ∧
      (∀ L I : Ideal O,Supported I → ∀ β : Ideal O → ℂ,∀ t : ℝ,
        divisorCoefficient L (fun J : Ideal O => CompletedGauss.primaryGenerator J)
          (fun J => β J*rowWeight η m 1 1 t J*rightCoefficient e r ρ (CompletedGauss.primaryGenerator J)) ξ₂ I=
          (if L∣I then β I else 0)*heightCoeff τ₂ t I) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_first_ideal_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro L I hI β t
    exact divisor_column_of_family η τ₁ m _ ξ₁ h₁ L I hI β t
  · intro L I hI β t
    exact divisor_column_of_family η τ₂ m _ ξ₂ h₂ L I hI β t

end SevenEighths.CenteredMomentFirstChildProfile

end

end OAI
end OAIOriginalModule1552

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSource
Source SHA256: 71421215f1e4f0e2c5d5f56a750795520935626f73607599ea55803e94485aec
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1553




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy CenteredMomentFirstSectorTransform
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced CenteredMomentFirstFrequency CenteredMomentFirstWholeKernel
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentSmooth CenteredMomentScale CenteredMomentPrimitive IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

def columns (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O)):Finset (Ideal O):=
  (residualPool D hD (supportedColumns S)).filter (fun I=>IsCoprime C I)

lemma column_supported (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))
    (a:columns C D hD S):Supported (a:Ideal O):=
  residualPool_supported D hD S ⟨a.val,(Finset.mem_filter.mp a.property).1⟩

def element (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):O:=
  CompletedGauss.primaryGenerator a

lemma element_span (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    Ideal.span {element C D hD S a}=a:=primary_span_supported a (column_supported C D hD S a)

lemma element_supported (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    Supported (Ideal.span {element C D hD S a}):=by
  rw [element_span];exact column_supported C D hD S a

lemma element_primary (C D:Ideal O)(hD:D≠0)(S:Finset (Ideal O))(a:columns C D hD S):
    goodLambda^2∣element C D hD S a-1:=
  (CompletedGauss.primaryGenerator_spec a (supported_primaryGenerator_ne_zero a
    (column_supported C D hD S a))).2

lemma active_span_dvd (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D):Ideal.span {activeConductor C D}∣C:=by
  have hh:=activeConductor_span_dvd C D
  rw [(fixed_common_parts C D hC hD hCD).1] at hh
  exact hh

lemma element_coprime_active (C D B:Ideal O)(hC:C≠0)(hD:D≠0)(hB:B≠0)
    (hCD:primeSupport C=primeSupport D)(S:Finset (Ideal O))(a:columns C B hB S):
    IsCoprime (element C B hB S a) (activeConductor C D):=by
  rw [←Ideal.isCoprime_span_singleton_iff,element_span]
  exact (Finset.mem_filter.mp a.property).2.symm.of_isCoprime_of_dvd_right (active_span_dvd C D hC hD hCD)

def coefficient (η:Character)(m A:O)(t:ℝ)(c:Ideal O→ℂ)(D:Ideal O)
    (I:Ideal O):ℂ:=c (D*I)*CenteredMomentHeckeExpansion.rowWeight η m A 1 t I

def inactiveWeight (C D:Ideal O)(E:Finset (CommonIndex C D)):ℂ:=
  (UniqueFactorizationMonoid.moebius (∏P∈E,P.val):ℂ)

def block (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (rows:Finset O)(W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  let r:=activeConductor C D
  inactiveWeight C D E * ∑h∈rows,
    ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
      let na:=element C C hC.1 S a
      let nb:=element C D hD.1 S b
      if IsCoprime (a:Ideal O) (b:Ideal O) then
        (tripleRow na nb r (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) e *
        ((k/‖eisEmbedding (na*(nb*r))‖^2:ℝ):ℂ)*
        tripleFourier na nb r
          (supported_element_ne_zero _ (element_supported C C hC.1 S a))
          (supported_element_ne_zero _ (element_supported C D hD.1 S b))
          (finitePrimeModulus_ne_zero _) (supportedModulusCharacter na (element_supported C C hC.1 S a))
          (supportedModulusCharacter nb (element_supported C D hD.1 S b))⁻¹ (activeFunction C D hC) h)*
        (coefficient η m A t c C a*star (coefficient η m A t c D b))*
        windows V (k/‖eisEmbedding r‖^2) (‖eisEmbedding h‖^2)
          (‖eisEmbedding na‖^2) (‖eisEmbedding nb‖^2) K₀ H₀ A₀ B₀*
        EisensteinSchwartzPoisson.paperRadialFourier W (k*‖eisEmbedding h‖^2/‖eisEmbedding (na*(nb*r))‖^2)
      else 0

def scalar (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))(K A₀ B₀:ℝ):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let k:=K/‖eisEmbedding e‖^2
  inactiveWeight C D E * ((k:ℂ)*canonicalNormalizedGauss (activePrime C D)
    (activeCoprime C D) (activeGood C D hC) (activeExponent C D)/
      ((‖eisEmbedding (activeConductor C D)‖:ℂ)*(Real.sqrt A₀:ℂ)*(Real.sqrt B₀:ℂ)))

theorem block_eq_whole (η:Character)(m A:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(rows:Finset O)(hrows:∀h∈rows,h≠0)
    (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)(K K₀ H₀ A₀ B₀:ℝ)
    (hK:0<K)(hK₀:0<K₀)(hH₀:0<H₀)(hA₀:0<A₀)(hB₀:0<B₀):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
    let k:=K/‖eisEmbedding e‖^2
    let r:=activeConductor C D
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    block η m A t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀=
      scalar C D hC E K A₀ B₀ * ∑h∈rows,star (ρ h)*
        ∑a:columns C C hC.1 S,∑b:columns C D hD.1 S,
          ((if IsCoprime (element C C hC.1 S a) (element C D hD.1 S b) then
            originalPhase e r ρ (element C C hC.1 S a) (element C D hD.1 S b) else 0)*
            (coefficient η m A t c C a*star (coefficient η m A t c D b)))*
          (gaussRow _ (element_supported C C hC.1 S a) h*
            star (gaussRow _ (element_supported C D hD.1 S b) (-h)))*
          wholeKernel W V (K₀*H₀/(A₀*B₀))
            (Real.log ((k/‖eisEmbedding r‖^2)/K₀)) (Real.log (‖eisEmbedding h‖^2/H₀))
            (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))
            (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀)):=by
  dsimp only
  have he:primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E≠0:=
    supported_element_ne_zero _ (subsetGenerator_supported C D hC E)
  have hk:0<K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
  unfold block scalar
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hcop:IsCoprime (element C C hC.1 S a) (element C D hD.1 S b)↔
      IsCoprime (a:Ideal O) (b:Ideal O):=by
    rw [←Ideal.isCoprime_span_singleton_iff,element_span,element_span]
  by_cases hab:IsCoprime (a:Ideal O) (b:Ideal O)
  · simp only [hab,ite_true,hcop]
    have hh:=dilated_frequency_whole_kernel (activePrime C D) (activeCoprime C D)
      (activeGood C D hC) (fun P=>common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=>netExponent_lt_six _ _)
      (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
      (element C C hC.1 S a) (element C D hD.1 S b)
      (element_supported C C hC.1 S a) (element_supported C D hD.1 S b)
      ((hcop.mpr hab).mul_right (element_coprime_active C D C hC.1 hD.1 hC.1 hCD S a))
      (element_coprime_active C D D hC.1 hD.1 hD.1 hCD S b)
      _ hk h (hrows h hh) W V K₀ H₀ A₀ B₀ hK₀ hH₀ hA₀ hB₀
    dsimp only at hh
    change inactiveWeight C D E * (_*_*_*_)=_
    calc
      _=inactiveWeight C D E*(coefficient η m A t c C a*star (coefficient η m A t c D b))*
        (dilatedFrequency (activePrime C D) (activeCoprime C D) (activeGood C D hC)
          (activeExponent C D) (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)
          (element C C hC.1 S a) (element C D hD.1 S b)
          (element_supported C C hC.1 S a) (element_supported C D hD.1 S b)
          (K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2) h *
        windows V _ _ _ _ K₀ H₀ A₀ B₀ * EisensteinSchwartzPoisson.paperRadialFourier W _):=by
          dsimp [dilatedFrequency,activeFunction,activeConductor];ring
      _=_:=by rw [hh];dsimp only [activeConductor];ring
  · simp [hab,hcop]

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule1553

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceBound
Source SHA256: bf69a0986843f96be0b29e5265bba853aafa8eef86dbba6cc4e4b52cfeba7b93
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1554


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCompleteCommon
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentFirstReduced
open CenteredMomentFirstColumns CenteredMomentFirstAssembly CenteredMomentGaussEnergy
open CenteredMomentFirstChildBound CenteredMomentChildAssembly CenteredMomentMobiusRegroup
open CenteredMomentSmooth RayFourExpansion IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem physical_block_child_bound (W:𝓢(ℝ,ℂ))(V:Fin 4→ℝ→ℂ)
    (M:Fin 4→ℝ)(hM:∀i,0≤M i)(hV:∀i y,V i y≠0→|y|≤M i)(A J₁ J₂:ℕ):
    ∃Cbound:ℝ,0≤Cbound ∧
    ∀(η:Character)(m:O)(t:ℝ)(S:Finset (Ideal O))(c:Ideal O→ℂ)
      (C D:Ideal O)(hC:Supported C)(hD:Supported D),primeSupport C=primeSupport D→
    ∀(E:Finset (CommonIndex C D))(rows:Finset O),(∀h∈rows,h≠0)→
    ∀K K₀ H₀ A₀ B₀:ℝ,0<K→0<K₀→0<H₀→0<A₀→0<B₀→
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let k:=K/‖eisEmbedding e‖^2;
    let r:=activeConductor C D;
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D);
    (∀h∈rows,‖V 0 (Real.log ((k/‖eisEmbedding r‖^2)/K₀))‖≤1)→
    (∀h∈rows,‖V 1 (Real.log (‖eisEmbedding h‖^2/H₀))‖≤1)→
    ∀(U:𝓢(ℝ,ℂ))(H:ℝ),0<H→
    (∀h:O,0≤(U (‖eisEmbedding h‖^2/H)).re)→
    (∀h∈rows,1≤(U (‖eisEmbedding h‖^2/H)).re)→
    ∀B₁ B₂:Ideal O→ℝ,
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),0≤B₁ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),0≤B₂ L)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),∀χ:RayCharacter,∀v:ℝ,
      (gaussEnergy Finset.univ (element C C hC.1 S) (element_supported C C hC.1 S)
        (fun a=>divisorCoefficient L (element C C hC.1 S)
          (fun a=>coefficient η m 1 t c C a*leftCoefficient e r ρ (element C C hC.1 S a)) χ a*
          columnPhase (V 2) (Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀)) v) U H).re
            ≤(B₁ L*(1+‖v‖)^J₁)^2)→
    (∀L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
      (fun b=>Ideal.span {element C D hD.1 S b}),∀χ:RayCharacter,∀v:ℝ,
      (gaussEnergy Finset.univ (element C D hD.1 S) (element_supported C D hD.1 S)
        (fun b=>divisorCoefficient L (element C D hD.1 S)
          (fun b=>coefficient η m 1 t c D b*rightCoefficient e r ρ (element C D hD.1 S b)) χ b*
          star (columnPhase (V 3) (Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀)) v)) U H).re
            ≤(B₂ L*(1+‖v‖)^J₂)^2)→
    (1+K₀*H₀/(A₀*B₀))^A*‖block η m 1 t S c C D hC hD E rows W V K K₀ H₀ A₀ B₀‖≤
      ‖scalar C D hC E K A₀ B₀‖*Cbound*
        ∑L∈divisorPool (Finset.univ:Finset (columns C D hD.1 S))
          (fun b=>Ideal.span {element C D hD.1 S b}),
          ‖(UniqueFactorizationMonoid.moebius L:ℂ)‖*(B₁ L*B₂ L):=by
  obtain ⟨Cbound,hCbound,hbound⟩:=whole_kernel_first_child_bound.{0,0} W V M hM hV A J₁ J₂
  refine ⟨Cbound,hCbound,?_⟩
  intro η m t S c C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀
  dsimp only
  intro hV₀ hV₁ U H hH hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  have hh:=hbound (K₀*H₀/(A₀*B₀)) (div_pos (mul_pos hK₀ hH₀) (mul_pos hA₀ hB₀))
    rows Finset.univ Finset.univ (element C C hC.1 S) (element C D hD.1 S)
    (element_supported C C hC.1 S) (element_supported C D hD.1 S)
    (element_primary C C hC.1 S) (element_primary C D hD.1 S)
    (fun a=>coefficient η m 1 t c C a) (fun b=>coefficient η m 1 t c D b)
    (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E) (activeConductor C D)
    (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D))
    (finiteSexticRow_mul _ _ _) (QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _)
    (fun h=>star (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D) h))
    (fun a=>Real.log (‖eisEmbedding (element C C hC.1 S a)‖^2/A₀))
    (fun b=>Real.log (‖eisEmbedding (element C D hD.1 S b)‖^2/B₀))
    (fun _=>Real.log ((K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2/
      ‖eisEmbedding (activeConductor C D)‖^2)/K₀))
    (fun h=>Real.log (‖eisEmbedding h‖^2/H₀))
    (fun h _=>by rw [norm_star];exact QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _)
    hV₀ hV₁ U H hH hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [block_eq_whole η m 1 t S c C D hC hD hCD E rows hrows W V K K₀ H₀ A₀ B₀ hK hK₀ hH₀ hA₀ hB₀,
    norm_mul]
  convert mul_le_mul_of_nonneg_left hh (norm_nonneg (scalar C D hC E K A₀ B₀)) using 1 <;> ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule1554

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourcePool
Source SHA256: abe51fccbeed4ddf7f82ae38abc09b0f93a2127646ea643aa4827a79b0685105
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1555


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceRow CenteredMomentFirstSectors CenteredMomentFirstSectorEnergy
open CenteredMomentFirstSectorTransform CenteredMomentFirstChildProfile
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeExpansion RayFourExpansion
local notation "O"=>ActualEisensteinCubic.O

theorem original_pool_restriction (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (S:Finset (Ideal O))(f:Ideal O→Ideal O→ℂ):
    (∑a∈residualPool C hC (supportedColumns S),∑b∈residualPool D hD (supportedColumns S),
      if IsCoprime C a ∧ IsCoprime C b ∧ IsCoprime a b then f a b else 0)=
    ∑a:columns C C hC S,∑b:columns C D hD S,
      if IsCoprime (a:Ideal O) (b:Ideal O) then f a b else 0:=by
  rw [Finset.sum_coe_sort (columns C C hC S)
    (fun a:Ideal O=>∑b:columns C D hD S,if IsCoprime a (b:Ideal O) then f a b else 0)]
  unfold columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hca:IsCoprime C a
  · simp only [hca,true_and,ite_true]
    rw [Finset.sum_coe_sort _ (fun b:Ideal O=>if IsCoprime a b then f a b else 0),Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hcb:IsCoprime C b <;> simp [hcb]
  · simp [hca]

theorem actual_child_family (η:Character)(m:O)(hm:m≠0)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (ξ₁ ξ₂:RayCharacter):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let r:=activeConductor C D;
    let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D);
    let M:=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*r};
    ∃τ₁ τ₂:Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀S:Finset (Ideal O),∀c:Ideal O→ℂ,∀t:ℝ,∀L:Ideal O,∀a:columns C C hC.1 S,
        divisorCoefficient L (element C C hC.1 S)
          (fun a=>coefficient η m 1 t c C a*leftCoefficient e r ρ (element C C hC.1 S a)) ξ₁ a=
          (if L∣(a:Ideal O) then c (C*a) else 0)*heightCoeff τ₁ t a) ∧
      (∀S:Finset (Ideal O),∀c:Ideal O→ℂ,∀t:ℝ,∀L:Ideal O,∀b:columns C D hD.1 S,
        divisorCoefficient L (element C D hD.1 S)
          (fun b=>coefficient η m 1 t c D b*rightCoefficient e r ρ (element C D hD.1 S b)) ξ₂ b=
          (if L∣(b:Ideal O) then c (D*b) else 0)*heightCoeff τ₂ t b):=by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩:=exists_first_divisor_pair η m hm hmLam hm2 C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_,?_⟩
  · intro S c t L a
    exact h₁ L a (column_supported C C hC.1 S a) (fun I=>c (C*I)) t
  · intro S c t L b
    exact h₂ L b (column_supported C D hD.1 S b) (fun I=>c (D*I)) t

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule1555

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceNormalization
Source SHA256: f361d4f71f1a04447f0e8ab8bb0b704bc782f801d9d7c3dea8a1bc10b1bc5385
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1556


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentSupportedCorrelation CenteredMomentCommonSupport CenteredMomentActive
open CenteredMomentFirstReduced
local notation "O"=>ActualEisensteinCubic.O

theorem scalar_norm (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (K A₀ B₀:ℝ)(hK:0<K)(_hA₀:0<A₀)(_hB₀:0<B₀):
    ‖scalar C D hC E K A₀ B₀‖=
      ‖inactiveWeight C D E‖*K/
        (‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
          ‖eisEmbedding (activeConductor C D)‖*Real.sqrt A₀*Real.sqrt B₀):=by
  have he:0<‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖:=
    norm_pos_iff.mpr (eisEmbedding_ne_zero
      (supported_element_ne_zero _ (subsetGenerator_supported C D hC E)))
  have hk:0<K/‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2:=
    div_pos hK (sq_pos_of_pos he)
  unfold scalar
  rw [norm_mul,norm_div,norm_mul,
    norm_canonicalNormalizedGauss (activePrime C D) (activeCoprime C D) (activeGood C D hC)
      (fun P=>common_odd C D hC P.val) (activeExponent C D)
      (netExponent_ne_zero _ _ _) (fun P=>netExponent_lt_six _ _)]
  simp only [mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hk,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule1556

/-! Original module: OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
Source SHA256: 0ba89957b692e5fce86ab510560866efeba801acbaf5a516c7209cf46d95087c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1557


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem finite_weighted_integral_energy {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (w : ℝ → ℝ) (hw : ∀ t,0<w t)
    (E : ℝ) (hE : 0≤E) (hb : Integrable (fun t => w t*‖b t‖))
    (hφ : ∀ k,Integrable (fun t => b t*φ k t))
    (hbound : ∀ t,(∑ k,‖φ k t‖^2)≤E*(w t)^2) :
    (∑ k,‖∫ t : ℝ,b t*φ k t‖^2)≤E*(∫ t : ℝ,w t*‖b t‖)^2 := by
  have hn (t : ℝ) : (w t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw t).ne'
  have hnorm (t : ℝ) : ‖(w t:ℂ)‖=w t := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hw t)]
  have he (k : κ) (t : ℝ) : ((w t:ℂ)*b t)*(φ k t/(w t:ℂ))=b t*φ k t := by
    field_simp [hn t]
  have hh := CompletedGauss.finite_integral_energy_bound
    (fun t => (w t:ℂ)*b t) (fun k t => φ k t/(w t:ℂ)) E hE
    (by simpa only [norm_mul,hnorm] using hb)
    (fun k => by simpa only [he] using hφ k) (fun t => by
      simp only [norm_div,hnorm,div_pow,← Finset.sum_div]
      exact (div_le_iff₀ (sq_pos_of_pos (hw t))).mpr (hbound t))
  simpa only [he,norm_mul,hnorm] using hh

theorem gauss_column_integrable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (gaussRow (a i) (ha i) z)
  convert integrable_finsetSum S (fun i _ => hi i) using 1
  funext w
  simp only [gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem window_energy_from_shifted {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X) (rows : Finset O)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(∑ z∈rows,‖gaussPolynomial S a ha
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)≤
      E*(1+‖w‖)^(2*J)) :
    (∑ z∈rows,‖gaussPolynomial S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z‖^2)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let φ := fun z : rows => fun w : ℝ => logPhase (θ-w) (Real.log X)*
    gaussPolynomial S a ha (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z
  have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
    simpa only [φ,mul_assoc] using gauss_column_integrable S a ha β τ t θ X hX V hVc hVs z
  have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
    simp only [φ,norm_mul,logPhase_norm,one_mul,← pow_mul]
    rw [Finset.sum_coe_sort rows (fun z : O => ‖gaussPolynomial S a ha
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
    simpa only [Nat.mul_comm] using henergy w
  have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
    (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE
    (columnDensity_moments V hVc hVs J) hi hb
  calc
    _ = ∑ z : rows,‖∫ w : ℝ,columnDensity V hVc hVs w*φ z w‖^2 := by
      rw [← Finset.sum_coe_sort rows]
      apply Finset.sum_congr rfl
      intro z hz
      rw [gauss_column_integral S a ha β τ t θ X hX V hVc hVs z]
      simp only [φ,mul_assoc]
    _ ≤ _ := hh

def heightCost (t θ : ℝ) : ℝ := (1+‖t‖+2*Real.pi*‖θ‖)*(1+2*Real.pi)

theorem heightCost_pos (t θ : ℝ) : 0<heightCost t θ := by
  unfold heightCost
  positivity

theorem norm_height_shift (t θ w : ℝ) :
    1+‖t+2*Real.pi*(w-θ)‖≤heightCost t θ*(1+‖w‖) := by
  have hπ : 0≤2*Real.pi := by positivity
  have hn := norm_add_le t (2*Real.pi*(w-θ))
  rw [norm_mul,Real.norm_of_nonneg hπ] at hn
  have hs := norm_sub_le w θ
  have hr : 1+‖t+2*Real.pi*(w-θ)‖≤1+‖t‖+2*Real.pi*‖θ‖+2*Real.pi*‖w‖ := by
    nlinarith
  have hb : 1≤1+‖t‖+2*Real.pi*‖θ‖ := by
    nlinarith [norm_nonneg t,mul_nonneg hπ (norm_nonneg θ)]
  have hw : 0≤2*Real.pi*‖w‖ := by positivity
  calc
    _ ≤ (1+‖t‖+2*Real.pi*‖θ‖)*(1+2*Real.pi*‖w‖) := by nlinarith
    _ ≤ _ := by
      unfold heightCost
      rw [mul_assoc (1+‖t‖+2*Real.pi*‖θ‖) (1+2*Real.pi) (1+‖w‖)]
      apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hb)
      nlinarith [norm_nonneg w,Real.pi_pos]

theorem window_energy_from_height {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X) (rows : Finset O)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(∑ z∈rows,‖gaussPolynomial S a ha
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) z‖^2)≤E*(1+‖v‖)^(2*J)) :
    (∑ z∈rows,‖gaussPolynomial S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z‖^2)≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply window_energy_from_shifted V hVc hVs J S a ha β τ t θ X hX rows
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end SevenEighths.CenteredMomentHeckeWindowEnergy

end

end OAI
end OAIOriginalModule1557

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ClippedEnergy
Source SHA256: 356474327f3fe191325d71907d97eb5eff25e2592a13d85257cde62342f8f30a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1558



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns InverseInitialOverlapFourier CompletedGauss
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem normalized_energy_vector
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(hD:∀f∈labels,0≤D f)
    (W:ℝ→ℂ)(X Z F:ℝ):
    (∑v:labels×rows,‖(Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a W X‖^2)=
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F:=by
  unfold normalizedColumnEnergy
  rw [Fintype.sum_prod_type,←Finset.sum_coe_sort labels]
  apply Finset.sum_congr rfl
  intro f hf
  rw [←Finset.sum_coe_sort rows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [mul_assoc,norm_mul,mul_pow,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hD f f.property)]

theorem canonical_clipped_energy
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(hD:∀f∈labels,0≤D f)
    (W:ℝ→ℂ)(lo hi:ℝ)(hlo:0<lo)(hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (wFresh:ℝ→ℂ)(c θ X Z F E:ℝ)(J:ℕ)(hc:0<c)(hX:0<X)(hE:0≤E)
    (hw:∀y,0<y→wFresh y*W (c*y)=W (c*y))
    (he:∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest wFresh s) X Z F≤E*(1+‖s‖)^(2*J)):
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest W c θ) X Z F≤
      E*(1+‖θ‖)^(2*J)*(∫t:ℝ,(1+‖t‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) t‖)^2:=by
  let g:=CubicReflectionKernel.logSchwartz W lo hi hlo hs hW
  let b:=density g (Real.log c)
  let phi:labels×rows→ℝ→ℂ:=fun v t=>(Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a
      (childLogTest wFresh (θ+t)) X
  have hint(v:labels×rows):Integrable (fun t:ℝ=>b t*phi v t):=by
    convert (canonical_clipped_mode_integrable p hp hcop hg hpr pool Ψ m (primaryGenerator v.1) v.2
      slots lists a g wFresh c θ X).const_mul ((Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)) using 1
    funext t
    dsimp [b,phi]
    ring
  have hbound(t:ℝ):(∑v:labels×rows,‖phi v t‖^2)≤
      (E*(1+‖θ‖)^(2*J))*((1+‖t‖)^J)^2:=by
    dsimp only [phi]
    rw [normalized_energy_vector p hp hcop hg pool Ψ m slots lists a labels rows D hD]
    apply (he (θ+t)).trans
    have hb:1+‖θ+t‖≤(1+‖θ‖)*(1+‖t‖):=by
      have hh:=norm_add_le θ t
      nlinarith [mul_nonneg (norm_nonneg θ) (norm_nonneg t)]
    calc
      _≤E*((1+‖θ‖)*(1+‖t‖))^(2*J):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) hE
      _= _:=by rw [mul_pow,pow_mul];ring
  have hden:Integrable (fun t:ℝ=>(1+‖t‖)^J*‖b t‖):=by
    simpa only [b,density_norm] using AnalyticBridge.schwartz_fourier_one_plus_integrable g J
  have hh:=CenteredMomentHeckeWindowEnergy.finite_weighted_integral_energy b phi
    (fun t:ℝ=>(1+‖t‖)^J) (by intro t;positivity)
    (E*(1+‖θ‖)^(2*J)) (by positivity) hden hint hbound
  have heq(v:labels×rows): (∫t:ℝ,b t*phi v t)=
      (Real.sqrt (D v.1):ℂ)*((Z^(-F/2):ℝ):ℂ)*
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator v.1) v.2 slots lists a
        (clippedTest W c θ) X:=by
    rw [canonical_clipped_fourier p hp hcop hg hpr pool Ψ m (primaryGenerator v.1) v.2
      slots lists a W lo hi hlo hs hW wFresh c θ X hc hX hw,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [b,phi,g]
    ring
  simp_rw [heq] at hh
  rw [normalized_energy_vector p hp hcop hg pool Ψ m slots lists a labels rows D hD] at hh
  simpa only [b,density_norm,g] using hh

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1558

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ClippedUniform
Source SHA256: d6914ab37c5d60fedb3082ce5a3fbde91d4c035b52e18e74ba70bf83471645f7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1559


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem canonical_clipped_uniform
    (W:ℝ→ℂ)(lo hi b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(_hD:∀f∈labels,0≤D f)
      (c θ X Z F E:ℝ),1≤c→c≤b→0<X→0≤E→
      (∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) X Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (clippedTest W c θ) X Z F≤C*E*(1+‖θ‖)^(2*J):=by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,hagree⟩:=clipped_fixed_window W lo hi b hlo hb hs
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  let M:=(∫t:ℝ,(1+‖t‖)^J*‖(𝓕 (CubicReflectionKernel.logSchwartz W lo hi hlo hs hW)) t‖)^2
  refine ⟨M+1,by dsimp [M];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD c θ X Z F E hc1 hcb hX hE he
  have hh:=canonical_clipped_energy p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
    W lo hi hlo hs hW wFresh c θ X Z F E J (zero_lt_one.trans_le hc1) hX hE
    (hagree c hc1 hcb) he
  apply hh.trans
  change E*(1+‖θ‖)^(2*J)*M≤(M+1)*E*(1+‖θ‖)^(2*J)
  have hn:0≤E*(1+‖θ‖)^(2*J):=by positivity
  nlinarith

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1559

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ClippedChild
Source SHA256: d0e52b05cce323949b3d3d1c588f33f5b7a516cb99df6d10e7f38fbd4f12bf5d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1560




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.InverseMoment
open InverseInitialClippedColumns JointLogSeparation InverseAmbientProfileTower
open InverseSecondSourceBlocks
local notation "O"=>ActualEisensteinCubic.O

def secondChildHeight (right:Bool)(t:Ambient (Fin 6)):ℝ :=
  if right then profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2 5
  else -profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2 4

theorem second_child_height_budget (J:ℕ)(right:Bool)(t:Ambient (Fin 6)):
    (1+‖secondChildHeight right t‖)^J≤tripleHeight J t.1*coordinateHeight J t.2:=by
  cases right
  · have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedLeft 4 t‖) (inheritedLeft_bound 4 t) J
    rw [←ambientWeight_eq_pow] at h
    simpa only [secondChildHeight,Bool.false_eq_true,ite_false,norm_neg,
      second_inherited_left_eq,ambientWeight,tripleHeight,coordinateHeight] using h
  · have h:=pow_le_pow_left₀ (by positivity : 0≤1+‖inheritedRight 5 t‖) (inheritedRight_bound 5 t) J
    rw [←ambientWeight_eq_pow] at h
    simpa only [secondChildHeight,ite_true,second_inherited_right_eq,norm_neg,
      ambientWeight,tripleHeight,coordinateHeight] using h

theorem canonical_actual_child_uniform
    (W:ℝ→ℂ)(lo hi b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hs:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W):
    ∃(wFresh:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (wFresh:ℝ→ℂ) ∧
      tsupport (wFresh:ℝ→ℂ)⊆Set.Icc af bf ∧
      ∀J:ℕ,∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(rows:Finset O)(D:Ideal O→ℝ)(_hD:∀f∈labels,0≤D f)
      (Z X F E:ℝ)(d:BlockIndex)(right:Bool)(t:Ambient (Fin 6)),
      1<Z→0<X→scales d 0*scales d 2≤b*X→0≤E→
      (∀s,normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (childLogTest wFresh s) (Z^(max 0 (secondCellColumnExponent Z X d))) Z F≤E*(1+‖s‖)^(2*J))→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
        (clippedTest W (Z^(max 0 (secondCellColumnExponent Z X d)-secondCellColumnExponent Z X d))
          (secondChildHeight right t)) (Z^(max 0 (secondCellColumnExponent Z X d))) Z F≤
        C*E*(tripleHeight (2*J) t.1*coordinateHeight (2*J) t.2):=by
  obtain ⟨wFresh,af,bf,haf,hab,hc,hsf,he⟩:=canonical_clipped_uniform W lo hi b hlo hb hs hW
  refine ⟨wFresh,af,bf,haf,hab,hc,hsf,?_⟩
  intro J
  obtain ⟨C,hC,hbound⟩:=he J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr pool Ψ m slots lists a labels rows D hD Z X F E d right t hZ hX hgeom hE hmoment
  obtain ⟨hc1,hcb⟩:=second_cell_clipping_ratio Z X b d hZ hX hb hgeom
  have hz:0<Z:=zero_lt_one.trans hZ
  exact (hbound p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
    _ (secondChildHeight right t) _ Z F E hc1 hcb (Real.rpow_pos_of_pos hz _) hE hmoment).trans
      (mul_le_mul_of_nonneg_left (second_child_height_budget (2*J) right t) (mul_nonneg hC.le hE))

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1560

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFixedChildStep
Source SHA256: f182075056626fb227dfd9b301de44e2c7ddc53d6de94b38a796dd0ec6dfb81f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1561



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentGlobalPriorityTail
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_fixed_child_step
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (bcap:ℝ)(hbcap:1≤bcap)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → b≤bcap → (slots:Set σ).PairwiseDisjoint lists→slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ s:ℝ,∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (childLogTest ω₁ s)
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(1+‖s‖)^(2*J)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ s:ℝ,∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (childLogTest ω₂ s)
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(1+‖s‖)^(2*J))) →
      Jo≤Jmax→0≤ell+eta→0≤Bfirst→0≤j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤pi+eta/2→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(tcount+eta))→
      1≤Y→1≤X*Real.exp window→Y≤Z^Lcap→Y⁻¹≤Z^Lcap→X*Real.exp window≤Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤Lcap→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^Lcap)→
      (∀G E,0≤cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*J))*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨v₁,v₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hstep⟩:=
    global_priority_filtered_physical_step (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      window Lcap tau saving hhi hLcap htau Jmax dsmall hdsmall caps hcaps B₀ hB₀ K εmass hεmass
  obtain ⟨w₁,a₁,b₁,ha₁,hab₁,hw₁,hsw₁,hfixed₁⟩:=canonical_actual_child_uniform
    v₁ af bf bcap haf hbcap ((subset_tsupport _).trans hs₁) (v₁.smooth ⊤)
  obtain ⟨w₂,a₂,b₂,ha₂,hab₂,hw₂,hsw₂,hfixed₂⟩:=canonical_actual_child_uniform
    v₂ af bf bcap haf hbcap ((subset_tsupport _).trans hs₂) (v₂.smooth ⊤)
  refine ⟨w₁,w₂,min a₁ a₂,max b₁ b₂,lt_min ha₁ ha₂,
    (min_le_left _ _).trans (hab₁.trans (le_max_left _ _)),hw₁,hw₂,
    hsw₁.trans (Set.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _)),
    hsw₂.trans (Set.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)),?_⟩
  intro J
  obtain ⟨C₁,hC₁,he₁⟩:=hfixed₁ J
  obtain ⟨C₂,hC₂,he₂⟩:=hfixed₂ J
  obtain ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,he⟩:=hstep (2*J)
  let Cmax:=max C₁ C₂
  have hmax:0≤Cmax:=hC₁.le.trans (le_max_left _ _)
  refine ⟨C*Cmax,Cbin,Czero,Ctail,mul_nonneg hC hmax,hCbin,hCzero,hCtail,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hbcap' hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hout:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels (Cmax*A)
    hhib hdisj hslots (mul_nonneg hmax hA)
  have hnew:
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*(Cmax*A)*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*J))*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
    apply hout
    · intro ray core assigned hassigned
      obtain ⟨haa,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hb₁,hb₂,hactive',hj',hq,hΨ,
        hal,har,hlabels,ho,hsl,hsr,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned hassigned
      refine ⟨haa,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hb₁,hb₂,hactive',hj',hq,hΨ,
        hal,har,hlabels,ho,hsl,hsr,mul_nonneg hmax hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,?_,?_⟩
      · intro z d hd u J₁ hJ₁ γ hγ
        have hgeomcell:=source_cell_joint_bound p hp _ (fun x hx=>(Finset.mem_erase.mp (hrows x hx)).1) b X hgeom d hd
        have hh:=he₁ p hp hcop hg hpr pool _ _ ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (fun f hf=>pow_nonneg (Nat.cast_nonneg _) _) Z X _
          (A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild)) d false u hZ hX
          (hgeomcell.trans (mul_le_mul_of_nonneg_right hbcap' hX.le)) (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
          (fun s=>hleft z d hd s J₁ hJ₁ γ hγ)
        change _≤(Cmax*A)*Z^(_)*_
        apply hh.trans
        have hH:0≤tripleHeight (2*J) u.1*coordinateHeight (2*J) u.2:=by
          unfold tripleHeight coordinateHeight
          positivity
        have hE:0≤A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild):=
          mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hE) hH using 1 ; ring
      · intro z d hd u J₂ hJ₂ γ hγ
        have hgeomcell:=source_cell_joint_bound p hp _ (fun x hx=>(Finset.mem_erase.mp (hrows x hx)).1) b X hgeom d hd
        have hh:=he₂ p hp hcop hg hpr pool _ _ ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (fun f hf=>pow_nonneg (Nat.cast_nonneg _) _) Z X _
          (A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild)) d true u hZ hX
          (hgeomcell.trans (mul_le_mul_of_nonneg_right hbcap' hX.le)) (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
          (fun s=>hright z d hd s J₂ hJ₂ γ hγ)
        change _≤(Cmax*A)*Z^(_)*_
        apply hh.trans
        have hH:0≤tripleHeight (2*J) u.1*coordinateHeight (2*J) u.2:=by
          unfold tripleHeight coordinateHeight
          positivity
        have hE:0≤A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild):=
          mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hE) hH using 1 ; ring
    all_goals assumption
  convert hnew using 1 ; ring
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1561

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFixedChildStepUniform
Source SHA256: e775f3d67a6de0ccbca51d227b9408dd9d4b00c8c0d49d5d115f5c84e79fd2f0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1562





namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentGlobalPriorityTail
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
theorem global_priority_fixed_child_step_uniform_types
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (window Lcap tau saving:ℝ)(hhi:hi≤Real.exp window)(hLcap:0≤Lcap)(htau:0<tau)
    (bcap:ℝ)(hbcap:1≤bcap)
    (Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin Czero Ctail : ℝ,0 ≤ C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      hi≤b → b≤bcap → (slots:Set σ).PairwiseDisjoint lists→slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=InverseMomentGlobalRetainedGates.geometrySource p (unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff)) b X;
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ s:ℝ,∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (childLogTest ω₁ s)
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(1+‖s‖)^(2*J)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ s:ℝ,∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (childLogTest ω₂ s)
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(1+‖s‖)^(2*J))) →
      Jo≤Jmax→0≤ell+eta→0≤Bfirst→0≤j→
      εmass*(r-Acol-Bfirst-tcount)+7*eta/2+dsmall*(3*ell+Bfirst+tcount+5*eta)+
        2*εmass*(2*ell+Bfirst+tcount+4*eta)≤pi+eta/2→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(tcount+eta))→
      1≤Y→1≤X*Real.exp window→Y≤Z^Lcap→Y⁻¹≤Z^Lcap→X*Real.exp window≤Z^Lcap→
      firstKappa M r ell V delta Acol Bfirst Ractive+(9/2:ℝ)*eta≤Lcap→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^Lcap)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (∏i∈cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^Lcap)→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^Lcap)→
      (∀G E,0≤cutoff G E)→
      (∀x∈original,∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p (parent p x)) G E.val
          (X*Real.exp window) Y (Z^tau)≤cutoff G E.val)→
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*J))*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
  obtain ⟨v₁,v₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hstep⟩:=
    global_priority_filtered_physical_step_uniform_types  om lo hi hlo hsupport negative
      window Lcap tau saving hhi hLcap htau Jmax dsmall hdsmall caps hcaps B₀ hB₀ K εmass hεmass
  obtain ⟨w₁,a₁,b₁,ha₁,hab₁,hw₁,hsw₁,hfixed₁⟩:=canonical_actual_child_uniform
    v₁ af bf bcap haf hbcap ((subset_tsupport _).trans hs₁) (v₁.smooth ⊤)
  obtain ⟨w₂,a₂,b₂,ha₂,hab₂,hw₂,hsw₂,hfixed₂⟩:=canonical_actual_child_uniform
    v₂ af bf bcap haf hbcap ((subset_tsupport _).trans hs₂) (v₂.smooth ⊤)
  refine ⟨w₁,w₂,min a₁ a₂,max b₁ b₂,lt_min ha₁ ha₂,
    (min_le_left _ _).trans (hab₁.trans (le_max_left _ _)),hw₁,hw₂,
    hsw₁.trans (Set.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _)),
    hsw₂.trans (Set.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)),?_⟩
  intro J
  obtain ⟨C₁,hC₁,he₁⟩:=hfixed₁ J
  obtain ⟨C₂,hC₂,he₂⟩:=hfixed₂ J
  obtain ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,he⟩:=hstep (2*J)
  let Cmax:=max C₁ C₂
  have hmax:0≤Cmax:=hC₁.le.trans (le_max_left _ _)
  refine ⟨C*Cmax,Cbin,Czero,Ctail,mul_nonneg hC hmax,hCbin,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels A
    hhib hbcap' hdisj hslots hA hdata hJo hell hBfirst hj hcost hcube₁ hcube₂ hactive hcommon hquotient
    hYone hscale hy hyi hx hPcap hcubeCap₁ hcubeCap₂ hactiveCap hcommonCap hquotCap hrad hcutoff
  have hout:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hw Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst pi b ρ t labels (Cmax*A)
    hhib hdisj hslots (mul_nonneg hmax hA)
  have hnew:
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y ≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*(Cmax*A)*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*J))*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)+Ctail*Z^(-saving) := by
    apply hout
    · intro ray core assigned hassigned
      obtain ⟨haa,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hb₁,hb₂,hactive',hj',hq,hΨ,
        hal,har,hlabels,ho,hsl,hsr,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned hassigned
      refine ⟨haa,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hb₁,hb₂,hactive',hj',hq,hΨ,
        hal,har,hlabels,ho,hsl,hsr,mul_nonneg hmax hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,?_,?_⟩
      · intro z d hd u J₁ hJ₁ γ hγ
        have hgeomcell:=source_cell_joint_bound p hp _ (fun x hx=>(Finset.mem_erase.mp (hrows x hx)).1) b X hgeom d hd
        have hh:=he₁ p hp hcop hg hpr pool _ _ ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (fun f hf=>pow_nonneg (Nat.cast_nonneg _) _) Z X _
          (A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild)) d false u hZ hX
          (hgeomcell.trans (mul_le_mul_of_nonneg_right hbcap' hX.le)) (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
          (fun s=>hleft z d hd s J₁ hJ₁ γ hγ)
        change _≤(Cmax*A)*Z^(_)*_
        apply hh.trans
        have hH:0≤tripleHeight (2*J) u.1*coordinateHeight (2*J) u.2:=by
          unfold tripleHeight coordinateHeight
          positivity
        have hE:0≤A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild):=
          mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hE) hH using 1 ; ring
      · intro z d hd u J₂ hJ₂ γ hγ
        have hgeomcell:=source_cell_joint_bound p hp _ (fun x hx=>(Finset.mem_erase.mp (hrows x hx)).1) b X hgeom d hd
        have hh:=he₂ p hp hcop hg hpr pool _ _ ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (fun f hf=>pow_nonneg (Nat.cast_nonneg _) _) Z X _
          (A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild)) d true u hZ hX
          (hgeomcell.trans (mul_le_mul_of_nonneg_right hbcap' hX.le)) (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _))
          (fun s=>hright z d hd s J₂ hJ₂ γ hγ)
        change _≤(Cmax*A)*Z^(_)*_
        apply hh.trans
        have hH:0≤tripleHeight (2*J) u.1*coordinateHeight (2*J) u.2:=by
          unfold tripleHeight coordinateHeight
          positivity
        have hE:0≤A*Z^(max 0 (secondCellColumnExponent Z X d)+Vlabel d+εchild):=
          mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        convert mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hE) hH using 1 ; ring
    all_goals assumption
  convert hnew using 1 ; ring
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1562

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStep
Source SHA256: 4c1bcc504450f19010aa131f90697d4fe3d8ed8ca33d21ceee5bffe5206d32dc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1563



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondFibers InverseInitialClippedColumns RayFourExpansion FirstCauchyArithmetic
open InverseWholePriorityRetainedSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def ChildBounds {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (Z M r ell V eta tau window b epschild A : ℝ) (K degree : ℕ) : Prop :=
  ∀(ray : RayCharacter×RayCharacter)(core : FirstCoreIndex)(assigned : Finset σ),assigned⊆slots→
  let S := source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀ := firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  (∀z : SecondRayIndex,∀d∈keys p S,∀s : ℝ,∀J₁∈(slots\assigned).powerset,∀γ∈actualSecondTriples p 1 1 (cell p S d),
    normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
      (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
      ((actualCellLabels p S d).filter Squarefree)
      (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
      (secondLabelWeight K) (childLogTest ω₁ s)
      (Z^(max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
      (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d)≤
      A*Z^(actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d+epschild)*
        (1+‖s‖)^(2*degree)) ∧
  (∀z : SecondRayIndex,∀d∈keys p S,∀s : ℝ,∀J₂∈(slots\assigned).powerset,∀γ∈actualSecondTriples p 1 1 (cell p S d),
    normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
      (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
      ((actualCellLabels p S d).filter Squarefree)
      (nonzeroChildFrequencyBall 1 (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d))
      (secondLabelWeight K) (childLogTest ω₂ s)
      (Z^(max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))) Z
      (actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d)≤
      A*Z^(actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d+epschild)*
        (1+‖s‖)^(2*degree))

theorem actual_label_cell_step (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo)
    (hsupport : Function.support om⊆Set.Icc lo hi) (negative : Bool)
    (window Ltail Lgate tau saving : ℝ) (hhi : hi≤Real.exp window)
    (hLtail : 0≤Ltail) (hLgate : 0≤Lgate) (htau : 0<tau)
    (bcap : ℝ) (hbcap : 1≤bcap) (dsmall : ℝ) (hdsmall : 0<dsmall)
    (B₀ : Fin 6→ℝ) (hB₀ : ∀i,0≤B₀ i) (K : ℕ) (epsmass : ℝ) (hepsmass : 0<epsmass) :
    ∃(ω₁ ω₂ : 𝓢(ℝ,ℂ))(loFresh hiFresh : ℝ),0<loFresh ∧ loFresh≤hiFresh ∧
      HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
    ∀degree : ℕ,∃C Cbin Czero Ctail : ℝ,0≤C ∧ 0≤Cbin ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ : Type}[DecidableEq ι][DecidableEq σ](p : ι→O)(hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (hinj : Function.Injective (fun i=>Ideal.span {p i})) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι)(Q : Finset (ι→₀ℕ))(k : SourceIndex)(l j : ℕ)
      (Ψ : O→*ℂ)(m : O)(slots : Finset σ)(lists : σ→Finset ι)(a : σ→ι→ℂ)
      (Z M r ell V eta pi b Lcol LY epschild A t : ℝ)(ρ : Fin 6→ℝ),
      2≤Z→0≤eta→2≤Z^eta→0≤ell+eta→
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (slots:Set σ).PairwiseDisjoint lists→slots.card≤K→(∀i∈slots,∀q∈lists i,‖a i q‖≤1)→
      (∀u,‖Ψ u‖≤1)→(∀i,|ρ i|≤B₀ i)→hi≤b→b≤bcap→1≤b→b≤Z^(6*eta)→
      Real.exp window≤Z^(4*eta)→0≤A→
      columnScale Z r k l negative*Real.exp window≤Z^Lcol→
      (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY→
      b*columnScale Z r k l negative≤Z^Lgate→exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lgate→
      epsmass*(ell+exponent Z (k 4)/2+exponent Z l+Lgate+11*eta/2)≤pi→
      epsmass*(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)+7*eta/2+
        dsmall*(3*ell+exponent Z (k 2)+exponent Z l+5*eta)+
        2*epsmass*(2*ell+exponent Z (k 2)+exponent Z l+4*eta)≤pi+eta/2→
      1≤firstCellRadius Z M r ell V eta tau k j→1≤columnScale Z r k l negative*Real.exp window→
      firstCellRadius Z M r ell V eta tau k j≤Z^Ltail→
      (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^Ltail→
      columnScale Z r k l negative*Real.exp window≤Z^Ltail→
      firstKappa M r ell V (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) (exponent Z (k 4))+
        (9/2:ℝ)*eta≤Ltail→
      ell+eta≤Ltail→exponent Z (k 4)+eta≤Ltail→exponent Z (k 2)+eta≤Ltail→exponent Z l+eta≤Ltail→
      ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree→
      (Z^(firstKappa M r ell V (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) (exponent Z (k 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j) (parentWeight p l)
        negative Ψ m slots lists a om (columnScale Z r k l negative) t (firstCellRadius Z M r ell V eta tau k j)≤
      Czero*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*degree))*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+epschild)+Ctail*Z^(-saving) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,hstep⟩ := global_priority_fixed_child_step_uniform_types
    om lo hi hlo hsupport negative window Ltail tau saving hhi hLtail htau bcap hbcap
    0 dsmall hdsmall (fun _=>Lgate) (fun _=>hLgate) B₀ hB₀ K epsmass hepsmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree
  obtain ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,he⟩ := hstep degree
  refine ⟨C,Cbin,Czero,Ctail,hC,hCbin,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q k l j Ψ m slots lists a
    Z M r ell V eta pi b Lcol LY epschild A t ρ hZ2 heta hbin hell hQ hdisj hslots ha hΨ hρ hhib hbb hb1 hb6
    hwindow hA hcol hYi hgeom hphysical hbudget hcost hY1 hX1 hYcap hYicap hXcap hPcap hellcap hactivecap hcommoncap hquotcap hchild
  have hZ : 1<Z := by linarith
  have hz : 0<Z := zero_lt_one.trans hZ
  have hX : 0<columnScale Z r k l negative := Real.rpow_pos_of_pos hz _
  have hY : 0<firstCellRadius Z M r ell V eta tau k j := Real.rpow_pos_of_pos hz _
  have hparent := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  have htail := parent_tail_caps p hp pool Q k l j Z ell eta Ltail hZ heta hbin hLtail hQ
    hellcap hactivecap hcommoncap hquotcap
  apply he p hp hcop hg hpr hinj hc (extra negative) pool
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    (label_parent_valid p pool Q k l j) (fun y hy=>extra_subset negative y.cube)
    (parentWeight p l) (fun y hy=>parentWeight_norm p l y) Ψ m slots lists a
    (secondCutoff p Z M r ell V eta tau window k l j negative)
    (firstCellRadius Z M r ell V eta tau k j)
    (fun _ d=>actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
    (eta*Real.log Z) Z (columnScale Z r k l negative) epschild
    (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta)
    ell (exponent Z (k 4)) (exponent Z j) (exponent Z l) eta M r V
    (exponent Z (k 3)) (columnA Z k negative) (exponent Z (k 2)) pi b ρ t
    (fun assigned d=>actualCellLabels p (source p pool Q k l j negative assigned lists Z M r ell V eta tau window b) d) A
    hhib hbb hdisj hslots hA
  · intro ray core assigned hassigned
    obtain ⟨_,_,hrows,_,hn,hlabels,_,hcaps,hgeometry,hmass⟩ := source_step_arithmetic p hp pool Q k l j
      negative assigned lists Z M r ell V eta tau window b Lcol LY Lgate epsmass pi
      hZ heta hbin hepsmass.le hwindow hQ hcol hYi hgeom hphysical hbudget
    have hJ : assigned.card≤K := (Finset.card_le_card hassigned).trans hslots
    have hrest : (slots\assigned).card≤K := (Finset.card_le_card Finset.sdiff_subset).trans hslots
    have hbchild := hchild ray core assigned hassigned
    refine ⟨(fun i hi q hq=>ha i (hassigned hi) q hq),hρ,mul_nonneg heta (Real.log_nonneg hZ.le),hZ,hX,hY,heta,hbin,
      hrows,(fun x hx=>(hn x hx).1),(fun x hx=>(hn x hx).2.1),(fun x hx=>(hn x hx).2.2.1),
      (fun x hx=>(hn x hx).2.2.2.2.2.1),(fun x hx=>(hn x hx).2.2.2.2.1),hΨ,
      (fun i hi q hq=>ha i (Finset.mem_sdiff.mp hi).1 q hq),
      (fun i hi q hq=>ha i (Finset.mem_sdiff.mp hi).1 q hq),
      (fun d hd x hx=>hlabels d x hx),by omega,hrest,hrest,hA,rfl,rfl,rfl,(fun _=>rfl),hZ2,hb1,hb6,
      hcaps,hgeometry,hmass,hbchild.1,hbchild.2⟩
  · exact Nat.zero_le _
  · exact hell
  · exact dyadic_exponent_nonneg Z hZ _
  · exact dyadic_exponent_nonneg Z hZ _
  · exact hcost
  · exact fun y hy=>(hparent y hy).1
  · exact fun y hy=>(hparent y hy).2.1
  · exact fun y hy=>(hparent y hy).2.2.1
  · exact fun y hy=>(hparent y hy).2.2.2.1
  · exact fun y hy=>(hparent y hy).2.2.2.2.1
  · exact hY1
  · exact hX1
  · exact hYcap
  · exact hYicap
  · exact hXcap
  · exact hPcap
  · exact fun y hy=>(htail y hy).1
  · exact fun y hy=>(htail y hy).2.1
  · exact fun y hy=>(htail y hy).2.2.1
  · exact fun y hy=>(htail y hy).2.2.2.1
  · exact fun y hy=>(htail y hy).2.2.2.2
  · exact fun G E=>secondCutoff_nonneg p Z M r ell V eta tau window k l j negative hz G E
  · exact fun y hy G hG E=>secondCutoff_dominates p hp pool Q k l j negative Z M r ell V eta tau window hZ hbin y hy G E.val

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end OAIOriginalModule1563

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLowerMoments
Source SHA256: 0765eab6c717bd7f07edb71ec69b9fa6861bb749ec7a90e055102a400cdf06e5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1564



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialClippedColumns InverseSecondFibers InverseSecondSourceBlocks
open CanonicalCoefficientClass InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def CanonicalLowerMoments (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ):Prop :=
  ∀(Ψ:O→*ℂ),IsBaseRayTwist base Ψ→∀(m:O),m≠0→∀N V M Qwidth:ℝ,
    0≤N→0≤V→0≤M→0≤Qwidth→M<Mmax→N+V≤Fcap→
    CanonicalMargins (N+V) M Qwidth z c→
    ‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Qwidth→
    ∀(subslots:Finset σ),subslots⊆slots→∀labels:Finset (Ideal O),
      (∀I∈labels,Admissible I ∧ (Ideal.absNorm I:ℝ)≤Z^V)→∀s:ℝ,
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels
      (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest W s) (Z^N) Z (N+V)≤
      A*Z^(N+V+eps)*(1+‖s‖)^(2*degree)

include hp in
theorem canonical_lower_moments_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A:ℝ)(K degree:ℕ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hd:0<cutoff)(hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ:∀v∈Q,‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (h₁:CanonicalLowerMoments p hp hcop hg pool base slots lists a ω₁ Z M (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree)
    (h₂:CanonicalLowerMoments p hp hcop hg pool base slots lists a ω₂ Z M (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  intro ray core assigned hass
  let S:=source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  have hbase:IsBaseRayTwist base Ψ₀:=hΨ.firstCore _ _ _
  have hstate:=source_state_bounds p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b cutoff
    hZ heta hbin hell hV hb hbt hwindow hterminal hsmall hQ
  have hmargin:=source_child_margins p hp hpr pool Q k l j negative assigned lists Z M r ell V eta tau window b
    m hm Qwidth z c hZ heta hbin hV hparent hpuncture hQ
  have hlabels:=source_labels p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b hZ heta hbin hQ
  constructor
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₁ (secondRayMinus Ψ₀ zz) (hbase.secondMinus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₂ (secondRayPlus Ψ₀ zz) (hbase.secondPlus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1564

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalRankMoments
Source SHA256: 2a6c0cca77ab991b09b82d21c678f5038b0b74c00cbd3df1139df38c66c67a47
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1565



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialClippedColumns InverseSecondFibers InverseSecondSourceBlocks
open CanonicalCoefficientClass InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def CanonicalRankMoments (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ):Prop :=
  ∀(Ψ:O→*ℂ),IsBaseRayTwist base Ψ→∀(m:O),m≠0→∀N V M Qwidth:ℝ,
    0≤N→0≤V→0≤M→0≤Qwidth→M≤Mmax→N+V≤Fcap→
    CanonicalMargins (N+V) M Qwidth z c→
    ‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Qwidth→
    ∀(subslots:Finset σ),subslots⊆slots→∀labels:Finset (Ideal O),
      (∀I∈labels,Admissible I ∧ (Ideal.absNorm I:ℝ)≤Z^V)→∀s:ℝ,
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels
      (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest W s) (Z^N) Z (N+V)≤
      A*Z^(N+V+eps)*(1+‖s‖)^(2*degree)

include hp in
theorem canonical_rank_moments_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A:ℝ)(K degree:ℕ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (_hd:0<cutoff)(hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ:∀v∈Q,‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (h₁:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₁ Z (M-3*cutoff/2) (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree)
    (h₂:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₂ Z (M-3*cutoff/2) (r+3*ell+V+15*eta) z (c-7*eta) eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  intro ray core assigned hass
  let S:=source p pool Q k l j negative assigned lists Z M r ell V eta tau window b
  let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
  have hbase:IsBaseRayTwist base Ψ₀:=hΨ.firstCore _ _ _
  have hstate:=source_state_bounds p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b cutoff
    hZ heta hbin hell hV hb hbt hwindow hterminal hsmall hQ
  have hmargin:=source_child_margins p hp hpr pool Q k l j negative assigned lists Z M r ell V eta tau window b
    m hm Qwidth z c hZ heta hbin hV hparent hpuncture hQ
  have hlabels:=source_labels p hp pool Q k l j negative assigned lists Z M r ell V eta tau window b hZ heta hbin hQ
  constructor
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₁ (secondRayMinus Ψ₀ zz) (hbase.secondMinus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩
  · intro zz d hdcell s J hJ γ hγ
    have st:=hstate d hdcell
    have mg:=hmargin d γ hγ
    apply h₂ (secondRayPlus Ψ₀ zz) (hbase.secondPlus zz) (actualSecondInheritedRadicalPuncture m γ) mg.1
      (max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d))
      (actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)
      (actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d)
      (actualSecondPunctureWidth Z m γ) st.1 st.2.1 st.2.2.2.1 mg.2.1 (by linarith [st.2.2.2.2]) st.2.2.1 mg.2.2.2 mg.2.2.1
      ((slots\assigned)\J) (Finset.sdiff_subset.trans Finset.sdiff_subset)
      ((actualCellLabels p S d).filter Squarefree) ?_ s
    intro I hI
    exact ⟨actual_cell_labels_admissible p hp hg hc S d I hI,(hlabels.2 d I hI).2.2⟩

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1565

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalRankMonotone
Source SHA256: a489c2809a516cf7f089d35b3d5c0d8e52e7135782577e5289e5d350d220ce1b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1566


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq σ] in
theorem canonical_rank_negative (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ)(hM:Mmax<0):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z Mmax Fcap z c eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc
  exfalso
  linarith

omit [DecidableEq σ] in
theorem canonical_rank_restrict (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M₁ M₂ F₁ F₂ z c₁ c₂ eps A:ℝ)(K degree:ℕ)
    (hM:M₁≤M₂)(hF:F₁≤F₂)(hc:c₂≤c₁)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₂ F₂ z c₂ eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₁ F₁ z c₁ eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  have hmarg:CanonicalMargins (N+V) M Qwidth z c₂:=by
    unfold CanonicalMargins at *
    constructor <;> linarith [hmargin.1,hmargin.2]
  exact h Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ (hMc.trans hM) (hFc.trans hF) hmarg hnorm ss hss labels hlabels s

omit [DecidableEq σ] in
theorem canonical_rank_height_constant (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps A B:ℝ)(K degree J:ℕ)
    (hZ:0<Z)(hA:0≤A)(hAB:A≤B)(hJ:degree≤J)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps B K J :=by
  intro Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  have hB:0≤B:=hA.trans hAB
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hZ.le _)
  · exact pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.mul_le_mul_left 2 hJ)
  · positivity
  · positivity

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1566

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalRankCapChildren
Source SHA256: 53b6facef29b0726ef44cbc07e9bae682009f5f55f5e1f970580cf826c3a59ea
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1567


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows InverseFirstGlobalCaps
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_rank_cap_children
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)(negative:Bool)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:𝓢(ℝ,ℂ))
    (Z M r ell V eta tau window b cutoff Qwidth z c eps A Mnext Fnext cnext:ℝ)(K degree:ℕ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hd:0<cutoff)(hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hparent:CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ:∀v∈Q,‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hMc:M-3*cutoff/2≤Mnext)(hFc:r+3*ell+V+15*eta≤Fnext)(hcc:cnext≤c-7*eta)
    (h₁:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree)
    (h₂:CanonicalRankMoments p hp hcop hg pool base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree):
    ChildBounds p hp hcop hg pool Q k l j negative Ψ m slots lists a ω₁ ω₂
      Z M r ell V eta tau window b eps A K degree :=by
  exact canonical_rank_moments_children p hp hcop hg hc hpr pool Q k l j negative base Ψ hΨ m hm
    slots lists a ω₁ ω₂ Z M r ell V eta tau window b cutoff Qwidth z c eps A K degree
    hZ heta hbin hell hV hb hbt hwindow hd hterminal hsmall hparent hpuncture hQ
    (canonical_rank_restrict p hp hcop hg pool base slots lists a ω₁ Z _ _ _ _ z _ _ eps A K degree hMc hFc hcc h₁)
    (canonical_rank_restrict p hp hcop hg pool base slots lists a ω₂ Z _ _ _ _ z _ _ eps A K degree hMc hFc hcc h₂)

theorem canonical_depth_ceilings (n:ℕ)(cutoff Fbase cbase eta:ℝ)(M F c:ℝ)
    (hM:M≤3*(n:ℝ)*cutoff/2)(hF:F≤Fbase-15*(n:ℝ)*eta)
    (hc:cbase+7*((n:ℝ)+1)*eta≤c):
    M-3*cutoff/2≤3*((n:ℝ)-1)*cutoff/2 ∧
    F+15*eta≤Fbase-15*((n:ℝ)-1)*eta ∧
    cbase+7*(n:ℝ)*eta≤c-7*eta :=by
  constructor
  · linarith
  constructor <;> linarith

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1567

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLiveBinRank
Source SHA256: 9cb8ae76f7730676eb36f89757f698d9560dd0facc3b06ec8a29f088d3ac1ba3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1568



namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstChildWindows
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_bin_rank_children
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Z N V M cutoff eta L b window bW Qwidth z c eps A Mnext Fnext cnext tau:ℝ)
    (j:ℕ)(hZ:1<Z)(hL:1≤L)(heta:0≤eta)(heta1:eta≤1)
    (hcut:0<cutoff)(hsmall:eta≤cutoff/32)(hV:0≤V)(hparentcap:N+V≤L)
    (hbW:bW≤Z^eta)(hlog:1≤eta*Real.log Z)(hexp:Real.exp 1≤Z^eta)
    (hbin:2≤Z^eta)(hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j)).Nonempty)
    (base Ψ:O→*ℂ)(hΨ:CanonicalCoefficientClass.IsBaseRayTwist base Ψ)(m:O)(hm:m≠0)
    (hparent:CanonicalMargins (N+V) M Qwidth z c)
    (hpuncture:(Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hMc:M-3*(cutoff/2)/2≤Mnext)(hFc:N+V+15*eta≤Fnext)(hcc:cnext≤c-7*eta)
    {σ:Type}[DecidableEq σ](slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (ω₁ ω₂:𝓢(ℝ,ℂ))(K degree:ℕ):
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₁ Z Mnext Fnext z cnext eps A K degree →
    CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ base slots lists a ω₂ Z Mnext Fnext z cnext eps A K degree →
    ∀k:SourceIndex,∀l jj:ℕ,∀negative:Bool,
      ChildBounds (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ
        (progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D bW (Z^N) j))
        k l jj negative Ψ m slots lists a ω₁ ω₂
        Z M (N-3*actualCubeLength Z j) (actualCubeLength Z j) V eta tau window b eps A K degree :=by
  dsimp only
  intro h₁ h₂ k l jj negative
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  obtain ⟨hel,hr,hrL,helL,hFL,hgap,hqn⟩:=actual_long_bin_geometry S D hbad bW Z N V cutoff eta L j
    hZ hL heta1 hV hparentcap hbW hlog hne
  have hs:(N-3*actualCubeLength Z j)+3*actualCubeLength Z j+V=N+V:=by ring
  apply canonical_rank_cap_children (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
    (fun i=>(primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2)
    Finset.univ _ k l jj negative base Ψ hΨ m hm slots lists a ω₁ ω₂
    Z M _ _ V eta tau window b (cutoff/2) Qwidth z c eps A Mnext Fnext cnext K degree
    hZ heta hbin hel hV hb hbt hwindow (by linarith) (by linarith) (by linarith)
    (by simpa only [hs] using hparent) hpuncture ?_ hMc (by simpa only [hs] using hFc) hcc h₁ h₂
  intro v hv
  apply (hqn v hv).2.trans
  calc
    _≤Z^eta*Z^(actualCubeLength Z j):=mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg (by linarith) _)
    _=Z^(actualCubeLength Z j+eta):=by rw [Real.rpow_add (by linarith : 0<Z)];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1568

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLiveStepScalars
Source SHA256: 8b33b44f298e8f1e3dd294c8da2bce73ac2a2265c08e3295f840847cfd970fcd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1569






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

lemma columnScale_physical (Z r:ℝ)(hZ:1<Z)(k:SourceIndex)(l:ℕ)(negative:Bool):
    columnScale Z r k l negative=physicalScales (Z^r) k l (if negative then 7 else 8):=by
  rw [physicalScales_rpow Z r hZ k l]
  cases negative <;> rfl

 theorem original_live_step_scalars {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
    (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(om:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (K Z M r ell V F eta tau theta oldb b window em ed pi:ℝ)
    (hZ:1<Z)(hbin:2≤Z^eta)(hF:0≤F)(hM:0≤M)(hMF:M≤F)
    (hr: -eta≤r)(hrF:r≤F)(hell:0≤ell)(hellF:ell≤F)(hV:0≤V)(hVF:V≤F)
    (heta:0≤eta)(heta1:eta≤1)(htau:0≤tau)(htau1:tau≤1)
    (hwindow:Real.exp window≤Z^eta)(hold:oldb≤Real.exp window)(hb:b≤Real.exp window)
    (hem:0≤em)(hed:0≤ed)(hpi:0≤pi)(hetapi:6*eta≤pi)
    (hsmall:em*(20*(3*F+16)+30)≤pi/4)(hsmall':ed*(20*(3*F+16)+30)≤pi/4)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hlabels:∀I∈labels,I≠0)(hs:∀y,om y≠0→y≤oldb):
    let A:=3*F+16;
    let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
    let W:=fun y=>normTwistedSource om theta (y/Z^r);
    let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
    ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K),∀negative:Bool,
      let X:=columnScale Z r k.1 k.2.1 negative;
      let Y:=firstCellRadius Z M r ell V eta tau k.1 k.2.2;
      1≤Y ∧ 1≤X*Real.exp window ∧ X*Real.exp window≤Z^(A+1) ∧ Y≤Z^(16*A+20) ∧ Y⁻¹≤Z^(4*A+2) ∧
      b*X≤Z^(16*A+20) ∧ exponent Z (k.1 3)+eta+2*(A+1)+tau+(4*A+2)≤16*A+20 ∧
      firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4))+
        (9/2:ℝ)*eta≤16*A+20 ∧
      em*(ell+exponent Z (k.1 4)/2+exponent Z k.2.1+(16*A+20)+11*eta/2)≤pi ∧
      em*(r-columnA Z k.1 negative-exponent Z (k.1 2)-exponent Z k.2.1)+7*eta/2+
        ed*(3*ell+exponent Z (k.1 2)+exponent Z k.2.1+5*eta)+
        2*em*(2*ell+exponent Z (k.1 2)+exponent Z k.2.1+4*eta)≤pi+eta/2 ∧
      ell+eta≤16*A+20 ∧ exponent Z (k.1 4)+eta≤16*A+20 ∧
      exponent Z (k.1 2)+eta≤16*A+20 ∧ exponent Z k.2.1+eta≤16*A+20:=by
  intro A cutoff W S k hk negative X Y
  have hz:0<Z:=zero_lt_one.trans hZ
  have hA:0≤A:=by dsimp [A];linarith
  have hFA:F≤A:=by dsimp [A];linarith
  obtain ⟨hcoords,ht,hj⟩:=original_live_exponent_caps p hp hcop hg pool Q labels β cutoff Ψ m mark om Φ K Z r ell F eta tau theta oldb
    hZ hbin hF hrF hellF heta htau (hold.trans hwindow) hQ hlabels hs k hk
  have hecap:3*F+15*eta+tau≤A:=by dsimp [A];linarith
  have hkcap:∀i,0≤exponent Z (k.1 i) ∧ exponent Z (k.1 i)≤A:=fun i=>⟨(hcoords i).1,(hcoords i).2.trans hecap⟩
  have hacap:0≤columnA Z k.1 negative ∧ columnA Z k.1 negative≤A:=hkcap (if negative then 0 else 1)
  have htcap:exponent Z k.2.1≤A:=ht.2.trans hecap
  have hjcap:exponent Z k.2.2≤A:=hj.2.trans hecap
  have hscl:=first_step_scalar_caps Z A M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative)
    (exponent Z (k.1 2)) (exponent Z (k.1 4)) (exponent Z k.2.1) (exponent Z k.2.2) eta tau window b
    hZ hA hM (hMF.trans hFA) (by linarith) (hrF.trans hFA) hell (hellF.trans hFA) hV (hVF.trans hFA)
    (hkcap 3).1 (hkcap 3).2 hacap.1 hacap.2 (hkcap 2).1 (hkcap 2).2 (hkcap 4).1 (hkcap 4).2
    ht.1 htcap hj.1 hjcap heta heta1 htau htau1 hwindow (hb.trans hwindow)
  have hloss:=first_step_scalar_losses A r ell (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4))
    (exponent Z k.2.1) eta pi em ed hA (hrF.trans hFA) (hellF.trans hFA) hacap.1 (hkcap 2).1 (hkcap 2).2
    (hkcap 4).2 ht.1 htcap heta heta1 hem hed hpi hetapi hsmall hsmall'
  have hYone:=first_live_cell_radius_one p hp hcop hg pool Q labels _ Z M r ell V eta tau β Ψ m mark W Φ K hlabels k hk
  have hW:∀y,W y≠0→y≤oldb*Z^r:=by
    intro y hy
    have hnon:om (y/Z^r)≠0:=by intro h;exact hy (by simp [W,normTwistedSource,h])
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hnon)
  have hcol:=original_live_column_scale p hp hcop hg pool Q labels _ β cutoff Ψ m mark W Φ K (Z^r) oldb
    (Real.rpow_pos_of_pos hz _) hW k hk
  have hXone:1≤X*Real.exp window:=by
    have hpos:0≤X:=Real.rpow_nonneg hz.le _
    apply le_trans _ (mul_le_mul_of_nonneg_left hold hpos)
    dsimp [X]
    rw [columnScale_physical Z r hZ]
    cases negative
    · exact hcol.2
    · exact hcol.1
  refine ⟨hYone,hXone,hscl.1,hscl.2.1,hscl.2.2.1,hscl.2.2.2.1,hscl.2.2.2.2.1,
    hscl.2.2.2.2.2.1,hloss.1,hloss.2,?_,?_,?_,?_⟩ <;> linarith [(hkcap 4).2,(hkcap 2).2]

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1569

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLiveActualStep
Source SHA256: e18473b8d737bf1882051daca5ed807d18a5cdd13faf4ac47c65c42fa52858f1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1570


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_label_step
    (old:ℝ → ℂ)(oldb:ℝ)(hsold:∀y,old y≠0 → y≤oldb)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)(negative:Bool)
    (F tau saving window b em ed:ℝ)(hF:0≤F)(htau:0<tau)(hb:1≤b)
    (hhib:hi≤b)(hwindow: b≤Real.exp window)(hold:oldb≤Real.exp window)(hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁ ω₂:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (ω₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂:ℝ → ℂ) ∧
      tsupport (ω₁:ℝ → ℂ)⊆Set.Icc af bf ∧ tsupport (ω₂:ℝ → ℂ)⊆Set.Icc af bf ∧
    ∀degree:ℕ,∃C Cbin Cz Ct:ℝ,0≤C ∧ 0≤Cbin ∧ 0≤Cz ∧ 0≤Ct ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι → O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι →₀ ℕ))(labels:Finset (Ideal O))(β:Ideal O → (ι →₀ ℕ) → ℂ)
      (Ψ:O →* ℂ)(m:O)(slots:Finset σ)(lists:σ → Finset ι)(weights:σ → ι → ℂ)
      (Φ:𝓢(ℝ,ℂ))(Z M r ell V eta pi epschild A theta t Kphysical:ℝ),
      2≤Z → 2≤Z^eta → 0≤M → M≤F →  (-eta≤r)  → r≤F → 0≤ell → ell≤F → 0≤V → V≤F →
      0≤eta → eta≤1 → tau≤1 → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
      em*(20*(3*F+16)+30)≤pi/4 → ed*(20*(3*F+16)+30)≤pi/4 →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀u,‖Ψ u‖≤1) → (slots:Set σ).PairwiseDisjoint lists → slots.card≤K →
      (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) → 0≤A →
      let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource old theta (y/Z^r);
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
      ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ Kphysical),
      ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 negative Ψ m slots lists weights ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree →
      (Z^(firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2) (parentWeight p k.2.1)
        negative Ψ m slots lists weights om (columnScale Z r k.1 k.2.1 negative) t (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤
      Cz*Z^(r+3*ell+V+17*eta+tau+pi)+
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder (2*degree))*(1+Cbin*Real.log Z)^4*
        Z^(r+3*ell+V+48*eta+tau+pi+epschild)+Ct*Z^(-saving):=by
  let cap:=3*F+16
  have hcap:0≤cap:=by dsimp [cap];linarith
  have hbig:0≤16*cap+20:=by positivity
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,he⟩:=actual_label_cell_step om lo hi hlo hs negative
    window (16*cap+20) (16*cap+20) tau saving (hhib.trans hwindow) hbig hbig htau b hb ed hed (fun _=>0) (by intro i;norm_num) K em hem
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro degree
  obtain ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,hstep⟩:=he degree
  refine ⟨C,Cbin,Cz,Ct,hC,hCb,hCz,hCt,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc pool Q labels β Ψ m slots lists weights Φ
    Z M r ell V eta pi epschild A theta t Kphysical hZ hbin hM hMF hr hrF hell hellF hV hVF heta heta1 htau1
    hwin hpi hetapi hsmall hsmall' hQ hn hΨ hslots hcard hw hA cutoff W mark S k hk hchild
  have hZ1:1<Z:=by linarith
  have hz:0<Z:=by linarith
  obtain ⟨hY1,hX1,hcol,hYcap,hYi,hgeom,hphysical,hPcap,hbudget,hcost,hellcap,hactivecap,hcommoncap,hquotcap⟩:=
    original_live_step_scalars p hp hcop hg pool Q labels β Ψ m mark old Φ Kphysical Z M r ell V F eta tau theta oldb b window em ed pi
      hZ1 hbin hF hM hMF hr hrF hell hellF hV hVF heta heta1 htau.le htau1 hwin hold hwindow hem.le hed.le hpi hetapi
      hsmall hsmall' hQ hn hsold k hk negative
  apply hstep p hp hcop hg hpr hinj hc pool Q k.1 k.2.1 k.2.2 Ψ m slots lists weights
    Z M r ell V eta pi b (cap+1) (4*cap+2) epschild A t (fun _=>0)
    hZ heta hbin (by linarith) hQ hslots hcard hw hΨ (by intro i;simp) hhib le_rfl hb
  · exact (hwindow.trans hwin).trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hwin.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hA
  · exact hcol
  · exact hYi
  · exact hgeom
  · exact hphysical
  · exact hbudget
  · exact hcost
  · exact hY1
  · exact hX1
  · exact hYcap
  · exact hYi.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hcol.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith))
  · exact hPcap
  · exact hellcap
  · exact hactivecap
  · exact hcommoncap
  · exact hquotcap
  · exact hchild

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule1570

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstSecondHeightCost
Source SHA256: f7ccb2312c0c6a201f678d239c91bc427c5e2ac542d68fe993046b7ddb527d1d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1571




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstSecondHeightCost
open InverseMoment InverseAmbientProfileTower JointLogSeparation FourierBridge
open InverseMomentFirstOriginalProfile

def firstDegree (degree : ℕ) : ℕ := 2*InverseClippingProfiles.momentOrder (2*degree)

def firstHeight (negative : Bool) (z : Frequency×(Fin 9→ℝ)) : ℝ :=
  profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 (if negative then 7 else 8)

lemma first_height_cost (degree : ℕ) (negative : Bool) (z : Frequency×(Fin 9→ℝ)) :
    (1+‖firstHeight negative z‖)^(firstDegree degree)≤
      tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2 := by
  cases negative
  · exact first_right_height_budget _ z
  · exact first_left_height_budget _ z

lemma first_weight_one_le (J : ℕ) (z : Frequency×(Fin 9→ℝ)) :
    1≤tripleHeight J z.1*coordinateHeight J z.2 := by
  simpa only [ambientWeight,tripleHeight,coordinateHeight] using ambientWeight_one_le J z

def stepBudget (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ) : ℝ :=
  Czero*Z^(F+17*eta+tau+pi)+
    C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)

lemma stepBudget_nonneg (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hA : 0≤A) (hZ : 0≤Z) :
    0≤stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving := by
  unfold stepBudget
  positivity

theorem second_step_first_height (degree : ℕ) (negative : Bool)
    (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hA : 0≤A) (hZ : 0≤Z)
    (z : Frequency×(Fin 9→ℝ)) :
    Czero*Z^(F+17*eta+tau+pi)+
      C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
        Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  have hw := first_weight_one_le (firstDegree degree) z
  have hh := first_height_cost degree negative z
  have hzero : Czero*Z^(F+17*eta+tau+pi)≤
      (Czero*Z^(F+17*eta+tau+pi))*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) :=
    le_mul_of_one_le_right (by positivity) hw
  have htail : Ctail*Z^(-saving)≤
      (Ctail*Z^(-saving))*(tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) :=
    le_mul_of_one_le_right (by positivity) hw
  have hmiddle := mul_le_mul_of_nonneg_left hh
    (show 0≤C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild) by positivity)
  have hs := add_le_add (add_le_add hzero hmiddle) htail
  convert hs using 1 <;> dsimp [stepBudget] <;> ring

lemma log_fourth_small_power (Cbin ε : ℝ) (hε : 0<ε) :
    ∃ Clog : ℝ,0<Clog ∧ ∀ Z : ℝ,2≤Z→
      (1+Cbin*Real.log Z)^4≤Clog*Z^ε := by
  obtain ⟨C,hC,he⟩ := log_eighth_small_power ε hε
  let b := 1+|Cbin|
  have hb : 0<b := by dsimp [b];positivity
  refine ⟨b^4*C,mul_pos (pow_pos hb _) hC,?_⟩
  intro Z hZ
  have hZ1 : 1≤Z := by linarith
  have hl : 0≤Real.log Z := Real.log_nonneg hZ1
  have hn : |1+Cbin*Real.log Z|≤b*(1+Real.log Z) := by
    calc
      _≤1+|Cbin| *Real.log Z := by simpa [abs_mul,abs_of_nonneg hl] using abs_add_le (1:ℝ) (Cbin*Real.log Z)
      _≤_ := by dsimp [b];nlinarith [abs_nonneg Cbin]
  calc
    _ = |1+Cbin*Real.log Z|^4 := by rw [←abs_pow,abs_of_nonneg (by positivity)]
    _ ≤ (b*(1+Real.log Z))^4 := pow_le_pow_left₀ (abs_nonneg _) hn 4
    _≤b^4*(1+Real.log Z)^8 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith : 1≤1+Real.log Z) (by norm_num : 4≤8)) (by positivity)
    _≤b^4*(C*Z^ε) := mul_le_mul_of_nonneg_left (he Z hZ1) (by positivity)
    _=_ := by ring

theorem stepBudget_small_power (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0<Ctotal ∧ ∀ A Z F eta tau pi epschild saving : ℝ,
      0≤A→2≤Z→0≤eta→0≤epschild→
      -saving≤F+48*eta+tau+pi+epschild+ε→
      stepBudget C Cbin Czero Ctail A Z F eta tau pi epschild saving≤
        Ctotal*(1+A)*Z^(F+48*eta+tau+pi+epschild+ε) := by
  obtain ⟨Clog,hlog,hlogs⟩ := log_fourth_small_power Cbin ε hε
  refine ⟨1+Czero+C*Clog+Ctail,by positivity,?_⟩
  intro A Z F eta tau pi epschild saving hA hZ heta hepschild hsaving
  have hZ1 : 1≤Z := by linarith
  have hZ0 : 0<Z := by linarith
  have h0 : Z^(F+17*eta+tau+pi)≤Z^(F+48*eta+tau+pi+epschild+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have h1 : C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild)≤
      C*A*Clog*Z^(F+48*eta+tau+pi+epschild+ε) := by
    calc
      _≤C*A*(Clog*Z^ε)*Z^(F+48*eta+tau+pi+epschild) := by gcongr;exact hlogs Z hZ
      _=_ := by rw [show C*A*(Clog*Z^ε)*Z^(F+48*eta+tau+pi+epschild)=
          C*A*Clog*(Z^ε*Z^(F+48*eta+tau+pi+epschild)) by ring,←Real.rpow_add hZ0];congr 1;congr 1;ring
  have h2 : Z^(-saving)≤Z^(F+48*eta+tau+pi+epschild+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ1 hsaving
  have hsum := add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 hz) h1)
    (mul_le_mul_of_nonneg_left h2 ht)
  unfold stepBudget
  apply hsum.trans
  have hpow : 0≤Z^(F+48*eta+tau+pi+epschild+ε) := Real.rpow_nonneg hZ0.le _
  have hcoef : Czero+C*A*Clog+Ctail≤(1+Czero+C*Clog+Ctail)*(1+A) := by
    have hza : 0≤Czero*A := mul_nonneg hz hA
    have hta : 0≤Ctail*A := mul_nonneg ht hA
    have hc : 0≤C*Clog := mul_nonneg hC hlog.le
    nlinarith
  convert mul_le_mul_of_nonneg_right hcoef hpow using 1 ; ring

theorem first_source_budget (degree : ℕ) (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0<Ctotal ∧ ∀ A Z F eta tau pi epschild saving : ℝ,
      0≤A→2≤Z→0≤eta→0≤epschild→
      -saving≤F+48*eta+tau+pi+epschild+ε→
      ∀(negative : Bool)(z : Frequency×(Fin 9→ℝ)),
      Czero*Z^(F+17*eta+tau+pi)+
        C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
          Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      (Ctotal*(1+A)*Z^(F+48*eta+tau+pi+epschild+ε))*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  obtain ⟨Ct,hCt,hbudget⟩ := stepBudget_small_power C Cbin Czero Ctail ε hC hz ht hε
  refine ⟨Ct,hCt,?_⟩
  intro A Z F eta tau pi epschild saving hA hZ heta heps hsaving negative z
  exact (second_step_first_height degree negative C Cbin Czero Ctail A Z F eta tau pi epschild saving
    hC hz ht hA (by linarith) z).trans
    (mul_le_mul_of_nonneg_right (hbudget A Z F eta tau pi epschild saving hA hZ heta heps hsaving)
      (le_trans zero_le_one (first_weight_one_le _ z)))

theorem first_source_requested_loss (degree : ℕ) (C Cbin Czero Ctail ε : ℝ)
    (hC : 0≤C) (hz : 0≤Czero) (ht : 0≤Ctail) (hε : 0<ε) :
    ∃ Ctotal : ℝ,0<Ctotal ∧ ∀ A Z F eta tau pi epschild saving loss : ℝ,
      0≤A→2≤Z→0≤eta→0≤epschild→
      -saving≤F+48*eta+tau+pi+epschild+ε→
      48*eta+tau+pi+epschild+ε≤loss→
      ∀(negative : Bool)(z : Frequency×(Fin 9→ℝ)),
      Czero*Z^(F+17*eta+tau+pi)+
        C*A*(1+‖firstHeight negative z‖)^(firstDegree degree)*(1+Cbin*Real.log Z)^4*
          Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)≤
      (Ctotal*(1+A)*Z^(F+loss))*
        (tripleHeight (firstDegree degree) z.1*coordinateHeight (firstDegree degree) z.2) := by
  obtain ⟨Ct,hCt,hbudget⟩ := first_source_budget degree C Cbin Czero Ctail ε hC hz ht hε
  refine ⟨Ct,hCt,?_⟩
  intro A Z F eta tau pi epschild saving loss hA hZ heta heps hsaving hloss negative z
  apply (hbudget A Z F eta tau pi epschild saving hA hZ heta heps hsaving negative z).trans
  apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one (first_weight_one_le _ z))
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end SevenEighths.InverseMomentFirstSecondHeightCost
end

end OAI
end OAIOriginalModule1571

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLiveHeightStep
Source SHA256: 7263adc71acd4cfef17564601a073539272ead8bd9bf1348db560273a28f7dff
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1572



namespace OAI

noncomputable section
