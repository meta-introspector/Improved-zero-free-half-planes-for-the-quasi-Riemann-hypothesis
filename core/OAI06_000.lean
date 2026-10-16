import core.OAI05
-- import Mathlib.Algebra.BigOperators.Ring.Finset
-- import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
-- import Mathlib.Analysis.Normed.Group.Tannery
-- import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
-- import Mathlib.Analysis.SpecialFunctions.Log.Base
-- import Mathlib.Data.Int.Interval
-- import Mathlib.MeasureTheory.Group.Prod
-- import Mathlib.MeasureTheory.Integral.DominatedConvergence
-- import Mathlib.MeasureTheory.Integral.Prod
-- import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

/-! Pinned OAI dependency closure, consolidated without changing public namespaces.
Original module boundaries and hashes are preserved below. -/

/-! Original module: OAI.NumberTheory.DirichletL.Detector.IdealFactorization
Source SHA256: 884a54ef77d8d66811279d51b23db625beb4b471d4f5515f447f0a565c4ef09a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1369



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PrimeIdeal := {P : Id // Prime P}

def primeValuations (I : Id) : PrimeIdeal →₀ ℕ :=
  (factorization I).subtypeDomain Prime

def idealFromValuations (v : PrimeIdeal →₀ ℕ) : Id :=
  v.prod (fun P n=>P.val^n)

lemma idealFromValuations_ne_zero (v : PrimeIdeal →₀ ℕ) : idealFromValuations v≠0 := by
  unfold idealFromValuations Finsupp.prod
  exact Finset.prod_ne_zero_iff.mpr (fun P hP=>pow_ne_zero _ P.property.ne_zero)

@[simp] lemma primeValuations_apply (I : Id) (P : PrimeIdeal) :
    primeValuations I P=(normalizedFactors I).count P.val := by
  simp only [primeValuations,Finsupp.subtypeDomain_apply,factorization_eq_count]

@[simp] lemma primeValuations_one : primeValuations 1=0 := by
  simp only [primeValuations,factorization_one,Finsupp.subtypeDomain_zero]

lemma primeValuations_mul (I J : Id) (hI : I≠0) (hJ : J≠0) :
    primeValuations (I*J)=primeValuations I+primeValuations J := by
  simp only [primeValuations,factorization_mul hI hJ,Finsupp.subtypeDomain_add]

@[simp] lemma primeValuations_prime (P : PrimeIdeal) :
    primeValuations P.val=Finsupp.single P 1 := by
  ext Q
  simp only [primeValuations_apply,normalizedFactors_irreducible P.property.irreducible,
    normalize_eq,Multiset.count_singleton,Finsupp.single_apply]
  by_cases h : Q=P
  · subst Q
    simp
  · have hv : Q.val≠P.val := fun hh=>h (Subtype.ext hh)
    simp [Ne.symm h,hv]

lemma primeValuations_pow (I : Id) (n : ℕ) :
    primeValuations (I^n)=n • primeValuations I := by
  ext P
  simp only [primeValuations_apply,normalizedFactors_pow,Multiset.count_nsmul,
    Finsupp.coe_smul,Pi.smul_apply,smul_eq_mul]

@[simp] lemma idealFromValuations_zero : idealFromValuations 0=1 := by
  simp [idealFromValuations]

lemma idealFromValuations_add (v w : PrimeIdeal →₀ ℕ) :
    idealFromValuations (v+w)=idealFromValuations v*idealFromValuations w := by
  exact Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)

@[simp] lemma idealFromValuations_single (P : PrimeIdeal) (n : ℕ) :
    idealFromValuations (Finsupp.single P n)=P.val^n := by
  simp [idealFromValuations]

@[simp] theorem primeValuations_idealFromValuations (v : PrimeIdeal →₀ ℕ) :
    primeValuations (idealFromValuations v)=v := by
  induction v using Finsupp.induction with
  | zero => simp only [idealFromValuations_zero,primeValuations_one]
  | @single_add P n v hP hn ih =>
    rw [idealFromValuations_add,primeValuations_mul _ _
      (idealFromValuations_ne_zero _) (idealFromValuations_ne_zero _),ih]
    simp only [idealFromValuations_single,primeValuations_pow,primeValuations_prime,
      Finsupp.smul_single,smul_eq_mul,mul_one]

@[simp] theorem idealFromValuations_primeValuations (I : Id) (hI : I≠0) :
    idealFromValuations (primeValuations I)=I := by
  have hs : ∀ P∈(factorization I).support,Prime P := by
    intro P hP
    exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp (by simpa using hP))
  unfold idealFromValuations primeValuations
  rw [Finsupp.prod_subtypeDomain_index hs]
  simp only [Finsupp.prod,support_factorization,factorization_eq_count]
  rw [← Finset.prod_multiset_count_of_subset _ _ (Finset.Subset.refl _)]
  exact Ideal.prod_normalizedFactors_eq_self hI

def nonzeroIdealValuationEquiv : {I : Id // I≠0} ≃ (PrimeIdeal →₀ ℕ) where
  toFun I := primeValuations I.val
  invFun v := ⟨idealFromValuations v,idealFromValuations_ne_zero v⟩
  left_inv I := Subtype.ext (idealFromValuations_primeValuations I.val I.property)
  right_inv := primeValuations_idealFromValuations

lemma primeIdeal_coprime (P Q : PrimeIdeal) (h : P≠Q) : IsCoprime P.val Q.val := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : Q.val.IsPrime := Ideal.isPrime_of_prime Q.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  let : Q.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance Q.property.ne_zero
  exact Ideal.isCoprime_of_isMaximal (fun hh=>h (Subtype.ext hh))

lemma prime_coprime_idealFromValuations (P : PrimeIdeal) (v : PrimeIdeal →₀ ℕ)
    (hP : v P=0) : IsCoprime P.val (idealFromValuations v) := by
  apply IsCoprime.prod_right
  intro Q hQ
  apply IsCoprime.pow_right
  apply primeIdeal_coprime
  intro hh
  subst Q
  exact Finsupp.mem_support_iff.mp hQ hP

def finsuppPairEquiv {α β γ : Type*} [Zero β] [Zero γ] :
    ((α→₀β)×(α→₀γ)) ≃ (α→₀(β×γ)) where
  toFun v := Finsupp.zipWith Prod.mk rfl v.1 v.2
  invFun v := (v.mapRange Prod.fst rfl,v.mapRange Prod.snd rfl)
  left_inv v := by
    apply Prod.ext <;> ext a <;> rfl
  right_inv v := by
    apply Finsupp.ext
    intro a
    exact Prod.eta (v a)

abbrev HighValuation := (ℕ×ℕ)×(ℕ×ℕ)
abbrev NonzeroIdeal := {I : Id // I≠0}

def highValuationEquiv : ((NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) ≃
    (PrimeIdeal→₀HighValuation) :=
  (Equiv.prodCongr
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)
    (Equiv.prodCongr nonzeroIdealValuationEquiv nonzeroIdealValuationEquiv)).trans
      ((Equiv.prodCongr finsuppPairEquiv finsuppPairEquiv).trans finsuppPairEquiv)

@[simp] lemma highValuationEquiv_apply
    (a : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal)) (P : PrimeIdeal) :
    highValuationEquiv a P =
      ((primeValuations a.1.1.val P,primeValuations a.1.2.val P),
        (primeValuations a.2.1.val P,primeValuations a.2.2.val P)) := rfl

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1369

/-! Original module: OAI.NumberTheory.DirichletL.Detector.EulerFinsupp
Source SHA256: 68ef98e1a5abc9fb5606a9fe102e355fabcc9bbe1a78aa620489fff65a2c576e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1370



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeEulerFinsupp

lemma finitePi_fin {β : Type*} (n : ℕ) (f : Fin n→β→ℂ)
    (hf : ∀ i,Summable (fun b=>‖f i b‖)) :
    Summable (fun v : Fin n→β => ‖∏ i,f i (v i)‖) ∧
      (∑' v : Fin n→β,∏ i,f i (v i))=∏ i,∑' b,f i b := by
  induction n with
  | zero =>
    constructor
    · exact (hasSum_fintype _).summable
    · simp
  | succ n ih =>
    have ht := ih (fun i=>f i.succ) (fun i=>hf i.succ)
    let e := Fin.consEquiv (fun _ : Fin (n+1)=>β)
    have he (v : β×(Fin n→β)) :
        (∏ i,f i (e v i))=f 0 v.1*(∏ i,f i.succ (v.2 i)) := by
      rw [Fin.prod_univ_succ]
      rfl
    constructor
    · rw [←e.summable_iff]
      simp only [Function.comp_def,he]
      have hm : Summable (fun v : β×(Fin n→β)=>‖f 0 v.1‖ * ‖∏ i : Fin n,f i.succ (v.2 i)‖) :=
        (hf 0).mul_of_nonneg ht.1 (fun _=>norm_nonneg _) (fun _=>norm_nonneg _)
      simpa only [norm_mul] using hm
    · rw [←e.tsum_eq (fun v=>∏ i,f i (v i))]
      simp only [he]
      rw [←tsum_mul_tsum_of_summable_norm (f:=f 0)
        (g:=fun v : Fin n→β=>∏ i : Fin n,f i.succ (v i)) (hf 0) ht.1,ht.2,Fin.prod_univ_succ]

lemma finitePi {α β : Type*} [Fintype α] (f : α→β→ℂ)
    (hf : ∀ i,Summable (fun b=>‖f i b‖)) :
    Summable (fun v : α→β => ‖∏ i,f i (v i)‖) ∧
      (∑' v : α→β,∏ i,f i (v i))=∏ i,∑' b,f i b := by
  let e := Fintype.equivFin α
  let d := Equiv.arrowCongr e.symm (Equiv.refl β)
  have h := finitePi_fin (Fintype.card α) (fun i=>f (e.symm i)) (fun i=>hf (e.symm i))
  have hd (v : Fin (Fintype.card α)→β) :
      (∏ i,f i (d v i))=∏ j,f (e.symm j) (v j) := by
    apply Fintype.prod_equiv e
    intro i
    simp only [d,Equiv.arrowCongr_apply,Equiv.symm_symm,Equiv.refl_apply,e.symm_apply_apply,Function.comp_apply]
  constructor
  · rw [←d.summable_iff]
    simpa only [Function.comp_def,hd] using h.1
  · rw [←d.tsum_eq (fun v=>∏ i,f i (v i))]
    simp only [hd]
    rw [h.2]
    exact e.symm.prod_comp (fun i=>∑' b,f i b)

variable {α β : Type*} [AddCommMonoid β]

lemma finiteEuler (f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hf : ∀a,Summable (fun b=>‖f a b‖)) (S : Finset α) :
    (∑' v : {v : α→₀β // (v.support:Set α)⊆S},v.val.prod f)=
      ∏ a∈S,∑' b,f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      v.val.prod f=∏ a:S,f a.val (e v a) := by
    rw [←Finsupp.prod_subtypeDomain_index (p:=fun a=>a∈S) (fun a ha=>v.property ha)]
    exact Finsupp.prod_fintype _ _ (fun a=>h0 a.val)
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏ a:S,f a.val (v a))]
  rw [(finitePi (fun a:S=>f a.val) (fun a=>hf a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑' b,f a b)

theorem hasProd_of_summable (f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hs : Summable (fun v : α→₀β=>‖v.prod f‖)) :
    HasProd (fun a=>∑' b,f a b) (∑' v : α→₀β,v.prod f) := by
  have hf (a : α) : Summable (fun b=>‖f a b‖) := by
    have hh := hs.comp_injective (Finsupp.single_injective a)
    simpa only [Function.comp_def,Finsupp.prod_single_index (h0 a)] using hh
  have ht : Tendsto (fun S : Finset α=>∑' v : α→₀β,
      if v.support⊆S then v.prod f else 0) atTop (𝓝 (∑' v : α→₀β,v.prod f)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro v
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop v.support] with S hS
      simp only [ite_eq_left hS]
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero] using norm_nonneg (v.prod f)
  have he (S : Finset α) : (∑' v : α→₀β,if v.support⊆S then v.prod f else 0)=
      ∏a∈S,∑' b,f a b := by
    rw [←finiteEuler f h0 hf S]
    trans ∑' v : α→₀β, {v : α→₀β | (v.support:Set α)⊆S}.indicator (fun v=>v.prod f) v
    · apply tsum_congr
      intro v
      simp only [Set.indicator,Set.mem_ofPred_eq,Finset.coe_subset]
    · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (fun v=>v.prod f)).symm
  change Tendsto (fun S : Finset α=>∏a∈S,∑' b,f a b) atTop _
  simpa only [he] using ht

end SevenEighths.ProbeEulerFinsupp
end

end OAI
end OAIOriginalModule1370

/-! Original module: OAI.NumberTheory.DirichletL.Detector.EulerMarked
Source SHA256: 6dd8d439e24b3cf7058756b2ce3189ba5bdc8a021a14b4b9b0323d4ddc5f2023
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1371


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeEulerFinsupp
variable {α β : Type*} [AddCommMonoid β]

def markedArray (T : Finset α) (m f : α→β→ℂ) (v : α→₀β) : ℂ :=
  (∏a∈T,m a (v a))*v.prod f

def markedLocal (T : Finset α) (m f : α→β→ℂ) (a : α) (b : β) : ℂ :=
  (if a∈T then m a b else 1)*f a b

lemma markedArray_finite (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ)
    (h0 : ∀a,f a 0=1) (v : α→₀β) (hv : v.support⊆S) :
    markedArray T m f v=∏a∈S,markedLocal T m f a (v a) := by
  simp only [markedArray,markedLocal,Finset.prod_mul_distrib]
  congr 1
  · symm
    rw [←Finset.prod_subset hTS]
    · apply Finset.prod_congr rfl
      intro a ha
      simp only [ite_eq_left ha]
    · intro a ha hna
      simp only [ite_eq_right hna]
  · exact Finsupp.prod_of_support_subset v hv _ (fun a _=>h0 a)

lemma markedArray_norm_le (T : Finset α) (m f : α→β→ℂ)
    (hm : ∀a∈T,∀b,‖m a b‖≤1) (v : α→₀β) :
    ‖markedArray T m f v‖≤‖v.prod f‖ := by
  rw [markedArray,norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun a ha=>hm a ha _)

lemma marked_finiteEuler (T S : Finset α) (hTS : T⊆S) (m f : α→β→ℂ)
    (h0 : ∀a,f a 0=1) (hf : ∀a,Summable (fun b=>‖f a b‖))
    (hm : ∀a∈T,∀b,‖m a b‖≤1) :
    (∑'v : {v : α→₀β // (v.support:Set α)⊆S},markedArray T m f v.val)=
      ∏a∈S,∑'b,markedLocal T m f a b := by
  let e : {v : α→₀β // (v.support:Set α)⊆S} ≃ (S→β) :=
    (Finsupp.restrictSupportEquiv (S:Set α) β).trans Finsupp.equivFunOnFinite
  have he (v : {v : α→₀β // (v.support:Set α)⊆S}) :
      markedArray T m f v.val=∏a:S,markedLocal T m f a.val (e v a) := by
    rw [markedArray_finite T S hTS m f h0 v.val v.property]
    exact (Finset.prod_coe_sort S _).symm
  have hg (a : α) : Summable (fun b=>‖markedLocal T m f a b‖) := by
    apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ (hf a)
    intro b
    rw [markedLocal,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    split_ifs with ha
    · exact hm a ha b
    · simp
  simp_rw [he]
  rw [e.tsum_eq (fun v : S→β=>∏a:S,markedLocal T m f a.val (v a))]
  rw [(finitePi (fun a:S=>markedLocal T m f a.val) (fun a=>hg a.val)).2]
  exact Finset.prod_coe_sort S (fun a=>∑'b,markedLocal T m f a b)

theorem marked_hasProd (T : Finset α) (m f : α→β→ℂ) (h0 : ∀a,f a 0=1)
    (hs : Summable (fun v : α→₀β=>‖v.prod f‖))
    (hm : ∀a∈T,∀b,‖m a b‖≤1) :
    HasProd (fun a=>∑'b,markedLocal T m f a b) (∑'v : α→₀β,markedArray T m f v) := by
  have hf (a : α) : Summable (fun b=>‖f a b‖) := by
    have hh := hs.comp_injective (Finsupp.single_injective a)
    simpa only [Function.comp_def,Finsupp.prod_single_index (h0 a)] using hh
  have ht : Tendsto (fun S : Finset α=>∑'v : α→₀β,
      if v.support⊆S then markedArray T m f v else 0) atTop
      (𝓝 (∑'v : α→₀β,markedArray T m f v)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro v
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop v.support] with S hS
      simp only [ite_eq_left hS]
    · apply Filter.Eventually.of_forall
      intro S v
      split_ifs
      · exact markedArray_norm_le T m f hm v
      · simpa only [norm_zero] using norm_nonneg (v.prod f)
  change Tendsto (fun S : Finset α=>∏a∈S,∑'b,markedLocal T m f a b) atTop _
  apply ht.congr'
  filter_upwards [eventually_ge_atTop T] with S hTS
  rw [←marked_finiteEuler T S hTS m f h0 hf hm]
  trans ∑'v : α→₀β,{v : α→₀β | (v.support:Set α)⊆S}.indicator (markedArray T m f) v
  · apply tsum_congr
    intro v
    simp only [Set.indicator,Set.mem_ofPred_eq,Finset.coe_subset]
  · exact (tsum_subtype {v : α→₀β | (v.support:Set α)⊆S} (markedArray T m f)).symm

end SevenEighths.ProbeEulerFinsupp
end

end OAI
end OAIOriginalModule1371

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RadialExchange
Source SHA256: 23d7da49f52d45f6ab7e5a08a701ddc165a387d0e809cc67319335e2426a5abe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1372





namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma radialFourier_vertical_inverse (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (σ r : ℝ) (hσ : 0<σ) (hr : 0<r) :
    paperRadialFourier W r=verticalIntegral σ (fun z=>(r:ℂ)^(-z)*mellin (paperRadialFourier W) z) := by
  have he := ProbeRadialMellin.radial_mellin_inversion W a b ha hW σ r hσ hr
  simpa only [mellinInv,verticalIntegral,Complex.real_smul,smul_eq_mul] using he.symm

lemma radial_sum_exchange {ι : Type*} [Countable ι] (W : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W⊆Set.Icc a b)
    (σ : ℝ) (hσ : 0<σ) (c : ι→ℂ) (r : ι→ℝ) (hr : ∀i,0<r i)
    (hc : Summable (fun i=>‖c i‖*(r i)^(-σ))) :
    (∑'i,c i*paperRadialFourier W (r i))=
      verticalIntegral σ (fun z=>∑'i,c i*(r i:ℂ)^(-z)*mellin (paperRadialFourier W) z) := by
  let F := fun i (t : ℝ)=>c i*(r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*
    mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)
  have hF (i) : Integrable (F i) := by
    simpa only [F,mul_assoc] using
      (ProbeRadialMellin.radial_mellin_inverse_integrable W a b ha hW σ (r i) hσ (hr i)).const_mul (c i)
  have hn (i) (t : ℝ) : ‖F i t‖=(‖c i‖*(r i)^(-σ))*
      ‖mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)‖ := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hr i)]
    simp
  have hsum : Summable (fun i=>∫t : ℝ,‖F i t‖) := by
    simp only [hn,integral_const_mul]
    exact hc.mul_right _
  have he := integral_tsum_of_summable_integral_norm hF hsum
  simp_rw [radialFourier_vertical_inverse W a b ha hW σ _ hσ (hr _)]
  unfold verticalIntegral
  have hi (i) : c i*(↑(1/(2*Real.pi))*(∫t : ℝ,
      (r i:ℂ)^(-((σ:ℂ)+t*Complex.I))*mellin (paperRadialFourier W) ((σ:ℂ)+t*Complex.I)))=
      (↑(1/(2*Real.pi)):ℂ)*(∫t : ℝ,F i t) := by
    simp only [F,mul_assoc,integral_const_mul]
    ring
  simp_rw [hi]
  rw [tsum_mul_left,he]

lemma frequency_rpow_summable (σ : ℝ) (hσ : 1<σ) :
    Summable (fun H : NonzeroFrequency=>(elementNorm H.val)^(-σ)) := by
  have he (H : NonzeroFrequency) : ‖frequencyWeight (σ:ℂ) H‖=(elementNorm H.val)^(-σ) := by
    have hH : 0<elementNorm H.val := by
      unfold elementNorm
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr H.property))
    rw [frequencyWeight,Complex.norm_cpow_eq_rpow_re_of_pos hH]
    simp
  simpa only [he,Complex.ofReal_re] using frequencyWeight_summable_norm (σ:ℂ) hσ

theorem actualFrequency_moment_summable (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    Summable (fun H : NonzeroFrequency=>‖actualCongruenceCoefficient C A s hA H.val‖*
      (K*elementNorm H.val/elementNorm ((C.generator*A)*s))^(-σ)) := by
  have hd : 0<elementNorm ((C.generator*A)*s) := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)))
  have hr (H : NonzeroFrequency) :
      (K*elementNorm H.val/elementNorm ((C.generator*A)*s))^(-σ)=
        (K/elementNorm ((C.generator*A)*s))^(-σ)*(elementNorm H.val)^(-σ) := by
    rw [show K*elementNorm H.val/elementNorm ((C.generator*A)*s)=
      (K/elementNorm ((C.generator*A)*s))*elementNorm H.val by ring]
    apply Real.mul_rpow (div_pos hK hd).le
    unfold elementNorm
    positivity
  simp only [hr]
  have hb := (frequency_rpow_summable σ hσ).mul_left
    (((Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {C.generator*A}):ℝ))*
      (K/elementNorm ((C.generator*A)*s))^(-σ))
  apply Summable.of_nonneg_of_le (fun H=>mul_nonneg (norm_nonneg _)
    (mul_nonneg (Real.rpow_nonneg (div_pos hK hd).le _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _))) _ hb
  intro H
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (actualCongruenceCoefficient_norm_le C A s hA hs H.val)
      (Real.rpow_nonneg (div_pos hK hd).le _)) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1372

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RadialIdentity
Source SHA256: 86b7cad968595a0915cbd27dcebe8529c098c0065981009db22a3e240d1a6fe2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1373



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma elementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

lemma actualCongruenceCoefficient_zero_frequency (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) :
    actualCongruenceCoefficient (calibrationForSet S hS) A s hA 0=0 := by
  apply actualCongruenceCoefficient_zero_off_calibration S hS A s hA hs hcop
  intro hc
  have hz := (calibrationForSet_coprime_iff S hS 0).mp hc
  obtain ⟨P,hP⟩ := hSne
  exact hz P hP P.zero_mem

theorem actualFrequency_mellin_nonzero (C : CalibrationData) (A s : O)
    (hA : A≠0) (hs : s≠0) (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    (∑'H : NonzeroFrequency,actualCongruenceCoefficient C A s hA H.val*
      paperRadialFourier W (K*elementNorm H.val/elementNorm ((C.generator*A)*s)))=
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C A s hA H.val*
        ((K*elementNorm H.val/elementNorm ((C.generator*A)*s)):ℂ)^(-z)*
          mellin (paperRadialFourier W) z) := by
  let : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  have he := radial_sum_exchange W a b ha hW σ (by linarith)
    (fun H : NonzeroFrequency=>actualCongruenceCoefficient C A s hA H.val)
    (fun H=>K*elementNorm H.val/elementNorm ((C.generator*A)*s)) (by
      intro H
      exact div_pos (mul_pos hK (elementNorm_pos H.val H.property))
        (elementNorm_pos _ (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)))
    (actualFrequency_moment_summable C A s hA hs K hK σ hσ)
  simpa only [Complex.ofReal_mul,Complex.ofReal_div] using he

theorem actualFrequency_mellin (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (A s : O) (hA : A≠0) (hs : s≠0)
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s))
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (K : ℝ) (hK : 0<K) (σ : ℝ) (hσ : 1<σ) :
    let C := calibrationForSet S hS
    (∑'H : O,actualCongruenceCoefficient C A s hA H*
      paperRadialFourier W (K*elementNorm H/elementNorm ((C.generator*A)*s)))=
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C A s hA H.val*
        ((K*elementNorm H.val/elementNorm ((C.generator*A)*s)):ℂ)^(-z)*
          mellin (paperRadialFourier W) z) := by
  dsimp only
  rw [←actualFrequency_mellin_nonzero (calibrationForSet S hS) A s hA hs W a b ha hW K hK σ hσ]
  symm
  apply (Subtype.val_injective : Function.Injective (fun H : NonzeroFrequency=>H.val)).tsum_eq
    (f:=fun H : O=>actualCongruenceCoefficient (calibrationForSet S hS) A s hA H*
      paperRadialFourier W (K*elementNorm H/elementNorm (((calibrationForSet S hS).generator*A)*s)))
  intro H hH
  have hn : H≠0 := by
    intro hz
    subst H
    exact hH (by dsimp only; rw [actualCongruenceCoefficient_zero_frequency S hS hSne A s hA hs hcop,zero_mul])
  exact ⟨⟨H,hn⟩,rfl⟩

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1373

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RadialSpectral
Source SHA256: f5ee7a76bdb3d0a9208ff86c785cd3671dcb342ddd0fc8f7da4358f796072332
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1374



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma spectralSummand_mask_nonzero (S : Finset Id) (D I J : Id) (Ψ : O→*ℂ) (t : ℂ)
    (h : spectralSummand S D Ψ t I J≠0) : completedMask S D I J≠0 := by
  intro hz
  exact h (by simp only [spectralSummand,hz,zero_mul])

lemma spectralSummand_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D I J : Id) (Ψ : O→*ℂ) (t : ℂ) (h : spectralSummand S D Ψ t I J≠0) :
    IsCoprime (calibrationForSet S hS).generator (completedIndex I J) := by
  have hm := spectralSummand_mask_nonzero S D I J Ψ t h
  have hA : completedIndex I J≠0 := by
    intro hz
    exact h (spectralSummand_zero_completedIndex S D I J Ψ t hz)
  have hout : ∀P∈S,¬P∣I*J^3 := by
    unfold completedMask at hm
    split_ifs at hm with hd
    · exact hd.2
    · exact False.elim (hm rfl)
  apply calibrationForSet_coprime_of_excluded S hS
  rw [completedIndex_eq_primaryGenerator] at hA ⊢
  rw [(primaryGenerator_spec (I*J^3) hA).1]
  exact hout

def radialMellinSpectralTerm (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset Id) (D : Id) (s : O) (hs : Supported (Ideal.span {s}))
    (W : SchwartzMap ℝ ℂ) (K σ : ℝ) (t : ℂ) (I J : Id) : ℂ :=
  if hA : completedIndex I J≠0 then
    spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J *
      ((K/elementNorm (C.generator*completedIndex I J):ℝ):ℂ) *
      verticalIntegral σ (fun z=>∑'H : NonzeroFrequency,
        actualCongruenceCoefficient C (completedIndex I J) s hA H.val*
          ((K*elementNorm H.val/elementNorm ((C.generator*completedIndex I J)*s)):ℂ)^(-z)*
            mellin (paperRadialFourier W) z)
  else 0

theorem transformedSpectralTerm_radial_mellin (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty) (D : Id)
    (s : O) (hs : Supported (Ideal.span {s})) (hcs : IsCoprime (calibrationForSet S hS).generator s)
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W⊆Set.Icc a b)
    (K σ : ℝ) (hK : 0<K) (hσ : 1<σ) (t : ℂ) (I J : Id) :
    transformedSpectralTerm η (calibrationForSet S hS) S D s hs W K t I J=
      radialMellinSpectralTerm η (calibrationForSet S hS) S D s hs W K σ t I J := by
  unfold transformedSpectralTerm radialMellinSpectralTerm
  split_ifs with hA
  · by_cases hz : spectralSummand S D (baseRowCoefficient η (calibrationForSet S hS).Xi s hs) t I J=0
    · simp only [hz,zero_mul]
    · rw [actualFrequency_mellin S hS hSne (completedIndex I J) s hA (supportedElement_ne_zero s hs)
        ((spectralSummand_calibration_coprime S hS D I J _ t hz).mul_right hcs)
        W a b ha hW K hK σ hσ]
  · rfl

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1374

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalRadial
Source SHA256: 5618ad5c655abca16647c176857d4fcb169e206186ef0559d837a7b815c440d4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1375



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

def radialMellinPhysicalProbe (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ) (X Y Z σ : ℝ) : ℂ :=
  (Y:ℂ)⁻¹*∑'s : {I : Ideal O // Supported I},
    if ∀P∈C.excluded,¬P∣s.val then
      let a := primaryGenerator s.val
      let has := (supported_span_primaryGenerator_iff s.val).mpr s.property
      let qs : ℝ := Ideal.absNorm s.val
      W1 (qs/Y)*CanonicalRowCompletion.idealRowHom C.generator s.val /
        (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*qs*X):ℂ))*
      verticalIntegral 4 (fun t=>(Real.sqrt qs:ℂ)⁻¹*((Z:ℂ)^t*Complex.exp (t^2))*
        ∑'p : Ideal O×Ideal O,radialMellinSpectralTerm η C C.excluded D a has W0
          (elementNorm C.generator*qs*X) σ t p.1 p.2)
    else 0

theorem markedPhysicalProbe_eq_radial_mellin (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hSne : S.Nonempty)
    (D : Ideal O) (W0 : SchwartzMap ℝ ℂ) (W1 : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Set.Icc a b)
    (X Y Z σ : ℝ) (hX : 0<X) (hZ : 0<Z) (hσ : 1<σ) :
    markedPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z=
      radialMellinPhysicalProbe η (calibrationForSet S hS) D W0 W1 X Y Z σ := by
  have hWc : HasCompactSupport (W0 : ℝ→ℂ) := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW
  rw [markedPhysicalProbe_eq_poisson η (calibrationForSet S hS) D W0 W1 hWc (W0.smooth (⊤:ℕ∞)) X Y Z hX hZ]
  unfold poissonPhysicalProbe radialMellinPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with hs
  · dsimp only
    congr 1
    unfold verticalIntegral
    congr 1
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    congr 1
    apply tsum_congr
    intro p
    have hcs : IsCoprime (calibrationForSet S hS).generator (primaryGenerator s.val) := by
      apply calibrationForSet_coprime_of_excluded S hS
      rw [(primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1]
      simpa only [calibrationForSet_excluded] using hs
    have hK : 0<elementNorm (calibrationForSet S hS).generator*(Ideal.absNorm s.val:ℝ)*X :=
      mul_pos (mul_pos (elementNorm_pos _ (calibrationForSet S hS).generator_ne_zero)
        (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1))) hX
    simpa only [calibrationForSet_excluded] using transformedSpectralTerm_radial_mellin η S hS hSne D
      (primaryGenerator s.val) ((supported_span_primaryGenerator_iff s.val).mpr s.property) hcs
      W0 a b ha hW _ σ hK hσ _ p.1 p.2
  · rfl

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1375

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SixthDecomposition
Source SHA256: 9b03e1100a886fef891e79e664b2c895699f7eab0389b6c1e10a77334870ff90
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1376




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ActualEisensteinCubic HeckeInverseAmplification CenteredExceptionalCount ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem sixthRow_surjective (H : NonzeroFrequency) :
    ∃p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,rowMap p=H.val := by
  let I : Id := Ideal.span {H.val}
  have hI : I≠0 := Ideal.span_singleton_eq_bot.not.mpr H.property
  let J : Id := sixthQuotient I
  have hJ : J≠0 := sixthQuotient_ne_zero I
  let a := idealGenerator J
  have ha : a≠0 := idealGenerator_ne_zero J hJ
  have hspan : Ideal.span {a}=J := span_idealGenerator J
  have hd : a^6∣H.val := by
    apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
    rw [←Ideal.span_singleton_pow,hspan]
    change J^6∣I
    rw [←sixth_normal_form I hI]
    exact dvd_mul_left _ _
  obtain ⟨u,hu⟩ := hd
  have hu0 : u≠0 := by
    intro hz
    rw [hz,mul_zero] at hu
    exact H.property hu
  have hsu : Ideal.span {u}=sixthRemainder I := by
    have hi : Ideal.span {u}*J^6=I := by
      rw [←hspan,Ideal.span_singleton_pow,Ideal.span_singleton_mul_span_singleton]
      exact congrArg (fun b : O=>Ideal.span {b}) (by simpa only [mul_comm] using hu.symm)
    apply mul_right_cancel₀ (pow_ne_zero 6 hJ)
    exact hi.trans (sixth_normal_form I hI).symm
  have hf : SixthFree (Ideal.span {u}) := by
    rw [hsu]
    intro P
    exact sixthRemainder_valuation_lt I P
  refine ⟨(⟨u,hu0,hf⟩,⟨J,hJ⟩),?_⟩
  change u*a^6=H.val
  simpa only [mul_comm] using hu.symm

def sixthFrequencyEquiv : FreeRow×HeckeInverseAmplification.NonzeroIdeal ≃ NonzeroFrequency :=
  Equiv.ofBijective (fun p=>⟨rowMap p,rowMap_ne_zero p⟩) ⟨
    fun p q h=>rowMap_injective (congrArg Subtype.val h),
    fun H=>by obtain ⟨p,hp⟩ := sixthRow_surjective H;exact ⟨p,Subtype.ext hp⟩⟩

lemma sixthFrequencyEquiv_apply (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) :
    (sixthFrequencyEquiv p).val=p.1.val*(idealGenerator p.2.val)^6 := rfl

theorem tsum_sixth_decomposition (f : NonzeroFrequency→ℂ) :
    (∑'H : NonzeroFrequency,f H)=
      ∑'p : FreeRow×HeckeInverseAmplification.NonzeroIdeal,f (sixthFrequencyEquiv p) :=
  (sixthFrequencyEquiv.tsum_eq f).symm

lemma idealGenerator_sixth_eq_primary (I : Id) (hI : CanonicalQuadraticSieve.Supported I) :
    (idealGenerator I)^6=(CompletedGauss.primaryGenerator I)^6 := by
  have he : Ideal.span {idealGenerator I}=Ideal.span {CompletedGauss.primaryGenerator I} :=
    (span_idealGenerator I).trans
      (CompletedGauss.primaryGenerator_spec I
        (supported_primaryGenerator_ne_zero I hI)).1.symm
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp he
  have hh := congrArg (fun a : O=>a^6) hu
  simpa only [mul_pow,CanonicalUnitEuler.unit_pow_six,mul_one] using hh

lemma sixthFrequencyEquiv_primary (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal)
    (hP : CanonicalQuadraticSieve.Supported p.2.val) :
    (sixthFrequencyEquiv p).val=p.1.val*(CompletedGauss.primaryGenerator p.2.val)^6 := by
  rw [sixthFrequencyEquiv_apply,idealGenerator_sixth_eq_primary p.2.val hP]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1376

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SourcePrime
Source SHA256: dcbeb867b568cf4da52fd647b502cc23f6ede73808f48f7fe34b3a93e3e9fe39
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1377



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CubicEisenstein ConcreteTraceCRT
open ProbePhase ProbeEuler ProbePrimePower FiniteGaussPhase QuadraticGaussRay
local notation "O" => ActualEisensteinCubic.O

theorem gaussTwo_prime_localGamma (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hprimary : goodLambda^2∣p-1) (hI : primaryGenerator (Ideal.span {p})≠0) :
    gaussTwo (Ideal.span {p}) hI=localGamma p hp.ne_zero hg 2 := by
  let pp : Unit→O := fun _=>p
  have hpp : ∀i,pp i≠0 := fun _=>hp.ne_zero
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hi : primaryGenerator (Ideal.span {∏i,pp i})≠0 := by simpa [pp] using hI
  have he := gaussTwo_eq_canonicalProductGauss pp hpp hcop (fun _=>hg) (fun _=>hprimary) hi
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 2)] at he
  simpa [pp,localGamma,ConcreteBreveE.normalizedTraceGauss] using he

theorem G_prime_localG (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1) :
    G p=MixedGaussConversion.localG p hp hg := by
  let pp : Unit→O := fun _=>p
  have hpp : ∀i,pp i≠0 := fun _=>hp
  have hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have he := canonicalProductG_eq_fixedGValue pp hpp hcop (fun _=>hg)
    (fun _=>hchar) (fun _=>hprimary)
  unfold canonicalProductG at he
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 3)] at he
  simpa [pp,G,fixedGQuotientValue,MixedGaussConversion.localG,breveLocalG,breveGamma3,
    ConcreteBreveE.normalizedTraceGauss] using he.symm

theorem localGamma_one_two_full_signal (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1) :
    localGamma p hp hg 1 * localGamma p hp hg 2 =
      -FiniteGaussPhase.angularFactor p * G p := by
  rw [G_prime_localG p hp hg hchar hprimary]
  exact localGamma_one_two_signal p hp hg hchar hprimary

lemma angularFactor_pow (p : O) (n : ℕ) : angularFactor (p^n)=angularFactor p^n := by
  simp only [angularFactor,map_pow,norm_pow,Complex.ofReal_pow,div_pow]

lemma gaussTwo_one : gaussTwo (1:Ideal O) (by rw [primaryGenerator_one]; exact one_ne_zero)=1 := by
  have hI : CubicSieve.Admissible (1:Ideal O) := ⟨squarefree_one,by rw [primaryGenerator_one]; exact one_ne_zero⟩
  rw [gaussTwo_eq_elementFourier (1:Ideal O) hI]
  simp only [primaryGenerator_one,map_one,norm_one,Complex.ofReal_one,div_one]
  have hrow (a : O) : CubicSieve.cubicRow (1:Ideal O) a=1 := by
    rw [CubicSieve.cubicRow,←idealRowHom_square,map_one,one_pow]
  rw [show CubicSieve.cubicRow (1:Ideal O)=(fun _=>1) from funext hrow]
  have he : elementFourier 1 one_ne_zero (fun _=>1) 1=sexticGauss 1 one_ne_zero 1 := by
    unfold elementFourier sexticGauss
    apply tsum_congr
    intro x
    simp only [Ideal.span_singleton_one,←Ideal.one_eq_top,map_one,one_mul]
  rw [he,sexticGauss_one]

lemma gaussTwo_prime_power_small (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hprimary : goodLambda^2∣p-1) (e : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    gaussTwo (Ideal.span {p^e}) hI=localGamma p hp.ne_zero hg 2^e := by
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero,Ideal.span_singleton_one,←Ideal.one_eq_top] using gaussTwo_one
  · have hi : primaryGenerator (Ideal.span {p})≠0 := by simpa only [pow_one] using hI
    simpa only [pow_one] using gaussTwo_prime_localGamma p hp hg hprimary hi

lemma corrected_prime_cubic_signal (p : O) (hp : p≠0)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) :
    localGamma p hp hg 2 * star (angularFactor p) * star (G p) = -(localGamma p hp hg 1)⁻¹ := by
  have hsig := localGamma_one_two_full_signal p hp hg hchar hprimary
  have hn := localGamma_norm_one p hp hg hchar 1 (by decide) (by decide)
  have hne : localGamma p hp hg 1≠0 := by intro h; rw [h,norm_zero] at hn; norm_num at hn
  have hG : G p*star (G p)=1 := by
    rw [mul_comm]
    exact G_conjugate_cancel p (supported_residue_odd p hs)
      (cubicTwo_isUnit_of_odd p (supported_residue_odd p hs))
  apply mul_left_cancel₀ hne
  calc
    _ = (localGamma p hp hg 1*localGamma p hp hg 2)*star (angularFactor p)*star (G p) := by ring
    _ = -1 := by
      rw [hsig]
      calc
        _ = -(angularFactor p*star (angularFactor p))*(G p*star (G p)) := by ring
        _ = _ := by rw [angularFactor_mul_star p hp,hG]; ring
    _ = _ := by rw [mul_neg,mul_inv_cancel₀ hne]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1377

/-! Original module: OAI.NumberTheory.DirichletL.Detector.IdealUnit
Source SHA256: 9e945bfd6f13795198085de4a9bbfa9b4ac50070b3a2fbe511ad5f33b90d9746
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1378



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CubicEisenstein ProbePhase ConcretePrimeRowBridge ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma supported_one_ideal : Supported (1 : Ideal O) := by
  refine ⟨one_ne_zero,?_⟩
  intro P hP
  simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP

lemma G_one : G (1:O)=1 := by
  have hs : Supported (Ideal.span {(1:O)}) := by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top]
    exact supported_one_ideal
  have ho := supported_residue_odd (1:O) hs
  have hn : G (1:O)≠0 := by
    intro hz
    have hh := G_norm_one_of_odd (1:O) ho
    rw [hz,norm_zero] at hh
    norm_num at hh
  have he := G_mul (1:O) 1 ho ho
  rw [one_mul,reciprocitySign_one_left (1:O) ho,mul_one] at he
  exact mul_left_cancel₀ hn (by simpa only [mul_one] using he.symm)

lemma angularFactor_one : FiniteGaussPhase.angularFactor (1:O)=1 := by
  simp only [FiniteGaussPhase.angularFactor,map_one,norm_one,Complex.ofReal_one,div_one]

@[simp] theorem bareIdealHighCoefficient_one (η : HeckeFamily.Character) :
    bareIdealHighCoefficient η 1 1 1 1 1=1 := by
  have hs := supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hg]
  simp only [primaryGenerator_one,one_pow,one_mul]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,G_one,angularFactor_one]
  have ho := supported_residue_odd (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_one (η : HeckeFamily.Character) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_one,hw,one_mul]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1378

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighValuations
Source SHA256: f5665ad6b57bb64680b003724c20a72c757ed0806a90f8d140e5f161de1c2369
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1379



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev HighIdeal := (Id×Id)×(Id×Id)

def highIdeals (v : PrimeIdeal→₀HighValuation) : HighIdeal :=
  ((idealFromValuations (v.mapRange (fun b=>b.1.1) rfl),
    idealFromValuations (v.mapRange (fun b=>b.1.2) rfl)),
   (idealFromValuations (v.mapRange (fun b=>b.2.1) rfl),
    idealFromValuations (v.mapRange (fun b=>b.2.2) rfl)))

lemma highIdeals_eq_equiv (v : PrimeIdeal→₀HighValuation) :
    highIdeals v =
      (((highValuationEquiv.symm v).1.1.val,(highValuationEquiv.symm v).1.2.val),
       ((highValuationEquiv.symm v).2.1.val,(highValuationEquiv.symm v).2.2.val)) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    apply congrArg idealFromValuations
    ext P
    rfl

lemma highIdeals_injective : Function.Injective highIdeals := by
  intro v w h
  apply highValuationEquiv.symm.injective
  rw [highIdeals_eq_equiv,highIdeals_eq_equiv] at h
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.1.1) h)
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.1.2) h)
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.2.1) h)
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.2.2) h)

lemma highIdeals_zero : highIdeals 0=1 := by
  simp only [highIdeals,Finsupp.mapRange_zero,idealFromValuations_zero]
  rfl

lemma highIdeals_single (P : PrimeIdeal) (b : HighValuation) :
    highIdeals (Finsupp.single P b)=((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2)) := by
  simp only [highIdeals,Finsupp.mapRange_single,idealFromValuations_single]

lemma highIdeals_add (v w : PrimeIdeal→₀HighValuation) :
    highIdeals (v+w)=highIdeals v*highIdeals w := by
  have hproj (f : HighValuation→ℕ) (hf0 : f 0=0) (hf : ∀a b,f (a+b)=f a+f b) :
      (v+w).mapRange f hf0=v.mapRange f hf0+w.mapRange f hf0 := by
    ext P
    simp only [Finsupp.mapRange_apply,Finsupp.add_apply,hf]
  simp only [highIdeals,hproj (fun b=>b.1.1) rfl (fun _ _=>rfl),
    hproj (fun b=>b.1.2) rfl (fun _ _=>rfl),hproj (fun b=>b.2.1) rfl (fun _ _=>rfl),
    hproj (fun b=>b.2.2) rfl (fun _ _=>rfl),idealFromValuations_add]
  rfl

lemma prime_coprime_highIdeals (P : PrimeIdeal) (v : PrimeIdeal→₀HighValuation)
    (hv : v P=0) : IsCoprime P.val
      ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) := by
  have hc (f : HighValuation→ℕ) (hf0 : f 0=0) :
      IsCoprime P.val (idealFromValuations (v.mapRange f hf0)) := by
    apply prime_coprime_idealFromValuations
    simp only [Finsupp.mapRange_apply,hv,hf0]
  exact ((hc _ rfl).mul_right (hc _ rfl)).mul_right (hc _ rfl) |>.mul_right (hc _ rfl)

def highValuationTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (highIdeals v).1.1 (highIdeals v).1.2
    (highIdeals v).2.1 (highIdeals v).2.2

def highPrimeTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

lemma highPrimeTerm_zero (η : HeckeFamily.Character) (x w z : ℂ) (P : PrimeIdeal) :
    highPrimeTerm η x w z P 0=1 := by
  simp only [highPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_one]

theorem highValuationTerm_eq_prod (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) :
    highValuationTerm η x w z v=v.prod (highPrimeTerm η x w z) := by
  induction v using Finsupp.induction with
  | zero =>
    simp only [highValuationTerm,highIdeals_zero,Prod.fst_one,Prod.snd_one,
      bareIdealHighSummand_one,Finsupp.prod_zero_index]
  | @single_add P b v hP hb ih =>
    have hv : v P=0 := Finsupp.notMem_support_iff.mp hP
    have hc := prime_coprime_highIdeals P v hv
    have hpow : IsCoprime (P.val^b.1.1*P.val^b.1.2*P.val^b.2.1*P.val^b.2.2)
        ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) :=
      ((hc.pow_left.mul_left hc.pow_left).mul_left hc.pow_left).mul_left hc.pow_left
    have hd : Disjoint (Finsupp.single P b).support v.support := by
      rw [Finsupp.support_single _ hb]
      exact Finset.disjoint_singleton_left.mpr hP
    rw [Finsupp.prod_add_index_of_disjoint hd,Finsupp.prod_single_index (highPrimeTerm_zero η x w z P),←ih]
    unfold highValuationTerm
    rw [highIdeals_add,highIdeals_single]
    exact bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hpow

theorem highValuationTerm_summable_norm (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun v : PrimeIdeal→₀HighValuation=>‖highValuationTerm η x w z v‖) :=
  (bareIdealHighSummand_summable η 1 x w z hx hw hz).norm.comp_injective highIdeals_injective

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1379

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SourcePrimeFactor
Source SHA256: 82d75a913c0811c2adb2f9328315efb2d782fc605a2b0a42384dcbd33cf13ba4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1380


namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareSourceCoefficient_prime_formula (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k j : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^j) =
    (-1:ℂ)^e * ((localGamma p hp.ne_zero hg 1)⁻¹)^e * (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3 * (targetMonoid η p)^3 *
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
  have ho := supported_residue_odd p hs
  have hself := reciprocitySign_self_eq_sextic_neg_one p hp.ne_zero hg hchar ho
  have hstar : star (actualSextic (Ideal.span {p}) hg (-1))=
      actualSextic (Ideal.span {p}) hg (-1) := by
    rw [←hself,reciprocitySign_star]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_prime_power_small p hp hg hprimary e he hI,
    bareCongruenceCoefficient_all_prime_powers p hp hg,
    angularFactor_pow,map_pow,
    G_completed_prime_power p ho e l he,
    G_cube_eq_normalizedTraceGauss p hp.ne_zero hg hchar ho,
    reciprocitySign_pow_left p _ (odd_residue_pow p ho k),reciprocitySign_pow_right p p ho,
    hself]
  change _ = _
  simp only [star_mul,star_pow,hstar]
  change (targetMonoid η p)^(e+3*l) * star (FiniteGaussPhase.angularFactor p)^(e+3*l) *
    (localGamma p hp.ne_zero hg 2^e *
      ((actualSextic (Ideal.span {p}) hg (-1))^(e*l+l.choose 2) *
        (star (localGamma p hp.ne_zero hg 3)^l * star (G p)^e)) *
      (((actualSextic (Ideal.span {p}) hg (-1))^k)^(e+3*l) *
        sourceScalar p hp hg (e+3*l) k j)) = _
  calc
    _ = (localGamma p hp.ne_zero hg 2 * star (FiniteGaussPhase.angularFactor p) * star (G p))^e *
      (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j := by
        simp only [pow_add,pow_mul,mul_pow]
        ring
    _ = _ := by
      rw [corrected_prime_cubic_signal p hp.ne_zero hg hchar hprimary hs]
      rw [neg_eq_neg_one_mul ((localGamma p hp.ne_zero hg 1)⁻¹),mul_pow]

theorem bareSourceCoefficient_weighted_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) (x w z : ℂ) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (p^(6*m)) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  rw [bareSourceCoefficient_prime_formula η p hp hg hchar hprimary hs e l k (6*m) he hI]
  unfold sourcePrincipalTerm sourceWeightedScalar
  simp only [zpow_neg,zpow_natCast,←inv_pow,Complex.ofReal_natCast]
  have hpdiag := source_signed_phase
    (actualACube η p*star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) (actualSextic_neg_one_sq _ hg) e l k
  simp only [localCubePhase] at hpdiag
  have ha : actualACube η p=
      star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3 := rfl
  rw [ha] at hpdiag ⊢
  calc
    _ = ((-1:ℂ)^e*((localGamma p hp.ne_zero hg 1)⁻¹)^e*(targetMonoid η p)^e) *
      ((star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3*
        star (localGamma p hp.ne_zero hg 3))^l *
        (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2)) *
      sourceScalar p hp hg (e+3*l) k (6*m) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by ring
    _ = _ := by rw [←hpdiag]; ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1380

/-! Original module: OAI.NumberTheory.DirichletL.Detector.IdealLocalEuler
Source SHA256: 01fd17bb0c9ac3e39734d4811083462a7fc8490e04561b16799ae9e3d4556f74
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1381




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

lemma primaryGenerator_prime_power (p : O) (hp : p≠0) (hprimary : goodLambda^2∣p-1) (e : ℕ) :
    primaryGenerator ((Ideal.span {p})^e)=p^e := by
  rw [primaryGenerator_pow,primaryGenerator_span p hp hprimary]

lemma prime_power_small_squarefree (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (e : ℕ) (he : e≤1) :
    Squarefree ((Ideal.span {p})^e) := by
  have hP : Prime (Ideal.span {p}:Ideal O) :=
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero) inferInstance
  have hcases : e=0 ∨ e=1 := by omega
  rcases hcases with rfl|rfl
  · simpa only [pow_zero] using (squarefree_one : Squarefree (1:Ideal O))
  · simpa only [pow_one] using hP.squarefree

theorem bareIdealHighCoefficient_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η 1 ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hguard]
  simp only [primaryGenerator_prime_power p hp.ne_zero hprimary,one_mul]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

lemma fullIdealWeight_power (s : ℂ) (I : Ideal O) (n : ℕ) :
    fullIdealWeight s (I^n)=fullIdealWeight s I^n := (IdealEuler.normWeight s).map_pow I n

lemma prime_spectral_weights (p : O) (hp : p≠0) (e l k m : ℕ) (x w z : ℂ) :
    fullIdealWeight (x+1/2) ((Ideal.span {p})^e) *
      fullIdealWeight (1+3*x) ((Ideal.span {p})^l) *
      fullIdealWeight w ((Ideal.span {p})^k) * fullIdealWeight (6*z) ((Ideal.span {p})^m) =
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) := by
  have hI : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  have hQ : (Ideal.absNorm (Ideal.span {p}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hI
  simp only [fullIdealWeight_power]
  simp only [fullIdealWeight,ite_eq_right hI]
  rw [←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,←Complex.cpow_mul_nat,
    ←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ,←Complex.cpow_add _ _ hQ]
  congr 1
  ring

theorem bareIdealHighSummand_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η 1 x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    sourcePrincipalTerm p hp hg (targetMonoid η p) (actualACube η p) x w z e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_at_prime η p hp hprimary hs e l k m he]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_weighted_prime η p hp hg hchar hprimary hs e l k m he _ x w z

def idealHighLocalFactor (η : HeckeFamily.Character) (P : Ideal O) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l, ∑' k, ∑' m,
    bareIdealHighSummand η 1 x w z (P^e.val) (P^l) (P^k) (P^m)

theorem idealHighLocalFactor_eq_source (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ) :
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z := by
  unfold idealHighLocalFactor sourcePrincipalSeries
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_at_prime η p hp hg hchar hprimary hs e.val l k m (by omega) x w z

theorem idealHighLocalFactor_euler_identity (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      (1-coordD Q (targetMonoid η p) 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q ((actualACube η p)^2) (targetMonoid η p) 1 x w z := by
  rw [idealHighLocalFactor_eq_source η p hp hg hchar hprimary hs]
  exact sourcePrincipalSeries_euler_identity p hp hg hchar _ _ x w z hV hR hW hD

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1381

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighEuler
Source SHA256: 86ca26f94a71e214d4361ddbd80ca5e83bdff37b592dac93b1eac03a6b584c32
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1382




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma bareIdealHighSummand_support (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (I J K L : Id) (h : bareIdealHighSummand η u x w z I J K L≠0) :
    highSupport I J K L := by
  by_contra hn
  apply h
  unfold highSupport at hn
  simp only [bareIdealHighSummand,bareIdealHighCoefficient,dite_eq_right hn,zero_mul]

theorem highValuationTerm_tsum_eq (η : HeckeFamily.Character) (x w z : ℂ) :
    (∑'v : PrimeIdeal→₀HighValuation,highValuationTerm η x w z v)=
      bareIdealHighSeries η 1 x w z := by
  unfold highValuationTerm bareIdealHighSeries
  apply highIdeals_injective.tsum_eq (f:=fun a : HighIdeal=>
    bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
  intro a ha
  have hs := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
  let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
    ((⟨a.1.1,hs.2.1.1⟩,⟨a.1.2,hs.2.2.1.1⟩),
      (⟨a.2.1,hs.2.2.2.1.1⟩,⟨a.2.2,hs.2.2.2.2.1⟩))
  refine ⟨highValuationEquiv b,?_⟩
  rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]

theorem bareIdealHighSeries_hasProd (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,highPrimeTerm η x w z P b)
      (bareIdealHighSeries η 1 x w z) := by
  have hs := highValuationTerm_summable_norm η x w z hx hw hz
  simp only [highValuationTerm_eq_prod] at hs
  have he := ProbeEulerFinsupp.hasProd_of_summable (highPrimeTerm η x w z)
    (highPrimeTerm_zero η x w z) hs
  simpa only [←highValuationTerm_eq_prod,highValuationTerm_tsum_eq] using he

theorem bareIdealHighSeries_eq_tprod (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    bareIdealHighSeries η 1 x w z =
      ∏' P : PrimeIdeal,∑' b : HighValuation,highPrimeTerm η x w z P b :=
  (bareIdealHighSeries_hasProd η x w z hx hw hz).tprod_eq.symm

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1382

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighEulerGeneral
Source SHA256: 32bb464b6df128eb31f45538e068cf6da905a15eab738f3e34cad41f1e9b50cc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1383


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highArray_val_prod (F : HighIdeal→ℂ) (h1 : F 1=1)
    (hmul : ∀ a b : HighIdeal,
      IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2) → F (a*b)=F a*F b)
    (v : PrimeIdeal→₀HighValuation) :
    F (highIdeals v)=v.prod (fun P b=>F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) := by
  have hzero (P : PrimeIdeal) : F ((P.val^0,P.val^0),(P.val^0,P.val^0))=1 := by
    simp only [pow_zero]
    change F (1 : HighIdeal)=1
    exact h1
  induction v using Finsupp.induction with
  | zero => simp only [highIdeals_zero,h1,Finsupp.prod_zero_index]
  | @single_add P b v hP hb ih =>
    have hc := prime_coprime_highIdeals P v (Finsupp.notMem_support_iff.mp hP)
    have hpow : IsCoprime (P.val^b.1.1*P.val^b.1.2*P.val^b.2.1*P.val^b.2.2)
        ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) :=
      ((hc.pow_left.mul_left hc.pow_left).mul_left hc.pow_left).mul_left hc.pow_left
    have hd : Disjoint (Finsupp.single P b).support v.support := by
      rw [Finsupp.support_single _ hb]
      exact Finset.disjoint_singleton_left.mpr hP
    rw [Finsupp.prod_add_index_of_disjoint hd,Finsupp.prod_single_index (hzero P),←ih,
      highIdeals_add,highIdeals_single]
    exact hmul _ _ hpow

theorem highArray_hasProd (F : HighIdeal→ℂ) (h1 : F 1=1)
    (hmul : ∀ a b : HighIdeal,
      IsCoprime (a.1.1*a.1.2*a.2.1*a.2.2) (b.1.1*b.1.2*b.2.1*b.2.2) → F (a*b)=F a*F b)
    (hzero : ∀ a : HighIdeal,F a≠0 → a.1.1≠0 ∧ a.1.2≠0 ∧ a.2.1≠0 ∧ a.2.2≠0)
    (hs : Summable (fun a=>‖F a‖)) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) (∑' a,F a) := by
  have hv := hs.comp_injective highIdeals_injective
  have hp := highArray_val_prod F h1 hmul
  simp only [Function.comp_def,hp] at hv
  have hlocal (P : PrimeIdeal) : F ((P.val^0,P.val^0),(P.val^0,P.val^0))=1 := by
    simp only [pow_zero]
    change F (1 : HighIdeal)=1
    exact h1
  have he := ProbeEulerFinsupp.hasProd_of_summable
    (fun (P : PrimeIdeal) (b : HighValuation)=>F ((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2))) hlocal hv
  have hsum : (∑' v : PrimeIdeal→₀HighValuation,F (highIdeals v))=∑' a,F a := by
    apply highIdeals_injective.tsum_eq
    intro a ha
    have hn := hzero a ha
    let b : (NonzeroIdeal×NonzeroIdeal)×(NonzeroIdeal×NonzeroIdeal) :=
      ((⟨a.1.1,hn.1⟩,⟨a.1.2,hn.2.1⟩),(⟨a.2.1,hn.2.2.1⟩,⟨a.2.2,hn.2.2.2⟩))
    refine ⟨highValuationEquiv b,?_⟩
    rw [highIdeals_eq_equiv,highValuationEquiv.symm_apply_apply]
  simpa only [←hp,hsum] using he

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1383

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighEulerLocal
Source SHA256: 0cb562c7600fc508281e4b5bf04c8b06797f1e46d17a4f80e125f1440778fb18
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1384


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highPrimeTerm_summable_norm (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    Summable (fun b : HighValuation=>‖highPrimeTerm η x w z P b‖) := by
  have hs := (highValuationTerm_summable_norm η x w z hx hw hz).comp_injective
    (Finsupp.single_injective P)
  simpa only [Function.comp_def,highValuationTerm_eq_prod,
    Finsupp.prod_single_index (highPrimeTerm_zero η x w z P)] using hs

lemma highPrimeTerm_zero_of_two_le (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (e l k m : ℕ) (he : 2≤e) :
    highPrimeTerm η x w z P ((e,l),(k,m))=0 := by
  by_contra hn
  have hs := bareIdealHighSummand_support η 1 x w z (P.val^e) (P.val^l) (P.val^k) (P.val^m) hn
  have hc := hs.1.eq_zero_or_one_of_pow_of_not_isUnit P.property.not_isUnit
  omega

theorem highPrimeTerm_tsum_eq_localFactor (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,highPrimeTerm η x w z P b)=
      idealHighLocalFactor η P.val x w z := by
  have hs := (highPrimeTerm_summable_norm η x w z hx hw hz P).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) :
      (∑' b : ℕ×ℕ, highPrimeTerm η x w z P ((e,l),b))=
        ∑' k,∑' m,highPrimeTerm η x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [highPrimeTerm_zero_of_two_le η x w z P e _ _ _ hh,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

theorem bareIdealHighSeries_hasProd_localFactor (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>idealHighLocalFactor η P.val x w z)
      (bareIdealHighSeries η 1 x w z) := by
  have h := bareIdealHighSeries_hasProd η x w z hx hw hz
  simpa only [highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz] using h

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1384

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighEulerRational
Source SHA256: 9b8177391e39881163f87443b6de514fbf0c807cbd9ce6383bf93c049b4e1507
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1385



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma supported_primeGenerator_prime (P : PrimeIdeal) (hs : Supported P.val) :
    Prime (primaryGenerator P.val) := by
  apply (Ideal.span_singleton_prime (supported_primaryGenerator_ne_zero P.val hs)).mp
  rw [span_primaryGenerator_of_supported P.val hs]
  exact Ideal.isPrime_of_prime P.property

lemma targetMonoid_primaryGenerator (η : HeckeFamily.Character) (I : Ideal O) (hs : Supported I) :
    targetMonoid η (primaryGenerator I)=HeckeFamily.idealCoeff η I := by
  calc
    _ = HeckeFamily.idealCoeff η (Ideal.span {primaryGenerator I}) :=
      (HeckeFamily.idealCoeff_span η (supported_primaryGenerator_ne_zero I hs)).symm
    _ = _ := by rw [span_primaryGenerator_of_supported I hs]

def idealClosedCorrection (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
    (HeckeFamily.idealCoeff η P.val) 1 x w z

theorem idealHighLocalFactor_rational (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm P.val
    idealHighLocalFactor η P.val x w z =
      (1-HeckeFamily.idealCoeff η P.val*(Q:ℂ)^(-x)) /
        ((1-(Q:ℂ)^(-6*z))*(1-(Q:ℂ)^(-w))) * idealClosedCorrection η P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    rw [hspan]
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) ((actualACube η p)^2) x z‖<1 := by
    rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1 := by
    apply (coordW_norm_le _ hQ0 1 w (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hDnorm : ‖coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x‖<1 := by
    apply (coordD_norm_le _ hQ0 _ 1 x (targetMonoid_norm_le_one η p) (by simp)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  have hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x≠0 := by
    intro he
    have hh : coordD (Ideal.absNorm (Ideal.span {p})) (targetMonoid η p) 1 x=1 := (sub_eq_zero.mp he).symm
    rw [hh,norm_one] at hDnorm
    exact lt_irrefl _ hDnorm
  have he := idealHighLocalFactor_euler_identity η p hp hg.1 hg.2 hprimary hsp x w z hV hR hW hD
  dsimp only at he ⊢
  rw [hspan,actualACube_sq,targetMonoid_primaryGenerator η P.val hs] at he
  simpa only [coordD,coordV,coordW,star_one,mul_one,one_mul,idealClosedCorrection,p] using he

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1385

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GlobalCorrection
Source SHA256: 93fe6f7968ef080b15cfe60b0f007948c6acee2949a8d8f8cce83e8ca2cb49a6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1386





namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def globalPrimeDefectBound (P : PrimeIdeal) : ℝ :=
  240*(Ideal.absNorm P.val:ℝ)^(-(17/10:ℝ))

def globalClosedCorrection (η : HeckeFamily.Character) (S : Finset Id) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},idealClosedCorrection η P.val x w z

lemma globalPrimeDefectBound_nonneg (P : PrimeIdeal) : 0≤globalPrimeDefectBound P := by
  unfold globalPrimeDefectBound
  positivity

lemma globalPrimeDefectBound_summable : Summable globalPrimeDefectBound := by
  have h := (CubicEisenstein.fullIdealWeight_summable_norm ((17/10:ℝ):ℂ) (by norm_num)).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight ((17/10:ℝ):ℂ) P.val‖=globalPrimeDefectBound P
  unfold globalPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

structure CorrectionTail (S : Finset Id) : Prop where
  norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤Ideal.absNorm P.val
  small : (∑' P : {P : PrimeIdeal // P.val∉S},globalPrimeDefectBound P.val)≤1/6

lemma CorrectionTail.summable {S : Finset Id} (_h : CorrectionTail S) :
    Summable (fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val) :=
  globalPrimeDefectBound_summable.subtype _

lemma CorrectionTail.half {S : Finset Id} (h : CorrectionTail S)
    (P : {P : PrimeIdeal // P.val∉S}) : globalPrimeDefectBound P.val≤1/2 := by
  have hh := Summable.le_tsum h.summable P (fun Q _=>globalPrimeDefectBound_nonneg Q.val)
  linarith [h.small]

lemma idealClosedCorrection_bound (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4≤Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤globalPrimeDefectBound P := by
  apply unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=>idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 7/8≤x.re) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    Multipliable (fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : PrimeIdeal // P.val∉S}=>idealClosedCorrection η P.val x w z
  let B := fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤B P :=
    idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤w.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun x=>globalClosedCorrection η S x w z) {x : ℂ|7/8<x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 7/8≤x.re) (hz : 4/25≤z.re) :
    AnalyticOnNhd ℂ (fun w=>globalClosedCorrection η S x w z) {w : ℂ|9/10<w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 7/8≤x.re) (hw : 9/10≤w.re) :
    AnalyticOnNhd ℂ (fun z=>globalClosedCorrection η S x w z) {z : ℂ|4/25<z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

theorem globalClosedCorrection_principal (η : HeckeFamily.Character) (S : Finset Id)
    (hs : ∀P : PrimeIdeal,P.val∉S → CanonicalQuadraticSieve.Supported P.val) (x : ℂ) :
    globalClosedCorrection η S x 1 (1/6)=principalCorrection η S x := by
  apply tprod_congr
  intro P
  unfold idealClosedCorrection principalLocal
  rw [←targetMonoid_primaryGenerator η P.val.val (hs P.val P.property)]
  rfl

theorem exists_uniform_global_cutoff :
    ∃N : ℕ,4≤N ∧ ∀S : Finset Id,
      (∀P : PrimeIdeal,Ideal.absNorm P.val≤N → P.val∈S) → CorrectionTail S := by
  have ht := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero globalPrimeDefectBound)).2 (1/6) (by norm_num)
  obtain ⟨F,hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P=>Ideal.absNorm P.val))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS
  let T := {P : PrimeIdeal // P.val∉S}
  have hnot (P : T) : P.val∉F := by
    intro hm
    exact P.property (hS P.val ((Finset.le_sup (f:=fun P : PrimeIdeal=>Ideal.absNorm P.val) hm).trans (le_max_right _ _)))
  let inc : T→{P : PrimeIdeal // P∉F} := fun P=>⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun P : {P : PrimeIdeal // P∉F}=>P.val) h)
  constructor
  · intro P hP
    have hn : ¬Ideal.absNorm P.val≤N := fun hn=>hP (hS P hn)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hn))
  · apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _=>globalPrimeDefectBound_nonneg P.val) (fun _=>le_rfl)
      (globalPrimeDefectBound_summable.subtype _) (globalPrimeDefectBound_summable.subtype _)

theorem exists_global_correction (S₀ : Finset Id) :
    ∃S : Finset Id,S₀⊆S ∧ CorrectionTail S := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_global_cutoff
  refine ⟨S₀∪smallPrimeSet N,Finset.subset_union_left,hcut _ ?_⟩
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1386

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighExcludedEuler
Source SHA256: 0b11695c3a22d240125d20b2609f169d91b0feebaf1e6d086903a1b9038247f3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1387



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeCompleted CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma outside_mul (S : Finset Id) (hS : ∀P∈S,Prime P) (A B : Id) :
    (∀P∈S,¬P∣A*B) ↔ (∀P∈S,¬P∣A) ∧ (∀P∈S,¬P∣B) := by
  constructor
  · intro h
    constructor
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inl hd))
    · intro P hP hd
      exact h P hP ((hS P hP).dvd_mul.mpr (Or.inr hd))
  · rintro ⟨hA,hB⟩ P hP hd
    exact ((hS P hP).dvd_mul.mp hd).elim (hA P hP) (hB P hP)

lemma outside_cube (S : Finset Id) (hS : ∀P∈S,Prime P) (A : Id) :
    (∀P∈S,¬P∣A^3) ↔ ∀P∈S,¬P∣A := by
  constructor
  · intro h P hP hd
    exact h P hP (dvd_trans hd (dvd_pow_self A (by decide : (3:ℕ)≠0)))
  · intro h P hP hd
    exact h P hP ((hS P hP).dvd_of_dvd_pow hd)

def highExclusion (S : Finset Id) (hS : ∀P∈S,Prime P) : Id→*ℂ where
  toFun A := if ∀P∈S,¬P∣A then 1 else 0
  map_one' := by
    rw [ite_eq_left]
    intro P hP hd
    exact (hS P hP).not_isUnit (isUnit_of_dvd_one hd)
  map_mul' A B := by
    simp only [outside_mul S hS A B]
    split_ifs <;> simp_all

lemma highExclusion_cube (S : Finset Id) (hS : ∀P∈S,Prime P) (A : Id) :
    highExclusion S hS (A^3)=highExclusion S hS A := by
  change (if ∀P∈S,¬P∣A^3 then (1:ℂ) else 0)=_
  simp only [outside_cube S hS]
  rfl

theorem highIdealMask_unmarked (S : Finset Id) (hS : ∀P∈S,Prime P) (I J K L : Id) :
    highIdealMask S 1 I J K L =
      highExclusion S hS I*highExclusion S hS J*highExclusion S hS K*highExclusion S hS L := by
  have he : completedMask S 1 I J=highExclusion S hS (I*J^3) := by
    simp only [completedMask,one_dvd,true_and]
    rfl
  unfold highIdealMask
  rw [he,map_mul,highExclusion_cube]
  rfl

lemma highIdealMask_unmarked_one (S : Finset Id) (hS : ∀P∈S,Prime P) :
    highIdealMask S 1 1 1 1 1=1 := by
  rw [highIdealMask_unmarked S hS]
  simp only [map_one,one_mul]

lemma highIdealMask_unmarked_mul (S : Finset Id) (hS : ∀P∈S,Prime P)
    (a b : HighIdeal) :
    highIdealMask S 1 (a.1.1*b.1.1) (a.1.2*b.1.2) (a.2.1*b.2.1) (a.2.2*b.2.2)=
      highIdealMask S 1 a.1.1 a.1.2 a.2.1 a.2.2 * highIdealMask S 1 b.1.1 b.1.2 b.2.1 b.2.2 := by
  simp only [highIdealMask_unmarked S hS,map_mul]
  ring

theorem excludedIdealHighSeries_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η 1 x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>markedIdealHighSummand S 1 η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · simp only [Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
      highIdealMask_unmarked_one S hS,bareIdealHighSummand_one,one_mul]
  · intro a b hc
    simp only [Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
      highIdealMask_unmarked_mul S hS a b,
      bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hc]
    ring
  · intro a ha
    have hh : bareIdealHighSummand η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hs := bareIdealHighSummand_support η 1 x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (markedIdealHighSummand_summable S 1 η 1 x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1387

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighExcludedLocal
Source SHA256: 7351f907db305282a1ee41ce6c4ff427115535d30cce89552201c3d18fdc89ec
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1388



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma highExclusion_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    highExclusion S hS P.val=if P.val∈S then 0 else 1 := by
  change (if ∀Q∈S,¬Q∣P.val then (1:ℂ) else 0)=_
  by_cases hP : P.val∈S
  · rw [ite_eq_right (fun h=>h P.val hP (dvd_refl _)),ite_eq_left hP]
  · have houtside : ∀Q∈S,¬Q∣P.val := by
      intro Q hQ hd
      have hn : (⟨Q,hS Q hQ⟩ : PrimeIdeal)≠P := by
        intro hh
        exact hP ((congrArg Subtype.val hh) ▸ hQ)
      exact (hS Q hQ).not_isUnit ((primeIdeal_coprime ⟨Q,hS Q hQ⟩ P hn).isUnit_of_dvd hd)
    rw [ite_eq_left houtside,ite_eq_right hP]

lemma highIdealMask_prime_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (P : PrimeIdeal) (hP : P.val∉S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=1 := by
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,
    ite_eq_right hP,one_pow,one_mul]

lemma highIdealMask_prime_inside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (P : PrimeIdeal) (hP : P.val∈S) (b : HighValuation) :
    highIdealMask S 1 (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=
      if b=0 then 1 else 0 := by
  rcases b with ⟨⟨e,l⟩,k,m⟩
  simp only [highIdealMask_unmarked S hS,map_pow,highExclusion_prime S hS P,ite_eq_left hP]
  by_cases he : e=0 <;> by_cases hl : l=0 <;> by_cases hk : k=0 <;> by_cases hm : m=0 <;>
    simp [he,hl,hk,hm,Prod.mk_eq_zero]

theorem excludedHighLocalFactor (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η 1 x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealHighLocalFactor η P.val x w z := by
  by_cases hP : P.val∈S
  · rw [ite_eq_left hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η 1 x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · subst b
        simp only [Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_one,mul_one]
      · simp only [ite_eq_right hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [ite_eq_right hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact highPrimeTerm_tsum_eq_localFactor η x w z hx hw hz P

theorem excludedIdealHighSeries_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealHighLocalFactor η P.val.val x w z)
      (markedIdealHighSeries S 1 η 1 x w z) := by
  have h := excludedIdealHighSeries_hasProd S hS η x w z hx hw hz
  simp only [excludedHighLocalFactor S hS η x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=>idealHighLocalFactor η P.val x w z)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1388

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FixedEuler
Source SHA256: 0e463f91308f01561e4c8dd1d71275e67f18009389f6e0a17d86187f994c807b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1389




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic HeckeFamily
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma fixedPrimeProduct_ne_zero (S : Finset Id) (hS : ∀P∈S,Prime P) :
    (∏P∈S,P)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)

def fixedSourcePrincipal (S : Finset Id) (hS : ∀P∈S,Prime P) : Character :=
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  HeckeRayFamily.character (∏P∈S,P) 1

lemma prime_coprime_fixedProduct (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    IsCoprime P.val (∏Q∈S,Q) ↔ P.val∉S := by
  rw [IsCoprime.prod_right_iff]
  constructor
  · intro h hP
    exact P.property.not_isUnit (isCoprime_self.mp (h P.val hP))
  · intro h Q hQ
    exact primeIdeal_coprime P ⟨Q,hS Q hQ⟩ (fun he=>h ((congrArg Subtype.val he).symm ▸ hQ))

lemma fixedSourcePrincipal_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (fixedSourcePrincipal S hS) P.val=if P.val∈S then 0 else 1 := by
  unfold fixedSourcePrincipal
  rw [HeckeRayFamily.idealCoeff_character,RayOrthogonality.idealCharacter_one]
  change (if P.val=0 then (0:ℂ) else if IsCoprime P.val (∏Q∈S,Q) then 1 else 0)=_
  simp only [P.property.ne_zero,ite_false,prime_coprime_fixedProduct S hS P]
  split_ifs <;> simp_all

lemma excludedTarget_prime (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (η.excludePrimes S hS) P.val=if P.val∈S then 0 else idealCoeff η P.val := by
  rw [idealCoeff_excludePrimes]
  have he : (∀Q∈S,IsCoprime P.val Q) ↔ P.val∉S := by
    rw [←IsCoprime.prod_right_iff]
    exact prime_coprime_fixedProduct S hS P
  simp only [he]
  split_ifs <;> simp_all

theorem LFunction_hasProd_outside (χ : Character) (S : Finset Id) (a : Id→ℂ)
    (ha : ∀P : PrimeIdeal,idealCoeff χ P.val=if P.val∈S then 0 else a P.val)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-a P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction χ s) := by
  have h := IdealEuler.euler_hasProd (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs
  rw [←LFunction_eq_series χ hs] at h
  have he (P : PrimeIdeal) : (1-IdealEuler.weighted (idealCoeff χ) s P.val)⁻¹=
      if P.val∈S then 1 else (1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹ := by
    change (1-idealCoeff χ P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹=_
    rw [ha]
    split_ifs <;> simp only [zero_mul,sub_zero,inv_one]
  simp only [he] at h
  apply (hasProd_subtype_iff_mulIndicator (s:={P : PrimeIdeal|P.val∉S})
    (f:=fun P : PrimeIdeal=>(1-a P.val*CubicEisenstein.fullIdealWeight s P.val)⁻¹)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

theorem fixedSourcePrincipal_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-CubicEisenstein.fullIdealWeight s P.val.val)⁻¹) (LFunction (fixedSourcePrincipal S hS) s) := by
  simpa only [one_mul] using
    LFunction_hasProd_outside (fixedSourcePrincipal S hS) S (fun _=>1) (fixedSourcePrincipal_prime S hS) s hs

theorem excludedTarget_hasProd (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P)
    (s : ℂ) (hs : 1<s.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>
      (1-idealCoeff η P.val.val*CubicEisenstein.fullIdealWeight s P.val.val)⁻¹)
      (LFunction (η.excludePrimes S hS) s) :=
  LFunction_hasProd_outside _ S (idealCoeff η) (excludedTarget_prime η S hS) s hs

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1389

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighLFactorization
Source SHA256: d8c8a3a586e22d112f6f91b080c8d1fbb7fa8cfa177bfdf93ba12d3abe18df29
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1390



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem principalHigh_L_factorization (S : Finset Id) (hS : ∀P∈S,Prime P)
    (hgood : ∀P : PrimeIdeal,P.val∉S → Supported P.val) (htail : CorrectionTail S)
    (η : Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by
    norm_num [Complex.mul_re]
    linarith
  have hH := globalClosedCorrection_multipliable η S htail x w z (by linarith) (by linarith) (by linarith)
  have he := (((fixedSourcePrincipal_hasProd S hS (6*z) hz1).mul
    (fixedSourcePrincipal_hasProd S hS w hw1)).mul
      ((excludedTarget_hasProd η S hS x hx1).inv₀
        (LFunction_ne_zero_of_one_lt_re (η.excludePrimes S hS) hx1))).mul hH.hasProd
  have hlocal (P : {P : PrimeIdeal // P.val∉S}) :
      ((1-CubicEisenstein.fullIdealWeight (6*z) P.val.val)⁻¹ *
       (1-CubicEisenstein.fullIdealWeight w P.val.val)⁻¹ *
       ((1-idealCoeff η P.val.val*CubicEisenstein.fullIdealWeight x P.val.val)⁻¹)⁻¹) *
       idealClosedCorrection η P.val x w z = idealHighLocalFactor η P.val.val x w z := by
    rw [idealHighLocalFactor_rational η P.val (hgood P.val P.property) x w z hx hw hz]
    simp only [CubicEisenstein.fullIdealWeight,P.val.property.ne_zero,ite_false,
      Complex.ofReal_natCast,div_eq_mul_inv,mul_inv_rev,inv_inv]
    rw [show -(6*z)=(-6:ℂ)*z by ring]
    ring
  have he' : HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealHighLocalFactor η P.val.val x w z)
      (LFunction (fixedSourcePrincipal S hS) (6*z) * LFunction (fixedSourcePrincipal S hS) w /
        LFunction (η.excludePrimes S hS) x * globalClosedCorrection η S x w z) := by
    simpa only [hlocal,div_eq_mul_inv,globalClosedCorrection] using he
  exact (excludedIdealHighSeries_hasProd_outside S hS η x w z hx hw hz).unique he'

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1390

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsMultiplicative
Source SHA256: bc3e024e0ad6f3aee38e1c0e7ffa8b232d0f40872de5ea3b8662ba926fba9955
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1391



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem bareSourceCoefficient_product_row_frequency (η : HeckeFamily.Character) (u : O) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryGenerator I})) (hd : Supported (Ideal.span {primaryGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : goodLambda^2∣primaryGenerator I-1) (hpd : goodLambda^2∣primaryGenerator J-1)
    (hpn : goodLambda^2∣n-1) (hpm : goodLambda^2∣m-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime ((primaryGenerator I*n^3)*s) ((primaryGenerator J*m^3)*r)) (a b : O)
    (hba : IsCoprime b ((primaryGenerator I*n^3)*s))
    (hab : IsCoprime a ((primaryGenerator J*m^3)*r)) :
    let A := primaryGenerator I*n^3
    let B := primaryGenerator J*m^3
    let hA := supportedElement_ne_zero A (supported_completed _ _ hc hn)
    let hB := supportedElement_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) (u*(a*b)^6) =
      bareSourceCoefficient η I hI.2 A s hA (u*a^6) * bareSourceCoefficient η J hJ.2 B r hB (u*b^6) := by
  have he := bareSourceCoefficient_product η I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop (u*(a*b)^6)
  dsimp only at he ⊢
  have hi := bareSourceCoefficient_sixth_frequency η I hI.2 (primaryGenerator I*n^3) s
    (supported_completed _ _ hc hn) hs b (u*a^6) hba
  have hj := bareSourceCoefficient_sixth_frequency η J hJ.2 (primaryGenerator J*m^3) r
    (supported_completed _ _ hd hm) hr a (u*b^6) hab
  rw [show b^6*(u*a^6)=u*(a*b)^6 by ring] at hi
  rw [show a^6*(u*b^6)=u*(a*b)^6 by ring] at hj
  rw [hi,hj] at he
  exact he

theorem bareIdealHighCoefficient_row_mul (η : HeckeFamily.Character) (u : O)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighCoefficient η u (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighCoefficient η u I J K L * bareIdealHighCoefficient η u I' J' K' L' := by
  have hII := hcop.mono (first_block_dvd I J K L) (first_block_dvd I' J' K' L')
  by_cases h : highSupport I J K L ∧ highSupport I' J' K' L'
  · have hprod := (highSupport_mul I J K L I' J' K' L' hII).mpr h
    rcases h with ⟨h,h'⟩
    have hsA := (supported_mul_iff (I*J^3) K).mpr
      ⟨(supported_mul_iff I (J^3)).mpr ⟨h.2.1,supported_pow h.2.2.1 3⟩,h.2.2.2.1⟩
    have hsB := (supported_mul_iff (I'*J'^3) K').mpr
      ⟨(supported_mul_iff I' (J'^3)).mpr ⟨h'.2.1,supported_pow h'.2.2.1 3⟩,h'.2.2.2.1⟩
    have hc3 : IsCoprime ((I*J*K*L)^3) ((I'*J'*K'*L')^3) := hcop.pow_left.pow_right
    have hab := primaryGenerator_coprime _ _ hsA hsB
      (hc3.mono (completed_block_dvd_cube I J K L) (completed_block_dvd_cube I' J' K' L'))
    have hba := primaryGenerator_coprime _ _ h'.2.2.2.2 hsA
      (hcop.symm.pow_right.mono (last_block_dvd I' J' K' L') (completed_block_dvd_cube I J K L))
    have hab' := primaryGenerator_coprime _ _ h.2.2.2.2 hsB
      (hcop.pow_right.mono (last_block_dvd I J K L) (completed_block_dvd_cube I' J' K' L'))
    simp only [primaryGenerator_mul,primaryGenerator_pow] at hab hba hab'
    have he := bareSourceCoefficient_product_row_frequency η u I I'
      ⟨h.1,supported_primaryGenerator_ne_zero I h.2.1⟩
      ⟨h'.1,supported_primaryGenerator_ne_zero I' h'.2.1⟩
      ⟨hprod.1,supported_primaryGenerator_ne_zero (I*I') hprod.2.1⟩ hII
      (primaryGenerator J) (primaryGenerator J') (primaryGenerator K) (primaryGenerator K')
      ((supported_span_primaryGenerator_iff I).mpr h.2.1)
      ((supported_span_primaryGenerator_iff I').mpr h'.2.1)
      ((supported_span_primaryGenerator_iff J).mpr h.2.2.1)
      ((supported_span_primaryGenerator_iff J').mpr h'.2.2.1)
      ((supported_span_primaryGenerator_iff K).mpr h.2.2.2.1)
      ((supported_span_primaryGenerator_iff K').mpr h'.2.2.2.1)
      (primaryGenerator_spec I (supported_primaryGenerator_ne_zero I h.2.1)).2
      (primaryGenerator_spec I' (supported_primaryGenerator_ne_zero I' h'.2.1)).2
      (primaryGenerator_spec J (supported_primaryGenerator_ne_zero J h.2.2.1)).2
      (primaryGenerator_spec J' (supported_primaryGenerator_ne_zero J' h'.2.2.1)).2
      (primaryGenerator_spec K (supported_primaryGenerator_ne_zero K h.2.2.2.1)).2
      (primaryGenerator_spec K' (supported_primaryGenerator_ne_zero K' h'.2.2.2.1)).2
      hab (primaryGenerator L) (primaryGenerator L') hba hab'
    unfold highSupport at hprod h h'
    unfold bareIdealHighCoefficient
    rw [dite_eq_left hprod,dite_eq_left h,dite_eq_left h']
    simp only [primaryGenerator_mul]
    dsimp only at he
    convert he using 1 ; ring_nf
  · have hprod := mt (highSupport_mul I J K L I' J' K' L' hII).mp h
    unfold highSupport at hprod
    unfold bareIdealHighCoefficient
    rw [dite_eq_right hprod]
    by_cases hi : highSupport I J K L
    · have hj : ¬highSupport I' J' K' L' := fun hj=>h ⟨hi,hj⟩
      unfold highSupport at hj
      rw [dite_eq_right hj,mul_zero]
    · unfold highSupport at hi
      rw [dite_eq_right hi,zero_mul]

theorem bareIdealHighSummand_row_mul (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (I J K L I' J' K' L' : Id)
    (hcop : IsCoprime (I*J*K*L) (I'*J'*K'*L')) :
    bareIdealHighSummand η u x w z (I*I') (J*J') (K*K') (L*L') =
      bareIdealHighSummand η u x w z I J K L * bareIdealHighSummand η u x w z I' J' K' L' := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_row_mul η u I J K L I' J' K' L' hcop,
    fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul,fullIdealWeight_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1391

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsEuler
Source SHA256: 3f494f7fb3fa2ff558f4a96d08dc3fd3ac502550fa9d421d332b65f3127b59bd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1392


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CubicEisenstein ProbePhase ConcretePrimeRowBridge ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

@[simp] theorem bareIdealHighCoefficient_row_one (η : HeckeFamily.Character) (u : O) :
    bareIdealHighCoefficient η u 1 1 1 1=1 := by
  have hs := supported_one_ideal
  have hg : Squarefree (1:Ideal O) ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 ∧ Supported 1 :=
    ⟨squarefree_one,hs,hs,hs,hs⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hg]
  simp only [primaryGenerator_one,one_pow,mul_one]
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [gaussTwo_one,G_one,angularFactor_one]
  have ho := supported_residue_odd (1:O) (by
    rw [Ideal.span_singleton_one,←Ideal.one_eq_top];exact hs)
  rw [reciprocitySign_one_left (1:O) ho,
    bareCongruenceCoefficient_inner_one 1 one_ne_zero,outerQuotient_mk]
  simp only [map_one,star_one,one_mul,Ideal.span_singleton_one,←Ideal.one_eq_top]

@[simp] theorem bareIdealHighSummand_row_one (η : HeckeFamily.Character) (u : O) (x w z : ℂ) :
    bareIdealHighSummand η u x w z 1 1 1 1=1 := by
  have hw (t : ℂ) : fullIdealWeight t (1:Ideal O)=1 := (IdealEuler.normWeight t).map_one
  simp only [bareIdealHighSummand,bareIdealHighCoefficient_row_one,hw,one_mul]

theorem bareIdealHighSeries_row_hasProd (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (bareIdealHighSeries η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · exact bareIdealHighSummand_row_one η u x w z
  · intro a b hc
    exact bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc
  · intro a ha
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 ha
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (bareIdealHighSummand_summable η u x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1392

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsExcluded
Source SHA256: 682547640246401c505db0cefde78fc7b0ab2fcd0b846ae4516350e9904863ef
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1393



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem excludedIdealHighSeries_row_hasProd (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,
      markedIdealHighSummand S 1 η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))
      (markedIdealHighSeries S 1 η u x w z) := by
  apply highArray_hasProd (fun a : HighIdeal=>markedIdealHighSummand S 1 η u x w z a.1.1 a.1.2 a.2.1 a.2.2)
  · simp only [Prod.fst_one,Prod.snd_one,markedIdealHighSummand,
      highIdealMask_unmarked_one S hS,bareIdealHighSummand_row_one,one_mul]
  · intro a b hc
    simp only [Prod.fst_mul,Prod.snd_mul,markedIdealHighSummand,
      highIdealMask_unmarked_mul S hS a b,
      bareIdealHighSummand_row_mul η u x w z _ _ _ _ _ _ _ _ hc]
    ring
  · intro a ha
    have hh : bareIdealHighSummand η u x w z a.1.1 a.1.2 a.2.1 a.2.2≠0 :=
      (mul_ne_zero_iff.mp ha).2
    have hs := bareIdealHighSummand_support η u x w z a.1.1 a.1.2 a.2.1 a.2.2 hh
    exact ⟨hs.2.1.1,hs.2.2.1.1,hs.2.2.2.1.1,hs.2.2.2.2.1⟩
  · exact (markedIdealHighSummand_summable S 1 η u x w z hx hw hz).norm

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1393

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsLocal
Source SHA256: 2fc6b3ae70dc532defc6344ca77dbe156f129d65a14ae8f7862b26d5603382c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1394


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def rowHighPrimeTerm (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η u x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

def idealRowHighLocalFactor (η : HeckeFamily.Character) (u : O) (P : Id) (x w z : ℂ) : ℂ :=
  ∑ e : Fin 2, ∑' l : ℕ, ∑' k : ℕ, ∑' m : ℕ,
    bareIdealHighSummand η u x w z (P^e.val) (P^l) (P^k) (P^m)

lemma rowHighPrimeTerm_summable_norm (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    Summable (fun b : HighValuation=>‖rowHighPrimeTerm η u x w z P b‖) := by
  have hs := ((bareIdealHighSummand_summable η u x w z hx hw hz).norm.comp_injective
    highIdeals_injective).comp_injective (Finsupp.single_injective P)
  simpa only [Function.comp_def,highIdeals_single,rowHighPrimeTerm] using hs

lemma rowHighPrimeTerm_zero_of_two_le (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (P : PrimeIdeal) (e l k m : ℕ) (he : 2≤e) :
    rowHighPrimeTerm η u x w z P ((e,l),(k,m))=0 := by
  by_contra hn
  have hs := bareIdealHighSummand_support η u x w z (P.val^e) (P.val^l) (P.val^k) (P.val^m) hn
  have hc := hs.1.eq_zero_or_one_of_pow_of_not_isUnit P.property.not_isUnit
  omega

theorem rowHighPrimeTerm_tsum_eq_localFactor (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,rowHighPrimeTerm η u x w z P b)=
      idealRowHighLocalFactor η u P.val x w z := by
  have hs := (rowHighPrimeTerm_summable_norm η u x w z hx hw hz P).of_norm
  rw [hs.tsum_prod,hs.prod.tsum_prod]
  have he (e l : ℕ) :
      (∑' b : ℕ×ℕ, rowHighPrimeTerm η u x w z P ((e,l),b))=
        ∑' k,∑' m,rowHighPrimeTerm η u x w z P ((e,l),(k,m)) :=
    (hs.prod_factor (e,l)).tsum_prod
  simp_rw [he]
  rw [tsum_eq_sum (s:=Finset.range 2) (fun e he=>by
    have hh : 2≤e := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using he)
    simp only [rowHighPrimeTerm_zero_of_two_le η u x w z P e _ _ _ hh,tsum_zero]),
    ←Fin.sum_univ_eq_sum_range]
  rfl

theorem bareIdealHighSeries_row_hasProd_localFactor (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : PrimeIdeal=>idealRowHighLocalFactor η u P.val x w z)
      (bareIdealHighSeries η u x w z) := by
  have h := bareIdealHighSeries_row_hasProd η u x w z hx hw hz
  change HasProd (fun P : PrimeIdeal=>∑' b : HighValuation,rowHighPrimeTerm η u x w z P b) _ at h
  simpa only [rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz] using h

theorem excludedRowHighLocalFactor (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) (P : PrimeIdeal) :
    (∑' b : HighValuation,markedIdealHighSummand S 1 η u x w z
      (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)) =
      if P.val∈S then 1 else idealRowHighLocalFactor η u P.val x w z := by
  by_cases hP : P.val∈S
  · rw [ite_eq_left hP]
    have he (b : HighValuation) : markedIdealHighSummand S 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)=if b=0 then 1 else 0 := by
      rw [markedIdealHighSummand,highIdealMask_prime_inside S hS P hP b]
      by_cases hb : b=0
      · subst b
        simp only [Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_row_one,mul_one]
      · simp only [ite_eq_right hb,zero_mul]
    simp only [he,tsum_ite_eq]
  · rw [ite_eq_right hP]
    simp only [markedIdealHighSummand,highIdealMask_prime_outside S hS P hP,one_mul]
    exact rowHighPrimeTerm_tsum_eq_localFactor η u x w z hx hw hz P

theorem excludedIdealHighSeries_row_hasProd_outside (S : Finset Id) (hS : ∀P∈S,Prime P)
    (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    HasProd (fun P : {P : PrimeIdeal // P.val∉S}=>idealRowHighLocalFactor η u P.val.val x w z)
      (markedIdealHighSeries S 1 η u x w z) := by
  have h := excludedIdealHighSeries_row_hasProd S hS η u x w z hx hw hz
  simp only [excludedRowHighLocalFactor S hS η u x w z hx hw hz] at h
  apply (hasProd_subtype_iff_mulIndicator
    (s:={P : PrimeIdeal | P.val∉S})
    (f:=fun P : PrimeIdeal=>idealRowHighLocalFactor η u P.val x w z)).mpr
  convert h using 1
  funext P
  simp only [Set.mulIndicator,Set.mem_ofPred_eq]
  split_ifs <;> simp_all

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1394

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsPrime
Source SHA256: 512d888e7a3d039b7d715d62e468f636b5cfafaa4595bd25234c5277dbf94c0a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1395




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

def sourceRowTerm (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (eta a rho x w z : ℂ) (j e l k m : ℕ) : ℂ :=
  (rho^k/rho^(e+3*l))*sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
    (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) x w z
    (sourceScalar p hp hg (e+3*l) k (j+6*m)) e l k m

theorem sourceRowTerm_pos (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (eta a rho x w z : ℂ) (j e l k m : ℕ)
    (ht : e+3*l≠0) :
    sourceRowTerm p hp hg eta a rho x w z j e l k m=
      rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k m := by
  unfold sourceRowTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [rowMarkedTerm,rowWeightedScalar,sourceScalar,ite_eq_right ht,coordV,Complex.ofReal_natCast]

end SevenEighths.ProbeEuler
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem bareSourceCoefficient_unit_frequency (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryGenerator I≠0) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) (b*H)=
      ((idealRowHom b (Ideal.span {A}))⁻¹*idealRowHom b (Ideal.span {s}))*
        bareSourceCoefficient η I hI A s (supportedElement_ne_zero A hA) H := by
  unfold bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  rw [bareCongruenceCoefficient_unit_frequency A s hA hs b H hcop]
  ring

theorem bareSourceCoefficient_row_prime_formula (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (e l k j : ℕ) (he : e≤1) (hI : primaryGenerator (Ideal.span {p^e})≠0) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (b*p^j)=
    ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^(e+3*l)) *
    ((-1:ℂ)^e * ((localGamma p hp.ne_zero hg 1)⁻¹)^e * (targetMonoid η p)^e *
      (star (FiniteGaussPhase.angularFactor p)^3 * (targetMonoid η p)^3 *
        star (localGamma p hp.ne_zero hg 3))^l *
      (actualSextic (Ideal.span {p}) hg (-1))^((e+3*l)*k+e*l+l.choose 2) *
      sourceScalar p hp hg (e+3*l) k j) := by
  rw [bareSourceCoefficient_unit_frequency η _ hI _ _
    (supported_element_power p hs _) (supported_element_power p hs _) b _
    (hb.pow_right.mul_right hb.pow_right),
    bareSourceCoefficient_prime_formula η p hp hg hchar hprimary hs e l k j he hI,
    idealRowHom_prime_power_value p b hg,idealRowHom_prime_power_value p b hg]
  simp only [div_eq_mul_inv]
  ac_rfl

theorem bareSourceCoefficient_row_weighted_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p) (j e l k m : ℕ) (he : e≤1)
    (hI : primaryGenerator (Ideal.span {p^e})≠0) (x w z : ℂ) :
    bareSourceCoefficient η (Ideal.span {p^e}) hI (p^(e+3*l)) (p^k)
      (pow_ne_zero _ hp.ne_zero) (b*p^(j+6*m)) *
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
    sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e l k m := by
  rw [bareSourceCoefficient_row_prime_formula η p hp hg hchar hprimary hs b hb e l k (j+6*m) he hI]
  unfold sourceRowTerm sourceWeightedScalar
  simp only [zpow_neg,zpow_natCast,←inv_pow,Complex.ofReal_natCast]
  have hpdiag := source_signed_phase
    (actualACube η p*star (localGamma p hp.ne_zero hg 3))
    (actualSextic (Ideal.span {p}) hg (-1)) (actualSextic_neg_one_sq _ hg) e l k
  simp only [localCubePhase] at hpdiag
  have ha : actualACube η p=
      star (FiniteGaussPhase.angularFactor p)^3*(targetMonoid η p)^3 := rfl
  rw [ha] at hpdiag ⊢
  linear_combination -((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^(e+3*l)) *
    ((-1:ℂ)^e*((localGamma p hp.ne_zero hg 1)⁻¹)^e*(targetMonoid η p)^e) *
    sourceScalar p hp hg (e+3*l) k (j+6*m) *
    (Ideal.absNorm (Ideal.span {p}):ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) * hpdiag

theorem bareIdealHighCoefficient_row_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (u : O) (e l k m : ℕ) (he : e≤1) :
    bareIdealHighCoefficient η u ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m) =
    bareSourceCoefficient η (Ideal.span {p^e})
      (by rw [← Ideal.span_singleton_pow,primaryGenerator_prime_power p hp.ne_zero hprimary e];
          exact pow_ne_zero _ hp.ne_zero)
      (p^(e+3*l)) (p^k) (pow_ne_zero _ hp.ne_zero) (u*p^(6*m)) := by
  have hguard : Squarefree ((Ideal.span {p})^e) ∧ Supported ((Ideal.span {p})^e) ∧
      Supported ((Ideal.span {p})^l) ∧ Supported ((Ideal.span {p})^k) ∧ Supported ((Ideal.span {p})^m) :=
    ⟨prime_power_small_squarefree p hp e he,supported_pow hs e,supported_pow hs l,supported_pow hs k,supported_pow hs m⟩
  unfold bareIdealHighCoefficient
  rw [dite_eq_left hguard]
  simp only [primaryGenerator_prime_power p hp.ne_zero hprimary]
  have hA : p^e*(p^l)^3=p^(e+3*l) := by rw [←pow_mul,Nat.mul_comm l 3,←pow_add]
  have hH : (p^m)^6=p^(6*m) := by rw [←pow_mul,Nat.mul_comm m 6]
  simp only [hA,hH,Ideal.span_singleton_pow]

theorem bareIdealHighSummand_row_at_prime (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (j e l k m : ℕ) (he : e≤1) (x w z : ℂ) :
    bareIdealHighSummand η (b*p^j) x w z ((Ideal.span {p})^e) ((Ideal.span {p})^l)
      ((Ideal.span {p})^k) ((Ideal.span {p})^m)=
      sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e l k m := by
  unfold bareIdealHighSummand
  rw [bareIdealHighCoefficient_row_at_prime η p hp hprimary hs (b*p^j) e l k m he]
  rw [show b*p^j*p^(6*m)=b*p^(j+6*m) by rw [pow_add]; ring]
  have hw := prime_spectral_weights p hp.ne_zero e l k m x w z
  simp only [mul_assoc] at hw ⊢
  rw [hw]
  simpa only [mul_assoc] using
    bareSourceCoefficient_row_weighted_prime η p hp hg hchar hprimary hs b hb j e l k m he _ x w z

theorem idealRowHighLocalFactor_eq_source (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p) (j : ℕ) (x w z : ℂ) :
    idealRowHighLocalFactor η (b*p^j) (Ideal.span {p}) x w z=
      ∑ e : Fin 2,∑' l,∑' k,∑' m,sourceRowTerm p hp hg (targetMonoid η p) (actualACube η p)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) x w z j e.val l k m := by
  unfold idealRowHighLocalFactor
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact bareIdealHighSummand_row_at_prime η p hp hg hchar hprimary hs b hb j e.val l k m (by omega) x w z

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1395

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsZero
Source SHA256: 834355e893a176809d69957b902848b38026a5cea5e58a2668f166b504b6c1fd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1396


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

def rowZeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (j k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(j+6*m))))*W^k*V^m

theorem sourceRowTerm_zero (eta a rho x w z : ℂ) (j k m : ℕ) :
    sourceRowTerm p hp hg eta a rho x w z j 0 0 k m=
      rowZeroIndexTerm p (actualSextic (Ideal.span {p}) hg)
        (rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) j k m := by
  unfold sourceRowTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [rowZeroIndexTerm,sourceScalar,weightedScalar,localCubePhase,
    coordV,Complex.ofReal_natCast,mul_zero,add_zero,pow_zero,one_mul,mul_one,
    zero_mul,Nat.choose_zero_succ,ite_true,div_one,mul_pow]
  ring

omit [(Ideal.span {p}).IsMaximal] in
lemma rowZeroIndex_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j : ℕ) (hV : ‖V‖<1) :
    HasSum (fun m=>rowZeroIndexTerm p χ W V j 0 m) (1/(1-V)) := by
  simpa only [rowZeroIndexTerm,ite_true,pow_zero,one_mul,one_div] using
    hasSum_geometric_of_norm_lt_one hV

include hp in
theorem rowZeroIndex_pos_ramified (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j k m : ℕ) (hj : j≠0) (hk : k≠0) : rowZeroIndexTerm p χ W V j k m=0 := by
  rw [rowZeroIndexTerm,ite_eq_right hk,zero_index_scalar p hp χ k (j+6*m) hk,
    ite_eq_right (by omega),zero_mul,zero_mul]

include hp in
theorem rowZeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j : ℕ) (hW : ‖W‖<1) (hV : ‖V‖<1) :
    (∑' k,∑' m,rowZeroIndexTerm p χ W V j k m)=
      1/(1-V)+(if j=0 then W/(1-W) else 0) := by
  by_cases hj : j=0
  · subst j
    simp only [rowZeroIndexTerm,zero_add,ite_true]
    exact zeroIndexSeries_eq p hp χ W V hW hV
  · rw [ite_eq_right hj,add_zero]
    rw [tsum_eq_single 0]
    · exact (rowZeroIndex_zero p χ W V j hV).tsum_eq
    · intro k hk
      simp only [rowZeroIndex_pos_ramified p hp χ W V j k _ hj hk,tsum_zero]

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1396

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsClosed
Source SHA256: f46abcd5097dc05f09dfd87ea06aec8b94ce44bfe3cbb7ac0b6eec3ceb346dca
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1397



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def rowBaseFinite (eta a X W V rho : ℂ) (j e l : ℕ) : ℂ :=
  ∑ k : Fin 2,
    (rowMarkedTerm p hp hg eta a X W V rho j e l k.val 0+
     rowMarkedTerm p hp hg eta a X W V rho j e l k.val 1+
     rowMarkedTerm p hp hg eta a X W V rho j e l k.val 2/(1-V))

def rowClosedMarked (eta a X W V rho : ℂ) (j : ℕ) : ℂ :=
  (rowBaseFinite p hp hg eta a X W V rho j 0 2+
   rowBaseFinite p hp hg eta a X W V rho j 1 0+
   rowBaseFinite p hp hg eta a X W V rho j 0 1+
   rowBaseFinite p hp hg eta a X W V rho j 1 1)/
    (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)

include hc in
theorem rowMarkedSeries_eq_closed (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) :
    rowMarkedSeries p hp hg eta a X W V rho j=rowClosedMarked p hp hg eta a X W V rho j := by
  rw [rowMarkedSeries_four_families p hp hg hc eta a X W V rho hρ hV hR j hj]
  unfold rowClosedMarked rowBaseFinite
  rw [rowInner_base_rational p hp hg hc eta a X W V rho hV j 0 2 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 1 0 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 0 1 (by omega) (by omega),
    rowInner_base_rational p hp hg hc eta a X W V rho hV j 1 1 (by omega) (by omega)]

include hc in
lemma rowInner_zero_squarefree_summable (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) : Summable (fun l=>rowInner p hp hg eta a X W V rho j 0 l) := by
  have h02 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 2 hj (by omega)
  have h01 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 1 hj (by omega)
  have hs : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*(r+1)))
      (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    convert h02 using 1
    funext r
    congr 1
    omega
  have he := hs.sum_range_add (f:=fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r)) (k:=1)
  have ho : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 0 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h01
  exact (he.even_add_odd ho).summable

def sourceRowSeries (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2,∑' l,∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j e.val l k m

include hc in

theorem sourceRowSeries_eq_closed (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1) (j : ℕ) (hj : j<6) :
    sourceRowSeries p hp hg eta a rho x w z j=
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
      (if j=0 then (rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))/
        (1-rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))) else 0)+
      rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j := by
  let X : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)
  let W : ℂ := (Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)
  let V : ℂ := coordV (Ideal.absNorm (Ideal.span {p})) z
  let Z0 := 1/(1-V)+(if j=0 then rho*W/(1-rho*W) else 0)
  have he0 (l : ℕ) : (∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j 0 l k m)=
      rowInner p hp hg eta a X W V rho j 0 l+(if l=0 then Z0 else 0) := by
    by_cases hl : l=0
    · subst l
      simp only [sourceRowTerm_zero,rowInner_zero,ite_true,zero_add]
      exact rowZeroIndexSeries_eq p hp (actualSextic (Ideal.span {p}) hg) (rho*W) V j hW hV
    · rw [ite_eq_right hl,add_zero]
      apply tsum_congr
      intro k
      apply tsum_congr
      intro m
      exact sourceRowTerm_pos p hp hg eta a rho x w z j 0 l k m (by omega)
  have he1 (l : ℕ) : (∑' k,∑' m,sourceRowTerm p hp hg eta a rho x w z j 1 l k m)=
      rowInner p hp hg eta a X W V rho j 1 l := by
    apply tsum_congr
    intro k
    apply tsum_congr
    intro m
    exact sourceRowTerm_pos p hp hg eta a rho x w z j 1 l k m (by omega)
  have hs := rowInner_zero_squarefree_summable p hp hg hc eta a X W V rho hρ hV hR j hj
  have hc' := rowMarkedSeries_eq_closed p hp hg hc eta a X W V rho hρ hV hR j hj
  unfold rowMarkedSeries at hc'
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one] at hc'
  unfold sourceRowSeries
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,he0,he1]
  rw [hs.tsum_add (hasSum_ite_eq 0 Z0).summable,tsum_ite_eq]
  change _=Z0+rowClosedMarked p hp hg eta a X W V rho j
  rw [←hc']
  ring

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1397

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsActual
Source SHA256: 2c0cd6b295f08a019a91fb7d20239ee71d2385083fb10fb2bd219eba7bc9a9cc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1398


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower ProbeEuler
open CanonicalQuadraticSieve CanonicalRowCompletion ProbeRow CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem actualSextic_unit_six (p b : O) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hb : IsCoprime b p) :
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^6=1 := by
  have h := congrArg (fun χ : MulChar (O ⧸ Ideal.span {p}) ℂ =>
    χ (Ideal.Quotient.mk _ b)) (actualSextic_six _ hg hc)
  simpa only [MulChar.pow_apply' _ (by decide : (6:ℕ)≠0),
    MulChar.one_apply ((isUnit_quotient_span_iff p b).mpr hb.symm)] using h

theorem idealRowHighLocalFactor_eq_closed (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (j : ℕ) (hj : j<6) (x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1) :
    idealRowHighLocalFactor η (b*p^j) (Ideal.span {p}) x w z=
      1/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)+
      (if j=0 then
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))/
        (1-actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)*
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))) else 0)+
      rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)) j := by
  rw [idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb j x w z]
  exact sourceRowSeries_eq_closed p hp hg hc _ _ _ x w z
    (actualSextic_unit_six p b hg hc hb) hV hR hW j hj

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1398

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsUnramified
Source SHA256: 16fcaa8d157aa5cb64478d76f335f8123b49aa27dbdfe01f17f796141ccb4a2d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1399


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma rowMarkedTerm_unramified (eta a X W V rho : ℂ) (e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho 0 e l k m=
      principalMarkedTerm p hp hg (eta/rho) (a/rho^3) X (rho*W) V e l k m := by
  unfold rowMarkedTerm principalMarkedTerm
  split_ifs
  · rfl
  · simp only [zero_add,rowWeightedScalar_parameters]

lemma rowMarkedSeries_unramified (eta a X W V rho : ℂ) :
    rowMarkedSeries p hp hg eta a X W V rho 0=
      principalMarkedSeries p hp hg (eta/rho) (a/rho^3) X (rho*W) V := by
  unfold rowMarkedSeries principalMarkedSeries rowInner principalInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  exact rowMarkedTerm_unramified p hp hg eta a X W V rho e.val l k m

include hc in
lemma rowClosedMarked_unramified (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1) :
    rowClosedMarked p hp hg eta a X W V rho 0=
      markedFactor (evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) V
        (Ideal.absNorm (Ideal.span {p}):ℂ)⁻¹
        (eta*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)*X*W)
        (-(eta/rho)*X+(rho*W)*evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) 1 := by
  have hn : rho≠0 := by intro h; simp [h] at hρ
  rw [←rowMarkedSeries_eq_closed p hp hg hc eta a X W V rho hρ hV hR 0 (by decide),
    rowMarkedSeries_unramified p hp hg,
    principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV
      (by simpa only [evenRatio_unit _ _ _ _ _ hρ] using hR),
    evenRatio_unit _ _ _ _ _ hρ]
  congr 1
  field_simp

include hc in

theorem sourceRowSeries_unramified_euler (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) rho w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta rho x≠0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    sourceRowSeries p hp hg eta a rho x w z 0=
      (1-coordD Q eta rho x)/((1-coordV Q z)*(1-coordW Q rho w))*
        unramifiedClosed Q (a^2) eta rho x w z := by
  dsimp only
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hr := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a x z
  simp only [Complex.ofReal_natCast] at hr
  have hr' : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hr]; exact hR
  rw [sourceRowSeries_eq_closed p hp hg hc eta a rho x w z hρ hV hr' hW 0 (by decide)]
  rw [rowClosedMarked_unramified p hp hg hc _ _ _ _ _ _ hρ hV hr',hr]
  have hk := coordK_eq_geometric (Ideal.absNorm (Ideal.span {p}):ℝ) hQ eta x w
  simp only [Complex.ofReal_natCast] at hk
  rw [←hk]
  have hinv : rho⁻¹=star rho := Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hρ (by decide))
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  simp only [ite_true,div_eq_mul_inv,hinv]
  unfold unramifiedClosed ProbeLocal.continuedCorrection
  dsimp only
  simp only [coordW,coordD,Complex.ofReal_natCast] at hD hw ⊢
  field_simp [hD,hv,hw]
  ; ring

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1399

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsRegion
Source SHA256: eb55f04a7c709ceaab8ad689480be86b8eee67450d53bc37734cf1be12820b8d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1400



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma row_initial_geometric (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (b : O) (hb : IsCoprime b p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    ‖coordV Q z‖<1 ∧ ‖coordR Q ((actualACube η p)^2) x z‖<1 ∧
      ‖coordW Q rho w‖<1 ∧ ‖coordD Q (targetMonoid η p) rho x‖<1 := by
  dsimp only
  have hP : Prime (Ideal.span {p}:Ideal O) := (Ideal.prime_span_singleton_iff).mpr hp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hQ1 : (1:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hn : ‖actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)‖≤1 :=
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_unit_six p b hg hc hb) (by decide)).le
  refine ⟨?_,?_,?_,?_⟩
  · rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · rw [actualACube_sq]
    apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η p)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · apply (coordW_norm_le _ hQ0 _ w hn).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)
  · apply (coordD_norm_le _ hQ0 _ _ x (targetMonoid_norm_le_one η p) hn).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ1 (by linarith)

theorem idealRowHighLocalFactor_unramified (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (b : O) (hb : IsCoprime b p)
    (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let rho := actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b)
    idealRowHighLocalFactor η b (Ideal.span {p}) x w z=
      (1-coordD Q (targetMonoid η p) rho x)/((1-coordV Q z)*(1-coordW Q rho w))*
        unramifiedClosed Q (actualAPhase η p) (targetMonoid η p) rho x w z := by
  have hd := row_initial_geometric η p hp hg hc b hb x w z hx hw hz
  dsimp only at hd ⊢
  have he := idealRowHighLocalFactor_eq_source η p hp hg hc hprimary hs b hb 0 x w z
  simp only [pow_zero,mul_one] at he
  rw [he]
  simpa only [actualACube_sq,sourceRowSeries] using
    sourceRowSeries_unramified_euler p hp hg hc (targetMonoid η p) (actualACube η p)
      _ x w z (actualSextic_unit_six p b hg hc hb) hd.1 hd.2.1 hd.2.2.1
      (one_sub_ne_zero_of_norm_lt_one _ hd.2.2.2)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1400

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsScalarBounds
Source SHA256: 2ab5a4a256af16fe1741e6ad756c823fb94af8e047866506f2a8a1c03f3a1df2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1401


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CubicEisenstein ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma primeGauss_norm_le (p : O) (hp : p≠0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (h : O) :
    ‖primeGauss p hp χ h‖≤(Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let := finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primeGauss,tsum_fintype]
  calc
    _ ≤ ∑ x : O ⧸ Ideal.span {p},‖χ x*quotientTrace p hp (Ideal.Quotient.mk _ h*x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : O ⧸ Ideal.span {p},(1:ℝ) := Finset.sum_le_sum fun x _=>by
      rw [norm_mul,(quotientTrace p hp).norm_apply,mul_one]
      exact QuadraticInitialBound.norm_finite_character_le_one χ x
    _ = _ := by simp [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

lemma primeGauss_actual_norm (p : O) (hp : p≠0) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2) :
    ‖primeGauss p hp (actualSextic (Ideal.span {p}) hg) 1‖=
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn := localGamma_norm_one p hp hg hc 1 (by decide) (by decide)
  rw [localGamma,ProbePhase.normalizedTraceGauss_eq_normalizedGauss] at hn
  simp only [pow_one,ProbeGauss.normalizedGauss,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp))
  have hcard : (Fintype.card (O ⧸ Ideal.span {p}):ℝ)=Ideal.absNorm (Ideal.span {p}) := by
    rw [←Nat.card_eq_fintype_card];rfl
  rw [hcard] at hn
  have hn' := (div_eq_one_iff_eq (Real.sqrt_pos.mpr hQ).ne').mp hn
  simpa only [primeGauss,tsum_fintype,gaussSum,map_one,one_mul] using hn'

lemma gaussValuationTable_norm_le (Q : ℝ) (hQ : 1≤Q) (G : ℂ) (hG : ‖G‖≤Q)
    (r n j : ℕ) : ‖gaussValuationTable (Q:ℂ) G r n j‖≤2*Q^(n+1) := by
  have hQ0 : 0≤Q := by linarith
  have hn : Q^n≤Q^(n+1) := by simpa only [pow_succ] using
    (le_mul_of_one_le_right (pow_nonneg hQ0 n) hQ)
  have hpow (a : ℕ) : ‖(Q:ℂ)^a‖=Q^a := by simp [norm_pow,abs_of_nonneg hQ0]
  have hi (a : ℕ) : ‖(if a≤j then (Q:ℂ)^a else 0)‖≤Q^a := by
    split_ifs
    · exact (hpow a).le
    · simpa only [norm_zero] using pow_nonneg hQ0 a
  unfold gaussValuationTable
  by_cases hr : 6∣r
  · rw [ite_eq_left hr]
    exact (norm_sub_le _ _).trans ((add_le_add (hi (n+1)) (hi n)).trans (by linarith))
  · rw [ite_eq_right hr]
    by_cases hj : j=n
    · rw [ite_eq_left hj,norm_mul,hpow]
      calc
        _ ≤ Q^n*Q := mul_le_mul_of_nonneg_left hG (pow_nonneg hQ0 n)
        _ ≤ 2*Q^(n+1) := by rw [←pow_succ];nlinarith [pow_nonneg hQ0 (n+1)]
    · rw [ite_eq_right hj,norm_zero]
      positivity

lemma positiveScalar_norm_le (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (n k j : ℕ) (hk : k≤1) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k j‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)*
        (Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ))^k := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
    change 2≤Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (by omega : 1≤Ideal.absNorm (Ideal.span {p}))
  have ht (r j : ℕ) := gaussValuationTable_norm_le (Ideal.absNorm (Ideal.span {p}):ℝ) hQ
    (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^r) 1)
    (primeGauss_norm_le p hp.ne_zero _ _) r n j
  have ho : ‖actualSextic (Ideal.span {p}) hg (-1)‖=1 :=
    Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)
  rw [positiveScalar_actual_table p hp hg hc]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
  · simpa only [ite_true,pow_zero,mul_one,Complex.ofReal_natCast] using ht (n+1) j
  · simp only [Nat.one_ne_zero,ite_false,true_and]
    split_ifs
    · rw [norm_mul,norm_mul,norm_inv,ho,inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
      simpa only [pow_one,mul_comm,Complex.ofReal_natCast] using
        mul_le_mul_of_nonneg_left (ht n (j-1)) (Real.sqrt_nonneg (Ideal.absNorm (Ideal.span {p}):ℝ))
    · simp only [norm_zero,pow_one]
      positivity

end SevenEighths.ProbePrimePower
end

end OAI
end OAIOriginalModule1401

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsTermBounds
Source SHA256: c06cf490e4ea8a021af76d4298846351b856fc3d2b48e3b85074a1d281978684
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1402


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma sourceWeightedScalar_norm_le (Q : ℝ) (hQ : 0<Q)
    (eta a gamma C omega x w z scalar : ℂ) (heta : ‖eta‖≤1) (ha : ‖a‖≤1)
    (hgamma : ‖gamma‖=1) (hC : ‖C‖=1) (ho : ‖omega‖=1) (e l k m : ℕ) :
    ‖sourceWeightedScalar Q eta a gamma C omega x w z scalar e l k m‖≤
      ‖scalar‖*Q^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
  let coeff : ℂ := (-1:ℂ)^e*gamma^(-(e:ℤ))*eta^e*(a*C)^l*
    omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ))
  have hn : ‖coeff‖≤1 := by
    simp only [coeff,norm_mul,norm_pow,norm_zpow,hgamma,hC,ho,norm_neg,norm_one,
      one_pow,one_zpow,mul_one,one_mul]
    exact (mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) heta)).trans (pow_le_one₀ (norm_nonneg _) ha)
  change ‖coeff*scalar*(Q:ℂ)^_‖≤_
  rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  have he : (-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)).re=
      -(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ) := by simp
  rw [he]
  exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hn) (by positivity)

lemma scalar_spectral_power (Q x w z : ℝ) (hQ : 0<Q) (e l k m : ℕ) :
    (2*Q^(e+3*l)*(Real.sqrt Q)^k)*
      Q^(-(x+1/2)*(e:ℝ)-(1+3*x)*(l:ℝ)-w*(k:ℝ)-6*z*(m:ℝ))=
      2*Q^((1/2-x)*(e:ℝ)+(2-3*x)*(l:ℝ)+(1/2-w)*(k:ℝ)-6*z*(m:ℝ)) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul_natCast hQ.le,←Real.rpow_natCast Q (e+3*l)]
  rw [mul_assoc 2,←Real.rpow_add hQ,mul_assoc 2,←Real.rpow_add hQ]
  congr 1
  push_cast
  ring_nf

theorem sourceRowTerm_norm_le (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
    (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (eta a rho x w z : ℂ) (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (ht : 0<e+3*l) (hk : k≤1) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^((1/2-x.re)*(e:ℝ)+(2-3*x.re)*(l:ℝ)+
        (1/2-w.re)*(k:ℝ)-6*z.re*(m:ℝ)) := by
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)) e l k m).trans
  have hs := positiveScalar_norm_le p hp hg hc (e+3*l-1) k (j+6*m) hk
  rw [show e+3*l-1+1=e+3*l by omega] at hs
  rw [sourceScalar,ite_eq_right (by omega)]
  exact (mul_le_mul_of_nonneg_right hs (by positivity)).trans_eq
    (scalar_spectral_power _ x.re w.re z.re hQ e l k m)

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1402

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsFiniteBounds
Source SHA256: 53d5ba3bedc3dd1ddcda7d13c5c27dc4b887c4df36b9e5d60b9f6ec8efcc7644
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1403



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma rowMarkedTerm_second_region (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (19/20:ℝ)≤w.re) (hz : (33/200:ℝ)≤z.re)
    (j e l k m : ℕ) (ht : 0<e+3*l) (hk : k≤1) :
    ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l k m‖≤2 := by
  rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k m (by omega)]
  apply (sourceRowTerm_norm_le p hp hg hc eta a rho x w z heta ha hρ j e l k m ht hk).trans
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ1 : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
    have hh := SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
    change 2≤Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (by omega : 1≤Ideal.absNorm (Ideal.span {p}))
  have he : (1/2-x.re)*(e:ℝ)+(2-3*x.re)*(l:ℝ)+(1/2-w.re)*(k:ℝ)-6*z.re*(m:ℝ)≤0 := by
    have h1 := mul_nonpos_of_nonpos_of_nonneg (show 1/2-x.re≤0 by linarith) (Nat.cast_nonneg e : (0:ℝ)≤_)
    have h2 := mul_nonpos_of_nonpos_of_nonneg (show 2-3*x.re≤0 by linarith) (Nat.cast_nonneg l : (0:ℝ)≤_)
    have h3 := mul_nonpos_of_nonpos_of_nonneg (show 1/2-w.re≤0 by linarith) (Nat.cast_nonneg k : (0:ℝ)≤_)
    have h4 : 0≤6*z.re*(m:ℝ) := by positivity
    linarith
  have hh := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  linarith

lemma second_region_V_half (Q : ℝ) (hQ : 4≤Q) (z : ℂ) (hz : (33/200:ℝ)≤z.re) :
    ‖coordV Q z‖≤1/2 := by
  rw [coordV_norm Q (by linarith)]
  exact rpow_le_half Q _ hQ (by linarith)

lemma second_region_R_half (Q : ℝ) (hQ : 4≤Q) (a x z : ℂ) (ha : ‖a‖≤1)
    (hx : (7/8:ℝ)≤x.re) (hz : (33/200:ℝ)≤z.re) :
    ‖evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z)‖≤1/2 := by
  rw [evenRatio_eq_coordR Q (by linarith)]
  apply (coordR_norm_le Q (by linarith) (a^2) x z (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha)).trans
  exact rpow_le_half Q _ hQ (by linarith)

include hc in
lemma rowBaseFinite_second_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (19/20:ℝ)≤w.re) (hz : (33/200:ℝ)≤z.re)
    (j e l : ℕ) (ht : 0<e+3*l) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l‖≤16 := by
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (second_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : ℕ) := rowMarkedTerm_second_region p hp hg hc eta a rho x w z heta ha hρ hx hw hz
    j e l k.val m ht (by omega)
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,(8:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)‖≤4 := by
        rw [div_eq_mul_inv,norm_mul]
        exact (mul_le_mul (ht' k 2) hv (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
      linarith
    _ = _ := by norm_num

include hc in
theorem rowClosedMarked_second_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (19/20:ℝ)≤w.re) (hz : (33/200:ℝ)≤z.re) (j : ℕ) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤128 := by
  have h02 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 2 (by omega)
  have h10 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 0 (by omega)
  have h01 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 0 1 (by omega)
  have h11 := rowBaseFinite_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j 1 1 (by omega)
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (second_region_R_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  unfold rowClosedMarked
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul_of_nonneg_right
    ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1403

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsRamified
Source SHA256: 79be9321e84e1b91ac7373396d174039977a83cb9442f4c0876b6b548da16592
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1404


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedClosed (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  1+(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j

include hc in
theorem ramifiedClosed_bound (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (hw : (19/20:ℝ)≤w.re) (hz : (33/200:ℝ)≤z.re) (j : ℕ) :
    ‖ramifiedClosed p hp hg eta a rho x w z j‖≤193 := by
  have hb := rowClosedMarked_second_region p hp hg hc eta a rho x w z hQ heta ha hρ hx hw hz j
  have hv := second_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  simp only [norm_one] at hs
  unfold ramifiedClosed
  apply (norm_add_le _ _).trans
  rw [norm_one,norm_mul]
  have hm := mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)
  linarith

include hc in

theorem sourceRowSeries_ramified (eta a rho x w z : ℂ) (hρ : rho^6=1)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1)
    (hW : ‖rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))‖<1)
    (j : ℕ) (hj0 : j≠0) (hj : j<6) :
    sourceRowSeries p hp hg eta a rho x w z j*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)=
      ramifiedClosed p hp hg eta a rho x w z j := by
  rw [sourceRowSeries_eq_closed p hp hg hc eta a rho x w z hρ hV hR hW j hj,ite_eq_right hj0,add_zero]
  unfold ramifiedClosed
  have hn := one_sub_ne_zero_of_norm_lt_one _ hV
  field_simp

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1404

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsHolomorphic
Source SHA256: 49e64d9cfd70b2f8449108732f13bd999cafe0d4f2bc80409d68741ba74f8698
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1405



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

lemma rowMarkedTerm_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (j e l k m : ℕ) :
    DifferentiableAt ℂ (fun s=>rowMarkedTerm p hp hg eta a (X s) (W s) (V s) rho j e l k m) t := by
  unfold rowMarkedTerm
  split_ifs
  · fun_prop
  · unfold rowWeightedScalar weightedScalar
    fun_prop

lemma rowBaseFinite_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (hv : 1-V t≠0) (j e l : ℕ) :
    DifferentiableAt ℂ (fun s=>rowBaseFinite p hp hg eta a (X s) (W s) (V s) rho j e l) t := by
  have hd (k m : ℕ) := rowMarkedTerm_differentiableAt p hp hg eta a rho X W V t hX hW hV j e l k m
  unfold rowBaseFinite
  fun_prop (disch := assumption)

lemma rowClosedMarked_differentiableAt (eta a rho : ℂ) (X W V : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hV : DifferentiableAt ℂ V t)
    (hv : 1-V t≠0) (hr : 1-evenRatio (Ideal.absNorm (Ideal.span {p})) a (X t) (V t)≠0) (j : ℕ) :
    DifferentiableAt ℂ (fun s=>rowClosedMarked p hp hg eta a (X s) (W s) (V s) rho j) t := by
  have hd (e l : ℕ) := rowBaseFinite_differentiableAt p hp hg eta a rho X W V t hX hW hV hv j e l
  have hR : DifferentiableAt ℂ (fun s=>evenRatio (Ideal.absNorm (Ideal.span {p})) a (X s) (V s)) t := by
    unfold evenRatio
    fun_prop
  unfold rowClosedMarked
  fun_prop (disch := assumption)

lemma ramifiedClosed_differentiableAt (eta a rho : ℂ) (X W Z : ℂ→ℂ) (t : ℂ)
    (hX : DifferentiableAt ℂ X t) (hW : DifferentiableAt ℂ W t) (hZ : DifferentiableAt ℂ Z t)
    (hv : 1-coordV (Ideal.absNorm (Ideal.span {p})) (Z t)≠0)
    (hr : 1-coordR (Ideal.absNorm (Ideal.span {p})) (a^2) (X t) (Z t)≠0) (j : ℕ) :
    DifferentiableAt ℂ (fun s=>ramifiedClosed p hp hg eta a rho (X s) (W s) (Z s) j) t := by
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hcx : DifferentiableAt ℂ (fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-X s)) t := by
    exact hX.neg.const_cpow (Or.inl (by exact_mod_cast hQ.ne'))
  have hcw : DifferentiableAt ℂ (fun s=>(Ideal.absNorm (Ideal.span {p}):ℂ)^(-W s)) t := by
    exact hW.neg.const_cpow (Or.inl (by exact_mod_cast hQ.ne'))
  have hcv := (coordV_differentiable _ hQ).differentiableAt.comp t hZ
  change DifferentiableAt ℂ (fun s=>coordV (Ideal.absNorm (Ideal.span {p})) (Z s)) t at hcv
  have hr' := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a (X t) (Z t)
  simp only [Complex.ofReal_natCast] at hr'
  have hd := rowClosedMarked_differentiableAt p hp hg eta a rho _ _ _ t hcx hcw hcv hv
    (by rw [hr'];exact hr) j
  unfold ramifiedClosed
  fun_prop

lemma ramifiedClosed_analytic_x (eta a rho w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hz : (4/25:ℝ)≤z.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun x=>ramifiedClosed p hp hg eta a rho x w z j) {x : ℂ|7/8<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id (fun _=>w) (fun _=>z) x
    differentiableAt_id (differentiableAt_const w) (differentiableAt_const z) hd.2.1 hd.1 j).differentiableWithinAt

lemma ramifiedClosed_analytic_w (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1)
    (hx : (7/8:ℝ)≤x.re) (hz : (4/25:ℝ)≤z.re) (j : ℕ) :
    Differentiable ℂ (fun w=>ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) id (fun _=>z) w
    (differentiableAt_const x) differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

lemma ramifiedClosed_analytic_z (eta a rho x w : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hx : (7/8:ℝ)≤x.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun z=>ramifiedClosed p hp hg eta a rho x w z j) {z : ℂ|4/25<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) (fun _=>w) id z
    (differentiableAt_const x) (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1405

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsFirstHolomorphic
Source SHA256: 3d64cf8bc5a0e60cab067939bc54b10a4bd7cd50760b99d6d5a52b4890ba8e98
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1406


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma first_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 1/2≤x.re) (hz : 1/3≤z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem unramifiedClosed_first_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 1/3≤z.re) :
    AnalyticOnNhd ℂ (fun x=>unramifiedClosed Q A eta v x w z) {x : ℂ|1/2<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_first_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 1/2≤x.re) (hz : 1/3≤z.re) :
    AnalyticOnNhd ℂ (fun w=>unramifiedClosed Q A eta v x w z) (Set.univ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro w hw
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem unramifiedClosed_first_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 1/2≤x.re) :
    AnalyticOnNhd ℂ (fun z=>unramifiedClosed Q A eta v x w z) {z : ℂ|1/3<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := first_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

lemma ramifiedClosed_first_analytic_x (eta a rho w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hz : (1/3:ℝ)≤z.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun x=>ramifiedClosed p hp hg eta a rho x w z j) {x : ℂ|1/2<x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx.le hz
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho id (fun _=>w) (fun _=>z) x
    differentiableAt_id (differentiableAt_const w) (differentiableAt_const z) hd.2.1 hd.1 j).differentiableWithinAt

lemma ramifiedClosed_first_analytic_w (eta a rho x z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1)
    (hx : (1/2:ℝ)≤x.re) (hz : (1/3:ℝ)≤z.re) (j : ℕ) :
    Differentiable ℂ (fun w=>ramifiedClosed p hp hg eta a rho x w z j) := by
  intro w
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz
  exact ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) id (fun _=>z) w
    (differentiableAt_const x) differentiableAt_id (differentiableAt_const z) hd.2.1 hd.1 j

lemma ramifiedClosed_first_analytic_z (eta a rho x w : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p})) (ha : ‖a‖≤1) (hx : (1/2:ℝ)≤x.re) (j : ℕ) :
    AnalyticOnNhd ℂ (fun z=>ramifiedClosed p hp hg eta a rho x w z j) {z : ℂ|1/3<z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := first_open_region_denominators _ (a^2) 0 0 x z hQ
    (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha) (by norm_num) (by norm_num) hx hz.le
  exact (ramifiedClosed_differentiableAt p hp hg eta a rho (fun _=>x) (fun _=>w) id z
    (differentiableAt_const x) (differentiableAt_const w) differentiableAt_id hd.2.1 hd.1 j).differentiableWithinAt

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1406

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsFirstRegion
Source SHA256: cadf2b87084c5ccad01c0cbc691c9f97a782d07badf9d908630d181ee6804e4f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1407


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_first_region_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0<eps) (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hw : -(1/100:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let L := Q^(1/100:ℝ)
  let E := Q^(-(109/100:ℝ))
  let T := Q^(-1-min eps (1/50:ℝ))
  have hL1 : 1≤L := Real.one_le_rpow hQ1 (by norm_num)
  have hT : 0≤T := Real.rpow_nonneg hQ0.le _
  have hV : ‖V‖≤Q^(-(51/25:ℝ)) := by
    rw [show V=coordV Q z from rfl,coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖≤Q^(-(11/10:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖≤L :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖≤Q^(-(51/100:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖≤Q^(-eps) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖≤1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb c : ℝ) (ha : 0≤a) (hb : 0≤b)
      (haa : a≤Q^aa) (hbb : b≤Q^bb) (hc : aa+bb≤c) : a*b≤Q^c := by
    calc
      a*b≤Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤Q^c := Real.rpow_le_rpow_of_exponent_le hQ1 hc
  have hRL : ‖R‖*L≤E := hprod _ _ _ _ _ (norm_nonneg _) (by positivity) hR le_rfl (by norm_num)
  have hKV : ‖K‖*‖V‖≤E := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith)
  have hRW : ‖R‖*(1+‖W‖)≤2*E := by
    calc
      _≤‖R‖*(2*L) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _≤2*E := by nlinarith
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hPE : ‖P+D‖≤28*E := by
    have hh := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    dsimp only [P]
    nlinarith
  have hEL : E*L≤T := hprod _ _ _ _ _ (by positivity) (by positivity) le_rfl le_rfl
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hWE : (1+‖W‖)*‖P+D‖≤56*T := by
    calc
      _≤(2*L)*(28*E) := mul_le_mul (by linarith) hPE (norm_nonneg _) (by positivity)
      _≤56*T := by nlinarith
  have hDV : ‖D‖*‖V‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hVW : ‖V‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hDW : ‖D‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (coordD_norm_le Q hQ0 eta v x heta hv) (coordW_norm_le Q hQ0 v w hv)
    (by have := min_le_left eps (1/50:ℝ);linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖≤T := by
    calc
      _ = (‖D‖*‖W‖)*‖V‖ := by ring
      _ ≤ ‖D‖*‖W‖ := mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ T := hDW
  have hh := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖≤240*T
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1407

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsFirstNeighborhood
Source SHA256: 4ee3b3925f68a6c07a6642d304f2c7a4513a96a2b438508210c80935a636083f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1408


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

theorem unramifiedClosed_first_neighborhood_bound (Q : ℝ) (A eta v x w z : ℂ) (eps : ℝ)
    (hQ : 4≤Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (heps : 0<eps) (hx : (101/200:ℝ)≤x.re) (hz : (27/80:ℝ)≤z.re)
    (hw : -(3/200:ℝ)≤w.re) (hxw : 1+eps≤x.re+w.re) :
    ‖unramifiedClosed Q A eta v x w z-1‖≤240*Q^(-1-min eps (1/50:ℝ)) := by
  have hQ0 : 0<Q := by linarith
  have hQ1 : 1≤Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let L := Q^(3/200:ℝ)
  let E := Q^(-(26/25:ℝ))
  let T := Q^(-1-min eps (1/50:ℝ))
  have hL1 : 1≤L := Real.one_le_rpow hQ1 (by norm_num)
  have hT : 0≤T := Real.rpow_nonneg hQ0.le _
  have hV : ‖V‖≤Q^(-(81/40:ℝ)) := by
    rw [show V=coordV Q z from rfl,coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖≤Q^(-(211/200:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖≤L :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖≤Q^(-(101/200:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖≤Q^(-eps) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖≤1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb c : ℝ) (ha : 0≤a) (hb : 0≤b)
      (haa : a≤Q^aa) (hbb : b≤Q^bb) (hc : aa+bb≤c) : a*b≤Q^c := by
    calc
      a*b≤Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤Q^c := Real.rpow_le_rpow_of_exponent_le hQ1 hc
  have hRL : ‖R‖*L≤E := hprod _ _ _ _ _ (norm_nonneg _) (by positivity) hR le_rfl (by norm_num)
  have hKV : ‖K‖*‖V‖≤E := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by linarith)
  have hRW : ‖R‖*(1+‖W‖)≤2*E := by
    calc
      _≤‖R‖*(2*L) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _≤2*E := by nlinarith
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hPE : ‖P+D‖≤28*E := by
    have hh := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    dsimp only [P]
    nlinarith
  have hEL : E*L≤T := hprod _ _ _ _ _ (by positivity) (by positivity) le_rfl le_rfl
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hWE : (1+‖W‖)*‖P+D‖≤56*T := by
    calc
      _≤(2*L)*(28*E) := mul_le_mul (by linarith) hPE (norm_nonneg _) (by positivity)
      _≤56*T := by nlinarith
  have hDV : ‖D‖*‖V‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hVW : ‖V‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW
    (by have := min_le_right eps (1/50:ℝ);linarith)
  have hDW : ‖D‖*‖W‖≤T := hprod _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (coordD_norm_le Q hQ0 eta v x heta hv) (coordW_norm_le Q hQ0 v w hv)
    (by have := min_le_left eps (1/50:ℝ);linarith)
  have hDVW : ‖D‖*‖V‖*‖W‖≤T := by
    calc
      _ = (‖D‖*‖W‖)*‖V‖ := by ring
      _ ≤ ‖D‖*‖W‖ := mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ T := hDW
  have hh := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖≤240*T
  nlinarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1408

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsSharpScalar
Source SHA256: e18f17ba395bfb991aa22ec942c278ae3a62b21e642080ac0dde703ca9e0b23f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1409


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma primeGauss_actual_pow_norm (r : ℕ) (hr : r≠0) (hr6 : r<6) :
    ‖primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^r) 1‖=
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn := localGamma_norm_one p hp.ne_zero hg hc r hr hr6
  rw [localGamma,ProbePhase.normalizedTraceGauss_eq_normalizedGauss] at hn
  simp only [ProbeGauss.normalizedGauss,norm_div,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)] at hn
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hcard : (Fintype.card (O ⧸ Ideal.span {p}):ℝ)=Ideal.absNorm (Ideal.span {p}) := by
    rw [←Nat.card_eq_fintype_card];rfl
  rw [hcard] at hn
  have hn' := (div_eq_one_iff_eq (Real.sqrt_pos.mpr hQ).ne').mp hn
  simpa only [primeGauss,tsum_fintype,gaussSum,map_one,one_mul] using hn'

include hc in
lemma nonprincipal_kzero_norm (n j : ℕ) (hn : n<5) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n 0 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^n*Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  rw [positiveScalar_kzero,actualSextic_primePowerGauss_at_pow p hp hg hc,
    ite_eq_right (by omega : ¬6∣n+1)]
  split_ifs
  · rw [norm_mul,norm_pow,Complex.norm_natCast,primeGauss_actual_pow_norm p hp hg hc (n+1) (by omega) (by omega)]
  · simp only [norm_zero]
    positivity

include hc in
lemma nonprincipal_kone_norm (n j : ℕ) (hn : 0<n) (hn6 : n<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n 1 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1) := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hj : 1≤j
  · rw [ite_eq_left ⟨rfl,hj⟩,gaussValuationTable,ite_eq_right (by omega : ¬6∣n)]
    split_ifs
    · rw [norm_mul,norm_mul,norm_inv,
        Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide),inv_one,one_mul,
        primeGauss_actual_norm p hp.ne_zero hg hc,norm_mul,norm_pow,Complex.norm_natCast,
        primeGauss_actual_pow_norm p hp hg hc n (by omega) hn6]
      have hsq := Real.sq_sqrt (Nat.cast_nonneg (Ideal.absNorm (Ideal.span {p})) : (0:ℝ)≤_)
      rw [pow_succ]
      apply le_of_eq
      calc
        _ = (Ideal.absNorm (Ideal.span {p}):ℝ)^n*(Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ))^2 := by ring
        _ = _ := by rw [hsq]
    · simp only [mul_zero,norm_zero]
      positivity
  · rw [ite_eq_right (by omega),norm_zero]
    positivity

include hc in
lemma even_base_kzero_norm (m j : ℕ) (hj : j<6) :
    ‖positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 5 0 (j+6*m)‖≤
      if m=0 then (Ideal.absNorm (Ideal.span {p}):ℝ)^5 else (Ideal.absNorm (Ideal.span {p}):ℝ)^6 := by
  have he := row_even_kzero p hp hg hc 0 m j hj
  norm_num only [Nat.mul_zero,zero_add] at he
  rw [he]
  by_cases hm : m=0
  · subst m
    norm_num only [Nat.reduceLeDiff,ite_false,ite_true,and_true]
    split_ifs <;> simp [norm_pow]
  · rw [ite_eq_left (by omega),ite_eq_right hm,norm_mul,norm_pow,Complex.norm_natCast]
    have hQ1 : (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by
      have hh := SmoothMobiusCorrection.prime_norm_two_le
        ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩
      change 2≤Ideal.absNorm (Ideal.span {p}) at hh
      exact_mod_cast (by omega : 1≤Ideal.absNorm (Ideal.span {p}))
    have hsub : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)-1‖=(Ideal.absNorm (Ideal.span {p}):ℝ)-1 := by
      rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    rw [hsub,show (Ideal.absNorm (Ideal.span {p}):ℝ)^6=(Ideal.absNorm (Ideal.span {p}):ℝ)^5*(Ideal.absNorm (Ideal.span {p}):ℝ) by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

include hc in
lemma even_base_kone_zero (j : ℕ) (hj : j<6) :
    positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 5 1 j=0 := by
  rw [positiveScalar_actual_table p hp hg hc,ite_eq_right (by decide : (1:ℕ)≠0)]
  by_cases hj1 : 1≤j
  · rw [ite_eq_left ⟨rfl,hj1⟩,gaussValuationTable,ite_eq_right (by decide : ¬6∣5),
      ite_eq_right (by omega : j-1≠5),mul_zero]
  · rw [ite_eq_right (by omega)]

end SevenEighths.ProbePrimePower
end

end OAI
end OAIOriginalModule1409

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsFirstTerms
Source SHA256: 33f3a648d2262942af8c3e4423314650c9e37172b552677da6ca48a888595bee
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1410


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma pow_mul_sqrt (Q : ℝ) (hQ : 0<Q) (n : ℕ) : Q^n*Real.sqrt Q=Q^((n:ℝ)+1/2) := by
  rw [Real.rpow_add hQ,Real.rpow_natCast,Real.sqrt_eq_rpow]

include hc in
lemma sourceRowTerm_norm_from_scalar (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (j e l k m : ℕ) (nu : ℝ)
    (hs : ‖sourceScalar p hp hg (e+3*l) k (j+6*m)‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)
    (he : nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)≤0) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2 := by
  have hP : Prime (Ideal.span {p}:Ideal O) := Ideal.prime_span_singleton_iff.mpr hp
  have hQ2 : (2:ℝ)≤Ideal.absNorm (Ideal.span {p}) := by exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le ⟨_,hP⟩
  have hQ : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) := by linarith
  have hrho := Complex.norm_eq_one_of_pow_eq_one hρ (by decide : (6:ℕ)≠0)
  rw [sourceRowTerm,norm_mul,norm_div,norm_pow,norm_pow,hrho,one_pow,one_pow,div_self (by norm_num : (1:ℝ)≠0),one_mul]
  apply (sourceWeightedScalar_norm_le _ hQ eta a _ _ _ x w z _ heta ha
    (localGamma_norm_one p hp.ne_zero hg hc 1 (by decide) (by decide))
    (by rw [norm_star];exact localGamma_norm_one p hp.ne_zero hg hc 3 (by decide) (by decide))
    (Complex.norm_eq_one_of_pow_eq_one (actualSextic_neg_one_sq _ hg) (by decide)) e l k m).trans
  calc
    _ ≤ (2*(Ideal.absNorm (Ideal.span {p}):ℝ)^nu)*
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = 2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(nu-(x.re+1/2)*(e:ℝ)-(1+3*x.re)*(l:ℝ)-w.re*(k:ℝ)-6*z.re*(m:ℝ)) := by
      rw [mul_assoc,←Real.rpow_add hQ]
      congr 2
      ring
    _ ≤ 2 := by
      have hh := Real.rpow_le_one_of_one_le_of_nonpos (show (1:ℝ)≤Ideal.absNorm (Ideal.span {p}) by linarith) he
      linarith

include hc in
theorem sourceRowTerm_first_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (_hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1≤x.re+w.re) (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2 := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ : 0<Q := by
    dsimp only [Q]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg m
  have hzm : 0≤6*z.re*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*z.re≤6*z.re*(m:ℝ) := by
    have hm1 : (1:ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
    nlinarith
  have hrelax (v : ℝ) : Q^v≤2*Q^v := by nlinarith [Real.rpow_nonneg hQ.le v]
  have hz0 (t k : ℕ) (ht : t≠0) : sourceScalar p hp hg t k (j+6*m)=
      positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (t-1) k (j+6*m) := by
    rw [sourceScalar,ite_eq_right ht]
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · by_cases hm : m=0
      · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 5
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_left hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^5≤2*Q^5 by nlinarith [pow_nonneg hQ.le 5])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          linarith
      · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 2 0 m 6
        · have hs := even_base_kzero_norm p hp hg hc m j hj
          rw [ite_eq_right hm] at hs
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 0 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
    · by_cases hm : m=0
      · subst m
        simp only [sourceRowTerm,sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,
          Nat.reduceEqDiff,ite_false,mul_zero,add_zero,even_base_kone_zero p hp hg hc j hj,
          sourceWeightedScalar,zero_mul,mul_zero,norm_zero]
        norm_num
      · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 2 1 m 6
        · have hs := nonprincipal_kone_norm p hp hg hc 5 (j+6*m) (by decide) (by decide)
          simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 6 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
            hs.trans (show Q^6≤2*Q^6 by nlinarith [pow_nonneg hQ.le 6])
        · norm_num only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,mul_one,sub_zero]
          nlinarith [hzm1 hm]
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 0 0 m (1/2)
      · have hs := nonprincipal_kzero_norm p hp hg hc 0 (j+6*m) (by decide)
        simp only [pow_zero,one_mul,Real.sqrt_eq_rpow] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 0 (by decide),Nat.reduceSub] using hs.trans (hrelax (1/2))
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 0 1 m (3/2)
      · have hs := positiveScalar_norm_le p hp hg hc 0 1 (j+6*m) (by decide)
        simp only [Nat.zero_add,pow_one] at hs
        have he : 2*Q*Real.sqrt Q=2*Q^(3/2:ℝ) := by
          have ht := pow_mul_sqrt Q hQ 1
          norm_num at ht
          rw [mul_assoc,ht]
        rw [he] at hs
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 1 1 (by decide),Nat.reduceSub] using hs
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 1 0 m (5/2)
      · have hs := nonprincipal_kzero_norm p hp hg hc 2 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (5/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 0 1 1 m 3
      · have hs := nonprincipal_kone_norm p hp hg hc 2 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 3 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^3≤2*Q^3 by nlinarith [pow_nonneg hQ.le 3])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 1 0 m (7/2)
      · have hs := nonprincipal_kzero_norm p hp hg hc 3 (j+6*m) (by decide)
        rw [pow_mul_sqrt _ hQ] at hs
        norm_num only [Nat.cast_ofNat] at hs
        convert hs.trans (hrelax (7/2)) using 1 ;
          simp only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceEqDiff,ite_false,Nat.reduceSub]
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith
    · apply sourceRowTerm_norm_from_scalar p hp hg hc eta a rho x w z heta ha hρ j 1 1 1 m 4
      · have hs := nonprincipal_kone_norm p hp hg hc 3 (j+6*m) (by decide) (by decide)
        simpa only [Nat.reduceMul,Nat.reduceAdd,hz0 4 1 (by decide),Nat.reduceSub,Real.rpow_natCast,Real.rpow_ofNat] using
          hs.trans (show Q^4≤2*Q^4 by nlinarith [pow_nonneg hQ.le 4])
      · norm_num only [Nat.cast_zero,Nat.cast_one,mul_zero,mul_one,sub_zero]
        linarith

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1410

/-! Original module: OAI.NumberTheory.DirichletL.Detector.HighRowsFirstRamified
Source SHA256: 761c1527e0cbe2807acac9e27b012211a97edf08c842fd2330e0e6b8e74f78b6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1411



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma first_region_V_half (Q : ℝ) (hQ : 4≤Q) (z : ℂ) (hz : (17/50:ℝ)≤z.re) :
    ‖coordV Q z‖≤1/2 := by
  rw [coordV_norm Q (by linarith)]
  exact rpow_le_half Q _ hQ (by linarith)

lemma first_region_R_half (Q : ℝ) (hQ : 4≤Q) (a x z : ℂ) (ha : ‖a‖≤1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) :
    ‖evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z)‖≤1/2 := by
  rw [evenRatio_eq_coordR Q (by linarith)]
  apply (coordR_norm_le Q (by linarith) (a^2) x z (by simpa only [norm_pow] using pow_le_one₀ (norm_nonneg a) ha)).trans
  exact rpow_le_half Q _ hQ (by linarith)

include hc in
lemma rowBaseFinite_first_region (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1≤x.re+w.re) (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖rowBaseFinite p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
      rho j e l‖≤16 := by
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z hz)
  have ht' (k : Fin 2) (m : ℕ) :
      ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
        rho j e l k.val m‖≤2 := by
    have ht : e+3*l≠0 := by rcases hf with h|h|h|h <;> omega
    rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k.val m ht]
    exact sourceRowTerm_first_base p hp hg hc eta a rho x w z heta ha hρ hx hw hz hxw
      j e l k.val m hj (by omega) hf
  unfold rowBaseFinite
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k : Fin 2,(8:ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply (norm_add_le _ _).trans
      have hab := (norm_add_le _ _).trans (add_le_add (ht' k 0) (ht' k 1))
      have hd : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
          ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
          rho j e l k.val 2/(1-coordV (Ideal.absNorm (Ideal.span {p})) z)‖≤4 := by
