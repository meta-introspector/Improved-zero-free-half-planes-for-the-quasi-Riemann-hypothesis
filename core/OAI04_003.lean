section OAIOriginalModule0423


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_span_primeProduct (S : Finset ι) (v : ι→ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣Ideal.span {primeProduct p S v} ↔ i∈S ∧ 0<v i := by
  simp only [primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
  rw [←dvd_iff_emultiplicity_pos,primeIdealProduct_emultiplicity (fun i=>Ideal.span {p i}) hinj]
  by_cases hi : i∈S <;> simp [hi]

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_reopened_index (S : Finset ι) (v : ι→₀ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣(Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 ↔
      i∈S∪v.support := by
  have hi : Prime (Ideal.span {p i}:Ideal O) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have hs := prime_dvd_span_primeProduct p hinj S (fun _=>1) i
  simp only [primeProduct,pow_one,Nat.zero_lt_one,and_true] at hs
  rw [hi.dvd_mul,hi.dvd_pow_iff_dvd (by decide : (3:ℕ)≠0),hs,
    prime_dvd_span_primeProduct p hinj v.support v i,Finset.mem_union]
  have hv : i∈v.support ↔ 0<v i := by rw [Finsupp.mem_support_iff]; omega
  tauto

include hinj in

omit [DecidableEq σ] in
theorem reopened_whole_mark_divisibility (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
    ∏j∈slots,∑i∈lists j,if (Ideal.span {p i}:Ideal O)∣
      (Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 then a j i else 0 := by
  unfold primeMark primeSlot
  simp_rw [prime_dvd_reopened_index p hinj]

theorem reopened_mark_priority (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
      ∑J∈slots.powerset,primeMark J lists a v.support *
        primeMark (slots\J) (fun j=>lists j\v.support) a S := by
  rw [Finset.union_comm,primeMark_priority]
  simp only [primeMark_residual_lists]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0423

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CompleteMarkedPool
Source SHA256: bebed519aa36ad338824fc1dd6de627adc519720ac3b77d0b8db6c13de031ab1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0424



namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def indexedIdealMark {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (primes : ι→Ideal O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (I : Ideal O) : ℂ :=
  ∏j∈slots,∑i∈lists j,if primes i∣I then a j i else 0

theorem complete_pool_mark {σ : Type*} [DecidableEq σ]
    (F : Finset (Ideal O)) (hF : ∀ I∈F,Admissible I)
    (slots : Finset σ) (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (T : Finset (primePool F)) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val) =
      primeMark slots lists a T := by
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hinj : Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j h
    dsimp only at h
    rw [poolPrimary_span F hF i,poolPrimary_span F hF j] at h
    exact Subtype.ext h
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T 0
  simp only [Finsupp.support_zero,Finset.union_empty,primeProduct,Finset.prod_empty,
    Ideal.span_singleton_one,←Ideal.one_eq_top,one_pow,mul_one] at he
  have hspan : Ideal.span {∏i∈T,poolPrimary F i}=∏i∈T,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  rw [hspan] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem finiteCanonicalMarkedRow_complete_global {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X =
    ∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a I*W ((Ideal.absNorm I:ℝ)/X) := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b X hX hW hD
    (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)
  dsimp only at he
  have hmark : (fun T:Finset (primePool F)=>W (primeProductNorm (poolPrimary F) T/X)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (∏i∈T,i.val)) =
      (fun T=>primeMark slots lists a T*W (primeProductNorm (poolPrimary F) T/X)) := by
    funext T
    rw [complete_pool_mark F hF slots lists a T,mul_comm]
  rw [hmark] at he
  unfold finiteCanonicalMarkedRow
  calc
    _ = _ := he
    _ = _ := tsum_congr (fun I=>by ring)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0424

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CompletedReopening
Source SHA256: 5272ee5555c18fdeed0be37f85137022ea73a3f3e2ea77bc15d542c192590f3f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0425


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def outsideCanonicalMarkedRow {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (Ψ : O →* ℂ) (m f z : O) (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  finiteCanonicalMarkedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m f z slots lists a W X

theorem outsideCanonicalMarkedRow_cube_split {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      ∑ B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑' I:Ideal O,summand Ψrow W X I B*mark (I*B^3) := by
  dsimp only
  unfold outsideCanonicalMarkedRow
  rw [finiteCanonicalMarkedRow_complete_global S D hbad hSp Ψ m f z W b X hX hW hD]
  rw [marked_completed_cube_inverse_split _ W hWc X H₀ hX]
  rw [marked_large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]

theorem outsideCanonicalMarkedRow_reopened {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      ∑ B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B*cubeWeight Ψrow B*
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹)*
        ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))*mark (I*B^3) := by
  rw [outsideCanonicalMarkedRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  rw [marked_inner_completed_sum _ W X hX B (outsideIdealsUpTo_ne_bot S D B hB)]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0425

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedPriority
Source SHA256: 7c82d1994a91abaa3552a6d4ec4b69b32cc24c8832e2b59c40bd193d03701ab8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0426


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_reopened_prime_priority
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (β : (ι→₀ℕ)→ℂ)
    (Ψ : O→*ℂ) (m f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : (ι→₀ℕ)→Finset ι→ℂ) (z : O) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v S=>primeMark slots lists a (S∪v.support)*V v S) z =
    ∑J∈slots.powerset,varyingReopenedRow p hp hcop hg pool Q
      (fun v=>β v*primeMark J lists a v.support) Ψ m f
      (fun v S=>primeMark (slots\J) (fun j=>lists j\v.support) a S*V v S) z := by
  unfold varyingReopenedRow
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [canonicalSourceCoefficient]
  rw [reopened_mark_priority]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem allocated_cube_coefficient_bound
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (hJ : J⊆slots) (hslots : (slots : Set σ).PairwiseDisjoint lists)
    (ha : ∀ j∈slots,∀ i∈lists j,‖a j i‖≤1)
    (β : (ι→₀ℕ)→ℂ) (v : ι→₀ℕ) :
    ‖β v*primeMark J lists a v.support‖≤‖β v‖*(2:ℝ)^v.support.card := by
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact primeMark_norm_le_divisor_count J lists a v.support
    (fun i hi j hj hne=>hslots (hJ hi) (hJ hj) hne) (fun j hj i hi=>ha j (hJ hj) i hi)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0426

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedIdentification
Source SHA256: 113c6ad8673d89301a160f5e069945777c2c3c6640eedc8f12d35043eb6caa54
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0427



namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem complete_pool_whole_cube_mark {σ : Type*} [DecidableEq σ]
    (F : Finset (Ideal O)) (hF : ∀ I∈F,Admissible I)
    (slots : Finset σ) (lists : σ→Finset (primePool F)) (a : σ→primePool F→ℂ)
    (T : Finset (primePool F)) (v : primePool F→₀ℕ) :
    indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      ((∏i∈T,i.val)*cubeIdeal F v^3) = primeMark slots lists a (T∪v.support) := by
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  have hinj : Function.Injective (fun i:primePool F=>Ideal.span {poolPrimary F i}) := by
    intro i j h
    dsimp only at h
    rw [poolPrimary_span F hF i,poolPrimary_span F hF j] at h
    exact Subtype.ext h
  have he := reopened_whole_mark_divisibility (poolPrimary F) hinj slots lists a T v
  have hspan : Ideal.span {∏i∈T,poolPrimary F i}=∏i∈T,i.val := by
    rw [FiniteGaussPhase.span_finset_prod]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  rw [hspan,cubeIdeal_eq_primeProduct_span F hF v] at he
  simpa only [indexedIdealMark,poolPrimary_span F hF] using he.symm

theorem reopened_marked_global_column {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X : ℝ) (hb : 0≤b) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (v : primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let Y := X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3
    (∑' I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I*W ((Ideal.absNorm I:ℝ)/Y)*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)) =
    fixedChildRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) Finset.univ Ψ m
      (fun T=>primeMark slots lists a (T∪v.support)*W (primeProductNorm (poolPrimary F) T/Y)) f z := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let Y := X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3
  have hN := norm_at_least_one (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  have hY : 0<Y := by dsimp [Y];positivity
  have hYD : b*Y≤D := (mul_le_mul_of_nonneg_left
    (div_le_self hX.le (one_le_pow₀ hN)) hb).trans hD
  have he := marked_complete_pool_eq_global S D hbad hSp Ψ m f z W b Y hY hW hYD
    (fun I=>indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3))
  dsimp only at he ⊢
  rw [←he]
  congr 1
  funext T
  rw [complete_pool_whole_cube_mark F hF slots lists a T v,mul_comm]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0427

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedOriginalRow
Source SHA256: b43ad2724fc2a5cd1e9534ddde8c3caf7477462eaad9bf90514088786f87685b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0428


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

def markedReopenedCubeBin {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (X H₀ : ℝ)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) : ℂ :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
  ∑ v∈Q,(largeCubeCoefficient H₀ (cubeIdeal F v)*cubeWeight Ψrow (cubeIdeal F v)*
    (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹)*
    ∑' I:Ideal O,columnWeight Ψrow I*W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3))*
      indexedIdealMark (fun i:primePool F=>i.val) slots lists a (I*cubeIdeal F v^3)

theorem original_marked_split_to_bins {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let Ψrow := rowTwist Ψ (m*excludedGenerator S) f z
    let mark := indexedIdealMark (fun i:primePool F=>i.val) slots lists a
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
      (∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
        (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
          markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0) +
      markedReopenedCubeBin S D ((outsideIdealsUpTo S D).image (cubeIndex F)) Ψ m f z W X H₀ slots lists a := by
  rw [outsideCanonicalMarkedRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  dsimp only
  rw [sum_outside_cubeIndex S D]
  rfl

theorem markedReopenedCubeBin_eq_varying {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X H₀ : ℝ) (hb : 0≤b) (hX : 0<X)
    (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β := fun v=>largeCubeCoefficient H₀ (cubeIdeal F v)*
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)*
      (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists a =
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q β Ψ m f
        (fun v T=>primeMark slots lists a (T∪v.support)*
          W (primeProductNorm (poolPrimary F) T/(X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3))) z := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  unfold markedReopenedCubeBin varyingReopenedRow
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [reopened_marked_global_column S D hbad hSp Ψ m f z W b X hb hX hW hD slots lists a v]
  rw [cubeWeight_row_factor,cubeIdeal_row F hF v z]
  unfold fixedChildRow
  simp only [Finset.mul_sum,secondChildColumn,canonicalSourceCoefficient]
  apply Finset.sum_congr rfl
  intro T hT
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0428

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedSeparation
Source SHA256: af0ec010d957c8a7fb0e203ca0ffcea6526443af654e5555f6fab46a6d22243c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0429


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open CanonicalCubeSeparation JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varyingReopenedRow_integrand
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (Ψ : O →* ℂ) (m f z : O) (H : (ι→₀ℕ)→Finset ι → ℂ) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f H z =
      ∑ v ∈ Q, ∑ T ∈ pool.powerset,
        β v * (multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
          canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
          finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) * H v T := by
  unfold varyingReopenedRow
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  simp only [canonicalSourceCoefficient]
  ring

theorem varying_canonical_bin_separation
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Ψ : O →* ℂ) (m f z : O) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B ≤ n v) (hn' : ∀ v ∈ Q, n v ≤ Real.exp 1*B) :
    (∑ v ∈ Q, (β v * (n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹) *
      multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      fixedChildRow p hp hcop hg pool Ψ m
        (fun T => mark v T*W (primeProductNorm p T/(X/(n v)^3))) f z) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          varyingReopenedRow p hp hcop hg pool Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z*mark v T
  have hsep := reopening_finite_sum W a b ha hs hW V hV Q pool.powerset β A n
    (primeProductNorm p) B ell X hB hell hX hn hn'
    (fun T _ => primeProductNorm_pos p hp T)
  calc
    _ = ∑ v ∈ Q, ∑ T ∈ pool.powerset, (β v * A v T) *
        ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ *
          W (primeProductNorm p T/(X/(n v)^3))) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [fixedChildRow_coefficient_expansion p hp hcop hg, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only [A]
      ring
    _ = _ := by
      rw [hsep]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [varyingReopenedRow_integrand p hp hcop hg]
      simp only [A, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only [columnLog]
      ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0429

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedCommonMeasure
Source SHA256: 65af77d50a947738e074c94ab3e2818589d33acd5c1466d69b75031ec8274ed2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0430


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem markedReopenedCubeBin_separated {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hb : 0≤b) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u,|u|≤columnWindowRadius a b→V u=1)
    (B ell X H₀ : ℝ) (hB : 0<B) (hell : 0<ell) (hX : X=B^3*ell)
    (hD : b*X≤D)
    (hn : ∀ v∈Q,B≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ))
    (hn' : ∀ v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*B)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    let β := fun v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
    let n := fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists weights =
      ((B*Real.sqrt ell:ℝ):ℂ)⁻¹ * ∫ ξ:ℝ,reopeningCoefficient W a b ha hs hW ξ*
        varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
          (separatedCubeCoefficient β n B ξ) Ψ m f
          (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z := by
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let β := fun v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
  let n := fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  have hXp : 0<X := hX ▸ mul_pos (pow_pos hB _) hell
  have hupper : ∀ t,W t≠0→t≤b := fun t ht=>(hs ht).2
  dsimp only
  rw [←varying_canonical_bin_separation (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) W a b ha hs hW V hV
    Finset.univ Q β n (fun v T=>primeMark slots lists weights (T∪v.support))
    Ψ m f z B ell X hB hell hX hn hn']
  unfold markedReopenedCubeBin
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [reopened_marked_global_column S D hbad hSp Ψ m f z W b X hb hXp hupper hD slots lists weights v]
  rw [cubeWeight_row_factor,cubeIdeal_row F hF v z]
  have hc := cube_coefficient_restore H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
    (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  have hc' : β v*(n v:ℂ)⁻¹=largeCubeCoefficient H₀ (cubeIdeal F v)*
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) := by
    simpa only [β,n,Complex.ofReal_natCast] using hc
  rw [hc']
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0430

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedIntegralEnergy
Source SHA256: b72f0437ca9844899acfc4c793f66104c5fd53facbbf9894a85422be9206b778
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0431


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalCubeSeparation JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_separated_canonical_integrable
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Ψ : O →* ℂ) (m f z : O)
    (b V : 𝓢(ℝ,ℂ)) (B ell : ℝ) :
    Integrable (fun ξ : ℝ => b ξ *
      varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient β n B ξ)
        Ψ m f (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow (fun i => Ideal.span {p i}) hg pool v z ^ 3 *
      canonicalSourceCoefficient p hp hcop hg Ψ m f (fun _ => 1) T *
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z*mark v T
  have hi := reopening_finite_sum_integrable Q pool.powerset β A n (primeProductNorm p) B ell b V
  convert hi using 1
  funext ξ
  rw [varyingReopenedRow_integrand p hp hcop hg]
  simp only [A,Finset.mul_sum,columnLog]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  ring

theorem varying_separated_canonical_family_energy
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O → (ι →₀ ℕ) → ℂ) (n : (ι →₀ ℕ) → ℝ) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (Ψ : O →* ℂ) (m : O) (b V : 𝓢(ℝ,ℂ))
    (B ell K E : ℝ) (d : ℕ) (hB : 0 < B) (hell : 0 < ell) (hK : 0 < K) (hE : 0 ≤ E)
    (hbound : ∀ ξ : ℝ,
      rowFamilyEnergy labels (fun I z =>
        varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) K ≤
        E*(1+|ξ|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℝ, b ξ *
        varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
          Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) K ≤
      (B^2*ell)⁻¹ * E*(∫ ξ : ℝ, ‖b ξ‖*(1+|ξ|)^d)^2 := by
  have hb : Integrable (fun ξ : ℝ => ‖b ξ‖*(1+|ξ|)^d) := by
    simpa only [Real.norm_eq_abs,mul_comm] using weighted_schwartz_integrable b d
  have hφ (I : Ideal O) (z : O) : Integrable (fun ξ : ℝ => b ξ *
      varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
        Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z) :=
    varying_separated_canonical_integrable p hp hcop hg pool Q (β I) n mark Ψ m (idealGenerator I) z b V B ell
  have hm := rowFamilyEnergy_integral_polynomial labels K hK b
    (fun I z ξ => varyingReopenedRow p hp hcop hg pool Q (separatedCubeCoefficient (β I) n B ξ)
      Ψ m (idealGenerator I) (fun v T => mark v T*frequencyTwist V ξ (columnLog p ell T)) z)
    d E hE hb hφ hbound
  have hn : ‖((B*Real.sqrt ell : ℝ) : ℂ)⁻¹‖^2 = (B^2*ell)⁻¹ := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (mul_pos hB (Real.sqrt_pos.mpr hell)),inv_pow,mul_pow,Real.sq_sqrt hell.le]
  rw [rowFamilyEnergy_const_mul labels _ K hK, hn]
  convert mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (B^2*ell)⁻¹) using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0431

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedBinEnergy
Source SHA256: bad0207308172495388e4b8c2ebc2fbce7c57b648c5a56eb7f6b20fa227f3b15
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0432


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem markedReopenedCubeBin_energy
    {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal O)) (Ψ : O →* ℂ) (m : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hb : 0≤b) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (B ell X H₀ K E : ℝ) (d : ℕ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell) (hD : b*X≤D) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, B ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*B)
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, rowFamilyEnergy labels (fun I z =>
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
        (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    rowFamilyEnergy labels (fun I z =>
      markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z W X H₀ slots lists weights) K ≤
      (B^2*ell)⁻¹ * E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F := InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun I v => reopenedCubeCoefficient H₀
    (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  intro hbound
  have hrows : (fun I z => markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z W X H₀ slots lists weights) =
      (fun I z => ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ * ∫ ξ : ℝ,
        reopeningCoefficient W a b ha hs hW ξ *
          varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
            (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient (β I) n B ξ) Ψ m (idealGenerator I)
            (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z) := by
    funext I z
    exact markedReopenedCubeBin_separated S D hbad hSp Q Ψ m (idealGenerator I) z W a b ha hb hs hW V hV
      B ell X H₀ hB hell hX hD hn hn' slots lists weights
  rw [hrows]
  exact varying_separated_canonical_family_energy (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q labels β n (fun v T=>primeMark slots lists weights (T∪v.support)) Ψ m
    (reopeningCoefficient W a b ha hs hW) V B ell K E d hB hell hK hE hbound

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0432

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedBins
Source SHA256: 2c927a68279170fe73593c185de8857e978f5dbf7cdb9d720854eff7d95f5a20
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0433


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

theorem marked_column_zero_of_subunit (Ψ : O→*ℂ) (W : ℝ→ℂ) (b Y : ℝ)
    (hY : 0<Y) (hW : ∀ t,W t≠0→t≤b) (hsub : b*Y<1) (mark : Ideal O→ℂ) :
    (∑' I:Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I:ℝ)/Y)*mark I)=0 := by
  suffices hz : ∀ I:Ideal O,columnWeight Ψ I*W ((Ideal.absNorm I:ℝ)/Y)*mark I=0 by
    simp only [hz,tsum_zero]
  intro I
  by_cases hI : I=0
  · simp only [hI,columnWeight_zero,zero_mul]
  have hw : W ((Ideal.absNorm I:ℝ)/Y)=0 := by
    by_contra hn
    have hh := (div_le_iff₀ hY).mp (hW _ hn)
    have hone := norm_at_least_one I hI
    linarith
  simp only [hw,mul_zero,zero_mul]

variable {σ : Type*} [DecidableEq σ]
  (S : Finset (Ideal O)) (D : ℕ)
  (Ψ : O→*ℂ) (m f z : O) (W : ℝ→ℂ) (b X H₀ : ℝ)
  (slots : Finset σ)
  (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
  (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)

theorem markedReopenedCubeBin_eq_active (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) :
    markedReopenedCubeBin S D
      ((outsideIdealsUpTo S D).image (cubeIndex (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      Ψ m f z W X H₀ slots lists a =
    markedReopenedCubeBin S D (activeCubeExponents S D b X) Ψ m f z W X H₀ slots lists a := by
  unfold markedReopenedCubeBin activeCubeExponents
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hlarge : b*X<(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3 := by
    exact lt_of_not_ge (fun hh=>hn (Finset.mem_filter.mpr ⟨hv,hh⟩))
  have hN : 0<(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ) :=
    lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  have hsub : b*(X/(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3)<1 := by
    rw [←mul_div_assoc]
    exact (div_lt_one (pow_pos hN _)).mpr hlarge
  rw [marked_column_zero_of_subunit _ W b _ (div_pos hX (pow_pos hN _)) hW hsub,mul_zero]

theorem markedReopenedCubeBin_log_bins :
    markedReopenedCubeBin S D (activeCubeExponents S D b X) Ψ m f z W X H₀ slots lists a =
    ∑ j∈cubeLogRange b X,
      markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a := by
  unfold markedReopenedCubeBin
  dsimp only
  exact sum_activeCubeLogBins S D b X _

def markedShortCompletedSum (Ψrow : O→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (mark : Ideal O→ℂ) : ℂ :=
  ∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
    (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
      markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0

theorem original_marked_reopened_binned (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D) :
    (Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X =
    markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a) +
    ∑ j∈cubeLogRange b X,
      markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a := by
  rw [original_marked_split_to_bins S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [markedReopenedCubeBin_eq_active S D Ψ m f z W b X H₀ slots lists a hX hW,
    markedReopenedCubeBin_log_bins]
  rfl

theorem original_marked_binned_energy (hbad : fixedBadPrimes⊆S) (hSp : ∀ P∈S,Prime P)
    (hWc : HasCompactSupport W) (hX : 0<X) (hW : ∀ t,W t≠0→t≤b) (hD : b*X≤D) :
    ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 ≤
    2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2 +
    (cubeLogRange b X).card*∑ j∈cubeLogRange b X,
      ‖markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a‖^2) := by
  have hs := norm_add_sum_sq_le (cubeLogRange b X)
    (markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀
      (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a))
    (fun j=>markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m f z W X H₀ slots lists a)
  rw [←original_marked_reopened_binned S D Ψ m f z W b X H₀ slots lists a hbad hSp hWc hX hW hD] at hs
  have hn : ‖outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 =
      X*‖(Real.sqrt X:ℂ)⁻¹*outsideCanonicalMarkedRow S D hbad Ψ m f z slots lists a W X‖^2 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X),
      mul_pow,inv_pow,Real.sq_sqrt hX.le]
    field_simp
  rw [hn]
  convert mul_le_mul_of_nonneg_left hs hX.le using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0433

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondTailCost
Source SHA256: 68afe817a4d09a212df9f4746c01b7e51e630765a3e547fbed37bf116f709f65
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0434


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem residualPairWeight_bounded_test
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : O)
    (Hcol : Finset ι → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (G S T : Finset ι) :
    ‖residualPairWeight p hg Ψ Ψ m c d
      (fun U => Hcol (G ∪ U)) (fun U => Hcol (G ∪ U)) S T‖ ≤ B^2 := by
  simp only [residualPairWeight, norm_mul, norm_star, sourceSupportMobius_norm p hinj, one_mul]
  have hS := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (fun U => Hcol (G ∪ U)) S).trans (hcol _)
  have hT := (secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d
    (fun U => Hcol (G ∪ U)) T).trans (hcol _)
  simpa only [pow_two] using mul_le_mul hS hT (norm_nonneg _) hB

include hp hinj
theorem residualTailCost_bounded_test
    (F G E : Finset ι) (hEG : E ⊆ G) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (Hcol : Finset ι → ℂ) (B Y H lengthScale P : ℝ) (A : ℕ)
    (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) :
    residualTailCost p hg F G Ψ Ψ m c d
      (fun S => Hcol (G∪S))
      (fun S => Hcol (G∪S))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P ≤
      if primeProductNorm p G ≤ lengthScale then
        (128*lengthScale)^2 * (B^2 *
          (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) else 0 := by
  let C := B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let w := residualPairWeight p hg Ψ Ψ m c d
    (fun S => Hcol (G∪S))
    (fun S => Hcol (G∪S))
  have hsupp (S T : Finset ι) (hw : w S T ≠ 0) :
      primeProductNorm p G ≤ lengthScale ∧ primeProductNorm p E ≤ lengthScale ∧
      primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale := by
    obtain ⟨hS,hT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
    have hGS := hsupport (G ∪ S) hS
    have hGT := hsupport (G ∪ T) hT
    have hG := (primeProductNorm_mono p hp Finset.subset_union_left).trans hGS
    exact ⟨hG, (primeProductNorm_mono p hp hEG).trans hG,
      (primeProductNorm_mono p hp Finset.subset_union_right).trans hGS,
      (primeProductNorm_mono p hp Finset.subset_union_right).trans hGT⟩
  by_cases hG : primeProductNorm p G ≤ lengthScale
  · rw [ite_eq_left hG]
    calc
      _ ≤ ∑ S ∈ (F\G).powerset, ∑ T ∈ (F\G).powerset,
          if primeProductNorm p S ≤ lengthScale ∧ primeProductNorm p T ≤ lengthScale then C else 0 := by
        unfold residualTailCost
        apply Finset.sum_le_sum
        intro S hS
        apply Finset.sum_le_sum
        intro T hT
        by_cases hd : Disjoint S T
        · rw [ite_eq_left hd]
          dsimp only
          by_cases hw : w S T = 0
          · change ‖w S T‖ * _ ≤ _
            rw [hw, norm_zero, zero_mul]
            split_ifs <;> positivity
          · obtain ⟨_,hE,hSn,hTn⟩ := hsupp S T hw
            rw [ite_eq_left ⟨hSn,hTn⟩]
            have hn2 : ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 =
                primeProductNorm p S * primeProductNorm p T := active_norm_sq_disjoint p S T hd
            have hn : 1 ≤ ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖ := by
              have hpS := primeProductNorm_ge_one p hp S
              have hpT := primeProductNorm_ge_one p hp T
              have hpST : 1 ≤ primeProductNorm p S * primeProductNorm p T := one_le_mul_of_one_le_of_one_le hpS hpT
              rw [← hn2] at hpST
              nlinarith [norm_nonneg (eisEmbedding (∏ i : activeSupport T S, p i.val))]
            have hNe : 0 < ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 :=
              SecondPassIntegration.elementNorm_pos _ (primeSubsetGenerator_ne_zero _ _)
            have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2 *
                ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2 ≤ lengthScale^3 := by
              rw [primeSubsetGenerator_norm_eq_productNorm, hn2]
              have hST := mul_le_mul hSn hTn (FirstPassCubeLabels.primeProductNorm_pos p hp T).le
                (zero_le_one.trans hL)
              have hEST := mul_le_mul hE hST
                (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
                  (FirstPassCubeLabels.primeProductNorm_pos p hp T).le) (zero_le_one.trans hL)
              nlinarith
            have hscalar := tail_radial_scalar_le Y
              (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2)
              (‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖) lengthScale H P A hY hNe hn hL hden hH hP
            exact mul_le_mul (residualPairWeight_bounded_test p hg hinj Ψ hΨ m c d Hcol B hB hcol G S T)
              hscalar (by positivity) (sq_nonneg _)
        · rw [ite_eq_right hd]
          split_ifs <;> positivity
      _ = ((boundedPrimeSupports p (F\G) lengthScale).card : ℝ)^2 * C :=
        sum_pair_indicator (F\G).powerset (fun S => primeProductNorm p S ≤ lengthScale) C
      _ ≤ (128*lengthScale)^2 * C := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (boundedPrimeSupports_card p hinj (F\G) lengthScale hL) 2) hC
  · rw [ite_eq_right hG]
    have hz : residualTailCost p hg F G Ψ Ψ m c d
        (fun S => Hcol (G∪S))
        (fun S => Hcol (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E) Y H A P = 0 := by
      unfold residualTailCost
      apply Finset.sum_eq_zero
      intro S hS
      apply Finset.sum_eq_zero
      intro T hT
      by_cases hd : Disjoint S T
      · rw [ite_eq_left hd]
        have hw : w S T = 0 := by
          by_contra hw
          exact hG (hsupp S T hw).1
        change ‖w S T‖ * _ = 0
        rw [hw, norm_zero, zero_mul]
      · rw [ite_eq_right hd]
    exact hz.le

theorem secondSourceTailCost_bounded_test
    (F : Finset ι) (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
    (m c d : O) (Hcol : Finset ι → ℂ) (B Y H lengthScale P : ℝ) (A : ℕ)
    (hB : 0 ≤ B) (hY : 0 < Y) (hH : 0 ≤ H) (hP : 0 ≤ P) (hL : 1 ≤ lengthScale)
    (hcol : ∀ U, ‖Hcol U‖ ≤ B) (hsupport : ∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) :
    (∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
      residualTailCost p hg F G Ψ Ψ m c d
        (fun S => Hcol (G∪S))
        (fun S => Hcol (G∪S))
        (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A P) ≤
      (128*lengthScale)^4 * (B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  let C := B^2 * (Y*P*(1+lengthScale^3/Y)^2/(1+H)^A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h128 : 0 ≤ 128*lengthScale := by positivity
  calc
    _ ≤ ∑ G ∈ F.powerset, if primeProductNorm p G ≤ lengthScale then (128*lengthScale)^3*C else 0 := by
      apply Finset.sum_le_sum
      intro G hG
      by_cases hGn : primeProductNorm p G ≤ lengthScale
      · rw [ite_eq_left hGn]
        have heq : boundedPrimeSupports p G lengthScale = G.powerset := by
          apply Finset.filter_eq_self.mpr
          intro E hE
          exact (primeProductNorm_mono p hp (Finset.mem_powerset.mp hE)).trans hGn
        have hcard : (G.powerset.card : ℝ) ≤ 128*lengthScale := by
          simpa only [heq] using boundedPrimeSupports_card p hinj G lengthScale hL
        calc
          _ ≤ ∑ E : G.powerset, (128*lengthScale)^2*C := by
            apply Finset.sum_le_sum
            intro E hE
            have hr := residualTailCost_bounded_test p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
              Ψ hΨ m c d Hcol B Y H lengthScale P A hB hY hH hP hL hcol hsupport
            rw [ite_eq_left hGn] at hr
            have hc := secondSourceCommonCoefficient_norm_le_one p hp hg hinj Ψ hΨ m c d G E.val
            exact (mul_le_mul_of_nonneg_left hr (norm_nonneg _)).trans
              (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hC))
          _ = (G.powerset.card : ℝ)*((128*lengthScale)^2*C) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
          _ ≤ (128*lengthScale)*((128*lengthScale)^2*C) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (sq_nonneg _) hC)
          _ = _ := by ring
      · rw [ite_eq_right hGn]
        apply Finset.sum_nonpos
        intro E hE
        have hr := residualTailCost_bounded_test p hp hg hinj F G E.val (Finset.mem_powerset.mp E.property)
          Ψ hΨ m c d Hcol B Y H lengthScale P A hB hY hH hP hL hcol hsupport
        rw [ite_eq_right hGn] at hr
        exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hr
    _ = ((boundedPrimeSupports p F lengthScale).card : ℝ)*((128*lengthScale)^3*C) := by
      rw [← Finset.sum_filter]
      simp only [boundedPrimeSupports, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (128*lengthScale)*((128*lengthScale)^3*C) :=
      mul_le_mul_of_nonneg_right (boundedPrimeSupports_card p hinj F lengthScale hL)
        (mul_nonneg (pow_nonneg h128 _) hC)
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0434

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondWholeTail
Source SHA256: 23ca2cae2d42ece345eaa6f18d39d4e3ff1192b7508424e93e0a7e15f99206a5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0435



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_second_supported_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H lengthScale : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ lengthScale →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
        (128*lengthScale)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+lengthScale^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_secondSourceTail_bound order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Hcol W B Y H lengthScale hB hY hH hL hcol hsupp K hK
  exact (htail p hp hg hinj hc F Ψ m c d Hcol W Y H hY hH K hK).trans
    (secondSourceTailCost_bounded_test p hp hg hinj F Ψ hΨ m c d Hcol B Y H lengthScale
      (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) order hB hY hH (by positivity) hL hcol hsupp)

def supportedSecondRadius (d : O) (lengthScale Y H : ℝ) : ℝ :=
  childOuterRadius Y (‖eisEmbedding d‖^2 * lengthScale) lengthScale lengthScale lengthScale H

lemma supportedSecondRadius_eq (d : O) (lengthScale Y H : ℝ) :
    supportedSecondRadius d lengthScale Y H = ‖eisEmbedding d‖^2 * lengthScale^4 * H / Y := by
  unfold supportedSecondRadius childOuterRadius
  ring

theorem full_second_child_supported_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H lengthScale R : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ lengthScale →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) →
      supportedSecondRadius d lengthScale Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun _ E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*lengthScale)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+lengthScale^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H lengthScale R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H lengthScale hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hGS' := hsupp (G ∪ S) hGS
  have hGT' := hsupp (G ∪ T) hGT
  have hGn := (primeProductNorm_mono p hp Finset.subset_union_left).trans hGS'
  have hEn := (primeProductNorm_mono p hp (Finset.mem_powerset.mp E.property)).trans hGn
  have hSn := (primeProductNorm_mono p hp Finset.subset_union_right).trans hGS'
  have hTn := (primeProductNorm_mono p hp Finset.subset_union_right).trans hGT'
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde : d*e ≠ 0 := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have hL0 : 0 < lengthScale := lt_of_lt_of_le zero_lt_one hL
  have heN : ‖eisEmbedding e‖^2 ≤ lengthScale := by
    simpa only [e,primeSubsetGenerator_norm_eq_productNorm] using hEn
  have hdeN : ‖eisEmbedding (d*e)‖^2 ≤ ‖eisEmbedding d‖^2 * lengthScale := by
    simp only [map_mul,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_left heN (sq_nonneg _)
  apply childFrequencyBall_raw_tail p hp Y (‖eisEmbedding d‖^2*lengthScale)
    lengthScale lengthScale lengthScale H hY (mul_pos hdN hL0) hL0 hL0 hL0 hH
    (d*e) e hde he hdeN heN S T hST hSn hTn k
  intro hsmall
  apply hk
  apply (mem_childFrequencyBall (d*e) hde R k).mpr
  exact ((mem_childFrequencyBall (d*e) hde _ k).mp hsmall).trans hR

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0435

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondWholeCutoff
Source SHA256: f8ac8aa6d25d5616afdb40706fbb6a668329f3726423d921ec9ec7241133a02d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0436


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_whole_column_denominator {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal] (G E S T : Finset ι)
    (hEG : E ⊆ G) (hGS : Disjoint G S) (hGT : Disjoint G T)
    (L : ℝ) (hL : 0 ≤ L)
    (hS : primeProductNorm p (G ∪ S) ≤ L)
    (hT : primeProductNorm p (G ∪ T) ≤ L) :
    (primeProductNorm p E)^2 * (primeProductNorm p S * primeProductNorm p T) ≤ L^2 := by
  have hE := primeProductNorm_mono p hp hEG
  have hE0 := (primeProductNorm_pos p hp E).le
  have hS0 := (primeProductNorm_pos p hp S).le
  have hT0 := (primeProductNorm_pos p hp T).le
  rw [primeProductNorm_union p G S hGS] at hS
  rw [primeProductNorm_union p G T hGT] at hT
  calc
    _ ≤ (primeProductNorm p G)^2 * (primeProductNorm p S * primeProductNorm p T) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hE0 hE 2) (mul_nonneg hS0 hT0)
    _ = (primeProductNorm p G * primeProductNorm p S) *
      (primeProductNorm p G * primeProductNorm p T) := by ring
    _ ≤ L*L := mul_le_mul hS hT (mul_nonneg (primeProductNorm_pos p hp G).le hT0) hL
    _ = _ := by ring

def wholeSecondRadius (d : O) (L Y H : ℝ) : ℝ := ‖eisEmbedding d‖^2 * L^2 * H / Y

theorem full_second_whole_column_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H L R : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ L →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ L) →
      wholeSecondRadius d L Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun _ E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*L)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+L^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H L R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H L hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hdGS : Disjoint G S := Finset.disjoint_left.mpr (by
    intro i hiG hiS
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hiS)).2 hiG)
  have hdGT : Disjoint G T := Finset.disjoint_left.mpr (by
    intro i hiG hiT
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hT) hiT)).2 hiG)
  have hden := second_whole_column_denominator p hp G E.val S T
    (Finset.mem_powerset.mp E.property) hdGS hdGT L (zero_le_one.trans hL)
    (hsupp _ hGS) (hsupp _ hGT)
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have heN : 0 < ‖eisEmbedding e‖^2 := SecondPassIntegration.elementNorm_pos e he
  have henorm : ‖eisEmbedding e‖^2 = primeProductNorm p E.val :=
    primeSubsetGenerator_norm_eq_productNorm p E.val
  have hkR := (outside_childFrequencyBall (d*e) hde R k hk).le
  have hR' : ‖eisEmbedding d‖^2 * L^2 * H ≤
      Y * (‖eisEmbedding d‖^2 * ‖eisEmbedding e‖^2 * ‖eisEmbedding k‖^2) := by
    have hh := (div_le_iff₀ hY).mp hR
    have hh' := mul_le_mul_of_nonneg_right hkR hY.le
    simp only [map_mul,norm_mul,mul_pow] at hh'
    nlinarith
  have hbound : H * (‖eisEmbedding e‖^2 *
      (primeProductNorm p S * primeProductNorm p T)) ≤ Y*‖eisEmbedding k‖^2 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hdN heN)).mp
    have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg hdN.le hH)
    rw [←henorm] at hh
    nlinarith [hh,hR']
  rw [active_norm_sq_disjoint p S T hST,div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos heN (mul_pos (primeProductNorm_pos p hp S)
    (primeProductNorm_pos p hp T)))).mpr
  exact hbound

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0436

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondCorrelatedCutoff
Source SHA256: ffd4c0bafb330437708928fa11bd28d4b8a3efd90d9beef57c916f86593c309a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0437


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_correlated_column_denominator {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (G E S T : Finset ι) (hGS : Disjoint G S) (hGT : Disjoint G T)
    (L : ℝ) (hL : 0 ≤ L)
    (hS : primeProductNorm p (G ∪ S) ≤ L)
    (hT : primeProductNorm p (G ∪ T) ≤ L) :
    (primeProductNorm p E)^2 * (primeProductNorm p S * primeProductNorm p T) ≤
      (primeProductNorm p E/primeProductNorm p G)^2 * L^2 := by
  have hG0 := (primeProductNorm_pos p hp G).ne'
  have hbound := second_whole_column_denominator p hp G G S T Finset.Subset.rfl hGS hGT L hL hS hT
  calc
    _ = (primeProductNorm p E/primeProductNorm p G)^2 *
      ((primeProductNorm p G)^2 * (primeProductNorm p S*primeProductNorm p T)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (sq_nonneg _)

def correlatedSecondRadius {ι : Type*} [DecidableEq ι] (p : ι → O)
    (d : O) (G E : Finset ι) (L Y H : ℝ) : ℝ :=
  ‖eisEmbedding d‖^2 * (primeProductNorm p E/primeProductNorm p G)^2 * L^2 * H / Y

theorem full_second_correlated_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H L : ℝ) (R : Finset ι → Finset ι → ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ L →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ L) →
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        correlatedSecondRadius p d G E.val L Y H ≤ R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun G E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) (R G E))‖ ≤
        (128*L)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+L^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H L R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H L hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hdGS : Disjoint G S := Finset.disjoint_left.mpr (by
    intro i hiG hiS
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hiS)).2 hiG)
  have hdGT : Disjoint G T := Finset.disjoint_left.mpr (by
    intro i hiG hiT
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hT) hiT)).2 hiG)
  have hden := second_correlated_column_denominator p hp G E.val S T hdGS hdGT L (zero_le_one.trans hL)
    (hsupp _ hGS) (hsupp _ hGT)
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have heN : 0 < ‖eisEmbedding e‖^2 := SecondPassIntegration.elementNorm_pos e he
  have henorm : ‖eisEmbedding e‖^2 = primeProductNorm p E.val :=
    primeSubsetGenerator_norm_eq_productNorm p E.val
  have hkR := (outside_childFrequencyBall (d*e) hde (R G E.val) k hk).le
  have hR' : ‖eisEmbedding d‖^2 * (primeProductNorm p E.val/primeProductNorm p G)^2 * L^2 * H ≤
      Y * (‖eisEmbedding d‖^2 * ‖eisEmbedding e‖^2 * ‖eisEmbedding k‖^2) := by
    have hh := (div_le_iff₀ hY).mp (hR G hG E)
    have hh' := mul_le_mul_of_nonneg_right hkR hY.le
    simp only [map_mul,norm_mul,mul_pow] at hh'
    nlinarith
  have hbound : H * (‖eisEmbedding e‖^2 *
      (primeProductNorm p S * primeProductNorm p T)) ≤ Y*‖eisEmbedding k‖^2 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hdN heN)).mp
    have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg hdN.le hH)
    rw [←henorm] at hh
    rw [←henorm] at hR'
    nlinarith [hh,hR']
  rw [active_norm_sq_disjoint p S T hST,div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos heN (mul_pos (primeProductNorm_pos p hp S)
    (primeProductNorm_pos p hp T)))).mpr
  exact hbound

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0437

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ShortCompletionEnergy
Source SHA256: 7d876ef4e5731a96bb47bf146004ea212ecb0af6742f34fa5720d7b4f2434ac4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0438


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem markedShortCompletedSum_eq (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) (mark : Ideal O→ℂ) :
    markedShortCompletedSum Ψ W X H₀ mark = ∑H∈shortCubeRange H₀,
      (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
        markedCompletedT Ψ W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) := by
  unfold markedShortCompletedSum
  rw [tsum_eq_sum (s:=shortCubeRange H₀)]
  · exact Finset.sum_congr rfl (fun H hH => ite_eq_left ((mem_shortCubeRange H₀ H).mp hH).2)
  · intro H hH
    by_cases hz : H=0
    · simp [hz]
    · have hn : ¬(Ideal.absNorm H:ℝ)<H₀ := fun hn => hH ((mem_shortCubeRange H₀ H).mpr ⟨hz,hn⟩)
      exact ite_eq_right hn

theorem marked_short_completed_energy {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (mark : κ→Ideal O→ℂ) (W : ℝ → ℂ) (X H₀ A : ℝ) (hA : 0≤A)
    (hcompleted : ∀H∈shortCubeRange H₀,
      (∑k,‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2)≤A) :
    (∑k,‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2)≤
      A*(256*(columnDyadicLength H₀+1:ℝ))^2 := by
  let S := shortCubeRange H₀
  let lengthScale : ℝ := ∑H∈S,1/(Ideal.absNorm H:ℝ)
  have hS (H : Ideal O) (hH : H∈S) : H≠0 := ((mem_shortCubeRange H₀ H).mp hH).1
  have hn (H : Ideal O) (hH : H∈S) : 0<(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS H hH (Ideal.absNorm_eq_zero_iff.mp hz))
  have hL : 0≤lengthScale := Finset.sum_nonneg (fun H hH => by positivity)
  have hb (k : κ) : ‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2≤
      lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 := by
    rw [markedShortCompletedSum_eq]
    apply (ideal_reciprocal_cauchy S hS _).trans
    apply mul_le_mul_of_nonneg_left _ hL
    apply Finset.sum_le_sum
    intro H hH
    rw [norm_mul]
    calc
      _ ≤ (Ideal.absNorm H:ℝ)*((1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖)^2 := by
        gcongr
        exact cube_inverse_weight_norm (Ψ k) (hΨ k) H
      _ = _ := by field_simp [(hn H hH).ne']
  have hsum : (∑k,‖markedShortCompletedSum (Ψ k) W X H₀ (mark k)‖^2)≤A*lengthScale^2 := by
    calc
      _ ≤ ∑k,lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 :=
        Finset.sum_le_sum (fun k _ => hb k)
      _ = lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*∑k,‖markedCompletedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark k (H^3*I))‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro H hH
        rw [←Finset.mul_sum]
      _ ≤ lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*A := by
        gcongr with H hH
        exact hcompleted H hH
      _ = A*lengthScale^2 := by rw [←Finset.sum_mul]; change lengthScale*(lengthScale*A)=A*lengthScale^2; ring
  have hbound : lengthScale≤256*(columnDyadicLength H₀+1:ℝ) :=
    finite_inverse_norm_sum S H₀ hS (fun H hH => ((mem_shortCubeRange H₀ H).mp hH).2.le)
  exact hsum.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hbound 2) hA)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0438

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SourceHybrid
Source SHA256: ac0fabf6238766c0b426e7987abd0f5af2bf9fc3b601e06fb418a6aefd1d5469
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0439


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def sourceGridCoefficient (beta : Ideal Eis → Ideal Eis → ℂ)
    (t c m h : Ideal Eis) : ℂ := beta (c * m) ((c * h) * t ^ 2)

theorem reconstructed_fixed_square_grid
    (D : Finset HybridColumnData) (t : Ideal Eis) (hD : ∀ d ∈ D, d.square = t)
    (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    (∑ d ∈ D, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d) =
      (if IsCoprime k t then 1 else 0) *
        maskedGridHybridRow (hybridGridSupport D) Pset a (sourceGridCoefficient beta t) t k := by
  unfold maskedGridHybridRow hybridGridSupport
  rw [Finset.sum_image]
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro P hP
    simp only [reconstructedHybridTerm, HybridColumnData.gridIndex,
      sourceGridCoefficient, hD d hd]
    ac_rfl
  · intro d hd e he hg
    exact HybridColumnData.gridIndex_injective_on_square t (hD d hd) (hD e he) hg

theorem reconstructed_fixed_square_energy_le
    (D : Finset HybridColumnData) (t : Ideal Eis) (hD : ∀ d ∈ D, d.square = t)
    (rows Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) :
    (∑ k ∈ rows, ‖∑ d ∈ D, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d‖ ^ 2) ≤
      ∑ k ∈ rows,
        ‖maskedGridHybridRow (hybridGridSupport D) Pset a (sourceGridCoefficient beta t) t k‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  rw [reconstructed_fixed_square_grid D t hD Pset a beta k]
  by_cases hkt : IsCoprime k t
  · simp only [hkt, ite_true, one_mul, le_refl]
  · simp only [hkt, ite_false, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

theorem finite_double_row_energy {I J : Type*} [Fintype I] [Fintype J]
    (rows : Finset (Ideal Eis)) (F : I → J → Ideal Eis → ℂ) (E : ℝ) (_hE : 0 ≤ E)
    (hF : ∀ i j, (∑ k ∈ rows, ‖F i j k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ i, ∑ j, F i j k‖ ^ 2) ≤
      ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) ^ 2 * E := by
  have hk (k : Ideal Eis) :
      ‖∑ i, ∑ j, F i j k‖ ^ 2 ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
          ∑ i, ∑ j, ‖F i j k‖ ^ 2 := by
    simpa only [one_mul, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul] using
      bounded_coefficient_sum_sq (fun _ : I × J => 1) (fun u => F u.1 u.2 k) (by simp)
  calc
    _ ≤ ∑ k ∈ rows, ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
        ∑ i, ∑ j, ‖F i j k‖ ^ 2 := Finset.sum_le_sum (fun k _ => hk k)
    _ = ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
        ∑ i, ∑ j, ∑ k ∈ rows, ‖F i j k‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ ≤ ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) * ∑ _i : I, ∑ _j : J, E := by
      gcongr with i hi j hj
      exact hF i j
    _ = _ := by simp; ring

theorem supportedHybridRow_energy_log (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C₀ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B *
        CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2 *
          (columnDyadicLength N + 1 : ℝ) ^ 2 * (columnDyadicLength B + 1 : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hfixed⟩ := hybrid_fixed_square_grid_energy ε hε
  refine ⟨256 ^ 2 * C₁, by positivity, ?_⟩
  intro K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  let nset := S.image Prod.fst
  let E := C₁ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B *
    CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2
  let F (j : Fin (columnDyadicLength B + 1)) (i : Fin (columnDyadicLength N + 1))
      (k : Ideal Eis) : ℂ :=
    ∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
      ∑ d ∈ hybridCommonBlock S N i t, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hnset : ∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨⟨(hS p hp).1, (hS p hp).2.1⟩, (hS p hp).2.2.2.1⟩
  have hBsup : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B := fun p hp => (hS p hp).2.2.2.2
  have hlen : ∀ p ∈ S, (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B :=
    fun p hp => (hS p hp).2.2.2
  have hlabel (j : Fin (columnDyadicLength B + 1))
      (i : Fin (columnDyadicLength N + 1)) :
      (∑ k ∈ rows, ‖F j i k‖ ^ 2) ≤ 256 ^ 2 * E := by
    let Td := divisorDyadicScale j.val
    have hTd : 0 < Td := by dsimp only [Td]; linarith [divisorDyadicScale_ge_one j.val]
    have htEnergy (t : Ideal Eis) (ht : t ∈ divisorDyadicBin (hybridSquarePool S) B j) :
        (∑ k ∈ rows, ‖∑ d ∈ hybridCommonBlock S N i t,
          ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d‖ ^ 2) ≤ E / Td ^ 2 := by
      let D := hybridCommonBlock S N i t
      have hD (d : HybridColumnData) (hd : d ∈ D) :
          d.square = t ∧ divisorDyadicScale i.val ≤ (Ideal.absNorm d.common : ℝ) ∧
          (Ideal.absNorm d.common : ℝ) ≤ 2 * divisorDyadicScale i.val ∧
          d.common * d.residualN ∈ nset ∧
          (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B := by
        obtain ⟨hdS, hdt, hdi⟩ := Finset.mem_filter.mp hd
        have hdorig := (mem_hybridColumnSupport S d).mp hdS
        have hb := hybridCommonBlock_bounds S N B (by linarith) (by linarith) hlen i j t ht d hd
        exact ⟨hdt, hb.1, hb.2.1, Finset.mem_image.mpr ⟨d.reconstruct, hdorig, rfl⟩,
          hBsup d.reconstruct hdorig⟩
      have hβ : ∀ d ∈ D, ‖sourceGridCoefficient beta t d.common d.residualN d.residualB‖ ≤ 1 := by
        intro d hd
        have hdo := (mem_hybridColumnSupport S d).mp (Finset.mem_filter.mp hd).1
        simpa only [sourceGridCoefficient, ← (hD d hd).1, HybridColumnData.reconstruct] using
          hbeta d.reconstruct hdo
      have hfix := hfixed K N B L (divisorDyadicScale i.val) Td hK hN hB
        (divisorDyadicScale_ge_one i.val) (divisorDyadicScale_ge_one j.val) t
        (divisorDyadicBin_bounds (hybridSquarePool S) B (hybridSquarePool_bounds S B hBsup) j t ht).1
        rows nset Pset D a (sourceGridCoefficient beta t) hrows hnset hP ha hD hβ
      apply (reconstructed_fixed_square_energy_le D t (fun d hd => (hD d hd).1) rows Pset a beta).trans
      convert hfix using 1 ; dsimp only [E] ; ring
    have he := hybrid_square_dyad_energy S B hBsup j rows
      (fun t k => ∑ d ∈ hybridCommonBlock S N i t,
        ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d)
      (E / Td ^ 2) (div_nonneg hE (sq_nonneg _)) htEnergy
    calc
      _ ≤ (256 * Td) ^ 2 * (E / Td ^ 2) := he
      _ = 256 ^ 2 * E := by field_simp
  have hrow (k : Ideal Eis) (hk : k ∈ rows) :
      supportedHybridRow S Pset a beta k = ∑ j, ∑ i, F j i k := by
    rw [supportedHybridRow_reconstruct S Pset
      (fun p hp => ⟨(hS p hp).1,
        primaryGenerator_ne_zero_ideal p.2 (hS p hp).2.2.1,
        (hS p hp).2.1, (hS p hp).2.2.1⟩)
      (fun P hPP => (hP P hPP).1.2) a beta k (hrows k hk).1]
    exact hybrid_dyadic_reindex S N B _
  calc
    _ = ∑ k ∈ rows, ‖∑ j, ∑ i, F j i k‖ ^ 2 :=
      Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow k hk))
    _ ≤ ((Fintype.card (Fin (columnDyadicLength B + 1)) : ℝ) *
        (Fintype.card (Fin (columnDyadicLength N + 1)) : ℝ)) ^ 2 * (256 ^ 2 * E) :=
      finite_double_row_energy rows F (256 ^ 2 * E) (by positivity) hlabel
    _ = _ := by simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, E]; ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0439

/-! Original module: OAI.NumberTheory.DirichletL.Descent.HybridBound
Source SHA256: e11e3939ce1dc7d7ed14407cdd3462c9d8554a681cdb38d73eae7a57f803a99c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0440


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

private theorem hybrid_log_cost_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
      K ^ (ε / 9) * (K * (N * B) * N) ^ (ε / 9) *
        (columnDyadicLength K + 1 : ℝ) ^ 2 * (columnDyadicLength N + 1 : ℝ) ^ 2 *
          (columnDyadicLength B + 1 : ℝ) ^ 2 ≤ C * (K * N * B) ^ ε := by
  let δ := ε / 9
  let A := 2 + 1 / (δ * Real.log 2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A ^ 6, pow_pos hA 6, ?_⟩
  intro K N B hK hN hB
  let Q := K * N * B
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK hN) hB
  have hQ0 : 0 < Q := by linarith
  have hKQ : K ≤ Q :=
    (le_mul_of_one_le_right (by linarith : 0 ≤ K) hN).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ K * N) hB)
  have hNQ : N ≤ Q :=
    (le_mul_of_one_le_left (by linarith : 0 ≤ N) hK).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ K * N) hB)
  have hBQ : B ≤ Q := le_mul_of_one_le_left (by linarith)
    (one_le_mul_of_one_le_of_one_le hK hN)
  have hquad : K * (N * B) * N ≤ Q ^ 2 := by
    calc
      _ = Q * N := by dsimp only [Q]; ring
      _ ≤ Q * Q := mul_le_mul_of_nonneg_left hNQ hQ0.le
      _ = _ := by ring
  have hlog (Y : ℝ) (hY : 1 ≤ Y) (hYQ : Y ≤ Q) :
      (columnDyadicLength Y + 1 : ℝ) ≤ A * Q ^ δ := by
    exact (columnDyadicLength_small_power δ hδ Y hY).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hYQ hδ.le) hA.le)
  have hpow2 : (Q ^ 2) ^ δ = (Q ^ δ) ^ 2 := by
    rw [← Real.rpow_natCast_mul hQ0.le 2 δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    ring
  have hpow9 : (Q ^ δ) ^ 9 = Q ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    dsimp only [δ]
    ring
  calc
    _ ≤ Q ^ δ * (Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 := by
      have hbase := Real.rpow_le_rpow (by positivity : 0 ≤ K * (N * B) * N) hquad hδ.le
      rw [hpow2] at hbase
      gcongr
      · exact hlog K hK hKQ
      · exact hlog N hN hNQ
      · exact hlog B hB hBQ
    _ = A ^ 6 * (Q ^ δ) ^ 9 := by ring
    _ = _ := by rw [hpow9]

theorem supportedHybridRow_energy_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₀, hC₀, he⟩ := supportedHybridRow_energy_log (ε / 9) (by positivity)
  obtain ⟨C₁, hC₁, hlogs⟩ := hybrid_log_cost_bound ε hε
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  have hb := he K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  apply hb.trans
  calc
    _ = C₀ * (K ^ (ε / 9) * (K * (N * B) * N) ^ (ε / 9) *
        (columnDyadicLength K + 1 : ℝ) ^ 2 * (columnDyadicLength N + 1 : ℝ) ^ 2 *
          (columnDyadicLength B + 1 : ℝ) ^ 2) *
        (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by ring
    _ ≤ C₀ * (C₁ * (K * N * B) ^ ε) * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hlogs K N B hK hN hB) hC₀.le)
            (by positivity)) (by linarith)) hs
    _ = _ := by ring

theorem hybridRow_energy_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows nset bset Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C, hC, he⟩ := supportedHybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B L hK hN hB rows nset bset Pset a beta hrows hn hb hP ha hbeta
  have hprod : ∀ p ∈ nset ×ˢ bset,
      Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B := by
    intro p hp
    obtain ⟨hpn, hpb⟩ := Finset.mem_product.mp hp
    exact ⟨(hn p.1 hpn).1.1, (hn p.1 hpn).1.2, (hb p.2 hpb).1,
      (hn p.1 hpn).2, (hb p.2 hpb).2⟩
  have hh := he K N B L hK hN hB rows (nset ×ˢ bset) Pset a beta hrows hprod hP ha
    (fun p hp => hbeta p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
  simpa only [supportedHybridRow_product] using hh

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0440

/-! Original module: OAI.NumberTheory.DirichletL.Descent.Sharp
Source SHA256: 2a51870c9215041ac9fd9366adfdcd2ef974aca2b338078000b5aa66f76dd708
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0441



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_sharp_cubic_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      (K * N * B) ^ (ε / 2) * CubicSieve.sieveNorm N (2 * L) ≤
        C * (K * N * B * L) ^ ε * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := CubicSieve.sieveNorm_sharp (ε / 2) (by positivity)
  refine ⟨2 * C * (2 : ℝ) ^ (ε / 2), by positivity, ?_⟩
  intro K N B L hK hN hB hL
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  let Q := K * N * B * L
  have hQ0 : 0 < Q := by dsimp only [Q]; positivity
  have hKNB : K * N * B ≤ Q := le_mul_of_one_le_right (by positivity) hL
  have hNL : N * L ≤ Q := by
    have hKB : 1 ≤ K * B := one_le_mul_of_one_le_of_one_le hK hB
    have hh := le_mul_of_one_le_left (by positivity : 0 ≤ N * L) hKB
    convert hh using 1 ; dsimp only [Q] ; ring
  have hdouble (t : ℝ) : (N * (2 * L)) ^ t = (2 : ℝ) ^ t * (N * L) ^ t := by
    rw [show N * (2 * L) = 2 * (N * L) by ring, Real.mul_rpow (by norm_num) (by positivity)]
  have h23 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  have hshape : N + 2 * L + (N * (2 * L)) ^ (2 / 3 : ℝ) ≤
      2 * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
    rw [hdouble]
    have hh := mul_le_mul_of_nonneg_right h23 (Real.rpow_nonneg (by positivity : 0 ≤ N * L) (2 / 3 : ℝ))
    linarith
  have hcost : (K * N * B) ^ (ε / 2) * (N * L) ^ (ε / 2) ≤ Q ^ ε := by
    calc
      _ ≤ Q ^ (ε / 2) * Q ^ (ε / 2) := by
        exact mul_le_mul (Real.rpow_le_rpow (by positivity) hKNB (by positivity))
          (Real.rpow_le_rpow (by positivity) hNL (by positivity))
          (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hQ0.le _)
      _ = _ := by rw [← Real.rpow_add hQ0]; congr 1; ring
  have hh := hb N (2 * L) hN (by linarith)
  calc
    _ ≤ (K * N * B) ^ (ε / 2) *
        (C * (N * (2 * L)) ^ (ε / 2) * (N + 2 * L + (N * (2 * L)) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by positivity) _)
    _ ≤ (K * N * B) ^ (ε / 2) *
        (C * (N * (2 * L)) ^ (ε / 2) * (2 * (N + L + (N * L) ^ (2 / 3 : ℝ)))) := by
      gcongr
    _ = (2 * C * (2 : ℝ) ^ (ε / 2)) *
        ((K * N * B) ^ (ε / 2) * (N * L) ^ (ε / 2)) * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
      rw [hdouble]
      ring
    _ ≤ _ := by gcongr

theorem supportedHybridRow_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C * (K * N * B * L) ^ ε * (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C0, hC0, he⟩ := supportedHybridRow_energy_sieve_norm (ε / 2) (by positivity)
  obtain ⟨C1, hC1, hc⟩ := hybrid_sharp_cubic_factor ε hε
  refine ⟨C0 * C1, mul_pos hC0 hC1, ?_⟩
  intro K N B L hK hN hB hL rows S Pset a beta hrows hS hP ha hbeta
  apply (he K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta).trans
  have hh := mul_le_mul_of_nonneg_left (hc K N B L hK hN hB hL)
    (show 0 ≤ C0 * (K + N * B) * B by positivity)
  convert hh using 1 <;> ring

theorem hybridRow_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
    ∀ (rows nset bset Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
      C * (K * N * B * L) ^ ε * (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C0, hC0, he⟩ := hybridRow_energy_sieve_norm (ε / 2) (by positivity)
  obtain ⟨C1, hC1, hc⟩ := hybrid_sharp_cubic_factor ε hε
  refine ⟨C0 * C1, mul_pos hC0 hC1, ?_⟩
  intro K N B L hK hN hB hL rows nset bset Pset a beta hrows hn hb hP ha hbeta
  apply (he K N B L hK hN hB rows nset bset Pset a beta hrows hn hb hP ha hbeta).trans
  have hh := mul_le_mul_of_nonneg_left (hc K N B L hK hN hB hL)
    (show 0 ≤ C0 * (K + N * B) * B by positivity)
  convert hh using 1 <;> ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0441

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SlotProducts
Source SHA256: 1ac5909236389b88d7698a901f54b4f73b88a29d918382b835a298e4e450c55c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0442


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def slotTupleProduct (p : ι → Ideal Eis) : Ideal Eis := ∏ i, p i

theorem slotTupleProduct_injective_on
    (L : ι → Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P ∈ L i, Prime P) :
    Set.InjOn (slotTupleProduct (ι := ι)) {p | ∀ i, p i ∈ L i} := by
  intro p hpL q hqL he
  funext i
  change (∏ i, p i) = ∏ i, q i at he
  have hdiv : p i ∣ ∏ j, q j := by
    rw [← he]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  obtain ⟨j, hj, hd⟩ := ((hp i (p i) (hpL i)).dvd_finsetProd_iff q).mp hdiv
  have hpq : p i = q j := associated_iff_eq.mp
    ((hp i (p i) (hpL i)).associated_of_dvd (hp j (q j) (hqL j)) hd)
  have hij : i = j := by
    by_contra hne
    exact Finset.disjoint_left.mp (hL hne) (hpL i) (hpq.symm ▸ hqL j)
  simpa only [← hij] using hpq

omit [DecidableEq ι] in
theorem slotTupleProduct_admissible
    (L : ι → Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P ∈ L i, Prime P)
    (hgen : ∀ i, ∀ P ∈ L i, primaryGenerator P ≠ 0)
    (p : ι → Ideal Eis) (hpL : ∀ i, p i ∈ L i) :
    CubicSieve.Admissible (slotTupleProduct p) := by
  constructor
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      have hpi := hp i (p i) (hpL i)
      have hpj := hp j (p j) (hpL j)
      let : (p i).IsMaximal := (Ideal.isPrime_of_prime hpi).isMaximal hpi.ne_zero
      let : (p j).IsMaximal := (Ideal.isPrime_of_prime hpj).isMaximal hpj.ne_zero
      apply (Ideal.isCoprime_of_isMaximal ?_).isRelPrime
      intro he
      exact Finset.disjoint_left.mp (hL hij) (hpL i) (he.symm ▸ hpL j)
    · intro i hi
      exact (hp i (p i) (hpL i)).squarefree
  · change primaryGeneratorHom (∏ i, p i) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hgen i (p i) (hpL i))

def slotProductCoefficient (tuples : Finset (ι → Ideal Eis))
    (a : (ι → Ideal Eis) → ℂ) (P : Ideal Eis) : ℂ :=
  ∑ p ∈ tuples, if slotTupleProduct p = P then a p else 0

omit [DecidableEq ι] in
theorem slotProductCoefficient_at_product
    (tuples : Finset (ι → Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)))
    (a : (ι → Ideal Eis) → ℂ) (p : ι → Ideal Eis) (hp : p ∈ tuples) :
    slotProductCoefficient tuples a (slotTupleProduct p) = a p := by
  unfold slotProductCoefficient
  rw [Finset.sum_eq_single p]
  · simp
  · intro q hq hqp
    exact ite_eq_right (fun he => hqp (hinj hq hp he))
  · exact fun hn => (hn hp).elim

omit [DecidableEq ι] in
theorem active_slot_hybrid_reindex
    (tuples : Finset (ι → Ideal Eis))
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)))
    (nset bset : Finset (Ideal Eis)) (a : (ι → Ideal Eis) → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    (∑ p ∈ tuples, a p / (Real.sqrt (Ideal.absNorm (slotTupleProduct p) : ℝ) : ℂ) *
      (if IsCoprime k (slotTupleProduct p) then 1 else 0) *
        hybridInner nset bset beta k (slotTupleProduct p)) =
      hybridRow (tuples.image slotTupleProduct) nset bset (slotProductCoefficient tuples a) beta k := by
  rw [hybridRow, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro p hp
  rw [slotProductCoefficient_at_product tuples hinj a p hp]

theorem active_slot_hybrid_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B V : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (L : ι → Finset (Ideal Eis)),
      Pairwise (fun i j => Disjoint (L i) (L j)) →
      (∀ i, ∀ P ∈ L i, Prime P) → (∀ i, ∀ P ∈ L i, primaryGenerator P ≠ 0) →
    ∀ (tuples : Finset (ι → Ideal Eis)), (∀ p ∈ tuples, ∀ i, p i ∈ L i) →
      (∀ p ∈ tuples, V ≤ (Ideal.absNorm (slotTupleProduct p) : ℝ) ∧
        (Ideal.absNorm (slotTupleProduct p) : ℝ) ≤ 2 * V) →
    ∀ (rows nset bset : Finset (Ideal Eis)) (a : (ι → Ideal Eis) → ℂ)
      (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ p ∈ tuples, ‖a p‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖∑ p ∈ tuples,
        a p / (Real.sqrt (Ideal.absNorm (slotTupleProduct p) : ℝ) : ℂ) *
        (if IsCoprime k (slotTupleProduct p) then 1 else 0) *
          hybridInner nset bset beta k (slotTupleProduct p)‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * V) := by
  obtain ⟨C, hC, he⟩ := hybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B V hK hN hB L hL hp hgen tuples htuples hnorm rows nset bset a beta
    hrows hn hb ha hbeta
  have hinj : Set.InjOn slotTupleProduct (↑tuples : Set (ι → Ideal Eis)) :=
    (slotTupleProduct_injective_on L hL hp).mono htuples
  have hP : ∀ P ∈ tuples.image slotTupleProduct,
      CubicSieve.Admissible P ∧ V ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * V := by
    intro P hP
    obtain ⟨p, hpT, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨slotTupleProduct_admissible L hL hp hgen p (htuples p hpT), hnorm p hpT⟩
  have hcoeff : ∀ P ∈ tuples.image slotTupleProduct, ‖slotProductCoefficient tuples a P‖ ≤ 1 := by
    intro P hP
    obtain ⟨p, hpT, rfl⟩ := Finset.mem_image.mp hP
    rw [slotProductCoefficient_at_product tuples hinj a p hpT]
    exact ha p hpT
  simp_rw [active_slot_hybrid_reindex tuples hinj nset bset a beta]
  exact he K N B V hK hN hB rows nset bset (tuples.image slotTupleProduct)
    (slotProductCoefficient tuples a) beta hrows hn hb hP hcoeff hbeta

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0442

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CommonMeasure
Source SHA256: 8508f4b31a8921ade61f0cfe0015d5bdeedd49fcbb03e9f1aae8c425dbd0c7c8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0443


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open MeasureTheory CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem common_measure_energy {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (b : Ω → ℂ) (φ : κ → Ω → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖) μ)
    (hφ : ∀ k, Integrable (fun t => b t * φ k t) μ)
    (hbound : ∀ t, (∑ k, ‖φ k t‖ ^ 2) ≤ E) :
    (∑ k, ‖∫ t, b t * φ k t ∂μ‖ ^ 2) ≤ E * (∫ t, ‖b t‖ ∂μ) ^ 2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : Ω → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t * φ k t)
  have hF (t : Ω) : ‖F t‖ ≤ ‖b t‖ * Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE]
    change (∑ k, ‖b t * φ k t‖ ^ 2) ≤ ‖b t‖ ^ 2 * E
    simp only [norm_mul, mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫ t, F t ∂μ) = e.symm (fun k => ∫ t, b t * φ k t ∂μ) := by
    rw [show F = (fun t => e.symm (fun k => b t * φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t, b t * φ k t ∂μ)‖ ≤
      (∫ t, ‖b t‖ ∂μ) * Real.sqrt E := by
    rw [← he, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE] at hs
  simpa [e, mul_comm] using hs

theorem integrated_hybridRow_energy {Ω : Type*} [MeasurableSpace Ω]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ v ∈ bset, primaryGenerator v ≠ 0 ∧ (Ideal.absNorm v : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
    ∀ (μ : Measure Ω) (b : Ω → ℂ)
      (a : Ω → Ideal Eis → ℂ) (beta : Ω → Ideal Eis → Ideal Eis → ℂ)
      (rowPhase : Ideal Eis → Ω → ℂ) (m : ℂ),
      Integrable b μ →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => a t P) μ) →
      (∀ n ∈ nset, ∀ v ∈ bset, AEStronglyMeasurable (fun t => beta t n v) μ) →
      (∀ k ∈ rows, AEStronglyMeasurable (rowPhase k) μ) →
      (∀ t, ∀ P ∈ Pset, ‖a t P‖ ≤ 1) →
      (∀ t, ∀ n ∈ nset, ∀ v ∈ bset, ‖beta t n v‖ ≤ 1) →
      (∀ k ∈ rows, ∀ t, ‖rowPhase k t‖ ≤ 1) →
      (∑ k ∈ rows, ‖m * ∫ t, b t * (rowPhase k t *
        hybridRow Pset nset bset (a t) (beta t) k) ∂μ‖ ^ 2) ≤
      ‖m‖ ^ 2 * (C * (K * N * B) ^ ε * (K + N * B) * B *
        CubicSieve.sieveNorm N (2 * L)) * (∫ t, ‖b t‖ ∂μ) ^ 2 := by
  obtain ⟨C, hC, he⟩ := hybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B L hK hN hB rows nset bset Pset hrows hn hv hP μ b a beta phase m
    hb haM hbetaM hphaseM ha hbeta hphase
  let E := C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L)
  have hE : 0 ≤ E := by
    have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
    dsimp only [E]
    positivity
  let φ : rows → Ω → ℂ := fun k t => phase k t * hybridRow Pset nset bset (a t) (beta t) k
  have hbound (t : Ω) : (∑ k, ‖φ k t‖ ^ 2) ≤ E := by
    calc
      _ ≤ ∑ k : rows, ‖hybridRow Pset nset bset (a t) (beta t) k‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hphase k k.property t)
      _ = ∑ k ∈ rows, ‖hybridRow Pset nset bset (a t) (beta t) k‖ ^ 2 := by
        exact Finset.sum_coe_sort rows (fun k : Ideal Eis => ‖hybridRow Pset nset bset (a t) (beta t) k‖ ^ 2)
      _ ≤ E := he K N B L hK hN hB rows nset bset Pset (a t) (beta t)
        hrows hn hv hP (ha t) (hbeta t)
  have hφM (k : rows) : AEStronglyMeasurable (φ k) μ := by
    apply (hphaseM k k.property).mul
    unfold hybridRow
    apply Finset.aestronglyMeasurable_fun_sum
    intro P hPS
    simp only [div_eq_mul_inv]
    apply ((haM P hPS).mul_const _ |>.mul_const _).mul
    unfold hybridInner
    apply Finset.aestronglyMeasurable_fun_sum
    intro n hns
    apply Finset.aestronglyMeasurable_fun_sum
    intro v hvs
    exact (((hbetaM n hns v hvs).mul_const _).mul_const _).mul_const _
  have hpoint (k : rows) (t : Ω) : ‖φ k t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖φ j t‖)
      (Finset.mem_univ k)).trans (hbound t)
  have hint (k : rows) : Integrable (fun t => b t * φ k t) μ :=
    hb.mul_bdd (hφM k) (Filter.Eventually.of_forall (hpoint k))
  have hm := mul_le_mul_of_nonneg_left
    (common_measure_energy μ b φ E hE hb.norm hint hbound) (sq_nonneg ‖m‖)
  simp only [norm_mul, mul_pow, ← Finset.mul_sum] at hm ⊢
  rw [mul_assoc]
  rw [show (∑ k : rows, ‖∫ t, b t * φ k t ∂μ‖ ^ 2) =
      ∑ k ∈ rows, ‖∫ t, b t * (phase k t * hybridRow Pset nset bset (a t) (beta t) k) ∂μ‖ ^ 2 from
    Finset.sum_coe_sort rows (fun k : Ideal Eis =>
      ‖∫ t, b t * (phase k t * hybridRow Pset nset bset (a t) (beta t) k) ∂μ‖ ^ 2)] at hm
  exact hm

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0443

/-! Original module: OAI.NumberTheory.DirichletL.Descent.Widths
Source SHA256: 6b7d67df4751dcec7b2cbf008eef2551f33577a0e100989aae7af900ca65e771
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0444


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma actual_ideal_norm_pos (I : Ideal Eis) (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))

theorem actual_residual_norm_width (I Q : Ideal Eis) (hI : I ≠ 0) :
    (Ideal.absNorm (rowResidualPart I Q) : ℝ) *
      (Ideal.absNorm (rowPowerfulPart I) : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
  have hm : 1 ≤ (Ideal.absNorm (rowMaskPart I Q) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz =>
      squarefreeMaskPart_ne_zero (rowSimplePart I) Q (Ideal.absNorm_eq_zero_iff.mp hz))
  have he := congrArg (fun J : Ideal Eis => (Ideal.absNorm J : ℝ))
    (row_powerful_mask_residual_product I Q hI)
  simp only [map_mul, Nat.cast_mul] at he
  calc
    _ ≤ (Ideal.absNorm (rowPowerfulPart I) : ℝ) *
        (Ideal.absNorm (rowMaskPart I Q) : ℝ) * (Ideal.absNorm (rowResidualPart I Q) : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hm
        (show 0 ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ) *
          (Ideal.absNorm (rowPowerfulPart I) : ℝ) by positivity)
      nlinarith [hh]
    _ = _ := he

theorem actual_common_width_charge {ι : Type*} [Fintype ι]
    (I F Q : Ideal Eis) (hI : I ≠ 0) (hQ : Q ≠ 0)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * Q)
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I Q) (e : ι → Fin 3) :
    (Ideal.absNorm (rowResidualPart I Q) : ℝ)^2 *
      reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e ≤
      (Ideal.absNorm I : ℝ)^2 / (Ideal.absNorm (rowPowerfulPart I) : ℝ) *
        (Ideal.absNorm Q : ℝ) := by
  have hp := actual_ideal_norm_pos (rowPowerfulPart I) (rowPowerfulPart_ne_zero I)
  have hm := actual_ideal_norm_pos (rowMaskPart I Q)
    (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)
  have he := rowResidualPart_norm I Q hI
  calc
    _ ≤ (Ideal.absNorm (rowResidualPart I Q) : ℝ)^2 *
        ((Ideal.absNorm (rowPowerfulPart I) : ℝ) *
          (Ideal.absNorm (rowMaskPart I Q) : ℝ)^2 * (Ideal.absNorm Q : ℝ)) :=
      mul_le_mul_of_nonneg_left (reflectionConductorCost_bound I F Q hI hQ P hcop hpool hres e)
        (sq_nonneg _)
    _ = _ := by rw [he]; field_simp

theorem actual_common_width_charge_label_puncture {ι : Type*} [Fintype ι]
    (I F rho S : Ideal Eis) (hI : I ≠ 0) (hF : F ≠ 0) (hrho : rho ≠ 0) (hS : S ≠ 0)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀ i, P i ∣ I * (S * F * rho))
    (hres : ∀ i, ¬ P i ∣ rowResidualPart I (S * F * rho)) (e : ι → Fin 3) :
    (Ideal.absNorm (rowResidualPart I (S * F * rho)) : ℝ)^2 *
      reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e ≤
      (Ideal.absNorm S : ℝ) *
        ((Ideal.absNorm I : ℝ)^2 / (Ideal.absNorm (rowPowerfulPart I) : ℝ)) *
        (Ideal.absNorm F : ℝ) * (Ideal.absNorm rho : ℝ) := by
  convert actual_common_width_charge I F (S * F * rho) hI
    (mul_ne_zero (mul_ne_zero hS hF) hrho) P hcop hpool hres e using 1
  simp only [map_mul, Nat.cast_mul]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0444

/-! Original module: OAI.NumberTheory.DirichletL.Descent.WindowFourier
Source SHA256: 615b7d415c0e5e29f3544f24a15c3a45dc65165e5103012f012438ec3bc4a9ed
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0445



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

variable {ι : Type*} [Fintype ι]

def coordinateDensity (g : ι → 𝓢(ℝ, ℂ)) (t : ι → ℝ) : ℂ :=
  ∏ i, (𝓕 (g i)) (t i)

def coordinatePhase (t y : ι → ℝ) : ℂ := ∏ i, logPhase (t i) (y i)

theorem coordinate_fourier_inversion (g : ι → 𝓢(ℝ, ℂ)) (y : ι → ℝ) :
    (∏ i, g i (y i)) = ∫ t : ι → ℝ, coordinateDensity g t * coordinatePhase t y := by
  simp only [coordinateDensity, coordinatePhase, ← Finset.prod_mul_distrib]
  have hp := integral_fintype_prod_volume_eq_prod (E := fun _ : ι => ℝ)
    (fun (i : ι) (t : ℝ) => (𝓕 (g i) : 𝓢(ℝ, ℂ)) t * logPhase t (y i))
  rw [hp]
  apply Finset.prod_congr rfl
  intro i hi
  simpa only [mul_comm] using schwartz_logPhase_inversion (g i) (y i)

theorem coordinate_density_weighted_integrable (g : ι → 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ι → ℝ => (∏ i, (1 + ‖t i‖)^J) * ‖coordinateDensity g t‖) := by
  have hi (i : ι) := AnalyticBridge.schwartz_fourier_one_plus_integrable (g i) J
  convert Integrable.fintype_prod hi using 1
  funext t
  simp only [coordinateDensity, norm_prod, Finset.prod_mul_distrib]

theorem coordinate_density_weighted_integral (g : ι → 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ t : ι → ℝ, (∏ i, (1 + ‖t i‖)^J) * ‖coordinateDensity g t‖) =
      ∏ i, ∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (g i)) t‖ := by
  simp only [coordinateDensity, norm_prod, ← Finset.prod_mul_distrib]
  exact integral_fintype_prod_volume_eq_prod (E := fun _ : ι => ℝ)
    (fun i t => (1 + ‖t‖)^J * ‖(𝓕 (g i)) t‖)

def pureProfileMode (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ)
    (t : Frequency) (u : ι → ℝ) : ℂ :=
  ∏ i, logPhase (u i) (y i) * logPhase t.1 (a₁ i * y i) *
    logPhase t.2.1 (a₂ i * y i) * logPhase t.2.2 (ak i * y i)

theorem profileMode_coordinate_separation (g : ι → 𝓢(ℝ, ℂ))
    (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ) (t : Frequency) :
    profileMode (fun i => g i) a₁ a₂ ak y t =
      ∫ u : ι → ℝ, coordinateDensity g u * pureProfileMode a₁ a₂ ak y t u := by
  simp only [profileMode, pureProfileMode, Finset.prod_mul_distrib]
  simp only [← mul_assoc]
  rw [integral_mul_const, integral_mul_const, integral_mul_const]
  have he := coordinate_fourier_inversion g y
  simp only [coordinatePhase] at he
  rw [← he]

 theorem pureProfileMode_norm (a₁ a₂ ak : ι → ℝ) (y : ι → ℝ)
    (t : Frequency) (u : ι → ℝ) : ‖pureProfileMode a₁ a₂ ak y t u‖ = 1 := by
  simp [pureProfileMode, norm_prod,  logPhase_norm]

def fullProfileDensity (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (p : Frequency × (ι → ℝ)) : ℂ :=
  tripleCoefficient b₁ b₂ b₃ p.1 * coordinateDensity g p.2

def tripleHeight (J : ℕ) (t : Frequency) : ℝ :=
  (1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J

def coordinateHeight (J : ℕ) (u : ι → ℝ) : ℝ := ∏ i, (1 + ‖u i‖)^J

theorem fullProfileDensity_weighted_integrable (g : ι → 𝓢(ℝ, ℂ))
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun p : Frequency × (ι → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 * ‖fullProfileDensity g b₁ b₂ b₃ p‖) := by
  convert (tripleCoefficient_weighted_integrable b₁ b₂ b₃ J).mul_prod
    (coordinate_density_weighted_integrable g J) using 1
  funext p
  simp only [tripleHeight, coordinateHeight, fullProfileDensity, norm_mul]
  ring

theorem fullProfileDensity_weighted_integral (g : ι → 𝓢(ℝ, ℂ))
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ p : Frequency × (ι → ℝ),
      tripleHeight J p.1 * coordinateHeight J p.2 * ‖fullProfileDensity g b₁ b₂ b₃ p‖) =
      (∫ t : Frequency, tripleHeight J t * ‖tripleCoefficient b₁ b₂ b₃ t‖) *
      (∏ i, ∫ u : ℝ, (1 + ‖u‖)^J * ‖(𝓕 (g i)) u‖) := by
  have he (p : Frequency × (ι → ℝ)) :
      tripleHeight J p.1 * coordinateHeight J p.2 * ‖fullProfileDensity g b₁ b₂ b₃ p‖ =
        (tripleHeight J p.1 * ‖tripleCoefficient b₁ b₂ b₃ p.1‖) *
        (coordinateHeight J p.2 * ‖coordinateDensity g p.2‖) := by
    simp only [fullProfileDensity, norm_mul]
    ring
  simp_rw [he]
  simp only [Measure.volume_eq_prod]
  rw [integral_prod_mul (fun t : Frequency => tripleHeight J t * ‖tripleCoefficient b₁ b₂ b₃ t‖)
    (fun u : ι → ℝ => coordinateHeight J u * ‖coordinateDensity g u‖)]
  simp only [coordinateHeight]
  rw [coordinate_density_weighted_integral g J]

theorem profile_integral_coordinate_absorption (g : ι → 𝓢(ℝ, ℂ))
    (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (a₁ a₂ ak y : ι → ℝ) :
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
      tripleCoefficient b₁ b₂ b₃ (t₁,t₂,t₃) *
        profileMode (fun i => g i) a₁ a₂ ak y (t₁,t₂,t₃)) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : ι → ℝ,
      fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
        pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u := by
  apply integral_congr_ae
  filter_upwards with t₁
  apply integral_congr_ae
  filter_upwards with t₂
  apply integral_congr_ae
  filter_upwards with t₃
  rw [profileMode_coordinate_separation, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [fullProfileDensity]
  ring

def profileHeight (a₁ a₂ ak : ι → ℝ) (t : Frequency) (u : ι → ℝ) (i : ι) : ℝ :=
  u i + a₁ i * t.1 + a₂ i * t.2.1 + ak i * t.2.2

lemma logPhase_scaled_coordinate (t a y : ℝ) : logPhase t (a*y) = logPhase (a*t) y := by
  unfold logPhase
  congr 1
  push_cast
  ring

theorem pureProfileMode_height (a₁ a₂ ak y : ι → ℝ) (t : Frequency) (u : ι → ℝ) :
    pureProfileMode a₁ a₂ ak y t u = ∏ i, logPhase (profileHeight a₁ a₂ ak t u i) (y i) := by
  apply Finset.prod_congr rfl
  intro i hi
  simp only [profileHeight, logPhase_add_frequency, logPhase_scaled_coordinate]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0445

/-! Original module: OAI.NumberTheory.DirichletL.Descent.RootWindows
Source SHA256: 971384242537e44b41713306cdadeed7c60d75b0d2706e519ff60d8a336b980d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0446


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section

theorem inverseNormWindow_contDiff (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (inverseNormWindow V) := by
  unfold inverseNormWindow
  have hn : ∀ y : ℝ, (Real.exp y : ℂ) ≠ 0 := by
    intro y
    exact_mod_cast Real.exp_ne_zero y
  simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using
    hV.mul ((Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).inv hn)

theorem inverseRootWindow_contDiff (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (inverseRootWindow V) := by
  unfold inverseRootWindow
  have hs : ContDiff ℝ ∞ (fun y : ℝ => Real.sqrt (Real.exp y)) :=
    Real.contDiff_exp.sqrt Real.exp_ne_zero
  have hn : ∀ y : ℝ, (Real.sqrt (Real.exp y) : ℂ) ≠ 0 := by
    intro y
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (Real.exp_pos y))
  simpa only [div_eq_mul_inv, Pi.inv_apply, Function.comp_apply, Complex.ofRealCLM_apply] using
    hV.mul ((Complex.ofRealCLM.contDiff.comp hs).inv hn)

theorem inverseNormWindow_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (inverseNormWindow V) := by
  apply hV.mono
  intro y hy
  exact (div_ne_zero_iff.mp hy).1

theorem inverseRootWindow_compact (V : ℝ → ℂ) (hV : HasCompactSupport V) :
    HasCompactSupport (inverseRootWindow V) := by
  apply hV.mono
  intro y hy
  exact (div_ne_zero_iff.mp hy).1

theorem firstRootWindows_smooth_compact (V : Fin 9 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    ∀ i, ContDiff ℝ ∞ (firstRootWindows V i) ∧ HasCompactSupport (firstRootWindows V i) := by
  intro i
  fin_cases i <;> first
    | exact ⟨hV _, hS _⟩
    | exact ⟨inverseNormWindow_contDiff _ (hV _), inverseNormWindow_compact _ (hS _)⟩
    | exact ⟨inverseRootWindow_contDiff _ (hV _), inverseRootWindow_compact _ (hS _)⟩

theorem secondRootWindows_smooth_compact (V : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    ∀ i, ContDiff ℝ ∞ (secondRootWindows V i) ∧ HasCompactSupport (secondRootWindows V i) := by
  intro i
  fin_cases i <;> first
    | exact ⟨hV _, hS _⟩
    | exact ⟨inverseNormWindow_contDiff _ (hV _), inverseNormWindow_compact _ (hS _)⟩
    | exact ⟨inverseRootWindow_contDiff _ (hV _), inverseRootWindow_compact _ (hS _)⟩

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0446

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FullProfile
Source SHA256: 5a655ad3986219a6de60099bd72b644f66a407dc15d21628d79b99bbd5e00810
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0447


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

def rootSchwartz {ι : Type*} (U : ι → ℝ → ℂ)
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hS : ∀ i, HasCompactSupport (U i))
    (i : ι) : 𝓢(ℝ, ℂ) := (hS i).toSchwartzMap (hU i)

@[simp] theorem rootSchwartz_apply {ι : Type*} (U : ι → ℝ → ℂ)
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hS : ∀ i, HasCompactSupport (U i))
    (i : ι) (y : ℝ) : rootSchwartz U hU hS i y = U i y := rfl

theorem full_source_profile_common_measure {ι : Type*} [Fintype ι]
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (U : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hS : ∀ i, HasCompactSupport (U i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, U i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : ι → ℝ,
        (∏ i, U i (y i)) * W₁ (Real.exp (∑ i, a₁ i * y i)) *
          W₂ (Real.exp (∑ i, a₂ i * y i)) *
          paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : ι → ℝ,
          fullProfileDensity (rootSchwartz U hU hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight a₁ a₂ ak (t₁,t₂,t₃) u i) (y i))) ∧
      Integrable (fun p : Frequency × (ι → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (rootSchwartz U hU hS) b₁ b₂ b₃ p‖) ∧
      (1 + R)^A * (∫ p : Frequency × (ι → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (rootSchwartz U hU hS) b₁ b₂ b₃ p‖) ≤ C := by
  obtain ⟨b₁,b₂,C,hC,hsep⟩ := source_descent_profile_separation
    W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ U a₁ a₂ ak M hM hbox A J
  let g := rootSchwartz U hU hS
  let D : ℝ := ∏ i, ∫ u : ℝ, (1 + ‖u‖)^J * ‖(𝓕 (g i)) u‖
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i hi => integral_nonneg (fun u => by positivity))
  refine ⟨b₁,b₂,C*D,mul_nonneg hC hD, ?_⟩
  intro R hR
  obtain ⟨b₃,he,hi,hb⟩ := hsep R hR
  refine ⟨b₃,?_,fullProfileDensity_weighted_integrable g b₁ b₂ b₃ J,?_⟩
  · intro y
    rw [he y]
    have habs := profile_integral_coordinate_absorption g b₁ b₂ b₃ a₁ a₂ ak y
    simpa only [g, profileMode, rootSchwartz_apply, pureProfileMode_height] using habs
  · rw [fullProfileDensity_weighted_integral]
    change (1+R)^A * ((∫ t : Frequency, tripleHeight J t * ‖tripleCoefficient b₁ b₂ b₃ t‖) * D) ≤ C*D
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hb hD

def firstRootSchwartz (V : Fin 9 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    Fin 9 → 𝓢(ℝ, ℂ) :=
  rootSchwartz (firstRootWindows V)
    (fun i => (firstRootWindows_smooth_compact V hV hS i).1)
    (fun i => (firstRootWindows_smooth_compact V hV hS i).2)

theorem first_full_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (M : Fin 9 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 9 → ℝ,
          fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      Integrable (fun p : Frequency × (Fin 9 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + R)^A * (∫ p : Frequency × (Fin 9 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (firstRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  have hb : ∀ i y, firstRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact full_source_profile_common_measure W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (firstRootWindows V) firstLeftSlope firstRightSlope firstKernelSlope M
    (fun i => (firstRootWindows_smooth_compact V hV hS i).1)
    (fun i => (firstRootWindows_smooth_compact V hV hS i).2) hM hb A J

def secondRootSchwartz (V : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    Fin 6 → 𝓢(ℝ, ℂ) :=
  rootSchwartz (secondRootWindows V)
    (fun i => (secondRootWindows_smooth_compact V hV hS i).1)
    (fun i => (secondRootWindows_smooth_compact V hV hS i).2)

theorem second_full_profile_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 6 → ℝ, secondPoissonProfile W₁ W₂ Φ V R y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
          fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ∧
      (1 + R)^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖fullProfileDensity (secondRootSchwartz V hV hS) b₁ b₂ b₃ p‖) ≤ C := by
  have hb : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  exact full_source_profile_common_measure W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ
    (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope M
    (fun i => (secondRootWindows_smooth_compact V hV hS i).1)
    (fun i => (secondRootWindows_smooth_compact V hV hS i).2) hM hb A J

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0447

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstProfileIdentity
Source SHA256: 349a6c19fae2e65ef8627aef3637edbf7bc47d2365097016baaa490aa39e99e3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0448


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def firstNormProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (q : Fin 9 → ℝ) : ℂ :=
  (∏ i, V i (Real.log (q i))) * W₁ (q 0*q 2*q 5*q 7) *
    W₂ (q 1*q 2*q 5*q 8) *
    paperRadialFourier Φ (R*q 6/(q 3*q 4*(q 5)^2*q 7*q 8)) /
      ((q 3:ℂ)*(Real.sqrt (q 4):ℂ)*(q 5:ℂ)*
        (Real.sqrt (q 7):ℂ)*(Real.sqrt (q 8):ℂ))

theorem firstPoissonProfile_log (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (R : ℝ) (q : Fin 9 → ℝ) (hq : ∀ i, 0 < q i) :
    firstPoissonProfile W₁ W₂ Φ V R (fun i => Real.log (q i)) =
      firstNormProfile W₁ W₂ Φ V R q := by
  have hl : (∑ i, firstLeftSlope i * Real.log (q i)) =
      Real.log (q 0)+Real.log (q 2)+Real.log (q 5)+Real.log (q 7) := by
    simp [Fin.sum_univ_succ,firstLeftSlope]; ring
  have hr : (∑ i, firstRightSlope i * Real.log (q i)) =
      Real.log (q 1)+Real.log (q 2)+Real.log (q 5)+Real.log (q 8) := by
    simp [Fin.sum_univ_succ,firstRightSlope]; ring
  have hk : (∑ i, firstKernelSlope i * Real.log (q i)) =
      Real.log (q 6) - (Real.log (q 3)+Real.log (q 4)+Real.log (q 5)+
        Real.log (q 5)+Real.log (q 7)+Real.log (q 8)) := by
    simp [Fin.sum_univ_succ,firstKernelSlope]; ring
  unfold firstPoissonProfile firstNormProfile
  rw [hl,hr,hk]
  simp only [Real.exp_add,Real.exp_sub,Real.exp_log (hq _)]
  rw [show R*(q 6/(q 3*q 4*q 5*q 5*q 7*q 8)) =
    R*q 6/(q 3*q 4*(q 5)^2*q 7*q 8) from by ring]
  simp only [Fin.prod_univ_succ,firstRootWindows,inverseNormWindow,inverseRootWindow,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.isValue,Real.exp_log (hq _),
    Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  norm_num
  ring

theorem canonicalPairMode_whole_profile {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C K : ℝ) (d h : Eis) :
    (‖eisEmbedding d‖^2 : ℂ)⁻¹ *
      canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ Φ
        (fun y => W₁ (A₁*C*Real.exp y)) (fun y => W₂ (A₂*C*Real.exp y)) 1 1 K d h =
    (K:ℂ) * firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
      ![A₁,A₂,C,‖eisEmbedding d‖^2,primeProductNorm p (cubeActiveSupport B v ε₁ ε₂),
        1,‖eisEmbedding h‖^2,primeProductNorm p N,primeProductNorm p P] *
      threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) :=
    hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) :=
    hPB.mono_right (Finset.filter_subset _ _)
  have hs (S : Finset ι) : ‖eisEmbedding (∏ i ∈ S,p i)‖ =
      Real.sqrt (primeProductNorm p S) := by
    simp only [primeProductNorm,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  unfold canonicalPairMode firstNormProfile
  simp only [columnLog,div_one,Real.exp_log (primeProductNorm_pos p hp _),
    Matrix.cons_val_zero,Fin.isValue,
    Finset.prod_const_one,one_mul,]
  rw [primeProductNorm_union p (N ∪ P) _ (Finset.disjoint_union_left.mpr ⟨hNC,hPC⟩),
    primeProductNorm_union p N P hNP]
  rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨hNC,hPC⟩),Finset.prod_union hNP]
  simp only [map_mul,norm_mul,hs]
  rw [show K*‖eisEmbedding h‖^2 /
      (‖eisEmbedding d‖^2*(primeProductNorm p N*primeProductNorm p P*
        primeProductNorm p (cubeActiveSupport B v ε₁ ε₂))) =
      K*‖eisEmbedding h‖^2 /
      (‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*
        primeProductNorm p N*primeProductNorm p P) from by ring]
  push_cast
  ring_nf

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0448

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstNominal
Source SHA256: 03a4dc3d1398b0ad0829cffc0ea5ad1234d9187d06e1017528995efe52bdd654
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0449


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
noncomputable section

def firstRootScale (s : Fin 9 → ℝ) : ℝ :=
  s 3 * Real.sqrt (s 4) * s 5 * Real.sqrt (s 7) * Real.sqrt (s 8)

theorem firstRootScale_pos (s : Fin 9 → ℝ) (hs : ∀ i, 0 < s i) :
    0 < firstRootScale s := by
  unfold firstRootScale
  exact mul_pos (mul_pos (mul_pos (mul_pos (hs 3) (Real.sqrt_pos.2 (hs 4)))
    (hs 5)) (Real.sqrt_pos.2 (hs 7))) (Real.sqrt_pos.2 (hs 8))

theorem firstNormProfile_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (V : Fin 9 → ℝ → ℂ) (s q : Fin 9 → ℝ)
    (hs : ∀ i, 0 < s i) (hq : ∀ i, 0 < q i) (K : ℝ) :
    firstNormProfile (fun x => W₁ (x/(s 0*s 2*s 5*s 7)))
      (fun x => W₂ (x/(s 1*s 2*s 5*s 8))) Φ
      (fun i y => V i (y-Real.log (s i))) K q =
    ((firstRootScale s : ℝ):ℂ)⁻¹ *
      firstNormProfile W₁ W₂ Φ V (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))
        (fun i => q i/s i) := by
  have hl : (q 0/s 0)*(q 2/s 2)*(q 5/s 5)*(q 7/s 7) =
      q 0*q 2*q 5*q 7/(s 0*s 2*s 5*s 7) := by ring
  have hr : (q 1/s 1)*(q 2/s 2)*(q 5/s 5)*(q 8/s 8) =
      q 1*q 2*q 5*q 8/(s 1*s 2*s 5*s 8) := by ring
  have hk : (K*s 6/(s 3*s 4*(s 5)^2*s 7*s 8))*(q 6/s 6)/
      ((q 3/s 3)*(q 4/s 4)*(q 5/s 5)^2*(q 7/s 7)*(q 8/s 8)) =
      K*q 6/(q 3*q 4*(q 5)^2*q 7*q 8) := by
    field_simp [(hs 3).ne', (hs 4).ne', (hs 5).ne', (hs 6).ne', (hs 7).ne', (hs 8).ne']
  have hd : (q 3/s 3)*Real.sqrt (q 4/s 4)*(q 5/s 5)*
      Real.sqrt (q 7/s 7)*Real.sqrt (q 8/s 8) =
      (q 3*Real.sqrt (q 4)*q 5*Real.sqrt (q 7)*Real.sqrt (q 8))/firstRootScale s := by
    rw [Real.sqrt_div (hq 4).le,Real.sqrt_div (hq 7).le,Real.sqrt_div (hq 8).le]
    unfold firstRootScale
    ring
  unfold firstNormProfile
  simp only [Real.log_div (hq _).ne' (hs _).ne']
  rw [hl,hr,hk]
  have hdC : (↑(q 3/s 3):ℂ)*↑(Real.sqrt (q 4/s 4))*↑(q 5/s 5)*
      ↑(Real.sqrt (q 7/s 7))*↑(Real.sqrt (q 8/s 8)) =
      ((q 3:ℂ)*↑(Real.sqrt (q 4))*(q 5:ℂ)*↑(Real.sqrt (q 7))*↑(Real.sqrt (q 8)))/
        (firstRootScale s:ℂ) := by exact_mod_cast hd
  rw [hdC]
  have hDc : (firstRootScale s:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (firstRootScale_pos s hs).ne'
  field_simp [hDc]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0449

/-! Original module: OAI.NumberTheory.DirichletL.Descent.PhysicalExponents
Source SHA256: e42b4d828ae468c90f999fe013861a11965ec5aa3e0426864cac862f5e1d907c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0450



namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section

theorem firstRootScale_rpow (Z : ℝ) (hZ : 0 < Z) (s : Fin 9 → ℝ) :
    firstRootScale (fun i => Z^(s i)) = Z^(s 3+s 4/2+s 5+s 7/2+s 8/2) := by
  have hs (x : ℝ) : Real.sqrt (Z^x) = Z^(x/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hZ.le]
    congr 1
    ring
  unfold firstRootScale
  rw [hs,hs,hs,← Real.rpow_add hZ,← Real.rpow_add hZ,← Real.rpow_add hZ,← Real.rpow_add hZ]

def firstKappa (M r ell V δ A B R : ℝ) : ℝ := M-2*r-2*ell-V-δ+A+B-R/2
def firstPhysicalHeight (M r ell V δ B j : ℝ) : ℝ := 2*r-2*B-M+4*ell+2*V+δ-j
def secondLambda (M r ell V δ A B j t g θ : ℝ) : ℝ :=
  firstPhysicalHeight M r ell V δ B j - θ - (r-A-B-t-g)
def secondCount (ell R j t g θ : ℝ) : ℝ := ell+R/2-j+t+g-θ
def secondFormalColumn (r A B t g v : ℝ) : ℝ := r-A-B-t-g-v
def secondFormalLabel (B θ v j : ℝ) : ℝ := B+θ+v+j

theorem first_physical_scalar (Z : ℝ) (hZ : 0 < Z)
    (M r ell V δ A₁ A₂ B R t h : ℝ) :
    Z^(-r-2*ell-V) * Z^M /
      firstRootScale (fun i => Z^(![A₁,A₂,B,δ,R,t,h,r-A₁-B-t,r-A₂-B-t] i)) =
    Z^((firstKappa M r ell V δ A₁ B R+firstKappa M r ell V δ A₂ B R)/2) := by
  rw [firstRootScale_rpow Z hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  norm_num [firstKappa]
  ring

theorem second_physical_scalar (Z : ℝ) (hZ : 0 < Z)
    (M r ell V δ A B j t g θ v η τ : ℝ) :
    Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ) /
      (Z^θ*Z^v*Z^(secondFormalColumn r A B t g v)) * Real.exp (6*(η*Real.log Z)) =
    Z^(secondLambda M r ell V δ A B j t g θ+18*η+τ) := by
  have he : Real.exp (6*(η*Real.log Z)) = Z^(6*η) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he,←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_sub hZ,←Real.rpow_add hZ]
  congr 1
  unfold secondLambda secondFormalColumn
  ring

theorem physical_prefactor_identity (M r ell V δ A B R j t g θ v : ℝ) :
    firstKappa M r ell V δ A B R + secondLambda M r ell V δ A B j t g θ +
      secondCount ell R j t g θ +
      2*(secondFormalColumn r A B t g v+secondFormalLabel B θ v j) = r+3*ell+V := by
  unfold firstKappa secondLambda firstPhysicalHeight secondCount secondFormalColumn secondFormalLabel
  ring

theorem physical_step_energy_exponent (M r ell V δ A B R j t g θ v η τ π ε clip : ℝ)
    (hclip : clip ≤ 6*η) :
    firstKappa M r ell V δ A B R + secondLambda M r ell V δ A B j t g θ +
      secondCount ell R j t g θ +
      2*(secondFormalColumn r A B t g v+secondFormalLabel B θ v j+clip) +
      (9/2+18+11/2)*η+τ+π+ε ≤ r+3*ell+V+40*η+τ+π+ε :=
  step_energy_exponent (physical_prefactor_identity M r ell V δ A B R j t g θ v) hclip

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0450

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstRowGeometry
Source SHA256: bb3dc58b157290278ca53f3b39e919c1fc82e0c99a3bb9e54b99567ea788571b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0451



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma first_whole_frequency_numeric (K P dn an cn a1 a2 sn tn hn L : ℝ)
    (hK : 0<K) (hP : 0<P) (hdn : 0<dn) (han : 0<an)
    (hcn : 0<cn) (ha1 : 0<a1) (ha2 : 0<a2)
    (hsn : 0<sn) (htn : 0<tn) (_hhn : 0≤hn) (hL : 0<L)
    (hS : a1*cn*sn≤L) (hT : a2*cn*tn≤L)
    (hratio : (K/(dn*(sn*tn*an)))*hn≤P) :
    hn≤L^2*an*dn/((K/P)*a1*a2*cn^2) := by
  have hprod : sn*tn*(a1*a2*cn^2)≤L^2 := by
    have hh := mul_le_mul hS hT (by positivity : 0≤a2*cn*tn) hL.le
    nlinarith [hh]
  have hraw : K*hn≤P*(dn*(sn*tn*an)) := by
    rw [div_mul_eq_mul_div] at hratio
    exact (div_le_iff₀ (by positivity)).mp hratio
  have hfull : K*hn*(a1*a2*cn^2)≤P*dn*an*L^2 := by
    have hh := mul_le_mul_of_nonneg_right hraw (by positivity : 0≤a1*a2*cn^2)
    have hh' := mul_le_mul_of_nonneg_left hprod (by positivity : 0≤P*dn*an)
    nlinarith [hh,hh']
  apply (le_div_iff₀ (by positivity)).mpr
  convert div_le_div_of_nonneg_right hfull hP.le using 1 <;> field_simp

theorem first_ratio_actual_row {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (h : O)
    (K P L B F : ℝ) (hK : 0<K) (hP : 0<P) (hL : 0<L) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤B)
    (hf : (Ideal.absNorm f : ℝ)≤F)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤L)
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤L)
    (hratio : (K/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2≤P) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h))‖^2 ≤
    P*L^2*B^4*F^2*primeProductNorm p divisor /
      (K*(primeProductNorm p common)^2*‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2) := by
  let active := cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let e := dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let j := jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂
  let a1 := aLabel p S ε₁
  let a2 := aLabel p S ε₂
  have hactive : active ⊆ S := Finset.filter_subset _ _
  have hnorm : primeProductNorm p ((N∪Q)∪active)=
      primeProductNorm p N*primeProductNorm p Q*primeProductNorm p active := by
    rw [primeProductNorm_union p (N∪Q) active (Finset.disjoint_union_left.mpr
      ⟨hNS.mono_right hactive,hQS.mono_right hactive⟩),
      primeProductNorm_union p _ _ hNQ]
  change (K/(primeProductNorm p divisor*primeProductNorm p ((N∪Q)∪active)))*‖eisEmbedding h‖^2≤P at hratio
  rw [hnorm] at hratio
  have hpos (v : ι→ℕ) : 0<‖eisEmbedding (primeProduct p S v)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  have hfreq := first_whole_frequency_numeric K P (primeProductNorm p divisor)
    (primeProductNorm p active) (primeProductNorm p common) (‖eisEmbedding a1‖^2)
    (‖eisEmbedding a2‖^2) (primeProductNorm p N) (primeProductNorm p Q)
    (‖eisEmbedding h‖^2) L hK hP (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)
    (primeProductNorm_pos p hp _) (hpos _) (hpos _) (primeProductNorm_pos p hp _)
    (primeProductNorm_pos p hp _) (sq_nonneg _) hL hcol₁ hcol₂ hratio
  have hcon := first_conductor_norm_bound p hp S v₁ v₂ ε₁ ε₂ hv B hB.le hb₁ hb₂
  have hnum := first_row_numeric_bound (primeProductNorm p active) (‖eisEmbedding e‖^2)
    (‖eisEmbedding j‖^2) (‖eisEmbedding a1‖^2) (‖eisEmbedding a2‖^2)
    (primeProductNorm p common) (primeProductNorm p divisor) (‖eisEmbedding h‖^2)
    (Ideal.absNorm f) L (K/P) B F (primeProductNorm_pos p hp _).le (sq_nonneg _)
    (hpos _) (hpos _) (hpos _) (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _).le
    (sq_nonneg _) (Nat.cast_nonneg _) hL (div_pos hK hP) hB hF hcon hfreq hf
  have hgen : ‖eisEmbedding (ConcretePrimeRowBridge.idealGenerator f)‖^2=(Ideal.absNorm f : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,ConcretePrimeRowBridge.span_idealGenerator]
  have hrow : ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap e (f,h))‖^2 =
      ‖eisEmbedding h‖^2*(Ideal.absNorm f : ℝ)^2*‖eisEmbedding e‖^2 := by
    simp only [DescentWeightedCauchy.firstElementRowMap,map_mul,map_pow,norm_mul,norm_pow,mul_pow]
    rw [hgen]
  rw [hrow]
  apply hnum.trans_eq
  field_simp
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0451

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstCutoffScale
Source SHA256: 1c67095d68b638129bc5ec05b143045c897ede8db54c2d83042fd308f412b9f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0452


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem first_physical_row_scale_bound
    (Z M r ell V delta B j eta tau dn cn jn : ℝ) (hZ : 0<Z)
    (_hdn : 0≤dn) (hcn : 0<cn) (_hjn : 0<jn)
    (hd : dn≤Z^(delta+eta)) (hc : Z^(B-eta)≤cn) (hj : Z^(j-eta)≤jn) :
    Z^tau*(Z^(r+eta))^2*(Z^(ell+eta))^4*(Z^(V+eta))^2*dn /
      (Z^M*cn^2*jn) ≤ Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau) := by
  have hpow (x : ℝ) (n : ℕ) : (Z^x)^n=Z^(x*n) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  calc
    _ ≤ Z^tau*(Z^(r+eta))^2*(Z^(ell+eta))^4*(Z^(V+eta))^2*Z^(delta+eta) /
        (Z^M*(Z^(B-eta))^2*Z^(j-eta)) := by
      apply div_le_div₀ (by positivity)
      · exact mul_le_mul_of_nonneg_left hd (by positivity)
      · positivity
      · exact mul_le_mul (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.rpow_pos_of_pos hZ _).le hc 2) (Real.rpow_pos_of_pos hZ _).le)
          hj (Real.rpow_pos_of_pos hZ _).le (by positivity)
    _ = _ := by
      simp only [hpow,←Real.rpow_add hZ,←Real.rpow_sub hZ]
      congr 1
      unfold firstPhysicalHeight
      norm_num
      ring

theorem first_ratio_canonical_row {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (h : O)
    (Z M r ell V delta B j eta tau : ℝ) (hZ : 0<Z)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta))
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta))
    (hf : (Ideal.absNorm f : ℝ)≤Z^(V+eta))
    (hd : primeProductNorm p divisor≤Z^(delta+eta))
    (hc : Z^(B-eta)≤primeProductNorm p common)
    (hj : Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta))
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta))
    (hratio : (Z^M/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2≤Z^tau) :
    ‖eisEmbedding (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h))‖^2 ≤
      Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau) := by
  have hrow := first_ratio_actual_row p hp S N Q v₁ v₂ ε₁ ε₂ hv hNQ hNS hQS common divisor f h
    (Z^M) (Z^tau) (Z^(r+eta)) (Z^(ell+eta)) (Z^(V+eta))
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hb₁ hb₂ hf hcol₁ hcol₂ hratio
  exact hrow.trans (first_physical_row_scale_bound Z M r ell V delta B j eta tau
    (primeProductNorm p divisor) (primeProductNorm p common)
    (‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2) hZ
    (primeProductNorm_pos p hp _).le (primeProductNorm_pos p hp _)
    (SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)) hd hc hj)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0452

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstPhysicalCutoff
Source SHA256: eddeeee94eedba9116d5411a4200e1b6ea4ed6201bf735fac78dcbd8b69e99f0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0453


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def firstPhysicalMultiplier {ι : Type*} (p : ι→O) (S : Finset ι)
    (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) : O :=
  (ConcretePrimeRowBridge.idealGenerator f)^2 * dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂

lemma firstPhysicalMultiplier_ne_zero {ι : Type*} (p : ι→O) (hp : ∀ i,p i≠0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (S : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) (hf : f≠0) :
    firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f≠0 :=
  mul_ne_zero (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero f hf))
    (primeProduct_ne_zero p hp _ _)

lemma firstPhysicalMultiplier_row {ι : Type*} (p : ι→O) (S : Finset ι)
    (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool) (f : Ideal O) (h : O) :
    firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f*h =
      DescentWeightedCauchy.firstElementRowMap (dilationLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂) (f,h) := by
  unfold firstPhysicalMultiplier DescentWeightedCauchy.firstElementRowMap
  ring

theorem first_physical_cutoff_raw_tail {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (S N Q : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i)
    (hNQ : Disjoint N Q) (hNS : Disjoint N S) (hQS : Disjoint Q S)
    (common divisor : Finset ι) (f : Ideal O) (hf0 : f≠0) (h : O)
    (Z M r ell V delta B j eta tau : ℝ) (hZ : 0<Z)
    (hb₁ : ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta))
    (hb₂ : ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta))
    (hf : (Ideal.absNorm f : ℝ)≤Z^(V+eta))
    (hd : primeProductNorm p divisor≤Z^(delta+eta))
    (hc : Z^(B-eta)≤primeProductNorm p common)
    (hj : Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2)
    (hcol₁ : ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta))
    (hcol₂ : ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta))
    (hout : h∉childFrequencyBall (firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f)
      (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))) :
    Z^tau ≤ (Z^M/(primeProductNorm p divisor *
      primeProductNorm p ((N∪Q)∪cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂)))*‖eisEmbedding h‖^2 := by
  by_contra hbad
  have hratio := (lt_of_not_ge hbad).le
  have hrow := first_ratio_canonical_row p hp S N Q v₁ v₂ ε₁ ε₂ hv hNQ hNS hQS common divisor f h
    Z M r ell V delta B j eta tau hZ hb₁ hb₂ hf hd hc hj hcol₁ hcol₂ hratio
  apply hout
  apply (mem_childFrequencyBall _ (firstPhysicalMultiplier_ne_zero p hp S v₁ v₂ ε₁ ε₂ f hf0) _ h).mpr
  simpa only [firstPhysicalMultiplier_row] using hrow

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0453

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstPhysicalTail
Source SHA256: 432dda7c3ea59986502eb3701eb085329940fea2ee5ef1c4d7a59fe98b27a9ae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0454



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_first_physical_tail (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct : ℝ),0<Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool S common divisor : Finset ι) (v₁ v₂ : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈S,0<v₁ i+v₂ i) → Disjoint pool S →
      ∀ (f : Ideal O),f≠0 → ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤G₁ → 0≤G₂ → 0<Z →
      (∀ U∈pool.powerset,‖C₁ U‖≤G₁) → (∀ U∈pool.powerset,‖C₂ U‖≤G₂) →
      ‖eisEmbedding (primeProduct p S v₁)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p S v₂)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤Z^(V+eta) → primeProductNorm p divisor≤Z^(delta+eta) →
      Z^(B-eta)≤primeProductNorm p common →
      Z^(j-eta)≤‖eisEmbedding (jLabel p S (fun i=>v₁ i+v₂ i) ε₁ ε₂)‖^2 →
      (∀ N∈pool.powerset,C₁ N≠0 →
        ‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common*primeProductNorm p N≤Z^(r+eta)) →
      (∀ Q∈pool.powerset,C₂ Q≠0 →
        ‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common*primeProductNorm p Q≤Z^(r+eta)) →
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p S ε₂)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p S ε₁)‖^2*primeProductNorm p common)
      let active := cubeActiveSupport S (fun i=>v₁ i+v₂ i) ε₁ ε₂
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p S v₁ v₂ ε₁ ε₂ f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hcop hg pool S (fun i=>v₁ i+v₂ i) ε₁ ε₂
        C₁ C₂ W (fun _=>1) (fun _=>1) 1 1 (Z^M)
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁*G₂*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,hfull⟩ := full_first_supported_remainder order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hinj hcop hg hchar pool S common divisor v₁ v₂ ε₁ ε₂ hv hpool f hf0
    C₁ C₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ hC₁ hC₂ hb₁ hb₂ hf hd hc hj hcol₁ hcol₂
    U₁ U₂ active slow T
  have hA (ε : ι→Bool) : 0<‖eisEmbedding (aLabel p S ε)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  have hU₁ : 0<U₁ := div_pos (Real.rpow_pos_of_pos hZ _)
    (mul_pos (hA ε₂) (primeProductNorm_pos p hp _))
  have hU₂ : 0<U₂ := div_pos (Real.rpow_pos_of_pos hZ _)
    (mul_pos (hA ε₁) (primeProductNorm_pos p hp _))
  have hlog₁ (N : Finset ι) (hN : N∈pool.powerset) (hn : C₁ N≠0) : columnLog p 1 N≤Real.log U₁ := by
    unfold columnLog
    rw [div_one]
    apply Real.log_le_log (primeProductNorm_pos p hp _)
    apply (le_div_iff₀ (mul_pos (hA ε₂) (primeProductNorm_pos p hp _))).mpr
    simpa only [mul_comm] using hcol₁ N hN hn
  have hlog₂ (N : Finset ι) (hN : N∈pool.powerset) (hn : C₂ N≠0) : columnLog p 1 N≤Real.log U₂ := by
    unfold columnLog
    rw [div_one]
    apply Real.log_le_log (primeProductNorm_pos p hp _)
    apply (le_div_iff₀ (mul_pos (hA ε₁) (primeProductNorm_pos p hp _))).mpr
    simpa only [mul_comm] using hcol₂ N hN hn
  have hb := hfull p hp hinj hcop hg hchar pool S (fun i=>v₁ i+v₂ i) ε₁ ε₂ hpool C₁ C₂ W
    G₁ G₂ 1 1 (Z^M) (Z^tau) (Real.log U₁) (Real.log U₂) hG₁ hG₂ zero_lt_one zero_lt_one
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _).le hC₁ hC₂ hlog₁ hlog₂
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) (primeSubsetGenerator_ne_zero _ _) T
    (fun N hN Q hQ hNQ hn hq h hout=>by
      simpa only [primeSubsetGenerator_norm_eq_productNorm, Finset.union_comm] using
        first_physical_cutoff_raw_tail p hp S Q N v₁ v₂ ε₁ ε₂ hv hNQ.symm
          (hpool.mono_left (Finset.mem_powerset.mp hQ)) (hpool.mono_left (Finset.mem_powerset.mp hN))
          common divisor f hf0 h Z M r ell V delta B j eta tau hZ hb₁ hb₂ hf hd hc hj
          (hcol₂ Q hQ hq) (hcol₁ N hN hn) hout)
  simpa only [Real.exp_log hU₁,Real.exp_log hU₂,one_mul,primeSubsetGenerator_norm_eq_productNorm]
    using hb

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0454

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstMarkedColumns
Source SHA256: a45f25331b7da7fba9e4018e776d68b0dfa30f8aec8f2df7a031dcaf947d08f2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0455



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]

theorem cube_whole_column_norm (p : ι→O) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C N : Finset ι) (hC : Disjoint C b.support) (hN : Disjoint N (b.support∪C))
    (negative : Bool) :
    primeProductNorm p (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N) =
      ‖eisEmbedding (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
        primeProductNorm p C * primeProductNorm p N := by
  have hd : (if negative then b.rightDivisor else b.leftDivisor) ⊆ b.support := by
    cases negative
    · exact hb.1
    · exact hb.2
  rw [primeProductNorm_union p _ _ (hN.symm.mono_left (Finset.union_subset_union hd (Finset.Subset.refl C))),
    primeProductNorm_union p _ _ (hC.symm.mono_left hd)]
  congr 2
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [CubeCoordinates.aLabel_left p b hb]; rfl
  · rw [CubeCoordinates.aLabel_right p b hb]; rfl

def wholeMarkedTest {σ : Type*} [DecidableEq σ] (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (test : Finset ι→ℂ) (U : Finset ι) : ℂ :=
  primeMark slots lists a U * test U

theorem whole_marked_test_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ, 0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test : Finset ι→ℂ) (G L : ℝ),0≤G → 0≤L →
      (∀ U,‖test U‖≤G) → (∀ U,test U≠0 → primeProductNorm p U≤L) →
      ∀ U,‖wholeMarkedTest slots lists a test U‖≤Cm*L^ε*G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha test G L hG hL hb hs U
  by_cases hz : test U=0
  · simp only [wholeMarkedTest,hz,mul_zero,norm_zero]; positivity
  · have hn0 := (primeProductNorm_pos p hp U).le
    rw [wholeMarkedTest,norm_mul]
    calc
      _ ≤ (Cm*(primeProductNorm p U)^ε)*G :=
        mul_le_mul (hmark p hp hcop slots lists a hslots ha U) (hb U) (norm_nonneg _) (by positivity)
      _ ≤ Cm*L^ε*G := by gcongr; exact hs U hz

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_residual_norm (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀ u,‖Ψ u‖≤1) (m f : O) (H : Finset ι→ℂ) (N : Finset ι) :
    ‖canonicalCubeResidual p hg b C negative Ψ m f H N‖ ≤
      ‖H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N)‖ := by
  exact originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit negative
    Ψ hΨ m (∏i∈C,p i) f _ N

theorem canonical_residual_test_nonzero (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) (N : Finset ι)
    (hn : canonicalCubeResidual p hg b C negative Ψ m f H N≠0) :
    H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪N)≠0 := by
  exact originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit negative
    Ψ m (∏i∈C,p i) f _ N hn

theorem canonical_marked_residual_support {σ : Type*} [DecidableEq σ]
    (b : CubeCoordinates ι) (hb : b.Admissible) (C N : Finset ι)
    (hC : Disjoint C b.support) (hN : Disjoint N (b.support∪C)) (negative : Bool)
    (Ψ : O→*ℂ) (m f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (test : Finset ι→ℂ) (L : ℝ) (hs : ∀ U,test U≠0 → primeProductNorm p U≤L)
    (hn : canonicalCubeResidual p hg b C negative Ψ m f (wholeMarkedTest slots lists a test) N≠0) :
    ‖eisEmbedding (aLabel p b.support (if negative then b.rightBit else b.leftBit))‖^2 *
      primeProductNorm p C * primeProductNorm p N≤L := by
  have ht := canonical_residual_test_nonzero p hg b C negative Ψ m f _ N hn
  have htest := (mul_ne_zero_iff.mp ht).2
  simpa only [cube_whole_column_norm p b hb C N hC hN negative] using hs _ htest

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0455

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstCanonicalTail
Source SHA256: ae3792fc3a65f071dca07f19a05ddd60d91c850fd5e6e834eaa050c717d3d49f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0456


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem first_canonical_marked_tail (ε : ℝ) (hε : 0<ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ),0<Ct ∧ 0<Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι),b.Admissible →
      ∀ (common divisor : Finset ι),Disjoint common b.support →
      ∀ (f : Ideal O),f≠0 →
      ∀ (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤G₁ → 0≤G₂ → 0<Z →
      (∀ U,‖test₁ U‖≤G₁) → (∀ U,‖test₂ U‖≤G₂) →
      (∀ U,test₁ U≠0 → primeProductNorm p U≤Z^(r+eta)) →
      (∀ U,test₂ U≠0 → primeProductNorm p U≤Z^(r+eta)) →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤Z^(V+eta) → primeProductNorm p divisor≤Z^(delta+eta) →
      Z^(B-eta)≤primeProductNorm p common →
      Z^(j-eta)≤‖eisEmbedding (jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit)‖^2 →
      let residualPool := pool\(b.support∪common)
      let C₁ := canonicalCubeResidual p hg b common true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator f)
        (wholeMarkedTest slots lists a test₁)
      let C₂ := canonicalCubeResidual p hg b common false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator f)
        (wholeMarkedTest slots lists a test₂)
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p common)
      let G₁' := Cm*(Z^(r+eta))^ε*G₁
      let G₂' := Cm*(Z^(r+eta))^ε*G₂
      let active := cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hcop hg residualPool b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit C₁ C₂ W
        (fun _=>1) (fun _=>1) 1 1 (Z^M)
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁'*G₂'*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_first_physical_tail order
  obtain ⟨Cm,hCm,hmark⟩ := whole_marked_test_uniform ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hchar pool b hb common divisor hcommon f hf0 Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ slots lists a hslots ha test₁ test₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ
    htest₁ htest₂ hs₁ hs₂ hb₁ hb₂ hf hd hc hj residualPool C₁ C₂ U₁ U₂ G₁' G₂' active slow T
  have hdis : Disjoint residualPool (b.support∪common) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi2
    exact (Finset.mem_sdiff.mp hi).2 hi2
  apply htail p hp hinj hcop hg hchar residualPool b.support common divisor b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos (hdis.mono_right Finset.subset_union_left) f hf0 C₁ C₂ W
    G₁' G₂' Z M r ell V delta B j eta tau (by dsimp [G₁']; positivity) (by dsimp [G₂']; positivity) hZ
  · intro N hN
    exact (canonical_residual_norm p hg b common true Ψ₁ hΨ₁ m₁ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha test₁ G₁ (Z^(r+eta)) hG₁
        (Real.rpow_pos_of_pos hZ _).le htest₁ hs₁ _)
  · intro N hN
    exact (canonical_residual_norm p hg b common false Ψ₂ hΨ₂ m₂ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha test₂ G₂ (Z^(r+eta)) hG₂
        (Real.rpow_pos_of_pos hZ _).le htest₂ hs₂ _)
  · exact hb₁
  · exact hb₂
  · exact hf
  · exact hd
  · exact hc
  · exact hj
  · intro N hN hn
    exact canonical_marked_residual_support p hg b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) true Ψ₁ m₁ _ slots lists a test₁ _ hs₁ hn
  · intro N hN hn
    exact canonical_marked_residual_support p hg b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) false Ψ₂ m₂ _ slots lists a test₂ _ hs₂ hn

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0456

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstMarkedZero
Source SHA256: 2fef5c42980411086edb8dae7fc85240476181cb9ba08a10d51ab311a25eb262
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0457


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem first_marked_zero_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ L K : ℝ),0≤G₁ → 0≤G₂ → 0≤L →
      (∀ U,‖test₁ U‖≤G₁) → (∀ U,‖test₂ U‖≤G₂) →
      (∀ U,test₁ U≠0 → primeProductNorm p U≤L) →
      (∀ U,test₂ U≠0 → primeProductNorm p U≤L) →
      ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
        (wholeMarkedTest slots lists a test₁) (wholeMarkedTest slots lists a test₂) W K‖ ≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (Cm*L^ε*G₁)*(Cm*L^ε*G₂) * |K| * ‖paperRadialFourier W 0‖ else 0 := by
  obtain ⟨Cm,hCm,hmark⟩ := whole_marked_test_uniform ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f slots lists a hslots ha
    test₁ test₂ W G₁ G₂ L K hG₁ hG₂ hL ht₁ ht₂ hs₁ hs₂
  apply (canonicalCubeDualZero_norm_le p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hmark p hp hcop slots lists a hslots ha test₁ G₁ L hG₁ hL ht₁ hs₁ _)
        (hmark p hp hcop slots lists a hslots ha test₂ G₂ L hG₂ hL ht₂ hs₂ _)
        (norm_nonneg _) (by positivity)) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0457

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstTailAbsorption
Source SHA256: ae0e64c61941fe2b185365d6c5894215648bd25adfad072c67b3cff516e22221
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0458


namespace OAI

namespace SevenEighths.InverseMoment
open SecondPassArithmetic
noncomputable section

lemma first_tail_fixed_cap (K D E U₁ U₂ B G₁ G₂ P H : ℝ) (A : ℕ)
    (hK : 0<K) (hD : 0<D) (hE : 0<E) (hU₁ : 0<U₁) (hU₂ : 0<U₂) (hB : 1≤B)
    (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hP : 0≤P) (hH : 0≤H)
    (hKb : K≤B) (hKi : K⁻¹≤B) (hDb : D≤B) (hEb : E≤B) (h₁ : U₁≤B) (h₂ : U₂≤B) :
    (128*U₁)*(128*U₂)*(G₁*G₂*K)*
      (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+H)^A)) ≤
    65536*G₁*G₂*P*B^19/(1+H)^A := by
  have hB0 : 0≤B := zero_le_one.trans hB
  have hB2 : B≤B^2 := by nlinarith
  have hB3 : B≤B*B^2 := le_mul_of_one_le_right hB0 (one_le_pow₀ hB)
  have hb := firstTail_scalar_bound K D E U₁ U₂ B B G₁ G₂ P H A hK hD hE hU₁ hU₂
    hB0 hG₁ hG₂ hP hH (hDb.trans hB3) (hEb.trans hB2) h₁ h₂
  have hscale : 1+B^3*B^4/K≤2*B^8 := by
    calc
      _ ≤ 1+B^3*B^4*B := by rw [div_eq_mul_inv]; gcongr
      _ ≤ 2*B^8 := by have hh : 1≤B^8 := one_le_pow₀ hB; nlinarith [hh]
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (128*B)^2*(G₁*G₂*B)*P*(2*B^8)^2 := by gcongr
    _ = _ := by ring

theorem choose_first_tail_order (Lcap tau saving : ℝ) (hL : 0≤Lcap) (htau : 0<tau) :
    ∃ A : ℕ, ∀ (Z K D E U₁ U₂ G₁ G₂ P : ℝ),1≤Z →
      0<K → 0<D → 0<E → 0<U₁ → 0<U₂ → 0≤G₁ → 0≤G₂ → 0≤P →
      K≤Z^Lcap → K⁻¹≤Z^Lcap → D≤Z^Lcap → E≤Z^Lcap → U₁≤Z^Lcap → U₂≤Z^Lcap →
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+Z^tau)^A)) ≤
      65536*G₁*G₂*P*Z^(-saving) := by
  obtain ⟨A,hA⟩ := exists_nat_gt ((19*Lcap+saving)/tau)
  refine ⟨A,?_⟩
  intro Z K D E U₁ U₂ G₁ G₂ P hZ hK hD hE hU₁ hU₂ hG₁ hG₂ hP hKb hKi hDb hEb h₁ h₂
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := first_tail_fixed_cap K D E U₁ U₂ (Z^Lcap) G₁ G₂ P (Z^tau) A
    hK hD hE hU₁ hU₂ (Real.one_le_rpow hZ hL) hG₁ hG₂ hP
    (Real.rpow_pos_of_pos hz _).le hKb hKi hDb hEb h₁ h₂
  have hdecay : (Z^Lcap)^19/(1+Z^tau)^A≤Z^(-saving) := by
    calc
      _ ≤ (Z^Lcap)^19/(Z^tau)^A := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) A)
      _ = Z^(19*Lcap-tau*(A:ℝ)) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        have hh := (div_lt_iff₀ htau).mp hA
        nlinarith
  apply hb.trans
  calc
    _ = (65536*G₁*G₂*P)*((Z^Lcap)^19/(1+Z^tau)^A) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0458

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstSourceSize
Source SHA256: 8f7a4fc47a1f47deff84087b884ebde5d94b0d462b4bd1e48c07c3b5e59be23b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0459


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} (p : ι→O) (hp : ∀i,p i≠0)

include hp in
theorem first_nonempty_column_center (U : Finset ι) (Z r eta : ℝ) (hZ : 1<Z)
    (hU : primeProductNorm p U≤Z^(r+eta)) : -eta≤r := by
  have hh : Z^(0:ℝ)≤Z^(r+eta) := by
    rw [Real.rpow_zero]
    exact (primeProductNorm_ge_one p hp U).trans hU
  have := (Real.rpow_le_rpow_left_iff hZ).mp hh
  linarith

variable [DecidableEq ι]

include hp in

theorem first_source_divisor_center (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z r ell delta eta : ℝ) (hZ : 1<Z)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta))
    (hd : Z^(delta-eta)≤primeProductNorm p D) : delta≤r+2*ell+4*eta := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hh := hd.trans (cubeSourceDivisor_norm_bound p hp b C D (Z^(ell+eta)) (Z^(r+eta))
    (Real.rpow_pos_of_pos hz _).le (Real.rpow_pos_of_pos hz _).le hCB h1 h2 hC hD)
  rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz] at hh
  have := (Real.rpow_le_rpow_left_iff hZ).mp hh
  norm_num at this
  linarith

include hp in
theorem first_source_scalar_caps (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M Mmax Fmax r ell V eta : ℝ) (hZ : 1≤Z)
    (hM : 0≤M) (hMm : M≤Mmax) (hF : 0≤Fmax) (hell : 0≤ell) (hV : 0≤V)
    (heta : 0≤eta) (hr : -eta≤r) (hwhole : r+3*ell+V≤Fmax)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta)) :
    let cap := Mmax+Fmax+3*eta
    Z^M≤Z^cap ∧ (Z^M)⁻¹≤Z^cap ∧ primeProductNorm p D≤Z^cap ∧
    primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤Z^cap ∧
    (∀ eps : ι→Bool,Z^(r+eta)/(‖eisEmbedding (aLabel p b.support eps)‖^2*primeProductNorm p C)≤Z^cap) := by
  dsimp only
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hcap : 0≤Mmax+Fmax+3*eta := by linarith
  refine ⟨Real.rpow_le_rpow_of_exponent_le hZ (by linarith),?_,?_,?_,?_⟩
  · calc
      _ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hZ hM)
      _ ≤ _ := Real.one_le_rpow hZ hcap
  · have hd := cubeSourceDivisor_norm_bound p hp b C D (Z^(ell+eta)) (Z^(r+eta))
      (Real.rpow_pos_of_pos hz _).le (Real.rpow_pos_of_pos hz _).le hCB h1 h2 hC hD
    apply hd.trans
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  · apply (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
    apply (cubeCoordinates_radical_bound p hp b (Z^(ell+eta)) (Real.rpow_pos_of_pos hz _).le h1 h2).trans
    rw [←Real.rpow_mul_natCast hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  · intro eps
    have ha := element_norm_ge_one (aLabel p b.support eps) (primeProduct_ne_zero p hp _ _)
    have hc := primeProductNorm_ge_one p hp C
    calc
      _ ≤ Z^(r+eta) := div_le_self (Real.rpow_pos_of_pos hz _).le (one_le_mul_of_one_le_of_one_le ha hc)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0459

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstSourceTail
Source SHA256: d260b93650e0e09a09439a9633fbc09ff846376adbf4e71e40ccfd51e2e0c012
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0460


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem choose_actual_first_tail_order (Mmax Fmax eta tau saving : ℝ)
    (hMm : 0≤Mmax) (hFm : 0≤Fmax) (heta : 0≤eta) (htau : 0<tau) :
    ∃ order : ℕ,∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (b : CubeCoordinates ι) (C D : Finset ι),Disjoint C b.support →
      D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit →
      ∀ (Z M r ell V G₁ G₂ P : ℝ),1≤Z → 0≤M → M≤Mmax → 0≤ell → 0≤V → -eta≤r →
      r+3*ell+V≤Fmax → 0≤G₁ → 0≤G₂ → 0≤P →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      primeProductNorm p C≤Z^(r+eta) →
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p C)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p C)
      let active := cubeActiveSupport b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z^M/(primeProductNorm p D*primeProductNorm p active*U₁*U₂)
      (128*U₁)*(128*U₂)*(G₁*G₂*Z^M)*(P/((min 1 slow)^2*(1+Z^tau)^order))≤
        65536*G₁*G₂*P*Z^(-saving) := by
  obtain ⟨order,he⟩ := choose_first_tail_order (Mmax+Fmax+3*eta) tau saving (by linarith) htau
  refine ⟨order,?_⟩
  intro ι _ p hp _ b C D hCB hD Z M r ell V G₁ G₂ P hZ hM hMmax hell hV hr hwhole hG₁ hG₂ hP h1 h2 hC
  dsimp only
  have hz : 0<Z := zero_lt_one.trans_le hZ
  obtain ⟨hk,hki,hd,ha,hu⟩ := first_source_scalar_caps p hp b C D hCB hD
    Z M Mmax Fmax r ell V eta hZ hM hMmax hFm hell hV heta hr hwhole h1 h2 hC
  have hapos (eps : ι→Bool) : 0<‖eisEmbedding (aLabel p b.support eps)‖^2 :=
    SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
  exact he Z (Z^M) (primeProductNorm p D)
    (primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit))
    (Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p C))
    (Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p C))
    G₁ G₂ P hZ (Real.rpow_pos_of_pos hz _) (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _)
    (div_pos (Real.rpow_pos_of_pos hz _) (mul_pos (hapos _) (primeProductNorm_pos p hp _)))
    (div_pos (Real.rpow_pos_of_pos hz _) (mul_pos (hapos _) (primeProductNorm_pos p hp _)))
    hG₁ hG₂ hP hk hki hd ha (hu _) (hu _)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0460

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstWholeMarkedColumns
Source SHA256: 976397facadb2c73fa0a345a4da080d80798da9311edb311d5192cf407b651b3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0461


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

theorem primeProductNorm_union_le_mul {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal] (A U : Finset ι) :
    primeProductNorm p (A∪U)≤primeProductNorm p A*primeProductNorm p U := by
  have he : A∪U=A∪(U\A) := by ext i;simp only [Finset.mem_union,Finset.mem_sdiff];tauto
  rw [he,primeProductNorm_union p A (U\A) Finset.disjoint_sdiff]
  exact mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp Finset.sdiff_subset)
    (primeProductNorm_pos p hp A).le

theorem whole_cube_marked_test_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (extra : Finset ι) (test : Finset ι→ℂ) (E G L : ℝ),0≤E → 0≤G → 0≤L →
      primeProductNorm p extra≤E → (∀ U,‖test U‖≤G) →
      (∀ U,test U≠0→primeProductNorm p U≤L) →
      ∀ U,‖primeMark slots lists a (extra∪U)*test U‖≤Cm*(E*L)^ε*G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha extra test E G L hE hG hL he hb hs U
  by_cases hz : test U=0
  · simp only [hz,mul_zero,norm_zero];positivity
  have hnorm : primeProductNorm p (extra∪U)≤E*L :=
    (primeProductNorm_union_le_mul p hp extra U).trans
      (mul_le_mul he (hs U hz) (primeProductNorm_pos p hp U).le hE)
  have hnorm0 := (primeProductNorm_pos p hp (extra∪U)).le
  rw [norm_mul]
  calc
    _ ≤ (Cm*(primeProductNorm p (extra∪U))^ε)*G :=
      mul_le_mul (hmark p hp hcop slots lists a hslots ha _) (hb U) (norm_nonneg _) (by positivity)
    _ ≤ _ := by gcongr

theorem first_whole_cube_marked_zero_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra₁ extra₂ : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (E G₁ G₂ L K : ℝ),
      0≤E → 0≤G₁ → 0≤G₂ → 0≤L → primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (∀ U,‖test₁ U‖≤G₁) → (∀ U,‖test₂ U‖≤G₂) →
      (∀ U,test₁ U≠0→primeProductNorm p U≤L) → (∀ U,test₂ U≠0→primeProductNorm p U≤L) →
      ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U) W K‖ ≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (Cm*(E*L)^ε*G₁)*(Cm*(E*L)^ε*G₂) * |K| * ‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖ else 0 := by
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C extra₁ extra₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ f slots lists a hslots ha test₁ test₂ W E G₁ G₂ L K hE hG₁ hG₂ hL he₁ he₂ hb₁ hb₂ hs₁ hs₂
  apply (canonicalCubeDualZero_norm_le p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hmark p hp hcop slots lists a hslots ha extra₁ test₁ E G₁ L hE hG₁ hL he₁ hb₁ hs₁ _)
        (hmark p hp hcop slots lists a hslots ha extra₂ test₂ E G₂ L hE hG₂ hL he₂ hb₂ hs₂ _)
        (norm_nonneg _) (by positivity)) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0461

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstWholeCanonicalTail
Source SHA256: 2673f072cc0d6300e72e0ef14f492ca330612caa1f480bb5e1dfc51ad426b650
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0462


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem first_whole_cube_canonical_tail (ε : ℝ) (hε : 0<ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ),0<Ct ∧ 0<Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι),b.Admissible →
      ∀ (common divisor : Finset ι),Disjoint common b.support →
      ∀ (f : Ideal O),f≠0 →
      ∀ (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ : O) (extra₁ extra₂ : Finset ι) (E : ℝ) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      0≤E → primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤G₁ → 0≤G₂ → 0<Z →
      (∀ U,‖test₁ U‖≤G₁) → (∀ U,‖test₂ U‖≤G₂) →
      (∀ U,test₁ U≠0 → primeProductNorm p U≤Z^(r+eta)) →
      (∀ U,test₂ U≠0 → primeProductNorm p U≤Z^(r+eta)) →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤Z^(V+eta) → primeProductNorm p divisor≤Z^(delta+eta) →
      Z^(B-eta)≤primeProductNorm p common →
      Z^(j-eta)≤‖eisEmbedding (jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit)‖^2 →
      let residualPool := pool\(b.support∪common)
      let C₁ := canonicalCubeResidual p hg b common true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
      let C₂ := canonicalCubeResidual p hg b common false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U)
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p common)
      let G₁' := Cm*(E*Z^(r+eta))^ε*G₁
      let G₂' := Cm*(E*Z^(r+eta))^ε*G₂
      let active := cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hcop hg residualPool b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit C₁ C₂ W
        (fun _=>1) (fun _=>1) 1 1 (Z^M)
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁'*G₂'*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_first_physical_tail order
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hchar pool b hb common divisor hcommon f hf0 Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ extra₁ extra₂ E slots lists a hE he₁ he₂ hslots ha test₁ test₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ
    htest₁ htest₂ hs₁ hs₂ hb₁ hb₂ hf hd hc hj residualPool C₁ C₂ U₁ U₂ G₁' G₂' active slow T
  have hdis : Disjoint residualPool (b.support∪common) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi2
    exact (Finset.mem_sdiff.mp hi).2 hi2
  apply htail p hp hinj hcop hg hchar residualPool b.support common divisor b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos (hdis.mono_right Finset.subset_union_left) f hf0 C₁ C₂ W
    G₁' G₂' Z M r ell V delta B j eta tau (by dsimp [G₁']; positivity) (by dsimp [G₂']; positivity) hZ
  · intro N hN
    exact (canonical_residual_norm p hg b common true Ψ₁ hΨ₁ m₁ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha extra₁ test₁ E G₁ (Z^(r+eta)) hE hG₁
        (Real.rpow_pos_of_pos hZ _).le he₁ htest₁ hs₁ _)
  · intro N hN
    exact (canonical_residual_norm p hg b common false Ψ₂ hΨ₂ m₂ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha extra₂ test₂ E G₂ (Z^(r+eta)) hE hG₂
        (Real.rpow_pos_of_pos hZ _).le he₂ htest₂ hs₂ _)
  · exact hb₁
  · exact hb₂
  · exact hf
  · exact hd
  · exact hc
  · exact hj
  · intro N hN hn
    have ht := canonical_residual_test_nonzero p hg b common true Ψ₁ m₁
      (ConcretePrimeRowBridge.idealGenerator f) _ N hn
    have hn' := hs₁ _ (mul_ne_zero_iff.mp ht).2
    have he := cube_whole_column_norm p b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) true
    simp only [ite_true] at he
    exact he ▸ hn'
  · intro N hN hn
    have ht := canonical_residual_test_nonzero p hg b common false Ψ₂ m₂
      (ConcretePrimeRowBridge.idealGenerator f) _ N hn
    have hn' := hs₂ _ (mul_ne_zero_iff.mp ht).2
    have he := cube_whole_column_norm p b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) false
    simp only [ite_false,Bool.false_eq_true] at he
    exact he ▸ hn'

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0462

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstZeroSource
Source SHA256: 0e2972346427e4da9faa96df8133fcd6b642b1857902d7a88546c33045a0c6f8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0463


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))
  (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
include hinj hc in
theorem first_variable_zero_common_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (labels : Finset (Ideal O))
    (a : Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ : O) (H₁ H₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
    (Γ G₁ G₂ L K : ℝ) (hΓ : 0≤Γ) (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hL : 0<L)
    (ha : ∀C∈(pool\b.support).powerset,∀I∈labels,‖a C I‖≤Γ)
    (hH₁ : ∀U,‖H₁ U‖≤G₁) (hH₂ : ∀U,‖H₂ U‖≤G₂) (hsupp : ∀U,H₁ U≠0→primeProductNorm p U≤L) :
    ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator I)
        H₁ H₂ W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (128*(L))*(labels.card:ℝ)*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) else 0 := by
  let z (C:Finset ι) (I:Ideal O):ℂ:=canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
    (ConcretePrimeRowBridge.idealGenerator I)
    H₁ H₂ W K
  let Q:ℝ:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  have hQ:0≤Q:=by dsimp [Q];positivity
  have heq : (∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I)=
      ∑C∈boundedPrimeSupports p (pool\b.support) (L),∑I∈labels,a C I*z C I := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro C hC hnot
    have hbnd : ¬primeProductNorm p C≤L:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
    apply Finset.sum_eq_zero
    intro I hI
    have hz : H₁ (b.rightDivisor∪C)=0 := by
      by_contra hh
      exact hbnd ((primeProductNorm_mono p hp Finset.subset_union_right).trans (hsupp _ hh))
    have hz' : z C I=0 := by
      dsimp only [z]
      rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj]
      split_ifs <;> simp [hz]
    rw [hz',mul_zero]
  change ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I‖≤_
  rw [heq]
  by_cases hb : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  · rw [ite_eq_left hb]
    have hpnt (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) (L)) (I:Ideal O) (hI:I∈labels):‖a C I*z C I‖≤Q:=by
      rw [norm_mul]
      have hz:=canonicalCubeDualZero_norm_le p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator I) H₁ H₂ W K
      rw [ite_eq_left hb] at hz
      have hz' : ‖z C I‖≤G₁*G₂ * |K| * ‖paperRadialFourier W 0‖ := by
        apply hz.trans
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul (hH₁ _) (hH₂ _) (norm_nonneg _) hG₁) (abs_nonneg _)) (norm_nonneg _)
      exact mul_le_mul (ha C (Finset.mem_filter.mp hC).1 I hI) hz' (norm_nonneg _) hΓ
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (L),∑I∈labels,‖a C I*z C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (L),∑I∈labels,Q:=
        Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun I hI=>hpnt C hC I hI))
      _ = ((boundedPrimeSupports p (pool\b.support) (L)).card:ℝ)*(labels.card:ℝ)*Q:=by simp;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj _ _ hL) (Nat.cast_nonneg _)) hQ
  · rw [ite_eq_right hb]
    have hz (C:Finset ι) (I:Ideal O):z C I=0:=by
      dsimp [z]
      rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj,ite_eq_right hb]
    simp only [hz,mul_zero,Finset.sum_const_zero,norm_zero,le_refl]

end
theorem full_variable_first_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i}) (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (H₁ H₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ L K B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<L → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀b∈bs,∀U,‖H₁ b U‖≤G₁) → (∀b∈bs,∀U,‖H₂ b U‖≤G₂) → (∀b∈bs,∀U,H₁ b U≠0→primeProductNorm p U≤L) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (H₁ b) (H₂ b) W K‖≤
      C*B^(1+ε)*(L)*F*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) := by
  obtain ⟨C,hC,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨C*128*128,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ W Γ G₁ G₂ L K B F hΓ hG₁ hG₂ hL hB hF hΨ₁ hΨ₂ hadm hb1 hb2 hI0 hIF ha hH₁ hH₂ hsupp
  let Q:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  let good:=fun b:CubeCoordinates ι=>cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:((bs.filter good).card:ℝ)≤C*B^(1+ε):=by
    have h:=hcount p hp hinj (bs.filter good) B 1 hB (by norm_num)
      (fun b hb=>hadm b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb1 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb2 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>by
        have he : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ := (Finset.mem_filter.mp hb).2
        rw [he]
        simp)
    simpa only [mul_one] using h
  calc
    _ ≤ ∑b∈bs,‖∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (H₁ b) (H₂ b) W K‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,if good b then (128*(L))*(labels.card:ℝ)*Q else 0:=by
      apply Finset.sum_le_sum
      intro b hb
      exact first_variable_zero_common_bound p hp hcop hg hinj hc pool b labels (a b) Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ (H₁ b) (H₂ b) W Γ G₁ G₂ L K hΓ hG₁ hG₂ hL (ha b hb) (hH₁ b hb) (hH₂ b hb) (hsupp b hb)
    _ = ((bs.filter good).card:ℝ)*((128*(L))*(labels.card:ℝ)*Q):=by
      rw [←Finset.sum_filter];simp
    _ ≤ (C*B^(1+ε))*((128*(L))*(128*F)*Q):=by
      apply mul_le_mul hbcount _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlabel (by positivity)) hQ
    _ = _ := by dsimp [Q];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0463

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ProfileIntegral
Source SHA256: f6e1b2cea8d2a3d33353bf559704acd23ee02873dbb34f3a56f91e7b94e3e745
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0464


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma full_density_integrable (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) :
    Integrable (fullProfileDensity g b₁ b₂ b₃) := by
  have hc : Continuous (fullProfileDensity g b₁ b₂ b₃) := by
    unfold fullProfileDensity coordinateDensity tripleCoefficient
    fun_prop
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  simpa only [tripleHeight,coordinateHeight,pow_zero,Finset.prod_const_one,mul_one,one_mul] using
    fullProfileDensity_weighted_integrable g b₁ b₂ b₃ 0

lemma full_density_mode_integrable (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (a₁ a₂ ak y : ι → ℝ) :
    Integrable (fun p : Frequency × (ι → ℝ) => fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak y p.1 p.2) := by
  have hc : Continuous (fun p : Frequency × (ι → ℝ) => pureProfileMode a₁ a₂ ak y p.1 p.2) := by
    unfold pureProfileMode logPhase
    fun_prop
  exact (full_density_integrable g b₁ b₂ b₃).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => (pureProfileMode_norm a₁ a₂ ak y p.1 p.2).le))

theorem full_density_mode_fubini (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (a₁ a₂ ak y : ι → ℝ) :
    (∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak y p.1 p.2) =
    ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : ι → ℝ,
      fullProfileDensity g b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
        pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u := by
  let f : Frequency × (ι → ℝ) → ℂ := fun p => fullProfileDensity g b₁ b₂ b₃ p *
    pureProfileMode a₁ a₂ ak y p.1 p.2
  have hf : Integrable f (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using full_density_mode_integrable g b₁ b₂ b₃ a₁ a₂ ak y
  change (∫ p, f p) = _
  rw [Measure.volume_eq_prod, integral_prod _ hf]
  have ht : Integrable (fun t : Frequency => ∫ u, f (t,u)) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hf.integral_prod_left
  rw [Measure.volume_eq_prod, integral_prod _ ht]
  apply integral_congr_ae
  filter_upwards [ht.prod_right_ae] with t₁ ht₁
  simpa only [Measure.volume_eq_prod] using integral_prod (fun t : ℝ×ℝ => ∫ u, f ((t₁,t.1,t.2),u)) ht₁

theorem full_density_finite_sum {κ : Type*} (s : Finset κ)
    (g : ι → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) (a₁ a₂ ak : ι → ℝ)
    (c : κ → ℂ) (y : κ → ι → ℝ) :
    (∑ k ∈ s, c k * ∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      pureProfileMode a₁ a₂ ak (y k) p.1 p.2) =
    ∫ p : Frequency × (ι → ℝ), fullProfileDensity g b₁ b₂ b₃ p *
      ∑ k ∈ s, c k * pureProfileMode a₁ a₂ ak (y k) p.1 p.2 := by
