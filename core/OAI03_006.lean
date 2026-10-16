      rw [positiveHeightPower_eq_cpow _ _ hvpos,Complex.norm_cpow_eq_rpow_re_of_pos hvpos]
      norm_num
      have hh := Real.rpow_le_rpow_of_exponent_le hv1 (show (4/3:ℝ)≤2 by norm_num)
      simpa using hh
    rw [cuspSeedDefectProfile_dilate A v hApos.ne',norm_mul]
    have hm := mul_le_mul hp (hbound (v/A)) (norm_nonneg _) (sq_nonneg v)
    calc
      _ ≤ v^2*C := hm
      _ ≤ (2*A)^2*C := mul_le_mul_of_nonneg_right (sq_le_sq₀ hvpos.le (by positivity) |>.mpr hv.2) hC
      _ = (4*C)*A^2 := by ring
  · have hout : v<A ∨ 2*A<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hv
    rw [cuspSeedDefectProfile_zero A (2*A) (4/3) v (by linarith) hout,norm_zero]
    positivity

theorem smoothCuspSeedDefect_dilate_bound :
    ∃C : ℝ,0≤C ∧ ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2 := by
  obtain ⟨C,hC,hbound⟩ := cuspSeedDefectProfile_dilate_bound
  exact ⟨C,hC,fun A hA w => cuspCutoffCorrection_norm_le _ _ (by positivity) (hbound A hA) w⟩

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

lemma movingDefect_product_bound
    (f : KernelQuotient→ℂ) (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3)
    (hbound : ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2)
    (A : ℝ) (hA : 1<A) (q : KernelQuotient) :
    ‖f q‖*‖kernelQuotientDefect A (2*A) (4/3) q‖≤K*C/A := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change ‖f (integralOrbitProjection globalKubotaKernel w)‖*
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤_
    have hApos : 0<A := zero_lt_one.trans hA
    by_cases hz : smoothCuspSeedDefect A (2*A) (4/3) w=0
    · rw [hz,norm_zero,mul_zero]
      positivity
    obtain ⟨r,hr,hr'⟩ := smoothCuspSeedDefect_support A (2*A) (4/3) (by linarith) w hz
    have hheight : 0<cosetHeight r w := hApos.trans_le hr
    have hf : ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/A^3 := by
      apply (hdec w r (hA.trans_le hr)).trans
      apply div_le_div_of_nonneg_left hK (pow_pos hApos 3)
      exact pow_le_pow_left₀ hApos.le hr 3
    calc
      _ ≤ (K/A^3)*(C*A^2) := mul_le_mul hf (hbound A hA.le w) (norm_nonneg _) (by positivity)
      _ = K*C/A := by field_simp

lemma movingDefect_inner_bound
    (F : KernelQuotientL2) (f : KernelQuotient→ℂ)
    (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3)
    (hbound : ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2)
    (A : ℝ) (hA : 1<A) :
    ‖inner ℂ F (kernelL2Defect A (2*A) (by linarith) (by linarith) (4/3))‖≤
      (K*C/A)*(integralQuotientVolume globalKubotaKernel).real Set.univ := by
  rw [L2.inner_def]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [hrep,kernelL2Defect_ae_eq A (2*A) (by linarith) (by linarith) (4/3)] with q hf hd
  rw [hf,hd,RCLike.inner_apply,norm_mul]
  simpa only [starRingEnd_apply,norm_star,mul_comm] using
    movingDefect_product_bound f K C hK hC hdec hbound A hA q

theorem cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K : ℝ) (hK : 0≤K)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3) :
    inner ℂ F cubicEisensteinResidue=0 := by
  obtain ⟨C,hC,hbound⟩ := smoothCuspSeedDefect_dilate_bound
  let B : ℝ := (3/2)*(K*C)*(integralQuotientVolume globalKubotaKernel).real Set.univ
  have hB : 0≤B := by dsimp [B]; positivity
  have hb (A : ℝ) (hA : 1<A) : ‖inner ℂ F cubicEisensteinResidue‖≤B/A := by
    have he : cubicEisensteinResidue=
        kernelEisensteinResidueVector A (2*A) (by linarith) (by linarith) :=
      kernelEisensteinResidueVector_cutoff_independent 2 3 A (2*A)
        (by norm_num) (by norm_num) hA (by linarith)
    rw [he,kernelEisensteinResidueVector_pairing,norm_mul]
    norm_num
    calc
      _ ≤ (3/2)*((K*C/A)*(integralQuotientVolume globalKubotaKernel).real Set.univ) :=
        mul_le_mul_of_nonneg_left (movingDefect_inner_bound F f hrep K C hK hC hdec hbound A hA) (by norm_num)
      _ = B/A := by dsimp [B]; ring
    exact hF
  apply norm_eq_zero.mp
  by_contra hn
  have hnpos : 0<‖inner ℂ F cubicEisensteinResidue‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  let A := B/‖inner ℂ F cubicEisensteinResidue‖+2
  have hA : 1<A := by
    have hh := div_nonneg hB hnpos.le
    dsimp [A]
    linarith
  have hh := (le_div_iff₀ (zero_lt_one.trans hA)).mp (hb A hA)
  have he : ‖inner ℂ F cubicEisensteinResidue‖*A=B+2*‖inner ℂ F cubicEisensteinResidue‖ := by
    dsimp [A]
    field_simp

  rw [he] at hh
  linarith

lemma coset_decay_of_cusp_chart_decay
    (f : KernelQuotient→ℂ) (K : ℝ)
    (hdec : ∀M : CubicKubota.levelThree, ∀z : ℂ, ∀v : ℝ, ∀hv : 0<v,1<v →
      ‖f (integralOrbitProjection globalKubotaKernel
        (complexMatrix M • upperPoint z v hv))‖≤K/v^3) :
    ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3 := by
  intro w r
  induction r using Quotient.inductionOn with
  | _ M =>
    intro hr
    change 1<cosetHeight (cosetOf M) w at hr
    change _≤K/(cosetHeight (cosetOf M) w)^3
    rw [cosetHeight_cosetOf] at hr ⊢
    obtain ⟨z,v,hv,hpt⟩ := upperPoint_surjective (complexMatrix M • w)
    have hh : hyperbolicHeight (complexMatrix M • w)=v := by
      rw [←hpt,hyperbolicHeight_upperPoint]
    rw [hh] at hr ⊢
    have he : complexMatrix M⁻¹ • upperPoint z v hv=w := by
      rw [hpt,map_inv,inv_smul_smul]
    simpa only [he] using hdec M⁻¹ z v hv hr

theorem cubicEisensteinResidue_orthogonal_of_cusp_chart_decay
    (F : KernelQuotientL2) (hF : (F,(8/9:ℂ) • F)∈kernelEnergyLaplacian.graph)
    (f : KernelQuotient→ℂ) (hrep : F=ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (K : ℝ) (hK : 0≤K)
    (hdec : ∀M : CubicKubota.levelThree, ∀z : ℂ, ∀v : ℝ, ∀hv : 0<v,1<v →
      ‖f (integralOrbitProjection globalKubotaKernel
        (complexMatrix M • upperPoint z v hv))‖≤K/v^3) :
    inner ℂ F cubicEisensteinResidue=0 :=
  cubicEisensteinResidue_orthogonal_of_rapid_cusp_decay F hF f hrep K hK
    (coset_decay_of_cusp_chart_decay f K hdec)

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota

section
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_congruent_cusp_completion (A : SL(2,Eis)) (x y : Eis)
    (hxy : IsCoprime x y) (hx : (3:Eis)∣x-A 0 0) (hy : (3:Eis)∣y-A 1 0) :
    ∃ N : SL(2,Eis), N 0 0=x ∧ N 1 0=y ∧ N*A⁻¹∈levelThree := by
  obtain ⟨u,v,huv⟩ := hxy
  let t := u*A 0 1+v*A 1 1
  let N : SL(2,Eis) := ⟨!![x,-v+x*t;y,u+y*t],by
    rw [Matrix.det_fin_two_of]
    linear_combination huv⟩
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hr : (3:Eis)∣1+y*A 0 1-x*A 1 1 := by
    convert dvd_sub (dvd_mul_of_dvd_left hy (A 0 1))
      (dvd_mul_of_dvd_left hx (A 1 1)) using 1 ; linear_combination -hd
  have hmod : ∀i j,(3:Eis)∣N i j-A i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hx
    · have hv := dvd_mul_of_dvd_left hr (-v)
      convert hv using 1 ; dsimp [N,t] ; linear_combination (A 0 1)*huv
    · exact hy
    · have hu := dvd_mul_of_dvd_left hr u
      convert hu using 1 ; dsimp [N,t] ; linear_combination (A 1 1)*huv
  have hq : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) N =
      Matrix.SpecialLinearGroup.map (n:=Fin 2)
        (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) A := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (hmod i j))
  refine ⟨N,rfl,rfl,?_⟩
  change Matrix.SpecialLinearGroup.map (n:=Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (N*A⁻¹)=1
  rw [map_mul,map_inv,hq,mul_inv_cancel]

lemma cusp_completion_upper_factor (A N : SL(2,Eis)) (q g x y : Eis)
    (hx : A 0 0+3*q*A 1 0=g*N 0 0) (hy : x*A 1 0=g*N 1 0)
    (hg : g≠0) (hdet : x=g*y) :
    N.val⁻¹ * (!![1,3*q;0,x] * A.val) =
      !![g,(N.val⁻¹ * (!![1,3*q;0,x] * A.val)) 0 1;0,y] := by
  have hNdet : N 0 0*N 1 1-N 0 1*N 1 0=1 := by
    simpa only [Matrix.det_fin_two] using N.property
  have hAdet : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hinv : N.val⁻¹ = !![N 1 1,-N 0 1;-N 1 0,N 0 0] := by
    rw [Matrix.inv_def,Matrix.SpecialLinearGroup.det_coe,Ring.inverse_one,one_smul,Matrix.adjugate_fin_two]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hx,hy]
    linear_combination g*hNdet
  · rfl
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    rw [hx,hy]
    ring
  · norm_num [hinv,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    apply mul_left_cancel₀ hg
    linear_combination x*hAdet-x*(A 1 1)*hx+(A 0 1+3*q*A 1 1)*hy+hdet

end

open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

private lemma bounded_power_factor (p a : Eis) (n : ℕ) :
    ∃ j≤n,∃b,a=p^j*b ∧ (j=n ∨ ¬p∣b) := by
  induction n generalizing a with
  | zero => exact ⟨0,le_rfl,a,by simp,Or.inl rfl⟩
  | succ n ih =>
    by_cases h:p∣a
    · obtain ⟨a',rfl⟩:=h
      obtain ⟨j,hj,b,hab,hb⟩:=ih a'
      refine ⟨j+1,Nat.succ_le_succ hj,b,?_,?_⟩
      · rw [hab,pow_succ]
        ring
      · exact hb.elim (fun h=>Or.inl (congrArg (fun k=>k+1) h)) Or.inr
    · exact ⟨0,Nat.zero_le _,a,by simp,Or.inr h⟩

lemma cube_average_cusp_reduction (A : SL(2,Eis)) (p q : Eis)
    (hp : Prime p) (hprimary : lambda^2∣p-1) :
    ∃ j≤3,∃N : SL(2,Eis),
      A 0 0+3*q*A 1 0=p^j*N 0 0 ∧
      p^3*A 1 0=p^j*N 1 0 ∧ N*A⁻¹∈levelThree ∧
      (j=3 ∨ ¬p∣N 0 0) ∧
      N.val⁻¹*(!![1,3*q;0,p^3]*A.val)=
        !![p^j,(N.val⁻¹*(!![1,3*q;0,p^3]*A.val)) 0 1;0,p^(3-j)] := by
  let a:=A 0 0+3*q*A 1 0
  have haC:IsCoprime a (A 1 0) := by
    have hd : A 0 0*A 1 1-A 0 1*A 1 0=1 := by
      simpa only [Matrix.det_fin_two] using A.property
    refine ⟨A 1 1,-(A 0 1+3*q*A 1 1),?_⟩
    dsimp [a]
    linear_combination hd
  obtain ⟨j,hj,b,hab,hb⟩:=bounded_power_factor p a 3
  have hbC:IsCoprime b (A 1 0) := by
    rw [hab] at haC
    exact haC.of_mul_left_right
  have hbY:IsCoprime b (p^(3-j)*A 1 0) := by
    rcases hb with h | h
    · simpa [h] using hbC
    · exact ((hp.coprime_iff_not_dvd.mpr h).symm.pow_right).mul_right hbC
  have hpow (k:ℕ):(3:Eis)∣p^k-1 := by
    have hd:(3:Eis)∣p-1:=CubicJacobiGlobal.three_dvd_primary_sub_one p hprimary
    simpa using hd.trans (sub_dvd_pow_sub_pow p 1 k)
  have hbA:(3:Eis)∣b-A 0 0 := by
    have h1:(3:Eis)∣a-A 0 0:=by
      refine ⟨q*A 1 0,?_⟩
      dsimp [a]
      ring
    have h2:(3:Eis)∣a-b:=by
      rw [hab]
      convert dvd_mul_of_dvd_left (hpow j) b using 1 ; ring
    convert dvd_sub h1 h2 using 1 ; ring
  have hyC:(3:Eis)∣p^(3-j)*A 1 0-A 1 0 := by
    convert dvd_mul_of_dvd_left (hpow (3-j)) (A 1 0) using 1 ; ring
  obtain ⟨N,hN0,hN1,hNA⟩:=exists_congruent_cusp_completion A b (p^(3-j)*A 1 0) hbY hbA hyC
  have hA:a=p^j*N 0 0:=by rw [hN0];exact hab
  have hC:p^3*A 1 0=p^j*N 1 0:=by
    rw [hN1,←mul_assoc,←pow_add,Nat.add_sub_of_le hj]
  refine ⟨j,hj,N,hA,hC,hNA,?_,?_⟩
  · simpa [hN0] using hb
  · exact cusp_completion_upper_factor A N q (p^j) (p^3) (p^(3-j))
      hA hC (pow_ne_zero j hp.ne_zero) (by rw [←pow_add,Nat.add_sub_of_le hj])

end CubicKubota

end

end OAI
end OAIOriginalModule0272

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.RationalTranslations
Source SHA256: 617df3f531065924d9f62e2a65ba4f33b84c4e389084e6be4ea70594b3def2fb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0273


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

section
open scoped BigOperators Classical MatrixGroups

open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def rationalComplex : SL(2,ℤ) →* SL(2,ℂ) := integralComplexMatrix.comp rationalEmbedding

lemma rationalUnipotent_nat (n : ℕ) : rationalUnipotent (n:ℤ)=ModularGroup.T^n := by
  induction n with
  | zero => simpa using rationalUnipotent_zero
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,rationalUnipotent_add,ih,rationalUnipotent_one,pow_succ]

lemma rationalComplex_S_sq_row (v : Fin 2→ℂ) :
    rowOperator (rationalComplex (ModularGroup.S^2)) v = -v := by
  have hS : ((ModularGroup.S ^ 2 : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![-1,0;0,-1] := by decide
  have hC : (rationalComplex (ModularGroup.S ^ 2) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![-1,0;0,-1] := by
    apply Matrix.ext
    intro i j
    change eisEmbedding ((Int.castRingHom O) ((ModularGroup.S ^ 2 : SL(2,ℤ)) i j)) = _
    rw [congrFun (congrFun hS i) j]
    fin_cases i <;> fin_cases j <;> simp
  rw [rowOperator_apply,hC]
  funext j
  fin_cases j <;> simp [Matrix.vecMul,dotProduct,Fin.sum_univ_two]

lemma hyperbolicEisenstein_S_sq (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.S^2) • w)=hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    change eisenstein (rationalComplex (ModularGroup.S^2)*g) s=eisenstein g s
    apply tsum_congr
    intro x
    unfold summand
    rw [←rowOperator_mul,rationalComplex_S_sq_row,map_neg]
    simp [rowEnergy]

lemma hyperbolicEisenstein_T_pow (s : ℂ) (n : ℕ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.T^n) • w)=hyperbolicEisenstein s w := by
  simpa only [rationalUnipotent_nat,rationalComplex,MonoidHom.comp_apply] using hyperbolicEisenstein_unipotent (n:ℤ) s w

lemma hyperbolicEisenstein_S_even (s : ℂ) (e : Fin 2) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (ModularGroup.S^(2*e.val)) • w)=hyperbolicEisenstein s w := by
  fin_cases e
  · simp
  · exact hyperbolicEisenstein_S_sq s w

lemma hyperbolicEisenstein_bruhat (s : ℂ) (e : Fin 2) (a : Fin 3⊕(Fin 3×Fin 3)) (w : HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex (rationalBruhatRep (e,a)) • w)=
      match a with
      | Sum.inl _ => hyperbolicEisenstein s w
      | Sum.inr ab => hyperbolicEisenstein s
          (rationalComplex ModularGroup.S • (rationalComplex (ModularGroup.T^ab.2.val) • w)) := by
  simp only [rationalBruhatRep,map_mul,mul_smul,hyperbolicEisenstein_S_even]
  cases a with
  | inl a => exact hyperbolicEisenstein_T_pow s a.val w
  | inr ab => simp only [map_mul,mul_smul,hyperbolicEisenstein_T_pow]

theorem sourceEisenstein_four_cusps (s : ℂ) (w : HyperbolicSpace) :
    sourceEisenstein s w = (4:ℂ)⁻¹ * (hyperbolicEisenstein s w +
      ∑ b : Fin 3, hyperbolicEisenstein s
        (rationalComplex ModularGroup.S • (rationalComplex (ModularGroup.T^b.val) • w))) := by
  rw [sourceEisenstein,sourceProjection_eq_twentyFour]
  change (24:ℂ)⁻¹ * (∑ i : RationalBruhatIndex,
    hyperbolicEisenstein s (rationalComplex (rationalBruhatRep i) • w)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hyperbolicEisenstein_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  ring

end

section

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace MatrixGroups
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def translatedCuspCompact (M:levelTwo):Set KernelQuotient:=
  kernelSourceAction M '' kernelCuspAverageCompact

lemma translatedCuspCompact_isCompact (M:levelTwo):IsCompact (translatedCuspCompact M):=
  kernelCuspAverageCompact_isCompact.image (kernelSourceAction_continuous M)

def translatedCuspFourier (h:Eis) (M:levelTwo):KernelQuotientL2→L[ℂ]ℂ:=
  (kernelCuspFourier h).comp (kernelSourcePullback M).toContinuousLinearMap

lemma translatedCuspFourier_integral (h:Eis) (M:levelTwo) (F:KernelQuotientL2):
    translatedCuspFourier h M F=∫w in cuspPeriodStrip 5 6,
      F (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
        cuspFourierPhase h w∂hyperbolicVolume:=by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,kernelCuspFourier_integral]
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae
    (kernelSourcePullback_ae_eq M F) (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w) hw

lemma translatedCuspFourier_restrict (h:Eis) (M:levelTwo) (F:KernelQuotientL2):
    translatedCuspFourier h M
      (kernelMassRestrictionCLM (translatedCuspCompact M)
        (translatedCuspCompact_isCompact M).measurableSet F)=translatedCuspFourier h M F:=by
  rw [translatedCuspFourier_integral,translatedCuspFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelMassRestriction_coe (translatedCuspCompact M)
      (translatedCuspCompact_isCompact M).measurableSet F)
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  have hmem:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedCuspCompact M:=
    ⟨_,kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem hmem _))

def translatedCuspFamily (h:Eis) (M:levelTwo) (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ):ℂ:=
  translatedCuspFourier h M
    (kernelLocalCorrectedSeed (translatedCuspCompact M) (translatedCuspCompact_isCompact M) a b ha hab s)

lemma translatedCuspFamily_meromorphicAt (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b):
    MeromorphicAt (translatedCuspFamily h M a b ha hab) (4/3:ℂ):=
  meromorphicAt_clm (translatedCuspFourier h M)
    (kernelLocalCorrectedSeed_meromorphicAt _ (translatedCuspCompact_isCompact M) a b ha hab)

lemma translatedCuspFamily_analyticAt_nonreal (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ) (hs:s.re≠1) (hi:s.im≠0):
    AnalyticAt ℂ (translatedCuspFamily h M a b ha hab) s:=by
  exact (ContinuousLinearMap.analyticAt (𝕜:=ℂ) (E:=KernelQuotientL2) (F:=ℂ)
    (translatedCuspFourier h M) _).comp_of_eq
      (kernelLocalCorrectedSeed_analyticAt_nonreal _ (translatedCuspCompact_isCompact M)
        a b ha hab s hs hi) rfl

lemma translatedCuspFamily_residue_limit (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b):
    Tendsto (fun s:ℂ=>(s-4/3)*translatedCuspFamily h M a b ha hab s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (translatedCuspFourier h M (kernelEisensteinResidueVector a b ha hab))):=by
  have hh:=(translatedCuspFourier h M).continuous.continuousAt.tendsto.comp
    (kernelLocalCorrectedSeed_residue_limit _ (translatedCuspCompact_isCompact M) a b ha hab)
  simpa only [Function.comp_def,map_smul,smul_eq_mul,translatedCuspFourier_restrict,
    translatedCuspFamily] using hh

lemma translatedCuspFamily_actual_integral (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (s:ℂ):
    translatedCuspFamily h M a b ha hab s=∫w in cuspPeriodStrip 5 6,
      kernelCorrectedSeed a b ha hab s
        (kernelSourceAction M (integralOrbitProjection globalKubotaKernel w))*
          cuspFourierPhase h w∂hyperbolicVolume:=by
  rw [translatedCuspFamily,translatedCuspFourier_integral]
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp
    (kernelLocalCorrectedSeed_ae_eq _ (translatedCuspCompact_isCompact M) a b ha hab s)
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  apply integral_congr_ae
  filter_upwards [he,ae_restrict_mem (cuspPeriodStrip_measurable 5 6)] with w hw hwm
  have hmem:kernelSourceAction M (integralOrbitProjection globalKubotaKernel w)∈translatedCuspCompact M:=
    ⟨_,kernelCuspStripSet_subset_compact ⟨w,hwm,rfl⟩,rfl⟩
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (Set.indicator_of_mem hmem _))

theorem translatedCuspFamily_initial (h:Eis) (M:levelTwo)
    (a b:ℝ) (ha:0<a) (hab:a<b) (ha1:1<a) (s:ℂ) (hs:4<s.re) (hi:0<s.im):
    translatedCuspFamily h M a b ha hab s=∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspFourierPhase h w∂hyperbolicVolume:=by
  have hcorrected:kernelCorrectedSeed a b ha hab s=ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith):=by
    filter_upwards [kernelEisensteinL2Correction_initial_overlap a b ha1 hab s hs hi] with q hq
    change kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q=_
    rw [hq]
    ring
  have hsource:=(kernelSourceAction_measurePreserving M).quasiMeasurePreserving.ae_eq_comp hcorrected
  have hm:=kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he:=hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s:=kernelCuspStripSet))
  rw [translatedCuspFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w)
    (hw.trans (by dsimp only [Function.comp_def];rw [kernelSourceAction_mk,kernelQuotientEisenstein_mk]))

end

section

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix
open CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def oppositeSource:levelTwo:=rationalLift ModularGroup.S

lemma oppositeSource_matrix:sourceComplexMatrix oppositeSource=oppositeMatrix:=by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oppositeSource,sourceComplexMatrix,rationalLift,rationalEmbedding,
      integralComplexMatrix,Matrix.SpecialLinearGroup.map_apply_coe,ModularGroup.coe_S,oppositeMatrix]

lemma hyperbolicEisenstein_opposite_upper (s:ℂ) (z:ℂ) (v:ℝ) (hv:0<v):
    hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • upperPoint z v hv)=
      oppositeEisenstein z v hv s:=by
  rw [oppositeSource_matrix]
  rfl

theorem opposite_cusp_fourier_average (s:ℂ) (hs:2<s.re) (h:Eis):
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*
        cuspFourierPhase h w∂hyperbolicVolume)=
      unramifiedCubicGaussSeries s (9*h)*cuspWhittakerHeightFactor s h:=by
  let g:HyperbolicSpace→ℂ:=fun w=>
    hyperbolicEisenstein s (sourceComplexMatrix oppositeSource • w)*cuspFourierPhase h w
  have hg:Continuous g:=((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  rw [cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable
    (cuspCoordinateLift_weighted_integrable g hg)]
  have heq:(∫v in Set.Icc (5:ℝ) 6,
      (∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
      ∫v in Set.Icc (5:ℝ) 6,unramifiedCubicGaussSeries s (9*h)*
        ((v:ℂ)^(-s-1)*sourceFourierKernel s (cuspFrequency h*v)):=by
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hv0:0<v:=by linarith [hv.1]
    have hvz:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv0.ne'
    have hslice:(∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
          unramifiedCubicGaussSeries s (9*h):=by
      simp_rw [g,cuspCoordinateLift_positive v _ hv0,hyperbolicEisenstein_opposite_upper,
        cuspFourierPhase,hyperbolicHorizontal_upperPoint]
      exact oppositeEisenstein_fourier v hv0 s hs h
    have hp:(v:ℂ)^(-s-1)=(v:ℂ)^(2-s)/(v:ℂ)^3:=by
      rw [show -s-1=(2-s)-3 by ring,Complex.cpow_sub _ _ hvz]
      congr 1
      exact Complex.cpow_natCast _ 3
    dsimp only
    rw [hslice,hp]
    ring
  rw [heq,integral_const_mul]
  rfl

lemma translatedCuspFamily_opposite_initial (h:Eis) (s:ℂ)
    (hs:4<s.re) (hi:0<s.im):
    translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num) s=
      unramifiedCubicGaussSeries s h*cuspWhittakerHeightFactor s (3*h):=by
  rw [translatedCuspFamily_initial (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num) (by norm_num) s hs hi,
    opposite_cusp_fourier_average s (by linarith),
    show (9:Eis)*(3*h)=27*h by ring,unramifiedCubicGaussSeries_twentySeven]

def continuedUnramifiedGauss (h:Eis) (s:ℂ):ℂ:=
  translatedCuspFamily (3*h) oppositeSource 2 3 (by norm_num) (by norm_num) s/
    cuspWhittakerHeightFactor s (3*h)

def unramifiedGaussResidue (h:Eis):ℂ:=
  translatedCuspFourier (3*h) oppositeSource cubicEisensteinResidue/
    cuspWhittakerHeightFactor (4/3:ℂ) (3*h)

theorem continuedUnramifiedGauss_meromorphicAt_center (h:Eis):
    MeromorphicAt (continuedUnramifiedGauss h) (4/3:ℂ):=by
  exact (translatedCuspFamily_meromorphicAt (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num)).div
      (cuspWhittakerHeightFactor_analyticAt (3*h) (4/3) (by norm_num)).meromorphicAt

theorem continuedUnramifiedGauss_meromorphicOn_upper (h:Eis):
    MeromorphicOn (continuedUnramifiedGauss h) {s:ℂ|1<s.re ∧ 0<s.im}:=by
  intro s hs
  exact (translatedCuspFamily_analyticAt_nonreal (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num) s (ne_of_gt hs.1) (ne_of_gt hs.2)).meromorphicAt.div
      (cuspWhittakerHeightFactor_analyticAt (3*h) s hs.1).meromorphicAt

theorem continuedUnramifiedGauss_residue_limit (h:Eis):
    Tendsto (fun s:ℂ=>(s-4/3)*continuedUnramifiedGauss h s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (unramifiedGaussResidue h)):=by
  have hd:Tendsto (fun s:ℂ=>cuspWhittakerHeightFactor s (3*h))
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) (3*h))):=
    (cuspWhittakerHeightFactor_analyticAt (3*h) (4/3) (by norm_num)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hh:=(translatedCuspFamily_residue_limit (3*h) oppositeSource 2 3
    (by norm_num) (by norm_num)).div hd (cuspWhittakerHeightFactor_center_ne_zero (3*h))
  convert hh using 1
  · funext s
    simp only [continuedUnramifiedGauss,Pi.div_apply]
    ring
  · rfl

theorem continuedUnramifiedGauss_initial (h:Eis) (s:ℂ)
    (hs:4<s.re) (hi:0<s.im) (hH:cuspWhittakerHeightFactor s (3*h)≠0):
    continuedUnramifiedGauss h s=unramifiedCubicGaussSeries s h:=by
  rw [continuedUnramifiedGauss,translatedCuspFamily_opposite_initial h s hs hi,
    mul_div_cancel_right₀ _ hH]

theorem continuedUnramifiedGauss_initial_open (h:Eis):
    ∃U:Set ℂ,IsOpen U ∧ U.Nonempty ∧ U⊆{s:ℂ|4<s.re ∧ 0<s.im} ∧
      Set.EqOn (continuedUnramifiedGauss h) (fun s=>unramifiedCubicGaussSeries s h) U:=by
  obtain ⟨ε,hε,hball⟩:=Metric.eventually_nhds_iff.mp (cuspWhittakerHeightFactor_ne_zero_near_five (3*h))
  let z:ℂ:=5+(ε/2:ℝ)*Complex.I
  have hz:dist z (5:ℂ)<ε:=by
    have he:dist z (5:ℂ)=ε/2:=by simp [z,dist_eq_norm,hε.le]
    rw [he]
    linarith
  have hzim:0<z.im:=by simpa [z] using half_pos hε
  refine ⟨Metric.ball (5:ℂ) ε ∩ {s:ℂ|0<s.im},
    Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im),
    ⟨z,hz,hzim⟩,?_,?_⟩
  · intro s hs
    exact ⟨(hball hs.1).1,hs.2⟩
  · intro s hs
    exact continuedUnramifiedGauss_initial h s (hball hs.1).1 hs.2 (hball hs.1).2

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma gaussRep_mk_congr (c d : Eis) :
    c ∣ GaussianShiftedPartition.representative c (Ideal.Quotient.mk (Ideal.span {c}) d)-d := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact GaussianShiftedPartition.representative_spec c _

def cubicUnitCRTMap (a b : Eis) (r : CubicUnitResidue (a*b)) :
    CubicUnitResidue a × CubicUnitResidue b :=
  let d:=GaussianShiftedPartition.representative (a*b) r.1
  let hd:IsCoprime (a*b) d:=by
    apply (isUnit_quotient_span_iff (a*b) d).mp
    simpa only [d,GaussianShiftedPartition.representative_spec] using r.2
  (⟨Ideal.Quotient.mk (Ideal.span {a}) d,
      (isUnit_quotient_span_iff a d).mpr hd.of_mul_left_left⟩,
   ⟨Ideal.Quotient.mk (Ideal.span {b}) d,
      (isUnit_quotient_span_iff b d).mpr hd.of_mul_left_right⟩)

lemma cubicUnitCRTMap_injective (a b : Eis) (hab : IsCoprime a b) :
    Function.Injective (cubicUnitCRTMap a b) := by
  intro r t he
  have h1:=congrArg (fun z : CubicUnitResidue a × CubicUnitResidue b=>z.1.1) he
  have h2:=congrArg (fun z : CubicUnitResidue a × CubicUnitResidue b=>z.2.1) he
  change Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) t.1) at h1
  change Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) t.1) at h2
  have hdiv : a*b ∣ GaussianShiftedPartition.representative (a*b) r.1-
      GaussianShiftedPartition.representative (a*b) t.1 :=
    hab.mul_dvd
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1))
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2))
  apply Subtype.ext
  rw [←GaussianShiftedPartition.representative_spec (a*b) r.1,
    ←GaussianShiftedPartition.representative_spec (a*b) t.1]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hdiv)

lemma cubicUnitCRTMap_surjective (a b : Eis) (hab : IsCoprime a b) :
    Function.Surjective (cubicUnitCRTMap a b) := by
  rintro ⟨r,t⟩
  obtain ⟨u,v,huv⟩:=hab
  let delta:=GaussianShiftedPartition.representative a r.1
  let xi:=GaussianShiftedPartition.representative b t.1
  let d:=v*b*delta+u*a*xi
  have hda:a∣d-delta:=⟨u*(xi-delta),by dsimp [d];linear_combination delta*huv⟩
  have hdb:b∣d-xi:=⟨v*(delta-xi),by dsimp [d];linear_combination xi*huv⟩
  have had:IsCoprime a delta:=by
    apply (isUnit_quotient_span_iff a delta).mp
    simpa only [delta,GaussianShiftedPartition.representative_spec] using r.2
  have hbd:IsCoprime b xi:=by
    apply (isUnit_quotient_span_iff b xi).mp
    simpa only [xi,GaussianShiftedPartition.representative_spec] using t.2
  have hd:IsCoprime (a*b) d:=
    ((isCoprime_right_congr_of_dvd a d delta hda).mpr had).mul_left
      ((isCoprime_right_congr_of_dvd b d xi hdb).mpr hbd)
  let q:CubicUnitResidue (a*b):=⟨Ideal.Quotient.mk (Ideal.span {a*b}) d,
    (isUnit_quotient_span_iff (a*b) d).mpr hd⟩
  refine ⟨q,Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · change Ideal.Quotient.mk (Ideal.span {a}) (GaussianShiftedPartition.representative (a*b) q.1)=r.1
    rw [←GaussianShiftedPartition.representative_spec a r.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh:a∣GaussianShiftedPartition.representative (a*b) q.1-d:=
      (dvd_mul_right a b).trans (gaussRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hda
  · change Ideal.Quotient.mk (Ideal.span {b}) (GaussianShiftedPartition.representative (a*b) q.1)=t.1
    rw [←GaussianShiftedPartition.representative_spec b t.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh:b∣GaussianShiftedPartition.representative (a*b) q.1-d:=
      (dvd_mul_left b a).trans (gaussRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hdb

def cubicUnitCRTEquiv (a b:Eis) (hab:IsCoprime a b):
    CubicUnitResidue (a*b)≃CubicUnitResidue a×CubicUnitResidue b:=
  Equiv.ofBijective (cubicUnitCRTMap a b)
    ⟨cubicUnitCRTMap_injective a b hab,cubicUnitCRTMap_surjective a b hab⟩

lemma residueAdditive_unit_crt (h a b alpha beta d:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1):
    residueAdditive (3*h) (a*b) d=
      residueAdditive (3*(h*alpha)) a d*residueAdditive (3*(h*beta)) b d:=by
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  have hbeq:=congrArg eisEmbedding hbez
  simp only [map_add,map_mul,map_one] at hbeq
  simp only [cuspFrequency,map_mul,map_ofNat]
  field_simp [hae,hbe,eisLam_ne_zero]
  linear_combination -(eisEmbedding h*eisEmbedding d)*hbeq

lemma cubicUnitCRT_summand (h a b alpha beta:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1) (r:CubicUnitResidue (a*b)):
    eisEmbedding (symbol (GaussianShiftedPartition.representative (a*b) r.1) (a*b))*
      residueAdditive (3*h) (a*b) (GaussianShiftedPartition.representative (a*b) r.1)=
    (eisEmbedding (symbol (GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1) a)*
      residueAdditive (3*(h*alpha)) a (GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1))*
    (eisEmbedding (symbol (GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1) b)*
      residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1)):=by
  let d:=GaussianShiftedPartition.representative (a*b) r.1
  let delta:=GaussianShiftedPartition.representative a (cubicUnitCRTMap a b r).1.1
  let xi:=GaussianShiftedPartition.representative b (cubicUnitCRTMap a b r).2.1
  have hdelta:a∣delta-d:=gaussRep_mk_congr a d
  have hxi:b∣xi-d:=gaussRep_mk_congr b d
  change eisEmbedding (symbol d (a*b))*residueAdditive (3*h) (a*b) d=
    (eisEmbedding (symbol delta a)*residueAdditive (3*(h*alpha)) a delta)*
    (eisEmbedding (symbol xi b)*residueAdditive (3*(h*beta)) b xi)
  rw [symbol_mul_denominator,map_mul,symbol_congr hdelta,symbol_congr hxi,
    residueAdditive_unit_crt h a b alpha beta d ha hb hbez,
    residueAdditive_three_congr (h*alpha) a delta d ha hdelta,
    residueAdditive_three_congr (h*beta) b xi d hb hxi]
  ring

theorem cubicUnitGaussSum_crt (h a b alpha beta:Eis) (ha:a≠0) (hb:b≠0)
    (hbez:alpha*b+beta*a=1):
    cubicUnitGaussSum h (a*b)=
      cubicUnitGaussSum (h*alpha) a*cubicUnitGaussSum (h*beta) b:=by
  have hab:IsCoprime a b:=⟨beta,alpha,by linear_combination hbez⟩
  let f:CubicUnitResidue a→ℂ:=fun r=>eisEmbedding
    (symbol (GaussianShiftedPartition.representative a r.1) a)*
    residueAdditive (3*(h*alpha)) a (GaussianShiftedPartition.representative a r.1)
  let g:CubicUnitResidue b→ℂ:=fun r=>eisEmbedding
    (symbol (GaussianShiftedPartition.representative b r.1) b)*
    residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b r.1)
  have he:cubicUnitGaussSum h (a*b)=∑'r:CubicUnitResidue (a*b),
      f (cubicUnitCRTEquiv a b hab r).1*g (cubicUnitCRTEquiv a b hab r).2:=by
    unfold cubicUnitGaussSum
    apply tsum_congr
    intro r
    exact cubicUnitCRT_summand h a b alpha beta ha hb hbez r
  rw [he,(cubicUnitCRTEquiv a b hab).tsum_eq (fun r=>f r.1*g r.2)]
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span ha
  let:Finite (Eis⧸Ideal.span {b}):=finite_quotient_span hb
  let:Fintype (CubicUnitResidue a):=Fintype.ofFinite _
  let:Fintype (CubicUnitResidue b):=Fintype.ofFinite _
  change (∑'r:CubicUnitResidue a×CubicUnitResidue b,f r.1*g r.2)=
    (∑'r:CubicUnitResidue a,f r)*(∑'r:CubicUnitResidue b,g r)
  simp only [tsum_fintype,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

theorem cubicUnitGaussSum_coprime_product (h a b:Eis) (ha:a≠0) (hb:b≠0)
    (hap:lambda^2∣a-1) (hbp:lambda^2∣b-1) (hab:IsCoprime a b):
    cubicUnitGaussSum h (a*b)=cubicUnitGaussSum h a*cubicUnitGaussSum (h*a) b:=by
  obtain ⟨beta,alpha,hbez⟩:=hab
  have hbez':alpha*b+beta*a=1:=by linear_combination hbez
  have hab':IsCoprime a b:=⟨beta,alpha,hbez⟩
  have hA:=cubicUnitGaussSum_frequency_twist (h*alpha) a b ha hap hab'
  rw [cubicUnitGaussSum_frequency_congr _ h a ha
    (show a∣(h*alpha)*b-h from ⟨-h*beta,by linear_combination h*hbez'⟩)] at hA
  have hB:=cubicUnitGaussSum_frequency_twist (h*beta) b a hb hbp hab'.symm
  rw [cubicUnitGaussSum_frequency_congr _ h b hb
    (show b∣(h*beta)*a-h from ⟨-h*alpha,by linear_combination h*hbez'⟩)] at hB
  rw [cubicUnitGaussSum_crt h a b alpha beta ha hb hbez',←hA,←hB,
    symbol_reciprocity b a hb ha hbp hap]
  have hshift:=cubicUnitGaussSum_frequency_twist h b a hb hbp hab'.symm
  have hc:(eisEmbedding (symbol a b))^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime a b hbp hab',map_one]
  rw [←hshift]
  calc
    _=(eisEmbedding (symbol a b))^3*cubicUnitGaussSum h a*cubicUnitGaussSum (h*a) b:=by ring
    _=_:=by rw [hc,one_mul]

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedCongruence_zero (j : Fin 3) (n : ℕ) :
    ramifiedCongruence (0:Eis) j.val n ↔ j=0 ∧ 3∣n := by
  have hz : ActualEisensteinCoordinates.coords (0:Eis)=(0,0) := by
    have hh:=ShortDraftLatticeCount.coords_eval 0 0
    simpa [ActualEisensteinCoordinates.eval] using hh
  simp only [ramifiedCongruence,hz,add_zero,sub_zero]
  rw [←Int.natCast_dvd_natCast]
  constructor
  · rintro ⟨h1,h2⟩
    have hj : j.val=0 := by omega
    exact ⟨Fin.ext hj,by simpa only [hj,Nat.cast_zero,Nat.cast_ofNat,mul_zero,zero_add] using h1⟩
  · rintro ⟨rfl,hn⟩
    simpa using And.intro hn (dvd_zero (3:ℤ))

lemma arithmeticResidueSum_zero_ramified (u : Eisˣ) (n : ℕ) :
    arithmeticResidueSum 0 (u.val*lambda^(n+2))=
      if u=1 ∨ u= -1 then if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0 else 0 := by
  have hp : residueAdditive (0:Eis) 3 1=1 := by
    simp [residueAdditive,cuspFrequency]
  by_cases hu : u=1 ∨ u= -1
  · have hs : (u:Eis)=omega^0 ∨ (u:Eis)=-(omega^0) := by
      rcases hu with rfl|rfl <;> simp
    rw [ramified_arithmetic_explicit_table 0 0 u (n+2) 0 (by omega) hs (by simp),
      show ramifiedCongruence (0:Eis) 0 (n+2) ↔ 3∣n+2 by
        simpa using ramifiedCongruence_zero (0:Fin 3) (n+2),hp,mul_one,ite_eq_left hu]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
  · obtain ⟨j,hj⟩:=unit_eq_sign_omega u
    have hj0 : j≠0 := by
      intro he
      subst j
      apply hu
      rcases hj with hj|hj
      · left; apply Units.ext; simpa using hj
      · right; apply Units.ext; simpa using hj
    rw [ramified_arithmetic_explicit_table 0 0 u (n+2) j.val (by omega) hj (by simp),
      ramifiedCongruence_zero,ite_eq_right (by simp [hj0]),ite_eq_right hu]

lemma arithmeticDirichletSeries_zero_separate (s : ℂ) (hs : 2<s.re) :
    arithmeticDirichletSeries s 0=
      (∑'u:Eisˣ,∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
        arithmeticResidueSum 0 (u.val*lambda^(n+2)))*unramifiedCubicGaussSeries s 0 := by
  rw [arithmeticDirichletSeries_ramified_reindex s hs 0,←tsum_mul_right]
  apply tsum_congr
  intro u
  rw [←tsum_mul_right]
  apply tsum_congr
  intro n
  rw [unramifiedCubicGaussSeries,←tsum_mul_left]
  apply tsum_congr
  intro I
  change (if ramifiedLower u n I=0 then 0 else
    ((‖eisEmbedding (ramifiedLower u n I)‖^2:ℝ):ℂ)^(-s)*
      arithmeticResidueSum 0 (ramifiedLower u n I))=_
  rw [ite_eq_right (ramifiedLower_ne_zero u n I),eisEmbedding_norm_sq_eq_absNorm_span,
    Complex.ofReal_natCast,ramifiedLower_span,map_mul,map_pow,ramifiedIdeal_absNorm,
    Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have hp:lambda^2∣primaryGenerator I.1-1:=(primaryGenerator_spec I.1 I.2).2
  rw [show arithmeticResidueSum 0 (ramifiedLower u n I)=
      eisEmbedding (symbol (u.val*lambda^(n+2)) (primaryGenerator I.1))*
      eisEmbedding (symbol (3*(u.val*lambda^(n+2))) (primaryGenerator I.1))*
      arithmeticResidueSum 0 (u.val*lambda^(n+2))*cubicUnitGaussSum 0 (primaryGenerator I.1) from
    arithmeticResidueSum_ramified_split 0 u (n+2) (by omega) _ hp]
  have hg:=cubicUnitGaussSum_phase_shift 0 (u.val*lambda^(n+2)) (primaryGenerator I.1)
    I.2 hp (ramified_primary_coprime u (n+2) _ hp)
  simp only [zero_mul] at hg
  linear_combination ((3^(n+2):ℕ):ℂ)^(-s)*(Ideal.absNorm I.1:ℂ)^(-s)*
    arithmeticResidueSum 0 (u.val*lambda^(n+2))*hg

def ramifiedCubeExponent : ℕ ≃ {n:ℕ // 3∣n+2} :=
  Equiv.ofBijective (fun k=>⟨3*k+1,by use k+1;omega⟩) ⟨by
    intro a b h
    have hh:=congrArg Subtype.val h
    dsimp at hh
    omega,by
    rintro ⟨n,k,hk⟩
    refine ⟨k-1,Subtype.ext ?_⟩
    dsimp
    omega⟩

lemma zero_ramified_geometric (s : ℂ) (hs : 1<s.re) :
    (∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
      (if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0))=((3:ℂ)^(3*s-3)-1)⁻¹ := by
  let F : ℕ→ℂ := fun n=>((3^(n+2):ℕ):ℂ)^(-s)*
    (if 3∣n+2 then ((3^(n+2):ℕ):ℂ) else 0)
  have hsup:Function.support F⊆{n:ℕ|3∣n+2} := by
    intro n hn
    by_contra h
    change ¬3∣n+2 at h
    exact hn (by simp [F,h])
  change (∑'n,F n)=_
  rw [←tsum_subtype_eq_of_support_subset hsup]
  change (∑'n : {n:ℕ // 3∣n+2},F n.val)=_
  rw [←ramifiedCubeExponent.tsum_eq]
  have he (k:ℕ) : F (ramifiedCubeExponent k).val=ramifiedRatio s^(k+1) := by
    change ((3^(3*k+1+2):ℕ):ℂ)^(-s)*(if 3∣3*k+1+2 then ((3^(3*k+1+2):ℕ):ℂ) else 0)=_
    rw [ite_eq_left (by use k+1;omega),show 3*k+1+2=3*(k+1) by omega]
    simpa using cube_norm_weight_algebra s k 1 (by decide)
  simp_rw [he]
  exact ramified_geometric_sum s hs

lemma zero_ramified_factor (s : ℂ) (hs : 1<s.re) :
    (∑'u:Eisˣ,∑'n:ℕ,((3^(n+2):ℕ):ℂ)^(-s)*
      arithmeticResidueSum 0 (u.val*lambda^(n+2)))=
      2*((3:ℂ)^(3*s-3)-1)⁻¹ := by
  have hne : (1:Eisˣ)≠ -1 := by
    intro h
    have hh:=congrArg Units.val h
    norm_num at hh
  rw [tsum_eq_sum (s:={1,-1}) (fun u hu=>by
    have hn : ¬(u=1 ∨ u= -1):=by simpa using hu
    simp [arithmeticResidueSum_zero_ramified,hn])]
  simp only [Finset.sum_insert,Finset.mem_singleton,hne,not_false_eq_true,Finset.sum_singleton]
  simp only [arithmeticResidueSum_zero_ramified,true_or,or_true,ite_true]
  rw [zero_ramified_geometric s hs]
  ring

theorem arithmeticDirichletSeries_zero_unramified (s : ℂ) (hs : 2<s.re) :
    arithmeticDirichletSeries s 0=
      (2*((3:ℂ)^(3*s-3)-1)⁻¹)*unramifiedCubicGaussSeries s 0 := by
  rw [arithmeticDirichletSeries_zero_separate s hs,zero_ramified_factor s (by linarith)]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0273

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage
Source SHA256: f229f1fd1125b76732560aee62cfe3e7f9dea3a39626f9a2523acbe07a08285b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0274


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

open Filter MeasureTheory
open scoped BigOperators Classical Topology

lemma ramified_denominator_ne_zero (s : ℂ) (hs : 1<s.re) :
    (3:ℂ)^(3*s-3)-1≠0 := by
  intro he
  have hpow : (3:ℂ)^(3*s-3)=1 := sub_eq_zero.mp he
  have hnorm : 1<‖(3:ℂ)^(3*s-3)‖ := by
    rw [show (3:ℂ)=((3:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    apply Real.one_lt_rpow (by norm_num)
    norm_num
    linarith
  rw [hpow,norm_one] at hnorm
  exact lt_irrefl _ hnorm

theorem unramifiedCubicGaussSeries_zero (s : ℂ) (hs : 2<s.re) :
    unramifiedCubicGaussSeries s 0=unramifiedTotientSeries (3*s-2) := by
  have he:=arithmeticDirichletSeries_zero_unramified s hs
  rw [arithmeticDirichletSeries_zero_totient s (by linarith)] at he
  exact (mul_left_cancel₀ (mul_ne_zero (by norm_num) (inv_ne_zero (ramified_denominator_ne_zero s (by linarith)))) he).symm

lemma cuspWhittakerHeightFactor_zero (s : ℂ) (hs : 1<s.re) :
    cuspWhittakerHeightFactor s 0=((Real.pi:ℂ)/(s-1))*cuspScatterHeightFactor s := by
  have hs0 : s≠0 := by intro he;subst s;norm_num at hs
  unfold cuspWhittakerHeightFactor
  simp only [cuspFrequency,map_zero,zero_div,zero_mul,sourceFourierKernel_zero s hs]
  rw [integral_mul_const,cuspScatterHeightFactor_integral s hs0]
  ring

lemma opposite_zero_initial_cross (s : ℂ) (hs : 4<s.re) (hi : 0<s.im) :
    2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s=
      ((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s := by
  have hb : kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s=cuspConstantAverage s := by
    apply (kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num)
      s (by linarith) (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs hi)).trans
    exact hyperbolicEisenstein_cusp_average_eq s (by linarith)
  have ht:=translatedCuspFamily_opposite_initial 0 s hs hi
  simp only [mul_zero] at ht
  rw [ht,cuspWhittakerHeightFactor_zero s (by linarith),baseOutgoingConstant,hb,
    cuspConstantAverage,scatteringCoefficient,arithmeticDirichletSeries_zero_unramified s (by linarith)]
  have hs1 : s-1≠0 := by intro he;have hsx : s=1:=sub_eq_zero.mp he;subst s;norm_num at hs
  have halg (D V A P H U : ℂ) (hD:D≠0) (hV:V≠0) :
      2*(U*(P*H))=D*(V*(A+P*((2*D⁻¹)*U/V)*H)-V*A) := by
    field_simp
    ; ring
  exact halg _ _ _ _ _ _ (ramified_denominator_ne_zero s (by linarith)) cusp_volume_ne_zero

lemma opposite_zero_cross_identity :
    Set.EqOn (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s)
      (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s)
      {s : ℂ | 1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hleft : AnalyticOnNhd ℂ
      (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s) domain := by
    intro s hs
    exact analyticAt_const.mul (translatedCuspFamily_analyticAt_nonreal 0 oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
  have hright : AnalyticOnNhd ℂ
      (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s) domain := by
    intro s hs
    have hp : AnalyticAt ℂ (fun z:ℂ=>(3:ℂ)^(3*z-3)-1) s := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      exact Eventually.of_forall fun z=>
        ((((differentiableAt_const (3:ℂ)).mul differentiableAt_id).sub_const 3).const_cpow
          (Or.inl (by norm_num))).sub_const 1
    exact hp.mul (baseOutgoingConstant_analyticAt s hs.1 hs.2)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s=>2*translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) s)
      =ᶠ[𝓝 (5+Complex.I:ℂ)] (fun s=>((3:ℂ)^(3*s-3)-1)*baseOutgoingConstant s) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    exact opposite_zero_initial_cross s hs.1 hs.2
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

theorem translatedCuspFourier_opposite_zero_residue :
    translatedCuspFourier 0 oppositeSource cubicEisensteinResidue=cuspConstantAverageResidue := by
  have hd : Tendsto (fun s:ℂ=>(3:ℂ)^(3*s-3)-1) (𝓝[≠] (4/3:ℂ)) (𝓝 (2:ℂ)) := by
    have hc : Continuous (fun s:ℂ=>(3:ℂ)^(3*s-3)-1) :=
      (((continuous_const.mul continuous_id).sub continuous_const).const_cpow
        (Or.inl (by norm_num))).sub continuous_const
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 ; norm_num
  have hl := ((translatedCuspFamily_residue_limit 0 oppositeSource 2 3
    (by norm_num) (by norm_num)).const_mul 2).comp upperVertical_tendsto_cubic_punctured
  have hr := (hd.mul baseOutgoingConstant_residue_limit).comp upperVertical_tendsto_cubic_punctured
  have hevent : (fun t:ℝ=>2*((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily 0 oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I)))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((3:ℂ)^(3*((4/3:ℂ)+(t:ℂ)*Complex.I)-3)-1)*
        ((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*baseOutgoingConstant ((4/3:ℂ)+(t:ℂ)*Complex.I))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=opposite_zero_cross_identity (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : 2*translatedCuspFourier 0 oppositeSource cubicEisensteinResidue=2*cuspConstantAverageResidue :=
    tendsto_nhds_unique_of_eventuallyEq hl hr hevent
  exact mul_left_cancel₀ (by norm_num : (2:ℂ)≠0) heq

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma rationalComplex_conjugate (r:SL(2,ℤ)) (M:levelThree) :
    complexMatrix (levelThreeConjugate (rationalEmbedding r) M)*rationalComplex r=
      rationalComplex r*complexMatrix M := by
  rw [←integralComplexMatrix_levelThree,←integralComplexMatrix_levelThree]
  change integralComplexMatrix ((rationalEmbedding r)*(M:SL(2,Eis))*(rationalEmbedding r)⁻¹)*
    integralComplexMatrix (rationalEmbedding r)=
      integralComplexMatrix (rationalEmbedding r)*integralComplexMatrix (M:SL(2,Eis))
  rw [←map_mul,inv_mul_cancel_right,map_mul]

lemma hyperbolicEisenstein_rational_automorphy (r:SL(2,ℤ)) (M:levelThree)
    (s:ℂ) (hs:2<s.re) (w:HyperbolicSpace) :
    hyperbolicEisenstein s (rationalComplex r • (complexMatrix M • w))=
      complexCharacter M*hyperbolicEisenstein s (rationalComplex r • w) := by
  rw [←mul_smul,←rationalComplex_conjugate,mul_smul,hyperbolicEisenstein_automorphy _ _ hs,
    complexCharacter_conjugate_rational]

lemma hyperbolicEisenstein_rational_periodic (r:SL(2,ℤ)) (a:Eis)
    (s:ℂ) (hs:2<s.re) (z:ℂ) (v:ℝ) (hv:0<v) :
    hyperbolicEisenstein s (rationalComplex r • upperPoint (z+3*eisEmbedding a) v hv)=
      hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv) := by
  have he : upperPoint (z+3*eisEmbedding a) v hv=complexMatrix (upperTranslation a) • upperPoint z v hv :=
    congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace)) (upperTranslation_section a z v hv).symm
  rw [he,hyperbolicEisenstein_rational_automorphy r _ s hs,complexCharacter_upperTranslation,one_mul]

lemma rationalComplex_unipotent_coe (t : ℤ) :
    (rationalComplex (rationalUnipotent t) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![1,(t : ℂ);0,1] := by
  apply Matrix.ext
  intro i j
  change eisEmbedding ((Int.castRingHom Eis) ((!![1,t;0,1] : Matrix (Fin 2) (Fin 2) ℤ) i j)) = _
  fin_cases i <;> fin_cases j <;> simp

lemma rationalUnipotent_section (t:ℤ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex (rationalUnipotent t)*upperSection z v hv=upperSection (z+t) v hv := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, rationalComplex_unipotent_coe]
  change (!![1,(t : ℂ);0,1] *
    !![(Real.sqrt v : ℂ),z/(Real.sqrt v : ℂ);0,(Real.sqrt v : ℂ)⁻¹] :
      Matrix (Fin 2) (Fin 2) ℂ) =
    !![(Real.sqrt v : ℂ),(z+t)/(Real.sqrt v : ℂ);0,(Real.sqrt v : ℂ)⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  all_goals ring

lemma rationalComplex_T_pow_upper (n:ℕ) (z:ℂ) (v:ℝ) (hv:0<v) :
    rationalComplex (ModularGroup.T^n) • upperPoint z v hv=upperPoint (z+n) v hv := by
  change ((rationalComplex (ModularGroup.T^n)*upperSection z v hv):HyperbolicSpace)=
    (upperSection (z+(n:ℂ)) v hv:HyperbolicSpace)
  have he:=congrArg (fun g : SL(2,ℂ)=>(g:HyperbolicSpace)) (rationalUnipotent_section (n:ℤ) z v hv)
  simpa only [rationalUnipotent_nat,Int.cast_natCast] using he

theorem rational_cusp_average_right_T (r:SL(2,ℤ)) (n:ℕ) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)∂hyperbolicVolume)=
    ∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex r • w)∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s (rationalComplex r • w)
  have hf : Continuous f := (hyperbolicEisenstein_continuous s hs).comp (continuous_hyperbolic_action _)
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).comp (continuous_hyperbolic_action _)
  change (∫w in cuspPeriodStrip 5 6,f w∂hyperbolicVolume)=∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates f hf.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable f hf),
    cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg)]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  dsimp only
  apply congrArg (fun q:ℂ=>q/(v:ℂ)^3)
  simp_rw [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper]
  have hh:=period_integral_translation
    (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0))
    (fun a z=>hyperbolicEisenstein_rational_periodic r a s hs z v hv0) (n:ℂ)
  simpa only [add_comm] using hh

lemma cuspFourierPhase_zero (w:HyperbolicSpace) : cuspFourierPhase (0:Eis) w=1 := by
  simp [cuspFourierPhase,cuspFrequency]

lemma kernelCuspFourier_zero (F:KernelQuotientL2) :
    kernelCuspFourier (0:Eis) F=kernelCuspStripAverage F := by
  rw [kernelCuspFourier_integral,kernelCuspStripAverage_hyperbolic]
  simp only [cuspFourierPhase_zero,mul_one]

theorem translatedCuspFourier_residue_eq_of_initial (M N:levelTwo)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix M • w)∂hyperbolicVolume)=
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix N • w)∂hyperbolicVolume) :
    translatedCuspFourier 0 M cubicEisensteinResidue=
      translatedCuspFourier 0 N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedCuspFamily 0 M 2 3 (by norm_num) (by norm_num)
  let g : ℂ→ℂ := translatedCuspFamily 0 N 2 3 (by norm_num) (by norm_num)
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal 0 M 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal 0 N 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedCuspFamily_initial 0 M 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      translatedCuspFamily_initial 0 N 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2]
    simp only [cuspFourierPhase_zero,mul_one]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedCuspFamily_residue_limit 0 M 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  have hr := (translatedCuspFamily_residue_limit 0 N 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  exact congrArg (fun z:ℂ=>((4/3:ℂ)+(t:ℂ)*Complex.I-4/3)*z) hv

end

open CubicKubota

lemma sourceComplexMatrix_rationalLift (r:SL(2,ℤ)) :
    sourceComplexMatrix (rationalLift r)=rationalComplex r := rfl

lemma translatedCuspFourier_one_residue :
    translatedCuspFourier 0 1 cubicEisensteinResidue=cuspConstantAverageResidue := by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one,
    kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average]

lemma translatedCuspFourier_bruhat_residue (i:RationalBruhatIndex) :
    translatedCuspFourier 0 (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue=
      cuspConstantAverageResidue := by
  rcases i with ⟨e,a|⟨a,b⟩⟩
  · calc
      _=translatedCuspFourier 0 1 cubicEisensteinResidue := by
        apply translatedCuspFourier_residue_eq_of_initial
        intro s hs hi
        simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
        simp only [map_one,one_smul]
      _=cuspConstantAverageResidue := translatedCuspFourier_one_residue
  · calc
      _=translatedCuspFourier 0 oppositeSource cubicEisensteinResidue := by
        apply translatedCuspFourier_residue_eq_of_initial
        intro s hs hi
        simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
        change (∫w in cuspPeriodStrip 5 6,
          hyperbolicEisenstein s (rationalComplex ModularGroup.S •
            (rationalComplex (ModularGroup.T^b.val) • w))∂hyperbolicVolume)=
          ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)∂hyperbolicVolume
        simpa only [map_mul,mul_smul] using
          rational_cusp_average_right_T ModularGroup.S b.val s (by linarith)
      _=cuspConstantAverageResidue := translatedCuspFourier_opposite_zero_residue

theorem kernelSourceProjection_residue_cusp_average :
    kernelCuspStripAverage (kernelSourceProjection cubicEisensteinResidue)=
      cuspConstantAverageResidue := by
  rw [←kernelCuspFourier_zero,kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  have he (i:RationalBruhatIndex) :
      kernelCuspFourier 0 (kernelSourcePullback (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=
        cuspConstantAverageResidue := translatedCuspFourier_bruhat_residue i
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_sum,
    Fintype.card_fin,smul_eq_mul,nsmul_eq_mul]
  norm_num
  ring

theorem kernelSourceProjection_cubicEisensteinResidue_ne_zero :
    kernelSourceProjection cubicEisensteinResidue≠0 := by
  intro hz
  have hh:=kernelSourceProjection_residue_cusp_average
  rw [hz,map_zero] at hh
  exact cuspConstantAverageResidue_ne_zero hh.symm

theorem cubicSourceResidualFunction_cusp_average :
    (∫w in cuspPeriodStrip 5 6,cubicSourceResidualFunction w∂hyperbolicVolume)=
      cuspConstantAverageResidue := by
  rw [←kernelSourceProjection_residue_cusp_average,kernelCuspStripAverage_hyperbolic]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae cubicSourceResidualFunction_represents_projection] with w hw
  exact hw.symm

theorem cubicSourceResidualFunction_ne_zero : cubicSourceResidualFunction≠0 := by
  intro hz
  have he:=cubicSourceResidualFunction_cusp_average
  rw [hz] at he
  simp only [Pi.zero_apply,integral_zero] at he
  exact cuspConstantAverageResidue_ne_zero he.symm

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

section

lemma complex_gaussian_power_integrable (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0<r) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2))
      (Set.Ioi 0) volume := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have hbase : MellinConvergent (fun t : ℝ => Complex.exp (-(t:ℂ))) (s/2) := by
    simpa only [MellinConvergent,smul_eq_mul,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm]
      using Complex.GammaIntegral_convergent hs2
  have hlinear := (MellinConvergent.comp_mul_left
    (f := fun t : ℝ => Complex.exp (-(t:ℂ))) (s := s/2) hr).mpr hbase
  have hgaussian := (MellinConvergent.comp_rpow
    (f := fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) (s := s) (a := 2)
      (by norm_num)).mpr hlinear
  simpa only [MellinConvergent,smul_eq_mul,Real.rpow_two,
    Complex.ofReal_mul,Complex.ofReal_pow,neg_mul] using hgaussian

lemma complex_gaussian_power_integral (s : ℂ) (r : ℝ)
    (hs : 0<s.re) (hr : 0<r) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*Complex.exp (-(r:ℂ)*(x:ℂ)^2)) =
      (1/2:ℂ)*((1/(r:ℂ))^(s/2)*Complex.Gamma (s/2)) := by
  have hs2 : 0<(s/(2:ℂ)).re := by simpa using half_pos hs
  have he := mellin_comp_rpow (fun t : ℝ => Complex.exp (-((r*t:ℝ):ℂ))) s 2
  simp only [mellin,smul_eq_mul,Real.rpow_two,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.real_smul] at he
  norm_num only [Complex.ofReal_ofNat] at he
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs2 hr] at he
  simpa [neg_mul] using he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def cubicMellinMixture (s : ℂ) (t x : ℝ) : ℂ :=
  (t:ℂ)^(-(2:ℂ)/3)*Complex.exp (-(t:ℂ))*
    ((x:ℂ)^((s-1/3)-1)*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2))

lemma cubicMellinMixture_slice_integrable (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    IntegrableOn (cubicMellinMixture s t) (Set.Ioi 0) volume := by
  apply (complex_gaussian_power_integrable (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)).const_mul

lemma cubicMellinMixture_integral_x (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
  simp only [cubicMellinMixture,integral_const_mul]
  rw [complex_gaussian_power_integral (s-1/3) (1/(4*t))
    (by norm_num; linarith) (by positivity)]
  have hb : (1/(((1/(4*t):ℝ):ℂ)))=(4:ℂ)*(t:ℂ) := by
    push_cast
    field_simp
  have hm : ((4:ℂ)*(t:ℂ))^((s-1/3)/2)=
      (4:ℂ)^((s-1/3)/2)*(t:ℂ)^((s-1/3)/2) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : 0≤(4:ℝ)) ht.le ((s-1/3)/2)
  rw [hb,hm]
  have hp : (t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2)=
      (t:ℂ)^((s+1/3)/2-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 1
    ring
  calc
    _ = ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        (((t:ℂ)^(-(2:ℂ)/3)*(t:ℂ)^((s-1/3)/2))*Complex.exp (-(t:ℂ))) := by ring
    _ = _ := by rw [hp]

lemma cubicMellinMixture_norm (s : ℂ) (t x : ℝ) (ht : 0<t) (hx : 0<x) :
    ‖cubicMellinMixture s t x‖ =
      (t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
  have he : -((1/(4*t):ℝ):ℂ)*(x:ℂ)^2=(-(1/(4*t))*x^2:ℝ) := by
    push_cast
    rfl
  simp only [cubicMellinMixture,norm_mul,he,
    Complex.norm_cpow_eq_rpow_re_of_pos ht,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.norm_exp,Complex.ofReal_re,Complex.neg_re]
  norm_num

lemma real_gaussian_power_integral (sigma r : ℝ) (hs : 0<sigma) (hr : 0<r) :
    (∫x : ℝ in Set.Ioi 0,x^(sigma-1)*Real.exp (-r*x^2)) =
      r^(-sigma/2)*(1/2)*Real.Gamma (sigma/2) := by
  simpa only [Real.rpow_two,sub_add_cancel] using
    (_root_.integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=sigma-1) (b:=r)
      (by norm_num) (by linarith) hr)

lemma cubicMellinMixture_integral_norm (s : ℂ) (hs : 1/3<s.re)
    (t : ℝ) (ht : 0<t) :
    (∫x : ℝ in Set.Ioi 0,‖cubicMellinMixture s t x‖) =
      ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
        (t^((s.re+1/3)/2-1)*Real.exp (-t)) := by
  calc
    _ = ∫x : ℝ in Set.Ioi 0,(t^(-(2:ℝ)/3)*Real.exp (-t))*
        (x^((s.re-1/3)-1)*Real.exp (-(1/(4*t))*x^2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact cubicMellinMixture_norm s t x ht hx
    _ = _ := by
      rw [integral_const_mul,real_gaussian_power_integral (s.re-1/3) (1/(4*t))
        (by linarith) (by positivity)]
      have hpow : (1/(4*t):ℝ)^(-(s.re-1/3)/2)=(4:ℝ)^((s.re-1/3)/2)*t^((s.re-1/3)/2) := by
        rw [show -(s.re-1/3)/2=-((s.re-1/3)/2) by ring,
          Real.rpow_neg_eq_inv_rpow,one_div,inv_inv,
          Real.mul_rpow (by norm_num : 0≤(4:ℝ)) ht.le]
      rw [hpow]
      have hp : t^(-(2:ℝ)/3)*t^((s.re-1/3)/2)=t^((s.re+1/3)/2-1) := by
        rw [←Real.rpow_add ht]
        congr 1
        ring
      calc
        _ = ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))*
            ((t^(-(2:ℝ)/3)*t^((s.re-1/3)/2))*Real.exp (-t)) := by ring
        _ = _ := by rw [hp]

lemma cubicMellinMixture_integrable (s : ℂ) (hs : 1/3<s.re) :
    Integrable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => cubicMellinMixture s p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    unfold cubicMellinMixture
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact cubicMellinMixture_slice_integrable s hs t ht
  · have hg := (Real.GammaIntegral_convergent
        (show 0<(s.re+1/3)/2 by linarith)).const_mul
        ((1/2:ℝ)*(4:ℝ)^((s.re-1/3)/2)*Real.Gamma ((s.re-1/3)/2))
    apply hg.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [cubicMellinMixture_integral_norm s hs t ht]
    ring

lemma cubicMellinMixture_integral_t (s : ℂ) (x : ℝ) :
    (∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      (x:ℂ)^((s-1/3)-1)*schlafliIntegral (1/3) x := by
  rw [schlafliIntegral,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have he : Complex.exp (-(t:ℂ))*Complex.exp (-((1/(4*t):ℝ):ℂ)*(x:ℂ)^2)=
      Complex.exp (-(t:ℂ)-(x:ℂ)^2/(4*t)) := by
    rw [←Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  rw [show (1/3:ℂ)-1=-(2:ℂ)/3 by ring]
  unfold cubicMellinMixture
  linear_combination (t:ℂ)^(-(2:ℂ)/3)*(x:ℂ)^((s-1/3)-1)*he

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma schlafliBesselK_cubic_mellin_mixture (s : ℂ) (x : ℝ) (hx : 0<x) :
    (x:ℂ)^(s-1)*schlafliBesselK (1/3) x =
      ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*(∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
  rw [schlafliBesselK,cubicMellinMixture_integral_t]
  have hdiv : (x/2:ℂ)^(-(1/3:ℂ))=(x:ℂ)^(-(1/3:ℂ))/(2:ℂ)^(-(1/3:ℂ)) := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.div_cpow_ofReal_nonneg hx.le (by norm_num : 0≤(2:ℝ)) (-(1/3:ℂ))
  rw [hdiv,Complex.cpow_neg (2:ℂ) (1/3),div_inv_eq_mul]
  have hp : (x:ℂ)^(s-1)*(x:ℂ)^(-(1/3:ℂ))=(x:ℂ)^((s-1/3)-1) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    congr 1
    ring
  linear_combination (1/2:ℂ)*(2:ℂ)^(1/3:ℂ)*schlafliIntegral (1/3) x*hp

lemma schlafliBesselK_cubic_mellin_integrable (s : ℂ) (hs : 1/3<s.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(s-1)*schlafliBesselK (1/3) x)
      (Set.Ioi 0) volume := by
  apply ((cubicMellinMixture_integrable s hs).integral_prod_right.const_mul
    ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (schlafliBesselK_cubic_mellin_mixture s x hx).symm

lemma cubicMellinMixture_double_integral (s : ℂ) (hs : 1/3<s.re) :
    (∫t : ℝ in Set.Ioi 0,∫x : ℝ in Set.Ioi 0,cubicMellinMixture s t x) =
      ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
        Complex.Gamma ((s+1/3)/2) := by
  have hB : 0<((s+1/3)/2).re := by norm_num; linarith
  calc
    _ = ∫t : ℝ in Set.Ioi 0,
        ((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          ((t:ℂ)^((s+1/3)/2-1)*Complex.exp (-(t:ℂ))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact cubicMellinMixture_integral_x s hs t ht
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [Complex.GammaIntegral,Complex.ofReal_exp,Complex.ofReal_neg,mul_comm] using
        (Complex.Gamma_eq_integral hB).symm

theorem schlafliBesselK_cubic_mellin (s : ℂ) (hs : 1/3<s.re) :
    (∫x : ℝ in Set.Ioi 0,(x:ℂ)^(s-1)*schlafliBesselK (1/3) x) =
      (2:ℂ)^(s-2)*Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by
  have hmix : Integrable (Function.uncurry (cubicMellinMixture s))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
    convert cubicMellinMixture_integrable s hs using 1
    funext p
    rcases p with ⟨t,x⟩
    rfl
  have hswap := (integral_integral_swap hmix).symm
  have h4 : (4:ℂ)^((s-1/3)/2)=(2:ℂ)^(2*((s-1/3)/2)) := by
    have hh := (Complex.natCast_cpow_natCast_mul 2 2 ((s-1/3)/2)).symm
    norm_num at hh
    exact hh
  have hprod : (2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)=(2:ℂ)^s := by
    rw [h4,←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  have hscale : (1/4:ℂ)*(2:ℂ)^s=(2:ℂ)^(s-2) := by
    rw [Complex.cpow_sub _ _ (by norm_num : (2:ℂ)≠0)]
    norm_num
    ring
  calc
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (∫x : ℝ in Set.Ioi 0,∫t : ℝ in Set.Ioi 0,cubicMellinMixture s t x) := by
      rw [←integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact schlafliBesselK_cubic_mellin_mixture s x hx
    _ = ((1/2:ℂ)*(2:ℂ)^(1/3:ℂ))*
        (((1/2:ℂ)*(4:ℂ)^((s-1/3)/2)*Complex.Gamma ((s-1/3)/2))*
          Complex.Gamma ((s+1/3)/2)) := by
      rw [hswap,cubicMellinMixture_double_integral s hs]
    _ = ((1/4:ℂ)*((2:ℂ)^(1/3:ℂ)*(4:ℂ)^((s-1/3)/2)))*
        Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2) := by ring
    _ = _ := by rw [hprod,hscale]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0274

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform
Source SHA256: 3cc7ba1b5e4ccadb9b2e5099c9e850d910d1ee5284096813019fe64753af1dd7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0275


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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

lemma schlafliBesselK_cubic_scaled_mellin_integrable (s : ℂ) (c : ℝ)
    (hs : 1/3<s.re) (hc : 0<c) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(s-1)*schlafliBesselK (1/3) (c*v))
      (Set.Ioi 0) volume := by
  have hb : MellinConvergent (fun v => schlafliBesselK (1/3) v) s := by
    simpa only [MellinConvergent,smul_eq_mul] using schlafliBesselK_cubic_mellin_integrable s hs
  have hh := (MellinConvergent.comp_mul_left
    (f := fun v => schlafliBesselK (1/3) v) (s := s) hc).mpr hb
  simpa only [MellinConvergent,smul_eq_mul] using hh

lemma schlafliBesselK_cubic_scaled_mellin (s : ℂ) (c : ℝ)
    (hs : 1/3<s.re) (hc : 0<c) :
    (∫v : ℝ in Set.Ioi 0,(v:ℂ)^(s-1)*schlafliBesselK (1/3) (c*v)) =
      (c:ℂ)^(-s)*((2:ℂ)^(s-2)*Complex.Gamma ((s-1/3)/2)*Complex.Gamma ((s+1/3)/2)) := by
  have hh := mellin_comp_mul_left (fun v => schlafliBesselK (1/3) v) s hc
  simp only [mellin,smul_eq_mul] at hh
  rw [schlafliBesselK_cubic_mellin s hs] at hh
  exact hh

lemma source_cubic_bessel_mellin_integrable (s freq : ℂ)
    (hs : -(1/3)<s.re) (hfreq : freq≠0) :
    IntegrableOn (fun v : ℝ => (v:ℂ)^(2*s)*
      schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v)) (Set.Ioi 0) volume := by
  have hc : 0<4*Real.pi*‖freq‖ := by positivity
  have ht : 1/3<(2*s+1).re := by norm_num; linarith
  simpa only [show (2*s+1:ℂ)-1=2*s by ring] using
    schlafliBesselK_cubic_scaled_mellin_integrable (2*s+1) (4*Real.pi*‖freq‖) ht hc

theorem source_cubic_bessel_mellin (s freq : ℂ)
    (hs : -(1/3)<s.re) (hfreq : freq≠0) :
    (∫v : ℝ in Set.Ioi 0,(v:ℂ)^(2*s)*schlafliBesselK (1/3) (4*Real.pi*‖freq‖*v)) =
      ((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
        ((4*Real.pi*‖freq‖:ℝ):ℂ)^(2*s+1) := by
  have hc : 0<4*Real.pi*‖freq‖ := by positivity
  have ht : 1/3<(2*s+1).re := by norm_num; linarith
  have hh := schlafliBesselK_cubic_scaled_mellin (2*s+1) (4*Real.pi*‖freq‖) ht hc
  rw [show (2*s+1:ℂ)-1=2*s by ring,
    show (2*s+1:ℂ)-2=2*s-1 by ring,
    show ((2*s+1:ℂ)-1/3)/2=s+1/3 by ring,
    show ((2*s+1:ℂ)+1/3)/2=s+2/3 by ring,Complex.cpow_neg] at hh
  rw [hh]
  ring

end CubicEisenstein

open scoped BigOperators Classical

namespace ShortDraftCRT

section
variable {R : Type*} [CommRing R]

theorem exists_fixed_completion (M c r a d0 : R)
    (hfixed : c∣a*d0-1) (hr : IsCoprime r (M*c)) (ha : IsCoprime a r) :
    ∃b d : R,a*d-b*(c*r)=1 ∧ M*c∣d-d0 := by
  have hcr : IsCoprime c r := hr.of_mul_right_right.symm
  obtain ⟨u,v,huv⟩ := hr
  obtain ⟨x,y,hxy⟩ := ha
  let d : R := d0*u*r+x*v*(M*c)
  have hd : M*c∣d-d0 := by
    refine ⟨v*(x-d0),?_⟩
    dsimp [d]
    linear_combination d0*huv
  have hdr : r∣d-x := by
    refine ⟨u*(d0-x),?_⟩
    dsimp [d]
    linear_combination x*huv
  have hcd : c∣a*d-1 := by
    have hdiff : c∣a*(d-d0) := dvd_mul_of_dvd_right
      ((dvd_mul_left c M).trans hd) a
    convert dvd_add hdiff hfixed using 1 ; ring
  have hrd : r∣a*d-1 := by
    have hx : r∣a*x-1 := by
      refine ⟨-y,?_⟩
      linear_combination hxy
    have hdiff : r∣a*(d-x) := dvd_mul_of_dvd_right hdr a
    convert dvd_add hdiff hx using 1 ; ring
  obtain ⟨b,hb⟩ := hcr.mul_dvd hcd hrd
  refine ⟨b,d,?_,hd⟩
  linear_combination hb

variable [IsDomain R]

theorem fixed_completion_congr (M c r r0 a a0 b b0 d d0 : R)
    (hc : c≠0) (hr : IsCoprime M r)
    (hdet : a*d-b*(c*r)=1) (hdet0 : a0*d0-b0*(c*r0)=1)
    (ha : M*c∣a-a0) (hd : M*c∣d-d0) (hrr : M∣r-r0) : M∣b-b0 := by
  have hprod : M*c∣a*d-a0*d0 := by
    have h1 := dvd_mul_of_dvd_left ha d
    have h2 := dvd_mul_of_dvd_right hd a0
    convert dvd_add h1 h2 using 1 ; ring
  have hcancel : M*c∣c*(b*r-b0*r0) := by
    convert hprod using 1
    linear_combination -hdet+hdet0
  have hbr : M∣b*r-b0*r0 := by
    rw [mul_comm M c] at hcancel
    exact (mul_dvd_mul_iff_left hc).mp hcancel
  have hsub : M∣(b-b0)*r := by
    have hsmall := dvd_mul_of_dvd_right hrr b0
    convert dvd_sub hbr hsmall using 1 ; ring
  exact hr.dvd_of_dvd_mul_right hsub

end

open scoped BigOperators Classical Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
lemma quotient_eq_of_dvd_sub (M x y : R) (h : M ∣ x-y) :
    Ideal.Quotient.mk (Ideal.span {M}) x = Ideal.Quotient.mk (Ideal.span {M}) y := by
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr h)

theorem fixed_completion_matrix_congr (M c r r0 a a0 b b0 d d0 : R)
    (hc : c≠0) (hr : IsCoprime M r)
    (hdet : a*d-b*(c*r)=1) (hdet0 : a0*d0-b0*(c*r0)=1)
    (ha : M*c∣a-a0) (hd : M*c∣d-d0) (hrr : M∣r-r0) :
    (!![a,b;c*r,d] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})) =
      (!![a0,b0;c*r0,d0] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})) := by
  have hqa := quotient_eq_of_dvd_sub M a a0 ((dvd_mul_right M c).trans ha)
  have hqd := quotient_eq_of_dvd_sub M d d0 ((dvd_mul_right M c).trans hd)
  have hqb := quotient_eq_of_dvd_sub M b b0
    (fixed_completion_congr M c r r0 a a0 b b0 d d0 hc hr hdet hdet0 ha hd hrr)
  have hqc : Ideal.Quotient.mk (Ideal.span {M}) (c*r) =
      Ideal.Quotient.mk (Ideal.span {M}) (c*r0) := by
    apply quotient_eq_of_dvd_sub
    simpa only [mul_sub] using dvd_mul_of_dvd_right hrr c
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply,] <;>
    assumption

theorem exists_fixed_matrix_completion (M c a0 r0 d0 b0 : R)
    (hc : c≠0) (hdet0 : a0*d0-b0*(c*r0)=1) :
    ∀a r : R, M*c∣a-a0 → M∣r-r0 → IsCoprime r (M*c) → IsCoprime a r →
      ∃b d : R, a*d-b*(c*r)=1 ∧ M*c∣d-d0 ∧
        (!![a,b;c*r,d] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M})) =
          (!![a0,b0;c*r0,d0] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M})) := by
  intro a r ha hrr hr har
  have hbase : c ∣ a0*d0-1 := by
    refine ⟨b0*r0,?_⟩
    linear_combination hdet0
  have hfixed : c ∣ a*d0-1 := by
    have hdiff := dvd_mul_of_dvd_left ((dvd_mul_left c M).trans ha) d0
    convert dvd_add hdiff hbase using 1 ; ring
  obtain ⟨b,d,hdet,hd⟩ := exists_fixed_completion M c r a d0 hfixed hr har
  exact ⟨b,d,hdet,hd,fixed_completion_matrix_congr M c r r0 a a0 b b0 d d0 hc
    hr.of_mul_right_left.symm hdet hdet0 ha hd hrr⟩

end ShortDraftCRT

open scoped BigOperators Classical
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

def conductorReduction (a b:Eis):
    (Eis⧸Ideal.span {a*b})→+*(Eis⧸Ideal.span {a}):=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right a b))

lemma conductorReduction_surjective (a b:Eis):Function.Surjective (conductorReduction a b):=
  Ideal.Quotient.factor_surjective _

def quotientTrace (c:Eis) (hc:c≠0):AddChar (Eis⧸Ideal.span {c}) ℂ:=
  eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc

lemma quotientTrace_mk (c:Eis) (hc:c≠0) (x:Eis):
    quotientTrace c hc (Ideal.Quotient.mk _ x)=residueAdditive (3*x) c 1:=by
  simp only [quotientTrace,eisTraceModChar,IdealGaussCRT.traceModChar_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_one,map_ofNat]
  congr 1
  ring

def conductorFourier (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h:Eis):ℂ:=
  ∑'x:Eis⧸Ideal.span {a*b},F (conductorReduction a b x)*
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ h*x)

lemma conductorFourier_shift (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h t:Eis):
    conductorFourier a b ha hb F h=
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (h*a*t))*
        conductorFourier a b ha hb F h:=by
  let q:Eis⧸Ideal.span {a*b}:=Ideal.Quotient.mk _ (a*t)
  have hq:conductorReduction a b q=0:=by
    change Ideal.Quotient.mk (Ideal.span {a}) (a*t)=0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨t,rfl⟩)
  unfold conductorFourier
  conv_lhs => rw [←(Equiv.addRight q).tsum_eq]
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  change F (conductorReduction a b (x+q))*
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ h*(x+q))=_
  simp only [map_add,hq,add_zero,mul_add,AddChar.map_add_eq_mul]
  have he:Ideal.Quotient.mk (Ideal.span {a*b}) h*q=Ideal.Quotient.mk _ (h*a*t):=by
    dsimp [q]
    rw [←map_mul]
    congr 1
    ring
  rw [he]
  ring

theorem conductorFourier_support (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (h:Eis)
    (hF:conductorFourier a b ha hb F h≠0):b∣h:=by
  have hphase (t:Eis):
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (h*a*t))=1:=by
    apply mul_right_cancel₀ hF
    rw [one_mul,←conductorFourier_shift]
  have hz:Ideal.Quotient.mk (Ideal.span {a*b}) (h*a)=0:=by
    by_contra hn
    apply GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (a*b) (mul_ne_zero ha hb) hn
    ext x
    obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective x
    simpa only [AddChar.mulShift_apply,←map_mul,AddChar.one_apply,quotientTrace] using hphase t
  have hd:a*b∣h*a:=Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hd':a*b∣a*h:=by simpa only [mul_comm h a] using hd
  exact (mul_dvd_mul_iff_left ha).mp hd'

lemma conductorReduction_kernel_card (a b:Eis) (ha:a≠0) (_hb:b≠0):
    Nat.card (conductorReduction a b).toAddMonoidHom.ker=Ideal.absNorm (Ideal.span {b}):=by
  have hc:=card_ring_eq_card_mul_kernel (conductorReduction a b)
    (conductorReduction_surjective a b)
  change Ideal.absNorm (Ideal.span {a*b})=
    Ideal.absNorm (Ideal.span {a})*Nat.card (conductorReduction a b).toAddMonoidHom.ker at hc
  conv_lhs at hc => rw [←Ideal.span_singleton_mul_span_singleton,map_mul]
  have hpos:0<Ideal.absNorm (Ideal.span {a}):=by
    apply Nat.pos_iff_ne_zero.mpr
    intro hz
    exact ha (Ideal.span_singleton_eq_bot.mp (Ideal.absNorm_eq_zero_iff.mp hz))
  exact (Nat.eq_of_mul_eq_mul_left hpos hc).symm

private theorem finite_tsum_conductor_pullback {R S:Type*} [AddGroup R] [AddGroup S]
    [Finite R] [Finite S] (f:R→+S) (hf:Function.Surjective f) (F:S→ℂ):
    (∑'x:R,F (f x))=(Nat.card f.ker:ℂ)*∑'y:S,F y:=by
  let:Fintype R:=Fintype.ofFinite _
  let:Fintype S:=Fintype.ofFinite _
  let:Fintype f.ker:=Fintype.ofFinite _
  rw [tsum_fintype,tsum_fintype,←Fintype.sum_fiberwise' f F]
  have hc (y:S):Fintype.card {x:R//f x=y}=Fintype.card f.ker:=
    Fintype.card_congr (AddMonoidHom.fiberEquivKerOfSurjective hf y)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc,Nat.card_eq_fintype_card]
  rw [Finset.mul_sum]

lemma quotientTrace_conductor_scale (a b k:Eis) (ha:a≠0) (hb:b≠0)
    (x:Eis⧸Ideal.span {a*b}):
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (b*k)*x)=
      quotientTrace a ha (Ideal.Quotient.mk _ k*conductorReduction a b x):=by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  change quotientTrace (a*b) (mul_ne_zero ha hb)
    (Ideal.Quotient.mk _ (b*k)*Ideal.Quotient.mk _ d)=
    quotientTrace a ha (Ideal.Quotient.mk _ k*Ideal.Quotient.mk _ d)
  rw [←map_mul,←map_mul,quotientTrace_mk,quotientTrace_mk]
  simp only [residueAdditive,cuspFrequency,map_mul,map_one,map_ofNat]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  field_simp

theorem conductorFourier_lift (a b:Eis) (ha:a≠0) (hb:b≠0)
    (F:(Eis⧸Ideal.span {a})→ℂ) (k:Eis):
    conductorFourier a b ha hb F (b*k)=
      (Ideal.absNorm (Ideal.span {b}):ℂ)*
        ∑'x:Eis⧸Ideal.span {a},F x*quotientTrace a ha (Ideal.Quotient.mk _ k*x):=by
  let:Finite (Eis⧸Ideal.span {a*b}):=finite_quotient_span (mul_ne_zero ha hb)
  let:Finite (Eis⧸Ideal.span {a}):=finite_quotient_span ha
  unfold conductorFourier
  calc
    _=∑'x:Eis⧸Ideal.span {a*b},F (conductorReduction a b x)*
        quotientTrace a ha (Ideal.Quotient.mk _ k*conductorReduction a b x):=by
      apply tsum_congr
      intro x
      rw [quotientTrace_conductor_scale a b k ha hb]
    _=_:=by
      have he:=finite_tsum_conductor_pullback (conductorReduction a b).toAddMonoidHom
        (conductorReduction_surjective a b)
        (fun y=>F y*quotientTrace a ha (Ideal.Quotient.mk _ k*y))
      rw [conductorReduction_kernel_card a b ha hb] at he
      exact he

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicSymbol_pow_denominator (x p:Eis) (n:ℕ):
    symbol x (p^n)=(symbol x p)^n:=by
  induction n with
  | zero=>simp
  | succ n ih=>rw [pow_succ,symbol_mul_denominator,ih,pow_succ]

def primeCubicMulChar (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    MulChar (Eis⧸Ideal.span {p}) ℂ:=by
  letI:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  refine {toFun:=fun x=>eisEmbedding (symbol (GaussianShiftedPartition.representative p x) p)
          map_one':=?_,map_mul':=?_,map_nonunit':=?_}
  · have hd:p∣GaussianShiftedPartition.representative p 1-1:=by
      simpa only [map_one] using gaussRep_mk_congr p 1
    rw [symbol_congr hd,symbol_one_numerator p hprimary,map_one]
  · intro x y
    have hd:p∣GaussianShiftedPartition.representative p (x*y)-
        GaussianShiftedPartition.representative p x*GaussianShiftedPartition.representative p y:=by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      simp only [map_mul,GaussianShiftedPartition.representative_spec]
    rw [symbol_congr hd,symbol_mul_numerator _ _ p hprimary,map_mul]
  · intro x hx
    rw [symbol_prime p hp hprimary,primeValue_eq _ hg,
      GaussianShiftedPartition.representative_spec,MulChar.map_nonunit _ hx,map_zero]

lemma primeCubicMulChar_mk (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (x:Eis):
    primeCubicMulChar p hp hprimary (Ideal.Quotient.mk _ x)=eisEmbedding (symbol x p):=by
  change eisEmbedding (symbol (GaussianShiftedPartition.representative p
    (Ideal.Quotient.mk _ x)) p)=_
  rw [symbol_congr (gaussRep_mk_congr p x)]

lemma quotientTrace_mk_product (c:Eis) (hc:c≠0) (h d:Eis):
    quotientTrace c hc (Ideal.Quotient.mk _ h*Ideal.Quotient.mk _ d)=
      residueAdditive (3*h) c d:=by
  rw [←map_mul,quotientTrace_mk]
  unfold residueAdditive cuspFrequency
  simp only [map_mul,map_one,map_ofNat]
  congr 1
  ring

lemma conductorReduction_prime_power_unit (p:Eis) (n:ℕ)
    (x:Eis⧸Ideal.span {p*p^n}):
    IsUnit (conductorReduction p (p^n) x)↔IsUnit x:=by
  obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
  change IsUnit (Ideal.Quotient.mk (Ideal.span {p}) d)↔
    IsUnit (Ideal.Quotient.mk (Ideal.span {p*p^n}) d)
  rw [isUnit_quotient_span_iff,isUnit_quotient_span_iff,←pow_succ',
    IsCoprime.pow_left_iff (Nat.succ_pos n)]

theorem cubicUnitGaussSum_prime_power_fourier (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum h (p^(n+1))=
      conductorFourier p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero)
        (fun x=>(primeCubicMulChar p hp hprimary^(n+1)) x) h:=by
  let χ:=primeCubicMulChar p hp hprimary
  let f:(Eis⧸Ideal.span {p*p^n})→ℂ:=fun x=>
    (χ^(n+1)) (conductorReduction p (p^n) x)*
      quotientTrace (p*p^n) (mul_ne_zero hp.ne_zero (pow_ne_zero _ hp.ne_zero))
        (Ideal.Quotient.mk _ h*x)
  have hsup:Function.support f⊆{x|IsUnit x}:=by
    intro x hx
    by_contra hn
    have hn':¬IsUnit (conductorReduction p (p^n) x):=
      fun hh=>hn ((conductorReduction_prime_power_unit p n x).mp hh)
    exact hx (by dsimp [f];rw [MulChar.map_nonunit _ hn',zero_mul])
  rw [pow_succ']
  change cubicUnitGaussSum h (p*p^n)=∑'x,f x
  rw [←tsum_subtype_eq_of_support_subset hsup]
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro x
  let d:=GaussianShiftedPartition.representative (p*p^n) x.val
  have hd:Ideal.Quotient.mk (Ideal.span {p*p^n}) d=x.val:=
    GaussianShiftedPartition.representative_spec _ _
  change eisEmbedding (symbol d (p*p^n))*residueAdditive (3*h) (p*p^n) d=f x.val
  rw [←hd]
  dsimp [f]
  change _=(χ^(n+1)) (Ideal.Quotient.mk _ d)*_
  rw [MulChar.pow_apply' _ (Nat.succ_ne_zero n),primeCubicMulChar_mk,
    quotientTrace_mk_product,←pow_succ',cubicSymbol_pow_denominator,map_pow]

theorem cubicUnitGaussSum_prime_power_support (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis)
    (hne:cubicUnitGaussSum h (p^(n+1))≠0):p^n∣h:=by
  rw [cubicUnitGaussSum_prime_power_fourier p hp hprimary n h] at hne
  exact conductorFourier_support p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero) _ h hne

def primeCubicGauss (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis):ℂ:=
  ∑'x:Eis⧸Ideal.span {p},(primeCubicMulChar p hp hprimary^e) x*
    quotientTrace p hp.ne_zero (Ideal.Quotient.mk _ h*x)

theorem cubicUnitGaussSum_prime_power_lift (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (n:ℕ) (h:Eis):
    cubicUnitGaussSum (p^n*h) (p^(n+1))=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^n*primeCubicGauss p hp hprimary (n+1) h:=by
  rw [cubicUnitGaussSum_prime_power_fourier p hp hprimary n,
    conductorFourier_lift p (p^n) hp.ne_zero (pow_ne_zero _ hp.ne_zero)]
  have hn:Ideal.absNorm (Ideal.span {p^n})=Ideal.absNorm (Ideal.span {p})^n:=by
    rw [←Ideal.span_singleton_pow,map_pow]
  rw [hn,Nat.cast_pow]
  rfl

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma primeCubicMulChar_cube (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    primeCubicMulChar p hp hprimary^3=1:=by
  apply DFunLike.ext
  intro x
  by_cases hx:IsUnit x
  · obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
    rw [MulChar.pow_apply' _ (by decide),primeCubicMulChar_mk,←map_pow,
      symbol_cube_of_isCoprime d p hprimary ((isUnit_quotient_span_iff p d).mp hx).symm,map_one]
    exact (MulChar.one_apply_coe hx.unit).symm
  · rw [MulChar.map_nonunit _ hx,MulChar.map_nonunit _ hx]

lemma primeCubicMulChar_ne_one (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    primeCubicMulChar p hp hprimary≠1:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg:lambda∉(Ideal.span {p}:Ideal Eis):=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  intro hchar
  apply cubicChar_ne_one (Ideal.span {p}) hg
  apply DFunLike.ext
  intro x
  by_cases hx:IsUnit x
  · obtain ⟨d,rfl⟩:=Ideal.Quotient.mk_surjective x
    have he:=congrArg (fun χ:MulChar (Eis⧸Ideal.span {p}) ℂ=>χ (Ideal.Quotient.mk _ d)) hchar
    rw [primeCubicMulChar_mk,symbol_prime p hp hprimary,primeValue_eq _ hg] at he
    have hoc:(1:MulChar (Eis⧸Ideal.span {p}) ℂ) (Ideal.Quotient.mk _ d)=1:=
      MulChar.one_apply_coe hx.unit
    have hoo:(1:MulChar (Eis⧸Ideal.span {p}) Eis) (Ideal.Quotient.mk _ d)=1:=
      MulChar.one_apply_coe hx.unit
    rw [hoo]
    apply eisEmbedding_injective
    simpa only [hoc,map_one] using he
  · rw [MulChar.map_nonunit _ hx,MulChar.map_nonunit _ hx]

lemma primeCubicMulChar_order (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    orderOf (primeCubicMulChar p hp hprimary)=3:=by
  have hd:=orderOf_dvd_of_pow_eq_one (primeCubicMulChar_cube p hp hprimary)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1|h3
  · exact False.elim (primeCubicMulChar_ne_one p hp hprimary (orderOf_eq_one_iff.mp h1))
  · exact h3

lemma primeCubicMulChar_pow_eq_one (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (e:ℕ):
    primeCubicMulChar p hp hprimary^e=1↔3∣e:=by
  rw [←orderOf_dvd_iff_pow_eq_one,primeCubicMulChar_order]

lemma primeCubicGauss_mod_three (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (e:ℕ) (h:Eis):
    primeCubicGauss p hp hprimary e h=primeCubicGauss p hp hprimary (e%3) h:=by
  unfold primeCubicGauss
  have he:=pow_mod_orderOf (primeCubicMulChar p hp hprimary) e
  rw [primeCubicMulChar_order] at he
  rw [he]

lemma primeCubicGauss_eq_gaussSum (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis) [Fintype (Eis⧸Ideal.span {p})]:
    primeCubicGauss p hp hprimary e h=
      gaussSum (primeCubicMulChar p hp hprimary^e)
        ((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h)):=by
  simp only [primeCubicGauss,tsum_fintype,gaussSum,AddChar.mulShift_apply]

theorem primeCubicGauss_of_dvd (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (h:Eis) (hph:p∣h):
    primeCubicGauss p hp hprimary e h=
      if 3∣e then (Ideal.absNorm (Ideal.span {p}):ℂ)-1 else 0:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h=0:=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  rw [primeCubicGauss_eq_gaussSum,hh,AddChar.mulShift_zero]
  split_ifs with he
  · rw [(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he,gaussSum_one_one,
      Nat.card_units,Nat.cast_sub (Nat.succ_le_of_lt Nat.card_pos),Nat.cast_one]
    rfl
  · exact gaussSum_one_right (fun hχ=>he ((primeCubicMulChar_pow_eq_one p hp hprimary e).mp hχ))

theorem primeCubicGauss_trivial_nonzero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (e:ℕ) (he:3∣e) (h:Eis) (hph:¬p∣h):
    primeCubicGauss p hp hprimary e h=-1:=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h≠0:=by
    intro hh
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  rw [primeCubicGauss_eq_gaussSum,(primeCubicMulChar_pow_eq_one p hp hprimary e).mpr he]
  exact gaussSum_one_left (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero hh)

theorem primeCubicGauss_one_mul_two (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (h:Eis) (hph:¬p∣h):
    primeCubicGauss p hp hprimary 1 h*primeCubicGauss p hp hprimary 2 h=
      (Ideal.absNorm (Ideal.span {p}):ℂ):=by
  let:(Ideal.span {p}:Ideal Eis).IsMaximal:=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let:Field (Eis⧸Ideal.span {p}):=Ideal.Quotient.field _
  let:Fintype (Eis⧸Ideal.span {p}):=Fintype.ofFinite _
  have hh:Ideal.Quotient.mk (Ideal.span {p}) h≠0:=by
    intro hh
    exact hph (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hh))
  have hψ:((quotientTrace p hp.ne_zero).mulShift (Ideal.Quotient.mk _ h)).IsPrimitive:=
    AddChar.IsPrimitive.of_ne_one (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero hh)
  have he:=gaussSum_mul_gaussSum_pow_orderOf_sub_one
    (primeCubicMulChar_ne_one p hp hprimary) hψ
  rw [primeCubicMulChar_order] at he
  have hm:=MulChar.val_neg_one_eq_one_of_odd_order (by decide:Odd 3)
    (primeCubicMulChar_cube p hp hprimary)
  rw [hm,one_mul] at he
  change _=(Nat.card (Eis⧸Ideal.span {p}):ℂ)
  simpa only [primeCubicGauss_eq_gaussSum,pow_one,Nat.reduceSub,
    Nat.card_eq_fintype_card] using he

lemma primeCubicGauss_one_eq (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (h:Eis):
    primeCubicGauss p hp hprimary 1 h=cubicUnitGaussSum h p:=by
  have he:=cubicUnitGaussSum_prime_power_lift p hp hprimary 0 h
  simpa only [pow_zero,one_mul,pow_one,Nat.zero_add] using he.symm

end CubicEisenstein

end

end OAI
end OAIOriginalModule0275

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.TranslatedFourierResidues
Source SHA256: 7cdbe982716d2c4932a573634f7a019bfe9b93d627fdd31668977f1c77c86cee
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0276


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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

section
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma period_integral_fourier_translation (f:ℂ→ℂ)
    (hp:∀(n:Eis)(z:ℂ),f (z+3*eisEmbedding n)=f z) (h:Eis) (b:ℂ) :
    (∫z in periodDomain,f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ShortDraftTrace.breveE (cuspFrequency h*b)*
        ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  let g : ℂ→ℂ := fun z=>f z*ShortDraftTrace.breveE (-cuspFrequency h*z)
  have hg : ∀(n:Eis)(z:ℂ),g (z+3*eisEmbedding n)=g z := by
    intro n z
    dsimp only [g]
    rw [hp,cuspFrequency_negative_period]
  have he (z:ℂ) : f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z)=
      ShortDraftTrace.breveE (cuspFrequency h*b)*g (b+z) := by
    dsimp only [g]
    rw [mul_left_comm,←AddChar.map_add_eq_mul]
    congr 1
    · rw [add_comm]
    · congr 1
      ring
  simp_rw [he]
  rw [integral_const_mul,period_integral_translation g hg b]

theorem rational_cusp_fourier_right_T (r:SL(2,ℤ)) (n:ℕ) (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)*
        cuspFourierPhase h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*
        ∫w in cuspPeriodStrip 5 6,
          hyperbolicEisenstein s (rationalComplex r • w)*cuspFourierPhase h w∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex (r*ModularGroup.T^n) • w)*cuspFourierPhase h w
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex r • w)*cuspFourierPhase h w
  have hf : Continuous f := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  change (∫w in cuspPeriodStrip 5 6,f w∂hyperbolicVolume)=
    ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates f hf.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable f hf),
    cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg),
    ←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  dsimp only
  simp_rw [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper,
    cuspFourierPhase,hyperbolicHorizontal_upperPoint]
  rw [period_integral_fourier_translation
    (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0))
    (fun a z=>hyperbolicEisenstein_rational_periodic r a s hs z v hv0) h (n:ℂ)]
  ring

lemma translatedCuspFourier_residue_scaled_of_initial (h:Eis) (M N:levelTwo) (c:ℂ)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspFourierPhase h w∂hyperbolicVolume)=
      c*∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix N • w)*cuspFourierPhase h w∂hyperbolicVolume) :
    translatedCuspFourier h M cubicEisensteinResidue=
      c*translatedCuspFourier h N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedCuspFamily h M 2 3 (by norm_num) (by norm_num)
  let g : ℂ→ℂ := fun s=>c*translatedCuspFamily h N 2 3 (by norm_num) (by norm_num) s
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal h M 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>analyticAt_const.mul
    (translatedCuspFamily_analyticAt_nonreal h N 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedCuspFamily_initial h M 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      translatedCuspFamily_initial h N 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2]
    exact he s hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedCuspFamily_residue_limit h M 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  have hr := ((translatedCuspFamily_residue_limit h N 2 3 (by norm_num) (by norm_num)).const_mul c).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    · simpa using ht)
  dsimp only [f,g] at hv
  dsimp only [Function.comp_def]
  linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*hv

lemma translatedCuspFourier_one (h:Eis) (F:KernelQuotientL2) :
    translatedCuspFourier h 1 F=kernelCuspFourier h F := by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one]

lemma translatedCuspFourier_bruhat (h:Eis) (e:Fin 2) (a:Fin 3⊕(Fin 3×Fin 3)) :
    translatedCuspFourier h (rationalLift (rationalBruhatRep (e,a))) cubicEisensteinResidue=
      match a with
      | Sum.inl _=>kernelCuspFourier h cubicEisensteinResidue
      | Sum.inr ab=>ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
        translatedCuspFourier h oppositeSource cubicEisensteinResidue := by
  cases a with
  | inl a =>
    rw [←one_mul (kernelCuspFourier h cubicEisensteinResidue),←translatedCuspFourier_one h]
    apply translatedCuspFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    simp only [map_one,one_smul,one_mul]
  | inr ab =>
    apply translatedCuspFourier_residue_scaled_of_initial
    intro s hs hi
    simp_rw [sourceComplexMatrix_rationalLift,hyperbolicEisenstein_bruhat]
    change (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex ModularGroup.S •
        (rationalComplex (ModularGroup.T^ab.2.val) • w))*cuspFourierPhase h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(ab.2.val:ℂ))*
      ∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (rationalComplex ModularGroup.S • w)*
        cuspFourierPhase h w∂hyperbolicVolume
    simpa only [map_mul,mul_smul] using
      rational_cusp_fourier_right_T ModularGroup.S ab.2.val h s (by linarith)

def sourceRayPhaseSum (h:Eis) : ℂ :=
  ∑ b:Fin 3,ShortDraftTrace.breveE (cuspFrequency h*(b.val:ℂ))

theorem kernelSourceProjection_residue_fourier (h:Eis) :
    kernelCuspFourier h (kernelSourceProjection cubicEisensteinResidue)=
      (4:ℂ)⁻¹*(kernelCuspFourier h cubicEisensteinResidue+
        sourceRayPhaseSum h*translatedCuspFourier h oppositeSource cubicEisensteinResidue) := by
  rw [kernelSourceProjection_eq_twentyFour,map_smul,map_sum]
  change (24:ℂ)⁻¹*(∑i:RationalBruhatIndex,
    translatedCuspFourier h (rationalLift (rationalBruhatRep i)) cubicEisensteinResidue)=_
  rw [Fintype.sum_prod_type]
  simp_rw [translatedCuspFourier_bruhat]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  rw [←Finset.sum_mul]
  change (24:ℂ)⁻¹*((2:ℂ)*(3*kernelCuspFourier h cubicEisensteinResidue+
    3*(sourceRayPhaseSum h*translatedCuspFourier h oppositeSource cubicEisensteinResidue)))=_
  ring

end

section
open CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_cube (h:Eis) :
    ShortDraftTrace.breveE (cuspFrequency h)^3=1 := by
  rw [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  have hp:=cuspFrequency_period h (1:Eis)
  simpa only [map_one,mul_one,one_mul,Nat.cast_ofNat,mul_comm] using hp

lemma sourceRayPhaseSum_formula (h:Eis) :
    sourceRayPhaseSum h=1+ShortDraftTrace.breveE (cuspFrequency h)+
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
  unfold sourceRayPhaseSum
  simp only [Fin.sum_univ_succ,Fin.val_zero,Nat.cast_zero,mul_zero,AddChar.map_zero_eq_one,
    Fin.val_succ,Nat.cast_add,Nat.cast_one,zero_add,mul_one,Fin.sum_univ_zero,add_zero]
  have he : ShortDraftTrace.breveE (cuspFrequency h*(1+1))=
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
    rw [mul_add,mul_one,AddChar.map_add_eq_mul,pow_two]
  rw [he]
  ring

lemma sourceRayPhaseSum_eq (h:Eis) :
    sourceRayPhaseSum h=if ShortDraftTrace.breveE (cuspFrequency h)=1 then 3 else 0 := by
  rw [sourceRayPhaseSum_formula]
  split_ifs with he
  · rw [he]
    norm_num
  · have hc:=sourceRayPhase_cube h
    have hz : (ShortDraftTrace.breveE (cuspFrequency h)-1)*
        (1+ShortDraftTrace.breveE (cuspFrequency h)+ShortDraftTrace.breveE (cuspFrequency h)^2)=0 := by
      linear_combination hc
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr he)

lemma kernelCuspFourier_residue_horizontal (h:Eis) :
    kernelCuspFourier h cubicEisensteinResidue=
      ShortDraftTrace.breveE (cuspFrequency h)*kernelCuspFourier h cubicEisensteinResidue := by
  have hh:=translatedCuspFourier_residue_scaled_of_initial h 1 1
    (ShortDraftTrace.breveE (cuspFrequency h)) (by
      intro s hs hi
      have he:=rational_cusp_fourier_right_T (1:SL(2,ℤ)) 1 h s (by linarith)
      have hT (w:HyperbolicSpace) : hyperbolicEisenstein s (rationalComplex ModularGroup.T • w)=hyperbolicEisenstein s w := by
        simpa only [pow_one] using hyperbolicEisenstein_T_pow s 1 w
      simpa only [one_mul,pow_one,map_one,one_smul,Nat.cast_one,mul_one,hT] using he)
  simpa only [translatedCuspFourier_one] using hh

lemma kernelCuspFourier_residue_eq_zero_of_not_horizontal (h:Eis)
    (hh:ShortDraftTrace.breveE (cuspFrequency h)≠1) :
    kernelCuspFourier h cubicEisensteinResidue=0 := by
  have he:=kernelCuspFourier_residue_horizontal h
  have hz : (ShortDraftTrace.breveE (cuspFrequency h)-1)*
      kernelCuspFourier h cubicEisensteinResidue=0 := by linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hh)

theorem kernelSourceProjection_residue_fourier_mask (h:Eis) :
    kernelCuspFourier h (kernelSourceProjection cubicEisensteinResidue)=
      if ShortDraftTrace.breveE (cuspFrequency h)=1 then
        (4:ℂ)⁻¹*(kernelCuspFourier h cubicEisensteinResidue+
          3*translatedCuspFourier h oppositeSource cubicEisensteinResidue)
      else 0 := by
  rw [kernelSourceProjection_residue_fourier,sourceRayPhaseSum_eq]
  split_ifs with hh
  · rfl
  · rw [kernelCuspFourier_residue_eq_zero_of_not_horizontal h hh]
    ring

end

open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma oppositeFrequency_cross_identity (h:Eis) :
    Set.EqOn (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s (3*(9*h)))
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) {s:ℂ|1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s (3*(9*h))) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt (3*(9*h)) s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
      cuspWhittakerHeightFactor s (3*(9*h)))=ᶠ[𝓝 (5+Complex.I:ℂ)]
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num)
      (by norm_num) s hs.1 hs.2,opposite_cusp_fourier_average s (by linarith [hs.1]),
      translatedCuspFamily_opposite_initial (9*h) s hs.1 hs.2]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev

theorem translatedCuspFourier_unramified_residue (h:Eis) :
    translatedCuspFourier h oppositeSource cubicEisensteinResidue=
      unramifiedGaussResidue (9*h)*cuspWhittakerHeightFactor (4/3:ℂ) h := by
  have hh (k:Eis) : Tendsto (fun s:ℂ=>cuspWhittakerHeightFactor s k)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) k)) :=
    (cuspWhittakerHeightFactor_analyticAt k (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hl := ((translatedCuspFamily_residue_limit h oppositeSource 2 3
    (by norm_num) (by norm_num)).mul (hh (3*(9*h)))).comp upperVertical_tendsto_cubic_punctured
  have hr := ((translatedCuspFamily_residue_limit (3*(9*h)) oppositeSource 2 3
    (by norm_num) (by norm_num)).mul (hh h)).comp upperVertical_tendsto_cubic_punctured
  have hev : (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) (3*(9*h)))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=oppositeFrequency_cross_identity h (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      · simpa using ht)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : translatedCuspFourier h oppositeSource cubicEisensteinResidue*
      cuspWhittakerHeightFactor (4/3:ℂ) (3*(9*h))=
      translatedCuspFourier (3*(9*h)) oppositeSource cubicEisensteinResidue*
        cuspWhittakerHeightFactor (4/3:ℂ) h := tendsto_nhds_unique_of_eventuallyEq hl hr hev
  unfold unramifiedGaussResidue
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff (cuspWhittakerHeightFactor_center_ne_zero (3*(9*h)))).mpr heq

def principalArithmeticResidue (h:Eis) : ℂ :=
  if h=0 then constantArithmeticResidue else nonzeroScatteringResidue h

lemma kernelCuspFourier_principal_residue (h:Eis) :
    kernelCuspFourier h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*principalArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  by_cases hh:h=0
  · subst h
    rw [kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average,principalArithmeticResidue,ite_eq_left rfl,
      cuspWhittakerHeightFactor_zero (4/3) (by norm_num),cuspConstantAverageResidue]
    ring
  · rw [principalArithmeticResidue,ite_eq_right hh,nonzeroScatteringResidue]
    field_simp [cusp_volume_ne_zero,cuspWhittakerHeightFactor_center_ne_zero h]

def sourceArithmeticResidue (h:Eis) : ℂ :=
  if ShortDraftTrace.breveE (cuspFrequency h)=1 then
    (4:ℂ)⁻¹*(principalArithmeticResidue h+
      3*unramifiedGaussResidue (9*h)/((9*Real.sqrt 3/2:ℝ):ℂ))
  else 0

theorem kernelSourceProjection_gauss_residue (h:Eis) :
    kernelCuspFourier h (kernelSourceProjection cubicEisensteinResidue)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  rw [kernelSourceProjection_residue_fourier_mask,sourceArithmeticResidue]
  split_ifs with hh
  · rw [kernelCuspFourier_principal_residue,translatedCuspFourier_unramified_residue]
    field_simp [cusp_volume_ne_zero]

  · ring

theorem cubicSourceResidualFunction_fourier_average (h:Eis) :
    (∫w in cuspPeriodStrip 5 6,cubicSourceResidualFunction w*cuspFourierPhase h w∂hyperbolicVolume)=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*sourceArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  rw [←kernelSourceProjection_gauss_residue,kernelCuspFourier_integral]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae cubicSourceResidualFunction_represents_projection] with w hw
  exact congrArg (fun z:ℂ=>z*cuspFourierPhase h w) hw.symm

lemma unramifiedGaussResidue_zero :
    unramifiedGaussResidue 0=((9*Real.sqrt 3/2:ℝ):ℂ)*constantArithmeticResidue := by
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero (0:Eis))
  have ht:=translatedCuspFourier_unramified_residue (0:Eis)
  simp only [mul_zero] at ht
  rw [←ht,translatedCuspFourier_opposite_zero_residue]
  have hp:=kernelCuspFourier_principal_residue (0:Eis)
  rw [kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average] at hp
  simpa [principalArithmeticResidue] using hp

lemma sourceArithmeticResidue_zero : sourceArithmeticResidue 0=constantArithmeticResidue := by
  rw [sourceArithmeticResidue]
  simp only [cuspFrequency,map_zero,zero_div,AddChar.map_zero_eq_one,
    principalArithmeticResidue,mul_zero,unramifiedGaussResidue_zero,ite_true]
  field_simp [cusp_volume_ne_zero]
  ; ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

def horizontalPhaseMultiplier (freq direction : ℂ) : ℂ :=
  (2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))

lemma brevePhase_hasDerivAt (freq z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ShortDraftTrace.breveE (freq*(z+(x:ℂ)*direction)))
      (horizontalPhaseMultiplier freq direction*
        ShortDraftTrace.breveE (freq*(z+(t:ℂ)*direction))) t := by
  have hz : HasDerivAt (fun x : ℝ => freq*(z+(x:ℂ)*direction)) (freq*direction) t := by
    convert (((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const direction).const_add z).const_mul freq using 1 <;>
      simp
  have he := ((hz.add hz.star).const_mul (2*Real.pi*Complex.I)).cexp
  change HasDerivAt (fun x : ℝ => Complex.exp ((2*Real.pi*Complex.I)*
    (freq*(z+(x:ℂ)*direction)+star (freq*(z+(x:ℂ)*direction)))))
    ((2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))*
      Complex.exp ((2*Real.pi*Complex.I)*
        (freq*(z+(t:ℂ)*direction)+star (freq*(z+(t:ℂ)*direction))))) t
  simpa only [Pi.add_apply,mul_comm] using he

lemma horizontalPhaseMultiplier_norm (freq direction : ℂ) :
    ‖horizontalPhaseMultiplier freq direction‖≤4*Real.pi*‖freq‖*‖direction‖ := by
  have hc : ‖(2*Real.pi*Complex.I:ℂ)‖=2*Real.pi := by
    norm_num [norm_mul,abs_of_pos Real.pi_pos]
  unfold horizontalPhaseMultiplier
  rw [norm_mul,hc]
  calc
    _ ≤ (2*Real.pi)*(‖freq*direction‖+‖star (freq*direction)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = _ := by rw [norm_star,norm_mul];ring

lemma horizontalPhaseMultiplier_wirtinger (freq : ℂ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq 1+
      Complex.I*horizontalPhaseMultiplier freq Complex.I)=2*Real.pi*Complex.I*star freq := by
  simp only [horizontalPhaseMultiplier,mul_one,star_mul,Complex.star_def,
    Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ring

lemma norm_mul_exp_neg_bound (a r : ℝ) (ha : 0<a) :
    r*Real.exp (-a*r)≤(2/a)*Real.exp (-(a/2)*r) := by
  have hbase := Real.add_one_le_exp ((a/2)*r)
  have hr : r≤(2/a)*Real.exp ((a/2)*r) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    nlinarith
  calc
    _ ≤ ((2/a)*Real.exp ((a/2)*r))*Real.exp (-a*r) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc,←Real.exp_add];congr 2;ring

lemma summable_norm_mul_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => ‖cuspFrequency h‖*Real.exp (-a*‖cuspFrequency h‖)) := by
  apply Summable.of_nonneg_of_le (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
    (fun h => norm_mul_exp_neg_bound a _ ha)
  exact (summable_exp_neg_cuspFrequency_norm (a/2) (half_pos ha)).mul_left (2/a)

local notation "O" => ActualEisensteinCubic.O

def cubicResidualDirectionalTerm (h : ActualEisensteinCubic.O) (v : ℝ) (z direction : ℂ) : ℂ :=
  horizontalPhaseMultiplier (cuspFrequency h) direction*cubicResidualNonzeroTerm h (v,z)

lemma cubicResidualNonzeroTerm_horizontal_hasDerivAt (h : ActualEisensteinCubic.O) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => cubicResidualNonzeroTerm h (v,z+(x:ℂ)*direction))
      (cubicResidualDirectionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (brevePhase_hasDerivAt (cuspFrequency h) z direction t).const_mul
    (cubicResidualModeAmplitude v h)
  have hf : (fun x : ℝ => cubicResidualNonzeroTerm h (v,z+(x:ℂ)*direction))=
      (fun x : ℝ => cubicResidualModeAmplitude v h*
        ShortDraftTrace.breveE (cuspFrequency h*(z+(x:ℂ)*direction))) := by
    funext x
    exact cubicResidualNonzeroTerm_eq_amplitude v hv h _
  rw [hf]
  convert hh using 1
  rw [cubicResidualDirectionalTerm,cubicResidualNonzeroTerm_eq_amplitude v hv h]
  ring

lemma cubicResidualDirectionalTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),v∈Set.Icc a b →
      ‖cubicResidualDirectionalTerm h v z direction‖≤
        C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_slab_bound a b ha hab
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hv
  rw [cubicResidualDirectionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h (v,z) hv)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma cubicResidualDirectionalTerm_summable (v : ℝ) (hv : 0<v) (z direction : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => cubicResidualDirectionalTerm h v z direction) := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualDirectionalTerm_slab_bound v v hv le_rfl direction
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h v z ⟨le_rfl,le_rfl⟩)
  exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C

lemma cubicResidualNonzeroSeries_horizontal_hasDerivAt (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => cubicResidualNonzeroSeries (v,z+(x:ℂ)*direction))
      (∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualDirectionalTerm_slab_bound v v hv le_rfl direction
  have hs := (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C
  have hz : Summable (fun h : ActualEisensteinCubic.O => cubicResidualNonzeroTerm h (v,z+(0:ℂ)*direction)) := by
    simpa only [zero_mul,add_zero] using cubicResidualNonzeroTerm_summable (v,z) hv
  exact hasDerivAt_tsum hs (fun h x => cubicResidualNonzeroTerm_horizontal_hasDerivAt h v hv z direction x)
    (fun h x => hbound h v (z+(x:ℂ)*direction) ⟨le_rfl,le_rfl⟩) hz t

lemma cubicResidualFunction_horizontal_hasDerivAt (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => cubicResidualFunction (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (cubicResidualNonzeroSeries_horizontal_hasDerivAt v hv z direction t).const_add
    ((3*Real.pi:ℂ)*constantArithmeticResidue*(v:ℂ)^(2/3:ℂ))
  simpa only [cubicResidualFunction,cubicResidualNonzeroFunction,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint] using hh

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def horizontalWirtingerBar (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ => f (z+(t:ℂ))) 0+
    Complex.I*deriv (fun t : ℝ => f (z+(t:ℂ)*Complex.I)) 0)

lemma horizontalWirtingerBar_brevePhase (freq z : ℂ) :
    horizontalWirtingerBar (fun w => ShortDraftTrace.breveE (freq*w)) z=
      (2*Real.pi*Complex.I*star freq)*ShortDraftTrace.breveE (freq*z) := by
  have h1 := (brevePhase_hasDerivAt freq z 1 0).deriv
  have hI := (brevePhase_hasDerivAt freq z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI]
  linear_combination ShortDraftTrace.breveE (freq*z)*horizontalPhaseMultiplier_wirtinger freq

theorem cubicResidualFunction_wirtingerBar (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerBar (fun w => cubicResidualFunction (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*star (cuspFrequency h))*cubicResidualNonzeroTerm h (v,z) := by
  have h1 := (cubicResidualFunction_horizontal_hasDerivAt v hv z 1 0).deriv
  have hI := (cubicResidualFunction_horizontal_hasDerivAt v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI]
  have hs1 := cubicResidualDirectionalTerm_summable v hv z 1
  have hsI := (cubicResidualDirectionalTerm_summable v hv z Complex.I).mul_left Complex.I
  rw [←tsum_mul_left,←hs1.tsum_add hsI,←tsum_mul_left]
  apply tsum_congr
  intro h
  unfold cubicResidualDirectionalTerm
  linear_combination cubicResidualNonzeroTerm h (v,z)*horizontalPhaseMultiplier_wirtinger (cuspFrequency h)

lemma cubicResidualFunction_wirtingerBar_summable (v : ℝ) (hv : 0<v) (z : ℂ) :
    Summable (fun h : ActualEisensteinCubic.O => (2*Real.pi*Complex.I*star (cuspFrequency h))*cubicResidualNonzeroTerm h (v,z)) := by
  have hs := ((cubicResidualDirectionalTerm_summable v hv z 1).add
    ((cubicResidualDirectionalTerm_summable v hv z Complex.I).mul_left Complex.I)).mul_left (1/2:ℂ)
  apply hs.congr
  intro h
  unfold cubicResidualDirectionalTerm
  linear_combination cubicResidualNonzeroTerm h (v,z)*horizontalPhaseMultiplier_wirtinger (cuspFrequency h)

end CubicEisenstein

end

end OAI
end OAIOriginalModule0276

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.ResidualCuspDecay
Source SHA256: 74a59113fdcb7d904d27054530ada03ef3d876b1ffefbcb08b9a6f15d72f5c5c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0277



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
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def residualCuspDecayRate : ℝ := Real.pi*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹/4

lemma residualCuspDecayRate_pos : 0<residualCuspDecayRate := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  unfold residualCuspDecayRate
  positivity

lemma cubicResidualNonzeroTerm_cusp_bound (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖cubicResidualNonzeroTerm h (v,z)‖≤C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hCu := cubicBesselUpperAway_pos delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := cubicResidualFourierCoefficient_subexponential (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*cubicBesselUpperAway delta,mul_nonneg hC (cubicBesselUpperAway_pos delta hdelta).le,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · simp only [cubicResidualNonzeroTerm,ite_eq_left hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hav ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [cubicResidualNonzeroTerm_bessel h hh v hv z,norm_mul,norm_mul,norm_mul,
    breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*v*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hcoeff h hh) hv.le)
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*cubicBesselUpperAway delta)*v*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*v)/2=
        -(4*Real.pi*‖cuspFrequency h‖*v/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hav (mul_pos Real.pi_pos hr).le]

lemma cubicResidualDirectionalTerm_cusp_majorant (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃D : ℝ,0≤D ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖cubicResidualDirectionalTerm h v z direction‖≤
        (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*
          (‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)) := by
  obtain ⟨C,hC,hbound⟩ := cubicResidualNonzeroTerm_cusp_bound a ha
  refine ⟨4*Real.pi*‖direction‖*C,by positivity,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · subst h
    simp only [cubicResidualDirectionalTerm,cubicResidualNonzeroTerm,ite_true,mul_zero,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have he : Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)≤
      Real.exp (-(2*residualCuspDecayRate)*v)*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left (cuspFrequency_norm_lower h hh)
      (show 0≤Real.pi*v/2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hav (show 0≤Real.pi*‖cuspFrequency h‖/2 by positivity)
    unfold residualCuspDecayRate
    nlinarith
  rw [cubicResidualDirectionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h v z hav)
        (norm_nonneg _) (by positivity)
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*(Real.exp (-(2*residualCuspDecayRate)*v)*
          Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖))) := by
      gcongr
    _ = _ := by ring

lemma cubicResidualDirectionalSeries_cusp_decay (a : ℝ) (ha : 0<a) (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(z : ℂ),a≤v →
      ‖∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v z direction‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨D,hD,hbound⟩ := cubicResidualDirectionalTerm_cusp_majorant a ha direction
  have hc := residualCuspDecayRate_pos
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hs := summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a/2) (by positivity)
  refine ⟨D*S*(2/(2*residualCuspDecayRate)),by positivity,?_⟩
  intro v z hav
  have hsum := tsum_of_norm_bounded
    (hs.hasSum.mul_left (D*v*Real.exp (-(2*residualCuspDecayRate)*v)))
    (fun h => hbound h v z hav)
  calc
    _ ≤ (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D*S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D*S)*((2/(2*residualCuspDecayRate))*
        Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      rw [show -((2*residualCuspDecayRate)/2)*v=-residualCuspDecayRate*v by ring]
      ring

theorem cubicResidualFunction_wirtingerBar_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => cubicResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨C1,hC1,hbound1⟩ := cubicResidualDirectionalSeries_cusp_decay a ha 1
  obtain ⟨CI,hCI,hboundI⟩ := cubicResidualDirectionalSeries_cusp_decay a ha Complex.I
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (cubicResidualFunction_horizontal_hasDerivAt v hv z 1 0).deriv
  have hI := (cubicResidualFunction_horizontal_hasDerivAt v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v z 1‖+
        ‖Complex.I*(∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v z Complex.I)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v z 1‖+
        ‖∑'h : ActualEisensteinCubic.O,cubicResidualDirectionalTerm h v z Complex.I‖) := by
      rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-residualCuspDecayRate*v)+CI*Real.exp (-residualCuspDecayRate*v)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add (hbound1 v z hav) (hboundI v z hav)
    _ = _ := by ring

end CubicEisenstein

namespace ShortDraftCRT
open scoped BigOperators Classical Matrix

section
variable {R : Type*} [CommRing R]

theorem exists_frequency_lift (N p h : R) (hcop : IsCoprime N p) :
    ∃k : R, N∣k ∧ p∣k-h := by
  obtain ⟨u,v,huv⟩ := hcop
  refine ⟨h*u*N,⟨h*u,by ring⟩,⟨-h*v,?_⟩⟩
  linear_combination h*huv

theorem crossNum_congr_of_lift_dvd (N a c : R) (rows : List (R×R))
    (hlift : ∀ph∈rows,N∣ph.2) :
    N∣crossNum a c rows-a*(rows.map Prod.fst).prod := by
  induction rows with
  | nil => simp [crossNum]
  | cons ph rows ih =>
    rcases ph with ⟨p,h⟩
    have ht := ih (fun ph hm=>hlift ph (List.mem_cons_of_mem _ hm))
    have hh := hlift (p,h) (List.mem_cons_self ..)
    have h1 := dvd_mul_of_dvd_left ht p
    have h2 := dvd_mul_of_dvd_left hh (crossDen c rows)
    convert dvd_add h1 h2 using 1 ;
      simp only [crossNum,List.map_cons,List.prod_cons] ; ring

theorem crossNum_fixed_sector_congr (M a c : R) (rows rows0 : List (R×R))
    (hc : c∣M)
    (hlift : ∀ph∈rows,M^2∣ph.2) (hlift0 : ∀ph∈rows0,M^2∣ph.2)
    (hsector : M^2∣(rows.map Prod.fst).prod-(rows0.map Prod.fst).prod) :
    M*c∣crossNum a c rows-crossNum a c rows0 := by
  have hmc : M*c∣M^2 := by simpa only [pow_two] using mul_dvd_mul_left M hc
  have h1 := crossNum_congr_of_lift_dvd (M^2) a c rows hlift
  have h0 := crossNum_congr_of_lift_dvd (M^2) a c rows0 hlift0
  have h2 := dvd_mul_of_dvd_right hsector a
  apply hmc.trans
  convert dvd_sub (dvd_add h1 h2) h0 using 1 ; ring

variable [IsDomain R]

theorem fixed_ray_completion_in_sector (M a c : R) (rows rows0 : List (R×R))
    (b0 d0 : R) (hc0 : c≠0) (hc : c∣M)
    (hbase : IsCoprime a c) (hrows : GoodRows c rows)
    (hr : IsCoprime (rows.map Prod.fst).prod (M*c))
    (hlift : ∀ph∈rows,M^2∣ph.2) (hlift0 : ∀ph∈rows0,M^2∣ph.2)
    (hsector : M^2∣(rows.map Prod.fst).prod-(rows0.map Prod.fst).prod)
    (hdet0 : crossNum a c rows0*d0-b0*crossDen c rows0=1) :
    ∃b d : R, crossNum a c rows*d-b*crossDen c rows=1 ∧ M*c∣d-d0 ∧
      (!![crossNum a c rows,b;crossDen c rows,d] : Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) =
        (!![crossNum a c rows0,b0;crossDen c rows0,d0] : Matrix (Fin 2) (Fin 2) R).map
          (Ideal.Quotient.mk (Ideal.span {M})) := by
  have hn := crossNum_fixed_sector_congr M a c rows rows0 hc hlift hlift0 hsector
  have hrmod : M∣(rows.map Prod.fst).prod-(rows0.map Prod.fst).prod :=
    (show M∣M^2 by simpa only [pow_two] using (dvd_mul_right M M)).trans hsector
  have hcop := coprime_cross_num_list a c rows hbase hrows
  rw [crossDen_eq_product] at hcop hdet0 ⊢
  obtain ⟨b,d,hd,hdd,hmat⟩ := exists_fixed_matrix_completion M c
    (crossNum a c rows0) (rows0.map Prod.fst).prod d0 b0 hc0 hdet0
    (crossNum a c rows) (rows.map Prod.fst).prod hn hrmod hr hcop.of_mul_right_right
  refine ⟨b,d,hd,hdd,?_⟩
  simpa only [crossDen_eq_product] using hmat

end

variable {R : Type*} [CommRing R] [IsDomain R]

theorem exists_sectorwise_completions {ι Q : Type*} (M c : R) (hc : c≠0)
    (sector : ι→Q) (a r : ι→R)
    (hcop : ∀i,IsCoprime (a i) (c*r i))
    (hr : ∀i,IsCoprime (r i) (M*c))
    (ha : ∀i j,sector i=sector j → M*c∣a i-a j)
    (hrr : ∀i j,sector i=sector j → M∣r i-r j) :
    ∃(b d : ι→R) (C : Q→Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧
      ∀i,(!![a i,b i;c*r i,d i] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have hlocal (q : Q) :
      ∃C : Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M}),
        ∀i,sector i=q → ∃b d : R,a i*d-b*(c*r i)=1 ∧
          (!![a i,b;c*r i,d] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq : ∃i,sector i=q
    · obtain ⟨j,hj⟩ := hq
      obtain ⟨x,y,hxy⟩ := hcop j
      have hdet : a j*x-(-y)*(c*r j)=1 := by linear_combination hxy
      refine ⟨(!![a j,-y;c*r j,x] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs : sector i=sector j := hi.trans hj.symm
      obtain ⟨b,d,hd,_,he⟩ := exists_fixed_matrix_completion M c (a j) (r j) x (-y)
        hc hdet (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hd,he⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i : ι) := hC (sector i) i rfl
  choose b d hd he using hi
  exact ⟨b,d,C,hd,he⟩

def LiftedRows (M c : R) :=
  {rows : List (R×R) // GoodRows c rows ∧ (∀ph∈rows,M^2∣ph.2) ∧
    IsCoprime (rows.map Prod.fst).prod (M*c)}

theorem exists_uniform_cusp_completions (M a c : R) (hc0 : c≠0)
    (hc : c∣M) (hbase : IsCoprime a c) :
    ∃(b d : LiftedRows M c→R)
      (C : (R⧸Ideal.span {M^2})→Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M})),
      (∀i,crossNum a c i.val*d i-b i*crossDen c i.val=1) ∧
      ∀i,(!![crossNum a c i.val,b i;crossDen c i.val,d i] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M}))=
        C (Ideal.Quotient.mk (Ideal.span {M^2}) (i.val.map Prod.fst).prod) := by
  let sector : LiftedRows M c→R⧸Ideal.span {M^2} :=
    fun i=>Ideal.Quotient.mk (Ideal.span {M^2}) (i.val.map Prod.fst).prod
  have hsector (i j : LiftedRows M c) (hs : sector i=sector j) :
      M^2∣(i.val.map Prod.fst).prod-(j.val.map Prod.fst).prod :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hs)
  obtain ⟨b,d,C,hd,he⟩ := exists_sectorwise_completions M c hc0 sector
    (fun i=>crossNum a c i.val) (fun i=>(i.val.map Prod.fst).prod)
    (fun i=>by
      simpa only [←crossDen_eq_product] using coprime_cross_num_list a c i.val hbase i.property.1)
    (fun i=>i.property.2.2)
    (fun i j hs=>crossNum_fixed_sector_congr M a c i.val j.val hc
      i.property.2.1 j.property.2.1 (hsector i j hs))
    (fun i j hs=>(show M∣M^2 by simpa only [pow_two] using dvd_mul_right M M).trans
      (hsector i j hs))
  refine ⟨b,d,C,?_,?_⟩
  · intro i
    simpa only [crossDen_eq_product] using hd i
  · intro i
    simpa only [crossDen_eq_product,sector] using he i

theorem eisenstein_uniform_cusp_completions
    (M a c : ActualEisensteinCubic.O) (hM : M≠0) (hc0 : c≠0)
    (hc : c∣M) (hbase : IsCoprime a c) :
    ∃(b d : LiftedRows M c→ActualEisensteinCubic.O)
      (S : Set (Matrix (Fin 2) (Fin 2) (ActualEisensteinCubic.O⧸Ideal.span {M}))),
      S.Finite ∧ S.ncard≤Ideal.absNorm (Ideal.span {M^2}) ∧
      (∀i,crossNum a c i.val*d i-b i*crossDen c i.val=1) ∧
      ∀i,(!![crossNum a c i.val,b i;crossDen c i.val,d i] :
        Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O).map
          (Ideal.Quotient.mk (Ideal.span {M}))∈S := by
  let : Finite (ActualEisensteinCubic.O⧸Ideal.span {M^2}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero _ hM)
  obtain ⟨b,d,C,hd,he⟩ := exists_uniform_cusp_completions M a c hc0 hc hbase
  refine ⟨b,d,Set.range C,Set.finite_range C,?_,hd,?_⟩
  · have hh := Set.ncard_image_le (s := Set.univ) (f := C)
    simpa only [Set.image_univ,Set.ncard_univ,Ideal.absNorm_apply,
      Submodule.cardQuot_apply] using hh
  · intro i
    exact ⟨_,(he i).symm⟩

end ShortDraftCRT

open scoped BigOperators Classical

namespace ShortDraftCusp

section
open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_principal_global (a c0 r : Eis)
    (ha : lambda^2∣a-1) (hr : lambda^2∣r-1) :
    symbol (c0*r) a=symbol c0 a*symbol a r := by
  rw [symbol_mul_numerator _ _ a ha,
    symbol_reciprocity r a (primary_ne_zero r hr) (primary_ne_zero a ha) hr ha]

theorem A3_ramified_global (a b cprime d u : Eis)
    (hdet : a*d-b*(u*cprime)=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣(a-u*b)-1) :
    symbol (u*cprime-u*d) (a-u*b)=symbol (-u) (a-u*b)*symbol cprime a := by
  have h1 : symbol a (a-u*b)*symbol (u*cprime-u*d) (a-u*b)=symbol (-u) (a-u*b) := by
    rw [←symbol_mul_numerator _ _ _ hA]
    apply symbol_congr
    refine ⟨u*cprime,?_⟩
    linear_combination -u*hdet
  have h2 : symbol (a-u*b) a*symbol cprime a=1 := by
    rw [←symbol_mul_numerator _ _ _ ha,←symbol_one_numerator a ha]
    apply symbol_congr
    refine ⟨cprime-d,?_⟩
    linear_combination hdet
  rw [symbol_reciprocity a (a-u*b) (primary_ne_zero a ha)
    (primary_ne_zero _ hA) ha hA] at h1
  calc
    _ = (symbol (a-u*b) a*symbol cprime a)*symbol (u*cprime-u*d) (a-u*b) := by rw [h2,one_mul]
    _ = (symbol (a-u*b) a*symbol (u*cprime-u*d) (a-u*b))*symbol cprime a := by ring
    _ = _ := by rw [h1]

theorem A3_ramified_global_factor (a b c0 r d u : Eis)
    (hdet : a*d-b*(u*(c0*r))=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣(a-u*b)-1) (hr : lambda^2∣r-1) :
    symbol (u*(c0*r)-u*d) (a-u*b)=
      (symbol (-u) (a-u*b)*symbol c0 a)*symbol a r := by
  rw [A3_ramified_global a b (c0*r) d u hdet ha hA,
    A3_principal_global a c0 r ha hr]
  ring

theorem A3_unramified_global (a b c d : Eis)
    (hdet : a*d-b*c=1) (hb : lambda^2∣(-b)-1) (hc : lambda^2∣c-1)
    (h9 : (9:Eis)∣a*d) :
    symbol (-d) (-b)=symbol a c := by
  have hp : lambda^2∣((-b)*c)-1 := primary_mul (-b) c hb hc
  have hprod : symbol d (-b)*symbol d c=1 := by
    rw [←symbol_mul_denominator]
    have hnine : (9:Eis)∣(-b)*c-1 := by
      convert dvd_neg.mpr h9 using 1
      linear_combination hdet
    have hd : d∣(-b)*c-1 := by
      refine ⟨-a,?_⟩
      linear_combination hdet
    rw [symbol_denominator_congr d ((-b)*c) 1 hp (by simp) hnine hd,symbol_one]
  have hother : symbol a c*symbol d c=1 := by
    rw [←symbol_mul_numerator _ _ _ hc,←symbol_one_numerator c hc]
    apply symbol_congr
    refine ⟨b,?_⟩
    linear_combination hdet
  rw [symbol_neg_numerator _ _ hb]
  calc
    symbol d (-b) = symbol d (-b)*(symbol a c*symbol d c) := by rw [hother,mul_one]
    _ = (symbol d (-b)*symbol d c)*symbol a c := by ring
    _ = symbol a c := by rw [hprod,one_mul]

theorem A3_unramified_global_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (hb : lambda^2∣(-b)-1)
    (hc : lambda^2∣c0*r-1) (h9 : (9:Eis)∣a*d) :
    symbol (-d) (-b)=symbol a c0*symbol a r := by
  rw [A3_unramified_global a b (c0*r) d hdet hb hc h9,symbol_mul_denominator]

theorem A3_fixed_factor_congr (M c0 a a0 : Eis)
    (h9M : (9:Eis)∣M) (ha : lambda^2∣a-1) (ha0 : lambda^2∣a0-1)
    (hsector : M*c0∣a-a0) : symbol c0 a=symbol c0 a0 := by
  apply symbol_denominator_congr c0 a a0 ha ha0
  · exact (h9M.trans (dvd_mul_right M c0)).trans hsector
  · exact (dvd_mul_left c0 M).trans hsector

end

open ActualEisensteinCubic CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

theorem A3_ramified_fixed_factor_congr (M c0 u a a0 b b0 : Eis)
    (h9M : (9:Eis)∣M) (hcM : c0∣M) (huM : u∣M)
    (ha : lambda^2∣a-1) (ha0 : lambda^2∣a0-1)
    (hA : lambda^2∣a-u*b-1) (hA0 : lambda^2∣a0-u*b0-1)
    (hma : M∣a-a0) (hmb : M∣b-b0) :
    symbol (-u) (a-u*b)*symbol c0 a=
      symbol (-u) (a0-u*b0)*symbol c0 a0 := by
  have hdiff : M∣(a-u*b)-(a0-u*b0) := by
    convert dvd_sub hma (dvd_mul_of_dvd_right hmb u) using 1 ; ring
  have hfirst : symbol (-u) (a-u*b)=symbol (-u) (a0-u*b0) := by
    apply symbol_denominator_congr _ _ _ hA hA0 (h9M.trans hdiff)
    exact neg_dvd.mpr (huM.trans hdiff)
  have hsecond := symbol_denominator_congr c0 a a0 ha ha0 (h9M.trans hma) (hcM.trans hma)
  rw [hfirst,hsecond]

theorem A3_unramified_fixed_factor_congr (M c0 a a0 : Eis)
    (hcM : c0∣M) (hma : M∣a-a0) : symbol a c0=symbol a0 c0 :=
  symbol_congr (hcM.trans hma)

theorem norm_embedded_cubic_symbol (x a : Eis)
    (ha : lambda^2∣a-1) (hcop : IsCoprime x a) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol x a)‖=1 := by
  have hcube : ConcreteTraceCRT.eisEmbedding (symbol x a)^3=1 := by
    rw [←map_pow,symbol_cube_of_isCoprime x a ha hcop,map_one]
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm hcube

theorem norm_A3_principal_fixed_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (ha : lambda^2∣a-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol c0 a)‖=1 := by
  apply norm_embedded_cubic_symbol _ _ ha
  refine ⟨-b*r,d,?_⟩
  linear_combination hdet

theorem norm_A3_ramified_fixed_factor (a b c0 r d u : Eis)
    (hdet : a*d-b*(u*(c0*r))=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣a-u*b-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b)*symbol c0 a)‖=1 := by
  have hfirst : ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b))‖=1 := by
    apply norm_embedded_cubic_symbol _ _ hA
    refine ⟨b*(c0*r-d),d,?_⟩
    linear_combination hdet
  have hsecond : ‖ConcreteTraceCRT.eisEmbedding (symbol c0 a)‖=1 := by
    apply norm_embedded_cubic_symbol _ _ ha
    refine ⟨-b*u*r,d,?_⟩
    linear_combination hdet
  rw [map_mul,norm_mul,hfirst,hsecond,one_mul]

theorem norm_A3_unramified_fixed_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (hc : lambda^2∣c0-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol a c0)‖=1 := by
  apply norm_embedded_cubic_symbol _ _ hc
  refine ⟨d,-b*r,?_⟩
  linear_combination hdet

end ShortDraftCusp

open scoped BigOperators Classical
namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
local notation "Eis" => ActualEisensteinCubic.O

lemma cubicUnitGaussSum_norm_le (h c:Eis) (hc:c≠0) (hp:lambda^2∣c-1):
    ‖cubicUnitGaussSum h c‖≤Ideal.absNorm (Ideal.span {c}):=by
  let:Finite (Eis⧸Ideal.span {c}):=finite_quotient_span hc
  let:Fintype (Eis⧸Ideal.span {c}):=Fintype.ofFinite _
  let:Fintype (CubicUnitResidue c):=Fintype.ofFinite _
  have hs (r:CubicUnitResidue c):
      ‖eisEmbedding (symbol (GaussianShiftedPartition.representative c r.val) c)‖=1:=by
    apply Complex.norm_eq_one_of_pow_eq_one (n:=3) _ (by decide)
    rw [←map_pow,symbol_cube_of_isCoprime _ c hp _ ,map_one]
    apply IsCoprime.symm
    apply (isUnit_quotient_span_iff c _).mp
    simpa only [GaussianShiftedPartition.representative_spec] using r.2
  rw [cubicUnitGaussSum,tsum_fintype]
  calc
    _≤∑r:CubicUnitResidue c,‖eisEmbedding (symbol (GaussianShiftedPartition.representative c r.val) c)*
      residueAdditive (3*h) c (GaussianShiftedPartition.representative c r.val)‖:=norm_sum_le _ _
    _=(Fintype.card (CubicUnitResidue c):ℝ):=by
      simp only [norm_mul,hs,residueAdditive,breveE_norm,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    _≤(Fintype.card (Eis⧸Ideal.span {c}):ℝ):=by
      exact_mod_cast Fintype.card_subtype_le (fun r=>IsUnit r)
    _=Ideal.absNorm (Ideal.span {c}):=by
      simp only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem unramifiedCubicGaussSeries_summable_norm (s:ℂ) (hs:2<s.re) (h:Eis):
    Summable (fun I:GoodIdeal=>‖(Ideal.absNorm I.val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator I.val)‖):=by
  have hs':1<(s-1).re:=by simp only [Complex.sub_re,Complex.one_re];linarith
  apply ((unramifiedNormWeight_summable_norm (s-1) hs').subtype
    (fun I:Ideal Eis=>primaryGenerator I≠0)).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro I
  dsimp only [Function.comp_def]
  simp only [unramifiedNormWeight_shift,norm_mul,Complex.norm_natCast,
    unramifiedNormWeight_of_good s I.val I.2]
  have hg:=cubicUnitGaussSum_norm_le h (primaryGenerator I.val) I.2
    (primaryGenerator_spec I.val I.2).2
  rw [(primaryGenerator_spec I.val I.2).1] at hg
  nlinarith [norm_nonneg ((Ideal.absNorm I.val:ℂ)^(-s))]

abbrev PrimeDeletedIdeal (p:Eis):={I:GoodIdeal//¬(Ideal.span {p}:Ideal Eis)∣I.val}

def unramifiedPrimeDeletedSeries (p:Eis) (s:ℂ) (h:Eis):ℂ:=
  ∑'I:PrimeDeletedIdeal p,(Ideal.absNorm I.val.val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator I.val.val)

lemma primaryGenerator_pow (I:Ideal Eis) (n:ℕ):
    primaryGenerator (I^n)=primaryGenerator I^n:=
  map_pow primaryGeneratorHom I n

lemma gaussPrimeIdeal_prime (p:Eis) (hp:Prime p):Prime (Ideal.span {p}:Ideal Eis):=
  Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)

def gaussPrimeFactorMap (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (q:ℕ×PrimeDeletedIdeal p):GoodIdeal:=
  ⟨(Ideal.span {p})^q.1*q.2.val.val,by
    rw [primaryGenerator_mul,primaryGenerator_pow,primaryGenerator_span p hp.ne_zero hprimary]
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) q.2.val.2⟩

lemma gaussPrimeFactorMap_bijective (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    Function.Bijective (gaussPrimeFactorMap p hp hprimary):=by
  let P:Ideal Eis:=Ideal.span {p}
  have hP:Prime P:=gaussPrimeIdeal_prime p hp
  constructor
  · rintro ⟨n,I⟩ ⟨m,J⟩ heq
    have hh:P^n*I.val.val=P^m*J.val.val:=congrArg Subtype.val heq
    have hn:n=m:=by
      have hm:=congrArg (multiplicity P) hh
      rw [prime_power_remainder_multiplicity hP I.2,
        prime_power_remainder_multiplicity hP J.2] at hm
      exact hm
    subst m
    have hIJ:I=J:=Subtype.ext (Subtype.ext
      (mul_left_cancel₀ (pow_ne_zero n hP.ne_zero) hh))
    subst J
    rfl
  · intro I
    obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hP
      (primaryGenerator_ne_zero_ideal I.val I.2)).exists_eq_pow_mul_and_not_dvd
    have hgood:primaryGenerator J≠0:=by
      intro hzero
      apply I.2
      rw [hJ,primaryGenerator_mul,hzero,mul_zero]
    refine ⟨(multiplicity P I.val,⟨⟨J,hgood⟩,hnot⟩),?_⟩
    exact Subtype.ext hJ.symm

def gaussPrimeFactorEquiv (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    ℕ×PrimeDeletedIdeal p≃GoodIdeal:=
  Equiv.ofBijective (gaussPrimeFactorMap p hp hprimary)
    (gaussPrimeFactorMap_bijective p hp hprimary)

lemma primeDeleted_generator_coprime (p:Eis) (hp:Prime p) (I:PrimeDeletedIdeal p):
    IsCoprime p (primaryGenerator I.val.val):=by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  apply I.2
  rw [Ideal.dvd_iff_le,←(primaryGenerator_spec I.val.val I.val.2).1,
    Ideal.span_singleton_le_span_singleton]
  exact hd

lemma primary_pow_congruence (p:Eis) (hprimary:lambda^2∣p-1) (n:ℕ):
    lambda^2∣p^n-1:=by
  simpa only [one_pow] using hprimary.trans (sub_dvd_pow_sub_pow p 1 n)

lemma gaussPrimeFactor_term (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (s:ℂ) (h:Eis) (n:ℕ) (I:PrimeDeletedIdeal p):
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary (n,I)).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary (n,I)).val)=
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n*cubicUnitGaussSum h (p^n)*
      ((Ideal.absNorm I.val.val:ℂ)^(-s)*cubicUnitGaussSum (h*p^n) (primaryGenerator I.val.val)):=by
  change (Ideal.absNorm ((Ideal.span {p})^n*I.val.val):ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator ((Ideal.span {p})^n*I.val.val))=_
  rw [primaryGenerator_mul,primaryGenerator_pow,primaryGenerator_span p hp.ne_zero hprimary,
    cubicUnitGaussSum_coprime_product h (p^n) (primaryGenerator I.val.val)
      (pow_ne_zero _ hp.ne_zero) I.val.2 (primary_pow_congruence p hprimary n)
      (primaryGenerator_spec I.val.val I.val.2).2 (primeDeleted_generator_coprime p hp I).pow_left,
    map_mul,map_pow,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have he:((Ideal.absNorm (Ideal.span {p})^n:ℕ):ℂ)^(-s)=
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n:=by
    rw [Nat.cast_pow,←Complex.natCast_cpow_natCast_mul,Complex.cpow_nat_mul]
  rw [he]
  ring

theorem unramifiedCubicGaussSeries_prime_reindex (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis):
    unramifiedCubicGaussSeries s h=
      ∑'n:ℕ,((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n*cubicUnitGaussSum h (p^n)*
        unramifiedPrimeDeletedSeries p s (h*p^n):=by
  have hsum:Summable (fun I:GoodIdeal=>(Ideal.absNorm I.val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator I.val)):=
    (unramifiedCubicGaussSeries_summable_norm s hs h).of_norm
  have hpull:=(gaussPrimeFactorEquiv p hp hprimary).summable_iff.mpr hsum
  change Summable (fun q:ℕ×PrimeDeletedIdeal p=>
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary q).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary q).val)) at hpull
  rw [unramifiedCubicGaussSeries,←(gaussPrimeFactorEquiv p hp hprimary).tsum_eq]
  change (∑'q:ℕ×PrimeDeletedIdeal p,
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary q).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary q).val))=_
  rw [hpull.tsum_prod]
  apply tsum_congr
  intro n
  change (∑'I:PrimeDeletedIdeal p,(Ideal.absNorm (gaussPrimeFactorMap p hp hprimary (n,I)).val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary (n,I)).val))=_
  simp_rw [gaussPrimeFactor_term p hp hprimary s h n]
  exact tsum_mul_left

lemma unramifiedPrimeDeletedSeries_cube_shift (p:Eis) (hp:Prime p) (s:ℂ) (h:Eis):
    unramifiedPrimeDeletedSeries p s (h*p^3)=unramifiedPrimeDeletedSeries p s h:=by
  apply tsum_congr
  intro I
  congr 1
  exact cubicUnitGaussSum_cube_shift h _ p I.val.2
    (primaryGenerator_spec I.val.val I.val.2).2 (primeDeleted_generator_coprime p hp I).symm

end CubicEisenstein

end

end OAI
end OAIOriginalModule0277

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.PrimePowerGaussSums
Source SHA256: f08de15f301586d79eb28505f401324b83df709a7f4e374b47b13d1d37699af4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0278


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
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

@[simp] lemma cubicUnitGaussSum_one (h:Eis):cubicUnitGaussSum h 1=1:=by
  let:Subsingleton (Eis⧸Ideal.span {(1:Eis)}):=
    Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let r:CubicUnitResidue (1:Eis):=⟨1,isUnit_one⟩
  rw [cubicUnitGaussSum,tsum_eq_single r (fun b hb=>False.elim (hb (Subsingleton.elim b r)))]
  rw [symbol_one,map_one,one_mul,
    residueAdditive_three_congr h 1 _ 0 one_ne_zero (one_dvd _)]
  simp only [residueAdditive,map_zero,mul_zero,zero_div,AddChar.map_zero_eq_one]

lemma cubicUnitGaussSum_frequency_dvd (h c:Eis) (hc:c≠0) (hch:c∣h):
    cubicUnitGaussSum h c=cubicUnitGaussSum 0 c:=
  cubicUnitGaussSum_frequency_congr h 0 c hc (by simpa only [sub_zero] using hch)

lemma cubicUnitGaussSum_prime_power_zero (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) (n:ℕ):
    cubicUnitGaussSum 0 (p^(n+1))=
      if 3∣n+1 then (Ideal.absNorm (Ideal.span {p}):ℂ)^n*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)-1) else 0:=by
  have he:=cubicUnitGaussSum_prime_power_lift p hp hprimary n 0
  simp only [mul_zero] at he
  rw [he,primeCubicGauss_of_dvd p hp hprimary (n+1) 0 (dvd_zero _)]
  split_ifs <;>ring

lemma cubicUnitGaussSum_prime_power_too_large (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (h:Eis) (hph:¬p∣h) (a k:ℕ) (hk:a+1<k):
    cubicUnitGaussSum (h*p^a) (p^k)=0:=by
  by_contra hG
  cases k with
  | zero=>omega
  | succ n=>
    have hd:=cubicUnitGaussSum_prime_power_support p hp hprimary n (h*p^a) hG
    have hd':p^(a+1)∣p^a*h:=by
      rw [mul_comm]
      exact (pow_dvd_pow p (by omega:a+1≤n)).trans hd
    rw [pow_succ] at hd'
    exact hph ((mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)).mp hd')

lemma unramifiedPrimeDeletedSeries_pow_mod (p:Eis) (hp:Prime p) (s:ℂ) (h:Eis) (n:ℕ):
    unramifiedPrimeDeletedSeries p s (h*p^n)=
      unramifiedPrimeDeletedSeries p s (h*p^(n%3)):=by
  apply tsum_congr
  intro I
  congr 1
  have he:p^n=p^(n%3)*(p^(n/3))^3:=by
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  rw [he,←mul_assoc]
  exact cubicUnitGaussSum_cube_shift _ _ _ I.val.2
    (primaryGenerator_spec I.val.val I.val.2).2
    (primeDeleted_generator_coprime p hp I).symm.pow_right

theorem unramifiedCubicGaussSeries_prime_finite (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h) (a:ℕ):
    unramifiedCubicGaussSeries s (h*p^a)=
      ∑k∈Finset.range (a+2),((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^k*
        cubicUnitGaussSum (h*p^a) (p^k)*unramifiedPrimeDeletedSeries p s (h*p^a*p^k):=by
  rw [unramifiedCubicGaussSeries_prime_reindex p hp hprimary s hs]
  apply tsum_eq_sum
  intro k hk
  have hk':a+1<k:=by
    have hh: a+2≤k:=by simpa only [Finset.mem_range,not_lt] using hk
    omega
  rw [cubicUnitGaussSum_prime_power_too_large p hp hprimary h hph a k hk',mul_zero,zero_mul]

lemma unramifiedCubicGaussSeries_prime_zero_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s h=unramifiedPrimeDeletedSeries p s h+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h*
        unramifiedPrimeDeletedSeries p s (h*p):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 0
  simpa only [pow_zero,pow_one,mul_one,cubicUnitGaussSum_one,
    Finset.sum_range_succ,Finset.sum_range_zero,zero_add,one_mul,
    primeCubicGauss_one_eq] using he

lemma unramifiedCubicGaussSeries_prime_one_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p)=unramifiedPrimeDeletedSeries p s (h*p)+
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^2*(Ideal.absNorm (Ideal.span {p}):ℂ)*
        primeCubicGauss p hp hprimary 2 h*unramifiedPrimeDeletedSeries p s h:=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 1
  have hg1:cubicUnitGaussSum (h*p) p=0:=by
    rw [cubicUnitGaussSum_frequency_dvd _ p hp.ne_zero (dvd_mul_left p h)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p) (p^2)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)*primeCubicGauss p hp hprimary 2 h:=by
    simpa only [pow_one,mul_comm p h] using cubicUnitGaussSum_prime_power_lift p hp hprimary 1 h
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,mul_zero,zero_mul,add_zero,hg2] at he
  have hr:h*p*p^2=h*p^3:=by ring
  rw [hr,unramifiedPrimeDeletedSeries_cube_shift p hp] at he
  exact he.trans (by ring)

lemma unramifiedCubicGaussSeries_prime_three_power (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p^3)=
      (1+((Ideal.absNorm (Ideal.span {p}):ℂ)^3-(Ideal.absNorm (Ideal.span {p}):ℂ)^2)*
        ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*unramifiedPrimeDeletedSeries p s h+
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^4*
        primeCubicGauss p hp hprimary 1 h*unramifiedPrimeDeletedSeries p s (h*p):=by
  have he:=unramifiedCubicGaussSeries_prime_finite p hp hprimary s hs h hph 3
  have hg0 (k:ℕ) (hk:k≤3):cubicUnitGaussSum (h*p^3) (p^k)=cubicUnitGaussSum 0 (p^k):=
    cubicUnitGaussSum_frequency_dvd _ _ (pow_ne_zero _ hp.ne_zero)
      ((pow_dvd_pow p hk).trans (dvd_mul_left (p^3) h))
  have hg1:cubicUnitGaussSum (h*p^3) p=0:=by
    have hh:=hg0 1 (by omega)
    simp only [pow_one] at hh
    rw [hh]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 0
  have hg2:cubicUnitGaussSum (h*p^3) (p^2)=0:=by
    rw [hg0 2 (by omega)]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 1
  have hg3:cubicUnitGaussSum (h*p^3) (p^3)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1):=by
    rw [hg0 3 le_rfl]
    simpa using cubicUnitGaussSum_prime_power_zero p hp hprimary 2
  have hg4:cubicUnitGaussSum (h*p^3) (p^4)=
      (Ideal.absNorm (Ideal.span {p}):ℂ)^3*primeCubicGauss p hp hprimary 1 h:=by
    have hh:=cubicUnitGaussSum_prime_power_lift p hp hprimary 3 h
    rw [primeCubicGauss_mod_three p hp hprimary 4] at hh
    simpa only [mul_comm (p^3) h,Nat.reduceMod] using hh
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    cubicUnitGaussSum_one,mul_one,one_mul,hg1,hg2,hg3,hg4,mul_zero,zero_mul,add_zero] at he
  have hr6:h*p^3*p^3=h*p^6:=by ring
  have hr7:h*p^3*p^4=h*p^7:=by ring
  rw [unramifiedPrimeDeletedSeries_cube_shift p hp,hr6,hr7,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 6,
    unramifiedPrimeDeletedSeries_pow_mod p hp s h 7] at he
  norm_num only [Nat.reduceMod,pow_zero,pow_one,mul_one] at he
  exact he.trans (by ring)

theorem unramifiedCubicGaussSeries_prime_recurrence (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis) (hph:¬p∣h):
    unramifiedCubicGaussSeries s (h*p^3)=
      (1+(Ideal.absNorm (Ideal.span {p}):ℂ)^3*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3)*
        unramifiedCubicGaussSeries s h-
      (Ideal.absNorm (Ideal.span {p}):ℂ)^(-s)*primeCubicGauss p hp hprimary 1 h*
        unramifiedCubicGaussSeries s (h*p):=by
  rw [unramifiedCubicGaussSeries_prime_three_power p hp hprimary s hs h hph,
    unramifiedCubicGaussSeries_prime_zero_power p hp hprimary s hs h hph,
    unramifiedCubicGaussSeries_prime_one_power p hp hprimary s hs h hph]
  have hg:=primeCubicGauss_one_mul_two p hp hprimary h hph
  linear_combination ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^3*
    (Ideal.absNorm (Ideal.span {p}):ℂ)*unramifiedPrimeDeletedSeries p s h*hg

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

structure SubexponentialBesselCoefficients where
  value : ActualEisensteinCubic.O→ℂ
  growth : ∀epsilon : ℝ,0<epsilon → ∃C : ℝ,0≤C ∧ ∀h : ActualEisensteinCubic.O,h≠0 →
    ‖value h‖≤C*Real.exp (epsilon*‖cuspFrequency h‖)

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def term (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : ℂ :=
  if h=0 then 0 else (coeff.value h/cubicBesselNormalizer h)*(p.1:ℂ)^(2/3:ℂ)*
    sourceFourierKernel (4/3) (cuspFrequency h*p.1)*ShortDraftTrace.breveE (cuspFrequency h*p.2)

def amplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else coeff.value h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma term_bessel (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.term h (v,z)=coeff.value h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [term,ite_eq_right hh]
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hn := cubicBesselNormalizer_ne_zero h hh
  have hp : (v:ℂ)^3*(v:ℂ)^(-(4/3:ℂ)-1)=(v:ℂ)^(2/3:ℂ) := by
    rw [←Complex.cpow_ofNat (v:ℂ) 3,←Complex.cpow_add _ _ hv0]
    congr 1
    ring
  calc
    _ = (coeff.value h/cubicBesselNormalizer h)*(v:ℂ)^3*
        ((v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z) := by rw [←hp];ring
    _ = _ := by
      rw [sourceFourierKernel_cubic_height h hh v hv]
      field_simp

lemma term_eq_amplitude (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (z : ℂ) :
    coeff.term h (v,z)=coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  by_cases hh : h=0
  · simp only [term,amplitude,ite_eq_left hh,zero_mul]
  · rw [coeff.term_bessel h hh v hv z,amplitude,ite_eq_right hh]

lemma term_continuousOn (h : ActualEisensteinCubic.O) :
    ContinuousOn (coeff.term h) {p : ℝ × ℂ | 0<p.1} := by
  unfold term
  by_cases hh : h=0
  · simp only [ite_eq_left hh]
    exact continuousOn_const
  simp only [ite_eq_right hh]
  intro p hp
  change 0<p.1 at hp
  have hpow : ContinuousAt (fun q : ℝ × ℂ => (q.1:ℂ)^(2/3:ℂ)) p :=
    (Complex.continuousAt_ofReal_cpow_const p.1 (2/3:ℂ) (Or.inr hp.ne')).comp continuousAt_fst
  have hsource : ContinuousAt (fun q : ℝ × ℂ => sourceFourierKernel (4/3) (cuspFrequency h*q.1)) p :=
    (sourceFourierKernel_continuous_freq (4/3) (by norm_num)).continuousAt.comp (by fun_prop)
  have hphase : Continuous (fun q : ℝ × ℂ => ShortDraftTrace.breveE (cuspFrequency h*q.2)) := by
    change Continuous (fun q : ℝ × ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((cuspFrequency h*q.2)+starRingEnd ℂ (cuspFrequency h*q.2))))
    fun_prop
  exact (((continuousAt_const.mul hpow).mul hsource).mul hphase.continuousAt).continuousWithinAt

lemma slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖coeff.term h p‖≤C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hb : 0<b := ha.trans_le hab
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  let delta : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  have hdelta : 0<delta := by dsimp [delta];positivity
  have hCu := cubicBesselUpperAway_pos delta hdelta
  obtain ⟨C,hC,hcoeff⟩ := coeff.growth (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*b*cubicBesselUpperAway delta,by positivity,?_⟩
  intro h p hp
  have hv : 0<p.1 := ha.trans_le hp.1
  by_cases hh : h=0
  · simp only [term,ite_eq_left hh,norm_zero]
    positivity
  have hr : 0<‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h hh)
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*p.1 := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hp.1 ha.le (norm_nonneg _)
    dsimp [delta]
    nlinarith [mul_le_mul_of_nonneg_left hmul (by positivity : 0≤4*Real.pi)]
  rw [show p=(p.1,p.2) from rfl,coeff.term_bessel h hh _ hv,
    norm_mul,norm_mul,norm_mul,breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*b*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*p.1)/2)) :=
      mul_le_mul (mul_le_mul (hcoeff h hh) hp.2 hv.le (by positivity))
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*b*cubicBesselUpperAway delta)*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*p.1)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*p.1)/2=
        -(4*Real.pi*‖cuspFrequency h‖*p.1/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hp.1 (mul_pos Real.pi_pos hr).le]

lemma summable (p : ℝ × ℂ) (hp : 0<p.1) : Summable (fun h : ActualEisensteinCubic.O => coeff.term h p) := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound p.1 p.1 hp le_rfl
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h p ⟨le_rfl,le_rfl⟩)
    ((summable_exp_neg_cuspFrequency_norm (Real.pi*p.1) (mul_pos Real.pi_pos hp)).mul_left C)

def series (p : ℝ × ℂ) : ℂ := ∑'h : ActualEisensteinCubic.O,coeff.term h p

lemma series_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn coeff.series {p : ℝ × ℂ | p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  apply continuousOn_tsum (u := fun h : ActualEisensteinCubic.O => C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖))
  · intro h
    exact (coeff.term_continuousOn h).mono (fun p hp => ha.trans_le hp.1)
  · exact (summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C
  · exact hbound

lemma series_continuousOn : ContinuousOn coeff.series {p : ℝ × ℂ | 0<p.1} := by
  intro p hp
  change 0<p.1 at hp
  have hclosed := coeff.series_continuousOn_slab (p.1/2) (2*p.1) (by linarith) (by linarith)
  have hnb : {q : ℝ × ℂ | q.1∈Set.Icc (p.1/2) (2*p.1)}∈𝓝 p :=
    continuousAt_fst.tendsto.eventually (Icc_mem_nhds (by linarith) (by linarith))
  exact (hclosed.continuousAt hnb).continuousWithinAt

lemma series_uniform (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    TendstoUniformlyOn (fun t : Finset ActualEisensteinCubic.O => fun p : ℝ × ℂ => ∑h∈t,coeff.term h p)
      coeff.series atTop {p : ℝ × ℂ | p.1∈Set.Icc a b} := by
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound a b ha hab
  exact tendstoUniformlyOn_tsum
    ((summable_exp_neg_cuspFrequency_norm (Real.pi*a) (mul_pos Real.pi_pos ha)).mul_left C) hbound

lemma series_bessel (v : ℝ) (hv : 0<v) (z : ℂ) :
    coeff.series (v,z)=∑'h : ActualEisensteinCubic.O,coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  exact tsum_congr (fun h => coeff.term_eq_amplitude v hv h z)

lemma series_period (v : ℝ) (z : ℂ) (n : ActualEisensteinCubic.O) :
    coeff.series (v,z+3*ConcreteTraceCRT.eisEmbedding n)=coeff.series (v,z) := by
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · simp only [term,ite_eq_left hh]
  simp only [term,ite_eq_right hh]
  rw [mul_add,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

def function (w : HyperbolicSpace) : ℂ := coeff.series (hyperbolicHeight w,hyperbolicHorizontal w)

lemma function_continuous : Continuous coeff.function := by
  apply continuous_iff_continuousAt.mpr
  intro w
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  have hp : (hyperbolicHeight w,hyperbolicHorizontal w)∈{p : ℝ × ℂ | 0<p.1} := hyperbolicHeight_pos w
  exact (coeff.series_continuousOn.continuousAt (hopen.mem_nhds hp)).comp
    (f := fun u : HyperbolicSpace => (hyperbolicHeight u,hyperbolicHorizontal u))
    (hyperbolicHeight_continuous.prodMk hyperbolicHorizontal_continuous).continuousAt

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma series_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,coeff.series (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v k := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
    ShortDraftTrace.breveE (-cuspFrequency k*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => coeff.amplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*z)+starRingEnd ℂ (cuspFrequency h*z)))*
      Complex.exp (2*Real.pi*Complex.I*((-cuspFrequency k*z)+starRingEnd ℂ (-cuspFrequency k*z))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
    change ‖(coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z))*
      ShortDraftTrace.breveE (-cuspFrequency k*z)‖≤_
    rw [←coeff.term_eq_amplitude v hv h z,norm_mul,breveE_norm,mul_one]
    exact hbound h (v,z) ⟨le_rfl,le_rfl⟩
  have hi (h : ActualEisensteinCubic.O) : IntegrableOn (f h) periodDomain volume :=
    (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hfbound h))
  have hnorm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,‖f h z‖)≤
      volume.real periodDomain*(C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) := by
    have hh := integral_mono_ae (hi h).norm (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)))
      (Eventually.of_forall (hfbound h))
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hs : Summable (fun h : ActualEisensteinCubic.O => ∫z in periodDomain,‖f h z‖) := by
    apply Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
    exact ((summable_exp_neg_cuspFrequency_norm (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
      (volume.real periodDomain)
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=
      if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v h else 0 := by
    change (∫z in periodDomain,coeff.amplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=_
    simp_rw [mul_assoc]
    rw [integral_const_mul,integral_cusp_character_product]
    split_ifs <;> ring
  calc
    _ = ∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        change (∑'h : ActualEisensteinCubic.O,coeff.term h (v,z))*ShortDraftTrace.breveE (-cuspFrequency k*z)=_
        rw [←tsum_mul_right]
        apply tsum_congr
        intro h
        rw [coeff.term_eq_amplitude v hv h z])
    _ = ∑'h : ActualEisensteinCubic.O,∫z in periodDomain,f h z := (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = ∑'h : ActualEisensteinCubic.O,if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ)*coeff.amplitude v h else 0 := tsum_congr hterm
    _ = _ := by simp

lemma series_height_continuous (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ => coeff.series (v,z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hopen : IsOpen {p : ℝ × ℂ | 0<p.1} := isOpen_lt continuous_const continuous_fst
  exact (coeff.series_continuousOn.continuousAt (hopen.mem_nhds hv)).comp
    (f := fun z : ℂ => (v,z)) (by fun_prop)

def fullFunction (constant : ℂ) (w : HyperbolicSpace) : ℂ :=
  constant*(hyperbolicHeight w:ℂ)^(2/3:ℂ)+coeff.function w

lemma fullFunction_continuous (constant : ℂ) : Continuous (coeff.fullFunction constant) := by
  have hp : Continuous (fun w : HyperbolicSpace => (hyperbolicHeight w:ℂ)^(2/3:ℂ)) := by
