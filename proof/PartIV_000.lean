import core.OAI08
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import PartsI_III

/-! Part IV of combine_v2-2.tex: exact scalar certificates, extended physical
moment induction, actual source counts/probes, and L-function conclusions.
Consolidation preserves the proof bodies; lexical spacing and disambiguated
PrimeIdeal references accommodate the common import environment. -/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
set_option linter.unnecessarySeqFocus false

/- BEGIN consolidated Optimality.lean -/
section PartIVBlock0

/-! Exact real-algebraic core of Part IV. This file proves the dual lower
bound, isolates the fixed-point root, and proves endpoint-compatible
optimality. It makes no assertion about analytic moment estimates. -/
namespace CombineV22Optimality
noncomputable section
set_option linter.unnecessarySeqFocus false

def cubic (x : ℝ) : ℝ := 1188*x^3 - 2160*x^2 + 171*x + 190
def denom (x : ℝ) : ℝ := 36*x^2 - 78*x + 25
def kap (x : ℝ) : ℝ := (18*x^2 - 57*x + 20) / (6*denom x)
def boundary (x : ℝ) : ℝ := (18*x+7)/(18*x+9)
def length (x : ℝ) : ℝ := (5-6*x)/(9+18*x)
def low₀ (M l : ℝ) : ℝ := 5/6+M/12-l/6
def lowK (M l : ℝ) : ℝ := 1/3+7*M/12+l/3
def high (x M l : ℝ) : ℝ := 1+x-(1+x)*M/2+x*l
def critical (k x : ℝ) : ℝ :=
  (216*k-18)*x^2-(468*k-57)*x+150*k-20

theorem denom_pos {x : ℝ} (hx : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ)) :
    0 < denom x := by
  dsimp [denom]
  have := hx.2
  nlinarith [sq_nonneg (x-39/100)]

theorem boundary_den_pos {x : ℝ}
    (hx : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ)) : 0 < 18*x+9 := by
  have := hx.1
  linarith

theorem dual_identity (x M l : ℝ) (hx : 18*x+9 ≠ 0) :
    ((4+18*x)*low₀ M l+2*lowK M l+3*high x M l)/(18*x+9)
      = boundary x := by
  unfold low₀ lowK high boundary
  field_simp
  <;> ring

theorem dual_lower_bound (x M l B : ℝ)
    (hx : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ))
    (h₀ : low₀ M l ≤ B) (hK : lowK M l ≤ B) (hH : high x M l ≤ B) :
    boundary x ≤ B := by
  have hd := boundary_den_pos hx
  have hw : 0 ≤ 4+18*x := by have := hx.1; linarith
  have hweighted := mul_le_mul_of_nonneg_left h₀ hw
  rw [← dual_identity x M l (ne_of_gt hd)]
  apply (div_le_iff₀ hd).2
  nlinarith

theorem equal_branches (x : ℝ) (hx : 18*x+9 ≠ 0) :
    low₀ (1-length x) (length x) = boundary x ∧
    lowK (1-length x) (length x) = boundary x ∧
    high x (1-length x) (length x) = boundary x := by
  have h' : 9+18*x ≠ 0 := by simpa [add_comm] using hx
  unfold low₀ lowK high length boundary
  ring_nf at hx h'
  constructor
  · ring_nf
    field_simp [hx,h'] <;> ring
  constructor <;> ring_nf <;> field_simp [hx,h'] <;> ring

theorem fixed_point_identity (x : ℝ) (hx : 18*x+9 ≠ 0)
    (hd : denom x ≠ 0) :
    kap x-(2*boundary x-1) = -cubic x/(18*(2*x+1)*denom x) := by
  have hx' : 2*x+1 ≠ 0 := by intro h; apply hx; linarith
  have hn : 1+x*2 ≠ 0 := by simpa [add_comm,mul_comm] using hx'
  have hn' : 9+x*18 ≠ 0 := by simpa [add_comm,mul_comm] using hx
  unfold kap boundary cubic
  field_simp [hx,hx',hn,hn',hd]
  unfold denom
  ring_nf
  field_simp [hn]
  ring

theorem critical_iff_kap (k x : ℝ) (hd : denom x ≠ 0) :
    critical k x = 0 ↔ k = kap x := by
  unfold critical kap
  have hd' : 6*denom x ≠ 0 := mul_ne_zero (by norm_num) hd
  rw [eq_div_iff hd']
  unfold denom
  constructor <;> intro h <;> nlinarith [h]

theorem cubic_strictAnti : StrictAntiOn cubic (Set.Icc (19/50:ℝ) (39/100:ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := by have := hx.1; linarith
  have hy0 : 0 ≤ y := by have := hy.1; linarith
  have hx2 := mul_self_le_mul_self hx0 hx.2
  have hy2 := mul_self_le_mul_self hy0 hy.2
  have hxy2 := mul_le_mul hx.2 hy.2 hy0 (by norm_num : (0:ℝ) ≤ 39/100)
  have hfactor : 1188*(y^2+y*x+x^2)-2160*(y+x)+171 < 0 := by
    have := hx.1
    have := hy.1
    nlinarith
  have hprod := mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hfactor
  unfold cubic
  nlinarith [hprod]

theorem isolated_root_exists : ∃ x ∈ Set.Icc (38858/100000:ℝ) (38859/100000:ℝ),
    cubic x = 0 := by
  have hc : ContinuousOn cubic (Set.Icc (38858/100000:ℝ) (38859/100000:ℝ)) := by
    unfold cubic
    fun_prop
  have hL : 0 ≤ cubic (38858/100000) := by norm_num [cubic]
  have hU : cubic (38859/100000) ≤ 0 := by norm_num [cubic]
  have hh := intermediate_value_Icc' (by norm_num : (38858/100000:ℝ) ≤ 38859/100000) hc
  exact hh ⟨hU,hL⟩

def xiInf : ℝ := Classical.choose isolated_root_exists
theorem xiInf_mem_small : xiInf ∈ Set.Icc (38858/100000:ℝ) (38859/100000:ℝ) :=
  (Classical.choose_spec isolated_root_exists).1
theorem cubic_xiInf : cubic xiInf = 0 :=
  (Classical.choose_spec isolated_root_exists).2
theorem xiInf_mem : xiInf ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
  have h := xiInf_mem_small
  constructor <;> linarith [h.1,h.2]

theorem cubic_nonpos_iff (x : ℝ)
    (hx : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ)) :
    cubic x ≤ 0 ↔ xiInf ≤ x := by
  constructor
  · intro hp
    by_contra hn
    have hs := cubic_strictAnti hx xiInf_mem (lt_of_not_ge hn)
    rw [cubic_xiInf] at hs
    linarith
  · intro h
    rcases eq_or_lt_of_le h with he | hl
    · simpa [← he] using le_of_eq cubic_xiInf
    · have hs := cubic_strictAnti xiInf_mem hx hl
      rw [cubic_xiInf] at hs
      exact le_of_lt hs

theorem root_unique (x : ℝ) (hx : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ))
    (hp : cubic x = 0) : x = xiInf := by
  exact cubic_strictAnti.injOn hx xiInf_mem (hp.trans cubic_xiInf.symm)

theorem boundary_monotone : MonotoneOn boundary (Set.Icc (19/50:ℝ) (39/100:ℝ)) := by
  intro x hx y hy hxy
  unfold boundary
  apply (div_le_div_iff₀ (boundary_den_pos hx) (boundary_den_pos hy)).2
  nlinarith

theorem kap_strictMono : StrictMonoOn kap (Set.Icc (19/50:ℝ) (39/100:ℝ)) := by
  intro x hx y hy hxy
  have hd₁ : 0 < 6*denom x := mul_pos (by norm_num) (denom_pos hx)
  have hd₂ : 0 < 6*denom y := mul_pos (by norm_num) (denom_pos hy)
  have hx0 : 0 ≤ x := by have := hx.1; linarith
  have hxy0 := mul_le_mul hx.1 hy.1 (by norm_num : (0:ℝ) ≤ 19/50) hx0
  have hfactor : 0 < 24*x*y-10*x-10*y+5 := by
    have := hx.2
    have := hy.2
    nlinarith
  have hp := mul_pos (sub_pos.mpr hxy) hfactor
  unfold kap
  apply (div_lt_div_iff₀ hd₁ hd₂).2
  unfold denom
  nlinarith [hp]

theorem critical_root_exists (k : ℝ) (hk : k ∈ Set.Icc (13/18:ℝ) 1) :
    ∃ x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ), critical k x = 0 := by
  have hL : 0 ≤ critical k (19/50) := by
    have := hk.1
    have := hk.2
    norm_num [critical]
    nlinarith
  have hU : critical k (39/100) ≤ 0 := by
    have := hk.1
    have := hk.2
    norm_num [critical]
    nlinarith
  have hc : ContinuousOn (critical k) (Set.Icc (19/50:ℝ) (39/100:ℝ)) := by
    unfold critical
    fun_prop
  exact intermediate_value_Icc' (by norm_num : (19/50:ℝ) ≤ 39/100) hc ⟨hU,hL⟩

theorem critical_root_unique (k x y : ℝ)
    (hx : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ))
    (hy : y ∈ Set.Icc (19/50:ℝ) (39/100:ℝ))
    (hqx : critical k x = 0) (hqy : critical k y = 0) : x = y := by
  have hkx := (critical_iff_kap k x (ne_of_gt (denom_pos hx))).1 hqx
  have hky := (critical_iff_kap k y (ne_of_gt (denom_pos hy))).1 hqy
  exact kap_strictMono.injOn hx hy (hkx.symm.trans hky)

theorem root_fixed_point : kap xiInf = 2*boundary xiInf-1 := by
  have hi := fixed_point_identity xiInf (ne_of_gt (boundary_den_pos xiInf_mem))
    (ne_of_gt (denom_pos xiInf_mem))
  rw [cubic_xiInf] at hi
  simp only [neg_zero, zero_div] at hi
  linarith

/-- Actual three affine constraints plus endpoint compatibility force the
limiting lower bound. The root hypothesis is its explicit quadratic equation,
with an independently proved nonempty, unique rational isolating interval. -/
theorem endpoint_compatible_optimality (k x M l B : ℝ)
    (hx : x ∈ Set.Icc (19/50:ℝ) (39/100:ℝ))
    (hroot : critical k x = 0)
    (h₀ : low₀ M l ≤ B) (hK : lowK M l ≤ B) (hH : high x M l ≤ B)
    (hcompat : B ≤ (1+k)/2) : kap xiInf ≤ k ∧ boundary xiInf ≤ B := by
  have hk := (critical_iff_kap k x (ne_of_gt (denom_pos hx))).1 hroot
  have hdual := dual_lower_bound x M l B hx h₀ hK hH
  have hi := fixed_point_identity x (ne_of_gt (boundary_den_pos hx))
    (ne_of_gt (denom_pos hx))
  have hdiff : 0 ≤ kap x-(2*boundary x-1) := by rw [← hk]; linarith
  have hd : 0 < 18*(2*x+1)*denom x := by
    have hlin : 0 < 2*x+1 := by have := hx.1; linarith
    exact mul_pos (mul_pos (by norm_num) hlin) (denom_pos hx)
  have hp : cubic x ≤ 0 := by
    rw [hi] at hdiff
    have hn := (le_div_iff₀ hd).1 hdiff
    linarith
  have hxi := (cubic_nonpos_iff x hx).1 hp
  constructor
  · rw [hk]
    exact kap_strictMono.monotoneOn xiInf_mem hx hxi
  · exact le_trans (boundary_monotone xiInf_mem hx hxi) hdual

theorem endpoint_optimum_attained :
    let x := xiInf
    let l := length x
    let M := 1-l
    let B := boundary x
    low₀ M l = B ∧ lowK M l = B ∧ high x M l = B ∧ B = (1+kap x)/2 := by
  dsimp
  obtain ⟨h₀,hK,hH⟩ := equal_branches xiInf (ne_of_gt (boundary_den_pos xiInf_mem))
  exact ⟨h₀,hK,hH, by linarith [root_fixed_point]⟩

theorem kap_xiInf_range : kap xiInf ∈ Set.Icc (13/18:ℝ) (3/4:ℝ) := by
  have hL : (38858/100000:ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
    constructor <;> norm_num
  have hb := kap_strictMono.monotoneOn hL xiInf_mem xiInf_mem_small.1
  have hrat : (13/18:ℝ) ≤ kap (38858/100000) := by norm_num [kap,denom]
  constructor
  · exact le_trans hrat hb
  · rw [root_fixed_point]
    have hbU := boundary_monotone xiInf_mem
      (by constructor <;> norm_num : (38859/100000:ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ))
      xiInf_mem_small.2
    norm_num [boundary] at hbU
    unfold boundary
    linarith

/-- CONDITIONAL analytic assembly. The physical one-step implication is an
explicit hypothesis, not an axiom or a conclusion of this scalar file.
No passage to a uniform limit of analytic constants is needed. -/
theorem conditional_bootstrap_limit (beta : ℝ) (hinit : beta ≤ (7/8:ℝ))
    (hstep : ∀ x ∈ Set.Icc (38858/100000:ℝ) (38859/100000:ℝ),
      kap x ≤ (3/4:ℝ) → beta ≤ (1+kap x)/2 → beta ≤ boundary x) :
    beta ≤ boundary xiInf := by
  by_contra hn
  have hbeta : boundary xiInf < beta := lt_of_not_ge hn
  let k : ℝ := 2*beta-1
  have hklo : kap xiInf < k := by dsimp [k]; linarith [root_fixed_point]
  have hkhi : k ≤ (3/4:ℝ) := by dsimp [k]; linarith
  have hkdom : k ∈ Set.Icc (13/18:ℝ) 1 := by
    constructor
    · linarith [kap_xiInf_range.1]
    · linarith
  obtain ⟨x,hx,hqx⟩ := critical_root_exists k hkdom
  have hkx := (critical_iff_kap k x (ne_of_gt (denom_pos hx))).1 hqx
  have hxgt : xiInf < x := by
    by_contra he
    have hm := kap_strictMono.monotoneOn hx xiInf_mem (le_of_not_gt he)
    linarith
  have hU : (38859/100000:ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
    constructor <;> norm_num
  have hkapU : (3/4:ℝ) < kap (38859/100000) := by norm_num [kap,denom]
  have hxU : x ≤ (38859/100000:ℝ) := by
    by_contra he
    have hm := kap_strictMono hU hx (lt_of_not_ge he)
    linarith
  have hxsmall : x ∈ Set.Icc (38858/100000:ℝ) (38859/100000:ℝ) :=
    ⟨by linarith [xiInf_mem_small.1],hxU⟩
  have hb := hstep x hxsmall (by linarith) (by dsimp [k] at hkx; linarith)
  have hp := cubic_strictAnti xiInf_mem hx hxgt
  rw [cubic_xiInf] at hp
  have hd : 0 < 18*(2*x+1)*denom x := by
    have hlin : 0 < 2*x+1 := by have := hx.1; linarith
    exact mul_pos (mul_pos (by norm_num) hlin) (denom_pos hx)
  have hquot : 0 < -cubic x/(18*(2*x+1)*denom x) := div_pos (neg_pos.mpr hp) hd
  have hi := fixed_point_identity x (ne_of_gt (boundary_den_pos hx))
    (ne_of_gt (denom_pos hx))
  dsimp [k] at hkx
  linarith

#print axioms endpoint_compatible_optimality
#print axioms endpoint_optimum_attained
#print axioms isolated_root_exists
#print axioms conditional_bootstrap_limit

end
end CombineV22Optimality

end PartIVBlock0

/- BEGIN consolidated UniformEndpoint.lean -/
section PartIVBlock1
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000
/-! Exact rational Bernstein certificates for Part IV of combine_v2-2.tex.
This file verifies scalar algebra, endpoint signs and geometric reserves only.
The explicitly named derivative expressions have their printed rational formulas;
HasDerivAt and the analytic estimates are outside this file. -/
namespace CombineV22.Uniform
noncomputable section
def InInterval (t : ℝ) : Prop := 38858/100000 ≤ t ∧ t ≤ 38859/100000
def ell (t : ℝ) : ℝ := ((5 + ((-6) * t)) / (9 + (18 * t)))
def boundary (t : ℝ) : ℝ := ((7 + (18 * t)) / (9 + (18 * t)))
def kappa (t : ℝ) : ℝ := ((20 + ((-57) * t) + (18 * (t ^ 2))) / (150 + ((-468) * t) + (216 * (t ^ 2))))
def b (t : ℝ) : ℝ := ((8 * ((-1) + (3 * t)) * (15 + ((-40) * t) + (12 * (t ^ 2)))) / (9 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2)))))
def c (t : ℝ) : ℝ := ((100 + ((-312) * t) + (144 * (t ^ 2))) / (20 + ((-57) * t) + (18 * (t ^ 2))))
def lx (t : ℝ) : ℝ := ((70 + ((-320) * t) + (144 * (t ^ 3)) + (336 * (t ^ 2))) / (9 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2)))))
def ly (t : ℝ) : ℝ := ((2 * ((-5) + (6 * t)) * (5 + ((-30) * t) + (36 * (t ^ 2)))) / (9 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2)))))
def h (t : ℝ) : ℝ := ((4 * t * (((-5) + (6 * t)) ^ 2)) / (9 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2)))))
def C0 (t : ℝ) : ℝ := (((-80) * t * (((-1) + (3 * t)) ^ 2)) / (27 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2)))))
lemma base0_pos (t : ℝ) (ht : InInterval t) : 0 < (1 + (2 * t)) := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hp : 0 < ((1 + (2 * t)) : ℝ) := by
    have hid : ((1 + (2 * t)) : ℝ) = (44429 / 50000) + ((44429 / 50000) * z ^ 0 * (1-z) ^ 1) + ((4443 / 5000) * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  exact hp
lemma base1_pos (t : ℝ) (ht : InInterval t) : 0 < (20 + ((-57) * t) + (18 * (t ^ 2))) := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hp : 0 < ((20 + ((-57) * t) + (18 * (t ^ 2))) : ℝ) := by
    have hid : ((20 + ((-57) * t) + (18 * (t ^ 2))) : ℝ) = (2842046929 / 10000000000) + ((2846348023 / 10000000000) * z ^ 0 * (1-z) ^ 2) + ((2844197467 / 5000000000) * z ^ 1 * (1-z) ^ 1) + ((2842046929 / 10000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  exact hp
lemma base2_pos (t : ℝ) (ht : InInterval t) : 0 < (5 + ((-20) * t) + (24 * (t ^ 2))) := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hp : 0 < ((5 + ((-20) * t) + (24 * (t ^ 2))) : ℝ) := by
    have hid : ((5 + ((-20) * t) + (24 * (t ^ 2))) : ℝ) = (1065315643 / 2500000000) + ((1065349341 / 2500000000) * z ^ 0 * (1-z) ^ 2) + ((1065332489 / 1250000000) * z ^ 1 * (1-z) ^ 1) + ((1065315643 / 2500000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  exact hp
lemma base3_pos (t : ℝ) (ht : InInterval t) : 0 < (25 + ((-78) * t) + (36 * (t ^ 2))) := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hp : 0 < ((25 + ((-78) * t) + (36 * (t ^ 2))) : ℝ) := by
    have hid : ((25 + ((-78) * t) + (36 * (t ^ 2))) : ℝ) = (315146929 / 5000000000) + ((317648023 / 5000000000) * z ^ 0 * (1-z) ^ 2) + ((316397467 / 2500000000) * z ^ 1 * (1-z) ^ 1) + ((315146929 / 5000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  exact hp
def Ac0 (t : ℝ) : ℝ := (((-200) * (((-1) + (3 * t)) ^ 2) * ((-1) + (2 * t))) / (3 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2))) * (20 + ((-57) * t) + (18 * (t ^ 2)))))
def Ac1 (t : ℝ) : ℝ := ((9350 + ((-338580) * (t ^ 3)) + ((-79325) * t) + ((-33696) * (t ^ 5)) + (183600 * (t ^ 4)) + (248100 * (t ^ 2))) / (9 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2))) * (20 + ((-57) * t) + (18 * (t ^ 2)))))
def Ac2 (t : ℝ) : ℝ := (((-16000) + ((-501240) * (t ^ 2)) + ((-455328) * (t ^ 4)) + (98496 * (t ^ 5)) + (148990 * t) + (738072 * (t ^ 3))) / (9 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2))) * (20 + ((-57) * t) + (18 * (t ^ 2)))))
def Ac3 (t : ℝ) : ℝ := (((-8) * ((-5) + (6 * t)) * (25 + ((-78) * t) + (36 * (t ^ 2)))) / (9 * (1 + (2 * t)) * (20 + ((-57) * t) + (18 * (t ^ 2)))))
def Bc0 (t : ℝ) : ℝ := ((400 * t * (((-1) + (3 * t)) ^ 2) * ((-1) + (2 * t))) / (3 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2))) * (20 + ((-57) * t) + (18 * (t ^ 2)))))
def Bc1 (t : ℝ) : ℝ := (((-24000) + ((-556500) * (t ^ 2)) + ((-123120) * (t ^ 4)) + ((-38880) * (t ^ 5)) + (195725 * t) + (598500 * (t ^ 3))) / (18 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2))) * (20 + ((-57) * t) + (18 * (t ^ 2)))))
def Bc2 (t : ℝ) : ℝ := ((5000 + ((-142380) * (t ^ 3)) + ((-44375) * t) + (12960 * (t ^ 5)) + (23760 * (t ^ 4)) + (132060 * (t ^ 2))) / (9 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2))) * (20 + ((-57) * t) + (18 * (t ^ 2)))))
def Cc0 (t : ℝ) : ℝ := (((-200) * (t ^ 2) * (((-1) + (3 * t)) ^ 2) * ((-1) + (2 * t))) / (3 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2))) * (20 + ((-57) * t) + (18 * (t ^ 2)))))
def Cc1 (t : ℝ) : ℝ := ((400 * t * (((-1) + (3 * t)) ^ 2) * (40 + ((-123) * t) + (54 * (t ^ 2)))) / (27 * (1 + (2 * t)) * (5 + ((-20) * t) + (24 * (t ^ 2))) * (20 + ((-57) * t) + (18 * (t ^ 2)))))
def Dc1 (t : ℝ) : ℝ := ((400 * t * (((-1) + (3 * t)) ^ 2) * (((-5) + (6 * t)) ^ 2) * ((-1) + (2 * t)) * (1600 + ((-18000) * (t ^ 3)) + ((-10275) * t) + (5616 * (t ^ 4)) + (21990 * (t ^ 2)))) / (81 * ((1 + (2 * t)) ^ 2) * ((5 + ((-20) * t) + (24 * (t ^ 2))) ^ 2) * ((20 + ((-57) * t) + (18 * (t ^ 2))) ^ 2)))
def Dc2 (t : ℝ) : ℝ := (((-1728000000) + ((-7613649529200) * (t ^ 6)) + ((-3574064217600) * (t ^ 8)) + ((-3105592281000) * (t ^ 4)) + ((-239980746875) * (t ^ 2)) + ((-160403328000) * (t ^ 10)) + (30722000000 * t) + (1081475535000 * (t ^ 3)) + (1139843404800 * (t ^ 9)) + (5927241657600 * (t ^ 5)) + (6515940412800 * (t ^ 7))) / (972 * ((1 + (2 * t)) ^ 2) * ((5 + ((-20) * t) + (24 * (t ^ 2))) ^ 2) * ((20 + ((-57) * t) + (18 * (t ^ 2))) ^ 2)))
def Dc3 (t : ℝ) : ℝ := ((360000000 + ((-3094113168000) * (t ^ 7)) + ((-2255255481600) * (t ^ 5)) + ((-598895078400) * (t ^ 9)) + ((-319546725000) * (t ^ 3)) + ((-7154875000) * t) + (62775870625 * (t ^ 2)) + (83476915200 * (t ^ 10)) + (1041051411000 * (t ^ 4)) + (1821310272000 * (t ^ 8)) + (3265558059600 * (t ^ 6))) / (243 * ((1 + (2 * t)) ^ 2) * ((5 + ((-20) * t) + (24 * (t ^ 2))) ^ 2) * ((20 + ((-57) * t) + (18 * (t ^ 2))) ^ 2)))
def Dc4 (t : ℝ) : ℝ := (((-25) * ((-3000) + ((-111024) * (t ^ 4)) + ((-79044) * (t ^ 2)) + (25025 * t) + (33696 * (t ^ 5)) + (126900 * (t ^ 3))) * ((-1000) + ((-129168) * (t ^ 4)) + ((-65388) * (t ^ 2)) + (13675 * t) + (38880 * (t ^ 5)) + (139068 * (t ^ 3)))) / (243 * ((1 + (2 * t)) ^ 2) * ((5 + ((-20) * t) + (24 * (t ^ 2))) ^ 2) * ((20 + ((-57) * t) + (18 * (t ^ 2))) ^ 2)))
lemma Ac0_lower (t : ℝ) (ht : InInterval t) : (47 / 100) < Ac0 t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((5900 + ((-598572) * (t ^ 3)) + ((-121824) * (t ^ 5)) + ((-91615) * t) + (372060 * (t ^ 2)) + (426384 * (t ^ 4))) : ℝ) := by
    have hid : ((5900 + ((-598572) * (t ^ 3)) + ((-121824) * (t ^ 5)) + ((-91615) * t) + (372060 * (t ^ 2)) + (426384 * (t ^ 4))) : ℝ) = (9233979878163147581757 / 19531250000000000000000) + ((9233979878163147581757 / 19531250000000000000000) * z ^ 0 * (1-z) ^ 5) + ((972515783516821733819 / 390625000000000000000) * z ^ 1 * (1-z) ^ 4) + ((20432667323409378801923 / 3906250000000000000000) * z ^ 2 * (1-z) ^ 3) + ((42830029430154456182199 / 7812500000000000000000) * z ^ 3 * (1-z) ^ 2) + ((89589431379488391658261 / 31250000000000000000000) * z ^ 4 * (1-z) ^ 1) + ((37407514739721789539519 / 62500000000000000000000) * z ^ 5 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((30000 + ((-907200) * (t ^ 4)) + ((-145500) * t) + (102000 * (t ^ 2)) + (259200 * (t ^ 5)) + (507600 * (t ^ 3))) : ℝ) := by
    have hid : ((30000 + ((-907200) * (t ^ 4)) + ((-145500) * t) + (102000 * (t ^ 2)) + (259200 * (t ^ 5)) + (507600 * (t ^ 3))) : ℝ) = (807109065385388950872219 / 6250000000000000000000) + ((808337896903920805612197 / 6250000000000000000000) * z ^ 0 * (1-z) ^ 5) + ((808092127611066290033349 / 1250000000000000000000) * z ^ 1 * (1-z) ^ 4) + ((161569271962621057555569 / 125000000000000000000) * z ^ 2 * (1-z) ^ 3) + ((807600593509718360360253 / 625000000000000000000) * z ^ 3 * (1-z) ^ 2) + ((807354828700586064250137 / 1250000000000000000000) * z ^ 4 * (1-z) ^ 1) + ((807109065385388950872219 / 6250000000000000000000) * z ^ 5 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : Ac0 t - (47 / 100) = (5900 + ((-598572) * (t ^ 3)) + ((-121824) * (t ^ 5)) + ((-91615) * t) + (372060 * (t ^ 2)) + (426384 * (t ^ 4))) / (30000 + ((-907200) * (t ^ 4)) + ((-145500) * t) + (102000 * (t ^ 2)) + (259200 * (t ^ 5)) + (507600 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < Ac0 t - (47 / 100) := by rw [heq]; exact div_pos hn hd
  linarith
lemma Ac1_lower (t : ℝ) (ht : InInterval t) : (121 / 100) < Ac1 t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((826100 + ((-35700588) * (t ^ 3)) + ((-7404335) * t) + ((-4310496) * (t ^ 5)) + (21653136 * (t ^ 4)) + (24439740 * (t ^ 2))) : ℝ) := by
    have hid : ((826100 + ((-35700588) * (t ^ 3)) + ((-7404335) * t) + ((-4310496) * (t ^ 5)) + (21653136 * (t ^ 4)) + (24439740 * (t ^ 2))) : ℝ) = (9307234913358856350253 / 19531250000000000000000) + ((9307234913358856350253 / 19531250000000000000000) * z ^ 0 * (1-z) ^ 5) + ((961803830577147483851 / 390625000000000000000) * z ^ 1 * (1-z) ^ 4) + ((19857648254704541608467 / 3906250000000000000000) * z ^ 2 * (1-z) ^ 3) + ((40958369445582368148871 / 7812500000000000000000) * z ^ 3 * (1-z) ^ 2) + ((84402743929570440078469 / 31250000000000000000000) * z ^ 4 * (1-z) ^ 1) + ((34755443200159343579151 / 62500000000000000000000) * z ^ 5 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((90000 + ((-2721600) * (t ^ 4)) + ((-436500) * t) + (306000 * (t ^ 2)) + (777600 * (t ^ 5)) + (1522800 * (t ^ 3))) : ℝ) := by
    have hid : ((90000 + ((-2721600) * (t ^ 4)) + ((-436500) * t) + (306000 * (t ^ 2)) + (777600 * (t ^ 5)) + (1522800 * (t ^ 3))) : ℝ) = (2421327196156166852616657 / 6250000000000000000000) + ((2425013690711762416836591 / 6250000000000000000000) * z ^ 0 * (1-z) ^ 5) + ((2424276382833198870100047 / 1250000000000000000000) * z ^ 1 * (1-z) ^ 4) + ((484707815887863172666707 / 125000000000000000000) * z ^ 2 * (1-z) ^ 3) + ((2422801780529155081080759 / 625000000000000000000) * z ^ 3 * (1-z) ^ 2) + ((2422064486101758192750411 / 1250000000000000000000) * z ^ 4 * (1-z) ^ 1) + ((2421327196156166852616657 / 6250000000000000000000) * z ^ 5 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : Ac1 t - (121 / 100) = (826100 + ((-35700588) * (t ^ 3)) + ((-7404335) * t) + ((-4310496) * (t ^ 5)) + (21653136 * (t ^ 4)) + (24439740 * (t ^ 2))) / (90000 + ((-2721600) * (t ^ 4)) + ((-436500) * t) + (306000 * (t ^ 2)) + (777600 * (t ^ 5)) + (1522800 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < Ac1 t - (121 / 100) := by rw [heq]; exact div_pos hn hd
  linarith
lemma Ac2_lower (t : ℝ) (ht : InInterval t) : (43 / 50) < Ac2 t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-838700) + ((-25193580) * (t ^ 2)) + ((-21596112) * (t ^ 4)) + (4590432 * (t ^ 5)) + (7637195 * t) + (36248796 * (t ^ 3))) : ℝ) := by
    have hid : (((-838700) + ((-25193580) * (t ^ 2)) + ((-21596112) * (t ^ 4)) + (4590432 * (t ^ 5)) + (7637195 * t) + (36248796 * (t ^ 3))) : ℝ) = (898651847048709914699849 / 625000000000000000000000) + ((1319433062571423059200887 / 625000000000000000000000) * z ^ 0 * (1-z) ^ 5) + ((1235274429509238593061079 / 125000000000000000000000) * z ^ 1 * (1-z) ^ 4) + ((230223398165016303712699 / 12500000000000000000000) * z ^ 2 * (1-z) ^ 3) + ((1066960747119753286008063 / 62500000000000000000000) * z ^ 3 * (1-z) ^ 2) + ((982805698994039498992627 / 125000000000000000000000) * z ^ 4 * (1-z) ^ 1) + ((898651847048709914699849 / 625000000000000000000000) * z ^ 5 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((45000 + ((-1360800) * (t ^ 4)) + ((-218250) * t) + (153000 * (t ^ 2)) + (388800 * (t ^ 5)) + (761400 * (t ^ 3))) : ℝ) := by
    have hid : ((45000 + ((-1360800) * (t ^ 4)) + ((-218250) * t) + (153000 * (t ^ 2)) + (388800 * (t ^ 5)) + (761400 * (t ^ 3))) : ℝ) = (2421327196156166852616657 / 12500000000000000000000) + ((2425013690711762416836591 / 12500000000000000000000) * z ^ 0 * (1-z) ^ 5) + ((2424276382833198870100047 / 2500000000000000000000) * z ^ 1 * (1-z) ^ 4) + ((484707815887863172666707 / 250000000000000000000) * z ^ 2 * (1-z) ^ 3) + ((2422801780529155081080759 / 1250000000000000000000) * z ^ 3 * (1-z) ^ 2) + ((2422064486101758192750411 / 2500000000000000000000) * z ^ 4 * (1-z) ^ 1) + ((2421327196156166852616657 / 12500000000000000000000) * z ^ 5 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : Ac2 t - (43 / 50) = ((-838700) + ((-25193580) * (t ^ 2)) + ((-21596112) * (t ^ 4)) + (4590432 * (t ^ 5)) + (7637195 * t) + (36248796 * (t ^ 3))) / (45000 + ((-1360800) * (t ^ 4)) + ((-218250) * t) + (153000 * (t ^ 2)) + (388800 * (t ^ 5)) + (761400 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < Ac2 t - (43 / 50) := by rw [heq]; exact div_pos hn hd
  linarith
lemma Ac3_lower (t : ℝ) (ht : InInterval t) : (29 / 100) < Ac3 t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((94780 + ((-427563) * t) + ((-182196) * (t ^ 3)) + (543456 * (t ^ 2))) : ℝ) := by
    have hid : ((94780 + ((-427563) * t) + ((-182196) * (t ^ 3)) + (543456 * (t ^ 2))) : ℝ) = (1363239988040329 / 500000000000000) + ((360387158109179 / 100000000000000) * z ^ 0 * (1-z) ^ 3) + ((4967095016081469 / 500000000000000) * z ^ 1 * (1-z) ^ 2) + ((4528399213667001 / 500000000000000) * z ^ 2 * (1-z) ^ 1) + ((1363239988040329 / 500000000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((18000 + ((-86400) * (t ^ 2)) + ((-15300) * t) + (32400 * (t ^ 3))) : ℝ) := by
    have hid : ((18000 + ((-86400) * (t ^ 2)) + ((-15300) * t) + (32400 * (t ^ 3))) : ℝ) = (2272873032576099 / 5000000000000) + ((455252311045449 / 1000000000000) * z ^ 0 * (1-z) ^ 3) + ((6825396167345439 / 5000000000000) * z ^ 1 * (1-z) ^ 2) + ((6822007644694131 / 5000000000000) * z ^ 2 * (1-z) ^ 1) + ((2272873032576099 / 5000000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : Ac3 t - (29 / 100) = (94780 + ((-427563) * t) + ((-182196) * (t ^ 3)) + (543456 * (t ^ 2))) / (18000 + ((-86400) * (t ^ 2)) + ((-15300) * t) + (32400 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < Ac3 t - (29 / 100) := by rw [heq]; exact div_pos hn hd
  linarith
lemma Dc1_lower (t : ℝ) (ht : InInterval t) : (41 / 1000) < Dc1 t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-33210000) + ((-35504805043584) * (t ^ 7)) + ((-20485752301440) * (t ^ 5)) + ((-8772636607488) * (t ^ 9)) + ((-1954768560600) * (t ^ 3)) + ((-15677863000) * t) + (268142989775 * (t ^ 2)) + (1453188086784 * (t ^ 10)) + (8031265191240 * (t ^ 4)) + (23367236203008 * (t ^ 8)) + (33614456731056 * (t ^ 6))) : ℝ) := by
    have hid : (((-33210000) + ((-35504805043584) * (t ^ 7)) + ((-20485752301440) * (t ^ 5)) + ((-8772636607488) * (t ^ 9)) + ((-1954768560600) * (t ^ 3)) + ((-15677863000) * t) + (268142989775 * (t ^ 2)) + (1453188086784 * (t ^ 10)) + (8031265191240 * (t ^ 4)) + (23367236203008 * (t ^ 8)) + (33614456731056 * (t ^ 6))) : ℝ) = (5733135250894173768478150051700104068125503191 / 190734863281250000000000000000000000000000000) + ((5733135250894173768478150051700104068125503191 / 190734863281250000000000000000000000000000000) * z ^ 0 * (1-z) ^ 10) + ((584387995307087749228200886582749118346098097 / 1907348632812500000000000000000000000000000) * z ^ 1 * (1-z) ^ 9) + ((107182842712180775053570568636647144017782667841 / 76293945312500000000000000000000000000000000) * z ^ 2 * (1-z) ^ 8) + ((72783630106356062049294580238106351715737338111 / 19073486328125000000000000000000000000000000) * z ^ 3 * (1-z) ^ 7) + ((1037564700387228657684788496163168046109624261803 / 152587890625000000000000000000000000000000000) * z ^ 4 * (1-z) ^ 6) + ((1267385802104621249241666559529559315880420753411 / 152587890625000000000000000000000000000000000) * z ^ 5 * (1-z) ^ 5) + ((4298964901337154265419903186737761588685584603379 / 610351562500000000000000000000000000000000000) * z ^ 6 * (1-z) ^ 4) + ((1249512995284550731713642363960768379080383385971 / 305175781250000000000000000000000000000000000) * z ^ 7 * (1-z) ^ 3) + ((7624476147097433919327670608939599197340207509327 / 4882812500000000000000000000000000000000000000) * z ^ 8 * (1-z) ^ 2) + ((68905321253358879370202112144596150037112788137 / 195312500000000000000000000000000000000000000) * z ^ 9 * (1-z) ^ 1) + ((3501864645190292990971646568163008859345885834599 / 97656250000000000000000000000000000000000000000) * z ^ 10 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((810000000 + ((-781301376000) * (t ^ 7)) + ((-423263232000) * (t ^ 9)) + ((-172565640000) * (t ^ 4)) + ((-7857000000) * t) + ((-2554416000) * (t ^ 6)) + (696600000 * (t ^ 3)) + (24561225000 * (t ^ 2)) + (60466176000 * (t ^ 10)) + (344787840000 * (t ^ 5)) + (977536512000 * (t ^ 8))) : ℝ) := by
    have hid : ((810000000 + ((-781301376000) * (t ^ 7)) + ((-423263232000) * (t ^ 9)) + ((-172565640000) * (t ^ 4)) + ((-7857000000) * t) + ((-2554416000) * (t ^ 6)) + (696600000 * (t ^ 3)) + (24561225000 * (t ^ 2)) + (60466176000 * (t ^ 10)) + (344787840000 * (t ^ 5)) + (977536512000 * (t ^ 8))) : ℝ) = (5862825390845484510733258799263736669287793855649 / 195312500000000000000000000000000000000000000) + ((5880684605018429092350778457020815716630635019103 / 195312500000000000000000000000000000000000000) * z ^ 0 * (1-z) ^ 10) + ((5878897982359382907057334036646604146661844471647 / 19531250000000000000000000000000000000000000) * z ^ 1 * (1-z) ^ 9) + ((52894003639828881306364877318053791305812738105431 / 39062500000000000000000000000000000000000000) * z ^ 2 * (1-z) ^ 8) + ((3525195122728885620237582900421689342163740808761 / 976562500000000000000000000000000000000000) * z ^ 3 * (1-z) ^ 7) + ((123344320037240805394357799456977400189936489818443 / 19531250000000000000000000000000000000000000) * z ^ 4 * (1-z) ^ 6) + ((369920442154259288206448070060187305455986222866081 / 48828125000000000000000000000000000000000000) * z ^ 5 * (1-z) ^ 5) + ((123269311338010819290924217522346729749293902340459 / 19531250000000000000000000000000000000000000) * z ^ 6 * (1-z) ^ 4) + ((3520908911342197977618119800225952921723392615497 / 976562500000000000000000000000000000000000) * z ^ 7 * (1-z) ^ 3) + ((52797563883549021542258458505211079171026920423967 / 39062500000000000000000000000000000000000000) * z ^ 8 * (1-z) ^ 2) + ((5864610611042197323151472542910648809443062196027 / 19531250000000000000000000000000000000000000) * z ^ 9 * (1-z) ^ 1) + ((5862825390845484510733258799263736669287793855649 / 195312500000000000000000000000000000000000000) * z ^ 10 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : Dc1 t - (41 / 1000) = ((-33210000) + ((-35504805043584) * (t ^ 7)) + ((-20485752301440) * (t ^ 5)) + ((-8772636607488) * (t ^ 9)) + ((-1954768560600) * (t ^ 3)) + ((-15677863000) * t) + (268142989775 * (t ^ 2)) + (1453188086784 * (t ^ 10)) + (8031265191240 * (t ^ 4)) + (23367236203008 * (t ^ 8)) + (33614456731056 * (t ^ 6))) / (810000000 + ((-781301376000) * (t ^ 7)) + ((-423263232000) * (t ^ 9)) + ((-172565640000) * (t ^ 4)) + ((-7857000000) * t) + ((-2554416000) * (t ^ 6)) + (696600000 * (t ^ 3)) + (24561225000 * (t ^ 2)) + (60466176000 * (t ^ 10)) + (344787840000 * (t ^ 5)) + (977536512000 * (t ^ 8))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < Dc1 t - (41 / 1000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma Dc2_lower (t : ℝ) (ht : InInterval t) : (99 / 500) < Dc2 t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-54060142500) + ((-237926358122112) * (t ^ 6)) + ((-111762088886016) * (t ^ 8)) + ((-97036945782480) * (t ^ 4)) + ((-7501222010800) * (t ^ 2)) + ((-5017093613568) * (t ^ 10)) + (960645882250 * t) + (33796058746200 * (t ^ 3)) + (35651533694976 * (t ^ 9)) + (185200701302880 * (t ^ 5)) + (203681149527168 * (t ^ 7))) : ℝ) := by
    have hid : (((-54060142500) + ((-237926358122112) * (t ^ 6)) + ((-111762088886016) * (t ^ 8)) + ((-97036945782480) * (t ^ 4)) + ((-7501222010800) * (t ^ 2)) + ((-5017093613568) * (t ^ 10)) + (960645882250 * t) + (33796058746200 * (t ^ 3)) + (35651533694976 * (t ^ 9)) + (185200701302880 * (t ^ 5)) + (203681149527168 * (t ^ 7))) : ℝ) = (548372499120418001670711717057728299014123059 / 95367431640625000000000000000000000000000000) + ((548372499120418001670711717057728299014123059 / 95367431640625000000000000000000000000000000) * z ^ 0 * (1-z) ^ 10) + ((63780202043004522150668128544534333071110653 / 953674316406250000000000000000000000000000) * z ^ 1 * (1-z) ^ 9) + ((13089847265505393255650626386858740534733395909 / 38146972656250000000000000000000000000000000) * z ^ 2 * (1-z) ^ 8) + ((9799291806840618506800464262360751824403688139 / 9536743164062500000000000000000000000000000) * z ^ 3 * (1-z) ^ 7) + ((152205272191519556779268469393869509945135279447 / 76293945312500000000000000000000000000000000) * z ^ 4 * (1-z) ^ 6) + ((200660962565688164518640704263260953338843147839 / 76293945312500000000000000000000000000000000) * z ^ 5 * (1-z) ^ 5) + ((728906701766083824059654071235407861729343607871 / 305175781250000000000000000000000000000000000) * z ^ 6 * (1-z) ^ 4) + ((225409019894787832990510181197109170164585715279 / 152587890625000000000000000000000000000000000) * z ^ 7 * (1-z) ^ 3) + ((1455333394354693422511541551156954371302058486923 / 2441406250000000000000000000000000000000000000) * z ^ 8 * (1-z) ^ 2) + ((13850597092811104432302215828353154391160595613 / 97656250000000000000000000000000000000000000) * z ^ 9 * (1-z) ^ 1) + ((738235758767528331381492823312152538115936651651 / 48828125000000000000000000000000000000000000000) * z ^ 10 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((303750000 + ((-292988016000) * (t ^ 7)) + ((-158723712000) * (t ^ 9)) + ((-64712115000) * (t ^ 4)) + ((-2946375000) * t) + ((-957906000) * (t ^ 6)) + (261225000 * (t ^ 3)) + (9210459375 * (t ^ 2)) + (22674816000 * (t ^ 10)) + (129295440000 * (t ^ 5)) + (366576192000 * (t ^ 8))) : ℝ) := by
    have hid : ((303750000 + ((-292988016000) * (t ^ 7)) + ((-158723712000) * (t ^ 9)) + ((-64712115000) * (t ^ 4)) + ((-2946375000) * t) + ((-957906000) * (t ^ 6)) + (261225000 * (t ^ 3)) + (9210459375 * (t ^ 2)) + (22674816000 * (t ^ 10)) + (129295440000 * (t ^ 5)) + (366576192000 * (t ^ 8))) : ℝ) = (17588476172536453532199776397791210007863381566947 / 1562500000000000000000000000000000000000000000) + ((17642053815055287277052335371062447149891905057309 / 1562500000000000000000000000000000000000000000) * z ^ 0 * (1-z) ^ 10) + ((17636693947078148721172002109939812439985533414941 / 156250000000000000000000000000000000000000000) * z ^ 1 * (1-z) ^ 9) + ((158682010919486643919094631954161373917438214316293 / 312500000000000000000000000000000000000000000) * z ^ 2 * (1-z) ^ 8) + ((10575585368186656860712748701265068026491222426283 / 7812500000000000000000000000000000000000000) * z ^ 3 * (1-z) ^ 7) + ((370032960111722416183073398370932200569809469455329 / 156250000000000000000000000000000000000000000) * z ^ 4 * (1-z) ^ 6) + ((1109761326462777864619344210180561916367958668598243 / 390625000000000000000000000000000000000000000) * z ^ 5 * (1-z) ^ 5) + ((369807934014032457872772652567040189247881707021377 / 156250000000000000000000000000000000000000000) * z ^ 6 * (1-z) ^ 4) + ((10562726734026593932854359400677858765170177846491 / 7812500000000000000000000000000000000000000) * z ^ 7 * (1-z) ^ 3) + ((158392691650647064626775375515633237513080761271901 / 312500000000000000000000000000000000000000000) * z ^ 8 * (1-z) ^ 2) + ((17593831833126591969454417628731946428329186588081 / 156250000000000000000000000000000000000000000) * z ^ 9 * (1-z) ^ 1) + ((17588476172536453532199776397791210007863381566947 / 1562500000000000000000000000000000000000000000) * z ^ 10 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : Dc2 t - (99 / 500) = ((-54060142500) + ((-237926358122112) * (t ^ 6)) + ((-111762088886016) * (t ^ 8)) + ((-97036945782480) * (t ^ 4)) + ((-7501222010800) * (t ^ 2)) + ((-5017093613568) * (t ^ 10)) + (960645882250 * t) + (33796058746200 * (t ^ 3)) + (35651533694976 * (t ^ 9)) + (185200701302880 * (t ^ 5)) + (203681149527168 * (t ^ 7))) / (303750000 + ((-292988016000) * (t ^ 7)) + ((-158723712000) * (t ^ 9)) + ((-64712115000) * (t ^ 4)) + ((-2946375000) * t) + ((-957906000) * (t ^ 6)) + (261225000 * (t ^ 3)) + (9210459375 * (t ^ 2)) + (22674816000 * (t ^ 10)) + (129295440000 * (t ^ 5)) + (366576192000 * (t ^ 8))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < Dc2 t - (99 / 500) := by rw [heq]; exact div_pos hn hd
  linarith
lemma Dc3_lower (t : ℝ) (ht : InInterval t) : (267 / 1000) < Dc3 t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((359351190000 + ((-3093487345597824) * (t ^ 7)) + ((-2255531656659840) * (t ^ 5)) + ((-598556044551168) * (t ^ 9)) + ((-319547282976600) * (t ^ 3)) + ((-7148581543000) * t) + (62756197083775 * (t ^ 2)) + (83428481793024 * (t ^ 10)) + (1041189636077640 * (t ^ 4)) + (1820527265253888 * (t ^ 8)) + (3265560105687216 * (t ^ 6))) : ℝ) := by
    have hid : ((359351190000 + ((-3093487345597824) * (t ^ 7)) + ((-2255531656659840) * (t ^ 5)) + ((-598556044551168) * (t ^ 9)) + ((-319547282976600) * (t ^ 3)) + ((-7148581543000) * t) + (62756197083775 * (t ^ 2)) + (83428481793024 * (t ^ 10)) + (1041189636077640 * (t ^ 4)) + (1820527265253888 * (t ^ 8)) + (3265560105687216 * (t ^ 6))) : ℝ) = (10528394098008906350656369786024520309332412951 / 190734863281250000000000000000000000000000000) + ((10528394098008906350656369786024520309332412951 / 190734863281250000000000000000000000000000000) * z ^ 0 * (1-z) ^ 10) + ((1160848880310928044436519136095960211800200017 / 1907348632812500000000000000000000000000000) * z ^ 1 * (1-z) ^ 9) + ((228384944510915976383216203942704642683589001601 / 76293945312500000000000000000000000000000000) * z ^ 2 * (1-z) ^ 8) + ((165205022847385079807471221127664038962663139071 / 19073486328125000000000000000000000000000000) * z ^ 3 * (1-z) ^ 7) + ((2494058654066330125665015960658267453437120123883 / 152587890625000000000000000000000000000000000) * z ^ 4 * (1-z) ^ 6) + ((3210189407884317495115287147703620038751472362371 / 152587890625000000000000000000000000000000000) * z ^ 5 * (1-z) ^ 5) + ((11424671596939518656209271392094316206231116528819 / 610351562500000000000000000000000000000000000) * z ^ 6 * (1-z) ^ 4) + ((3470958690194263556469189611664670192395416476531 / 305175781250000000000000000000000000000000000) * z ^ 7 * (1-z) ^ 3) + ((22065742119900521155715613594809239190672855484047 / 4882812500000000000000000000000000000000000000) * z ^ 8 * (1-z) ^ 2) + ((207156634623479531360513164720109776719003644457 / 195312500000000000000000000000000000000000000) * z ^ 9 * (1-z) ^ 1) + ((10908395607460726758124752735146173016499641619239 / 97656250000000000000000000000000000000000000000) * z ^ 10 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((2430000000 + ((-2343904128000) * (t ^ 7)) + ((-1269789696000) * (t ^ 9)) + ((-517696920000) * (t ^ 4)) + ((-23571000000) * t) + ((-7663248000) * (t ^ 6)) + (2089800000 * (t ^ 3)) + (73683675000 * (t ^ 2)) + (181398528000 * (t ^ 10)) + (1034363520000 * (t ^ 5)) + (2932609536000 * (t ^ 8))) : ℝ) := by
    have hid : ((2430000000 + ((-2343904128000) * (t ^ 7)) + ((-1269789696000) * (t ^ 9)) + ((-517696920000) * (t ^ 4)) + ((-23571000000) * t) + ((-7663248000) * (t ^ 6)) + (2089800000 * (t ^ 3)) + (73683675000 * (t ^ 2)) + (181398528000 * (t ^ 10)) + (1034363520000 * (t ^ 5)) + (2932609536000 * (t ^ 8))) : ℝ) = (17588476172536453532199776397791210007863381566947 / 195312500000000000000000000000000000000000000) + ((17642053815055287277052335371062447149891905057309 / 195312500000000000000000000000000000000000000) * z ^ 0 * (1-z) ^ 10) + ((17636693947078148721172002109939812439985533414941 / 19531250000000000000000000000000000000000000) * z ^ 1 * (1-z) ^ 9) + ((158682010919486643919094631954161373917438214316293 / 39062500000000000000000000000000000000000000) * z ^ 2 * (1-z) ^ 8) + ((10575585368186656860712748701265068026491222426283 / 976562500000000000000000000000000000000000) * z ^ 3 * (1-z) ^ 7) + ((370032960111722416183073398370932200569809469455329 / 19531250000000000000000000000000000000000000) * z ^ 4 * (1-z) ^ 6) + ((1109761326462777864619344210180561916367958668598243 / 48828125000000000000000000000000000000000000) * z ^ 5 * (1-z) ^ 5) + ((369807934014032457872772652567040189247881707021377 / 19531250000000000000000000000000000000000000) * z ^ 6 * (1-z) ^ 4) + ((10562726734026593932854359400677858765170177846491 / 976562500000000000000000000000000000000000) * z ^ 7 * (1-z) ^ 3) + ((158392691650647064626775375515633237513080761271901 / 39062500000000000000000000000000000000000000) * z ^ 8 * (1-z) ^ 2) + ((17593831833126591969454417628731946428329186588081 / 19531250000000000000000000000000000000000000) * z ^ 9 * (1-z) ^ 1) + ((17588476172536453532199776397791210007863381566947 / 195312500000000000000000000000000000000000000) * z ^ 10 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : Dc3 t - (267 / 1000) = (359351190000 + ((-3093487345597824) * (t ^ 7)) + ((-2255531656659840) * (t ^ 5)) + ((-598556044551168) * (t ^ 9)) + ((-319547282976600) * (t ^ 3)) + ((-7148581543000) * t) + (62756197083775 * (t ^ 2)) + (83428481793024 * (t ^ 10)) + (1041189636077640 * (t ^ 4)) + (1820527265253888 * (t ^ 8)) + (3265560105687216 * (t ^ 6))) / (2430000000 + ((-2343904128000) * (t ^ 7)) + ((-1269789696000) * (t ^ 9)) + ((-517696920000) * (t ^ 4)) + ((-23571000000) * t) + ((-7663248000) * (t ^ 6)) + (2089800000 * (t ^ 3)) + (73683675000 * (t ^ 2)) + (181398528000 * (t ^ 10)) + (1034363520000 * (t ^ 5)) + (2932609536000 * (t ^ 8))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < Dc3 t - (267 / 1000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma Dc4_lower (t : ℝ) (ht : InInterval t) : (19 / 250) < Dc4 t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-18796170000) + ((-228444146298288) * (t ^ 6)) + ((-149809815581184) * (t ^ 8)) + ((-68006359208520) * (t ^ 4)) + ((-8191574572032) * (t ^ 10)) + ((-3860305458575) * (t ^ 2)) + (413260349000 * t) + (20383494043800 * (t ^ 3)) + (54205738804224 * (t ^ 9)) + (151175638293120 * (t ^ 5)) + (231968594178432 * (t ^ 7))) : ℝ) := by
    have hid : (((-18796170000) + ((-228444146298288) * (t ^ 6)) + ((-149809815581184) * (t ^ 8)) + ((-68006359208520) * (t ^ 4)) + ((-8191574572032) * (t ^ 10)) + ((-3860305458575) * (t ^ 2)) + (413260349000 * t) + (20383494043800 * (t ^ 3)) + (54205738804224 * (t ^ 9)) + (151175638293120 * (t ^ 5)) + (231968594178432 * (t ^ 7))) : ℝ) = (1368709221537165649891483975616126483657797759257 / 195312500000000000000000000000000000000000000000) + ((3660651680257998454998160096123961029668300379879 / 195312500000000000000000000000000000000000000000) * z ^ 0 * (1-z) ^ 10) + ((3432003000078037842586604068620261762425329584871 / 19531250000000000000000000000000000000000000000) * z ^ 1 * (1-z) ^ 9) + ((28829097129252971727107686522768485522319484209183 / 39062500000000000000000000000000000000000000000) * z ^ 2 * (1-z) ^ 8) + ((1784605049324431705647380687486958336795454181873 / 976562500000000000000000000000000000000000000) * z ^ 3 * (1-z) ^ 7) + ((57651913817048658116359209679373936389125166192499 / 19531250000000000000000000000000000000000000000) * z ^ 4 * (1-z) ^ 6) + ((158520315344456580572317260266535251884518848164633 / 48828125000000000000000000000000000000000000000) * z ^ 5 * (1-z) ^ 5) + ((48025751160846273514537711279126327322273629437587 / 19531250000000000000000000000000000000000000000) * z ^ 6 * (1-z) ^ 4) + ((1234538642752687559230895952834346787941405697921 / 976562500000000000000000000000000000000000000) * z ^ 7 * (1-z) ^ 3) + ((16452604141096288977053377668678106183668790302631 / 39062500000000000000000000000000000000000000000) * z ^ 8 * (1-z) ^ 2) + ((1598448723846023024387376479737103304757076170211 / 19531250000000000000000000000000000000000000000) * z ^ 9 * (1-z) ^ 1) + ((1368709221537165649891483975616126483657797759257 / 195312500000000000000000000000000000000000000000) * z ^ 10 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((607500000 + ((-585976032000) * (t ^ 7)) + ((-317447424000) * (t ^ 9)) + ((-129424230000) * (t ^ 4)) + ((-5892750000) * t) + ((-1915812000) * (t ^ 6)) + (522450000 * (t ^ 3)) + (18420918750 * (t ^ 2)) + (45349632000 * (t ^ 10)) + (258590880000 * (t ^ 5)) + (733152384000 * (t ^ 8))) : ℝ) := by
    have hid : ((607500000 + ((-585976032000) * (t ^ 7)) + ((-317447424000) * (t ^ 9)) + ((-129424230000) * (t ^ 4)) + ((-5892750000) * t) + ((-1915812000) * (t ^ 6)) + (522450000 * (t ^ 3)) + (18420918750 * (t ^ 2)) + (45349632000 * (t ^ 10)) + (258590880000 * (t ^ 5)) + (733152384000 * (t ^ 8))) : ℝ) = (17588476172536453532199776397791210007863381566947 / 781250000000000000000000000000000000000000000) + ((17642053815055287277052335371062447149891905057309 / 781250000000000000000000000000000000000000000) * z ^ 0 * (1-z) ^ 10) + ((17636693947078148721172002109939812439985533414941 / 78125000000000000000000000000000000000000000) * z ^ 1 * (1-z) ^ 9) + ((158682010919486643919094631954161373917438214316293 / 156250000000000000000000000000000000000000000) * z ^ 2 * (1-z) ^ 8) + ((10575585368186656860712748701265068026491222426283 / 3906250000000000000000000000000000000000000) * z ^ 3 * (1-z) ^ 7) + ((370032960111722416183073398370932200569809469455329 / 78125000000000000000000000000000000000000000) * z ^ 4 * (1-z) ^ 6) + ((1109761326462777864619344210180561916367958668598243 / 195312500000000000000000000000000000000000000) * z ^ 5 * (1-z) ^ 5) + ((369807934014032457872772652567040189247881707021377 / 78125000000000000000000000000000000000000000) * z ^ 6 * (1-z) ^ 4) + ((10562726734026593932854359400677858765170177846491 / 3906250000000000000000000000000000000000000) * z ^ 7 * (1-z) ^ 3) + ((158392691650647064626775375515633237513080761271901 / 156250000000000000000000000000000000000000000) * z ^ 8 * (1-z) ^ 2) + ((17593831833126591969454417628731946428329186588081 / 78125000000000000000000000000000000000000000) * z ^ 9 * (1-z) ^ 1) + ((17588476172536453532199776397791210007863381566947 / 781250000000000000000000000000000000000000000) * z ^ 10 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : Dc4 t - (19 / 250) = ((-18796170000) + ((-228444146298288) * (t ^ 6)) + ((-149809815581184) * (t ^ 8)) + ((-68006359208520) * (t ^ 4)) + ((-8191574572032) * (t ^ 10)) + ((-3860305458575) * (t ^ 2)) + (413260349000 * t) + (20383494043800 * (t ^ 3)) + (54205738804224 * (t ^ 9)) + (151175638293120 * (t ^ 5)) + (231968594178432 * (t ^ 7))) / (607500000 + ((-585976032000) * (t ^ 7)) + ((-317447424000) * (t ^ 9)) + ((-129424230000) * (t ^ 4)) + ((-5892750000) * t) + ((-1915812000) * (t ^ 6)) + (522450000 * (t ^ 3)) + (18420918750 * (t ^ 2)) + (45349632000 * (t ^ 10)) + (258590880000 * (t ^ 5)) + (733152384000 * (t ^ 8))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < Dc4 t - (19 / 250) := by rw [heq]; exact div_pos hn hd
  linarith
def critical_denominator (t : ℝ) : ℝ := ((25 + ((-78) * t) + (36 * (t ^ 2))) / 1)
def kappa_derivative (t : ℝ) : ℝ := ((45 + ((-180) * t) + (216 * (t ^ 2))) / (2 * ((25 + ((-78) * t) + (36 * (t ^ 2))) ^ 2)))
def boundary_derivative (t : ℝ) : ℝ := (4 / (9 * ((1 + (2 * t)) ^ 2)))
def contraction_derivative (t : ℝ) : ℝ := (((-4999595) + ((-63074916) * (t ^ 2)) + ((-10360224) * (t ^ 4)) + (31200000 * t) + (44929296 * (t ^ 3))) / (18 * ((1 + (2 * t)) ^ 2) * ((25 + ((-78) * t) + (36 * (t ^ 2))) ^ 2)))
def cubic_decrease (t : ℝ) : ℝ := (((-171) + ((-3564) * (t ^ 2)) + (4320 * t)) / 1)
lemma b_positive_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < b t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-3000045) + ((-26399856) * (t ^ 2)) + (7199568 * (t ^ 3)) + (17000090 * t)) : ℝ) := by
    have hid : (((-3000045) + ((-26399856) * (t ^ 2)) + (7199568 * (t ^ 3)) + (17000090 * t)) : ℝ) = (2627485792256057967 / 125000000000000) + ((525561088064481517 / 25000000000000) * z ^ 0 * (1-z) ^ 3) + ((7883096897987868187 / 125000000000000) * z ^ 1 * (1-z) ^ 2) + ((7882777249920618623 / 125000000000000) * z ^ 2 * (1-z) ^ 1) + ((2627485792256057967 / 125000000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) : ℝ) := by
    have hid : ((1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) : ℝ) = (851965944492033 / 5000000000) + ((170394743568483 / 1000000000) * z ^ 0 * (1-z) ^ 3) + ((2555913375681813 / 5000000000) * z ^ 1 * (1-z) ^ 2) + ((2555905602331377 / 5000000000) * z ^ 2 * (1-z) ^ 1) + ((851965944492033 / 5000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : b t - (1 / 25000) = ((-3000045) + ((-26399856) * (t ^ 2)) + (7199568 * (t ^ 3)) + (17000090 * t)) / (1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < b t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma ell_positive_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < ell t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((124991 + ((-150018) * t)) : ℝ) := by
    have hid : ((124991 + ((-150018) * t)) : ℝ) = (3334775269 / 100000) + ((3334925287 / 100000) * z ^ 0 * (1-z) ^ 1) + ((3334775269 / 100000) * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((225000 + (450000 * t)) : ℝ) := by
    have hid : ((225000 + (450000 * t)) : ℝ) = (399861 / 2) + ((399861 / 2) * z ^ 0 * (1-z) ^ 1) + (199935 * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : ell t - (1 / 25000) = (124991 + ((-150018) * t)) / (225000 + (450000 * t)) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < ell t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma ell_upper_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < 1/5-ell t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-80009) + (239982 * t)) : ℝ) := by
    have hid : (((-80009) + (239982 * t)) : ℝ) = (331080139 / 50000) + ((331080139 / 50000) * z ^ 0 * (1-z) ^ 1) + ((33120013 / 5000) * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((225000 + (450000 * t)) : ℝ) := by
    have hid : ((225000 + (450000 * t)) : ℝ) = (399861 / 2) + ((399861 / 2) * z ^ 0 * (1-z) ^ 1) + (199935 * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : 1/5-ell t - (1 / 25000) = ((-80009) + (239982 * t)) / (225000 + (450000 * t)) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < 1/5-ell t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma lx_reserve_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < lx t-b t-ell t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((1374985 + ((-7249970) * t) + ((-144) * (t ^ 3)) + (9600048 * (t ^ 2))) : ℝ) := by
    have hid : ((1374985 + ((-7249970) * t) + ((-144) * (t ^ 3)) + (9600048 * (t ^ 2))) : ℝ) = (57319168757034699 / 15625000000000) + ((57319168757034699 / 15625000000000) * z ^ 0 * (1-z) ^ 3) + ((17199043409518099 / 1562500000000) * z ^ 1 * (1-z) ^ 2) + ((344046753838141183 / 31250000000000) * z ^ 2 * (1-z) ^ 1) + ((229408446323697193 / 62500000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((375000 + ((-1200000) * (t ^ 2)) + ((-750000) * t) + (3600000 * (t ^ 3))) : ℝ) := by
    have hid : ((375000 + ((-1200000) * (t ^ 2)) + ((-750000) * t) + (3600000 * (t ^ 3))) : ℝ) = (283988648164011 / 5000000000) + ((56798247856161 / 1000000000) * z ^ 0 * (1-z) ^ 3) + ((851971125227271 / 5000000000) * z ^ 1 * (1-z) ^ 2) + ((851968534110459 / 5000000000) * z ^ 2 * (1-z) ^ 1) + ((283988648164011 / 5000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : lx t-b t-ell t - (1 / 25000) = (1374985 + ((-7249970) * t) + ((-144) * (t ^ 3)) + (9600048 * (t ^ 2))) / (375000 + ((-1200000) * (t ^ 2)) + ((-750000) * t) + (3600000 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < lx t-b t-ell t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma ly_reserve_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < ly t-ell t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-1875045) + ((-23999856) * (t ^ 2)) + (12250090 * t) + (14399568 * (t ^ 3))) : ℝ) := by
    have hid : (((-1875045) + ((-23999856) * (t ^ 2)) + (12250090 * t) + (14399568 * (t ^ 3))) : ℝ) = (829081902801204097 / 15625000000000) + ((829081902801204097 / 15625000000000) * z ^ 0 * (1-z) ^ 3) + ((248726463418654297 / 1562500000000) * z ^ 1 * (1-z) ^ 2) + ((4974567097396123549 / 31250000000000) * z ^ 2 * (1-z) ^ 1) + ((3316403269251791579 / 62500000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) : ℝ) := by
    have hid : ((1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) : ℝ) = (851965944492033 / 5000000000) + ((170394743568483 / 1000000000) * z ^ 0 * (1-z) ^ 3) + ((2555913375681813 / 5000000000) * z ^ 1 * (1-z) ^ 2) + ((2555905602331377 / 5000000000) * z ^ 2 * (1-z) ^ 1) + ((851965944492033 / 5000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : ly t-ell t - (1 / 25000) = ((-1875045) + ((-23999856) * (t ^ 2)) + (12250090 * t) + (14399568 * (t ^ 3))) / (1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < ly t-ell t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma gram_reserve_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < ly t-ell t-11*b t/6 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((10874865 + ((-56749730) * t) + (3598704 * (t ^ 3)) + (73200432 * (t ^ 2))) : ℝ) := by
    have hid : ((10874865 + ((-56749730) * t) + (3598704 * (t ^ 3)) + (73200432 * (t ^ 2))) : ℝ) = (680153617945837291 / 15625000000000) + ((680153617945837291 / 15625000000000) * z ^ 0 * (1-z) ^ 3) + ((204073723983187891 / 1562500000000) * z ^ 1 * (1-z) ^ 2) + ((4082027493513695647 / 31250000000000) * z ^ 2 * (1-z) ^ 1) + ((2721720499483449737 / 62500000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((3375000 + ((-10800000) * (t ^ 2)) + ((-6750000) * t) + (32400000 * (t ^ 3))) : ℝ) := by
    have hid : ((3375000 + ((-10800000) * (t ^ 2)) + ((-6750000) * t) + (32400000 * (t ^ 3))) : ℝ) = (2555897833476099 / 5000000000) + ((511184230705449 / 1000000000) * z ^ 0 * (1-z) ^ 3) + ((7667740127045439 / 5000000000) * z ^ 1 * (1-z) ^ 2) + ((7667716806994131 / 5000000000) * z ^ 2 * (1-z) ^ 1) + ((2555897833476099 / 5000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : ly t-ell t-11*b t/6 - (1 / 25000) = (10874865 + ((-56749730) * t) + (3598704 * (t ^ 3)) + (73200432 * (t ^ 2))) / (3375000 + ((-10800000) * (t ^ 2)) + ((-6750000) * t) + (32400000 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < ly t-ell t-11*b t/6 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma h_upper_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < 1-h t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((1124955 + ((-4749910) * t) + (2400144 * (t ^ 2)) + (7199568 * (t ^ 3))) : ℝ) := by
    have hid : ((1124955 + ((-4749910) * t) + (2400144 * (t ^ 2)) + (7199568 * (t ^ 3))) : ℝ) = (500519704536154097 / 15625000000000) + ((500519704536154097 / 15625000000000) * z ^ 0 * (1-z) ^ 3) + ((150161796823604297 / 1562500000000) * z ^ 1 * (1-z) ^ 2) + ((3003353679455273549 / 31250000000000) * z ^ 2 * (1-z) ^ 1) + ((2002314304111441579 / 62500000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) : ℝ) := by
    have hid : ((1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) : ℝ) = (851965944492033 / 5000000000) + ((170394743568483 / 1000000000) * z ^ 0 * (1-z) ^ 3) + ((2555913375681813 / 5000000000) * z ^ 1 * (1-z) ^ 2) + ((2555905602331377 / 5000000000) * z ^ 2 * (1-z) ^ 1) + ((851965944492033 / 5000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : 1-h t - (1 / 25000) = (1124955 + ((-4749910) * t) + (2400144 * (t ^ 2)) + (7199568 * (t ^ 3))) / (1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < 1-h t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma supply_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < 5*ell t-h t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((3124955 + ((-21600432) * (t ^ 3)) + ((-18749910) * t) + (36000144 * (t ^ 2))) : ℝ) := by
    have hid : ((3124955 + ((-21600432) * (t ^ 3)) + ((-18749910) * t) + (36000144 * (t ^ 2))) : ℝ) = (472445639453857967 / 125000000000000) + ((94628268832281517 / 25000000000000) * z ^ 0 * (1-z) ^ 3) + ((1418728192533668187 / 125000000000000) * z ^ 1 * (1-z) ^ 2) + ((1418032487828818623 / 125000000000000) * z ^ 2 * (1-z) ^ 1) + ((472445639453857967 / 125000000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) : ℝ) := by
    have hid : ((1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) : ℝ) = (851965944492033 / 5000000000) + ((170394743568483 / 1000000000) * z ^ 0 * (1-z) ^ 3) + ((2555913375681813 / 5000000000) * z ^ 1 * (1-z) ^ 2) + ((2555905602331377 / 5000000000) * z ^ 2 * (1-z) ^ 1) + ((851965944492033 / 5000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : 5*ell t-h t - (1 / 25000) = (3124955 + ((-21600432) * (t ^ 3)) + ((-18749910) * t) + (36000144 * (t ^ 2))) / (1125000 + ((-3600000) * (t ^ 2)) + ((-2250000) * t) + (10800000 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < 5*ell t-h t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma boundary_lower_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < boundary t-43/50 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-18509) + (62982 * t)) : ℝ) := by
    have hid : (((-18509) + (62982 * t)) : ℝ) = (149113639 / 50000) + ((149113639 / 50000) * z ^ 0 * (1-z) ^ 1) + ((14914513 / 5000) * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((225000 + (450000 * t)) : ℝ) := by
    have hid : ((225000 + (450000 * t)) : ℝ) = (399861 / 2) + ((399861 / 2) * z ^ 0 * (1-z) ^ 1) + (199935 * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : boundary t-43/50 - (1 / 25000) = ((-18509) + (62982 * t)) / (225000 + (450000 * t)) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < boundary t-43/50 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma boundary_principal_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < boundary t-437/500 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-21659) + (56682 * t)) : ℝ) := by
    have hid : (((-21659) + (56682 * t)) : ℝ) = (9162289 / 50000) + ((9162289 / 50000) * z ^ 0 * (1-z) ^ 1) + ((919063 / 5000) * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((225000 + (450000 * t)) : ℝ) := by
    have hid : ((225000 + (450000 * t)) : ℝ) = (399861 / 2) + ((399861 / 2) * z ^ 0 * (1-z) ^ 1) + (199935 * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : boundary t-437/500 - (1 / 25000) = ((-21659) + (56682 * t)) / (225000 + (450000 * t)) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < boundary t-437/500 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma boundary_upper_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < 7/8-boundary t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((10933 + ((-28134) * t)) : ℝ) := by
    have hid : ((10933 + ((-28134) * t)) : ℝ) = (20447 / 100000) + ((48581 / 100000) * z ^ 0 * (1-z) ^ 1) + ((20447 / 100000) * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((112500 + (225000 * t)) : ℝ) := by
    have hid : ((112500 + (225000 * t)) : ℝ) = (399861 / 4) + ((399861 / 4) * z ^ 0 * (1-z) ^ 1) + ((199935 / 2) * z ^ 1 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : 7/8-boundary t - (1 / 25000) = (10933 + ((-28134) * t)) / (112500 + (225000 * t)) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < 7/8-boundary t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma floor_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < -C0 t-(1/2+3*ell t/2)/50 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-90135) + ((-12431568) * (t ^ 2)) + (2360270 * t) + (17998704 * (t ^ 3))) : ℝ) := by
    have hid : (((-90135) + ((-12431568) * (t ^ 2)) + (2360270 * t) + (17998704 * (t ^ 3))) : ℝ) = (46614895375937291 / 15625000000000) + ((46614895375937291 / 15625000000000) * z ^ 0 * (1-z) ^ 3) + ((13997782113287891 / 1562500000000) * z ^ 1 * (1-z) ^ 2) + ((280221938995395647 / 31250000000000) * z ^ 2 * (1-z) ^ 1) + ((186992174964149737 / 62500000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((3375000 + ((-10800000) * (t ^ 2)) + ((-6750000) * t) + (32400000 * (t ^ 3))) : ℝ) := by
    have hid : ((3375000 + ((-10800000) * (t ^ 2)) + ((-6750000) * t) + (32400000 * (t ^ 3))) : ℝ) = (2555897833476099 / 5000000000) + ((511184230705449 / 1000000000) * z ^ 0 * (1-z) ^ 3) + ((7667740127045439 / 5000000000) * z ^ 1 * (1-z) ^ 2) + ((7667716806994131 / 5000000000) * z ^ 2 * (1-z) ^ 1) + ((2555897833476099 / 5000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : -C0 t-(1/2+3*ell t/2)/50 - (1 / 25000) = ((-90135) + ((-12431568) * (t ^ 2)) + (2360270 * t) + (17998704 * (t ^ 3))) / (3375000 + ((-10800000) * (t ^ 2)) + ((-6750000) * t) + (32400000 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < -C0 t-(1/2+3*ell t/2)/50 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma small_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < ly t/2-13*h t/75-1/50-(7/8-boundary t) := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-283845) + ((-3576696) * (t ^ 2)) + (1811440 * t) + (2216088 * (t ^ 3))) : ℝ) := by
    have hid : (((-283845) + ((-3576696) * (t ^ 2)) + (1811440 * t) + (2216088 * (t ^ 3))) : ℝ) = (156385477803999479 / 31250000000000) + ((156385477803999479 / 31250000000000) * z ^ 0 * (1-z) ^ 3) + ((46916756643680879 / 3125000000000) * z ^ 1 * (1-z) ^ 2) + ((938357392715028443 / 62500000000000) * z ^ 2 * (1-z) ^ 1) + ((625586430899096653 / 125000000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((421875 + ((-1350000) * (t ^ 2)) + ((-843750) * t) + (4050000 * (t ^ 3))) : ℝ) := by
    have hid : ((421875 + ((-1350000) * (t ^ 2)) + ((-843750) * t) + (4050000 * (t ^ 3))) : ℝ) = (2555897833476099 / 40000000000) + ((511184230705449 / 8000000000) * z ^ 0 * (1-z) ^ 3) + ((7667740127045439 / 40000000000) * z ^ 1 * (1-z) ^ 2) + ((7667716806994131 / 40000000000) * z ^ 2 * (1-z) ^ 1) + ((2555897833476099 / 40000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : ly t/2-13*h t/75-1/50-(7/8-boundary t) - (1 / 25000) = ((-283845) + ((-3576696) * (t ^ 2)) + (1811440 * t) + (2216088 * (t ^ 3))) / (421875 + ((-1350000) * (t ^ 2)) + ((-843750) * t) + (4050000 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < ly t/2-13*h t/75-1/50-(7/8-boundary t) - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma intermediate_floor_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < -((225*ell t+50-75*b t)/50+78*ell t-49*b t-73)/300 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-152595) + ((-2609196) * (t ^ 2)) + (1205815 * t) + (1797588 * (t ^ 3))) : ℝ) := by
    have hid : (((-152595) + ((-2609196) * (t ^ 2)) + (1205815 * t) + (1797588 * (t ^ 3))) : ℝ) = (6864276742273561263 / 500000000000000) + ((1372863024101687213 / 100000000000000) * z ^ 0 * (1-z) ^ 3) + ((20592907008973322843 / 500000000000000) * z ^ 1 * (1-z) ^ 2) + ((20592868630737549247 / 500000000000000) * z ^ 2 * (1-z) ^ 1) + ((6864276742273561263 / 500000000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((421875 + ((-1350000) * (t ^ 2)) + ((-843750) * t) + (4050000 * (t ^ 3))) : ℝ) := by
    have hid : ((421875 + ((-1350000) * (t ^ 2)) + ((-843750) * t) + (4050000 * (t ^ 3))) : ℝ) = (2555897833476099 / 40000000000) + ((511184230705449 / 8000000000) * z ^ 0 * (1-z) ^ 3) + ((7667740127045439 / 40000000000) * z ^ 1 * (1-z) ^ 2) + ((7667716806994131 / 40000000000) * z ^ 2 * (1-z) ^ 1) + ((2555897833476099 / 40000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : -((225*ell t+50-75*b t)/50+78*ell t-49*b t-73)/300 - (1 / 25000) = ((-152595) + ((-2609196) * (t ^ 2)) + (1205815 * t) + (1797588 * (t ^ 3))) / (421875 + ((-1350000) * (t ^ 2)) + ((-843750) * t) + (4050000 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < -((225*ell t+50-75*b t)/50+78*ell t-49*b t-73)/300 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma intermediate_buffer_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < -((225*ell t+50-75*b t)*(19/25)+78*ell t-49*b t-73)/300 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-4342635) + ((-44183568) * (t ^ 2)) + (20374704 * (t ^ 3)) + (25325270 * t)) : ℝ) := by
    have hid : (((-4342635) + ((-44183568) * (t ^ 2)) + (20374704 * (t ^ 3)) + (25325270 * t)) : ℝ) = (173747812553403791 / 15625000000000) + ((173747812553403791 / 15625000000000) * z ^ 0 * (1-z) ^ 3) + ((52127733889654391 / 1562500000000) * z ^ 1 * (1-z) ^ 2) + ((1042622416415876147 / 31250000000000) * z ^ 2 * (1-z) ^ 1) + ((695126727460465237 / 62500000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((3375000 + ((-10800000) * (t ^ 2)) + ((-6750000) * t) + (32400000 * (t ^ 3))) : ℝ) := by
    have hid : ((3375000 + ((-10800000) * (t ^ 2)) + ((-6750000) * t) + (32400000 * (t ^ 3))) : ℝ) = (2555897833476099 / 5000000000) + ((511184230705449 / 1000000000) * z ^ 0 * (1-z) ^ 3) + ((7667740127045439 / 5000000000) * z ^ 1 * (1-z) ^ 2) + ((7667716806994131 / 5000000000) * z ^ 2 * (1-z) ^ 1) + ((2555897833476099 / 5000000000) * z ^ 3 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : -((225*ell t+50-75*b t)*(19/25)+78*ell t-49*b t-73)/300 - (1 / 25000) = ((-4342635) + ((-44183568) * (t ^ 2)) + (20374704 * (t ^ 3)) + (25325270 * t)) / (3375000 + ((-10800000) * (t ^ 2)) + ((-6750000) * t) + (32400000 * (t ^ 3))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < -((225*ell t+50-75*b t)*(19/25)+78*ell t-49*b t-73)/300 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma c_positive_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < c t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((2499980 + ((-7799943) * t) + (3599982 * (t ^ 2))) : ℝ) := by
    have hid : ((2499980 + ((-7799943) * t) + (3599982 * (t ^ 2))) : ℝ) = (63026543753071 / 10000000000) + ((63526758251977 / 10000000000) * z ^ 0 * (1-z) ^ 2) + ((63276649202533 / 5000000000) * z ^ 1 * (1-z) ^ 1) + ((63026543753071 / 10000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((500000 + ((-1425000) * t) + (450000 * (t ^ 2))) : ℝ) := by
    have hid : ((500000 + ((-1425000) * t) + (450000 * (t ^ 2))) : ℝ) = (2842046929 / 400000) + ((2846348023 / 400000) * z ^ 0 * (1-z) ^ 2) + ((2844197467 / 200000) * z ^ 1 * (1-z) ^ 1) + ((2842046929 / 400000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : c t - (1 / 25000) = (2499980 + ((-7799943) * t) + (3599982 * (t ^ 2))) / (500000 + ((-1425000) * t) + (450000 * (t ^ 2))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < c t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma c_upper_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < 1-c t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-2000020) + ((-3150018) * (t ^ 2)) + (6375057 * t)) : ℝ) := by
    have hid : (((-2000020) + ((-3150018) * (t ^ 2)) + (6375057 * t)) : ℝ) = (1955649375631 / 2500000000) + ((1955649375631 / 2500000000) * z ^ 0 * (1-z) ^ 2) + ((200473673827 / 125000000) * z ^ 1 * (1-z) ^ 1) + ((4107646626809 / 5000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((500000 + ((-1425000) * t) + (450000 * (t ^ 2))) : ℝ) := by
    have hid : ((500000 + ((-1425000) * t) + (450000 * (t ^ 2))) : ℝ) = (2842046929 / 400000) + ((2846348023 / 400000) * z ^ 0 * (1-z) ^ 2) + ((2844197467 / 200000) * z ^ 1 * (1-z) ^ 1) + ((2842046929 / 400000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : 1-c t - (1 / 25000) = ((-2000020) + ((-3150018) * (t ^ 2)) + (6375057 * t)) / (500000 + ((-1425000) * t) + (450000 * (t ^ 2))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < 1-c t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
def capacity_inverse (t : ℝ) : ℝ := (((-25) + ((-36) * (t ^ 2)) + (78 * t)) / (135 * t * ((-1) + (2 * t))))
lemma capacity_inverse_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < capacity_inverse t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((125000 + ((-390027) * t) + (180054 * (t ^ 2))) : ℝ) := by
    have hid : ((125000 + ((-390027) * t) + (180054 * (t ^ 2))) : ℝ) = (3139780230787 / 10000000000) + ((3164789674069 / 10000000000) * z ^ 0 * (1-z) ^ 2) + ((3152284862401 / 5000000000) * z ^ 1 * (1-z) ^ 1) + ((3139780230787 / 10000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((((-1350000) * (t ^ 2)) + (675000 * t)) : ℝ) := by
    have hid : ((((-1350000) * (t ^ 2)) + (675000 * t)) : ℝ) = (11689059213 / 400000) + ((11690555931 / 400000) * z ^ 0 * (1-z) ^ 2) + ((11689807599 / 200000) * z ^ 1 * (1-z) ^ 1) + ((11689059213 / 400000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : capacity_inverse t - (1 / 25000) = (125000 + ((-390027) * t) + (180054 * (t ^ 2))) / (((-1350000) * (t ^ 2)) + (675000 * t)) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < capacity_inverse t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma capacity_plain_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < 1/5-c t/12 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-325060) + ((-630054) * (t ^ 2)) + (1095171 * t)) : ℝ) := by
    have hid : (((-325060) + ((-630054) * (t ^ 2)) + (1095171 * t)) : ℝ) = (6708638936893 / 2500000000) + ((6708638936893 / 2500000000) * z ^ 0 * (1-z) ^ 2) + ((671620791481 / 125000000) * z ^ 1 * (1-z) ^ 1) + ((13447553470427 / 5000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((1500000 + ((-4275000) * t) + (1350000 * (t ^ 2))) : ℝ) := by
    have hid : ((1500000 + ((-4275000) * t) + (1350000 * (t ^ 2))) : ℝ) = (8526140787 / 400000) + ((8539044069 / 400000) * z ^ 0 * (1-z) ^ 2) + ((8532592401 / 200000) * z ^ 1 * (1-z) ^ 1) + ((8526140787 / 400000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : 1/5-c t/12 - (1 / 25000) = ((-325060) + ((-630054) * (t ^ 2)) + (1095171 * t)) / (1500000 + ((-4275000) * t) + (1350000 * (t ^ 2))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < 1/5-c t/12 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma J_buffer_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < (5/6-19/25)*(5-c t)/2+(19/25)*(1-c t/4)-3/5 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-395020) + ((-661518) * (t ^ 2)) + (1278807 * t)) : ℝ) := by
    have hid : (((-395020) + ((-661518) * (t ^ 2)) + (1278807 * t)) : ℝ) = (2516624639881 / 2500000000) + ((2516624639881 / 2500000000) * z ^ 0 * (1-z) ^ 2) + ((252618341077 / 125000000) * z ^ 1 * (1-z) ^ 1) + ((5071484032559 / 5000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((500000 + ((-1425000) * t) + (450000 * (t ^ 2))) : ℝ) := by
    have hid : ((500000 + ((-1425000) * t) + (450000 * (t ^ 2))) : ℝ) = (2842046929 / 400000) + ((2846348023 / 400000) * z ^ 0 * (1-z) ^ 2) + ((2844197467 / 200000) * z ^ 1 * (1-z) ^ 1) + ((2842046929 / 400000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : (5/6-19/25)*(5-c t)/2+(19/25)*(1-c t/4)-3/5 - (1 / 25000) = ((-395020) + ((-661518) * (t ^ 2)) + (1278807 * t)) / (500000 + ((-1425000) * t) + (450000 * (t ^ 2))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < (5/6-19/25)*(5-c t)/2+(19/25)*(1-c t/4)-3/5 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma rounding_D_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < 3-(1+c t)*(51/100)-2 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-1030020) + ((-1615518) * (t ^ 2)) + (3279807 * t)) : ℝ) := by
    have hid : (((-1030020) + ((-1615518) * (t ^ 2)) + (3279807 * t)) : ℝ) = (641508082881 / 2500000000) + ((641508082881 / 2500000000) * z ^ 0 * (1-z) ^ 2) + ((66681172077 / 125000000) * z ^ 1 * (1-z) ^ 1) + ((1384229909559 / 5000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((500000 + ((-1425000) * t) + (450000 * (t ^ 2))) : ℝ) := by
    have hid : ((500000 + ((-1425000) * t) + (450000 * (t ^ 2))) : ℝ) = (2842046929 / 400000) + ((2846348023 / 400000) * z ^ 0 * (1-z) ^ 2) + ((2844197467 / 200000) * z ^ 1 * (1-z) ^ 1) + ((2842046929 / 400000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : 3-(1+c t)*(51/100)-2 - (1 / 25000) = ((-1030020) + ((-1615518) * (t ^ 2)) + (3279807 * t)) / (500000 + ((-1425000) * t) + (450000 * (t ^ 2))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < 3-(1+c t)*(51/100)-2 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma rounding_P_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < (2-c t*(51/100))*(49/100)-3/4 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-509770) + ((-796158) * (t ^ 2)) + (1621527 * t)) : ℝ) := by
    have hid : (((-509770) + ((-796158) * (t ^ 2)) + (1621527 * t)) : ℝ) = (134436359761 / 2500000000) + ((134436359761 / 2500000000) * z ^ 0 * (1-z) ^ 2) + ((14697117037 / 125000000) * z ^ 1 * (1-z) ^ 1) + ((319011563879 / 5000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((500000 + ((-1425000) * t) + (450000 * (t ^ 2))) : ℝ) := by
    have hid : ((500000 + ((-1425000) * t) + (450000 * (t ^ 2))) : ℝ) = (2842046929 / 400000) + ((2846348023 / 400000) * z ^ 0 * (1-z) ^ 2) + ((2844197467 / 200000) * z ^ 1 * (1-z) ^ 1) + ((2842046929 / 400000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : (2-c t*(51/100))*(49/100)-3/4 - (1 / 25000) = ((-509770) + ((-796158) * (t ^ 2)) + (1621527 * t)) / (500000 + ((-1425000) * t) + (450000 * (t ^ 2))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < (2-c t*(51/100))*(49/100)-3/4 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma kappa_lower_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < kappa t-13/18 := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-3312725) + ((-5175324) * (t ^ 2)) + (10538202 * t)) : ℝ) := by
    have hid : (((-3312725) + ((-5175324) * (t ^ 2)) + (10538202 * t)) : ℝ) = (477816311929 / 1250000000) + ((477816311929 / 1250000000) * z ^ 0 * (1-z) ^ 2) + ((51854223193 / 62500000) * z ^ 1 * (1-z) ^ 1) + ((1118535010031 / 2500000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((5625000 + ((-17550000) * t) + (8100000 * (t ^ 2))) : ℝ) := by
    have hid : ((5625000 + ((-17550000) * t) + (8100000 * (t ^ 2))) : ℝ) = (2836322361 / 200000) + ((2858832207 / 200000) * z ^ 0 * (1-z) ^ 2) + ((2847577203 / 100000) * z ^ 1 * (1-z) ^ 1) + ((2836322361 / 200000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : kappa t-13/18 - (1 / 25000) = ((-3312725) + ((-5175324) * (t ^ 2)) + (10538202 * t)) / (5625000 + ((-17550000) * t) + (8100000 * (t ^ 2))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < kappa t-13/18 - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma kappa_upper_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < 4/5-kappa t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((1249925 + ((-3967266) * t) + (1934892 * (t ^ 2))) : ℝ) := by
    have hid : ((1249925 + ((-3967266) * t) + (1934892 * (t ^ 2))) : ℝ) = (1145076992963 / 5000000000) + ((1268253292181 / 5000000000) * z ^ 0 * (1-z) ^ 2) + ((1206664658849 / 2500000000) * z ^ 1 * (1-z) ^ 1) + ((1145076992963 / 5000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((1875000 + ((-5850000) * t) + (2700000 * (t ^ 2))) : ℝ) := by
    have hid : ((1875000 + ((-5850000) * t) + (2700000 * (t ^ 2))) : ℝ) = (945440787 / 200000) + ((952944069 / 200000) * z ^ 0 * (1-z) ^ 2) + ((949192401 / 100000) * z ^ 1 * (1-z) ^ 1) + ((945440787 / 200000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : 4/5-kappa t - (1 / 25000) = (1249925 + ((-3967266) * t) + (1934892 * (t ^ 2))) / (1875000 + ((-5850000) * t) + (2700000 * (t ^ 2))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < 4/5-kappa t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma critical_denominator_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < critical_denominator t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((624999 / 25000) + ((-78) * t) + (36 * (t ^ 2))) : ℝ) := by
    have hid : (((624999 / 25000) + ((-78) * t) + (36 * (t ^ 2))) : ℝ) = (315046929 / 5000000000) + ((317548023 / 5000000000) * z ^ 0 * (1-z) ^ 2) + ((316297467 / 2500000000) * z ^ 1 * (1-z) ^ 1) + ((315046929 / 5000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < (1 : ℝ) := by
    have hid : (1 : ℝ) = (1 / 2) + ((1 / 2) * z ^ 0 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : critical_denominator t - (1 / 25000) = ((624999 / 25000) + ((-78) * t) + (36 * (t ^ 2))) / 1 := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < critical_denominator t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma kappa_derivative_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < kappa_derivative t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((561875 + ((-2246100) * t) + ((-1296) * (t ^ 4)) + (5616 * (t ^ 3)) + (2692116 * (t ^ 2))) : ℝ) := by
    have hid : ((561875 + ((-2246100) * t) + ((-1296) * (t ^ 4)) + (5616 * (t ^ 3)) + (2692116 * (t ^ 2))) : ℝ) = (599239949869913141868959 / 12500000000000000000) + ((599258903415361219789889 / 12500000000000000000) * z ^ 0 * (1-z) ^ 4) + ((119850832837206796357309 / 625000000000000000) * z ^ 1 * (1-z) ^ 3) + ((1797748276556050645885899 / 6250000000000000000) * z ^ 2 * (1-z) ^ 2) + ((599244687413309931571157 / 3125000000000000000) * z ^ 3 * (1-z) ^ 1) + ((599239949869913141868959 / 12500000000000000000) * z ^ 4 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((15625000 + ((-140400000) * (t ^ 3)) + ((-97500000) * t) + (32400000 * (t ^ 4)) + (197100000 * (t ^ 2))) : ℝ) := by
    have hid : ((15625000 + ((-140400000) * (t ^ 3)) + ((-97500000) * t) + (32400000 * (t ^ 4)) + (197100000 * (t ^ 2))) : ℝ) = (99317586858131041 / 500000000000000) + ((100897138780210111 / 500000000000000) * z ^ 0 * (1-z) ^ 4) + ((20100293203642691 / 25000000000000) * z ^ 1 * (1-z) ^ 3) + ((300318949354114101 / 250000000000000) * z ^ 2 * (1-z) ^ 2) + ((99711690068428843 / 125000000000000) * z ^ 3 * (1-z) ^ 1) + ((99317586858131041 / 500000000000000) * z ^ 4 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : kappa_derivative t - (1 / 25000) = (561875 + ((-2246100) * t) + ((-1296) * (t ^ 4)) + (5616 * (t ^ 3)) + (2692116 * (t ^ 2))) / (15625000 + ((-140400000) * (t ^ 3)) + ((-97500000) * t) + (32400000 * (t ^ 4)) + (197100000 * (t ^ 2))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < kappa_derivative t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma boundary_derivative_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < boundary_derivative t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < ((99991 + ((-36) * t) + ((-36) * (t ^ 2))) : ℝ) := by
    have hid : ((99991 + ((-36) * t) + ((-36) * (t ^ 2))) : ℝ) = (249928936703071 / 5000000000) + ((249928939901977 / 5000000000) * z ^ 0 * (1-z) ^ 2) + ((249928938302533 / 2500000000) * z ^ 1 * (1-z) ^ 1) + ((249928936703071 / 5000000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((225000 + (900000 * t) + (900000 * (t ^ 2))) : ℝ) := by
    have hid : ((225000 + (900000 * t) + (900000 * (t ^ 2))) : ℝ) = (17765424369 / 50000) + ((17765424369 / 50000) * z ^ 0 * (1-z) ^ 2) + ((1776582423 / 2500) * z ^ 1 * (1-z) ^ 1) + ((35532448191 / 100000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : boundary_derivative t - (1 / 25000) = (99991 + ((-36) * t) + ((-36) * (t ^ 2))) / (225000 + (900000 * t) + (900000 * (t ^ 2))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < boundary_derivative t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma contraction_derivative_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < contraction_derivative t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-62494943125) + ((-788436403056) * (t ^ 2)) + ((-129502893312) * (t ^ 4)) + ((-46656) * (t ^ 6)) + (155520 * (t ^ 5)) + (390000012600 * t) + (561616107120 * (t ^ 3))) : ℝ) := by
    have hid : (((-62494943125) + ((-788436403056) * (t ^ 2)) + ((-129502893312) * (t ^ 4)) + ((-46656) * (t ^ 6)) + (155520 * (t ^ 5)) + (390000012600 * t) + (561616107120 * (t ^ 3))) : ℝ) = (274325636936763964170781797614591 / 488281250000000000000000000) + ((274325636936763964170781797614591 / 488281250000000000000000000) * z ^ 0 * (1-z) ^ 6) + ((82607255599055489029644681985191 / 24414062500000000000000000) * z ^ 1 * (1-z) ^ 5) + ((1658331498762537427398590890719747 / 195312500000000000000000000) * z ^ 2 * (1-z) ^ 4) + ((1109675321345099368074255667400837 / 97656250000000000000000000) * z ^ 3 * (1-z) ^ 3) + ((6682758247196906913863670794385429 / 781250000000000000000000000) * z ^ 4 * (1-z) ^ 2) + ((2682977981056083643619015965787991 / 781250000000000000000000000) * z ^ 5 * (1-z) ^ 1) + ((8976149392815505420608117901459999 / 15625000000000000000000000000) * z ^ 6 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < ((140625000 + ((-3888000000) * (t ^ 5)) + ((-1173600000) * (t ^ 2)) + ((-315000000) * t) + (1166400000 * (t ^ 6)) + (2322000000 * (t ^ 3)) + (2332800000 * (t ^ 4))) : ℝ) := by
    have hid : ((140625000 + ((-3888000000) * (t ^ 5)) + ((-1173600000) * (t ^ 2)) + ((-315000000) * t) + (1166400000 * (t ^ 6)) + (2322000000 * (t ^ 3)) + (2332800000 * (t ^ 4))) : ℝ) = (7057835165171114364574873089 / 1250000000000000000000000) + ((7169763098381025565330459263 / 1250000000000000000000000) * z ^ 0 * (1-z) ^ 6) + ((21453215055038894204662857021 / 625000000000000000000000) * z ^ 1 * (1-z) ^ 5) + ((21397184923972911892630347357 / 250000000000000000000000) * z ^ 2 * (1-z) ^ 4) + ((1422746593481083501939875939 / 12500000000000000000000) * z ^ 3 * (1-z) ^ 3) + ((21285256990040032434778295829 / 250000000000000000000000) * z ^ 4 * (1-z) ^ 2) + ((21229359187715361481817619441 / 625000000000000000000000) * z ^ 5 * (1-z) ^ 1) + ((7057835165171114364574873089 / 1250000000000000000000000) * z ^ 6 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : contraction_derivative t - (1 / 25000) = ((-62494943125) + ((-788436403056) * (t ^ 2)) + ((-129502893312) * (t ^ 4)) + ((-46656) * (t ^ 6)) + (155520 * (t ^ 5)) + (390000012600 * t) + (561616107120 * (t ^ 3))) / (140625000 + ((-3888000000) * (t ^ 5)) + ((-1173600000) * (t ^ 2)) + ((-315000000) * t) + (1166400000 * (t ^ 6)) + (2322000000 * (t ^ 3)) + (2332800000 * (t ^ 4))) := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < contraction_derivative t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith
lemma cubic_decrease_lower (t : ℝ) (ht : InInterval t) : (1 / 25000) < cubic_decrease t := by
  let z := 100000*t-38858
  have hz : 0 ≤ z := by dsimp [z]; linarith [ht.1]
  have hz1 : 0 ≤ 1-z := by dsimp [z]; linarith [ht.2]
  have hn : 0 < (((-4275001 / 25000) + ((-3564) * (t ^ 2)) + (4320 * t)) : ℝ) := by
    have hid : (((-4275001 / 25000) + ((-3564) * (t ^ 2)) + (4320 * t)) : ℝ) = (605950912469 / 1250000000) + ((605950912469 / 1250000000) * z ^ 0 * (1-z) ^ 2) + ((60596060123 / 62500000) * z ^ 1 * (1-z) ^ 1) + ((1211940579091 / 2500000000) * z ^ 2 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have hd : 0 < (1 : ℝ) := by
    have hid : (1 : ℝ) = (1 / 2) + ((1 / 2) * z ^ 0 * (1-z) ^ 0) := by dsimp [z]; ring
    rw [hid]
    positivity
  have heq : cubic_decrease t - (1 / 25000) = ((-4275001 / 25000) + ((-3564) * (t ^ 2)) + (4320 * t)) / 1 := by
    simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
    apply (eq_div_iff (ne_of_gt hd)).2
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring
  have hp : 0 < cubic_decrease t - (1 / 25000) := by rw [heq]; exact div_pos hn hd
  linarith

def D (t v : ℝ) : ℝ := (5-c t)/2+(1+c t)*v
def P (t v : ℝ) : ℝ := 1-c t/4+2*v+c t*v^2
def J (t d v : ℝ) : ℝ := (5/6-d)*D t v+d*P t v
def R (t d v : ℝ) : ℝ := 1-d+(5/6-d)*d*P t v/(2*J t d v)
def E (t d v : ℝ) : ℝ := C0 t+(1/2+ell t)*d+ell t*(1/2-v)*d-h t*(1-R t d v)
def Q (t d v : ℝ) : ℝ := -2*C0 t*J t d v+(b t+2*ell t*v)*d*J t d v-h t*(5/6-d)*d*P t v
def Ac (t v : ℝ) : ℝ := Ac0 t+Ac1 t*v+Ac2 t*v^2+Ac3 t*v^3
def Bc (t v : ℝ) : ℝ := Bc0 t+Bc1 t*v+Bc2 t*v^2
def Cc (t v : ℝ) : ℝ := Cc0 t+Cc1 t*v
def Dc (t v : ℝ) : ℝ := Dc1 t*v+Dc2 t*v^2+Dc3 t*v^3+Dc4 t*v^4
lemma quadratic_identity (t d v : ℝ) (ht : InInterval t) : Q t d v = Ac t v*d^2+Bc t v*d+Cc t v := by
  simp only [Q, J, D, P, Ac, Bc, Cc, Dc, ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
  have hb0 := base0_pos t ht
  have hb1 := base1_pos t ht
  have hb2 := base2_pos t ht
  have hb3 := base3_pos t ht
  have hb01 := mul_pos hb0 hb1
  have hb02 := mul_pos hb0 hb2
  have hb12 := mul_pos hb1 hb2
  have hb012 := mul_pos hb0 hb12
  have hb03 := mul_pos hb0 hb3
  have hbt : 0 < t := by linarith [ht.1]
  have hbtc : 0 < 1-2*t := by linarith [ht.2]
  have hbtcprod := mul_pos hbt hbtc
  have hb0s := mul_pos hb0 hb0
  have hb1s := mul_pos hb1 hb1
  have hb2s := mul_pos hb2 hb2
  have hb3s := mul_pos hb3 hb3
  have hb01s := mul_pos hb01 hb01
  have hb02s := mul_pos hb02 hb02
  have hb12s := mul_pos hb12 hb12
  have hb012s := mul_pos hb012 hb012
  have hb03s := mul_pos hb03 hb03
  have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
  have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
  have hbtcneg : -1+2*t ≠ 0 := by linarith
  ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
  field_simp <;> ring_nf <;> field_simp <;> ring
lemma discriminant_identity (t d v : ℝ) (ht : InInterval t) : 4*Ac t v*Cc t v-(Bc t v)^2 = Dc t v := by
  simp only [Q, J, D, P, Ac, Bc, Cc, Dc, ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
  have hb0 := base0_pos t ht
  have hb1 := base1_pos t ht
  have hb2 := base2_pos t ht
  have hb3 := base3_pos t ht
  have hb01 := mul_pos hb0 hb1
  have hb02 := mul_pos hb0 hb2
  have hb12 := mul_pos hb1 hb2
  have hb012 := mul_pos hb0 hb12
  have hb03 := mul_pos hb0 hb3
  have hbt : 0 < t := by linarith [ht.1]
  have hbtc : 0 < 1-2*t := by linarith [ht.2]
  have hbtcprod := mul_pos hbt hbtc
  have hb0s := mul_pos hb0 hb0
  have hb1s := mul_pos hb1 hb1
  have hb2s := mul_pos hb2 hb2
  have hb3s := mul_pos hb3 hb3
  have hb01s := mul_pos hb01 hb01
  have hb02s := mul_pos hb02 hb02
  have hb12s := mul_pos hb12 hb12
  have hb012s := mul_pos hb012 hb012
  have hb03s := mul_pos hb03 hb03
  have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
  have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
  have hbtcneg : -1+2*t ≠ 0 := by linarith
  ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
  field_simp <;> ring_nf <;> field_simp <;> ring
lemma contact_identity (t d v : ℝ) (ht : InInterval t) : Q t d 0 = Ac0 t*(d-t)^2 := by
  simp only [Q, J, D, P, Ac, Bc, Cc, Dc, ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
  have hb0 := base0_pos t ht
  have hb1 := base1_pos t ht
  have hb2 := base2_pos t ht
  have hb3 := base3_pos t ht
  have hb01 := mul_pos hb0 hb1
  have hb02 := mul_pos hb0 hb2
  have hb12 := mul_pos hb1 hb2
  have hb012 := mul_pos hb0 hb12
  have hb03 := mul_pos hb0 hb3
  have hbt : 0 < t := by linarith [ht.1]
  have hbtc : 0 < 1-2*t := by linarith [ht.2]
  have hbtcprod := mul_pos hbt hbtc
  have hb0s := mul_pos hb0 hb0
  have hb1s := mul_pos hb1 hb1
  have hb2s := mul_pos hb2 hb2
  have hb3s := mul_pos hb3 hb3
  have hb01s := mul_pos hb01 hb01
  have hb02s := mul_pos hb02 hb02
  have hb12s := mul_pos hb12 hb12
  have hb012s := mul_pos hb012 hb012
  have hb03s := mul_pos hb03 hb03
  have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
  have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
  have hbtcneg : -1+2*t ≠ 0 := by linarith
  ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
  field_simp <;> ring_nf <;> field_simp <;> ring

lemma Ac_positive (t v : ℝ) (ht : InInterval t) (hv : 0 ≤ v) : 0 < Ac t v := by
  have h0 := Ac0_lower t ht
  have h1 := Ac1_lower t ht
  have h2 := Ac2_lower t ht
  have h3 := Ac3_lower t ht
  unfold Ac
  positivity
lemma Dc_nonnegative (t v : ℝ) (ht : InInterval t) (hv : 0 ≤ v) : 0 ≤ Dc t v := by
  have h1 := Dc1_lower t ht
  have h2 := Dc2_lower t ht
  have h3 := Dc3_lower t ht
  have h4 := Dc4_lower t ht
  unfold Dc
  positivity
lemma Dc_positive (t v : ℝ) (ht : InInterval t) (hv : 0 < v) : 0 < Dc t v := by
  have h1 := Dc1_lower t ht
  have h2 := Dc2_lower t ht
  have h3 := Dc3_lower t ht
  have h4 := Dc4_lower t ht
  unfold Dc
  positivity
lemma complete_square (t d v : ℝ) (ht : InInterval t) :
    4*Ac t v*Q t d v = (2*Ac t v*d+Bc t v)^2+Dc t v := by
  rw [quadratic_identity t d v ht, ← discriminant_identity t d v ht]
  ring
lemma Q_nonnegative (t d v : ℝ) (ht : InInterval t) (hv : 0 ≤ v) : 0 ≤ Q t d v := by
  have hA := Ac_positive t v ht hv
  have hD := Dc_nonnegative t v ht hv
  have hs := complete_square t d v ht
  have hsq := sq_nonneg (2*Ac t v*d+Bc t v)
  have hm : 0 ≤ 4*Ac t v*Q t d v := by linarith
  exact nonneg_of_mul_nonneg_right hm (by positivity)
lemma J_positive (t d v : ℝ) (ht : InInterval t) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 5/6) (hv : 0 ≤ v) : 0 < J t d v := by
  have hc0 : 0 < c t := by linarith [c_positive_lower t ht]
  have hc1 : c t < 1 := by linarith [c_upper_lower t ht]
  have hD : 2 ≤ D t v := by unfold D; nlinarith [mul_nonneg (by linarith : 0 ≤ 1+c t) hv]
  have hP : 3/4 ≤ P t v := by unfold P; nlinarith [mul_nonneg (le_of_lt hc0) (sq_nonneg v)]
  have h1 := mul_nonneg (by linarith : 0 ≤ 5/6-d) (by linarith : 0 ≤ D t v-2)
  have h2 := mul_nonneg hd0 (by linarith : 0 ≤ P t v-3/4)
  unfold J
  nlinarith
lemma exponent_identity (t d v : ℝ) (ht : InInterval t) (hj : J t d v ≠ 0) :
    Q t d v = -2*J t d v*E t d v := by
  unfold Q E R
  field_simp [hj]
  simp only [J, D, P, C0, b, ell, h, c]
  have hb0 := base0_pos t ht
  have hb1 := base1_pos t ht
  have hb2 := base2_pos t ht
  have hb3 := base3_pos t ht
  have hb01 := mul_pos hb0 hb1
  have hb02 := mul_pos hb0 hb2
  have hb12 := mul_pos hb1 hb2
  have hb012 := mul_pos hb0 hb12
  have hb03 := mul_pos hb0 hb3
  have hbt : 0 < t := by linarith [ht.1]
  have hbtc : 0 < 1-2*t := by linarith [ht.2]
  have hbtcprod := mul_pos hbt hbtc
  have hb0s := mul_pos hb0 hb0
  have hb1s := mul_pos hb1 hb1
  have hb2s := mul_pos hb2 hb2
  have hb3s := mul_pos hb3 hb3
  have hb01s := mul_pos hb01 hb01
  have hb02s := mul_pos hb02 hb02
  have hb12s := mul_pos hb12 hb12
  have hb012s := mul_pos hb012 hb012
  have hb03s := mul_pos hb03 hb03
  have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
  have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
  have hbtcneg : -1+2*t ≠ 0 := by linarith
  ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
  field_simp <;> ring_nf <;> field_simp <;> ring

/-- The endpoint exponent is nonpositive on the full deficit/amplitude rectangle.
The amplitude used in the manuscript is x=1/2-v. -/
theorem universal_endpoint (t d v : ℝ) (ht : InInterval t) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 5/6) (hv : 0 ≤ v) : E t d v ≤ 0 := by
  have hj := J_positive t d v ht hd0 hd1 hv
  have hq := Q_nonnegative t d v ht hv
  rw [exponent_identity t d v ht (ne_of_gt hj)] at hq
  nlinarith

theorem side_reserves (t : ℝ) (ht : InInterval t) :
    0 < b t ∧ 0 < ell t ∧ ell t < 1/5 ∧
    0 < lx t-b t-ell t ∧ 11*b t/6 < ly t-ell t ∧
    h t < 1 ∧ h t < 5*ell t ∧ 437/500 < boundary t ∧ boundary t < 7/8 := by
  have hb := b_positive_lower t ht
  have hl := ell_positive_lower t ht
  have hlu := ell_upper_lower t ht
  have hx := lx_reserve_lower t ht
  have hg := gram_reserve_lower t ht
  have hh := h_upper_lower t ht
  have hs := supply_lower t ht
  have hbl := boundary_principal_lower t ht
  have hbu := boundary_upper_lower t ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
lemma geometry_lx (t : ℝ) (ht : InInterval t) : lx t = (1-b t-ell t)/2 := by
  simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
  have hb0 := base0_pos t ht
  have hb1 := base1_pos t ht
  have hb2 := base2_pos t ht
  have hb3 := base3_pos t ht
  have hb01 := mul_pos hb0 hb1
  have hb02 := mul_pos hb0 hb2
  have hb12 := mul_pos hb1 hb2
  have hb012 := mul_pos hb0 hb12
  have hb03 := mul_pos hb0 hb3
  have hbt : 0 < t := by linarith [ht.1]
  have hbtc : 0 < 1-2*t := by linarith [ht.2]
  have hbtcprod := mul_pos hbt hbtc
  have hb0s := mul_pos hb0 hb0
  have hb1s := mul_pos hb1 hb1
  have hb2s := mul_pos hb2 hb2
  have hb3s := mul_pos hb3 hb3
  have hb01s := mul_pos hb01 hb01
  have hb02s := mul_pos hb02 hb02
  have hb12s := mul_pos hb12 hb12
  have hb012s := mul_pos hb012 hb012
  have hb03s := mul_pos hb03 hb03
  have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
  have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
  have hbtcneg : -1+2*t ≠ 0 := by linarith
  ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
  field_simp <;> ring_nf <;> field_simp <;> ring
lemma geometry_ly (t : ℝ) (ht : InInterval t) : ly t = lx t+b t := by
  simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
  have hb0 := base0_pos t ht
  have hb1 := base1_pos t ht
  have hb2 := base2_pos t ht
  have hb3 := base3_pos t ht
  have hb01 := mul_pos hb0 hb1
  have hb02 := mul_pos hb0 hb2
  have hb12 := mul_pos hb1 hb2
  have hb012 := mul_pos hb0 hb12
  have hb03 := mul_pos hb0 hb3
  have hbt : 0 < t := by linarith [ht.1]
  have hbtc : 0 < 1-2*t := by linarith [ht.2]
  have hbtcprod := mul_pos hbt hbtc
  have hb0s := mul_pos hb0 hb0
  have hb1s := mul_pos hb1 hb1
  have hb2s := mul_pos hb2 hb2
  have hb3s := mul_pos hb3 hb3
  have hb01s := mul_pos hb01 hb01
  have hb02s := mul_pos hb02 hb02
  have hb12s := mul_pos hb12 hb12
  have hb012s := mul_pos hb012 hb012
  have hb03s := mul_pos hb03 hb03
  have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
  have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
  have hbtcneg : -1+2*t ≠ 0 := by linarith
  ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
  field_simp <;> ring_nf <;> field_simp <;> ring
lemma geometry_h (t : ℝ) (ht : InInterval t) : h t = 1-lx t+ell t := by
  simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
  have hb0 := base0_pos t ht
  have hb1 := base1_pos t ht
  have hb2 := base2_pos t ht
  have hb3 := base3_pos t ht
  have hb01 := mul_pos hb0 hb1
  have hb02 := mul_pos hb0 hb2
  have hb12 := mul_pos hb1 hb2
  have hb012 := mul_pos hb0 hb12
  have hb03 := mul_pos hb0 hb3
  have hbt : 0 < t := by linarith [ht.1]
  have hbtc : 0 < 1-2*t := by linarith [ht.2]
  have hbtcprod := mul_pos hbt hbtc
  have hb0s := mul_pos hb0 hb0
  have hb1s := mul_pos hb1 hb1
  have hb2s := mul_pos hb2 hb2
  have hb3s := mul_pos hb3 hb3
  have hb01s := mul_pos hb01 hb01
  have hb02s := mul_pos hb02 hb02
  have hb12s := mul_pos hb12 hb12
  have hb012s := mul_pos hb012 hb012
  have hb03s := mul_pos hb03 hb03
  have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
  have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
  have hbtcneg : -1+2*t ≠ 0 := by linarith
  ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
  field_simp <;> ring_nf <;> field_simp <;> ring
lemma geometry_C0 (t : ℝ) (ht : InInterval t) : C0 t = -1/4+b t/6+5*ell t/4 := by
  simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
  have hb0 := base0_pos t ht
  have hb1 := base1_pos t ht
  have hb2 := base2_pos t ht
  have hb3 := base3_pos t ht
  have hb01 := mul_pos hb0 hb1
  have hb02 := mul_pos hb0 hb2
  have hb12 := mul_pos hb1 hb2
  have hb012 := mul_pos hb0 hb12
  have hb03 := mul_pos hb0 hb3
  have hbt : 0 < t := by linarith [ht.1]
  have hbtc : 0 < 1-2*t := by linarith [ht.2]
  have hbtcprod := mul_pos hbt hbtc
  have hb0s := mul_pos hb0 hb0
  have hb1s := mul_pos hb1 hb1
  have hb2s := mul_pos hb2 hb2
  have hb3s := mul_pos hb3 hb3
  have hb01s := mul_pos hb01 hb01
  have hb02s := mul_pos hb02 hb02
  have hb12s := mul_pos hb12 hb12
  have hb012s := mul_pos hb012 hb012
  have hb03s := mul_pos hb03 hb03
  have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
  have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
  have hbtcneg : -1+2*t ≠ 0 := by linarith
  ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
  field_simp <;> ring_nf <;> field_simp <;> ring
lemma geometry_boundary (t : ℝ) (ht : InInterval t) : boundary t = 11/12-ell t/4 := by
  simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
  have hb0 := base0_pos t ht
  have hb1 := base1_pos t ht
  have hb2 := base2_pos t ht
  have hb3 := base3_pos t ht
  have hb01 := mul_pos hb0 hb1
  have hb02 := mul_pos hb0 hb2
  have hb12 := mul_pos hb1 hb2
  have hb012 := mul_pos hb0 hb12
  have hb03 := mul_pos hb0 hb3
  have hbt : 0 < t := by linarith [ht.1]
  have hbtc : 0 < 1-2*t := by linarith [ht.2]
  have hbtcprod := mul_pos hbt hbtc
  have hb0s := mul_pos hb0 hb0
  have hb1s := mul_pos hb1 hb1
  have hb2s := mul_pos hb2 hb2
  have hb3s := mul_pos hb3 hb3
  have hb01s := mul_pos hb01 hb01
  have hb02s := mul_pos hb02 hb02
  have hb12s := mul_pos hb12 hb12
  have hb012s := mul_pos hb012 hb012
  have hb03s := mul_pos hb03 hb03
  have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
  have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
  have hbtcneg : -1+2*t ≠ 0 := by linarith
  ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
  field_simp <;> ring_nf <;> field_simp <;> ring
lemma moment_coefficient (t : ℝ) (ht : InInterval t) : c t = 2/(3*kappa t) := by
  simp only [ell, boundary, kappa, b, c, lx, ly, h, C0, Ac0, Ac1, Ac2, Ac3, Bc0, Bc1, Bc2, Cc0, Cc1, Dc1, Dc2, Dc3, Dc4, critical_denominator, kappa_derivative, boundary_derivative, contraction_derivative, cubic_decrease, capacity_inverse]
  have hb0 := base0_pos t ht
  have hb1 := base1_pos t ht
  have hb2 := base2_pos t ht
  have hb3 := base3_pos t ht
  have hb01 := mul_pos hb0 hb1
  have hb02 := mul_pos hb0 hb2
  have hb12 := mul_pos hb1 hb2
  have hb012 := mul_pos hb0 hb12
  have hb03 := mul_pos hb0 hb3
  have hbt : 0 < t := by linarith [ht.1]
  have hbtc : 0 < 1-2*t := by linarith [ht.2]
  have hbtcprod := mul_pos hbt hbtc
  have hb0s := mul_pos hb0 hb0
  have hb1s := mul_pos hb1 hb1
  have hb2s := mul_pos hb2 hb2
  have hb3s := mul_pos hb3 hb3
  have hb01s := mul_pos hb01 hb01
  have hb02s := mul_pos hb02 hb02
  have hb12s := mul_pos hb12 hb12
  have hb012s := mul_pos hb012 hb012
  have hb03s := mul_pos hb03 hb03
  have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
  have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
  have hbtcneg : -1+2*t ≠ 0 := by linarith
  ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
  field_simp <;> ring_nf <;> field_simp <;> ring
lemma capacity_inverse_identity (t : ℝ) (ht : InInterval t) : capacity_inverse t = 1/5-(4-c t)/(20-4*c t) := by
  have hcden : 20-4*c t ≠ 0 := by
    have hc := c_upper_lower t ht
    linarith
  have hid : (1/5-capacity_inverse t)*(20-4*c t) = 4-c t := by
    simp only [c, capacity_inverse]
    have hb0 := base0_pos t ht
    have hb1 := base1_pos t ht
    have hb2 := base2_pos t ht
    have hb3 := base3_pos t ht
    have hb01 := mul_pos hb0 hb1
    have hb02 := mul_pos hb0 hb2
    have hb12 := mul_pos hb1 hb2
    have hb012 := mul_pos hb0 hb12
    have hb03 := mul_pos hb0 hb3
    have hbt : 0 < t := by linarith [ht.1]
    have hbtc : 0 < 1-2*t := by linarith [ht.2]
    have hbtcprod := mul_pos hbt hbtc
    have hb0s := mul_pos hb0 hb0
    have hb1s := mul_pos hb1 hb1
    have hb2s := mul_pos hb2 hb2
    have hb3s := mul_pos hb3 hb3
    have hb01s := mul_pos hb01 hb01
    have hb02s := mul_pos hb02 hb02
    have hb12s := mul_pos hb12 hb12
    have hb012s := mul_pos hb012 hb012
    have hb03s := mul_pos hb03 hb03
    have hbtc108 := mul_pos (show (0:ℝ)<108 by norm_num) hbtcprod
    have hb3six := mul_pos (show (0:ℝ)<6 by norm_num) hb3
    have hbtcneg : -1+2*t ≠ 0 := by linarith
    ring_nf at hb0 hb1 hb2 hb3 hb01 hb02 hb12 hb012 hb03 hbt hbtc hbtcprod hb0s hb1s hb2s hb3s hb01s hb02s hb12s hb012s hb03s hb3six hbtcneg hbtc108
    field_simp <;> ring_nf <;> field_simp <;> ring_nf <;> field_simp <;> ring
  
  have hr := (eq_div_iff hcden).2 hid
  linarith
lemma Q_zero_iff (t d v : ℝ) (ht : InInterval t) (hv : 0 ≤ v) :
    Q t d v = 0 ↔ d = t ∧ v = 0 := by
  constructor
  · intro hq
    have hvz : v = 0 := by
      by_contra hn
      have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hn)
      have hD := Dc_positive t v ht hvp
      have hs := complete_square t d v ht
      rw [hq] at hs
      nlinarith [sq_nonneg (2*Ac t v*d+Bc t v)]
    subst v
    have hc : 0 < Ac0 t := by linarith [Ac0_lower t ht]
    have hfactor := contact_identity t d 0 ht
    rw [hq] at hfactor
    have hsq : (d-t)^2 = 0 := by
      have hz : Ac0 t*(d-t)^2 = 0 := hfactor.symm
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hc)
    constructor
    · nlinarith [sq_nonneg (d-t)]
    · rfl
  · rintro ⟨hd, hv⟩
    rw [hd, hv, contact_identity t t 0 ht]
    ring
/-- Equality is attained only at the tangent deficit and maximal amplitude. -/
theorem endpoint_equality (t d v : ℝ) (ht : InInterval t) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 5/6) (hv : 0 ≤ v) :
    E t d v = 0 ↔ d = t ∧ v = 0 := by
  have hj := J_positive t d v ht hd0 hd1 hv
  have hi := exponent_identity t d v ht (ne_of_gt hj)
  have hq : E t d v = 0 ↔ Q t d v = 0 := by
    constructor
    · intro he; rw [hi, he]; ring
    · intro he; rw [he] at hi; nlinarith
  exact hq.trans (Q_zero_iff t d v ht hv)
end
end CombineV22.Uniform

#print axioms CombineV22.Uniform.universal_endpoint
#print axioms CombineV22.Uniform.endpoint_equality
#print axioms CombineV22.Uniform.side_reserves

end PartIVBlock1

/- BEGIN consolidated Checkpoint.lean -/
section PartIVBlock2
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace CombineV22.Checkpoint
noncomputable section
/-! Proposition 34.6: exact rational certificate and its scalar consequences.
No analytic moment or zero-free conclusion is assumed or asserted here. -/
def kappa : ℝ := 74991414/100000000
def b : ℝ := 617/5000
def ell : ℝ := 5005157/30000000
def boundary : ℝ := 34998281/40000000
def lx : ℝ := (1-b-ell)/2
def ly : ℝ := lx+b
def h : ℝ := (1+b+3*ell)/2
def c : ℝ := 2/(3*kappa)
def C0 : ℝ := -1/4+b/6+5*ell/4
def D (x : ℝ) : ℝ := 3-(1+c)*x
def P (x : ℝ) : ℝ := (2-c*x)*(1-x)
def J (d x : ℝ) : ℝ := (5/6-d)*D x+d*P x
def R (d x : ℝ) : ℝ := 1-d+(5/6-d)*d*P x/(2*J d x)
def E (d x : ℝ) : ℝ := C0+(1/2+ell)*d+ell*x*d-h*(1-R d x)
def Q (d v : ℝ) : ℝ := -2*C0*J d (1/2-v)+(b+2*ell*v)*d*J d (1/2-v)-h*(5/6-d)*d*P (1/2-v)
def A (v : ℝ) : ℝ := (1065989771454997/2249742420000000 : ℝ) * v^0 + (1021881530971/843653407500 : ℝ) * v^1 + (1465536776082997/1687306815000000 : ℝ) * v^2 + (100103140/337461363 : ℝ) * v^3
def Bq (v : ℝ) : ℝ := (-165693258800201/449948484000000 : ℝ) * v^0 + (-2360120681859797/4049536356000000 : ℝ) * v^1 + (-79218923917003/2024768178000000 : ℝ) * v^2
def Cq (v : ℝ) : ℝ := (15452840663801/215975272320000 : ℝ) * v^0 + (35502560663801/539938180800000 : ℝ) * v^1
def disc (v : ℝ) : ℝ := (41201093701112639698391/303680457380847384000000000000 : ℝ) * v^0 + (2127747897368488079436299533/50613409563474564000000000000 : ℝ) * v^1 + (3257935189414802899824760796543/16398744698565758736000000000000 : ℝ) * v^2 + (219525369982742695890840084071/819937234928287936800000000000 : ℝ) * v^3 + (313576964137258889226167497991/4099686174641439684000000000000 : ℝ) * v^4
theorem quadratic_identity (d v : ℝ) : Q d v = A v*d^2+Bq v*d+Cq v := by
  norm_num [Q,J,D,P,C0,h,b,ell,c,kappa,A,Bq,Cq]
  ring
theorem discriminant_identity (v : ℝ) : 4*A v*Cq v-(Bq v)^2=disc v := by
  unfold A Cq Bq disc
  ring
theorem completed_square (d v : ℝ) :
    4*A v*Q d v=(2*A v*d+Bq v)^2+disc v := by
  rw [quadratic_identity, ← discriminant_identity]
  ring
theorem A_coefficient_bounds :
    (1/4 : ℝ) < (1065989771454997/2249742420000000 : ℝ) ∧
    (1/4 : ℝ) < (1021881530971/843653407500 : ℝ) ∧
    (1/4 : ℝ) < (1465536776082997/1687306815000000 : ℝ) ∧
    (1/4 : ℝ) < (100103140/337461363 : ℝ) := by norm_num
theorem A_pos (v : ℝ) (hv : 0 ≤ v) : 0 < A v := by
  unfold A
  positivity
theorem disc_coefficient_bounds :
    (1/10^7 : ℝ) < (41201093701112639698391/303680457380847384000000000000 : ℝ) ∧
    (1/10^7 : ℝ) < (2127747897368488079436299533/50613409563474564000000000000 : ℝ) ∧
    (1/10^7 : ℝ) < (3257935189414802899824760796543/16398744698565758736000000000000 : ℝ) ∧
    (1/10^7 : ℝ) < (219525369982742695890840084071/819937234928287936800000000000 : ℝ) ∧
    (1/10^7 : ℝ) < (313576964137258889226167497991/4099686174641439684000000000000 : ℝ) := by norm_num
theorem disc_pos (v : ℝ) (hv : 0 ≤ v) : 0 < disc v := by
  unfold disc
  positivity
theorem Q_pos (d v : ℝ) (hv : 0 ≤ v) : 0 < Q d v := by
  have ha := A_pos v hv
  have hd := disc_pos v hv
  have hh := completed_square d v
  have hs := sq_nonneg (2*A v*d+Bq v)
  have hp : 0 < 4*A v*Q d v := by linarith
  exact pos_of_mul_pos_right hp (by positivity)
theorem c_bounds : 0 < c ∧ c < 1 := by norm_num [c,kappa]
theorem D_lower (x : ℝ) (hx : x ≤ 1/2) : 2 < D x := by
  obtain ⟨hc,hc1⟩ := c_bounds
  have hh := mul_nonneg (show 0 ≤ 1+c by linarith) (show 0 ≤ 1/2-x by linarith)
  unfold D
  nlinarith
theorem P_lower (x : ℝ) (hx : x ≤ 1/2) : (3/4 : ℝ) < P x := by
  obtain ⟨hc,hc1⟩ := c_bounds
  have hh := mul_nonneg hc.le (sq_nonneg (1/2-x))
  unfold P
  nlinarith
theorem J_pos (d x : ℝ) (hd : 0 ≤ d) (hd1 : d ≤ 5/6)
    (hx : x ≤ 1/2) : 0 < J d x := by
  have hD := D_lower x hx
  have hP := P_lower x hx
  have hh := mul_nonneg (show 0 ≤ 5/6-d by linarith) (show 0 ≤ D x-2 by linarith)
  have hh2 := mul_nonneg hd (show 0 ≤ P x-3/4 by linarith)
  unfold J
  nlinarith
theorem physical_exponent_identity (d x : ℝ) (hj : J d x ≠ 0) :
    Q d (1/2-x) = -2*J d x*E d x := by
  unfold Q E R
  field_simp [hj]
  simp only [h]
  ring
theorem universal_endpoint (d x : ℝ) (hd : 0 ≤ d) (hd1 : d ≤ 5/6)
    (hx : x ≤ 1/2) : E d x < 0 := by
  have hj := J_pos d x hd hd1 hx
  have hq := Q_pos d (1/2-x) (by linarith)
  have he := physical_exponent_identity d x hj.ne'
  have hn : 0 < -E d x := pos_of_mul_pos_left (by nlinarith) (by positivity : 0 ≤ 2*J d x)
  linarith
theorem boundary_identity : boundary=11/12-ell/4 := by norm_num [boundary,ell]
theorem kappa_range : (13/18 : ℝ)< kappa ∧ kappa<3/4 := by norm_num [kappa]
theorem moment_premise : (1507-2*Real.sqrt 921)/1653 < (1+kappa)/2 := by
  have hs := Real.sqrt_nonneg (921:ℝ)
  have hsq : (Real.sqrt (921:ℝ))^2=921 := by norm_num [Real.sq_sqrt]
  norm_num [kappa]
  nlinarith
theorem improvement : boundary < (1507-2*Real.sqrt 921)/1653 := by
  have hs := Real.sqrt_nonneg (921:ℝ)
  have hsq : (Real.sqrt (921:ℝ))^2=921 := by norm_num [Real.sq_sqrt]
  norm_num [boundary]
  nlinarith
theorem side_certificate :
    (1/25000 : ℝ) < kappa-13/18 ∧
    (1/25000 : ℝ) < 4/5-kappa ∧
    (1/25000 : ℝ) < b ∧
    (1/25000 : ℝ) < ell ∧
    (1/25000 : ℝ) < 1/5-ell ∧
    (1/25000 : ℝ) < lx-b-ell ∧
    (1/25000 : ℝ) < ly-ell ∧
    (1/25000 : ℝ) < ly-ell-11*b/6 ∧
    (1/25000 : ℝ) < 1-h ∧
    (1/25000 : ℝ) < 5*ell-h ∧
    (1/25000 : ℝ) < boundary-43/50 ∧
    (1/25000 : ℝ) < boundary-437/500 ∧
    (1/25000 : ℝ) < 7/8-boundary ∧
    (1/25000 : ℝ) < -C0-(1/2+3*ell/2)/50 ∧
    (1/25000 : ℝ) < ly/2-13*h/75-1/50-(7/8-boundary) ∧
    (1/25000 : ℝ) < -((225*ell+50-75*b)/50+78*ell-49*b-73)/300 ∧
    (1/25000 : ℝ) < -((225*ell+50-75*b)*(19/25)+78*ell-49*b-73)/300 ∧
    (1/25000 : ℝ) < c ∧
    (1/25000 : ℝ) < 1-c ∧
    (1/25000 : ℝ) < 1/5-(4-c)/(20-4*c) ∧
    (1/25000 : ℝ) < 1/5-c/12 ∧
    (1/25000 : ℝ) < (5/6-19/25)*(5-c)/2+(19/25)*(1-c/4)-3/5 ∧
    (1/25000 : ℝ) < 3-(1+c)*51/100-2 ∧
    (1/25000 : ℝ) < (2-c*51/100)*(49/100)-3/4 := by
  norm_num [kappa,b,ell,lx,ly,h,boundary,c,C0]
end
end CombineV22.Checkpoint
#print axioms CombineV22.Checkpoint.universal_endpoint
#print axioms CombineV22.Checkpoint.side_certificate
#print axioms CombineV22.Checkpoint.A_coefficient_bounds
#print axioms CombineV22.Checkpoint.disc_coefficient_bounds
#print axioms CombineV22.Checkpoint.moment_premise
#print axioms CombineV22.Checkpoint.improvement

end PartIVBlock2

/- BEGIN consolidated ExplicitRoot.lean -/
section PartIVBlock3
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace CombineV22ExplicitRoot
open CombineV22Optimality
noncomputable section

def rad : ℝ := Real.sqrt 1391
def cosineArg : ℝ := 28470/(1391*rad)
def angle : ℝ := Real.arccos cosineArg/3-2*Real.pi/3
def explicitXi : ℝ := 20/33+rad/33*Real.cos angle
lemma rad_sq : rad^2 = 1391 := by norm_num [rad, Real.sq_sqrt]
lemma rad_pos : 0 < rad := by unfold rad; positivity
lemma rad_bounds : 37 < rad ∧ rad < 38 := by
  have hr := rad_pos
  constructor <;> nlinarith [rad_sq]
lemma rad_cube : rad^3 = 1391*rad := by
  calc rad^3 = rad*rad^2 := by ring
       _ = 1391*rad := by rw [rad_sq]; ring
lemma cosineArg_bounds : 0 < cosineArg ∧ cosineArg < 1 := by
  have hr := rad_bounds.1
  constructor
  · unfold cosineArg; positivity
  · unfold cosineArg
    apply (div_lt_one (by positivity : 0 < 1391*rad)).2
    nlinarith
lemma cos_angle_bounds : -(1/2:ℝ) < Real.cos angle ∧ Real.cos angle < 0 := by
  have ha0 := Real.arccos_pos.mpr cosineArg_bounds.2
  have ha1 := Real.arccos_lt_pi_div_two.mpr cosineArg_bounds.1
  have hp := Real.pi_pos
  have hlo : Real.pi/2 < -angle := by unfold angle; linarith
  have hhi : -angle < 2*Real.pi/3 := by unfold angle; linarith
  have hc : Real.cos (2*Real.pi/3) = -(1/2:ℝ) := by
    rw [show 2*Real.pi/3 = 2*(Real.pi/3) by ring, Real.cos_two_mul, Real.cos_pi_div_three]
    norm_num
  constructor
  · have hh := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ -angle)
      (by linarith : 2*Real.pi/3 ≤ Real.pi) hhi
    rw [Real.cos_neg, hc] at hh
    exact hh
  · have hh := Real.cos_neg_of_pi_div_two_lt_of_lt hlo (by linarith : -angle < Real.pi+Real.pi/2)
    rwa [Real.cos_neg] at hh
lemma explicitXi_bounds : 0 < explicitXi ∧ explicitXi < 1 := by
  have hr := rad_bounds
  have hc := cos_angle_bounds
  unfold explicitXi
  constructor
  · nlinarith [mul_pos rad_pos (by linarith : 0 < Real.cos angle+1/2)]
  · nlinarith [mul_neg_of_pos_of_neg rad_pos hc.2]
lemma cosine_cubic : 1391*rad*(4*(Real.cos angle)^3-3*Real.cos angle)=28470 := by
  have hc : Real.cos (3*angle) = cosineArg := by
    rw [show 3*angle = Real.arccos cosineArg-2*Real.pi by unfold angle; ring,
      Real.cos_sub_two_pi, Real.cos_arccos (by linarith [cosineArg_bounds.1])
        (le_of_lt cosineArg_bounds.2)]
  rw [Real.cos_three_mul] at hc
  unfold cosineArg at hc
  have hrpos := rad_pos
  have hr := (eq_div_iff (by positivity : 1391*rad ≠ 0)).1 hc
  nlinarith
lemma explicitXi_cubic : cubic explicitXi = 0 := by
  have hid : cubic explicitXi = (1391*rad*(4*(Real.cos angle)^3-3*Real.cos angle)-28470)/121 := by
    unfold cubic explicitXi
    ring_nf
    rw [rad_cube]
    ring
  rw [hid, cosine_cubic]
  norm_num
lemma root_unique_unit (x : ℝ) (hx : 0 < x ∧ x < 1) (hp : cubic x = 0) : x = xiInf := by
  have hr := xiInf_mem_small
  have hr0 : 0 ≤ xiInf := by linarith [hr.1]
  have hxr := mul_le_mul_of_nonneg_left hr.2 (le_of_lt hx.1)
  have hr2 := mul_self_le_mul_self hr0 hr.2
  have hx2 : x^2 ≤ x := by nlinarith [mul_nonneg (le_of_lt hx.1) (by linarith : 0 ≤ 1-x)]
  have hfac : 1188*(x^2+x*xiInf+xiInf^2)-2160*(x+xiInf)+171 < 0 := by
    nlinarith [hr.1,hr.2]
  have hid : cubic x-cubic xiInf = (x-xiInf)*(1188*(x^2+x*xiInf+xiInf^2)-2160*(x+xiInf)+171) := by
    unfold cubic; ring
  rw [hp,cubic_xiInf] at hid
  have hz := (mul_eq_zero.mp (by simpa using hid.symm)).resolve_right (ne_of_lt hfac)
  linarith
/-- The explicit trigonometric expression for the uniquely isolated fixed point. -/
theorem xiInf_explicit : xiInf = 20/33+Real.sqrt 1391/33 *
    Real.cos (Real.arccos (28470/(1391*Real.sqrt 1391))/3-2*Real.pi/3) := by
  have h := root_unique_unit explicitXi explicitXi_bounds explicitXi_cubic
  exact h.symm

/-- A rational interval of width 10⁻¹⁸ containing the isolated cubic root. -/
theorem xiInf_decimal_bracket :
    (388583354266034666/10^18 : ℝ) < xiInf ∧
    xiInf < (388583354266034667/10^18 : ℝ) := by
  have hlmem : (388583354266034666/10^18 : ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
    constructor <;> norm_num
  have humem : (388583354266034667/10^18 : ℝ) ∈ Set.Icc (19/50:ℝ) (39/100:ℝ) := by
    constructor <;> norm_num
  have hlp : 0 < cubic (388583354266034666/10^18) := by norm_num [cubic]
  have hup : cubic (388583354266034667/10^18) < 0 := by norm_num [cubic]
  constructor
  · by_contra hn
    have hc := (cubic_nonpos_iff _ hlmem).2 (le_of_not_gt hn)
    linarith
  · have he := (cubic_nonpos_iff _ humem).1 (le_of_lt hup)
    apply lt_of_le_of_ne he
    intro heq
    rw [← heq, cubic_xiInf] at hup
    linarith
/-- An exact 18-place rational enclosure of the limiting comparison bound. -/
theorem boundary_decimal_bracket :
    (874957019420098946/10^18 : ℝ) < boundary xiInf ∧
    boundary xiInf < (874957019420098947/10^18 : ℝ) := by
  have hb := xiInf_decimal_bracket
  have hd := boundary_den_pos xiInf_mem
  unfold boundary
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [hb.1]
  · apply (div_lt_iff₀ hd).2
    nlinarith [hb.2]
#print axioms xiInf_explicit
#print axioms xiInf_decimal_bracket
#print axioms boundary_decimal_bracket
end
end CombineV22ExplicitRoot

end PartIVBlock3

/- BEGIN consolidated analytic/ExtendedInduction.lean -/
section PartIVBlock4

/-! Extended physical induction, copied from the source proof with explicit 13/18 comparison margins. No vendor files are modified. -/

/- BEGIN OAI.NumberTheory.DirichletL.Moments.ReflectionRetainedLength -/
section ExtendedModule0

namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentReflectionRetainedLengthIV
open CenteredMomentComparisonReflection CenteredMomentReflectedTruncation
open CenteredMomentSectorLocalization

lemma retained_scale_lower (R Y : ℝ) (hY : 0< Y) (n : ℤ)
    (hn : n∈retainedAnnuli R Y hY) : 1≤ dyadicScale n*Y := by
  obtain ⟨hr,q,hq,hne⟩ := (retainedAnnuli_mem R Y hY n).mp hn
  have hs := (dyadicWeight_support n hne).2.le
  have hh := mul_le_mul_of_nonneg_right (hq.trans hs) hY.le
  simpa only [inv_mul_cancel₀ hY.ne'] using hh

theorem eventually_actual_retained_length (C box xi : ℝ) (hC : 0< C)
    (hbox : 1≤ box) (hxi : 0< xi) :
    ∀ᶠ Z : ℝ in atTop,1< Z ∧ ∀(M a Q R d h : ℝ),
      0< Q → 0< d → Q*R≤ C*Z^M → d≤ R → 1≤ h →
      ∀n : ℤ,∀hY : 0< Q*d/(Z^a*h),
      n∈retainedAnnuli (Z^(xi/4)) (Q*d/(Z^a*h)) hY →
      1≤ dyadicScale n*(Q*d/(Z^a*h)) ∧
      0≤ Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h)))) ∧
      Real.logb Z (box*(dyadicScale n*(Q*d/(Z^a*h))))≤ M-a+xi := by
  have hc := (tendsto_rpow_atTop (show 0< xi/2 by linarith)).eventually
    (eventually_ge_atTop (box*C))
  have hfour := (tendsto_rpow_atTop (show 0< xi/4 by linarith)).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc,hfour] with Z hZ hconst h4
  refine ⟨hZ,?_⟩
  intro M a Q R d h hQ hd hcap hdR hh n hY hn
  have hz : 0< Z := zero_lt_one.trans hZ
  have hs : dyadicScale n≤ Z^(xi/2) := by
    calc
      _≤4*Z^(xi/4) := retained_scale_le _ n ((retainedAnnuli_mem _ _ hY n).mp hn).1
      _≤ Z^(xi/4)*Z^(xi/4) := mul_le_mul_of_nonneg_right h4 (by positivity)
      _=Z^(xi/2) := by rw [←Real.rpow_add hz];congr 1;ring
  have hlo := retained_scale_lower _ _ hY n hn
  have hraw := reflected_scale_bound Z M a xi C Q R d h (dyadicScale n)
    hZ hC.le hQ.le hd.le (dyadicScale_pos n).le hcap hdR hh hs
  have hb : 1≤ box*(dyadicScale n*(Q*d/(Z^a*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤_ :=mul_le_mul hbox hlo zero_le_one (by linarith)
  refine ⟨hlo,Real.logb_nonneg hZ hb,?_⟩
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hb)).mpr
  calc
    _≤ box*(C*Z^(M-a+xi/2)) := mul_le_mul_of_nonneg_left hraw (by linarith)
    _=(box*C)*Z^(M-a+xi/2) :=by ring
    _≤ Z^(xi/2)*Z^(M-a+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
    _=Z^(M-a+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

lemma one_reflection_total_width (M A z b xi reflected : ℝ)
    (hb : b≤ M/4) (hreflection : reflected≤ M-(A-z-b)+xi) :
    reflected+b+z≤3*M/2-A+2*z+xi := by linarith

lemma positive_slot_width_drop (M A z xi kappa : ℝ)
    (_hM : 0≤ M) (hz : 0≤ z) (hk : 13/18≤ kappa)
    (hA : 5*M/6≤ A) (hcap : A+(6*kappa-1)*z≤ M) :
    3*M/2-A+2*z+xi≤23*M/30+xi ∧
    3*M/2-A+2*z+xi+(6*kappa-1)*z≤14*M/15+xi := by
  have hkz : 10/3*z≤(6*kappa-1)*z := mul_le_mul_of_nonneg_right (by linarith) hz
  have hsmall : z≤ M/20 := by linarith
  constructor <;> nlinarith

end SevenEighths.CenteredMomentReflectionRetainedLengthIV

end

end OAI

end ExtendedModule0

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceState -/
section ExtendedModule1

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceStateIV
open HeckeFamily ConcreteTraceCRT CenteredMomentEnergyState
open CenteredMomentRadialEligibleEnergy CenteredMomentOriginalRadialComparison
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
local notation "O"=> HeckeFamily.O

abbrev effectiveRadial (r:Radial):Radial:=
  CenteredMomentEnergyReferenceState.effectiveRadial r

lemma radialEnergy_effective (r:Radial)(f:O→ℂ):
    radialEnergy f (effectiveRadial r).keep r.profile r.scale=
      radialEnergy f r.keep r.profile r.scale:=by
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z <;> by_cases hz:r.profile (‖eisEmbedding z‖^2/r.scale)=0 <;>
    simp [effectiveRadial,CenteredMomentEnergyReferenceState.effectiveRadial,hk,hz]

abbrev effectiveState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):NaturalState Z Bmask bΦ:=
  CenteredMomentEnergyReferenceState.effectiveState s

lemma effective_row_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    ((Ideal.span {z}).absNorm:ℝ)≤ bΦ*Z^s.rowWidth:=by
  rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←s.scale_eq]
  exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hz.2)

lemma effective_character_nonprincipal {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    (naturalCharacter s.character z).residue≠1:=by
  have hn:=s.row_ne_zero z hz.1
  rw [naturalCharacter_eq s.character z hn]
  exact (naturalRow s.character z hn).nonprincipal hn s.fixedModulus s.puncture
    s.puncture_ne_zero (s.nonexceptional z hz.1)

lemma effective_character_cap {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(hbΦ:0≤ bΦ)
    (z:O)(hz:(effectiveState s).radial.keep z):
    ((naturalCharacter s.character z).modulus.absNorm:ℝ)≤
      (fixedConductorFactor:ℝ)*bΦ*Z^s.width:=by
  have hn:=s.row_ne_zero z hz.1
  rw [naturalCharacter_eq s.character z hn]
  have h:=(naturalRow s.character z hn).modulus_power_bound Z s.characterWidth s.rowWidth bΦ
    (zero_lt_one.trans_le s.base_ge_one) hbΦ s.modulus_bound (effective_row_norm s z hz)
  simpa only [NaturalState.width,add_comm s.characterWidth s.rowWidth] using h

def comparisonFirst (Z M:ℝ):ℝ:=Z^(M/4)
def comparisonSecond (Z M X₁ X₂:ℝ):ℝ:=X₁*X₂/comparisonFirst Z M

lemma comparison_positive (Z M X₁ X₂:ℝ)(hZ:0< Z)(hX₁:0< X₁)(hX₂:0< X₂):
    0< comparisonFirst Z M ∧ 0< comparisonSecond Z M X₁ X₂:=
  ⟨Real.rpow_pos_of_pos hZ _,div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos hZ _)⟩

lemma comparison_same_product (Z M X₁ X₂:ℝ)(hZ:0< Z):
    comparisonFirst Z M*comparisonSecond Z M X₁ X₂=X₁*X₂:=by
  unfold comparisonSecond
  exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hZ (M/4)).ne'

lemma comparison_second_power (Z M X₁ X₂:ℝ)(hZ:1< Z)(hX₁:0< X₁)(hX₂:0< X₂):
    comparisonSecond Z M X₁ X₂=Z^(Real.logb Z (X₁*X₂)-M/4):=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (mul_pos hX₁ hX₂)]
  rfl

theorem balanced_reference_geometry (Z M X₁ X₂ ell κ:ℝ)
    (hZ:1< Z)(hM:0≤ M)(hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hκ:13/18≤κ)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ M):
    ell≤ M/20 ∧
    1≤ comparisonFirst Z M ∧
    comparisonFirst Z M≤ comparisonSecond Z M X₁ X₂ ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4 ∧
    Real.logb Z (comparisonSecond Z M X₁ X₂)≤ M:=by
  have hkell:10/3*ell≤(6*κ-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  have he:ell≤ M/20:=by linarith
  have hlen:M/2≤ Real.logb Z (X₁*X₂):=by linarith
  have hupper:Real.logb Z (X₁*X₂)-M/4≤ M:=by linarith
  have hlog:Real.logb Z (comparisonSecond Z M X₁ X₂)=Real.logb Z (X₁*X₂)-M/4:=by
    rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂,Real.logb_rpow]
    · exact zero_lt_one.trans hZ
    · exact hZ.ne'
  refine ⟨he,Real.one_le_rpow hZ.le (by linarith),?_,hlog,by rw [hlog];exact hupper⟩
  rw [comparison_second_power Z M X₁ X₂ hZ hX₁ hX₂]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem balanced_reflection_margins (Z M X₁ X₂ ell κ ξ reflected:ℝ)
    (hZ:1< Z)(hM:0≤ M)(hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hκ:13/18≤κ)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ M)
    (href:reflected≤ M-Real.logb Z (comparisonSecond Z M X₁ X₂)+ξ):
    reflected+M/4+ell≤23*M/30+ξ ∧
    reflected+M/4+ell+(6*κ-1)*ell≤14*M/15+ξ:=by
  have hlog:=(balanced_reference_geometry Z M X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hlarge hcap).2.2.2.1
  rw [hlog] at href
  have hc:=CenteredMomentReflectionRetainedLengthIV.positive_slot_width_drop M
    (Real.logb Z (X₁*X₂)+ell) ell ξ κ hM hell hκ hlarge hcap
  constructor <;> linarith [hc.1,hc.2]

end SevenEighths.CenteredMomentEnergyReferenceStateIV

end

end OAI

end ExtendedModule1

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionCapacity -/
section ExtendedModule2

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentEnergyReferenceDeletionCapacityIV
open HeckeFamily CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyBands CenteredMomentLiveCapacity

local notation "O"=> HeckeFamily.O

lemma deleted_short_length (Z M:ℝ)(hZ:1< Z)(hM:0≤ M)
    (D:Finset (Ideal O))(hD:∀I∈D,Prime I):
    length Z (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤ M/4:=by
  have hn:=product_norm_ge_one D hD
  have hY:1≤ comparisonFirst Z M:=Real.one_le_rpow hZ.le (by linarith)
  have hdiv:comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ)≤ comparisonFirst Z M:=
    div_le_self (zero_le_one.trans hY) hn
  have hm:max 1 (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤ comparisonFirst Z M:=max_le hY hdiv
  have he:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) hm
  simpa only [length,comparisonFirst,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using he

theorem deleted_reflection_excess {α:Type*}[DecidableEq α]
    (F J:Finset α)(hJF:J⊆F)(w:α→ℝ)(hw:∀i∈F,0≤ w i)
    (Z M X₁ X₂ κ xi reflected:ℝ)(hZ:1< Z)(hM:0≤ M)
    (hX₁:0< X₁)(hX₂:0< X₂)(hκ:13/18≤κ)(hxi:0≤ xi)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+∑i∈F,w i)
    (hcap:Real.logb Z (X₁*X₂)+∑i∈F,w i+(6*κ-1)*(∑i∈F,w i)≤ M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤ M-Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi):
    excess J w (length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))) reflected M κ≤
      xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ):=by
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hn₂p:0<((∏I∈D₂,I).absNorm:ℝ):=zero_lt_one.trans_le hn₂
  have hlog:0≤ Real.logb Z ((∏I∈D₂,I).absNorm:ℝ):=Real.logb_nonneg hZ hn₂
  have hell:0≤∑i∈F,w i:=Finset.sum_nonneg hw
  have hY₂:0< comparisonSecond Z M X₁ X₂:=by
    unfold comparisonSecond
    exact div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  rw [Real.logb_div hY₂.ne' hn₂p.ne'] at href
  have hb:reflected≤ M-Real.logb Z (comparisonSecond Z M X₁ X₂)+
      (xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)):=by linarith
  have hh:=(balanced_reflection_margins Z M X₁ X₂ (∑i∈F,w i) κ
    (xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)) reflected hZ hM hX₁ hX₂ hell hκ hlarge hcap hb).2
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hsum:(∑i∈J,w i)≤∑i∈F,w i:=
    Finset.sum_le_sum_of_subset_of_nonneg hJF (fun i hi _=> hw i hi)
  have hks:=mul_le_mul_of_nonneg_left hsum (by linarith:0≤6*κ)
  unfold excess
  apply max_le _ (add_nonneg hxi hlog)
  nlinarith

theorem deleted_reflection_removal {α:Type*}[DecidableEq α]
    (F J:Finset α)(hJF:J⊆F)(w:α→ℝ)(hw:∀i∈F,0≤ w i)
    (Z M X₁ X₂ κ xi reflected mesh:ℝ)(hZ:1< Z)(hM:0≤ M)
    (hX₁:0< X₁)(hX₂:0< X₂)(hκ:13/18≤κ)(hxi:0≤ xi)(hm:0≤ mesh)(hwm:∀i∈J,w i≤ mesh)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+∑i∈F,w i)
    (hcap:Real.logb Z (X₁*X₂)+∑i∈F,w i+(6*κ-1)*(∑i∈F,w i)≤ M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤ M-Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi):
    ∃removed:Finset α,removed⊆J ∧
      (removed=J ∨ length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+reflected+
        6*κ*(∑i∈J\removed,w i)≤ M) ∧
      κ*(∑i∈removed,w i)≤ xi/6+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)/6+κ*mesh:=by
  obtain ⟨removed,hr,hcapacity,hcost⟩:=removal_excess_cost J w
    (length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))) reflected M κ mesh
    (by linarith) hm (fun i hi=> hw i (hJF hi)) hwm
  refine ⟨removed,hr,hcapacity,?_⟩
  have he:=deleted_reflection_excess F J hJF w hw Z M X₁ X₂ κ xi reflected
    hZ hM hX₁ hX₂ hκ hxi hlarge hcap D₁ D₂ hD₁ hD₂ href
  linarith

lemma plain_kappa_eq (beta : ℝ) :
    (3/4:ℝ)+2*(beta-7/8)=2*beta-1 := by ring

lemma plain_kappa_lower (beta : ℝ) (hbeta : 7/8 < beta) :
    (3/4:ℝ) < (3/4:ℝ)+2*(beta-7/8) := by linarith

lemma paid_divisor_power (Z cost xi kappa mesh : ℝ) (hZ : 1 < Z)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I)
    (hcost : cost ≤ xi/6 + Real.logb Z ((∏ I ∈ D, I).absNorm:ℝ)/6 + kappa*mesh) :
    Z^cost ≤ Z^(xi/6+kappa*mesh) * ((∏ I ∈ D, I).absNorm:ℝ)^(1/6:ℝ) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hn : 0 < ((∏ I ∈ D, I).absNorm:ℝ) :=
    zero_lt_one.trans_le (product_norm_ge_one D hD)
  calc
    Z^cost ≤ Z^((xi/6+kappa*mesh)+Real.logb Z ((∏ I ∈ D, I).absNorm:ℝ)/6) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = Z^(xi/6+kappa*mesh) * ((∏ I ∈ D, I).absNorm:ℝ)^(1/6:ℝ) := by
      rw [Real.rpow_add hZp]
      congr 1
      rw [div_eq_mul_inv, Real.rpow_mul hZp.le,
        Real.rpow_logb hZp hZ.ne' hn]
      norm_num

end SevenEighths.CenteredMomentEnergyReferenceDeletionCapacityIV

end

end OAI

end ExtendedModule2

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionClipped -/
section ExtendedModule3

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentEnergyReferenceDeletionClippedIV
open HeckeFamily CenteredMomentEnergyReferenceStateIV
open CenteredMomentEnergyReferenceDeletionBudget

local notation "O" => HeckeFamily.O

lemma deleted_long_le_width (Z M X₁ X₂ ell kappa : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 13/18 ≤ kappa)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I) :
    Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) ≤ M := by
  have hg := balanced_reference_geometry Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap
  have hn := product_norm_ge_one D hD
  have hp : 0 < ((∏ I ∈ D, I).absNorm:ℝ) := zero_lt_one.trans_le hn
  have hy := (comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂).2
  rw [Real.logb_div hy.ne' hp.ne']
  have hlog := Real.logb_nonneg hZ hn
  linarith [hg.2.2.2.2]

lemma clipped_reflected_bound (Z M X₁ X₂ ell kappa xi reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 13/18 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I)
    (href : reflected ≤ max 0 (M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi)) :
    reflected ≤ M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi := by
  have hlong := deleted_long_le_width Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap D hD
  rwa [max_eq_right (by linarith)] at href

end SevenEighths.CenteredMomentEnergyReferenceDeletionClippedIV

end

end OAI

end ExtendedModule3

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceLowBranchGeometry -/
section ExtendedModule4

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometryIV
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceStateIV
open CenteredMomentEnergyReferenceDeletionBudget CenteredMomentEnergyReferenceDeletionCapacityIV
local notation "O"=> HeckeFamily.O

lemma length_eq_max_log (Z X:ℝ)(hZ:1< Z)(hX:0< X):
    length Z X=max 0 (Real.logb Z X):=by
  by_cases h:1≤ X
  · rw [length,max_eq_right h,max_eq_right (Real.logb_nonneg hZ h)]
  · have hx:X≤1:=le_of_not_ge h
    have hl:Real.logb Z X≤0:=by
      simpa using Real.logb_le_logb_of_le hZ hX hx
    rw [length,max_eq_left hx,Real.logb_one,max_eq_left hl]

lemma slot_budgets (M total ell kappa:ℝ)(_hM:0≤ M)(hell:0≤ ell)(hk:13/18≤ kappa)
    (hlarge:5*M/6≤ total+ell)(hcap:total+ell+(6*kappa-1)*ell≤ M):
    ell≤ M/20 ∧ (6*kappa-1)*ell≤ M/6:=by
  have hkell:10/3*ell≤(6*kappa-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem reflected_low (M short along ell z kappa xi reflected:ℝ)
    (hM:0≤ M)(_hs:0≤ short)(hsM:short≤ M/4)(_hell:0≤ ell)(_hz:0≤ z)(hze:z≤ ell)
    (hk:13/18≤ kappa)(he:ell≤ M/20)(hbudget:(6*kappa-1)*ell≤ M/6)(hxi:0≤ xi)
    (hhigh:5*M/6< short+max 0 along+z)
    (href:reflected≤ max 0 (M-along+xi)):
    0< along ∧ reflected+short+z≤23*M/30+xi ∧
      reflected+short+6*kappa*z≤14*M/15+xi:=by
  have haz:0< along:=by
    by_contra hn
    have ha:along≤0:=le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget:(6*kappa-1)*z≤ M/6:=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap:z≤ M/20:=hze.trans he
  refine ⟨haz,?_⟩
  by_cases hr:0≤ M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem deleted_reference_cases (Z M X₁ X₂ ell z kappa xi reflected:ℝ)
    (hZ:1< Z)(hM:0≤ M)(hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hk:13/18≤ kappa)(hxi:0≤ xi)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤ M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤ max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi)):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let long:=length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+long+z≤5*M/6 ∧ short+long+6*kappa*z≤ M) ∨
    (0< Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) ∧
      reflected+short+z≤23*M/30+xi ∧ reflected+short+6*kappa*z≤14*M/15+xi):=by
  dsimp only
  have hg:=balanced_reference_geometry Z M X₁ X₂ ell kappa hZ hM hX₁ hX₂ hell hk hlarge hcap
  have hpos:=comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hlongpos:=div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0:=length_nonneg Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ)) hZ
  have hlong:length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))≤
      Real.logb Z (comparisonSecond Z M X₁ X₂):=by
    have hY:1≤ comparisonSecond Z M X₁ X₂:=hg.2.1.trans hg.2.2.1
    have hdiv:=div_le_self hpos.2.le hn₂
    exact Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) (max_le hY hdiv)
  by_cases hlo:length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+
      length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6
  · refine Or.inl ⟨hlo,?_⟩
    have hzcap:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*kappa)
    rw [hg.2.2.2.1] at hlong
    nlinarith
  · apply Or.inr
    obtain ⟨he,hbudget⟩:=slot_budgets M (Real.logb Z (X₁*X₂)) ell kappa hM hell hk hlarge hcap
    apply reflected_low M _ _ ell z kappa xi reflected hM hshort0 hshort hell hz hze hk he hbudget hxi _ href
    rw [←length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo

lemma reflected_low_admissible (M xi short reflected z kappa:ℝ)
    (hxi:xi≤ M/15)(ht:reflected+short+z≤23*M/30+xi)
    (hc:reflected+short+6*kappa*z≤14*M/15+xi):
    reflected+short+z≤5*M/6 ∧ reflected+short+6*kappa*z≤ M:=by
  constructor <;> linarith

end SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometryIV

end

end OAI

end ExtendedModule4

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow -/
section ExtendedModule5

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowWindowIV
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceStateIV
open CenteredMomentEnergyReferenceLowBranchGeometryIV
local notation "O"=> HeckeFamily.O

lemma reflection_window_length (Z R x:ℝ)(hZ:1< Z)(hR:0≤ R)
    (hx:x∈Set.Icc 0 (R*Real.log Z)):
    length Z (Real.exp x)≤ R ∧ Real.exp x≤ Z^R:=by
  have hlog:0< Real.log Z:=Real.log_pos hZ
  have hexp:Real.exp x≤ Z^R:=by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
    apply Real.exp_le_exp.mpr
    simpa [mul_comm] using hx.2
  refine ⟨?_,hexp⟩
  have hmax:max 1 (Real.exp x)≤ Z^R:=
    max_le (Real.one_le_rpow hZ.le hR) hexp
  have hl:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 (Real.exp x))) hmax
  simpa only [length,Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hl

theorem deleted_reference_window (Z M X₁ X₂ ell z kappa xi:ℝ)
    (hZ:1< Z)(hM:0≤ M)(hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hk:13/18≤ kappa)(hxi:0≤ xi)(hxiM:xi≤ M/15)
    (hlarge:5*M/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤ M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+6*kappa*z≤ M) ∨
    (0< along ∧ ∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
      length Z (Real.exp x)+short+z≤5*M/6 ∧
      length Z (Real.exp x)+short+6*kappa*z≤ M):=by
  dsimp only
  let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))
  rcases deleted_reference_cases Z M X₁ X₂ ell z kappa xi (max 0 (M-along+xi))
    hZ hM hX₁ hX₂ hell hz hze hk hxi hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h|h
  · exact Or.inl h
  · refine Or.inr ⟨h.1,?_⟩
    intro x hx
    have hh:=reflection_window_length Z (max 0 (M-along+xi)) x hZ (le_max_left _ _) hx
    have hb:=reflected_low_admissible M xi _ (max 0 (M-along+xi)) z kappa hxiM h.2.1 h.2.2
    constructor <;> linarith [hh.1]

end SevenEighths.CenteredMomentEnergyReferenceLowWindowIV

end

end OAI

end ExtendedModule5

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceDivisors -/
section ExtendedModule6

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceDivisorsIV
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyReferenceStateIV
local notation "O"=> HeckeFamily.O

lemma divisor_norm {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    1≤((∏P∈D,P).absNorm:ℝ) ∧ ((∏P∈D,P).absNorm:ℝ)≤ Z^Bmask:=by
  have hs:D⊆IdealMobiusDivisorSum.primeSupport s.puncture:=Finset.mem_powerset.mp hD
  have hn:=IdealMobiusDivisorSum.support_product_ne_zero hs
  have hp:0<(∏P∈D,P).absNorm:=Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)
  refine ⟨by exact_mod_cast hp,?_⟩
  apply le_trans _ s.puncture_bound
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.puncture_ne_zero))
    (map_dvd Ideal.absNorm (IdealMobiusDivisorSum.support_product_dvd s.puncture_ne_zero hs))

lemma divided_scale_power (Z Y N:ℝ)(hZ:1< Z)(hY:0< Y)(hN:0< N):
    Z^(Real.logb Z Y-Real.logb Z N)=Y/N:=by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hY,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hN]

theorem divisor_reflection_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(L Y:ℝ)(hwidth:s.width≤ L)(hY:1≤ Y)
    (D:Finset (Ideal O))(hD:D∈(CompletedGauss.primeSupport s.puncture).powerset):
    let a:=Real.logb Z Y-Real.logb Z ((∏P∈D,P).absNorm:ℝ);
    -Bmask≤ a ∧ s.width≤(L+Bmask)+a ∧
      Z^a=Y/((∏P∈D,P).absNorm:ℝ):=by
  dsimp only
  obtain ⟨hn,hcap⟩:=divisor_norm s D hD
  have hp:0<((∏P∈D,P).absNorm:ℝ):=zero_lt_one.trans_le hn
  have hlogN:Real.logb Z ((∏P∈D,P).absNorm:ℝ)≤ Bmask:=
    (Real.logb_le_iff_le_rpow hZ hp).mpr hcap
  have hlogY:=Real.logb_nonneg hZ hY
  refine ⟨by linarith,by linarith,divided_scale_power Z Y _ hZ (zero_lt_one.trans_le hY) hp⟩

theorem balanced_divisor_range {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(L X₁ X₂ ell κ:ℝ)(hwidth:s.width≤ L)
    (hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hκ:13/18≤κ)
    (hlarge:5*s.width/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ)
    let long:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    -Bmask≤ short ∧ -Bmask≤ long ∧ s.width≤(L+Bmask)+long ∧
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^long=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ):=by
  have hg:=balanced_reference_geometry Z s.width X₁ X₂ ell κ hZ s.width_nonneg
    hX₁ hX₂ hell hκ hlarge hcap
  have hfirst:Real.logb Z (comparisonFirst Z s.width)=s.width/4:=by
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  have hs:=divisor_reflection_range s hZ L (comparisonFirst Z s.width) hwidth hg.2.1 D₁ hD₁
  have hl:=divisor_reflection_range s hZ L (comparisonSecond Z s.width X₁ X₂) hwidth
    (hg.2.1.trans hg.2.2.1) D₂ hD₂
  dsimp only at hs hl ⊢
  rw [hfirst] at hs
  rw [hg.2.2.2.1] at hl
  exact ⟨hs.1,hl.1,hl.2.1,hs.2.2,hl.2.2⟩

end SevenEighths.CenteredMomentEnergyReferenceDivisorsIV

end

end OAI

end ExtendedModule6

/- BEGIN OAI.NumberTheory.DirichletL.Energy.ReferenceLowDeletedGeometry -/
section ExtendedModule7

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowDeletedGeometryIV
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceDivisorsIV
open CenteredMomentEnergyReferenceLowWindowIV
local notation "O"=> HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(hB:0≤ Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤ Mcap)(hL:Mcap+Bmask+xi≤ L)
    (hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hκ:13/18≤κ)(hxi:0≤ xi)(hxiM:xi≤ s.width/15)
    (hlarge:5*s.width/6≤ Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*κ-1)*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=s.width/4-Real.logb Z ((∏P∈D₁,P).absNorm:ℝ);
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ);
    Z^short=comparisonFirst Z s.width/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤ L ∧ along≤ L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤ L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤ s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤ s.width)):=by
  dsimp only
  have hg:=balanced_reference_geometry Z s.width X₁ X₂ ell κ hZ s.width_nonneg
    hX₁ hX₂ hell hκ hlarge hcap
  have hd:=balanced_divisor_range s hZ Mcap X₁ X₂ ell κ hwidth
    hX₁ hX₂ hell hκ hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hd
  have hn₁:=divisor_norm s D₁ hD₁
  have hn₂:=divisor_norm s D₂ hD₂
  have hl₁:=Real.logb_nonneg hZ hn₁.1
  have hl₂:=Real.logb_nonneg hZ hn₂.1
  have hMcap:0≤ Mcap:=s.width_nonneg.trans hwidth
  have hLc:0≤ L:=by linarith
  refine ⟨hd.2.2.2.1,hd.2.2.2.2,by linarith,by linarith [s.width_nonneg],?_,
    hd.2.2.1,?_,?_⟩
  · linarith [hg.2.2.2.2]
  · exact max_le hLc (by linarith [hd.2.1])
  · have hp₁:∀I∈D₁,Prime I:=fun I hi=>
      CenteredMomentNaturalRowSource.support_prime s.puncture I
        (Finset.mem_powerset.mp hD₁ hi)
    have hp₂:∀I∈D₂,Prime I:=fun I hi=>
      CenteredMomentNaturalRowSource.support_prime s.puncture I
        (Finset.mem_powerset.mp hD₂ hi)
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ)
    have halong:Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ))=along:=by
      rw [←hd.2.2.2.2]
      exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
    rcases CenteredMomentEnergyReferenceLowBranchGeometryIV.deleted_reference_cases
      Z s.width X₁ X₂ ell z κ xi (max 0 (s.width-along+xi)) hZ s.width_nonneg
      hX₁ hX₂ hell hz hze hκ hxi hlarge hcap D₁ D₂ hp₁ hp₂
      (by rw [halong]) with hc|hc
    · apply Or.inl
      simpa only [hd.2.2.2.1,hd.2.2.2.2] using hc
    · apply Or.inr
      have hh:=CenteredMomentEnergyReferenceLowBranchGeometryIV.reflected_low_admissible
        s.width xi _ (max 0 (s.width-along+xi)) z κ hxiM hc.2.1 hc.2.2
      simpa only [hd.2.2.2.1] using hh

end SevenEighths.CenteredMomentEnergyReferenceLowDeletedGeometryIV

end

end OAI

end ExtendedModule7

/- BEGIN OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionGeometry -/
section ExtendedModule8

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionGeometryIV
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceDivisorsIV
open CenteredMomentEnergyReferenceLowBranchGeometryIV
local notation "O"=> HeckeFamily.O

lemma original_long_positive (Z M X₁ X₂ ell κ:ℝ)(hZ:1< Z)(hM:0< M)
    (_hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hκ:13/18≤κ)
    (hshort:length Z X₁≤ M/4)
    (hlarge:5*M/6≤ length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤ M):
    0< Real.logb Z X₂ ∧ length Z X₂=Real.logb Z X₂ ∧ 1≤ X₂:=by
  have hbudget:=slot_budgets M (length Z X₁+length Z X₂) ell κ hM.le hell hκ hlarge (by linarith)
  have hpos:0< length Z X₂:=by linarith [hbudget.1]
  have he:=length_eq_max_log Z X₂ hZ hX₂
  have hl:0< Real.logb Z X₂:=by
    by_contra hn
    rw [he,max_eq_left (le_of_not_gt hn)] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨hl,he.trans (max_eq_right hl.le),?_⟩
  by_contra hn
  have hh:=Real.logb_le_logb_of_le hZ hX₂ (le_of_not_ge hn)
  rw [Real.logb_one] at hh
  linarith

lemma deleted_length_le (Z X N:ℝ)(hZ:1< Z)(hX:0< X)(hN:1≤ N):
    length Z (X/N)≤ length Z X:=by
  exact Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 _))
    (max_le_max_left 1 (div_le_self hX.le hN))

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1< Z)(hM:0< s.width)(hB:0≤ Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤ Mcap)(hL:Mcap+Bmask+xi≤ L)
    (hX₁:0< X₁)(hX₂:0< X₂)(hell:0≤ ell)(hz:0≤ z)(hze:z≤ ell)
    (hκ:13/18≤κ)(hxi:0≤ xi)(hxiM:xi≤ s.width/15)
    (hshort:length Z X₁≤ s.width/4)
    (hlarge:5*s.width/6≤ length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤ s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ));
    let along:=Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ));
    Z^short=X₁/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤ s.width/4 ∧ short≤ L ∧ along≤ L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤ L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤ s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤ s.width)):=by
  dsimp only
  have hZ0:=zero_lt_one.trans hZ
  obtain ⟨hn₁,hc₁⟩:=divisor_norm s D₁ hD₁
  obtain ⟨hn₂,hc₂⟩:=divisor_norm s D₂ hD₂
  have hp₁:=div_pos hX₁ (zero_lt_one.trans_le hn₁)
  have hp₂:=div_pos hX₂ (zero_lt_one.trans_le hn₂)
  have he₁:=Real.rpow_logb hZ0 hZ.ne' hp₁
  have he₂:=Real.rpow_logb hZ0 hZ.ne' hp₂
  have hd₁:=deleted_length_le Z X₁ _ hZ hX₁ hn₁
  have hd₂:=deleted_length_le Z X₂ _ hZ hX₂ hn₂
  have hraw₁:Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ))≤
      length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₁];exact le_max_right _ _
  have hraw₂:Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))≤
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₂];exact le_max_right _ _
  have hlen₁:=length_nonneg Z X₁ hZ
  have hlen₂:=length_nonneg Z X₂ hZ
  have hslot:0≤6*κ*ell:=mul_nonneg (by linarith) hell
  have hl:=original_long_positive Z s.width X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hshort hlarge hcap
  have hrange:=divisor_reflection_range s hZ Mcap X₂ hwidth hl.2.2 D₂ hD₂
  dsimp only at hrange
  have hlogdiv:=Real.logb_div (b:=Z) hX₂.ne' (zero_lt_one.trans_le hn₂).ne'
  rw [←hlogdiv] at hrange
  have hL0:0≤ L:=by linarith
  refine ⟨he₁,he₂,by linarith,by linarith,by linarith,hrange.2.1,
    max_le hL0 (by linarith [hrange.1]),?_⟩
  rw [he₁,he₂]
  by_cases hd:length Z (X₁/((∏P∈D₁,P).absNorm:ℝ))+
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+z≤5*s.width/6
  · refine Or.inl ⟨hd,?_⟩
    have hkz:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*κ)
    linarith
  · obtain ⟨he,hbudget⟩:=slot_budgets s.width (length Z X₁+length Z X₂) ell κ
      hM.le hell hκ hlarge (by linarith)
    have hlow:=reflected_low s.width (length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)))
      (Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))) ell z κ xi
      (max 0 (s.width-Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+xi))
      hM.le (length_nonneg Z _ hZ)
      (hd₁.trans hshort) hell hz hze hκ he hbudget hxi
      (by rw [←length_eq_max_log Z _ hZ hp₂];exact lt_of_not_ge hd) le_rfl
    exact Or.inr (reflected_low_admissible s.width xi _ _ z κ hxiM hlow.2.1 hlow.2.2)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionGeometryIV

end

end OAI

end ExtendedModule8

/- BEGIN OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionDeleted -/
section ExtendedModule9

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionDeletedIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionGeometryIV CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem deleted_original_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hBmask:0≤ Bmask)(hL:Mcap+Bmask+xi≤ L)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap → xi≤ s.width/15 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      length Z X₁≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀F:Finset α,
      let β:=fun i I=> heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i)):=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low_with_error (α:=α) M H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap D₁ hD₁ D₂ hD₂ F
  dsimp only
  let short:=Real.logb Z (X₁/((∏I∈D₁,I).absNorm:ℝ))
  let along:=Real.logb Z (X₂/((∏I∈D₂,I).absNorm:ℝ))
  have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ F) (fun i _ _=> hw i)
  have hg:=actual_deleted_gates s hZ.1 (by linarith) hBmask Mcap L X₁ X₂ (∑i,w i) (∑i∈F,w i) κ xi hs hL
    hX₁ hX₂ (Finset.sum_nonneg (fun i _=> hw i)) hsum hsumle hκ hxi.le hxiM hshort hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤ L:=by linarith [s.width_nonneg]
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
    (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
    (fun i _ _=> Real.one_le_rpow hZ.1.le (hw i))
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=direct_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z
      η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      s hQ hs W₁ W₂ hs₁ hs₂ (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Lslot Mcap ε κ η₀ Q K hK hlow hBmask F (Finset.subset_univ F)
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs W₂ W₁ hs₂ hs₁ along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap: (fun z=> polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))) =
      (fun z=> polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · gcongr
      · exact hZ.1.le
      · exact hg.2.2.1

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionDeletedIV

end

end OAI

end ExtendedModule9

/- BEGIN OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionOriginal -/
section ExtendedModule10

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginalIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionGeometryIV CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyOriginalHighReflectionDeletedIV CenteredMomentEnergyReferenceDeletionEnergy
open CenteredMomentInductionEnergy
theorem original_high_from_low
    (epsilonDelete:ℝ)(hepsilonDelete:0< epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hBmask:0≤ Bmask)(hL:Mcap+Bmask+xi≤ L)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0< C ∧ 0< D ∧ 0< Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap → xi≤ s.width/15 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      length Z X₁≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) :=by
  obtain ⟨Bslot,hBslot,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
  obtain ⟨Cweight,hCweight,hweight⟩:=original_energy_weighted_deletion (α:=α)
    (fun _=> bslot) (fun _=> Bslot) (fun _=> hBslot.le) epsilonDelete hepsilonDelete
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=deleted_original_from_low (α:=α) M H hH
    Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving Mcap Bmask L ha hlo hhi hbΦ hepsilon hxi hBmask hL B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,Cweight,hC,hD,hCweight,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  apply hweight Z Bmask bΦ a b s W₁ W₂ ha (by linarith) hs₁ hs₂
    (fun i=> primePool M H bslot (Z^(w i)))
    (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
    (fun i=> Z^(w i)) t X₁ X₂ _ 0
  · intro i I hI
    exact (Finset.mem_filter.mp hI).2.1
  · intro i
    exact Real.rpow_pos_of_pos hZpos _
  · intro i I hI
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh
  · intro i I hI hn
    have hpI:Prime I:=(Finset.mem_filter.mp hI).2.1
    have hh:=(hslot (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (freq i) 0
      (Real.rpow_pos_of_pos hZpos _) (hσlo i) (hσhi i) I hpI.ne_zero).2
    apply hh
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hX₁
  · exact hX₂
  · have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
    have hLpos:0≤ L:=by linarith [s.width_nonneg]
    have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
    positivity
  · norm_num
  · intro D₁ hD₁ D₂ hD₂ J hJ
    simpa only [Real.rpow_zero,mul_one] using hZ.2 Lslot ε κ η₀ Q K hK hlow
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hs hxiM
      W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap D₁ hD₁ D₂ hD₂ (Finset.univ\J)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginalIV

end

end OAI

end ExtendedModule10

/- BEGIN OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionPower -/
section ExtendedModule11

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionPowerIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionOriginalIV CenteredMomentEnergyReferenceScalarReserve
open CenteredMomentEnergyReferenceProfileBudget
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_high_power
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      length Z X₁≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
        (fun i I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=> Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+ε):=by
  obtain ⟨d,xi,saving,L,Cscalar,hd,hxi,hsaving,hCs,hxirho,hL,hscalar⟩:=
    exists_reference_reserve rho ε Mcap Bmask bΦ hrho hε hM hBmask
  refine ⟨d,xi,L,hd,hxi,hxirho,hL,?_⟩
  intro degree S
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,Cref,Dref,Cweight,hCr,hDr,hCw,href⟩:=
    original_high_from_low (α:=α) M H hH d hd Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ d xi saving Mcap Bmask L ha hlo hhi hbΦ hd hxi hBmask hL 2 (by norm_num) degree S
  obtain ⟨J,U,Cprofile,hCp,hprofile⟩:=reference_envelopes a b ha S T Slong degree n nlong
    Cref Dchild Dref hCr hDc hDr
  refine ⟨J,U,Cweight*Cprofile*Cscalar,by positivity,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hxiM:xi≤ s.width/15:=by linarith
  have hh:=hZ.2 Lslot d κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hxiM W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  have hsum:0≤∑i,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hsumcap:(∑i,w i)≤ Mcap:=by
    have hlen₁:=length_nonneg Z X₁ hZ.1
    have hlen₂:=length_nonneg Z X₂ hZ.1
    have hk:=mul_le_mul_of_nonneg_right (show (1:ℝ)≤6*κ by linarith) hsum
    nlinarith
  have hledger:=hscalar Z hZ.1.le s hs α w hsumcap
  have hp:=hprofile W₁ W₂ hs₁ hs₂ t height hheight
  dsimp only at hp
  let A:=Cprofile*(sourceControl U W₁*sourceControl U W₂)^2*(1+|t|+height)^J
  let E:=(K+1)*diagonalControl s.radial.profile*A
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hA:0≤ A:=by dsimp only [A];positivity
  have hE:0≤ E:=by dsimp only [E];positivity
  have hdir:K*diagonalControl s.radial.profile*
      ((CenteredMomentEnergyReferenceChild.independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
      (1+|t|+height)^degree≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hmain:Cref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
        (1+|t|+height)^(degree+2*n))≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.1 (mul_nonneg hK hdiag)
    have hk:K*diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hdiag) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have herr:Dref*(sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
      ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*diagonalControl s.radial.profile≤ E:=by
    have ht:=mul_le_mul_of_nonneg_left hp.2.2 hdiag
    have hk:diagonalControl s.radial.profile*A≤ E:=
      mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left hdiag (le_add_of_nonneg_left hK)) hA
    apply le_trans _ hk
    convert ht using 1 ; ring
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hLpos:0≤ L:=by linarith
  let P:=Z^(s.width+d)
  let Qmain:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*(1+2*(L*Real.log Z))*Z^(s.width+d)
  let Qerror:=(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
    max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i))
  have hP:0≤ P:=by dsimp only [P];positivity
  have hQmain:0≤ Qmain:=by dsimp only [Qmain];positivity
  have hQerror:0≤ Qerror:=by dsimp only [Qerror];positivity
  have htotal:=add_le_add (add_le_add (mul_le_mul_of_nonneg_right hdir hP)
    (mul_le_mul_of_nonneg_right hmain hQmain)) (mul_le_mul_of_nonneg_right herr hQerror)
  apply hh.trans
  have hfirst:=mul_le_mul_of_nonneg_left htotal
    (show 0≤ Cweight*(s.puncture.radical.absNorm:ℝ)^d by positivity)
  have hlast:=mul_le_mul_of_nonneg_left hledger (mul_nonneg hCw.le hE)
  refine le_trans ?_ (hlast.trans_eq ?_)
  · dsimp only [P,Qmain,Qerror] at hfirst
    convert hfirst using 1 <;> (try dsimp only [E,A]) <;> ring
  · dsimp only [E,A]
    ring

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionPowerIV

end

end OAI

end ExtendedModule11

/- BEGIN OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionSymmetric -/
section ExtendedModule12

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricIV
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceStateIV CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionPowerIV
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

omit [DecidableEq α] in
lemma energy_swap (η:Character)(m A:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(X₁ X₂:ℝ)
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₂ W₁ pool β P X₂ X₁ keep Φ K:=by
  unfold energy
  apply tsum_congr
  intro z
  have hh:positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      positiveSlotRow η m A z W₂ W₁ pool β P t X₂ X₁:=by
    unfold positiveSlotRow
    rw [mul_comm X₁ X₂]
    ring
  rw [hh]

theorem balanced_four_scale_gates (Z width X₁ X₂:ℝ)(hZ:1< Z)(hwidth:0< width)
    (hX₁:0< X₁)(hX₂:0< X₂)
    (hshort:width/4≤ min (length Z X₁) (length Z X₂)):
    Z^(width/4)≤ X₁ ∧ Z^(width/4)≤ X₂ ∧
    Z^(width/4)≤ comparisonFirst Z width ∧
    Z^(width/4)≤ comparisonSecond Z width X₁ X₂ ∧
    length Z X₁+length Z X₂=Real.logb Z (X₁*X₂):=by
  have h₁:width/4≤ length Z X₁:=hshort.trans (min_le_left _ _)
  have h₂:width/4≤ length Z X₂:=hshort.trans (min_le_right _ _)
  have hraw (X:ℝ)(hX:0< X)(h:width/4≤ length Z X):
      length Z X=Real.logb Z X ∧ width/4≤ Real.logb Z X:=by
    have he:=CenteredMomentEnergyReferenceLowBranchGeometryIV.length_eq_max_log Z X hZ hX
    have hp:0< Real.logb Z X:=by
      by_contra hn
      rw [he,max_eq_left (le_of_not_gt hn)] at h
      linarith
    refine ⟨he.trans (max_eq_right hp.le),?_⟩
    rwa [he,max_eq_right hp.le] at h
  obtain ⟨he₁,hr₁⟩:=hraw X₁ hX₁ h₁
  obtain ⟨he₂,hr₂⟩:=hraw X₂ hX₂ h₂
  refine ⟨?_,?_,le_refl _,?_,?_⟩
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₁] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₁
  · simpa only [Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX₂] using
      Real.rpow_le_rpow_of_exponent_le hZ.le hr₂
  · rw [comparison_second_power Z width X₁ X₂ hZ hX₁ hX₂,
      Real.logb_mul hX₁.ne' hX₂.ne']
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · rw [he₁,he₂,Real.logb_mul hX₁.ne' hX₂.ne']

variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem original_unbalanced_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask):
    ∃d xi L:ℝ,0< d ∧ 0< xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤ L ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → 13/18≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤ Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0< X₁ → 0< X₂ →
      min (length Z X₁) (length Z X₂)≤ s.width/4 →
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=> primePool M H bslot (Z^(w i)))
