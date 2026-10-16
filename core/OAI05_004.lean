end OAIOriginalModule0926

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Family
Source SHA256: 26f09624152863e1f38e55d58dc1c1604cac32dd3fbfe1d43d01f591c9034788
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0927


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators MatrixGroups
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase ShortDraftCRT CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem simultaneous_controlled_matrices_dependent {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:Eis) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ mat : ∀ x, (∀ i, (Eis ⧸ Ideal.span {p x i})ˣ) → SL(2,Eis),
      (∀ x v, mat x v 0 0 = (D x).matrix v 0 0) ∧
      (∀ x v, mat x v 1 0 = c*∏ i, p x i) ∧
      (∀ x v, if mode then (9:Eis) ∣ mat x v 0 1 ∧ (3:Eis) ∣ mat x v 1 1-1
        else (3:Eis) ∣ mat x v 0 1+1 ∧ (9:Eis) ∣ mat x v 1 1) ∧
      ∀ x y v w, sector x = sector y → ∀ i j, N ∣ mat x v i j-mat y w i j := by
  let X := Σ x : α, (∀ i, (Eis ⧸ Ideal.span {p x i})ˣ)
  let aa : X → Eis := fun x => (D x.1).matrix x.2 0 0
  let rr : X → Eis := fun x => ∏ i, p x.1 i
  let ss : X → Q := fun x => sector x.1
  have h3N : (3:Eis) ∣ N := (show (3:Eis) ∣ 9 from ⟨3,by norm_num⟩).trans h9N
  have hacop (x : X) : IsCoprime (aa x) (c*rr x) := by
    refine ⟨(D x.1).matrix x.2 1 1, -(D x.1).matrix x.2 0 1, ?_⟩
    have hd := ((D x.1).matrix x.2).property
    rw [Matrix.det_fin_two] at hd
    change (D x.1).matrix x.2 0 0 * (D x.1).matrix x.2 1 1 -
      (D x.1).matrix x.2 0 1 * (D x.1).matrix x.2 1 0 = 1 at hd
    rw [(D x.1).denominator] at hd
    dsimp [aa,rr]
    linear_combination hd
  have haa (x y : X) (h : ss x = ss y) : N*c ∣ aa x-aa y := by
    dsimp [aa]
    rw [(D x.1).numerator,(D y.1).numerator]
    exact finiteCrossNumerator_fixed_sector N a c ramifiedTraceLambda
      (p x.1) ((D x.1).lift x.2) (p y.1) ((D y.1).lift y.2)
      hcN ((D x.1).lift_period x.2) ((D y.1).lift_period y.2) (hsector x.1 y.1 h)
  have hrr (x y : X) (h : ss x = ss y) : N ∣ rr x-rr y :=
    (dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x.1 y.1 h)
  have hex : ∃ (b d : X → Eis) (C : Q → Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {N})),
      (∀ x, aa x*d x-b x*(c*rr x)=1) ∧
      (∀ x, if mode then (9:Eis) ∣ b x ∧ (3:Eis) ∣ d x-1
        else (3:Eis) ∣ b x+1 ∧ (9:Eis) ∣ d x) ∧
      ∀ x, (!![aa x,b x;c*rr x,d x] : Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {N})) = C (ss x) := by
    cases mode
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩ := exists_primary_denominator_sector_completions
        N c h9N hbase ss aa rr (fun x => hprimary x.1) hacop
        (fun x => hcop x.1) haa hrr
      exact ⟨b,d,C,hd,fun x => ⟨hb x,hz x⟩,hm⟩
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩ := exists_primary_numerator_sector_completions
        N c hc h9N ss aa rr
        (fun x => (D x.1).numerator_primary h3N (hprimary x.1) hbase x.2)
        (fun x => hprimary x.1) hacop (fun x => hcop x.1) haa hrr
      exact ⟨b,d,C,hd,fun x => ⟨hb x,hz x⟩,hm⟩
  obtain ⟨b,d,C,hdet,hcond,hmat⟩ := hex
  let mat := fun (x : α) (v : ∀ i, (Eis ⧸ Ideal.span {p x i})ˣ) =>
    controlledCompletionMatrix (aa ⟨x,v⟩) (b ⟨x,v⟩) (c*rr ⟨x,v⟩) (d ⟨x,v⟩) (hdet ⟨x,v⟩)
  refine ⟨mat,fun _ _ => rfl,fun _ _ => rfl,fun x v => hcond ⟨x,v⟩,?_⟩
  intro x y v w hs i j
  have hs' : ss ⟨x,v⟩ = ss ⟨y,w⟩ := hs
  have he := (hmat ⟨x,v⟩).trans ((congrArg C hs').trans (hmat ⟨y,w⟩).symm)
  have he' := congrArg (fun T : Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {N}) => T i j) he
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he')

theorem exists_sector_controlled_arithmetic_dependent {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:Eis) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∀ x y v w, sector x = sector y → ∀ i j,
        N ∣ (E x).matrix v i j-(E y).matrix w i j := by
  obtain ⟨mat,ha,hr,hcond,hfixed⟩ := simultaneous_controlled_matrices_dependent
    p N a c mode D hc h9N hcN hprimary hbase hcop sector hsector
  let E : ∀ x, ControlledStratumArithmetic (p x) N a c mode := fun x =>
    { D x with
      matrix := mat x
      numerator := fun v => (ha x v).trans ((D x).numerator v)
      denominator := hr x
      matrix_fixed := fun v i j => hfixed x x v (fun _ => 1) rfl i j
      conditions := hcond x }
  exact ⟨E,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,hfixed⟩

theorem exists_sector_templates {α Q : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i))
    (hmatrix : ∀ x y, sector x = sector y → ∀ i j,
      N ∣ (D x).matrix (fun _ => 1) i j-(D y).matrix (fun _ => 1) i j) :
    ∃ (κ : Q → ℂ) (β : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
      (∀ x, (D x).fixedFactor = κ (sector x)) ∧
      ∀ x u m n b,
        fixedCuspArrayWithPhase s.index u
          (s.reflectionStaticPhase c hc
            (Ideal.Quotient.mk _ (-((D x).matrix (fun _ => 1) 1 1)*(D x).U))
            (s.modelDualNumerator u) u) m n b = β (sector x) u m n b := by
  have hbad : ramifiedTraceLambda^3*c ∣ N := by
    apply (show ramifiedTraceLambda^3*c ∣ (9:Eis)*c from ?_).trans hN
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [← A4_traceLambda_pow_four]
    ring
  let A := fun x (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) =>
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc
        (Ideal.Quotient.mk _ (-((D x).matrix (fun _ => 1) 1 1)*(D x).U))
        (s.modelDualNumerator u) u) m n b
  have hf : (fun x => (D x).fixedFactor).FactorsThrough sector := by
    intro x y hxy
    exact controlled_fixedFactor_eq (D x) (D y) hN (hprimary x) (hprimary y) hbase
      (hmatrix x y hxy 0 0) (hmatrix x y hxy 0 1)
  have ha : A.FactorsThrough sector := by
    intro x y hxy
    funext u m n b
    exact controlled_static_array_eq (D x) (D y) hc s hbad
      ((dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x y hxy))
      (hmatrix x y hxy 1 1) u m n b
  obtain ⟨κ,hκ⟩ := (Function.factorsThrough_iff _).mp hf
  obtain ⟨β,hβ⟩ := (Function.factorsThrough_iff A).mp ha
  refine ⟨κ,β,fun x => congrFun hκ x,?_⟩
  intro x u m n b
  exact congrFun (congrFun (congrFun (congrFun (congrFun hβ x) u) m) n) b

theorem exists_separate_ray_templates {α : Type*} {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (f : Eis) (r P : α → Eis) (hprod : ∀ x, (∏ i, p x i) = f*r x*P x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x, (E x).fixedFactor = κ (separateSector N (r x) (P x))) ∧
        ∀ x u m n b,
          fixedCuspArrayWithPhase s.index u
            (s.reflectionStaticPhase c hc
              (Ideal.Quotient.mk _ (-((E x).matrix (fun _ => 1) 1 1)*(E x).U))
              (s.modelDualNumerator u) u) m n b = β (separateSector N (r x) (P x)) u m n b := by
  let sector := fun x => separateSector N (r x) (P x)
  have hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i) := by
    intro x y hxy
    rw [hprod x,hprod y]
    exact separateSector_product N f (r x) (r y) (P x) (P y) hxy
  obtain ⟨E,hlift,hU,hσ,hε,hmat⟩ := exists_sector_controlled_arithmetic_dependent p N a c mode D
    hc ((dvd_mul_right 9 c).trans hN) ((dvd_mul_left c 9).trans hN)
    hprimary hbase hcop sector hsector
  refine ⟨E,hlift,hU,hσ,hε,?_⟩
  exact exists_sector_templates p N a c mode E s hc hN hprimary hbase sector hsector
    (fun x y hxy => hmat x y (fun _ => 1) (fun _ => 1) hxy)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0927

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Transport
Source SHA256: 2a33785ea444b72835f9f7a9798920af209571d89b9f04c6a71417f1e6e13427
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0928


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι → Eis}
noncomputable local instance transportFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] [Fintype κ] in
theorem residualWithFrozen_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (f : κ → ι) (hf : Function.Injective f) (R F : Finset κ) :
    residualWithFrozen (fun i => hp (f i)) (fun i => hg (f i)) c R F =
      residualWithFrozen hp hg c (R.image f) (F.image f) := by
  unfold residualWithFrozen
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf R i,Finset.prod_image hf.injOn,Finset.prod_image hf.injOn]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem markedWithFrozen_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (f : κ → ι) (hf : Function.Injective f) (S F : Finset κ) :
    markedWithFrozen (fun i => hp (f i)) (fun i => hg (f i)) c S F =
      markedWithFrozen hp hg c (S.image f) (F.image f) := by
  unfold markedWithFrozen
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf S i,Finset.prod_image hf.injOn,Finset.prod_image hf.injOn]
  rfl

omit [Fintype ι] [Fintype κ] in
theorem ramifiedBlock_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (S : Finset κ) (u : Eisˣ) (m : ℕ) :
    ramifiedBlock (fun i => hg (f i)) (fun i => j (f i)) S u m =
      ramifiedBlock hg j (S.image f) u m := by
  unfold ramifiedBlock
  rw [Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem frozenArgument_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenArgument (fun i => hg (f i)) (fun i => j (f i)) F =
      frozenArgument hg j (F.image f) := by
  unfold frozenArgument
  rw [Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem sourceRowPhase_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (R F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s (fun i => hp (f i)) (fun i => hg (f i)) (fun i => j (f i)) R F u m =
      sourceRowPhase s hp hg j (R.image f) (F.image f) u m := by
  unfold sourceRowPhase
  rw [residualWithFrozen_transport hp hg c f hf R F,
    ramifiedBlock_transport hg (fun _ => 1) f hf R,
    frozenArgument_transport hg j f hf F,Finset.prod_image hf.injOn]

omit [Fintype ι] [Fintype κ] in
theorem sourceSlotPhase_transport [∀ i, (Ideal.span {p i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (S F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s (fun i => hp (f i)) (fun i => hg (f i)) (fun i => j (f i)) S F u m =
      sourceSlotPhase s hp hg j (S.image f) (F.image f) u m := by
  unfold sourceSlotPhase
  rw [markedWithFrozen_transport hp hg c f hf S F,
    ramifiedBlock_transport hg (fun _ => 0) f hf S,
    frozenArgument_transport hg j f hf F,Finset.prod_image hf.injOn]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0928

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Functions
Source SHA256: b581a07cf4670ac999371c7ed24e4b6f8e0a57baf00522b5f8d2d9b2e71536aa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0929


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma sourceRowPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (R F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceRowPhase s hp hg j R F u m = sourceRowPhase s hq hqg j' R F u m := by
  subst q
  subst j'
  rfl

lemma sourceSlotPhase_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (S F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    sourceSlotPhase s hp hg j S F u m = sourceSlotPhase s hq hqg j' S F u m := by
  subst q
  subst j'
  rfl

theorem sourceRowPhase_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (R F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s hp hg j (R.image f) (F.image f) u m =
      sourceRowPhase s hq hqg j' (R.image g) (F.image g) u m := by
  rw [← sourceRowPhase_transport s hp hg j f hf R F u m,
    ← sourceRowPhase_transport s hq hqg j' g hg' R F u m]
  exact sourceRowPhase_congr_functions s _ _ _ _ _ _ R F u m (funext he) (funext hj)

theorem sourceSlotPhase_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    {a c : Eis} {mode : Bool} (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (S F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s hp hg j (S.image f) (F.image f) u m =
      sourceSlotPhase s hq hqg j' (S.image g) (F.image g) u m := by
  rw [← sourceSlotPhase_transport s hp hg j f hf S F u m,
    ← sourceSlotPhase_transport s hq hqg j' g hg' S F u m]
  exact sourceSlotPhase_congr_functions s _ _ _ _ _ _ S F u m (funext he) (funext hj)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0929

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SectorIndependence
Source SHA256: 2eb3d8ac3a78fa16167afe1c8d9fd7cefae9321dc895a17b5c7d29ff75d2afbb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0930



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance sectorIndependentFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem frozenCore_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) :
    frozenCore (fun i => hp (f i)) (fun i => hg (f i)) c (fun i => j (f i)) F =
      frozenCore hp hg c j (F.image f) := by
  unfold frozenCore
  rw [Finset.prod_image hf.injOn]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase hf F i,Finset.prod_image hf.injOn]

lemma frozenCore_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (c : Eis) (j j' : κ → ℕ) (F : Finset κ) (he : p=q) (hj : j=j') :
    frozenCore hp hg c j F = frozenCore hq hqg c j' F := by
  subst q; subst j'; rfl

lemma ramifiedBlock_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (F : Finset κ) (u : Eisˣ) (m : ℕ) (he : p=q) (hj : j=j') :
    ramifiedBlock hg j F u m = ramifiedBlock hqg j' F u m := by
  subst q; subst j'; rfl

def frozenColumnProduct {κ : Type*} [Fintype κ]
    {p : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : κ → ℕ) (F : Finset κ) (n b : Ideal Eis) : ℂ :=
  ∏ i ∈ F, bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))

theorem frozenColumnProduct_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (f : κ → ι) (hf : Function.Injective f) (F : Finset κ) (n b : Ideal Eis) :
    frozenColumnProduct (fun i => hg (f i)) (fun i => j (f i)) F n b =
      frozenColumnProduct hg j (F.image f) n b := by
  unfold frozenColumnProduct
  rw [Finset.prod_image hf.injOn]

lemma frozenColumnProduct_congr_functions {κ : Type*} [Fintype κ]
    {p q : κ → Eis} [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (j j' : κ → ℕ) (F : Finset κ) (n b : Ideal Eis) (he : p=q) (hj : j=j') :
    frozenColumnProduct hg j F n b = frozenColumnProduct hqg j' F n b := by
  subst q; subst j'; rfl

theorem sourceFrozenPhase_sector_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (D₀ : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hq : ∀ i, q i ≠ 0) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (hN : (9:Eis)*c ∣ N) (hr : λ₀^2 ∣ (∏ i, p i)-1) (hr₀ : λ₀^2 ∣ (∏ i, q i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hmatrix : ∀ i j, N ∣ D.matrix (fun _ => 1) i j-D₀.matrix (fun _ => 1) i j)
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (F : Finset κ) (u : Eisˣ) (m : ℕ) :
    sourceFrozenPhase D s hp hg j (F.image f) u m =
      sourceFrozenPhase D₀ s hq hqg j' (F.image g) u m := by
  unfold sourceFrozenPhase
  rw [controlled_fixedFactor_eq D D₀ hN hr hr₀ hbase (hmatrix 0 0) (hmatrix 0 1),
    ← frozenCore_transport hp hg c j f hf F,← frozenCore_transport hq hqg c j' g hg' F,
    ← ramifiedBlock_transport hg j f hf F,← ramifiedBlock_transport hqg j' g hg' F,
    frozenCore_congr_functions _ _ _ _ c _ _ F (funext he) (funext hj),
    ramifiedBlock_congr_functions _ _ _ _ F _ _ (funext he) (funext hj)]

theorem sourceColumn_sector_independent {ι μ κ : Type*} [Fintype ι] [Fintype μ] [Fintype κ]
    {p : ι → Eis} {q : μ → Eis} {N a c : Eis} {mode : Bool}
    [∀ i, (Ideal.span {p i}).IsMaximal] [∀ i, (Ideal.span {q i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (D₀ : ControlledStratumArithmetic q N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (hqg : ∀ i, λ₀ ∉ Ideal.span {q i})
    (hbad : CubicEisenstein.ramifiedTraceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, q i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1-D₀.matrix (fun _ => 1) 1 1)
    (j : ι → ℕ) (j' : μ → ℕ) (f : κ → ι) (g : κ → μ)
    (hf : Function.Injective f) (hg' : Function.Injective g)
    (he : ∀ i, p (f i)=q (g i)) (hj : ∀ i, j (f i)=j' (g i))
    (F : Finset κ) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc hg j (F.image f) u m n b =
      sourceColumn D₀ s hc hqg j' (F.image g) u m n b := by
  unfold sourceColumn
  rw [controlled_static_array_eq D D₀ hc s hbad hr hd u m n b]
  congr 1
  change frozenColumnProduct hg j (F.image f) n b = frozenColumnProduct hqg j' (F.image g) n b
  rw [← frozenColumnProduct_transport hg j f hf F,← frozenColumnProduct_transport hqg j' g hg' F]
  exact frozenColumnProduct_congr_functions _ _ _ _ F n b (funext he) (funext hj)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0930

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Common
Source SHA256: fea2b7324cf95b73b3f303f2a3fb1826053df75ca796625543b1811feb874a0c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0931


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem exists_common_reflected_coefficients {α Q κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) [∀ x i, (Ideal.span {p x i}).IsMaximal]
    (N a c : Eis) (mode : Bool) (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ x i, p x i ≠ 0) (hc : c ≠ 0) (hg : ∀ x i, λ₀ ∉ Ideal.span {p x i})
    (hN : (9:Eis)*c ∣ N) (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, p x (f x i)=p y (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i))
    (hmatrix : ∀ x y, sector x = sector y → ∀ i j,
      N ∣ (D x).matrix (fun _ => 1) i j-(D y).matrix (fun _ => 1) i j) :
    ∃ (γ : Q → Eisˣ → ℕ → ℂ) (β : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
      (∀ x u m, sourceFrozenPhase (D x) s (hp x) (hg x) (j x) (F.image (f x)) u m =
        γ (sector x) u m) ∧
      ∀ x u m n b, sourceColumn (D x) s hc (hg x) (j x) (F.image (f x)) u m n b =
        β (sector x) u m n b := by
  have hbad : ramifiedTraceLambda^3*c ∣ N := by
    apply (show ramifiedTraceLambda^3*c ∣ (9:Eis)*c from ?_).trans hN
    refine ⟨ramifiedTraceLambda,?_⟩
    rw [← A4_traceLambda_pow_four]
    ring
  let G := fun x => sourceFrozenPhase (D x) s (hp x) (hg x) (j x) (F.image (f x))
  let B := fun x => sourceColumn (D x) s hc (hg x) (j x) (F.image (f x))
  have hG : G.FactorsThrough sector := by
    intro x y hxy
    funext u m
    exact sourceFrozenPhase_sector_independent (D x) (D y) s (hp x) (hg x) (hp y) (hg y)
      hN (hprimary x) (hprimary y) hbase (hmatrix x y hxy) (j x) (j y) (f x) (f y)
      (hf x) (hf y) (hfixed x y) (hjfixed x y) F u m
  have hB : B.FactorsThrough sector := by
    intro x y hxy
    funext u m n b
    exact sourceColumn_sector_independent (D x) (D y) s hc (hg x) (hg y) hbad
      ((dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x y hxy))
      (hmatrix x y hxy 1 1) (j x) (j y) (f x) (f y)
      (hf x) (hf y) (hfixed x y) (hjfixed x y) F u m n b
  obtain ⟨γ,hγ⟩ := (Function.factorsThrough_iff G).mp hG
  obtain ⟨β,hβ⟩ := (Function.factorsThrough_iff B).mp hB
  refine ⟨γ,β,?_,?_⟩
  · intro x u m
    exact congrFun (congrFun (congrFun hγ x) u) m
  · intro x u m n b
    exact congrFun (congrFun (congrFun (congrFun (congrFun hβ x) u) m) n) b

theorem exists_separate_common_reflected_coefficients {α κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)]
    (p : ∀ x, ι x → Eis) [∀ x i, (Ideal.span {p x i}).IsMaximal]
    (N a c : Eis) (mode : Bool) (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ x i, p x i ≠ 0) (hc : c ≠ 0) (hg : ∀ x i, λ₀ ∉ Ideal.span {p x i})
    (hN : (9:Eis)*c ∣ N) (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, p x (f x i)=p y (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (fixedProduct : Eis) (r P : α → Eis)
    (hprod : ∀ x, (∏ i, p x i) = fixedProduct*r x*P x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧ (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧ (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s (hp x) (hg x) (j x) (F.image (f x)) u m =
          γ (separateSector N (r x) (P x)) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc (hg x) (j x) (F.image (f x)) u m n b =
          β (separateSector N (r x) (P x)) u m n b := by
  let sector := fun x => separateSector N (r x) (P x)
  have hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i) := by
    intro x y hxy
    rw [hprod x,hprod y]
    exact separateSector_product N fixedProduct (r x) (r y) (P x) (P y) hxy
  obtain ⟨E,hlift,hU,hσ,hε,hmat⟩ := exists_sector_controlled_arithmetic_dependent p N a c mode D
    hc ((dvd_mul_right 9 c).trans hN) ((dvd_mul_left c 9).trans hN)
    hprimary hbase hcop sector hsector
  refine ⟨E,hlift,hU,hσ,hε,?_⟩
  exact exists_common_reflected_coefficients p N a c mode E s hp hc hg hN hprimary hbase
    j f hf hfixed hjfixed F sector hsector
    (fun x y hxy => hmat x y (fun _ => 1) (fun _ => 1) hxy)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0931

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Canonical
Source SHA256: 535687b83f38abf83d3d482d2dee2262a450d00c21b220d8057d1099296b209d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0932


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

structure PrimeFamily (ι : Type*) where
  ideal : ι → Ideal Eis
  maximal : ∀ i, (ideal i).IsMaximal
  good : ∀ i, λ₀ ∉ ideal i

namespace PrimeFamily
variable {ι : Type*} (G : PrimeFamily ι)
instance idealMaximal (i : ι) : (G.ideal i).IsMaximal := G.maximal i

def generator (i : ι) : Eis := primaryPrime (G.ideal i)

lemma generator_ne_zero (i : ι) : G.generator i ≠ 0 := primaryPrime_ne_zero _ (G.good i)
lemma generator_span (i : ι) : Ideal.span {G.generator i} = G.ideal i :=
  (primaryPrime_spec _ (G.generator_ne_zero i)).2.2.1
lemma generator_primary (i : ι) : λ₀^2 ∣ G.generator i-1 :=
  (primaryPrime_spec _ (G.generator_ne_zero i)).2.2.2
instance generatorMaximal (i : ι) : (Ideal.span {G.generator i}).IsMaximal :=
  G.generator_span i ▸ G.maximal i
lemma generator_good (i : ι) : λ₀ ∉ Ideal.span {G.generator i} := by
  rw [G.generator_span]
  exact G.good i

lemma generator_product [Fintype ι] :
    (∏ i, G.generator i) = primaryGenerator (∏ i, G.ideal i) := by
  change _ = primaryGeneratorHom (∏ i, G.ideal i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact primaryPrime_eq_primaryGenerator (G.ideal i)

lemma generator_product_primary [Fintype ι] : λ₀^2 ∣ (∏ i, G.generator i)-1 :=
  primary_finset_product Finset.univ G.generator (fun i _ => G.generator_primary i)

lemma generator_coprime_period (N : Eis)
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) (i : ι) :
    IsCoprime N (G.generator i) := by
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [G.generator_span]
  exact hN i

lemma generator_product_coprime_period [Fintype ι] (N c : Eis) (hc : c ∣ N)
    (hN : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    IsCoprime (∏ i, G.generator i) (N*c) := by
  have hh : IsCoprime N (∏ i, G.generator i) :=
    IsCoprime.prod_right (fun i _ => G.generator_coprime_period N hN i)
  exact hh.symm.mul_right (hh.symm.of_isCoprime_of_dvd_right hc)

theorem exists_controlled [Fintype ι] (N a c : Eis) (mode : Bool)
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : Pairwise (Function.onFun IsCoprime G.ideal))
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) (G.ideal i)) :
    Nonempty (ControlledStratumArithmetic G.generator N a c mode) := by
  apply exists_controlledStratumArithmetic G.generator G.generator_ne_zero
  · intro i k hik
    simpa only [G.generator_span] using hcop hik
  · exact G.generator_primary
  · exact hc
  · exact hN
  · exact hbase
  · exact hac
  · exact G.generator_coprime_period N hNp

end PrimeFamily

theorem canonical_common_reflected_coefficients {α κ : Type*} [Fintype κ]
    {ι : α → Type*} [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : ∀ x, Pairwise (Function.onFun IsCoprime (G x).ideal))
    (hNp : ∀ x i, IsCoprime (Ideal.span {N}) ((G x).ideal i))
    (j : ∀ x, ι x → ℕ) (f : ∀ x, κ → ι x) (hf : ∀ x, Function.Injective (f x))
    (hfixed : ∀ x y i, (G x).ideal (f x i)=(G y).ideal (f y i))
    (hjfixed : ∀ x y i, j x (f x i)=j y (f y i)) (F : Finset κ)
    (fixedIdeal : Ideal Eis) (row slot : α → Ideal Eis)
    (hprod : ∀ x, (∏ i, (G x).ideal i) = fixedIdeal*row x*slot x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode,
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s (G x).generator_ne_zero (G x).generator_good
          (j x) (F.image (f x)) u m =
          γ (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc (G x).generator_good (j x) (F.image (f x)) u m n b =
          β (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m n b := by
  let D : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode := fun x =>
    Classical.choice ((G x).exists_controlled N a c mode hc hN hbase hac (hcop x) (hNp x))
  have hproduct (x : α) : (∏ i, (G x).generator i) =
      primaryGenerator fixedIdeal*primaryGenerator (row x)*primaryGenerator (slot x) := by
    rw [(G x).generator_product,hprod x,primaryGenerator_mul,primaryGenerator_mul]
  obtain ⟨E,_,_,_,_,γ,β,hγ,hβ⟩ := exists_separate_common_reflected_coefficients
    (fun x => (G x).generator) N a c mode D s (fun x => (G x).generator_ne_zero) hc
    (fun x => (G x).generator_good) hN (fun x => (G x).generator_product_primary) hbase
    (fun x => (G x).generator_product_coprime_period N c ((dvd_mul_left c 9).trans hN) (hNp x))
    j f hf (fun x y i => congrArg primaryPrime (hfixed x y i)) hjfixed F
    (primaryGenerator fixedIdeal) (fun x => primaryGenerator (row x)) (fun x => primaryGenerator (slot x)) hproduct
  exact ⟨E,γ,β,hγ,hβ⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0932

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Rows
Source SHA256: 3df5a802d205eb8da9622a9577e4360580bee5b08646aa07c172b220d1db22b4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0933


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

namespace PrimeFamily
variable {ι κ : Type*}

def sum (G : PrimeFamily ι) (H : PrimeFamily κ) : PrimeFamily (ι ⊕ κ) where
  ideal := Sum.elim G.ideal H.ideal
  maximal i := by cases i with | inl i => exact G.maximal i | inr i => exact H.maximal i
  good i := by cases i with | inl i => exact G.good i | inr i => exact H.good i

lemma sum_product [Fintype ι] [Fintype κ] (G : PrimeFamily ι) (H : PrimeFamily κ) :
    (∏ i, (G.sum H).ideal i) = (∏ i, G.ideal i)*(∏ i, H.ideal i) := by
  simp only [sum,Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]

lemma sum_pairwise (G : PrimeFamily ι) (H : PrimeFamily κ)
    (hG : Pairwise (Function.onFun IsCoprime G.ideal))
    (hH : Pairwise (Function.onFun IsCoprime H.ideal))
    (hcross : ∀ i k, IsCoprime (G.ideal i) (H.ideal k)) :
    Pairwise (Function.onFun IsCoprime (G.sum H).ideal) := by
  intro i k hik
  cases i with
  | inl i => cases k with
    | inl k => exact hG (fun h => hik (congrArg Sum.inl h))
    | inr k => exact hcross i k
  | inr i => cases k with
    | inl k => exact (hcross k i).symm
    | inr k => exact hH (fun h => hik (congrArg Sum.inr h))

def residual (K : Ideal Eis) (hK : Admissible K) : PrimeFamily (PrimeIndex K) where
  ideal := fun P => P.val
  maximal _P := inferInstance
  good := admissiblePrimeGood K hK

lemma residual_product (K : Ideal Eis) (hK : Admissible K) :
    (∏ P, (residual K hK).ideal P) = K := admissible_primeIndex_product K hK

lemma residual_dvd (K : Ideal Eis) (hK : Admissible K) (P : PrimeIndex K) : P.val ∣ K :=
  Ideal.dvd_iff_le.mpr (primeIndex_le K hK.1 P)

lemma residual_pairwise (K : Ideal Eis) (hK : Admissible K) :
    Pairwise (Function.onFun IsCoprime (residual K hK).ideal) := by
  intro P Q hPQ
  apply Ideal.isCoprime_of_isMaximal
  intro h
  exact hPQ (Subtype.ext h)

def reflected {φ σ : Type*} (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) : PrimeFamily (φ ⊕ (PrimeIndex K ⊕ σ)) := F.sum ((residual K hK).sum S)

lemma reflected_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i, (F.reflected K hK S).ideal i) = (∏ i, F.ideal i)*K*(∏ i, S.ideal i) := by
  rw [reflected,sum_product,sum_product,residual_product]
  ring

lemma reflected_pairwise {φ σ : Type*} [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hS : Pairwise (Function.onFun IsCoprime S.ideal))
    (hKS : IsCoprime K (∏ i, S.ideal i))
    (hFK : ∀ f, IsCoprime (F.ideal f) K)
    (hFS : ∀ f i, IsCoprime (F.ideal f) (S.ideal i)) :
    Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal) := by
  apply sum_pairwise F _ hF
  · apply sum_pairwise _ S (residual_pairwise K hK) hS
    intro P i
    exact (hKS.of_isCoprime_of_dvd_left (residual_dvd K hK P)).of_isCoprime_of_dvd_right
      (Finset.dvd_prod_of_mem S.ideal (Finset.mem_univ i))
  · intro f i
    cases i with
    | inl P => exact (hFK f).of_isCoprime_of_dvd_right (residual_dvd K hK P)
    | inr i => exact hFS f i

lemma reflected_period {φ σ : Type*}
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (N : Eis)
    (hF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hK' : IsCoprime (Ideal.span {N}) K)
    (hS : ∀ i, IsCoprime (Ideal.span {N}) (S.ideal i)) :
    ∀ i, IsCoprime (Ideal.span {N}) ((F.reflected K hK S).ideal i) := by
  intro i
  cases i with
  | inl f => exact hF f
  | inr i => cases i with
    | inl P => exact hK'.of_isCoprime_of_dvd_right (residual_dvd K hK P)
    | inr i => exact hS i

end PrimeFamily
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0933

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Moving
Source SHA256: b881babdbe1ca6b68b15a79abfc3430246d31f72f08696687dac8f950d3900d1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0934


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def reflectedExponent {φ ρ σ : Type*} (jF : φ → ℕ) : φ ⊕ (ρ ⊕ σ) → ℕ :=
  Sum.elim jF (Sum.elim (fun _ => 1) (fun _ => 0))

def frozenIndices (φ ρ σ : Type*) [Fintype φ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image φ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) Sum.inl Finset.univ

def residualIndices (φ ρ σ : Type*) [Fintype ρ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image ρ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inl) Finset.univ

def slotIndices (φ ρ σ : Type*) [Fintype σ] : Finset (φ ⊕ (ρ ⊕ σ)) :=
  @Finset.image σ (φ ⊕ (ρ ⊕ σ)) (Classical.decEq _) (Sum.inr ∘ Sum.inr) Finset.univ

lemma reflected_indices_partition (φ ρ σ : Type*) [Fintype φ] [Fintype ρ] [Fintype σ] :
    Disjoint (residualIndices φ ρ σ) (slotIndices φ ρ σ) ∧
    Disjoint (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) (frozenIndices φ ρ σ) ∧
    (residualIndices φ ρ σ ∪ slotIndices φ ρ σ) ∪ frozenIndices φ ρ σ = Finset.univ := by
  classical
  simp only [residualIndices, slotIndices, frozenIndices, Finset.disjoint_left,
    Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Function.comp_apply]
  constructor
  · rintro i ⟨r, rfl⟩ ⟨s, h⟩
    cases h
  constructor
  · rintro i (⟨r, rfl⟩ | ⟨s, rfl⟩) ⟨f, h⟩ <;> cases h
  · ext i
    cases i with
    | inl f => simp
    | inr i => cases i with
      | inl r => simp
      | inr s => simp

lemma reflected_residual_exponent {φ ρ σ : Type*} [Fintype ρ] (jF : φ → ℕ) :
    ∀ i ∈ residualIndices φ ρ σ, reflectedExponent jF i = 1 := by
  let : DecidableEq (φ ⊕ (ρ ⊕ σ)) := Classical.decEq _
  rintro i hi
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
  rfl

namespace PrimeFamily
lemma reflected_residual_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i ∈ residualIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = K := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, residualIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inl_injective).injOn]
  exact residual_product K hK

lemma reflected_slot_product {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) :
    (∏ i ∈ slotIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) = ∏ i, S.ideal i := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  simp only [generator_span, slotIndices]
  rw [Finset.prod_image (Sum.inr_injective.comp Sum.inr_injective).injOn]
  rfl
end PrimeFamily

theorem moving_common_reflected_coefficients {α φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : α → Ideal Eis) (hK : ∀ x, Admissible (K x))
    (S : α → PrimeFamily σ) (jF : φ → ℕ)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2 ∣ a-1
      else ConcretePrimeRowBridge.goodLambda^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hS : ∀ x, Pairwise (Function.onFun IsCoprime (S x).ideal))
    (hKS : ∀ x, IsCoprime (K x) (∏ i, (S x).ideal i))
    (hFK : ∀ x f, IsCoprime (F.ideal f) (K x))
    (hFS : ∀ x f i, IsCoprime (F.ideal f) ((S x).ideal i))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hNK : ∀ x, IsCoprime (Ideal.span {N}) (K x))
    (hNS : ∀ x i, IsCoprime (Ideal.span {N}) ((S x).ideal i)) :
    ∃ E : ∀ x, ControlledStratumArithmetic (F.reflected (K x) (hK x) (S x)).generator N a c mode,
      ∃ (γ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → Eisˣ → ℕ → ℂ)
        (β : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ x u m, sourceFrozenPhase (E x) s
          (F.reflected (K x) (hK x) (S x)).generator_ne_zero
          (F.reflected (K x) (hK x) (S x)).generator_good
          (reflectedExponent jF) (frozenIndices φ (PrimeIndex (K x)) σ) u m =
          γ (separateSector N (primaryGenerator (K x))
            (primaryGenerator (∏ i, (S x).ideal i))) u m) ∧
        ∀ x u m n b, sourceColumn (E x) s hc
          (F.reflected (K x) (hK x) (S x)).generator_good
          (reflectedExponent jF) (frozenIndices φ (PrimeIndex (K x)) σ) u m n b =
          β (separateSector N (primaryGenerator (K x))
            (primaryGenerator (∏ i, (S x).ideal i))) u m n b := by
  classical
  simpa only [frozenIndices] using canonical_common_reflected_coefficients
    (fun x => F.reflected (K x) (hK x) (S x)) N a c mode s hc hN hbase hac
    (fun x => F.reflected_pairwise (K x) (hK x) (S x) hF (hS x) (hKS x) (hFK x) (hFS x))
    (fun x => F.reflected_period (K x) (hK x) (S x) N hNF (hNK x) (hNS x))
    (fun _ => reflectedExponent jF) (fun _ => Sum.inl) (fun _ => Sum.inl_injective)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) Finset.univ (∏ i, F.ideal i) K
    (fun x => ∏ i, (S x).ideal i) (fun x => F.reflected_product (K x) (hK x) (S x))

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0934

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Projections
Source SHA256: 2f1025975f5aacadb47cbb8b2074b23cd0c0d9efafb929ccc41a159d3bae65af
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0935


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {a c : Eis} {mode : Bool}

def actualRowPhase (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  sourceRowPhase s (F.sum (PrimeFamily.residual K hK)).generator_ne_zero
    (F.sum (PrimeFamily.residual K hK)).generator_good (Sum.elim jF (fun _ => 1))
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m

def actualSlotPhase (F : PrimeFamily φ) (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  sourceSlotPhase s (F.sum S).generator_ne_zero (F.sum S).generator_good
    (Sum.elim jF (fun _ => 0)) (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m

omit [Fintype σ] in
theorem sourceRowPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (residualIndices φ (PrimeIndex K) σ) (frozenIndices φ (PrimeIndex K) σ) u m =
      actualRowPhase F K hK jF s u m := by
  classical
  let f : φ ⊕ PrimeIndex K → φ ⊕ (PrimeIndex K ⊕ σ) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)
  have hf : Function.Injective f := by
    intro i k h
    cases i <;> cases k <;> simp_all [f]
  have he := sourceRowPhase_transport s (F.reflected K hK S).generator_ne_zero
    (F.reflected K hK S).generator_good (reflectedExponent jF) f hf
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m
  have hp : (fun i => (F.reflected K hK S).generator (f i)) =
      (F.sum (PrimeFamily.residual K hK)).generator := by
    funext i
    cases i <;> rfl
  have hj : (fun i => reflectedExponent jF (f i)) = Sum.elim jF (fun _ => 1) := by
    funext i
    cases i <;> rfl
  have hh := sourceRowPhase_congr_functions s
    (fun i => (F.reflected K hK S).generator_ne_zero (f i))
    (fun i => (F.reflected K hK S).generator_good (f i))
    (F.sum (PrimeFamily.residual K hK)).generator_ne_zero
    (F.sum (PrimeFamily.residual K hK)).generator_good
    _ _ (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m hp hj
  rw [he] at hh
  simpa only [actualRowPhase,residualIndices,frozenIndices,Finset.image_image,
    Function.comp_def,f,Sum.elim_inl,Sum.elim_inr] using hh

theorem sourceSlotPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceSlotPhase s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (frozenIndices φ (PrimeIndex K) σ) u m =
      actualSlotPhase F S jF s u m := by
  classical
  let f : φ ⊕ σ → φ ⊕ (PrimeIndex K ⊕ σ) := Sum.elim Sum.inl (Sum.inr ∘ Sum.inr)
  have hf : Function.Injective f := by
    intro i k h
    cases i <;> cases k <;> simp_all [f]
  have he := sourceSlotPhase_transport s (F.reflected K hK S).generator_ne_zero
    (F.reflected K hK S).generator_good (reflectedExponent jF) f hf
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m
  have hp : (fun i => (F.reflected K hK S).generator (f i)) = (F.sum S).generator := by
    funext i
    cases i <;> rfl
  have hj : (fun i => reflectedExponent jF (f i)) = Sum.elim jF (fun _ => 0) := by
    funext i
    cases i <;> rfl
  have hh := sourceSlotPhase_congr_functions s
    (fun i => (F.reflected K hK S).generator_ne_zero (f i))
    (fun i => (F.reflected K hK S).generator_good (f i))
    (F.sum S).generator_ne_zero (F.sum S).generator_good
    _ _ (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m hp hj
  rw [he] at hh
  simpa only [actualSlotPhase,slotIndices,frozenIndices,Finset.image_image,
    Function.comp_def,f,Sum.elim_inl,Sum.elim_inr] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0935

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Actual
Source SHA256: 68c96df5000b26fee478f9415ea8e16cafd08da640682aec710fdc4e6f552213
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0936


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualMixedCoefficient (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  s.amplitude u m n b *
    (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
      (s.modelDualNumerator u m n b)) *
    ∏ i, mixedActiveBracket (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) D i (s.modelDualNumerator u m n b)

theorem actualMixedCoefficient_factor (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    actualMixedCoefficient F K hK S jF D s hc u m n b =
      ((-1:ℂ)^(Fintype.card σ)*actualRowPhase F K hK jF s u m*actualSlotPhase F S jF s u m*
        sourceFrozenPhase D s (F.reflected K hK S).generator_ne_zero
          (F.reflected K hK S).generator_good (reflectedExponent jF)
          (frozenIndices φ (PrimeIndex K) σ) u m)*
      sourceColumn D s hc (F.reflected K hK S).generator_good (reflectedExponent jF)
        (frozenIndices φ (PrimeIndex K) σ) u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i, S.ideal i):ℝ):ℂ)⁻¹*
      quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel (∏ i, S.ideal i) n*
      (if IsCoprime (∏ i, S.ideal i) b then 1 else 0)*
      (if IsCoprime K (∏ i, S.ideal i) then 1 else 0) := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  obtain ⟨hRS,hF,hu⟩ := reflected_indices_partition φ (PrimeIndex K) σ
  have hF' : Disjoint (residualIndices φ (PrimeIndex K) σ ∪ slotIndices φ (PrimeIndex K) σ)
      (frozenIndices φ (PrimeIndex K) σ) := by
    simpa only [Finset.disjoint_left,Finset.mem_union] using hF
  have hu' : (residualIndices φ (PrimeIndex K) σ ∪ slotIndices φ (PrimeIndex K) σ) ∪
      frozenIndices φ (PrimeIndex K) σ = Finset.univ := by
    simpa only [Finset.ext_iff,Finset.mem_union] using hu
  have hcp : Pairwise (Function.onFun IsCoprime
      (fun i => Ideal.span {(F.reflected K hK S).generator i})) := by
    simpa only [PrimeFamily.generator_span] using hcop
  have hr : Admissible (∏ i ∈ residualIndices φ (PrimeIndex K) σ,
      Ideal.span {(F.reflected K hK S).generator i}) := by
    rw [F.reflected_residual_product K hK S]
    exact hK
  have he := mixed_coefficient_hybrid_original_exponents D s
    (F.reflected K hK S).generator_ne_zero hc (F.reflected K hK S).generator_good hcp
    (F.reflected K hK S).generator_primary _ _ _ hRS hF' hu'
    (reflectedExponent jF) (reflected_residual_exponent jF) hr u m n b hb
  have hcard : (slotIndices φ (PrimeIndex K) σ).card = Fintype.card σ := by
    rw [slotIndices,Finset.card_image_of_injective _ (Sum.inr_injective.comp Sum.inr_injective)]
    rfl
  rw [hcard,sourceRowPhase_eq_actual,sourceSlotPhase_eq_actual,
    F.reflected_residual_product K hK S,F.reflected_slot_product K hK S] at he
  exact he

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0936

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Columns
Source SHA256: 02c917c404c52834e1be416facad6e881a76fd2a708fe89b9bf5e0a363cea64f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0937


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι φ σ : Type*} [Fintype ι] [Fintype φ] [Fintype σ]
variable {p : ι → Eis} {N a c : Eis} {mode : Bool}

def actualCuspColumn (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase s.index u
    (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
      (s.modelDualNumerator u) u) m n b

lemma actualCuspColumn_norm_le_one (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ‖actualCuspColumn D s hc u m n b‖ ≤ 1 :=
  fixedCuspArrayWithPhase_norm_le_one s.index u _
    (s.reflectionStaticPhase_norm_le_one c hc _ _ u) m n b

def frozenBranchColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  A n b * reflectedBranch (fun i => Ideal.span {F.generator i}) F.generator_good jF e
    (primaryGenerator n) (primaryGenerator b)

def frozenExtracted (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) (v : Fin 3) : Ideal Eis :=
  reflectionExtractedDivisor (fun i => Ideal.span {F.generator i}) jF e v

def frozenBranchScale (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) : ℝ :=
  Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*
    Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)/
    Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 0):ℝ)

theorem sourceColumn_eq_sum_frozenBranches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc (F.reflected K hK S).generator_good (reflectedExponent jF)
      (frozenIndices φ (PrimeIndex K) σ) u m n b =
      ∑ e : φ → Fin 3, frozenBranchColumn F jF e (actualCuspColumn D s hc u m) n b := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  unfold sourceColumn frozenIndices
  rw [Finset.prod_image Sum.inl_injective.injOn]
  change actualCuspColumn D s hc u m n b *
    (∏ i, bracket (actualSextic (Ideal.span {F.generator i}) (F.generator_good i)) (jF i)
      (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))) = _
  exact (congrArg (actualCuspColumn D s hc u m n b * ·)
    (prod_bracket_eq_full_branches (fun i => Ideal.span {F.generator i}) F.generator_good
      jF (primaryGenerator n) (primaryGenerator b))).trans (Finset.mul_sum _ _ _)

theorem frozenBranchColumn_norm_le (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖frozenBranchColumn F jF e A n b‖ ≤ frozenBranchScale F jF e := by
  rw [frozenBranchColumn,norm_mul]
  calc
    _ ≤ 1*‖reflectedBranch (fun i => Ideal.span {F.generator i}) F.generator_good jF e
        (primaryGenerator n) (primaryGenerator b)‖ := mul_le_mul_of_nonneg_right (hA n b) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact reflectedBranch_norm_bound _ F.generator_good jF e _ _

theorem frozenBranchColumn_normalized_bound (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1)
    (n b : Ideal Eis) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖frozenBranchColumn F jF e A n b‖ /
      (Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
        ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 0):ℝ)*
        (Ideal.absNorm (frozenExtracted F jF e 2):ℝ))) := by
  apply (div_le_div_of_nonneg_right ?_ (by positivity)).trans
    (reflectedBranch_normalized_bound (fun i => Ideal.span {F.generator i}) F.generator_good
      jF e (primaryGenerator n) (primaryGenerator b) U B hU hB)
  rw [frozenBranchColumn,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hA n b)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0937

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.BoundedTemplates
Source SHA256: aacb891ea9e1fa5f1102883e25f2bb177ecb840d806f37166d93bb46d478a245
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0938


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def boundedExtension (z : ℂ) : ℂ := if ‖z‖ ≤ 1 then z else 0
lemma boundedExtension_norm (z : ℂ) : ‖boundedExtension z‖ ≤ 1 := by
  unfold boundedExtension
  split_ifs with h
  · exact h
  · simp
lemma boundedExtension_eq (z : ℂ) (hz : ‖z‖ ≤ 1) : boundedExtension z = z := ite_eq_left hz

theorem canonical_bounded_cusp_templates {α : Type*} {ι : α → Type*}
    [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : ∀ x, Pairwise (Function.onFun IsCoprime (G x).ideal))
    (hNp : ∀ x i, IsCoprime (Ideal.span {N}) ((G x).ideal i))
    (fixedIdeal : Ideal Eis) (row slot : α → Ideal Eis)
    (hprod : ∀ x, (∏ i, (G x).ideal i) = fixedIdeal*row x*slot x) :
    ∃ E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode,
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (A : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ q, ‖κ q‖ ≤ 1) ∧ (∀ q u m n b, ‖A q u m n b‖ ≤ 1) ∧
        (∀ x, (E x).fixedFactor = κ (separateSector N (primaryGenerator (row x))
          (primaryGenerator (slot x)))) ∧
        ∀ x u m n b, actualCuspColumn (E x) s hc u m n b =
          A (separateSector N (primaryGenerator (row x)) (primaryGenerator (slot x))) u m n b := by
  let D : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode := fun x =>
    Classical.choice ((G x).exists_controlled N a c mode hc hN hbase hac (hcop x) (hNp x))
  have hproduct (x : α) : (∏ i, (G x).generator i) =
      primaryGenerator fixedIdeal*primaryGenerator (row x)*primaryGenerator (slot x) := by
    rw [(G x).generator_product,hprod x,primaryGenerator_mul,primaryGenerator_mul]
  obtain ⟨E,_,_,_,_,κ,A,hκ,hA⟩ := exists_separate_ray_templates
    (fun x => (G x).generator) N a c mode D s hc hN
    (fun x => (G x).generator_product_primary) hbase
    (fun x => (G x).generator_product_coprime_period N c ((dvd_mul_left c 9).trans hN) (hNp x))
    (primaryGenerator fixedIdeal) (fun x => primaryGenerator (row x))
    (fun x => primaryGenerator (slot x)) hproduct
  refine ⟨E,fun q => boundedExtension (κ q),fun q u m n b => boundedExtension (A q u m n b),
    fun q => boundedExtension_norm _,fun q u m n b => boundedExtension_norm _,?_,?_⟩
  · intro x
    change (E x).fixedFactor = boundedExtension _
    rw [← hκ x,boundedExtension_eq _ ((E x).fixedFactor_norm hN
      (G x).generator_product_primary hbase).le]
  · intro x u m n b
    change actualCuspColumn (E x) s hc u m n b = boundedExtension _
    rw [← hA x u m n b]
    exact (boundedExtension_eq _ (actualCuspColumn_norm_le_one (E x) s hc u m n b)).symm

theorem common_frozen_branch_bound {φ Q : Type*} [Fintype φ]
    (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ)
    (hA : ∀ q u m n b, ‖A q u m n b‖ ≤ 1) (q : Q) (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    ‖frozenBranchColumn F jF e (A q u m) n b‖ ≤ frozenBranchScale F jF e :=
  frozenBranchColumn_norm_le F jF e (A q u m) (hA q u m) n b

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0938

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.FrozenNorms
Source SHA256: 89367f2757e7d5efd3a3e83d0c6e364eb9de23ef88c02239079d5083bc83a465
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0939


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} {p : ι → Eis} {N a c : Eis} {mode : Bool}

lemma frozenCofactorCharacter_cross_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) (j : ℕ) :
    ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (p k)‖ = 1 := by
  have hn := crossSymbol_norm hg hcop i k hik
  unfold frozenCofactorCharacter
  split_ifs
  · simp only [MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv',norm_pow,norm_inv]
    change ‖MixedCrossSeparation.crossSymbol p hg i k‖⁻¹^2 = 1
    rw [hn]; norm_num
  · simp only [MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0),norm_pow]
    change ‖MixedCrossSeparation.crossSymbol p hg i k‖^(2*j+2) = 1
    rw [hn,one_pow]

lemma frozenCofactorCharacter_product_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (S : Finset ι) (hi : i ∉ S) (j : ℕ) :
    ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (∏ k ∈ S, p k)‖ = 1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro k hk
  exact frozenCofactorCharacter_cross_norm hg hcop i k (fun h => hi (h ▸ hk)) j

variable [Fintype ι]

lemma frozenPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i : ι) (j : ℕ) (hj : j < 6) : ‖frozenPrimeScalar (p i) c (hp i) (hg i) j‖ = 1 := by
  have hh := local_phase_norm D hp hg hchar i j hj
  rw [controlled_frozen_phase,norm_mul] at hh
  have hn : ‖frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cofactor p i)‖ = 1 := by
    exact frozenCofactorCharacter_product_norm hg hcop i (Finset.univ.erase i) (by simp) j
  simpa only [hn,mul_one] using hh

lemma frozenCore_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i < 6) : ‖frozenCore hp hg c j F‖ = 1 := by
  rw [frozenCore,norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  rw [norm_mul,frozenPrimeScalar_norm D hp hg hchar hcop i (j i) (hj i hi),one_mul]
  exact frozenCofactorCharacter_product_norm hg hcop i (F.erase i) (by simp) (j i)

lemma sourceFrozenPhase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hN : (9:Eis)*c ∣ N) (hr : λ₀^2 ∣ (∏ i, p i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (j : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i < 6) (u : Eisˣ) (m : ℕ) :
    ‖sourceFrozenPhase D s hp hg j F u m‖ = 1 := by
  rw [sourceFrozenPhase,norm_mul,norm_mul,norm_star,D.fixedFactor_norm hN hr hbase,
    frozenCore_norm D hp hg hchar hcop j F hj,ramifiedBlock_norm]
  norm_num

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0939

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.NormalizedColumns
Source SHA256: a1688ade79f9072cfeac143264cac57f316a0dc8f8cb7e8ef477d6e729289fbc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0940


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualFrozenPhase (F : PrimeFamily φ) (jF : φ → ℕ) (κ : ℂ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  star κ * frozenCore F.generator_ne_zero F.generator_good c jF Finset.univ *
    ramifiedBlock F.generator_good jF Finset.univ
      (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

lemma sourceFrozenPhase_eq_actual (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) :
    sourceFrozenPhase D s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (frozenIndices φ (PrimeIndex K) σ) u m = actualFrozenPhase F jF D.fixedFactor s u m := by
  classical
  let : DecidableEq (φ ⊕ (PrimeIndex K ⊕ σ)) := Classical.decEq _
  unfold sourceFrozenPhase frozenIndices
  rw [← frozenCore_transport (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good c (reflectedExponent jF) Sum.inl Sum.inl_injective Finset.univ,
    ← ramifiedBlock_transport (F.reflected K hK S).generator_good
      (reflectedExponent jF) Sum.inl Sum.inl_injective Finset.univ]
  rfl

lemma frozenExtracted_ne_zero (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) (v : Fin 3) :
    frozenExtracted F jF e v ≠ 0 := by
  apply reflectionExtractedDivisor_ne_zero
  intro i
  rw [F.generator_span]
  exact NeZero.ne _

lemma frozenBranchScale_pos (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3) :
    0 < frozenBranchScale F jF e := by
  have hn (v : Fin 3) : (0:ℝ) < Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact div_pos (mul_pos (Real.sqrt_pos.mpr (hn 1)) (Real.sqrt_pos.mpr (hn 2)))
    (Real.sqrt_pos.mpr (hn 0))

def normalizedFrozenColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  (frozenBranchScale F jF e : ℂ)⁻¹ * frozenBranchColumn F jF e A n b

lemma normalizedFrozenColumn_norm_le_one (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖normalizedFrozenColumn F jF e A n b‖ ≤ 1 := by
  have hp := frozenBranchScale_pos F jF e
  rw [normalizedFrozenColumn,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  calc
    _ ≤ (frozenBranchScale F jF e)⁻¹*frozenBranchScale F jF e :=
      mul_le_mul_of_nonneg_left (frozenBranchColumn_norm_le F jF e A hA n b) (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

lemma frozenBranchColumn_eq_normalized (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) :
    frozenBranchColumn F jF e A n b =
      (frozenBranchScale F jF e : ℂ)*normalizedFrozenColumn F jF e A n b := by
  rw [normalizedFrozenColumn,← mul_assoc,mul_inv_cancel₀,one_mul]
  exact_mod_cast (frozenBranchScale_pos F jF e).ne'

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0940

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ActualBounds
Source SHA256: 7cace2e1bd480dec748ad47ddb6268035229a6c5bbe0b75bc524e50eb8ac908d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0941


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma two_block_phase_bounds (F : PrimeFamily φ) (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hcop : Pairwise (Function.onFun IsCoprime (F.sum S).ideal))
    (hNp : ∀ i, IsCoprime (Ideal.span {N}) ((F.sum S).ideal i))
    (hchar : ∀ i, ringChar (Eis ⧸ (F.sum S).ideal i) ≠ 2) (u : Eisˣ) (m : ℕ) :
    ‖sourceRowPhase s (F.sum S).generator_ne_zero (F.sum S).generator_good
      (Sum.elim jF (fun _ => 1)) (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m‖ ≤ 1 ∧
    ‖actualSlotPhase F S jF s u m‖ ≤ 1 := by
  classical
  obtain ⟨D⟩ := (F.sum S).exists_controlled N a c mode hc hN hbase hac hcop hNp
  have hcp : Pairwise (Function.onFun IsCoprime
      (fun i => Ideal.span {(F.sum S).generator i})) := by
    simpa only [PrimeFamily.generator_span] using hcop
  have hch : ∀ i, ringChar (Eis ⧸ Ideal.span {(F.sum S).generator i}) ≠ 2 := by
    intro i
    have he := congrArg (fun I : Ideal Eis => ringChar (Eis ⧸ I)) ((F.sum S).generator_span i)
    exact he.symm ▸ hchar i
  have hd : Disjoint (Finset.univ.image (Sum.inr : σ → φ ⊕ σ)) (Finset.univ.image Sum.inl) := by
    simp only [Finset.disjoint_left,Finset.mem_image,Finset.mem_univ,true_and]
    rintro i ⟨k,rfl⟩ ⟨f,h⟩
    cases h
  exact ⟨sourceRowPhase_norm_le_one D s _ _ hch hcp _ _ _ hd u m,
    sourceSlotPhase_norm_le_one D s _ _ hch hcp _ _ _ hd u m⟩

lemma actualRowPhase_norm_le_one (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (jF : φ → ℕ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hFK : ∀ f, IsCoprime (F.ideal f) K)
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hNK : IsCoprime (Ideal.span {N}) K)
    (hcharF : ∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) (u : Eisˣ) (m : ℕ) :
    ‖actualRowPhase F K hK jF s u m‖ ≤ 1 := by
  have hcp := PrimeFamily.sum_pairwise F (PrimeFamily.residual K hK) hF
    (PrimeFamily.residual_pairwise K hK) (fun f P =>
      (hFK f).of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK P))
  have hNp : ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (PrimeFamily.residual K hK)).ideal i) := by
    intro i
    cases i with
    | inl f => exact hNF f
    | inr P => exact hNK.of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK P)
  have hchar : ∀ i, ringChar (Eis ⧸ (F.sum (PrimeFamily.residual K hK)).ideal i) ≠ 2 := by
    intro i
    cases i with
    | inl f => exact hcharF f
    | inr P => exact (hK.2.2 P.val (Multiset.mem_toFinset.mp P.property)).2
  have hh := (two_block_phase_bounds F (PrimeFamily.residual K hK) jF s hc hN hbase hac hcp hNp hchar u m).1
  unfold actualRowPhase
  convert hh using 1 ; congr 2 <;> ext i <;> simp

lemma actualFrozenPhase_norm_le_one (F : PrimeFamily φ) (jF : φ → ℕ) (κ : ℂ) (hκ : ‖κ‖ ≤ 1)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hcharF : ∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) (hj : ∀ f, jF f < 6) (u : Eisˣ) (m : ℕ) :
    ‖actualFrozenPhase F jF κ s u m‖ ≤ 1 := by
  obtain ⟨D⟩ := F.exists_controlled N a c mode hc hN hbase hac hF hNF
  have hcp : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {F.generator i})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hch : ∀ i, ringChar (Eis ⧸ Ideal.span {F.generator i}) ≠ 2 := by
    intro i
    have he := congrArg (fun I : Ideal Eis => ringChar (Eis ⧸ I)) (F.generator_span i)
    exact he.symm ▸ hcharF i
  rw [actualFrozenPhase,norm_mul,norm_mul,norm_star,
    frozenCore_norm D _ _ hch hcp _ _ (fun i _ => hj i),ramifiedBlock_norm,mul_one,mul_one]
  exact hκ

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0941

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.FamilyFactorization
Source SHA256: 833d50720ceb190174675f6815a1783dd9d63eff1895bb35126f3b364690585b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0942


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem actualMixedCoefficient_common_branches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ → ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (κ : ℂ) (A : Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ)
    (hκ : D.fixedFactor = κ)
    (hA : ∀ u m n b, actualCuspColumn D s hc u m n b = A u m n b)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    actualMixedCoefficient F K hK S jF D s hc u m n b =
      ∑ e : φ → Fin 3,
        ((-1:ℂ)^(Fintype.card σ)*actualRowPhase F K hK jF s u m*
          actualSlotPhase F S jF s u m*actualFrozenPhase F jF κ s u m)*
        (frozenBranchScale F jF e:ℂ)*normalizedFrozenColumn F jF e (A u m) n b*
        (Real.sqrt (Ideal.absNorm (∏ i, S.ideal i):ℝ):ℂ)⁻¹*
        quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel (∏ i, S.ideal i) n*
        (if IsCoprime (∏ i, S.ideal i) b then 1 else 0)*
        (if IsCoprime K (∏ i, S.ideal i) then 1 else 0) := by
  rw [actualMixedCoefficient_factor F K hK S jF D s hc hcop u m n b hb,
    sourceFrozenPhase_eq_actual,hκ,sourceColumn_eq_sum_frozenBranches]
  have hfun : actualCuspColumn D s hc u m = A u m := funext (fun n => funext (fun b => hA u m n b))
  rw [hfun,Finset.mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [frozenBranchColumn_eq_normalized]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0942

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Energy
Source SHA256: a549a0cc0b93eb4ed9fd88168a2ff616341877e43704fc86dd5596926f46cd8e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0943




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def actualRowPhaseExtension (F : PrimeFamily φ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (u : Eisˣ) (m : ℕ) (K : Ideal Eis) : ℂ :=
  if hK : Admissible K then actualRowPhase F K hK jF s u m else 0

def reflectedBranchHybridRow (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal Eis → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis) : ℂ :=
  ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF κ s u m*
    actualRowPhaseExtension F jF s u m K)*
    hybridRow Pset nset bset (fun P => actualSlotPhase F (S P) jF s u m)
      (frozenBranchColumn F jF e A) K

lemma hybridRow_frozenColumn (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (Pset nset bset : Finset (Ideal Eis))
    (aP : Ideal Eis → ℂ) (K : Ideal Eis) :
    hybridRow Pset nset bset aP (frozenBranchColumn F jF e A) K =
      (frozenBranchScale F jF e:ℂ)*hybridRow Pset nset bset aP (normalizedFrozenColumn F jF e A) K := by
  unfold hybridRow hybridInner
  simp_rw [frozenBranchColumn_eq_normalized]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem actual_reflected_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∑ K ∈ rows, ‖reflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) u m Pset nset bset K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Y*B*L)^ε*(X+Y*B)*B*(Y+L+(Y*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := hybridRow_energy ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S hrows hrowcop _hproducts hScop hSN hSchar hn hb hP
  have hfrozen : ‖actualFrozenPhase F jF D0.fixedFactor s u m‖ ≤ 1 :=
    actualFrozenPhase_norm_le_one F jF D0.fixedFactor (D0.fixedFactor_norm hN G0.generator_product_primary hbase).le
      s hc hN hbase hac hF hNF hcharF hj u m
  have hrow (K : Ideal Eis) (hK : K ∈ rows) : ‖actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    rw [actualRowPhaseExtension,dite_eq_left (hrows K hK).1]
    exact actualRowPhase_norm_le_one F K (hrows K hK).1 jF s hc hN hbase hac hF
      (hrowcop K hK).1 hNF (hrowcop K hK).2 hcharF u m
  have hslot (P : Ideal Eis) (hP : P ∈ Pset) : ‖actualSlotPhase F (S P) jF s u m‖ ≤ 1 :=
    (two_block_phase_bounds F (S P) jF s hc hN hbase hac (hScop P hP) (hSN P hP) (hSchar P hP) u m).2
  have hcolumn : ∀ n b, ‖normalizedFrozenColumn F jF e (actualCuspColumn D0 s hc u m) n b‖ ≤ 1 :=
    normalizedFrozenColumn_norm_le_one F jF e _ (actualCuspColumn_norm_le_one D0 s hc u m)
  have hh := he X Y B L hX hY hB hL rows nset bset Pset
    (fun P => actualSlotPhase F (S P) jF s u m)
    (normalizedFrozenColumn F jF e (actualCuspColumn D0 s hc u m)) hrows hn hb hP hslot
    (fun n _ b _ => hcolumn n b)
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    ((by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)) :
      (∑ K ∈ rows, (frozenBranchScale F jF e)^2*
        ‖hybridRow Pset nset bset (fun P => actualSlotPhase F (S P) jF s u m)
          (normalizedFrozenColumn F jF e (actualCuspColumn D0 s hc u m)) K‖^2) ≤ _)
  rw [reflectedBranchHybridRow,hybridRow_frozenColumn]
  have hp := frozenBranchScale_pos F jF e
  have hphase : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hfrozen).trans (hrow K hK)
  rw [norm_mul,norm_mul (frozenBranchScale F jF e:ℂ) _,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow,mul_pow]
  have hs : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K‖^2 ≤ 1 := by
    have hpos := norm_nonneg ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*actualRowPhaseExtension F jF s u m K)
    nlinarith
  exact (mul_le_mul_of_nonneg_right hs (mul_nonneg (sq_nonneg _) (sq_nonneg _))).trans_eq (one_mul _)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0943

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SourceSum
Source SHA256: 972c0d8f29c440371c9e830be36717d8ce06fd0a9531b3bf08cdfb742674abfc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0944


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]
variable {N a c : Eis} {mode : Bool}

theorem masked_actual_coefficient (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (P : Ideal Eis) (hprod : (∏ i, S.ideal i) = P) (jF : φ → ℕ)
    (D : IsCoprime K P → ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (hcop : IsCoprime K P → Pairwise (Function.onFun IsCoprime (F.reflected K hK S).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ h, (D h).fixedFactor = D0.fixedFactor)
    (hA : ∀ h u m n b, actualCuspColumn (D h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (if h : IsCoprime K P then actualMixedCoefficient F K hK S jF (D h) s hc u m n b else 0) =
      ∑ e : φ → Fin 3,
        ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
          actualRowPhaseExtension F jF s u m K)*
        (actualSlotPhase F S jF s u m / (Real.sqrt (Ideal.absNorm P:ℝ):ℂ))*
        (if IsCoprime K P then 1 else 0)*
        (frozenBranchColumn F jF e (actualCuspColumn D0 s hc u m) n b*
          quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*
          (if IsCoprime P b then 1 else 0)) := by
  by_cases hKP : IsCoprime K P
  · rw [dite_eq_left hKP]
    have hh := actualMixedCoefficient_common_branches F K hK S jF (D hKP) s hc (hcop hKP)
      D0.fixedFactor (actualCuspColumn D0 s hc) (hκ hKP) (hA hKP) u m n b hb
    rw [hprod] at hh
    rw [hh]
    apply Finset.sum_congr rfl
    intro e he
    rw [actualRowPhaseExtension,dite_eq_left hK,frozenBranchColumn_eq_normalized]
    simp only [ite_eq_left hKP,div_eq_mul_inv]
    ring
  · simp only [dite_eq_right hKP,ite_eq_right hKP,mul_zero,zero_mul,Finset.sum_const_zero]

def actualPhysicalReflectedRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) : ℂ :=
  ∑ P : Pset, ∑ n ∈ nset, ∑ b ∈ bset,
    if h : IsCoprime K P.val then actualMixedCoefficient F K hK (S P.val) jF (D P h) s hc u m n b else 0

theorem actualPhysicalReflectedRow_eq_branches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (hcop : ∀ P : Pset, IsCoprime K P.val →
      Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ P h, (D P h).fixedFactor = D0.fixedFactor)
    (hA : ∀ P h u m n b, actualCuspColumn (D P h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0) (u : Eisˣ) (m : ℕ) :
    actualPhysicalReflectedRow F K hK S jF Pset nset bset D s hc u m =
      ∑ e : φ → Fin 3, reflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) u m Pset nset bset K := by
  unfold actualPhysicalReflectedRow
  have he (P : Pset) (n : Ideal Eis) (b : Ideal Eis) (hb' : b ∈ bset) :=
    masked_actual_coefficient F K hK (S P.val) P.val (hprod P.val P.property) jF
      (D P) (hcop P) G0 D0 s hc (hκ P) (hA P) u m n b (hb b hb')
  simp_rw [reflectedBranchHybridRow,hybridRow,hybridInner,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort Pset]
  apply Finset.sum_congr rfl
  intro P hP
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb'
  rw [he P n b hb']
  apply Finset.sum_congr rfl
  intro e he'
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0944

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Extraction
Source SHA256: 2636d26a2c1cd9c5f7e0049c886dafd100b978182ba3efa48f6d3b5337e5ddb2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0945



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ]

lemma frozenBranchColumn_divisibility (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis)
    (hn : primaryGenerator n ≠ 0) (hb : primaryGenerator b ≠ 0)
    (hz : frozenBranchColumn F jF e A n b ≠ 0) :
    frozenExtracted F jF e 1 ∣ n ∧ frozenExtracted F jF e 2 ∣ b ∧
      ∀ i, jF i=4 → e i=2 → primaryGenerator n ∉ F.ideal i := by
  have hcp : Pairwise (fun i k => IsCoprime (Ideal.span {F.generator i}) (Ideal.span {F.generator k})) := by
    simpa only [PrimeFamily.generator_span] using hF
  have hh := reflectedBranch_divisibility (fun i => Ideal.span {F.generator i}) F.generator_good hcp
    jF e (primaryGenerator n) (primaryGenerator b) (mul_ne_zero_iff.mp hz).2
  simpa only [frozenExtracted,(primaryGenerator_spec n hn).1,(primaryGenerator_spec b hb).1,
    PrimeFamily.generator_span] using hh

lemma frozenBranchColumn_zero_of_not_dvd (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis)
    (hn : primaryGenerator n ≠ 0) (hb : primaryGenerator b ≠ 0)
    (hz : ¬ frozenExtracted F jF e 1 ∣ n ∨ ¬ frozenExtracted F jF e 2 ∣ b) :
    frozenBranchColumn F jF e A n b = 0 := by
  by_contra hh
  obtain ⟨hd1,hd2,_⟩ := frozenBranchColumn_divisibility F hF jF e A n b hn hb hh
  exact hz.elim (fun h => h hd1) (fun h => h hd2)

theorem frozenBranchColumn_dual_reindex (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A W : Ideal Eis → Ideal Eis → ℂ) (nset bset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0) :
    (∑ n ∈ nset, ∑ b ∈ bset, frozenBranchColumn F jF e A n b*W n b) =
      ∑ n ∈ quotientSupport (frozenExtracted F jF e 1) nset,
        ∑ b ∈ quotientSupport (frozenExtracted F jF e 2) bset,
          frozenBranchColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)*
            W ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b) := by
  classical
  have hfilter :
      (∑ n ∈ nset, ∑ b ∈ bset, frozenBranchColumn F jF e A n b*W n b) =
      ∑ n ∈ nset with frozenExtracted F jF e 1 ∣ n,
        ∑ b ∈ bset with frozenExtracted F jF e 2 ∣ b, frozenBranchColumn F jF e A n b*W n b := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn'
    by_cases hd1 : frozenExtracted F jF e 1 ∣ n
    · rw [ite_eq_left hd1]
      apply Finset.sum_congr rfl
      intro b hb'
      by_cases hd2 : frozenExtracted F jF e 2 ∣ b
      · rw [ite_eq_left hd2]
      · rw [ite_eq_right hd2,frozenBranchColumn_zero_of_not_dvd F hF jF e A n b (hn n hn') (hb b hb') (Or.inr hd2),zero_mul]
    · rw [ite_eq_right hd1]
      apply Finset.sum_eq_zero
      intro b hb'
      rw [frozenBranchColumn_zero_of_not_dvd F hF jF e A n b (hn n hn') (hb b hb') (Or.inl hd1),zero_mul]
  rw [hfilter,sum_quotientSupport]
  apply Finset.sum_congr rfl
  intro n hn'
  exact sum_quotientSupport _ _ _

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0945

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ExtractedKernel
Source SHA256: 5c9d4ed85a3e7a94c9c42e1a872b33482b66b3e867358a12011d3cf313fb30da
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0946


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def extractedRowFactor (D1 D2 K : Ideal Eis) : ℂ := quadraticRow K (primaryGenerator (D1*D2))
def extractedSlotFactor (D1 D2 P : Ideal Eis) : ℂ :=
  inverseCubicKernel P D1 * (if IsCoprime P D2 then 1 else 0)

lemma extractedRowFactor_norm_le_one (D1 D2 K : Ideal Eis) : ‖extractedRowFactor D1 D2 K‖ ≤ 1 :=
  quadraticRow_norm_le_one K _

lemma extractedSlotFactor_norm_le_one (D1 D2 P : Ideal Eis) : ‖extractedSlotFactor D1 D2 P‖ ≤ 1 := by
  unfold extractedSlotFactor
  split_ifs
  · simpa only [mul_one] using inverseCubicKernel_norm_le_one P D1
  · simp

lemma coprime_product_mask (P D b : Ideal Eis) :
    (if IsCoprime P (D*b) then (1:ℂ) else 0) =
      (if IsCoprime P D then 1 else 0)*(if IsCoprime P b then 1 else 0) := by
  by_cases hD : IsCoprime P D <;> by_cases hb : IsCoprime P b
  · simp [hD,hb,hD.mul_right hb]
  · have hn : ¬IsCoprime P (D*b) := fun h => hb (h.of_isCoprime_of_dvd_right (dvd_mul_left _ _))
    simp [hD,hb,hn]
  · have hn : ¬IsCoprime P (D*b) := fun h => hD (h.of_isCoprime_of_dvd_right (dvd_mul_right _ _))
    simp [hD,hb,hn]
  · have hn : ¬IsCoprime P (D*b) := fun h => hD (h.of_isCoprime_of_dvd_right (dvd_mul_right _ _))
    simp [hD,hb,hn]

theorem forced_dual_kernel_factor (D1 D2 K P n b : Ideal Eis)
    (hK : Admissible K) (hP : primaryGenerator P ≠ 0) :
    quadraticRow K (primaryGenerator ((D1*n)*(D2*b)))*inverseCubicKernel P (D1*n)*
      (if IsCoprime P (D2*b) then 1 else 0)*(if IsCoprime K P then 1 else 0) =
      (extractedRowFactor D1 D2 K*extractedSlotFactor D1 D2 P)*
        quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*
        (if IsCoprime P b then 1 else 0)*(if IsCoprime K P then 1 else 0) := by
  rw [show (D1*n)*(D2*b)=(D1*D2)*(n*b) by ring,primaryGenerator_mul,
    canonical_quadraticRow_argument_mul K hK,inverseCubicKernel_mul_right P D1 n hP,
    coprime_product_mask]
  unfold extractedRowFactor extractedSlotFactor
  ring

def extractedFrozenColumn {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
    (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ) (n b : Ideal Eis) : ℂ :=
  normalizedFrozenColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)

lemma extractedFrozenColumn_norm_le_one {φ : Type*} [Fintype φ] (F : PrimeFamily φ)
    (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ)
    (hA : ∀ n b, ‖A n b‖ ≤ 1) (n b : Ideal Eis) : ‖extractedFrozenColumn F jF e A n b‖ ≤ 1 :=
  normalizedFrozenColumn_norm_le_one F jF e A hA _ _

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0946

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ExtractedRow
Source SHA256: 73df1424ebcb53259599e3e8d01c666fb12335b32d1f2a953677c2fde4472f47
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0947


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ : Type*} [Fintype φ]

lemma hybridInner_frozen_dual_reindex (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (nset bset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (K P : Ideal Eis) :
    hybridInner nset bset (frozenBranchColumn F jF e A) K P =
      ∑ n ∈ quotientSupport (frozenExtracted F jF e 1) nset,
        ∑ b ∈ quotientSupport (frozenExtracted F jF e 2) bset,
          frozenBranchColumn F jF e A ((frozenExtracted F jF e 1)*n) ((frozenExtracted F jF e 2)*b)*
            quadraticRow K (primaryGenerator (((frozenExtracted F jF e 1)*n)*((frozenExtracted F jF e 2)*b)))*
            inverseCubicKernel P ((frozenExtracted F jF e 1)*n)*
            (if IsCoprime P ((frozenExtracted F jF e 2)*b) then 1 else 0) := by
  simpa only [hybridInner,mul_assoc] using frozenBranchColumn_dual_reindex F hF jF e A
    (fun n b => quadraticRow K (primaryGenerator (n*b))*inverseCubicKernel P n*(if IsCoprime P b then 1 else 0))
    nset bset hn hb

theorem hybridRow_frozen_extraction (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal)) (jF : φ → ℕ) (e : φ → Fin 3)
    (A : Ideal Eis → Ideal Eis → ℂ) (nset bset Pset : Finset (Ideal Eis))
    (hn : ∀ n ∈ nset, primaryGenerator n ≠ 0) (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (aP : Ideal Eis → ℂ) (K : Ideal Eis) (hK : Admissible K)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0) :
    hybridRow Pset nset bset aP (frozenBranchColumn F jF e A) K =
      ((frozenBranchScale F jF e:ℂ)*extractedRowFactor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2) K)*
        hybridRow Pset (quotientSupport (frozenExtracted F jF e 1) nset)
          (quotientSupport (frozenExtracted F jF e 2) bset)
          (fun P => aP P*extractedSlotFactor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2) P)
          (extractedFrozenColumn F jF e A) K := by
  unfold hybridRow
  simp_rw [hybridInner_frozen_dual_reindex F hF jF e A nset bset hn hb]
  simp only [hybridInner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP'
  apply Finset.sum_congr rfl
  intro n hn'
  apply Finset.sum_congr rfl
  intro b hb'
  rw [frozenBranchColumn_eq_normalized]
  have hh := forced_dual_kernel_factor (frozenExtracted F jF e 1) (frozenExtracted F jF e 2)
    K P n b hK (hP P hP')
  have he := congrArg (fun z : ℂ => aP P/(Real.sqrt (Ideal.absNorm P:ℝ):ℂ)*
    (frozenBranchScale F jF e:ℂ)*extractedFrozenColumn F jF e A n b*z) hh
  convert he using 1 <;> simp only [extractedFrozenColumn,div_eq_mul_inv] <;> ring

lemma quotientSupport_norm_div (D : Ideal Eis) (hD : D ≠ 0) (S : Finset (Ideal Eis)) (Y : ℝ)
    (hS : ∀ I ∈ S, (Ideal.absNorm I:ℝ) ≤ Y) (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    (Ideal.absNorm J:ℝ) ≤ Y/(Ideal.absNorm D:ℝ) := by
  have hpos : (0:ℝ) < Ideal.absNorm D := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  have hh := hS (D*J) ((mem_quotientSupport D J hD S).mp hJ)
  rw [map_mul,Nat.cast_mul] at hh
  exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hh)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0947

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ExtractedEnergy
Source SHA256: e3df6f6a09c46334b2a05af8d5227e14e4c3b8f9bfbba0cb701006474cc024cf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0948


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ ι : Type*} [Fintype φ] [Fintype ι] {N a c : Eis} {mode : Bool}

def extractedDualScale (D : Ideal Eis) (Y : ℝ) : ℝ := max 1 (Y/(Ideal.absNorm D:ℝ))

theorem frozen_hybrid_energy_extracted (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y B L : ℝ, 1 ≤ X → 1 ≤ L →
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ → ℕ) (e : φ → Fin 3), ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0) (u : Eisˣ) (m : ℕ)
      (rows nset bset Pset : Finset (Ideal Eis)) (aP : Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ P ∈ Pset, ‖aP P‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖hybridRow Pset nset bset aP
        (frozenBranchColumn F jF e (actualCuspColumn D0 s hc u m)) K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := hybridRow_energy ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hL F hF jF e ι _ G0 D0 s hc u m rows nset bset Pset aP hrows hn hb hP ha
  let D1 := frozenExtracted F jF e 1
  let D2 := frozenExtracted F jF e 2
  let Yq := extractedDualScale D1 Y
  let Bq := extractedDualScale D2 B
  have hD1 : D1 ≠ 0 := frozenExtracted_ne_zero F jF e 1
  have hD2 : D2 ≠ 0 := frozenExtracted_ne_zero F jF e 2
  have hnq : ∀ n ∈ quotientSupport D1 nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Yq := by
    intro n hn'
    exact ⟨quotientSupport_cubic_admissible D1 hD1 nset (fun n h => (hn n h).1) n hn',
      (quotientSupport_norm_div D1 hD1 nset Y (fun n h => (hn n h).2) n hn').trans (le_max_right _ _)⟩
  have hbq : ∀ b ∈ quotientSupport D2 bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ Bq := by
    intro b hb'
    have hsource := hb (D2*b) ((mem_quotientSupport D2 b hD2 bset).mp hb')
    rw [primaryGenerator_mul] at hsource
    exact ⟨(mul_ne_zero_iff.mp hsource.1).2,
      (quotientSupport_norm_div D2 hD2 bset B (fun b h => (hb b h).2) b hb').trans (le_max_right _ _)⟩
  have hacoeff : ∀ P ∈ Pset, ‖aP P*extractedSlotFactor D1 D2 P‖ ≤ 1 := by
    intro P hP'
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha P hP')).trans (extractedSlotFactor_norm_le_one D1 D2 P)
  have hcolumn : ∀ n b, ‖extractedFrozenColumn F jF e (actualCuspColumn D0 s hc u m) n b‖ ≤ 1 :=
    extractedFrozenColumn_norm_le_one F jF e _ (actualCuspColumn_norm_le_one D0 s hc u m)
  have hh := he X Yq Bq L hX (le_max_left _ _) (le_max_left _ _) hL rows
    (quotientSupport D1 nset) (quotientSupport D2 bset) Pset
    (fun P => aP P*extractedSlotFactor D1 D2 P)
    (extractedFrozenColumn F jF e (actualCuspColumn D0 s hc u m))
    hrows hnq hbq hP hacoeff (fun n _ b _ => hcolumn n b)
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    ((by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)) :
      (∑ K ∈ rows, (frozenBranchScale F jF e)^2*
        ‖hybridRow Pset (quotientSupport D1 nset) (quotientSupport D2 bset)
          (fun P => aP P*extractedSlotFactor D1 D2 P)
          (extractedFrozenColumn F jF e (actualCuspColumn D0 s hc u m)) K‖^2) ≤ _)
  rw [hybridRow_frozen_extraction F hF jF e _ nset bset Pset
    (fun n h => (hn n h).1.2) (fun b h => (hb b h).1) aP K (hrows K hK).1
    (fun P h => (hP P h).1.2)]
  have hp := frozenBranchScale_pos F jF e
  have hs := extractedRowFactor_norm_le_one D1 D2 K
  have hs2 : ‖extractedRowFactor D1 D2 K‖^2 ≤ 1 := by
    have h0 := norm_nonneg (extractedRowFactor D1 D2 K)
    nlinarith
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow]
  change (frozenBranchScale F jF e)^2*‖extractedRowFactor D1 D2 K‖^2* _ ≤ _
  calc
    _ ≤ ((frozenBranchScale F jF e)^2*1)*_ := by gcongr
    _ = _ := by rw [mul_one]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0948

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ActualExtractedEnergy
Source SHA256: 0c35c6516192bb3ae29d3f3c9a05bfff6cef31d84c24288a0488dc6e55938e7b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0949


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem actual_reflected_branch_energy_extracted (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖reflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) u m Pset nset bset K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := frozen_hybrid_energy_extracted (φ := φ) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX _hY _hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S hrows hrowcop _hproducts hScop hSN hSchar hn hb hP
  have hfrozen : ‖actualFrozenPhase F jF D0.fixedFactor s u m‖ ≤ 1 :=
    actualFrozenPhase_norm_le_one F jF D0.fixedFactor (D0.fixedFactor_norm hN G0.generator_product_primary hbase).le
      s hc hN hbase hac hF hNF hcharF hj u m
  have hrow (K : Ideal Eis) (hK : K ∈ rows) : ‖actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    rw [actualRowPhaseExtension,dite_eq_left (hrows K hK).1]
    exact actualRowPhase_norm_le_one F K (hrows K hK).1 jF s hc hN hbase hac hF
      (hrowcop K hK).1 hNF (hrowcop K hK).2 hcharF u m
  have hslot (P : Ideal Eis) (hP : P ∈ Pset) : ‖actualSlotPhase F (S P) jF s u m‖ ≤ 1 :=
    (two_block_phase_bounds F (S P) jF s hc hN hbase hac (hScop P hP) (hSN P hP) (hSchar P hP) u m).2
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    (he X Y B L hX hL F hF jF e G0 D0 s hc u m rows nset bset Pset
      (fun P => actualSlotPhase F (S P) jF s u m) hrows hn hb hP hslot)
  have hphase : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hfrozen).trans (hrow K hK)
  have hphase0 := norm_nonneg ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K)
  have hs : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K‖^2 ≤ 1 := by nlinarith
  rw [reflectedBranchHybridRow,norm_mul,mul_pow]
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans_eq (one_mul _)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0949

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SourceFamily
Source SHA256: d9c8e4dfb38cd495859bffa58ab49a7b22fdc100663582207d10e29c037326e6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0950


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def SourcePair (rows Pset : Finset (Ideal Eis)) :=
  {x : rows × Pset // IsCoprime x.1.val x.2.val}

variable {φ σ : Type*} [Fintype φ] [Fintype σ]

theorem exists_source_pair_templates (F : PrimeFamily φ)
    (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis → PrimeFamily σ)
    (hrows : ∀ K ∈ rows, Admissible K)
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hScop : ∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((S P).ideal i)) :
    ∃ E : ∀ x : SourcePair rows Pset,
      ControlledStratumArithmetic
        (F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)).generator N a c mode,
      ∃ (κ : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) → ℂ)
        (A : ((Eis ⧸ Ideal.span {N^2}) × (Eis ⧸ Ideal.span {N^2})) →
          Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ),
        (∀ q, ‖κ q‖ ≤ 1) ∧ (∀ q u m n b, ‖A q u m n b‖ ≤ 1) ∧
        (∀ x, (E x).fixedFactor = κ (separateSector N (primaryGenerator x.val.1.val)
          (primaryGenerator x.val.2.val))) ∧
        ∀ x u m n b, actualCuspColumn (E x) s hc u m n b =
          A (separateSector N (primaryGenerator x.val.1.val) (primaryGenerator x.val.2.val)) u m n b := by
  let G := fun x : SourcePair rows Pset =>
    F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)
  have hpair (x : SourcePair rows Pset) : Pairwise (Function.onFun IsCoprime (G x).ideal) := by
    apply F.reflected_pairwise x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val) hF
    · intro i k hik
      change IsCoprime ((F.sum (S x.val.2.val)).ideal (Sum.inr i))
        ((F.sum (S x.val.2.val)).ideal (Sum.inr k))
      exact hScop x.val.2.val x.val.2.property (Sum.inr_injective.ne hik)
    · rw [hprod _ x.val.2.property]
      exact x.property
    · exact (hrowcop _ x.val.1.property).1
    · intro f i
      change IsCoprime ((F.sum (S x.val.2.val)).ideal (Sum.inl f))
        ((F.sum (S x.val.2.val)).ideal (Sum.inr i))
      exact hScop x.val.2.val x.val.2.property (Sum.inl_ne_inr : (Sum.inl f : φ ⊕ σ) ≠ Sum.inr i)
  have hNp (x : SourcePair rows Pset) : ∀ i, IsCoprime (Ideal.span {N}) ((G x).ideal i) :=
    F.reflected_period _ _ _ N hNF (hrowcop _ x.val.1.property).2 (hSN _ x.val.2.property)
  apply canonical_bounded_cusp_templates G N a c mode s hc hN hbase hac hpair hNp
    (∏ i, F.ideal i) (fun x => x.val.1.val) (fun x => x.val.2.val)
  intro x
  rw [PrimeFamily.reflected_product,hprod _ x.val.2.property]

theorem source_templates_equal_to_representative {α : Type*} {ι : α → Type*}
    [∀ x, Fintype (ι x)] (G : ∀ x, PrimeFamily (ι x))
    {N a c : Eis} {mode : Bool}
    (E : ∀ x, ControlledStratumArithmetic (G x).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    {Q : Type*} (q : α → Q) (κ : Q → ℂ) (A : Q → Eisˣ → ℕ → Ideal Eis → Ideal Eis → ℂ)
    (hκ : ∀ x, (E x).fixedFactor = κ (q x))
    (hA : ∀ x u m n b, actualCuspColumn (E x) s hc u m n b = A (q x) u m n b)
    (x0 x : α) (hq : q x = q x0) :
    (E x).fixedFactor = (E x0).fixedFactor ∧
      ∀ u m n b, actualCuspColumn (E x) s hc u m n b = actualCuspColumn (E x0) s hc u m n b := by
  constructor
  · rw [hκ x,hκ x0,hq]
  · intro u m n b
    rw [hA x u m n b,hA x0 u m n b,hq]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0950

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Shape
Source SHA256: bd46e2483b90a22f208eebff854c84028391322a81446560e58c2ca84ac34102
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0951


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CubicKubota ConcreteTraceCRT CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def shapeArgument (z : Eis) : ℂ := ((Ideal.absNorm (Ideal.span {z}):ℝ):ℂ)/(eisEmbedding z)^2

lemma shapeArgument_mul (x y : Eis) : shapeArgument (x*y) = shapeArgument x*shapeArgument y := by
  unfold shapeArgument
  rw [← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul,Complex.ofReal_mul,map_mul,mul_pow]
  exact mul_div_mul_comm _ _ _ _

lemma shapeArgument_norm (z : Eis) (hz : z ≠ 0) : ‖shapeArgument z‖ = 1 := by
  have hne : ‖eisEmbedding z‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hz))
  rw [shapeArgument,norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg (Nat.cast_nonneg _),
    ← eisEmbedding_norm_sq_eq_absNorm_span]
  exact div_self hne

lemma stratumShapeFactor_mul {H : Matrix.SpecialLinearGroup (Fin 2) Eis}
    (s : FixedCuspShape H) (c r P : Eis) :
    s.stratumShapeFactor (c*r*P) = s.stratumShapeFactor c*shapeArgument r*shapeArgument P := by
  have he (z : Eis) : s.stratumShapeFactor z =
      (-star (levelTwoComplexCharacter s.gamma)*eisEmbedding (s.upper 0 0)^2)*shapeArgument z := by
    unfold FixedCuspShape.stratumShapeFactor shapeArgument
    ring
  rw [he (c*r*P),he c,shapeArgument_mul,shapeArgument_mul]
  ring

lemma actual_shape_separation {φ σ : Type*} [Fintype φ] [Fintype σ]
    {H : Matrix.SpecialLinearGroup (Fin 2) Eis} (s : FixedCuspShape H)
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (c : Eis) :
    s.stratumShapeFactor (c*∏ i, (F.reflected K hK S).generator i) =
      s.stratumShapeFactor (c*primaryGenerator (∏ i, F.ideal i))*
        shapeArgument (primaryGenerator K)*shapeArgument (primaryGenerator (∏ i, S.ideal i)) := by
  rw [(F.reflected K hK S).generator_product,F.reflected_product K hK S,
    primaryGenerator_mul,primaryGenerator_mul]
  rw [show c*(primaryGenerator (∏ i, F.ideal i)*primaryGenerator K*primaryGenerator (∏ i, S.ideal i)) =
    (c*primaryGenerator (∏ i, F.ideal i))*primaryGenerator K*primaryGenerator (∏ i, S.ideal i) by ring]
  exact stratumShapeFactor_mul s _ _ _

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0951

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ShapeWeights
Source SHA256: e807b15271ef26835d3b1de76bf18343cd162d0cc80942e65075a292bfdea748
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0952



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[simp] lemma shapeArgument_one : shapeArgument (1:Eis)=1 := by
  simp [shapeArgument,Ideal.span_singleton_one]

lemma stratumShapeFactor_mul_one {H : Matrix.SpecialLinearGroup (Fin 2) Eis}
    (s : FixedCuspShape H) (c r : Eis) :
    s.stratumShapeFactor (c*r)=s.stratumShapeFactor c*shapeArgument r := by
  simpa only [mul_one,shapeArgument_one] using stratumShapeFactor_mul s c r 1

lemma primeFamily_primary_product_ne_zero {φ : Type*} [Fintype φ] (F : PrimeFamily φ) :
    primaryGenerator (∏ i,F.ideal i)≠0 := by
  rw [←F.generator_product]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => F.generator_ne_zero i)

lemma stratumShapeFactor_frozen_norm {φ : Type*} [Fintype φ]
    {H : Matrix.SpecialLinearGroup (Fin 2) Eis} (s : FixedCuspShape H) (c : Eis) (F : PrimeFamily φ) :
    ‖s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i))‖=‖s.stratumShapeFactor c‖ := by
  rw [stratumShapeFactor_mul_one,norm_mul,shapeArgument_norm _ (primeFamily_primary_product_ne_zero F),mul_one]

lemma row_shape_weight_norm (r : Ideal Eis→ℂ) (K : Ideal Eis) (hK : Admissible K) :
    ‖r K*shapeArgument (primaryGenerator K)‖=‖r K‖ := by
  have hk := PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors K hK.1 (fun P hP => (hK.2.2 P hP).1)
  rw [norm_mul,shapeArgument_norm _ hk,mul_one]

lemma slot_shape_weight_norm (aw : Ideal Eis→ℂ) (P : Ideal Eis) (hP : CubicSieve.Admissible P) :
    ‖aw P*shapeArgument (primaryGenerator P)‖=‖aw P‖ := by
  rw [norm_mul,shapeArgument_norm _ hP.2,mul_one]
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0952

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SourceSectors
Source SHA256: 3fe059eff8f4f169453ea223860ab13ab7031d98ed324ee22b7d04f39e922684
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0953


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

variable {φ σ : Type*} [Fintype φ] [Fintype σ]

theorem exists_fixed_ray_source_arithmetic (F : PrimeFamily φ)
    (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis → PrimeFamily σ)
    (hrows : ∀ K ∈ rows, Admissible K)
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c ≠ 0) (hN : (9:Eis)*c ∣ N)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hScop : ∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((S P).ideal i))
    (rowClass slotClass : Eis ⧸ Ideal.span {N^2})
    (hrowClass : ∀ K ∈ rows, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=rowClass)
    (hslotClass : ∀ P ∈ Pset, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator P)=slotClass) :
    ∃ E : ∀ x : SourcePair rows Pset,
      ControlledStratumArithmetic
        (F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property) (S x.val.2.val)).generator N a c mode,
      ∀ x0 x, (E x).fixedFactor = (E x0).fixedFactor ∧
        ∀ u m n b, actualCuspColumn (E x) s hc u m n b = actualCuspColumn (E x0) s hc u m n b := by
  obtain ⟨E,κ,A,_,_,hκ,hA⟩ := exists_source_pair_templates F rows Pset S hrows hprod
    N a c mode s hc hN hbase hac hF hNF hrowcop hScop hSN
  refine ⟨E,?_⟩
  intro x0 x
  have he (y : SourcePair rows Pset) :
      separateSector N (primaryGenerator y.val.1.val) (primaryGenerator y.val.2.val) = (rowClass,slotClass) := by
    exact Prod.ext (hrowClass _ y.val.1.property) (hslotClass _ y.val.2.property)
  constructor
  · rw [hκ x,hκ x0,he x,he x0]
  · intro u m n b
    rw [hA x u m n b,hA x0 u m n b,he x,he x0]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0953

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SectorData
Source SHA256: 2affed53165ad5e47fb1616a4dc1c105e4747f2d6df72093afbce39b5606bb0c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0954


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

structure SectorArithmetic (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows, Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0) where
  referenceIndex : Type (max u v)
  [referenceFintype : Fintype referenceIndex]
  referencePrimes : PrimeFamily referenceIndex
  referenceArithmetic : ControlledStratumArithmetic referencePrimes.generator N a c mode
  completion : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
    ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode
  fixedFactor_eq : ∀ K P hp, (completion K P hp).fixedFactor=referenceArithmetic.fixedFactor
  cuspColumn_eq : ∀ K P hp u m n b,
    actualCuspColumn (completion K P hp) s hc u m n b=actualCuspColumn referenceArithmetic s hc u m n b

attribute [instance] SectorArithmetic.referenceFintype

theorem exists_sector_arithmetic (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows, Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (hN : (9:Eis)*c∣N)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1)
    (hac : IsCoprime a c) (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K∈rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hprod : ∀ P∈Pset, (∏ i,(S P).ideal i)=P)
    (hScop : ∀ P∈Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal))
    (hSN : ∀ P∈Pset, ∀ i, IsCoprime (Ideal.span {N}) ((S P).ideal i))
    (rowClass slotClass : Eis⧸Ideal.span {N^2})
    (hrowClass : ∀ K∈rows, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=rowClass)
    (hslotClass : ∀ P∈Pset, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator P)=slotClass) :
    Nonempty (SectorArithmetic (N:=N) F rows Pset S hrows s hc) := by
  obtain ⟨E,hE⟩ := exists_fixed_ray_source_arithmetic F rows Pset S hrows hprod N a c mode s hc hN hbase hac
    hF hNF hrowcop hScop hSN rowClass slotClass hrowClass hslotClass
  let D := fun (K : rows) (P : Pset) (hp : IsCoprime K.val P.val) => E ⟨(K,P),hp⟩
  by_cases hnon : Nonempty (SourcePair rows Pset)
  · let x0 : SourcePair rows Pset := Classical.choice hnon
    exact ⟨{
      referenceIndex := φ ⊕ (PrimeIndex x0.val.1.val ⊕ σ)
      referencePrimes := F.reflected x0.val.1.val (hrows x0.val.1.val x0.val.1.property) (S x0.val.2.val)
      referenceArithmetic := E x0
      completion := D
      fixedFactor_eq := fun K P hp => (hE x0 ⟨(K,P),hp⟩).1
      cuspColumn_eq := fun K P hp => (hE x0 ⟨(K,P),hp⟩).2
    }⟩
  · let G0 : PrimeFamily (ULift.{v} φ) := ⟨fun x => F.ideal x.down,fun x => F.maximal x.down,fun x => F.good x.down⟩
    obtain ⟨D0⟩ := G0.exists_controlled N a c mode hc hN hbase hac
      (fun x y hxy => hF (fun h => hxy (ULift.ext x y h))) (fun x => hNF x.down)
    exact ⟨{
      referenceIndex := ULift.{v} φ
      referencePrimes := G0
      referenceArithmetic := D0
      completion := D
      fixedFactor_eq := fun K P hp => (hnon ⟨⟨(K,P),hp⟩⟩).elim
      cuspColumn_eq := fun K P hp => (hnon ⟨⟨(K,P),hp⟩⟩).elim
    }⟩
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0954

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.TupleFamily
Source SHA256: 874e201fb8863dfbf130d41d0aacd65998d3b842416aa9ed22fd0ed4ec17cb72
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0955



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def tupleRepresentative (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (P : Ideal Eis) : σ→Ideal Eis :=
  if h : ∃ p∈tuples, slotTupleProduct p=P then h.choose else hne.choose

omit [DecidableEq σ] in
lemma tupleRepresentative_mem (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (P : Ideal Eis) : tupleRepresentative tuples hne P∈tuples := by
  unfold tupleRepresentative
  split
  next h => exact h.choose_spec.1
  next h => exact hne.choose_spec

omit [DecidableEq σ] in
lemma tupleRepresentative_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (P : Ideal Eis) (hP : P∈tuples.image slotTupleProduct) :
    slotTupleProduct (tupleRepresentative tuples hne P)=P := by
  have h : ∃ p∈tuples, slotTupleProduct p=P := Finset.mem_image.mp hP
  simp only [tupleRepresentative,dite_eq_left h]
  exact h.choose_spec.2

omit [DecidableEq σ] in
lemma tupleRepresentative_at_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (p : σ→Ideal Eis) (hp : p∈tuples) :
    tupleRepresentative tuples hne (slotTupleProduct p)=p := by
  exact hinj (tupleRepresentative_mem tuples hne _) hp
    (tupleRepresentative_product tuples hne _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))

def tuplePrimeFamily (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i) (P : Ideal Eis) : PrimeFamily σ where
  ideal := tupleRepresentative tuples hne P
  maximal := hmax _ (tupleRepresentative_mem tuples hne P)
  good := hgood _ (tupleRepresentative_mem tuples hne P)

omit [DecidableEq σ] in
lemma tuplePrimeFamily_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i) (P : Ideal Eis)
    (hP : P∈tuples.image slotTupleProduct) :
    (∏ i, (tuplePrimeFamily tuples hne hmax hgood P).ideal i)=P :=
  tupleRepresentative_product tuples hne P hP

omit [DecidableEq σ] in
lemma tuplePrimeFamily_at_product (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (p : σ→Ideal Eis) (hp : p∈tuples) :
    (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p)).ideal=p :=
  tupleRepresentative_at_product tuples hne hinj p hp

lemma tuple_product_injective (L : σ→Finset (Ideal Eis))
    (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hp : ∀ i, ∀ P∈L i, Prime P) (tuples : Finset (σ→Ideal Eis))
    (hT : ∀ p∈tuples, ∀ i, p i∈L i) :
    Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)) :=
  (slotTupleProduct_injective_on L hL hp).mono hT

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0955

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.TupleSectors
Source SHA256: 9d0e54babc0d390bc779b9feb2cf0a7f4928cc43c88459d659ec5e3416982beb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0956



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ]

lemma tuplePrimeFamily_pairwise (L : σ→Finset (Ideal Eis))
    (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hT : ∀ p∈tuples, ∀ i, p i∈L i)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i) (P : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (tuplePrimeFamily tuples hne hmax hgood P).ideal) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  intro he
  have hp := tupleRepresentative_mem tuples hne P
  change tupleRepresentative tuples hne P i=tupleRepresentative tuples hne P j at he
  exact Finset.disjoint_left.mp (hL hij) (hT _ hp i) (he.symm ▸ hT _ hp j)

omit [Fintype φ] in
lemma tuplePrimeFamily_sum_pairwise (F : PrimeFamily φ)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (L : σ→Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hT : ∀ p∈tuples, ∀ i, p i∈L i)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i)
    (hfixed : ∀ p∈tuples, ∀ f i, p i≠F.ideal f) (P : Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (F.sum (tuplePrimeFamily tuples hne hmax hgood P)).ideal) := by
  intro i j hij
  cases i with
  | inl f => cases j with
    | inl g => exact hF (fun h => hij (congrArg Sum.inl h))
    | inr t =>
      apply Ideal.isCoprime_of_isMaximal
      exact (hfixed _ (tupleRepresentative_mem tuples hne P) f t).symm
  | inr t => cases j with
    | inl f =>
      apply Ideal.isCoprime_of_isMaximal
      exact hfixed _ (tupleRepresentative_mem tuples hne P) f t
    | inr u => exact tuplePrimeFamily_pairwise L hL tuples hne hT hmax hgood P (fun h => hij (congrArg Sum.inr h))

theorem exists_tuple_sector_arithmetic (F : PrimeFamily φ)
    (L : σ→Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hT : ∀ p∈tuples, ∀ i, p i∈L i)
    (hmax : ∀ p∈tuples, ∀ i, (p i).IsMaximal)
    (hgood : ∀ p∈tuples, ∀ i, λ₀∉p i)
    (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows, Admissible K)
    (N a c : Eis) (mode : Bool)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c≠0) (hN : (9:Eis)*c∣N)
    (hbase : if mode then λ₀^2∣a-1 else λ₀^2∣c-1) (hac : IsCoprime a c)
    (hF : Pairwise (Function.onFun IsCoprime F.ideal))
    (hNF : ∀ f, IsCoprime (Ideal.span {N}) (F.ideal f))
    (hrowcop : ∀ K∈rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K)
    (hfixed : ∀ p∈tuples, ∀ f i, p i≠F.ideal f)
    (hperiod : ∀ p∈tuples, ∀ i, IsCoprime (Ideal.span {N}) (p i))
    (rowClass slotClass : Eis⧸Ideal.span {N^2})
    (hrowClass : ∀ K∈rows, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=rowClass)
    (hslotClass : ∀ p∈tuples, Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator (slotTupleProduct p))=slotClass) :
    ∃ E : ∀ x : SourcePair rows (tuples.image slotTupleProduct),
      ControlledStratumArithmetic
        (F.reflected x.val.1.val (hrows x.val.1.val x.val.1.property)
          (tuplePrimeFamily tuples hne hmax hgood x.val.2.val)).generator N a c mode,
      ∀ x0 x, (E x).fixedFactor=(E x0).fixedFactor ∧
        ∀ u m n b, actualCuspColumn (E x) s hc u m n b=actualCuspColumn (E x0) s hc u m n b := by
  refine exists_fixed_ray_source_arithmetic F rows (tuples.image slotTupleProduct)
    (tuplePrimeFamily tuples hne hmax hgood) hrows
    (tuplePrimeFamily_product tuples hne hmax hgood) N a c mode s hc hN hbase hac hF hNF hrowcop ?_ ?_ rowClass slotClass hrowClass ?_
  · intro P hP
    exact tuplePrimeFamily_sum_pairwise F hF L hL tuples hne hT hmax hgood hfixed P
  · intro P hP i
    exact hperiod _ (tupleRepresentative_mem tuples hne P) i
  · intro P hP
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
    exact hslotClass p hp
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0956

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.WeightedEnergy
Source SHA256: 417d1b0d5e7de4e82d725097a7f162449a51dc3b6902aaebdc9304dd11f1ee48
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0957


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ ι : Type*} [Fintype φ] [Fintype ι] {N a c : Eis} {mode : Bool}

theorem bounded_column_hybrid_energy_extracted (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X Y B L : ℝ, 1 ≤ X → 1 ≤ L →
    ∀ (F : PrimeFamily φ), Pairwise (Function.onFun IsCoprime F.ideal) →
    ∀ (jF : φ → ℕ) (e : φ → Fin 3) (A : Ideal Eis → Ideal Eis → ℂ),
      (∀ n b, ‖A n b‖ ≤ 1) →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)) (aP : Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ P ∈ Pset, ‖aP P‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖hybridRow Pset nset bset aP
        (frozenBranchColumn F jF e A) K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := hybridRow_energy ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hL F hF jF e A hA rows nset bset Pset aP hrows hn hb hP ha
  let D1 := frozenExtracted F jF e 1
  let D2 := frozenExtracted F jF e 2
  let Yq := extractedDualScale D1 Y
  let Bq := extractedDualScale D2 B
  have hD1 : D1 ≠ 0 := frozenExtracted_ne_zero F jF e 1
  have hD2 : D2 ≠ 0 := frozenExtracted_ne_zero F jF e 2
  have hnq : ∀ n ∈ quotientSupport D1 nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Yq := by
    intro n hn'
    exact ⟨quotientSupport_cubic_admissible D1 hD1 nset (fun n h => (hn n h).1) n hn',
      (quotientSupport_norm_div D1 hD1 nset Y (fun n h => (hn n h).2) n hn').trans (le_max_right _ _)⟩
  have hbq : ∀ b ∈ quotientSupport D2 bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ Bq := by
    intro b hb'
    have hsource := hb (D2*b) ((mem_quotientSupport D2 b hD2 bset).mp hb')
    rw [primaryGenerator_mul] at hsource
    exact ⟨(mul_ne_zero_iff.mp hsource.1).2,
      (quotientSupport_norm_div D2 hD2 bset B (fun b h => (hb b h).2) b hb').trans (le_max_right _ _)⟩
  have hacoeff : ∀ P ∈ Pset, ‖aP P*extractedSlotFactor D1 D2 P‖ ≤ 1 := by
    intro P hP'
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha P hP')).trans (extractedSlotFactor_norm_le_one D1 D2 P)
  have hcolumn : ∀ n b, ‖extractedFrozenColumn F jF e A n b‖ ≤ 1 :=
    extractedFrozenColumn_norm_le_one F jF e A hA
  have hh := he X Yq Bq L hX (le_max_left _ _) (le_max_left _ _) hL rows
    (quotientSupport D1 nset) (quotientSupport D2 bset) Pset
    (fun P => aP P*extractedSlotFactor D1 D2 P)
    (extractedFrozenColumn F jF e A)
    hrows hnq hbq hP hacoeff (fun n _ b _ => hcolumn n b)
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    ((by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)) :
      (∑ K ∈ rows, (frozenBranchScale F jF e)^2*
        ‖hybridRow Pset (quotientSupport D1 nset) (quotientSupport D2 bset)
          (fun P => aP P*extractedSlotFactor D1 D2 P)
          (extractedFrozenColumn F jF e A) K‖^2) ≤ _)
  rw [hybridRow_frozen_extraction F hF jF e _ nset bset Pset
    (fun n h => (hn n h).1.2) (fun b h => (hb b h).1) aP K (hrows K hK).1
    (fun P h => (hP P h).1.2)]
  have hp := frozenBranchScale_pos F jF e
  have hs := extractedRowFactor_norm_le_one D1 D2 K
  have hs2 : ‖extractedRowFactor D1 D2 K‖^2 ≤ 1 := by
    have h0 := norm_nonneg (extractedRowFactor D1 D2 K)
    nlinarith
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,mul_pow]
  change (frozenBranchScale F jF e)^2*‖extractedRowFactor D1 D2 K‖^2* _ ≤ _
  calc
    _ ≤ ((frozenBranchScale F jF e)^2*1)*_ := by gcongr
    _ = _ := by rw [mul_one]

lemma actualCuspWeightedColumn_norm_le_one {ι : Type*} [Fintype ι]
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (u : Eisˣ) (m : ℕ) (w : Ideal Eis → Ideal Eis → ℂ)
    (hw : ∀ n b, ‖w n b‖ ≤ 1) (n b : Ideal Eis) :
    ‖actualCuspColumn D0 s hc u m n b*w n b‖ ≤ 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (actualCuspColumn_norm_le_one D0 s hc u m n b)).trans (hw n b)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0957

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ActualWeightedEnergy
Source SHA256: b2ea7ce16eb0200ce84c6d1c0f2adb341a5bae2155df4e76ba27d552fc747235
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0958


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

def weightedReflectedBranchHybridRow (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal Eis → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis → Ideal Eis → ℂ)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ)
    (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis) : ℂ :=
  ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF κ s u m*
    actualRowPhaseExtension F jF s u m K*r K)*
    hybridRow Pset nset bset (fun P => actualSlotPhase F (S P) jF s u m*aw P)
      (frozenBranchColumn F jF e (fun n b => A n b*w n b)) K

theorem actual_weighted_reflected_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      (∀ K ∈ rows, ‖r K‖ ≤ 1) → (∀ P ∈ Pset, ‖aw P‖ ≤ 1) → (∀ n b, ‖w n b‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K‖^2) ≤
      (frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))) := by
  obtain ⟨C,hC,he⟩ := bounded_column_hybrid_energy_extracted (φ := φ) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX _hY _hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S r aw w hrows hrowcop _hproducts hScop hSN hSchar hn hb hP hr haw hw
  have hfrozen : ‖actualFrozenPhase F jF D0.fixedFactor s u m‖ ≤ 1 :=
    actualFrozenPhase_norm_le_one F jF D0.fixedFactor (D0.fixedFactor_norm hN G0.generator_product_primary hbase).le
      s hc hN hbase hac hF hNF hcharF hj u m
  have hrow (K : Ideal Eis) (hK : K ∈ rows) : ‖actualRowPhaseExtension F jF s u m K‖ ≤ 1 := by
    rw [actualRowPhaseExtension,dite_eq_left (hrows K hK).1]
    exact actualRowPhase_norm_le_one F K (hrows K hK).1 jF s hc hN hbase hac hF
      (hrowcop K hK).1 hNF (hrowcop K hK).2 hcharF u m
  have hslot (P : Ideal Eis) (hP : P ∈ Pset) : ‖actualSlotPhase F (S P) jF s u m*aw P‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (two_block_phase_bounds F (S P) jF s hc hN hbase hac (hScop P hP) (hSN P hP) (hSchar P hP) u m).2).trans
      (haw P hP)
  have hcol := actualCuspWeightedColumn_norm_le_one G0 D0 s hc u m w hw
  apply le_trans (Finset.sum_le_sum (fun K hK => ?_))
    (he X Y B L hX hL F hF jF e (fun n b => actualCuspColumn D0 s hc u m n b*w n b) hcol
      rows nset bset Pset (fun P => actualSlotPhase F (S P) jF s u m*aw P) hrows hn hb hP hslot)
  have hphase : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K‖ ≤ 1 := by
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _) hfrozen).trans (hrow K hK))).trans (hr K hK)
  have hphase0 := norm_nonneg ((-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K)
  have hs : ‖(-1:ℂ)^(Fintype.card σ)*actualFrozenPhase F jF D0.fixedFactor s u m*
      actualRowPhaseExtension F jF s u m K*r K‖^2 ≤ 1 := by nlinarith
  rw [weightedReflectedBranchHybridRow,norm_mul,mul_pow]
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg _)).trans_eq (one_mul _)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0958

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.WeightedSourceSum
Source SHA256: 8a8effafa9862c77004892d06ff3f6e6c31b12d68ee9dddfdd90f5efb6259b14
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0959


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ ι : Type*} [Fintype φ] [Fintype σ] [Fintype ι]
variable {N a c : Eis} {mode : Bool}

def weightedPhysicalReflectedRow (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) : ℂ :=
  ∑ P : Pset, ∑ n ∈ nset, ∑ b ∈ bset,
    r K*aw P.val*w n b*(if h : IsCoprime K P.val then
      actualMixedCoefficient F K hK (S P.val) jF (D P h) s hc u m n b else 0)

theorem weightedPhysicalReflectedRow_eq_branches (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : Ideal Eis → PrimeFamily σ) (jF : φ → ℕ) (Pset nset bset : Finset (Ideal Eis))
    (hprod : ∀ P ∈ Pset, (∏ i, (S P).ideal i)=P)
    (D : ∀ P : Pset, IsCoprime K P.val →
      ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
    (hcop : ∀ P : Pset, IsCoprime K P.val →
      Pairwise (Function.onFun IsCoprime (F.reflected K hK (S P.val)).ideal))
    (G0 : PrimeFamily ι) (D0 : ControlledStratumArithmetic G0.generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hκ : ∀ P h, (D P h).fixedFactor = D0.fixedFactor)
    (hA : ∀ P h u m n b, actualCuspColumn (D P h) s hc u m n b = actualCuspColumn D0 s hc u m n b)
    (hb : ∀ b ∈ bset, primaryGenerator b ≠ 0)
    (r aw : Ideal Eis → ℂ) (w : Ideal Eis → Ideal Eis → ℂ) (u : Eisˣ) (m : ℕ) :
    weightedPhysicalReflectedRow F K hK S jF Pset nset bset D s hc r aw w u m =
      ∑ e : φ → Fin 3, weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K := by
  unfold weightedPhysicalReflectedRow
  have he (P : Pset) (n : Ideal Eis) (b : Ideal Eis) (hb' : b ∈ bset) :=
    masked_actual_coefficient F K hK (S P.val) P.val (hprod P.val P.property) jF
      (D P) (hcop P) G0 D0 s hc (hκ P) (hA P) u m n b (hb b hb')
  simp_rw [weightedReflectedBranchHybridRow,hybridRow,hybridInner,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort Pset]
  apply Finset.sum_congr rfl
  intro P hP
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb'
  rw [he P n b hb',Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he'
  unfold frozenBranchColumn
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0959

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.WeightedMeasurable
Source SHA256: 1545cd8bb6074c2a89164d78e52dcabc8f94c77deb8c597035730ac96009f8c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0960



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

lemma weightedReflectedBranchHybridRow_aestronglyMeasurable
    (μ : Measure Ω) (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
    (S : Ideal Eis → PrimeFamily σ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (κ : ℂ) (A : Ideal Eis → Ideal Eis → ℂ)
    (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ)
    (u : Eisˣ) (m : ℕ) (Pset nset bset : Finset (Ideal Eis)) (K : Ideal Eis)
    (hr : AEStronglyMeasurable (fun t => r t K) μ)
    (ha : ∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ)
    (hw : ∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) :
    AEStronglyMeasurable (fun t => weightedReflectedBranchHybridRow F jF e S s κ A
      (r t) (aw t) (w t) u m Pset nset bset K) μ := by
  unfold weightedReflectedBranchHybridRow
  apply (hr.const_mul _).mul
  unfold hybridRow
  apply Finset.aestronglyMeasurable_fun_sum
  intro P hP
  simp only [div_eq_mul_inv]
  apply (((ha P hP).const_mul _).mul_const _ |>.mul_const _).mul
  unfold hybridInner
  apply Finset.aestronglyMeasurable_fun_sum
  intro n hn
  apply Finset.aestronglyMeasurable_fun_sum
  intro b hb
  unfold frozenBranchColumn
  exact (((((hw n hn b hb).const_mul _).mul_const _).mul_const _).mul_const _).mul_const _

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0960

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CommonMeasure
Source SHA256: 7f00c590a7d9bc54a12fe747d9a89f8146cad289d12df5b6686004ac14942795
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0961


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

theorem integrated_actual_reflected_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
      let Bq := extractedDualScale (frozenExtracted F jF e 2) B
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K ∂μ‖^2) ≤
      ‖scalar‖^2*((frozenBranchScale F jF e)^2*
        (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ))))*(∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := actual_weighted_reflected_branch_energy (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  let Yq := extractedDualScale (frozenExtracted F jF e 1) Y
  let Bq := extractedDualScale (frozenExtracted F jF e 2) B
  let E : ℝ := (frozenBranchScale F jF e)^2*
    (C*(X*Yq*Bq*L)^ε*(X+Yq*Bq)*Bq*(Yq+L+(Yq*L)^(2/3:ℝ)))
  have hYq : 1 ≤ Yq := le_max_left _ _
  have hBq : 1 ≤ Bq := le_max_left _ _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  let ψ : rows → Ω → ℂ := fun K t => weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
    (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val
  have hbound (t : Ω) : (∑ K, ‖ψ K t‖^2) ≤ E := by
    change (∑ K : rows, ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K.val‖^2) ≤ E
    rw [Finset.sum_coe_sort rows (fun K : Ideal Eis => ‖weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K‖^2)]
    exact he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
      G0 D0 u m rows nset bset Pset S (r t) (aw t) (w t)
      hrows hrowcop hproducts hScop hSN hSchar hn hb hP (hr t) (haw t) (hw t)
  have hψM (K : rows) : AEStronglyMeasurable (ψ K) μ :=
    weightedReflectedBranchHybridRow_aestronglyMeasurable μ F jF e S s D0.fixedFactor
      (actualCuspColumn D0 s hc u m) r aw w u m Pset nset bset K.val
      (hrM K.val K.property) hawM hwM
  have hpoint (K : rows) (t : Ω) : ‖ψ K t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖ψ j t‖) (Finset.mem_univ K)).trans (hbound t)
  have hint (K : rows) : Integrable (fun t => density t*ψ K t) μ :=
    hdensity.mul_bdd (hψM K) (Filter.Eventually.of_forall (hpoint K))
  have hh := mul_le_mul_of_nonneg_left
    (common_measure_energy μ density ψ E hE hdensity.norm hint hbound) (sq_nonneg ‖scalar‖)
  have hsum : (∑ K : rows, ‖∫ t, density t*ψ K t ∂μ‖^2) =
      ∑ K ∈ rows, ‖∫ t, density t*weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K ∂μ‖^2 :=
    Finset.sum_coe_sort rows (fun K : Ideal Eis =>
      ‖∫ t, density t*weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K ∂μ‖^2)
  rw [hsum] at hh
  simp only [norm_mul,mul_pow,← Finset.mul_sum]
  simpa only [E,Yq,Bq,mul_assoc] using hh

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0961

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.ReflectedNormalization
Source SHA256: 5c4190a479edbb701a423948de5ad0b0b290cb7e3c8fdf4486c37dd430aefef2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0962




namespace OAI

namespace SevenEighths.InverseReflectedNormalization
open InverseTerminalWidths
noncomputable section

def outsideScalar (Z v ell el S₀ B₀ Td : ℝ) : ℝ :=
  Z ^ (-v/2-ell-el/3-(S₀+B₀)/2) *
    InverseKernelSourceUniform.smallScalar (Z ^ (v+3*ell+el-Td))

theorem smallScalar_rpow {Z : ℝ} (hZ : 1 ≤ Z) (d : ℝ) :
    InverseKernelSourceUniform.smallScalar (Z ^ (-d)) = Z ^ (-max 0 d/4) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  unfold InverseKernelSourceUniform.smallScalar
  rw [← Real.rpow_mul hZ0.le]
  by_cases hd : 0 ≤ d
  · rw [max_eq_right hd, min_eq_right]
    · congr 1; ring
    · calc
        Z ^ (-d * (1/4:ℝ)) ≤ Z ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
        _ = 1 := Real.rpow_zero _
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [max_eq_left hd', neg_zero, zero_div, Real.rpow_zero, min_eq_left]
    calc
      1 = Z ^ (0:ℝ) := (Real.rpow_zero _).symm
      _ ≤ Z ^ (-d*(1/4:ℝ)) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem outsideScalar_square {Z : ℝ} (hZ : 1 ≤ Z) (v ell el S₀ B₀ Td : ℝ) :
    outsideScalar Z v ell el S₀ B₀ Td ^ 2 =
      Z ^ (-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  unfold outsideScalar
  rw [show v+3*ell+el-Td = -(Td-v-3*ell-el) by ring, smallScalar_rpow hZ,
    ← Real.rpow_add hZ0, ← Real.rpow_mul_natCast hZ0.le]
  congr 1
  ring

theorem row_shape {Z : ℝ} (hZ : 1 ≤ Z) (H v ell : ℝ) :
    Z^H + Z^v*Z^ell ≤ 2*Z^(max H (v+ell)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  rw [← Real.rpow_add hZ0]
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ (le_max_left H (v+ell))
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ (le_max_right H (v+ell))
  linarith

theorem cubic_shape {Z : ℝ} (hZ : 1 ≤ Z) (v za : ℝ) :
    Z^v + Z^za + (Z^v*Z^za)^(2/3:ℝ) ≤ 3*Z^(v+za-hybridSaving v za) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hv : hybridSaving v za ≤ v := min_le_left _ _
  have hz : hybridSaving v za ≤ za := (min_le_right _ _).trans (min_le_left _ _)
  have ht : hybridSaving v za ≤ (v+za)/3 := (min_le_right _ _).trans (min_le_right _ _)
  rw [← Real.rpow_add hZ0, ← Real.rpow_mul hZ0.le]
  have h1 := Real.rpow_le_rpow_of_exponent_le hZ (show v ≤ v+za-hybridSaving v za by linarith)
  have h2 := Real.rpow_le_rpow_of_exponent_le hZ (show za ≤ v+za-hybridSaving v za by linarith)
  have h3 := Real.rpow_le_rpow_of_exponent_le hZ (show (v+za)*(2/3:ℝ) ≤ v+za-hybridSaving v za by linarith)
  linarith

theorem reflected_exponent_identity (H v ell el S₀ B₀ Td za ε : ℝ) :
    (-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) +
      (H+v+ell+za)*ε + max H (v+ell) + ell + (v+za-hybridSaving v za) =
    reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za) := by
  unfold reflectedExponent
  ring

theorem normalized_hybrid_shape {Z : ℝ} (hZ : 1 ≤ Z)
    (H v ell el S₀ B₀ Td za ε : ℝ) :
    (outsideScalar Z v ell el S₀ B₀ Td)^2 *
      ((Z^H*Z^v*Z^ell*Z^za)^ε * (Z^H+Z^v*Z^ell)*Z^ell*
        (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ))) ≤
      6*Z^(reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hp : (Z^H*Z^v*Z^ell*Z^za)^ε = Z^((H+v+ell+za)*ε) := by
    rw [← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0,
      ← Real.rpow_mul hZ0.le]
  have hb := mul_le_mul (row_shape hZ H v ell) (cubic_shape hZ v za)
    (by positivity : 0 ≤ Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ)) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (outsideScalar Z v ell el S₀ B₀ Td)^2 *
      (Z^H*Z^v*Z^ell*Z^za)^ε * Z^ell by positivity)
  calc
    _ ≤ (outsideScalar Z v ell el S₀ B₀ Td)^2 *
        (Z^H*Z^v*Z^ell*Z^za)^ε * Z^ell *
        ((2*Z^(max H (v+ell)))*(3*Z^(v+za-hybridSaving v za))) := by
      nlinarith only [hh]
    _ = 6*Z^(reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) := by
      rw [outsideScalar_square hZ,hp]
      calc
        _ = 6*(Z^(-v-2*ell-2*el/3-S₀-B₀-max 0 (Td-v-3*ell-el)/2) *
          Z^((H+v+ell+za)*ε) * Z^(max H (v+ell)) * Z^ell *
          Z^(v+za-hybridSaving v za)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0,
            ← Real.rpow_add hZ0,reflected_exponent_identity]

end
end SevenEighths.InverseReflectedNormalization

end OAI
end OAIOriginalModule0962

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.NormalizedEnergy
Source SHA256: 6bd4c3338098c66ac6e2a5fe6850838d5e9bc42b12c32cfe9e202b25cc3704cd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0963


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open InverseReflectedNormalization InverseTerminalWidths MeasureTheory ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {Ω φ σ : Type*} [MeasurableSpace Ω] [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}

theorem normalized_actual_reflected_branch_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z H v ell el S₀ B₀ Td za : ℝ), 1 ≤ Z →
    ∀ (X Y B L : ℝ), 1 ≤ X → 1 ≤ Y → 1 ≤ B → 1 ≤ L →
    ∀ (F : PrimeFamily φ) (jF : φ → ℕ) (e : φ → Fin 3)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
      (hc : c ≠ 0), (9:Eis)*c ∣ N →
      (if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1) → IsCoprime a c →
      Pairwise (Function.onFun IsCoprime F.ideal) →
      (∀ f, IsCoprime (Ideal.span {N}) (F.ideal f)) →
      (∀ f, ringChar (Eis ⧸ F.ideal f) ≠ 2) → (∀ f, jF f < 6) →
    ∀ {ι : Type*} [Fintype ι] (G0 : PrimeFamily ι)
      (D0 : ControlledStratumArithmetic G0.generator N a c mode)
      (u : Eisˣ) (m : ℕ) (rows nset bset Pset : Finset (Ideal Eis))
      (S : Ideal Eis → PrimeFamily σ)
      (μ : Measure Ω) (density : Ω → ℂ) (scalar : ℂ)
      (r aw : Ω → Ideal Eis → ℂ) (w : Ω → Ideal Eis → Ideal Eis → ℂ),
      (∀ K ∈ rows, Admissible K ∧ (Ideal.absNorm K:ℝ) ≤ X) →
      (∀ K ∈ rows, (∀ f, IsCoprime (F.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) →
      (∀ P ∈ Pset, (∏ i, (S P).ideal i) = P) →
      (∀ P ∈ Pset, Pairwise (Function.onFun IsCoprime (F.sum (S P)).ideal)) →
      (∀ P ∈ Pset, ∀ i, IsCoprime (Ideal.span {N}) ((F.sum (S P)).ideal i)) →
      (∀ P ∈ Pset, ∀ i, ringChar (Eis ⧸ (F.sum (S P)).ideal i) ≠ 2) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n:ℝ) ≤ Y) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b:ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ) ≤ 2*L) →
      Integrable density μ →
      (∀ K ∈ rows, AEStronglyMeasurable (fun t => r t K) μ) →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => aw t P) μ) →
      (∀ n ∈ nset, ∀ b ∈ bset, AEStronglyMeasurable (fun t => w t n b) μ) →
      (∀ t, ∀ K ∈ rows, ‖r t K‖ ≤ 1) → (∀ t, ∀ P ∈ Pset, ‖aw t P‖ ≤ 1) →
      (∀ t n b, ‖w t n b‖ ≤ 1) →
      X = Z^H → extractedDualScale (frozenExtracted F jF e 1) Y = Z^v →
      extractedDualScale (frozenExtracted F jF e 2) B = Z^ell → L = Z^za →
      ‖scalar‖*frozenBranchScale F jF e = outsideScalar Z v ell el S₀ B₀ Td →
      (∑ K ∈ rows, ‖scalar * ∫ t, density t * weightedReflectedBranchHybridRow F jF e S s D0.fixedFactor
        (actualCuspColumn D0 s hc u m) (r t) (aw t) (w t) u m Pset nset bset K ∂μ‖^2) ≤
      (6*C)*Z^(InverseTerminalWidths.reflectedExponent 0 H S₀ B₀ za v ell el Td + ε*(H+v+ell+za)) *
        (∫ t, ‖density t‖ ∂μ)^2 := by
  obtain ⟨C,hC,he⟩ := integrated_actual_reflected_branch_energy (Ω := Ω) (φ := φ) (σ := σ)
    (N := N) (a := a) (c := c) (mode := mode) ε hε
  refine ⟨C,hC,?_⟩
  intro Z H v ell el S₀ B₀ Td za hZ X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    ι _ G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
    hscaleX hscaleY hscaleB hscaleL hscalar
  have hh := he X Y B L hX hY hB hL F jF e s hc hN hbase hac hF hNF hcharF hj
    G0 D0 u m rows nset bset Pset S μ density scalar r aw w
    hrows hrowcop hproducts hScop hSN hSchar hn hb hP hdensity hrM hawM hwM hr haw hw
  dsimp only at hh
  rw [hscaleX,hscaleY,hscaleB,hscaleL] at hh
  have hs : ‖scalar‖^2*(frozenBranchScale F jF e)^2 =
      outsideScalar Z v ell el S₀ B₀ Td ^2 := by rw [← mul_pow,hscalar]
  have heq : ‖scalar‖^2*((frozenBranchScale F jF e)^2*
      (C*(Z^H*Z^v*Z^ell*Z^za)^ε*(Z^H+Z^v*Z^ell)*Z^ell*
        (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ)))) =
      C*((outsideScalar Z v ell el S₀ B₀ Td)^2 *
        ((Z^H*Z^v*Z^ell*Z^za)^ε*(Z^H+Z^v*Z^ell)*Z^ell*
          (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ)))) := by
    calc
      _ = (‖scalar‖^2*(frozenBranchScale F jF e)^2)*
        (C*(Z^H*Z^v*Z^ell*Z^za)^ε*(Z^H+Z^v*Z^ell)*Z^ell*
          (Z^v+Z^za+(Z^v*Z^za)^(2/3:ℝ))) := by ring
      _ = _ := by rw [hs]; ring
  rw [heq] at hh
  apply hh.trans
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (normalized_hybrid_shape hZ H v ell el S₀ B₀ Td za ε) hC.le)
    (sq_nonneg (∫ t, ‖density t‖ ∂μ))
  convert hbnd using 1 ; ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0963

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Denominator
Source SHA256: 18ee2369599f649f5a0010a00b5048ef3a54f2bff497d40710035099a81f9444
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0964


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

lemma sqrt_extraction_identity (A B C r U V : ℝ)
    (hA : 0<A) (hB : 0<B) (hC : 0<C) (hr : 0<r) (hU : 0<U) (hV : 0<V) :
    (Real.sqrt A*Real.sqrt B/Real.sqrt C) /
      (r*Real.sqrt (A*U)*(B*V)) =
      1/(r*Real.sqrt U*V*Real.sqrt (C*B)) := by
  rw [Real.sqrt_mul hA.le,Real.sqrt_mul hC.le]
  have hsa := (Real.sqrt_pos.mpr hA).ne'
  have hsb := (Real.sqrt_pos.mpr hB).ne'
  have hsc := (Real.sqrt_pos.mpr hC).ne'
  have hsu := (Real.sqrt_pos.mpr hU).ne'
  field_simp
  nlinarith [Real.sq_sqrt hB.le]

def extractedOutsideScalar (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r U B R : ℝ) : ℝ :=
  smallScalar R / (r*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
    ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B))

theorem extractedOutsideScalar_scale (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r U B R : ℝ) (hr : 0<r) (hU : 0<U) (hB : 0<B) :
    extractedOutsideScalar F jF e r U B R * frozenBranchScale F jF e =
      smallScalar R / (r*Real.sqrt U*B*
        Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 0):ℝ)*
          (Ideal.absNorm (frozenExtracted F jF e 2):ℝ))) := by
  have hn (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  unfold extractedOutsideScalar frozenBranchScale
  have hh := sqrt_extraction_identity _ _ _ r U B (hn 1) (hn 2) (hn 0) hr hU hB
  calc
    _ = smallScalar R * ((Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (frozenExtracted F jF e 0):ℝ))/
      (r*Real.sqrt ((Ideal.absNorm (frozenExtracted F jF e 1):ℝ)*U)*
        ((Ideal.absNorm (frozenExtracted F jF e 2):ℝ)*B))) := by ring
    _ = _ := by rw [hh]; ring

lemma power_normalizer {Z : ℝ} (hZ : 1≤Z) (v ell el S₀ B₀ Td : ℝ) :
    smallScalar (Z^(v+3*ell+el-Td)) /
      (Z^(el/3)*Real.sqrt (Z^v)*Z^ell*Real.sqrt (Z^S₀*Z^B₀)) =
      outsideScalar Z v ell el S₀ B₀ Td := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,← Real.rpow_add hZ0,
    ← Real.rpow_mul hZ0.le,← Real.rpow_mul hZ0.le,
    ← Real.rpow_add hZ0,← Real.rpow_add hZ0,← Real.rpow_add hZ0]
  unfold outsideScalar
  rw [div_eq_mul_inv,← Real.rpow_neg hZ0.le]
  have he : -(el/3+v*(1/2:ℝ)+ell+(S₀+B₀)*(1/2:ℝ)) =
      -v/2-ell-el/3-(S₀+B₀)/2 := by ring
  rw [he,mul_comm]

theorem extractedOutsideScalar_log_widths (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (Z r U B R : ℝ) (hZ : 1<Z) (hr : 0<r) (hU : 0<U) (hB : 0<B) (hR : 0<R) :
    extractedOutsideScalar F jF e r U B R * frozenBranchScale F jF e =
      outsideScalar Z (Real.logb Z U) (Real.logb Z B) (3*Real.logb Z r)
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
        (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
        (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) := by
  have hz0 : 0<Z := lt_trans zero_lt_one hZ
  have hn (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  rw [extractedOutsideScalar_scale F jF e r U B R hr hU hB]
  symm
  rw [← power_normalizer hZ.le]
  unfold InverseTerminalWidths.normWidth
  rw [show 3*Real.logb Z r/3=Real.logb Z r by ring,
    show Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-
      (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R)=Real.logb Z R by ring]
  rw [Real.rpow_logb hz0 (ne_of_gt hZ) hr,Real.rpow_logb hz0 (ne_of_gt hZ) hU,
    Real.rpow_logb hz0 (ne_of_gt hZ) hB,Real.rpow_logb hz0 (ne_of_gt hZ) hR,
    Real.rpow_logb hz0 (ne_of_gt hZ) (hn 0),Real.rpow_logb hz0 (ne_of_gt hZ) (hn 2)]

lemma extractedOutsideScalar_pos (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (r U B R : ℝ) (hr : 0<r) (hU : 0<U) (hB : 0<B) (hR : 0<R) :
    0 < extractedOutsideScalar F jF e r U B R := by
  have hn (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  exact div_pos (smallScalar_pos hR)
    (mul_pos (mul_pos hr (Real.sqrt_pos.mpr (mul_pos (hn 1) hU))) (mul_pos (hn 2) hB))

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0964

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.KernelGeometry
Source SHA256: 8d494a6aef9bce07d9838cda09d7050f97efbbcd7a75b90580655e22562ce00d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0965



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma PrimeFamily.product_span {ι : Type*} [Fintype ι] (G : PrimeFamily ι) :
    Ideal.span {∏ i, G.generator i} = ∏ i, G.ideal i := by
  have hf (T : Finset ι) : Ideal.span {∏ i ∈ T, G.generator i} = ∏ i ∈ T, G.ideal i := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi,Finset.prod_insert hi,← Ideal.span_singleton_mul_span_singleton,
        G.generator_span,ih]
  exact hf Finset.univ

lemma reflected_conductor_norm {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (c : Eis) :
    (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ) =
      (Ideal.absNorm (Ideal.span {c}*(∏ i, F.ideal i)):ℝ)*
        (Ideal.absNorm K:ℝ)*(Ideal.absNorm (∏ i, S.ideal i):ℝ) := by
  rw [← Ideal.span_singleton_mul_span_singleton,PrimeFamily.product_span,F.reflected_product]
  simp only [map_mul,Nat.cast_mul]
  ring

def kernelSlope : Fin 4 → ℝ := ![-2,-2,1,3]
def kernelLogCoordinates (QK QP Qn Qb k p n b : ℝ) : Fin 4 → ℝ :=
  ![Real.log (k/QK),Real.log (p/QP),Real.log (n/Qn),Real.log (b/Qb)]
def kernelCenter (C QK QP Qn Qb : ℝ) : ℝ := C*Qn*Qb^3/(QK^2*QP^2)

lemma kernelLogCoordinates_exp (QK QP Qn Qb k p n b : ℝ)
    (hQK : 0<QK) (hQP : 0<QP) (hQn : 0<Qn) (hQb : 0<Qb)
    (hk : 0<k) (hp : 0<p) (hn : 0<n) (hb : 0<b) :
    Real.exp (∑ i, kernelSlope i * kernelLogCoordinates QK QP Qn Qb k p n b i) =
      (n/Qn)*(b/Qb)^3/((k/QK)^2*(p/QP)^2) := by
  simp only [kernelSlope,kernelLogCoordinates,Fin.sum_univ_succ,Fin.isValue,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero,one_mul]
  rw [show -2*Real.log (k/QK)+(-2*Real.log (p/QP)+(Real.log (n/Qn)+3*Real.log (b/Qb))) =
    -(2*Real.log (k/QK)) + -(2*Real.log (p/QP)) + Real.log (n/Qn) + 3*Real.log (b/Qb) by ring]
  simp only [Real.exp_add,Real.exp_neg]
  rw [show (2:ℝ)=((2:ℕ):ℝ) by norm_num,show (3:ℝ)=((3:ℕ):ℝ) by norm_num,
    Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_nat_mul,
    Real.exp_log (div_pos hk hQK),Real.exp_log (div_pos hp hQP),
    Real.exp_log (div_pos hn hQn),Real.exp_log (div_pos hb hQb)]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem actual_annular_kernel_identity (C QK QP Qn Qb k p n b : ℝ)
    (hQK : 0<QK) (hQP : 0<QP) (hQn : 0<Qn) (hQb : 0<Qb)
    (hk : 0<k) (hp : 0<p) (hn : 0<n) (hb : 0<b) :
    C*n*b^3/(k^2*p^2) = kernelCenter C QK QP Qn Qb *
      Real.exp (∑ i, kernelSlope i * kernelLogCoordinates QK QP Qn Qb k p n b i) := by
  rw [kernelLogCoordinates_exp _ _ _ _ _ _ _ _ hQK hQP hQn hQb hk hp hn hb]
  unfold kernelCenter
  field_simp

def fixedKernelCoefficient (X tau r : ℝ) (C D1 D2 : Ideal Eis) : ℝ :=
  X/(27*tau^2*(Ideal.absNorm C:ℝ)^2)*r^3*
    (Ideal.absNorm D1:ℝ)*(Ideal.absNorm D2:ℝ)^3

lemma source_kernel_argument_factor {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (c : Eis) (X tau r : ℝ) (D1 D2 n b : Ideal Eis) :
    (X/(27*tau^2*(Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      r^3*(Ideal.absNorm (D1*n):ℝ)*(Ideal.absNorm (D2*b):ℝ)^3 =
    fixedKernelCoefficient X tau r (Ideal.span {c}*(∏ i, F.ideal i)) D1 D2 *
      (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 /
      ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2) := by
  rw [reflected_conductor_norm]
  simp only [fixedKernelCoefficient,map_mul,Nat.cast_mul,mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring

theorem source_kernel_argument_annuli {φ σ : Type*} [Fintype φ] [Fintype σ]
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ)
    (c : Eis) (X tau r : ℝ) (D1 D2 n b : Ideal Eis)
    (hn : n≠0) (hb : b≠0) (QK QP Qn Qb : ℝ)
    (hQK : 0<QK) (hQP : 0<QP) (hQn : 0<Qn) (hQb : 0<Qb) :
    (X/(27*tau^2*(Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      r^3*(Ideal.absNorm (D1*n):ℝ)*(Ideal.absNorm (D2*b):ℝ)^3 =
    kernelCenter (fixedKernelCoefficient X tau r (Ideal.span {c}*(∏ i, F.ideal i)) D1 D2)
      QK QP Qn Qb * Real.exp (∑ i, kernelSlope i *
        kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
          (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i) := by
  rw [source_kernel_argument_factor]
  have hn0 (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply actual_annular_kernel_identity _ _ _ _ _ _ _ _ _ hQK hQP hQn hQb
    (hn0 K hK.1) _ (hn0 n hn) (hn0 b hb)
  apply hn0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (S.ideal i))

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0965

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.KernelSeparation
Source SHA256: fe8ed3d4e305b689c8bcde896d3ee57c85a68ccb04b8bc767758ae69f6e7d4a0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0966



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section

def kernelCoordinateWeight (w : ℝ→ℂ) (slope Q t q : ℝ) : ℂ :=
  w (Real.log (q/Q))*logPhase t (slope*Real.log (q/Q))

def kernelDualWeight (windows : Fin 4→ℝ→ℂ) (Qn Qb t n b : ℝ) : ℂ :=
  kernelCoordinateWeight (windows 2) 1 Qn t n * kernelCoordinateWeight (windows 3) 3 Qb t b

lemma kernelCoordinateWeight_norm (w : ℝ→ℂ) (slope Q t q : ℝ) :
    ‖kernelCoordinateWeight w slope Q t q‖ = ‖w (Real.log (q/Q))‖ := by
  simp only [kernelCoordinateWeight,norm_mul,logPhase_norm,mul_one]

lemma kernelDualWeight_norm_le_one (windows : Fin 4→ℝ→ℂ)
    (hw : ∀ i y, ‖windows i y‖≤1) (Qn Qb t n b : ℝ) :
    ‖kernelDualWeight windows Qn Qb t n b‖≤1 := by
  rw [kernelDualWeight,norm_mul,kernelCoordinateWeight_norm,kernelCoordinateWeight_norm]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ _)).trans (hw _ _)

lemma kernelCoordinateWeight_continuous (w : ℝ→ℂ) (slope Q q : ℝ) :
    Continuous (fun t => kernelCoordinateWeight w slope Q t q) :=
  (logPhase_continuous_left _).const_mul _

lemma kernel_mode_separation (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb k p n b t : ℝ) :
    (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i) *
      logPhase t (kernelSlope i*kernelLogCoordinates QK QP Qn Qb k p n b i)) =
    kernelCoordinateWeight (windows 0) (-2) QK t k *
      kernelCoordinateWeight (windows 1) (-2) QP t p * kernelDualWeight windows Qn Qb t n b := by
  simp only [kernelCoordinateWeight,kernelDualWeight,kernelSlope,kernelLogCoordinates,
    Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  norm_num
  ring

theorem reflected_kernel_uniform_separation (a b : ℝ) (ha : 0<a)
    (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) (hM : ∀ i, 0≤M i)
    (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧
      HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ C QK QP Qn Qb : ℝ, 0<C → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter C QK QP Qn Qb
      (∀ k p n q : ℝ, 0<k → 0<p → 0<n → 0<q →
        (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n q i)) *
          CubicReflectionKernel.paperKernel (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
            (C*n*q^3/(k^2*p^2)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (kernelCoordinateWeight (windows 0) (-2) QK t k *
            kernelCoordinateWeight (windows 1) (-2) QP t p *
            kernelDualWeight windows Qn Qb t n q) * twistedDensity U W θ R t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := normTwistedSource_uniform_separation
    a b ha windows kernelSlope M hM hwindows W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro θ C QK QP Qn Qb hC hQK hQP hQn hQb
  have hR : 0<kernelCenter C QK QP Qn Qb := by unfold kernelCenter; positivity
  obtain ⟨he,hi,hm,hp⟩ := hsep θ _ hR
  refine ⟨?_,hi,hm,hp⟩
  intro k p n q hk hp hn hq
  rw [actual_annular_kernel_identity C QK QP Qn Qb k p n q hQK hQP hQn hQb hk hp hn hq]
  rw [he]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [kernel_mode_separation])

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0966

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.KernelWeights
Source SHA256: 01aa099f8a8cbbc8c6beffbfeaea0708f47c61cf069d6751b27a401a467737af
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0967


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section

def reciprocalWindow (w : ℝ→ℂ) (α M : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (-α*M):ℂ)*(w y*(Real.exp (-α*y):ℂ))

lemma reciprocalWindow_norm_le_one (w : ℝ→ℂ) (α M : ℝ) (hα : 0≤α)
    (hw : ∀ y, ‖w y‖≤1) (hs : ∀ y, w y≠0 → -M≤y) (y : ℝ) :
    ‖reciprocalWindow w α M y‖≤1 := by
  by_cases hy : w y=0
  · simp [reciprocalWindow,hy]
  · have he : Real.exp (-α*M)*Real.exp (-α*y) ≤ 1 := by
      rw [← Real.exp_add,← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hα (show 0≤M+y by linarith [hs y hy])]
    simp only [reciprocalWindow,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-α*M)*(1*Real.exp (-α*y)) := by gcongr; exact hw y
      _ ≤ 1 := by simpa only [one_mul] using he

lemma reciprocalWindow_support (w : ℝ→ℂ) (α M y : ℝ) :
    reciprocalWindow w α M y≠0 → w y≠0 := by
  intro h hw
  apply h
  simp [reciprocalWindow,hw]

lemma reciprocalWindow_reconstruct (w : ℝ→ℂ) (α M y : ℝ) :
    w y*(Real.exp (-α*y):ℂ) =
      (Real.exp (α*M):ℂ)*reciprocalWindow w α M y := by
  unfold reciprocalWindow
  rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add]
  simp

lemma reciprocal_norm_log (Q q : ℝ) (hQ : 0<Q) (hq : 0<q) :
    Real.exp (-(1/2:ℝ)*Real.log (q/Q)) = Real.sqrt Q/Real.sqrt q := by
  rw [show -(1/2:ℝ)*Real.log (q/Q) = Real.log (q/Q)*(-(1/2:ℝ)) by ring,
    ← Real.rpow_def_of_pos (div_pos hq hQ),Real.div_rpow hq.le hQ.le,
    Real.rpow_neg hq.le,Real.rpow_neg hQ.le,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow]
  field_simp

lemma reciprocal_cube_log (Q q : ℝ) (hQ : 0<Q) (hq : 0<q) :
    Real.exp (-Real.log (q/Q)) = Q/q := by
  rw [Real.exp_neg,Real.exp_log (div_pos hq hQ),inv_div]

def reciprocalKernelWindows (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ) : Fin 4→ℝ→ℂ :=
  ![windows 0,windows 1,reciprocalWindow (windows 2) (1/2) (M 2),
    reciprocalWindow (windows 3) 1 (M 3)]

lemma reciprocalKernelWindows_norm (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hw : ∀ i y, ‖windows i y‖≤1)
    (hs : ∀ i y, windows i y≠0 → |y|≤M i) :
    ∀ i y, ‖reciprocalKernelWindows windows M i y‖≤1 := by
  intro i y
  fin_cases i
  · exact hw 0 y
  · exact hw 1 y
  · exact reciprocalWindow_norm_le_one _ _ _ (by norm_num) (hw 2)
      (fun y hy => (abs_le.mp (hs 2 y hy)).1) y
  · exact reciprocalWindow_norm_le_one _ _ _ (by norm_num) (hw 3)
      (fun y hy => (abs_le.mp (hs 3 y hy)).1) y

lemma reciprocalKernelWindows_support (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hs : ∀ i y, windows i y≠0 → |y|≤M i) :
    ∀ i y, reciprocalKernelWindows windows M i y≠0 → |y|≤M i := by
  intro i y hy
  fin_cases i
  · exact hs 0 y hy
  · exact hs 1 y hy
  · exact hs 2 y (reciprocalWindow_support _ _ _ _ hy)
  · exact hs 3 y (reciprocalWindow_support _ _ _ _ hy)

lemma reciprocal_window_product (windows : Fin 4→ℝ→ℂ) (M y : Fin 4→ℝ) :
    (∏ i, windows i (y i)) *
      ((Real.exp (-(1/2:ℝ)*y 2):ℂ)*(Real.exp (-y 3):ℂ)) =
    (Real.exp (M 2/2+M 3):ℂ)*(∏ i, reciprocalKernelWindows windows M i (y i)) := by
  have h2 := reciprocalWindow_reconstruct (windows 2) (1/2) (M 2) (y 2)
  have h3 := reciprocalWindow_reconstruct (windows 3) 1 (M 3) (y 3)
  have hp : (Real.exp (M 2/2+M 3):ℂ) =
      (Real.exp ((1/2:ℝ)*M 2):ℂ)*(Real.exp (1*M 3):ℂ) := by
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  rw [hp]
  simp only [reciprocalKernelWindows,Fin.prod_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  simp only [Fin.succ,Fin.val_mk]
  simp only [one_mul,neg_one_mul] at h3 ⊢
  change (windows 0 (y 0)*(windows 1 (y 1)*(windows 2 (y 2)*windows 3 (y 3)))) *
    ((Real.exp (-(1/2:ℝ)*y 2):ℂ)*(Real.exp (-y 3):ℂ)) =
    ((Real.exp ((1/2:ℝ)*M 2):ℂ)*(Real.exp (M 3):ℂ))*
      (windows 0 (y 0)*(windows 1 (y 1)*
        (reciprocalWindow (windows 2) (1/2) (M 2) (y 2)*
         reciprocalWindow (windows 3) 1 (M 3) (y 3))))
  calc
    _ = windows 0 (y 0)*windows 1 (y 1)*
      (windows 2 (y 2)*(Real.exp (-(1/2:ℝ)*y 2):ℂ))*
      (windows 3 (y 3)*(Real.exp (-y 3):ℂ)) := by ring
    _ = _ := by rw [h2,h3]; ring

theorem reciprocal_source_window_identity (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (QK QP Qn Qb k p n b r : ℝ) (hQn : 0<Qn) (hQb : 0<Qb)
    (hn : 0<n) (hb : 0<b) (hr : 0<r) :
    (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i)) /
      ((r*Real.sqrt n*b:ℝ):ℂ) =
    ((Real.exp (M 2/2+M 3)/(r*Real.sqrt Qn*Qb):ℝ):ℂ) *
      (∏ i, reciprocalKernelWindows windows M i (kernelLogCoordinates QK QP Qn Qb k p n b i)) := by
  have hp := reciprocal_window_product windows M (kernelLogCoordinates QK QP Qn Qb k p n b)
  change (∏ i, windows i (kernelLogCoordinates QK QP Qn Qb k p n b i))*
      ((Real.exp (-(1/2:ℝ)*Real.log (n/Qn)):ℂ)*(Real.exp (-Real.log (b/Qb)):ℂ)) = _ at hp
  rw [reciprocal_norm_log Qn n hQn hn,reciprocal_cube_log Qb b hQb hb] at hp
  have he := congrArg (fun z : ℂ => z/((r*Real.sqrt Qn*Qb:ℝ):ℂ)) hp
  have hn0 := (Real.sqrt_pos.mpr hn).ne'
  have hQn0 := (Real.sqrt_pos.mpr hQn).ne'
  simp only [Complex.ofReal_mul,Complex.ofReal_div] at he ⊢
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hbC : (b:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hQbC : (Qb:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQb.ne'
  have hnC : (Real.sqrt n:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn0
  have hQnC : (Real.sqrt Qn:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQn0
  convert he using 1 <;> field_simp

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0967

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.KernelIntegral
Source SHA256: eff61daa998b963f22d2222a53b0c7ec078e03bb543feffef2c9b2b4b6101c87
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0968


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section

lemma reflected_density_integrable (U W : ℝ→ℂ) (hU : Measurable U)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (θ R : ℝ) (hR : 0<R) (J : ℕ)
    (hi : Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖)) :
    Integrable (twistedDensity U W θ R) := by
  have hm := (twistedDensity_joint_stronglyMeasurable U W hU a b ha hWs hW R hR).comp_measurable
    (measurable_const.prodMk measurable_id : Measurable (fun t : ℝ => (θ,t)))
  apply hi.mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg t]))

lemma kernel_mode_integrable (density : ℝ→ℂ) (hi : Integrable density)
    (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb k p n b : ℝ) :
    Integrable (fun t : ℝ => density t *
      (kernelCoordinateWeight (windows 0) (-2) QK t k *
        kernelCoordinateWeight (windows 1) (-2) QP t p * kernelDualWeight windows Qn Qb t n b)) := by
  have hc : Continuous (fun t : ℝ => kernelCoordinateWeight (windows 0) (-2) QK t k *
      kernelCoordinateWeight (windows 1) (-2) QP t p * kernelDualWeight windows Qn Qb t n b) :=
    ((kernelCoordinateWeight_continuous _ _ _ _).mul (kernelCoordinateWeight_continuous _ _ _ _)).mul
      ((kernelCoordinateWeight_continuous _ _ _ _).mul (kernelCoordinateWeight_continuous _ _ _ _))
  apply hi.mul_bdd (c := ‖windows 0 (Real.log (k/QK))‖*‖windows 1 (Real.log (p/QP))‖*
    (‖windows 2 (Real.log (n/Qn))‖*‖windows 3 (Real.log (b/Qb))‖)) hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  exact le_of_eq (by simp only [kernelDualWeight,norm_mul,kernelCoordinateWeight_norm])

theorem kernel_finite_contraction {κ : Type*} (source : Finset κ) (coeff value : κ→ℂ)
    (density : ℝ→ℂ) (hi : Integrable density) (scalar : ℂ)
    (windows : Fin 4→ℝ→ℂ) (QK QP Qn Qb : ℝ) (k p n b : κ→ℝ)
    (he : ∀ j ∈ source, value j = scalar*∫ t : ℝ,
      (kernelCoordinateWeight (windows 0) (-2) QK t (k j)*
        kernelCoordinateWeight (windows 1) (-2) QP t (p j)*
        kernelDualWeight windows Qn Qb t (n j) (b j))*density t) :
    (∑ j ∈ source, coeff j*value j) = scalar*∫ t : ℝ, density t*
      ∑ j ∈ source, coeff j*(kernelCoordinateWeight (windows 0) (-2) QK t (k j)*
        kernelCoordinateWeight (windows 1) (-2) QP t (p j)*
        kernelDualWeight windows Qn Qb t (n j) (b j)) := by
  have hint (j : κ) : Integrable (fun t : ℝ => density t*
      (coeff j*(kernelCoordinateWeight (windows 0) (-2) QK t (k j)*
        kernelCoordinateWeight (windows 1) (-2) QP t (p j)*
        kernelDualWeight windows Qn Qb t (n j) (b j)))) := by
    convert (kernel_mode_integrable density hi windows QK QP Qn Qb (k j) (p j) (n j) (b j)).const_mul (coeff j) using 1
    funext t
    ring
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum source (fun j _ => hint j),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  rw [← mul_assoc,mul_comm (coeff j) scalar,mul_assoc]
  apply congrArg (fun z : ℂ => scalar*z)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; ring)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0968

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.KernelSource
Source SHA256: ee287429f1f161640909574538355738a42e557cfd8aef4c86829868b0400580
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0969


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform
noncomputable section
universe u

theorem reflected_finite_source_uniform
    (a b : ℝ) (ha : 0<a) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧
      HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ C QK QP Qn Qb r : ℝ, 0<C → 0<QK → 0<QP → 0<Qn → 0<Qb → 0<r →
      let R := kernelCenter C QK QP Qn Qb
      (∀ {κ : Type u} (source : Finset κ) (coeff : κ→ℂ) (k p n q : κ→ℝ),
        (∀ j ∈ source, 0<k j ∧ 0<p j ∧ 0<n j ∧ 0<q j) →
        (∑ j ∈ source, coeff j *
          ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (k j) (p j) (n j) (q j) i)) /
            ((r*Real.sqrt (n j)*q j:ℝ):ℂ) *
            CubicReflectionKernel.paperKernel (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
              (C*n j*(q j)^3/((k j)^2*(p j)^2)))) =
        ((Real.exp (M 2/2+M 3)/(r*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            ∑ j ∈ source, coeff j *
              (kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (k j)*
                kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (p j)*
                kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (n j) (q j))) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
  obtain ⟨U,degree,C₀,hC₀,hUc,hUs,hsep⟩ := reflected_kernel_uniform_separation
    a b ha (reciprocalKernelWindows windows M) M hM
      (reciprocalKernelWindows_support windows M hwindows) W hWsupport hW J
  refine ⟨U,degree,C₀,hC₀,hUc,hUs,?_⟩
  intro θ C QK QP Qn Qb r hC hQK hQP hQn hQb hr
  obtain ⟨he,hi,hm,hp⟩ := hsep θ C QK QP Qn Qb hC hQK hQP hQn hQb
  have hR : 0<kernelCenter C QK QP Qn Qb := by unfold kernelCenter; positivity
  have hdi := reflected_density_integrable U W hUs.continuous.measurable
    a b ha hWsupport hW θ _ hR J hi
  refine ⟨?_,hdi,hi,hm,hp⟩
  intro κ source coeff k p n q hn
  apply kernel_finite_contraction source coeff _ _ hdi _
    (reciprocalKernelWindows windows M) QK QP Qn Qb k p n q
  intro j hj
  rw [reciprocal_source_window_identity windows M QK QP Qn Qb
    (k j) (p j) (n j) (q j) r hQn hQb (hn j hj).2.2.1 (hn j hj).2.2.2 hr]
  rw [mul_assoc,he (k j) (p j) (n j) (q j) (hn j hj).1 (hn j hj).2.1 (hn j hj).2.2.1 (hn j hj).2.2.2,
    Complex.ofReal_mul]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0969

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.KernelActual
Source SHA256: 57c08464f359de2e4d5a4c348345837326c232a3ef779f0c072f035062873b4b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0970



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma fixedKernelCoefficient_pos (X tau r : ℝ) (C D1 D2 : Ideal Eis)
    (hX : 0<X) (htau : 0<tau) (hr : 0<r) (hC : C≠0) (hD1 : D1≠0) (hD2 : D2≠0) :
    0<fixedKernelCoefficient X tau r C D1 D2 := by
  have hn (I : Ideal Eis) (hI : I≠0) : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hCn := hn C hC
  have h1 := hn D1 hD1
  have h2 := hn D2 hD2
  unfold fixedKernelCoefficient
  positivity

def actualKernelCoefficient (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (m : ℕ) (X : ℝ) : ℝ :=
  fixedKernelCoefficient X (sourceCuspScale s.index) (ramifiedScale 1 completedRamifiedStep m)
    (Ideal.span {c}*(∏ i, F.ideal i)) 1 1

lemma actualKernelCoefficient_pos (F : PrimeFamily φ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hc : c≠0) (m : ℕ) (X : ℝ) (hX : 0<X) : 0<actualKernelCoefficient F s m X := by
  apply fixedKernelCoefficient_pos _ _ _ _ _ _ hX (sourceCuspScale_pos _)
    (ramifiedScale_pos _ _ (by norm_num) (lt_trans zero_lt_one completedRamifiedStep_gt_one) _) _ one_ne_zero one_ne_zero
  apply mul_ne_zero
  · exact Ideal.span_singleton_eq_bot.not.mpr hc
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (F.ideal i))

theorem actual_theta_kernel_argument (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (m : ℕ) (X : ℝ) (n b : Ideal Eis) :
    (X/(27*(sourceCuspScale s.index)^2*
      (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
      (ramifiedScale 1 completedRamifiedStep m)^3*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3 =
    actualKernelCoefficient F s m X*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3/
      ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2) := by
  simpa only [one_mul,actualKernelCoefficient] using source_kernel_argument_factor F K hK S c
    X (sourceCuspScale s.index) (ramifiedScale 1 completedRamifiedStep m) 1 1 n b

def actualKernelSourceTerm (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (windows : Fin 4→ℝ→ℂ)
    (QK QP Qn Qb : ℝ) (W : ℝ→ℂ) (θ X : ℝ) : ℂ :=
  actualMixedCoefficient F K hK S jF D s hc u m n b *
    ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
      (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i)) /
      ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ) *
      CubicReflectionKernel.paperKernel (Vstar (CompletedHeight.normTwistedSource W θ))
        ((X/(27*(sourceCuspScale s.index)^2*
          (Ideal.absNorm (Ideal.span {c*∏ i, (F.reflected K hK S).generator i}):ℝ)^2))*
          (ramifiedScale 1 completedRamifiedStep m)^3*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3))

theorem actualKernelSourceTerm_numeric (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
    (S : PrimeFamily σ) (jF : φ→ℕ)
    (D : ControlledStratumArithmetic (F.reflected K hK S).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (windows : Fin 4→ℝ→ℂ)
    (QK QP Qn Qb : ℝ) (W : ℝ→ℂ) (θ X : ℝ) :
    actualKernelSourceTerm F K hK S jF D s hc u m n b windows QK QP Qn Qb W θ X =
    actualMixedCoefficient F K hK S jF D s hc u m n b *
      ((∏ i, windows i (kernelLogCoordinates QK QP Qn Qb (Ideal.absNorm K:ℝ)
        (Ideal.absNorm (∏ i, S.ideal i):ℝ) (Ideal.absNorm n:ℝ) (Ideal.absNorm b:ℝ) i)) /
        ((ramifiedScale 1 completedRamifiedStep m*Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ):ℝ):ℂ) *
        CubicReflectionKernel.paperKernel (Vstar (CompletedHeight.normTwistedSource W θ))
          (actualKernelCoefficient F s m X*(Ideal.absNorm n:ℝ)*(Ideal.absNorm b:ℝ)^3/
            ((Ideal.absNorm K:ℝ)^2*(Ideal.absNorm (∏ i, S.ideal i):ℝ)^2))) := by
  unfold actualKernelSourceTerm
  rw [actual_theta_kernel_argument]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0970

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.KernelActualSource
Source SHA256: 15992ec55191a036f7f6d5bc27e1d7c4a9fe0a67eea80c3295ca26287ebfe32f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0971


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open MeasureTheory FourierBridge InverseKernelSourceUniform
open CompletedDyadic ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
universe u
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem actual_reflected_finite_source_uniform
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (windows : Fin 4→ℝ→ℂ) (M : Fin 4→ℝ)
    (hM : ∀ i, 0≤M i) (hwindows : ∀ i y, windows i y≠0 → |y|≤M i)
    (W : ℝ→ℂ) (hWsupport : Function.support W ⊆ Set.Icc a₀ b₀)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ→ℂ) (degree : ℕ) (C₀ : ℝ), 0≤C₀ ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ (F : PrimeFamily φ)
        (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
        (unit : Eisˣ) (m : ℕ) (θ X QK QP Qn Qb : ℝ),
        0<X → 0<QK → 0<QP → 0<Qn → 0<Qb →
      let R := kernelCenter (actualKernelCoefficient F s m X) QK QP Qn Qb
      (∀ {κ : Type u} (source : Finset κ) (weight : κ→ℂ)
        (K : κ→Ideal Eis) (hK : ∀ j, Admissible (K j)) (S : κ→PrimeFamily σ) (jF : φ→ℕ)
        (D : ∀ j, ControlledStratumArithmetic (F.reflected (K j) (hK j) (S j)).generator N a c mode)
        (n b : κ→Ideal Eis), (∀ j ∈ source, n j≠0 ∧ b j≠0) →
        (∑ j ∈ source, weight j*actualKernelSourceTerm F (K j) (hK j) (S j) jF (D j) s hc
          unit m (n j) (b j) windows QK QP Qn Qb W θ X) =
        ((Real.exp (M 2/2+M 3)/(ramifiedScale 1 completedRamifiedStep m*Real.sqrt Qn*Qb)*smallScalar R:ℝ):ℂ)*
          ∫ t : ℝ, twistedDensity U W θ R t *
            ∑ j ∈ source, (weight j*actualMixedCoefficient F (K j) (hK j) (S j) jF (D j) s hc unit m (n j) (b j))*
              (kernelCoordinateWeight (reciprocalKernelWindows windows M 0) (-2) QK t (Ideal.absNorm (K j):ℝ)*
                kernelCoordinateWeight (reciprocalKernelWindows windows M 1) (-2) QP t (Ideal.absNorm (∏ i, (S j).ideal i):ℝ)*
                kernelDualWeight (reciprocalKernelWindows windows M) Qn Qb t (Ideal.absNorm (n j):ℝ) (Ideal.absNorm (b j):ℝ))) ∧
      Integrable (twistedDensity U W θ R) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖) ≤ C₀*(1+‖θ‖)^degree ∧
      (∀ t : ℝ, (1+‖t‖)^J*‖twistedDensity U W θ R t‖ ≤ C₀*(1+‖θ‖)^degree) := by
