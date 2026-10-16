    rw [←starRingEnd_apply,Complex.mul_conj',hΨ]
    norm_num
  have hmask : star (rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C))*
      rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C) := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hd := finiteSquarefreeRow_self_pair (fun i=>Ideal.span {p i}) hg V d
  have hh := finiteSquarefreeRow_self_pair (fun i=>Ideal.span {p i}) hg V h
  simp only [initialColumn,mul_one,star_mul,star_star]
  calc
    _ = (columnCoefficient p hp hcop hg V*star (columnCoefficient p hp hcop hg V))*
      (Ψ (∏ i∈V,p i)*star (Ψ (∏ i∈V,p i)))*
      (star (rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C))*
        rowCoprimeMask (fun i=>Ideal.span {p i}) V (j*C))*
      (star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V d)*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V d)*
      (star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V h)*
        finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg V h) := by ring
    _ = _ := by rw [hcol,hphase,hmask,hd,hh]; ring

theorem sourceIdeal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (sourceIdeal p) := by
  intro S T he
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod] at he
  exact FirstCauchyArithmetic.family_product_injective _ hinj he

@[ext] structure Source (J : ℕ) where
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : O
  assigned : Fin J→ι

def toTuple {J : ℕ} (x : Source (ι:=ι) J) : InitialTuple J :=
  sourceTuple p x.common x.divisor x.overlap x.frequency x.assigned

theorem toTuple_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) {J : ℕ} :
    Function.Injective (toTuple p (J:=J)) := by
  intro x y he
  have hC := congrArg InitialTuple.common he
  have hD := congrArg InitialTuple.divisor he
  have hV := congrArg InitialTuple.residual he
  have hf := congrArg InitialTuple.frequency he
  have ha := congrArg InitialTuple.assigned he
  apply Source.ext
  · exact sourceIdeal_injective p hinj hC
  · exact sourceIdeal_injective p hinj hD
  · exact sourceIdeal_injective p hinj hV
  · exact hf
  · funext i
    apply hinj
    exact congrArg Subtype.val (congrFun ha i)

def assignedTerm {J : ℕ} (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (outer : Finset ι) (assigned : Fin J→ι) : ℂ :=
  ∏ i, if assigned i∈lists i ∧ assigned i∈outer then a i (assigned i) else 0

theorem assignedTerm_source {J : ℕ} (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (outer : Finset ι) (assigned : Fin J→ι) (h : assignedTerm lists a outer assigned≠0) :
    ∀ i,assigned i∈lists i ∧ assigned i∈outer := by
  intro i
  have hn := Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)
  by_contra hi
  simp only [hi,ite_false,ne_eq,not_true_eq_false] at hn

include hp in

theorem actual_source_valid (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (x : Source (ι:=ι) J) (hdiv : x.divisor⊆x.common)
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hterm : assignedTerm lists a (x.common∪x.overlap) x.assigned≠0) :
    InitialSourceValid (toTuple p x) :=
  sourceTuple_valid p hp hpr x.common x.divisor x.overlap x.frequency x.assigned hdiv
    (fun i=>(assignedTerm_source lists a _ _ hterm i).2)

include hp in

theorem actual_source_fiber_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ}
    (sources : Finset (Source (ι:=ι) J))
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hdiv : ∀ x∈sources,x.divisor⊆x.common)
    (hterm : ∀ x∈sources,assignedTerm lists a (x.common∪x.overlap) x.assigned≠0)
    (t f : Ideal O) (k : O) (ht : t≠0) (hf : f≠0) :
    (sources.filter (fun x=>initialChild (toTuple p x)=(t,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(J+1)*
        (IdealMobiusDivisorSum.idealDivisors t).card^J := by
  let S := sources.filter (fun x=>initialChild (toTuple p x)=(t,f,k))
  let T := S.image (toTuple p)
  have hvalid : ∀ y∈T, Valid y t f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,hchild⟩ := Finset.mem_filter.mp hx
    have hv := initialChild_valid (toTuple p x)
      (actual_source_valid p hp hpr x (hdiv x hxs) lists a (hterm x hxs))
    simpa only [hchild] using hv
  have hh := valid_tuple_card_le_separated T t f k ht hf hvalid
  have hcard : T.card=S.card := Finset.card_image_of_injective _ (toTuple_injective p hinj)
  rw [hcard] at hh
  exact hh

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem poisson_generator_unit (hpr : ∀ i,λ₀^2∣p i-1) (E : Finset ι) :
    ∃ u : Oˣ, primeSubsetGenerator (fun i=>Ideal.span {p i}) E=
      (u : O)*primaryGenerator (sourceIdeal p E) := by
  have hg0 : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hs : Ideal.span {primaryGenerator (sourceIdeal p E)}=
      Ideal.span {primeSubsetGenerator (fun i=>Ideal.span {p i}) E} := by
    rw [(primaryGenerator_spec _ hg0).1]
    simp only [primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,
      sourceIdeal,FiniteGaussPhase.span_finset_prod]
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u,by simpa only [mul_comm] using hu.symm⟩

def sectorSource {J : ℕ} (u : Oˣ) (x : Source (ι:=ι) J) : Source (ι:=ι) J :=
  {x with frequency := (u : O)^5*x.frequency}

omit [DecidableEq ι] in
theorem sectorSource_injective {J : ℕ} (u : Oˣ) :
    Function.Injective (sectorSource (J:=J) (ι:=ι) u) := by
  intro x y he
  apply Source.ext
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.common) he
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.divisor) he
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.overlap) he
  · have hh := congrArg Source.frequency he
    exact mul_left_cancel₀ (pow_ne_zero 5 (Units.ne_zero u)) hh
  · simpa only [sectorSource] using congrArg (fun z : Source (ι:=ι) J=>z.assigned) he

include hp in

omit hp in
theorem sectorTuple_injective (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {J : ℕ} (u : Oˣ) :
    Function.Injective (fun x : Source (ι:=ι) J=>toTuple p (sectorSource u x)) :=
  (toTuple_injective p hinj).comp (sectorSource_injective u)

include hp in

theorem actual_sector_fiber_bound
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,λ₀^2∣p i-1) {J : ℕ} (u : Oˣ)
    (sources : Finset (Source (ι:=ι) J))
    (lists : Fin J→Finset ι) (a : Fin J→ι→ℂ)
    (hdiv : ∀ x∈sources,x.divisor⊆x.common)
    (hterm : ∀ x∈sources,assignedTerm lists a (x.common∪x.overlap) x.assigned≠0)
    (t f : Ideal O) (k : O) (ht : t≠0) (hf : f≠0) :
    (sources.filter (fun x=>initialChild (toTuple p (sectorSource u x))=(t,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(J+1)*
        (IdealMobiusDivisorSum.idealDivisors t).card^J := by
  let S := sources.filter (fun x=>initialChild (toTuple p (sectorSource u x))=(t,f,k))
  let T := S.image (fun x=>toTuple p (sectorSource u x))
  have hv : ∀ y∈T, Valid y t f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,hchild⟩ := Finset.mem_filter.mp hx
    have he := initialChild_valid (toTuple p (sectorSource u x))
      (actual_source_valid p hp hpr (sectorSource u x) (hdiv x hxs) lists a (hterm x hxs))
    simpa only [hchild] using he
  have hh := valid_tuple_card_le_separated T t f k ht hf hv
  have hcard : T.card=S.card := Finset.card_image_of_injective _ (sectorTuple_injective p hinj u)
  rw [hcard] at hh
  exact hh

theorem initial_poisson_child_normalized
    (hpr : ∀ i,λ₀^2∣p i-1) (G E V : Finset ι) (Ψ : O →* ℂ)
    (j e t h : O) (he : Ideal.span {e}=sourceIdeal p E)
    (ht : Ideal.span {t}=sourceIdeal p (G\E)) :
    ∃ u : Oˣ, e=(u:O)*primaryGenerator (sourceIdeal p E) ∧
      ∀ (H : Finset ι→ℂ) (N : Finset ι),
        secondChildColumn p hp hcop hg Ψ (j*t) (e*∏ i∈V,p i) (e*h) H N =
          secondChildColumn p hp hcop hg Ψ
            (j*primaryGenerator (sourceIdeal p (G\E)))
            (primaryGenerator (sourceIdeal p E*sourceIdeal p V))
            (primaryGenerator (sourceIdeal p E)*((u:O)^5*h)) H N := by
  have hgE : primaryGenerator (sourceIdeal p E)≠0 := by
    rw [sourceIdeal_gen p hp hpr E]
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  obtain ⟨u,hu⟩ := generator_eq_unit_primary (sourceIdeal p E) e he hgE
  refine ⟨u,hu,?_⟩
  intro H N
  have hts : Ideal.span {t}=Ideal.span {primaryGenerator (sourceIdeal p (G\E))} := by
    rw [ht,sourceIdeal_gen p hp hpr (G\E)]
    rfl
  have hmask := rowCoprimeMask_mul_eq_of_span_eq (fun i=>Ideal.span {p i}) N j hts
  have hchange : secondChildColumn p hp hcop hg Ψ (j*t) (e*∏ i∈V,p i) (e*h) H N =
      secondChildColumn p hp hcop hg Ψ (j*primaryGenerator (sourceIdeal p (G\E)))
        (e*∏ i∈V,p i) (e*h) H N := by
    simp only [secondChildColumn,hmask]
  rw [hchange,hu,primaryGenerator_mul,sourceIdeal_gen p hp hpr V]
  rw [mul_assoc (u:O)]
  exact secondChildColumn_generator_unit p hp hcop hg Ψ u _ _ _ h H N

end SevenEighths.InverseInitialArithmetic

end

end OAI
end OAIOriginalModule0506

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialOverlap
Source SHA256: 3e08d000494a74ed90649cd77b5dd0da496f419588f1dbde00ba4bb42eb18c33
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0507



namespace OAI

noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum
open UniqueFactorizationMonoid

namespace SevenEighths.InverseInitialOverlap

abbrev O := ActualEisensteinCubic.O

def residual (P j : Ideal O) : Ideal O := idealQuotient j P

def column (P j n : Ideal O) : Ideal O := idealQuotient j n * residual P j

def reconstruct (P j c : Ideal O) : Ideal O := j * idealQuotient (residual P j) c

def original (S : Finset (Ideal O)) (P j : Ideal O) : Finset (Ideal O) :=
  S.filter fun n => Squarefree n ∧ gcd n P = j

def columns (S : Finset (Ideal O)) (P j : Ideal O) : Finset (Ideal O) :=
  (original S P j).image (column P j)

theorem mem_original {S : Finset (Ideal O)} {P j n : Ideal O} :
    n ∈ original S P j ↔ n ∈ S ∧ Squarefree n ∧ gcd n P = j := by
  simp only [original, Finset.mem_filter]

theorem residual_mul {P j : Ideal O} (hj : j ∣ P) : j * residual P j = P :=
  idealQuotient_mul hj

theorem residual_squarefree {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P) :
    Squarefree (residual P j) :=
  hP.squarefree_of_dvd (idealQuotient_dvd hj)

theorem quotient_mul_cancel {D H : Ideal O} (hD : D ≠ 0) :
    idealQuotient D (D * H) = H :=
  mul_left_cancel₀ hD (idealQuotient_mul (dvd_mul_right D H))

theorem column_properties {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hn : Squarefree n) (hg : gcd n P = j) :
    Squarefree (column P j n) ∧ IsCoprime (column P j n) j ∧
      residual P j ∣ column P j n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hHP : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have hHj := hHP.mono (dvd_refl _) hj
  have hHP0 := hHP.mono (dvd_refl _) (idealQuotient_dvd hj)
  have hJP0 : IsCoprime j (residual P j) :=
    ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (j * residual P j) by rw [residual_mul hj]; exact hP)).1
  refine ⟨squarefree_mul_iff.mpr ⟨hHP0.isRelPrime,
    hn.squarefree_of_dvd (idealQuotient_dvd hjn), residual_squarefree hP hj⟩,
    hHj.mul_left hJP0.symm, dvd_mul_left _ _⟩

theorem reconstruct_column {P j n : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hg : gcd n P = j) : reconstruct P j (column P j n) = n := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hP0 := (residual_squarefree hP hj).ne_zero
  unfold reconstruct column
  rw [mul_comm (idealQuotient j n), quotient_mul_cancel hP0, idealQuotient_mul hjn]

theorem reconstruct_properties {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hc : Squarefree c) (hcj : IsCoprime c j) (hPc : residual P j ∣ c) :
    Squarefree (reconstruct P j c) ∧ gcd (reconstruct P j c) P = j := by
  let H := idealQuotient (residual P j) c
  have hHc : H ∣ c := idealQuotient_dvd hPc
  have hHj : IsCoprime H j := hcj.mono hHc (dvd_refl _)
  have hHP0 : IsCoprime H (residual P j) :=
    (ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp
      (show Squarefree (residual P j * H) by rw [idealQuotient_mul hPc]; exact hc)).1).symm
  have hHP : IsCoprime H P := by
    rw [← residual_mul hj]
    exact hHj.mul_right hHP0
  exact ⟨squarefree_mul_iff.mpr ⟨hHj.symm.isRelPrime,
    hP.squarefree_of_dvd hj, hc.squarefree_of_dvd hHc⟩,
    gcd_mul_of_coprime_divisor j H P hj hHP⟩

theorem column_reconstruct {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) : column P j (reconstruct P j c) = c := by
  have hj0 : j ≠ 0 := ne_zero_of_dvd_ne_zero hP.ne_zero hj
  unfold column reconstruct
  rw [quotient_mul_cancel hj0, mul_comm, idealQuotient_mul hPc]

theorem mem_columns {S : Finset (Ideal O)} {P j c : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    c ∈ columns S P j ↔ Squarefree c ∧ IsCoprime c j ∧
      residual P j ∣ c ∧ reconstruct P j c ∈ S := by
  constructor
  · intro hc
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hnS, hn, hg⟩ := mem_original.mp hn
    obtain ⟨hcs, hcj, hPc⟩ := column_properties hP hj hn hg
    exact ⟨hcs, hcj, hPc, by rwa [reconstruct_column hP hj hg]⟩
  · rintro ⟨hc, hcj, hPc, hnS⟩
    obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hc hcj hPc
    exact Finset.mem_image.mpr ⟨reconstruct P j c,
      mem_original.mpr ⟨hnS, hn, hg⟩, column_reconstruct hP hj hPc⟩

theorem column_injOn (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) :
    Set.InjOn (column P j) (original S P j) := by
  intro n hn m hm he
  have hn' := reconstruct_column hP hj (mem_original.mp hn).2.2
  have hm' := reconstruct_column hP hj (mem_original.mp hm).2.2
  rw [← hn', ← hm', he]

def overlapEquiv (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) : original S P j ≃ columns S P j where
  toFun n := ⟨column P j n, Finset.mem_image.mpr ⟨n, n.property, rfl⟩⟩
  invFun c := ⟨reconstruct P j c, by
    obtain ⟨hc, hcj, hPc, hnS⟩ := (mem_columns hP hj).mp c.property
    exact mem_original.mpr ⟨hnS, reconstruct_properties hP hj hc hcj hPc⟩⟩
  left_inv n := Subtype.ext (reconstruct_column hP hj (mem_original.mp n.property).2.2)
  right_inv c := Subtype.ext (column_reconstruct hP hj
    ((mem_columns hP hj).mp c.property).2.2.1)

theorem reconstruct_mul_residual {P j c : Ideal O} (hPc : residual P j ∣ c) :
    reconstruct P j c * residual P j = j * c := by
  unfold reconstruct
  rw [mul_assoc, mul_comm (idealQuotient _ _), idealQuotient_mul hPc]

theorem norm_reconstruct {P j c : Ideal O} (hPc : residual P j ∣ c) :
    Ideal.absNorm (reconstruct P j c) * Ideal.absNorm (residual P j) =
      Ideal.absNorm j * Ideal.absNorm c := by
  simpa only [map_mul] using congrArg Ideal.absNorm (reconstruct_mul_residual hPc)

theorem cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) (X : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / X =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c /
        ((Ideal.absNorm (residual P j) : ℝ) * X) := by
  have h0 : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hn : (Ideal.absNorm (reconstruct P j c) : ℝ) =
      (Ideal.absNorm j : ℝ) * Ideal.absNorm c / Ideal.absNorm (residual P j) := by
    apply (eq_div_iff h0).mpr
    exact_mod_cast norm_reconstruct hPc
  rw [hn, div_div]

theorem columns_filter (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (mask : Ideal O → Prop) [DecidablePred mask] :
    columns (S.filter mask) P j =
      (columns S P j).filter fun c => mask (reconstruct P j c) := by
  ext c
  simp only [mem_columns hP hj, Finset.mem_filter]
  tauto

theorem sum_reconstruct (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (F : Ideal O → ℂ) :
    (∑ n ∈ original S P j, F n) =
      ∑ c ∈ columns S P j, F (reconstruct P j c) := by
  rw [columns, Finset.sum_image (column_injOn S hP hj)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [reconstruct_column hP hj (mem_original.mp hn).2.2]

theorem coefficient_identity (ψ : Ideal O →* ℂ) {P j n : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (hn : Squarefree n) (hg : gcd n P = j) :
    (moebius n : ℂ) * ψ n * ψ P =
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2 *
        ((moebius (column P j n) : ℂ) * ψ (column P j n)) := by
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hH : IsCoprime (idealQuotient j n) P := by
    rw [← hg]
    exact squarefree_quotient_gcd_coprime n P hn
  have h := InverseMoment.moebius_character_overlap ψ
    (hH.mono (dvd_refl _) hj).symm.isRelPrime
    (hH.mono (dvd_refl _) (idealQuotient_dvd hj)).isRelPrime
    (residual_squarefree hP hj)
  rw [idealQuotient_mul hjn, idealQuotient_mul hj] at h
  change (moebius n : ℂ) * ψ n * ψ P = _
  rw [h]
  unfold column residual
  ring

theorem polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ original S P j,
      (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / X)) =
    ((moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * X)) := by
  rw [sum_reconstruct S hP hj, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨hcs, hcj, hPc, _⟩ := (mem_columns hP hj).mp hc
  obtain ⟨hn, hg⟩ := reconstruct_properties hP hj hcs hcj hPc
  rw [coefficient_identity ψ hP hj hn hg, column_reconstruct hP hj hPc,
    cutoff_argument hP hj hPc]
  ring

theorem sum_original_partition (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (F : Ideal O → ℂ) :
    (∑ n ∈ S.filter Squarefree, F n) =
      ∑ j ∈ idealDivisors P, ∑ n ∈ original S P j, F n := by
  have hmap : ∀ n ∈ S.filter Squarefree, gcd n P ∈ idealDivisors P := by
    intro n _
    exact (mem_idealDivisors hP.ne_zero).mpr (GCDMonoid.gcd_dvd_right _ _)
  have h := Finset.sum_fiberwise_of_maps_to hmap F
  simpa only [original, Finset.filter_filter] using h.symm

theorem polynomial_all_overlaps (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    (∑ n ∈ S.filter Squarefree,
      (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / X)) =
    ∑ j ∈ idealDivisors P,
      ((moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
            ((Ideal.absNorm (residual P j) : ℝ) * X)) := by
  rw [sum_original_partition S hP]
  apply Finset.sum_congr rfl
  intro j hj
  exact polynomial_fixed_overlap S hP ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W X

theorem scaled_cutoff_argument {P j c : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (hPc : residual P j ∣ c) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Ideal.absNorm (reconstruct P j c) : ℝ) / Z ^ r =
      (((Ideal.absNorm j : ℝ) / Z ^ G) *
        ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
        ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G)) := by
  have hnorm : (Ideal.absNorm (residual P j) : ℝ) ≠ 0 := by
    exact_mod_cast fun h => (residual_squarefree hP hj).ne_zero
      (Ideal.absNorm_eq_zero_iff.mp h)
  have hscale : Z ^ G * Z ^ (r + z - 2 * G) = Z ^ r * Z ^ (z - G) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  rw [cutoff_argument hP hj hPc]
  rw [div_mul_div_comm, div_div_eq_mul_div]
  field_simp [hnorm, (Real.rpow_pos_of_pos hZ r).ne',
    (Real.rpow_pos_of_pos hZ G).ne',
    (Real.rpow_pos_of_pos hZ (r + z - 2 * G)).ne',
    (Real.rpow_pos_of_pos hZ (z - G)).ne']
  linear_combination ((Ideal.absNorm j : ℝ) * Ideal.absNorm c) * hscale

theorem normalization_split {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    Z ^ (-(r + z) / 2) = Z ^ (-G) * Z ^ (-(r + z - 2 * G) / 2) := by
  rw [← Real.rpow_add hZ]
  congr 1
  ring

theorem normalized_polynomial_fixed_overlap (S : Finset (Ideal O)) {P j : Ideal O}
    (hP : Squarefree P) (hj : j ∣ P) (ψ : Ideal O →* ℂ)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ original S P j,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
      (Z ^ (-G) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G) / 2) : ℝ) *
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
  rw [polynomial_fixed_overlap S hP hj ψ a W, normalization_split hZ r z G,
    Complex.ofReal_mul]
  have hs : (∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((Ideal.absNorm j : ℝ) * Ideal.absNorm c /
          ((Ideal.absNorm (residual P j) : ℝ) * Z ^ r))) =
      ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
        W ((((Ideal.absNorm j : ℝ) / Z ^ G) *
          ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G))) /
          ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G))) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hPc := ((mem_columns hP hj).mp hc).2.2.1
    rw [← cutoff_argument hP hj hPc, scaled_cutoff_argument hP hj hPc hZ]
  rw [hs]
  ring

theorem normalized_polynomial_all_overlaps (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S.filter Squarefree,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  rw [sum_original_partition S hP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact normalized_polynomial_fixed_overlap S hP
    ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W hZ r z (G j)

theorem sum_moebius_filter (S : Finset (Ideal O)) (F : Ideal O → ℂ) :
    (∑ n ∈ S, (moebius n : ℂ) * F n) =
      ∑ n ∈ S.filter Squarefree, (moebius n : ℂ) * F n := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnf
  have hns : ¬ Squarefree n := fun h => hnf (Finset.mem_filter.mpr ⟨hn, h⟩)
  simp only [moebius_of_not_squarefree hns, Int.cast_zero, zero_mul]

theorem original_normalized_polynomial (S : Finset (Ideal O)) {P : Ideal O}
    (hP : Squarefree P) (ψ : Ideal O →* ℂ) (a : Ideal O → ℂ)
    (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal O → ℝ) :
    (Z ^ (-(r + z) / 2) : ℝ) *
      (∑ n ∈ S,
        (moebius n : ℂ) * ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r)) =
    ∑ j ∈ idealDivisors P,
      (moebius j : ℂ) * (moebius (residual P j) : ℂ) *
        (Z ^ (-G j) : ℝ) * ψ j ^ 2 * (Z ^ (-(r + z - 2 * G j) / 2) : ℝ) *
        ∑ c ∈ columns S P j, (moebius c : ℂ) * ψ c * a (reconstruct P j c) *
          W ((((Ideal.absNorm j : ℝ) / Z ^ G j) *
            ((Ideal.absNorm c : ℝ) / Z ^ (r + z - 2 * G j))) /
            ((Ideal.absNorm (residual P j) : ℝ) / Z ^ (z - G j))) := by
  have hf := sum_moebius_filter S (fun n =>
    ψ n * ψ P * a n * W ((Ideal.absNorm n : ℝ) / Z ^ r))
  simp only [← mul_assoc] at hf
  rw [hf]
  exact normalized_polynomial_all_overlaps S hP ψ a W hZ r z G

theorem overlap_coefficient_norm_le {P j : Ideal O} (hP : Squarefree P) (hj : j ∣ P)
    (ψ : Ideal O →* ℂ) (hψ : ‖ψ j‖ ≤ 1) :
    ‖(moebius j : ℂ) * (moebius (residual P j) : ℂ) * ψ j ^ 2‖ ≤ 1 := by
  have hjSF := hP.squarefree_of_dvd hj
  have hresSF := residual_squarefree hP hj
  simpa [norm_mul, hjSF.moebius_eq, hresSF.moebius_eq] using
    InverseMoment.overlap_scalar_norm_le hψ

end SevenEighths.InverseInitialOverlap

end

end OAI
end OAIOriginalModule0507

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialExcludedSource
Source SHA256: 1262e9bb255a2aa43e72385673bc74dce0c4c6d9dd363684428c355c8f4ff79b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0508


namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum UniqueFactorizationMonoid
namespace SevenEighths.InverseInitialExcludedSource
open InverseInitialOverlap
local notation "O"=>ActualEisensteinCubic.O

def columns (S:Finset (Ideal O))(P j:Ideal O):Finset (Ideal O):=
  (original S P j).image (idealQuotient j)

theorem quotient_properties {P j n:Ideal O}(hn:Squarefree n)(hg:gcd n P=j):
    Squarefree (idealQuotient j n) ∧ IsCoprime (idealQuotient j n) P ∧
      j*idealQuotient j n=n := by
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  exact ⟨hn.squarefree_of_dvd (idealQuotient_dvd hjn),by
    rw [←hg];exact squarefree_quotient_gcd_coprime n P hn,idealQuotient_mul hjn⟩

theorem reconstruct_properties {P j c:Ideal O}(hP:Squarefree P)(hj:j∣P)
    (hc:Squarefree c)(hcp:IsCoprime c P):
    Squarefree (j*c) ∧ gcd (j*c) P=j := by
  exact ⟨squarefree_mul_iff.mpr ⟨(hcp.mono (dvd_refl _) hj).symm.isRelPrime,
    hP.squarefree_of_dvd hj,hc⟩,gcd_mul_of_coprime_divisor j c P hj hcp⟩

theorem mem_columns {S:Finset (Ideal O)}{P j c:Ideal O}
    (hP:Squarefree P)(hj:j∣P):
    c∈columns S P j ↔ Squarefree c ∧ IsCoprime c P ∧ j*c∈S := by
  constructor
  · intro hc
    obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
    obtain ⟨hnS,hns,hng⟩:=mem_original.mp hn
    obtain ⟨hcs,hcp,he⟩:=quotient_properties hns hng
    exact ⟨hcs,hcp,he.symm ▸ hnS⟩
  · rintro ⟨hcs,hcp,hnS⟩
    obtain ⟨hns,hng⟩:=reconstruct_properties hP hj hcs hcp
    refine Finset.mem_image.mpr ⟨j*c,mem_original.mpr ⟨hnS,hns,hng⟩,?_⟩
    exact quotient_mul_cancel (ne_zero_of_dvd_ne_zero hP.ne_zero hj)

theorem sum_reconstruct (S:Finset (Ideal O)){P j:Ideal O}
    (_hP:Squarefree P)(_hj:j∣P)(f:Ideal O→ℂ):
    (∑n∈original S P j,f n)=∑c∈columns S P j,f (j*c) := by
  rw [columns,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2]
  · intro n hn n' hn' he
    have h1:=(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2
    have h2:=(quotient_properties (mem_original.mp hn').2.1 (mem_original.mp hn').2.2).2.2
    rw [←h1,←h2,he]

theorem cutoff_argument (j c:Ideal O)(X:ℝ):
    ((j*c).absNorm:ℝ)/X=(c.absNorm:ℝ)/(X/(j.absNorm:ℝ)) := by
  rw [map_mul,Nat.cast_mul,div_div_eq_mul_div]
  ring

theorem coefficient_identity (ψ:Ideal O→*ℂ){P j c:Ideal O}
    (hj:j∣P)(hcp:IsCoprime c P):
    (moebius (j*c):ℂ)*ψ (j*c)=(moebius j:ℂ)*ψ j*((moebius c:ℂ)*ψ c) := by
  rw [((hcp.mono (dvd_refl _) hj).symm.isRelPrime).moebius_mul,Int.cast_mul,map_mul]
  ring

theorem polynomial_slice (S:Finset (Ideal O)){P j:Ideal O}
    (hP:Squarefree P)(hj:j∣P)(ψ:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(X:ℝ):
    (∑n∈original S P j,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ((moebius j:ℂ)*ψ j)*∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  rw [sum_reconstruct S hP hj,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [coefficient_identity ψ hj ((mem_columns hP hj).mp hc).2.1,cutoff_argument]
  ring

theorem polynomial_decomposition (S:Finset (Ideal O)){P:Ideal O}(hP:Squarefree P)
    (ψ:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(X:ℝ):
    (∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ∑j∈idealDivisors P,((moebius j:ℂ)*ψ j)*
      ∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have hs:(∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
      ∑n∈S.filter Squarefree,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hs:Squarefree n
    · rw [ite_eq_left hs]
    · simp only [ite_eq_right hs,moebius_of_not_squarefree hs,Int.cast_zero,zero_mul]
  rw [hs,sum_original_partition S hP]
  apply Finset.sum_congr rfl
  intro j hj
  exact polynomial_slice S hP ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W X

end SevenEighths.InverseInitialExcludedSource

end

end OAI
end OAIOriginalModule0508

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialOverlapFourier
Source SHA256: 70df6fd7538818ce9f0f33c36f0658f087219e2fb1f23fb0b7096a0ef53abbe7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0509



namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapFourier
open InverseMoment
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def density (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ℂ := (𝓕 g) t*logPhase t xj

theorem density_norm (g : 𝓢(ℝ,ℂ)) (xj t : ℝ) : ‖density g xj t‖=‖(𝓕 g) t‖ := by
  simp only [density,norm_mul,logPhase_norm,mul_one]

theorem density_moment (g : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃C:ℝ,0≤C ∧ ∀xj,
      Integrable (fun t:ℝ=>(1+‖t‖)^J*‖density g xj t‖) ∧
      (∫t:ℝ,(1+‖t‖)^J*‖density g xj t‖)≤C := by
  refine ⟨∫t:ℝ,(1+‖t‖)^J*‖(𝓕 g) t‖,integral_nonneg (fun t=>by positivity),?_⟩
  intro xj
  simp only [density_norm]
  exact ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable g J,le_rfl⟩

lemma phase_neg (t x : ℝ) : logPhase (-t) x=logPhase t (-x) := by
  unfold logPhase
  congr 1
  push_cast
  ring

lemma phase_sub (t xj xc y : ℝ) :
    logPhase t xj*logPhase t xc*logPhase (-t) y=logPhase t (xj+xc-y) := by
  rw [phase_neg,←logPhase_add,←logPhase_add]
  rfl

lemma fourier_phase_integrable (g : 𝓢(ℝ,ℂ)) (x : ℝ) (a : ℂ) :
    Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x*a) := by
  have h : Integrable (fun t:ℝ=>(𝓕 g) t*logPhase t x) (volume:Measure ℝ) :=
    (𝓕 g).integrable.mul_bdd (c:=1)
    (logPhase_continuous_left x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>le_of_eq (logPhase_norm t x)))
  exact h.mul_const a

theorem tuple_mark_phase (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (A : Finset ι) (t : ℝ) :
    primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A =
      ∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
        logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property)) := by
  rw [primeMark_eq_tuple_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [logPhase_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  split_ifs <;> simp

theorem overlap_tuple_separation (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    (∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      g (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*logPhase t xc*
        primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A := by
  simp_rw [tuple_mark_phase]
  simp only [Finset.mul_sum,density]
  have he (p : ∀i∈I,ι) (t:ℝ) :
      (𝓕 g) t*logPhase t xj*logPhase t xc*
        ((∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
          logPhase (-t) (∑i∈I.attach,y i.val (p i.val i.property))) =
      (𝓕 g) t*logPhase t (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))*
        (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) := by
    rw [←phase_sub]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun p hp=>fourier_phase_integrable g _ _)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_mul_const]
  have hinv := schwartz_logPhase_inversion g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
  rw [mul_comm (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)]
  congr 1
  rw [hinv]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem overlap_mode_integrable (g : 𝓢(ℝ,ℂ))
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (A : Finset ι) (xj xc : ℝ) :
    Integrable (fun t:ℝ=>density g xj t*logPhase t xc*
      primeMark I L (fun i p=>a i p*logPhase (-t) (y i p)) A) := by
  simp_rw [tuple_mark_phase]
  simp only [Finset.mul_sum,density]
  apply integrable_finsetSum
  intro p hp
  convert fourier_phase_integrable g
    (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))
    (∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0) using 1
  funext t
  rw [←phase_sub]
  ring

theorem actual_overlap_separation
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (I : Finset σ) (L : σ→Finset ι) (a : σ→ι→ℂ) (y : σ→ι→ℝ)
    (hy : ∀i∈I,∀p∈L i,0<y i p) (A : Finset ι)
    (yj yc : ℝ) (hj : 0<yj) (hc : 0<yc) :
    (∑p∈I.pi L,(∏i∈I.attach,if p i.val i.property∈A then a i.val (p i.val i.property) else 0)*
      W (yj*yc/(∏i∈I.attach,y i.val (p i.val i.property)))) =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        logPhase t (Real.log yc)*
        primeMark I L (fun i p=>a i p*logPhase (-t) (Real.log (y i p))) A := by
  rw [←overlap_tuple_separation]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  simp only [CubicReflectionKernel.logSchwartz_apply,Real.exp_sub,Real.exp_add,
    Real.exp_log hj,Real.exp_log hc,Real.exp_sum]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact (Real.exp_log (hy i.val i.property (p i.val i.property)
    ((Finset.mem_pi.mp hp) i.val i.property))).symm

end SevenEighths.InverseInitialOverlapFourier

end

end OAI
end OAIOriginalModule0509

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialOverlapIdealFourier
Source SHA256: 77f2e7a493c20aa877388dc5dce1121dccdb2b799b2c29803aeb91cec002dcfe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0510



namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic
namespace SevenEighths.InverseInitialOverlapIdealFourier
open InverseMoment InverseInitialOverlapFourier
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def activeIndices (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (c : Ideal Eis) : Finset ι := (I.biUnion L).filter (fun p=>primes p∣c)

omit [DecidableEq σ] in
theorem activeIndices_mem (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (c : Ideal Eis) {i : σ} (hi : i∈I) {p : ι} (hp : p∈L i) :
    p∈activeIndices primes I L c ↔ primes p∣c := by
  simp only [activeIndices,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,hi,hp⟩)

theorem indexed_mark_active (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (c : Ideal Eis) :
    indexedIdealMark primes I L a c=primeMark I L a (activeIndices primes I L c) := by
  unfold indexedIdealMark primeMark primeSlot
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro p hp
  simp only [activeIndices_mem primes I L c hi hp]

theorem indexed_overlap_separation (g : 𝓢(ℝ,ℂ))
    (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (c : Ideal Eis) (xj xc : ℝ) :
    (∑p∈I.pi L,(∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)*
      g (xj+xc-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*logPhase t xc*
        indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c := by
  simp_rw [indexed_mark_active]
  rw [←overlap_tuple_separation]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [activeIndices_mem primes I L c i.property ((Finset.mem_pi.mp hp) i.val i.property)]

theorem indexed_overlap_integrable (g : 𝓢(ℝ,ℂ))
    (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (c : Ideal Eis) (xj xc : ℝ) :
    Integrable (fun t:ℝ=>density g xj t*logPhase t xc*
      indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c) := by
  simp_rw [indexed_mark_active]
  exact overlap_mode_integrable g I L a y _ xj xc

omit [DecidableEq σ] [DecidableEq ι] in
theorem tuple_gate_product (primes : ι→Ideal Eis) (I : Finset σ)
    (a : σ→ι→ℂ) (p : ∀i∈I,ι) (c : Ideal Eis)
    (hc : Pairwise (Function.onFun IsCoprime (fun i:I=>primes (p i.val i.property)))) :
    (∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)=
      if (∏i∈I.attach,primes (p i.val i.property))∣c then
        ∏i∈I.attach,a i.val (p i.val i.property) else 0 := by
  by_cases h : (∏i∈I.attach,primes (p i.val i.property))∣c
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i hi
    exact ite_eq_left ((Finset.dvd_prod_of_mem (fun i:I=>primes (p i.val i.property)) hi).trans h)
  · rw [ite_eq_right h]
    have hn : ∃i:I,¬primes (p i.val i.property)∣c := by
      by_contra hn
      push Not at hn
      apply h
      exact Finset.prod_dvd_of_coprime (hc.set_pairwise _) (fun i _=>hn i)
    obtain ⟨i,hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_attach _ i) (ite_eq_right hi)

theorem finite_ideal_overlap_separation (g : 𝓢(ℝ,ℂ))
    (primes : ι→Ideal Eis) (I : Finset σ) (L : σ→Finset ι)
    (a : σ→ι→ℂ) (y : σ→ι→ℝ) (C : Finset (Ideal Eis))
    (coefficient : Ideal Eis→ℂ) (xj : ℝ) (xc : Ideal Eis→ℝ) :
    (∑c∈C,coefficient c*
      ∑p∈I.pi L,(∏i∈I.attach,if primes (p i.val i.property)∣c then a i.val (p i.val i.property) else 0)*
        g (xj+xc c-∑i∈I.attach,y i.val (p i.val i.property))) =
      ∫t:ℝ,density g xj t*
        ∑c∈C,coefficient c*logPhase t (xc c)*
          indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c := by
  simp_rw [indexed_overlap_separation]
  simp only [Finset.mul_sum]
  have hi (c:Ideal Eis) : Integrable (fun t:ℝ=>coefficient c*
      (density g xj t*logPhase t (xc c)*indexedIdealMark primes I L
        (fun i p=>a i p*logPhase (-t) (y i p)) c)) :=
    (indexed_overlap_integrable g primes I L a y c xj (xc c)).const_mul _
  have he (c:Ideal Eis) (t:ℝ) : density g xj t*(coefficient c*logPhase t (xc c)*
      indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c)=
      coefficient c*(density g xj t*logPhase t (xc c)*
      indexedIdealMark primes I L (fun i p=>a i p*logPhase (-t) (y i p)) c) := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun c _=>hi c)]
  simp only [integral_const_mul]

end SevenEighths.InverseInitialOverlapIdealFourier

end

end OAI
end OAIOriginalModule0510

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialPoissonBridge
Source SHA256: 1fa14960d39536579bb725bd657b9017e53d9a95af3e0ae6d2eab8cd895af660
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0511


namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseInitialPoissonBridge
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ConcreteTraceCRT EisensteinSchwartzPoisson
open UniqueFactorizationMonoid InverseInitialOverlap
local notation "Eis" => ActualEisensteinCubic.O

def rowPolynomial (F : Finset (Ideal Eis)) (A : Ideal Eis → ℂ) (u : Eis) : ℂ :=
  ∑ I ∈ F, A I * idealRowHom u I

lemma pool_positive (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I) :
    ∀ I ∈ F, I ≠ 0 := fun I hI => (hF I hI).1

lemma pool_good (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I) :
    ∀ I ∈ F, ∀ Q ∈ normalizedFactors I, goodLambda ∉ Q :=
  fun I hI Q hQ => ((hF I hI).2.2 Q hQ).1

lemma pool_char (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I)
    (q : primePool F) : ringChar (Eis ⧸ q.val) ≠ 2 := by
  obtain ⟨I,hI,hq⟩ := mem_primePool_iff.mp q.property
  exact ((hF I hI).2.2 q.val hq).2

theorem idealRowHom_eq_idealSexticRow
    (F : Finset (Ideal Eis)) (hF : ∀ I ∈ F, Admissible I)
    {I : Ideal Eis} (hI : I ∈ F) (u : Eis) :
    idealRowHom u I = idealSexticRow F (pool_positive F hF) (pool_good F hF) I u := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  conv_lhs => rw [← idealSupport_product_eq F hI (hF I hI).2.1]
  rw [map_prod]
  change (∏ q ∈ idealSupport F I, idealRowHom u q.val) =
    ∏ q ∈ idealSupport F I, CompletedGauss.actualSextic q.val (primePool_good F (pool_good F hF) q)
      (Ideal.Quotient.mk q.val u)
  apply Finset.prod_congr rfl
  intro q hq
  exact idealRowHom_prime u q.val (primePool_good F (pool_good F hF) q)

theorem rowPolynomial_eq_finite (F : Finset (Ideal Eis))
    (hF : ∀ I ∈ F, Admissible I) (A : Ideal Eis → ℂ) (u : Eis) :
    rowPolynomial F A u = ∑ I ∈ F, A I *
      idealSexticRow F (pool_positive F hF) (pool_good F hF) I u := by
  apply Finset.sum_congr rfl
  intro I hI
  rw [idealRowHom_eq_idealSexticRow F hF hI]

theorem rowPolynomial_smoothed_summable (F : Finset (Ideal Eis))
    (hF : ∀ I ∈ F, Admissible I) (A : Ideal Eis → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y) *
      (‖rowPolynomial F A u‖^2 : ℝ)) := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  simpa only [rowPolynomial_eq_finite F hF A,idealSexticRow] using
    finiteSquarefreeRow_smoothed_mean_square_summable
      (fun q : primePool F => q.val) (primePool_good F (pool_good F hF))
      F (idealSupport F) A Φ Y hY

theorem rowPolynomial_smoothed_expand (F : Finset (Ideal Eis))
    (hF : ∀ I ∈ F, Admissible I) (A : Ideal Eis → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y) * (‖rowPolynomial F A u‖^2 : ℝ)) =
      ∑ I ∈ F, ∑ J ∈ F, (star (A I)*A J) *
        ∑' u : Eis, (star (idealRowHom u I)*idealRowHom u J)*Φ (‖eisEmbedding u‖^2/Y) := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he := finiteSquarefreeRow_smoothed_mean_square_expand
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF))
    F (idealSupport F) A Φ Y hY
  simp_rw [rowPolynomial_eq_finite F hF A]
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  simp_rw [idealRowHom_eq_idealSexticRow F hF hI, idealRowHom_eq_idealSexticRow F hF hJ]
  rfl

theorem rowPolynomial_smoothed_poisson (F : Finset (Ideal Eis))
    (hF : ∀ I ∈ F, Admissible I) (A : Ideal Eis → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y) * (‖rowPolynomial F A u‖^2 : ℝ)) =
      ∑ I ∈ F, ∑ J ∈ F, (star (A I)*A J) *
        idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) I J Φ Y := by
  rw [rowPolynomial_smoothed_expand F hF A Φ Y hY]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  simp_rw [idealRowHom_eq_idealSexticRow F hF hI, idealRowHom_eq_idealSexticRow F hF hJ]
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  exact finiteSquarefreeRow_pair_radial_poisson
    (fun q : primePool F => q.val) Subtype.val_injective
    (primePool_good F (pool_good F hF)) (pool_char F hF)
    (idealSupport F I) (idealSupport F J) Φ Y hY

theorem indexed_smoothed_poisson {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let F := C.image L
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact hL c hc
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * idealRowHom u (L c)‖^2 : ℝ)) =
      ∑ c ∈ C, ∑ d ∈ C, (star (A c)*A d) *
        idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) (L c) (L d) Φ Y := by
  intro F hF
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he (u : Eis) : (∑ c ∈ C, A c*idealRowHom u (L c)) =
      ∑ c ∈ C, A c*idealSexticRow F (pool_positive F hF) (pool_good F hF) (L c) u := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_image.mpr ⟨c,hc,rfl⟩)]
  simp_rw [he]
  simp only [idealSexticRow]
  rw [finiteSquarefreeRow_smoothed_mean_square_expand
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF))
    C (fun c => idealSupport F (L c)) A Φ Y hY]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  exact finiteSquarefreeRow_pair_radial_poisson
    (fun q : primePool F => q.val) Subtype.val_injective
    (primePool_good F (pool_good F hF)) (pool_char F hF)
    (idealSupport F (L c)) (idealSupport F (L d)) Φ Y hY

theorem indexed_conjugate_smoothed_poisson {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let F := C.image L
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact hL c hc
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * star (idealRowHom u (L c))‖^2 : ℝ)) =
      ∑ c ∈ C, ∑ d ∈ C, (A c*star (A d)) *
        idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) (L c) (L d) Φ Y := by
  intro F hF
  have he (u : Eis) : (∑ c ∈ C, A c * star (idealRowHom u (L c))) =
      star (∑ c ∈ C, star (A c) * idealRowHom u (L c)) := by
    simp only [star_sum,star_mul,star_star,mul_comm]
  simp_rw [he,norm_star]
  simpa only [star_star] using indexed_smoothed_poisson C L hL (fun c => star (A c)) Φ Y hY

theorem indexed_smoothed_summable {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * idealRowHom u (L c)‖^2 : ℝ)) := by
  let F := C.image L
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
    exact hL c hc
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he (u : Eis) : (∑ c ∈ C, A c*idealRowHom u (L c)) =
      ∑ c ∈ C, A c*idealSexticRow F (pool_positive F hF) (pool_good F hF) (L c) u := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_image.mpr ⟨c,hc,rfl⟩)]
  simpa only [he,idealSexticRow] using finiteSquarefreeRow_smoothed_mean_square_summable
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF))
    C (fun c => idealSupport F (L c)) A Φ Y hY

theorem supported_of_dvd {I J : Ideal Eis} (hI : Supported I) (hJI : J ∣ I) : Supported J := by
  obtain ⟨K,rfl⟩ := hJI
  exact (supported_mul_iff J K).mp hI |>.1

theorem columns_admissible (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n)
    {c : Ideal Eis} (hc : c ∈ columns S P j) : Admissible c := by
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hnS,hns,hg⟩ := mem_original.mp hn
  have hjn : j ∣ n := hg ▸ GCDMonoid.gcd_dvd_left n P
  have hs := (supported_mul_iff (idealQuotient j n) (residual P j)).mpr
    ⟨supported_of_dvd (hS n hnS hns) (idealQuotient_dvd hjn),
     supported_of_dvd (admissible_supported hP) (idealQuotient_dvd hj)⟩
  exact ⟨hs.1,(column_properties hP.2.1 hj hns hg).1,hs.2⟩

theorem masked_columns_admissible (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n)
    {c : Ideal Eis} (hc : c ∈ columns S P j) : Admissible (j*c) := by
  have hjA := admissible_of_dvd hP hj
  have hcA := columns_admissible S hP hj hS hc
  have hs := (supported_mul_iff j c).mpr ⟨admissible_supported hjA,admissible_supported hcA⟩
  exact ⟨hs.1,squarefree_mul_iff.mpr
    ⟨((mem_columns hP.2.1 hj).mp hc).2.1.symm.isRelPrime,hjA.2.1,hcA.2.1⟩,hs.2⟩

theorem norm_idealRowHom_four_eq_two (I : Ideal Eis) (hI : Admissible I) (u : Eis) :
    ‖idealRowHom u I‖^4 = ‖idealRowHom u I‖^2 := by
  let F : Finset (Ideal Eis) := {I}
  have hF : ∀ J ∈ F, Admissible J := by
    intro J hJ
    have he : J=I := Finset.mem_singleton.mp hJ
    simpa only [he] using hI
  rw [idealRowHom_eq_idealSexticRow F hF (Finset.mem_singleton_self I)]
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F (pool_positive F hF)
  have he := congrArg norm (finiteSquarefreeRow_self_pair
    (fun q : primePool F => q.val) (primePool_good F (pool_good F hF)) (idealSupport F I) u)
  simp only [norm_mul,norm_star,←pow_two] at he
  change ‖idealSexticRow F (pool_positive F hF) (pool_good F hF) I u‖^2 = _ at he
  have hp : ∀ x : ℝ, x^4=(x^2)^2 := by intro x; ring
  rw [hp,he]
  unfold rowCoprimeMask
  split_ifs <;> norm_num

def heckeIdealCharacter (η : Ideal Eis →* ℂ) (u : Eis) : Ideal Eis →* ℂ :=
  η * (idealRowHom u).toMonoidHom

theorem heckeIdealCharacter_apply (η : Ideal Eis →* ℂ) (u : Eis) (I : Ideal Eis) :
    heckeIdealCharacter η u I = η I * idealRowHom u I := rfl

def originalFixedPolynomial (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    (Z r z : ℝ) (u : Eis) : ℂ :=
  (Z^(-(r+z)/2) : ℝ) * ∑ n ∈ original S P j,
    (moebius n : ℂ) * heckeIdealCharacter η u n * heckeIdealCharacter η u P *
      a n * W ((Ideal.absNorm n : ℝ)/Z^r)

def overlapResidualCoefficient (P j : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) (c : Ideal Eis) : ℂ :=
  (moebius c : ℂ) * η c * a (reconstruct P j c) *
    W ((((Ideal.absNorm j : ℝ)/Z^G)*((Ideal.absNorm c : ℝ)/Z^(r+z-2*G))) /
      ((Ideal.absNorm (residual P j) : ℝ)/Z^(z-G)))

def overlapPrefactor (P j : Ideal Eis) (η : Ideal Eis →* ℂ) (Z r z G : ℝ) : ℂ :=
  (moebius j : ℂ)*(moebius (residual P j) : ℂ)*(Z^(-G) : ℝ)*η j^2*
    (Z^(-(r+z-2*G)/2) : ℝ)

theorem originalFixedPolynomial_eq (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Squarefree P) (hj : j ∣ P) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) (u : Eis) :
    originalFixedPolynomial S P j η a W Z r z u =
      overlapPrefactor P j η Z r z G * (idealRowHom u j)^2 *
        rowPolynomial (columns S P j) (overlapResidualCoefficient P j η a W Z r z G) u := by
  have he := normalized_polynomial_fixed_overlap S hP hj (heckeIdealCharacter η u) a W hZ r z G
  change originalFixedPolynomial S P j η a W Z r z u = _ at he
  rw [he]
  simp only [heckeIdealCharacter_apply,
    rowPolynomial,overlapPrefactor,overlapResidualCoefficient,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem maskedResidual_eq (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (A : Ideal Eis → ℂ) (u : Eis) :
    (∑ c ∈ columns S P j, A c*idealRowHom u (j*c)) =
      idealRowHom u j * rowPolynomial (columns S P j) A u := by
  simp only [map_mul,rowPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

lemma norm_sq_square_factor (r s : ℂ) (h : ‖r‖^4=‖r‖^2) :
    ‖r^2*s‖^2=‖r*s‖^2 := by
  calc
    _ = ‖r‖^4*‖s‖^2 := by simp only [norm_mul,norm_pow]; ring
    _ = ‖r*s‖^2 := by rw [h,norm_mul,mul_pow]

theorem originalFixedPolynomial_norm_sq (S : Finset (Ideal Eis)) {P j : Ideal Eis}
    (hP : Admissible P) (hj : j ∣ P) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) (u : Eis) :
    ‖originalFixedPolynomial S P j η a W Z r z u‖^2 =
      ‖overlapPrefactor P j η Z r z G‖^2 *
        ‖∑ c ∈ columns S P j, overlapResidualCoefficient P j η a W Z r z G c *
          idealRowHom u (j*c)‖^2 := by
  rw [originalFixedPolynomial_eq S hP.2.1 hj η a W hZ r z G,
    maskedResidual_eq,mul_assoc,norm_mul,mul_pow]
  congr 1
  exact norm_sq_square_factor _ _ (norm_idealRowHom_four_eq_two j (admissible_of_dvd hP hj) u)

theorem norm_overlapPrefactor_sq {P j : Ideal Eis} (hP : Squarefree P) (hj : j ∣ P)
    (η : Ideal Eis →* ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ) :
    ‖overlapPrefactor P j η Z r z G‖^2 =
      Z^(-2*G-(r+z-2*G))*‖η j‖^4 := by
  have hjn : ‖(moebius j : ℂ)‖=1 := by simp [(hP.squarefree_of_dvd hj).moebius_eq]
  have hpn : ‖(moebius (residual P j) : ℂ)‖=1 := by simp [(residual_squarefree hP hj).moebius_eq]
  simp only [overlapPrefactor,norm_mul,norm_pow,hjn,hpn,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ (-G)),
    abs_of_pos (Real.rpow_pos_of_pos hZ (-(r+z-2*G)/2))]
  have hs : (Z^(-G))^2*(Z^(-(r+z-2*G)/2))^2=Z^(-2*G-(r+z-2*G)) := by
    rw [←Real.rpow_natCast,←Real.rpow_natCast,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,
      ←Real.rpow_add hZ]
    congr 1
    norm_num
    ring
  calc
    _ = ((Z^(-G))^2*(Z^(-(r+z-2*G)/2))^2)*‖η j‖^4 := by ring
    _ = _ := by rw [hs]

theorem original_fixed_overlap_smoothed_poisson
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let C := columns S P j
    let F := C.image (fun c => j*c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact masked_columns_admissible S hP hj hS hc
    let A := overlapResidualCoefficient P j η a W Z r z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) =
      ((Z^(-2*G-(r+z-2*G))*‖η j‖^4 : ℝ) : ℂ) *
        ∑ c ∈ C, ∑ d ∈ C, (star (A c)*A d) *
          idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) (j*c) (j*d) Φ Y := by
  intro C F hF A
  have he := indexed_smoothed_poisson C (fun c => j*c)
    (fun c hc => masked_columns_admissible S hP hj hS hc) A Φ Y hY
  calc
    _ = ∑' u : Eis, ((Z^(-2*G-(r+z-2*G))*‖η j‖^4 : ℝ) : ℂ) *
        (Φ (‖eisEmbedding u‖^2/Y) * (‖∑ c ∈ C, A c*idealRowHom u (j*c)‖^2 : ℝ)) := by
      apply tsum_congr
      intro u
      rw [originalFixedPolynomial_norm_sq S hP hj η a W hZ r z G,
        norm_overlapPrefactor_sq hP.2.1 hj η hZ r z G,Complex.ofReal_mul]
      ring
    _ = _ := by rw [tsum_mul_left,he]

theorem original_fixed_overlap_smoothed_poisson_zero_split
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let C := columns S P j
    let F := C.image (fun c => j*c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact masked_columns_admissible S hP hj hS hc
    let A := overlapResidualCoefficient P j η a W Z r z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) =
      ((Z^(-2*G-(r+z-2*G))*‖η j‖^4 : ℝ) : ℂ) *
        ∑ c ∈ C, ∑ d ∈ C, (star (A c)*A d) *
          (idealPairPoissonZeroMode F (pool_positive F hF) (pool_good F hF) (j*c) (j*d) Φ Y +
           idealPairPoissonNonzeroMode F (pool_positive F hF) (pool_good F hF) (j*c) (j*d) Φ Y) := by
  intro C F hF A
  rw [original_fixed_overlap_smoothed_poisson S hP hj hS η a W hZ r z G Φ Y hY]
  simp_rw [idealPairPoissonKernel_zero_split _ _ _ _ _ _ _ hY]
  rfl

def residualNormalizedPolynomial (S : Finset (Ideal Eis)) (P j : Ideal Eis)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    (Z r z G : ℝ) (u : Eis) : ℂ :=
  (Z^(-(r+z-2*G)/2) : ℝ) * ∑ c ∈ columns S P j,
    overlapResidualCoefficient P j η a W Z r z G c * star (idealRowHom u c)

lemma norm_rpow_half_sq {Z : ℝ} (hZ : 0 < Z) (D : ℝ) :
    ‖((Z^(-D/2) : ℝ) : ℂ)‖^2=Z^(-D) := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
    ←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1
  norm_num

theorem residual_normalized_smoothed_poisson
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let C := columns S P j
    let F := C.image (fun c => c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact columns_admissible S hP hj hS hc
    let A := overlapResidualCoefficient P j η a W Z r z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) =
      (Z^(-(r+z-2*G)) : ℝ) *
        ∑ c ∈ C, ∑ d ∈ C, (A c*star (A d)) *
          idealPairPoissonKernel F (pool_positive F hF) (pool_good F hF) c d Φ Y := by
  intro C F hF A
  have he := indexed_conjugate_smoothed_poisson C (fun c => c)
    (fun c hc => columns_admissible S hP hj hS hc) A Φ Y hY
  calc
    _ = ∑' u : Eis, (Z^(-(r+z-2*G)) : ℝ) *
        (Φ (‖eisEmbedding u‖^2/Y) * (‖∑ c ∈ C, A c*star (idealRowHom u c)‖^2 : ℝ)) := by
      apply tsum_congr
      intro u
      rw [residualNormalizedPolynomial,norm_mul,mul_pow,norm_rpow_half_sq hZ,Complex.ofReal_mul]
      ring
    _ = _ := by rw [tsum_mul_left,he]

theorem residual_normalized_smoothed_poisson_zero_split
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let C := columns S P j
    let F := C.image (fun c => c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact columns_admissible S hP hj hS hc
    let A := overlapResidualCoefficient P j η a W Z r z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Y)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) =
      (Z^(-(r+z-2*G)) : ℝ) *
        ∑ c ∈ C, ∑ d ∈ C, (A c*star (A d)) *
          (idealPairPoissonZeroMode F (pool_positive F hF) (pool_good F hF) c d Φ Y +
           idealPairPoissonNonzeroMode F (pool_positive F hF) (pool_good F hF) c d Φ Y) := by
  intro C F hF A
  rw [residual_normalized_smoothed_poisson S hP hj hS η a W hZ r z G Φ Y hY]
  simp_rw [idealPairPoissonKernel_zero_split _ _ _ _ _ _ _ hY]
  rfl

theorem original_fixed_overlap_smoothed_summable
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) := by
  have hs := (indexed_smoothed_summable (columns S P j) (fun c => j*c)
    (fun c hc => masked_columns_admissible S hP hj hS hc)
    (overlapResidualCoefficient P j η a W Z r z G) Φ Y hY).mul_left
      ((‖overlapPrefactor P j η Z r z G‖^2 : ℝ) : ℂ)
  apply hs.congr
  intro u
  rw [originalFixedPolynomial_norm_sq S hP hj η a W hZ r z G,Complex.ofReal_mul]
  ring

theorem original_normalized_polynomial_hecke_rows
    (S : Finset (Ideal Eis)) {P : Ideal Eis} (hP : Squarefree P)
    (η : Ideal Eis →* ℂ) (a : Ideal Eis → ℂ) (W : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (r z : ℝ) (G : Ideal Eis → ℝ) (u : Eis) :
    (Z^(-(r+z)/2) : ℝ) * (∑ n ∈ S,
      (moebius n : ℂ)*heckeIdealCharacter η u n*heckeIdealCharacter η u P*
        a n*W ((Ideal.absNorm n : ℝ)/Z^r)) =
      ∑ j ∈ IdealMobiusDivisorSum.idealDivisors P,
        overlapPrefactor P j η Z r z (G j) * (idealRowHom u j)^2 *
          rowPolynomial (columns S P j)
            (overlapResidualCoefficient P j η a W Z r z (G j)) u := by
  rw [original_normalized_polynomial S hP (heckeIdealCharacter η u) a W hZ r z G]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [heckeIdealCharacter_apply,rowPolynomial,overlapPrefactor,
    overlapResidualCoefficient,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem indexed_conjugate_smoothed_summable {β : Type*} (C : Finset β)
    (L : β → Ideal Eis) (hL : ∀ c ∈ C, Admissible (L c)) (A : β → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y) *
      (‖∑ c ∈ C, A c * star (idealRowHom u (L c))‖^2 : ℝ)) := by
  have he (u : Eis) : (∑ c ∈ C, A c * star (idealRowHom u (L c))) =
      star (∑ c ∈ C, star (A c) * idealRowHom u (L c)) := by
    simp only [star_sum,star_mul,star_star,mul_comm]
  simpa only [he,norm_star] using
    indexed_smoothed_summable C L hL (fun c => star (A c)) Φ Y hY

theorem residual_normalized_smoothed_summable
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun u : Eis => Φ (‖eisEmbedding u‖^2/Y)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) := by
  have hs := (indexed_conjugate_smoothed_summable (columns S P j) (fun c => c)
    (fun c hc => columns_admissible S hP hj hS hc)
    (overlapResidualCoefficient P j η a W Z r z G) Φ Y hY).mul_left
      ((Z^(-(r+z-2*G)) : ℝ) : ℂ)
  apply hs.congr
  intro u
  rw [residualNormalizedPolynomial,norm_mul,mul_pow,norm_rpow_half_sq hZ,Complex.ofReal_mul]
  ring

end SevenEighths.InverseInitialPoissonBridge

end

end OAI
end OAIOriginalModule0511

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform
Source SHA256: 61f1b6a4ca9e5d5000557221035f410f3ff61d6ebb1b25da6e45c284a5c09dc2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0512


namespace OAI

namespace SevenEighths.InverseKernelSourceUniform

open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory LocalLogFourier
noncomputable section

def smallScalar (R : ℝ) : ℝ := min 1 (R ^ (1/4 : ℝ))

lemma smallScalar_pos {R : ℝ} (hR : 0 < R) : 0 < smallScalar R :=
  lt_min zero_lt_one (Real.rpow_pos_of_pos hR _)

def canonicalDensity (U : ℝ → ℂ) (V : 𝓢(ℝ, ℂ)) (R t : ℝ) : ℂ :=
  ((smallScalar R : ℝ) : ℂ)⁻¹ *
    (𝓕 (fun s : ℝ => U s * CubicReflectionKernel.paperKernel V (R * Real.exp s))) t

theorem paperKernel_window_source_bound (a b : ℝ) (ha : 0 < a) (K : ℕ) (L : ℝ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ R : ℝ, 0 < R → ∀ j ≤ K, ∀ s : ℝ, |s| ≤ L →
      ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R * Real.exp s)‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V * smallScalar R := by
  choose orders c hc hb using fun j : Fin (K+1) =>
    CubicReflectionKernel.paperKernel_euler_source_power_decay a b ha 0 j.val
  let S := Finset.univ.biUnion orders
  let D := (∑ j : Fin (K+1), c j) + 1
  let E := (Real.exp L) ^ (1/4 : ℝ)
  have hD : 0 < D := by
    have hh := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin (K+1)))) => (hc j).le)
    dsimp only [D]
    linarith
  have hE : 0 < E := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hcD (j : Fin (K+1)) : c j ≤ D := by
    have hh := Finset.single_le_sum
      (fun q (_ : q ∈ (Finset.univ : Finset (Fin (K+1)))) => (hc q).le) (Finset.mem_univ j)
    dsimp only [D]
    linarith
  refine ⟨S, D*(1+E), by positivity, ?_⟩
  intro V hV R hR j hj s hs
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let q : Fin (K+1) := ⟨j, Nat.lt_succ_iff.mpr hj⟩
  have hsource : c q * (orders q).sup (schwartzSeminormFamily ℝ ℝ ℂ) V ≤ D*Q := by
    have hsub : orders q ⊆ S := Finset.subset_biUnion_of_mem orders (Finset.mem_univ q)
    exact mul_le_mul (hcD q) (Seminorm.le_def.mp (Finset.sup_mono hsub) V)
      (by positivity) hD.le
  have hsmall := (hb q V hV (R*Real.exp s) (mul_pos hR (Real.exp_pos _))).1
  have hlarge := (hb q V hV (R*Real.exp s) (mul_pos hR (Real.exp_pos _))).2
  have hsmall' : ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R*Real.exp s)‖ ≤
      D*(1+E)*Q * R^(1/4 : ℝ) := by
    have he : (Real.exp s)^(1/4 : ℝ) ≤ E :=
      Real.rpow_le_rpow (by positivity) (Real.exp_le_exp.mpr ((le_abs_self s).trans hs)) (by norm_num)
    rw [Real.mul_rpow hR.le (Real.exp_pos _).le] at hsmall
    calc
      _ ≤ (c q * (orders q).sup (schwartzSeminormFamily ℝ ℝ ℂ) V) *
          (R^(1/4 : ℝ) * (Real.exp s)^(1/4 : ℝ)) := hsmall
      _ ≤ (D*Q) * (R^(1/4 : ℝ) * E) := mul_le_mul hsource
          (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hR.le _)) (by positivity) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hQ (Real.rpow_nonneg hR.le (1/4 : ℝ))]
  have hlarge' : ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R*Real.exp s)‖ ≤ D*(1+E)*Q := by
    have hh : ‖eulerDeriv (CubicReflectionKernel.paperKernel V) j (R*Real.exp s)‖ ≤ D*Q := by
      apply (le_trans ?_ hsource)
      simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] using hlarge
    exact hh.trans (by nlinarith [mul_nonneg (mul_nonneg hD.le hE.le) hQ])
  change _ ≤ D*(1+E)*Q * min 1 (R^(1/4 : ℝ))
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ D*(1+E)*Q), mul_one]
  exact le_min hlarge' hsmall'

private theorem localized_source_seminorm
    (V F : ℝ → ℂ) (R L CW CF : ℝ) (n k : ℕ)
    (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (hF : ContDiffOn ℝ ∞ F (Set.Ioi 0)) (hR : 0 < R)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ n, ∀ s, ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s, (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) → |s| ≤ L)
    (hEuler : ∀ i ≤ n, ∀ s, |s| ≤ L → ‖eulerDeriv F i (R * Real.exp s)‖ ≤ CF) :
    (SchwartzMap.seminorm ℝ k n) (positiveLogProfile V F R hVc hVs hF hR) ≤
      L ^ k * derivativeConstant n CW CF := by
  let g := positiveLogProfile V F R hVc hVs hF hR
  let G : ℝ → ℂ := fun z => F (R * Real.exp z)
  have hG : ContDiff ℝ ∞ G := by
    apply hF.comp_contDiff (by fun_prop)
    intro z
    exact mul_pos hR (Real.exp_pos _)
  have hgeq : (g : ℝ → ℂ) = fun z => V z * G z := by
    funext z
    exact positiveLogProfile_apply V F R z hVc hVs hF hR
  have hD : 0 ≤ derivativeConstant n CW CF := derivativeConstant_nonneg _ _ _ hCW hCF
  apply SchwartzMap.seminorm_le_bound' ℝ k n g (mul_nonneg (pow_nonneg hL _) hD)
  intro s
  have hprod := norm_iteratedFDeriv_mul_le hVs hG s (n := n) (by simp)
  by_cases hs : ∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0
  · have hwindow' := hwindow s hs
    have hraw : ‖iteratedDeriv n g s‖ ≤ derivativeConstant n CW CF := by
      rw [hgeq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      apply hprod.trans
      unfold derivativeConstant
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hGi : ‖iteratedFDeriv ℝ (n - i) G s‖ ≤ CF := by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, show (G : ℝ → ℂ) = fun z => F (R * Real.exp z) from rfl,
          iteratedDeriv_log_eq_euler]
        exact hEuler (n - i) (Nat.sub_le _ _) s hwindow'
      gcongr
      exact hVderiv i hi' s
    have hsk : ‖s‖ ^ k ≤ L ^ k := by simpa only [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg s) hwindow' k
    exact mul_le_mul hsk hraw (norm_nonneg _) (pow_nonneg hL _)
  · have hz (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i V s‖ = 0 := by
      by_contra hne
      exact hs ⟨i, hi, hne⟩
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i V s‖ *
        ‖iteratedFDeriv ℝ (n - i) G s‖) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      ring
    have hgzero : ‖iteratedDeriv n g s‖ = 0 := by
      rw [hgeq, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact le_antisymm (hprod.trans_eq hsum) (norm_nonneg _)
    rw [hgzero, mul_zero]
    positivity

theorem source_uniform_separation {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 < a)
    (windows : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hwindows : ∀ i y, windows i y ≠ 0 → |y| ≤ M i)
    (J : ℕ) :
    ∃ (U : ℝ → ℂ) (S : Finset (ℕ × ℕ)) (C : ℝ),
      0 ≤ C ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ V : 𝓢(ℝ, ℂ), Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b →
      ∀ R : ℝ, 0 < R →
      (∀ y : ι → ℝ,
        (∏ i, windows i (y i)) * CubicReflectionKernel.paperKernel V
          (R * Real.exp (∑ i, slope i * y i)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (∏ i, windows i (y i) * FourierBridge.logPhase t (slope i * y i)) *
            canonicalDensity U V R t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖) ∧
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖) ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V ∧
      (∀ t : ℝ, (1 + ‖t‖)^J * ‖canonicalDensity U V R t‖ ≤
        C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V) := by
  let T := ∑ i, |slope i| * M i
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hM i))
  let K := J + (volume : Measure ℝ).integrablePower
  let L := T+1
  have hL : 0 ≤ L := by dsimp only [L]; linarith
  obtain ⟨U, CW, hUc, hUs, hUone, hCW, hUderiv, hwindow⟩ :=
    FourierBridge.exists_complex_smooth_cutoff_with_derivative_bounds T K hT
  obtain ⟨S, CF, hCF, hkernel⟩ := paperKernel_window_source_bound a b ha K L
  let P0 := momentConstant K L CW CF
  let B0 := (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 P0 +
    FourierBridge.coefficientMomentBound J P0)
  let B1 := FourierBridge.fourierPointBound J P0
  have hP0 : 0 ≤ P0 := momentConstant_nonneg K L CW CF hL hCW hCF.le
  have hB0 : 0 ≤ B0 := mul_nonneg (by positivity) (add_nonneg
    (FourierBridge.coefficientMomentBound_nonneg 0 P0 hP0)
    (FourierBridge.coefficientMomentBound_nonneg J P0 hP0))
  have hB1 : 0 ≤ B1 := FourierBridge.fourierPointBound_nonneg J P0 hP0
  refine ⟨U, S, B0+B1, add_nonneg hB0 hB1, hUc, hUs, ?_⟩
  intro V hV R hR
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  let m := smallScalar R
  have hm : 0 < m := smallScalar_pos hR
  have hF := CubicReflectionKernel.paperKernel_compact_source_smooth V a b ha hV (V.smooth ⊤)
  let g := positiveLogProfile U (CubicReflectionKernel.paperKernel V) R hUc hUs hF hR
  let B : 𝓢(ℝ, ℂ) := ((m : ℂ)⁻¹) • (𝓕 g)
  have hcan (t : ℝ) : B t = canonicalDensity U V R t := by
    rfl
  have hnorm (t : ℝ) : ‖B t‖ = m⁻¹ * ‖(𝓕 g) t‖ := by
    simp only [B, smul_apply, smul_eq_mul, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  have hP : 0 ≤ P0*Q := mul_nonneg hP0 hQ
  have hsource (n : ℕ) (hn : n ≤ K) : m⁻¹ *
      ((SchwartzMap.seminorm ℝ 0 n) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g) ≤ P0*Q := by
    have hsemi (k : ℕ) : (SchwartzMap.seminorm ℝ k n) g ≤
        L^k * derivativeConstant n CW (CF*Q*m) := by
      apply localized_source_seminorm U (CubicReflectionKernel.paperKernel V)
        R L CW (CF*Q*m) n k hUc hUs hF hR hL hCW (by positivity)
      · intro i hi
        exact hUderiv i (hi.trans hn)
      · intro s hs
        exact (hwindow s (by obtain ⟨i, hi, hz⟩ := hs; exact ⟨i, hi.trans hn, hz⟩)).2.2
      · intro i hi s hs
        exact hkernel V hV R hR i (hi.trans hn) s hs
    have hd : derivativeConstant n CW (CF*Q*m) = derivativeConstant n CW CF * Q * m := by
      simp only [derivativeConstant, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hs : (SchwartzMap.seminorm ℝ 0 n) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n) g ≤ (P0*Q)*m := by
      calc
        _ ≤ L^0 * derivativeConstant n CW (CF*Q*m) +
            L^(volume : Measure ℝ).integrablePower * derivativeConstant n CW (CF*Q*m) :=
          add_le_add (hsemi 0) (hsemi _)
        _ = ((1+L^(volume : Measure ℝ).integrablePower)*derivativeConstant n CW CF)*Q*m := by
          rw [hd]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (momentConstant_dominates K n L CW CF hL hCW hCF.le hn) hQ) hm.le
    exact (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hm.le)).trans_eq (by field_simp)
  have hB0Q : (2 : ℝ)^J * (FourierBridge.coefficientMomentBound 0 (P0*Q) +
      FourierBridge.coefficientMomentBound J (P0*Q)) = B0*Q := by
    dsimp only [B0]
    unfold FourierBridge.coefficientMomentBound
    ring
  have hB1Q : FourierBridge.fourierPointBound J (P0*Q) = B1*Q := by
    dsimp only [B1]
    unfold FourierBridge.fourierPointBound FourierBridge.fourierSeminormBound
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    have hactive : (∏ i, windows i (y i)) ≠ 0 → U (∑ i, slope i*y i) = 1 :=
      FourierBridge.coupled_cutoff_active windows U slope y M hwindows (by simpa [T] using hUone)
    have hsep := coupled_positive_log_separation windows (CubicReflectionKernel.paperKernel V)
      U R slope y hUc hUs hF hR hactive
    rw [hsep, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    rw [← hcan]
    dsimp only [B]
    simp only [smul_apply, smul_eq_mul]
    have hmC : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm.ne'
    change _ = (m : ℂ)*_
    field_simp
    rfl
  · simp_rw [← hcan, hnorm]
    exact AnalyticBridge.schwartz_fourier_one_plus_integrable g J |>.const_mul m⁻¹ |>.congr
      (Filter.Eventually.of_forall (fun t => by dsimp only; ring))
  · simp_rw [← hcan, hnorm]
    have hh := FourierBridge.uniform_fourier_one_plus_moment g J m⁻¹ (P0*Q)
      (inv_nonneg.mpr hm.le) hP hsource
    rw [hB0Q] at hh
    have he : (∫ t : ℝ, (1+‖t‖)^J * (m⁻¹ * ‖(𝓕 g) t‖)) =
        m⁻¹ * ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 g) t‖ := by
      simp_rw [← mul_assoc, mul_comm ((1+‖_‖)^J) m⁻¹, mul_assoc]
      rw [integral_const_mul]
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB1) hQ)
  · intro t
    rw [← hcan, hnorm]
    have hh := FourierBridge.uniform_fourier_pointwise g J m⁻¹ (P0*Q)
      (inv_nonneg.mpr hm.le) hP (fun i hi => hsource i (hi.trans (by dsimp only [K]; omega))) t
    rw [hB1Q] at hh
    have he : (1+‖t‖)^J*(m⁻¹*‖(𝓕 g) t‖) = m⁻¹*(1+‖t‖)^J*‖(𝓕 g) t‖ := by ring
    rw [he]
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB0) hQ)

def twistedDensity (U W : ℝ → ℂ) (θ R t : ℝ) : ℂ :=
  (smallScalar R : ℂ)⁻¹ *
    (𝓕 (fun s : ℝ => U s * CubicReflectionKernel.paperKernel
      (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ)) (R * Real.exp s))) t

theorem normTwistedSource_uniform_separation {ι : Type*} [Fintype ι]
    (a b : ℝ) (ha : 0 < a)
    (windows : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hwindows : ∀ i y, windows i y ≠ 0 → |y| ≤ M i)
    (W : ℝ → ℂ) (hsupp : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃ (U : ℝ → ℂ) (n : ℕ) (C : ℝ),
      0 ≤ C ∧ HasCompactSupport U ∧ ContDiff ℝ ∞ U ∧
      ∀ θ R : ℝ, 0 < R →
      (∀ y : ι → ℝ,
        (∏ i, windows i (y i)) * CubicReflectionKernel.paperKernel
          (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ))
          (R * Real.exp (∑ i, slope i * y i)) =
        (smallScalar R : ℂ) * ∫ t : ℝ,
          (∏ i, windows i (y i) * FourierBridge.logPhase t (slope i * y i)) *
            twistedDensity U W θ R t) ∧
      Integrable (fun t : ℝ => (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖) ∧
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖) ≤ C * (1 + ‖θ‖)^n ∧
      (∀ t : ℝ, (1 + ‖t‖)^J * ‖twistedDensity U W θ R t‖ ≤ C * (1 + ‖θ‖)^n) := by
  obtain ⟨U, orders, C, hC, hUc, hUs, hsep⟩ :=
    source_uniform_separation a b ha windows slope M hM hwindows J
  let V := CompletedGauss.vstarSchwartz W a b ha hsupp hW
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b :=
    CompletedGauss.Vstar_support W a b hsupp
  obtain ⟨G, hG, hbound⟩ := CompletedHeight.normTwistedSource_schwartz V a b ha hV
  have hlink (θ : ℝ) : (G θ : ℝ → ℂ) =
      CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hG θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x) =
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hGs (θ : ℝ) : Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b := by
    intro x hx
    change G θ x ≠ 0 at hx
    rw [hG θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  obtain ⟨n, D, hD, hpoly⟩ := hbound orders
  refine ⟨U, n, C*D, mul_nonneg hC hD.le, hUc, hUs, ?_⟩
  intro θ R hR
  have hcan : canonicalDensity U (G θ) R = twistedDensity U W θ R := by
    unfold canonicalDensity twistedDensity
    rw [hlink θ]
  obtain ⟨heq, hi, hm, hp⟩ := hsep (G θ) (hGs θ) R hR
  rw [hcan] at heq hi hm hp
  rw [hlink θ] at heq
  have hb : C * orders.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G θ) ≤
      C*D * (1+‖θ‖)^n :=
    (mul_le_mul_of_nonneg_left (hpoly θ) hC).trans_eq (by ring)
  exact ⟨heq, hi, hm.trans hb, fun t => (hp t).trans hb⟩

theorem fourier_joint_stronglyMeasurable {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable (fun p : α × ℝ => (𝓕 (f p.1)) p.2) := by
  simp_rw [Real.fourier_eq']
  apply StronglyMeasurable.integral_prod_right
  have he : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((↑(-2 * Real.pi * inner ℝ p.1 p.2) : ℂ) * Complex.I)) := by
    fun_prop
  exact (he.stronglyMeasurable.comp_measurable
    (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).smul
    (hf.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

theorem paperKernel_joint_stronglyMeasurable {α : Type*} [MeasurableSpace α]
    (a b : ℝ) (ha : 0 < a) (V : α → 𝓢(ℝ, ℂ))
    (hV : ∀ θ, Function.support (V θ : ℝ → ℂ) ⊆ Set.Icc a b)
    (hf : StronglyMeasurable (fun p : α × ℝ => V p.1 (Real.exp p.2))) :
    StronglyMeasurable (fun p : α × Set.Ioi (0 : ℝ) =>
      CubicReflectionKernel.paperKernel (V p.1) p.2) := by
  let f : α → ℝ → ℂ := fun θ s => V θ (Real.exp s)
  let g : α → ℝ → ℂ := fun θ u => CubicReflectionKernel.axisMultiplier u * (𝓕 (f θ)) u
  have hfF := fourier_joint_stronglyMeasurable f hf
  have hg : StronglyMeasurable (Function.uncurry g) :=
    (CubicReflectionKernel.axisMultiplier_continuous.stronglyMeasurable.comp_measurable
      measurable_snd).mul hfF
  have hgF := fourier_joint_stronglyMeasurable g hg
  have harg : Measurable (fun p : α × Set.Ioi (0 : ℝ) =>
      (p.1, Real.log (CubicReflectionKernel.paperScale * (p.2 : ℝ)))) :=
    measurable_fst.prodMk (Real.measurable_log.comp
      (measurable_const.mul (measurable_subtype_coe.comp measurable_snd)))
  convert hgF.comp_measurable harg using 1
  funext p
  let L := CubicReflectionKernel.logSchwartz (V p.1) a b ha (hV p.1) ((V p.1).smooth ⊤)
  exact CubicReflectionKernel.paperKernel_eq_logFourier (V p.1) L
    (fun _ => rfl) p.2 p.2.property

private theorem twistedDensity_measurable_of_profile
    (U W : ℝ → ℂ) (R : ℝ)
    (hprofile : StronglyMeasurable (fun p : ℝ × ℝ =>
      U p.2 * CubicReflectionKernel.paperKernel
        (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W p.1)) (R * Real.exp p.2))) :
    StronglyMeasurable (fun p : ℝ × ℝ => twistedDensity U W p.1 R p.2) := by
  unfold twistedDensity
  exact stronglyMeasurable_const.mul (fourier_joint_stronglyMeasurable
    (fun θ s => U s * CubicReflectionKernel.paperKernel
      (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ)) (R * Real.exp s)) hprofile)

private theorem exists_measurable_twisted_source
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃ G : ℝ → 𝓢(ℝ, ℂ),
      (∀ θ, (G θ : ℝ → ℂ) = CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ)) ∧
      (∀ θ, Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b) ∧
      StronglyMeasurable (fun p : ℝ × ℝ => G p.1 (Real.exp p.2)) := by
  let V := CompletedGauss.vstarSchwartz W a b ha hsupp hW
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Icc a b :=
    CompletedGauss.Vstar_support W a b hsupp
  obtain ⟨G, hG, _⟩ := CompletedHeight.normTwistedSource_schwartz V a b ha hV
  have hlink (θ : ℝ) : (G θ : ℝ → ℂ) =
      CompletedGauss.Vstar (CompletedHeight.normTwistedSource W θ) := by
    funext x
    rw [hG θ x]
    change FourierBridge.logPhase θ (Real.log x)*((Real.sqrt x:ℂ)*W x) =
      (Real.sqrt x:ℂ)*(FourierBridge.logPhase θ (Real.log x)*W x)
    ring
  have hGs (θ : ℝ) : Function.support (G θ : ℝ → ℂ) ⊆ Set.Icc a b := by
    intro x hx
    change G θ x ≠ 0 at hx
    rw [hG θ x] at hx
    exact hV (CompletedHeight.normTwistedSource_support V θ hx)
  have hf : StronglyMeasurable (fun p : ℝ × ℝ => G p.1 (Real.exp p.2)) := by
    simp_rw [hG, CompletedHeight.normTwistedSource, Real.log_exp]
    apply Continuous.stronglyMeasurable
    unfold FourierBridge.logPhase
    exact (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Complex.exp ((↑(2*Real.pi*p.1*p.2) : ℂ)*Complex.I))).mul
      (V.continuous.comp (Real.continuous_exp.comp continuous_snd))
  exact ⟨G, hlink, hGs, hf⟩

theorem twistedDensity_joint_stronglyMeasurable
    (U W : ℝ → ℂ) (hU : Measurable U)
    (a b : ℝ) (ha : 0 < a) (hsupp : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (R : ℝ) (hR : 0 < R) :
    StronglyMeasurable (fun p : ℝ × ℝ => twistedDensity U W p.1 R p.2) := by
  obtain ⟨G, hlink, hGs, hf⟩ := exists_measurable_twisted_source W a b ha hsupp hW
  have hkernel := paperKernel_joint_stronglyMeasurable a b ha G hGs hf
  have harg : Measurable (fun p : ℝ × ℝ =>
      (p.1, (⟨R * Real.exp p.2, mul_pos hR (Real.exp_pos _)⟩ : Set.Ioi (0 : ℝ)))) :=
    measurable_fst.prodMk ((measurable_const.mul (Real.measurable_exp.comp measurable_snd)).subtype_mk)
  have hcomposed := hkernel.comp_measurable harg
  change StronglyMeasurable (fun p : ℝ × ℝ =>
    CubicReflectionKernel.paperKernel (G p.1) (R * Real.exp p.2)) at hcomposed
  have hprofile : StronglyMeasurable (fun p : ℝ × ℝ =>
      U p.2 * CubicReflectionKernel.paperKernel
        (CompletedGauss.Vstar (CompletedHeight.normTwistedSource W p.1)) (R*Real.exp p.2)) := by
    have hprofileG : StronglyMeasurable (fun p : ℝ × ℝ =>
        U p.2 * CubicReflectionKernel.paperKernel (G p.1) (R * Real.exp p.2)) :=
      (hU.stronglyMeasurable.comp_measurable measurable_snd).mul
        hcomposed
    convert hprofileG using 1
    exact funext (fun p => congrArg
      (fun V : ℝ → ℂ => U p.2 * CubicReflectionKernel.paperKernel V (R * Real.exp p.2))
      (hlink p.1).symm)
  exact twistedDensity_measurable_of_profile U W R hprofile

end
end SevenEighths.InverseKernelSourceUniform

end OAI
end OAIOriginalModule0512

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.AmbientProfileTower
Source SHA256: b37c1388089d04d55a03d1674eb3a8c090f9e93a523a9cbeba0af1a926bc8ed5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0513





namespace OAI

namespace SevenEighths.InverseAmbientProfileTower
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open SevenEighths.InverseMoment
noncomputable section

theorem frequencyTwist_fourier_joint_stronglyMeasurable (g : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : ℝ × ℝ => (𝓕 (frequencyTwist g p.1)) p.2) := by
  have hf : StronglyMeasurable
      (fun p : ℝ × ℝ => frequencyTwist g p.1 p.2) := by
    simp only [frequencyTwist_apply]
    apply Continuous.stronglyMeasurable
    unfold logPhase
    fun_prop
  exact InverseKernelSourceUniform.fourier_joint_stronglyMeasurable
    (fun θ => (frequencyTwist g θ : ℝ → ℂ)) hf

theorem logSource_fourier_joint_stronglyMeasurable
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    StronglyMeasurable (fun p : ℝ × ℝ =>
      (𝓕 (frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) p.1)) p.2) :=
  frequencyTwist_fourier_joint_stronglyMeasurable _

theorem twistedTriple_joint_stronglyMeasurable (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × Frequency =>
      tripleCoefficient (𝓕 (frequencyTwist g₁ p.1.1))
        (𝓕 (frequencyTwist g₂ p.1.2)) b₃ p.2) := by
  unfold tripleCoefficient
  exact ((frequencyTwist_fourier_joint_stronglyMeasurable g₁).comp_measurable
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))).mul
      (((frequencyTwist_fourier_joint_stronglyMeasurable g₂).comp_measurable
      ((measurable_snd.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd)))).mul
      (b₃.continuous.stronglyMeasurable.comp_measurable
        (measurable_snd.comp (measurable_snd.comp measurable_snd))))

abbrev Ambient (ι : Type*) := Frequency × (ι → ℝ)

def ambientWeight {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) : ℝ :=
  ((1 + ‖p.1.1‖)^J * (1 + ‖p.1.2.1‖)^J * (1 + ‖p.1.2.2‖)^J) *
    ∏ i, (1 + ‖p.2 i‖)^J

theorem ambientWeight_eq_pow {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) :
    ambientWeight J p = (ambientWeight 1 p)^J := by
  simp [ambientWeight, mul_pow, Finset.prod_pow]

theorem ambientWeight_one_le {ι : Type*} [Fintype ι] (J : ℕ) (p : Ambient ι) :
    1 ≤ ambientWeight J p := by
  unfold ambientWeight
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg p.1.1]))
        (one_le_pow₀ (by linarith [norm_nonneg p.1.2.1])))
        (one_le_pow₀ (by linarith [norm_nonneg p.1.2.2])))
    (Finset.one_le_prod₀ (fun i _ => one_le_pow₀ (by linarith [norm_nonneg (p.2 i)])))

theorem ambientWeight_add {ι : Type*} [Fintype ι] (J K : ℕ) (p : Ambient ι) :
    ambientWeight (J + K) p = ambientWeight J p * ambientWeight K p := by
  rw [ambientWeight_eq_pow (J+K), ambientWeight_eq_pow J, ambientWeight_eq_pow K, pow_add]

def inheritedLeft {ι : Type*} (i : ι) (p : Ambient ι) : ℝ :=
  p.2 i + p.1.1 - p.1.2.2

def inheritedRight {ι : Type*} (i : ι) (p : Ambient ι) : ℝ :=
  -(p.2 i + p.1.2.1 - p.1.2.2)

private theorem one_add_norm_add_le (x y : ℝ) :
    1 + ‖x + y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
  have h := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  nlinarith [mul_nonneg hx hy]

private theorem coordinate_factor_le {ι : Type*} [Fintype ι]
    (i : ι) (u : ι → ℝ) :
    1 + ‖u i‖ ≤ ∏ j, (1 + ‖u j‖) :=
  by
  have hm (j : ι) : max (1 + ‖u j‖) 1 = 1 + ‖u j‖ :=
    max_eq_left (by linarith [norm_nonneg (u j)])
  simpa only [hm] using
    Finset.le_prod_max_one (Finset.mem_univ i) (fun j => 1 + ‖u j‖)

theorem inheritedLeft_bound {ι : Type*} [Fintype ι] (i : ι) (p : Ambient ι) :
    1 + ‖inheritedLeft i p‖ ≤ ambientWeight 1 p := by
  have h := (one_add_norm_add_le (p.2 i + p.1.1) (-p.1.2.2)).trans
    (mul_le_mul_of_nonneg_right (one_add_norm_add_le (p.2 i) p.1.1) (by positivity))
  simp only [norm_neg, ← sub_eq_add_neg] at h
  have hc := coordinate_factor_le i p.2
  have ht : (1 + ‖p.1.1‖) * (1 + ‖p.1.2.2‖) ≤
      (1 + ‖p.1.1‖) * (1 + ‖p.1.2.1‖) * (1 + ‖p.1.2.2‖) := by
    nlinarith [norm_nonneg p.1.1, norm_nonneg p.1.2.1, norm_nonneg p.1.2.2,
      mul_nonneg (mul_nonneg (show 0 ≤ 1 + ‖p.1.1‖ by positivity)
        (norm_nonneg p.1.2.1)) (show 0 ≤ 1 + ‖p.1.2.2‖ by positivity)]
  have hh := mul_le_mul hc ht (by positivity)
    (Finset.prod_nonneg (fun j _ => by positivity))
  change _ ≤ (∏ j, (1 + ‖p.2 j‖)) * _ at hh
  exact h.trans (by simpa [ambientWeight, inheritedLeft, mul_comm, mul_left_comm, mul_assoc] using hh)

theorem inheritedRight_bound {ι : Type*} [Fintype ι] (i : ι) (p : Ambient ι) :
    1 + ‖inheritedRight i p‖ ≤ ambientWeight 1 p := by
  have h := inheritedLeft_bound i ((p.1.2.1, p.1.1, p.1.2.2), p.2)
  change 1 + ‖-(p.2 i + p.1.2.1 - p.1.2.2)‖ ≤ _
  rw [norm_neg]
  simpa [inheritedLeft, ambientWeight, mul_comm, mul_left_comm, mul_assoc] using h

theorem inherited_pair_weight_bound {ι : Type*} [Fintype ι]
    (i j : ι) (J K : ℕ) (p : Ambient ι) :
    ambientWeight J p * ((1 + ‖inheritedLeft i p‖)^K *
      (1 + ‖inheritedRight j p‖)^K) ≤ ambientWeight (J + 2*K) p := by
  have h₁ := pow_le_pow_left₀ (by positivity) (inheritedLeft_bound i p) K
  have h₂ := pow_le_pow_left₀ (by positivity) (inheritedRight_bound j p) K
  have hh := mul_le_mul h₁ h₂ (by positivity)
    (pow_nonneg (le_trans zero_le_one (ambientWeight_one_le 1 p)) K)
  rw [← pow_add] at hh
  rw [ambientWeight_add, ambientWeight_eq_pow (2*K)]
  exact mul_le_mul_of_nonneg_left (by simpa [two_mul] using hh)
    (le_trans zero_le_one (ambientWeight_one_le J p))

theorem ambientWeight_continuous {ι : Type*} [Fintype ι] (J : ℕ) :
    Continuous (ambientWeight (ι := ι) J) := by
  unfold ambientWeight
  fun_prop

theorem inheritedLeft_continuous {ι : Type*} (i : ι) :
    Continuous (inheritedLeft i) := by unfold inheritedLeft; fun_prop

theorem inheritedRight_continuous {ι : Type*} (i : ι) :
    Continuous (inheritedRight i) := by unfold inheritedRight; fun_prop

private theorem inheritedParameter_measurable {ι κ : Type*} (i j : ι) :
    Measurable (fun z : Ambient ι × Ambient κ =>
      ((inheritedLeft i z.1,inheritedRight j z.1),z.2)) := by
  unfold inheritedLeft inheritedRight
  fun_prop

private theorem conditional_tower_integrable
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (J K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (B : Ambient ι → ℂ) (hB : StronglyMeasurable B)
    (D : Ambient ι → Ambient κ → ℂ)
    (hD : StronglyMeasurable (Function.uncurry D))
    (hi : ∀ p, Integrable (fun q => ambientWeight J q * ‖D p q‖))
    (hb : ∀ p, (∫ q, ambientWeight J q * ‖D p q‖) ≤
      C * ((1 + ‖inheritedLeft i p‖)^K * (1 + ‖inheritedRight j p‖)^K))
    (houter : Integrable (fun p => ambientWeight (J+2*K) p * ‖B p‖)) :
    Integrable (fun z : Ambient ι × Ambient κ =>
      ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖) := by
  let f : Ambient ι × Ambient κ → ℝ := fun z =>
    ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖
  have hf_nonneg (z) : 0 ≤ f z := by
    dsimp only [f]
    exact mul_nonneg (mul_nonneg
      (le_trans zero_le_one (ambientWeight_one_le J z.1))
      (le_trans zero_le_one (ambientWeight_one_le J z.2))) (norm_nonneg _)
  have hsm : StronglyMeasurable f :=
    (((ambientWeight_continuous J).comp continuous_fst).stronglyMeasurable.mul
      ((ambientWeight_continuous J).comp continuous_snd).stronglyMeasurable).mul
        ((hB.comp_measurable measurable_fst).mul hD).norm
  apply (integrable_prod_iff hsm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun p => by
      convert (hi p).const_mul (ambientWeight J p * ‖B p‖) using 1
      funext q; dsimp only [f]; rw [norm_mul]; ring)
  · apply (houter.const_mul C).mono' (hsm.norm.integral_prod_right').aestronglyMeasurable
    filter_upwards with p
    have he : (∫ q, ‖f (p,q)‖) =
        ambientWeight J p * ‖B p‖ * (∫ q, ambientWeight J q * ‖D p q‖) := by
      simp_rw [Real.norm_of_nonneg (hf_nonneg _)]
      have heq (q) : f (p,q) =
          (ambientWeight J p * ‖B p‖) * (ambientWeight J q * ‖D p q‖) := by
        dsimp only [f]; rw [norm_mul]; ring
      simp_rw [heq]
      exact integral_const_mul _ _
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
    calc
      _ ≤ ambientWeight J p * ‖B p‖ *
          (C * ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) :=
        mul_le_mul_of_nonneg_left (hb p)
          (mul_nonneg (le_trans zero_le_one (ambientWeight_one_le J p)) (norm_nonneg _))
      _ = (C * ‖B p‖) * (ambientWeight J p *
          ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) := by ring
      _ ≤ (C * ‖B p‖) * ambientWeight (J+2*K) p :=
        mul_le_mul_of_nonneg_left (inherited_pair_weight_bound i j J K p)
          (mul_nonneg hC (norm_nonneg _))
      _ = C * (ambientWeight (J+2*K) p * ‖B p‖) := by ring

private theorem conditional_tower_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (J K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (B : Ambient ι → ℂ) (hB : StronglyMeasurable B)
    (D : Ambient ι → Ambient κ → ℂ)
    (hD : StronglyMeasurable (Function.uncurry D))
    (hi : ∀ p, Integrable (fun q => ambientWeight J q * ‖D p q‖))
    (hb : ∀ p, (∫ q, ambientWeight J q * ‖D p q‖) ≤
      C * ((1 + ‖inheritedLeft i p‖)^K * (1 + ‖inheritedRight j p‖)^K))
    (houter : Integrable (fun p => ambientWeight (J+2*K) p * ‖B p‖)) :
    (∫ z : Ambient ι × Ambient κ,
      ambientWeight J z.1 * ambientWeight J z.2 * ‖B z.1 * D z.1 z.2‖) ≤
      C * (∫ p, ambientWeight (J+2*K) p * ‖B p‖) := by
  have hprod := conditional_tower_integrable i j J K C hC B hB D hD hi hb houter
  rw [Measure.volume_eq_prod, integral_prod _ hprod, ← integral_const_mul]
  apply integral_mono hprod.integral_prod_left (houter.const_mul C)
  intro p
  have he (q) : ambientWeight J p * ambientWeight J q * ‖B p * D p q‖ =
      (ambientWeight J p * ‖B p‖) * (ambientWeight J q * ‖D p q‖) := by
    rw [norm_mul]; ring
  simp_rw [he]
  rw [integral_const_mul]
  calc
    _ ≤ ambientWeight J p * ‖B p‖ *
        (C * ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) :=
      mul_le_mul_of_nonneg_left (hb p)
        (mul_nonneg (le_trans zero_le_one (ambientWeight_one_le J p)) (norm_nonneg _))
    _ = (C * ‖B p‖) * (ambientWeight J p *
        ((1+‖inheritedLeft i p‖)^K * (1+‖inheritedRight j p‖)^K)) := by ring
    _ ≤ (C * ‖B p‖) * ambientWeight (J+2*K) p :=
      mul_le_mul_of_nonneg_left (inherited_pair_weight_bound i j J K p)
        (mul_nonneg hC (norm_nonneg _))
    _ = C * (ambientWeight (J+2*K) p * ‖B p‖) := by ring

theorem integrable_density_test {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D F : Ambient ι × Ambient κ → ℂ)
    (hD : StronglyMeasurable D) (hF : StronglyMeasurable F) (J : ℕ)
    (hi : Integrable (fun z => ambientWeight J z.1 * ambientWeight J z.2 * ‖D z‖))
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    Integrable (fun z => D z * F z) := by
  apply hi.mono' (hD.mul hF).aestronglyMeasurable
  filter_upwards with z
  change ‖D z * F z‖ ≤ _
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hFbound z) (norm_nonneg _)

theorem density_test_fubini {ι κ : Type*} [Fintype ι] [Fintype κ]
    (D F : Ambient ι × Ambient κ → ℂ)
    (hD : StronglyMeasurable D) (hF : StronglyMeasurable F) (J : ℕ)
    (hi : Integrable (fun z => ambientWeight J z.1 * ambientWeight J z.2 * ‖D z‖))
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, D z * F z) = ∫ p, ∫ q, D (p,q) * F (p,q) := by
  have h := integrable_density_test D F hD hF J hi hFbound
  simpa only [Measure.volume_eq_prod] using integral_prod (fun z => D z * F z) h

def twistedFullDensity {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (θ : ℝ × ℝ) (p : Ambient ι) : ℂ :=
  fullProfileDensity g (𝓕 (frequencyTwist g₁ θ.1))
    (𝓕 (frequencyTwist g₂ θ.2)) b₃ p

theorem fullProfileDensity_continuous {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) :
    Continuous (fullProfileDensity g b₁ b₂ b₃) := by
  unfold fullProfileDensity tripleCoefficient coordinateDensity
  fun_prop

theorem twistedFullDensity_joint_stronglyMeasurable {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × Ambient ι =>
      twistedFullDensity g g₁ g₂ b₃ p.1 p.2) := by
  unfold twistedFullDensity fullProfileDensity
  apply StronglyMeasurable.mul
  · have hm : Measurable (fun p : (ℝ × ℝ) × Ambient ι => (p.1,p.2.1)) := by fun_prop
    simpa only [Function.comp_def] using
      (twistedTriple_joint_stronglyMeasurable g₁ g₂ b₃).comp_measurable hm
  · apply Continuous.stronglyMeasurable
    unfold coordinateDensity
    fun_prop

theorem fullProfileDensity_weighted_integrable {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun p : Ambient ι =>
      ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖) := by
  convert (tripleCoefficient_weighted_integrable b₁ b₂ b₃ J).mul_prod
    (coordinate_density_weighted_integrable g J) using 1
  funext p
  simp only [ambientWeight, fullProfileDensity, norm_mul]
  ring

theorem fullProfileDensity_weighted_integral {ι : Type*} [Fintype ι]
    (g : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)) (J : ℕ) :
    (∫ p : Ambient ι, ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖) =
      (∫ t : Frequency,
        ((1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) *
          ‖tripleCoefficient b₁ b₂ b₃ t‖) *
      (∫ u : ι → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖) := by
  have he (p : Ambient ι) :
      ambientWeight J p * ‖fullProfileDensity g b₁ b₂ b₃ p‖ =
      (((1+‖p.1.1‖)^J * (1+‖p.1.2.1‖)^J * (1+‖p.1.2.2‖)^J) *
        ‖tripleCoefficient b₁ b₂ b₃ p.1‖) *
      ((∏ i, (1+‖p.2 i‖)^J) * ‖coordinateDensity g p.2‖) := by
    simp only [ambientWeight, fullProfileDensity, norm_mul]; ring
  simp_rw [he, Measure.volume_eq_prod]
  exact integral_prod_mul
    (fun t : Frequency => ((1+‖t.1‖)^J * (1+‖t.2.1‖)^J * (1+‖t.2.2‖)^J) *
      ‖tripleCoefficient b₁ b₂ b₃ t‖)
    (fun u : ι → ℝ => (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖)

def towerMomentOrder (J : ℕ) : ℕ := J + 2*(J + (volume : Measure ℝ).integrablePower)

theorem twistedFullDensity_moment {ι : Type*} [Fintype ι]
    (J : ℕ) (g : ι → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ × ℝ,
      (∫ p : Ambient ι, ambientWeight J p * ‖twistedFullDensity g g₁ g₂ b₃ θ p‖) ≤
      C * ((1+‖θ.1‖)^(J + (volume : Measure ℝ).integrablePower) *
        (1+‖θ.2‖)^(J + (volume : Measure ℝ).integrablePower)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂, hC₂, h₂⟩ := frequencyTwist_fourier_moment J g₂
  let M := ∫ u : ι → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖
  let B := ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖
  have hM : 0 ≤ M := integral_nonneg (fun _ => by positivity)
  have hB : 0 ≤ B := integral_nonneg (fun _ => by positivity)
  refine ⟨C₁*C₂*B*M, by positivity, ?_⟩
  intro θ
  unfold twistedFullDensity
  rw [fullProfileDensity_weighted_integral,
    tripleCoefficient_weighted_integral]
  have hh := mul_le_mul (h₁ θ.1) (h₂ θ.2)
    (integral_nonneg (fun _ => by positivity)) (by positivity)
  have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hB) hM
  convert hh' using 1
  ring

def towerDensity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (z : Ambient ι × Ambient κ) : ℂ :=
  fullProfileDensity outer b₁ b₂ b₃ z.1 *
    twistedFullDensity inner g₁ g₂ c₃
      (inheritedLeft i z.1, inheritedRight j z.1) z.2

theorem towerDensity_joint_stronglyMeasurable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃) := by
  unfold towerDensity
  apply StronglyMeasurable.mul
  · exact ((fullProfileDensity_continuous outer b₁ b₂ b₃).comp continuous_fst).stronglyMeasurable
  · simpa only [Function.comp_def] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)

theorem towerDensity_weighted {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : ℕ) (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
      Integrable (fun z : Ambient ι × Ambient κ =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ∧
      (∫ z : Ambient ι × Ambient κ,
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ≤
        C * (∫ p : Ambient ι, ambientWeight (towerMomentOrder J) p *
          ‖fullProfileDensity outer b₁ b₂ b₃ p‖) := by
  obtain ⟨C,hC,hb⟩ := twistedFullDensity_moment J inner g₁ g₂ c₃
  refine ⟨C,hC,?_⟩
  intro i j outer b₁ b₂ b₃
  let D : Ambient ι → Ambient κ → ℂ := fun p q =>
    twistedFullDensity inner g₁ g₂ c₃ (inheritedLeft i p, inheritedRight j p) q
  have hD : StronglyMeasurable (Function.uncurry D) := by
    simpa only [Function.comp_def, Function.uncurry_def, D] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)
  have hi (p : Ambient ι) : Integrable (fun q => ambientWeight J q * ‖D p q‖) :=
    fullProfileDensity_weighted_integrable inner
      (𝓕 (frequencyTwist g₁ (inheritedLeft i p)))
      (𝓕 (frequencyTwist g₂ (inheritedRight j p))) c₃ J
  have hout := fullProfileDensity_weighted_integrable outer b₁ b₂ b₃ (towerMomentOrder J)
  have hB := (fullProfileDensity_continuous outer b₁ b₂ b₃).stronglyMeasurable
  exact ⟨conditional_tower_integrable i j J _ C hC _ hB D hD hi
      (fun p => hb (inheritedLeft i p,inheritedRight j p)) hout,
    conditional_tower_bound i j J _ C hC _ hB D hD hi
      (fun p => hb (inheritedLeft i p,inheritedRight j p)) hout⟩

theorem towerDensity_fubini {ι κ : Type*} [Fintype ι] [Fintype κ]
    (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ))
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ c₃ : 𝓢(ℝ, ℂ))
    (F : Ambient ι × Ambient κ → ℂ) (hF : StronglyMeasurable F) (J : ℕ)
    (hFbound : ∀ z, ‖F z‖ ≤ ambientWeight J z.1 * ambientWeight J z.2) :
    (∫ z, towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z * F z) =
      ∫ p, ∫ q, towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ (p,q) * F (p,q) := by
  obtain ⟨C,hC,h⟩ := towerDensity_weighted (ι := ι) J inner g₁ g₂ c₃
  exact density_test_fubini _ F
    (towerDensity_joint_stronglyMeasurable i j outer b₁ b₂ b₃ inner g₁ g₂ c₃)
    hF J (h i j outer b₁ b₂ b₃).1 hFbound

theorem first_inherited_left_eq (p : Ambient (Fin 9)) :
    inheritedLeft 7 p = profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 7 := by
  simp [inheritedLeft, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem first_inherited_right_eq (p : Ambient (Fin 9)) :
    inheritedRight 8 p = -profileHeight firstLeftSlope firstRightSlope firstKernelSlope p.1 p.2 8 := by
  simp [inheritedRight, profileHeight, firstLeftSlope, firstRightSlope, firstKernelSlope]
  ring

theorem second_inherited_left_eq (p : Ambient (Fin 6)) :
    inheritedLeft 4 p = profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 4 := by
  simp [inheritedLeft, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

theorem second_inherited_right_eq (p : Ambient (Fin 6)) :
    inheritedRight 5 p = -profileHeight secondLeftSlope secondRightSlope secondKernelSlope p.1 p.2 5 := by
  simp [inheritedRight, profileHeight, secondLeftSlope, secondRightSlope, secondKernelSlope]
  ring

theorem twistedFullDensity_uniform_separation {κ : Type*} [Fintype κ]
    (g : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (a₁ a₂ ak M : κ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hbox : ∀ i y, g i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      (∀ (θ : ℝ × ℝ) (y : κ → ℝ),
        (∏ i, g i (y i)) * frequencyTwist g₁ θ.1 (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ.2 (∑ i, a₂ i * y i) *
          EisensteinSchwartzPoisson.paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : κ → ℝ,
          twistedFullDensity g g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u) ∧
      (∀ θ : ℝ × ℝ,
        (1+R)^A * (∫ p : Ambient κ,
          ambientWeight J p * ‖twistedFullDensity g g₁ g₂ c₃ θ p‖) ≤
        C * ((1+‖θ.1‖)^(J + (volume : Measure ℝ).integrablePower) *
          (1+‖θ.2‖)^(J + (volume : Measure ℝ).integrablePower))) := by
  obtain ⟨C,hC,hs⟩ := twisted_descent_profile_separation
    g₁ g₂ Φ (fun i => g i) a₁ a₂ ak M hM hbox A J
  let G := ∫ u : κ → ℝ, (∏ i, (1+‖u i‖)^J) * ‖coordinateDensity g u‖
  have hG : 0 ≤ G := integral_nonneg (fun _ => by positivity)
  refine ⟨C*G,mul_nonneg hC hG,?_⟩
  intro R hR
  obtain ⟨c₃,hc⟩ := hs R hR
  refine ⟨c₃,?_,?_⟩
  · intro θ y
    rw [(hc θ.1 θ.2).1 y]
    exact profile_integral_coordinate_absorption g
      (𝓕 (frequencyTwist g₁ θ.1)) (𝓕 (frequencyTwist g₂ θ.2)) c₃ a₁ a₂ ak y
  · intro θ
    unfold twistedFullDensity
    rw [fullProfileDensity_weighted_integral]
    have hh := mul_le_mul_of_nonneg_right (hc θ.1 θ.2).2.2 hG
    convert hh using 1 <;> ring

theorem fullProfile_tower_uniform {ι κ : Type*} [Fintype ι] [Fintype κ]
    (inner : κ → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (a₁ a₂ ak M : κ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hbox : ∀ i y, inner i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ c₃ : 𝓢(ℝ, ℂ),
      (∀ (θ : ℝ × ℝ) (y : κ → ℝ),
        (∏ i, inner i (y i)) * frequencyTwist g₁ θ.1 (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ.2 (∑ i, a₂ i * y i) *
          EisensteinSchwartzPoisson.paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : κ → ℝ,
          twistedFullDensity inner g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode a₁ a₂ ak y (t₁,t₂,t₃) u) ∧
      (∀ (i j : ι) (outer : ι → 𝓢(ℝ, ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ, ℂ)),
        Integrable (fun z : Ambient ι × Ambient κ =>
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ∧
        (1+R)^A * (∫ z : Ambient ι × Ambient κ,
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity i j outer b₁ b₂ b₃ inner g₁ g₂ c₃ z‖) ≤
          C * (∫ p : Ambient ι, ambientWeight (towerMomentOrder J) p *
            ‖fullProfileDensity outer b₁ b₂ b₃ p‖)) := by
  obtain ⟨C,hC,hs⟩ := twistedFullDensity_uniform_separation inner g₁ g₂ Φ a₁ a₂ ak M hM hbox A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨c₃,he,hb⟩ := hs R hR
  refine ⟨c₃,he,?_⟩
  intro i j outer b₁ b₂ b₃
  have hRpow : 0 < (1+R)^A := pow_pos (by linarith) A
  let D : Ambient ι → Ambient κ → ℂ := fun p q =>
    twistedFullDensity inner g₁ g₂ c₃ (inheritedLeft i p,inheritedRight j p) q
  have hD : StronglyMeasurable (Function.uncurry D) := by
    simpa only [Function.comp_def, Function.uncurry_def, D] using
      (twistedFullDensity_joint_stronglyMeasurable inner g₁ g₂ c₃).comp_measurable
        (inheritedParameter_measurable i j)
  have hi (p : Ambient ι) : Integrable (fun q => ambientWeight J q * ‖D p q‖) :=
    fullProfileDensity_weighted_integrable inner
      (𝓕 (frequencyTwist g₁ (inheritedLeft i p)))
      (𝓕 (frequencyTwist g₂ (inheritedRight j p))) c₃ J
  have hb' (p : Ambient ι) : (∫ q, ambientWeight J q * ‖D p q‖) ≤
      (C/(1+R)^A) * ((1+‖inheritedLeft i p‖)^(J + (volume : Measure ℝ).integrablePower) *
        (1+‖inheritedRight j p‖)^(J + (volume : Measure ℝ).integrablePower)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hRpow).mpr
    simpa only [mul_comm] using hb (inheritedLeft i p,inheritedRight j p)
  have hout := fullProfileDensity_weighted_integrable outer b₁ b₂ b₃ (towerMomentOrder J)
  have hB := (fullProfileDensity_continuous outer b₁ b₂ b₃).stronglyMeasurable
  have hi' := conditional_tower_integrable i j J _ (C/(1+R)^A)
    (div_nonneg hC hRpow.le) _ hB D hD hi hb' hout
  have hb'' := conditional_tower_bound i j J _ (C/(1+R)^A)
    (div_nonneg hC hRpow.le) _ hB D hD hi hb' hout
  refine ⟨hi',?_⟩
  have hh := mul_le_mul_of_nonneg_left hb'' hRpow.le
  have hcancel (x : ℝ) : (1+R)^A * (C/(1+R)^A*x) = C*x := by
    field_simp [ne_of_gt hRpow]
  rw [hcancel] at hh
  simpa only [towerDensity, D, towerMomentOrder] using hh

def twistedPositiveSource (W : ℝ → ℂ) (θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x) * W x

theorem first_second_profile_tower
    (W₁ W₂ U₁ U₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsW₁ : Function.support W₁ ⊆ Set.Icc a b) (hsW₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hsU₁ : Function.support U₁ ⊆ Set.Icc a b) (hsU₂ : Function.support U₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hU₁ : ContDiff ℝ ∞ U₁) (hU₂ : ContDiff ℝ ∞ U₂)
    (Φ Ψ : 𝓢(ℝ, ℂ)) (V : Fin 9 → ℝ → ℂ) (T : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hVS : ∀ i, HasCompactSupport (V i))
    (hT : ∀ i, ContDiff ℝ ∞ (T i)) (hTS : ∀ i, HasCompactSupport (T i))
    (MV : Fin 9 → ℝ) (MT : Fin 6 → ℝ)
    (hMV : ∀ i, 0 ≤ MV i) (hMT : ∀ i, 0 ≤ MT i)
    (hVbox : ∀ i y, V i y ≠ 0 → |y| ≤ MV i)
    (hTbox : ∀ i y, T i y ≠ 0 → |y| ≤ MT i) (A₁ A₂ J : ℕ) :
    let G := firstRootSchwartz V hV hVS
    let H := secondRootSchwartz T hT hTS
    let g₁ := CubicReflectionKernel.logSchwartz U₁ a b ha hsU₁ hU₁
    let g₂ := CubicReflectionKernel.logSchwartz U₂ a b ha hsU₂ hU₂
    ∃ (b₁ b₂ : 𝓢(ℝ, ℂ)) (C : ℝ), 0 ≤ C ∧
      ∀ R₁ R₂ : ℝ, 0 < R₁ → 0 < R₂ → ∃ b₃ c₃ : 𝓢(ℝ, ℂ),
      (∀ y : Fin 9 → ℝ, firstPoissonProfile W₁ W₂ Φ V R₁ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 9 → ℝ,
          fullProfileDensity G b₁ b₂ b₃ ((t₁,t₂,t₃),u) *
            (∏ i, logPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope
              (t₁,t₂,t₃) u i) (y i))) ∧
      (∀ (θ : ℝ × ℝ) (y : Fin 6 → ℝ),
        secondPoissonProfile (twistedPositiveSource U₁ θ.1)
          (twistedPositiveSource U₂ θ.2) Ψ T R₂ y =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, ∫ u : Fin 6 → ℝ,
          twistedFullDensity H g₁ g₂ c₃ θ ((t₁,t₂,t₃),u) *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y (t₁,t₂,t₃) u) ∧
      Integrable (fun z : Ambient (Fin 9) × Ambient (Fin 6) =>
        ambientWeight J z.1 * ambientWeight J z.2 *
          ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖) ∧
      (1+R₁)^A₁ * (1+R₂)^A₂ *
        (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
          ambientWeight J z.1 * ambientWeight J z.2 *
            ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖) ≤ C := by
  dsimp only
  let G := firstRootSchwartz V hV hVS
  let H := secondRootSchwartz T hT hTS
  let g₁ := CubicReflectionKernel.logSchwartz U₁ a b ha hsU₁ hU₁
  let g₂ := CubicReflectionKernel.logSchwartz U₂ a b ha hsU₂ hU₂
  obtain ⟨b₁,b₂,C₁,hC₁,hfirst⟩ := first_full_profile_common_measure
    W₁ W₂ a b ha hsW₁ hsW₂ hW₁ hW₂ Φ V MV hV hVS hMV hVbox A₁ (towerMomentOrder J)
  have hbox : ∀ i y, H i y ≠ 0 → |y| ≤ MT i := by
    intro i y hy
    change secondRootWindows T i y ≠ 0 at hy
    fin_cases i <;> apply hTbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  obtain ⟨C₂,hC₂,hsecond⟩ := fullProfile_tower_uniform (ι := Fin 9)
    H g₁ g₂ Ψ secondLeftSlope secondRightSlope secondKernelSlope MT hMT hbox A₂ J
  refine ⟨b₁,b₂,C₂*C₁,mul_nonneg hC₂ hC₁,?_⟩
  intro R₁ R₂ hR₁ hR₂
  obtain ⟨b₃,he₁,hi₁,hb₁⟩ := hfirst R₁ hR₁
  obtain ⟨c₃,he₂,htower⟩ := hsecond R₂ hR₂
  have ht := htower 7 8 G b₁ b₂ b₃
  refine ⟨b₃,c₃,he₁,?_,ht.1,?_⟩
  · intro θ y
    simpa only [secondPoissonProfile, twistedPositiveSource, Real.log_exp,
      frequencyTwist_apply, g₁, g₂, CubicReflectionKernel.logSchwartz_apply,
      H, secondRootSchwartz, rootSchwartz_apply] using he₂ θ y
  · have hh := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ (1+R₁)^A₁ by positivity)
    have hh' := mul_le_mul_of_nonneg_left hb₁ hC₂
    calc
      _ = (1+R₁)^A₁ * ((1+R₂)^A₂ *
          (∫ z : Ambient (Fin 9) × Ambient (Fin 6),
            ambientWeight J z.1 * ambientWeight J z.2 *
              ‖towerDensity 7 8 G b₁ b₂ b₃ H g₁ g₂ c₃ z‖)) := by ring
      _ ≤ (1+R₁)^A₁ * (C₂ * (∫ p : Ambient (Fin 9),
          ambientWeight (towerMomentOrder J) p * ‖fullProfileDensity G b₁ b₂ b₃ p‖)) := hh
      _ ≤ C₂*C₁ := by
        simpa only [ambientWeight, tripleHeight, coordinateHeight, G, mul_assoc,
          mul_left_comm, mul_comm] using hh'

end
end SevenEighths.InverseAmbientProfileTower

end OAI
end OAIOriginalModule0513

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.ClippingProfiles
Source SHA256: 1da4c69d0ea7e310feeeed905e208f1eb62f87284a2ca24c321dfe7244f81c43
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0514






namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
namespace SevenEighths.InverseClippingProfiles

def logWindow (v : ℝ → ℂ) (L ρ : ℝ) (y : ℝ) : ℂ := v ((y + ρ) / L)

def rootedWindow (v : ℝ → ℂ) (L ρ a H : ℝ) (y : ℝ) : ℂ :=
  (Real.exp (a * y - H * L) : ℂ) * logWindow v L ρ y

lemma logWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ : ℝ) :
    ContDiff ℝ ∞ (logWindow v L ρ) := by
  exact hv.comp ((contDiff_id.add contDiff_const).div_const L)

lemma rootedWindow_contDiff (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (L ρ a H : ℝ) :
    ContDiff ℝ ∞ (rootedWindow v L ρ a H) := by
  apply ContDiff.mul _ (logWindow_contDiff v hv L ρ)
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma logWindow_iteratedDeriv (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v)
    (L ρ : ℝ) (n : ℕ) :
    iteratedDeriv n (logWindow v L ρ) =
      fun y => (L⁻¹)^n • iteratedDeriv n v ((y + ρ) / L) := by
  have h : (logWindow v L ρ) =
      fun y => (fun z => v (L⁻¹ * z)) (y + ρ) := by
    funext y
    simp only [logWindow, div_eq_mul_inv, mul_comm]
  rw [h, iteratedDeriv_comp_add_const n (fun z => v (L⁻¹ * z)) ρ,
    iteratedDeriv_comp_const_smul (hv.of_le (by simp))]
  simp only [div_eq_mul_inv, mul_comm]

lemma expAffine_iteratedDeriv (a b : ℝ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => (Real.exp (a * y + b) : ℂ)) =
      fun y => (a : ℂ)^n * (Real.exp (a * y + b) : ℂ) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h := (((hasDerivAt_id y).const_mul a).add_const b).exp
    have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y h).const_mul ((a : ℂ)^n)
    simp only [Function.comp_def, id_eq, Complex.ofRealCLM_apply] at hc
    rw [hc.deriv]
    simp only [mul_one, Complex.ofReal_mul, pow_succ]
    ring

lemma logWindow_support (v : ℝ → ℂ) (M B L ρ : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    Function.support (logWindow v L ρ) ⊆ Set.Icc (-(M+B)*L) ((M+B)*L) := by
  intro y hy
  have hy' := hv hy
  change -M ≤ (y+ρ)/L ∧ (y+ρ)/L ≤ M at hy'
  have hl := (le_div_iff₀ hL).mp hy'.1
  have hu := (div_le_iff₀ hL).mp hy'.2
  have hr := abs_le.mp hρ
  constructor <;> nlinarith

lemma rootedWindow_compact (v : ℝ → ℂ) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    HasCompactSupport (rootedWindow v L ρ a H) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro y hy
  apply logWindow_support v M B L ρ hL hρ hv
  exact (mul_ne_zero_iff.mp hy).2

def rootSchwartz (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  (rootedWindow_compact v M B L ρ a H hL hρ hv).toSchwartzMap
    (rootedWindow_contDiff v (v.smooth ⊤) L ρ a H)

@[simp] lemma rootSchwartz_apply (v : 𝓢(ℝ, ℂ)) (M B L ρ a H y : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    rootSchwartz v M B L ρ a H hL hρ hv y = rootedWindow v L ρ a H y := rfl

lemma derivative_support (v : 𝓢(ℝ, ℂ)) (M : ℝ)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (n : ℕ) :
    Function.support (iteratedDeriv n v) ⊆ Set.Icc (-M) M :=
  (subset_tsupport _).trans
    ((CompactProfileFamily.tsupport_iteratedDeriv_subset v n).trans
      (closure_minimal hv isClosed_Icc))

lemma root_exp_le_one (a H M B L ρ y : ℝ)
    (hL : 0 ≤ L) (hρ : |ρ| ≤ B*L) (hy : |(y+ρ)/L| ≤ M)
    (hL0 : L ≠ 0) (hH : |a| *(M+B) ≤ H) :
    Real.exp (a*y-H*L) ≤ 1 := by
  have hs : |y| ≤ (M+B)*L := by
    have h := (abs_le.mp hy)
    have hLp : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    have h1 := (le_div_iff₀ hLp).mp h.1
    have h2 := (div_le_iff₀ hLp).mp h.2
    have hr := abs_le.mp hρ
    apply abs_le.mpr
    constructor <;> nlinarith
  have ha := le_abs_self (a*y)
  rw [abs_mul] at ha
  have hh := mul_le_mul_of_nonneg_left hs (abs_nonneg a)
  have hb := mul_le_mul_of_nonneg_right hH hL
  apply Real.exp_le_one_iff.mpr
  nlinarith

lemma expAffine_iteratedFDeriv_norm (a b y : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ => (Real.exp (a*x+b) : ℂ)) y‖ =
      |a|^n * Real.exp (a*y+b) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, expAffine_iteratedDeriv]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem rootSchwartz_seminorm (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n)
        (rootSchwartz v M B L ρ a H (by linarith) hρ hv) ≤
      ((M+B)*L)^k * (2:ℝ)^n * (1+|a|)^n * derivativeSeminormSum v 0 n := by
  have hLp : 0 < L := by linarith
  have hC : 0 ≤ ((M+B)*L)^k * (2:ℝ)^n * (1+|a|)^n *
      derivativeSeminormSum v 0 n := by
    apply mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  apply SchwartzMap.seminorm_le_bound ℝ k n _ hC
  intro y
  have hbase (j : ℕ) (hj : j ≤ n) :
      ‖y‖^k * Real.exp (a*y-H*L) *
          ‖iteratedFDeriv ℝ j (logWindow v L ρ) y‖ ≤
        ((M+B)*L)^k * derivativeSeminormSum v 0 n := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, logWindow_iteratedDeriv v (v.smooth ⊤)]
    by_cases hz : iteratedDeriv j v ((y+ρ)/L) = 0
    · simp only [hz, smul_zero, norm_zero, mul_zero]
      exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
    have harg := derivative_support v M hv j hz
    have hy : |(y+ρ)/L| ≤ M := abs_le.mpr harg
    have he := root_exp_le_one a H M B L ρ y hLp.le hρ hy (ne_of_gt hLp) hH
    have hx : ‖y‖ ≤ (M+B)*L := by
      have ht := logWindow_support (iteratedDeriv j v) M B L ρ hLp hρ
        (derivative_support v M hv j) hz
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor <;> linarith [ht.1, ht.2]
    have hd : ‖iteratedDeriv j v ((y+ρ)/L)‖ ≤ derivativeSeminormSum v 0 n := by
      have hh := (SchwartzMap.le_seminorm ℝ 0 j v ((y+ρ)/L)).trans
        (seminorm_le_derivativeSeminormSum v 0 n j hj)
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hh
    have hi : ‖L⁻¹‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hLp.le)]
      exact inv_le_one_of_one_le₀ hL
    have hs : ‖(L⁻¹)^j • iteratedDeriv j v ((y+ρ)/L)‖ ≤
        derivativeSeminormSum v 0 n := by
      rw [norm_smul, norm_pow]
      calc
        _ ≤ 1 * ‖iteratedDeriv j v ((y+ρ)/L)‖ := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hi
        _ ≤ _ := by simpa using hd
    calc
      _ ≤ ((M+B)*L)^k * 1 * derivativeSeminormSum v 0 n := by gcongr
      _ = _ := by ring
  have he : ContDiff ℝ ∞ (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
  have hh := norm_iteratedFDeriv_mul_le he (logWindow_contDiff v (v.smooth ⊤) L ρ)
    y (n := n) (by exact_mod_cast le_top)
  change ‖y‖^k * ‖iteratedFDeriv ℝ n (rootedWindow v L ρ a H) y‖ ≤ _
  unfold rootedWindow
  calc
    _ ≤ ‖y‖^k * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) y‖ *
        ‖iteratedFDeriv ℝ (n-i) (logWindow v L ρ) y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * |a|^i *
        (‖y‖^k * Real.exp (a*y-H*L) *
          ‖iteratedFDeriv ℝ (n-i) (logWindow v L ρ) y‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (fun x : ℝ => (Real.exp (a*x-H*L) : ℂ)) =
        (fun x : ℝ => (Real.exp (a*x+(-H*L)) : ℂ)) by ext x; congr 2; ring]
      rw [expAffine_iteratedFDeriv_norm]
      rw [show a*y+(-H*L) = a*y-H*L by ring]
      ring
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (1+|a|)^n *
        (((M+B)*L)^k * derivativeSeminormSum v 0 n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hp : |a|^i ≤ (1+|a|)^n := by
        calc
          _ ≤ (1+|a|)^i := by gcongr; linarith [abs_nonneg a]
          _ ≤ _ := pow_le_pow_right₀ (by linarith [abs_nonneg a])
            (Finset.mem_range_succ_iff.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity))
        (hbase (n-i) (Nat.sub_le _ _)) (by positivity) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring

def rootDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (2:ℝ)^i * (1+|a|)^i * derivativeSeminormSum v 0 i

def twistedDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) : ℝ :=
  (2:ℝ)^n * (1+2*Real.pi)^n * rootDerivativeBound v a n

lemma rootDerivativeBound_nonneg (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) :
    0 ≤ rootDerivativeBound v a n := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)

lemma twistedDerivativeBound_nonneg (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ) :
    0 ≤ twistedDerivativeBound v a n :=
  mul_nonneg (by positivity) (rootDerivativeBound_nonneg _ _ _)

lemma rootSchwartz_derivativeSum (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    derivativeSeminormSum (rootSchwartz v M B L ρ a H (by linarith) hρ hv) k n ≤
      ((M+B)*L)^k * rootDerivativeBound v a n := by
  unfold derivativeSeminormSum rootDerivativeBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  convert rootSchwartz_seminorm v M B L ρ a H hM hB hL hρ hv hH k i using 1
  ring

theorem rooted_twist_seminorm (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (k n : ℕ) :
    (SchwartzMap.seminorm ℝ k n)
      (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) ≤
      (M+B)^k * twistedDerivativeBound v a n * L^k * (1+‖θ‖)^n := by
  have hb := frequencyTwist_seminorm_polynomial
    (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ k n
  have hd := rootSchwartz_derivativeSum v M B L ρ a H hM hB hL hρ hv hH k n
  calc
    _ ≤ ((2:ℝ)^n * (1+2*Real.pi)^n *
        derivativeSeminormSum (rootSchwartz v M B L ρ a H (by linarith) hρ hv) k n) *
        (1+‖θ‖)^n := hb
    _ ≤ ((2:ℝ)^n * (1+2*Real.pi)^n *
        (((M+B)*L)^k * rootDerivativeBound v a n)) * (1+‖θ‖)^n := by gcongr
    _ = _ := by unfold twistedDerivativeBound; rw [mul_pow]; ring

def momentOrder (J : ℕ) : ℕ := J + (volume : Measure ℝ).integrablePower

def windowSourceBound (v : 𝓢(ℝ, ℂ)) (M B a : ℝ) (J : ℕ) : ℝ :=
  (1+(M+B)^(volume : Measure ℝ).integrablePower) *
    ∑ i ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a i

lemma windowSourceBound_nonneg (v : 𝓢(ℝ, ℂ)) (M B a : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (J : ℕ) : 0 ≤ windowSourceBound v M B a J := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun _ _ => twistedDerivativeBound_nonneg _ _ _)

theorem rooted_twist_moment_sources (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H)
    (J i : ℕ) (hi : i ≤ momentOrder J) :
    (SchwartzMap.seminorm ℝ 0 i)
        (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i)
        (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) ≤
      windowSourceBound v M B a J * L^(volume : Measure ℝ).integrablePower *
        (1+‖θ‖)^(momentOrder J) := by
  let p := (volume : Measure ℝ).integrablePower
  have h0 := rooted_twist_seminorm v M B L ρ a H θ hM hB hL hρ hv hH 0 i
  have hp := rooted_twist_seminorm v M B L ρ a H θ hM hB hL hρ hv hH p i
  simp only [pow_zero, one_mul, mul_one] at h0
  have hs : twistedDerivativeBound v a i ≤
      ∑ j ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a j := by
    apply Finset.single_le_sum (fun j _ => twistedDerivativeBound_nonneg v a j)
    exact Finset.mem_range_succ_iff.mpr hi
  have hl : 1 ≤ L^p := one_le_pow₀ hL
  have ht : (1+‖θ‖)^i ≤ (1+‖θ‖)^(momentOrder J) :=
    pow_le_pow_right₀ (by linarith [norm_nonneg θ]) hi
  have hc := twistedDerivativeBound_nonneg v a i
  have hsum : 0 ≤ ∑ j ∈ Finset.range (momentOrder J+1), twistedDerivativeBound v a j :=
    Finset.sum_nonneg (fun _ _ => twistedDerivativeBound_nonneg _ _ _)
  calc
    _ ≤ twistedDerivativeBound v a i * (1+‖θ‖)^i +
        (M+B)^p * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := add_le_add h0 hp
    _ ≤ twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i +
        (M+B)^p * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := by gcongr; nlinarith
    _ = (1+(M+B)^p) * twistedDerivativeBound v a i * L^p * (1+‖θ‖)^i := by ring
    _ ≤ _ := by unfold windowSourceBound; gcongr

lemma coefficientMomentBound_mul (J : ℕ) (C D : ℝ) :
    coefficientMomentBound J (C*D) = coefficientMomentBound J C * D := by
  unfold coefficientMomentBound
  ring

theorem rooted_twist_fourier_moment (v : 𝓢(ℝ, ℂ)) (M B L ρ a H θ : ℝ)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 1 ≤ L) (hρ : |ρ| ≤ B*L)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (hH : |a| *(M+B) ≤ H) (J : ℕ) :
    (∫ t : ℝ, (1+‖t‖)^J *
      ‖(𝓕 (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ)) t‖) ≤
      ((2:ℝ)^J * (coefficientMomentBound 0 (windowSourceBound v M B a J) +
        coefficientMomentBound J (windowSourceBound v M B a J))) *
      L^(volume : Measure ℝ).integrablePower * (1+‖θ‖)^(momentOrder J) := by
  have hc := windowSourceBound_nonneg v M B a hM hB J
  have h := uniform_fourier_one_plus_moment
    (frequencyTwist (rootSchwartz v M B L ρ a H (by linarith) hρ hv) θ) J 1
    (windowSourceBound v M B a J * L^(volume : Measure ℝ).integrablePower *
      (1+‖θ‖)^(momentOrder J)) (by norm_num) (by positivity)
    (by
      intro i hi
      simpa using (rooted_twist_moment_sources v M B L ρ a H θ
        hM hB hL hρ hv hH J i hi))
  simp only [one_mul, coefficientMomentBound_mul] at h
  convert h using 1
  ring

theorem child_log_window_parameters (η Z δ : ℝ) (_hη : 0 ≤ η)
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hδu : δ ≤ 6*η) :
    0 ≤ δ*Real.log Z ∧ |δ*Real.log Z| ≤ 6*(η*Real.log Z) := by
  have hz : 0 ≤ Real.log Z := Real.log_nonneg hZ
  constructor
  · positivity
  · rw [abs_of_nonneg (by positivity : 0 ≤ δ*Real.log Z)]
    nlinarith [mul_le_mul_of_nonneg_right hδu hz]

theorem clipping_ratio_of_column_witness (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q / Z^N) ≠ 0) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  have hz : 0 < Z := by linarith
  have hn : 0 ≤ max 0 N-N := sub_nonneg.mpr (le_max_right _ _)
  refine ⟨Real.one_le_rpow hZ.le hn, ?_⟩
  by_cases hN : 0 ≤ N
  · simpa [max_eq_right hN] using hb
  · have hN' : N ≤ 0 := le_of_lt (lt_of_not_ge hN)
    rw [max_eq_left hN', zero_sub, Real.rpow_neg hz.le]
    have hsupport := (hw hwitness).2
    calc
      _ = 1 / Z^N := (one_div _).symm
      _ ≤ q / Z^N := div_le_div_of_nonneg_right hq (Real.rpow_nonneg hz.le _)
      _ ≤ b := hsupport

theorem clipped_positive_support (w : ℝ → ℂ) (a b c : ℝ)
    (ha : 0 < a) (hc : 1 ≤ c) (hcb : c ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) :
    Function.support (fun y => w (c*y)) ⊆ Set.Icc (a/b) b := by
  intro y hy
  have hs := hw hy
  have hcp : 0 < c := by linarith
  have hbp : 0 < b := lt_of_lt_of_le hcp hcb
  have hyp : 0 < y := by nlinarith [hs.1]
  constructor
  · apply (div_le_iff₀ hbp).mpr
    nlinarith [mul_le_mul_of_nonneg_right hcb hyp.le, hs.1]
  · nlinarith [hs.2]

theorem clipped_log_source (w : ℝ → ℂ) (c y : ℝ) (hc : 0 < c) :
    w (c*Real.exp y) = (fun s => w (Real.exp s)) (y+Real.log c) := by
  change w (c*Real.exp y) = w (Real.exp (y+Real.log c))
  rw [Real.exp_add, Real.exp_log hc]
  congr 1
  ring

open InverseMoment

def firstRootExponent (y : Fin 9 → ℝ) : ℝ :=
  -y 3-y 4/2-y 5-(y 7+y 8)/2

def secondRootExponent (y : Fin 6 → ℝ) : ℝ :=
  -y 1-y 2-(y 4+y 5)/2

theorem first_root_coupled_identity (y : Fin 9 → ℝ) :
    firstRootExponent y = -y 3-y 4/2+(y 0+y 1)/2+y 2 -
      ((∑ i, firstLeftSlope i*y i)+(∑ i, firstRightSlope i*y i))/2 := by
  simp [firstRootExponent, firstLeftSlope, firstRightSlope, Fin.sum_univ_succ]
  ring

theorem second_root_coupled_identity (y : Fin 6 → ℝ) :
    secondRootExponent y = -y 1+y 0 -
      ((∑ i, secondLeftSlope i*y i)+(∑ i, secondRightSlope i*y i))/2 := by
  simp [secondRootExponent, secondLeftSlope, secondRightSlope, Fin.sum_univ_succ]
  ring

theorem first_root_budget (y : Fin 9 → ℝ) (L : ℝ)
    (h0 : |y 0| ≤ L) (h1 : |y 1| ≤ L) (h2 : |y 2| ≤ L)
    (h3 : |y 3| ≤ L) (h4 : |y 4| ≤ L)
    (hl : |∑ i, firstLeftSlope i*y i| ≤ L)
    (hr : |∑ i, firstRightSlope i*y i| ≤ L) :
    firstRootExponent y ≤ (9/2:ℝ)*L := by
  rw [first_root_coupled_identity]
  rcases abs_le.mp h0 with ⟨_, h0⟩
  rcases abs_le.mp h1 with ⟨_, h1⟩
  rcases abs_le.mp h2 with ⟨_, h2⟩
  rcases abs_le.mp h3 with ⟨h3, _⟩
  rcases abs_le.mp h4 with ⟨h4, _⟩
  rcases abs_le.mp hl with ⟨hl, _⟩
  rcases abs_le.mp hr with ⟨hr, _⟩
  linarith

theorem second_root_budget (y : Fin 6 → ℝ) (L : ℝ)
    (h0 : |y 0| ≤ L) (h1 : |y 1| ≤ L)
    (hl : |∑ i, secondLeftSlope i*y i| ≤ 4*L)
    (hr : |∑ i, secondRightSlope i*y i| ≤ 4*L) :
    secondRootExponent y ≤ 6*L := by
  rw [second_root_coupled_identity]
  rcases abs_le.mp h0 with ⟨_, h0⟩
  rcases abs_le.mp h1 with ⟨h1, _⟩
  rcases abs_le.mp hl with ⟨hl, _⟩
  rcases abs_le.mp hr with ⟨hr, _⟩
  linarith

def firstRootSlope : Fin 9 → ℝ := ![0,0,0,-1,-(1/2),-1,0,-(1/2),-(1/2)]
def secondRootSlope : Fin 6 → ℝ := ![0,-1,-1,0,-(1/2),-(1/2)]

lemma inverseNormWindow_exp (V : ℝ → ℂ) (y : ℝ) :
    inverseNormWindow V y = (Real.exp (-y) : ℂ)*V y := by
  simp only [inverseNormWindow, Real.exp_neg, Complex.ofReal_inv, div_eq_mul_inv]
  ring

lemma inverseRootWindow_exp (V : ℝ → ℂ) (y : ℝ) :
    inverseRootWindow V y = (Real.exp (-(y/2)) : ℂ)*V y := by
  rw [inverseRootWindow, ← Real.exp_half, Real.exp_neg, Complex.ofReal_inv]
  ring

theorem firstRootWindows_exp (V : Fin 9 → ℝ → ℂ) (i : Fin 9) (y : ℝ) :
    firstRootWindows V i y = (Real.exp (firstRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [firstRootWindows, firstRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem secondRootWindows_exp (V : Fin 6 → ℝ → ℂ) (i : Fin 6) (y : ℝ) :
    secondRootWindows V i y = (Real.exp (secondRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [secondRootWindows, secondRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem firstRootWindows_prod (V : Fin 9 → ℝ → ℂ) (y : Fin 9 → ℝ) :
    (∏ i, firstRootWindows V i (y i)) =
      (Real.exp (firstRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [firstRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [firstRootSlope, firstRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem secondRootWindows_prod (V : Fin 6 → ℝ → ℂ) (y : Fin 6 → ℝ) :
    (∏ i, secondRootWindows V i (y i)) =
      (Real.exp (secondRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [secondRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [secondRootSlope, secondRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem first_profile_normalized_identity (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 9 → ℝ → ℂ) (R L : ℝ) (y : Fin 9 → ℝ) :
    (Real.exp (-(9/2:ℝ)*L) : ℂ)*firstPoissonProfile W₁ W₂ Φ V R y =
      (Real.exp (firstRootExponent y-(9/2:ℝ)*L) : ℂ) *
      (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, firstLeftSlope i*y i)) *
      W₂ (Real.exp (∑ i, firstRightSlope i*y i)) *
      EisensteinSchwartzPoisson.paperRadialFourier Φ
        (R*Real.exp (∑ i, firstKernelSlope i*y i)) := by
  rw [firstPoissonProfile, firstRootWindows_prod]
  simp only [Real.exp_sub, div_eq_mul_inv, neg_mul, Real.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem second_profile_normalized_identity (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) :
    (Real.exp (-6*L) : ℂ)*secondPoissonProfile W₁ W₂ Φ V R y =
      (Real.exp (secondRootExponent y-6*L) : ℂ) *
      (∏ i, V i (y i)) * W₁ (Real.exp (∑ i, secondLeftSlope i*y i)) *
      W₂ (Real.exp (∑ i, secondRightSlope i*y i)) *
      EisensteinSchwartzPoisson.paperRadialFourier Φ
        (R*Real.exp (∑ i, secondKernelSlope i*y i)) := by
  rw [secondPoissonProfile, secondRootWindows_prod]
  simp only [Real.exp_sub, div_eq_mul_inv, neg_mul, Real.exp_neg,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem fourier_phase_shift (f : ℝ → ℂ) (θ t : ℝ) :
    (𝓕 (fun y => logPhase θ y * f y)) t = (𝓕 f) (t-θ) := by
  simp only [Real.fourier_eq', logPhase, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translate (f : ℝ → ℂ) (ρ t : ℝ) :
    (𝓕 (fun y => f (y+ρ))) t = logPhase t ρ * (𝓕 f) t := by
  have h := congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) f ρ) t
  change _ = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t at h
  have h' : (𝓕 (fun y => f (y+ρ))) t = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t := by
    simpa only [Real.fourier_eq, VectorFourier.fourierIntegral, Function.comp_def, innerₗ_apply_apply] using h
  rw [h']
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, logPhase]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    (𝓕 (fun y => logPhase θ y * f (y+ρ))) t =
      logPhase (t-θ) ρ * (𝓕 f) (t-θ) := by
  rw [fourier_phase_shift, fourier_translate]

theorem norm_fourier_translated_twist (f : ℝ → ℂ) (ρ θ t : ℝ) :
    ‖(𝓕 (fun y => logPhase θ y * f (y+ρ))) t‖ = ‖(𝓕 f) (t-θ)‖ := by
  rw [fourier_translated_twist, norm_mul, logPhase_norm, one_mul]

theorem rooted_family_fourier_joint_measurable (v : 𝓢(ℝ, ℂ)) (a H : ℝ) :
    StronglyMeasurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
      (𝓕 (fun y => logPhase p.1.2.2 y * rootedWindow v p.1.1 p.1.2.1 a H y)) p.2) := by
  apply InverseKernelSourceUniform.fourier_joint_stronglyMeasurable
    (fun q : ℝ × ℝ × ℝ => fun y => logPhase q.2.2 y * rootedWindow v q.1 q.2.1 a H y)
  apply Measurable.stronglyMeasurable
  change Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
    logPhase p.1.2.2 p.2 * ((Real.exp (a*p.2-H*p.1.1) : ℂ) *
      v ((p.2+p.1.2.1)/p.1.1)))
  have hp : Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ => logPhase p.1.2.2 p.2) := by
    unfold logPhase
    fun_prop
  exact hp.mul ((show Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ =>
    (Real.exp (a*p.2-H*p.1.1) : ℂ)) by fun_prop).mul
      (v.continuous.measurable.comp (by fun_prop)))

def childWindowDensity (v : 𝓢(ℝ, ℂ)) (η Z δ θ t : ℝ) : ℂ :=
  (𝓕 (fun y => logPhase θ y * v ((y+δ*Real.log Z)/(η*Real.log Z)))) t

def windowMomentConstant (v : 𝓢(ℝ, ℂ)) (M B a : ℝ) (J : ℕ) : ℝ :=
  (2:ℝ)^J * (coefficientMomentBound 0 (windowSourceBound v M B a J) +
    coefficientMomentBound J (windowSourceBound v M B a J))

theorem childWindowDensity_moment (v : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 ≤ M)
    (hv : Function.support v ⊆ Set.Icc (-M) M) (J : ℕ)
    (η Z δ θ : ℝ) (hη : 0 ≤ η) (hZ : 1 ≤ Z)
    (hL : 1 ≤ η*Real.log Z) (hδ : 0 ≤ δ) (hδu : δ ≤ 6*η) :
    Integrable (fun t : ℝ => (1+‖t‖)^J * ‖childWindowDensity v η Z δ θ t‖) ∧
    (∫ t : ℝ, (1+‖t‖)^J * ‖childWindowDensity v η Z δ θ t‖) ≤
      windowMomentConstant v M 6 0 J * (η*Real.log Z)^(volume : Measure ℝ).integrablePower *
        (1+‖θ‖)^(momentOrder J) := by
  have hρ := (child_log_window_parameters η Z δ hη hZ hδ hδu).2
  let g := frequencyTwist (rootSchwartz v M 6 (η*Real.log Z) (δ*Real.log Z) 0 0
    (by linarith) hρ hv) θ
  have he (t : ℝ) : childWindowDensity v η Z δ θ t = (𝓕 g) t := by
    rw [congrFun (SchwartzMap.fourier_coe g) t]
    unfold childWindowDensity
    have hg : (g : ℝ → ℂ) = fun y =>
        logPhase θ y * v ((y+δ*Real.log Z)/(η*Real.log Z)) := by
      funext y
      simp [g, frequencyTwist_apply, rootSchwartz_apply, rootedWindow, logWindow]
    rw [hg]
  simp_rw [he]
  refine ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable g J, ?_⟩
  exact rooted_twist_fourier_moment v M 6 (η*Real.log Z) (δ*Real.log Z) 0 0 θ
    hM (by norm_num) hL hρ hv (by simp) J

theorem retained_clipped_column (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q/Z^N) ≠ 0) :
    let c := Z^(max 0 N-N)
    1 ≤ c ∧ c ≤ b ∧
    Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b ∧
    ∀ θ t : ℝ,
      (𝓕 (fun y => logPhase θ y * w (c*Real.exp y))) t =
        logPhase (t-θ) (Real.log c) * (𝓕 (fun y => w (Real.exp y))) (t-θ) := by
  dsimp only
  have hc := clipping_ratio_of_column_witness w Z N q a b hZ hq hb hw hwitness
  refine ⟨hc.1, hc.2, clipped_positive_support w a b _ ha hc.1 hc.2 hw, ?_⟩
  intro θ t
  have he : (fun y => logPhase θ y * w (Z^(max 0 N-N)*Real.exp y)) =
      (fun y => logPhase θ y * (fun s => w (Real.exp s)) (y+Real.log (Z^(max 0 N-N)))) := by
    ext y
    rw [clipped_log_source w _ y (by linarith)]
  rw [he]
  exact fourier_translated_twist (fun s => w (Real.exp s)) (Real.log (Z^(max 0 N-N))) θ t

theorem translated_twist_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J *
        ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ≤
        C*(1+‖θ‖)^(momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseMoment.frequencyTwist_fourier_moment J g
  refine ⟨C, hC, ?_⟩
  intro ρ θ
  have he (t : ℝ) : ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖ =
      ‖(𝓕 (frequencyTwist g θ)) t‖ := by
    rw [norm_fourier_translated_twist, congrFun (SchwartzMap.fourier_coe _) t]
    have hf : (frequencyTwist g θ : ℝ → ℂ) = fun y => logPhase θ y * g y := by
      funext y
      exact frequencyTwist_apply g θ y
    rw [hf, fourier_phase_shift]
  simp_rw [he]
  exact ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable _ _, hb θ⟩

theorem eventually_log_scale_pow_le (C η π : ℝ) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hπ : 0 < π) (k : ℕ) :
    ∀ᶠ Z : ℝ in Filter.atTop, C*(η*Real.log Z)^k ≤ Z^π := by
  have h := (_root_.isLittleO_log_rpow_rpow_atTop (k:ℝ) hπ).const_mul_left (C*η^k)
  filter_upwards [h.bound (by norm_num : (0:ℝ) < 1),
    Filter.eventually_ge_atTop (1:ℝ)] with Z hZ hZ1
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have hz : 0 ≤ Z := by linarith
  rw [Real.rpow_natCast, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (Real.rpow_nonneg hz π), one_mul] at hZ
  convert hZ using 1
  ring

def firstBalancedSlope : Fin 9 → ℝ := ![1/2,1/2,1,-1,-(1/2),0,0,0,0]
def secondBalancedSlope : Fin 6 → ℝ := ![1,-1,0,0,0,0]

theorem first_root_normalization_split (y : Fin 9 → ℝ) (L : ℝ) :
    Real.exp (firstRootExponent y-(9/2:ℝ)*L) =
      (∏ i, Real.exp (firstBalancedSlope i*y i-|firstBalancedSlope i| *L)) *
      Real.exp (-(∑ i, firstLeftSlope i*y i)/2-L/2) *
      Real.exp (-(∑ i, firstRightSlope i*y i)/2-L/2) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [firstRootExponent, firstBalancedSlope, firstLeftSlope, firstRightSlope,
    Fin.sum_univ_succ]
  ring

theorem second_root_normalization_split (y : Fin 6 → ℝ) (L : ℝ) :
    Real.exp (secondRootExponent y-6*L) =
      (∏ i, Real.exp (secondBalancedSlope i*y i-|secondBalancedSlope i| *L)) *
      Real.exp (-(∑ i, secondLeftSlope i*y i)/2-2*L) *
      Real.exp (-(∑ i, secondRightSlope i*y i)/2-2*L) := by
  rw [← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [secondRootExponent, secondBalancedSlope, secondLeftSlope, secondRightSlope,
    Fin.sum_univ_succ]
  ring

end SevenEighths.InverseClippingProfiles

end

end OAI
end OAIOriginalModule0514

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialProfile
Source SHA256: 446ac4ecee7755bceae9cc60b5ea239a8ca521b2db50256d80c5c5b71f994945
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0515




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment

namespace SevenEighths.InverseInitialProfile

def clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ : ℝ) : 𝓢(ℝ, ℂ) :=
  frequencyTwist (SchwartzMap.compSubConstCLM ℂ (-Real.log c) g) θ

@[simp] theorem clippedTwist_apply (g : 𝓢(ℝ, ℂ)) (c θ y : ℝ) :
    clippedTwist g c θ y = logPhase θ y * g (y + Real.log c) := by
  simp [clippedTwist]

def sourceDensity (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) : ℂ :=
  logPhase (t-θ) (Real.log c) * (𝓕 g) (t-θ)

theorem fourier_clippedTwist (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    (𝓕 (clippedTwist g c θ)) t = sourceDensity g c θ t := by
  rw [SchwartzMap.fourier_coe]
  have he : (clippedTwist g c θ : ℝ → ℂ) =
      fun y => logPhase θ y * g (y + Real.log c) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translated_twist]
  rfl

theorem sourceDensity_joint_measurable (g : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun p : (ℝ × ℝ) × ℝ => sourceDensity g p.1.1 p.1.2 p.2) := by
  unfold sourceDensity logPhase
  apply Measurable.stronglyMeasurable
  apply Measurable.mul
  · exact Complex.continuous_exp.measurable.comp (by fun_prop)
  · exact (𝓕 g : 𝓢(ℝ, ℂ)).continuous.measurable.comp (by fun_prop)

theorem sourceDensity_norm (g : 𝓢(ℝ, ℂ)) (c θ t : ℝ) :
    ‖sourceDensity g c θ t‖ = ‖(𝓕 g) (t-θ)‖ := by
  simp [sourceDensity, logPhase_norm]

theorem sourceDensity_moment_uniform (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
        C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseClippingProfiles.translated_twist_moment_uniform g J
  refine ⟨C, hC, ?_⟩
  intro c θ
  simpa only [InverseClippingProfiles.fourier_translated_twist, sourceDensity,
    SchwartzMap.fourier_coe] using hb (Real.log c) θ

def clippedSource (W : ℝ → ℂ) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x) * W (c*x)

theorem clipped_log_source (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c : ℝ} (hc : 0 < c) (θ y : ℝ) :
    clippedTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) c θ y =
      clippedSource W c θ (Real.exp y) := by
  simp only [clippedTwist_apply, CubicReflectionKernel.logSchwartz_apply,
    clippedSource, Real.log_exp, Real.exp_add, Real.exp_log hc]
  rw [mul_comm (Real.exp y) c]

def rootExponent (y : Fin 6 → ℝ) : ℝ := -y 1-y 2-(y 4+y 5)/2

theorem root_coupled_identity (y : Fin 6 → ℝ) :
    rootExponent y = -y 1+y 0-((y 0+y 2+y 4)+(y 0+y 2+y 5))/2 := by
  unfold rootExponent
  ring

theorem root_budget (y : Fin 6 → ℝ) (L : ℝ)
    (hd : |y 1| ≤ L) (hC : |y 0| ≤ L)
    (hc₁ : |y 0+y 2+y 4| ≤ L) (hc₂ : |y 0+y 2+y 5| ≤ L) :
    rootExponent y ≤ 3*L := by
  rw [root_coupled_identity]
  have hd' := (abs_le.mp hd).1
  have hC' := (abs_le.mp hC).2
  have h1 := (abs_le.mp hc₁).1
  have h2 := (abs_le.mp hc₂).1
  linarith

def normalizedProfile (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) * secondPoissonProfile W₁ W₂ Φ V R y

theorem normalizedProfile_exact (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (y : Fin 6 → ℝ) :
    normalizedProfile W₁ W₂ Φ V R L y =
      (Real.exp (rootExponent y-3*L) : ℂ) * (∏ i, V i (y i)) *
      W₁ (Real.exp (y 0+y 2+y 4)) * W₂ (Real.exp (y 0+y 2+y 5)) *
      paperRadialFourier Φ (R*Real.exp (y 3-y 1-2*y 2-y 4-y 5)) := by
  unfold normalizedProfile secondPoissonProfile
  rw [InverseClippingProfiles.secondRootWindows_prod]
  have hleft : (∑ i, secondLeftSlope i*y i) = y 0+y 2+y 4 := by
    simp [secondLeftSlope, Fin.sum_univ_succ]
    ring
  have hright : (∑ i, secondRightSlope i*y i) = y 0+y 2+y 5 := by
    simp [secondRightSlope, Fin.sum_univ_succ]
    ring
  have hker : (∑ i, secondKernelSlope i*y i) = y 3-y 1-2*y 2-y 4-y 5 := by
    simp [secondKernelSlope, Fin.sum_univ_succ]
    ring
  rw [hleft, hright, hker]
  change (Real.exp (-3*L) : ℂ) * (((Real.exp (rootExponent y) : ℂ)*_)*_*_*_) = _
  rw [show Real.exp (rootExponent y-3*L) = Real.exp (-3*L)*Real.exp (rootExponent y) by
    rw [← Real.exp_add]; congr 1; ring, Complex.ofReal_mul]
  ring

def familyDensity (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) : ℂ :=
  (Real.exp (-3*L) : ℂ) * fullProfileDensity g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem familyDensity_formula (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Frequency × (Fin 6 → ℝ)) :
    familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p =
      (Real.exp (-3*L) : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 *
          (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) * coordinateDensity g p.2 := by
  simp only [familyDensity, fullProfileDensity, tripleCoefficient, fourier_clippedTwist]
  ring

theorem familyDensity_weighted_integrable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) := by
  convert (InverseMoment.fullProfileDensity_weighted_integrable g
    (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ J).const_mul
      (Real.exp (-3*L)) using 1
  funext p
  simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  ring

theorem familyDensity_weighted_integral
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Frequency × (Fin 6 → ℝ),
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) =
    Real.exp (-3*L) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
      (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
      ∏ i, ∫ u : ℝ, (1+‖u‖)^J * ‖(𝓕 (g i)) u‖ := by
  have he (p : Frequency × (Fin 6 → ℝ)) :
      tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖ =
      Real.exp (-3*L) * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (clippedTwist g₁ c₁ θ₁))
          (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p‖) := by
    simp only [familyDensity, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  simp only [fourier_clippedTwist]
  ring

def logFamilyProfile (g₁ g₂ : 𝓢(ℝ, ℂ)) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (Real.exp (-3*L) : ℂ) *
    ((∏ i, secondRootWindows V i (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

theorem family_common_measure
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ c₁ c₂ θ₁ θ₂ L : ℝ, 0 ≤ L →
      (∀ y : Fin 6 → ℝ,
        logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
          ∫ p : Frequency × (Fin 6 → ℝ),
            familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity (secondRootSchwartz V hV hS) g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  have hb : ∀ i y, secondRootWindows V i y ≠ 0 → |y| ≤ M i := by
    intro i y hy
    fin_cases i <;> apply hbox _ y
    all_goals first | exact hy | exact (div_ne_zero_iff.mp hy).1
  obtain ⟨C₃, hC₃, hsep⟩ := paperRadialFourier_log_separation_envelope
    Φ (secondRootWindows V) secondKernelSlope M hM hb A J
  obtain ⟨C₁, hC₁, h₁⟩ := sourceDensity_moment_uniform g₁ J
  obtain ⟨C₂, hC₂, h₂⟩ := sourceDensity_moment_uniform g₂ J
  let D : ℝ := ∏ i, ∫ u : ℝ, (1+‖u‖)^J *
    ‖(𝓕 (secondRootSchwartz V hV hS i)) u‖
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun u => by positivity))
  refine ⟨C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, _, hm, _⟩ := hsep R hR
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ L hL
  refine ⟨?_, familyDensity_weighted_integrable _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (secondRootWindows V) secondLeftSlope secondRightSlope secondKernelSlope R b₃ he y
    have habs := profile_integral_coordinate_absorption (secondRootSchwartz V hV hS)
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      secondLeftSlope secondRightSlope secondKernelSlope y
    have hid' : logFamilyProfile g₁ g₂ Φ V c₁ c₂ θ₁ θ₂ R L y =
        (Real.exp (-3*L) : ℂ) *
          ∫ p : Frequency × (Fin 6 → ℝ),
            fullProfileDensity (secondRootSchwartz V hV hS)
              (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p *
              pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y p.1 p.2 := by
      unfold logFamilyProfile
      rw [hid]
      congr 1
      rw [full_density_mode_fubini]
      simpa only [profileMode, secondRootSchwartz, rootSchwartz_apply] using habs
    rw [hid', ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold familyDensity
    ring
  · rw [familyDensity_weighted_integral]
    have h1 := (h₁ c₁ θ₁).2
    have h2 := (h₂ c₂ θ₂).2
    have h12 := mul_le_mul h1 h2 (integral_nonneg (fun _ => by positivity))
      (mul_nonneg hC₁ (by positivity))
    have hm0 : 0 ≤ (1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖ := by positivity
    have h123 := mul_le_mul h12 hm hm0 (by positivity)
    have h123D := mul_le_mul_of_nonneg_right h123 hD
    have hnorm : Real.exp (-3*L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have heq : (1+R)^A * (Real.exp (-3*L) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) =
      Real.exp (-3*L) * (((∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₁ c₁ θ₁ t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g₂ c₂ θ₂ t‖)) *
        ((1+R)^A * ∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) * D) := by ring
    change (1+R)^A * (_ * _ * _ * _ * D) ≤ _
    rw [heq]
    exact (mul_le_mul_of_nonneg_left h123D (Real.exp_pos _).le).trans
      ((mul_le_of_le_one_left (by positivity) hnorm).trans_eq (by ring))

theorem sourceDensity_moment_seminorm (g : 𝓢(ℝ, ℂ)) (M b : ℝ)
    (hM : 0 ≤ M) (hb : 1 ≤ b) (hg : Function.support g ⊆ Set.Icc (-M) M)
    (J : ℕ) {c : ℝ} (hc : 1 ≤ c) (hcb : c ≤ b) (θ : ℝ) :
    (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
      InverseClippingProfiles.windowMomentConstant g M (Real.log b) 0 J *
        (1+‖θ‖)^(InverseClippingProfiles.momentOrder J) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hlog : |Real.log c| ≤ Real.log b * 1 := by
    rw [mul_one, abs_of_nonneg (Real.log_nonneg hc)]
    exact Real.log_le_log hc0 hcb
  have he : clippedTwist g c θ = frequencyTwist
      (InverseClippingProfiles.rootSchwartz g M (Real.log b) 1 (Real.log c) 0 0
        zero_lt_one hlog hg) θ := by
    ext y
    simp [InverseClippingProfiles.rootSchwartz_apply,
      InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]
  have hm := InverseClippingProfiles.rooted_twist_fourier_moment g M (Real.log b)
    1 (Real.log c) 0 0 θ hM (Real.log_nonneg hb) le_rfl hlog hg (by simp) J
  simp_rw [← fourier_clippedTwist, he]
  simpa only [InverseClippingProfiles.windowMomentConstant, one_pow, mul_one] using hm

theorem clippedSource_conjugate (W : ℝ → ℂ) (c θ x : ℝ) :
    star (clippedSource W c θ x) = clippedSource (fun x => star (W x)) c (-θ) x := by
  simp only [clippedSource, star_mul, SecondPassIntegration.logPhase_conjugate]
  ring

theorem familyDensity_joint_measurable
    (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) (L : ℝ) :
    StronglyMeasurable (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × (Frequency × (Fin 6 → ℝ)) =>
      familyDensity g g₁ g₂ b₃ z.1.1.1 z.1.2.1 z.1.1.2 z.1.2.2 L z.2) := by
  simp_rw [familyDensity_formula]
  apply Measurable.stronglyMeasurable
  unfold sourceDensity coordinateDensity logPhase
  have h1 : Measurable ((𝓕 g₁ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 : Measurable ((𝓕 g₂ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 : Measurable (b₃ : ℝ → ℂ) := b₃.continuous.measurable
  have hu (i : Fin 6) : Measurable ((𝓕 (g i) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have hexp : Measurable Complex.exp := Complex.continuous_exp.measurable
  fun_prop

theorem fresh_cutoff_one (W w : ℝ → ℂ) (a b bclip A₀ B₀ A₂ B₂ : ℝ)
    (_ha : 0 < a) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hclip : 1 ≤ bclip)
    (hW : Function.support W ⊆ Set.Icc a b)
    (hω : ∀ x ∈ Set.Icc (a/(bclip*B₀*B₂)) (b/(A₀*A₂)), w x = 1)
    {c u v x : ℝ} (hc : 1 ≤ c) (hcb : c ≤ bclip)
    (hu : u ∈ Set.Icc A₀ B₀) (hv : v ∈ Set.Icc A₂ B₂) (hx : 0 < x)
    (hs : W (c*(u*v*x)) ≠ 0) : w x = 1 := by
  have hu0 : 0 < u := hA₀.trans_le hu.1
  have hv0 : 0 < v := hA₂.trans_le hv.1
  have hB₀ : 0 < B₀ := hu0.trans_le hu.2
  have hB₂ : 0 < B₂ := hv0.trans_le hv.2
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hs' := hW hs
  have hlo : A₀*A₂ ≤ c*(u*v) := by
    have hprod := mul_le_mul hu.1 hv.1 hA₂.le hu0.le
    exact hprod.trans (le_mul_of_one_le_left (mul_nonneg hu0.le hv0.le) hc)
  have hhi : c*(u*v) ≤ bclip*B₀*B₂ := by
    have hprod := mul_le_mul hu.2 hv.2 hv0.le hB₀.le
    exact (mul_le_mul hcb hprod (mul_nonneg hu0.le hv0.le)
      (zero_lt_one.trans_le hclip).le).trans_eq (by ring)
  apply hω x
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < bclip*B₀*B₂)).mpr
    have hh := mul_le_mul_of_nonneg_right hhi hx.le
    nlinarith [hs'.1]
  · apply (le_div_iff₀ (mul_pos hA₀ hA₂)).mpr
    have hh := mul_le_mul_of_nonneg_right hlo hx.le
    nlinarith [hs'.2]

def columnCenter (D B v : ℝ) : ℝ := D-B-v
def prefactorCenter (m D B θ : ℝ) : ℝ := m-2*D+B-θ
def radialCenter (m H θ D B : ℝ) : ℝ := m+H-θ-2*(D-B)

theorem original_column_scale {Z : ℝ} (hZ : 0 < Z) (D B v : ℝ) :
    Z^B * Z^v * Z^(columnCenter D B v) = Z^D := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  unfold columnCenter
  ring

theorem initial_prefactor_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ : ℝ) :
    Z^(-D) * Z^m / (Z^θ * Z^v * Z^(columnCenter D B v)) =
      Z^(prefactorCenter m D B θ) := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter prefactorCenter
  ring

theorem initial_radial_scale {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ) :
    Z^m * Z^H / (Z^θ * (Z^v)^2 * (Z^(columnCenter D B v))^2) =
      Z^(radialCenter m H θ D B) := by
  simp only [pow_two]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_sub hZ]
  congr 1
  unfold columnCenter radialCenter
  ring

theorem initial_normalization_scalar {Z : ℝ} (hZ : 0 < Z) (κ η : ℝ) :
    Z^(κ+3*η) * Real.exp (-3*(η*Real.log Z)) = Z^κ := by
  have he : Real.exp (-3*(η*Real.log Z)) = Z^(-3*η) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  rw [he, ← Real.rpow_add hZ]
  congr 1
  ring

def physicalKernel (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) : ℂ :=
  ((Z^(-D)*Z^m/(q 1*q 2*Real.sqrt (q 4*q 5)) : ℝ) : ℂ) *
    W₁ (q 0*q 2*q 4/Z^D) * W₂ (q 0*q 2*q 5/Z^D) *
      paperRadialFourier Φ (Z^m*q 3/(q 1*(q 2)^2*q 4*q 5))

theorem physicalKernel_eq_secondNorm (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (Z D m : ℝ) (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      ((Z^(-D)*Z^m : ℝ) : ℂ) *
        secondNormProfile (fun x => W₁ (x/Z^D)) (fun x => W₂ (x/Z^D))
          Φ (fun _ _ => 1) (Z^m) q := by
  unfold physicalKernel secondNormProfile
  rw [Real.sqrt_mul (hq 4).le]
  simp only [Finset.prod_const_one, one_mul, Complex.ofReal_div, Complex.ofReal_mul]
  ring

theorem physicalKernel_nominal (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ) : ℝ) *
        secondNormProfile W₁ W₂ Φ (fun _ _ => 1) (Z^(radialCenter m H θ D B))
          (secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))) := by
  have hn := secondNormProfile_nominal W₁ W₂ Φ
    (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v)) (Z^m)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) q hq
  rw [original_column_scale hZ D B v, initial_radial_scale hZ D B v m θ H] at hn
  rw [physicalKernel_eq_secondNorm W₁ W₂ Φ Z D m q hq, hn]
  change ((Z^(-D)*Z^m : ℝ) : ℂ) *
      (((Z^θ*Z^v*Z^(columnCenter D B v) : ℝ) : ℂ)⁻¹ * _) = _
  rw [← mul_assoc, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← div_eq_mul_inv, initial_prefactor_scale hZ D B v m θ]
  rfl

theorem normalizedProfile_eq_family (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (θ₁ θ₂ R L : ℝ)
    (y : Fin 6 → ℝ) :
    normalizedProfile (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ V R L y =
      logFamilyProfile (CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁)
        (CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂)
        Φ V c₁ c₂ θ₁ θ₂ R L y := by
  unfold normalizedProfile logFamilyProfile secondPoissonProfile
  rw [clipped_log_source W₁ a b ha hs₁ hW₁ hc₁,
    clipped_log_source W₂ a b ha hs₂ hW₂ hc₂]

theorem fresh_profile_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (R L : ℝ) (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i)
    (hw₁ : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1)
    (hw₂ : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1)
    (hV : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 → ∀ i, V i (Real.log (x i)) = 1) :
    (Real.exp (-3*L) : ℂ) * secondNormProfile W₁ W₂ Φ (fun _ _ => 1) R x =
      (w₁ (x 4)*w₂ (x 5)) * normalizedProfile W₁ W₂ Φ V R L (fun i => Real.log (x i)) := by
  unfold normalizedProfile
  rw [secondPoissonProfile_log W₁ W₂ Φ V R x hx]
  by_cases h1 : W₁ (x 0*x 2*x 4) = 0
  · simp only [secondNormProfile, h1, mul_zero, zero_mul, zero_div]
  by_cases h2 : W₂ (x 0*x 2*x 5) = 0
  · simp only [secondNormProfile, h2, mul_zero, zero_mul, zero_div]
  have hv := hV (by rw [hw₁ h1]; exact one_ne_zero) (by rw [hw₂ h2]; exact one_ne_zero)
  simp only [secondNormProfile, hv, hw₁ h1, hw₂ h2, Finset.prod_const_one, one_mul]

def relativeNorm (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) : Fin 6 → ℝ :=
  secondRelativeNorm q (Z^B) (Z^θ) (Z^v) (Z^H) (Z^(columnCenter D B v))

def relativeLog (q : Fin 6 → ℝ) (Z D B v θ H : ℝ) (i : Fin 6) : ℝ :=
  Real.log (relativeNorm q Z D B v θ H i)

theorem relativeNorm_pos (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    {Z : ℝ} (hZ : 0 < Z) (D B v θ H : ℝ) :
    ∀ i, 0 < relativeNorm q Z D B v θ H i :=
  secondRelativeNorm_pos q hq _ _ _ _ _
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _)
    (Real.rpow_pos_of_pos hZ _)

theorem initial_kernel_restore (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i)
    (hw₁ : W₁ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1)
    (hw₂ : W₂ (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
      relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1)
    (hV : w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 → ∀ i, V i (relativeLog q Z D B v θ H i) = 1) :
    physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        normalizedProfile W₁ W₂ Φ V (Z^(radialCenter m H θ D B))
          (η*Real.log Z) (relativeLog q Z D B v θ H) := by
  rw [physicalKernel_nominal W₁ W₂ Φ hZ D B v m θ H q hq]
  have hs := fresh_profile_restore W₁ W₂ w₁ w₂ Φ V (Z^(radialCenter m H θ D B))
    (η*Real.log Z) (relativeNorm q Z D B v θ H)
    (relativeNorm_pos q hq hZ D B v θ H) hw₁ hw₂ hV
  have hn : ((Z^(prefactorCenter m D B θ) : ℝ) : ℂ) =
      (Z^(prefactorCenter m D B θ+3*η) : ℝ) * (Real.exp (-3*(η*Real.log Z)) : ℂ) := by
    rw [← Complex.ofReal_mul, initial_normalization_scalar hZ]
  rw [show relativeLog q Z D B v θ H =
    (fun i => Real.log (relativeNorm q Z D B v θ H i)) by rfl]
  rw [hn, mul_assoc]
  simpa only [mul_assoc, relativeNorm] using congrArg
    (fun z : ℂ => (Z^(prefactorCenter m D B θ+3*η) : ℝ) * z) hs

def PhysicalIdentityAt (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (V : Fin 6 → ℝ → ℂ) (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (Z D B v m θ H η c₁ c₂ θ₁ θ₂ : ℝ) : Prop :=
  ∀ (w₁ w₂ : ℝ → ℂ) (q : Fin 6 → ℝ), (∀ i, 0 < q i) →
    (clippedSource W₁ c₁ θ₁
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 4) ≠ 0 → w₁ (relativeNorm q Z D B v θ H 4) = 1) →
    (clippedSource W₂ c₂ θ₂
      (relativeNorm q Z D B v θ H 0 * relativeNorm q Z D B v θ H 2 *
        relativeNorm q Z D B v θ H 5) ≠ 0 → w₂ (relativeNorm q Z D B v θ H 5) = 1) →
    (w₁ (relativeNorm q Z D B v θ H 4) ≠ 0 →
      w₂ (relativeNorm q Z D B v θ H 5) ≠ 0 →
      ∀ i, V i (relativeLog q Z D B v θ H i) = 1) →
    physicalKernel (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m q =
      (Z^(prefactorCenter m D B θ + 3*η) : ℝ) *
        (w₁ (relativeNorm q Z D B v θ H 4)*w₂ (relativeNorm q Z D B v θ H 5)) *
        ∫ p : Frequency × (Fin 6 → ℝ),
          familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p *
            pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
              (relativeLog q Z D B v θ H) p.1 p.2

theorem initial_physical_family_common_measure
    (W₁ W₂ : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b) (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (Φ : 𝓢(ℝ, ℂ)) (V : Fin 6 → ℝ → ℂ) (M : Fin 6 → ℝ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i))
    (hM : ∀ i, 0 ≤ M i) (hbox : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    let g := secondRootSchwartz V hV hS
    let g₁ := CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁
    let g₂ := CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z D B v m θ H η : ℝ, 0 < Z → 0 ≤ η*Real.log Z →
      ∃ b₃ : 𝓢(ℝ, ℂ), ∀ c₁ c₂ θ₁ θ₂ : ℝ, 0 < c₁ → 0 < c₂ →
      PhysicalIdentityAt W₁ W₂ Φ V g g₁ g₂ b₃ Z D B v m θ H η c₁ c₂ θ₁ θ₂ ∧
      Integrable (fun p : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ∧
      (1+Z^(radialCenter m H θ D B))^A * (∫ p : Frequency × (Fin 6 → ℝ),
        tripleHeight J p.1 * coordinateHeight J p.2 *
          ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) p‖) ≤
        C * ((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hsep⟩ := family_common_measure
    (CubicReflectionKernel.logSchwartz W₁ a b ha hs₁ hW₁)
    (CubicReflectionKernel.logSchwartz W₂ a b ha hs₂ hW₂)
    Φ V M hV hS hM hbox A J
  refine ⟨C, hC, ?_⟩
  intro Z D B v m θ H η hZ hL
  obtain ⟨b₃, hb₃⟩ := hsep (Z^(radialCenter m H θ D B)) (Real.rpow_pos_of_pos hZ _)
  refine ⟨b₃, ?_⟩
  intro c₁ c₂ θ₁ θ₂ hc₁ hc₂
  obtain ⟨he, hi, hbound⟩ := hb₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) hL
  refine ⟨?_, hi, hbound⟩
  intro w₁ w₂ q hq hw₁ hw₂ hcut
  rw [initial_kernel_restore _ _ w₁ w₂ Φ V hZ D B v m θ H η q hq hw₁ hw₂ hcut,
    normalizedProfile_eq_family W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂ Φ V hc₁ hc₂, he]

theorem fresh_cutoff_one_clippedSource (W w : ℝ → ℂ) (a b bclip A₀ B₀ A₂ B₂ : ℝ)
    (ha : 0 < a) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂) (hclip : 1 ≤ bclip)
    (hW : Function.support W ⊆ Set.Icc a b)
    (hw : ∀ x ∈ Set.Icc (a/(bclip*B₀*B₂)) (b/(A₀*A₂)), w x = 1)
    {c u v x : ℝ} (hc : 1 ≤ c) (hcb : c ≤ bclip)
    (hu : u ∈ Set.Icc A₀ B₀) (hv : v ∈ Set.Icc A₂ B₂) (hx : 0 < x)
    (θ : ℝ) (hs : clippedSource W c θ (u*v*x) ≠ 0) : w x = 1 := by
  exact fresh_cutoff_one W w a b bclip A₀ B₀ A₂ B₂ ha hA₀ hA₂ hclip hW hw
    hc hcb hu hv hx (mul_ne_zero_iff.mp hs).2

theorem clipped_column_ratio {Z : ℝ} (hZ : 0 < Z) (N q : ℝ) :
    q / Z^N = Z^(max 0 N-N) * (q / Z^(max 0 N)) := by
  rw [Real.rpow_sub hZ]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hZ N),
    ne_of_gt (Real.rpow_pos_of_pos hZ (max 0 N))]

theorem clipped_column_source_identity (w : ℝ → ℂ) {Z q : ℝ}
    (hZ : 0 < Z) (hq : 0 < q) (N θ : ℝ) :
    logPhase θ (Real.log (q/Z^N)) * w (q/Z^N) =
      logPhase θ (Real.log (Z^(max 0 N-N))) *
        clippedSource w (Z^(max 0 N-N)) θ (q/Z^(max 0 N)) := by
  rw [clipped_column_ratio hZ N q]
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hZ _))
    (ne_of_gt (div_pos hq (Real.rpow_pos_of_pos hZ _))), logPhase_add]
  unfold clippedSource
  ring

theorem retained_initial_clipping (w : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b) (hs : ContDiff ℝ ∞ w) (J : ℕ) :
    let g := CubicReflectionKernel.logSchwartz w a b ha hw hs
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z N q : ℝ, 1 < Z → 1 ≤ q → w (q/Z^N) ≠ 0 →
      let c := Z^(max 0 N-N)
      1 ≤ c ∧ c ≤ b ∧
      Function.support (fun x => w (c*x)) ⊆ Set.Icc (a/b) b ∧
      (∀ θ : ℝ, logPhase θ (Real.log (q/Z^N)) * w (q/Z^N) =
        logPhase θ (Real.log c) * clippedSource w c θ (q/Z^(max 0 N))) ∧
      (∀ θ : ℝ, Integrable (fun t : ℝ => (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ∧
        (∫ t : ℝ, (1+‖t‖)^J * ‖sourceDensity g c θ t‖) ≤
          C*(1+‖θ‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C, hC, hbound⟩ := sourceDensity_moment_uniform
    (CubicReflectionKernel.logSchwartz w a b ha hw hs) J
  refine ⟨C, hC, ?_⟩
  intro Z N q hZ hq hwitness
  obtain ⟨hc, hcb, hsupport, _⟩ := InverseClippingProfiles.retained_clipped_column
    w Z N q a b hZ hq ha hb hw hwitness
  refine ⟨hc, hcb, hsupport, ?_, fun θ => hbound _ θ⟩
  exact fun θ => clipped_column_source_identity w (zero_lt_one.trans hZ)
    (zero_lt_one.trans_le hq) N θ

end SevenEighths.InverseInitialProfile

end

end OAI
end OAIOriginalModule0515

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialKernelBridge
Source SHA256: 2f1dbd2141754f9c738c42be6f85e26a9ad99ed913d18faac09325882184fe89
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0516




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge ConcreteTraceCRT
open EisensteinSchwartzPoisson UniqueFactorizationMonoid CanonicalQuadraticSieve
open SevenEighths.InverseInitialPoissonBridge SevenEighths.InverseInitialOverlap
open SevenEighths.InverseInitialProfile
namespace SevenEighths.InverseInitialKernelBridge

local notation "Eis" => ActualEisensteinCubic.O
local notation "N" => fun I : Ideal Eis => (Ideal.absNorm I : ℝ)
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal Eis)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
  (hg : ∀ i, goodLambda ∉ P i)

def pairRow (S T : Finset ι) (h : Eis) : ℂ :=
  finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T) h

def pairGauss (S T : Finset ι) : ℂ :=
  canonicalNormalizedGauss (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val) (activeExponent S T)

def pairCoordinates (S T E : Finset ι) (h : Eis) : Fin 6 → ℝ :=
  ![N (∏ i ∈ S∩T,P i), N (∏ i ∈ E,P i), 1, ‖eisEmbedding h‖^2,
    N (∏ i ∈ S\T,P i), N (∏ i ∈ T\S,P i)]

omit [∀ i, (P i).IsMaximal] in
theorem common_left_product (S T : Finset ι) :
    (∏ i ∈ S∩T,P i)*(∏ i ∈ S\T,P i) = ∏ i ∈ S,P i := by
  rw [mul_comm,←Finset.prod_union (Finset.disjoint_sdiff_inter S T),Finset.sdiff_union_inter]

omit [∀ i, (P i).IsMaximal] in
theorem common_right_product (S T : Finset ι) :
    (∏ i ∈ S∩T,P i)*(∏ i ∈ T\S,P i) = ∏ i ∈ T,P i := by
  simpa only [Finset.inter_comm] using common_left_product P T S

omit [∀ i, (P i).IsMaximal] in
theorem conductor_norm (S T : Finset ι) :
    ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ =
      Real.sqrt (N (∏ i ∈ S\T,P i)*N (∏ i ∈ T\S,P i)) := by
  have hn := activePrimeModulus_norm_sq P S T
  have hd : Disjoint (S\T) (T\S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  simp only [activeSupport,Finset.prod_union hd,map_mul,Nat.cast_mul] at hn
  rw [←hn,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  rfl

def pairArithmetic (S T E : Finset ι) (h : Eis) : ℂ :=
  pairGauss P hinj hg S T * (moebius (∏ i ∈ E,P i) : ℂ) *
    pairRow P hg S T (primeSubsetGenerator P E) * star (pairRow P hg S T h)

def pairMode (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (h : Eis) : ℂ :=
  ((Y : ℂ)*pairGauss P hinj hg S T /
    (‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖ : ℂ)) *
    (((moebius (∏ i ∈ E,P i) : ℂ)*pairRow P hg S T (primeSubsetGenerator P E) /
      (‖eisEmbedding (primeSubsetGenerator P E)‖^2 : ℝ)) *
      (star (pairRow P hg S T h)*paperRadialFourier Φ
        (Y*‖eisEmbedding h‖^2/(‖eisEmbedding (primeSubsetGenerator P E)‖^2 *
          ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖^2))))

theorem pairKernel_eq_modes (S T : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    squarefreePairPoissonKernel P hinj hg S T Φ Y =
      ∑ E ∈ (S∩T).powerset, ∑' h : Eis, pairMode P hinj hg S T E Φ Y h := by
  simp only [squarefreePairPoissonKernel,pairMode,pairGauss,pairRow,
    tsum_mul_left,Finset.mul_sum]

private theorem physicalKernel_vector (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (Z D m q₀ q₁ q₂ q₃ q₄ q₅ : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m ![q₀,q₁,q₂,q₃,q₄,q₅] =
      ((Z^(-D)*Z^m/(q₁*q₂*Real.sqrt (q₄*q₅)) : ℝ) : ℂ)*
        W₁ (q₀*q₂*q₄/Z^D)*W₂ (q₀*q₂*q₅/Z^D)*
          paperRadialFourier Φ (Z^m*q₃/(q₁*q₂^2*q₄*q₅)) := rfl

theorem pairMode_physical (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ))
    (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) (h : Eis) :
    (Z^(-D) : ℝ)*W₁ (N (∏ i ∈ S,P i)/Z^D)*W₂ (N (∏ i ∈ T,P i)/Z^D)*
      pairMode P hinj hg S T E Φ (Z^m) h =
    pairArithmetic P hinj hg S T E h *
      physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h) := by
  have hs := congrArg N (common_left_product P S T)
  have ht := congrArg N (common_right_product P S T)
  simp only [map_mul,Nat.cast_mul] at hs ht
  have hc := conductor_norm P S T
  have hc2 := congrArg (fun x : ℝ => x^2) hc
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at hc2
  unfold pairMode pairArithmetic pairCoordinates
  rw [physicalKernel_vector]
  simp only [mul_one,one_pow,primeSubsetGenerator_norm_sq,hc2]
  rw [hc,hs,ht]
  push_cast
  ring_nf

theorem pairKernel_physical (S T : Finset ι) (Φ : 𝓢(ℝ,ℂ))
    (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) :
    (Z^(-D) : ℝ)*W₁ (N (∏ i ∈ S,P i)/Z^D)*W₂ (N (∏ i ∈ T,P i)/Z^D)*
      squarefreePairPoissonKernel P hinj hg S T Φ (Z^m) =
    ∑ E ∈ (S∩T).powerset, ∑' h : Eis,
      pairArithmetic P hinj hg S T E h *
        physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h) := by
  rw [pairKernel_eq_modes]
  simp only [Finset.mul_sum,←tsum_mul_left]
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro h
  exact pairMode_physical P hinj hg S T E Φ W₁ W₂ Z D m h

def idealPhysicalPair (F : Finset (Ideal Eis)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ Q ∈ normalizedFactors I, goodLambda ∉ Q)
    (I J : Ideal Eis) (Φ : 𝓢(ℝ,ℂ)) (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) : ℂ := by
  letI : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F hFpos
  exact ∑ E ∈ (idealSupport F I ∩ idealSupport F J).powerset, ∑' h : Eis,
    pairArithmetic (fun q : primePool F => q.val) Subtype.val_injective
      (primePool_good F hFgood) (idealSupport F I) (idealSupport F J) E h *
      physicalKernel W₁ W₂ Φ Z D m
        (pairCoordinates (fun q : primePool F => q.val) (idealSupport F I) (idealSupport F J) E h)

theorem ideal_conductor_norm_sq (F : Finset (Ideal Eis)) {I J : Ideal Eis}
    (hI : I ∈ F) (hJ : J ∈ F) (hsI : Squarefree I) (hsJ : Squarefree J) :
    ‖eisEmbedding (finitePrimeModulus (activePrimes (fun q : primePool F => q.val)
      (idealSupport F I) (idealSupport F J)))‖^2 *
        (N (primeSubsetProduct F (idealSupport F I∩idealSupport F J)))^2 = N I*N J :=
  idealPairPoisson_conductor_norm_sq F hI hJ hsI hsJ

theorem idealPairKernel_physical (F : Finset (Ideal Eis)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ Q ∈ normalizedFactors I, goodLambda ∉ Q)
    {I J : Ideal Eis} (hI : I ∈ F) (hJ : J ∈ F) (hsI : Squarefree I) (hsJ : Squarefree J)
    (Φ : 𝓢(ℝ,ℂ)) (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) :
    (Z^(-D) : ℝ)*W₁ (N I/Z^D)*W₂ (N J/Z^D)*
      idealPairPoissonKernel F hFpos hFgood I J Φ (Z^m) =
      idealPhysicalPair F hFpos hFgood I J Φ W₁ W₂ Z D m := by
  let : ∀ q : primePool F, q.val.IsMaximal := primePool_maximal F hFpos
  simpa only [idealPairPoissonKernel,idealPhysicalPair,
    idealSupport_product_eq F hI hsI,idealSupport_product_eq F hJ hsJ] using
    pairKernel_physical (fun q : primePool F => q.val) Subtype.val_injective
      (primePool_good F hFgood) (idealSupport F I) (idealSupport F J) Φ W₁ W₂ Z D m

def bareOverlapCoefficient (P j : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (c : Ideal Eis) : ℂ :=
  (moebius c : ℂ)*η c*a (reconstruct P j c)

def maskedOverlapWindow (P j : Ideal Eis) (W : ℝ → ℂ) (Z z G : ℝ) (x : ℝ) : ℂ :=
  W ((x/Z^G)/((N (residual P j))/Z^(z-G)))

def residualOverlapWindow (P j : Ideal Eis) (W : ℝ → ℂ) (Z z G : ℝ) (x : ℝ) : ℂ :=
  W (((N j/Z^G)*x)/((N (residual P j))/Z^(z-G)))

theorem overlapCoefficient_masked (P j c : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) :
    overlapResidualCoefficient P j η a W Z r z G c =
      bareOverlapCoefficient P j η a c *
        maskedOverlapWindow P j W Z z G (N (j*c)/Z^(r+z-2*G)) := by
  unfold overlapResidualCoefficient bareOverlapCoefficient maskedOverlapWindow
  simp only [map_mul,Nat.cast_mul]
  congr 2
  ring_nf

theorem overlapCoefficient_residual (P j c : Ideal Eis) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) (Z r z G : ℝ) :
    overlapResidualCoefficient P j η a W Z r z G c =
      bareOverlapCoefficient P j η a c *
        residualOverlapWindow P j W Z z G (N c/Z^(r+z-2*G)) := rfl

theorem original_fixed_overlap_physical
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G m : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) :
    let C := columns S P j
    let F := C.image (fun c => j*c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact masked_columns_admissible S hP hj hS hc
    let b := bareOverlapCoefficient P j η a
    let V := maskedOverlapWindow P j W Z z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖originalFixedPolynomial S P j η a W Z r z u‖^2 : ℝ)) =
      ((Z^(-2*G)*‖η j‖^4 : ℝ) : ℂ)*
        ∑ c ∈ C, ∑ d ∈ C, (star (b c)*b d)*
          idealPhysicalPair F (pool_positive F hF) (pool_good F hF) (j*c) (j*d)
            Φ (fun x => star (V x)) V Z (r+z-2*G) m := by
  intro C F hF b V
  rw [original_fixed_overlap_smoothed_poisson S hP hj hS η a W hZ r z G Φ
    (Z^m) (Real.rpow_pos_of_pos hZ m)]
  have he : Z^(-2*G-(r+z-2*G)) = Z^(-2*G)*Z^(-(r+z-2*G)) := by
    rw [←Real.rpow_add hZ]
    congr 1
  rw [he]
  simp only [Complex.ofReal_mul]
  rw [show ((Z^(-2*G):ℝ):ℂ)*((Z^(-(r+z-2*G)):ℝ):ℂ)*↑(‖η j‖^4) =
    (((Z^(-2*G):ℝ):ℂ)*↑(‖η j‖^4))*((Z^(-(r+z-2*G)):ℝ):ℂ) from by ring_nf,mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  have hcF : j*c ∈ F := Finset.mem_image.mpr ⟨c,hc,rfl⟩
  have hdF : j*d ∈ F := Finset.mem_image.mpr ⟨d,hd,rfl⟩
  have hker := idealPairKernel_physical F (pool_positive F hF) (pool_good F hF)
    hcF hdF (hF _ hcF).2.1 (hF _ hdF).2.1 Φ (fun x => star (V x)) V Z (r+z-2*G) m
  rw [overlapCoefficient_masked,overlapCoefficient_masked]
  simp only [star_mul]
  dsimp only [b,V,F,C] at hker ⊢
  rw [←hker]
  ring_nf

theorem residual_normalized_physical
    (S : Finset (Ideal Eis)) {P j : Ideal Eis} (hP : Admissible P) (hj : j ∣ P)
    (hS : ∀ n ∈ S, Squarefree n → Supported n) (η : Ideal Eis →* ℂ)
    (a : Ideal Eis → ℂ) (W : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (r z G m : ℝ)
    (Φ : 𝓢(ℝ,ℂ)) :
    let C := columns S P j
    let F := C.image (fun c => c)
    let hF : ∀ I ∈ F, Admissible I := fun I hI => by
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hI
      exact columns_admissible S hP hj hS hc
    let b := bareOverlapCoefficient P j η a
    let V := residualOverlapWindow P j W Z z G
    (∑' u : Eis, Φ (‖eisEmbedding u‖^2/Z^m)*
      (‖residualNormalizedPolynomial S P j η a W Z r z G u‖^2 : ℝ)) =
        ∑ c ∈ C, ∑ d ∈ C, (b c*star (b d))*
          idealPhysicalPair F (pool_positive F hF) (pool_good F hF) c d
            Φ V (fun x => star (V x)) Z (r+z-2*G) m := by
  intro C F hF b V
  rw [residual_normalized_smoothed_poisson S hP hj hS η a W hZ r z G Φ
    (Z^m) (Real.rpow_pos_of_pos hZ m)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  have hcF : c ∈ F := Finset.mem_image.mpr ⟨c,hc,rfl⟩
  have hdF : d ∈ F := Finset.mem_image.mpr ⟨d,hd,rfl⟩
  have hker := idealPairKernel_physical F (pool_positive F hF) (pool_good F hF)
    hcF hdF (hF _ hcF).2.1 (hF _ hdF).2.1 Φ V (fun x => star (V x)) Z (r+z-2*G) m
  rw [overlapCoefficient_residual,overlapCoefficient_residual]
  simp only [star_mul]
  dsimp only [b,V,F,C] at hker ⊢
  rw [←hker]
  ring_nf

def physicalCoordinates (C d s n₁ n₂ : Ideal Eis) (h : Eis) : Fin 6 → ℝ :=
  ![N C,N d,N s,‖eisEmbedding h‖^2,N n₁,N n₂]

theorem physicalCoordinates_pos (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (hC : C ≠ 0) (hd : d ≠ 0) (hs : s ≠ 0) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) (hh : h ≠ 0) :
    ∀ i, 0 < physicalCoordinates C d s n₁ n₂ h i := by
  have hp (I : Ideal Eis) (hI : I ≠ 0) : 0 < N I := by
    change 0 < (Ideal.absNorm I : ℝ)
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hp C hC
  · exact hp d hd
  · exact hp s hs
  · exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh))
  · exact hp n₁ h₁
  · exact hp n₂ h₂

theorem physicalKernel_common_factor (C d s n₁ n₂ : Ideal Eis) (h : Eis)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ) :
    physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d 1 (s*n₁) (s*n₂) h) =
      physicalKernel W₁ W₂ Φ Z D m (physicalCoordinates C d s n₁ n₂ h) := by
  have hroot : Real.sqrt ((N s*N n₁)*(N s*N n₂)) = N s*Real.sqrt (N n₁*N n₂) := by
    rw [show (N s*N n₁)*(N s*N n₂) = (N s)^2*(N n₁*N n₂) from by ring_nf,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  unfold physicalCoordinates
  rw [physicalKernel_vector,physicalKernel_vector]
  simp only [map_one,Nat.cast_one,map_mul,Nat.cast_mul,mul_one,one_pow]
  rw [hroot]
  have hl : N C*(N s*N n₁)/Z^D = N C*N s*N n₁/Z^D := by ring_nf
  have hr : N C*(N s*N n₂)/Z^D = N C*N s*N n₂/Z^D := by ring_nf
  have hk : Z^m*‖eisEmbedding h‖^2/(N d*(N s*N n₁)*(N s*N n₂)) =
      Z^m*‖eisEmbedding h‖^2/(N d*(N s)^2*N n₁*N n₂) := by ring_nf
  rw [hl,hr,hk]
  push_cast
  ring_nf

omit [∀ i, (P i).IsMaximal] in

theorem pairCoordinates_eq (S T E : Finset ι) (h : Eis) :
    pairCoordinates P S T E h = physicalCoordinates
      (∏ i ∈ S∩T,P i) (∏ i ∈ E,P i) 1 (∏ i ∈ S\T,P i) (∏ i ∈ T\S,P i) h := by
  simp only [pairCoordinates,physicalCoordinates,map_one,Nat.cast_one]

theorem pairArithmetic_residual_rows (S T E : Finset ι) (h : Eis) :
    pairArithmetic P hinj hg S T E h =
      pairGauss P hinj hg S T * (moebius (∏ i ∈ E,P i) : ℂ) *
        (star (finiteSquarefreeRow P hg (S\T) (primeSubsetGenerator P E)) *
          finiteSquarefreeRow P hg (T\S) (primeSubsetGenerator P E)) *
        (finiteSquarefreeRow P hg (S\T) h * star (finiteSquarefreeRow P hg (T\S) h)) := by
  have he (u : Eis) : pairRow P hg S T u =
      star (finiteSquarefreeRow P hg (S\T) u)*finiteSquarefreeRow P hg (T\S) u :=
    finiteSexticRow_activeSupport P hg S T u
  simp only [pairArithmetic,he,star_mul,star_star]
  ring_nf

theorem pairMode_summable (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (pairMode P hinj hg S T E Φ Y) := by
  let den := ‖eisEmbedding (primeSubsetGenerator P E)‖^2 *
    ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖^2
  have hd : 0 < den := mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E))))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero _))))
  have hs := activeRow_paperFourier_summable P hg S T Φ (Y/den) (div_pos hY hd)
  have he (h : Eis) : (Y/den)*‖eisEmbedding h‖^2 = Y*‖eisEmbedding h‖^2/den := by ring_nf
  simp_rw [he] at hs
  exact (hs.mul_left _).mul_left _

theorem pairMode_zero_split (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' h : Eis, pairMode P hinj hg S T E Φ Y h) =
      pairMode P hinj hg S T E Φ Y 0 +
        ∑' h : Eis, if h=0 then 0 else pairMode P hinj hg S T E Φ Y h :=
  (pairMode_summable P hinj hg S T E Φ Y hY).tsum_eq_add_tsum_ite 0

theorem physicalMode_zero_split (S T E : Finset ι) (Φ : 𝓢(ℝ,ℂ))
    (W₁ W₂ : ℝ → ℂ) (Z D m : ℝ) (hZ : 0 < Z) :
    (∑' h : Eis, pairArithmetic P hinj hg S T E h *
      physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h)) =
      pairArithmetic P hinj hg S T E 0 *
        physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E 0) +
      ∑' h : Eis, if h=0 then 0 else pairArithmetic P hinj hg S T E h *
        physicalKernel W₁ W₂ Φ Z D m (pairCoordinates P S T E h) := by
