import P5HybridClosurePorts

/-! The actual tied-factor law at the distinguished MAIN coordinate.
All variable symbols remain independent. Work with the exact primitive
sample and literal cell maps already verified in the companion replay. -/
namespace Paper5.HybridClosure
open scoped BigOperators
set_option maxSynthPendingDepth 16
open J1MainSourceLabels J1MainSourceCollision DiagonalAbundance

variable {V : Type*} [Fintype V] [DecidableEq V]

def triangleTie {E : Finset (TriVertex V×TriVertex V)} : ClauseIndex E→Option V
  | .inl v => some v.1
  | .inr _ => none

private theorem triangle_tied_tag_injective (E : Finset (TriVertex V×TriVertex V)) (v : V) :
    ∃ f : (tagFibre ((triangleTie (E:=E)) ∘ cloneFactor E) v)→Fin 3, Function.Injective f := by
  let f := fun p : (tagFibre ((triangleTie (E:=E)) ∘ cloneFactor E) v) =>
    match p.val with
    | .inl w => w.2
    | .inr _ => 0
  refine ⟨f,?_⟩
  intro p q h
  rcases p with ⟨p,hp⟩
  rcases q with ⟨q,hq⟩
  have ep := (Finset.mem_filter.mp hp).2
  have eq := (Finset.mem_filter.mp hq).2
  cases p with
  | inl p =>
    cases q with
    | inl q =>
      apply Subtype.ext
      apply congrArg Sum.inl
      exact Prod.ext
        ((Option.some.inj ep).trans (Option.some.inj eq).symm) h
    | inr q => cases q <;> cases eq
  | inr p => cases p <;> cases ep

theorem triangle_tied_fibre (E : Finset (TriVertex V×TriVertex V)) (v : V) :
    (tagFibre ((triangleTie (E:=E)) ∘ cloneFactor E) v).card ≤ 3 := by
  obtain ⟨f,hf⟩ := triangle_tied_tag_injective E v
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective f hf

omit [DecidableEq V] in
theorem triangle_tied_slots (E : Finset (TriVertex V×TriVertex V)) :
    (tiedSlots ((triangleTie (E:=E)) ∘ cloneFactor E)).card = Fintype.card (TriVertex V) := by
  have h : tiedSlots ((triangleTie (E:=E)) ∘ cloneFactor E) =
      Finset.univ.map (MainClonedCNF.pinPort E) := by
    ext port
    rcases port with p|q
    · simp [tiedSlots,triangleTie,cloneFactor,MainClonedCNF.pinPort]
    · rcases q with q|q <;> simp [tiedSlots,triangleTie,cloneFactor,MainClonedCNF.pinPort]
  rw [h,Finset.card_map,Finset.card_univ]

theorem mean_le_select {Ω : Type*} [Fintype Ω] [Nonempty Ω] (F : Ω→ℚ) :
    ∃ z, F z≤mean F := by
  obtain ⟨z,_,hz⟩ := Finset.exists_min_image Finset.univ F Finset.univ_nonempty
  have h := mean_mono (fun _ => F z) F (fun x => hz x (Finset.mem_univ _))
  rw [mean_const] at h
  exact ⟨z,h⟩

theorem deviation_load_bound {E C : Type*} [Fintype E] [Fintype C] [Nonempty C]
    (color : E→C) (B : ℚ)
    (hDev : deviation color ≤ 2*(Fintype.card E:ℚ)*B)
    (hNum : 2*B*(Fintype.card C:ℚ)^2 ≤ (Fintype.card E:ℚ)) (c : C) :
    load color c ≤ 2*(Fintype.card E:ℚ)/(Fintype.card C:ℚ) := by
  let d : ℚ := Fintype.card C
  let m : ℚ := Fintype.card E
  have hd : 0<d := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card C)
  have hsq : (load color c-m/d)^2 ≤ deviation color := by
    unfold deviation
    exact Finset.single_le_sum (f := fun x => (load color x-m/d)^2)
      (fun x _ => sq_nonneg _) (Finset.mem_univ c)
  have hm : 0≤m := by dsimp [m]; positivity
  have hinv : 2*m*B ≤ (m/d)^2 := by
    have h := mul_le_mul_of_nonneg_right hNum hm
    rw [div_pow,le_div_iff₀ (pow_pos hd 2)]
    nlinarith only [h]
  have hE := hsq.trans (hDev.trans hinv)
  have hmD : 0≤m/d := div_nonneg hm hd.le
  have h1 : load color c-m/d ≤ m/d := by
    by_contra! hn
    have hpos := mul_pos (sub_pos.mpr hn) (show 0<load color c-m/d+m/d by linarith only [hn,hmD])
    nlinarith only [hpos,hE]
  change load color c≤2*m/d
  rw [mul_div_assoc,two_mul]
  exact (sub_le_iff_le_add).mp h1

section Main
variable {I S : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype S] [Nonempty S]
variable [Nonempty V]

abbrev MainPrimitives (E : Finset (TriVertex V×TriVertex V)) (I : Type*) :=
  Primitive (Clone (TriVertex V)) (ClauseIndex E) V I

set_option maxHeartbeats 1500000 in
theorem main_actual_tied_placement (E : Finset (TriVertex V×TriVertex V))
    (cubic : ∀v,GraphCutMoments.degree E v=3) (t : I)
    (hCells : 2*5*(Fintype.card (Draw I S):ℚ)^2 ≤ 12*(Fintype.card (TriVertex V):ℚ))
    (hGroup : 2*(Fintype.card I:ℚ)*(Fintype.card S:ℚ)^2 ≤ 4*(Fintype.card (TriVertex V):ℚ)) :
    ∃ z : MainPrimitives E I→S,
      (∀ v, factorWord t triangleTie z (.inl v) t = z (.inr (.inr v.1))) ∧
      (∀ u, load (literalCell t triangleTie (cloneOwner E cubic) (cloneFactor E) z) u ≤
        2*(12*(Fintype.card (TriVertex V):ℚ))/(Fintype.card (Draw I S):ℚ)) ∧
      (∀ j g,load (fun v : Clone (TriVertex V) => variableWord z v j) g ≤
        2*(4*(Fintype.card (TriVertex V):ℚ))/(Fintype.card S:ℚ)) := by
  letI : DecidableEq (E⊕Clone (TriVertex V)) :=
    @instDecidableEqSum E (Clone (TriVertex V)) inferInstance inferInstance
  letI : DecidableEq (ClauseIndex E) :=
    @instDecidableEqSum (TriVertex V) (E⊕Clone (TriVertex V)) inferInstance inferInstance
  letI : DecidableEq ((ClauseIndex E×I)⊕V) :=
    @instDecidableEqSum (ClauseIndex E×I) V inferInstance inferInstance
  letI : DecidableEq (MainPrimitives E I) :=
    @instDecidableEqSum (Clone (TriVertex V)×I) ((ClauseIndex E×I)⊕V) inferInstance inferInstance
  letI : DecidableEq ((E×Bool)⊕(TriVertex V×Fin 4×Bool)) :=
    @instDecidableEqSum (E×Bool) (TriVertex V×Fin 4×Bool) inferInstance inferInstance
  letI : DecidableEq (MainClonedCNF.Port E) :=
    @instDecidableEqSum (TriVertex V) ((E×Bool)⊕(TriVertex V×Fin 4×Bool)) inferInstance inferInstance
  let phi := incidenceCost (S:=S) t triangleTie (cloneOwner E cubic) (cloneFactor E)
  let xi := variableCost (V:=Clone (TriVertex V)) (F:=ClauseIndex E) (B:=V) (I:=I) (S:=S)
  let N : ℚ := Fintype.card (TriVertex V)
  let M : ℚ := 12*N
  let n : ℚ := 4*N
  let Q : ℚ := Fintype.card I
  have hN : 0<N := by dsimp [N]; exact_mod_cast (Fintype.card_pos : 0<Fintype.card (TriVertex V))
  have hQ : 0<Q := by dsimp [Q]; exact_mod_cast (Fintype.card_pos : 0<Fintype.card I)
  have hM : 0<M := by dsimp [M]; positivity
  have hn : 0<n := by dsimp [n]; positivity
  have hports : (Fintype.card (MainClonedCNF.Port E):ℚ)=M := by
    dsimp [M,N]
    exact_mod_cast MainClonedCNF.port_card E cubic
  have hclones : (Fintype.card (Clone (TriVertex V)):ℚ)=n := by
    simp [n,N,Clone,mul_comm]
  have hphi₀ := expected_main_phi (E:=MainClonedCNF.Port E) (V:=Clone (TriVertex V))
    (F:=ClauseIndex E) (B:=V) (S:=S) t triangleTie (cloneOwner E cubic) (cloneFactor E)
    (Fintype.card (TriVertex V))
    (fun v => (every_clone_three E cubic v).le) (every_clause_at_most_two E)
    (triangle_tied_fibre E) (triangle_tied_slots E).le
  rw [hports] at hphi₀
  change mean phi ≤ 4*M+2*N at hphi₀
  have hphi : mean phi≤5*M := by
    unfold M at *
    linarith only [hphi₀,hN]
  have hxi : mean xi≤Q*n := by
    have h₀ := expected_variableCost (V:=Clone (TriVertex V)) (F:=ClauseIndex E) (B:=V) (I:=I) (S:=S)
    rw [hclones] at h₀
    exact h₀
  let f := fun z => (5*M)⁻¹*phi z+(Q*n)⁻¹*xi z
  have hMean : mean f≤2 := by
    unfold f
    rw [mean_lin_add,mean_scale,mean_scale]
    have hm5 : 0<5*M := by positivity
    have hqn : 0<Q*n := mul_pos hQ hn
    rw [inv_mul_eq_div,inv_mul_eq_div]
    have h₁ := (div_le_iff₀ hm5).mpr (by simpa using hphi : mean phi≤1*(5*M))
    have h₂ := (div_le_iff₀ hqn).mpr (by simpa using hxi : mean xi≤1*(Q*n))
    linarith only [h₁,h₂]
  obtain ⟨z,hz⟩ := mean_le_select f
  have hz2 := hz.trans hMean
  have hphi0 : 0≤phi z := deviation_nonneg _
  have hxi0 : 0≤xi z := Finset.sum_nonneg (fun _ _ => deviation_nonneg _)
  have hφ : phi z≤2*M*5 := by
    have h := (show (5*M)⁻¹*phi z≤2 by
      have hnon := mul_nonneg (inv_nonneg.mpr (mul_pos hQ hn).le) hxi0
      exact (le_add_of_nonneg_right hnon).trans hz2)
    rw [inv_mul_eq_div,div_le_iff₀ (show 0<5*M by positivity)] at h
    linarith only [h]
  have hξ : xi z≤2*n*Q := by
    have h := (show (Q*n)⁻¹*xi z≤2 by
      have hnon := mul_nonneg (inv_nonneg.mpr (mul_nonneg (by decide : (0:ℚ)≤5) hM.le)) hphi0
      exact (le_add_of_nonneg_left hnon).trans hz2)
    rw [inv_mul_eq_div,div_le_iff₀ (mul_pos hQ hn)] at h
    linarith only [h]
  refine ⟨z,?_,?_,?_⟩
  · intro v
    simp [factorWord,factorKey,triangleTie]
  · intro u
    have hd : phi z≤2*(Fintype.card (MainClonedCNF.Port E):ℚ)*5 := by rw [hports]; exact hφ
    have hnum : 2*5*(Fintype.card (Draw I S):ℚ)^2≤(Fintype.card (MainClonedCNF.Port E):ℚ) := by
      rw [hports]
      exact hCells
    simpa only [hports] using deviation_load_bound _ 5 hd hnum u
  · intro j g
    have h := Finset.single_le_sum (s := (Finset.univ : Finset I))
      (f := fun j => deviation (fun v : Clone (TriVertex V) => variableWord z v j))
      (fun j _ => deviation_nonneg _) (Finset.mem_univ j)
    have hd : deviation (fun v : Clone (TriVertex V) => variableWord z v j) ≤
        2*(Fintype.card (Clone (TriVertex V)):ℚ)*Q := by
      rw [hclones]
      exact h.trans hξ
    have hnum : 2*Q*(Fintype.card S:ℚ)^2≤(Fintype.card (Clone (TriVertex V)):ℚ) := by
      rw [hclones]
      exact hGroup
    simpa only [hclones] using deviation_load_bound _ Q hd hnum g
end Main

#print axioms triangle_tied_fibre
#print axioms triangle_tied_slots
#print axioms deviation_load_bound
#print axioms main_actual_tied_placement
end Paper5.HybridClosure