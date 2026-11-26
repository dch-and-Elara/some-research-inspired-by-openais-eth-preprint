
import P5HybridMainOnlyCount
import P5HybridClosureMainSeats

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-! The very same source sample controls both phi and the unchanged xi.
The resulting actual cell labels determine occupied copied seats. -/
namespace Paper5.HybridMainOnly
open scoped Classical BigOperators
open Paper5.HybridClosure J1MainSourceLabels J1MainSourceCollision DiagonalAbundance
open J1MainSourcePlacement J1MainSourceBridge EmpiricalCutMoments ProductVariance
noncomputable section

theorem simultaneous_nonnegative_mean {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (φ ξ : Ω→ℚ) (A B : ℚ) (ha : 0<A) (hb : 0<B)
    (hnφ : ∀ z,0≤φ z) (hnξ : ∀ z,0≤ξ z)
    (hφ : mean φ≤A) (hξ : mean ξ≤B) :
    ∃ z, φ z≤2*A ∧ ξ z≤2*B ∧ φ z/A+ξ z/B≤2 := by
  let J : Ω→ℚ := fun z=>A⁻¹*φ z+B⁻¹*ξ z
  have hJ : mean J≤2 := by
    unfold J
    rw [mean_lin_add,mean_scale,mean_scale,inv_mul_eq_div,inv_mul_eq_div]
    have hx : mean φ/A≤1 := (div_le_iff₀ ha).mpr (by simpa using hφ)
    have hy : mean ξ/B≤1 := (div_le_iff₀ hb).mpr (by simpa using hξ)
    linarith only [hx,hy]
  obtain ⟨z,hz⟩ := mean_le_select J
  have h := hz.trans hJ
  change A⁻¹*φ z+B⁻¹*ξ z≤2 at h
  have hu : A⁻¹*φ z≤2 := (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hb.le) (hnξ z))).trans h
  have hv : B⁻¹*ξ z≤2 := (le_add_of_nonneg_left (mul_nonneg (inv_nonneg.mpr ha.le) (hnφ z))).trans h
  rw [inv_mul_eq_div,div_le_iff₀ ha] at hu
  rw [inv_mul_eq_div,div_le_iff₀ hb] at hv
  rw [inv_mul_eq_div,inv_mul_eq_div] at h
  exact ⟨z,hu,hv,h⟩

variable {V I S : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype S] [Nonempty S]
variable (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "F" => (replacedEdges E cubic)
local notation "Port" => (MainClonedCNF.Port F)
local notation "reg" => (replaced_cubic E cubic loopless)
local notation "NV" => (Fintype.card (TriVertex V))

abbrev SourceCell (t u : I) (z : SourcePrimitive E cubic I→S) : Port→Draw I S :=
  twoCell (literalTags E cubic t u) (cloneOwner F reg) (cloneFactor F) z

abbrev SourceVarGroup (z : SourcePrimitive E cubic I→S) (j : I) : Clone (TriVertex V)→S :=
  fun v=>variableWord z v j

def sourceXi (z : SourcePrimitive E cubic I→S) : ℚ :=
  variableCost (V:=Clone (TriVertex V)) («F»:=ClauseIndex F) (B:=V⊕E) z

abbrev actualPinWord (t u : I) (z : SourcePrimitive E cubic I→S) (p : TriVertex V) : I→S :=
  factorAt (literalTags E cubic t u) z (.inl p)

theorem source_pin_first (t u : I) (z : SourcePrimitive E cubic I→S) (p : TriVertex V) :
    actualPinWord E cubic t u z p t=mainPinColor (fun v=>z (.inr (.inr (.inl v)))) p := by
  simp [factorAt,factorKeyAt,literal_tags_first,mainPinColor]

theorem source_pin_second (t u : I) (tu : t≠u) (z : SourcePrimitive E cubic I→S) (p : TriVertex V) :
    actualPinWord E cubic t u z p u=
      dPinColor E cubic (fun e=>z (.inr (.inr (.inr e)))) p := by
  simp [factorAt,factorKeyAt,literal_tags_second E cubic t u tu,dPinColor]

theorem simultaneous_source_loads (t u : I)
    (hCells : 2*5*(Fintype.card (Draw I S):ℚ)^2 ≤ 12*(NV:ℚ))
    (hGroup : 2*(Fintype.card I:ℚ)*(Fintype.card S:ℚ)^2 ≤ 4*(NV:ℚ)) :
    ∃ z : SourcePrimitive E cubic I→S,
      sourcePhi E cubic loopless t u z≤2*(12*(NV:ℚ))*5 ∧
      sourceXi E cubic z≤2*(4*(NV:ℚ))*(Fintype.card I:ℚ) ∧
      sourcePhi E cubic loopless t u z/(5*(12*(NV:ℚ)))+
        sourceXi E cubic z/((Fintype.card I:ℚ)*(4*(NV:ℚ)))≤2 ∧
      (∀ c, load (SourceCell E cubic loopless t u z) c≤
        2*(12*(NV:ℚ))/(Fintype.card (Draw I S):ℚ)) ∧
      (∀ j g,load (SourceVarGroup E cubic z j) g≤2*(4*(NV:ℚ))/(Fintype.card S:ℚ)) := by
  let φ := sourcePhi (S:=S) E cubic loopless t u
  let ξ := sourceXi (I:=I) (S:=S) E cubic
  let M : ℚ := 12*(NV:ℚ)
  let n : ℚ := 4*(NV:ℚ)
  let Q : ℚ := Fintype.card I
  have hp : (Fintype.card Port:ℚ)=M := by
    dsimp [M]
    exact_mod_cast MainClonedCNF.port_card F reg
  have hn : (Fintype.card (Clone (TriVertex V)):ℚ)=n := by simp [n,Clone,mul_comm]
  have hN : 0<(NV:ℚ) := by exact_mod_cast (Fintype.card_pos : 0<NV)
  have hQ : 0<Q := by dsimp [Q]; exact_mod_cast (Fintype.card_pos : 0<Fintype.card I)
  have hm : 0<5*M := by dsimp [M]; positivity
  have hq : 0<Q*n := mul_pos hQ (by dsimp [n]; positivity)
  have hφ : mean φ≤5*M := by
    have h := actual_main_only_expectation (S:=S) E cubic loopless t u
    rw [hp] at h
    dsimp [M] at h ⊢
    linarith only [h,hN]
  have hξ : mean ξ≤Q*n := by
    have h := expected_variableCost (V:=Clone (TriVertex V)) («F»:=ClauseIndex F) (B:=V⊕E) (I:=I) (S:=S)
    rw [hn] at h
    exact h
  obtain ⟨z,hzφ,hzξ,hJ⟩ := simultaneous_nonnegative_mean φ ξ _ _ hm hq
    (fun _=>deviation_nonneg _) (fun _=>Finset.sum_nonneg fun _ _=>deviation_nonneg _) hφ hξ
  have hφ' : φ z≤2*M*5 := by linarith only [hzφ]
  have hξ' : ξ z≤2*n*Q := by linarith only [hzξ]
  refine ⟨z,hφ',hξ',hJ,?_,?_⟩
  · intro c
    have hd : φ z≤2*(Fintype.card Port:ℚ)*5 := by rw [hp]; exact hφ'
    have hg : 2*5*(Fintype.card (Draw I S):ℚ)^2≤(Fintype.card Port:ℚ) := by rw [hp]; exact hCells
    simpa only [hp] using deviation_load_bound (SourceCell E cubic loopless t u z) 5 hd hg c
  · intro j g
    have h := Finset.single_le_sum (s:=(Finset.univ : Finset I))
      (f:=fun k=>deviation (SourceVarGroup E cubic z k))
      (fun k _=>deviation_nonneg (SourceVarGroup E cubic z k)) (Finset.mem_univ j)
    have hd : deviation (SourceVarGroup E cubic z j)≤2*(Fintype.card (Clone (TriVertex V)):ℚ)*Q := by
      rw [hn]
      exact h.trans hξ'
    have hg : 2*Q*(Fintype.card S:ℚ)^2≤(Fintype.card (Clone (TriVertex V)):ℚ) := by rw [hn]; exact hGroup
    simpa only [hn] using deviation_load_bound (SourceVarGroup E cubic z j) Q hd hg g

def sourceIncidenceData (t u : I) (z : SourcePrimitive E cubic I→S) :
    IncidenceData I S Port (Clone (TriVertex V)) (ClauseIndex F) where
  var := cloneOwner F reg
  factor := cloneFactor F
  wordVar := variableWord z
  wordFactor := factorAt (literalTags E cubic t u) z

def ActualSeats (t u : I) (z : SourcePrimitive E cubic I→S) (cap : ℚ) : Prop :=
  let D := sourceIncidenceData E cubic loopless t u z
  (copies D:ℚ)≤cap ∧
  Function.Injective (position D (copies D) (copies_suffice D)) ∧
  ∀ p : Port, occupied D (copies D) (copies_suffice D) (copyIndex D (copies D) (copies_suffice D) p)
    (D.cell p)=some (cloneOwner F reg p)

theorem actual_copied_seats (t u : I) (z : SourcePrimitive E cubic I→S) (cap : ℚ)
    (hc : ∀ c,load (SourceCell E cubic loopless t u z) c≤cap) :
    ActualSeats E cubic loopless t u z cap := by
  let D := sourceIncidenceData E cubic loopless t u z
  let cnt := fun c : Draw I S=>Fintype.card (CellFibre D c)
  obtain ⟨c,_,hh⟩ := Finset.exists_max_image Finset.univ cnt Finset.univ_nonempty
  have h := copies_budget D (cnt c) (fun v=>hh v (Finset.mem_univ _))
  have hcnt : (cnt c:ℚ)=load D.cell c := by
    unfold cnt
    rw [←Nat.card_eq_fintype_card]
    exact J6R11CollisionReindex.card_fibre_load D.cell c
  have hh' : (copies D:ℚ)≤cnt c := by exact_mod_cast h
  refine ⟨hh'.trans ?_,position_injective D _ _,?_⟩
  · rw [hcnt]
    exact hc c
  · exact occupied_at D _ _

theorem actual_pin_density (t u : I) (z : SourcePrimitive E cubic I→S)
    (hcell : ∀ c, load (SourceCell E cubic loopless t u z) c≤
      2*(12*(NV:ℚ))/(Fintype.card (Draw I S):ℚ)) :
    ∀ w, empiricalLaw (actualPinWord E cubic t u z) w≤24*uniformWeight (I→S) := by
  have hpp := MainClonedCNF.port_card F reg
  have hp : 2*Fintype.card Port≤24*NV := by rw [hpp]; omega
  refine main_pin_domination (MainClonedCNF.pinPort F) (SourceCell E cubic loopless t u z) 24 hp ?_
  intro c
  rw [hpp,Nat.cast_mul]
  simpa using hcell c

#print axioms simultaneous_nonnegative_mean
#print axioms source_pin_first
#print axioms source_pin_second
#print axioms simultaneous_source_loads
#print axioms actual_copied_seats
#print axioms actual_pin_density
end
end Paper5.HybridMainOnly
