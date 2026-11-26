import P5AlwaysSatOriginalCNF

/-! The literal source ports of (M.7), independent of the pin signs.
This identifies the unique uncycled port and validates the nominal
cloning ledgers; it does not construct the physical MAIN/D layouts. -/
namespace Paper5.AlwaysSatOriginal
open scoped BigOperators
variable {V : Type*}

def template (E : Finset (V×V)) (T : Finset V) :=
  clause E T (fun _=>false)

abbrev Port (E : Finset (V×V)) (T : Finset V) :=
  (i : Factor E T) × Fin ((template E T i).length)

def owner {E : Finset (V×V)} {T : Finset V} (p : Port E T) : Var T :=
  ((template E T p.1).get p.2).1

theorem literal_width_independent (E : Finset (V×V)) (T : Finset V) (s : V→Bool)
    (i : Factor E T) : (template E T i).length=(clause E T s i).length := by
  rcases i with v|(e|(_|⟨v,b⟩))
  · rfl
  · rfl
  · rfl
  · cases b <;> rfl

def realLiteral {E : Finset (V×V)} {T : Finset V} (s : V→Bool) (p : Port E T) :
    Var T×Bool :=
  (clause E T s p.1).get (Fin.cast (literal_width_independent E T s p.1) p.2)

theorem realLiteral_owner {E : Finset (V×V)} {T : Finset V} (s : V→Bool) (p : Port E T) :
    (realLiteral s p).1=owner p := by
  rcases p with ⟨i,j⟩
  rcases i with v|(e|(_|⟨v,b⟩))
  · have hj : j=⟨0,by change 0<1; decide⟩ := by
      apply Fin.ext
      have hh := j.isLt
      change j.val<1 at hh
      exact Nat.lt_one_iff.mp hh
    subst j
    rfl
  · rfl
  · rfl
  · cases b <;> rfl

def pinPort (E : Finset (V×V)) (T : Finset V) (v : V) : Port E T :=
  ⟨.inl v,⟨0,by change 0<1; decide⟩⟩
def ePortY (E : Finset (V×V)) (T : Finset V) (e : ↥E) : Port E T :=
  ⟨.inr (.inl e),⟨0,by change 0<3; decide⟩⟩
def ePortL (E : Finset (V×V)) (T : Finset V) (e : ↥E) : Port E T :=
  ⟨.inr (.inl e),⟨1,by change 1<3; decide⟩⟩
def ePortR (E : Finset (V×V)) (T : Finset V) (e : ↥E) : Port E T :=
  ⟨.inr (.inl e),⟨2,by change 2<3; decide⟩⟩
def bonusZeroPort (E : Finset (V×V)) (T : Finset V) : Port E T :=
  ⟨.inr (.inr (.inl ())),⟨0,by change 0<2; decide⟩⟩
def bonusZeroY (E : Finset (V×V)) (T : Finset V) : Port E T :=
  ⟨.inr (.inr (.inl ())),⟨1,by change 1<2; decide⟩⟩
def bonusPort (E : Finset (V×V)) (T : Finset V) (v : ↥T) (b : Bool) : Port E T :=
  ⟨.inr (.inr (.inr (v,b))),⟨0,by cases b <;> (change 0<2; decide)⟩⟩

theorem bonus0_unique_port {E : Finset (V×V)} {T : Finset V} (p : Port E T) :
    owner p=b₀ T ↔ p=bonusZeroPort E T := by
  constructor
  · intro h
    rcases p with ⟨i,j⟩
    rcases i with v|(e|(u|⟨v,b⟩))
    · change Fin 1 at j
      fin_cases j
      simp [owner,template,clause,old,b₀] at h
    · change Fin 3 at j
      fin_cases j <;> simp [owner,template,clause,old,y,b₀] at h
    · cases u
      change Fin 2 at j
      fin_cases j
      · rfl
      · simp [owner,template,clause,y,b₀] at h
    · cases b
      all_goals change Fin 2 at j
      all_goals fin_cases j <;> simp [owner,template,clause,bonus,old,y,b₀] at h
  · rintro rfl
    rfl

theorem every_variable_has_port (E : Finset (V×V)) (T : Finset V) :
    Function.Surjective (owner (E:=E) (T:=T)) := by
  intro w
  rcases w with v|(c|v)
  · exact ⟨pinPort E T v,rfl⟩
  · cases c
    · exact ⟨bonusZeroY E T,rfl⟩
    · exact ⟨bonusZeroPort E T,rfl⟩
  · exact ⟨bonusPort E T v false,rfl⟩

private theorem some_incident [DecidableEq V] (E : Finset (V×V)) (v : V)
    (hC : GraphCutMoments.degree E v=3) : ∃ e∈E,e.1=v ∨ e.2=v := by
  by_cases hL : (E.filter fun e=>e.1=v).Nonempty
  · obtain ⟨e,he⟩ := hL
    obtain ⟨he,hl⟩ := Finset.mem_filter.mp he
    exact ⟨e,he,Or.inl hl⟩
  by_cases hR : (E.filter fun e=>e.2=v).Nonempty
  · obtain ⟨e,he⟩ := hR
    obtain ⟨he,hr⟩ := Finset.mem_filter.mp he
    exact ⟨e,he,Or.inr hr⟩
  have h0 := Finset.not_nonempty_iff_eq_empty.mp hL
  have h1 := Finset.not_nonempty_iff_eq_empty.mp hR
  simp [GraphCutMoments.degree,h0,h1] at hC

theorem two_ports_except_bonus0 [DecidableEq V] [Nonempty V] (E : Finset (V×V))
    (T : Finset V) (hC : ∀ v, GraphCutMoments.degree E v=3)
    (w : Var T) (h : w≠b₀ T) :
    ∃ a b : Port E T, a≠b ∧ owner a=w ∧ owner b=w := by
  rcases w with v|(c|v)
  · obtain ⟨e,he,hl|hr⟩ := some_incident E v (hC v)
    · refine ⟨pinPort E T v,ePortL E T ⟨e,he⟩,?_,rfl,?_⟩
      · intro hh
        have hv := congrArg Sigma.fst hh
        simp [pinPort,ePortL] at hv
      · exact congrArg Sum.inl hl
    · refine ⟨pinPort E T v,ePortR E T ⟨e,he⟩,?_,rfl,?_⟩
      · intro hh
        have hv := congrArg Sigma.fst hh
        simp [pinPort,ePortR] at hv
      · exact congrArg Sum.inl hr
  · cases c
    · obtain ⟨v⟩ := ‹Nonempty V›
      obtain ⟨e,he,_⟩ := some_incident E v (hC v)
      refine ⟨bonusZeroY E T,ePortY E T ⟨e,he⟩,?_,rfl,rfl⟩
      intro hh
      have hv := congrArg Sigma.fst hh
      simp [bonusZeroY,ePortY] at hv
    · exact (h rfl).elim
  · refine ⟨bonusPort E T v false,bonusPort E T v true,?_,rfl,rfl⟩
    intro hh
    have hv := congrArg Sigma.fst hh
    simp [bonusPort] at hv

theorem original_port_card [Fintype V] (E : Finset (V×V)) (T : Finset V) :
    Fintype.card (Port E T)=Fintype.card V+3*E.card+4*T.card+2 := by
  rw [Fintype.card_sigma]
  simpa only [Fintype.card_fin,template] using literal_occurrences E T (fun _=>false)

noncomputable def cycleSlots [Fintype V] (E : Finset (V×V)) (T : Finset V) : Finset (Port E T) := by
  classical
  exact Finset.univ.filter fun p=>owner p≠b₀ T

theorem cycle_slots_card [Fintype V] (E : Finset (V×V)) (T : Finset V) :
    (cycleSlots E T).card=Fintype.card (Port E T)-1 := by
  classical
  have hF : cycleSlots E T=(Finset.univ : Finset (Port E T)).erase (bonusZeroPort E T) := by
    ext p
    simp [cycleSlots,bonus0_unique_port]
  rw [hF,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ]

theorem original_nominal_clone_sizes [Fintype V] [DecidableEq V]
    (E : Finset (V×V)) (T : Finset V) (s : V→Bool)
    (hC : ∀ v,GraphCutMoments.degree E v=3) :
    (formula E T s).length+(cycleSlots E T).card=8*Fintype.card V+6*T.card+2 ∧
    2*(Fintype.card (Port E T)+2*(cycleSlots E T).card)=33*Fintype.card V+24*T.card+8 ∧
    (Fintype.card (Port E T)+2*(cycleSlots E T).card)+Fintype.card (Port E T)=
      22*Fintype.card V+16*T.card+6 := by
  have hp := original_port_card E T
  have hcl := formula_length E T s
  have hcy := cycle_slots_card E T
  have hE := GraphCutMoments.regular_edge_count E 3 hC
  omega

#print axioms literal_width_independent
#print axioms realLiteral_owner
#print axioms bonus0_unique_port
#print axioms every_variable_has_port
#print axioms two_ports_except_bonus0
#print axioms original_port_card
#print axioms cycle_slots_card
#print axioms original_nominal_clone_sizes
end Paper5.AlwaysSatOriginal