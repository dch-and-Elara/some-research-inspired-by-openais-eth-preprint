
import J7R9Size

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7300000
set_option maxRecDepth 2250
set_option linter.unusedSectionVars false

/-! Lines 2314--2324: the *path*, not the frozen caterpillar/subdivision.
This records only the occurrence constraints and their exact models.
The separate A3 file supplies the actual binary local gate identity. -/
namespace A2R45Literal
open scoped Classical BigOperators
open Std.Sat J7R9Compiler J7R9EqualityTree

noncomputable section
variable {A : Type*}

def directPath : List A→List (A×A)
  | []=>[]
  | [_]=>[]
  | a::b::l=>(a,b)::directPath (b::l)

theorem path_links_exact (l : List A) : (directPath l).length=l.length-1 := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
    cases tail with
    | nil => rfl
    | cons b rest =>
      simp only [directPath,List.length_cons] at ih ⊢
      omega

theorem path_second_ends (l : List A) : (directPath l).map Prod.snd=l.tail := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
    cases tail with
    | nil => rfl
    | cons b rest =>
      change b :: (directPath (b::rest)).map Prod.snd=b::rest
      rw [ih]
      rfl

theorem path_first_count [DecidableEq A] (l : List A) (z : A) :
    ((directPath l).map Prod.fst).count z≤l.count z := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
    cases tail with
    | nil => simp [directPath]
    | cons b rest =>
      simp only [List.count_cons] at ih
      simp only [directPath,List.map_cons,List.count_cons]
      omega

theorem path_both_port_counts [DecidableEq A] (l : List A) (z : A) :
    ((directPath l).map Prod.fst).count z+((directPath l).map Prod.snd).count z
      ≤2*l.count z := by
  have ha := path_first_count l z
  have hb : l.tail.count z≤l.count z := by cases l <;> simp [List.count_cons]
  rw [path_second_ends]
  omega

theorem actual_path_iff_agrees (x : A→Bool) (l : List A) :
    (∀ e∈directPath l,x e.1=x e.2)↔agrees x l := by
  induction l with
  | nil => simp [directPath,agrees_nil]
  | cons a tail ih =>
    cases tail with
    | nil => simp [directPath,agrees_cons]
    | cons b rest =>
      constructor
      · intro H
        have hab : x a=x b := H (a,b) (List.mem_cons_self)
        have hrest : ∀ e∈directPath (b::rest),x e.1=x e.2 :=
          fun e h=>H e (List.mem_cons_of_mem _ h)
        obtain ⟨w,hw⟩ := ih.mp hrest
        refine (agrees_cons x a _).mpr (fun j hj=>?_ )
        exact (hw j hj).trans ((hw b List.mem_cons_self).symm.trans hab.symm)
      · rintro ⟨w,hw⟩ e he
        rcases List.mem_cons.mp he with rfl|he
        · exact (hw a List.mem_cons_self).trans
            (hw b (List.mem_cons_of_mem _ List.mem_cons_self)).symm
        · exact ih.mpr ⟨w,fun j hj=>hw j (List.mem_cons_of_mem _ hj)⟩ e he

variable {V : Type} [DecidableEq V] (F : CNF V)

def directClausesOK (x : Occurrence F→Bool) : Prop :=
  ∀ c : ClauseIndex F,∃ j : Fin (F.get c).length,x ⟨c,j⟩=(literal F ⟨c,j⟩).2

def actualPathOK (x : Occurrence F→Bool) : Prop :=
  ∀ v e,e∈directPath (occurrences F v) → x e.1=x e.2

def directAccepts (x : Occurrence F→Bool) : Prop := directClausesOK F x ∧ actualPathOK F x

def directOccurrenceLift (x : V→Bool) : Occurrence F→Bool := fun o=>x (literal F o).1

theorem direct_path_leaf_acceptance (x : V→Bool) :
    directAccepts F (directOccurrenceLift F x)↔CNF.Sat x F := by
  constructor
  · intro h
    exact (sat_at_positions F x).mpr h.1
  · intro h
    refine ⟨(sat_at_positions F x).mp h,?_⟩
    intro v
    apply (actual_path_iff_agrees _ _).mpr
    exact ⟨x v,fun o ho=>congrArg x ((mem_occurrences F v o).mp ho)⟩

def directPathRead (h : AllOccur F) (x : Occurrence F→Bool) : V→Bool :=
  fun v=>x (Classical.choose (h v))

theorem direct_path_left (h : AllOccur F) (x : V→Bool) :
    directPathRead F h (directOccurrenceLift F x)=x := by
  funext v
  exact congrArg x (Classical.choose_spec (h v))

theorem direct_path_right (h : AllOccur F) (x : Occurrence F→Bool) (hx : actualPathOK F x) :
    directOccurrenceLift F (directPathRead F h x)=x := by
  funext o
  let v := (literal F o).1
  obtain ⟨z,hz⟩ := (actual_path_iff_agrees x _).mp (hx v)
  have h₁ : x (Classical.choose (h v))=z :=
    hz _ ((mem_occurrences F v _).mpr (Classical.choose_spec (h v)))
  have h₂ : x o=z := hz _ ((mem_occurrences F v _).mpr rfl)
  exact h₁.trans h₂.symm

def directPathEquiv (h : AllOccur F) :
    {x : V→Bool//CNF.Sat x F}≃{x : Occurrence F→Bool//directAccepts F x} where
  toFun x := ⟨directOccurrenceLift F x.val,(direct_path_leaf_acceptance F x.val).mpr x.property⟩
  invFun x := ⟨directPathRead F h x.val,(direct_path_leaf_acceptance F _).mp (by
    rw [direct_path_right F h x.val x.property.2]
    exact x.property)⟩
  left_inv x := Subtype.ext (direct_path_left F h x.val)
  right_inv x := Subtype.ext (direct_path_right F h x.val x.property.2)

theorem direct_path_has_one_extension [Fintype V] (h : AllOccur F) :
    Nat.card {x : Occurrence F→Bool//directAccepts F x}=PinnedCNF.modelCount F := by
  rw [modelCount_card F]
  exact Nat.card_congr (directPathEquiv F h).symm

theorem direct_path_literal_size [Fintype V] :
    (∑ v : V,(directPath (occurrences F v)).length)≤Fintype.card (Occurrence F) := by
  rw [←J7R9Size.occurrence_partition F]
  exact Finset.sum_le_sum (fun v _=>by rw [path_links_exact]; exact Nat.sub_le _ _)

#print axioms path_links_exact
#print axioms path_both_port_counts
#print axioms actual_path_iff_agrees
#print axioms directPathEquiv
#print axioms direct_path_has_one_extension
#print axioms direct_path_literal_size
end
end A2R45Literal
