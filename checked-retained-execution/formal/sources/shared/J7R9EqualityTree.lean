import Mathlib.Tactic
import Mathlib.Data.List.Count

/-!
# Literal trivalent equality trees

The rows listed below are actual local equality gates. For d≥3 we
choose a caterpillar with d-3 internal edges and d-2 trivalent gates:
attach the first two external ports to a new internal edge and
recurse on that edge and the remaining external ports. No access
to a large equality tensor is used.
-/

namespace J7R9EqualityTree

def gates {A : Type*} (ext : List A) : List A → List (List A)
  | [] => if ext.isEmpty then [] else [ext]
  | e::es => match ext with
    | a::b::rest => [a,b,e] :: gates (e::rest) es
    | _ => []

/-- Joint shape invariant includes all d=0,1,2,3 cases. -/
def shape (d k : ℕ) : Prop := k=d-3

def agrees {A : Type*} (x : A → Bool) (ps : List A) : Prop :=
  ∃ b : Bool, ∀ j ∈ ps, x j=b

theorem agrees_nil {A : Type*} (x : A → Bool) : agrees x [] := ⟨false, by simp⟩

theorem agrees_cons {A : Type*} (x : A → Bool) (a : A) (ps : List A) :
    agrees x (a::ps) ↔ ∀ j ∈ ps, x j=x a := by
  constructor
  · rintro ⟨b,h⟩ j hj
    rw [h j (List.mem_cons_of_mem _ hj), h a (List.mem_cons_self)]
  · intro hh
    refine ⟨x a,?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl|hj
    · rfl
    · exact hh j hj

/-- A local gate product is one exactly when all external and internal
values coincide. In particular, extending a compatible external
assignment costs no multiplicity factor. -/
theorem gates_agree {A : Type*} (x : A → Bool) (ps es : List A)
    (h : shape ps.length es.length) :
    (∀ gate ∈ gates ps es, agrees x gate) ↔ agrees x (ps++es) := by
  induction es generalizing ps with
  | nil =>
    cases ps with
    | nil => simp [gates, agrees_nil]
    | cons a ps => simp [gates]
  | cons e es ih =>
    have hh : es.length+1=ps.length-3 := h
    cases ps with
    | nil => simp at hh
    | cons a ps =>
      cases ps with
      | nil => simp at hh
      | cons b ps =>
        have htail : shape (e::ps).length es.length := by
          simp only [shape, List.length_cons] at *
          omega
        rw [gates, List.forall_mem_cons, ih (e::ps) htail]
        constructor
        · rintro ⟨⟨c,hc⟩,⟨d,hd⟩⟩
          have hec := hc e (by simp)
          have hed := hd e (by simp)
          have hcd : c=d := hec.symm.trans hed
          refine ⟨c,?_⟩
          intro j hj
          simp only [List.cons_append, List.mem_cons, List.mem_append] at hj
          rcases hj with rfl|rfl|hj|rfl|hj
          · exact hc _ (by simp)
          · exact hc _ (by simp)
          · exact (hd _ (by simp [hj])).trans hcd.symm
          · exact hec
          · exact (hd _ (by simp [hj])).trans hcd.symm
        · rintro ⟨c,hc⟩
          constructor
          · refine ⟨c,?_⟩
            intro j hj
            have hi : j=a ∨ j=b ∨ j=e := by simpa using hj
            rcases hi with rfl|rfl|rfl <;> exact hc _ (by simp)
          · refine ⟨c,?_⟩
            intro j hj
            simp only [List.cons_append,List.mem_cons,List.mem_append] at hj
            rcases hj with rfl|hj|hj <;> exact hc _ (by simp [*])

def boolGate {A : Type*} (x : A → Bool) : List A → Bool
  | [] => true
  | a::ps => ps.all (fun j => x j == x a)

theorem boolGate_true {A : Type*} (x : A → Bool) (ps : List A) :
    boolGate x ps=true ↔ agrees x ps := by
  cases ps with
  | nil => simp [boolGate, agrees_nil]
  | cons a ps => simp [boolGate, agrees_cons]

theorem actual_product {A : Type*} (x : A → Bool) (ps es : List A)
    (h : shape ps.length es.length) :
    ((gates ps es).all (boolGate x))=true ↔ agrees x (ps++es) := by
  simp only [List.all_eq_true, boolGate_true]
  exact gates_agree x ps es h

theorem degree_counts {A : Type*} (ps es : List A) (h : shape ps.length es.length) :
    (gates ps es).length = (if ps.isEmpty then 0 else es.length+1) ∧
    (∀ g ∈ gates ps es, g.length≤3) ∧
    (3≤ps.length → ∀ g ∈ gates ps es, g.length=3) := by
  induction es generalizing ps with
  | nil =>
    cases ps with
    | nil => simp [gates]
    | cons a ps =>
      have hv : ps.length+1≤3 := by
        have h' : 0=ps.length+1-3 := h
        omega
      simp [gates,hv]
      omega
  | cons e es ih =>
    have hh : es.length+1=ps.length-3 := h
    cases ps with
    | nil => simp at hh
    | cons a ps =>
      cases ps with
      | nil => simp at hh
      | cons b ps =>
        have htail : shape (e::ps).length es.length := by
          simp only [shape, List.length_cons] at *
          omega
        obtain ⟨h1,h2,h3⟩ := ih (e::ps) htail
        have hthree : 3≤(e::ps).length := by simp at hh ⊢; omega
        simp only [gates,List.isEmpty_cons,Bool.false_eq_true,if_false,List.length_cons] at h1 ⊢
        refine ⟨by omega, ?_, ?_⟩
        · intro g hg
          rcases List.mem_cons.mp hg with rfl|hg
          · simp
          · exact h2 _ hg
        · intro _ g hg
          rcases List.mem_cons.mp hg with rfl|hg
          · simp
          · exact h3 hthree _ hg

/-- Literal incidence multiplicities: one gate port for each external
wire and two gate ports for each fresh internal wire. -/
theorem occurrence_count {A : Type*} [DecidableEq A] (ps es : List A)
    (h : shape ps.length es.length) (a : A) :
    ((gates ps es).flatten).count a=ps.count a+2*es.count a := by
  induction es generalizing ps with
  | nil =>
    cases ps <;> simp [gates]
  | cons e es ih =>
    have hh : es.length+1=ps.length-3 := h
    cases ps with
    | nil => simp at hh
    | cons j ps =>
      cases ps with
      | nil => simp at hh
      | cons k ps =>
        have htail : shape (e::ps).length es.length := by
          simp only [shape, List.length_cons] at *
          omega
        rw [gates,List.flatten_cons,List.count_append,ih _ htail]
        simp only [List.count_cons, List.count_nil]
        omega

#print axioms gates_agree
#print axioms actual_product
#print axioms degree_counts
#print axioms occurrence_count

end J7R9EqualityTree

