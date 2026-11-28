import Acquisition
import J6R10RepackPrecision
import PinnedCNF

/-! The literal A4 sparse CNF has one fresh variable per actual clause
port, a unary all-ones variable leaf, and one equality subdivision for
each occurrence. This file constructs that exact host, not a general
tensor graph with tables supplied by an oracle. -/
namespace A4R45LiteralNetwork
open Acquisition J6R10Repack
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

abbrev Var (V₂ V₃ U : Type*) := CoverOccurrences V₂ V₃ U
abbrev Row (V₂ V₃ U : Type*) := CoverRow V₂ V₃ U ⊕ Var V₂ V₃ U
abbrev Wire (V₂ V₃ U : Type*) := Var V₂ V₃ U × Bool

variable {V₂ V₃ U : Type*}

def network : Network (Wire V₂ V₃ U) (Row V₂ V₃ U) (Var V₂ V₃ U) where
  row w := if w.2 then .inl w.1.1 else .inr w.1
  col := Prod.fst

def sign : CoverRow V₂ V₃ U → Bool
  | .inr (.inr (.inl _)) => true
  | _ => false

noncomputable def clause (r : CoverRow V₂ V₃ U) :
    List (Var V₂ V₃ U × Bool) :=
  Finset.univ.toList.map fun j : CoverPort r => (⟨r,j⟩,sign r)

noncomputable def formula [Fintype V₂] [Fintype V₃] [Fintype U] :
    Std.Sat.CNF (Var V₂ V₃ U) :=
  Finset.univ.toList.map clause

theorem clause_length (r : CoverRow V₂ V₃ U) :
    (clause r).length=Fintype.card (CoverPort r) := by
  simp [clause]

theorem true_widths (r : CoverRow V₂ V₃ U) :
    (clause r).length =
      match r with
      | .inl _ => 2
      | .inr (.inl _) => 4
      | .inr (.inr _) => 1 := by
  rw [clause_length]
  rcases r with r|r
  · exact Fintype.card_fin 2
  rcases r with r|r
  · change Fintype.card (Fin 3 ⊕ Unit) = 4
    simp
  · change Fintype.card Unit = 1
    simp

theorem literal_location (r : CoverRow V₂ V₃ U) (v : Var V₂ V₃ U) (b : Bool) :
    (v,b)∈clause r ↔ v.1=r ∧ b=sign r := by
  simp only [clause,List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj⟩
    have eq := Prod.mk.inj hj
    exact ⟨(congrArg Sigma.fst eq.1).symm,eq.2.symm⟩
  · rcases v with ⟨r',j⟩
    simp only
    rintro ⟨rfl,rfl⟩
    exact ⟨j,rfl⟩

theorem literal_present_once (v : Var V₂ V₃ U) :
    ((v,sign v.1)∈clause v.1) ∧
      (∀ r b, (v,b)∈clause r → r=v.1 ∧ b=sign v.1) := by
  exact ⟨(literal_location _ _ _).2 ⟨rfl,rfl⟩,
    fun r b h => let h' := (literal_location r v b).1 h; ⟨h'.1.symm,h'.2.trans (congrArg sign h'.1.symm)⟩⟩

theorem distinct_clause_literals (r : CoverRow V₂ V₃ U) : (clause r).Nodup := by
  unfold clause
  apply List.Nodup.map
  · intro x y eq
    have es := congrArg Prod.fst eq
    exact eq_of_heq (Sigma.mk.inj_iff.mp es).2
  · exact Finset.nodup_toList _

theorem formula_clause_count [Fintype V₂] [Fintype V₃] [Fintype U] :
    (formula (V₂:=V₂) (V₃:=V₃) (U:=U)).length =
    Fintype.card (CoverRow V₂ V₃ U) := by simp [formula]

theorem real_clause_ports (r : CoverRow V₂ V₃ U) :
    ∀ w : Wire V₂ V₃ U, (network.row w : Row V₂ V₃ U)=.inl r ↔
      ∃ j : CoverPort r, w=(⟨r,j⟩,true) := by
  rintro ⟨⟨r',j⟩,b⟩
  cases b
  · simp [network]
  · constructor
    · intro h
      change Sum.inl r'=Sum.inl r at h
      obtain rfl := Sum.inl.inj h
      exact ⟨j,rfl⟩
    · rintro ⟨z,e⟩
      rw [e]
      rfl

def real_column_ports (v : Var V₂ V₃ U) :
    {w : Wire V₂ V₃ U // network.col w = v} ≃ Bool where
  toFun w := w.val.2
  invFun b := ⟨(v,b),rfl⟩
  left_inv w := Subtype.ext (Prod.ext w.2.symm rfl)
  right_inv _ := rfl

theorem real_unary_variable_port (v : Var V₂ V₃ U) (w : Wire V₂ V₃ U) :
    (network.row w : Row V₂ V₃ U)=.inr v ↔ w=(v,false) := by
  rcases w with ⟨w,b⟩
  cases b <;> simp [network]

variable [Fintype V₂] [Fintype V₃] [Fintype U]

theorem occurrence_count : Fintype.card (Var V₂ V₃ U) =
    2*Fintype.card V₂+5*Fintype.card V₃+Fintype.card U := by
  rw [Fintype.card_sigma]
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [CoverPort,Fintype.card_sum]
  omega

/-- Each input edge has two ports total. This actual incidence certificate
also forces the number of degree-three vertices to be even. -/
theorem handshake_even {E : Type*} [Fintype E]
    (actual : (V₂×Fin 2) ⊕ (V₃×Fin 3) ≃ E×Bool) :
    2*Fintype.card V₂+3*Fintype.card V₃=2*Fintype.card E ∧ Even (Fintype.card V₃) := by
  have h := Fintype.card_congr actual
  simp only [Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,Fintype.card_bool] at h
  exact ⟨by omega, ⟨Fintype.card E-Fintype.card V₂-Fintype.card V₃,by omega⟩⟩

theorem exact_unpadded_size {E : Type*} [Fintype E]
    (actual : (V₂×Fin 2) ⊕ (V₃×Fin 3) ≃ E×Bool)
    (padding : Fintype.card U=Fintype.card E+Fintype.card V₃) :
    Fintype.card (Wire V₂ V₃ U)=6*(Fintype.card E+Fintype.card V₃) ∧
    Fintype.card (Var V₂ V₃ U)+(formula (V₂:=V₂) (V₃:=V₃) (U:=U)).length ≤
      Fintype.card (Wire V₂ V₃ U) := by
  rw [Fintype.card_prod,Fintype.card_bool,formula_clause_count,occurrence_count]
  have h := (handshake_even actual).1
  simp only [Fintype.card_sum]
  omega

#print axioms true_widths
#print axioms literal_present_once
#print axioms distinct_clause_literals
#print axioms real_clause_ports
#print axioms real_column_ports
#print axioms real_unary_variable_port
#print axioms handshake_even
#print axioms exact_unpadded_size
end A4R45LiteralNetwork
