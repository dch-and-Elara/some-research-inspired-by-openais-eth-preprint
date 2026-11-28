import A4R45LiteralNetwork
import J6R12RepackBoolean
import J6R10RepackState

/-! Binary source tables for the sparse A4 network, derived from the actual
single-occurrence CNF. The old variable rows are all ones and subdivision
columns test equality on their two true ports. -/
namespace A4R45LiteralTables
open Acquisition J6R10Repack J6R9Recursive DenominatorBudget A4R45LiteralNetwork
open scoped Polynomial BigOperators
set_option autoImplicit false
set_option warningAsError true

variable {V₂ V₃ U : Type*}

def clausePort (r : CoverRow V₂ V₃ U) (j : CoverPort r) :
    ParentPorts (network (V₂:=V₂) (V₃:=V₃) (U:=U)) (.inl (.inl r)) :=
  ⟨.inl (⟨r,j⟩,true),rfl⟩

def colPort (v : Var V₂ V₃ U) (b : Bool) :
    ParentPorts (network (V₂:=V₂) (V₃:=V₃) (U:=U)) (.inr v) :=
  ⟨.inr (v,b),rfl⟩

noncomputable def trueFlags :
    ∀ x : Row V₂ V₃ U ⊕ Var V₂ V₃ U,
      (ParentPorts (network (V₂:=V₂) (V₃:=V₃) (U:=U)) x → Bool) → Bool
  | .inl (.inl r), word =>
      Finset.univ.toList.any fun j : CoverPort r => word (clausePort r j) == sign r
  | .inl (.inr _), _ => true
  | .inr v, word => word (colPort v false) == word (colPort v true)

theorem actual_clause_table (r : CoverRow V₂ V₃ U) (x : Var V₂ V₃ U→Bool)
    (word : ParentPorts (network (V₂:=V₂) (V₃:=V₃) (U:=U)) (.inl (.inl r))→Bool)
    (assign : ∀ j,word (clausePort r j)=x ⟨r,j⟩) :
    trueFlags (.inl (.inl r)) word =
      (clause r).any (fun l => x l.1 == l.2) := by
  simp only [trueFlags,clause,List.any_map,assign]
  rfl

theorem bit_prod_indicator {I K : Type*} [Fintype I] [CommRing K] (x : I→Bool) :
    (∏ j, bit (K:=K) (x j)) = if ∀ j, x j=true then 1 else 0 := by
  classical
  by_cases h : ∀ j,x j=true
  · simp [h,bit]
  · obtain ⟨j,jh⟩ := not_forall.mp h
    have jf : x j=false := by cases hq : x j <;> simp_all
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [bit,jf])

theorem actual_signed_flag_as_ring {K : Type*} [CommRing K]
    (r : CoverRow V₂ V₃ U)
    (word : ParentPorts (network (V₂:=V₂) (V₃:=V₃) (U:=U)) (.inl (.inl r))→Bool) :
    bit (K:=K) (trueFlags (.inl (.inl r)) word) =
      coverTables r (fun j => word (clausePort r j)) := by
  classical
  have hn (hs : sign r=false) :
      trueFlags (.inl (.inl r)) word = false ↔ ∀ j, word (clausePort r j)=true := by
    simp only [trueFlags,hs,List.any_eq_false,Finset.mem_toList,Finset.mem_univ,true_implies]
    constructor <;> intro h j <;> specialize h j <;> cases hj : word (clausePort r j) <;> simp_all
  have negFormula (hs : sign r=false) :
      bit (K:=K) (trueFlags (.inl (.inl r)) word) =
        1 - ∏ j : CoverPort r, bit (word (clausePort r j)) := by
    rw [bit_prod_indicator]
    by_cases z : trueFlags (.inl (.inl r)) word=false
    · have all := (hn hs).1 z
      rw [if_pos all]
      simp [bit,z]
    · have ht : trueFlags (.inl (.inl r)) word=true := by
        cases h : trueFlags (.inl (.inl r)) word <;> simp_all
      have na := fun all => z ((hn hs).2 all)
      rw [if_neg na]
      simp [bit,ht]
  rcases r with r|r
  · exact negFormula rfl
  rcases r with r|r
  · exact negFormula rfl
  rcases r with r|r
  · have list : (Finset.univ.toList : List (CoverPort (V₂:=V₂) (V₃:=V₃) (U:=U)
        (.inr (.inr (.inl r)))))=[()] := by
      change (Finset.univ.toList : List Unit)=[()]
      have set : (Finset.univ:Finset Unit)={()} := by ext x; cases x; simp
      rw [set]
      simp
    simp [trueFlags,sign,coverTables,list]
  · exact negFormula rfl

theorem variable_leaf_one (v : Var V₂ V₃ U)
    (word : ParentPorts (network (V₂:=V₂) (V₃:=V₃) (U:=U)) (.inl (.inr v))→Bool) :
    trueFlags (.inl (.inr v)) word = true := rfl

theorem column_literal_equality (v : Var V₂ V₃ U)
    (word : ParentPorts (network (V₂:=V₂) (V₃:=V₃) (U:=U)) (.inr v) → Bool) :
    trueFlags (.inr v) word = true ↔ word (colPort v false)=word (colPort v true) := by
  simp [trueFlags]

noncomputable def sourceFile (f : ℤ[X]) (P₀ : ℕ) :
    EntryFile f 1 (network (V₂:=V₂) (V₃:=V₃) (U:=U)) :=
  fun v => ⟨P₀,fun x => if trueFlags v x then 1 else 0⟩

theorem sourceFile_read {f : ℤ[X]} (p₀ p : ℕ) (hp₀ : 0<p₀)
    (hf : f.Monic) (hd : 0<f.natDegree) (v : Row V₂ V₃ U ⊕ Var V₂ V₃ U)
    (x : ParentPorts (network (V₂:=V₂) (V₃:=V₃) (U:=U)) v→Bool) :
    ((sourceFile f p₀) v).read hf p x = (if trueFlags v x then 1 else 0) := by
  change reduce p f 1 (canonicalLift p₀ f hf 1 (if trueFlags v x then 1 else 0)) = _
  rw [J6R12Repack.canonical_lift_bool p₀ hp₀ f hf hd 1 (by decide)]
  cases trueFlags v x <;> simp

#print axioms actual_clause_table
#print axioms actual_signed_flag_as_ring
#print axioms variable_leaf_one
#print axioms column_literal_equality
#print axioms sourceFile_read
end A4R45LiteralTables
