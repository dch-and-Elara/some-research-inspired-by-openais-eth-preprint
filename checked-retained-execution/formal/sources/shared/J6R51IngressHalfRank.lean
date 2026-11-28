import J6R51IngressRankEnd

/-! Both physical sides have the same numbered subdivision, with
the real little-endian side bit. A paid prefix of the output wire
rank produces exactly the fresh Plant's half-wire ordinal. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime AOracleMachineTimeTape J6R49RootIngress
open J7R9Compiler J7R9Subdivision J7R10Plant
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12200000

theorem paired_index {A : Type*} [DecidableEq A] (x : A) (b : Bool)
    (l : List A) (m : x∈l) :
    indexByEq (x,b) (l.product [false,true])=2*indexByEq x l+b.toNat := by
  induction l with
  | nil => simp at m
  | cons y ys ih =>
    by_cases E : y=x
    · subst y
      cases b <;> simp [List.product,indexByEq]
    · have hn : x∈ys := (List.mem_cons.mp m).resolve_left (Ne.symm E)
      have f₀ : (y,false)≠(x,b) := fun e=>E (congrArg Prod.fst e)
      have f₁ : (y,true)≠(x,b) := fun e=>E (congrArg Prod.fst e)
      change indexByEq (x,b) ((y,false)::(y,true)::ys.product [false,true])=_
      have e₀ : indexByEq (x,b) ((y,false)::(y,true)::ys.product [false,true])=
          (indexByEq (x,b) ((y,true)::ys.product [false,true])).succ := List.idxOf_cons_ne _ f₀
      have e₁ : indexByEq (x,b) ((y,true)::ys.product [false,true])=
          (indexByEq (x,b) (ys.product [false,true])).succ := List.idxOf_cons_ne _ f₁
      have e₂ : indexByEq x (y::ys)=(indexByEq x ys).succ := List.idxOf_cons_ne _ E
      rw [e₀,e₁,e₂,ih hn]
      omega

theorem half_rank_pair {V : Type*} [DecidableEq V] [Fintype V] (H : CNF V)
    (s : DeclaredOrder V) (x : Wire H) (b : Bool) :
    ((halfRank H s) (x,b)).val=2*((wireRank H s) x).val+b.toNat := by
  change indexByEq (x,b) (halfOrder H s)=2*indexByEq x (wireOrder H s)+b.toNat
  exact paired_index x b _ (wire_order_all H s x)

def sideWord {q : ℕ} (b : Bool) (w : Word q) : Word (q+1) :=
  ⟨b::w.val,by simp [w.property]⟩

theorem side_word_exact (q x : ℕ) (b : Bool) :
    sideWord b (wordAt q x)=wordAt (q+1) (2*x+b.toNat) := by
  apply Subtype.ext
  change b::encodeBits q x=encodeBits (q+1) (2*x+b.toNat)
  have bnd : b.toNat≤1 := by cases b <;> decide
  have hl : (2*x+b.toNat)/2=x := by omega
  have hr : (2*x+b.toNat)%2=b.toNat := by omega
  simp only [encodeBits,hl,hr]
  cases b <;> rfl

def rankRawHalf {h d j q : ℕ} (v : WireKey h d j) (b : Bool)
    (declares : List (List Bool)) (F : BitsCNF) : Meter (Option (Word (q+1))) :=
  let R := rankRawCNF (q:=q) v declares F
  ⟨R.result.map (sideWord b),R.steps+4*q+5⟩

theorem raw_CNF_half_rank {V : Type} [DecidableEq V] [Fintype V] {h d j q : ℕ}
    (F : CNF V) (s : DeclaredOrder V) (code : V→List Bool) (inj : Function.Injective code)
    (hh : 0<h) (hd : 0<d) (hj : 0<j) (hq : 0<q)
    (fitH : (guardedInOrder F s.roster).length≤2^h)
    (fitD : ∀ row∈guardedInOrder F s.roster,row.length≤2^d)
    (fitJ : ∀ v,(occurrences (guardedInOrder F s.roster) v).length-3≤2^j)
    (fitQ : (wireOrder (guardedInOrder F s.roster) (guardRoster s)).length≤2^q)
    (v : Wire (guardedInOrder F s.roster)) (b : Bool) :
    let H := guardedInOrder F s.roster
    let k := keyOf (h:=h) (d:=d) (j:=j) H (guardCode code) v
    (rankRawHalf (q:=q) k b (s.roster.map code) (codeCNF code F)).result=
      some (wordAt (q+1) ((halfRank H (guardRoster s)) (v,b)).val) := by
  dsimp only [rankRawHalf]
  rw [actual_generated_graph_rank F s code inj hh hd hj hq fitH fitD fitJ fitQ v]
  simp only [Option.map_some,side_word_exact,half_rank_pair]

#print axioms paired_index
#print axioms half_rank_pair
#print axioms side_word_exact
#print axioms raw_CNF_half_rank
end J6R51Ingress
