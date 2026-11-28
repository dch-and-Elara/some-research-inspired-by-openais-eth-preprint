import J6R53OldOwnerBits

/-! A roster contains all logical owners, not just those seen in
a half-port scan. Lookup, copying the payload, and writing a changed
owner key have separate explicit bills. -/
namespace J6R53OldOwner
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost
open J6R21Ancestor J6R27OriginalGate J6R36ChildFramedRoute J6R25PreparedSupply J6R26DescriptorTree
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 2400
set_option maxHeartbeats 7700000
set_option Elab.async false

structure CompleteRoster {V : Type} {own gate key prec page : ℕ}
    (name : V→Word own) (value : V→OwnerData gate key prec page) where
  order : List V
  unique : order.Nodup
  complete : ∀ x,x∈order
  raw : RawRoster own gate key prec page
  exactRows : raw=order.map (fun x=>⟨name x,value x⟩)

theorem complete_owner_hit {V : Type} {own gate key prec page : ℕ}
    {name : V→Word own} {value : V→OwnerData gate key prec page}
    (R : CompleteRoster name value) (inj : Function.Injective name) (v : V) :
    (locate (name v) R.raw).result=some (value v) := by
  apply locate_hit
  · rw [R.exactRows]
    exact List.mem_map.mpr ⟨v,R.complete v,rfl⟩
  · intro row belongs addr
    rw [R.exactRows] at belongs
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp belongs
    have eq : x=v := inj addr
    subst x
    rfl

def gatherOwners {own gate key prec page : ℕ} (raw : RawRoster own gate key prec page) :
    List (Word own)→Meter (Option (List (OwnerData gate key prec page)))
  | []=>⟨some [],3⟩
  | h::tail=>
    let got := paidOwnerLookup raw h
    match got.result with
    | none=>⟨none,got.steps+4⟩
    | some v=>
      let rest := gatherOwners raw tail
      ⟨rest.result.map (v::·),got.steps+rest.steps+4⟩

theorem gather_owner_words_exact {V : Type} {own gate key prec page : ℕ}
    (raw : RawRoster own gate key prec page)
    (name : V→Word own) (value : V→OwnerData gate key prec page) (xs : List V)
    (lookup : ∀ x∈xs,(locate (name x) raw).result=some (value x)) :
    gatherOwners raw (xs.map name)=⟨some (xs.map value),
      3+(xs.map (fun x=>(locate (name x) raw).steps+ownerDataFee (value x)+8)).sum⟩ := by
  induction xs with
  | nil=>rfl
  | cons x xs ih =>
    have q := paid_owner_lookup_exact raw (name x) (value x) (lookup x List.mem_cons_self)
    have t := ih (fun u hu=>lookup u (List.mem_cons_of_mem _ hu))
    simp only [List.map_cons,gatherOwners,q,t,Option.map_some,List.sum_cons]
    congr 1
    omega

def freshOwnerData {gate key prec page : ℕ} (s : Stamp key prec) (p : Word page) :
    OwnerData gate key prec page := ⟨⟨s,some p⟩,none⟩

def writeFreshOwners {gate key prec page : ℕ} (s : Stamp key prec) :
    List (Word page)→Meter (List (OwnerData gate key prec page))
  | []=>⟨[],3⟩
  | p::ps=>
    let here := copyOwnerData (freshOwnerData s p)
    let rest := writeFreshOwners s ps
    ⟨here.result::rest.result,here.steps+rest.steps+4⟩

theorem write_fresh_owners_exact {gate key prec page : ℕ} (s : Stamp key prec) (ps : List (Word page)) :
    writeFreshOwners (gate:=gate) s ps=⟨ps.map (freshOwnerData s),
      3+(ps.map (fun p=>ownerDataFee (freshOwnerData (gate:=gate) s p)+4)).sum⟩ := by
  induction ps with
  | nil=>rfl
  | cons p ps ih =>
    simp only [writeFreshOwners,copy_owner_data_exact,ih,List.map_cons,List.sum_cons]
    congr 1
    omega

/-- Store the already emitted immutable payload under the next key.
The byte copy of the payload itself is the preceding gather/creation
operation; this pass copies the new key, not the payload a second time. -/
def setOwnerKeys {new gate key prec page : ℕ} :
    List (Word new)→List (OwnerData gate key prec page)→
      Meter (Option (RawRoster new gate key prec page))
  | [],[]=>⟨some [],3⟩
  | x::xs,y::ys=>
    let code := copyFixed x
    let rest := setOwnerKeys xs ys
    ⟨rest.result.map (fun rows=>⟨code.result,y⟩::rows), code.steps+rest.steps+5⟩
  | _,_=>⟨none,3⟩

theorem set_owner_keys_exact {V : Type} {new gate key prec page : ℕ}
    (name : V→Word new) (value : V→OwnerData gate key prec page) (xs : List V) :
    setOwnerKeys (xs.map name) (xs.map value)=
      ⟨some (xs.map fun x=>⟨name x,value x⟩),3+(3*new+6)*xs.length⟩ := by
  induction xs with
  | nil=>rfl
  | cons x xs ih =>
    simp only [List.map_cons,setOwnerKeys,copy_fixed_exact,ih,Option.map_some,List.length_cons,Nat.mul_succ]
    congr 1
    omega

#print axioms complete_owner_hit
#print axioms gather_owner_words_exact
#print axioms write_fresh_owners_exact
#print axioms set_owner_keys_exact
end J6R53OldOwner
