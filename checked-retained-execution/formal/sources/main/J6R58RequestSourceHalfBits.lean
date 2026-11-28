import J6R48RawRouteWriter

/-! The checked native half-port address appends exactly one side
bit after the predecessor edge key. Here the value is decoded by
an actual counted fixed-width bit scan. -/
namespace J6R58RequestSource
open AOracleMachineTime J6R15ModeCost J6R48RawRoute
set_option autoImplicit false
set_option warningAsError true

def splitChildBits : (w : ℕ)→List Bool→Meter (Option (Word w × Bool))
  | 0,[b] => ⟨some (⟨[],rfl⟩,b),4⟩
  | 0,_ => ⟨none,4⟩
  | _+1,[] => ⟨none,4⟩
  | w+1,b::bs =>
    let R := splitChildBits w bs
    let out := R.result.map (fun (x,s)=> (⟨b::x.bits,by rw [List.length_cons,x.size]⟩,s))
    ⟨out,R.steps+5⟩

theorem exact_appended_side_bit (bs : List Bool) (b : Bool) :
    splitChildBits bs.length (bs++[b])=
      ⟨some (⟨bs,rfl⟩,b),5*bs.length+4⟩ := by
  induction bs with
  | nil => rfl
  | cons a more ih =>
    simp only [List.length_cons,List.cons_append,splitChildBits,ih,Option.map_some]
    congr 1

theorem measured_decoder_strips_exact_ancestor_address {w : ℕ} (raw : Word w) (b : Bool) :
    splitChildBits w (childHalfKey raw b).bits=⟨some (raw,b),5*w+4⟩ := by
  obtain ⟨bits,size⟩ := raw
  subst w
  exact exact_appended_side_bit bits b

#print axioms exact_appended_side_bit
#print axioms measured_decoder_strips_exact_ancestor_address
end J6R58RequestSource
