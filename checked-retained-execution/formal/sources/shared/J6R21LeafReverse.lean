
import J6R21LeafMachine

/-! Expose the actual sequential reverse tape traversal, with the
same cost already used at each physical leaf assignment. -/
namespace J6R21Leaf
open AOracleMachineTime A1R10 A1R12

def reverseTape : List Bool→List Bool→Meter (List Bool)
  | [],acc => ⟨acc,2⟩
  | b::bs,acc => padCost (reverseTape bs (b::acc)) 3

theorem reverse_tape_exact (bits acc : List Bool) :
    (reverseTape bits acc).result=bits.reverse++acc ∧
      (reverseTape bits acc).steps=reverseFee bits.length := by
  induction bits generalizing acc with
  | nil => simp [reverseTape,reverseFee]
  | cons b bs ih =>
    obtain ⟨h,k⟩ := ih (b::acc)
    constructor
    · simp only [reverseTape,padCost,h,List.reverse_cons,List.append_assoc,List.singleton_append]
    · simp only [reverseTape,padCost,k,reverseFee,List.length_cons]
      omega

def exactBitDFS {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (read : List Bool→Meter (UVBlock fw ell)) :
    ℕ→List Bool→Meter (UVBlock fw ell)
  | 0,bits =>
    let t := reverseTape bits []
    padCost (read t.result) t.steps
  | n+1,bits => padCost (addM hp (exactBitDFS hp read n (false::bits))
      (exactBitDFS hp read n (true::bits))) 4

theorem exactBitDFS_public {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (read : List Bool→Meter (UVBlock fw ell)) (n : ℕ) (bits : List Bool) :
    exactBitDFS hp read n bits = enumerate hp read n bits := by
  induction n generalizing bits with
  | zero =>
    obtain ⟨h,k⟩ := reverse_tape_exact bits []
    simp only [exactBitDFS,enumerate,h,k,List.append_nil]
  | succ n ih => simp only [exactBitDFS,enumerate,ih]

#print axioms reverse_tape_exact
#print axioms exactBitDFS_public
end J6R21Leaf
