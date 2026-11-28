import J1R14QueryMenu
import Mathlib.Data.Fin.Tuple.Basic

/-! Executable enumeration of the printed MAIN address fields. The lists
describe the emitted stream and allow exact output bit accounting; this
implementation itself does not claim the source's sequential space bound. -/
namespace J1R14Query
open scoped BigOperators

def boxWords (D : ℕ) : (m : ℕ) → List (Fin m → Box D)
  | 0 => [Fin.elim0]
  | m+1 => (List.finRange (2*D+1)).flatMap fun x => (boxWords D m).map (Fin.cons x)

theorem boxWords_length (D m : ℕ) : (boxWords D m).length = (2*D+1)^m := by
  induction m with
  | zero => simp [boxWords]
  | succ m ih =>
    unfold boxWords
    have h (x : Box D) : ((boxWords D m).map (@Fin.cons m (fun _ => Box D) x)).length = (boxWords D m).length := by simp
    rw [flatMap_length_const _ _ h _,List.length_finRange,ih,pow_succ]
    exact Nat.mul_comm _ _

theorem boxWords_complete (D m : ℕ) (y : Fin m → Box D) : y ∈ boxWords D m := by
  induction m with
  | zero =>
    have h : y = Fin.elim0 := funext fun i => Fin.elim0 i
    simp [boxWords,h]
  | succ m ih =>
    change y ∈ (List.finRange (2*D+1)).flatMap _
    exact List.mem_flatMap.mpr ⟨y 0,List.mem_finRange _,List.mem_map.mpr
      ⟨Fin.tail y,ih (Fin.tail y),Fin.cons_self_tail y⟩⟩

def legalPairs (n q : ℕ) : List {p : Pair n // p.2 ⊆ p.1 ∧ p.1.card ≤ q} :=
  (pairs n q).pmap (fun p h => ⟨p,(mem_pairs p.1 p.2).mp h⟩) (fun _ h => h)

@[simp] theorem legalPairs_length (n q : ℕ) : (legalPairs n q).length = (pairs n q).length := by
  simp [legalPairs]

def allAddresses (Q n m D q : ℕ) : List (Address Q n m D q) :=
  (List.finRange Q).flatMap fun t =>
    (legalPairs n q).flatMap fun p =>
      (boxWords D m).map fun y => ⟨t,p.val.1,p.val.2,y,p.property.1,p.property.2⟩

theorem allAddresses_length (Q n m D q : ℕ) :
    (allAddresses Q n m D q).length =
      Q * (∑ s ∈ Finset.range (min q n+1), 2^s * n.choose s) * (2*D+1)^m := by
  unfold allAddresses
  have h (t : Fin Q) : ((legalPairs n q).flatMap fun p =>
      (boxWords D m).map (fun y => (⟨t,p.val.1,p.val.2,y,p.property.1,p.property.2⟩ :
        Address Q n m D q))).length = (pairs n q).length * (boxWords D m).length := by
    have he (p : {p : Pair n // p.2 ⊆ p.1 ∧ p.1.card ≤ q}) :
        ((boxWords D m).map (fun y => (⟨t,p.val.1,p.val.2,y,p.property.1,p.property.2⟩ :
          Address Q n m D q))).length = (boxWords D m).length := by simp
    rw [flatMap_length_const _ _ he _,legalPairs_length]
  rw [flatMap_length_const _ _ h _,List.length_finRange,pairs_length,boxWords_length,
    Nat.mul_assoc]

theorem allAddresses_emitted_bits (Q n m D q : ℕ) :
    ((allAddresses Q n m D q).flatMap tape).length =
      Q * (∑ s ∈ Finset.range (min q n+1), 2^s * n.choose s) * (2*D+1)^m *
        rootWidth Q n m D := by
  rw [emitted_bits,allAddresses_length]

#print axioms boxWords_length
#print axioms boxWords_complete
#print axioms legalPairs_length
#print axioms allAddresses_length
#print axioms allAddresses_emitted_bits
end J1R14Query
