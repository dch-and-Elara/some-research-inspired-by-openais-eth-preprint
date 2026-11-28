import J6R27PrescribedProbeBits
import J6R21AncestorDirectory
import J6Mesh

/-! Actual finite bits in a request to the completed-slot oracle.
The fixed literal input and one chart are shared, and the request
carries its true positive odd integer t, a fixed zero-mode tag,
and the actual row of binary extension coordinates. -/
namespace J6R33OriginalJ6
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6Mesh

def oddCounter (width : ℕ) : ℕ→Meter (Word width)
  | 0 => ⟨word 1,3*width+2⟩
  | n+1 =>
    let R := oddCounter width n
    let A := increment R.result
    let B := increment A.result
    ⟨B.result,R.steps+A.steps+B.steps+3⟩

theorem odd_counter_exact {w n : ℕ} (hw : 0<w) (fit : 2*n+1<2^w) :
    (oddCounter w n).result.val=2*n+1 ∧
      (oddCounter w n).steps=3*w+2+n*(26*w+11) := by
  induction n with
  | zero =>
    refine ⟨?_,by simp [oddCounter]⟩
    have one : 1 < (2:ℕ)^w := by omega
    exact word_val one
  | succ n ih =>
    obtain ⟨index,fee⟩ := ih (by omega)
    let r := oddCounter w n
    let a := increment r.result
    let b := increment a.result
    have e := increment_exact hw r.result (by change r.result.val = _ at index; omega)
    have av : a.result.val=r.result.val+1 := e.1
    have d := increment_exact hw a.result (by change r.result.val=_ at index; omega)
    change b.result.val=2*(n+1)+1 ∧
      r.steps+a.steps+b.steps+3=3*w+2+(n+1)*(26*w+11)
    change a.result.val=r.result.val+1 ∧ a.steps=13*w+4 at e
    change b.result.val=a.result.val+1 ∧ b.steps=13*w+4 at d
    change r.result.val=2*n+1 at index
    change r.steps=3*w+2+n*(26*w+11) at fee
    refine ⟨by omega,?_⟩
    rw [fee,e.2,d.2,Nat.add_mul]
    omega

theorem positive_odd_word_fits (m : ℕ) (i : Fin (m+1)) : index m i<2^(m+2) := by
  have all : ∀ k : ℕ,k≤(2:ℕ)^k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hs : 0<(2:ℕ)^k := by positivity
      rw [pow_succ]
      omega
  have h := all (m+1)
  have hi := (address_index m i).2.2.1
  rw [pow_succ]
  omega

def signedQuery (m : ℕ) (i : Fin (m+1)) (probe : List Bool) : Meter (List Bool) :=
  let v := oddCounter (m+2) i.val
  let c := copyBytes (v.result.bits++false::probe)
  ⟨c.result,v.steps+c.steps+4⟩

def queryFee (m e : ℕ) : ℕ :=
  (3*(m+2)+2)+m*(26*(m+2)+11)+3*(m+3+e)+5

theorem signed_query_exact (m : ℕ) (i : Fin (m+1)) (probe : List Bool) :
    (signedQuery m i probe).result=encodeBits (m+2) (index m i)++false::probe ∧
      (signedQuery m i probe).steps≤queryFee m probe.length := by
  let N := oddCounter (m+2) i.val
  have fit := positive_odd_word_fits m i
  obtain ⟨v,b⟩ := odd_counter_exact (show 0<m+2 by omega) fit
  have key : N.result=word (q:=m+2) (index m i) :=
    (valued_word N.result).symm.trans (congrArg word v)
  have cap : i.val*(26*(m+2)+11)≤m*(26*(m+2)+11) :=
    Nat.mul_le_mul_right _ (Nat.le_of_lt_succ i.isLt)
  constructor
  · change (copyBytes (N.result.bits++false::probe)).result=_
    rw [copyBytes_exact,key]
    rfl
  · change N.steps+(copyBytes (N.result.bits++false::probe)).steps+4≤_
    rw [copyBytes_exact,List.length_append,N.result.size,List.length_cons]
    rw [show N.steps=3*(m+2)+2+i.val*(26*(m+2)+11) from b]
    change (3*(m+2)+2+i.val*(26*(m+2)+11))+(3*((m+2)+(probe.length+1))+1)+4≤queryFee m probe.length
    unfold queryFee
    omega

def peelRequest : ℕ → List Bool→Meter (List Bool)
  | 0,xs => ⟨xs,2⟩
  | _+1,[] => ⟨[],2⟩
  | n+1,_::xs =>
    let R := peelRequest n xs
    ⟨R.result,R.steps+3⟩

theorem peel_request_exact (head body : List Bool) :
    peelRequest head.length (head++body)=⟨body,3*head.length+2⟩ := by
  induction head with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons,List.cons_append,peelRequest,ih]
    congr 1

theorem query_payload_exact (m : ℕ) (i : Fin (m+1)) (probe : List Bool) :
    peelRequest (m+3) (signedQuery m i probe).result=⟨probe,3*(m+3)+2⟩ := by
  let front := encodeBits (m+2) (index m i)++[false]
  have h : front.length=m+3 := by
    simp only [front,List.length_append,encodeBits_length,List.length_cons,List.length_nil]
  rw [←h,(signed_query_exact m i probe).1]
  have t : encodeBits (m+2) (index m i)++false::probe=front++probe := by
    simp only [front,List.append_assoc,List.singleton_append]
  rw [t,peel_request_exact]

#print axioms odd_counter_exact
#print axioms positive_odd_word_fits
#print axioms signed_query_exact
#print axioms peel_request_exact
#print axioms query_payload_exact
end J6R33OriginalJ6
