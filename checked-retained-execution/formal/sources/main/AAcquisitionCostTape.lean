import AAcquisitionCostSeats
import AAcquisitionCostSwitch

/-! A4's sparse predecessor plan can be produced by a sequential scan
of the public packet records, with no repeated search or random access.
At a packet boundary the previous-address register is reset. -/

namespace AAcquisitionCost

def tapePred {A : Type*} (previous : Option A) : List A → List (Option A)
  | [] => []
  | a::as => previous :: tapePred (some a) as

theorem tapePred_head {A : Type*} (previous : Option A) (words : List A)
    (h : 0 < words.length) : (tapePred previous words)[0]? = some previous := by
  cases words with
  | nil => simp at h
  | cons a as => rfl

theorem tapePred_succ {A : Type*} (previous : Option A) (words : List A) (i : ℕ)
    (h : i+1 < words.length) :
    (tapePred previous words)[i+1]? = (words[i]?).map some := by
  induction words generalizing previous i with
  | nil => simp at h
  | cons a as ih =>
    cases i with
    | zero =>
      cases as with
      | nil => simp at h
      | cons b bs => rfl
    | succ i =>
      have ht : i+1 < as.length := by simp only [List.length_cons] at h; omega
      change (tapePred (some a) as)[i+1]? = (as[i]?).map some
      exact ih (some a) i ht

def packetRecords {W P A : Type*} {L : ℕ} (seat : W ≃ P × Fin L)
    (record : W → A) (packet : P) : List A :=
  List.ofFn fun j => record (seat.symm (packet,j))

theorem tape_matches_wirePred {W P A : Type*} {L : ℕ} (seat : W ≃ P × Fin L)
    (record : W → A) (packet : P) (j : Fin L) :
    (tapePred none (packetRecords seat record packet))[j.val]? =
      some ((wirePred seat (seat.symm (packet,j))).map record) := by
  rcases j with ⟨j,hj⟩
  have hlen : (packetRecords seat record packet).length = L := by simp [packetRecords]
  cases j with
  | zero =>
    rw [tapePred_head _ _ (by omega)]
    simp [wirePred, slotPred]
  | succ j =>
    rw [tapePred_succ _ _ j (by omega)]
    have hj' : j < L := by omega
    have get : (packetRecords seat record packet)[j]? =
        some (record (seat.symm (packet,⟨j,hj'⟩))) := by
      simp [packetRecords, hj']
    rw [get]
    simp [wirePred, slotPred]

/-- Tag then payload; an empty predecessor has no payload. -/
def serializePred (x : Option (List Bool)) : List Bool :=
  x.isSome :: x.getD []

def tapeTrace (prev : Option (List Bool)) : List (List Bool) → List BitOp
  | [] => []
  | w::ws => w.map BitOp.read ++ (serializePred prev).map BitOp.write ++ tapeTrace (some w) ws

theorem tapeTrace_exact (prev : Option (List Bool)) (words : List (List Bool)) :
    consumed (tapeTrace prev words) = words.flatten ∧
    emitted (tapeTrace prev words) = ((tapePred prev words).map serializePred).flatten := by
  induction words generalizing prev with
  | nil => simp [tapeTrace,tapePred,consumed,emitted]
  | cons w ws ih =>
    obtain ⟨hread,hwrite⟩ := ih (some w)
    unfold consumed at hread
    unfold emitted at hwrite
    simp [tapeTrace,tapePred,consumed,emitted,hread,hwrite,List.filterMap_append,
      List.filterMap_map,Function.comp_def]

theorem tapeTrace_budget (prev : Option (List Bool)) (words : List (List Bool)) (width : ℕ)
    (hprev : (prev.getD []).length ≤ width) (hwords : ∀ w ∈ words, w.length ≤ width) :
    (tapeTrace prev words).length ≤ (2*width+1)*words.length := by
  induction words generalizing prev with
  | nil => simp [tapeTrace]
  | cons w ws ih =>
    have hw := hwords w (by simp)
    have hrem := ih (some w) hw (fun q hq => hwords q (by simp [hq]))
    simp only [tapeTrace,List.length_append,List.length_map, serializePred,List.length_cons,
      Nat.mul_succ]
    omega

def explicitAddressBits (m width : ℕ) : ℕ := m*(width+1)+1

theorem tapeTrace_linear_bits (prev : Option (List Bool)) (words : List (List Bool)) (width : ℕ)
    (hprev : (prev.getD []).length ≤ width) (hwords : ∀ w ∈ words, w.length ≤ width) :
    (tapeTrace prev words).length ≤ 2*explicitAddressBits words.length width := by
  refine (tapeTrace_budget prev words width hprev hwords).trans ?_
  unfold explicitAddressBits
  ring_nf
  omega

#print axioms tape_matches_wirePred
#print axioms tapeTrace_exact
#print axioms tapeTrace_budget
#print axioms tapeTrace_linear_bits

end AAcquisitionCost
