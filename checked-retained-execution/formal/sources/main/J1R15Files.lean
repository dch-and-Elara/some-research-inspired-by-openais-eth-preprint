import J1R15BitLookup
import J1MainSourcePlacement

/-! Exact file lookups grounded in literal original MAIN incidence
positions, not a function that supplies an already computed row token. -/
namespace J1R15
open AOracleMachineTime J1R14Query J1MainSourcePlacement MainProbe

def symbols {q r : ℕ} (a : Fin q → Fin r) : List Bool :=
  (List.ofFn a).flatMap finWord

@[simp] theorem symbols_length {q r : ℕ} (a : Fin q → Fin r) :
    (symbols a).length = q*Nat.clog 2 r := by
  unfold symbols
  rw [flatMap_length_const _ _ finWord_length,List.length_ofFn]

theorem symbols_injective (q r : ℕ) : Function.Injective (@symbols q r) := by
  intro a b he
  have h : List.ofFn a = List.ofFn b :=
    flatMap_fixed_injective finWord _ finWord_length (finWord_injective r) (by simp) he
  funext i
  have hi : i.val < (List.ofFn a).length := by simp
  simpa using List.getElem_of_eq h hi

def cellCode {q r : ℕ} (u : Cell (Fin q) (Fin r)) : List Bool :=
  symbols u.1 ++ symbols u.2

@[simp] theorem cellCode_length {q r : ℕ} (u : Cell (Fin q) (Fin r)) :
    (cellCode u).length = 2*q*Nat.clog 2 r := by
  unfold cellCode
  simp only [List.length_append,symbols_length,two_mul,Nat.add_mul]

theorem cellCode_injective (q r : ℕ) : Function.Injective (@cellCode q r) := by
  intro a b he
  obtain ⟨h₁,h₂⟩ := List.append_inj he (by simp [symbols_length])
  exact Prod.ext (symbols_injective q r h₁) (symbols_injective q r h₂)

def positionCode {q r h : ℕ} (p : Fin h × Cell (Fin q) (Fin r)) : List Bool :=
  finWord p.1 ++ cellCode p.2

@[simp] theorem positionCode_length {q r h : ℕ} (p : Fin h × Cell (Fin q) (Fin r)) :
    (positionCode p).length = Nat.clog 2 h + 2*q*Nat.clog 2 r := by
  simp [positionCode]

theorem positionCode_injective (q r h : ℕ) : Function.Injective (@positionCode q r h) := by
  intro a b he
  obtain ⟨h₁,h₂⟩ := List.append_inj he (by simp [finWord_length])
  exact Prod.ext (finWord_injective h h₁) (cellCode_injective q r h₂)

def nodeVarCode {q n : ℕ} (t : Fin q) (v : Fin n) : List Bool :=
  finWord t ++ finWord v

@[simp] theorem nodeVarCode_length {q n : ℕ} (t : Fin q) (v : Fin n) :
    (nodeVarCode t v).length = Nat.clog 2 q + Nat.clog 2 n := by
  simp [nodeVarCode]

theorem nodeVar_eq {q n : ℕ} {t t' : Fin q} {v v' : Fin n}
    (h : nodeVarCode t v = nodeVarCode t' v') : t=t' ∧ v=v' := by
  obtain ⟨h₁,h₂⟩ := List.append_inj h (by simp [finWord_length])
  exact ⟨finWord_injective q h₁,finWord_injective n h₂⟩

def groupFile {q r n : ℕ} (labels : Fin n → Fin q → Fin r) : File :=
  (List.finRange q).flatMap fun t => List.ofFn fun v : Fin n =>
    (nodeVarCode t v,finWord (labels v t))

@[simp] theorem groupFile_length {q r n : ℕ} (labels : Fin n → Fin q → Fin r) :
    (groupFile labels).length = q*n := by
  unfold groupFile
  rw [flatMap_length_const _ n (fun _ => List.length_ofFn) _,List.length_finRange]

theorem groupFile_read {q r n : ℕ} (labels : Fin n → Fin q → Fin r)
    (t : Fin q) (v : Fin n) :
    (lookup (nodeVarCode t v) (groupFile labels)).result = some (finWord (labels v t)) := by
  apply lookup_unique
  · exact List.mem_flatMap.mpr ⟨t,List.mem_finRange _,List.mem_ofFn.mpr ⟨v,rfl⟩⟩
  · intro w hw
    obtain ⟨t',_,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨v',he⟩ := List.mem_ofFn.mp hw
    obtain ⟨ht,hv⟩ := nodeVar_eq (congrArg Prod.fst he)
    subst t'
    subst v'
    exact (congrArg Prod.snd he).symm

theorem groupFile_cost {q r n : ℕ} (labels : Fin n → Fin q → Fin r)
    (t : Fin q) (v : Fin n) :
    (lookup (nodeVarCode t v) (groupFile labels)).steps ≤
      q*n*(5*(Nat.clog 2 q+Nat.clog 2 n)+Nat.clog 2 r+3)+1 := by
  rw [← groupFile_length labels]
  apply lookup_cost _ _ _ _ (by simp)
  intro z hz
  obtain ⟨t',_,hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨v',he⟩ := List.mem_ofFn.mp hz
  subst z
  simp

theorem attach_ofFn {n : ℕ} (key : Fin n → List Bool) (x : Fin n → Bool) :
    (attachCandidates (List.ofFn key) (List.ofFn x)).result =
      List.ofFn (fun j => (key j,[x j])) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ]
    simp [attachCandidates,ih]

def indexedCandidate {n : ℕ} (raw : List Bool) : Meter File :=
  attachCandidates (List.ofFn (@finWord n)) raw

theorem indexedCandidate_read {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    (lookup (finWord v) (indexedCandidate (n:=n) (List.ofFn x)).result).result =
      some [x v] := by
  rw [indexedCandidate,attach_ofFn]
  apply lookup_unique
  · exact List.mem_ofFn.mpr ⟨v,rfl⟩
  · intro b hb
    obtain ⟨j,h⟩ := List.mem_ofFn.mp hb
    have hj := finWord_injective n (congrArg Prod.fst h)
    subst j
    exact (congrArg Prod.snd h).symm

theorem indexedCandidate_setup_cost (n : ℕ) (raw : List Bool) :
    (indexedCandidate (n:=n) raw).steps ≤ n*(2*Nat.clog 2 n+3)+1 := by
  unfold indexedCandidate
  have h := attachCandidates_cost (List.ofFn (@finWord n)) raw (Nat.clog 2 n) (by
    intro t ht
    obtain ⟨v,rfl⟩ := List.mem_ofFn.mp ht
    simp)
  simpa only [List.length_ofFn] using h

theorem indexedCandidate_read_cost {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    (lookup (finWord v) (indexedCandidate (n:=n) (List.ofFn x)).result).steps ≤
      n*(5*Nat.clog 2 n+1+3)+1 := by
  rw [indexedCandidate,attach_ofFn]
  have he := lookup_cost (finWord v) (List.ofFn fun j => (finWord j,[x j]))
    (Nat.clog 2 n) 1 (by simp) (by
      intro z hz
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hz
      simp)
  simpa only [List.length_ofFn] using he

section Placement
variable {q r n M h : ℕ} {E F : Type*} [Fintype E]
variable (data : IncidenceData (Fin q) (Fin r) E (Fin n) F)
variable (cap : ∀ u, Fintype.card (CellFibre data u) ≤ h)
variable (ord : Fin M ≃ E)

noncomputable def placedFile : File :=
  List.ofFn fun i : Fin M =>
    (positionCode (position data h cap (ord i)),finWord (data.var (ord i)))

@[simp] theorem placedFile_length : (placedFile data cap ord).length = M := by
  simp [placedFile]

theorem placedFile_read (c : Fin h) (u : Cell (Fin q) (Fin r)) :
    (lookup (positionCode (c,u)) (placedFile data cap ord)).result =
      (occupied data h cap c u).map finWord := by
  classical
  by_cases hs : ∃ e : E, position data h cap e = (c,u)
  · obtain ⟨e,he⟩ := hs
    have hc := occupied_at data h cap e
    change occupied data h cap (position data h cap e).1 (position data h cap e).2 = _ at hc
    rw [he] at hc
    rw [hc,Option.map_some]
    apply lookup_unique
    · exact List.mem_ofFn.mpr ⟨ord.symm e,by simp [he]⟩
    · intro bits hb
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hb
      have hp := positionCode_injective q r h (congrArg Prod.fst hi)
      have hj := position_injective data h cap (hp.trans he.symm)
      exact (congrArg Prod.snd hi).symm.trans (congrArg (finWord ∘ data.var) hj)
  · rw [empty_slot data h cap c u hs]
    apply lookup_absent
    intro z hz
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hz
    exact hs ⟨ord i, positionCode_injective q r h (congrArg Prod.fst hi)⟩

theorem placedFile_cost (c : Fin h) (u : Cell (Fin q) (Fin r)) :
    (lookup (positionCode (c,u)) (placedFile data cap ord)).steps ≤
      M*(5*(Nat.clog 2 h+2*q*Nat.clog 2 r)+Nat.clog 2 n+3)+1 := by
  have he := lookup_cost (positionCode (c,u)) (placedFile data cap ord)
    (Nat.clog 2 h+2*q*Nat.clog 2 r) (Nat.clog 2 n) (by simp) (by
      intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      simp)
  simpa only [placedFile_length] using he
end Placement

#print axioms symbols_injective
#print axioms cellCode_injective
#print axioms positionCode_injective
#print axioms nodeVar_eq
#print axioms groupFile_read
#print axioms groupFile_cost
#print axioms indexedCandidate_read
#print axioms indexedCandidate_setup_cost
#print axioms indexedCandidate_read_cost
#print axioms placedFile_read
#print axioms placedFile_cost
end J1R15
