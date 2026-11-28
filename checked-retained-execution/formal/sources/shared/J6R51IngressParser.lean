import J6R50RootIngressRankChart

/-! Deterministic literal encounter order, with raw finite-word clause
and local-leg counters. No ordering from Finset.toList is used for
literal occurrences. Declared variables still enter as the input roster. -/
namespace J6R51Ingress
open Std.Sat A1R10 AOracleMachineTime J6R49RootIngress J6R50RootIngress J7R9Compiler
open J6R27OriginalGate
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8500000

structure OccToken (h d : ℕ) where
  clause : Word h
  leg : Word d
  nameBits : List Bool
  sign : Bool

def parseClause {h d : ℕ} (clause : Word h) (row : BitsClause) : Meter (List (OccToken h d)) :=
  let L := indexTape d row.length
  let out := row.zipWith (fun a j => (⟨clause,j,a.1,a.2⟩ : OccToken h d)) L.result
  ⟨out,L.steps+5+(row.map (fun l=>16+4*(h+d+l.1.length))).sum⟩

def parseRows {h d : ℕ} : BitsCNF → List (Word h) → Meter (List (List (OccToken h d)))
  | a::as,k::ks =>
    let H := parseClause k a
    let T := parseRows as ks
    ⟨H.result::T.result,H.steps+T.steps+5⟩
  | _,_ => ⟨[],2⟩

def parseGuard {h d : ℕ} (rows : BitsCNF) : Meter (List (OccToken h d)) :=
  let K := indexTape h rows.length
  let R := parseRows (d:=d) rows K.result
  ⟨R.result.flatten,K.steps+R.steps+5+4*(rows.length+R.result.flatten.length)⟩

def parseInput {h d : ℕ} (declares : List (List Bool)) (F : BitsCNF) :
    Meter (List (OccToken h d)) :=
  let G := guardedMeter declares F
  let P := parseGuard (h:=h) (d:=d) G.result
  ⟨P.result,G.steps+P.steps+4⟩

def occurrenceRows {V : Type*} (H : CNF V) : List (List (Occurrence H)) :=
  List.ofFn (fun i : ClauseIndex H => List.ofFn (fun j : Fin (H.get i).length => ⟨i,j⟩))

def occurrenceOrder {V : Type*} (H : CNF V) : List (Occurrence H) :=
  (occurrenceRows H).flatten

def guardToken {V : Type*} {h d : ℕ} (H : CNF V) (code : V→List Bool)
    (o : Occurrence H) : OccToken h d :=
  ⟨wordAt h o.1.val,wordAt d o.2.val,code (literal H o).1,(literal H o).2⟩

theorem parse_clause_exact {V : Type*} {h d : ℕ} (row : CNF.Clause V) (code : V→List Bool)
    (k : Word h) (hd : 0<d) (fit : row.length≤2^d) :
    (parseClause (d:=d) k (row.map (codeLit code))).result =
      List.ofFn (fun j : Fin row.length => (⟨k,wordAt d j.val,code (row.get j).1,
        (row.get j).2⟩ : OccToken h d)) := by
  have E := (index_tape_exact d row.length hd fit).1
  have L : row.map (codeLit code)=List.ofFn (fun j : Fin row.length => codeLit code (row.get j)) := by
    change _=List.ofFn (codeLit code ∘ row.get)
    rw [←List.map_ofFn,List.ofFn_get]
  dsimp only [parseClause]
  rw [List.length_map,E,L,zip_ofFn_exact]
  rfl

theorem parse_rows_map_ofFn {h d : ℕ}
    (n : ℕ) (a : Fin n→BitsClause) (b : Fin n→Word h)
    (out : Fin n→List (OccToken h d))
    (hex : ∀ i,(parseClause (b i) (a i)).result=out i) :
    (parseRows (List.ofFn a) (List.ofFn b)).result=List.ofFn out := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.ofFn_succ]
    simp only [parseRows,hex]
    rw [ih _ _ _ (fun i=>hex i.succ)]

theorem parse_guard_exact {V : Type*} {h d : ℕ} (H : CNF V) (code : V→List Bool)
    (hh : 0<h) (hd : 0<d) (fitH : H.length≤2^h) (fitD : ∀ row∈H,row.length≤2^d) :
    (parseGuard (h:=h) (d:=d) (codeCNF code H)).result =
      (occurrenceOrder H).map (guardToken H code) := by
  have lhs : codeCNF code H=List.ofFn (fun i : ClauseIndex H => (H.get i).map (codeLit code)) := by
    change (H.map (List.map (codeLit code)))=List.ofFn (List.map (codeLit code) ∘ H.get)
    rw [← List.map_ofFn,List.ofFn_get]
  have E := (index_tape_exact h H.length hh fitH).1
  simp only [parseGuard,codeCNF,List.length_map,E]
  change (parseRows (d:=d) (codeCNF code H)
    (List.ofFn (fun i : ClauseIndex H=>wordAt h i.val))).result.flatten=_
  rw [lhs,parse_rows_map_ofFn H.length _ _ (fun i => (List.ofFn (fun j : Fin (H.get i).length =>
    guardToken H code ⟨i,j⟩)))]
  · simp [occurrenceOrder,occurrenceRows,List.map_flatten,List.map_ofFn,Function.comp_def]
  · intro i
    exact parse_clause_exact (H.get i) code (wordAt h i.val) hd (fitD _ (List.get_mem _ _))

theorem parse_actual_cnf {V : Type} [DecidableEq V] [Fintype V] {h d : ℕ}
    (F : CNF V) (code : V→List Bool) (inj : Function.Injective code)
    (hh : 0<h) (hd : 0<d) (fitH : (guarded F).length≤2^h)
    (fitD : ∀ row∈(guarded F),row.length≤2^d) :
    (parseInput (h:=h) (d:=d) ((Finset.univ : Finset V).toList.map code) (codeCNF code F)).result =
      (occurrenceOrder (guarded F)).map (guardToken (guarded F) (guardCode code)) := by
  dsimp only [parseInput]
  rw [paid_guard_original_syntax code inj F]
  exact parse_guard_exact (guarded F) (guardCode code) hh hd fitH fitD

def bucket {h d : ℕ} (v : List Bool) : List (OccToken h d)→Meter (List (OccToken h d))
  | [] => ⟨[],2⟩
  | z::zs =>
    let R := eqRawBits v z.nameBits
    let T := bucket v zs
    ⟨if R.result then z::T.result else T.result,R.steps+T.steps+6⟩

theorem bucket_exact {h d : ℕ} (v : List Bool) (slots : List (OccToken h d)) :
    (bucket v slots).result=slots.filter (fun z=>decide (z.nameBits=v)) ∧
      (bucket v slots).steps≤2+slots.length*(5*v.length+8) := by
  induction slots with
  | nil => simp [bucket]
  | cons z zs ih =>
    obtain ⟨e,n⟩ := eq_raw_bits_exact v z.nameBits
    constructor
    · simp only [bucket,ih.1,List.filter_cons]
      by_cases hv : z.nameBits=v
      · rw [e.mpr hv.symm]
        simp [hv]
      · have R := Bool.eq_false_iff.mpr (fun t => hv (e.mp t).symm)
        rw [R]
        simp [hv]
    · simp only [bucket,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem bucket_actual_occurrences {V : Type*} [DecidableEq V] {h d : ℕ}
    (H : CNF V) (code : V→List Bool) (inj : Function.Injective code) (v : V) :
    (bucket (code v) ((occurrenceOrder H).map (guardToken H code) : List (OccToken h d))).result=
      ((occurrenceOrder H).filter (fun i=>decide ((literal H i).1=v))).map (guardToken H code) := by
  rw [(bucket_exact _ _).1,List.filter_map]
  have E : ((fun z : OccToken h d => decide (z.nameBits=code v)) ∘ guardToken H code) =
      (fun i => decide ((literal H i).1=v)) := by
    funext q
    simp [guardToken,Function.Injective.eq_iff inj]
  rw [E]

#print axioms parse_clause_exact
#print axioms parse_rows_map_ofFn
#print axioms parse_guard_exact
#print axioms parse_actual_cnf
#print axioms bucket_exact
#print axioms bucket_actual_occurrences
end J6R51Ingress
