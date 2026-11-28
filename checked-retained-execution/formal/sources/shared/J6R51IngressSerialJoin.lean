import J6R51IngressPhysicalFile

/-! A serializer on raw declarations and raw CNF, not on an
externally supplied incidence file. Each signed old half also yields
the raw row/column pair needed by R11. The target roster is emitted
independently of (and includes zero-degree rows not in) that tape. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6R49RootIngress J6R50RootIngress J6R30GeneratedRootLayout
open J7R9Compiler J7R9Subdivision J7R10Plant
open J6R12CollisionGreedyStep J6R12CollisionEdges J6R10Repack
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 15000000

def copyEndpoints {r c d : ℕ} (p : SignedHalfPort r c d) :
    Meter (List Bool×List Bool) :=
  let row := copyPortWord p.row
  let col := copyPortWord p.column
  ⟨(row.result.val,col.result.val),row.steps+col.steps+6⟩

theorem copy_endpoints_exact {r c d : ℕ} (p : SignedHalfPort r c d) :
    (copyEndpoints p).result=(p.row.val,p.column.val) ∧
      (copyEndpoints p).steps=10+4*r+4*c := by
  simp only [copyEndpoints,port_word_copy]
  constructor
  · trivial
  · omega

structure SerializedFrame (r c d : ℕ) where
  targets : List Target
  ports : List (SignedHalfPort r c d)
  incidence : List (List Bool×List Bool)

def serializeRawCNF {d r c : ℕ}
    (hw jw : ℕ) (declares : List (List Bool)) (F : BitsCNF) :
    Meter (Option (SerializedFrame r c d)) :=
  -- These are actual input-word widths used by the parsers, not data callbacks.
  let G := compilePortRoster (h:=hw) (d:=d) (j:=jw) declares F
  let A := buildPhysicalFrame (r:=r) (c:=c) G.result
  match A.result with
  | none => ⟨none,G.steps+A.steps+5⟩
  | some p =>
    let B := mapMeter copyEndpoints p.ports
    ⟨some ⟨p.targets,p.ports,B.result⟩,G.steps+A.steps+B.steps+9⟩

theorem raw_endpoint_tape_fee {r c d : ℕ} (ps : List (SignedHalfPort r c d)) :
    (mapMeter copyEndpoints ps).result=ps.map (fun p=>(p.row.val,p.column.val)) ∧
      (mapMeter copyEndpoints ps).steps≤(16+4*r+4*c)*ps.length := by
  have E := mapMeter_exact copyEndpoints (fun p : SignedHalfPort r c d=>(p.row.val,p.column.val))
    (10+4*r+4*c) ps (fun p _=>⟨(copy_endpoints_exact p).1,(copy_endpoints_exact p).2.le⟩)
  exact ⟨E.1,E.2.trans (by
    apply Nat.mul_le_mul_right
    omega)⟩

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V]

theorem endpoints_match_fresh_format
    (H : CNF V) (s : DeclaredOrder V) (a e r c d : ℕ)
    (ef : nWires H<2^e) (rf : Fintype.card (OrderedOld H)≤2^r) (cf : nSubdiv H≤2^c)
    (df : ∀ v : OrderedOld H,orderedDegree H v≤2^d) :
    let F := freshFormat H s a e r c ef rf cf
    (List.ofFn (plantHalfPort (freshPlant H s) (freshCodec H s r c d rf cf df))).map
        (fun p=>(p.row.val,p.column.val)) =
      F.edges.map (fun u=>(encodeBits F.kR (F.rCode (F.row u)),
        encodeBits F.kC (F.cCode (F.col u)))) := by
  have D : List.finRange (nWires H)=List.ofFn (fun i : Fin (nWires H)=>i) := by
    apply List.ext_getElem
    · simp
    · intro k hk hl
      apply Fin.ext
      simp
  dsimp only [freshFormat]
  change (_ : List (List Bool×List Bool))=(List.finRange (nWires H)).map _
  rw [D,List.map_ofFn,List.map_ofFn]
  rfl

theorem serialized_actual_fresh_input (F : CNF V) (s : DeclaredOrder V)
    (code : V→List Bool) (inj : Function.Injective code)
    (h d j r c a e : ℕ) (hh : 0<h) (hd : 0<d) (hj : 0<j) (hr : 0<r) (hc : 0<c)
    (fitH : (guardedInOrder F s.roster).length≤2^h)
    (fitD : ∀ row∈guardedInOrder F s.roster,row.length≤2^d)
    (fitJ : ∀ v,(occurrences (guardedInOrder F s.roster) v).length-3≤2^j)
    (ef : nWires (guardedInOrder F s.roster)<2^e)
    (rf : Fintype.card (OrderedOld (guardedInOrder F s.roster))≤2^r)
    (cf : nSubdiv (guardedInOrder F s.roster)≤2^c)
    (df : ∀ v : OrderedOld (guardedInOrder F s.roster),orderedDegree (guardedInOrder F s.roster) v≤2^d) :
    let H := guardedInOrder F s.roster
    let R := guardRoster s
    let S := freshFormat H R a e r c ef rf cf
    let C := freshCodec H R r c d rf cf df
    let P := serializeRawCNF (r:=r) (c:=c) (d:=d) h j (s.roster.map code) (codeCNF code F)
    ∃ file : SerializedFrame r c d,
      P.result=some file ∧
      file.targets=(freshVisits H R).map S.target ∧
      file.ports=List.ofFn (plantHalfPort (freshPlant H R) C) ∧
      file.incidence=S.edges.map (fun u=>
        (encodeBits S.kR (S.rCode (S.row u)),encodeBits S.kC (S.cCode (S.col u)))) := by
  let H := guardedInOrder F s.roster
  let S := guardRoster s
  let Q := freshFormat H S a e r c ef rf cf
  let L := List.ofFn (plantHalfPort (freshPlant H S) (freshCodec H S r c d rf cf df))
  let T := (freshVisits H S).map Q.target
  let A := (mapMeter copyEndpoints L).result
  let G := compilePortRoster (h:=h) (d:=d) (j:=j) (s.roster.map code) (codeCNF code F)
  obtain ⟨u,w⟩ := actual_raw_port_roster F s code inj hh hd hj fitH fitD fitJ
  have shape : G.result=(⟨rawWires (h:=h) (d:=d) (j:=j) H S (guardCode code),
      (oldRoster H S).map (rowSeeds H (guardCode code))⟩ : PortRoster h d j) := by
    change G.result.wires=_ at u
    change G.result.rows=_ at w
    cases E : G.result with
    | mk ws rs =>
      rw [E] at u w
      change ws=_ at u
      change rs=_ at w
      rw [u,w]
      rfl
  have frame := frame_on_legal_roster H S (guardCode code) (guard_code_injective code inj)
    fitH fitD fitJ a e hr hc hd ef rf cf df
  refine ⟨⟨T,L,A⟩,?_,rfl,rfl,?_⟩
  · dsimp only [serializeRawCNF]
    rw [shape,frame]
  · exact (raw_endpoint_tape_fee L).1.trans (endpoints_match_fresh_format H S a e r c d ef rf cf df)

#print axioms copy_endpoints_exact
#print axioms raw_endpoint_tape_fee
#print axioms endpoints_match_fresh_format
#print axioms serialized_actual_fresh_input
end
end J6R51Ingress
