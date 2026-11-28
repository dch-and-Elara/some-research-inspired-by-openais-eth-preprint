import J6R50LeafGate
import J6R50LeafPage
import J6R49LeafCore

/-! One finite leaf command is built by paid lookup from the original
gateData / existing page origin bank, not from a supplied decoded slot.
The erased old opcode evaluator agrees with the typed R48 command
on both words and actual read cost. -/
namespace J6R50Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Leaf J6R21Ancestor
open J6R22Active J6R24MeteredRecursion J6R27OriginalGate J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R26DescriptorTree
open J6OrientedHost A1R10 A1R11 A1R12
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000

inductive ReadCmd (key page : ℕ) where
  | gate (b : ℕ) (op : CodeGate (J6R15ModeCost.Word b))
  | packet (creator : J6R15ModeCost.Word key) (pageID : J6R15ModeCost.Word page)
      (depth : ℕ) (wires : List WireRead)

def eraseCode {N key page : ℕ} : PageReadCode N key page → ReadCmd key page
  | .original b G => .gate b (forgetGate G)
  | .generated id pg d w => .packet id pg d w

def ReadCmd.read {f : ℤ[X]} {p ell key prec tw bw page : ℕ}
    (op : ReadCmd key page) (hf : f.Monic)
    (F : Frame f p) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (bits : List Bool) : Meter (Block F ell) :=
  match op with
  | .gate _ G =>
    let r := runCode bits G
    ⟨if r.result then uvOne F.hp F.sizePos pos else uvZero F.hp F.words ell,
      r.steps+uvWidth F.words.length ell p+4⟩
  | .packet id pg d wires => readPage hf F pos id pg d wires bits B

theorem erase_read_exact {f : ℤ[X]} {N p ell key prec tw bw page : ℕ}
    (op : PageReadCode N key page) (hf : f.Monic)
    (F : Frame f p) (pos : 0<ell) (B : PageBank f ell key prec tw bw page) (bits : List Bool) :
    (eraseCode op).read hf F pos B bits=op.run hf F pos B bits := by
  cases op with
  | generated id pg d wires => rfl
  | original b G =>
    simp only [eraseCode,ReadCmd.read,PageReadCode.run,uvGate,coded_run_is_original]

inductive SourceHead (w key prec page : ℕ) where
  | old (gateData : CodeGate (J6R15ModeCost.Word w))
  | paged (origin : PageOrigin key prec page)

abbrev OriginTable (owner w key prec page : ℕ) :=
  List (RefRow owner (SourceHead w key prec page))

def buildBody {own w key prec page : ℕ} (N b : ℕ) (keys : List (J6R15ModeCost.Word w))
    (owner : J6R15ModeCost.Word own) (lines : List (ResidentPort own w))
    (head : SourceHead w key prec page) : Meter (Option (ReadCmd key page)) :=
  match head with
  | .old gateData =>
    let src := compileCurrentGate b keys gateData
    ⟨src.result.map (ReadCmd.gate b),src.steps+5⟩
  | .paged site =>
    let src := buildPage N keys owner lines site
    ⟨src.result.map eraseCode,src.steps+5⟩

def buildOwner {own w key prec page : ℕ} (N b : ℕ) (keys : List (J6R15ModeCost.Word w))
    (lines : List (ResidentPort own w)) (table : OriginTable own w key prec page)
    (owner : J6R15ModeCost.Word own) : Meter (Option (ReadCmd key page)) :=
  let head := locate owner table
  match head.result with
  | none => ⟨none,head.steps+3⟩
  | some h =>
    let out := buildBody N b keys owner lines h
    ⟨out.result,head.steps+out.steps+4⟩

theorem bought_owner_record {own w key prec page : ℕ} (N b : ℕ)
    (keys : List (J6R15ModeCost.Word w)) (lines : List (ResidentPort own w))
    (table : OriginTable own w key prec page) (owner : J6R15ModeCost.Word own)
    (entry : SourceHead w key prec page)
    (listed : (⟨owner,entry⟩ : RefRow own (SourceHead w key prec page))∈table)
    (single : ∀ (r : RefRow own (SourceHead w key prec page)),r∈table→RefRow.address r=owner→RefRow.payload r=entry) :
    let out := buildOwner N b keys lines table owner
    let c :=  buildBody N b keys owner lines entry
    out.result=c.result ∧ out.steps≤locateFee own table.length+c.steps+4 := by
  have get : (locate owner table).result=some entry := by
    apply locate_hit
    · exact listed
    · intro r hr h
      exact single r hr h
  dsimp only [buildOwner]
  rw [get]
  exact ⟨rfl,Nat.add_le_add_right (Nat.add_le_add_right (locate_bound _ _) _) _⟩

theorem paid_original_body {own w key prec page N b d : ℕ}
    (keys : List (J6R15ModeCost.Word w)) (keyAt : Fin N→J6R15ModeCost.Word w)
    (inj : Function.Injective keyAt) (actual : keys=List.ofFn keyAt)
    (owner : J6R15ModeCost.Word own) (lines : List (ResidentPort own w))
    (slot : Fin d→Fin N) (G : Gate d) (hb : 0<b) (fit : N≤2^b) :
    let run := buildBody (key:=key) (prec:=prec) (page:=page) N b keys owner lines
      (.old (encodeGate (keyAt∘slot) G))
    run.result=some (eraseCode (.original b (gateTape fit slot G))) ∧
      run.steps≤currentGateFee w b N d+5 := by
  obtain ⟨val,cost⟩ := current_source_gate hb fit keys keyAt inj actual slot G
  dsimp only [buildBody]
  rw [val]
  exact ⟨rfl,Nat.add_le_add_right cost _⟩

theorem paid_page_body {V : Type*} {own w key prec page N b : ℕ}
    (keys : List (J6R15ModeCost.Word w)) (keyAt : Fin N→J6R15ModeCost.Word w)
    (inj : Function.Injective keyAt) (actual : keys=List.ofFn keyAt)
    (owner : J6R15ModeCost.Word own) (lines : List (ResidentPort own w))
    (site : PageOrigin key prec page) (born : Stamp key prec) (pageID : J6R15ModeCost.Word page)
    (origin : site.header=⟨born,some pageID⟩)
    (ports : List V) (body : V→List Bool) (slot : V→Fin N)
    (actualPorts : (lines.filter (fun r=>(cmpAddr owner r.address).result)).map RefRow.payload=
      ports.map (fun u=>⟨keyAt (slot u),body u⟩)) :
    let out := buildBody N b keys owner lines (.paged site)
    out.result=some (.packet born.creator pageID site.clock.length
      (ports.map (fun u=>⟨body u,List.replicate (slot u).val true⟩))) ∧
    out.steps=pageBuildFee owner lines key prec page site.clock.length
      (ports.map (fun u=>J6R34ChildPath.sourceWireFee w (slot u).val (body u).length)).sum+5 := by
  obtain ⟨val,cost⟩ := build_page_from_resident keys keyAt inj actual owner lines site born pageID
    origin ports body slot actualPorts
  dsimp only [buildBody]
  rw [val,cost]
  exact ⟨rfl,rfl⟩

#print axioms erase_read_exact
#print axioms bought_owner_record
#print axioms paid_original_body
#print axioms paid_page_body
end J6R50Leaf
