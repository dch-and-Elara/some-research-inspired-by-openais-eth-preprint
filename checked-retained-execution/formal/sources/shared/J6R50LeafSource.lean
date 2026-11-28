import J6R50LeafOnline
import J6R49LeafRuntime

/-! The static condition on a resident owner chart talks about real
source incidence, old syntax, and existing born page keys. It does not
provide completed ordinal words, arbitrary ring readings or a successful
resident compiler result as an axiom. -/
namespace J6R50Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R21Leaf J6R27OriginalGate
open J6ActiveRun J6R10Repack J6R11Blueprint J6R22Active J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R26DescriptorTree J6R36ChildFramedRoute J6R48Leaf J6R49Leaf
open J6R9Recursive J6OrientedHost
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 21000000

structure HasEntry {own w key prec page : ℕ}
    (table : OriginTable own w key prec page) (owner : J6R15ModeCost.Word own)
    (head : SourceHead w key prec page) : Prop where
  appears : (⟨owner,head⟩ : RefRow own (SourceHead w key prec page))∈table
  same : ∀ (r : RefRow own (SourceHead w key prec page)),r∈table→RefRow.address r=owner→RefRow.payload r=head

inductive SourceCommand {N own w key prec page : ℕ} (b : ℕ)
    (keyAt : Fin N→J6R15ModeCost.Word w) (lines : List (ResidentPort own w))
    (table : OriginTable own w key prec page) (owner : J6R15ModeCost.Word own) :
    PageReadCode N key page→Prop
  | old {d : ℕ} (slot : Fin d→Fin N) (gate : Gate d) (fit : N≤2^b)
      (listed : HasEntry table owner (.old (encodeGate (keyAt∘slot) gate))) :
      SourceCommand b keyAt lines table owner (.original b (gateTape fit slot gate))
  | paged {V : Type} (site : PageOrigin key prec page) (born : Stamp key prec)
      (pg : J6R15ModeCost.Word page) (ports : List V)
      (headers : V→List Bool) (slot : V→Fin N)
      (tag : site.header=⟨born,some pg⟩) (listed : HasEntry table owner (.paged site))
      (actual : (lines.filter (fun r=>(cmpAddr owner r.address).result)).map RefRow.payload=
        ports.map (fun u=>⟨keyAt (slot u),headers u⟩)) :
      SourceCommand b keyAt lines table owner
        (.generated born.creator pg site.clock.length
          (ports.map (fun u=>⟨headers u,List.replicate (slot u).val true⟩)))

theorem real_source_command_is_bought {N own w key prec page : ℕ} {b : ℕ}
    (hb : 0<b) (keys : List (J6R15ModeCost.Word w)) (keyAt : Fin N→J6R15ModeCost.Word w)
    (keyInj : Function.Injective keyAt) (keyTape : keys=List.ofFn keyAt)
    (lines : List (ResidentPort own w)) (table : OriginTable own w key prec page)
    (owner : J6R15ModeCost.Word own) {cmd : PageReadCode N key page}
    (check : SourceCommand b keyAt lines table owner cmd) :
    (buildOwner N b keys lines table owner).result=some (eraseCode cmd) := by
  cases check with
  | old slot gate fit listed =>
    exact (bought_owner_record N b keys lines table owner _ listed.appears listed.same).1.trans
      (paid_original_body keys keyAt keyInj keyTape owner lines slot gate hb fit).1
  | paged site born pg ports headers slot tag listed actual =>
    exact (bought_owner_record N b keys lines table owner _ listed.appears listed.same).1.trans
      (paid_page_body (b:=b) keys keyAt keyInj keyTape owner lines site born pg tag
        ports headers slot actual).1

theorem checked_online_leaf_from_rows {f : ℤ[X]} {ell own w key prec tw bw page : ℕ}
    {c : Call (PhysicalHost f ell)}
    (hf : f.Monic) (F : Frame f c.prec) (pos : 0<ell) (B : PageBank f ell key prec tw bw page)
    (b : ℕ) (hb : 0<b) (book : Meter (List (J6R15ModeCost.Word w)))
    (keyAt : Fin c.edges→J6R15ModeCost.Word w) (keyInj : Function.Injective keyAt)
    (keyTape : book.result=List.ofFn keyAt)
    (lines : List (ResidentPort own w)) (table : OriginTable own w key prec page)
    (roster : List (J6R15ModeCost.Word own))
    (name : Vertex c→J6R15ModeCost.Word own)
    (actualNames : roster=(vertexList c.host).map name)
    (ord : Fin c.edges≃c.host.Edge) (edgeCount : c.host.edgeCount=c.edges)
    (live : PageBank f ell key prec tw bw page→Prop) (opened : live B)
    (rows : ∀ v : Vertex c,@RowAt f ell key prec tw bw page c hf F pos ord v live)
    (validation : ∀ v,SourceCommand b keyAt lines table (name v) (rows v).code) :
    let D := PagedLeaf.toRaw (compiledLeaf edgeCount rows)
    let out := onlineLeaf hf F pos B c.edges b book lines table roster
    ∃ value, out.result=some value ∧
      F.decode value=reduce c.prec f ell (c.host.contract hf) ∧
      out.steps≤book.steps+4*c.edges+12+
        (D.rows.map (fun x=>(buildOwner c.edges b book.result lines table (name x.1)).steps+7)).sum+
        rawLeafCap F.words.length ell c.prec c.edges D.rows.length (prepriced D F B) F.hp := by
  let D := PagedLeaf.toRaw (compiledLeaf edgeCount rows)
  have names : roster=D.rows.map (name∘Prod.fst) := by
    change roster=((vertexList c.host).map (fun v=>(v,(rows v).code))).map (name∘Prod.fst)
    rw [List.map_map]
    exact actualNames
  have width : book.result.length=c.edges := by rw [keyTape,List.length_ofFn]
  have loaded : ∀ x∈D.rows,(buildOwner c.edges b book.result lines table (name x.1)).result=
      some (eraseCode x.2) := by
    intro x hx
    change x∈(vertexList c.host).map (fun v=>(v,(rows v).code)) at hx
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
    exact real_source_command_is_bought hb book.result keyAt keyInj keyTape lines table _ (validation v)
  have form : HasResidentFormat D B := compiled_leaf_format edgeCount rows B opened
  obtain ⟨same,bill⟩ := online_leaf_replays_raw hf F pos B D b book width lines table name loaded form
  rw [← names] at same bill
  have run := raw_leaf_is_same_dispatch (compiledLeaf edgeCount rows) hf F pos B
  have value := compiled_leaf_in_literal_order edgeCount rows B opened
  exact ⟨(runTape D hf F pos B).result,same,
    (congrArg F.decode (congrArg Meter.result run)).trans value,bill⟩

#print axioms real_source_command_is_bought
#print axioms checked_online_leaf_from_rows
end J6R50Leaf
