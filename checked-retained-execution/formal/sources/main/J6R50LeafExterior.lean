import J6R50LeafRead
import J6R49LeafExterior

/-! In the exterior generated case the actual incoming roster may have
its physical order, not List.univ order. A complete resident port list
suffices; the read refers to the same immutable exterior page. -/
namespace J6R50Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R11Repack J6R20Ancestor J6R32RootGeneratedRegistryInputs
open J6R14ZeroMode J6R27PrescribedProbe J6R34RootAtlas J6R31RootResidentTables
open J6R30GeneratedRootLayout J6R24MeteredRecursion J6R33StatefulArithmeticPage
open J6R32StatefulArithmetic J6R22Active J6R9PacketScopes J6R35RootOrigins J6R49Leaf J6R48Leaf
open J6ActiveRun J6R26StablePreparedRoot J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 27000000
set_option maxRecDepth 3000

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own w : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (pad : ℕ)
local notation "pg" => pageKeyWidth m+pad

theorem online_exterior_row_real_order {c : Call (PhysicalHost f ell)}
    (F : Frame f c.prec) (vertex : Vertex c) (ord : Fin c.edges≃c.host.Edge)
    (k : CanonicalPage m) (tr : Trace (stableBorn X k) (atVertex c vertex))
    (ports : List (PortAt (atVertex c vertex))) (complete : ∀ u,u∈ports)
    (b : ℕ) (keys : List (J6R15ModeCost.Word w)) (keyAt : Fin c.edges→J6R15ModeCost.Word w)
    (keyInj : Function.Injective keyAt) (trueKeys : keys=List.ofFn keyAt)
    (owner : J6R15ModeCost.Word own) (lines : List (ResidentPort own w))
    (table : OriginTable own w key prec pg) (site : PageOrigin key prec pg)
    (hasAt : (⟨owner,SourceHead.paged site⟩ : RefRow own (SourceHead w key prec pg))∈table)
    (single : ∀ (r : RefRow own (SourceHead w key prec pg)),
      r∈table→RefRow.address r=owner→RefRow.payload r=.paged site)
    (tag : site.header=⟨(X.seed pad).immutable.payload.stamp,
      some (widened pad (residentPageKey m k)).result⟩)
    (depth : site.clock.length=tr.depth)
    (actual : (lines.filter (fun r=>(cmpAddr owner r.address).result)).map RefRow.payload=
      ports.map (fun u=>⟨keyAt (ord.symm (edge u.val)),
        tr.literal (originSeed (rootChart T) (oddAxis m) X.group k) u⟩))
    (B : PageBank f ell key prec tw bw pg) (alive : IsLive (X.seed pad) B) :
    let out := buildOwner c.edges b keys lines table owner
    ∃ cmd, out.result=some cmd ∧
      (∀ bits : Fin c.edges→Bool,
        F.decode (cmd.read X.hf F X.positive B (List.ofFn bits)).result=
          (c.host.file vertex).read X.hf c.prec (assignment c.host.network (bits∘ord.symm) vertex)) ∧
      out.steps≤locateFee own table.length+
        pageBuildFee owner lines key prec pg tr.depth
        (ports.map (fun u=>J6R34ChildPath.sourceWireFee w (ord.symm (edge u.val)).val
          (tr.literal (originSeed (rootChart T) (oddAxis m) X.group k) u).length)).sum+9 := by
  let body := tr.literal (originSeed (rootChart T) (oddAxis m) X.group k)
  let j (u : PortAt (atVertex c vertex)) := ord.symm (edge u.val)
  let W : List WireRead := ports.map (fun u=>⟨body u,List.replicate (j u).val true⟩)
  let p := (widened pad (residentPageKey m k)).result
  let born := (X.seed pad).immutable.payload.stamp
  let read : ReadCmd key pg := .packet born.creator p tr.depth W
  obtain ⟨ownerAt,ownerFee⟩ := bought_owner_record c.edges b keys lines table owner
    (.paged site) hasAt single
  obtain ⟨emit,bill⟩ := paid_page_body (b:=b) keys keyAt keyInj trueKeys owner lines site
    born p tag ports body j actual
  dsimp only at emit bill ownerAt ownerFee ⊢
  rw [depth] at emit bill
  refine ⟨read,ownerAt.trans emit,?_,?_⟩
  · intro bits
    have e := (true_exterior_seed_entry X pad k B alive tr F ord bits ports complete W rfl).1
    exact e
  · dsimp only [body,j] at bill ⊢
    omega

#print axioms online_exterior_row_real_order
end
end J6R50Leaf
