
import J6R21LeafOriginalGate
import J6R21LeafPhysical
import J6R11RepackRootHost

/-! The original Plant gates use their actual printed row and column
ports to compile into the serial bit reader; no arbitrary truth function
or precomputed original ring value is accepted. -/
namespace J6R21Leaf
open scoped BigOperators Polynomial Classical
open Polynomial AOracleMachineTime AOracleCoordinates A1R10 A1R11 A1R12
open J6ActiveRun J6R9Recursive J6R10Repack J6R11Blueprint J6R11Repack J6OrientedHost
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

structure IndexedGate (n : ℕ) where
  degree : ℕ
  port : Fin degree→Fin n
  gate : Gate degree

def IndexedGate.tape {n k : ℕ} (G : IndexedGate n) (fit : n≤2^k) : OriginalGateTape n k :=
  gateTape fit G.port G.gate

variable {S V : Type} [LinearOrder S]
variable {a b m q l n : ℕ}

def plantIndexedGate (T : Plant V m q) (w : Fin a→S)
    (slot : Wire w m b l→Fin n) : Left V w m b l⊕Right w m b l q→IndexedGate n
  | .inl (.inl (v,j)) =>
    ⟨T.degree v,fun i=>slot (rowPort T w (.inl (v,j)) i),T.old v⟩
  | .inl (.inr (pad,tag)) =>
    ⟨1,fun _=>slot (.inr (pad,tag)),if tag then Gate.free else Gate.clause (fun _=>false)⟩
  | .inr v =>
    ⟨2,fun i=>slot (colPort T w v (i.val==1)),Gate.equal⟩

theorem two_ports_truth (x : Bool→Bool) :
    (Gate.equal : Gate 2).eval (fun i=>x (i.val==1)) = decide (x false=x true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Gate.eval,decide_eq_true_eq]
  constructor
  · intro h
    exact h 0 1
  · intro h i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact h | exact h.symm

theorem plant_indexed_gate_actual (T : Plant V m q) (w : Fin a→S)
    (slot : Wire w m b l→Fin n) (x : Fin n→Bool)
    (v : Left V w m b l⊕Right w m b l q) :
    let G := plantIndexedGate T w slot v
    G.gate.eval (x∘G.port)=rootFlag T w (x∘slot) v := by
  rcases v with ((⟨s,j⟩|⟨pad,tag⟩)|v)
  · rfl
  · cases tag with
    | true => rfl
    | false =>
      change decide (∃ i : Fin 1,x (slot (.inr (pad,false)))=false) =
        !(x (slot (.inr (pad,false))))
      cases h : x (slot (.inr (pad,false))) <;> simp
  · exact two_ports_truth (fun bit=>x (slot (colPort T w v bit)))

def plantReader (T : Plant V m q) (w : Fin a→S)
    {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hℓ : 0<ell) (slot : Wire w m b l→Fin n)
    {k : ℕ} (fit : n≤2^k)
    (v : Left V w m b l⊕Right w m b l q) (bits : List Bool) : Meter (UVBlock fw ell) :=
  uvGate hp he hℓ ((plantIndexedGate T w slot v).tape fit) bits

theorem plant_reader_exact (T : Plant V m q) (w : Fin a→S)
    {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hℓ : 0<ell) (slot : Wire w m b l→Fin n)
    {k : ℕ} (fit : n≤2^k)
    (x : Fin n→Bool) (v : Left V w m b l⊕Right w m b l q) :
    let r := plantReader T w hp he hℓ slot fit v (List.ofFn x)
    uvRead hp fw ell r.result = (if rootFlag T w (x∘slot) v then 1 else 0) ∧
      r.steps≤originalGateFee n k (plantIndexedGate T w slot v).degree+uvWidth fw.length ell p+4 := by
  have K := uv_gate_exact hp he hℓ fit (plantIndexedGate T w slot v).port
    (plantIndexedGate T w slot v).gate x
  simpa only [plantReader,IndexedGate.tape,plant_indexed_gate_actual] using K

theorem plant_query_at_physical_root {f : ℤ[X]} [Fintype S] [Fintype V]
    (ell p m l q : ℕ) (T : Plant V m q) (w : Fin (J6Mesh.a m)→S)
    (hp : 0<p) {fw : List (A1R10.Word p)} (he : 0<fw.length) (hℓ : 0<ell)
    (hPoly : Modulus p hp fw=NativeProbeRing.liftPoly p f) (hf : f.Monic)
    (count : (physicalRootCall f ell p m l q T w).host.edgeCount=
      (physicalRootCall f ell p m l q T w).edges)
    (k : ℕ) (fit : (physicalRootCall f ell p m l q T w).edges≤2^k) :
    let c := physicalRootCall f ell p m l q T w
    let ord := c.host.edgeOrder c.edges count
    let read := plantReader T w hp he hℓ ord fit
    ∀ (x : Fin c.edges→Bool) (v : c.host.Row⊕c.host.Col),
      J6R18ChildWrite.castBox hPoly (uvRead hp fw ell (read v (List.ofFn x)).result)=
      (c.host.file v).read hf c.prec (assignment c.host.network (x∘ord) v) := by
  dsimp only
  intro x v
  rw [(plant_reader_exact T w hp he hℓ _ fit x v).1,← literalChart_is_cast]
  have h := root_gate_read f ell p T w hf (x∘(physicalRootCall f ell p m l q T w).host.edgeOrder _ count) v
  change _=reduce p f ell ((rootEntryFile f ell p T w v).frozen hf
    (assignment (rootNetwork T w) (x∘(physicalRootCall f ell p m l q T w).host.edgeOrder _ count) v))
  rw [h]
  split <;> simp only [map_one,map_zero]

#print axioms two_ports_truth
#print axioms plant_indexed_gate_actual
#print axioms plant_reader_exact
#print axioms plant_query_at_physical_root
end J6R21Leaf
