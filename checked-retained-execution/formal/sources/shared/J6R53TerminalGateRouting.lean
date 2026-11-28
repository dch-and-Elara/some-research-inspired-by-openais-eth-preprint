import J6R53TerminalGateSuffix
import J6R50LeafGate
import J6R34ChildPathWires

/-! One retained owner: buy the suffix-to-live-wire table from this
owner's actual request list, then resolve the original ordered literal
names. Neither current wire names nor ordinals are caller input. -/
namespace J6R53TerminalGate
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R34ChildPath J6OrientedHost J6R50Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11000000
set_option Elab.async false

def suffixTable {W : ℕ} (w : ℕ) : List (WireRequest W) → Meter (List (RefRow w (Word W)))
  | [] => ⟨[],3⟩
  | wire::rest =>
    let key := suffix w wire.ancestry
    let name := copyFixed wire.incumbent
    let next := suffixTable w rest
    ⟨⟨key.result,name.result⟩::next.result,key.steps+name.steps+next.steps+7⟩

theorem suffix_table_exact {A : Type} {w W : ℕ} (ports : List A)
    (seed : A→Word w) (name : A→Word W) (headBits : A→List Bool) :
    suffixTable w (ports.map fun x=>⟨name x,headBits x++(seed x).bits⟩) =
      ⟨ports.map (fun x=>⟨seed x,name x⟩),
        3+(ports.map (fun x=>17+8*w+3*W+5*(headBits x).length)).sum⟩ := by
  induction ports with
  | nil => rfl
  | cons u us ih =>
    simp only [List.map_cons,List.sum_cons,suffixTable,suffix_exact,copy_fixed_exact,ih]
    congr 1
    omega

theorem locate_true_suffix {A : Type} {w W : ℕ} (ports : List A)
    (seed : A→Word w) (injective : Function.Injective seed) (name : A→Word W)
    (p : A) (present : p∈ports) :
    (locate (seed p) (ports.map fun x=>⟨seed x,name x⟩)).result=some (name p) := by
  apply locate_hit
  · exact List.mem_map_of_mem present
  · intro row h addr
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp h
    exact congrArg name (injective addr)

def rerouteGate {w W : ℕ} (bank : List (RefRow w (Word W))) :
    CodeGate (Word w) → Meter (Option (CodeGate (Word W)))
  | .free => ⟨some .free,2⟩
  | .equal ports =>
    let names := gatherOptions W (fun a=>locate a bank) ports
    ⟨names.result.map CodeGate.equal,names.steps+4⟩
  | .clause ports signs =>
    let names := gatherOptions W (fun a=>locate a bank) ports
    let ss := copyBytes signs
    ⟨names.result.map (fun ps=>.clause ps ss.result),names.steps+ss.steps+4⟩

theorem reroute_actual_gate {A : Type} {w W d : ℕ} (ports : List A)
    (seed : A→Word w) (injective : Function.Injective seed) (name : A→Word W)
    (scope : Fin d→A) (all : ∀ x,scope x∈ports) (G : Gate d) :
    let bank := ports.map (fun x=>⟨seed x,name x⟩)
    let R := rerouteGate bank (encodeGate (seed∘scope) G)
    R.result=some (encodeGate (name∘scope) G) ∧
      R.steps≤8+d*(locateFee w ports.length+W+9) := by
  let bank : List (RefRow w (Word W)) := ports.map (fun x=>⟨seed x,name x⟩)
  let line := (List.ofFn scope).map seed
  let dest := (List.ofFn scope).map name
  let named := gatherOptions W (fun a=>locate a bank) line
  have e (xs : List A) : gatherOptions W (fun a=>locate a bank) (xs.map seed)=
      gatherOptions W (fun x=>locate (seed x) bank) xs := by
    induction xs with
    | nil => rfl
    | cons a as ih => simp only [List.map_cons,gatherOptions,ih]
  have hNamed : named.result=some dest := by
    unfold named line
    rw [e,gather_options_exact W (fun x=>locate (seed x) bank) name (List.ofFn scope)]
    intro p h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact locate_true_suffix ports seed injective name _ (all i)
  have hFee : named.steps≤3+d*(locateFee w ports.length+W+6) := by
    have q := gather_options_bound W (locateFee w bank.length) (fun a=>locate a bank) line
      (fun a _=>locate_bound a bank)
    simpa only [bank,line,List.length_map,List.length_ofFn] using q
  have src : line=List.ofFn (seed∘scope) := List.map_ofFn scope seed
  have dst : dest=List.ofFn (name∘scope) := List.map_ofFn scope name
  have mul : d*(locateFee w ports.length+W+6)+3*d=d*(locateFee w ports.length+W+9) := by
    ring
  cases G with
  | free => exact ⟨rfl,by change 2≤8+_; omega⟩
  | equal =>
    constructor
    · change ((gatherOptions W (fun a=>locate a bank) (List.ofFn (seed∘scope))).result.map
        CodeGate.equal)=some (.equal (List.ofFn (name∘scope)))
      rw [← src,← dst]
      exact congrArg (Option.map CodeGate.equal) hNamed
    · change (gatherOptions W (fun a=>locate a bank) (List.ofFn (seed∘scope))).steps+4≤_
      rw [← src]
      change named.steps+4≤_
      omega
  | clause signs =>
    constructor
    · change ((gatherOptions W (fun a=>locate a bank) (List.ofFn (seed∘scope))).result.map
        (fun ps=>CodeGate.clause ps (copyBytes (List.ofFn signs)).result))=
        some (.clause (List.ofFn (name∘scope)) (List.ofFn signs))
      rw [← src,← dst,copyBytes_exact]
      exact congrArg (Option.map (fun ns=>CodeGate.clause ns (List.ofFn signs))) hNamed
    · change (gatherOptions W (fun a=>locate a bank) (List.ofFn (seed∘scope))).steps+
        (copyBytes (List.ofFn signs)).steps+4≤_
      rw [← src,copyBytes_exact]
      change named.steps+(3*(List.ofFn signs).length+1)+4≤_
      rw [List.length_ofFn]
      omega

#print axioms suffix_table_exact
#print axioms locate_true_suffix
#print axioms reroute_actual_gate
end J6R53TerminalGate
