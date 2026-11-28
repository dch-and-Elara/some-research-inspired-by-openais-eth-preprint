import F5R62PhysicalEmit
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

/-! A model bijection for the emitted F1 CNF itself. This theorem
does not claim that the separate reduction from width-three SAT
preserves model counts. -/
namespace F5R62.PhysicalEmit
set_option autoImplicit false
set_option warningAsError true
open F5R60 F5R61

variable {V E T : Type}

abbrev AllowedModels (G : RequestGraph V E T) := {x : V → Bool // Allowed G x}
abbrev DetachedModels := {d : Bool × Bool // (d.1 || d.2)=true}

def privatePart (a : PhysicalVar V E T → Bool) : PrivatePos V E T → Bool := fun p => a (.inl p)
def detachedPart (a : PhysicalVar V E T → Bool) : Bool × Bool := (a (.inr false),a (.inr true))

def canonicalPrivate (G : RequestGraph V E T) (x : V → Bool) : PrivatePos V E T → Bool :=
  restrictBits G (logicalBits x (asY G x))

def readLogical {G : RequestGraph V E T} (D : PrintedCycles G)
    (b : PrivatePos V E T → Bool) : V → Bool :=
  fun v => b (D.first (.inl v))

theorem lifted_allowed_for_any_true_detached {G : RequestGraph V E T} (D : PrintedCycles G)
    (x : AllowedModels G) (d : DetachedModels) :
    PhysicalPrinted G D (canonicalPrivate G x.val) d.val := by
  let bits := logicalBits x.val (asY G x.val)
  let b := canonicalPrivate G x.val
  refine ⟨(actual_positions_reduce G x.val _).2
    ((printed_logical_iff G x.val _).2 ⟨x.property,fun _ => rfl⟩),?_,d.property⟩
  intro n
  have f : b (D.first n)=bits n := congrArg bits (D.firstName n)
  have l : b (D.last n)=bits n := congrArg bits (D.lastName n)
  refine ⟨lift_chain b (D.rest n) (D.chainOrder n) ?_,fun h => (f.trans l.symm).trans h⟩
  intro z hz
  rcases List.mem_cons.mp hz with equal | tail
  · exact congrArg b equal
  · exact (congrArg bits (D.restName n z tail)).trans f.symm

theorem recover_unique_private {G : RequestGraph V E T} (D : PrintedCycles G)
    (b : PrivatePos V E T → Bool) (d : Bool × Bool)
    (h : PhysicalPrinted G D b d) :
    Allowed G (readLogical D b) ∧ b = canonicalPrivate G (readLogical D b) := by
  let x := readLogical D b
  let y : T → Bool := fun t => b (D.first (.inr t))
  have eq : b=restrictBits G (logicalBits x y) := printed_cycle_copyback G D b h.2.1
  have base : BasePositions G (restrictBits G (logicalBits x y)) := eq ▸ h.1
  have core := (printed_logical_iff G x y).1 ((actual_positions_reduce G x y).1 base)
  exact ⟨core.1,eq.trans (congrArg (fun y' => restrictBits G (logicalBits x y')) (funext core.2))⟩

theorem read_canonical_private {G : RequestGraph V E T} (D : PrintedCycles G) (x : V → Bool) :
    readLogical D (canonicalPrivate G x)=x := by
  funext v
  change logicalBits x (asY G x) (nameOf G (D.first (.inl v)))=x v
  rw [D.firstName]
  rfl

def detachedModelEquiv : DetachedModels ≃ Fin 3 where
  toFun d := match d.val with
    | (false,_) => 0
    | (true,false) => 1
    | (true,true) => 2
  invFun i := if i.val=0 then ⟨(false,true),rfl⟩ else
    if i.val=1 then ⟨(true,false),rfl⟩ else ⟨(true,true),rfl⟩
  left_inv d := by
    rcases d with ⟨⟨x,y⟩,h⟩
    cases x <;> cases y
    · contradiction
    all_goals rfl
  right_inv i := by
    fin_cases i <;> rfl

variable [DecidableEq V] [DecidableEq T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

abbrev EmittedModels :=
  {a : PhysicalVar V E T → Bool // CnfSat a (f1ActualCNF G v e t)}

private theorem emitted_models_split (a : EmittedModels G v e t) :
    PhysicalPrinted G (generatedPrintedCycles G v e t) (privatePart a.val) (detachedPart a.val) := by
  apply (actual_f1_cnf_assignment_exact G v e t _ _).1
  change CnfSat
    (assignment (fun p : PrivatePos V E T => a.val (.inl p)) (a.val (.inr false),a.val (.inr true)))
    (f1ActualCNF G v e t)
  rw [reconstruct_assignment]
  exact a.property

def emittedModelsEquiv :
    EmittedModels G v e t ≃ (AllowedModels G × DetachedModels) where
  toFun a :=
    let b := privatePart a.val
    let d := detachedPart a.val
    let D := generatedPrintedCycles G v e t
    let h := emitted_models_split G v e t a
    ⟨⟨readLogical D b,(recover_unique_private D b d h).1⟩,⟨d,h.2.2⟩⟩
  invFun p :=
    ⟨assignment (canonicalPrivate G p.1.val) p.2.val,
      (actual_f1_cnf_assignment_exact G v e t _ _).2
        (lifted_allowed_for_any_true_detached (generatedPrintedCycles G v e t) p.1 p.2)⟩
  left_inv a := by
    apply Subtype.ext
    let D := generatedPrintedCycles G v e t
    let b := privatePart a.val
    let d := detachedPart a.val
    have h := emitted_models_split G v e t a
    have eq := (recover_unique_private D b d h).2
    change assignment (canonicalPrivate G (readLogical D b)) d=a.val
    rw [← eq]
    exact reconstruct_assignment a.val
  right_inv p := by
    rcases p with ⟨⟨x,hx⟩,⟨d,hd⟩⟩
    apply Prod.ext
    · apply Subtype.ext
      change readLogical (generatedPrintedCycles G v e t) (canonicalPrivate G x)=x
      exact read_canonical_private (generatedPrintedCycles G v e t) x
    · apply Subtype.ext
      cases d
      rfl

theorem exact_emitted_models_three_times_allowed :
    Nat.card (EmittedModels G v e t)=3*Nat.card (AllowedModels G) := by
  rw [Nat.card_congr (emittedModelsEquiv G v e t),Nat.card_prod,
    Nat.card_congr detachedModelEquiv,Nat.card_fin,Nat.mul_comm]

#print axioms lifted_allowed_for_any_true_detached
#print axioms recover_unique_private
#print axioms read_canonical_private
#print axioms detachedModelEquiv
#print axioms emittedModelsEquiv
#print axioms exact_emitted_models_three_times_allowed
end F5R62.PhysicalEmit
