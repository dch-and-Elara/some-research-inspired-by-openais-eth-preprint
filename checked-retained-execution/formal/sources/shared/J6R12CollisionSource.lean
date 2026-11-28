import J6R12CollisionMenu
import J6R12CollisionRun

/-!
# Source label selection without a supplied menu or score literals

The program writes the four constants 0,1,B,B^2 on binary tapes
using one hot bit (B=2^b), and generates all B candidates once.
It then runs the verified graph labeler. Fields of the input graph
and the vertex ordering are fixed-width supplied tapes, not uncharged
computed functions. Sorting/packet embedding is a subsequent phase.
-/

namespace J6R12CollisionSource
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionGraphScore
open J6R12CollisionGreedyStep J6R12CollisionRun J6R12CollisionMenu
open J6R12CollisionAccumulator J6R11Collision J6R11CollisionGreedy

/-- With an in-range offset this writes one bit at the prescribed
static tape position, all other positions being zero. -/
def hot (w i : ℕ) : List Bool :=
  List.replicate i false ++ (true :: List.replicate (w-i-1) false)

private theorem value_append (xs ys : List Bool) :
    bitsValue (xs++ys)=bitsValue xs+2^xs.length*bitsValue ys := by
  induction xs with
  | nil => simp [bitsValue]
  | cons x xs ih =>
    simp only [List.cons_append,bitsValue,List.length_cons,pow_succ,ih]
    ring

theorem hot_exact (w i : ℕ) (hi : i<w) :
    (hot w i).length=w ∧ bitsValue (hot w i)=2^i := by
  constructor
  · simp only [hot,List.length_append,List.length_replicate,List.length_cons]
    omega
  · simp only [hot,value_append,zero_value,List.length_replicate,bitsValue,
      Bool.toNat_true,mul_zero,add_zero,mul_one,zero_add]

def literalSeed (w b : ℕ) : Meter Literals :=
  ⟨⟨List.replicate w false,hot w 0,hot w b,hot w (2*b)⟩,12*w+12⟩

theorem literalSeed_exact (w b : ℕ) (h : 2*b<w) :
    (literalSeed w b).result=makeLiterals w (2^b) := by
  have eh (i : ℕ) (hi : i<w) : hot w i=encodeBits w (2^i) := by
    obtain ⟨hv,he⟩ := hot_exact w i hi
    have hf : (2:ℕ)^i<2^w := by
      rw [← hv,← he]
      exact bitsValue_lt _
    exact equal_width_inj (hv.trans (encodeBits_length _ _).symm)
      (he.trans (encodeBits_exact _ _ hf).symm)
  have h₁ : hot w 0=encodeBits w 1 := by simpa using eh 0 (by omega)
  have hB : hot w b=encodeBits w (2^b) := eh b (by omega)
  have hD : hot w (2*b)=encodeBits w ((2^b)^2) := by
    rw [Nat.mul_comm 2 b,← pow_mul]
    exact eh (b*2) (by omega)
  have h0 : List.replicate w false=encodeBits w 0 := by
    apply equal_width_inj
    · rw [List.length_replicate,encodeBits_length]
    · rw [zero_value,encodeBits_exact _ _ (by positivity : 0<(2:ℕ)^w)]
  simp [literalSeed,makeLiterals,h0,h₁,hB,hD]

def drive (e kR kC b : ℕ) (vertices : List Target) (edges : List EdgeTape) :
    Meter (List EdgeTape × List (List Bool)) :=
  let w := scoreWidth e b
  let m := menuMachine b
  let L := literalSeed w b
  match m.result with
  | [] => ⟨(edges,[]),m.steps+L.steps+8⟩
  | first::rest =>
    let r := run w kR kC b L.result first rest vertices edges
    ⟨r.result,m.steps+L.steps+r.steps+8⟩

variable {E R C A : Type*} [Fintype E] [Fintype R] [Fintype C] [Fintype A] [Nonempty A]

theorem drive_exact (F : Format E R C A) (hB : Fintype.card A=2^F.b)
    (vs : List (R⊕C)) (hvs : vs.Nodup) (hVertices : ∀ i : R⊕C, i ∈ vs)
    (Δ : ℕ) (hr : ∀ v, (fibre F.row v).card≤Δ) (hc : ∀ v, (fibre F.col v).card≤Δ) :
    let out := drive F.e F.kR F.kC F.b (vs.map F.target) (F.graph (fun _ => none))
    ∃ z : R⊕C→A,
      out.result.1=F.graph (fun i => some (z i)) ∧
      out.result.2=vs.map (fun i => F.label (z i)) ∧
      J1MainSourceCollision.deviation (edgeCell F.row F.col (splitSample z))≤
        2*(Fintype.card E:ℚ)*Δ ∧
      out.steps≤(F.stepBound (Fintype.card A)+2*F.b+6)*(Fintype.card R+Fintype.card C) +
        16*(F.b+1)*Fintype.card A+12*F.width+20 := by
  obtain ⟨first,rest,hm,hd,hAll,hMc⟩ := full_alphabet F hB
  have hl : (literalSeed F.width F.b).result=F.literals := by
    rw [Format.literals,hB]
    exact literalSeed_exact _ _ (by unfold Format.width scoreWidth; omega)
  obtain ⟨z,hg,hout,hvar,hCost⟩ := complete_greedy F first rest vs hvs hVertices hd hAll Δ hr hc
  let r := run F.width F.kR F.kC F.b F.literals (F.label first) (rest.map F.label)
    (vs.map F.target) (F.graph (fun _ => none))
  change r.steps≤_ at hCost
  dsimp only [drive]
  rw [hm,show scoreWidth F.e F.b=F.width from rfl,hl]
  refine ⟨z,hg,hout,hvar,?_⟩
  change (menuMachine F.b).steps+(12*F.width+12)+r.steps+8≤_
  omega

omit [Fintype A] [Nonempty A] in
theorem source_64 {G : Type*} [Fintype G] [Nonempty G] (a : ℕ) (hG : Fintype.card G=64)
    (F : Format E R C (Fin a→G)) (hb : F.b=6*a)
    (vs : List (R⊕C)) (hvs : vs.Nodup) (hVertices : ∀ i : R⊕C, i ∈ vs)
    (Δ : ℕ) (hr : ∀ v, (fibre F.row v).card≤Δ) (hc : ∀ v, (fibre F.col v).card≤Δ) :
    let out := drive F.e F.kR F.kC F.b (vs.map F.target) (F.graph (fun _ => none))
    ∃ z : R⊕C→Fin a→G,
      out.result.1=F.graph (fun i => some (z i)) ∧
      out.result.2=vs.map (fun i => F.label (z i)) ∧
      J1MainSourceCollision.deviation (edgeCell F.row F.col (splitSample z))≤
        2*(Fintype.card E:ℚ)*Δ ∧
      out.steps≤(F.stepBound (2^(6*a))+2*F.b+6)*(Fintype.card R+Fintype.card C) +
        16*(F.b+1)*2^(6*a)+12*F.width+20 := by
  have he : Fintype.card (Fin a→G)=2^(6*a) := source_alphabet hG a
  have he' : Fintype.card (Fin a→G)=2^F.b := by rw [hb,he]
  simpa only [he] using drive_exact F he' vs hvs hVertices Δ hr hc

/-- The source packing slot hypothesis prevents B label candidates
from being exponential in the already explicit edge count. -/
theorem source_menu_size (a M : ℕ) (hslots : 2^a*(2^(6*a))^2≤M) :
    2^(6*a)≤M := by
  have h : 1≤(2:ℕ)^a := Nat.succ_le_of_lt (by positivity)
  calc
    _ ≤ ((2:ℕ)^(6*a))^2 := by rw [pow_two]; exact Nat.le_mul_self _
    _ ≤ _ := by simpa only [one_mul] using Nat.mul_le_mul_right (((2:ℕ)^(6*a))^2) h
    _ ≤ M := hslots

#print axioms hot_exact
#print axioms literalSeed_exact
#print axioms drive_exact
#print axioms source_64
#print axioms source_menu_size

end J6R12CollisionSource
