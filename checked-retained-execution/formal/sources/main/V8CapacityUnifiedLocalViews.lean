import V8CapacityUnifiedU7

/-! Capacity transport from sender/receiver semantic types to real
mixed cuts. No hand-selected values replace a physical view: the
other axis is changed only to the same-fiber representative. -/
namespace V8CapacityUnified.U7
open scoped Classical BigOperators

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000

variable {m : ℕ} (C : Cut m)

def rowAnchor (f : Fiber C) : Bits m :=
  fun i => if hi : i∈C.rowFixed then f.1 ⟨i,hi⟩ else false

def colAnchor (f : Fiber C) : Bits m :=
  fun i => if hi : i∈C.colFixed then f.2 ⟨i,hi⟩ else false

theorem rowAnchor_mem (f : Fiber C) : rowFiber C f (rowAnchor C f) := by
  funext i
  exact dif_pos i.property

theorem colAnchor_mem (f : Fiber C) : colFiber C f (colAnchor C f) := by
  funext i
  exact dif_pos i.property

variable {O K S R : Type*} [CommRing O] [Field K] [Algebra O K]

/-- Finite, one-way, fractional representative property on arbitrary
sender and receiver sets. No bounded intermediate degree or gate count
is posited by this interface. -/
def bipartite (π : O) (decode : S → R → K) (H : ℕ) : Prop :=
  ∀ {X Y : Type} [Fintype X] [Fintype Y] (s : X → S) (r : Y → R),
    ∃ A : Matrix X Y K, A.rank≤H ∧
      ∀ x y, ∃ e : O, decode (s x) (r y)-A x y=algebraMap O K (π*e)

theorem block_on_fiber (π : O) (D : S → R → K) (H : ℕ)
    (u : Bits m → Bits m → S) (v : Bits m → Bits m → R)
    (hs : senderLocal C u) (hr : receiverLocal C v)
    (hCap : bipartite π D H) (f : Fiber C) :
    ∃ A : Matrix {a // rowFiber C f a} {b // colFiber C f b} K,
      A.rank≤H ∧ ∀ a b, ∃ e : O,
        D (u a.val b.val) (v a.val b.val)-A a b=algebraMap O K (π*e) := by
  let a₀ := rowAnchor C f
  let b₀ := colAnchor C f
  have ha : rowFiber C f a₀ := rowAnchor_mem C f
  have hb : colFiber C f b₀ := colAnchor_mem C f
  have hView := fiber_views C hs hr f
  by_cases h : C.pb.card≤C.pa.card
  · rw [if_pos h] at hView
    let ad (a : {a // rowFiber C f a}) := u a.val b₀
    let bd (b : {b // colFiber C f b}) := v a₀ b.val
    obtain ⟨A,hA,hGood⟩ := hCap ad bd
    refine ⟨A,hA,fun a b => ?_⟩
    rw [hView.1 a.val b.val b₀ b.property hb,hView.2 a.val a₀ b.val a.property ha]
    exact hGood a b
  · rw [if_neg h] at hView
    let ad (b : {b // colFiber C f b}) := u a₀ b.val
    let bd (a : {a // rowFiber C f a}) := v a.val b₀
    obtain ⟨A,hA,hGood⟩ := hCap ad bd
    refine ⟨A.transpose,by simpa only [Matrix.rank_transpose] using hA,fun a b => ?_⟩
    rw [hView.1 a.val a₀ b.val a.property ha,hView.2 a.val b.val b₀ b.property hb]
    exact hGood b a

variable {B : Type*} [Fintype B] [IsDomain O] [IsLocalRing O] [IsFractionRing O K]

/-- Different blocks may use different message types and decoder types.
Each block retains its own overlap, direction and representative bound. -/
theorem U7_local_views (π : O) (hz : IsLocalRing.residue O π=0) (cuts : B → Cut m)
    (S R : B → Type*)
    (u : (b : B) → Bits m → Bits m → S b) (v : (b : B) → Bits m → Bits m → R b)
    (D : (b : B) → S b → R b → K) (H : B → ℕ)
    (hs : ∀ b, senderLocal (cuts b) (u b))
    (hr : ∀ b, receiverLocal (cuts b) (v b))
    (hCap : ∀ b, bipartite π (D b) (H b))
    (hCorrect : CorrectBlocks π (fun b x y => D b (u b x y) (v b x y))) :
    (1:ℚ)≤∑ b, min 1 ((2:ℚ)^(m-(cuts b).delta+(cuts b).hazard)*H b/2^m) :=
  U7_normalized π hz cuts (fun b x y => D b (u b x y) (v b x y)) H hCorrect
    (fun b f => block_on_fiber (cuts b) π (D b) (H b) (u b) (v b) (hs b) (hr b) (hCap b) f)

#print axioms rowAnchor_mem
#print axioms colAnchor_mem
#print axioms block_on_fiber
#print axioms U7_local_views
end
end V8CapacityUnified.U7
