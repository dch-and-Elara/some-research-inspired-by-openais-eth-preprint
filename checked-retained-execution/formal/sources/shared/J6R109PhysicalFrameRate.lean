import J6R109PhysicalFrame

namespace J6R109PhysicalFrame
open AOracleMachineTime AOracleMachineTimeTape A1R10
open J6R49RootIngress J6R51Ingress J6R50RootIngress J6R30GeneratedRootLayout
open J6R12CollisionEdges
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 15000000

theorem flat_length_affine {A : Type*} (R : List (List A)) (n : ℕ)
    (bounded : ∀ xs∈R,xs.length≤n) : R.flatten.length≤n*R.length := by
  induction R with
  | nil => simp
  | cons xs R ih =>
    have row := bounded xs List.mem_cons_self
    have tail := ih (fun ys hy=>bounded ys (List.mem_cons_of_mem _ hy))
    simp only [List.flatten_cons,List.length_append,List.length_cons,Nat.mul_succ]
    omega

def rosterRankRoof (r c d wires wide rows legs : ℕ) : ℕ :=
  tapeFee r rows+(rowRankRoof r c d wires wide legs+6)*rows+
      7+4*(rows+legs*rows)

theorem actual_rank_roster_uses_paid_searches {h d j r c : ℕ}
    (G : PortRoster h d j) (wide : ℕ) (widths : ∀ u∈G.wires,keyWidth u≤wide) :
    let T := rankRoster (r:=r) (c:=c) G
    T.result.length≤G.rows.flatten.length*G.rows.length ∧
      T.steps≤rosterRankRoof r c d G.wires.length wide G.rows.length G.rows.flatten.length := by
  let C := indexTape r G.rows.length
  let pairs := G.rows.zipWith Prod.mk C.result
  let L := G.rows.flatten.length
  let f := fun p : List (PortSeed h d j) × Word r=>rankRow (c:=c) G.wires p.2 p.1
  let A := mapMeter f pairs
  have count : pairs.length=G.rows.length := by
    dsimp only [pairs]
    rw [List.length_zipWith,show C.result.length=G.rows.length from (actual_bit_index_tape_cost _ _).1,
      min_self]
  have each (p : List (PortSeed h d j) × Word r) (hp : p∈pairs) :
      (f p).result.length≤L ∧
        (f p).steps≤rowRankRoof r c d G.wires.length wide L := by
    have here : p.1∈G.rows := zipper_left G.rows C.result p hp
    have len : p.1.length≤L := row_in_flatten_no_larger _ _ here
    have S := one_actual_row_rank_cost (c:=c) G.wires p.2 p.1 wide widths
    refine ⟨S.1.trans len,S.2.trans ?_⟩
    unfold rowRankRoof tapeFee
    gcongr
  have produced := mapMeter_exact f (fun p=>(f p).result)
    (rowRankRoof r c d G.wires.length wide L) pairs (fun p hp=>⟨rfl,(each p hp).2⟩)
  have rows := flat_length_affine A.result L (by
    rw [show A.result=pairs.map (fun p=>(f p).result) from produced.1]
    intro row mem
    obtain ⟨p,hp,same⟩ := List.mem_map.mp mem
    rw [←same]
    exact (each p hp).1)
  have size : A.result.length=G.rows.length := by
    rw [show A.result=pairs.map (fun p=>(f p).result) from produced.1,List.length_map,count]
  have cFee : C.steps≤tapeFee r G.rows.length := (actual_bit_index_tape_cost _ _).2
  have aFee : A.steps≤(rowRankRoof r c d G.wires.length wide L+6)*G.rows.length :=
    produced.2.trans_eq (congrArg (fun v=>(rowRankRoof r c d G.wires.length wide L+6)*v) count)
  have lim : A.result.flatten.length≤L*G.rows.length := by simpa only [size] using rows
  change A.result.flatten.length≤L*G.rows.length ∧ C.steps+A.steps+7+
    4*(G.rows.length+A.result.flatten.length)≤_
  refine ⟨lim,?_⟩
  unfold rosterRankRoof
  change _≤tapeFee r G.rows.length+(rowRankRoof r c d G.wires.length wide L+6)*G.rows.length+
    7+4*(G.rows.length+L*G.rows.length)
  omega

def halfSeekRoof (r c d seats : ℕ) : ℕ :=
  2+seats*(5*(c+1)+6)+seedFee r c d+7

theorem actual_pick_holds_the_ranked_seats {r c d : ℕ}
    (seats : List (RankedSeed r c d)) (keys : List (Word (c+1))) :
    (pickPorts seats keys).steps≤2+keys.length*halfSeekRoof r c d seats.length := by
  induction keys with
  | nil => simp [pickPorts]
  | cons k keys ih =>
    have fee := find_rank_fee k seats
    unfold pickPorts
    dsimp only
    cases F : (findRank k seats).result <;> cases G : (pickPorts seats keys).result <;>
      simp only [F,G,List.length_cons,Nat.succ_mul,seed_copy_exact,halfSeekRoof] at * <;>
      omega

def physicalFrameRoof (r c d wires wide rows legs : ℕ) : ℕ :=
  rosterRankRoof r c d wires wide rows legs+tapeFee (c+1) (2*wires)+
    (2+(2*wires)*halfSeekRoof r c d (legs*rows))+
    (tapeFee r rows+tapeFee c wires+8+rows*(7+4*r)+wires*(7+4*c))+12

theorem actual_physical_frame_has_explicit_polynomial_cost {h d j r c : ℕ}
    (G : PortRoster h d j) (wide : ℕ) (widths : ∀ u∈G.wires,keyWidth u≤wide) :
    (buildPhysicalFrame (r:=r) (c:=c) G).steps≤
      physicalFrameRoof r c d G.wires.length wide G.rows.length G.rows.flatten.length := by
  let R := rankRoster (r:=r) (c:=c) G
  let K := indexTape (c+1) (2*G.wires.length)
  let P := pickPorts R.result K.result
  let V := frameTargets r c G.rows.length G.wires.length
  have qr := actual_rank_roster_uses_paid_searches (r:=r) (c:=c) G wide widths
  have rLen : R.result.length≤G.rows.flatten.length*G.rows.length := qr.1
  have rFee : R.steps≤_ := qr.2
  have key := actual_bit_index_tape_cost (c+1) (2*G.wires.length)
  have kFee : K.steps≤_ := key.2
  have hits := actual_pick_holds_the_ranked_seats R.result K.result
  have pFee : P.steps≤2+(2*G.wires.length)*
      halfSeekRoof r c d (G.rows.flatten.length*G.rows.length) := by
    refine hits.trans ?_
    rw [show K.result.length=2*G.wires.length from key.1]
    unfold halfSeekRoof
    gcongr
  have vFee : V.steps≤tapeFee r G.rows.length+tapeFee c G.wires.length+8+
      G.rows.length*(7+4*r)+G.wires.length*(7+4*c) := by
    have c0 := (actual_bit_index_tape_cost r G.rows.length).2
    have c1 := (actual_bit_index_tape_cost c G.wires.length).2
    unfold V frameTargets
    dsimp only
    omega
  change R.steps+K.steps+P.steps+V.steps+12≤_
  unfold physicalFrameRoof
  omega

#print axioms actual_rank_roster_uses_paid_searches
#print axioms actual_pick_holds_the_ranked_seats
#print axioms actual_physical_frame_has_explicit_polynomial_cost
end J6R109PhysicalFrame
