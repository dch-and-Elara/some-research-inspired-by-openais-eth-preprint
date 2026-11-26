import SolverSchedule
import SolverPacketWords
import SolverBaseCount

noncomputable section
namespace RootSeparation.Solver

open S11 Execution Classical
open scoped BigOperators

private def checkedStep {R I : Type*} [CommSemiring R] [DecidableEq I] {p : ℕ}
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → Option R)
    (slot : Slot) : Option (BatchState I p) → Option (BatchState I p)
  | none => none
  | some st =>
    if h : ∀ g, (child slot g).isSome then
      some (stepTuple codec track (fun _ g => (child slot g).get (h g)) st slot)
    else none

/-- Same streaming tuple fold and bit-accumulator transition as Wegener.
    A child failure is propagated before using the accumulator at that slot. -/
def checkedBatch {R I : Type*} [CommSemiring R] [DecidableEq I] (p : ℕ)
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → Option R)
    (weights : List ℕ) (t : ℤ) (j : ℕ) : Option (BatchState I p) :=
  foldTuples weights p (fun state β => checkedStep codec track child ⟨t,j,β⟩ state) (some ⟨0,[]⟩)

theorem checkedBatch_success {R I : Type*} [CommSemiring R] [DecidableEq I] (p : ℕ)
    (codec : R ≃+ Coords I p) (track : I) (child : Slot → Fin 64 → Option R)
    (ret : Slot → Fin 64 → R) (weights : List ℕ) (t : ℤ) (j : ℕ)
    (h : ∀ β ∈ tuples weights p, ∀ g, child ⟨t,j,β⟩ g = some (ret ⟨t,j,β⟩ g)) :
    checkedBatch p codec track child weights t j = some (executeBatch p codec track ret weights t j) := by
  have fold (xs : List (List ℕ)) (st : BatchState I p)
      (hh : ∀ β ∈ xs, ∀ g, child ⟨t,j,β⟩ g = some (ret ⟨t,j,β⟩ g)) :
      xs.foldl (fun a β => checkedStep codec track child ⟨t,j,β⟩ a) (some st) =
        some (xs.foldl (fun a β => stepTuple codec track ret a ⟨t,j,β⟩) st) := by
    induction xs generalizing st with
    | nil => rfl
    | cons β bs ih =>
      have ha (g) := hh β (List.mem_cons_self ..) g
      have hvalid : ∀ g, (child ⟨t,j,β⟩ g).isSome := by intro g; rw [ha]; rfl
      have hop (g : Fin 64) : (child ⟨t,j,β⟩ g).get (hvalid g) = ret ⟨t,j,β⟩ g :=
        Option.get_of_eq_some (hvalid g) (ha g)
      have hx :
          stepTuple codec track (fun _ g => (child ⟨t,j,β⟩ g).get (hvalid g)) st ⟨t,j,β⟩ =
            stepTuple codec track ret st ⟨t,j,β⟩ := by
        unfold stepTuple groupProduct
        simp only [hop]
      simp only [List.foldl_cons, checkedStep, dif_pos hvalid, hx]
      apply ih
      exact fun b hb => hh b (List.mem_cons_of_mem _ hb)
  rw [checkedBatch,executeBatch,foldTuples_eq,foldTuples_eq]
  exact fold _ _ h

theorem checkedBatch_project {R I : Type*} [CommSemiring R] [DecidableEq I]
    (p : ℕ) (hp : 0 < p) (codec : R ≃+ Coords I p) (track : I)
    (child : Slot → Fin 64 → Option R) (weights : List ℕ) (t : ℤ) (j : ℕ)
    (st : BatchState I p) (h : checkedBatch p codec track child weights t j = some st) :
    rootProjection st.trace = (tuples weights p).map (Slot.mk t j) := by
  let next := fun a β => checkedStep codec track child ⟨t,j,β⟩ a
  have empty (xs : List (List ℕ)) : xs.foldl next none = none := by
    induction xs with
    | nil => rfl
    | cons x xs ih => exact ih
  have fold (xs : List (List ℕ)) (a b : BatchState I p) (hhh : xs.foldl next (some a) = some b) :
      rootProjection b.trace = rootProjection a.trace ++ xs.map (Slot.mk t j) := by
    induction xs generalizing a with
    | nil =>
      injection hhh with he
      rw [he]
      simp
    | cons β bs ih =>
      let slot : Slot := ⟨t,j,β⟩
      by_cases he : ∀ g, (child slot g).isSome
      · have eq : next (some a) β =
            some (stepTuple codec track (fun _ g => (child slot g).get (he g)) a slot) := by
          unfold next checkedStep
          exact dif_pos he
        rw [List.foldl_cons, eq] at hhh
        rw [ih _ hhh, stepTuple_project _ _ _ _ _ hp]
        simp [slot]
      · have eq : next (some a) β = none := by
          unfold next checkedStep
          exact dif_neg he
        rw [List.foldl_cons,eq,empty] at hhh
        cases hhh
  rw [checkedBatch,foldTuples_eq] at h
  simpa [BatchState.trace,rootProjection,executedDigits] using fold _ _ _ h

structure NativeState {e s : ℕ} (F : SourcePolynomial e) where
  call : Call F.f
  load : 8^call.depth * call.edges ≤ 3*s
  degrees : degreeBound s call

variable {s : ℕ}
variable (F : SourcePolynomial (4*lambda s))

abbrev CallReturned (c : Call F.f) :=
  (t : callCenters s c) → callProbes s c → WordRing F.f (callPrecision s c t.val)

/-- Exact source Lagrange/Hermite operation, followed by p-word reduction
    in the actual odd-localized coefficient algebra. -/
def recoverCall (c : Call F.f)
    (cap : probeCount c.edges (callL s c) ≤ 2^(4*lambda s))
    (samples : CallReturned F c) : Option (WordRing F.f c.precision) := by
  let embed : IntegerRing F.f →+* RationalCoefficients F := integerRational F.f
  let read := readout (K := RationalCoefficients F) (fun t : callCenters s c => S7.scaledCenter (callA s c) t.val)
    (fun t => multiplicity c.edges (callU s c) t.val)
    (fun _ (j : callProbes s c) => callPoint F cap j)
  exact tryWord F.monic c.precision (read (fun t j =>
    embed (liftCanonical F.monic F.degree (callPrecision_pos s c t.val) (samples t j))))

def childState (state : NativeState (s := s) F) (G : CallLayout s state.call)
    (cap : probeCount state.call.edges (callL s state.call) ≤ 2^(4*lambda s))
    (hpack : 2*callL s state.call ≤ degreeEnvelope s)
    (t : callCenters s state.call) (j : callProbes s state.call) (β : List ℕ) (g : Fin 64) :
    NativeState (s := s) F := by
  let tables := nativeTables F G cap
  refine ⟨childCall F.monic F.degree G tables t j β g,?_,
    childCall_degrees s state.call F.monic F.degree G tables state.degrees hpack t j β g⟩
  change 8^(state.call.depth+1) * (childCall F.monic F.degree G tables t j β g).edges ≤ 3*s
  have h := childNetwork_shrink state.call.network G.left G.right (G.coord t) g
    (RingHom.id _) G.packing G.cells (degreeEnvelope s : ℚ) G.legal
    (fun k bits => liftCanonical F.monic F.degree (callPrecision_pos s state.call t.val) (tables t j β g k bits))
  change 8 * (childCall F.monic F.degree G tables t j β g).edges ≤ state.call.edges at h
  rw [pow_succ,Nat.mul_assoc]
  exact (Nat.mul_le_mul_left _ h).trans state.load

set_option maxHeartbeats 3000000 in
/-- Partial executable semantics of the frozen active recursion. The
    failure branch flags a nonintegral exact readout or a failed child.
    Strict descent uses the actual retained-port wire count. -/
def runNativeCall (hs : 2^40 ≤ lambda s) (track : Fin (4*lambda s))
    (state : NativeState (s := s) F) : Option (CallResult F.f state.call.precision) :=
  let c := state.call
  if active : leafThreshold s < c.edges then
    let cert := active_numeric s c.depth c.edges hs state.load active
    let G := selectCallLayout s c active state.degrees cert.2.2.1 cert.2.2.2.1
    let cap := cert.2.2.2.2.2
    let hpack := cert.2.2.2.2.1
    let eval : (t : callCenters s c) → callProbes s c → Option (BatchState (Fin (4*lambda s))
        (callPrecision s c t.val)) := fun t j =>
      let pt := callPrecision s c t.val
      let codec := wordCoords F.monic F.degree pt (callPrecision_pos s c t.val)
      checkedBatch pt codec track (fun slot g =>
        (runNativeCall hs track (childState F state G cap hpack t j slot.exponents g)).map CallResult.value)
        (G.weights t.val) t.val j.val
    if h : ∀ t j, (eval t j).isSome then
      let states : ProbeStates (4*lambda s) s c := fun t j => (eval t j).get (h t j)
      let decode : CallReturned F c := fun t j =>
        (wordCoords F.monic F.degree (callPrecision s c t.val) (callPrecision_pos s c t.val)).symm
          (states t j).accumulator
      let trace := (callCenters s c).attach.toList.flatMap fun t =>
        (List.finRange (probeCount c.edges (callL s c))).flatMap fun j => (states t j).trace
      (recoverCall F c cap decode).map (fun value => ⟨value,trace⟩)
    else none
  else some ⟨leafValue c,[]⟩
termination_by state.call.edges
decreasing_by
  exact childCall_shrink F.monic F.degree _ _ _ _ _ _

theorem runNativeCall_leaf (hs : 2^40 ≤ lambda s) (track : Fin (4*lambda s))
    (state : NativeState (s := s) F) (hleaf : state.call.edges ≤ leafThreshold s) :
    runNativeCall F hs track state = some ⟨fromInteger F.f _ state.call.network.contract,[]⟩ := by
  rw [runNativeCall,dif_neg (not_lt_of_ge hleaf),leafValue_contract]

end RootSeparation.Solver

#print axioms RootSeparation.Solver.checkedBatch_success
#print axioms RootSeparation.Solver.checkedBatch_project
#print axioms RootSeparation.Solver.recoverCall
#print axioms RootSeparation.Solver.childState
#print axioms RootSeparation.Solver.runNativeCall
#print axioms RootSeparation.Solver.runNativeCall_leaf
