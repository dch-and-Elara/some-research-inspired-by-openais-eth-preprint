import J6R58BootScopeReads
import J6R58BootScopeWriter
import J6R55BootBodiesFactory

/-! Price the actual input tables already resident after one common
boot prefix. Numeric/physical descriptor payloads are retained by
reference and are billed when their fields are executed, not copied
once again just to look up a descriptor. -/
namespace J6R58BootScope
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R27OriginalGate
open J6R51Peak J6R53OldOwner J6R49SourceLayout J6R55TerminalOrigin J6R48GeneratedAddons
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R50SourceProducer J6R41StructuredAllPaths J6R10Repack J6R34RootAtlas J6R36ChildFramedRoute
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 25000000
set_option maxRecDepth 5200
set_option Elab.async false
noncomputable section

def checkedBootHandle {X : Type} {T : X→Type} {w : ℕ}
    (rows : List (RefRow w (Sigma T))) (k : Word w) (x : X) (obj : T x)
    (hit : (locate k rows).result=some ⟨x,obj⟩) : Meter (T x) :=
  let asked := readBootReference rows k
  have exactResult : asked.result=some ⟨x,obj⟩ :=
    (metered_boot_reference_from_existing_register rows k).1.trans hit
  have has : asked.result.isSome := by rw [exactResult]; rfl
  let got := asked.result.get has
  have eq : got=⟨x,obj⟩ := Option.get_of_eq_some has exactResult
  ⟨cast (congrArg T (congrArg Sigma.fst eq)) got.snd,asked.steps⟩

theorem checked_boot_handle_retains_actual_source {X : Type} {T : X→Type} {w : ℕ}
    (rows : List (RefRow w (Sigma T))) (k : Word w) (x : X) (obj : T x)
    (hit : (locate k rows).result=some ⟨x,obj⟩) :
    (checkedBootHandle rows k x obj hit).result=obj ∧
      (checkedBootHandle rows k x obj hit).steps≤locateFee w rows.length+3*w+5 := by
  have e (z : Sigma T) (e : z=⟨x,obj⟩) :
      cast (congrArg T (congrArg Sigma.fst e)) z.snd=obj := by subst z; rfl
  refine ⟨?_,(metered_boot_reference_from_existing_register rows k).2⟩
  unfold checkedBootHandle
  dsimp only
  apply e
  exact Option.get_of_eq_some _ ((metered_boot_reference_from_existing_register rows k).1.trans hit)

section ports
variable {f : ℤ[X]} {ell s C key prec tw bw pg own : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {I : OccurrenceInput T v key prec tw bw pg}
variable {name : (v.parent.host.Row⊕v.parent.host.Col)→Word own}
variable (D : BootPortWords I name)
local notation "Port₀" => (Port v.parent.host.Edge)
local notation "B" => (compileOccurrence I)

structure ResidentBootQueries where
  raw : List (RefRow (B).port (Word own × Word D.seatWidth × Bool))
  exactRows : raw=(B).native.physical.order.map
    (fun h : Port₀=>⟨((B).native.physical.record h).address,(D.queries h).result⟩)

variable (F : ResidentBootQueries D)

theorem actual_boot_query_is_same_half_port (h : Port₀) :
    (locate ((B).native.physical.record h).address F.raw).result=some (D.queries h).result := by
  rw [F.exactRows]
  apply locate_hit
  · exact List.mem_map.mpr ⟨h,(B).native.physical.complete h,rfl⟩
  · intro row hm eq
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hm
    have e : k=h := (B).native.physical.distinct eq
    subst k
    rfl

def paidResidentBootPorts : BootPortWords I name where
  seatWidth := D.seatWidth
  seats := copyBootSeatRows D.seats.result
  queries h := readBootQueryRow F.raw ((B).native.physical.record h).address
  ownerQuery h :=
    (congrArg Prod.fst (actual_boot_query_row_and_width F.raw _ _ (actual_boot_query_is_same_half_port D F h)).1).trans
      (D.ownerQuery h)
  sideExact h :=
    (congrArg (fun a=>a.2.2) (actual_boot_query_row_and_width F.raw _ _ (actual_boot_query_is_same_half_port D F h)).1).trans
      (D.sideExact h)
  seatHit h := by
    have e := (actual_boot_query_row_and_width F.raw _ _ (actual_boot_query_is_same_half_port D F h)).1
    rw [e,copy_boot_seat_rows_exact]
    exact D.seatHit h
  seatUnique h x found addr := by
    have e := (actual_boot_query_row_and_width F.raw _ _ (actual_boot_query_is_same_half_port D F h)).1
    rw [e] at addr
    rw [copy_boot_seat_rows_exact] at found
    exact D.seatUnique h x found addr
  fallback := D.fallback

theorem paid_boot_seat_input_same_bytes :
    (paidResidentBootPorts D F).seats=⟨D.seats.result,
      3+(3*D.seatWidth+3*dim v+3*pg+48)*D.seats.result.length⟩ :=
  copy_boot_seat_rows_exact D.seats.result

theorem boot_query_tape_has_no_extra_catalogue_rows :
    F.raw.length=2*v.parent.edges := by
  rw [F.exactRows,List.length_map,boot_native_half_port_count]

theorem paid_boot_query_bill_from_actual_port_tape :
    bootAddressBill (paidResidentBootPorts D F) (B).native.physical.order≤
      (2*v.parent.edges)*(locateFee (B).port (2*v.parent.edges)+3*(B).port+3*own+3*D.seatWidth+9) := by
  have len := boot_query_tape_has_no_extra_catalogue_rows D F
  have cost (h : Port₀) : ((paidResidentBootPorts D F).queries h).steps≤
        locateFee (B).port (2*v.parent.edges)+3*(B).port+3*own+3*D.seatWidth+9 := by
    rw [←len]
    exact (actual_boot_query_row_and_width F.raw ((B).native.physical.record h).address
      (D.queries h).result (actual_boot_query_is_same_half_port D F h)).2
  unfold bootAddressBill
  have eq : (B).native.physical.order.length=2*v.parent.edges := boot_native_half_port_count I
  rw [←eq]
  exact uniform_sum_bound _ _ _ (fun h _=>by rw [eq]; exact cost h)

end ports
end
#print axioms checkedBootHandle
#print axioms checked_boot_handle_retains_actual_source
#print axioms actual_boot_query_is_same_half_port
#print axioms paidResidentBootPorts
#print axioms paid_boot_seat_input_same_bytes
#print axioms boot_query_tape_has_no_extra_catalogue_rows
#print axioms paid_boot_query_bill_from_actual_port_tape
end J6R58BootScope
