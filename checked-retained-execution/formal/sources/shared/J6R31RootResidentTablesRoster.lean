
import J6R30GeneratedRootLayoutReceipt
import J6R27OriginalGateCapsuleJoin
import J6R17ModeTapeBuild

/-! The stable root uses the complete paid ordered-cell header menu of
R24/R30. Its R17 roster needs only these headers, the copy count and the
legal receiver precision; this scratch header-only stream is *not* the
resident physical seat table, which is generated independently. -/
namespace J6R31RootResidentTables
open scoped Classical
open AOracleMachineTime AOracleMachineTimeLocal AOracleMachineTimeTape
open J6R14LayoutCost J6R24LegalLayout J6R30GeneratedRootLayout
open J6R15ModeCost J6R17ModeTape J6Mesh P11FullPacking J6R12CollisionEdges
set_option maxRecDepth 1900
set_option maxHeartbeats 11500000

def oneHeader (a : ℕ) (k : CellWord) : Meter ExportBox :=
  let h := prepareHeader a k
  ⟨⟨k,h.result.1,h.result.2,[]⟩,h.steps+12⟩

def headerBox {a : ℕ} (c : CellType a) : ExportBox :=
  ⟨wordCell c,axesOf c,marksOf c,[]⟩

theorem header_constructor_exact {a : ℕ} (c : CellType a) :
    (oneHeader a (wordCell c)).result=headerBox c ∧
      (oneHeader a (wordCell c)).steps≤headerCap a+12 := by
  obtain ⟨e,b⟩ := prepareHeader_exact c
  exact ⟨by simp only [oneHeader,e,headerBox],Nat.add_le_add_right b _⟩

def makeHeaders (a : ℕ) : Meter (List ExportBox) :=
  let z := allPairsMachine (6*a)
  let H := mapMeter (oneHeader a) z.result
  ⟨H.result,z.steps+H.steps+4⟩

def headerBankFee (a : ℕ) :=
  allPairsCap (6*a)+(headerCap a+18)*(2^(6*a)*2^(6*a))+4

theorem header_bank_exact (a : ℕ) :
    let z := makeHeaders a
    z.result=(typedCells a).map headerBox ∧
      z.steps≤headerBankFee a := by
  obtain ⟨k,b⟩ := allPairsMachine_exact (6*a)
  have cases : (allPairsMachine (6*a)).result=(typedCells a).map wordCell :=
    k.trans (typed_cells_exact a).2.2.symm
  have formAt (cs : List (CellType a)) :
      (mapMeter (oneHeader a) (cs.map wordCell)).result=cs.map headerBox ∧
      (mapMeter (oneHeader a) (cs.map wordCell)).steps≤(headerCap a+18)*cs.length := by
    induction cs with
    | nil => simp [mapMeter]
    | cons c cs ih =>
      obtain ⟨eq,ca⟩ := header_constructor_exact c
      obtain ⟨r,u⟩ := ih
      constructor
      · simp only [List.map_cons,mapMeter,eq,r]
      · change (oneHeader a (wordCell c)).steps+
          (mapMeter (oneHeader a) (cs.map wordCell)).steps+6≤(headerCap a+18)*(cs.length+1)
        rw [Nat.mul_add,Nat.mul_one]
        omega
  have form := formAt (typedCells a)
  have hLen : (typedCells a).length=2^(6*a)*2^(6*a) := by
    have e := congrArg List.length (typed_cells_exact a).2.2
    rwa [List.length_map,allPairs_len] at e
  refine ⟨?_,?_⟩
  · change (mapMeter (oneHeader a) (allPairsMachine (6*a)).result).result=_
    rw [cases]
    exact form.1
  · change (allPairsMachine (6*a)).steps+(mapMeter (oneHeader a) (allPairsMachine (6*a)).result).steps+4≤_
    rw [cases]
    have f := form.2
    rw [hLen] at f
    unfold headerBankFee
    omega

theorem actual_header_fields (a : ℕ) :
    let z := (makeHeaders a).result
    z.map headerOf=(typedCells a).map encodeHeader ∧
      exportRows z=0 ∧ z.length=2^(6*a)*2^(6*a) := by
  have r := (header_bank_exact a).1
  rw [r]
  have H : (typedCells a).length=2^(6*a)*2^(6*a) := by
    have e := congrArg List.length (typed_cells_exact a).2.2
    rwa [List.length_map,allPairs_len] at e
  refine ⟨?_,?_,?_⟩
  · rw [List.map_map]
    rfl
  · unfold exportRows
    rw [List.flatMap_map]
    simp [headerBox]
  · rwa [List.length_map]

def rootRoster {q : ℕ} (hq : 0<q) (m center : ℕ) (copies precision : Word q) :
    Meter (RawTape q) :=
  let H := makeHeaders (a m)
  let X := buildTape hq (a m) center 0 H.result copies precision
  ⟨X.result,H.steps+X.steps+4⟩

def rosterFee (m q i p : ℕ) :=
  headerBankFee (a m)+buildCap (a m) q (D m) 0 0 (K m) (2^(i+1)) p+4

theorem root_ordered_roster_exact {q m p : ℕ} (hq : 0<q) (i : Fin (a m))
    (hi : i.val+1<q) (copies precision : Word q)
    (hCopies : copies.val=K m) (hPrecision : precision.val=p) (hp : 0<p) :
    let z := rootRoster hq m i.val copies precision
    ∃ ms : List (PacketMode i (K m) (2^(i.val+1)) p),
      ms.Nodup ∧ (∀ j,j∈ms) ∧ z.result.modes=ms.map (encodeMode i) ∧ z.result.modes.Nodup ∧
      z.result.weights.map Word.val=ms.map modeWeight ∧ z.result.precision.val=p ∧
      z.steps≤rosterFee m q i.val p := by
  let H := makeHeaders (a m)
  obtain ⟨E,R,D⟩ := actual_header_fields (a m)
  obtain ⟨M,nd,all,F,N,W,P,C⟩ := buildTape_exact hq i hi 0 H.result (typedCells (a m)) E
    (typed_cells_exact _).1 (typed_cells_exact _).2.1 copies precision hCopies hPrecision hp
  have Hfee := (header_bank_exact (a m)).2
  rw [D,R,printed_menu_identity m] at C
  refine ⟨M,nd,all,F,N,W,P,?_⟩
  change H.steps+(buildTape hq (a m) i.val 0 H.result copies precision).steps+4≤_
  change H.steps≤_ at Hfee
  unfold rosterFee
  omega

#print axioms header_constructor_exact
#print axioms header_bank_exact
#print axioms actual_header_fields
#print axioms root_ordered_roster_exact
end J6R31RootResidentTables
