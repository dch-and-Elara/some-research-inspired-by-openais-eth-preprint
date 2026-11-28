import J6R12CollisionSource

/-! Kernel-reduced machine fixture with 3 edges, 4 vertices and 2 labels. -/
namespace J6R12CollisionSmoke
open AOracleMachineTime
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionGreedyStep
open J6R12CollisionSource J6R12CollisionGraphScore

def fixtureGraph : List EdgeTape :=
  [⟨⟨[false],none⟩,⟨[false],none⟩⟩, ⟨⟨[false],none⟩,⟨[true],none⟩⟩,
   ⟨⟨[true],none⟩,⟨[true],none⟩⟩]

def fixture := drive 2 1 1 1 [.row [false],.row [true],.col [false],.col [true]] fixtureGraph

theorem fixture_labels : fixture.result.2 = [[false],[true],[false],[true]] := by decide

theorem fixture_score :
    bitsValue (scoreGraph 7 1 1 1 (makeLiterals 7 2) fixture.result.1).result=12 := by decide

#print axioms fixture_labels
#print axioms fixture_score

end J6R12CollisionSmoke
