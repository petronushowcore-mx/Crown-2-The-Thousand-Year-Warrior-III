import Std

namespace CrownC2

def Factors {H O : Type} (v : H → O) (q : H → Prop) : Prop :=
  ∃ f : O → Prop, ∀ h, q h ↔ f (v h)

theorem mixedFibre {H O : Type} (v : H → O) (q : H → Prop)
    (x y : H) (hv : v x = v y) (hx : q x) (hy : ¬ q y) :
    ¬ Factors v q := by
  rintro ⟨f, hf⟩
  have hh := (hf x).mp hx
  rw [hv] at hh
  exact hy ((hf y).mpr hh)

abbrev History := Fin 3 × Fin 3
def label (k : Fin 3) : Int := if k.val = 2 then -1 else Int.ofNat k.val
def good : History := (0, 0)
def cancel : History := (1, 2)
def persist (h : History) : Prop := label h.1 = 0 ∧ label h.2 = 0
def endpoint (_ : History) : Unit := ()
def total (h : History) : Int := label h.1 + label h.2
def ledger (_ : History) : Nat := 2

theorem seamControl : persist good ∧ ¬ persist cancel := by
  unfold persist good cancel label
  decide

theorem tDoesNotFactor : ¬ Factors endpoint persist :=
  mixedFibre endpoint persist good cancel rfl seamControl.1 seamControl.2

theorem cancelledTotalDoesNotFactor : ¬ Factors total persist :=
  mixedFibre total persist good cancel (by decide) seamControl.1 seamControl.2

theorem budgetDoesNotDecideSeams :
    ¬ Factors (fun h : History => (endpoint h, ledger h)) persist :=
  mixedFibre _ persist good cancel rfl seamControl.1 seamControl.2

def word (h : History) : Prop × Prop := (label h.1 = 0, label h.2 = 0)

theorem wordDoesDecide : Factors word persist := by
  exact ⟨fun w => w.1 ∧ w.2, fun _ => Iff.rfl⟩

-- One-event instance of Mirrors M11. none is eternal silence; some k is
-- exactly one event at tick k, followed by silence. Every history costs ≤ 1.
def observedPrefix (t : Nat) (h : Option Nat) : Option Nat :=
  match h with
  | none => none
  | some k => if k < t then some k else none

def completed (h : Option Nat) : Prop := h.isSome = true

theorem prefixControl (n : Nat) : observedPrefix n none = observedPrefix n (some n) := by
  simp [observedPrefix]

theorem noFinitePrefixDecides (n : Nat) : ¬ Factors (observedPrefix n) completed := by
  apply mixedFibre (observedPrefix n) completed (some n) none (prefixControl n).symm
  · simp [completed]
  · simp [completed]

theorem noCoarserSliceDecides {O : Type} (n : Nat) (v : Option Nat → O) :
    ¬ Factors (fun h => v (observedPrefix n h)) completed := by
  apply mixedFibre _ completed (some n) none
  · exact congrArg v (prefixControl n).symm
  · simp [completed]
  · simp [completed]

theorem fullEventRecordDecides : Factors (fun h : Option Nat => h) completed := by
  exact ⟨completed, fun _ => Iff.rfl⟩

theorem deterministicTailControl {H S U : Type} (state : H → S)
    (future : S → U) (q : U → Prop) :
    Factors state (fun h => q (future (state h))) := by
  exact ⟨fun s => q (future s), fun _ => Iff.rfl⟩

theorem pastBudget (a b capacity : Nat) (h : a + b ≤ capacity) :
    a ≤ capacity ∧ a + b ≤ capacity := by omega

-- Pairing-kernel collision. E and the maps must separately be shown to
-- represent the declared homology and period transport of a physical model.
theorem killedClassCollision {E : Type} (a r : E → Int) (z w : E)
    (az : a z = 0) (rz : r z = 0) (aw : a w ≠ 0) (rw : r w = 0) :
    ¬ Factors r (fun x => a x ≠ 0) := by
  apply mixedFibre r (fun x => a x ≠ 0) w z (rw.trans rz.symm) aw
  simpa [az]

end CrownC2
