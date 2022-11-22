import Mathlib.Order.Basic
import Mathlib.Init.Set
import Mathlib.Init.Function

open Function

class Lattice (α : Type u) extends PartialOrder α, Sup α, Inf α where
  sup_ub_left (a b : α) : a ≤ a ⊔ b
  sup_ub_right (a b : α) : b ≤ a ⊔ b
  sup_lub (a b c : α) : a ≤ c → b ≤ c → a ⊔ b ≤ c
  inf_lb_left (a b : α) : a ⊓ b ≤ a
  inf_lb_right (a b : α) : a ⊓ b ≤ b
  inf_glb (a b c : α) : a ≤ b → a ≤ c → a ≤ b ⊓ c

class Top (α : Type u) where
  top : α

notation "⊤" => Top.top

class Bot (α : Type u) where
  bot : α

notation "⊥" => Bot.bot

class CompleteLattice (α : Type u) extends Lattice α, Top α, Bot α where
  le_top : ∀ (a : α), a ≤ ⊤
  bot_le : ∀ (a : α), ⊥ ≤ a
  supr : Set α → α
  infi : Set α → α
  supr_ub  : ∀ (s : Set α) (a : α), a ∈ s → a ≤ supr s
  supr_lub : ∀ (s : Set α) (a : α), (∀ (b : α), b ∈ s → b ≤ a) → supr s ≤ a
  infi_lb  : ∀ (s : Set α) (a : α), a ∈ s → infi s ≤ a
  infi_glb : ∀ (s : Set α) (a : α), (∀ (b : α), b ∈ s → a ≤ b) → a ≤ infi s

def monotone_pre [Preorder α] [Preorder β] (f : α → β) :=
  ∀ {a b}, a ≤ b → f a ≤ f b

def monotone_latt [Lattice α] [Lattice β] (f : α → β) :=
  ∀ {a b}, f a ⊔ f b ≤ f (a ⊔ b)

theorem monotone_pre_latt [Lattice α] [Lattice β] (f : α → β) (h : monotone_pre f) : monotone_latt f :=
  fun {a b} => 
  have haab : f a ≤ f (a ⊔ b) := h (Lattice.sup_ub_left a b) 
  have habb : f b ≤ f (a ⊔ b) := h (Lattice.sup_ub_right a b) 
  show f a ⊔ f b ≤ f (a ⊔ b) from Lattice.sup_lub (f a) (f b) (f (a ⊔ b)) haab habb

theorem monotone_pre_latt3 [Lattice α] [Lattice β] (f : α → β) (h : monotone_pre f) : monotone_latt f := by 
  intro a b
  repeat (any_goals (first | apply Lattice.sup_lub | apply h | apply Lattice.sup_ub_left | apply Lattice.sup_ub_right))

def galoisConnection {α β} [PartialOrder α] [PartialOrder β]
  (l : α → β) (u : β → α) := ∀ a b,  l a ≤ b ↔ a ≤ u b  

/- 
Interesting features:
  - calc
  - by assumption, ‹a ≤ b› 
  - any_goals, first
  - split
  - other tactics?
-/

#check {1,2} ⊆  ({1,2,3} : Set ℕ)

instance {α : Type u} : CompleteLattice (Set α) :=
{ le := (· ⊆ ·) 
  sup := (· ∪ ·)
  inf := (· ∩ ·)
  top := Set.univ
  bot := {}
  supr := fun ss x => ∃s ∈ ss, s x   
  infi := fun ss x => ∀s ∈ ss, s x   
  le_refl := fun a b x => x
  le_trans := fun a b c s1 s2 x p => s2 (s1 p)
  lt_iff_le_not_le := by sorry
  le_antisymm := by sorry
  sup_lub := by sorry
  sup_ub_left := by sorry
  sup_ub_right := by sorry
  inf_glb := by sorry
  inf_lb_left := by sorry
  inf_lb_right := by sorry
  le_top := by sorry
  bot_le := by sorry
  supr_ub := by sorry
  supr_lub := by sorry
  infi_glb := by sorry
  infi_lb := by sorry
  }


