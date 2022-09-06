import Mathlib.Init.Set
import Mathlib.Init.Algebra.Order
import Mathlib.Order.Basic

class SUP (α : Type u) where
    sup : α → α → α

infix:65 " ⊔ " => SUP.sup

class INF (α : Type u) where
  inf : α → α → α

infix:70 " ⊓ " => INF.inf

class Lattice (α : Type u) extends PartialOrder α, SUP α, INF α where
  sup_ub_left (a b : α) : a ≤ a ⊔ b
  sup_ub_right (a b : α) : b ≤ a ⊔ b
  sup_lub (a b c : α) : a ≤ c → b ≤ c → a ⊔ b ≤ c
  inf_lb_left (a b : α) : a ⊓ b ≤ a
  inf_lb_right (a b : α) : a ⊓ b ≤ b
  inf_glb (a b c : α) : a ≤ b → a ≤ c → a ≤ b ⊓ c

class TOP (α : Type u) where
  top : α

notation "⊤" => TOP.top

class BOT (α : Type u) where
  bot : α

notation "⊥" => BOT.bot

class CompleteLattice (α : Type u) extends Lattice α, TOP α, BOT α where
  le_top : ∀ (a : α), a ≤ ⊤
  bot_le : ∀ (a : α), ⊥ ≤ a
  supr : Set α → α
  infi : Set α → α
  supr_ub  : ∀ (s : Set α) (a : α), a ∈ s → a ≤ supr s
  supr_lub : ∀ (s : Set α) (a : α), (∀ (b : α), b ∈ s → b ≤ a) → supr s ≤ a
  infi_lb  : ∀ (s : Set α) (a : α), a ∈ s → infi s ≤ a
  infi_glb : ∀ (s : Set α) (a : α), (∀ (b : α), b ∈ s → a ≤ b) → a ≤ infi s

-- In Lean 3, we defined `monotone` using the strict implicit notation `{{ ... }}`.
-- Implicit lambdas in Lean 4 allow us to use the regular `{...}`
def monotone_pre [Preorder α] [Preorder β] (f : α → β) :=
  ∀ {a b}, a ≤ b → f a ≤ f b

def galoisConnection {α β} [PartialOrder α] [PartialOrder β]
  (l : α → β) (u : β → α) := ∀ a b,  l a ≤ b ↔ a ≤ u b  
