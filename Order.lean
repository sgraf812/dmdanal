class HasMem (α : outParam $ Type u) (β : Type v) where
    mem : α → β → Prop

infix:50 " ∈ " => HasMem.mem

def Set (α : Type u) := α → Prop

namespace Set

variable {α : Type u}

instance : HasMem α (Set α) := ⟨λ a s => s a⟩

theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext $ λ x=> propext $ h x

namespace Set

class Preorder (α : Type u) extends LE α where
  le_refl  (a : α) : a ≤ a
  le_trans {a b c : α} : a ≤ b → b ≤ c → a ≤ c

class PartialOrder (α : Type u) extends LE α where
  le_antisym (a b : α) : a ≤ b → b ≤ a → a = b

class PartialOrder (α : Type u) extends LE α where
  le_antisym (a b : α) : a ≤ b → b ≤ a → a = b

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

instance {α : Type u} {β : α → Type v} [(a : α) → Preorder (β a)] : Preorder ((a : α) → β a) where
  le f g := ∀ a, f a ≤ g a
  le_refl f  := fun a => Preorder.le_refl (f a)
  le_trans   := fun h₁ h₂ a => Preorder.le_trans (h₁ a) (h₂ a)

instance {α : Type u} {β : α → Type v} [(a : α) → PartialOrder (β a)] : PartialOrder ((a : α) → β a) where
  le f g := ∀ a, f a ≤ g a
  le_antisym f g := fun h₁ h₂ => funext fun a => PartialOrder.le_antisym (f a) (g a) (h₁ a) (h₂ a)

-- In Lean 3, we defined `monotone` using the strict implicit notation `{{ ... }}`.
-- Implicit lambdas in Lean 4 allow us to use the regular `{...}`
def Monotone [Preorder α] [Preorder β] (f : α → β) :=
  ∀ {a b}, a ≤ b → f a ≤ f b

def galoisConnection {α β} [PartialOrder α] [PartialOrder β]
  (l : α → β) (u : β → α) := ∀ a b,  l a ≤ b ↔ a ≤ u b  
