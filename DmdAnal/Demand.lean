import DmdAnal.Order
import Init.Data.List
import Mathlib.Init.Function
import Mathlib.Init.Set
import Mathlib.Order.Basic

open Function

abbrev Map (α β : Type) := List (α × β)

namespace Map

def empty : Map α β := []

def update [DecidableEq α] (m : Map α β) (k : α) (v : Option β) : Map α β :=
  match v with
  | none   => List.filter (¬ ·.fst = k) m
  | some v => (k,v) :: m

def lookup [DecidableEq α] (m : Map α β) (k : α) : Option β := 
  List.lookup k m 

def dom (m : Map α β) := 
  List.map Prod.fst m

macro:max m:term noWs "[" k:term " ↦ " v:term "]" : term => `(update $m $k $v)

end Map

abbrev Con := Int

inductive Lb where
  | l0 
  | l1 
  deriving Repr

inductive Ub where
  | u0 
  | u1 
  | uN
  deriving Repr

inductive Card where
  | mk (l: Lb) (u: Ub)
  deriving Repr

namespace Card

def c00 : Card := ⟨Lb.l0, Ub.u0⟩ 
def c01 : Card := ⟨Lb.l0, Ub.u1⟩ 
def c0N : Card := ⟨Lb.l0, Ub.uN⟩ 
def c10 : Card := ⟨Lb.l1, Ub.u0⟩ 
def c11 : Card := ⟨Lb.l1, Ub.u1⟩ 
def c1N : Card := ⟨Lb.l1, Ub.uN⟩ 

end Card

open Card

mutual
  inductive Demand where
    | mk (n : Card) (sd : SubDemand)
    deriving Repr

  inductive SubDemand where
    | poly (n : Card) : SubDemand
    | ap (n : Card) (sd : SubDemand) : SubDemand
    | sel (alts : List (Con × (List Demand))) : SubDemand
    deriving Repr
end

#eval Demand.mk Card.c0N (SubDemand.poly Card.c0N)


/-
mutual
  inductive EquiD : Demand → Demand → Prop where
    | bot : EquiD ⟨c10, sd₁⟩ ⟨c10, sd₂⟩
    | abs : EquiD ⟨c00, sd₁⟩ ⟨c00, sd₂⟩
    | cong : EquiSD sd₁ sd₂ → EquiD ⟨n, sd₁⟩ ⟨n, sd₂⟩
  inductive EquiSD : SubDemand → SubDemand → Prop where
    | ap_bot : EquiSD (SubDemand.ap c10 sd₁) (SubDemand.ap c10 sd₂)
    | ap_abs : EquiSD (SubDemand.ap c00 sd₁) (SubDemand.ap c00 sd₂)
    | ap_poly : {n ∉ [c11,c1N]} → EquiSD (SubDemand.ap n (SubDemand.poly n)) (SubDemand.poly n)
    | sel : {n : Card} → (∀c ∈ Map.dom alts, ∀d ∈ Map.lookup c alts, d = Demand.mk n (SubDemand.poly n)) → EquiSD (SubDemand.sel alts) (SubDemand.poly n) 
    | cong_ap : EquiSD (SubDemand.ap n sd₁) (SubDemand.ap n sd₂) 
end    
-/

namespace Card

@[inline]
def concLb : Lb -> Set ℕ 
  | Lb.l0 => { n | n >= 0 }
  | Lb.l1 => { n | n >= 1 }

@[inline]
def concUb : Ub -> Set ℕ 
  | Ub.u0 => {0} 
  | Ub.u1 => {0,1}
  | Ub.uN => { n | true }

@[inline]
def conc : Card -> Set ℕ 
  | ⟨ l, u ⟩ => concLb l ∩ concUb u
  
@[inline]
def absLb (s : Set ℕ) : Lb := match infi s with
  | 0 => Lb.l0 
  | _ => Lb.l1
  
@[inline]
def absUb (s : Set ℕ) : Ub := match supr s with
  | 0 => Ub.u0
  | 1 => Ub.u1
  | _ => Ub.uN

@[inline]
def abs (s : Set ℕ) : Card := ⟨ absLb s, absUb s ⟩ 

def concLb_injective : Function.injective concLb
  | Lb.l0, Lb.l0 => by simp
  | Lb.l0, Lb.l1 => by delta concLb; simp; intro; show ¬ ({n | True} = {n | n >= 1}) by sorry  
  | Lb.l1, Lb.l0 => by delta concLb; simp
  | Lb.l1, Lb.l1 => by simp
  

--match (a₁, a₂) with
--  | (Lb.l0, Lb.l0) => by simp
--  | (Lb.l0, Lb.l1) => by contradiction
--  | (Lb.l1, Lb.l0) => by sorry
--  | (Lb.l1, Lb.l1) => by sorry
    
    
  
def concUb_injective : Function.injective concUb := by
  intros a₁ a₂ h
  simp
  
def conc_injective : Function.injective conc := by
  intros a₁ a₂ h
  


instance CompleteLattic Card :=
  {

  }

theorem galois_abs_conc : galoisConnection abs conc := by sorry

end Card
