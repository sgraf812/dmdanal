import Order

abbrev Map (α β : Type) := α → Option β

namespace Map

def empty : Map α β := fun k => none

def update [DecidableEq α] (m : Map α β) (k : α) (v : Option β) : Map α β :=
  fun k' => if k = k' then v else m k'

macro:max m:term noWs "[" k:term " ↦ " v:term "]" : term => `(update $m $k $v)

end Map

def Con := Int

inductive Card where
  | C_00 | C_01 | C_0N
  | C_10 | C_11 | C_1N

structure Demand where
  (n : Card) (sd : SubDemand)

inductive SubDemand where
  | Poly (n : Card) : SubDemand
  | Ap (n : Card) (sd : SubDemand) : SubDemand
  | Sel (alts : Map Con (List Demand)) : SubDemand


