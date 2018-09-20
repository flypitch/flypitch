inductive term : Type
    | 

structure Language := 
    language :: (relations : Type) (functions : Type ) (arityF :  functions →  nat) (arityR : relations → nat)
variable L : Language