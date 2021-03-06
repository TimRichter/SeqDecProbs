> module Trajectories

> import Data.So

> import Exists.Ops

> import DynamicProgramming.S1301_Context
> import DynamicProgramming.S1302_Viability
> import DynamicProgramming.S1302_Reachability
> import DynamicProgramming.S1303_OptimalPolicies
> import DynamicProgramming.S1302_Viability


> data StateCtrlSeq : (t : Nat) -> (n : Nat) -> Type where
>   Nil   :  (x : State t) -> StateCtrlSeq t Z
>   (::)  :  (x : State t ** Ctrl t x) -> StateCtrlSeq (S t) n -> StateCtrlSeq t (S n)

> stateCtrlTrj  :  (t : Nat) -> (n : Nat) ->
>                  (x : State t) -> (r : Reachable x) -> (v : Viable n x) ->
>                  (ps : PolicySeq t n) -> M (StateCtrlSeq t n)
> stateCtrlTrj _  Z      x  _  _  _            = Mret (Nil x)
> stateCtrlTrj t  (S n)  x  r  v  (p :: ps')   = Mmap prepend (toSub mx' `Mbind` f) where
>   y    : Ctrl t x;;         y    = outl (p x r v)
>   mx'  : M (State (S t));;  mx'  = step t x y
>   prepend : StateCtrlSeq (S t) n -> StateCtrlSeq t (S n)
>   prepend xys = (x ** y) :: xys
>   f : (x' : State (S t) ** So (x' `MisIn` mx')) -> M (StateCtrlSeq (S t) n)
>   f (x' ** x'inmx') = stateCtrlTrj (S t) n x' r' v' ps' where
>     r'  : Reachable x';;  r'  = reachableSpec1 x r y x' x'inmx'
>     v'  : Viable n x';;   v'  = Mspec2 mx' (viable n) (outr (p x r v)) x' x'inmx'

> {-
>   Mmap ((::) (x ** y)) (mx' `Mbind` f) where
>     y    :  Ctrl t x
>     y    =  outl (p x r v)
>     mx'  :  M (State (S t))
>     mx'  =  step t x y
>     f     :  State (S t) -> M (StateCtrlSeq (S t) n)
>     f x'  =  stateCtrlTrj (S t) n x' r' v' ps' where
>       postulate x'inmx' : So (x' `MisIn` mx')
>       r'  :  Reachable x'
>       r'  =  reachableSpec1 x r y x' x'inmx'
>       v'  :  Viable n x'
>       v'  =  MisInMareAllTrueSpec mx' (viable n) (getProof (p x r v)) x' x'inmx'
> -}
