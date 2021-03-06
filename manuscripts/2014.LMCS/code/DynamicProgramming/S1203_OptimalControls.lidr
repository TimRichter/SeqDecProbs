> module OptimalControls

> import Data.So

> import Double.Properties
> import Exists.Ops

> import DynamicProgramming.S1201_Context
> import DynamicProgramming.S1202_ReachabilityViability


> %default total

> %access public export


Sequences of feasible controls of length |n| starting in |x : State t| can
be represented by values of type

> data CtrlSeq : (x : State t) -> (n : Nat) -> Type where
>   Nil   :  CtrlSeq x Z
>   (::)  :  (yv : GoodCtrl t n x) -> CtrlSeq (step t x (outl yv)) n -> CtrlSeq x (S n)

For such sequences to exist, |x| is required to be viable (at least) |n|
steps. The first control of a sequence of length |S n| is required to
yield a state which is viable |n| steps. The existence of such a control
is granted by the first viability theorem |viability1|, see
S1202_reachabilityViability.lidr. Similarly for the second, third,
etc. control. The last control is required to yield a state which is
viable |0| steps. This holds, per definition, for every feasible control.

The sum of the rewards obtained in |n| steps when starting in |x| is

> val  :  (x : State t) -> (n : Nat) -> CtrlSeq x n -> Double
> val      _   Z      _           =  0
> val {t}  x   (S n)  (yv :: ys)  =  reward t x y x' + val x' n ys where
>   y   :  Ctrl t x;;      y   =  outl yv
>   x'  :  State (S t);;   x'  =  step t x y

A sequence of |n| feasible controls is optimal when starting in |x| if no
other sequence of feasible controls of the same length yield a better
|val| when starting in the same |x|:

> OptCtrlSeq : (x : State t) -> (n : Nat) -> CtrlSeq x n -> Type
> OptCtrlSeq x n ys = (ys' : CtrlSeq x n) -> So (val x n ys' <= val x n ys)

Sanity check: |Nil| is optimal control sequence

> nilIsOptCtrlSeq        :  (x : State t) -> OptCtrlSeq x Z Nil
> nilIsOptCtrlSeq x Nil  =  reflexive_Double_lte 0
