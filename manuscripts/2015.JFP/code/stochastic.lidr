> module Stochastic

> import Data.So
> import Data.Fin
> import Data.Vect

> %default total


> data Prob : Type -> Type where
>   MkProb  :  {A : Type} ->
>              {n : Nat} ->
>              (as : Vect n A) ->
>              (ps : Vect n Double) ->
>              (k : Fin n -> So (index k ps >= 0.0)) ->
>              sum ps = 1.0 ->
>              Prob A

> X : (t : Nat) -> Type

> Y : (t : Nat) -> (x : X t) -> Type

> step : (t : Nat) -> (x : X t) -> (y : Y t x) -> Prob (X (S t))

> reward : (t : Nat) -> (x : X t) -> (y : Y t x) -> (x' : X (S t)) -> Double

> fmap : {A, B : Type} -> (A -> B) -> Prob A -> Prob B
> fmap f (MkProb as ps p q) = MkProb (map f as) ps p q

> rewards : (t : Nat) -> (x : X t) -> (y : Y t x) -> Prob Double
> rewards t x y = fmap (reward t x y) (step t x y)

> oneGTzero : So (1.0 >= 0.0)
> oneGTzero = Oh

> helper : (i : Fin 1) -> So (index i [1.0] >= 0.0)
> helper FZ     = oneGTzero
> helper (FS q) = FinZElim q

> certain : {A : Type} -> A -> Prob A
> certain a = MkProb [a] [1.0] helper Refl

2015-12-08: PaJa: I get
- + Errors (1)
 `-- stochastic.lidr line 41 col 8:
     No such variable i

But there is no variable i mentioned!?
