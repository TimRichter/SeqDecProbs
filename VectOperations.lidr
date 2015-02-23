> module VectOperations


> import Data.Vect
> import Data.Fin
> import Data.So
> import Decidable.Order

> import Decidable


> %default total


> ||| Lookup the index of an element of a vector
> lookup : {A : Type} -> (a : A) -> (as : Vect n A) -> Elem a as -> Fin n
> lookup {n = Z}   a  Nil        Here         impossible
> lookup {n = Z}   a  Nil       (There p)     impossible
> lookup {n = S m} a (a :: as)   Here       = FZ
> lookup {n = S m} a (a' :: as) (There prf) = FS (lookup a as prf)


> ||| Filters a vector on a decidable property
> filter : {A : Type} ->
>          {P : A -> Type} ->
>          Dec1 P ->
>          Vect n A -> 
>          (m : Nat ** Vect m A)
> filter d1P Nil = (Z ** Nil)
> filter d1P (a :: as) with (filter d1P as)
>   | (n ** as') with (d1P a)
>     | (Yes _) = (S n ** a :: as')
>     | (No  _) = (n ** as')


> ||| Filters a vector on a decidable property and pairs elements with proofs
> filterTag : {A : Type} ->
>             {P : A -> Type} ->
>             Dec1 P ->
>             Vect n A -> 
>             (m : Nat ** Vect m (Sigma A P))
> filterTag d1P Nil = (Z ** Nil)
> filterTag d1P (a :: as) with (filterTag d1P as)
>   | (_ ** tail) with (d1P a)
>     | (Yes p)     = (_ ** (a ** p) :: tail)
>     | (No contra) = (_ ** tail)


> |||
> argmaxMax : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO => 
>             Vect (S n) (A,F) -> (A,F)
> argmaxMax {n = Z}   (af :: Nil) = af
> argmaxMax {n = S m} (af :: (af' :: afs)) with (order (snd af) (snd (argmaxMax (af' :: afs))))
>   | (Left  _) = argmaxMax (af' :: afs)
>   | (Right _) = af


> |||
> argmax : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO => 
>          Vect (S n) (A,F) -> A
> argmax = fst . argmaxMax


> |||
> max : {A, F : Type} -> {TO : F -> F -> Type} -> Ordered F TO => 
>       Vect (S n) (A,F) -> F
> max = snd . argmaxMax


