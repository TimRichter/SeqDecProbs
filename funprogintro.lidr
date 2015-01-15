> import Syntax.PreorderReasoning
> 
> postulate  A : Type
> postulate  B : Type
> postulate  C : Type
> postulate  f : A -> B
> postulate  g : A -> B -> c
> postulate  x : A
> postulate  y : B

> test1 : B
> test1 = f x
> test2 : C
> test2 = (g x) y
> test3 : Int
> test3 = 2 + 3
> gx : B -> C
> gx = g x

> aNumber : Nat
> aNumber = 1738

> aFun : Nat -> Nat
> aFun = \x => 2*x+1

> aFun' : Nat -> Nat
> aFun' x = 2*x+1

> infixr 10 ^
> (^) : Float -> Nat -> Float
> x ^ Z      = 1
> x ^ (S n)  = x * (x^n)

> namespace monomorphic
>   curry : ((A, B) -> C) -> A -> B -> C
>   curry f a b = f (a, b)
>   
>   uncurry : (A -> B -> C) -> (A, B) -> C
>   uncurry f (a, b) = f a b

> discount : Float -> (Nat -> A -> Float) -> (Nat -> A -> Float)
> discount   rate     reward              =  \t =>  \x => rate^t * reward t x

> namespace polymorphic
>   curry : ((a, b) -> c) -> a -> b -> c
>   curry f a b = f (a, b)
>   
>   uncurry : (a -> b -> c) -> (a, b) -> c
>   uncurry f (a, b) = f a b

>   fst1 : (s, t) -> s
>   fst1 (x, y) = x

The type signature uses two \emph{type variables} |s| and |t| and
behind the scenes the definition is actually treated like this:

>   fst2 : {s : Type} -> {t : Type} -> (s, t) -> s
>   fst2 {s} {t} (x, y) = x

Equality and equational reasoning

> postulate unitMult   : (y : Float) -> (1*y = y)
> postulate assocMult  : (x : Float) -> (y : Float) ->  (z : Float) ->  (x*y)*z = x*(y*z)

> expLemma : (x : Float) -> (m : Nat) -> (n : Nat) -> (x^m * x^n = x^(m+n))
> expLemma x Z      n = unitMult (x^n)
> expLemma x (S m)  n = 
>     ( x^(S m) * x^n      ) 
>   ={ Refl }= 
>     ( (x * x^m) * x^n    ) 
>   ={ assocMult x (x^m) (x^n) }= 
>     ( x * (x^m * x^n)    )
>   ={ cong (expLemma x m n) }= 
>     ( x * x^(m + n)      )
>   ={ Refl }= 
>     ( x^(S m + n)        )
>   QED

For many examples of using the equality proof notation (in Idris'
sister language Agda), see \cite{MuKoJansson2009AoPA}.
