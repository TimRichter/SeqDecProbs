> module SplitQuotient

> %default total


> Fixpoints : {A: Type} -> (c : A -> A) -> Type
> Fixpoints {A} c = (x : A ** c x = x)


> IsIdempotent : {A : Type} -> (c : A -> A) -> Type
> IsIdempotent {A} c = (x : A) -> c (c x) = c x

> IdempotentEndo : (A : Type) -> Type
> IdempotentEndo A = ( c : (A -> A) ** IsIdempotent c )

> infix 5 //
> (//) : (A : Type) -> IdempotentEndo A -> Type
> A // (c ** idemC) = Fixpoints {A} c
 
> ||| there is a canonical map to the quotient
> canon : (A : Type) -> (c : IdempotentEndo A) -> A -> (A // c)
> canon A (c ** idemC) x = ?lala 

((c x) ** (idemC c x))

