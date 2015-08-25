> module SplitQuotient

> import Syntax.PreorderReasoning
> import Unique
> import SigmaProperties
> import EqualityProperties

> %default total


> FixpointFam : {A : Type} -> (A -> A) -> A -> Type
> FixpointFam {A} c x = (c x = x)

> Fixpoints : {A : Type} -> (c : (A -> A)) -> Type
> Fixpoints {A} c = Sigma A (FixpointFam c)

> IsIdempotent : {A : Type} -> (c : (A -> A)) -> Type
> IsIdempotent {A} c = (x : A) -> (c (c x)) = (c x)

> IdempotentEndo : (A : Type) -> Type
> IdempotentEndo A = Sigma (A -> A) IsIdempotent

> Quot : {A : Type} -> IdempotentEndo A -> Type
> Quot c = Fixpoints (getWitness c)


> ||| there is a canonical map into the quotient
>
> can : {A : Type} -> (c : (IdempotentEndo A)) -> A -> Quot c
> can (c ** cIdem ) y = ((c y) ** (cIdem y) )


> canLemma : {A : Type} -> (c : IdempotentEndo A) -> (x : A) ->
>           getWitness (can c x) = (getWitness c) x
> canLemma (c ** _) x = Refl


> ||| to prove two elements x y in the quotient equal
> ||| it suffices to prove c x = c y
>
> quotEqLemma : {A : Type} -> {c : IdempotentEndo A} ->
>               (x, y : Quot c) -> 
>               (getWitness c) (getWitness x) = 
>                   (getWitness c) (getWitness y) ->
>               x = y
> quotEqLemma {A} {c} (q ** cqIsq) (p ** cpIsp) cqIscp = 
>   sigmaEqLemma1 (q ** cqIsq) (p ** cpIsp) qIsp (uniqueEq (cW q) q) where
>   cW : A -> A
>   cW = getWitness c
>   qIsp : q = p
>   qIsp = 
>     q      ={ sym cqIsq }=
>     (cW q) ={ cqIscp }=
>     (cW p) ={ cpIsp }=
>     p      QED

 
> ||| we can use this to prove surjectivity of can
>
> canSurj : {A : Type} -> {c : IdempotentEndo A} -> 
>           (x : Quot c) ->
>           Sigma A (\y => can c y = x)
> canSurj {c} (x ** cxIsx) = ( x  **  canCxIsx  ) where
>   cxIsx' : getWitness (can c x) = x
>   cxIsx' = trans (canLemma c x) cxIsx
>   canCxIsx : (can c x) = (x ** cxIsx)
>   canCxIsx = quotEqLemma (can c x) (x ** cxIsx) 
>              (cong {f = getWitness c} cxIsx')


> ||| we can use this to prove surjectivity of can
>
> canSurj' :  {A : Type} -> {c : IdempotentEndo A} -> 
>             (x : Quot c) ->
>             ((can c) . getWitness) x = x
> canSurj' {c} (x ** cxIsx) = canCxIsx where
>   cxIsx' : getWitness (can c x) = x
>   cxIsx' = trans (canLemma c x) cxIsx
>   canCxIsx : (can c x) = (x ** cxIsx)
>   canCxIsx = quotEqLemma (can c x) (x ** cxIsx) 
>              (cong {f = getWitness c} cxIsx')

> ||| lift functions A -> B to Quot c -> B by precomposing 
> ||| with getWitness, i.e. restrict them to the Fixpoints of c
>
> liftQ : {A, B : Type} -> (c : IdempotentEndo A) -> (f : A -> B) ->
>         Quot c -> B
> liftQ c f ( x ** _ ) = f x

> ||| same for curried functions of two arguments
>
> liftQ2 : {A, B : Type} -> (c : IdempotentEndo A) -> 
>         (f : A -> A -> B) ->
>         Quot c -> Quot c -> B
> liftQ2 c f ( x ** _ ) ( y ** _ ) = f x y

> ||| for c-invariant functions f : A -> B 
> ||| (c x = cy => f x = f y, i.e. the kernel 
> ||| of c is a congruence for f), (liftQ c f) . (can c)
> ||| is (pointwise equal to) f
>
> liftQcanLemma : {A, B : Type} -> (c : IdempotentEndo A) -> 
>                 (f : A -> B) ->
>                 ((x, y : A) -> ((getWitness c) x = (getWitness c) y) -> f x = f y) ->
>                 (x : A) -> ((liftQ c f) . (can c)) x = f x
> liftQcanLemma (c ** cIdem) f fIsInv x = fIsInv (c x) x (cIdem x)

> ||| same for curried functions of two arguments
>
> liftQcanLemma2 :  {A, B : Type} -> (c : IdempotentEndo A) -> 
>                   (f : A -> A -> B) ->
>                   ( (x, x', y, y' : A) -> 
>                     ((getWitness c) x = (getWitness c) y) -> 
>                     ((getWitness c) x' = (getWitness c) y') -> 
>                     f x x' = f y y') ->
>                   (x, y : A) -> (liftQ2 c f) (can c x) (can c y) = f x y
> liftQcanLemma2 (c ** cIdem) f fIsInv x y = fIsInv (c x) (c y) x y (cIdem x) (cIdem y)

> ||| important special case: binary operations on A define
> ||| binary operations on Quot c
>
> liftBinQuot : {A : Type} -> (c : IdempotentEndo A) ->
>               (op : A -> A -> A) ->
>               (Quot c -> Quot c -> Quot c)
> liftBinQuot {A} c op x y = liftQ2 c cqop x y where
>   cqop : A -> A -> Quot c
>   cqop x y = can c ( x `op` y)






