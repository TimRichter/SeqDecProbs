> module SplitQuotient

> import Syntax.PreorderReasoning
> import Unique
> import SigmaProperties

> %default total


> FixpointFam : {A : Type} -> (A -> A) -> A -> Type
> FixpointFam {A} c x = (c x = x)

> Fixpoints : {A : Type} -> (c : (A -> A)) -> Type
> Fixpoints {A} c = Sigma A (FixpointFam {A} c)

> IsIdempotent : {A : Type} -> (c : (A -> A)) -> Type
> IsIdempotent {A} c = (x : A) -> (c (c x)) = (c x)

> IdempotentEndo : (A : Type) -> Type
> IdempotentEndo A = Sigma (A -> A) IsIdempotent


> Quot : (A : Type) -> IdempotentEndo A -> Type
> Quot A c = Fixpoints {A} (getWitness c)


> ||| there is a canonical map into the quotient
>
> can : (A : Type) -> (c : (IdempotentEndo A)) -> A -> Quot A c
> can A (c ** cIdem ) y = pf where
>   pf' : c (c y) = c y
>   pf' = cIdem y
>   pf : Sigma A (FixpointFam {A} c)
>   pf = ( (c y) ** pf' )


> ||| to prove two elements x y in the quotient equal
> ||| it suffices to prove c x = cy
>
> quotEqLemma : (A : Type) -> (c : IdempotentEndo A) ->
>               (x, y : Quot A c) -> 
>               (getWitness c) (getWitness x) = 
>                   (getWitness c) (getWitness y) ->
>               x = y
> quotEqLemma A (c ** cIdem) (q ** cqIsq) (p ** cpIsp) cqIscp = 
>         sigmaEqLemma1 (q ** cqIsq) (p ** cpIsp) qIsp cqIsqUni where
>   qIsp : q = p
>   qIsp = 
>     q     ={ sym cqIsq }=
>     (c q) ={ cqIscp }=
>     (c p) ={ cpIsp }=
>     p     QED
>   Equalsq : A -> Type
>   Equalsq l = (l = q)
>   base : Unique (Equalsq q)
>   base Refl Refl = Refl
>   cqIsqUni : Unique (Equalsq (c q))
>   cqIsqUni = replace {P = \m => Unique (Equalsq m)} (sym cqIsq) base

 
> ||| we can use this to prove surjectivity of can
>
> canSurj : (A : Type) -> (c : IdempotentEndo A) -> (x : Quot A c) ->
>           Sigma A (\y => can A c y = x)
> canSurj A c (x ** cxIsx) = ( cx  **  canCxIsx  ) where
>   cx : A
>   cx = x
>   canCxIsx : (can A c cx) = (x ** cxIsx)
>   canCxIsx = quotEqLemma A c (can A c cx) (x ** cxIsx) 
>               (cong {f = getWitness c} ?shouldbecxIsx)


