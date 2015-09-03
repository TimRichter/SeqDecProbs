> module Quotient

> %default total

goal define a type class for types that can be takes as
quotients of a type by an equivalence relation

preliminary definitions

> data BinRel : Type -> Type where
>   MkBinRel :  {A : Type} -> 
>               (A -> A -> Type) -> 
>               BinRel A
>
> unwrapBinRel : {A : Type} -> BinRel A -> A -> A -> Type
> unwrapBinRel (MkBinRel rel) = rel

> Compatible :  {A, B : Type} -> 
>               (A -> B) -> 
>               BinRel A -> 
>               Type
> Compatible {A} {B} f (MkBinRel rel) = 
>               (x, y : A) -> 
>               rel x y -> 
>               f x = f y

> CompatibleD : {A : Type} -> 
>               {B : A -> Type} ->
>               (f : (x : A) -> B x) ->
>               (rel : BinRel A) ->
>               (subst : {x, y : A} -> unwrapBinRel rel x y -> B x -> B y) ->
>               Type
> CompatibleD {A} {B} f (MkBinRel rel) subst =
>               (x, y : A) ->
>               (xRy : rel x y) ->
>               subst xRy (f x) = f y




> class QuotientData (A : Type) (rel : BinRel A) (Q : Type) where
>   cla       : A -> Q
>   claEq     : {x, y : A} ->
>               (unwrapBinRel rel x y) ->
>               cla x = cla y
>   lift1     : {B : Type} ->
>               (f : A -> B) ->
>               (Compatible 
>   liftD1    : {B : Q -> Type} ->
>               (f : (x : A) -> B (cla x)) ->
>               (CompatibleD {B = (\x => B (cla x))} f rel ?subst ) ->

                 (\xRy => \bclx => replace {P = \q => B q} (claEq xRy) bclx)) ->

>               ((q : Q) -> B q)



