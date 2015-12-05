> module NFun

> import Data.Vect
> import Syntax.PreorderReasoning

> %default total

n-ary functions from A to B in curried form

> NFun : Nat -> Type -> Type -> Type
> NFun Z     A B = B
> NFun (S n) A B = A -> (NFun n A B)

special case: n-ary operations

> NOp : Nat -> Type -> Type
> NOp n A = NFun n A A

NFun n is a contravariant functor in A:

> nFunFmapA : {n : Nat} -> {A, B, A' : Type} ->
>             (f : A -> A') ->
>             (NFun n A' B) -> (NFun n A B)
> nFunFmapA {n=Z}      f b = b
> nFunFmapA {n=(S n')} f g = \x => (nFunFmapA f (g (f x)))

and a covariant functor in B

> nFunFmapB : {n : Nat} -> {A, B : Type} ->
>             {B' : Type} -> (f : B -> B') ->
>             (NFun n A B) -> (NFun n A B')
> nFunFmapB {n=Z}      f b = f b
> nFunFmapB {n=(S n')} f g = \x => nFunFmapB f (g x)


binary relations

> BinRel : Type -> Type
> BinRel A = NFun 2 A Type -- (= A -> A -> Type)

on A and B induce a binary relation on any |NFun n A B| 

> liftBinRelNFun : {n : Nat} -> {A, B : Type} ->
>                  (relA : BinRel A) -> (relB : BinRel B) ->
>                  BinRel (NFun n A B)
> liftBinRelNFun {n=Z}         _    relB b b' = relB b b'
> liftBinRelNFun {n=(S _)} {A} relA relB f f' =
>   (x, x' : A) -> (relA x x') -> liftBinRelNFun relA relB (f x) (f' x')

The lifting of the equality relations is pointwise equality of n-ary
functions (a.k.a. homotopy)

> homotopic : {n : Nat} -> {A, B : Type} -> BinRel (NFun n A B)
> homotopic = liftBinRelNFun (=) (=)

we can now prove the functor properties of NFun n as follows:

> nFunFmapAId : {n : Nat} -> {A, B: Type} -> nFunFmapA 

An n-ary function is "invariant" w.r.t. binary relations on its 
source and target types if it is related to itself w.r.t. the lifted 
relation

> isInvariantNFun : {n : Nat} -> {A, B : Type} ->
>                   (relA : BinRel A) -> (relB : BinRel B) ->
>                   (f : NFun n A B) -> Type
> isInvariantNFun relA relB f = liftBinRelNFun relA relB f f

dependent n-ary functions on a type: the target is now a family
over (copies of) A, i.e. of type |NFun n A Type|

> NDFun : (n : Nat) -> (A : Type) -> (B : NFun n A Type) -> Type
> NDFun Z     A B = B
> NDFun (S n) A B = (x : A) -> NDFun n A (B x)


  BinRel B = NFun 2 B Type

> test1 : {n, m : Nat} -> {A, B, C : Type} ->
>         (Vect n (NFun m A B)) ->
>         (NFun n B C) -> 
>         (NFun m A C)
> test1 {n=Z}     {m=Z}             Nil     c = c
> test1 {n=Z}     {m=(S _)}     {B} Nil     c = \x => test1 {B} Nil c
> test1 {n=(S _)} {m=Z}     {A} {B} (b::bs) g = test1 {m=Z} {A} {B} bs (g b)
> test1 {n=(S _)} {m=(S _)}         fs      g = \x => test1 (map (\h => h x) fs) g



> test2 : {n : Nat} -> {A, B : Type} ->
>        (relB : BinRel B) ->
>        (f, g : NFun n A B) ->
>        (fRelg : liftBinRelNFun (=) relB f g) ->
>        NDFun n A (test1 [f, g] relB)
> test2 {n=Z}     relB f g fRelg = fRelg
> test2 {n=(S _)} relB f g fRelg = \x => test2 relB (f x) (g x) (fRelg x x Refl)



