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

addArgsLeft: from an n-ary function form an (n + m)-ary
one that ignores it's first m arguments

> addArgsLeft : {n: Nat} -> {A, B : Type} ->
>         (m : Nat) ->
>         NFun n       A B -> 
>         NFun (n + m) A B
> addArgsLeft {n} {A} {B} Z     f = 
>     replace {P = \x => NFun x A B } (sym (plusZeroRightNeutral n)) f
> addArgsLeft {n} {A} {B} (S m) f = 
>     replace {P = \x => NFun x A B } (plusSuccRightSucc n m) recCall where
>     recCall : NFun (S (n + m)) A B
>     recCall = \x => (addArgsLeft {n} {A} {B} m f)

constants (ignore all their arguments)

> constN : {n : Nat} -> {A, B : Type} -> 
>          B -> NFun n A B
> constN {n} = addArgsLeft {n=Z} n

addArgsRight: from an n-ary function form an (n + m)-ary 
one that ignores its last m arguments

> addArgsRight : {n : Nat} -> {A, B : Type} ->
>                (m : Nat) ->
>                NFun n       A B -> 
>                NFun (n + m) A B
> addArgsRight {n=Z}      {A} {B} m b = constN b 
> addArgsRight {n=(S n')} {A} {B} m f = \x => addArgsRight {n=n'} {A} {B} m (f x)  

> insertArgsAt : {n : Nat} -> {A, B : Type} ->
>                (m : Nat) -> (i : Nat) -> 
>                {auto smaller : i `LTE` n} ->
>                NFun n       A B ->
>                NFun (n + m) A B
> insertArgsAt            m Z          f = addArgsLeft m f
> insertArgsAt {n=(S n')} m (S i) {smaller=(LTESucc iLten')} f = 
>                \x => insertArgsAt {n=n'} m i {smaller=iLten'} (f x)

projections

> pr : {A : Type} -> {n : Nat} -> 
>      (i : Nat) -> 
>      {auto smaller : i `LT` n} ->
>      NOp n A
> pr {n=S _}  Z                               = \x => constN x
> pr {n=S n'} (S i') {smaller=LTESucc i'LTn'} = \x => pr {n=n'} i' {smaller= i'LTn'}

of an m-ary function f, make a vector of length n 
of (m * n)-ary functions where the i'th entry is just 
f applied to the arguments x_i*m, x_i*m+1 ,... x_i*m+m-1

> spread : {m : Nat} -> {A, B : Type} ->
>          (n : Nat) ->
>          NFun m A B ->
>          Vect n (NFun (m * n) A B)
> spread                     Z    f = []
> spread {m} {A} {B} (S n) f = 
>         (replace {P = \k => NFun k A B} (pf1 m n) (addArgsRight {n=m} (m * n) f)) :: 
>         (map (replace {P= \k => NFun (m * n) A B -> NFun k A B} (pf2 m n) (addArgsLeft m)) 
>             (spread {m} {A} {B} n f)) where
>     pf1 : (r, s : Nat) -> r + (r * s) = r * S s
>     pf1 r s = sym (multRightSuccPlus r s)
>     pf2 : (r, s : Nat) -> (r * s) + r = r * S s
>     pf2 r s= trans (plusCommutative (r * s) r) (pf1 r s)

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

An n-ary function is "invariant" w.r.t. binary relations on its 
source and target types if it is related to itself w.r.t. the lifted 
relation

> isInvariantNFun : {n : Nat} -> {A, B : Type} ->
>                   (relA : BinRel A) -> (relB : BinRel B) ->
>                   (f : NFun n A B) -> Type
> isInvariantNFun relA relB f = liftBinRelNFun relA relB f f

dependent n-ary functions on a type: the target is now an
n-ary type family on A, i.e. of type |NFun n A Type|

> NDFun : (n : Nat) -> (A : Type) -> (B : NFun n A Type) -> Type
> NDFun Z     A B = B
> NDFun (S n) A B = (x : A) -> NDFun n A (B x)

composition 

> compose : {n, m : Nat} -> {A, B, C : Type} ->
>           (Vect n (NFun m A B)) ->
>           (NFun n B C) -> 
>           (NFun m A C)
> compose {n=Z}     {m=Z}             Nil     c = c
> compose {n=Z}     {m=(S _)}     {B} Nil     c = \x => compose {B} Nil c
> compose {n=(S _)} {m=Z}     {A} {B} (b::bs) g = compose {m=Z} {A} {B} bs (g b)
> compose {n=(S _)} {m=(S _)}         fs      g = \x => compose (map (\h => h x) fs) g

variant avoiding Vect, feels like impossible, but why?

< compose' : {n, m : Nat} -> {A, B, C : Type} ->
<            NFun n (NFun m A B) ((NFun n B C) -> (NFun m A C))
< compose' {n=Z}              = \c => constN c
< compose' {n=S Z}    {m=Z}   = \b => (\g => compose' {n=n'} (g b))

NFun n is a contravariant functor in A:

> nFunFmapA : {n : Nat} -> {A, B, A' : Type} ->
>             (f : A -> A') ->
>             (NFun n A' B) -> 
>             (NFun n A B)

could prove it "by hand"

< nFunFmapA {n=Z}      f b = b
< nFunFmapA {n=(S n')} f g = \x => (nFunFmapA f (g (f x)))

but maybe better via compose

> nFunFmapA {A} {B} {n} f g = 
>     replace {P = \k => NFun k A B} (multOneLeftNeutral n) (compose (spread {m=1} n f) g)

NFun is a covariant functor in B

> nFunFmapB : {n : Nat} -> {A, B, B' : Type} -> 
>             (f : B -> B') ->
>             (NFun n A B) -> 
>             (NFun n A B')
> nFunFmapB f g = compose [g] f


given a relation |relB| on B, and n-ary functions 
|f, g : NFun n A B| that are in the relation lifting
|(=)| on |A| and |relB|, i.e. we have a function

fRg: x1, x1' : A -> x1 = x1' -> ... -> xn, xn' : A -> 
      relB (f x1 ... xn) (g x1' ... xn')

we can form

    \x1 => \x2 => ... \xn => fRg x1 x1 Refl x2 x2 Refl ... xn xn Refl

which is of type

  (x1 : A) -> .... -> (xn : A) -> relB (f x1 ... xn) (g x1 ... xn)

i.e. a dependent n-ary function on A into the type family
   (compose [f, g] relB) : NFun n A Type

> test2 : {n : Nat} -> {A, B : Type} ->
>         (relB : BinRel B) ->
>         (f, g : NFun n A B) ->
>         (fRg  : liftBinRelNFun (=) relB f g) ->
>         NDFun n A (compose [f, g] relB)
> test2 {n=Z}     relB f g fRg = fRg
> test2 {n=(S _)} relB f g fRg = \x => test2 relB (f x) (g x) (fRg x x Refl)

what else do we need?

- define identity NFun id (= pr 1 0)

- properties of compose:

  + compose [id,...,id] f = f
  + compose [f] id = f
  + compose [f_0,...,f_n-1] (pr n i) = f_i
  + associativity:
    





