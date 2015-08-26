> module SplitQuotient

> import Syntax.PreorderReasoning
> import Unique
> import SigmaProperties
> import EqualityProperties

> %default total

An idempotent endomap c of a type A can be thought of as 
a choice function for representatives of the kernel of c :

  ker c : A -> A -> Type
  ker c x y = c x = c y

which is an (in Idris even propositional a.k.a. unique)
equivalence relation on A.

The subset of elements in A fixed by c can then be 
identified with the quotient of A by the kernel of c.

So to construct the quotient by any given equivalence ~ on
A, it suffices to find an idempotent endomap c such that
the relations  ~ and (ker c) are isomorphic.

> FixpointFam : {A : Type} -> (A -> A) -> A -> Type
> FixpointFam {A} c x = (c x = x)

> Fixpoints : {A : Type} -> (c : (A -> A)) -> Type
> Fixpoints {A} c = Sigma A (FixpointFam c)

> IsIdempotent : {A : Type} -> (c : (A -> A)) -> Type
> IsIdempotent {A} c = (x : A) -> (c (c x)) = (c x)

> IdempotentEndo : (A : Type) -> Type
> IdempotentEndo A = Sigma (A -> A) IsIdempotent

> SQuot : {A : Type} -> IdempotentEndo A -> Type
> SQuot c = Fixpoints (getWitness c)


> ||| there is a canonical map into the quotient
>
> can : {A : Type} -> (c : (IdempotentEndo A)) -> A -> SQuot c
> can (c ** cIdem ) y = ((c y) ** (cIdem y) )


> canLemma : {A : Type} -> (c : IdempotentEndo A) -> (x : A) ->
>           getWitness (can c x) = (getWitness c) x
> canLemma (c ** _) x = Refl


> ||| to prove two elements x y in the quotient equal
> ||| it suffices to prove c x = c y
>
> quotEqLemma : {A : Type} -> {c : IdempotentEndo A} ->
>               (x, y : SQuot c) -> 
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
>           (x : SQuot c) ->
>           Sigma A (\y => can c y = x)
> canSurj {c} (x ** cxIsx) = ( x  **  canCxIsx  ) where
>   cxIsx' : getWitness (can c x) = x
>   cxIsx' = trans (canLemma c x) cxIsx
>   canCxIsx : (can c x) = (x ** cxIsx)
>   canCxIsx = quotEqLemma (can c x) (x ** cxIsx) 
>              (cong {f = getWitness c} cxIsx')


> ||| or, in other words, getWitness is a section
> ||| of (can c)
>
> canSurj' :  {A : Type} -> {c : IdempotentEndo A} -> 
>             (x : SQuot c) ->
>             ((can c) . getWitness) x = x
> canSurj' {c} (x ** cxIsx) = canCxIsx where
>   cxIsx' : getWitness (can c x) = x
>   cxIsx' = trans (canLemma c x) cxIsx
>   canCxIsx : (can c x) = (x ** cxIsx)
>   canCxIsx = quotEqLemma (can c x) (x ** cxIsx) 
>              (cong {f = getWitness c} cxIsx')

> ||| lift functions A -> B to SQuot c -> B by precomposing 
> ||| with getWitness, i.e. restrict them to the Fixpoints of c
>
> liftQ : {A, B : Type} -> (c : IdempotentEndo A) -> (f : A -> B) ->
>         SQuot c -> B
> liftQ c f ( x ** _ ) = f x

> ||| same for curried functions of two arguments
>
> liftQ2 : {A, B : Type} -> (c : IdempotentEndo A) -> 
>         (f : A -> A -> B) ->
>         SQuot c -> SQuot c -> B
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


> ||| helper for liftQBinop
>
> postcan : {A : Type} -> (c : IdempotentEndo A) ->
>           (op : A -> A -> A) ->
>           (A -> A -> SQuot c)
> postcan c op x y = can c (x `op` y)

> ||| important special case: binary operations on A define
> ||| binary operations on SQuot c
>
> liftQBinop : {A : Type} -> (c : IdempotentEndo A) ->
>               (op : A -> A -> A) ->
>               (SQuot c -> SQuot c -> SQuot c)
> liftQBinop {A} c op x y = liftQ2 c (postcan c op) x y

> ||| 
>
> liftQBinopLemma :  {A : Type} -> (c : IdempotentEndo A) -> 
>                   (op : A -> A -> A) ->
>                   ( (x, x', y, y' : A) -> 
>                     ((getWitness c) x = (getWitness c) y) -> 
>                     ((getWitness c) x' = (getWitness c) y') -> 
>                     can c (x `op` x') = can c (y `op` y')  
>                   ) ->
>                   (x, y : A) -> 
>                   (liftQBinop c op) (can c x) (can c y) = can c (x `op` y)
> liftQBinopLemma {A} c op opIsInv x y = liftQcanLemma2 {A} {B=SQuot c} c (postcan c op) opIsInv x y

> ||| combined with canSurj', we obtain a
> ||| "computation rule" for the lifted operation.
> ||| 
> ||| If we could write [x] for (can c x) and 
> ||| [op] for (liftQBinop c op) that would read:
> |||
> ||| [x] [op] [y] = [ x op y ]
>
> compLiftQBinop :  {A : Type} -> {c : IdempotentEndo A} ->
>                   (op : A -> A -> A) ->
>                   ( (x, x', y, y' : A) -> 
>                     ((getWitness c) x = (getWitness c) y) -> 
>                     ((getWitness c) x' = (getWitness c) y') -> 
>                     can c (x `op` x') = can c (y `op` y')  
>                   ) ->
>                   (x : SQuot c) -> (y : SQuot c) ->
>                   (liftQBinop c op) x y = can c ((getWitness x) `op` (getWitness y))
> compLiftQBinop {A} {c} op opInv (x ** cxIsx) (y ** cyIsy) =
>     ((liftQBinop c op) (x ** cxIsx) (y ** cyIsy))
>     ={ cong {f = \k => (liftQBinop c op) k (y ** cyIsy)}
>             (sym (canSurj' (x ** cxIsx))) }=
>     ((liftQBinop c op) (can c x) (y ** cyIsy))
>     ={ cong {f = \k => (liftQBinop c op) (can c x) k }
>             (sym (canSurj' (y ** cyIsy))) }=
>     ((liftQBinop c op) (can c x) (can c y))
>     ={ liftQBinopLemma c op opInv x y }=
>     (can c (x `op` y))
>     QED


