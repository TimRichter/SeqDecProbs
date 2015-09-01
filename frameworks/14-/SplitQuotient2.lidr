> module SplitQuotient2

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


> IsIdempotent : {A : Type} -> (c : (A -> A)) -> Type
> IsIdempotent {A} c = (x : A) -> (c (c x)) = (c x)

> Base : Type

> normalize : Base -> Base
> normalizeIsIdem : IsIdempotent normalize


> data SQuot : Type where
>   Class : (x : Base) -> normalize x = x -> SQuot

Any class has a "canonical" representant

> representant : SQuot -> Base
> representant (Class x _) = x

which is a fixpoint of normalize (i.e. "is normal"):

> representantIsNormal :  (cl : SQuot) -> 
>                         normalize (representant cl) = representant cl
> representantIsNormal (Class _ nxIsx) = nxIsx

> ||| to prove two elements x y in the quotient equal
> ||| it suffices to prove rx = ry for the canonical representants rx and ry 
>
> quotEqLemma : (cl1, cl2 : SQuot) -> 
>               (representant cl1 = representant cl2) ->
>               cl1 = cl2
> quotEqLemma (Class q nqIsq) (Class q nqIsq') Refl = 
>   cong (uniqueEq (normalize q) q nqIsq nqIsq')


> ||| since normalize is idempotent, there is a canonical map 
> ||| Base -> SQuot, assigning to |x : Base| its equivalence class
>
> classOf : Base -> SQuot
> classOf y = Class (normalize y) (normalizeIsIdem y)

> ||| the representant of image of the class of |x| is just |normalize x|

> repAfterClassOfIsNormalize :  (x : Base) ->
>                               representant (classOf x) = normalize x
> repAfterClassOfIsNormalize x = Refl

> ||| the classes of elements x y that are in the ker c relation 
> ||| (i.e. such that c x = c y) are equal
> 
> classOfMapLemma : (x, y : Base) -> (normalize x = normalize y) -> 
>                   (classOf x) = (classOf y)
> classOfMapLemma x y nxIsny = quotEqLemma (classOf x) (classOf y) rCxIsrCy where
>   rCxIsrCy : representant (classOf x) = representant (classOf y)
>   rCxIsrCy =
>     (representant (classOf x))    ={ repAfterClassOfIsNormalize x       }=
>     (normalize x)                 ={ nxIsny                             }=
>     (normalize y)                 ={ sym (repAfterClassOfIsNormalize y) }=
>     (representant (classOf y))    QED

> ||| 
>
> classOfAfterRepIsId : (cl : SQuot) -> 
>                       classOf (representant cl) = cl
> classOfAfterRepIsId cl = quotEqLemma (classOf (representant cl)) cl sameRep where
>   sameRep : representant (classOf (representant cl)) = representant cl
>   sameRep =
>     (representant (classOf (representant cl)))
>     ={ repAfterClassOfIsNormalize (representant cl) }=
>     (normalize (representant cl))
>     ={ representantIsNormal cl }=
>     (representant cl)
>     QED



 
 ||| we can use this to prove surjectivity of can

 canSurj : {A : Type} -> {c : IdempotentEndo A} -> 
           (x : SQuot c) ->
           Sigma A (\y => can c y = x)
 canSurj {c} (x ** cxIsx) = ( x  **  canCxIsx  ) where
   cxIsx' : getWitness (can c x) = x
   cxIsx' = trans (canLemma c x) cxIsx
   canCxIsx : (can c x) = (x ** cxIsx)
   canCxIsx = quotEqLemma (can c x) (x ** cxIsx) 
              (cong {f = getWitness c} cxIsx')


 ||| or, in other words, getWitness is a section
 ||| of (can c)

 canSurj' :  {A : Type} -> {c : IdempotentEndo A} -> 
             (x : SQuot c) ->
             ((can c) . getWitness) x = x
 canSurj' {c} (x ** cxIsx) = canCxIsx where
   cxIsx' : getWitness (can c x) = x
   cxIsx' = trans (canLemma c x) cxIsx
   canCxIsx : (can c x) = (x ** cxIsx)
   canCxIsx = quotEqLemma (can c x) (x ** cxIsx) 
              (cong {f = getWitness c} cxIsx')

 ||| lift functions A -> B to SQuot c -> B by precomposing 
 ||| with getWitness, i.e. restrict them to the Fixpoints of c

 liftQ : {A, B : Type} -> (c : IdempotentEndo A) -> (f : A -> B) ->
         SQuot c -> B
 liftQ c f ( x ** _ ) = f x

 ||| same for curried functions of two arguments

 liftQ2 : {A, B : Type} -> (c : IdempotentEndo A) -> 
         (f : A -> A -> B) ->
         SQuot c -> SQuot c -> B
 liftQ2 c f ( x ** _ ) ( y ** _ ) = f x y

 ||| for c-invariant functions f : A -> B 
 ||| (c x = cy => f x = f y, i.e. the kernel 
 ||| of c is a congruence for f), (liftQ c f) . (can c)
 ||| is (pointwise equal to) f

 liftQcanLemma : {A, B : Type} -> (c : IdempotentEndo A) -> 
                 (f : A -> B) ->
                 ((x, y : A) -> ((getWitness c) x = (getWitness c) y) -> f x = f y) ->
                 (x : A) -> ((liftQ c f) . (can c)) x = f x
 liftQcanLemma (c ** cIdem) f fIsInv x = fIsInv (c x) x (cIdem x)

 ||| same for curried functions of two arguments

 liftQcanLemma2 :  {A, B : Type} -> (c : IdempotentEndo A) -> 
                   (f : A -> A -> B) ->
                   ( (x, x', y, y' : A) -> 
                     ((getWitness c) x = (getWitness c) y) -> 
                     ((getWitness c) x' = (getWitness c) y') -> 
                     f x x' = f y y') ->
                   (x, y : A) -> (liftQ2 c f) (can c x) (can c y) = f x y
 liftQcanLemma2 (c ** cIdem) f fIsInv x y = fIsInv (c x) (c y) x y (cIdem x) (cIdem y)


 ||| helper for liftQBinop

 postcan : {A : Type} -> (c : IdempotentEndo A) ->
           (op : A -> A -> A) ->
           (A -> A -> SQuot c)
 postcan c op x y = can c (x `op` y)

 ||| important special case: binary operations on A define
 ||| binary operations on SQuot c

 liftQBinop : {A : Type} -> (c : IdempotentEndo A) ->
               (op : A -> A -> A) ->
               (SQuot c -> SQuot c -> SQuot c)
 liftQBinop {A} c op x y = liftQ2 c (postcan c op) x y

 ||| 

 liftQBinopLemma :  {A : Type} -> (c : IdempotentEndo A) -> 
                   (op : A -> A -> A) ->
                   ( (x, x', y, y' : A) -> 
                     ((getWitness c) x = (getWitness c) y) -> 
                     ((getWitness c) x' = (getWitness c) y') -> 
                     can c (x `op` x') = can c (y `op` y')  
                   ) ->
                   (x, y : A) -> 
                   (liftQBinop c op) (can c x) (can c y) = can c (x `op` y)
 liftQBinopLemma {A} c op opIsInv x y = liftQcanLemma2 {A} {B=SQuot c} c (postcan c op) opIsInv x y

 ||| combined with canSurj', we obtain a
 ||| "computation rule" for the lifted operation.
 ||| 
 ||| If we could write [x] for (can c x) and 
 ||| [op] for (liftQBinop c op) that would read:
 |||
 ||| [x] [op] [y] = [ x op y ]

 compLiftQBinop :  {A : Type} -> {c : IdempotentEndo A} ->
                   (op : A -> A -> A) ->
                   ( (x, x', y, y' : A) -> 
                     ((getWitness c) x = (getWitness c) y) -> 
                     ((getWitness c) x' = (getWitness c) y') -> 
                     can c (x `op` x') = can c (y `op` y')  
                   ) ->
                   (x : SQuot c) -> (y : SQuot c) ->
                   (liftQBinop c op) x y = can c ((getWitness x) `op` (getWitness y))
 compLiftQBinop {A} {c} op opInv (x ** cxIsx) (y ** cyIsy) =
     ((liftQBinop c op) (x ** cxIsx) (y ** cyIsy))
     ={ cong {f = \k => (liftQBinop c op) k (y ** cyIsy)}
             (sym (canSurj' (x ** cxIsx))) }=
     ((liftQBinop c op) (can c x) (y ** cyIsy))
     ={ cong {f = \k => (liftQBinop c op) (can c x) k }
             (sym (canSurj' (y ** cyIsy))) }=
     ((liftQBinop c op) (can c x) (can c y))
     ={ liftQBinopLemma c op opInv x y }=
     (can c (x `op` y))
     QED


