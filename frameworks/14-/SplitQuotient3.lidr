> module SplitQuotient3

> import Syntax.PreorderReasoning
> import Unique
> import SigmaProperties
> import EqualityProperties
> import Decidable.Equality

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

> Idempotent : {A : Type} -> (c : (A -> A)) -> Type
> Idempotent {A} c = (x : A) -> (c (c x)) = (c x)

----------------------------------------------------------
module parameters

> Base : Type
> normalize : Base -> Base
> normalizeIdem : Idempotent normalize

----------------------------------------------------------

>
> data SQuot : Type where
>   Class : (x : Base) -> normalize x = x -> SQuot

Any class has a "canonical" representant

> repr : SQuot -> Base
> repr (Class x _) = x

which is a fixpoint of normalize (i.e. "is normal"):

> reprNormal :  (cl : SQuot) -> 
>               normalize (repr cl) = repr cl
> reprNormal (Class _ nxIsx) = nxIsx

> ||| to prove two elements x y in the quotient equal
> ||| it suffices to prove rx = ry for the canonical representants rx and ry 
> 
> quotEqLemma : (cl1, cl2 : SQuot) -> 
>               (repr cl1 = repr cl2) ->
>               cl1 = cl2
> quotEqLemma (Class q nqIsq) (Class q nqIsq') Refl = 
>   cong (uniqueEq (normalize q) q nqIsq nqIsq')

> ||| since normalize is idempotent, there is a canonical map 
> ||| Base -> SQuot, assigning to |x : Base| its equivalence class
> 
> classOf : Base -> SQuot
> classOf y = Class (normalize y) (normalizeIdem y)

> syntax "~" [x] = classOf x



> ||| the representant of the class of |x| is just |normalize x|

> reprAfterClassOfIsNormalize :   (x : Base) ->
>                                 repr (classOf x) = normalize x
> reprAfterClassOfIsNormalize x = Refl

> ||| the classes of elements |x| and |y| that are in the 
> ||| |kernel normalize|  relation (i.e. such that c x = c y) are equal
> 
> classOfEqualLemma : (x, y : Base) -> 
>                     (normalize x = normalize y) -> 
>                     (classOf x) = (classOf y)
> 
> classOfEqualLemma x y nxIsny = quotEqLemma (classOf x) (classOf y) rCxIsrCy where
>   rCxIsrCy : repr (classOf x) = repr (classOf y)
>   rCxIsrCy =
>     (repr (classOf x))    ={ reprAfterClassOfIsNormalize x        }=
>     (normalize x)         ={ nxIsny                               }=
>     (normalize y)         ={ sym (reprAfterClassOfIsNormalize y)  }=
>     (repr (classOf y))    QED

> ||| 
> 
> classOfAfterReprIsId :  (cl : SQuot) -> 
>                         classOf (repr cl) = cl
> classOfAfterReprIsId cl = quotEqLemma (classOf (repr cl)) cl sameRepr where
>   sameRepr : repr (classOf (repr cl)) = repr cl
>   sameRepr =
>     (repr (classOf (repr cl)))
>     ={ reprAfterClassOfIsNormalize (repr cl) }=
>     (normalize (repr cl))
>     ={ reprNormal cl }=
>     (repr cl)
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


> ||| lift functions Base -> B to SQuot -> B by precomposing 
> ||| with getWitness, i.e. restrict them to the Fixpoints of c
> 
> lift : {B : Type} -> (f : Base -> B) ->
>         SQuot -> B
> lift f (Class x _) = f x
> 
> ||| same for curried functions of two arguments
> 
> lift2 : {B : Type} -> (f : Base -> Base -> B) ->
>         SQuot -> SQuot -> B
> lift2 f (Class x _) (Class y _) = f x y
> 
> ||| functions |f : Base -> B| invariant under the |kernel normalize|
> ||| relation (i.e. |normalize x = normalize y -> f x = f y|),  
> ||| |(liftQ f) . (classOf c)| is (pointwise equal to) |f|
> 
> liftClassOfLemma :  {B : Type} ->
>                     (f : Base -> B) ->
>                     ((x, y : Base) -> (normalize x = normalize y) -> f x = f y) ->
>                     (x : Base) -> ((lift f) . classOf) x = f x
> liftClassOfLemma f fInv x = fInv (normalize x) x (normalizeIdem x)
> 
> ||| same for curried functions of two arguments
> 
> liftClassOfLemma2 : {B : Type} -> 
>                   (f : Base -> Base -> B) ->
>                   ( (x, x', y, y' : Base) -> 
>                     (normalize x  = normalize y ) -> 
>                     (normalize x' = normalize y') -> 
>                     f x x' = f y y') ->
>                   (x, y : Base) -> 
>                   (lift2 f) (classOf x) (classOf y) = f x y
> 
> liftClassOfLemma2 f fInv x y = 
>   fInv (normalize x) (normalize y) x y (normalizeIdem x) (normalizeIdem y)


> ||| helper for liftQBinop
> 
> postcan : (op : Base -> Base -> Base) ->
>           (Base -> Base -> SQuot)
> postcan op x y = classOf (x `op` y)
> 
> ||| important special case: binary operations on Base define
> ||| binary operations on SQuot
> 
> liftBinop : (op : Base -> Base -> Base) ->
>             (SQuot -> SQuot -> SQuot) 
> liftBinop op x y = lift2 (postcan op) x y
> 

Type classes

> instance Num Base => Num SQuot where
>   (+) = liftBinop (+)
>   (-) = liftBinop (-)
>   (*) = liftBinop (*)
>   fromInteger = classOf . fromInteger
>   abs = classOf . (lift abs) 

> instance Show Base => Show SQuot where
>   show (Class x _) = "~" ++ show x

> instance DecEq Base => DecEq SQuot where
>   decEq (Class x nxIsx) (Class y nyIsy) with (decEq (normalize x) (normalize y))
>     | (Yes p) = Yes (quotEqLemma (Class x nxIsx) (Class y nyIsy) xIsy) where
>         xIsy =
>           (x)             ={ sym nxIsx }=
>           (normalize x)   ={ p }=
>           (normalize y)   ={ nyIsy }=
>           (y)             QED
>     | (No contra) = No (contra . (cong {f = normalize . repr}))


> 
> liftBinopLemma : (op : Base -> Base -> Base) ->
>                   ( (x, x', y, y' : Base) -> 
>                     (normalize x = normalize y) -> 
>                     (normalize x' = normalize y') -> 
>                     classOf (x `op` x') = classOf (y `op` y')  
>                   ) ->
>                   (x, y : Base) -> 
>                   (liftBinop op) (classOf x) (classOf y) = classOf (x `op` y)
> 
> liftBinopLemma op opInv x y = liftClassOfLemma2 {B=SQuot} (postcan op) opInv x y


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


