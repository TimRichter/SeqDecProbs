> module KernelQuotient

> import Syntax.PreorderReasoning
> import EqualityProperties

> %default total

An idempotent endomap c of a type A can be thought of as
a choice function for representatives of the kernel of c :

  ker c : A -> A -> Type
  ker c x y = c x = c y

which is an (in Idris even propositional a.k.a. unique)
equivalence relation on A.

The subset of elements in A fixed by c can then be
identified with the quotient of A by that equivalence.

> Idempotent : {A : Type} -> (c : (A -> A)) -> Type
> Idempotent {A} c = (x : A) -> (c (c x)) = (c x)

----------------------------------------------------------
module parameters

> Base : Type
> normalize : KernelQuotient.Base -> 
>             KernelQuotient.Base
> normalizeIdem : Idempotent KernelQuotient.normalize

----------------------------------------------------------

> ||| Define the quotient type as elements of Base
> ||| that are fixed by |normalize|
> |||
> data Quot : Type where
>   Class : (x : Base) -> normalize x = x -> Quot


> ||| Any class has a canonical representant
> |||
> repr : Quot -> Base
> repr (Class x _) = x


> ||| which is a fixpoint of |normalize|.
> |||
> reprNormal :  (cl : Quot) ->
>               normalize (repr cl) = repr cl
> reprNormal (Class _ nxIsx) = nxIsx


> ||| Since Idris has UIP, two elements |cl1, cl2 : Quot|
> ||| are equal if their representants are equal.
> |||
> classesEqIfReprEq : (cl1, cl2 : Quot) ->
>                     repr cl1 = repr cl2 ->
>                     cl1 = cl2
> classesEqIfReprEq (Class q nqIsq) (Class q nqIsq') Refl =
>   cong (uniqueEq (normalize q) q nqIsq nqIsq')


> ||| Since |normalize| is idempotent, there is a canonical
> ||| map |Base -> Quot|, assigning to |x : Base| its
> ||| equivalence class, represented by |normalize x|.
> |||
> classOf : Base -> Quot
> classOf x = Class (normalize x) (normalizeIdem x)
>
> syntax "[" [x] "]" = classOf x


> ||| The representant of |[x]| is |normalize x|.
> |||
> reprAfterClassOfIsNormalize :   (x : Base) ->
>                                 repr [x] = normalize x
> reprAfterClassOfIsNormalize x = Refl


> ||| The classes of elements |x| and |y| such that
> ||| |normalize x = normalize y| (, i.e. |x| and |y|
> ||| are in the |ker normalize| relation, are equal.
> |||
> classOfEqIfNormalizeEq :  (x, y : Base) ->
>                           (normalize x = normalize y) ->
>                           [x] = [y]
>
> classOfEqIfNormalizeEq x y nxIsny =
>   classesEqIfReprEq [x] [y] rCxIsrCy where
>     rCxIsrCy : repr [x] = repr [y]
>     rCxIsrCy =
>       (repr [x])  
>         ={ reprAfterClassOfIsNormalize x       }=
>       (normalize x)
>         ={ nxIsny                              }=
>       (normalize y)  
>         ={ sym (reprAfterClassOfIsNormalize y) }=
>       (repr [y])     
>         QED


> ||| The class of the canonical representant of any 
> ||| given class is that class itself.
> |||
> classOfAfterReprIsId :  (cl : Quot) ->
>                         [repr cl] = cl
>
> classOfAfterReprIsId cl =
>   classesEqIfReprEq [repr cl] cl sameRepr where
>     sameRepr : repr [repr cl] = repr cl
>     sameRepr =
>       (repr [repr cl])      
>         ={ reprAfterClassOfIsNormalize (repr cl) }=
>       (normalize (repr cl)) 
>         ={ reprNormal cl                         }=
>       (repr cl)
>         QED


> ||| Any function |Base -> B| can be lifted to a function
> ||| |Quot -> B|.
> |||
> lift :  {B : Type} ->
>         (f : Base -> B) ->
>         Quot -> B
>
> lift f (Class x _) = f x


> ||| If |f: Base -> B| is invariant under the |ker normalize|
> ||| relation, |lift f| is a lift of |f| along the canonical map
> ||| |classOf: Base -> Quot|, i.e. |(lift f) . classOf|
> ||| is (pointwise) equal to |f|, i.e. this diagram commutes:
> |||
> |||              lift f
> |||         Quot ------> B
> |||            ^        ^
> |||             \      /
> |||         [_]  \    / f
> |||               \  /
> |||               Base
> ||| 
> ||| This can be seen as a "computation rule" for |lift f|:
> ||| |(lift f) [x] = f x|.
> ||| 
> liftComp: {B : Type} ->
>           (f : Base -> B) ->
>           ( (x, y : Base) ->
>             (normalize x = normalize y) ->
>             f x = f y
>           ) ->
>           (x : Base) ->
>           (lift f) [x] = f x
>
> liftComp f fInv x = fInv (normalize x) x (normalizeIdem x)


> ||| Any binary function |Base -> Base -> B| can be lifted
> ||| to a function |Quot -> Quot -> B|.
> |||
> lift2 : {B : Type} ->
>         (f : Base -> Base -> B) ->
>         Quot -> Quot -> B
>
> lift2 f (Class x _) (Class y _) = f x y


> ||| If |f: Base -> Base -> B| is invariant under the
> ||| |ker normalize| relation in each argument, |lift2 f|
> ||| is (the currying of) a lift of (the uncurrying of)
> ||| |f|, i.e. the following diagram commutes
> |||
> |||                 uncurry (lift f)
> |||         Quot x Quot ----------> B
> |||                  ^             ^
> |||                   \           /
> |||         [_] x [_]  \         / uncurry f
> |||                     \       /
> |||                    Base x Base
> |||
> ||| This can be seen as a "computation rule" for
> ||| |lift2 f|: |(lift f) [x] [y] = f x y|.
> ||| 
> lift2Comp:  {B : Type} ->
>             (f : Base -> Base -> B) ->
>             ( (x, x', y, y' : Base) ->
>               (normalize x  = normalize y ) ->
>               (normalize x' = normalize y') ->
>               f x x' = f y y') ->
>             (x, y : Base) ->
>             (lift2 f) [x] [y] = f x y
>
> lift2Comp f fInv x y =
>   fInv (normalize x) (normalize y) x y
>        (normalizeIdem x) (normalizeIdem y)


> ||| Helper for liftBinop and liftBinopLemma, mapping
> ||| `op` to curry (classOf . (uncurry op)).
> |||
> classOfAfterOp :  (op : Base -> Base -> Base) ->
>                   (Base -> Base -> Quot)
>
> classOfAfterOp op x y = [x `op` y]


> ||| Important special case of |lift2| (in combination
> ||| with |classOfAfterOp|): A binary operation on Base 
> ||| lifts to a binary operation on Quot.
> |||
> liftBinop : (op : Base -> Base -> Base) ->
>             (Quot -> Quot -> Quot)
>
> liftBinop op x y = lift2 (classOfAfterOp op) x y


> ||| For a |ker normalize|-invariant binary operation |op|,
> ||| |liftBinOp op| is (the currying of) a lift of (the 
> ||| uncurrying of) |op| in the sense that this diagram commutes:
> |||
> |||                 uncurry (liftBinop op)
> |||        Quot x Quot ------------------> Quot
> |||             ^                           ^
> |||   [_] x [_] |                           | [_]
> |||             |                           |
> |||        Base x Base ------------------> Base
> |||                       uncurry op
> ||| 
> ||| This can be seen as a "computation rule" for
> ||| |liftBinop op|: |(liftBinop op) [x] [y] = [x `op` y]|.
> |||
> liftBinopComp:  (op : Base -> Base -> Base) ->
>                 ( (x, x', y, y' : Base) ->
>                   (normalize x = normalize y) ->
>                   (normalize x' = normalize y') ->
>                   [x `op` x'] = [y `op` y']
>                 ) ->
>                 (x, y : Base) ->
>                 (liftBinop op) [x] [y] = [x `op` y]
>
> liftBinopComp op opInv x y =
>   lift2Comp {B=Quot} (classOfAfterOp op) opInv x y

----------------------------
Type classes
----------------------------

 instance Num Base => Num Quot where
   (+) = liftBinop (+)
   (*) = liftBinop (*)
   fromInteger = classOf . fromInteger
   -- abs = classOf . (lift abs)

 instance Show Base => Show Quot where
   show (Class x _) = "[" ++ show x ++ "]"

 instance DecEq Base => DecEq Quot where
   decEq (Class x nxIsx) (Class y nyIsy)
     with (decEq (normalize x) (normalize y))
     | (Yes p) = Yes (classesEqIfReprEq  (Class x nxIsx)
                                         (Class y nyIsy)
                                         xIsy) where
         xIsy =
           (x)             ={ sym nxIsx }=
           (normalize x)   ={ p }=
           (normalize y)   ={ nyIsy }=
           (y)             QED
     | (No contra) = No (contra . (cong {f = normalize . repr}))

