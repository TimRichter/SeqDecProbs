> module SplitQuotient3

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
> normalize : SplitQuotient3.Base -> SplitQuotient3.Base
> normalizeIdem : Idempotent SplitQuotient3.normalize

----------------------------------------------------------

> ||| Define the quotient type as elements of Base
> ||| that are fixed by |normalize|
> |||
> data SQuot : Type where
>   Class : (x : Base) -> normalize x = x -> SQuot


> ||| Any class has a canonical representant
> |||
> repr : SQuot -> Base
> repr (Class x _) = x


> ||| which is a fixpoint of |normalize|.
> |||
> reprNormal :  (cl : SQuot) ->
>               normalize (repr cl) = repr cl
> reprNormal (Class _ nxIsx) = nxIsx


> ||| Since Idris has UIP, two elements |cl1, cl2 : SQuot|
> ||| are equal if their representants are equal.
> |||
> classesEqIfReprEq : (cl1, cl2 : SQuot) ->
>                     repr cl1 = repr cl2 ->
>                     cl1 = cl2
> classesEqIfReprEq (Class q nqIsq) (Class q nqIsq') Refl =
>   cong (uniqueEq (normalize q) q nqIsq nqIsq')


> ||| Since |normalize| is idempotent, there is a canonical
> ||| map |Base -> SQuot|, assigning to |x : Base| its
> ||| equivalence class, represented by |normalize x|.
> |||
> classOf : Base -> SQuot
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
> classOfAfterReprIsId :  (cl : SQuot) ->
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
> ||| |SQuot -> B|.
> |||
> lift :  {B : Type} ->
>         (f : Base -> B) ->
>         SQuot -> B
>
> lift f (Class x _) = f x


> ||| If |f: Base -> B| is invariant under the |ker normalize|
> ||| relation, |lift f| is a lift of |f| along the canonical map
> ||| |classOf: Base -> SQuot|, i.e. |(lift f) . classOf|
> ||| is (pointwise) equal to |f|, i.e. this diagram commutes:
> |||
> |||              lift f
> |||        SQuot ------> B
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
> ||| to a function |SQuot -> SQuot -> B|.
> |||
> lift2 : {B : Type} ->
>         (f : Base -> Base -> B) ->
>         SQuot -> SQuot -> B
>
> lift2 f (Class x _) (Class y _) = f x y


> ||| If |f: Base -> Base -> B| is invariant under the
> ||| |ker normalize| relation in each argument, |lift2 f|
> ||| is (the currying of) a lift of (the uncurrying of)
> ||| |f|, i.e. the following diagram commutes
> |||
> |||                 uncurry (lift f)
> |||      SQuot x SQuot ----------> B
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
>                   (Base -> Base -> SQuot)
>
> classOfAfterOp op x y = [x `op` y]


> ||| Important special case of |lift2| (in combination
> ||| with |classOfAfterOp|): A binary operation on Base 
> ||| lifts to a binary operation on SQuot.
> |||
> liftBinop : (op : Base -> Base -> Base) ->
>             (SQuot -> SQuot -> SQuot)
>
> liftBinop op x y = lift2 (classOfAfterOp op) x y


> ||| For a |ker normalize|-invariant binary operation |op|,
> ||| |liftBinOp op| is (the currying of) a lift of (the 
> ||| uncurrying of) |op| in the sense that this diagram commutes:
> |||
> |||                 uncurry (liftBinop op)
> |||       SQuot x SQuot -----------------> SQuot
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
>   lift2Comp {B=SQuot} (classOfAfterOp op) opInv x y

----------------------------
Type classes
----------------------------

> instance Num Base => Num SQuot where
>   (+) = liftBinop (+)
>   (*) = liftBinop (*)
>   fromInteger = classOf . fromInteger
>   -- abs = classOf . (lift abs)

> instance Show Base => Show SQuot where
>   show (Class x _) = "[" ++ show x ++ "]"

> instance DecEq Base => DecEq SQuot where
>   decEq (Class x nxIsx) (Class y nyIsy)
>     with (decEq (normalize x) (normalize y))
>     | (Yes p) = Yes (classesEqIfReprEq  (Class x nxIsx)
>                                         (Class y nyIsy)
>                                         xIsy) where
>         xIsy =
>           (x)             ={ sym nxIsx }=
>           (normalize x)   ={ p }=
>           (normalize y)   ={ nyIsy }=
>           (y)             QED
>     | (No contra) = No (contra . (cong {f = normalize . repr}))

