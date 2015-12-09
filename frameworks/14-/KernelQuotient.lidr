> module KernelQuotient

> import Syntax.PreorderReasoning
> import EqualityProperties
> import NFun

> %default total

An idempotent endomap c of a type A can be thought of as
a choice function for representatives of the kernel of c :

  ker c : A -> A -> Type
  ker c x y = (c x = c y)

which is an (in Idris even propositional a.k.a. unique)
equivalence relation on A.

The subset of elements in A fixed by c can then be
identified with the quotient of A by that equivalence.

> Idempotent : {A : Type} -> (c : (A -> A)) -> Type
> Idempotent {A} c = (x : A) -> (c (c x)) = (c x)

----------------------------------------------------------
module parameters

> KBase : Type
> normalize : KernelQuotient.KBase ->
>             KernelQuotient.KBase
> normalizeIdem : Idempotent KernelQuotient.normalize

----------------------------------------------------------

> ||| Define the quotient type as elements of KBase
> ||| that are fixed by |normalize|
> |||
> data KQuot : Type where
>   Class : (x : KBase) -> .(xNormal : normalize x = x) -> KQuot


> ||| Any class has a canonical representant
> |||
> repr : KQuot -> KBase
> repr (Class x _) = x


> ||| which is a fixpoint of |normalize|.
> |||
> reprNormal :  (cl : KQuot) ->
>               normalize (repr cl) = repr cl
> reprNormal (Class _ nxIsx) = nxIsx


> ||| Since Idris has UIP, two elements |cl1, cl2 : KQuot|
> ||| are equal if their representants are equal.
> |||
> classesEqIfReprEq : (cl1, cl2 : KQuot)    ->
>                     repr cl1 = repr cl2   ->
>                     cl1 = cl2
> classesEqIfReprEq (Class q nqIsq) (Class q nqIsq') Refl =
>   cong (uniqueEq (normalize q) q nqIsq nqIsq')


> ||| Since |normalize| is idempotent, there is a canonical
> ||| map |KBase -> KQuot|, assigning to |x : KBase| its
> ||| equivalence class, represented by |normalize x|.
> |||
> classOf : KBase -> KQuot
> classOf x = Class (normalize x) (normalizeIdem x)
>
> syntax "[" [x] "]" = classOf x


> ||| The representant of |[x]| is |normalize x|.
> |||
> reprAfterClassOfIsNormalize :   (x : KBase) ->
>                                 repr [x] = normalize x
> reprAfterClassOfIsNormalize x = Refl


> ||| The classes of elements |x| and |y| such that
> ||| |normalize x = normalize y| (i.e. such that |x|
> ||| and |y| are in the |ker normalize| relation) are
> ||| equal.
> |||
> classOfEqIfNormalizeEq :  (x, y : KBase) ->
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
> classOfAfterReprIsId :  (cl : KQuot) ->
>                         [repr cl] = cl
>
> classOfAfterReprIsId cl =
>   classesEqIfReprEq [repr cl] cl sameRepr  where
>     sameRepr : repr [repr cl] = repr cl
>     sameRepr =
>       (repr [repr cl])
>         ={ reprAfterClassOfIsNormalize (repr cl) }=
>       (normalize (repr cl))
>         ={ reprNormal cl                         }=
>       (repr cl)
>         QED

> ||| Any function |KBase -> B| can be lifted to a function
> ||| |KQuot -> B|.
> |||
> lift :  {B : Type} ->
>         (f : KBase -> B) ->
>              KQuot -> B
>
> lift f (Class x _) = f x


> ||| If |f : KBase -> B| is invariant under the |ker normalize|
> ||| relation, |lift f| is a lift of |f| along the canonical map
> ||| |classOf : KBase -> KQuot|, i.e. |(lift f) . classOf|
> ||| is (pointwise) equal to |f|, i.e. this diagram commutes:
> |||
> |||              lift f
> |||        KQuot ------> B
> |||            ^        ^
> |||             \      /
> |||         [_]  \    / f
> |||               \  /
> |||               KBase
> ||| 
> ||| This can be seen as a "computation rule" for |lift f|:
> ||| |(lift f) [x] = f x|.
> |||
> liftComp: {B : Type} ->
>           (f : KBase -> B) ->
>           ( (x, y : KBase) ->
>             (normalize x = normalize y) ->
>             f x = f y
>           ) ->
>           (x : KBase) ->
>           (lift f) [x] = f x
>
> liftComp f fInv x = fInv (normalize x) x (normalizeIdem x)


> ||| Any binary function |KBase -> KBase -> B| can be lifted
> ||| to a function |KQuot -> KQuot -> B|.
> |||
> lift2 : {B : Type} ->
>         (f : KBase -> KBase -> B) ->
>              KQuot -> KQuot -> B
>
> lift2 f (Class x _) (Class y _) = f x y


> ||| If |f: KBase -> KBase -> B| is invariant under the
> ||| |ker normalize| relation in each argument, |lift2 f|
> ||| is (the currying of) a lift of (the uncurrying of)
> ||| |f|, i.e. the following diagram commutes
> |||
> |||                 uncurry (lift f)
> |||       KQuot x KQuot ----------> B
> |||                  ^             ^
> |||                   \           /
> |||         [_] x [_]  \         / uncurry f
> |||                     \       /
> |||                    KBase x KBase
> |||
> ||| This can be seen as a "computation rule" for
> ||| |lift2 f|: |(lift f) [x] [y] = f x y|.
> ||| 
> lift2Comp:  {B : Type} ->
>             (f : KBase -> KBase -> B) ->
>             ( (x, x' : KBase) ->
>               (normalize x  = normalize x' ) ->
>               (y, y' : KBase) ->
>               (normalize y = normalize y') ->
>               f x y = f x' y') ->
>             (x, y : KBase) ->
>             (lift2 f) [x] [y] = f x y
>
> lift2Comp f fInv x y =
>   fInv (normalize x) x (normalizeIdem x)
>        (normalize y) y (normalizeIdem y)


> ||| Helper for liftBinop and liftBinopLemma, mapping
> ||| `op` to curry (classOf . (uncurry op)).
> |||
> classOfAfterOp :  (op : KBase -> KBase -> KBase) ->
>                   (KBase -> KBase -> KQuot)
>
> classOfAfterOp op x y = [x `op` y]


> ||| Important special case of |lift2| (in combination
> ||| with |classOfAfterOp|): A binary operation on KBase 
> ||| lifts to a binary operation on KQuot.
> |||
> liftBinop : (op : KBase -> KBase -> KBase) ->
>                   KQuot -> KQuot -> KQuot
>
> liftBinop op x y = lift2 (classOfAfterOp op) x y


> ||| For a |ker normalize|-invariant binary operation |op|,
> ||| |liftBinOp op| is (the currying of) a lift of (the 
> ||| uncurrying of) |op| in the sense that this diagram commutes:
> |||
> |||                 uncurry (liftBinop op)
> |||       KQuot x KQuot ------------------> KQuot
> |||             ^                           ^
> |||   [_] x [_] |                           | [_]
> |||             |                           |
> |||        KBase x KBase ------------------> KBase
> |||                       uncurry op
> ||| 
> ||| This can be seen as a "computation rule" for
> ||| |liftBinop op|: |(liftBinop op) [x] [y] = [x `op` y]|.
> |||
> liftBinopComp:  (op : KBase -> KBase -> KBase) ->
>                 ( (x, x' : KBase) ->
>                   (normalize x = normalize x') ->
>                   (y, y' : KBase) ->
>                   (normalize y = normalize y') ->
>                   [x `op` y] = [x' `op` y']
>                 ) ->
>                 (x, y : KBase) ->
>                 (liftBinop op) [x] [y] = [x `op` y]
>
> liftBinopComp op opInv x y =
>   lift2Comp {B=KQuot} (classOfAfterOp op) opInv x y

given a (ternary) type family on KQuot, to give a section
of that type family it is enough to give a value for any
[x], [y], [z] with x, y, z in KBase

> test3 : {B : KQuot -> KQuot -> KQuot -> Type} ->
>         (f : (x : KBase) -> (y : KBase) -> (z : KBase) -> B [x] [y] [z]) ->
>         (x : KQuot) -> (y : KQuot) -> (z : KQuot) -> B x y z
> test3 {B} f x y z = replace {P = id} BEq (f (repr x) (repr y) (repr z)) where
>     BEq : B [repr x] [repr y] [repr z] = B x y z
>     BEq =
>       (B [repr x] [repr y] [repr z])
>         ={ cong {f = \w => B w [repr y] [repr z]} (classOfAfterReprIsId x) }=
>       (B x [repr y] [repr z])
>         ={ cong {f = \w => B x w [repr z]}        (classOfAfterReprIsId y) }=
>       (B x y [repr z])
>         ={ cong {f = \w => B x y w}               (classOfAfterReprIsId z) }=
>       (B x y z)
>         QED

> test2 : {B : KQuot -> KQuot -> Type} ->
>         (f : (x : KBase) -> (y : KBase) -> B [x] [y]) ->
>         (x : KQuot) -> (y : KQuot) -> B x y
> test2 {B} f x y = replace {P = id} BEq (f (repr x) (repr y)) where
>     BEq : B [repr x] [repr y] = B x y
>     BEq =
>       (B [repr x] [repr y])
>         ={ cong {f = \w => B w [repr y]} (classOfAfterReprIsId x) }=
>       (B x [repr y])
>         ={ cong {f = \w => B x w}        (classOfAfterReprIsId y) }=
>       (B x y )
>         QED


lifting n-ary functions:

> liftN : {n : Nat} -> {B : Type} ->
>         (NFun n KBase B) -> (NFun n KQuot B)
> liftN = nFunFmapA repr

lifting n-ary operations:

> liftNOp : {n : Nat} -> (NOp n KBase) -> (NOp n KQuot)
> liftNOp = liftN . (nFunFmapB classOf)

lifting dependent n-ary functions:
note that lift is a section of the lifted type family

> liftD : {n : Nat} ->
>         {B : NFun n KBase Type} ->
>         (f : NDFun n KBase B) ->
>         NDFun n KQuot (liftN B)
> liftD {n=Z}      {B} b = b
> liftD {n=(S n')} {B} f = \x => liftD {n=n'} {B=B (repr x)} (f (repr x)) 

For the lifting itself we don't need invariance of the type family!

towards generalizing the computation rule for NFun:

> kernel : {A, B : Type} -> (f : A -> B) -> BinRel A
> kernel f x y = f x = f y


But now we have to show things like
liftN (\x => \y => \z => x + y + z = x + (y + z))

is (homotopic to)
\x => \y => \z => (x `liftNOp (+)` y) `liftNOp (+)` z = x `liftNOp (+)` (y `liftNOp (+)` z)

we have 
liftNOp  = liftN . (nFunFmapB classOf)
liftN    = nFunFmap repr

so e.g.

liftNOp (+) = (liftN (nFunFmapB classOf (+)))
            = (liftN (compose [(+)] classOf))
            = ((nFunFmapA repr) (compose [(+)] classOf))
            = compose (spread 2 repr) (compose [(+)] classOf)

     ( so 
        liftNOp (+) x y =   classOf ((repr x) + (repr y))    )

so what we need to prove that the lift can be transported to
the "right" family, is

(x, y, z : KQuot) -> ((repr x + repr y) + repr z = repr x + (repr y + repr z)) = 
                     (classOf (repr (classOf (repr x + repr y)) + repr z) = 
                      classOf (repr x + repr (classOf (repr y + repr z))))

-- ingredients:

(T, T' : NOp n KBase ) -> relTT' : liftBinRelNFun (kernel normalize) (kernel normalize) T T' ->
   liftBinRelNFun (=) (=) (liftNOp T) (liftNOp T')

...



"computation rule"

 liftNFunComp : {n : Nat} -> {B : Type} -> 
                (f : NFun n KBase B) ->
                (fInv : isInvariantNFun (kernel normalize) (=) f) ->
                NDFun n KBase (NFun                


