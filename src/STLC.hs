{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK prune #-}

module STLC
  ( -- * Variables and finite types
    -- $finiteTypes
    Z,
    S (..),

    -- * Types and expressions
    -- $typesAndExpressions
    Type (..),
    Expr (..),
    Ctx,
    (|>),
    check,

    -- * Normalization by substitution
    -- $normalizationBySubstitution
    Sub,
    ext,
    sub,
    sub0,
    pattern Red,
    step,
    nbs,

    -- * Normalization by evalution
    -- $normalizationByEvaluation
    Spine (..),
    Val (..),
    Env (..),
    (!),
    eval,
    quote,
    nbe,

    -- * Properties
    -- $properties
    prop_NbsPreservesTypes,
    prop_NbePreservesTypes,
    prop_NbsEqNbe,
  )
where

import Control.Enumerable
import Data.Coolean (Cool, Coolean (toCool), false, (&&&), (==>))

-- $finiteTypes
--
-- This section implements finite types, which we will use to represent variables in deBruijn notation.
--
-- Finite types are a family of types which represent the natural numbers smaller than some number /n/.
-- Finite types can be encoded in Haskell '98 using a pair of datatypes, 'Z' and 'S', which represent the number 0 and the successor function.
-- These are used to represent the number /bounding/ the finite type, /e.g./, @('S' ('S' 'Z'))@ represents the number 2, and as such it is the type of all natural numbers smaller than 2, /i.e./, 0 and 1, or 'FZ' and @('FS' 'FZ')@.

-- | The type of natural numbers smaller than 0.
--
--   There are no such numbers, so there are no values of type 'Z'.
data Z
  deriving (Eq, Ord, Show)

-- | The type of natural numbers smaller than @n + 1@..
--   For example:
--
--   * There are no values of type 'Z'.
--   * There is one value of type @('S' 'Z')@, 'FZ'.
--     We cannot use 'FS' at this type, as it needs an argument of type 'Z'.
--   * There are two values of type @('S' ('S' 'Z'))@, 'FZ' and @('FS' 'FZ')@.
--     We /can/ use 'FS' at this type, as it needs an argument of type @('S' 'Z')@, and there is one such value, 'FZ'.
--   * /Etc./
data S n
  = -- | The number @0@.
    FZ
  | -- | The successor function. @('FS' n)@ represents @(n + 1)@.
    FS n
  deriving (Eq, Ord, Functor)

-- | The eliminator for the empty type.
fromZ :: Z -> a
fromZ n = case n of -- No inhabitants, no cases

-- | The eliminator for the successor type.
fromS :: a -> (n -> a) -> (S n -> a)
fromS fz _ FZ = fz
fromS _ fs (FS n) = fs n

-- | This instance is needed to satisfy instant search, but it implements no functions.
instance Num Z

-- | This instance is needed to satisfy the superclass constraint on 'Integral', but it implements no functions.
instance Real Z

-- | This instance is needed to satisfy the superclass constraint on 'Integral', but it implements no functions.
instance Enum Z

-- | This instance is needed to satisfy instant search, but it implements no functions.
instance Integral Z

-- | This instance allows us to write deBruijn indices using numbers.
--   However, writing indices that are out of scope results in a runtime error.
--   It only implements 'fromInteger'.
instance Num n => Num (S n) where
  fromInteger 0 = FZ
  fromInteger n = FS (fromInteger (n - 1))

-- | This instance is needed to satisfy the superclass constraint on 'Integral', but it implements no functions.
instance Real n => Real (S n)

-- | This instance is needed to satisfy the superclass constraint on 'Integral', but it implements no functions.
instance Enum n => Enum (S n)

-- | This instance allows us to convert deBruijn indices to integers.
--   It only implements 'toInteger'.
instance Integral n => Integral (S n) where
  toInteger = fromS 0 ((+ 1) . toInteger)

-- | This instance shows deBruijn indices as numbers using 'toInteger'.
instance Integral n => Show (S n) where
  show = show . toInteger

instance Enumerable Z where
  enumerate = share . aconcat $ []

instance Enumerable n => Enumerable (S n) where
  enumerate = share . aconcat $ [c0 FZ, c1 FS]

-- $typesAndExpressions
--
-- This section implements simple types and well-scoped by construction expressions, as well as a simple type checker which we will use to generate well-typed expressions the [lazy-search](https://hackage.haskell.org/package/lazy-search) package.

-- | The type of simple types.
data Type
  = -- | The atomic type, usually called "ι", which has no inhabitants.
    Iota
  | -- | The function type.
    Type :-> Type
  deriving (Eq, Show)

deriveEnumerable ''Type

-- | The type of expressions with @i@ free variables.
--
--   We instantiate @i@ with a finite type which representing the number of free variables, /e.g./, @'Expr' ('S' ('S' 'Z'))@ is the type of expressions with two free variables.
--   That way, when we construct a variable using 'Var', we only have @i@ options, and they all refer to one of the free variables.
--   These finite types are interpreted as deBruijn indices, which means that an index @i@ refer to the @i@/th/ lambda you encounter when traversing the expression.
--   For example:
--
--   +---------------------------+---------------------------+--------------------------+-------------------------------------+
--   | Haskell expression        | \(\lambda\)-expression    | using DeBruijn notation  | as value of type @'Expr' 'Z'@       |
--   +===========================+===========================+==========================+=====================================+
--   | @\\x -> x@                | \(\lambda x.x\)           | \(\lambda.0\)            | @'Lam' ('Var' 'FZ')@                |
--   +---------------------------+---------------------------+--------------------------+-------------------------------------+
--   | @\\x -> \\y -> x@         | \(\lambda x.\lambda y.x\) | \(\lambda.\lambda.1\)    | @'Lam' ('Lam' ('Var' ('FS' 'FZ')))@ |
--   +---------------------------+---------------------------+--------------------------+-------------------------------------+
data Expr i
  = -- | A variable.
    Var i
  | -- | A lambda binder.
    --
    --   The body has one additional variable, bound by this lambda, which is reflected in its type, @'Expr' ('S' i)@.
    Lam (Expr (S i))
  | -- | An application.
    --
    --   Function applications store the type of their argument so that type checking can be parallelized, /i.e./, in the case for 'App', 'check' can immediately recur into both sub-expressions, rather than having to 1/st/ infer the type of the argument. This is important for efficient enumeration using the [lazy-search](https://hackage.haskell.org/package/lazy-search-0.1.2.1) package.
    App (Expr i) (Expr i) Type
  deriving (Eq, Show, Functor)

deriveEnumerable ''Expr

-- | The type of typing contexts.
--
--   Typing contexts are total maps from the deBruijn indices to types.
type Ctx i = i -> Type

-- | Extend a typing context with an additional type, mapped to the 0/th/ variable.
--
-- > (ctx |> a) FZ     = a
-- > (ctx |> a) (FS i) = ctx i
(|>) :: Ctx i -> Type -> Ctx (S i)
(|>) = flip fromS

-- | Check if an expression has the given type under the given typing context. The algorithm is straightforward, modulo the conversion between 'Bool' and concurrent booleans, /i.e./, 'Cool', which is omitted here:
--
-- > check ctx a         (Var i)       = a == ctx i
-- > check ctx (a :-> b) (Lam e)       = check (ctx |> a) b e
-- > check ctx _         (Lam e)       = False
-- > check ctx b         (App e1 e2 a) = check ctx (a :-> b) e1 && check ctx a e2
check :: Ctx i -> Type -> Expr i -> Cool
check ctx a (Var i) = toCool (a == ctx i)
check ctx (a :-> b) (Lam e) = check (ctx |> a) b e
check _ _ (Lam _) = false
check ctx b (App e1 e2 a) = check ctx (a :-> b) e1 &&& check ctx a e2

-- $normalizationBySubstitution

-- | The type of substitutions from expressions with @i@ free variables to expressions with /j/ free variables.
--
--   Substitutions are total maps from deBruijn indices bound by @i@ to expressions with /j/ free variables.
type Sub i j = i -> Expr j

-- | Extend a substitution with another variable, which is mapped to itself.
ext :: Sub i j -> Sub (S i) (S j)
ext s = fromS (Var FZ) (fmap FS . s)

-- | Apply a substitution to an expression.
sub :: Sub i j -> Expr i -> Expr j
sub s = \case
  Var i -> s i
  Lam e -> Lam (sub (ext s) e)
  App e1 e2 t -> App (sub s e1) (sub s e2) t

-- | Replace all occurrences of the 0/th/ variable in the 2/nd/ expression with the 1/st/ expression. For example:
--
-- >>> let e1 = Lam (Var 0)
-- >>> let e2 = App (Var 0) (Lam (App (Var 1) (Var 0) Iota)) Iota
-- >>> sub0 @Z e1 e2
-- App (Lam (Var 0)) (Lam (App (Lam (Var 0)) (Var 0) Iota)) Iota
sub0 :: Expr i -> Expr (S i) -> Expr i
sub0 e = sub (fromS e Var)

-- | The pattern of redexes, /i.e./, \((\lambda x.e_1)\;e_2\) or @'App' ('Lam' e1) e2 t@.
pattern Red :: Expr (S i) -> Expr i -> Type -> Expr i
pattern Red e1 e2 t = App (Lam e1) e2 t

-- | Reduce the expression by one step, and return 'Just' the result. If no redex exists, return 'Nothing'.
--
--   The algorithm can be written as follows, using idiom brackets:
--
-- > step (Var n)       = Nothing
-- > step (Lam e)       = ⟦ Lam (step e) ⟧
-- > step (Red e1 e2 t) = ⟦ sub (fromS e2 Var) e1 ⟧
-- > step (App e1 e2 t) = ⟦ App (step e1) e2 t ⟧ <|> ⟦ App e1 (step e2) t ⟧
step :: Expr i -> Maybe (Expr i)
step = \case
  Var _ -> empty
  Lam e -> Lam <$> step e
  Red e1 e2 _ -> pure (sub (fromS e2 Var) e1)
  App e1 e2 t ->
    (App <$> step e1 <*> pure e2 <*> pure t)
      <|> (App e1 <$> step e2 <*> pure t)

-- | Reduce the expression using 'step' until no more redexes exist.
--
--   Implements normalization by substitution.
nbs :: Expr i -> Expr i
nbs e = maybe e nbs (step e)

-- $normalizationByEvaluation

data Spine i
  = SId
  | SApp (Spine i) (Val i) Type

deriving instance Functor Spine

data Val j
  = VVar j (Spine j)
  | forall i. VLam (Env i j) (Expr (S i))

deriving instance Functor Val

data Env i j where
  Nil :: Env Z j
  (:>) :: Env i j -> Val j -> Env (S i) j

deriving instance Functor (Env i)

(!) :: Env i j -> i -> Val j
Nil ! i = fromZ i
_ :> v ! FZ = v
env :> _ ! FS i = env ! i

eval :: Env i j -> Expr i -> Val j
eval env = \case
  Var i -> env ! i
  Lam e -> VLam env e
  App e1 e2 t -> evalApp (eval env e1) (eval env e2) t

evalApp :: Val j -> Val j -> Type -> Val j
evalApp (VVar j sp) v t = VVar j (SApp sp v t)
evalApp (VLam env e) v _ = eval (env :> v) e

quote :: Val j -> Expr j
quote = \case
  VVar i sp -> quoteSpine (Var i) sp
  VLam env e -> Lam (quote (eval ((FS <$> env) :> VVar FZ SId) e))

quoteSpine :: Expr j -> Spine j -> Expr j
quoteSpine e = \case
  SId -> e
  SApp sp v t -> App (quoteSpine e sp) (quote v) t

nbe :: Expr Z -> Expr Z
nbe e = quote (eval @Z @Z Nil e)

-- $properties

prop_NbsPreservesTypes :: Expr Z -> Cool
prop_NbsPreservesTypes e = check fromZ (Iota :-> Iota) e ==> check fromZ (Iota :-> Iota) (nbs e)

prop_NbePreservesTypes :: Expr Z -> Cool
prop_NbePreservesTypes e = check fromZ (Iota :-> Iota) e ==> check fromZ (Iota :-> Iota) (nbs e)

prop_NbsEqNbe :: Expr Z -> Cool
prop_NbsEqNbe e = check fromZ (Iota :-> Iota) e ==> nbs e == nbe e
