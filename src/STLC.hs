{-# LANGUAGE TemplateHaskell #-}

module STLC
  ( -- * Types and expressions
    -- $typesAndExpressions
    Type (..),
    Expr (..),
    Ctx,
    (|>),
    check,

    -- * Normalization by substitution
    Sub,
    extSub,
    appSub,
    step,
    nbs,

    -- * Normalization by evalution
    Spine (..),
    Val (..),
    Env (..),
    (!),
    eval,
    quote,
    nbe,

    -- * Properties
    prop_NbsPreservesTypes,
    prop_NbePreservesTypes,
    prop_NbsEqNbe,

    -- * Finite types
    -- $finiteTypes
    Z,
    S (..),
    fromZ,
    fromS,
    Fin (..),
  )
where

import Control.Applicative (Alternative (..))
import Control.Enumerable
import Data.Coolean

-- $finiteTypes
--
-- Finite types are natural numbers which are bounded on the type level by a type-level natural number. We use finite types throughout this development to represent variables as deBruijn indices, to get a type of expressions which are well-scoped by construction.
--
-- Finite types can be encoded in Haskell '98 using a pair of datatypes, 'Z' and 'S', which represent the constructors of natural numbers on the type level. Together, these datatypes construct the number /bounding/ the finite type, e.g., @'S' ('S' 'Z')@ represents the number 2, and as a type it has two inhabitants, @'FZ'@ and @'FS' 'FZ'@, the numbers smaller than two.

-- | The empty type with zero inhabitants.
data Z
  deriving (Eq, Show)

-- | The successor type with one more inhabitant than its type argument /n/. For example, 'Z' has zero inhabitants, so @'S' 'Z'@ has one inhabitant, 'FZ', and @'S' ('S' 'Z')@ has two inhabitants, 'FZ' and @'FS' 'FZ'@, /etc./
data S n
  = FZ
  | FS n
  deriving (Eq, Functor)

-- | The eliminator for the empty type.
fromZ :: Z -> a
fromZ n = case n of -- No inhabitants, no cases

-- | The eliminator for the successor type.
fromS :: a -> (n -> a) -> (S n -> a)
fromS fz fs FZ = fz
fromS fz fs (FS n) = fs n

-- | The class of finite types, which can be converted to positive integers using the 'toInt' function.
class Fin n where
  toInt :: n -> Int

instance Fin Z where
  toInt = fromZ

instance Fin n => Fin (S n) where
  toInt = fromS 0 (succ . toInt)

-- | NOTE: we print finite types as numbers via the 'toInt' function of the 'Fin' class.
instance Fin n => Show (S n) where
  show = show . toInt

instance Enumerable Z where
  enumerate = share . aconcat $ []

instance Enumerable n => Enumerable (S n) where
  enumerate = share . aconcat $ [c0 FZ, c1 FS]

-- $typesAndExpressions

-- | The type of simple types.
data Type
  = -- | The atomic type, usually called "ι", which has no inhabitants.
    Iota
  | -- | The function type.
    Type :-> Type
  deriving (Eq, Show)

deriveEnumerable ''Type

-- | The type of expressions with /i/ free variables. Commonly, /i/ will be instantiated with a finite type, e.g., @'Expr' ('S' ('S' 'Z'))@ is the type of expressions with two free variables, @'FZ'@ and @'FS' 'FZ'@. These finite types are interpreted as deBruijn indices, which means that @'Var' 'FZ'@ is the variable bound by the nearest binder, @'Var' ('FS' 'FZ')@ is the variable bound by the bound or one up, /etc./
data Expr i
  = -- | A variable.
    Var i
  | -- | A lambda binder.
    --
    --   The body has one additional variable, bound by this lambda, which is reflected in its type, @'Expr' ('S' i)@.
    Lam (Expr (S i))
  | -- | An application.
    --
    --   Applications store the type of the argument so that type checking can be parallelized, i.e., it can immediately recur into both sub-expressions, rather than having to first infer the type of the argument.
    App (Expr i) (Expr i) Type
  deriving (Eq, Show, Functor)

deriveEnumerable ''Expr

-- Type Checking

-- | Typing contexts are total maps from the deBruijn indices to types.
type Ctx i = i -> Type

-- | Extend a type context with one additional type.
(|>) :: Ctx i -> Type -> Ctx (S i)
(|>) ctx a = fromS a ctx

-- | Check if an expression has the given type under the given typing context. The algorithm is straightforward, modulo the conversion between 'Bool' and concurrent booleans, i.e., 'Cool', which is omitted here:
--
-- > check ctx a         (Var i)       = a == ctx i
-- > check ctx (a :-> b) (Lam e)       = check (ctx |> a) b e
-- > check ctx _         (Lam e)       = False
-- > check ctx b         (App e1 e2 a) = check ctx (a :-> b) e1 && check ctx a e2
check :: Ctx i -> Type -> Expr i -> Cool
check ctx a (Var i) = toCool (a == ctx i)
check ctx (a :-> b) (Lam e) = check (ctx |> a) b e
check ctx _ (Lam e) = false
check ctx b (App e1 e2 a) = check ctx (a :-> b) e1 &&& check ctx a e2

-- * Normalization by Substitution

type Sub i j = i -> Expr j

extSub :: Sub i j -> Sub (S i) (S j)
extSub s = fromS (Var FZ) (fmap FS . s)

appSub :: Sub i j -> Expr i -> Expr j
appSub s = \case
  Var i -> s i
  Lam e -> Lam (appSub (extSub s) e)
  App e1 e2 t -> App (appSub s e1) (appSub s e2) t

pattern Red :: Expr (S i) -> Expr i -> Type -> Expr i
pattern Red e1 e2 t = App (Lam e1) e2 t

step :: Expr i -> Maybe (Expr i)
step = \case
  Var n -> empty
  Lam e -> Lam <$> step e
  Red e1 e2 t -> pure (appSub (fromS e2 Var) e1)
  App e1 e2 t ->
    (App <$> step e1 <*> pure e2 <*> pure t)
      <|> (App e1 <$> step e2 <*> pure t)

nbs :: Expr i -> Expr i
nbs e = maybe e nbs (step e)

-- Normalization by Evaluation

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
env :> v ! FZ = v
env :> v ! FS i = env ! i

eval :: Env i j -> Expr i -> Val j
eval env = \case
  Var i -> env ! i
  Lam e -> VLam env e
  App e1 e2 t -> evalApp (eval env e1) (eval env e2) t

evalApp :: Val j -> Val j -> Type -> Val j
evalApp (VVar j sp) v t = VVar j (SApp sp v t)
evalApp (VLam env e) v t = eval (env :> v) e

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

-- Tests

prop_NbsPreservesTypes :: Expr Z -> Cool
prop_NbsPreservesTypes e = check fromZ (Iota :-> Iota) e ==> check fromZ (Iota :-> Iota) (nbs e)

prop_NbePreservesTypes :: Expr Z -> Cool
prop_NbePreservesTypes e = check fromZ (Iota :-> Iota) e ==> check fromZ (Iota :-> Iota) (nbs e)

prop_NbsEqNbe :: Expr Z -> Cool
prop_NbsEqNbe e = check fromZ (Iota :-> Iota) e ==> nbs e == nbe e