import Data.List            (union, (\\))
import Control.Monad        (when, liftM)
import Control.Monad.Except (throwError)

type Sym = String

data Exp =
      Var Sym
    | App Exp Exp
    | Lam Sym Type Exp
    | Pi  Sym Type Type
    | Kind Kinds
    deriving (Eq, Read, Show)

type Type = Exp

data Kinds =
      Star
    | Box
    deriving (Eq, Read, Show)

--redex
nf :: Exp -> Exp
nf ee = spine ee []
  where spine (App f a) as       = spine f (a:as)
        spine (Lam s t e) []     = Lam s (nf t) (nf e)
        spine (Lam s _ e) (a:as) = spine (subst s a e) as
        spine (Pi  s k t) as     = app (Pi s (nf k) (nf t)) as
        spine f as = app f as
        app f as = foldl App f (map nf as)

freeVars :: Exp -> [Sym]
freeVars (Var s) = [s]
freeVars (App f a)   = freeVars f `union` freeVars a
freeVars (Lam i t e) = freeVars t `union` (freeVars e \\ [i])
freeVars (Pi  i k t) = freeVars k `union` (freeVars t \\ [i])
freeVars (Kind _)    = []

subst :: Sym -> Exp -> Exp -> Exp
subst v x = sub
  where sub e@(Var i)   = if i == v then x else e
        sub (App f a)   = App (sub f) (sub a)
        sub (Lam i t e) = abstr Lam i t e
        sub (Pi  i k t) = abstr Pi  i k t
        sub (Kind k)    = Kind k
        fvx = freeVars x
        cloneSym e i = loop i
            where loop i' = if i' `elem` vars then loop (i ++ "'") else i'
                  vars = fvx ++ freeVars e
        abstr con i t e =
            if v == i then
                con i (sub t) e
            else if i `elem` fvx then
                let i' = cloneSym e i
                    e' = substVar i i' e
                in  con i' (sub t) (sub e')
            else
                con i (sub t) (sub e)

substVar :: Sym -> Sym -> Exp -> Exp
substVar s s' e = subst s (Var s') e

alphaEq :: Exp -> Exp -> Bool
alphaEq (Var v) (Var v') = v == v'
alphaEq (App f a) (App f' a') = alphaEq f f' && alphaEq a a'
alphaEq (Lam s t e) (Lam s' t' e') = alphaEq t t' && alphaEq e (substVar s' s e')
alphaEq (Pi  s k t) (Pi  s' k' t') = alphaEq k k' && alphaEq t (substVar s' s t')
alphaEq (Kind k) (Kind k') = k == k'
alphaEq _ _ = False

betaEq :: Exp -> Exp -> Bool
betaEq e1 e2 = alphaEq (nf e1) (nf e2)

--type check
initialEnv :: Env
initialEnv = Env []

newtype Env = Env [(Sym, Type)]
    deriving (Show)
type ErrorMsg = String
type TC a = Either ErrorMsg a

extend :: Sym -> Type -> Env -> Env
extend s t (Env r) = Env ((s, t) : r)

findVar :: Env -> Sym -> TC Type
findVar (Env r) s =
    case lookup s r of
        Just t -> return t
        Nothing -> throwError $ "Cannot find variable " ++ s

tCheck :: Env -> Exp -> TC Type
tCheck r (Var s) = findVar r s
tCheck r (App f a) = do
    tf <- tCheckRed r f
    case tf of
        Pi x at rt -> do
            ta <- tCheck r a
            when (not $ betaEq ta at) $ throwError "Bad function argument type"
            return $ subst x a rt
        _ -> throwError "Non-function in application"
tCheck r (Lam s t e) = do
    tCheck r t
    let r' = extend s t r
    te <- tCheck r' e
    let lt = Pi s t te
    tCheck r lt
    return lt
tCheck _ (Kind Star) = return $ Kind Box
tCheck _ (Kind Box)  = throwError "Found a Box"
tCheck r (Pi x a b) = do
    s <- tCheckRed r a
    let r' = extend x a r
    t <- tCheckRed r' b
    when ((s,t) `notElem` allowedKinds) $ throwError "Bad abstraction"
    return t

tCheckRed r e = liftM nf (tCheck r e)

allowedKinds :: [(Type, Type)]
allowedKinds =
    [ (Kind Star, Kind Star)  -- 0 values depend on values
    , (Kind Star, Kind Box )  -- 1 types  depend on values
    , (Kind Box , Kind Star)  -- 2 values depend on types
    , (Kind Box , Kind Box )] -- 4 types  depend on types
-- lambda cube
-- 0    0 simply typed lambda calculus
-- 01   1 dependent types
-- 0 2  2 system F
-- 012  3
-- 0  4 4
-- 01 4 5
-- 0 24 6 system Fω
-- 0124 7 calculus of constructions

typeCheck :: Exp -> Type
typeCheck e =
    case tCheck initialEnv e of
        Left msg -> error ("Type error:\n" ++ msg)
        Right t -> t

-- test
[z,s,m,n] = map (Var . (:[])) "zsmn"
app2 f x y = App (App f x) y
zero  = Lam "s" (Kind Star) $ Lam "z" (Kind Star) z
one   = Lam "s" (Kind Star) $ Lam "z" (Kind Star) $ App s z
two   = Lam "s" (Kind Star) $ Lam "z" (Kind Star) $ App s $ App s z
three = Lam "s" (Kind Star) $ Lam "z" (Kind Star) $ App s $ App s $ App s z
plus  = Lam "m" (Kind Star) $ Lam "n" (Kind Star) $ Lam "s" (Kind Star) $ Lam "z" (Kind Star) $ app2 m s (app2 n s z)
-- betaEq two $ app2 plus one one
-- >true


