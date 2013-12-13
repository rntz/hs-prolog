module Prolog where

import Control.Applicative
import Control.Monad

import Data.List
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Char
import qualified Data.Map as Map
import qualified Data.Set as Set

type Atom = String

data Decl = Decl { declName :: Atom
                 , declArgs :: [Term]
                 , declBody :: Query }
            deriving Show

data Query = Holds Atom [Term]
           | All [Query]
           | Any [Query]

data Term = Var String (Maybe Int)
          | App Atom [Term]

type DB = Map Atom [([Term], Query)]

instance Show Term where
    show (Var s i) = map Data.Char.toUpper s ++ post
        where post = maybe "" (("#" ++) . show) i
    show (App a []) = a
    show (App a ts) = a ++ "(" ++ intercalate ", " (map show ts) ++ ")"

instance Show Query where
    show (Holds a ts) = a ++ "(" ++ intercalate ", " (map show ts) ++ ")"
    show (All qs) = "ALL{" ++ intercalate ", " (map show qs) ++ "}"
    show (Any qs) = "ANY{" ++ intercalate ", " (map show qs) ++ "}"


-- Basic operations
initialize :: [Decl] -> DB
initialize decls = Map.map reverse $ foldl' add Map.empty decls
    where add db (Decl name args body) =
              Map.insertWith (++) name [(args,body)] db

queryFV :: Query -> Set String
queryFV (Holds _ xs) = Set.unions $ map termFV xs
queryFV (All xs) = Set.unions $ map queryFV xs
queryFV (Any xs) = Set.unions $ map queryFV xs

termFV :: Term -> Set String
termFV (Var x Nothing) = Set.singleton x
termFV (Var x _) = error "impossible"
termFV (App _ xs) = Set.unions $ map termFV xs


-- Backtracking search
type Subst = Map Int Term
data Search a = Search { runSearch :: (DB, Int, Subst) -> [(Int, Subst, a)] }

instance Functor Search where
    fmap f (Search s) = Search (map f' . s)
        where f' (i, sub, a) = (i, sub, f a)

instance Applicative Search where
    pure = return
    (<*>) = ap

instance Alternative Search where
    empty = Search (\_ -> [])
    Search f <|> Search g = Search (\x -> f x ++ g x)

instance Monad Search where
    return x = Search (\(db,i,subst) -> [(i,subst,x)])
    Search s >>= f = Search func
        where func x@(db,_,_) = do (i, subst, a) <- s x
                                   runSearch (f a) (db, i, subst)

instance MonadPlus Search where
    mzero = empty
    mplus = (<|>)


-- Helper functions
getDB :: Search DB
getSubst :: Search Subst
getI :: Search Int
getDB = Search (\(db,i,sub) -> [(i,sub,db)])
getSubst = Search (\(db,i,sub) -> [(i,sub,sub)])
getI = Search (\(db,i,sub) -> [(i,sub,i)])

choose :: [a] -> Search a
choose l = Search (\(_,i,sub) -> [(i,sub,a) | a <- l])

lookupAtom :: Atom -> Search ([Term], Query)
lookupAtom atom = do db <- getDB
                     choose $ Map.findWithDefault [] atom db

lookupVar :: Int -> Search (Maybe Term)
lookupVar i = do subst <- getSubst
                 return $ Map.lookup i subst


-- Performing queries
type Solution = Map String Term

query :: DB -> Query -> [Solution]
query db q = map getResult $ runSearch s (db, 0, Map.empty)
    where getResult (_, _, result) = result
          s = do (vars, [], q') <- uniqify [] q
                 search q'
                 subst <- getSubst
                 return $ solution subst vars

-- Uniqifies some terms and a query. Need to do both together for trying to
-- solve predicate invocations.
uniqify :: [Term] -> Query -> Search (Map String Int, [Term], Query)
uniqify ts q = Search func
    where
      func (_,i,sub) = [(i',sub,(m,ts',q'))]
          where (im',ts') = umap (i,Map.empty) id uniqTerm ts
                ((i',m),q') = uniqQuery im' q
      uniqQuery im (Any qs) = umap im Any uniqQuery qs
      uniqQuery im (All qs) = umap im All uniqQuery qs
      uniqQuery im (Holds p ts) = umap im (Holds p) uniqTerm ts
      uniqTerm (i,m) (Var s Nothing) =
          case Map.lookup s m of
            Nothing -> ((i+1, Map.insert s i m), Var s (Just i))
            Just j -> ((i,m), Var s (Just j))
      uniqTerm im (Var s _ ) = error "impossible"
      uniqTerm im (App p ts) = umap im (App p) uniqTerm ts
      umap im f g xs = (im', f xs')
          where (im',xs') = mapAccumL g im xs

-- Gets the solution for a uniqified query.
solution :: Subst -> Map String Int -> Solution
solution subst vars = Map.mapWithKey simplify vars
    where simplify name ident = simplifyTerm subst (Var name (Just ident))

simplifyTerm :: Subst -> Term -> Term
simplifyTerm sub (Var x Nothing) = error "impossible"
simplifyTerm sub v@(Var x (Just i)) =
    maybe v (simplifyTerm sub) $ Map.lookup i sub
simplifyTerm sub (App a ts) = App a $ map (simplifyTerm sub) ts

-- Solves a uniqified query
search :: Query -> Search ()
search (All qs) = mapM_ search qs
search (Any qs) = msum (map search qs)
--search (Any qs) = do q <- choose qs; search q
search (Holds a ts) = do (args, body) <- lookupAtom a
                         solve args body ts

-- Solves an un-uniqified query given its arguments and parameters to them.
solve :: [Term] -> Query -> [Term] -> Search ()
solve args query terms = do
  guard $ length args == length terms
  (_, args',query') <- uniqify args query
  zipWithM_ unify args' terms
  search query'

-- Unification!
-- TODO/FIXME: circularity checking
unify :: Term -> Term -> Search ()
unify (App a1 ts1) (App a2 ts2)
    | a1 == a2 = zipWithM_ unify ts1 ts2
    | otherwise = empty
-- unifying a variable with itself is a no-op
unify (Var _ (Just i)) (Var _ (Just j)) | i == j = return ()
unify (Var _ (Just i)) t = do
  x <- lookupVar i
  case x of
    Just vt -> unify t vt
    Nothing -> setVar i t
unify (Var _ Nothing) _ = error "impossible"
unify t v@Var{} = unify v t

setVar :: Int -> Term -> Search ()
setVar i t = Search func
    where func (db,j,subst) = [(j, Map.insert i term subst, ())]
              where term = simplifyTerm subst t


-- Some example terms, queries, and programs
var x = Var x Nothing

tNil = App "nil" []
tCons x y = App "cons" [x,y]
tList [] = tNil
tList (t:ts) = tCons t (tList ts)

tZero = App "z" []
tSuc x = App "s" [x]
tNat 0 = tZero
tNat n = tSuc (tNat (n-1))

qTrue = All []
qEq x y = Holds "eq" [x,y]

program :: [Decl]
program =
    [ Decl "eq" [var "x", var "x"] qTrue
    , Decl "isnil" [tNil] qTrue
    , Decl "len" [tNil, tZero] qTrue
    , Decl "len" [tCons (var "_") (var "x"),
                  tSuc (var "n")]
               (Holds "len" [var "x", var "n"])
    , Decl "append" [tNil, var "x", var "x"] qTrue
    , Decl "append" [tCons (var "x") (var "xs"), var "y",
                     tCons (var "x") (var "z")]
               (Holds "append" [var "xs", var "y", var "z"])
    ]

db = initialize program
