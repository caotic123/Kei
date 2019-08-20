module KeiTerms where
import Data.Maybe
import Data.Map as Map
import Kei_parser

data VarLocally = Bound_Free | Lambda_Abstraction | Pi_Abstraction | RewriteConst | Function_Abstraction | Const deriving Show

instance Eq VarLocally where
    (==) _ _ = True

instance Ord VarLocally where
    compare _ _ = EQ

data Term = 
      Var VarUnit VarLocally
    | Abs Term Term 
    | App Term Term
    | Pi Term Term Term
    | Match Term Term [(Term, Term)] 
    | Type
    | Kind deriving (Eq, Ord)

type Local_env = Map Term Term
type Definitions_env = Map Term Term
type Lambda_vars = Local_env
type Name_env = Map VarUnit VarUnit

foldr_f :: (a -> Term -> a) -> a -> Term -> a
foldr_f f k x = case x of
    Pi n x' y' -> (foldr_f f (foldr_f f (f k (Pi n x' y')) y') x')
    Abs x y ->  (foldr_f f (f k (Abs x y)) y)
    App t t' -> foldr_f f (foldr_f f (f k (App t t')) t) t'
    Var t' x -> f k (Var t' x)
    Match matched type' k' ->  do
        let x' = (foldr_f f (foldr_f f (f k (Match matched type' k')) matched) type')
        Prelude.foldr (\(_, x) -> \y -> foldr_f f y x) x' k'
    Type -> f k Type
    Kind -> f k Kind

apply_f f x = case x of
    Pi n x' y' -> f (Pi n (apply_f f x') (apply_f f y')) 
    Abs x' y ->  f (Abs x' (apply_f f y))
    App t t' -> f (App (apply_f f t) (apply_f f t'))
    Var t' x -> f (Var t' x)
    Match matched type' k' -> do
        let expr' = Prelude.map (\(x, y) -> (x, apply_f f y)) k' 
        Match (apply_f f matched) (apply_f f type') expr'
    Type -> f Type
    Kind -> f Kind

instance Show Term where
    show (Abs t t') = "[λ" ++ (show t) ++ ". " ++ (show t') ++ "]"
    show (Pi n t t') = "π (" ++ ((show n) ++ ":" ++ (show t)) ++ ") -> " ++ show t'
    show (App t t') = "(" ++ show t ++ " " ++ show t' ++ ")"
    show (Match t t' ts) = do
        (show t) ++ " -> \n{" ++ (Prelude.foldl (\y -> \(x, x') -> "|" ++ (show x) ++ " -> " ++ (show x') ++ "  " ++ y) "" ts) ++ "}\n"
    show (Var x _) = show x 
    show Type = "*"
    show Kind = "Kind"

data Context = Context {term :: Term, local :: Local_env, lambda_var :: Lambda_vars} deriving Show

data Definition = Definition Term Term deriving (Show, Eq, Ord)
data TypedT  = Typed PTerm PTerm deriving Show

to_symbolic_structural :: PTerm -> (VarUnit, VarUnit) -> PTerm
to_symbolic_structural pk (s, v) = case pk of
    PValue k -> if k == s then PValue v else PValue k
    PAbs k t ->  if k == s then PAbs k t else PAbs k (to_symbolic_structural t (s, v))
    PType k t t' -> if k == s then PType k t t' else (PType k (to_symbolic_structural t (s, v)) (to_symbolic_structural t' (s, v)))
    PApp k k' ->
        PApp (to_symbolic_structural k (s, v)) (to_symbolic_structural k' (s, v))
    PMatch term type' matchs -> do
        let n = to_symbolic_structural type' (s, v)
        let tr = Prelude.map (\(x, y) -> (x, to_symbolic_structural y (s, v))) matchs
        PMatch (to_symbolic_structural term (s, v)) n tr 

pure_structural :: Symbol -> PTerm -> (Symbol, PTerm)
pure_structural s t = case t of
    PAbs u y -> do
        let structured_substituition = to_symbolic_structural y (u, VarSimbol (Next s) u)
        let (s', y) = pure_structural (Next s) structured_substituition
        (s', PAbs (VarSimbol (Next s) u) y)
    PType u t t' -> do
        let structured_substituition = to_symbolic_structural t (u, VarSimbol (Next s) u)
        let (s1, y) = pure_structural (Next s) structured_substituition 
        let structured_substituition' = to_symbolic_structural t' (u, VarSimbol (Next s) u)
        let (s2, y') = pure_structural s1 structured_substituition'
        (s2, PType (VarSimbol (Next s) u) y y')
    PApp k k' -> do
        let (s1, y) = (pure_structural s k) 
        let (s2, y') = (pure_structural s1 k') 
        (s2, PApp y y')
    PMatch value type' k -> do
       let (s1, type'') = pure_structural s type'
       let (s2, value') = pure_structural s1 value 
       let (purity_terms, s3) = pure_match (Next s2) k
       let (k', s4) = symbolic_match_op purity_terms s3
       (s4, PMatch value' type'' k' )
    PValue k -> (s, PValue k)

    where  -- very imperative this piece of code :c a ideia is substitute to a monad with a state of the current symbol
        symbolic_match (var : xs) s' = do
            let (xs', s) = symbolic_match xs (Next s')
            ((VarSimbol s' var) : xs', s)
        symbolic_match [] s = ([], s)
        symbolic_match_op (((vars, pred), term) : xs) s' = do
            let (ls, s) =  (symbolic_match vars s')
            let (ts, s'') = symbolic_match_op xs s
            let term_pred = Prelude.foldl (\x -> \(VarSimbol sim' u) -> to_symbolic_structural x (u, (VarSimbol sim' u))) pred ls
            let term_symb = Prelude.foldl (\x -> \(VarSimbol sim' u) -> to_symbolic_structural x (u, (VarSimbol sim' u))) term ls
            (((ls, term_pred), term_symb) : ts , s'')
        symbolic_match_op [] s' = ([], s')
        pure_match s (((vars, pred), term) : xs) = do
            let (s1, term0) = pure_structural s term
            let (v, s2) = pure_match s1 xs
            (((vars, pred), term0) : v, s2) -- s ....1000 lah this seriously should be a state monad
        pure_match s [] = ([], s)

untyped_parsedTerm (PAbs v y) = Abs (Var v Lambda_Abstraction) (untyped_parsedTerm y)
untyped_parsedTerm (PType v y y') = Pi (Var v Pi_Abstraction) (untyped_parsedTerm y)  (untyped_parsedTerm y')
untyped_parsedTerm (PApp y y') = App (untyped_parsedTerm y) (untyped_parsedTerm y')
untyped_parsedTerm (PValue (VarName "Type")) = Type
untyped_parsedTerm (PValue (VarName "Kind")) = Kind
untyped_parsedTerm (PMatch matched type' k) = do
    let pair' = Prelude.map (\((vars, pred), term) -> (untyped_parsedTerm pred, untyped_parsedTerm term)) k
    Match (untyped_parsedTerm matched) (untyped_parsedTerm type') pair'
untyped_parsedTerm (PValue k) = (Var k Bound_Free)

getTermsByAst (AST k) s = s_continuation k s -- i had to to face somes design problemas so this function solves *com gambiarra*
 where 
    s_continuation y k = case y of
        ((FuncDef (Def name (Function t' t))) : xs) -> do
                let (s', term) = pure_structural k t
                let (s_, term') = pure_structural s' t'
                let (v, ls) = s_continuation xs s_
                (v, Typed term term' : ls)
        x : xs -> s_continuation xs k 
        [] -> (k, [])

getTermVarNameByAst (AST k) = Prelude.foldr (\x -> \y -> case x of
    (FuncDef (Def name (Function t' t))) -> (Var (VarName name) Function_Abstraction) : y
    _ -> y
    ) [] k

getTermsType contexts = case contexts of
    (Context term local _) : xs -> fromJust (Map.lookup term local) : getTermsType xs
    [] -> []