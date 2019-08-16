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
    | Type
    | Kind deriving (Eq, Ord)

instance Show Term where
    show (Abs t t') = "[λ" ++ (show t) ++ ". " ++ (show t') ++ "]"
    show (Pi n t t') = "π (" ++ ((show n) ++ ":" ++ (show t)) ++ ") -> " ++ show t'
    show (App t t') = "(" ++ show t ++ " " ++ show t' ++ ")"
    show (Var x _) = show x 
    show Type = "*"
    show Kind = "Kind"

type Local_env = Map Term Term
type Definitions_env = Map Term Term
type Lambda_vars = Local_env
type Name_env = Map VarUnit VarUnit
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
 ---   PMatch var type' matchs -> do
    --    let n = to_symbolic_structural type' (s, v)
      --  let tr = Prelude.map (\(x, y) -> (x, to_symbolic_structural y (s, v))) matchs
       -- PMatch var n tr 

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
 --   PMatch var type' matchs -> do
   --     let n = (pure_structural )

    PValue k -> (s, PValue k)

untyped_parsedTerm (PAbs v y) = Abs (Var v Lambda_Abstraction) (untyped_parsedTerm y)
untyped_parsedTerm (PType v y y') = Pi (Var v Pi_Abstraction) (untyped_parsedTerm y)  (untyped_parsedTerm y')
untyped_parsedTerm (PApp y y') = App (untyped_parsedTerm y) (untyped_parsedTerm y')
untyped_parsedTerm (PValue (VarName "Type")) = Type
untyped_parsedTerm (PValue (VarName "Kind")) = Kind
untyped_parsedTerm (PValue k) = (Var k Bound_Free)

getTermsByAst (AST k) s = s_continuation k s -- Seems like i have to face somes design problemas so this function solves *com gambiarra*
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