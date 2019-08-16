module Main where
import KeiTerms
import Kei_parser
import KeiRules
import KeiNormalization
import Data.Map as Map

data Jugdment = TypeJudge Term Term
type LambdaDef = Map Term Context
data GlobalContext  = GlobalContext {context :: [Context], rules :: Rule, context_def :: Definitions_env, lambda_def :: LambdaDef} deriving Show
data TypeErrors = TypeError Term String deriving Show
data State = State GlobalContext [TypeErrors] deriving Show
type CContext = (Context, State)

formalize_terms :: Local_env -> TypedT -> Lambda_vars -> Context
formalize_terms y k args =
    case k of
        (Typed (PAbs k by) (PType u q q')) -> do 
            let untyped_term = Abs (Var k Lambda_Abstraction) (untyped_parsedTerm by)
            let (Pi name type_var term_dependent) = untyped_parsedTerm (PType u q q')
            let (pi_premisse, names) = decompose_types_assumptions' untyped_term (Pi name type_var term_dependent) y args
            let env = do
                let v = insert untyped_term (Pi (Var u Pi_Abstraction) (untyped_parsedTerm q) (untyped_parsedTerm q')) pi_premisse
                (insert (Var k Lambda_Abstraction) (untyped_parsedTerm q) (insert name type_var v))
            Context untyped_term env (insert (Var k Lambda_Abstraction) (Var u Pi_Abstraction) names)
        (Typed (PValue k) f) -> do
            let t = untyped_parsedTerm (PValue k)
            Context t (insert t (untyped_parsedTerm f) y) args
        (Typed (PApp k y') f) -> do
            let t = untyped_parsedTerm (PApp k y')
            Context t  (insert t (untyped_parsedTerm f) y) args
        (Typed (PType k y1 y2) f) -> do
            let (Pi x type_t term_dependent) = untyped_parsedTerm (PType k y1 y2)
            let pi_premisse = decompose_types_assumptions (Pi x type_t term_dependent) y -- every pi type has a premisse that x carry a T type/kind.
            Context (Pi x type_t term_dependent) (insert (Pi x type_t term_dependent) (untyped_parsedTerm f) pi_premisse) args

getLocalContexts :: [TypedT] -> [Context]
getLocalContexts (x : xs) = do
    formalize_terms empty x empty : (getLocalContexts xs)
getLocalContexts [] = []

getGlobalContext :: AST -> GlobalContext
getGlobalContext k = do
   let (uniquess_symbol, terms) = (getTermsByAst k Initial)
   let locals = getLocalContexts terms
   let (_, rules) = get_rules_typed_context (getRulesByAst k) uniquess_symbol
   let funcs = fromList (zip (getTermVarNameByAst k) locals) 
   let local_def_types = fromList (zip (getTermVarNameByAst k) (getTermsType locals))

   let def_env = union (union (getDefRulesEnviroment (toList rules)) (fromList [(Kind, Kind), (Type, Kind)])) local_def_types 
   GlobalContext locals rules def_env funcs

getCTerm (k, y) = do
    let (Context term local lambda_var) = k
    term

getLocalContext (k, y) = do
    let (Context term local lambda_var) = k
    local

getListErros :: CContext -> [TypeErrors]
getListErros (_, (State _ y)) = y

getEnvDef :: CContext -> Definitions_env
getEnvDef (k, State (GlobalContext _ _ env_def lambdas) er) = env_def

getTermFromLambdaDefs term' (GlobalContext _ _ def_env lambdas) = Map.lookup term' lambdas

mapContext (Context term' local vars') f = (Context term' (Map.map f local) vars')

get_type :: Term -> CContext -> Maybe Term
get_type term' cc = case (get_type' term') of
    Just x -> Just x
    Nothing -> get_type' (normalize_term' term' cc) --if don't the type try normalizing the type
  where
    get_type' term' = case (Map.lookup term' (getLocalContext cc)) of
        Just x -> Just x
        Nothing -> case (Map.lookup term' (getEnvDef cc)) of
            Just x -> Just x
            Nothing -> Nothing

pushTypeError bad_typed (State t ts) = (State t (bad_typed : ts))
pushTypeError' (k, (State t ts)) bad_typed = (k, (State t (bad_typed : ts)))
pushLeakType (k, (State t ts)) bad_typed helper = (k, (State t (TypeError bad_typed ("The term " ++ (show bad_typed) ++ " leaks of type term" ++ " in " ++ (show helper)) : ts)))

unionContext (Context term local vars) (Context _ local' vars') = do
    Context term (union local local') (union vars vars')

assert_local :: Jugdment -> CContext -> Term -> CContext
assert_local (TypeJudge term type') cc helper = do
   let type_error k = TypeError term ("The term " ++ (show term) ++ " should be a type " ++ (show (pi_lambda_substituion type' cc)) ++ " instead of " ++ (show (pi_lambda_substituion k cc)) ++ " where " ++ show helper ++ " is your jugdment")
   case (get_type term cc) of
       Just k -> do
        let normalized_term1 = normalize_term' k cc
        let normalized_term2 = normalize_term' type' cc
        if k == type' || normalized_term1 == normalized_term2 || (pi_equality (pi_lambda_substituion normalized_term1 cc, pi_lambda_substituion normalized_term2 cc)) then cc
        else pushTypeError' cc (type_error k)
       Nothing -> pushLeakType cc term helper

get_rules_typed_context :: [RewriteRule] -> Symbol -> (Symbol, Rule)
get_rules_typed_context r s = case r of
    ((RewriteRule x y) : xs) -> do
        let (s', t) = pure_structural s y
        let (s, map') = get_rules_typed_context xs s'
        let rule_typed = formalize_terms empty (Typed t (PValue (VarName "Type"))) empty
        (s, insert x rule_typed map')
    [] -> (s, empty)

is_strong_normalized :: State -> Term -> Bool
is_strong_normalized (State cc e) c = foldr_f (\x -> \y ->
    case (getTermFromLambdaDefs y cc) of
        Just x' -> False 
        Nothing -> x) True c

strong_normalize :: Term -> Term
strong_normalize c 
 | check_normalized c = c
 | otherwise = strong_normalize (apply_f (\x -> case x of
    (App (Abs x y) t) -> beta_reduction (App (Abs x y) t) 
    _ -> x) c)
  where 
    check_normalized = foldr_f (\x -> \y ->
        case y of
            App (Abs _ _) (Var (VarSimbol _ _) _) -> False
            _  -> x) True

change_local :: (Term, Term) -> CContext -> CContext 
change_local (t, t') ((Context term' local lambda_vars), k) = ((Context term' (insert t t' local) lambda_vars), k)
--context_strong_normalized :: CContext -> Bool
--context_strong_normalized (c, (State cc e)) = fold (\x -> \y -> (is_strong_normalized (x, (State cc e))) && y) True (toList (local c)) 

substitute_definitions :: CContext -> CContext -- Trying get normal terms from the context is a way of obtain sucessuful typed conversion equality
substitute_definitions (c, (State cc e)) 
  | not (is_strong_normalized (State cc e) (term c)) = substitute_definitions ((substitute_terms c (term c)), (State cc e))
  | otherwise = (c, (State cc e)) 
  where 
    substitute_terms = foldr_f (\x -> \y ->
        case (getTermFromLambdaDefs y cc) of
            Just x' -> unionContext (substitute_env_vars x y (term x')) x'
            Nothing -> x)
    substitute_env_vars (Context x y' z) y t' = (Context (apply_f (\x -> if x == y then t' else x) x) y' z)

normalize_term' :: Term -> CContext-> Term -- Trying get normal terms from the context is a way of obtain sucessuful typed conversion equality
normalize_term' term' (context, (State cc e)) = (substitute_terms term')
  where 
    substitute_terms =
        apply_f (\y -> case y of
            App x' y' -> case (getTermFromLambdaDefs x' cc) of
                Just (Context t local vars) -> do
                    let (t0, _) = substitute_definitions ((Context (App t y) local vars), (State cc e))
                    strong_normalize (term t0)
                Nothing -> y
            _ -> y)

pi_uniquiness :: Term -> Symbol -> Term
pi_uniquiness (Pi (Var (VarSimbol x y) l) t t') s = do
    let v = (Var (VarSimbol x y) l) 
    Pi (Var (VarSimbol s y) l) t (apply_f (\x -> if x == v then (Var (VarSimbol s y) l) else x) (pi_uniquiness t' (Next s)))
pi_uniquiness (Abs k y) s = Abs k (pi_uniquiness y s)
pi_uniquiness (App t t') s = App (pi_uniquiness t s) (pi_uniquiness t' s)
pi_uniquiness (Var k x) s = (Var k x)
pi_uniquiness Type s = Type
  
pi_equality :: (Term, Term) -> Bool
pi_equality (t, x) = do
    let b = Initial
    pi_uniquiness t b == pi_uniquiness x b

pi_lambda_substituion :: Term -> CContext -> Term
pi_lambda_substituion k ((Context  _ _ lambda_var, _)) = apply_f (\x -> case (Map.lookup x lambda_var) of {Just x' -> x'; Nothing -> x}) k

prod_rule :: Term -> CContext -> CContext
prod_rule t c = pi_typed_env t
    where
         pi_typed_env (Pi var_name type_var term_dependent) = do
            let a_type = assert_local (TypeJudge type_var Type) c (Pi var_name type_var term_dependent)
            let _B_type = assert_local (TypeJudge term_dependent (case term_dependent of {Type -> Kind; _ -> Type})) a_type (Pi var_name type_var term_dependent)
            change_local ((Pi var_name type_var term_dependent), Type) (change_local (var_name, type_var) _B_type)


abs_rule :: Term -> CContext -> CContext -- Maybe someone could guess that abs_rules don't have all rules of abs however there are somes rules already inside of abs that have in prod as well, therefore prod_rule is just called is this function
abs_rule t c = abs_type t
  where
    abs_type (Abs x _M) = do
        let pi = get_type (Abs x _M) c
        case pi of
            Just (Pi x _A _B) -> assert_local (TypeJudge _M _B) (inference (Pi x _A _B) c) (Abs x _M) 
            Nothing -> pushLeakType c (Abs x _M) (getCTerm c)

app_rule :: Term -> CContext -> CContext
app_rule k cc = app_typed k
  where
    app_typed (App _M _N) = case (get_type _M cc) of
        Just (Pi x _A _B) -> do
            let v = assert_local (TypeJudge _N _A) cc (App _M _N)
            change_local ((App _M _N), (pi_reduction' (Pi x _A _B) _N)) v
            where 
                pi_reduction' k y = pi_reduction (k, y)
        Just x -> pushTypeError' cc (TypeError x ("The type of " ++ (show _M) ++ " is " ++ (show x) ++ " however this should be a Pi type (Maybe you applied more arguments than function have)"))
        Nothing -> pushLeakType cc _M (getCTerm cc)

inference (Abs k t) cc = abs_rule (Abs k t) (inference t cc)
inference (Pi var t t') cc = prod_rule (Pi var t t') (inference t' (inference t cc))
inference (App x y) cc = app_rule (App x y) (inference x (inference y cc))
inference  _  cc = cc

checkTerm :: CContext -> CContext
checkTerm cc = inference (getCTerm cc) cc

checkKeiTerms :: AST -> IO ()
checkKeiTerms k = do
    let (GlobalContext contexts rules context_def lambdas) = getGlobalContext k

    let state = State (getGlobalContext k) []
    let uncheck_rules = snd $ unzip $ (toList (rules))
    x <- (checkTerms state contexts)
    y <- (checkTerms state uncheck_rules)
    putStrLn (print_type_erros (Prelude.foldl (\x -> \y -> x ++ y) [] (x ++ y)))
  --  print contexts
  where
    checkTerms state (context : xs) = checkTerms state xs >>= (\xs -> do
   --     print (getCTerm (context, state), (getCTerm normalized_context))
      --  print (checkTerm (normalized_context, state))
       -- print ((checkTerm normalized_context))
        print (getCTerm (checkTerm (context, state)))
        print (normalize_term' (term context) (context, state))
        return ((getListErros (checkTerm (context, state))) : xs))
    checkTerms state [] = return []
    print_type_erros ((TypeError k s) : xs) = s ++ "\n" ++ print_type_erros xs
    print_type_erros [] = ""

--getAstType :: Context -> Term -> Term
--getAstType k term = case term of 
  --                 Var s _ -> get s (local k)
    --               Abs s t _ -> Pi s (get s (local k)) (getType k t)

main = do
    getAST >>= (\a -> do
        case a of 
         Right x -> do
            checkKeiTerms x
         Left y -> y
      )
                   