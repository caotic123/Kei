module Main where
import Terms
import Parser
import Rules
import Normalization
import Data.Map as Map

data Jugdment = TypeJudge Term Term
type LambdaDef = Map Term Context
data GlobalContext  = GlobalContext {context :: [Context], rules :: Rule, context_def :: Definitions_env, lambda_def :: LambdaDef} deriving Show
data TypeErrors = TypeError Term String deriving Show
data State = State GlobalContext [TypeErrors] deriving Show
type CContext = (Context, State)

formalize_terms :: Local_env -> TypedT -> Context
formalize_terms y k =
    case k of
        (Typed (PAbs k by) (PType u q q')) -> do 
            let untyped_term = Abs (Var k Lambda_Abstraction) (untyped_parsedTerm by)
            let (Pi name type_var term_dependent) = equal_types untyped_term (untyped_parsedTerm (PType u q q'))
            let (pi_premisse, names) = decompose_types_assumptions' untyped_term (Pi name type_var term_dependent) y empty
            Context untyped_term pi_premisse empty
        (Typed (PValue k) f) -> do
            let t = untyped_parsedTerm (PValue k)
            Context t (insert t (untyped_parsedTerm f) y) empty
        (Typed (PApp k y') f) -> do
            let t = untyped_parsedTerm (PApp k y')
            Context t  (insert t (untyped_parsedTerm f) y) empty
        (Typed (PType k y1 y2) f) -> do
            let (Pi x type_t term_dependent) = untyped_parsedTerm (PType k y1 y2)
            let pi_premisse = decompose_types_assumptions (Pi x type_t term_dependent) y -- every pi type has a premisse that x carry a T type/kind.
            Context (Pi x type_t term_dependent) (insert (Pi x type_t term_dependent) (untyped_parsedTerm f) pi_premisse) empty
        (Typed (PMatch matched type' k) f) -> do
           -- let typed_expr_match = Prelude.foldl (\x -> \(condition, term) ->
           --      (insert (untyped_parsedTerm term) (untyped_parsedTerm type') x)) y k
            let t = untyped_parsedTerm (PMatch matched type' k)
            Context t y empty

getLocalContexts :: [TypedT] -> [Context]
getLocalContexts (x : xs) = do
    formalize_terms empty x : (getLocalContexts xs)
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
    let (Context term local _) = k
    term

getLocalContext (k, y) = do
    let (Context term local _) = k
    local

getListErros :: CContext -> [TypeErrors]
getListErros (_, (State _ y)) = y

getEnvDef :: CContext -> Definitions_env
getEnvDef (k, State (GlobalContext _ _ env_def lambdas) er) = env_def

getTermFromLambdaDefs term' (GlobalContext _ _ def_env lambdas) = Map.lookup term' lambdas

mapContext (Context term' local match_vars) f = (Context term' (Map.map f local) match_vars)

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

assert_local :: Jugdment -> CContext -> Term -> CContext
assert_local (TypeJudge term type') cc helper = do
   let type_error k = TypeError term ("The term " ++ (show term) ++ " should be a type " ++ (show (normalize_term' (matching_substituion type' cc) cc)) ++ " instead of " ++ (show (normalize_term' (matching_substituion k cc) cc)) ++ " where " ++ show helper ++ " is your jugdment\n")
   let equal_types k' type' = pi_equality (k', type') cc
   let subst term' = (matching_substituion term' cc)
   case (get_type term cc) of
       Just k -> do
        if (equal_types k type' ||
            equal_types (subst k) (subst type')) then cc -- A weak equality (lambda )
        else pushTypeError' cc (type_error k)
       Nothing -> pushLeakType cc term helper

get_rules_typed_context :: [RewriteRule] -> Symbol -> (Symbol, Rule)
get_rules_typed_context r s = case r of
    ((RewriteRule x y) : xs) -> do
        let (s', t) = pure_structural s y
        let (s, map') = get_rules_typed_context xs s'
        let rule_typed = formalize_terms empty (Typed t (PValue (VarName "Type")))
        (s, insert x rule_typed map')
    [] -> (s, empty)

have_a_fix_point (k', f) = foldr_f (\x -> \y -> (y == f) || x) False (evaluates_avaliable_match k')
have_const (App _ k') = foldr_f (\x -> \y -> case y of
    (Var (VarName _) _) -> True
    _ -> x
    ) False (evaluates_avaliable_match k')  
    
just_linear_substuitions term' cc = not (foldr_f (\x -> \y -> search x y) True term')
    where 
        search x y = case y of
            (App y' t) ->
                case (getTermFromLambdaDefs y' cc) of
                    Just x' -> if (have_a_fix_point ((term x'), y')) then x else False
                    Nothing -> x
            _ -> x

is_weak_normalized :: State -> Term -> Bool
is_weak_normalized (State cc e) c = is_weak_normalized' && there_are_no_definitions && there_are_no_free_matchs
    where
        there_are_no_definitions = foldr_f (\x -> \y ->
            case y of
                (App y' t) ->
                    case (getTermFromLambdaDefs y' cc) of
                        Just x' -> if (have_a_fix_point ((term x'), y')) && (have_const (App y' t)) then False else x
                        Nothing -> x
                _ -> x) True c
        is_ResolvableMatch k = 
            case k of
                Match matched _ terms -> do
                    let n = Prelude.foldl (\y -> \(predicate, term) -> if check_matching matched predicate then (predicate, term) : y else y) [] terms
                    (length n) > 0
                _ -> False       
        there_are_no_free_matchs = 
            foldr_f (\x -> \y -> (not (is_ResolvableMatch y)) && x) True c
        is_weak_normalized' = 
            foldr_f (\x -> \y -> (is_non_abs_app y) && x) True c
            where 
                is_non_abs_app k = case k of {App (Abs _ _) _ -> False; _ -> True;}

weak_normalize :: Term -> Term
weak_normalize c = (evaluates_avaliable_match (apply_f (\x -> case x of
    (App (Abs x y) t) -> beta_reduction (App (Abs x y) t) 
    _ -> x) c))

check_matching :: Term -> Term -> Bool
check_matching k y = case (y, k) of
    ((App k k'), (App k2 k2')) -> check_matching k2 k && check_matching k2' k'
    ((Var (VarSimbol _ _) _), (Var (VarSimbol _ _) _)) -> True
    ((Var (VarSimbol k _) k'), _) -> True
    ((Var k k'), (Var k0 k0')) -> (Var k k') == (Var k0 k0')
    _ -> False

evaluates_avaliable_match :: Term -> Term
evaluates_avaliable_match k = case k of
    App x x' -> App (evaluates_avaliable_match x) (evaluates_avaliable_match x')
    Abs n y' -> Abs n (evaluates_avaliable_match y')
    Pi n x' y' -> Pi n (evaluates_avaliable_match x') (evaluates_avaliable_match y')
    Match matched type' terms -> do
        let n = Prelude.foldl (\y -> \(predicate, term) -> if check_matching matched predicate then (predicate, term) : y else y) [] terms
        let terms' = Prelude.map (\(predicate, term) -> (predicate, evaluates_avaliable_match term)) terms
        case n of 
            ((construction, term') : xs) -> destruct_matching matched construction term' -- by sequence of matching take the head of the matching
            _ -> Match matched type' terms'
    Var s y' -> Var s y'
    Type -> Type
    Kind -> Kind

  where
    destruct_matching matched construction term' = do
        let substuitions = get_match_composition matched construction []
        let substitute_def term' (k, u) = apply_f (\x -> if x == k then u else x) term'
        Prelude.foldl (\y -> \(u, x') -> substitute_def y (u, x')) term' substuitions
        where
            get_match_composition k y ls = case (y, k) of
                (App x x', App u u') -> (get_match_composition u x (get_match_composition u' x' ls))
                (Var (VarSimbol s s') x, n) -> (Var (VarSimbol s s') x, n) : ls
                _ -> ls
                

change_local :: (Term, Term) -> CContext -> CContext 
change_local (t, t') ((Context term' local match_vars), k) = ((Context term' (insert t t' local) match_vars), k)

change_match_vars :: (Term, Term) -> CContext -> CContext
change_match_vars  (t, t') ((Context term' local match_vars), k) = ((Context term' local (insert t t' match_vars)), k)

set_matching_vars :: CContext -> Lambda_vars -> CContext 
set_matching_vars ((Context term' local _), k) match_vars = ((Context term' local match_vars), k)

--context_weak_normalized :: CContext -> Bool
--context_weak_normalized (c, (State cc e)) = fold (\x -> \y -> (is_weak_normalized (x, (State cc e))) && y) True (toList (local c)) 

simply_eval :: Term -> GlobalContext -> Term -- Trying get normal terms from the context is a way of obtain sucessuful typed conversion equality
simply_eval k cc = apply_f (\y -> 
    case (getTermFromLambdaDefs y cc) of
        Just x' -> (term x')
        Nothing -> y) k
        
normalize_term' :: Term -> CContext -> Term -- Trying get normal terms from the context is a way of obtain sucessuful typed conversion equality
normalize_term' term' c'@(context, (State cc e)) = do
    let solved_linear = solve_non_recursives_terms term' c'
    if (not (is_weak_normalized (State cc e) solved_linear)) then
        normalize_term' (weak_normalize (substitute_terms $ solved_linear)) $ c' else solved_linear 
  where 
    substitute_terms =
        apply_f (\y -> case y of
            App x' y' -> case (getTermFromLambdaDefs x' cc) of
                Just (Context t local _) -> do
              --      let (t0, _) = substitute_definitions ((Context (App t y') local vars), (State cc e))
                      weak_normalize  (App t y')
                Nothing -> y
            _ -> y)

solve_non_recursives_terms :: Term -> CContext -> Term -- Trying get normal terms from the context is a way of obtain sucessuful typed conversion equality
solve_non_recursives_terms term' (context, (State cc e))
 | just_linear_substuitions term' cc = (solve_linear_terms term')
 | otherwise = term'
  where 
    solve_linear_terms =
        apply_f (\y -> case y of
            App x' y' -> case (getTermFromLambdaDefs x' cc) of
                Just (Context t local _) -> do
                    if (not (have_a_fix_point (t, x'))) then weak_normalize (App t y') else y
                Nothing -> y
            _ -> y)

pi_uniquiness :: Term -> Symbol -> Term
pi_uniquiness (Pi (Var (VarSimbol x y) l) t t') s = do
    let v = (Var (VarSimbol x y) l) 
    Pi (Var (VarSimbol s y) l) t (apply_f (\x -> if x == v then (Var (VarSimbol s y) l) else x) (pi_uniquiness t' (Next s)))
pi_uniquiness (Pi v t t') s = Pi v (pi_uniquiness t s) (pi_uniquiness t' s)
pi_uniquiness (Abs k y) s = Abs k (pi_uniquiness y s)
pi_uniquiness (App t t') s = App (pi_uniquiness t s) (pi_uniquiness t' s)
pi_uniquiness (Match matched type' terms) s = 
    Match (pi_uniquiness matched s) (pi_uniquiness type' s) ((Prelude.map (\(x, y) -> (x, pi_uniquiness y s))) terms)
pi_uniquiness (Var k x) s = (Var k x)
pi_uniquiness Type s = Type
pi_uniquiness Kind s = Kind
 
pi_equality :: (Term, Term) -> CContext -> Bool
pi_equality (t, x) cc = do
    let b = Initial
    t == x || (pi_uniquiness t b) == (pi_uniquiness x b)  || normalize_term' (pi_uniquiness t b) cc == normalize_term' (pi_uniquiness x b) cc

matching_substituion :: Term -> CContext -> Term
matching_substituion k ((Context u i match_vars, m))
     | there_is_substitons k = 
        matching_substituion (apply_f (\x -> case (Map.lookup x match_vars) of {Just x' -> x'; Nothing -> x}) k) ((Context u i  match_vars, m))
     | otherwise = k
  where there_is_substitons k = foldr_f (\x -> \y -> case (Map.lookup y match_vars) of {Just x' -> True; Nothing -> x}) False k

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

match_typing :: Term -> CContext -> CContext
match_typing k cc = do
    let (Match destructed type' matchs) = k
    (change_local ((Match destructed type' matchs), type') cc)

type_match_option :: CContext -> Term -> Term -> (Term, Term) -> CContext
type_match_option cc destructed type' (predicate, term) = do
    (type_construction_equality destructed predicate (infer_by_aplication predicate cc) term)

infer_by_aplication :: Term -> CContext -> CContext
infer_by_aplication k cc =
    case k of
        App x y -> do
            let u' = (infer_by_aplication x (infer_by_aplication y cc))
            case (get_type x u') of
                Just (Pi n term term_dependent) ->
                    change_local ((App x y), pi_reduction ((Pi n term term_dependent), y)) (change_local (y, term) u')
                Nothing ->
                    pushTypeError' u' (TypeError k ("The type of " ++ (show x) ++  "can't be inferred on " ++ (show k) ++ " construction"))
        Var _ _ -> cc
        f -> pushTypeError' cc (TypeError f ("Construction just allow applications products : " ++ (show k)))
    
type_construction_equality x u cc k =
    case (get_type x cc, get_type u cc) of
        (Just y, Just y') -> assert_local (TypeJudge x y) (type_construction_correspodence y y' (type_construction_correspodence x u cc)) k
        _ -> pushTypeError' cc (TypeError x ("Impossible of infer the " ++ (show x) ++ " and " ++ (show u) ++ " in " ++ (show k)))
    
type_construction_correspodence x y cc = do
    case (x, y) of --two productons canonically construed by the same construction *should* be equal 
      ((App k k'), (App k0 k0')) -> do
        change_match_vars (k', k0') (type_construction_correspodence k' k0' (type_construction_correspodence k k0 cc))
      (v@(Var (VarSimbol _ _) _), v') -> change_match_vars (v, v') cc
      _ -> cc
    
assert_constructions x y cc helper = case (get_type y cc) of
    Just type' -> assert_local (TypeJudge x type') cc helper
    Nothing -> pushTypeError' cc (TypeError x ("Impossible of infer the " ++ (show x) ++ " and " ++ (show y) ++ " in " ++ (show helper)))


inference (Abs k t) cc = abs_rule (Abs k t) (inference t cc)
inference (Pi var t t') cc = prod_rule (Pi var t t') (inference t' (inference t cc))
inference (App x y) cc = app_rule (App x y) (inference x (inference y cc))
inference (Match x y matchs) cc = do
    let k = match_typing (Match x y matchs) (inference x (inference y cc))
    Prelude.foldl (\y' -> \(predicate, term) -> do
        let state_match = (match_vars (fst y')) -- saves the actual context to avoid problem with scopes variables of matching context
        let try = type_match_option y' x y (predicate, term)
        set_matching_vars (assert_local (TypeJudge term y) (inference term try) (Match x y matchs)) state_match) k matchs -- Preserve and guarantees expr match hygienic scopes 
inference  _  cc = cc

checkTerm :: CContext -> CContext
checkTerm cc = inference (getCTerm cc) cc

test k = case k of
    (FuncDef (Def name (Function t' t))) : xs -> print (pure_structural Initial t) >> test xs
    (k : xs) -> test xs
    [] -> return ()

eval k env = case k of
        (Eval k) : xs -> do
            let expr' = untyped_parsedTerm k
            print (normalize_term' expr' env)
        (k : xs) -> eval xs env
        [] -> return ()

checkKeiTerms :: AST -> IO ()
checkKeiTerms k = do
     let (GlobalContext contexts rules context_def lambdas) = getGlobalContext k
     let state = State (getGlobalContext k) []
     let uncheck_rules = snd $ unzip $ (toList (rules))
     y <- (checkTerms state uncheck_rules)
     x <- (checkTerms state contexts)
     let concat = Prelude.foldl (\x -> \y -> x ++ y) []
     case (concat y) of
        ls@(_ : _) -> do
            (putStrLn (print_type_erros ls))
        _ -> case (concat x) of
            ls@(_ : _) -> do
                (putStrLn (print_type_erros ls))
                putStrLn "Error in function definition, by default don't eval bad typed encoding"
            _ -> do
                putStrLn "Kei checked the terms with sucess"
                eval ((\(AST k) -> k) k) (undefined, state) 
    
  where
    checkTerms state (context : xs) = checkTerms state xs >>= (\xs -> do
        return ((getListErros (checkTerm (context, state))) : xs))
    checkTerms state [] = return []
    print_type_erros ((TypeError k s) : xs) = s ++ "\n" ++ print_type_erros xs
    print_type_erros [] = ""

main = do
    getAST >>= (\a -> do
        case a of 
         Right x -> do
            checkKeiTerms x
         Left y -> y
      )
                   