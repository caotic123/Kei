module KeiRules where
import Data.Maybe
import Data.Map as Map
import KeiTerms
import Kei_parser

type Rule = Map String Context

getRulesByAst :: AST -> [RewriteRule]
getRulesByAst (AST k) = Prelude.foldr (\x -> \y -> case x of
    (RewriteDef k) -> k : y
    _ -> []
    ) [] k

getDefRulesEnviroment :: [(String, Context)] -> Definitions_env
getDefRulesEnviroment r = case r of
    ((s, (Context t _ _)) : xs) -> do
        insert (Var (VarName s) RewriteConst) t (getDefRulesEnviroment xs)
    [] -> empty