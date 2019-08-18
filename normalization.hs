module KeiNormalization where
import KeiTerms
import Data.Map as Map

pi_reduction :: (Term, Term) -> Term
pi_reduction (Pi n x y, t) = apply_f (\x -> if x == n then t else x) y

beta_reduction :: Term -> Term
beta_reduction (App (Abs x y) t) = apply_f (\x' -> if x' == x then t else x') y

decompose_types_assumptions (Pi n k y) env = (insert n k (decompose_types_assumptions k (decompose_types_assumptions y env)))
decompose_types_assumptions (Abs k y) env = decompose_types_assumptions y env
decompose_types_assumptions (App k y) env = (decompose_types_assumptions k (decompose_types_assumptions y env))
decompose_types_assumptions _ env = env

decompose_types_assumptions' (Abs k y) (Pi n type' y') env names = do
    let (x, names') = decompose_types_assumptions' y y' (decompose_types_assumptions y' env) names
    let f = insert (Abs k y) (Pi n type' y') x
    ((insert k type' f), (insert k n names'))
decompose_types_assumptions' _ (Pi n type' y') env names = (names, decompose_types_assumptions y' env)
decompose_types_assumptions' _ _ env names = (env, names) 