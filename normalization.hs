module KeiNormalization where
import KeiTerms
import Data.Map as Map

foldr_f f k x = case x of
    Pi n x' y' -> (foldr_f f (foldr_f f (f k (Pi n x' y' )) y') x')
    Abs x y ->  (foldr_f f (f k (Abs x y)) y)
    App t t' -> foldr_f f (foldr_f f (f k (App t t')) t) t'
    Var t' x -> f k (Var t' x)
    Type -> f k Type
    Kind -> f k Kind

apply_f f x = case x of
    Pi n x' y' -> f (Pi n (apply_f f x') (apply_f f y')) 
    Abs x' y ->  f (Abs x' (apply_f f y))
    App t t' -> f (App (apply_f f t) (apply_f f t'))
    Var t' x -> f (Var t' x)
    Type -> f Type
    Kind -> f Kind

pi_reduction :: (Term, Term) -> Term
pi_reduction (Pi n x y, t) = apply_f (\x -> if x == n then t else x) y

beta_reduction :: Term -> Term
beta_reduction (App (Abs x y) t) = apply_f (\x' -> if x' == x then t else x) y

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