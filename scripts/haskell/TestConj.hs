-- Conjecture batches (plemas) and conjeturasAll for the functions of foundations Test.env,
-- with an empty rule store: ground truth for Strategic/Conjecture.lean.
module TestConj where
import qualified Test as T
import PrettyPrint
import Syntax
import Type
import Prove
import Propose
import Data.List

ppTy :: Type -> String
ppTy (TAtm (TCon c)) = c
ppTy (TAtm (TVar v)) = v
ppTy (TBin TCom a b) = "(" ++ ppTy a ++ " -> " ++ ppTy b ++ ")"

ppAff :: Affirm -> String
ppAff (Affirm vts l r) = intercalate " " [v ++ ":" ++ ppTy t | (v,t) <- vts] ++ " |- " ++ toCLI l ++ " = " ++ toCLI r

fns :: [String]
fns = ["suma","mult","flipexp","not","and","or","ssi","xor","mayoria","par","doble","pred","min","max","absr","concat","largo","rev"]

main :: IO ()
main = do
  mapM_ (\f -> do
      putStrLn ("## fn " ++ f)
      let batches = plemas T.env T.tenv T.datas 30 emptyRec (Var f)
      mapM_ (\(j,b) -> do putStrLn ("# batch " ++ show j); mapM_ (putStrLn . ppAff) b) (zip [0::Int ..] batches)
    ) (filter (\f -> Atm (Var f) `elem` map fst T.tenv) fns)
  putStrLn "## all suma mult"
  mapM_ (putStrLn . ppAff) (pfindlemasAll T.env T.tenv T.datas 30 emptyRec [Var "suma", Var "mult"])
  putStrLn "## all concat rev"
  mapM_ (putStrLn . ppAff) (pfindlemasAll T.env T.tenv T.datas 30 emptyRec [Var "concat", Var "rev"])
