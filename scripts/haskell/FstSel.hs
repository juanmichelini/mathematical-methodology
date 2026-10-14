-- The functions kept by the first search (f0..f2) as foundations Main builds them: definition
-- (binder names are refreshed by the renaming f -> f0), type, the lemmas found with the
-- number of finished proofs, the variable names the definition uses, and the lemma store
-- `fstRec` (simp / reor / basu, in order).  Ground truth for Strategic/FirstSearch.lean.
module FstSel where
import qualified Main as M
import PrettyPrint
import Syntax
import Type
import Prove
import Propose
import Compute (Env)
import Data.List

ppTy :: Type -> String
ppTy (TAtm (TCon c)) = c
ppTy (TAtm (TVar v)) = v
ppTy (TBin TCom a b) = "(" ++ ppTy a ++ " -> " ++ ppTy b ++ ")"

ppAff :: Affirm -> String
ppAff (Affirm vts l r) = intercalate " " [v ++ ":" ++ ppTy t | (v,t) <- vts] ++ " |- " ++ toCLI l ++ " = " ++ toCLI r

dones :: Proof -> Int
dones PDone = 1
dones PFail = 0
dones (PStep _ _ p) = dones p
dones (PInd _ _ cs) = sum [dones p | (_, (_, p)) <- cs]

main :: IO ()
main = do
  mapM_ (\(((Var n, d), t), ls) -> do
      putStrLn ("## " ++ n)
      putStrLn ("def " ++ toCLI d)
      putStrLn ("type " ++ ppTy t)
      putStrLn ("used " ++ intercalate " " (sort (nub (usedVars d))))
      mapM_ (putStrLn . ("lemma " ++) . ppAff . headProof) ls
      putStrLn ("done " ++ show (sum (map dones ls)))
    ) [ (((v, d), t), ls) | (((Atm v', d), t), ls) <- map (\(((a, d), t), ls) -> (((Atm a, d), t), ls)) M.namedFstSel, let v = case v' of Var x -> Var x ]
  let r = M.fstRec
  putStrLn "## fstRec"
  mapM_ (putStrLn . ("simp " ++) . ppAff) (simp r)
  mapM_ (putStrLn . ("reor " ++) . ppAff) (reor r)
  mapM_ (putStrLn . ("basu " ++) . ppAff) (basu r)
