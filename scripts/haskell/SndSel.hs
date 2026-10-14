-- The second search as foundations Main builds it: the 164 candidates (in order), and the
-- functions kept (f3..f30) with definition (renamed binders), type, used names, lemmas and
-- finished proofs, followed by the final lemma store.  Ground truth for
-- Strategic/SecondSearch.lean.
module SndSel where
import qualified Main as M
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

dones :: Proof -> Int
dones PDone = 1
dones PFail = 0
dones (PStep _ _ p) = dones p
dones (PInd _ _ cs) = sum [dones p | (_, (_, p)) <- cs]

main :: IO ()
main = do
  putStrLn ("## candidates " ++ show (length M.candidatosSnd))
  mapM_ (\(e,t) -> putStrLn (toCLI e ++ "  ::  " ++ ppTy t)) M.candidatosSnd
  mapM_ (\(((Var n, d), t), ls) -> do
      putStrLn ("## " ++ n)
      putStrLn ("def " ++ toCLI d)
      putStrLn ("type " ++ ppTy t)
      putStrLn ("used " ++ intercalate " " (sort (nub (usedVars d))))
      mapM_ (putStrLn . ("lemma " ++) . ppAff . headProof) ls
      putStrLn ("done " ++ show (sum (map dones ls)))
    ) M.namedSndSel
