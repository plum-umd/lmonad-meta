verify:
	cd src/src && liquid ProofCombinators.hs && liquid Label.hs && liquid Language.hs && liquid Programs.hs && liquid MetaFunctions.hs && liquid Determinacy.hs && liquid Simulations/Helpers.hs && liquid Simulations/Language.hs && liquid Simulations/Programs.hs && liquid Simulations/MetaFunctions.hs && liquid Simulations/EraseSubErase.hs && liquid Simulations/EraseEvalErase.hs && liquid Simulations.hs && liquid LLIO.hs

run:
	stack build && stack exec -- lmonad-meta-exe
