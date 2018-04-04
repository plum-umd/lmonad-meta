LIQUID = stack exec -- liquid
verify:
	cd src && $(LIQUID) ProofCombinators.hs && $(LIQUID) Label.hs && $(LIQUID) Language.hs && $(LIQUID) Programs.hs && $(LIQUID) MetaFunctions.hs && $(LIQUID) Determinacy.hs && $(LIQUID) Simulations/Helpers.hs && $(LIQUID) Simulations/Language.hs && $(LIQUID) Simulations/Programs.hs && $(LIQUID) Simulations/MetaFunctions.hs && $(LIQUID) Simulations/EraseSubErase.hs && $(LIQUID) Simulations/EraseEvalErase.hs && $(LIQUID) Simulations.hs && $(LIQUID) LLIO.hs

run:
	stack build && stack exec -- lmonad-meta-exe
