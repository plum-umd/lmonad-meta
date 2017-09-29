verify:
	cd src/src && liquid Label.hs && liquid Language.hs && liquid Programs.hs && liquid MetaFunctions.hs && liquid Determinacy.hs && liquid Simulations.hs && liquid LLIO.hs

run:
	stack build && stack exec -- lmonad-meta-exe
