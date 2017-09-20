verify:
	cd src/src && liquid Language && liquid Programs && liquid MetaFunctions && liquid Determinacy && liquid Simulations && liquid LLIO

run:
	stack build && stack exec -- lmonad-meta-exe
