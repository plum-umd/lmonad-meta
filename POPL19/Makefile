LIQUID = liquid

verify:
	$(LIQUID) ProofCombinators.hs
	$(LIQUID) Predicates.hs
	$(LIQUID) Labels.hs
	$(LIQUID) Programs.hs
	$(LIQUID) DBValueErase.hs  

## Generally Used Theorems

	$(LIQUID) Monotonicity.hs 
	$(LIQUID) Idempotence.hs
	$(LIQUID) TableInfoErase.hs
	$(LIQUID) HomomorphicSubst.hs
	
## Simulations

	$(LIQUID) Simulations/Terms.hs

## Simulations.Insert

	$(LIQUID) Simulations/Insert.hs   
	$(LIQUID) Simulations/TInsert0.hs
	$(LIQUID) Simulations/TInsert.hs   


## Simulations.Delete

	$(LIQUID) LabelPredImplies.hs
	$(LIQUID) LookupTableErase.hs
	$(LIQUID) LabelPredErase.hs

	$(LIQUID) Simulations/DeleteAll.hs
	$(LIQUID) Simulations/DeleteHelpers.hs
	$(LIQUID) Simulations/TDeleteFound.hs
	$(LIQUID) Simulations/Delete.hs

	$(LIQUID) Simulations/TDelete.hs 
	$(LIQUID) Simulations/TDeletePgHole.hs 


## Simulations.Update
#	$(LIQUID) Simulations/Update.hs && $(LIQUID) Simulations/TUpdate.hs 

## Simulations.Select
#	$(LIQUID) Simulations/Select.hs && $(LIQUID) Simulations/TSelect.hs 

## Simulations.Bind
#	$(LIQUID) Simulations/TBind.hs 

## Simulations.Unlabel
#	$(LIQUID) Simulations/TUnlabel.hs 

## All Together

	$(LIQUID) Simulations/Simulations.hs
	$(LIQUID) NonInterference.hs

clean: 
	rm -rf .liquid/ && rm -rf Terms/.liquid/ && rm -rf DataBase/.liquid/ && rm -rf Simulations/.liquid
	
