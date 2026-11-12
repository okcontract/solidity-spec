LAKE ?= lake
TECTONIC ?= tectonic
JOBS ?= 4

.PHONY: check manifest replay paper clean
check:
	LEAN_NUM_THREADS=$(JOBS) $(LAKE) build

manifest: check
	python3 -m unittest discover -s scripts -p 'test_*.py'
	python3 scripts/check_theorems.py

replay: manifest
	@set -e; for module in Solidity \
		Solidity.Pilots.AliasCallRollbackResourceTests \
		Solidity.Pilots.AliasCallRollbackGroupTests \
		Solidity.Pilots.OrderAliasRollbackTests \
		Solidity.Conformance.ScalarMachineTests; do \
		echo "Replaying $$module"; \
		LEAN_NUM_THREADS=1 $(LAKE) env leanchecker --fresh "$$module"; \
	done

paper:
	mkdir -p paper/build
	$(TECTONIC) --keep-logs --outdir paper/build paper/solidity-semantics.tex
	cp paper/build/solidity-semantics.pdf paper/solidity-semantics.pdf

clean:
	rm -rf paper/build
