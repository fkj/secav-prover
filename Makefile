ISABELLE := isabelle
HASKELL := haskell
EXPORT := $(HASKELL)/export
APP := $(HASKELL)/app
LIB := $(HASKELL)/lib
ISABELLE_SOURCES = $(wildcard $(ISABELLE)/*.thy)

.PHONY: clean test

build: $(EXPORT)/%.hs
	cabal build

test:
	cabal test
	rm -rf test-tmp

$(EXPORT)/%.hs: $(ISABELLE_SOURCES) $(ISABELLE)/ROOT
	~/m/bin/Isabelle2021/bin/isabelle export -d $(ISABELLE) -x "*:**.hs" -p 3 -O $(EXPORT) -o quick_and_dirty SeCaV_Coinductive

clean:
	rm -rf $(EXPORT)
	cabal clean
