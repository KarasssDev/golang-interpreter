.PHONY: repl tests test celan 

all:
	dune build

repl:
	dune exec ./REPL.exe

tests: test
test:
	dune runtest

celan: clean
clean:
	@$(RM) -r _build
