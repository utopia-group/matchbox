##
# Capisce
#
# @version OOPSLA 2024

all:
	dune build

clean:
	rm -fr _build
	rm -fr ./doc

check: all
	dune build ./test/stijl_test.exe && ./_build/default/test/stijl_test.exe test -- ${TEST}
