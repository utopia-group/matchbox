##
# MatchBox — PLDI 2026 Artifact
#
# Build:       make                     (produces ./matchbox)
# Install:     make install             (to $(PREFIX)/bin, default /usr/local)
# Tests:       make check
# Reproduce:   make reproduce          (full end-to-end)
#              make run                 (experiments only, uses existing data)
#              make report              (figures + stats from existing results)

PREFIX ?= /usr/local
BINDIR  = $(PREFIX)/bin

all: matchbox

matchbox:
	dune build
	cp -f _build/install/default/bin/matchbox ./matchbox

install: all
	install -d $(BINDIR)
	install -m 755 ./matchbox $(BINDIR)/matchbox

uninstall:
	rm -f $(BINDIR)/matchbox

clean:
	rm -fr _build
	rm -fr ./doc
	rm -f ./matchbox

check: all
	dune build ./test/matchbox_test.exe && ./_build/default/test/matchbox_test.exe test -- ${TEST}

# ── Experiment Reproduction ──────────────────────────────────────────────────

reproduce: all
	python3 experiments.py

run: all
	python3 experiments.py --step run

report:
	python3 experiments.py --step report

.PHONY: all matchbox install uninstall clean check reproduce run report
