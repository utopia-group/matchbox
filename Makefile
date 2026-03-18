##
# MatchBox — PLDI 2026 Artifact
#
# Build:       make
# Tests:       make check
# Reproduce:   make reproduce          (full end-to-end)
#              make run                 (experiments only, uses existing data)
#              make report              (figures + stats from existing results)

all:
	dune build

clean:
	rm -fr _build
	rm -fr ./doc

check: all
	dune build ./test/stijl_test.exe && ./_build/default/test/stijl_test.exe test -- ${TEST}

# ── Experiment Reproduction ──────────────────────────────────────────────────

reproduce: all
	python3 experiments.py

run: all
	python3 experiments.py --step run

report:
	python3 experiments.py --step report

.PHONY: all clean check reproduce run report
