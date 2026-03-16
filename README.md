# MatchBox: A Semantic Foundation for Data Plane Portability (PLDI 2026, Paper 153)

This artifact reproduces all experiments from Section 8 of the paper:
three case studies evaluating MatchBox's compiler on match-action table translations.

## Getting Started

**Docker (recommended, ~10 minutes to build):**

```
docker build -t matchbox-artifact .
docker run --rm -it matchbox-artifact
```

The container runs `python3 reproduce.py` automatically, executing all experiments
and generating figures (~25 min). To get an interactive shell instead (e.g., to
run individual steps):

```
docker run --rm -it matchbox-artifact bash
```

Each `docker run` starts a fresh container. To preserve results between commands,
use a single interactive session.

**Native requirements:** OCaml 4.14+ with opam, Python 3 with matplotlib/pandas/numpy,
LaTeX with libertine fonts (for plot rendering). Then:

```
opam pin add gpl deps/gpl --no-action
opam install . --deps-only --yes
make
python3 reproduce.py
```

**Quick smoke test (~10 seconds):**
Run only the eBPF case study, the fastest of the three:

```
python3 reproduce.py --case ebpf
```

This builds the compiler, generates configs, runs 60 translations, produces
`programs/ebpf/results.csv` and `_output/figure-18.pdf`, and prints Table 3 statistics.
Verify the output matches the paper's Figure 18 and Table 3.

## Step-by-Step Instructions

`reproduce.py` runs five steps in order. Each can be run independently via `--step`.

| Step       | Command                                | What it does                                      |
|------------|----------------------------------------|---------------------------------------------------|
| `build`    | `python3 reproduce.py --step build`    | Compile OCaml binaries via `dune build`            |
| `generate` | `python3 reproduce.py --step generate` | Create base JSON configs from synthetic/ClassBench data |
| `sample`   | `python3 reproduce.py --step sample`   | Subsample at 10 uniform sizes, write experiment JSONs |
| `run`      | `python3 reproduce.py --step run`      | Run all translations via `stijl exp`               |
| `report`   | `python3 reproduce.py --step report`   | Generate Figures 15-18, print Tables 1-3 and inline stats |

Use `--case retarget`, `--case acl`, or `--case ebpf` to restrict to one case study.
Flags are repeatable: `--case retarget --case acl` runs two of three.

**Expected runtimes** (on a modern laptop):

| Case study                          | Section | Translations | Runtime  |
|-------------------------------------|---------|--------------|----------|
| Programmable Switch Evolution       | 8.1     | 300 (30x10)  | ~25 min  |
| Consistent Multi-Cloud Firewalls    | 8.2     | 60 (6x10)    | ~8 sec   |
| eBPF Architectural Changes          | 8.3     | 60 (6x10)    | ~1 sec   |

The retargeting case study is the slowest because some translations (notably
`link_aggregation` to `double`) produce large intermediate configs via parallel
joins. If the run is killed (OOM), the script prints a warning with the number
of completed experiments. Try closing other applications or running case studies
individually.

**Output files:**

| File                                | Paper element |
|-------------------------------------|---------------|
| `_output/figure-15.pdf`            | Figure 15 (evolution compilation time)  |
| `_output/figure-16.pdf`            | Figure 16 (evolution output config size) |
| `_output/figure-17.pdf`            | Figure 17 (cloud firewall compilation time) |
| `_output/figure-18.pdf`            | Figure 18 (eBPF compilation time) |
| `programs/retargeting/results.csv` | Raw data for Figures 15-16, Table 1 |
| `programs/acl/results.csv`         | Raw data for Figure 17, Table 2 |
| `programs/ebpf/results.csv`        | Raw data for Figure 18, Table 3 |

### Using the original results

The repository ships the original paper results in `programs/*/results.csv` and
`_output/figure-{15..18}.pdf`. Running `python3 reproduce.py --step report`
without `--step run` will generate figures and statistics from these committed
results, so you can inspect the paper's data without re-running experiments.

### Verifying reproduced results with git diff

After running `--step run`, use `git diff` to compare against the originals.
Only the timing columns (`typetime`, `eval_time`, `min_eval_time`) should differ;
all structural columns (`size`, `num_fds`, `eval_in_size`, `eval_out_size`, etc.)
should be identical.

### Warnings safe to ignore

- matplotlib font substitution warnings when LaTeX libertine fonts are unavailable.
  Plots still render correctly with fallback fonts.
- `dune build` warnings about unused variables in OCaml source files.
- `ld: warning: -undefined suppress is deprecated` on macOS (linker noise, harmless).

## Claims Supported by Artifact

**Claim 1 (Table 1, Section 8.1):** The 30 retargeting MatchStix programs have
AST sizes 3-47 (median 20.5), at most 3 GFD annotations (10 of 30 programs
require any), and type-check efficiently.
Verify: `python3 reproduce.py --step report`

**Claim 2 (Section 8.1):** Retargeting compilation averages ~0.6 ms per input
rule on configurations of 6 to 10,517 rules. Translations from
`action_decompose` and `link_aggregation` are slower due to parallel join and
composition operators.
Verify: `--step report` prints avg time per rule; compare `_output/figure-15.pdf`
with paper Figure 15 for the per-source-pipeline breakdown.

**Claim 3 (Figure 16, Section 8.1):** Output configuration size grows linearly
with input size; larger outputs occur when rules are duplicated across target tables.
Verify: compare `_output/figure-16.pdf` with paper Figure 16.

**Claim 4 (Table 2, Section 8.2):** The 6 cloud firewall programs use 2-10 AST
nodes, at most 2 GFD annotations (only 2 programs require any), and type-check
efficiently.
Verify: `python3 reproduce.py --step report`

**Claim 5 (Figure 17, Section 8.2):** Cloud firewall compilation scales linearly,
averaging ~0.5 us per rule, on configs up to 10,695 entries. Output size is
nearly identical to input size.
Verify: compare `_output/figure-17.pdf` with paper Figure 17.

**Claim 6 (Table 3, Section 8.3):** The 6 eBPF programs use 64-95 AST nodes
(median 79.5) and up to 32 GFD annotations. System-wide-to-per-CPU translations
require more annotations and are more expensive to type-check.
Verify: `python3 reproduce.py --step report`

**Claim 7 (Figure 18, Section 8.3):** eBPF compilation averages ~2 us per rule
on configurations of 64 to 1,793 rules. System-wide to per-CPU translations
are slower than the reverse.
Verify: compare `_output/figure-18.pdf` with paper Figure 18.

**Note on timing:** Typecheck and compilation times are runtime measurements that
vary across machines and runs. Typecheck times in particular are measured in
microseconds and are sensitive to CPU frequency scaling, background load, and
caching effects -- expect noticeable variance in these columns. The deterministic
columns (AST size, annotation count, input/output config sizes) should match exactly.

## Claims Not Supported by Artifact

- **Correctness proofs (Sections 4-7):** The formal metatheory (soundness of the
  type system, semantic preservation of compilation) is a pen-and-paper proof
  in the paper and is not mechanized in this artifact.
- **Comparison with hand-written translations:** The paper's qualitative discussion
  of engineering effort vs. hand-written scripts (Section 1, Section 8) is not
  quantitatively measured by the artifact.

## Repository Layout

```
reproduce.py                  - Main reproduction script
Dockerfile                    - Docker build (two-stage: OCaml build + Python runtime)
Makefile                      - make / make check / make reproduce
programs/retargeting/         - Switch evolution case study (Section 8.1)
programs/acl/                 - Cloud firewall case study (Section 8.2)
programs/ebpf/                - eBPF case study (Section 8.3)
programs/*/programs/*.mb      - MatchStix translation programs
programs/*/experiments.json   - Experiment templates
programs/*/results.csv        - Committed paper results (overwritten on reproduction)
_output/figure-{15..18}.pdf   - Committed paper figures (overwritten on reproduction)
lib/                          - OCaml compiler source
test/                         - Unit tests (run via `make check`)
deps/gpl/                     - Vendored GPL dependency (private repo)
```
