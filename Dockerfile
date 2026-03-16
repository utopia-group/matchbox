# ============================================================================
# MatchBox — PLDI 2026 Artifact
#
# Build:  docker build -t matchbox-artifact .
# Run:    docker run --rm -it matchbox-artifact
# Shell:  docker run --rm -it matchbox-artifact bash
# ============================================================================

# ---------- Stage 1: OCaml build ----------
FROM ocaml/opam:ubuntu-24.04-ocaml-4.14 AS builder

USER root
RUN apt-get update && apt-get install -y --no-install-recommends \
      pkg-config libgmp-dev m4 git ca-certificates \
    && rm -rf /var/lib/apt/lists/*
USER opam
WORKDIR /home/opam

# Vendor gpl
COPY --chown=opam:opam deps/gpl ./gpl
RUN opam pin add gpl ./gpl --no-action

# Install OCaml deps (cached unless stijl.opam changes)
COPY --chown=opam:opam stijl.opam ./stijl.opam
RUN opam install . --deps-only --yes

# Build
COPY --chown=opam:opam . ./matchbox
WORKDIR /home/opam/matchbox
RUN eval $(opam env) && dune build

# ---------- Stage 2: Runtime ----------
FROM ubuntu:24.04

RUN apt-get update && apt-get install -y --no-install-recommends \
      python3 python3-pip libgmp10 \
      texlive-latex-base texlive-fonts-recommended texlive-fonts-extra \
      texlive-latex-extra cm-super dvipng fonts-linuxlibertine \
    && rm -rf /var/lib/apt/lists/*

RUN pip3 install --no-cache-dir --break-system-packages \
      matplotlib pandas numpy

WORKDIR /artifact
COPY --from=builder /home/opam/matchbox /artifact

# Install the stijl binary and a dune shim so `dune exec -- stijl` works
# without the full OCaml toolchain.
COPY --from=builder /home/opam/matchbox/_build/install/default/bin/stijl /usr/local/bin/stijl
RUN printf '#!/bin/sh\n\
if [ "$1" = "build" ]; then echo "Already built"; exit 0; fi\n\
if [ "$1" = "exec" ]; then shift; while [ "$1" = "--" ]; do shift; done; exec "$@"; fi\n\
echo "dune shim: unsupported: $*" >&2; exit 1\n' \
  > /usr/local/bin/dune && chmod +x /usr/local/bin/dune

CMD ["python3", "reproduce.py"]
