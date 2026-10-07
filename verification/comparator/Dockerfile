# The compiler and checker run in separate containers. Candidate compilation receives
# only its source tree and writable build cache; reference sources are never mounted.
FROM ubuntu:24.04@sha256:534baea6a22c03a63003dbc8dbe78fe34bc0d7e595d9a9dc9834884ff530eb55

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git elan build-essential python3 zstd \
    && rm -rf /var/lib/apt/lists/*

ENV ELAN_HOME=/opt/elan
RUN elan toolchain install leanprover/lean4:v4.35.0-rc3
ENV PATH=/opt/elan/toolchains/leanprover--lean4---v4.35.0-rc3/bin:$PATH

WORKDIR /opt/comparator
RUN git clone https://github.com/leanprover/comparator.git . \
    && git checkout --detach fd5d5bcf14177b187f66d4502071268d877887c3 \
    && lake build comparator lean4export \
    && test "$(git -C .lake/packages/lean4export rev-parse HEAD)" = \
       66f1fb4bc256072069767fce52d39480e4524869 \
    && cp Main.lean Comparator/Driver.lean \
    && lake build Comparator.Driver \
    && git config --system --add safe.directory /opt/comparator \
    && git config --system --add safe.directory /opt/comparator/.lake/packages/lean4export

COPY Replay.lean /opt/comparator/Replay.lean
RUN lake env lean Replay.lean
WORKDIR /work
