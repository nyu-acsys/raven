# Raven verifier image: the raven binary, Z3, the example suite under test/, and the
# benchmark scripts (with the extension sources bench_ext.sh measures).
#
#   docker build -t raven .
#   docker run --rm raven test/concurrent/lock/ticket-lock.rav
#
# Both stages use the same Alpine release, so the binary built in the first runs
# against the libraries it was linked with.
ARG ALPINE_VERSION=3.24

# --- Stage 1: build ---
FROM ocaml/opam:alpine-${ALPINE_VERSION}-ocaml-5.2 AS build

WORKDIR /home/opam/app

# Raven runs the z3 executable, which the runtime stage installs from Alpine; it does
# not link the OCaml bindings. Satisfy opam's z3 dependency with an empty stand-in
# package rather than compiling Z3 from source (same approach as release.yml).
RUN mkdir -p /home/opam/z3-stub \
 && printf '%s\n' \
      'opam-version: "2.0"' \
      'name: "z3"' \
      'version: "4.13.0"' \
      'synopsis: "Stand-in for z3: the build only needs the opam dependency satisfied"' \
      'build: []' \
      'install: []' \
      > /home/opam/z3-stub/opam \
 && opam pin add -y z3 /home/opam/z3-stub

# Dependencies first, so this layer is reused when only the sources change.
COPY --chown=opam:opam Raven.opam ./
RUN opam install . --deps-only -y

COPY --chown=opam:opam . .
RUN opam exec -- dune build bin/raven.exe

# --- Stage 2: runtime ---
FROM alpine:${ALPINE_VERSION}

# z3 for verification; the rest is what the scripts under scripts/ use.
RUN apk add --no-cache z3 bash bc cloc findutils hyperfine jq

WORKDIR /app

COPY --from=build /home/opam/app/_build/default/bin/raven.exe /usr/local/bin/raven
COPY --from=build /home/opam/app/test ./test
COPY --from=build /home/opam/app/lib/ext ./lib/ext
COPY --from=build /home/opam/app/scripts ./scripts

# Fail the build if Alpine's Z3 is older than the version raven requires.
RUN min=$(raven --manifest | sed -n 's/.*"min_z3":"\([^"]*\)".*/\1/p') \
 && have=$(z3 --version | sed -n 's/^Z3 version \([0-9.]*\).*/\1/p') \
 && printf '%s\n%s\n' "$min" "$have" | sort -V -c 2>/dev/null \
 || { echo "Z3 $have is older than the required $min" >&2; exit 1; }

ENTRYPOINT ["raven"]
