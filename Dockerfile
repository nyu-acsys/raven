# --- Stage 1: Build Stage ---
FROM ocaml/opam:alpine AS build

# Install system dependencies (bash, m4, etc. required for many OCaml libs)
USER root
RUN apk add --no-cache bash m4 pkgconfig build-base gmp-dev jq hyperfine

# Switch back to the opam user to manage OCaml packages
USER opam
WORKDIR /home/opam/app

# Update opam and install the build tool (Dune)
RUN opam update && opam install dune -y

RUN opam install z3 ocamlformat base stdio logs fmt cmdliner ppx_custom_printf ppx_compare ppx_hash ppx_sexp_conv ppx_let ppx_blob yojson -y --jobs=8

# Copy Raven's source code into the container
COPY --chown=opam:opam . .

# Build the project
# 'opam exec --' ensures the OCaml environment variables are set
RUN opam install . --deps -j 8
RUN eval $(opam env)
RUN opam exec -- dune build

# --- Stage 2: Runtime Stage ---
# We use a fresh, tiny Alpine image for the final container
FROM alpine:latest

# 1. Install the C++ and Math libraries Z3 needs (found via ldd)
RUN apk add --no-cache \
    bash gmp \
    libstdc++ libgcc z3 jq hyperfine findutils

WORKDIR /app

# Copy the compiled binary from the 'build' stage
COPY --from=build /home/opam/app/_build/default/bin/raven.exe /usr/local/bin/raven

# Copy repository of examples
COPY --from=build /home/opam/app/test ./test
COPY --from=build /home/opam/app/lib/ext ./lib/ext
COPY --from=build /home/opam/app/scripts ./scripts

# Set the command to run raven
ENTRYPOINT ["raven"]