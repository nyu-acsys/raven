#!/bin/bash

WARMUP=0
RUNS=2
OPAM_SWITCH="raven"

opam switch $OPAM_SWITCH

eval $(opam env --switch=$OPAM_SWITCH)



# Array of extensions to count
EXT_LIST=(
  "lib/ext/atomicExt"
  "lib/ext/errorCreditsExt"
  "lib/ext/prophecyExt"
  "lib/ext/listExt"
)

EXAMPLES=(
  "test/ext_error-credits/amortised_hash.rav"
  "test/ext_error-credits/cf_hashmap.rav"
  "test/ext_error-credits/ec_dynamic_vec.rav"
# 
  "test/ext_prophecy/clairvoyant_coin.rav"
  "test/ext_prophecy/lazy_coin.rav"
  "test/ext_prophecy/rdcss.rav"
)


count_line() {
  # Print table header
  printf "%-20s %12s %12s %12s %12s %12s\n" "Extension" "Total LoC" "Parser LoC" "AstDef LoC" "Typing LoC" "Rewrite LoC" 
  printf "%s\n" "========================================================================================"

  # Counter for totals
  total_parser=0
  total_lines=0
  total_astdef=0
  total_typing=0
  total_rewrites=0

  # Process each extension
  for ext in "${EXT_LIST[@]}"; do
    ext_name=$(basename "$ext")
    
    # Run cloc on the extension directory for total OCaml lines
    total=$(cloc "$ext" --json 2>/dev/null | jq '.OCaml.code // 0')
    
    # Find the main .ml file in the extension
    main_file=$(find "$ext" -maxdepth 1 -name "*.ml" | grep -v _parser | head -1)
    
    astdef=0
    typing=0
    rewrites=0
    parser=0
    
    if [ -n "$main_file" ]; then
      # Call count_sections.sh with --csv flag and parse output
      while IFS=',' read -r file section lines; do
        if [ "$file" != "File" ]; then  # Skip header
          case "$section" in
            "AstDef") astdef=$lines ;;
            "Typing") typing=$lines ;;
            "Rewrites") rewrites=$lines ;;
          esac

          parser=$(cloc "${ext}/${ext_name}_parser.mly" --json 2>/dev/null | jq '.OCaml.code // 0')
        fi
      done < <(./scripts/count_sections.sh "$main_file" --csv)
    fi
    
    # Print the row
    printf "%-20s %12s %12s %12s %12s %12s\n" "$ext_name" "$total" "$parser" "$astdef" "$typing" "$rewrites" 
    
    # Add to totals
    total_parser=$((total_parser + parser))
    total_lines=$((total_lines + total))
    total_astdef=$((total_astdef + astdef))
    total_typing=$((total_typing + typing))
    total_rewrites=$((total_rewrites + rewrites))
  done

  # Print separator and total
  printf "%s\n" "========================================================================================"
  printf "%-20s %12s %12s %12s %12s %12s\n" "Total" "$total_lines" "$total_parser" "$total_astdef" "$total_typing" "$total_rewrites"
}


run_benchmark() {
  # local array_name=$1
  local args=$2
  # local files=("${!array_name}")
  # Print table header
  printf "%-45s %10s %10s %10s %10s %10s\n" "File" "ProgLen" "ProofDecl" "ProofInstr" "Overhead" "Runtime(s)"
  printf "%-45s %10s %10s %10s %10s %10s\n" "$(printf '%.0s=' {1..45})" "$(printf '%.0s=' {1..10})" "$(printf '%.0s=' {1..10})" "$(printf '%.0s=' {1..10})" "$(printf '%.0s=' {1..10})" "$(printf '%.0s=' {1..10})"

  for file in "${EXAMPLES[@]}"; do
    if [ -z "$file" ]; then
      echo ""
      continue
    fi

    # echo "Running file $file"
    line_count=$(wc -l < "$file")
    output=$(raven "$file" --stats)
    
    # Extract statistics from the output
    program_declarations=$(echo "$output" | grep "Program Declarations" | awk '{print $3}')
    proof_declarations=$(echo "$output" | grep "Proof Declarations" | awk '{print $3}')
    program_instructions=$(echo "$output" | grep "Program Instructions" | awk '{print $3}')
    proof_instructions=$(echo "$output" | grep "Proof Instructions" | awk '{print $3}')
    proof_predicate_instructions=$(echo "$output" | grep "Proof Predicate Instructions" | awk '{print $4}')
    proof_invariant_instructions=$(echo "$output" | grep "Proof Invariant Instructions" | awk '{print $4}')
    proof_atomicity_instructions=$(echo "$output" | grep "Proof Atomicity Instructions" | awk '{print $4}')
    proof_remaining_instructions=$(echo "$output" | grep "Proof Remaining Instructions" | awk '{print $4}')
    specification_count=$(echo "$output" | grep "Specification Count" | awk '{print $3}')

    # Ensure numeric defaults for calculations
    program_declarations=${program_declarations:-0}
    program_instructions=${program_instructions:-0}
    proof_declarations=${proof_declarations:-0}
    proof_instructions=${proof_instructions:-0}
    specification_count=${specification_count:-0}

    program_length=$((program_declarations + program_instructions))
    proof_declarations=$((proof_declarations + specification_count))

    # Compute overhead
    if [ "$program_length" -eq 0 ]; then
      overhead="n/a"
    else
      overhead=$(echo "scale=2; ($proof_declarations + $proof_instructions) / $program_length" | bc)
    fi

    # Run hyperfine to measure runtime
    runtime=$(hyperfine --warmup $WARMUP --runs $RUNS $args "raven \"$file\"" --export-json /tmp/hyperfine.json)
    runtime=$(jq '.results[0].mean' /tmp/hyperfine.json)
    runtime=$(printf "%.3f" "$runtime")
    
    # Print formatted table row to stdout (skip first 5 chars of filename for aesthetics)
    printf "%-45s %10s %10s %10s %10s %10s\n" "${file:5}" "$program_length" "$proof_declarations" "$proof_instructions" "$overhead" "$runtime"
  done
}


echo "Table 1: Extensions by OCaml LoC (with Section Breakdown)"
count_line
echo

echo "Table 2: Program Overhead and Runtimes for Benchmark Examples"
run_benchmark
