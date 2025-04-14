#!/bin/bash

WARMUP=2
RUNS=10

EXPERIMENT1=(
  "test/comparison/arc.rav"
  "test/concurrent/treiber_stack/treiber_stack_atomics.rav"
  "test/comparison/barrier.rav"
  "test/comparison/bounded_counter.rav"
  "test/comparison/cas_counter.rav"
  "test/concurrent/lock/clh-lock.rav"
  "test/comparison/fork_join.rav"
  "test/comparison/inc_dec.rav"
  "test/comparison/lclist.rav"
  "test/concurrent/lock/mcs-lock.rav"
  "test/comparison/msc_queue.rav"
  "test/comparison/peterson.rav"
  "test/comparison/queue.rav"
  "test/concurrent/lock/spin-lock_compact.rav"
  "test/comparison/rwlock_duolock.rav"
  "test/comparison/rwlock_lockless_faa.rav"
  "test/comparison/rwlock_ticket_bounded.rav"
  "test/comparison/rwlock_ticket_unbounded.rav"
  "test/concurrent/lock/ticket-lock.rav"
  "test/comparison/barrier_client.rav"
  "test/comparison/cas_counter_client.rav"
  "test/comparison/fork_join_client.rav"
  "test/comparison/ticket_lock_client.rav"
  "test/comparison/tokens.rav"
)

EXPERIMENT2=(
  "test/concurrent/templates/ccm.rav"
  "test/concurrent/templates/flows_ra.rav"
  "test/concurrent/templates/keyset_ra.rav"
  "test/concurrent/templates/give-up.rav"
  "test/concurrent/templates/bplustree.rav"
  "test/arrays/array_utils.rav"
)

EXPERIMENT3=(
  "test/iterated-star/adt.rav"
  "test/iterated-star/array-max.rav"
  "test/iterated-star/binary-search.rav"
  "test/iterated-star/dutch-flag.rav"
  "test/iterated-star/graph_marking.rav"
  "test/rec-preds/tree_delete.rav"
)

EXPERIMENT4=(
  "test/iterated-star/adt_correct.rav"
  "test/iterated-star/adt.rav"
  "test/comparison/arc.rav"
  "test/comparison/arc_buggy.rav"
  "test/comparison/barrier.rav"
  "test/comparison/barrier_buggy.rav"
  "test/iterated-star/graph_marking_correct.rav"
  "test/iterated-star/graph_marking.rav"
  "test/comparison/lclist.rav"
  "test/comparison/lclist_buggy.rav"
  "test/comparison/peterson.rav"
  "test/comparison/peterson_buggy.rav"
  "test/comparison/rwlock_duolock.rav"
  "test/comparison/rwlock_duolock_buggy.rav"
)

# Initialize CSV file
timestamp=$(date +"%Y%m%d_%H%M%S")
CSV_FILE="./bench_results/bench_$timestamp.csv"
echo "File, Program Length, Proof Declarations, Proof Instructions, Overhead, Runtime" > "$CSV_FILE"

run_benchmark() {
  local array_name=$1
  local args=$2
  local files=("${!array_name}")
  for file in "${files[@]}"; do
    if [ -z "$file" ]; then
      echo "" >> "$CSV_FILE"
      continue
    fi

    echo "Running file $file"
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
    
    # Append statistics to CSV file
    echo "$file, $program_length, $proof_declarations, $proof_instructions, $overhead, $runtime" >> "$CSV_FILE"
  done
}

echo "STARTING EXPERIMENT 1"
echo "EXPERIMENT 1" >> "$CSV_FILE"
run_benchmark EXPERIMENT1[@]
echo "" >> "$CSV_FILE"

echo -e "\nSTARTING EXPERIMENT 2"
echo "EXPERIMENT 2" >> "$CSV_FILE"
run_benchmark EXPERIMENT2[@]
echo "" >> "$CSV_FILE"

echo -e "\nSTARTING EXPERIMENT 3"
echo "EXPERIMENT 3" >> "$CSV_FILE"
run_benchmark EXPERIMENT3[@] "-i"
echo "" >> "$CSV_FILE"

echo -e "\nSTARTING EXPERIMENT 4"
echo "EXPERIMENT 4" >> "$CSV_FILE"
run_benchmark EXPERIMENT4[@] "-i"
echo "" >> "$CSV_FILE"

echo "" >> "$CSV_FILE"
echo "WARMUP,$WARMUP" >> "$CSV_FILE"
echo "RUNS,$RUNS" >> "$CSV_FILE"

echo "Results saved in $CSV_FILE"