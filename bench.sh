#!/bin/bash

WARMUP=0
RUNS=1

FILES=(
  "test/comparison/peterson.rav"
  "test/comparison/bounded_counter.rav"
  "test/comparison/inc_dec.rav"
  "test/comparison/lclist.rav"
  "test/comparison/barrier.rav"
  "test/concurrent/lock/clh-lock.rav"
  "test/comparison/fork_join.rav"
  "test/concurrent/lock/mcs-lock.rav"
  "test/comparison/msc_queue.rav"
  "test/comparison/queue.rav"
  ""
  "test/comparison/rwlock_duolock.rav"
  "test/comparison/rwlock_lockless_faa.rav"
  "test/comparison/rwlock_ticket_bounded.rav"
  "test/comparison/rwlock_ticket_unbounded.rav"
  "" 
  "test/comparison/fork_join_client.rav"
  "test/comparison/cas_counter_client.rav"
  "test/comparison/barrier_client.rav"
  "test/comparison/ticket_lock_client.rav"
  ""
  "test/concurrent/lock/spin-lock_compact.rav"
  "test/concurrent/lock/ticket-lock.rav"
  "test/comparison/arc.rav"
  "test/concurrent/treiber_stack/treiber_stack_atomics.rav"
  "test/comparison/cas_counter.rav"
  ""
  "test/comparison/tokens.rav"
  ""
  "test/concurrent/templates/ccm.rav"
  "test/concurrent/templates/flows_ra.rav"
  "test/concurrent/templates/keyset_ra.rav"
  "test/concurrent/templates/give-up.rav"
  "test/concurrent/templates/bplustree.rav"
  "test/arrays/array.rav" "test/arrays/ordered_array.rav" 
)

# Initialize CSV file
timestamp=$(date +"%Y%m%d_%H%M%S")
CSV_FILE="./bench_results/bench_$timestamp.csv"
echo "File,Program Length,Proof Declarations,Proof Instructions,Runtime" > "$CSV_FILE"

for file in "${FILES[@]}"; do
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

  # Run hyperfine to measure runtime
  runtime=$(hyperfine --warmup $WARMUP --runs $RUNS "raven \"$file\"" --export-json /tmp/hyperfine.json)
  runtime=$(jq '.results[0].mean' /tmp/hyperfine.json)
  runtime=$(printf "%.3f" "$runtime")
  
  # Append statistics to CSV file
  echo "$file,$program_length,$proof_declarations,$proof_instructions,$runtime" >> "$CSV_FILE"
done