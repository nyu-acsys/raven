#!/bin/bash

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
  # 
  "test/comparison/rwlock_duolock.rav"
  "test/comparison/rwlock_lockless_faa.rav"
  "test/comparison/rwlock_ticket_bounded.rav"
  "test/comparison/rwlock_ticket_unbounded.rav"
  # 
  "test/comparison/fork_join_client.rav"
  #
  "test/concurrent/lock/spin-lock_compact.rav"
  "test/concurrent/lock/ticket-lock.rav"
  "test/comparison/arc.rav"
  "test/concurrent/treiber_stack/treiber_stack_atomics.rav"
  "test/concurrent/counter/counter_monotonic.rav"
  test/concurrent/templates/bplustree.rav
)

# Initialize CSV file
CSV_FILE="./benchmarks.csv"
echo "File,Program Declarations,Proof Declarations,Program Instructions,Proof Instructions,Proof Predicate Instructions,Proof Invariant Instructions,Proof Atomicity Instructions,Proof Remaining Instructions,Specification Count" > "$CSV_FILE"

for file in "${FILES[@]}"; do
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
  
  # Append statistics to CSV file
  echo "$file,$program_declarations,$proof_declarations,$program_instructions,$proof_instructions,$proof_predicate_instructions,$proof_invariant_instructions,$proof_atomicity_instructions,$proof_remaining_instructions,$specification_count" >> "$CSV_FILE"
done
