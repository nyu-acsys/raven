#!/bin/bash

# Script to count lines of code per section in a file
# Usage: ./count_sections.sh <filepath> [--csv]
# With --csv flag, output is comma-separated for easy parsing

SECTIONS=(
  "AstDef"
  "Typing"
  "Rewrites"
)

if [ -z "$1" ]; then
  echo "Usage: $0 <filepath> [--csv]"
  exit 1
fi

filepath="$1"
csv_mode="$2"

if [ ! -f "$filepath" ]; then
  echo "Error: File '$filepath' not found"
  exit 1
fi

# Print table header (or CSV header)
if [ "$csv_mode" = "--csv" ]; then
  printf "File,Section,Lines\n"
else
  printf "%-30s %15s\n" "Section" "Lines of Code"
  printf "%s\n" "================================================"
fi

# Counter for total
total_lines=0

# Process each section in order
for section_name in "${SECTIONS[@]}"; do
  # Find line number of section marker
  section_line=$(grep -n "(\* $section_name \*)" "$filepath" | cut -d: -f1 | head -1)
  
  # If section not found, skip it
  if [ -z "$section_line" ]; then
    continue
  fi
  
  # Find the next section marker or use end of file
  next_section_line=$(tail -n +$((section_line + 1)) "$filepath" | grep -n "(\* [A-Za-z]* \*)" | head -1 | cut -d: -f1)
  
  if [ -n "$next_section_line" ]; then
    end_line=$((section_line + next_section_line - 2))
  else
    end_line=$(wc -l < "$filepath")
  fi
  
  # Extract section to temp file
  temp_file="/tmp/section_${section_name// /_}.ml"
  sed -n "${section_line},${end_line}p" "$filepath" > "$temp_file"

  
  # Run cloc on the temp file, count only OCaml code
  result=$(cloc "$temp_file" 2>/dev/null | grep "^OCaml" | awk '{print $NF}')
  
  # If cloc returns nothing, count non-empty, non-comment lines manually
  if [ -z "$result" ]; then
    result=$(grep -v "^\s*$" "$temp_file" | grep -v "^\s*(\*" | wc -l)
  fi
  
  # Clean up temp file
  rm -f "$temp_file"
  
  # Print the row (CSV or table format)
  if [ "$csv_mode" = "--csv" ]; then
    printf "%s,%s,%s\n" "$(basename "$filepath")" "$section_name" "$result"
  else
    printf "%-30s %15s\n" "$section_name" "$result"
  fi
  
  # Add to total
  total_lines=$((total_lines + result))
done

# Print separator and total (only in table mode)
if [ "$csv_mode" != "--csv" ]; then
  printf "%s\n" "================================================"
  printf "%-30s %15s\n" "Total" "$total_lines"
fi
