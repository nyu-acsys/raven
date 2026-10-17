import json
import sys

# Prints each name the program in argv[1] uses, from the JSON on the last line of stdin:
# its text, what it refers to, where that is declared, and the first line of its hover.
source = open(sys.argv[1]).read().split('\n')
output = json.loads(sys.stdin.read().splitlines()[-1])
symbols = output['symbols']
for reference in output['references']:
    symbol = symbols[reference['symbol']]
    definition = symbol['definition']
    text = source[reference['line'] - 1][reference['start_col']:reference['end_col']]
    detail = symbol.get('detail', '').split('\n')[0]
    print(f"{reference['line']}:{reference['start_col']} {text} -> {symbol['name']} "
          f"({symbol['kind']}, {definition['file'].split('/')[-1]}:{definition['start_line']}): {detail}")
