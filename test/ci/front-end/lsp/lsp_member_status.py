import json
import sys

# Prints the status of each member from the JSON on the last line of stdin, or - if it
# has none, whether a module inherits it, and for a module the number of its members
# with each status.
output = json.loads(sys.stdin.read().splitlines()[-1])
for member in output['members']:
    counts = [f'{status}={n}' for status, n in member.get('counts', {}).items()]
    inherited = ['inherited'] if member.get('inherited') else []
    print(' '.join([str(member['start_line']), member['kind'], member['name'], member.get('status', '-')]
                   + inherited + counts))
