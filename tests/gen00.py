#! /usr/bin/env python3

# generates tests corresponding to simple automata
# INPUT:
#   state_cnt seq_len
#   letter source_state target_states # repeated
# letters leave unchanged states that aren't mentioned

from sys import argv, exit, stderr, stdin, stdout

def check(b, m):
  if not b:
    stderr.write('Invalid input: {}\n'.format(m))
    exit(2)

if len(argv) != 2:
  stderr.write('usage: {} [infer|check]\n'.format(argv[0]))
  exit(1)
comment = '// ' if argv[1] == 'infer' else ''

# read input
xs = stdin.readlines()
[state_cnt, seq_len] = [int(x) for x in xs[0].split()]
automaton = {}
for line in xs[1:]:
  ws = line.split()
  letter = ws[0]
  al = automaton.setdefault(letter, {})
  if len(ws) == 1:
    continue
  x = int(ws[1])
  ys = [int(y) for y in ws[2:]]
  check(x not in al, '(letter,src) repeated')
  al[x] = ys

# generate one procedure per letter
for letter, ts in automaton.items():
  stdout.write('procedure {}\n'.format(letter))
  for x, ys in ts.items():
    stdout.write('  {{@s={}}} (@s) {{false'.format(x))
    for y in ys:
      stdout.write('||@s={}'.format(y))
    stdout.write('}\n')
  stdout.write('  {emp')
  for x in range(1,state_cnt+1):
    if x in ts:
      stdout.write('*@s!={}'.format(x))
  stdout.write('} () {emp}\n')

# generate words, form length 0 up to length seq_len
ls = list(automaton.keys())
m = len(ls)
for n in range(seq_len + 1):
  for i in range(m ** n):
    w = []
    for _ in range(n):
      w.append(ls[i % m])
      i //= m
    stdout.write('\nprocedure seq_{}\n'.format('_'.join(w)))
    for x in range(1,state_cnt+1):
      nxt = set([x])
      for l in w:
        now = nxt
        nxt = set()
        for y in now:
          if y not in automaton[l]:
            nxt |= set([y])
          else:
            nxt |= set(automaton[l][y])
      stdout.write('  {}{{@s={}}} (@s) {{false'.format(comment, x))
      for y in nxt:
        stdout.write('||@s={}'.format(y))
      stdout.write('}\n')
    stdout.write(':');
    if w != []:
      stdout.write(' call seq_{}();'.format('_'.join(w[:-1])))
      stdout.write(' call {}();'.format(w[-1]))
    stdout.write('\n')

