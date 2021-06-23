def even (start, stop):
  #@ ensures forall i. 0 <= i < len(result) -> result[i] % 2 == 0
  step = 0
  deb = 0
  if start < stop:
    step = 2
  else:
    step = -2
  if start % 2 == 0:
    deb = start
  else:
    deb = start + 1
  return range(deb, stop, step)