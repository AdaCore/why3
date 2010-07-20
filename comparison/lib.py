#!/usr/bin/env python
#-*- coding: UTF-8 -*-

# utilitaires pour manipuler la BDD

import sys




def diff(cursor, prover1, prover2):
  "trouve les (file,goal) dont le résultat est différent\
  pour prover1 et prover2"

  query = """SELECT distinct r1.file, r1.goal, r1.prover, r1.result, r2.prover, r2.result
    FROM runs r1 JOIN runs r2
    WHERE r1.prover = "%s" and r2.prover = "%s" and r1.result <> r2.result""" % \
      (prover1, prover2)
  try:
    result = cursor.execute(query)
    return result.fetchall()
  except Exception, e:
    print >> sys.stderr, "exception :", repr(e)
    return []


def superior(cursor, prover1, prover2):
  "trouve les (file,goal) pour lesquels prover1 > prover2"

  query = """SELECT distinct r1.file, r1.goal
    FROM runs r1 JOIN runs r2
    WHERE r1.prover = "%s" AND r2.prover = "%s"
      AND r1.result = "Valid"
      AND r2.result = "Timeout"
      AND r1.file = r2.file AND r1.goal = r2.goal
    """ % (prover1, prover2)

  try:
    result = cursor.execute(query)
    return result.fetchall()
  except Exception, e:
    print >> sys.stderr, "exception :", repr(e)
    return None



def print_columns(lines, sep = "."):
  "affiche les colonnes bien alignées"
  if len(lines) == 0:
    return
  column_width = len(lines[0])
  widths = [0 for x in xrange(column_width)]

  for line in lines:
    for i in xrange(column_width-1):
      widths[i] = max(widths[i], len(unicode(line[i])))

  for line in lines:
    for i in xrange(column_width-1):
      assert(len(unicode(line[i])) <= widths[i])
      print unicode(line[i]).ljust(widths[i]+2, sep),
    print line[-1]


def print_sep():
  "affiche une ligne de '-' pour séparer clairement des sections de l'affichage"
  print "---------------------------------------------------------------"



def erase_line(stream = sys.stdout):
  "efface la ligne et revient au début"
  stream.write("\033[2K\r")
  stream.flush()
