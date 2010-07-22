#!/usr/bin/env python
#-*- coding: UTF-8 -*-

# utilitaires pour manipuler la BDD

import sys


# différences de résultats entre les 2 prouveurs
def diff(cursor, prover1, prover2):
  "trouve les (file,goal) dont le résultat est différent\
  pour prover1 et prover2"

  query = """SELECT r1.file, r1.goal, r1.prover, r1.result, r2.prover, r2.result
    FROM runs r1
    INNER JOIN runs r2
    WHERE r1.prover = "%s" AND r2.prover = "%s"
      AND r1.file = r2.file AND r1.goal = r2.goal
      AND r1.result <> r2.result""" % \
      (prover1, prover2)
  try:
    result = cursor.execute(query)
    return result.fetchall()
  except Exception, e:
    print >> sys.stderr, "exception :", repr(e)
    return []


# (file,goal) sur lesquels le premier prouveur est meilleur que le second
def superior(cursor, prover1, prover2):
  "trouve les (file,goal) pour lesquels prover1 > prover2"

  query = """SELECT distinct r1.file, r1.goal
    FROM runs r1
    INNER JOIN runs r2
    WHERE r1.prover = "%s" AND r2.prover = "%s"
      AND r1.file = r2.file AND r1.goal = r2.goal
      AND r1.result = "Valid"
      AND r2.result <> "Valid"
    """ % (prover1, prover2)

  try:
    result = cursor.execute(query)
    return result.fetchall()
  except Exception, e:
    print >> sys.stderr, "exception :", repr(e)
    return None


# affichage aligné en colonnes
def print_columns(lines, sep = u"."):
  "affiche les colonnes bien alignées"
  sep = unicode(sep)
  if len(lines) == 0:
    return
  column_width = len(lines[0])
  widths = [0 for x in xrange(column_width)]
  # calculer la largeur de chaque colonne (max des largeurs de ses éléments)
  for line in lines:
    for i in xrange(column_width-1):
      widths[i] = max(widths[i], len(unicode(line[i])))

  for line in lines:
    for i in xrange(column_width-1):
      assert(len(unicode(line[i])) <= widths[i])
      item = unicode(line[i])
      item = item.ljust(widths[i]+2, sep)
      print item,
    print line[-1]


# petite facilité
def print_sep():
  "affiche une ligne de '-' pour séparer clairement des\
  sections de l'affichage"
  print "---------------------------------------------------------------"


# effacer la ligne courante du terminal
def erase_line(stream = sys.stdout):
  "efface la ligne et revient au début"
  stream.write("\033[2K\r")
  stream.flush()


# récupéré sur le net, pour obtenir largeur et hauteur du terminal
def getTerminalSize():
  "récupère la largeur et la hauteur du terminal"
# {{{
  def ioctl_GWINSZ(fd):
    try:
      import fcntl, termios, struct, os
      cr = struct.unpack('hh', fcntl.ioctl(fd, termios.TIOCGWINSZ, '1234'))
    except:
      return None
    return cr
  cr = ioctl_GWINSZ(0) or ioctl_GWINSZ(1) or ioctl_GWINSZ(2)
  if not cr:
    try:
      fd = os.open(os.ctermid(), os.O_RDONLY)
      cr = ioctl_GWINSZ(fd)
      os.close(fd)
    except:
        pass
  if not cr:
    try:
      cr = (env['LINES'], env['COLUMNS'])
    except:
      cr = (25, 80)
  return int(cr[1]), int(cr[0])
# }}}



# tente d'affichier un tableau donné en entrée. Ce tableau
# est un dictionnaire (colonne,ligne) -> item qui doit vérifier
# la propriété suivante :
# pour tout (i,j) dans tab, (j,i) est aussi dans tab
def printTab(tab):
  "affiche le tableau carré donné en entrée"

  items = list(set( [unicode(x) for (x,y) in tab.keys()] )) # enlever doublons
  for i in items:
    tab[ (None,i) ] = i # pour la première ligne

  max_width = 0
  normal_sum = 0
  for i in items:
    max_width = max(max_width, len(i)+1)
    normal_sum += len(i) + 1

  width,height = getTerminalSize()
  if max_width * (len(items)+1)  >= width: # ça ne rentre pas
    print >> sys.stderr, "terminal trop étroit"
    max_width = width / (len(items) + 1)

  def print_line(item):
    if item != None:
      sys.stdout.write(item[:max_width-1].ljust(max_width-1, " ")+"|")
    else:
      sys.stdout.write("x\y : x>y".ljust(max_width-1, " ")+"|")
    for i in xrange(len(items)):
      i = items[i]
      if i == item:
        sys.stdout.write("x".ljust(max_width, " "))
      else:
        num = unicode(tab[ (item,i) ])
        sys.stdout.write(num[:max_width-1].ljust(max_width, " "))
    sys.stdout.write("\n")

  print "légende : [colonne] est meilleur que [ligne] sur [case] buts\n"
  print_line(None)
  for i in items:
    print("-"*(len(items)+1)*max_width)
    print_line(i)

  for i in items:
    try:
      del tab[ (None,i) ]
    except:
      pass

