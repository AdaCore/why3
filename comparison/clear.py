#!/usr/bin/env python
#-*- coding: UTF-8 -*-

# ce script affiche le contenu de la base de données

import sys
import sqlite3

# demander confirmation pour effacer la base
print "ceci va effacer la base de tests. Continuer ?"
while True:
  confirm = raw_input("[y/n] ")
  if confirm in ["y","yes","Y","Yes"]:
    break
  elif confirm in ["n","No","N","no"]:
    sys.exit(0)

# on veut effacer la base. Pour cela, il faut d'abord s'y connecter.
conn = sqlite3.connect("output.db")
cursor = conn.cursor()

try:
  cursor.execute("delete from runs")
  cursor.close()
  conn.commit()
  conn.close()
except:
  print >> sys.stderr, "database non valide !"
  sys.exit(1)

print >> sys.stderr, "cleanup terminé !"
