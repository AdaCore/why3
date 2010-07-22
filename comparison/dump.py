#!/usr/bin/env python
#-*- coding: UTF-8 -*-

# ce script affiche le contenu de la base de données

import sys
import sqlite3

# ouvrir la DB
db_file = "output.db"

if len(sys.argv) > 1:
  db_file = sys.argv[1]

print >> sys.stderr, "utile la database", db_file

conn = sqlite3.connect(db_file)
cursor = conn.cursor()

# essayer de dumper la table runs (échoue si elle n'existe pas)
try:
  dump = cursor.execute("select * from runs")
  dump = dump.fetchall()
except:
  print >> sys.stderr, "database %s non valide !" % db_file
  sys.exit(1)

# afficher le dump
import lib

lib.print_columns(dump)
