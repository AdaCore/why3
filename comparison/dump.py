#!/usr/bin/env python
#-*- coding: UTF-8 -*-

# ce script affiche le contenu de la base de données

import sys
import sqlite3

db_file = "output.db"

if len(sys.argv) > 1:
  db_file = sys.argv[1]

print >> sys.stderr, "utile la database", db_file

conn = sqlite3.connect(db_file)
cursor = conn.cursor()

try:
  dump = cursor.execute("select * from runs")
except:
  print >> sys.stderr, "database %s non valide !" % db_file
  sys.exit(1)


dump = dump.fetchall()

import lib

lib.print_columns(dump)
