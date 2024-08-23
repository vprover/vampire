#!/usr/bin/env python3

import sys, os
import sqlite3
from typing import Iterable, Sequence

#CREATE TABLE stmts(pred text NOT NULL, arg1 text NOT NULL, arg2 text NOT NULL, arg3 text, arg4 text, arg5 text);
#CREATE TABLE arity (pred text NOT NULL, value integer NOT NULL);

debug = False

def init():
  path = os.getenv('XDB')
  if debug:
    print(path)
  sqliteConnection = sqlite3.connect(path + '/db/stmts.db')
  cursor = sqliteConnection.cursor()
  return sqliteConnection, cursor
    
def decompQuery(q:str):
  pred,rest = q.split("(")
  assert rest.endswith(")")
  rest = rest[:-1]
  args = rest.split(",")
  return pred, args

def buildQuery(pred:str, args:Sequence):
  query = 'SELECT '
  hasArg = 0
  for n in range(0,len(args)):
    if debug:
      print("n:",n)
    if (args[n].istitle()):
      query = query + 'arg' + str(n+1) + ', '
      hasArg = 1
  if hasArg:
    query = query[0:(len(query)-2)]
  else:
    query = 'SELECT *'
  query = query + ' FROM stmts'
  selection = "pred='" + pred + "'"
  hasArg = 0
  for n in range(0,len(args)):
    if not (args[n].istitle()):
      selection = selection + 'AND arg' + str(n+1) + '="' + args[n] + '" '
      hasArg = 1       
  if selection:
    query = query + " WHERE " + selection + ";"
  return query

def processResults(results:Iterable, pred:str, args:Sequence):
  if results == []:
    return ""
  resstr = ""
  for res in results:
    if debug:
      print('result: ',res)
    resstr = resstr + pred + "("
    resindx = 0
    for n in range(0,len(args)):
      if debug:
        print('in progress: ',resstr)
      if (args[n].istitle()):
        resstr = resstr + res[resindx]
        resindx = resindx + 1
      else:
        resstr = resstr + args[n]
      if n == len(args)-1:
        resstr = resstr + ")\n"
      else:
        resstr = resstr + ","
  return resstr
    
if __name__ == "__main__":
  sqliteConnection = None
  try:
    sqliteConnection, cursor = init()
    pred,args = decompQuery(sys.argv[1])
    if debug:
      print('DB Init')
    query = buildQuery(pred,args)
    if debug:
      print("query: ",query)
    cursor.execute(query)
    results = cursor.fetchall()
    if debug:
      print("results:", results)
    resstr = processResults(results,pred,args)
    if debug:
      print("results: ")
    print(resstr)
    cursor.close()

  # Handle errors
  except sqlite3.Error as error:
    print('Error occurred - ', error)

  # Close DB Connection irrespective of success
  # or failure
  finally:
    if sqliteConnection:
        sqliteConnection.close()
        #print('SQLite Connection closed')

  exit(0)

