#!/usr/bin/env python3

import sys, os
import sqlite3
from typing import Iterable, Sequence

#CREATE TABLE stmts(pred text NOT NULL, arg1 text NOT NULL, arg2 text NOT NULL, arg3 text, arg4 text, arg5 text);
#CREATE TABLE arity (pred text NOT NULL, value integer NOT NULL);

def init():
  sqliteConnection = sqlite3.connect('/Users/msuda/Projects/vampire/xDB/stmts-composers.db')
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
    #print(n)
    if (args[n].istitle()):
      query = query + 'arg' + str(n+1) + ', '
      hasArg = 1
  if hasArg:
    query = query[0:(len(query)-2)]
  else:
    query = 'SELECT *'
  query = query + ' FROM stmts'
  selection = ""
  hasArg = 0
  for n in range(0,len(args)):
    if not (args[n].istitle()):
      selection = selection + 'arg' + str(n+1) + '="' + args[n] + '" AND '
      hasArg = 1
  if hasArg:
    selection = selection[0:(len(selection)-5)]        
  if selection:
    query = query + " WHERE " + selection + ";"
  return query

def processResults(results:Iterable, pred:str, args:Sequence):
    for res in results:
      resstr = pred + "("
      resindx = 0
      for n in range(0,len(args)):
        #print('result: ',result)
        #print('in progress: ',resstr)
        if (args[n].istitle()):
          resstr = resstr + res[resindx]
          resindx = resindx + 1
        else:
          resstr = resstr + args[n]
        if n == len(args)-1:
          resstr = resstr + ")"
        else:
          resstr = resstr + ","
    return resstr
    
if __name__ == "__main__":
  try:
    sqliteConnection, cursor = init()
    pred,args = decompQuery(sys.argv[1])
    #print('DB Init')
    query = buildQuery(pred,args)
    #print("query: ",query)
    cursor.execute(query)
    results = cursor.fetchall()
    resstr = processResults(results,pred,args)
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

