#!/usr/bin/env python3
# shell of a program to convert statements in YAGO into an SQL database and update them to be current with SUMO
# depends upon setting a $YAGO environment variable to point to where you have expanded the YAGO files

import sys
import sqlite3
import os

map = dict()

def readMap():
    with open("$YAGO/yago-sumo-mappings.txt", mode='r') as f:
        content = f.read()
        thelist = content.splitlines()
        f.close()
        for l in thelist:
            pair = l.split(" ")
            map.update([pair[0],pair[1]])

def assertFact(args, sqliteConnection):
    # insert into arity (pred,value) values ("capitalCity",2);
    # insert into stmts (pred,arg1,arg2,arg3) values ("domain","birthdate","1","str");
    cursor = sqliteConnection.cursor()
    #print('DB Init')
    query = 'insert into stmts (pred,arg1,arg2) values ("' + args[0] + '","' + args[1] + '","' + args[2] + '");'
    #print(query)
    cursor.execute(query)
    sqliteConnection.commit()

def readFiles(sqliteConnection):
    for filename in os.listdir("$YAGO"):
        filepath = os.path.join("$YAGO", filename)
        with open(filepath, mode='r') as f:
            content = f.read()
            thelist = content.splitlines()
            f.close()
            for l in thelist:
                l = l[1:len(l)-1]
                args = l.split(" ")
                newargs = []
                for arg in args:
                    if map.keys.contains(arg):
                        newargs.add(map.get(arg))
                    else:
                        newargs.add(arg)
                    assertFact(newargs,sqliteConnection)

if __name__ == "__main__":
    readMap()
    try:
        sqliteConnection = sqlite3.connect('$XDB/db/yago.db')
        cursor = sqliteConnection.cursor()
        #print('DB Init')
        query = 'SELECT city FROM capitals WHERE country="' + args[1] + '";'
        #print(query)
        cursor.execute(query)
        sqliteConnection.commit()
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
  
