 /*execute.c*/

//
// Project: Execution of queries for SimpleSQL
//
// DONELL MAKUVIRE
// Northwestern University
// CS 211, Winter 2023
//

#include <stdbool.h> // true, false
#include <stdio.h>
#include <stdlib.h>
//
// #include any other system <.h> files?
#include <string.h>   // strcpy, strcat
#include <assert.h>
#include <ctype.h>
// assert
//
// #include any other of our ".h" files?
//

#include "tokenqueue.h"
#include "scanner.h"
#include "parser.h"
#include "ast.h"
#include "database.h"
#include "util.h"
#include "analyzer.h"
#include "resultset.h"
#include "execute.h"
//
// implementation of function(s), both private and public
//
void execute_query(struct Database* db, struct QUERY* query)
{
  if (db == NULL) panic("db is NULL (execute)");
  if (query == NULL) panic("query is NULL (execute)");

  if (query->queryType != SELECT_QUERY)
  {
    printf("**INTERNAL ERROR: execute() only supports SELECT queries.\n");
    return;
  }

  struct SELECT* select = query->q.select;  // alias for less typing:

  //
  // the query has been analyzed and so we know it's correct: the
  // database exists, the table(s) exist, the column(s) exist, etc.
  //

  //
  // (1) we need a pointer to the table meta data, so find it:
  //
  struct TableMeta* tablemeta = NULL;
  struct ResultSet* rs = resultset_create();

  for (int t = 0; t < db->numTables; t++)
  {
    if (icmpStrings(db->tables[t].name, select->table) == 0)  // found it:
    {
      tablemeta = &db->tables[t];

      for (int i = 1; i <= tablemeta->numColumns; i++){
        resultset_insertColumn(rs, i, tablemeta->name, tablemeta->columns[i-1].name, NO_FUNCTION, tablemeta->columns[i-1].colType);
      }
      
      break;
    }
  }

  // resultset_print(rs);
  assert(tablemeta != NULL);

  // 
  // (2) open the table's data file
  //
  // the table exists within a sub-directory under the executable
  // where the directory has the same name as the database, and with 
  // a "TABLE-NAME.data" filename within that sub-directory:
  //
  char path[(2 * DATABASE_MAX_ID_LENGTH) + 10];

  strcpy(path, db->name);    // name/name.data
  strcat(path, "/");
  strcat(path, tablemeta->name);
  strcat(path, ".data");

  FILE* datafile = fopen(path, "r");
  if (datafile == NULL) // unable to open:
  {
    printf("**INTERNAL ERROR: table's data file '%s' not found.\n", path);
    panic("execution halted");
    exit(-1);
  }

  //
  // (3) allocate a buffer for input, and start reading the data:
  //
  int   dataBufferSize = tablemeta->recordSize + 3;  // ends with $\n + null terminator
  char* dataBuffer = (char*)malloc(sizeof(char) * dataBufferSize);
  if (dataBuffer == NULL) panic("out of memory");

  while(true)
  {
    fgets(dataBuffer, dataBufferSize, datafile);

    if (feof(datafile)){ // end of the data file, we're done
      break;
    }
    int newRow = resultset_addRow(rs);
    char* cp = dataBuffer;
    char* end;
//make string into mini-string and print in corresponding column
    for (int i = 0; i < tablemeta->numColumns; i++){
      if (tablemeta->columns[i].colType == COL_TYPE_INT){
        end = strchr(cp, ' ');
        *end = '\0';
        resultset_putInt(rs, newRow, i+1, atoi(cp));
        cp = end + 1;
      } else if (tablemeta->columns[i].colType == COL_TYPE_STRING) {
        char startingQuote = *cp;
        cp++;
        end = cp;
        while (*end != startingQuote) {
          end++;
        }
        *end = '\0';
        resultset_putString(rs, newRow, i + 1, cp);
        cp = end + 2;

        end = cp;
      } else {
        end  = strchr(cp, ' ');
        *end = '\0';
        resultset_putReal(rs, newRow, i + 1,atoi(cp));
        cp = end + 1;
      }
    }
  }

//apply condition and display data that falls under specification  
  struct WHERE *where = select->where;
  if (where != NULL){
    for (int j = rs->numRows; j > 0; j --){
      int cols = resultset_findColumn(rs, 1, tablemeta->name, where->expr->column->name);
      
      double num;
     if (tablemeta->columns[cols - 1].colType == COL_TYPE_REAL){
        double v1 = resultset_getReal(rs, j, cols);
        double v2 = atoi(where->expr->value);
        num = v1 - v2;
      }else if (tablemeta->columns[cols - 1].colType == COL_TYPE_INT){
          int v1 = resultset_getInt(rs, j, cols);
          int v2 = atoi(where->expr->value);
          num = v1 - v2;
      }else {
        char *v1 = resultset_getString(rs, j, cols);
        char *v2 = where->expr->value;
        num = strcmp(v1,v2);
        free(v1);
      }

      switch (where->expr->operator) {
        case EXPR_GT: 
          if (num <= 0) {
          resultset_deleteRow(rs, j);
        }
        break;
        case EXPR_GTE: 
          if (num < 0){
          resultset_deleteRow(rs, j);
        }
        break;
        case EXPR_LT: 
          if (num >= 0){
          resultset_deleteRow(rs, j);
        }
        break;
        case EXPR_LTE: if (num > 0){
          resultset_deleteRow(rs, j);
        }
        break;
        case EXPR_EQUAL: if (num != 0){
          resultset_deleteRow(rs, j);
        }
        break;
         case EXPR_NOT_EQUAL: if (num == 0){
          resultset_deleteRow(rs, j);
        }
        break;
      }
    }  
  }

  //give the specified columns
   for (int k = 0; k < tablemeta->numColumns; k++){
     bool broke = false;
     struct ColumnMeta *colm = tablemeta->columns;
     struct COLUMN *allColumns = select->columns;
     struct COLUMN *trav = allColumns;

     while (trav != NULL){
       if (icmpStrings(trav->name, colm[k].name) == 0){
         broke = true;
         break;
       }
       trav = trav->next;
     }
     if (broke == false){
       int P = resultset_findColumn(rs, 1, tablemeta->name, colm[k].name);
       resultset_deleteColumn(rs, P);
     }
   }

  //apply aggregate function is specified in query
  struct COLUMN* trav = select->columns;
  int pos = 1;
  while (trav != NULL){
    int P = resultset_findColumn(rs, 1, trav->table, trav->name);
    resultset_moveColumn(rs, P, pos);
    trav = trav->next;
    pos++;
  }

  pos = 1;
  trav = select->columns;
  while (trav != NULL){
    if (trav->function != NO_FUNCTION){
      resultset_applyFunction(rs, trav->function, pos);
    }
    trav = trav->next;
    pos++;
    }
  free(trav);

  //give a limited number of results as specified in query
  struct LIMIT *lim = select->limit;
  if (lim != NULL){
    for (int r = rs->numRows; r > 0; r--){
      if (r > lim->N){
        resultset_deleteRow(rs, r);
      }
    } 
  }

  

  

  resultset_print(rs);
  resultset_destroy(rs);
  free(dataBuffer);
  fclose(datafile);

  //
  // done!
  //

}
