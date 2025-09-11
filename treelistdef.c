#include<stdlib.h>
#include<stdbool.h>

struct sll {int key; struct sll *next;};
typedef struct sll **sllbox;

//character sll
struct sllc {char key; struct sll *next;};
typedef struct sllc **sllboxc;

struct tree {int key; int value; struct tree *left, *right;};
typedef struct tree **treebox;

void dummylist()
{
   struct sll *sllDummy = (struct sll *) malloc (sizeof *sllDummy);
   free(sllDummy);
}

void dummylistc()
{
   struct sllc *sllcDummy = (struct sllc *) malloc (sizeof *sllcDummy);
   free(sllcDummy);
}

void dummyTree()
{
    struct tree *treeDummy = (struct tree *) malloc (sizeof *treeDummy);
    free(treeDummy);
}