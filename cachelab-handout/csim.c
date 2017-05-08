#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <unistd.h>
#include <getopt.h>
#include "cachelab.h"

static int v = 0, s = 0, E = 0, b = 0;

static struct Line{
  bool isValid;
  unsigned long tag;
  char *block;
}**Sets;

static struct Sum{
  int hits;
  int misses;
  int evictions;
}*Summary;

static struct Node{
  int index;
  struct Node *next;
}**head, **tail;

static char detail[100];

int initCache();
int readTrace(char *target); 
int process(char access_type, unsigned long address, int size); 
int loadCache(char access_type, unsigned long address, unsigned long tag,
  unsigned long setIndex, struct Line *Set); 
int excitedLRU(unsigned long setIndex, int EIndex);
int verbose(char access_type, unsigned long address, int size, char *operate);

int main(int argc, char **argv)
{
    int c = 0;
    char *target = NULL;
    while((c = getopt(argc, argv, "hvs:E:b:t:")) != -1){
      switch(c) {
        case 'v':
	  v = 1;
	  break;
	case 's':
	  s = atoi(optarg);
	  break;
	case 'E':
	  E = atoi(optarg);
	  break;
	case 'b':
	  b = atoi(optarg);
	  break;
	case 't':
	  target = optarg;
	  break;
	case 'h':
	  printf("help\n");
	default:
	  printf("Usage:-v -s -E -b -t\n");
	  abort();
      }
    }
    if (s == 0 || E == 0 || b == 0 || target == NULL) {
      printf("Usage: ...\n");
      abort();
    }
    initCache();
    readTrace(target);
    printSummary(Summary->hits, Summary->misses, Summary->evictions);
    return 0;
}
int initCache(){
  int S = 1 << s;
  int B = 1 << b;
  Sets = malloc(S*sizeof(struct Line*));
  struct Line *Set;
  for (int i = 0; i < S; i++) {
    Set = *(Sets + i) = malloc(E*sizeof(struct Line));
    for (int j = 0; j < E; j++) {
      (Set + j)->block = malloc(B*sizeof(char));
      (Set + j)->isValid = 0;
    }
  }

  Summary = malloc(sizeof(struct Sum));
  Summary->hits = 0;
  Summary->misses = 0;
  Summary->evictions = 0;

  head = malloc(S * sizeof(struct Node*));
  tail = malloc(S * sizeof(struct Node*));
  for (int i = 0; i < S; i++) {
    struct Node *cur;
    struct Node *node = malloc(sizeof(struct Node));
    node->index = 0;
    *(head + i) = node;
    cur = node;
    for (int j = 1; j < E; j++) {
      node = malloc(sizeof(struct Node));
      node->index = j;
      cur->next = node;
      cur = cur->next;
    }
    node->next = NULL;
    *(tail + i) = node;
  }
  if (Sets == NULL || head == NULL || tail == NULL) {
    printf("malloc failed\n");
    abort();
  }
  return 0;
}

int readTrace(char *target) {
  FILE *pFile; 
  pFile = fopen(target,"r");
  char access_type;
  unsigned long address;
  int size;
  while(fscanf(pFile, " %c %lx,%d", &access_type, &address, &size) > 0){
    if (access_type != 'L'&& access_type != 'M' && access_type != 'S') continue; 
    process(access_type, address, size); 
  }
  return 0;
}

int process(char access_type, unsigned long address, int size) {
  memset(detail,0,sizeof(detail));
  int t = 64 - s - b;
  unsigned long tag = address >> (s + b);
  unsigned long setIndex = (address << t) >> (t + b);
 // unsigned long bOffset = (address << (s + t)) >> (s + t); 
  struct Line *Set = *(Sets + setIndex);
  int index = 0;
  while ((Set + index)->tag != tag && index < E - 1) index++;
  struct Line *line = Set + index;
  if (line->tag == tag && line->isValid == 1) {
    Summary->hits++;
    excitedLRU(setIndex,index);
    strcat(detail," hit");
  } else {
    Summary->misses++;
    strcat(detail," miss");
    loadCache(access_type,address,tag,setIndex,Set); 
  }
  if (access_type == 'M') {
    Summary->hits++;
    strcat(detail," hit");
  }
  verbose(access_type, address, size, detail);
  return 0;
}

int loadCache(char access_type, unsigned long address, unsigned long tag,
  unsigned long setIndex, struct Line *Set) {
  int index = 0;
  while ((Set + index)->isValid == 1 && index < E - 1) index++;
  struct Line *line = Set + index;
  if (line->isValid == 0) {
    line->isValid = 1;
  } else {
    strcat(detail," eviction");
    Summary->evictions++;
    index = (*(tail + setIndex))->index;
    line = Set + index;
   /*@TODO
      ...
      restore the block data of Set
    */
  }
  /*@TODO
    cache the data from memory
  */
  line->tag = tag;
  excitedLRU(setIndex, index);
  return 0;
}

int excitedLRU(unsigned long setIndex, int EIndex) {
  if (E <= 1) return 0;
  struct Node *cursor = *(head + setIndex);
  struct Node *preCursor;
  while (EIndex != cursor->index) {
    preCursor = cursor;
    cursor = cursor->next;
  }
  if (cursor == *(tail + setIndex)) *(tail + setIndex) = preCursor;

  if (cursor != *(head + setIndex) && cursor != NULL) {
    preCursor->next = cursor->next;
    cursor->next = *(head + setIndex);
    *(head + setIndex) = cursor;
  }
  return 0;
}

int verbose(char access_type, unsigned long address, int size, char* operate){
  if (v == 1) printf("%c %lx,%d%s \n",access_type,address,size,operate);
  return 0;
}

