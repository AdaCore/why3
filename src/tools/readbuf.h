#ifndef READBUF_H
#define READBUF_H

// Implement a read buffer, which is intended to be used for read/ReadFile
// operations. Before doing a read of <n> bytes, call <prepare_read> with <n>
// as argument. After the read, register the number of bytes read using
// <have_read>. You can then inspect the read buffer and call "have taken" to
// indicate how many bytes have been taken out.

typedef struct {
  char* data;
  int len;
  int capacity;
} t_readbuf, *preadbuf;

// return a read buf of initial capacity <capacity>
preadbuf init_readbuf(int capacity);

// return a pointer to a memory region which is unused and can act as a buffer
// for a read operation reading up to size bytes
char* prepare_read(preadbuf b, int size);

//notify the buffer that <size> bytes have been read
void have_read(preadbuf b, int size);

// allow the readbuf to delete the first <size> byte of the buffer
void have_taken(preadbuf b, int size);

// allow the readbuf to all of the buffer
void clear_readbuf(preadbuf b);

// free the memory associated with the buffer
void free_readbuf(preadbuf b);

#endif
