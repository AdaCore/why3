#ifdef _WIN32
# include <windows.h>
#else
# include <sys/socket.h>
# include <sys/types.h>
# include <sys/un.h>
# include <unistd.h>
# include <errno.h>
#endif
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <assert.h>
#include <stdio.h>

#ifdef _WIN32
HANDLE pipe;

CAMLprim value c_client_connect(value v) {
   CAMLparam1(v);
   char *basename;
   char *socket_name;
   unsigned namelen;
   basename = String_val(v);
   namelen = caml_string_length(v);
   socket_name = (char*) malloc(sizeof(char) * (namelen + 10));
   strcpy(socket_name, TEXT("\\\\.\\pipe\\"));
   strcat(socket_name, basename);
   pipe = CreateFile(
         socket_name,   // pipe name
         GENERIC_READ |  // read and write access
         GENERIC_WRITE,
         0,              // no sharing
         NULL,           // default security attributes
         OPEN_EXISTING,  // opens existing pipe
         0,              // default attributes
         NULL);
   CAMLreturn(Val_unit);
}

CAMLprim value c_client_disconnect(value unit) {
   CAMLparam1(unit);
   CloseHandle(pipe);
   CAMLreturn(Val_unit);
}


CAMLprim value c_send_request_string(value v) {
   CAMLparam1(v);
   char *msg;
   int to_write, pointer;
   DWORD written;
   BOOL res;
   msg = String_val(v);
   to_write = caml_string_length(v);
   pointer = 0;
   while (pointer < to_write) {
      res = WriteFile(
         pipe,                  // pipe handle
         msg+pointer,           // message
         to_write-pointer,              // message length
         &written,              // bytes written
         NULL);
      pointer += written;
   }
   CAMLreturn(Val_unit);
}

CAMLprim value c_read_from_client(value unit) {
   CAMLparam1(unit);
   DWORD read;
   char buf[1024];
   CAMLlocal1( ml_data );
   ReadFile(pipe, buf, 1024, &read, NULL);
   ml_data = caml_alloc_string(read);
   memcpy(String_val(ml_data), buf, read);
   CAMLreturn(ml_data);
}

#else

int client_sock;

CAMLprim value c_client_connect(value v) {
   CAMLparam1(v);
   struct sockaddr_un addr;
   int res;
   unsigned namelen = caml_string_length(v);
   addr.sun_family = AF_UNIX;
   memcpy(addr.sun_path, String_val(v), namelen + 1);
   client_sock = socket(AF_UNIX, SOCK_STREAM, 0);
   res = connect(client_sock, (struct sockaddr*) &addr, sizeof(struct sockaddr_un));
   if (res == -1) {
     printf("connection failed : %d\n", errno);
     exit(1);
   }
   CAMLreturn(Val_unit);
}

CAMLprim value c_client_disconnect(value unit) {
   CAMLparam1(unit);
   close(client_sock);
   CAMLreturn(Val_unit);
}


CAMLprim value c_send_request_string(value v) {
   CAMLparam1(v);
   char *msg;
   ssize_t to_write, pointer;
   ssize_t res;
   msg = String_val(v);
   to_write = caml_string_length(v);
   pointer = 0;
   while (pointer < to_write) {
      res = write(client_sock, msg + pointer, to_write - pointer);
      if (res == -1) {
        break;
      }
      pointer += res;
   }
   CAMLreturn(Val_unit);
}

CAMLprim value c_read_from_client(value unit) {
   CAMLparam1(unit);
   ssize_t have_read;
   char buf[1024];
   CAMLlocal1( ml_data );
   have_read = read(client_sock, buf, 1024);
   ml_data = caml_alloc_string(have_read);
   memcpy(String_val(ml_data), buf, have_read);
   CAMLreturn(ml_data);
}
#endif
