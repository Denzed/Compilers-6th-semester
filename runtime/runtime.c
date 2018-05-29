/* Runtime library */

# include <stdio.h>

/* read is an implementation of the "read" construct */
extern int read () {
  int result;

  printf ("> "); 
  fflush (stdout);
  scanf  ("%d", &result);

  return result;
}

/* write is an implementation of the "write" construct */
extern int write (int n) {
  printf ("%d\n", n);
  fflush (stdout);

  return 0;
}
