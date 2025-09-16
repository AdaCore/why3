/* This file has been extracted from module UnreachableFixed. */
public class UnreachableFixed {

  public static int return1972() {
    int i = 0;
    int j = 1;
    while (j > 0) {
      if (i == 1972) {
        return i;
      }
      i = i + 1;
    }
    throw new RuntimeException("unreachable statement");
  }
  
  
}
