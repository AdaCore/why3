/* This file has been extracted from module Unreachable. */
public class Unreachable {

  public static int return1972() {
    int i = 0;
    while (true) {
      if (i == 1972) {
        return i;
      }
      i = i + 1;
    }
    throw new RuntimeException("unreachable statement");
  }
  
  
}
