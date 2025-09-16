/* This file has been extracted from module ExceptionThrow. */
import java.util.NoSuchElementException;
public class ExceptionThrow {

  public static int func(int i) throws IndexOutOfBoundsException,
                               NoSuchElementException, Exception1, Exception2 {
    
    if (i == 0) {
      throw new Exception1(i);
    }
    if (i == 1) {
      throw new Exception2(i);
    }
    if (i == 2) {
      throw new IndexOutOfBoundsException ();
    }
    if (i == 3) {
      throw new NoSuchElementException ();
    }
    return i;
  }
  
  
}
