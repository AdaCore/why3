/* This file has been extracted from module MutRec. */
import java.util.Random;

import java.util.Arrays;

public class MutRec {

  public static boolean even(int number) {
    
    if (number == 0) {
      return true;
    } else if (number < 0) {
      return odd (number + 1);
    } else {
      return odd (number - 1);
    }
    
  }
  public static boolean odd(int number1) {
    
    if (number1 == 0) {
      return false;
    } else if (number1 < 0) {
      return MutRec.even(number1 + 1);
    } else {
      return MutRec.even(number1 - 1);
    }
    
  }
  
  public static void main(String [] us) {
    
    try {
      
      Random rnd = (new Random());
      for (int i = 0; i <= 100; i++) {
        
        int b = rnd.nextInt(72);
        if (b % 2 == 0 && MutRec.odd(b) || b % 2 == 1 && MutRec.even(b)) {
          throw new ArithmeticException ();
        }
        
      }
      
    } catch (IllegalArgumentException eX) {
      throw new RuntimeException("unreachable statement");
    }
    catch (ArithmeticException eX) {
    throw new RuntimeException("unreachable statement");
    }
  }
  
  
}
