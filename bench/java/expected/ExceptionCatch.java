/* This file has been extracted from module ExceptionCatch. */
import java.util.NoSuchElementException;
public class ExceptionCatch {

  public static int noRaise(int i) throws Exception1 {
    
    try {
      return ExceptionThrow.func(i);
    } catch (IndexOutOfBoundsException eX) {
      return i;
    } catch (NoSuchElementException eX) {
      return i;
    }
    catch (Exception2 us) {
    throw new RuntimeException("unreachable statement");
    }
  }
  
  
}
