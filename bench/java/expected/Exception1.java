/* This file has been extracted from module Exception1. */
public class Exception1 extends Exception {

  public final int value;
  public final boolean d;
  public final boolean equals(Object obj) {
    
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (!(this.getClass() == obj.getClass())) {
      return false;
    }
    
    Exception1 other = (Exception1) obj;
    if (!(this.value == other.value)) {
      return false;
    }
    if (!(this.d == other.d)) {
      return false;
    }
    return true;
    
  }
  public final int hashCode() {
    int hashValue = 1;
    hashValue = 31 * hashValue + this.value;
    hashValue = 31 * hashValue + (this.d ? 1 : 0);
    return hashValue;
  }
  
  
  
  public Exception1(int i) {
    
    this.value = i;
    this.d = false;
  }
  
  
}
