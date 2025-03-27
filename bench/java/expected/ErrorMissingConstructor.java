/* This file has been extracted from module ErrorMissingConstructor. */
public class ErrorMissingConstructor {

  public final boolean a;
  public final boolean b;
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
    
    ErrorMissingConstructor other = (ErrorMissingConstructor) obj;
    if (!(this.a == other.a)) {
      return false;
    }
    if (!(this.b == other.b)) {
      return false;
    }
    return true;
    
  }
  public final int hashCode() {
    int hashValue = 1;
    hashValue = 31 * hashValue + (this.a ? 1 : 0);
    hashValue = 31 * hashValue + (this.b ? 1 : 0);
    return hashValue;
  }
  
  
}
