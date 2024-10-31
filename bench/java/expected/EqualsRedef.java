/* This file has been extracted from module EqualsRedef. */
public class EqualsRedef {

  public int a;
  public boolean b;
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
    
    EqualsRedef other = (EqualsRedef) obj;
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
    hashValue = 31 * hashValue + this.a;
    hashValue = 31 * hashValue + (this.b ? 1 : 0);
    return hashValue;
  }
  
  public boolean equals(EqualsRedef obj) {
    
    if (this.a == obj.a) {
      if (this.b) {
        return obj.b;
      } else {
        return !obj.b;
      }
    } else {
      return false;
    }
  }
  
  
}
