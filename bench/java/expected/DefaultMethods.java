/* This file has been extracted from module DefaultMethods. */
import java.util.Arrays;

public class DefaultMethods {

  public int a;
  public ClassA c;
  public boolean [] [] b;
  public String d;
  public boolean z;
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
    
    DefaultMethods other = (DefaultMethods) obj;
    if (!(this.a == other.a)) {
      return false;
    }
    if (!(this.c == null ? other.c == null : this.c.equals(other.c))) {
      return false;
    }
    if (!(this.b).equals(other.b)) {
      return false;
    }
    if (!(this.d == null ? other.d == null : this.d.equals(other.d))) {
      return false;
    }
    if (!(this.z == other.z)) {
      return false;
    }
    return true;
    
  }
  public final int hashCode() {
    int hashValue = 1;
    hashValue = 31 * hashValue + this.a;
    hashValue = 31 * hashValue + (this.c == null ? 0 : this.c.hashCode());
    hashValue = 31 * hashValue + (this.b == null ? 0 : (this.b).hashCode());
    hashValue = 31 * hashValue + (this.d == null ? 0 : this.d.hashCode());
    hashValue = 31 * hashValue + (this.z ? 1 : 0);
    return hashValue;
  }
  
  
}
