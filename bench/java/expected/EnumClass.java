/* This file has been extracted from module EnumClass. */
public class EnumClass {

  public enum KindOfT
  {
     SOME_KIND,
     ANOTHER_KIND,
     SOME_OTHER_SORT
  }
  
  public final KindOfT kind;
  public final int dummyValue;
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
    
    EnumClass other = (EnumClass) obj;
    if (!(this.kind == other.kind)) {
      return false;
    }
    if (!(this.dummyValue == other.dummyValue)) {
      return false;
    }
    return true;
    
  }
  public final int hashCode() {
    int hashValue = 1;
    hashValue = 31 * hashValue + this.kind.hashCode();
    hashValue = 31 * hashValue + this.dummyValue;
    return hashValue;
  }
  
  public EnumClass() {
    
    this.kind = KindOfT.SOME_OTHER_SORT;
    this.dummyValue = 0;
  }
  
  public KindOfT getKind() {
    
    return this.kind;
  }
  
  public int getIntegerKind() {
    
    if (this.kind == KindOfT.SOME_KIND) {
      return 1;
    } else if (this.kind == KindOfT.ANOTHER_KIND) {
      return 0;
    } else {
      return 2;
    }
    
  }
  
  
}
