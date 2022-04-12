
Specifications of ``whyml2java``

Integers
========

Several choices below.
Can be selected as compilation options.

- (hard) refuse to convert whyml using int in arbitrary precision
  - pros: simplicity
  - cons:
    - few projects can be converted / projects should be rewritten using mach.int.Int32 or mach.int.Int64
    - semantic of mach.int.Int32: no arithmetic overfow allowed at all.
    - Problem with length of whyml lists.

- (medium) perform all arithmetical operations with Math.exact, and interrupt the program with ArithmeticException in case of overflow
  - example
  - .. code-block:: java

      long a = Long.MAX_VALUE;
      long z = Math.multiplyExact(a,a);

  - pros: 
    - simplicity.
  - cons: 
    - exception stopping the execution at runtime. ok for parcoursup, not for Ariane 5
  
- (soft) use an arbitrary precision arithmetic library (e.g.: java.math.BigInteger)
  - example
  - .. code-block:: java
					
    BigInteger a = new BigInteger(a);
    BigInteger z = BigInteger.multiply(a,a);

  - pros: 
    - simple
    - mach.int.Int32 still converted to int
  - cons: 
    - heavy code / performance

- (very soft) don't care, convert to int and cross fingers
  - pros: ultrasimple
  - cons: loss of security garantees
  

Class creation from a module with annotation  'single_class'
____________________________________________________________

Creates a unique class named like the module.
At most one type definition in the module is allowed.

.. code-block:: whyml

  module MyModule [@java_pkg:fr.labri.example, @java:single_class]
  use mach.int.Int32

  type my_type = {
    my_mutable_int: ref int32;
  } by {
	my_mutable_int <- 0;
  }

  let function my_fun (self : my_type) (b : int32) =
    self.my_mutable_int <- b

	let function my_fun2 (a : int32) (b : int32) : int32 =
	  a+b


Generates a directory ``fr/labri/example/`` containing a file ``MyModule.java`` whose content is:

.. code-block:: java

	package fr.labri.example;

	public class MyModule {

		public myMutableInt int;

		public MyModule() {
			myMutableInt = 0;
		}

		public MyModule(int myMutableInt) {
			this.myMutableInt = myMutableInt;
		}

		public void myFun(int b) {
			this.myMutableInt = b;
		}

		public static int myFun2(int a, int b) {
			return a + b;
		}
	}

Remark: we forget the ``my_type`` identifier when converting to java.


Default processing of modules, without any specific annotation
______________________________________________________________

The conversion creates:
- one static class named like the module
- one class per type defined in the module
  
Functions of the module become static methods of the static class,
except for those annotated by the ``non_static`` label.


Example with record types:

.. code-block:: whyml

	module MyModule [@java_pkg:fr.labri.example]
  		use mach.int.Int32

		type my_type = {
    		my_unmutable_int: int32;
			my_mutable_int: ref int32;
			my_unitialized_int: int32;
			ghost my_ghost_int: int;
		} by {
			my_unmutable_int = 0;
			!my_mutable_int = 0;
		}

		let function my_fun [@java: non_static] (self : my_type) (b : int32) =
			self.my_mutable_int <- b

		let function my_fun2 (a : int32) (b : int32) : int32 =
			0

		let function my_fun3 (a : int32) (b : int32) =
			{my_unmutable_int  = a,  my_mutable_int = ref 1, my_unitialized_int = b, my_ghost_int = b }

		type my_type2 = {
			my_unmutable_int: int32;
		}

		let function my_fun4 (a : my_type2) (b : int32) = ()


generates a directory ``fr/labri/example/mymodule/`` containing three files
 ``MyType.java`` and ``MyType2.java`` and ``MyModule.java``
whose content is repectively

.. code-block:: java

	//type my_type from module MyModule generated from file ....
	package fr.labri.example.mymodule;

	public class MyType {

		public final myUnmutableInt int;

		public myMutableInt int;

		public final myUnitializedInt int;

		public MyType() {
			this.myUnmutableInt = 0;
			this.myMutableInt = 0;
		}

		public MyType(int myUnmutableInt, int myMutableInt, int myUnitializedInt) {
			this.myUnmutableInt = myUnmutableInt;
			this.myMutableInt = myMutableInt;
			this.myUnitializedInt = myUnitializedInt;
		}

		//function my_fun annotated with method flag
		public void myFun(int b) {
			this.myMutableInt = b;
		}

	}

and

.. code-block:: java

	//type my_type2 from module MyModule generated from file ....
	package fr.labri.example.mymodule;

	public class MyType2 {

		public final myUnmutableInt int;
	
	}


and

.. code-block:: java

	// module MyModule generated from file ....
	package fr.labri.example.mymodule;

	public class Module {

		//remark: return type inferred, in this case (int)
		public static int myFun2(int a, int b) {
			return 0;
		}

		public static MyType myFun3(int a, int b) {
			return new MyType(a,1,b);
		}

		public static void myFun4(MyType2 a, int b) {

		}

	    //private empty constructor: the class cannot be instantiated
		private Module() {}

	}





Type alias
__________

.. code-block:: whyml

	module MyModule2
		use MyModule.MyType

		type my_type_alias = MyType;

		let function my_fun [@java: non_static] (self : my_type_alias) (b : my_type) =
			self.myMutableInt <- b.myMutableInt


generates a file ``MyTypeAlias.java`` whose content is

.. code-block:: java

	public class MyTypeAlias extends MyType {

		public MyTypeAlias() {
			super();
		}

		public void myFun (MyType b) {
			this.myMutableInt = b.myMutableInt;
		}

	}


Generic Types
_____________

.. code-block:: whyml

	module MyModule3

		type my_type 'a = { mutable length : 'a; };

		let function my_fun [@java: non_static] (self : my_type 'a) (b : 'a) =
			a.length <- b
	end

	module MyModule4
		use MyModule3

		type my_type_alias = my_type int32;

		let function my_fun [@java: non_static] (a : my_type_alias) (b c : int32) =
			Module3.my_fun a (b+c)
	end

generates two files ``MyModule3.java`` and ``MyModule4.java``

.. code-block:: java

	package ...mymodule3;

	class MyType<T> {
		public T length;

		public MyType(T length) {
			this.length = length;
		}

		public myFun (T b) {
			this.length = b;
		}
	 }

.. code-block:: java

	package ...mymodule4;

	class MyTypeAlias extends MyType<int> {
		public MyTypeAlias(int length) {
			super (length);
		}

		public myFun (int b, int c) {
			super.myFun(b+c);
		}
	 }

Processing arrays and maps
__________________________

.. code-block:: whyml

	module MyModule [@java_pkg:fr.labri.example, @java:single_class]
		use mach.int.Int32

	type my_type 'a = { mutable my_array : array 'a, mutable my_map : map int32 'a }


generates a file `MyModule.java` in the directory `fr/labri/example/` with the following content.
Types array and maps are by default converted to ``ArrayList``and ``HashMap``.

.. code-block:: java

	package fr.labri.example;

	public class MyModule<T> {

		public final myArray List<T>;

		public final myMap Map<Integer,T>;

		public MyModule() {
			this.myArray = new ArrayList<T>();
			this.myMap = new HashMap<Integer,T>();
		}

		public MyModule(List<T> myArray, Map<Integer,T> myMap) {
			this.myArray = myArray;
			this.myMap = myMap;
		}

	}


