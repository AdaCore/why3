

type element =
    { name : string;
      attributes : (string * Why.Rc.rc_value) list;
      elements : element list;
    }

val from_file : string -> element list


