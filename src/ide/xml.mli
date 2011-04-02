

type element =
    { name : string;
      attributes : (string * string) list;
      elements : element list;
    }

val from_file : string -> element list


