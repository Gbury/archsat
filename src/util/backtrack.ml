
type 'a t = {
  stack : 'a Vector.t;
  mutable current : 'a;
}

type level = int

let base s = {
  stack = Vector.make 10 s;
  current = s;
}

let top st = st.current

let update st f = st.current <- f st.current

let current_level st =
  Vector.push st.stack st.current;
  Vector.size st.stack

let backtrack st level =
  if level < Vector.size st.stack then begin
    st.current <- Vector.get st.stack (level - 1);
    Vector.shrink st.stack (Vector.size st.stack - level - 1)
  end
