
(* State *)
(* ************************************************************************ *)

type state = {

  (* Current terminal *)
  mutable term : Notty_unix.Term.t option;

  (* Current cursor. *)
  mutable cursor_row : int;   (* printed line of the cursor *)
  mutable cursor_col : int;   (* printed column of the cursor *)
  mutable cursor_log : Logs.t option;

  (* Opened sections *)
  mutable section_row : int;  (* starting log index *)
  mutable section_num : int;  (* number of opened section panels *)
  mutable section_col : int;  (* starting index of sectiosn to print in the
                                 [section_tbl] array. *)
  section_tbl : Section.t CCVector.vector;
  (** Sections opened for printing. *)

  mutable overlay : Notty.image;
}

let st = {
  term = None;

  cursor_row = 0;
  cursor_col = 0;
  cursor_log = None;

  section_row = 0;
  section_num = 2;
  section_col = 0;
  section_tbl = CCVector.make 2 Section.root;

  overlay = Notty.I.empty;
}

(* Helpers *)
(* ************************************************************************ *)

let bg_pad bg img (w, h) =
  Notty.I.(img </> char bg ' ' w h)

let sized (w, h) img =
  let w' = Notty.I.width img in
  let h' = Notty.I.height img in
  Notty.I.pad ~r:(w - w') ~b:(h - h') img

let first_line s =
  match CCString.Split.left ~by:"\n" s with
  | Some (res, _) -> res
  | None -> s

(* Colors *)
(* ************************************************************************ *)

let bg_blue = Notty.A.(bg blue ++ fg black ++ st bold)
let bg_black = Notty.A.(bg black ++ fg white ++ st bold)
let bg_yellow = Notty.A.(bg yellow ++ fg white ++ st bold)

(* Header *)
(* ************************************************************************ *)

let render_header w =
  let name = Notty.I.(string bg_blue "Archsat") in
  let count = Notty.I.(string bg_black (
      Format.sprintf "%d messages in logs" (Logs.length ())
    )) in
  Notty.I.(bg_pad bg_blue name (w,1) <->
           bg_pad bg_black count (w,1))

(* Footer *)
(* ************************************************************************ *)

let pad s l =
  assert (String.length s <= l);
  let b = Bytes.make l ' ' in
  Bytes.blit_string s 0 b 0 (String.length s);
  Bytes.unsafe_to_string b

let align_magic l =
  let max = List.fold_left (fun i (_, s) ->
      max i (String.length s)) 0 l + 1 in
  List.map (fun (x, y) -> (x ^ " ", pad y max)) l

let ctrl_keys = align_magic [
    "Esc/q",      "Quit";
    "Enter",      "Expand";
    "r",          "Run";
  ]

let render_footer w =
  let img =
    List.fold_left (fun i (k, s) ->
        Notty.I.(i <|> string bg_black k <|> string bg_blue s)
      ) Notty.I.empty ctrl_keys in
  bg_pad bg_blue img (w, 1)

(* Body *)
(* ************************************************************************ *)

let rec render_row w line col t j =
  if j >= st.section_num then Notty.I.empty
  else begin
    let bg =
      if line = st.cursor_row && j = st.cursor_col then begin
        st.cursor_log <- if j = col then Some t else None;
        bg_yellow
      end else
        bg_black
    in
    let msg =
      if j = col then first_line t.Logs.msg else " - "
    in
    Notty.I.(sized (w - 1, 1) (string bg msg)
             <|> char bg_black '|' 1 1
             <|> render_row w line col t (j + 1))
  end

let render_line w i j t =
  Notty.I.(
    string bg_black (Format.sprintf "%8.3f " (Time.time_of_clock t.Logs.time))
    <|> char bg_black '|' 1 1
    <|> render_row w i j t 0)


let rec render_lines p (w, h) acc line i =
  if line >= h then acc
  else if i >= Logs.length () then
    Notty.I.(acc <-> void 0 (h - line))
  else begin
    let t = Logs.get i in
    let j = p t in
    if j < 0 then render_lines p (w, h) acc line (i + 1)
    else begin
      let acc' = Notty.I.(acc <-> render_line w line j t) in
      render_lines p (w, h) acc' (line + 1) (i + 1)
    end
  end

let rec render_top_row w j =
  if j >= st.section_num then Notty.I.empty
  else begin
    let section = CCVector.get st.section_tbl (st.section_col + j) in
    Notty.I.(
      sized (w - 1, 1) (string bg_black (Section.short_name section))
      <|> char bg_black '|' 1 1
      <|> render_top_row w (j + 1))
  end

let render_top_line w =
  Notty.I.(
    void 9 1
    <|> char bg_black '|' 1 1
    <|> render_top_row w 0)

let render_body (w, h) =
  let filter t =
    let rec aux i t =
      if i >= st.section_num then -1
      else begin
        let s = CCVector.get st.section_tbl i in
        if Section.equal t.Logs.section s
        then i else aux (i + 1) t
      end
    in aux 0 t
  in
  let w' = (w - 10) / st.section_num in
  Notty.I.(
    render_top_line w' <->
    char bg_black '-' w 1 <->
    render_lines filter (w', h - 2) Notty.I.empty 0 st.section_row
  )

(* Rendering *)
(* ************************************************************************ *)

let render term =
  let (w, h) = Notty_unix.Term.size term in
  (* Render header&footer *)
  let header = render_header w in
  let footer = render_footer w in
  (* Compute sizes *)
  let header_h = Notty.I.height header in
  let footer_h = Notty.I.height footer in
  (* Render body *)
  let body_h = h - header_h - footer_h - 2 in
  let body = render_body (w, body_h) in
  (* assert (Notty.I.height body = body_h); *)
  let img = Notty.I.(
      header <-> void 0 1 <->
      body <-> void 0 1 <->
      footer
    ) in
  Notty_unix.Term.image term img

(* Updating the state *)
(* ************************************************************************ *)

let update event = ()

(* Main loop *)
(* ************************************************************************ *)

let init () =
  st.term <- Some (Notty_unix.Term.create ~mouse:false ())

let rec loop term =
  match Notty_unix.Term.event term with
  | `Key (`Escape, _)
  | `Key (`Uchar 113, _) (* 'q' *) ->
    exit 0
  | `Key (`Uchar 114, _) (* 'r' *) as event ->
    update event;
    ()
  | event ->
    update event;
    refresh term

and refresh term =
  render term;
  loop term

let rec display () =
  match st.term with
  | None -> init (); display ()
  | Some term -> refresh term


