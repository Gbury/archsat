
(* State *)
(* ************************************************************************ *)

type state = {

  (* Current terminal *)
  mutable term : Notty_unix.Term.t option;

  (* Current cursor. *)
  mutable cursor_row : int;   (* printed line of the cursor *)
  mutable cursor_col : int;   (* printed column of the cursor *)

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

  section_row = 0;
  section_num = 1;
  section_col = 0;
  section_tbl = CCVector.create ();

  overlay = Notty.I.empty;
}

(* Helpers *)
(* ************************************************************************ *)

let bg_pad bg img (w, h) =
  Notty.I.(img </> char bg ' ' w h)

let sized img (w, h) =
  let w' = Notty.I.height img in
  let h' = Notty.I.width img in
  Notty.I.pad ~r:(w - w') ~b:(h - h') img

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
      Format.sprintf ""
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

let render_panel_aux col acc i x =
  let bg =
    if col = st.cursor_col && i = st.cursor_row
    then bg_yellow else bg_black
  in
  match x with
  | None -> Notty.I.(acc <-> string bg " - ")
  | Some s -> Notty.I.(acc <-> string bg s)

let render_panel (w, h) col (section, a) =
  let img = CCArray.foldi (render_panel_aux col) Notty.I.empty a in
  Notty.I.(string bg_black (Section.full_name section) <->
           char bg_black '-' w 1 <-> img)

let render_body (w, h) =
  let time, panels = compute_panels (h - 2) in
  let w = w / st.section_num - 1 in
  let img =
    CCArray.foldi (fun acc i panel ->
        Notty.I.(acc <|> char bg_black ' ' 1 h <|> render_panel (w, h) i panel)
      ) (render_time time) panels in
  img

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
  assert (Notty.I.height body = body_h);
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
  | `Key (`Escape, _) -> exit 0
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


