
(* State *)
(* ************************************************************************ *)

type 'a selection = {
  choices : 'a array;
  mutable idx : int;
}

type overlay =
  | Empty
  | Log of Logs.t
  | SSelection of Section.t selection

type state = {

  (* Current terminal *)
  mutable term : Notty_unix.Term.t option;

  (* Current cursor. *)
  mutable cursor_row : int;   (* printed line of the cursor *)
  mutable cursor_col : int;   (* printed column of the cursor *)
  mutable cursor_log : Logs.t option;

  (* Panel numbers *)
  mutable panel_cols : int;  (* number of opened section panels *)
  mutable panel_rows : int;  (* number of lines displayed in each panel *)

  (* Opened sections *)
  mutable section_row : int;  (* starting log index *)
  mutable section_col : int;  (* starting index of sectiosn to print in the
                                 [section_tbl] array. *)
  section_tbl : Section.t CCVector.vector;
  (** Sections opened for printing. *)

  mutable overlay : overlay;
}

let st = {
  term = None;

  cursor_row = 0;
  cursor_col = 0;
  cursor_log = None;

  panel_cols = 1;
  panel_rows = 0;

  section_row = 0;
  section_col = 0;
  section_tbl = CCVector.return Section.root;

  overlay = Empty;
}

(* Colors *)
(* ************************************************************************ *)

let bg_blue = Notty.A.(bg blue ++ fg black ++ st bold)
let bg_black = Notty.A.(bg black ++ fg white ++ st bold)
let bg_yellow = Notty.A.(bg yellow ++ fg white ++ st bold)

(* Helpers *)
(* ************************************************************************ *)

let bg_pad bg img (w, h) =
  Notty.I.(img </> char bg ' ' w h)

let sized (w, h) img =
  let w' = Notty.I.width img in
  let h' = Notty.I.height img in
  Notty.I.pad ~r:(w - w') ~b:(h - h') img

let centered (w, h) img =
  let w' = (w - Notty.I.width img) / 2 in
  let h' = (h - Notty.I.height img) / 2 in
  Notty.I.pad ~l:w' ~r:w' ~t:h' ~b:h' img

let bordered img =
  let w = Notty.I.width img in
  let h = Notty.I.height img in
  let line = Notty.I.(
      char bg_black '+' 1 1 <|>
      char bg_black '-' w 1 <|>
      char bg_black '+' 1 1) in
  let col = Notty.I.(char bg_black '|' 1 h) in
  Notty.I.
    (line <-> (col <|> (img </> char bg_black ' ' w h) <|> col) <-> line)

let first_line s =
  match CCString.Split.left ~by:"\n" s with
  | Some (res, _) -> res
  | None -> s

let table a =
  let widths =
    Array.init (Array.length a.(0)) (fun i ->
        let r = ref 0 in
        for j = 0 to Array.length a - 1 do
          r := max !r (Notty.I.width a.(j).(i))
        done;
        !r)
  in
  Array.fold_left (fun acc l ->
      let h = Array.fold_left (fun acc img ->
          max acc (Notty.I.height img)) 0 l in
      let line = CCArray.foldi (fun acc i img ->
          Notty.I.(acc <|> void 2 1 <|> sized (widths.(i), h) img)
        ) Notty.I.empty l in
      Notty.I.(acc <-> line)
    ) Notty.I.empty a

let strings bg msg =
  let l = CCString.lines msg in
  List.fold_left (fun acc s ->
      Notty.I.(acc <-> string bg s)) Notty.I.empty l

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
  if j >= st.panel_cols then Notty.I.empty
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
  if line >= h then begin
    st.panel_rows <- line;
    acc
  end else if i >= Logs.length () then begin
    st.panel_rows <- line;
    Notty.I.(acc <-> void 0 (h - line))
  end else begin
    let t = Logs.get i in
    let j = p t in
    if j < 0 then render_lines p (w, h) acc line (i + 1)
    else begin
      let acc' = Notty.I.(acc <-> render_line w line j t) in
      render_lines p (w, h) acc' (line + 1) (i + 1)
    end
  end

let rec render_top_row w j =
  if j >= st.panel_cols then Notty.I.empty
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
      if i >= st.panel_cols then -1
      else begin
        let s = CCVector.get st.section_tbl i in
        if Section.equal t.Logs.section s
        then i else aux (i + 1) t
      end
    in aux 0 t
  in
  let w' = (w - 10) / st.panel_cols in
  Notty.I.(
    render_top_line w' <->
    char bg_black '-' w 1 <->
    render_lines filter (w', h - 2) Notty.I.empty 0 st.section_row
  )

(* Rendering overlays *)
(* ************************************************************************ *)

let render_log (w, h) t =
  let open Notty.I in
  centered (w, h) @@ bordered @@ pad ~l:1 ~r:1 ~t:1 ~b:1 @@
  table [|
    [| string bg_black "Time";
       string bg_black (Format.sprintf "%.3f" (Time.time_of_clock t.Logs.time))|];
    [| string bg_black "Level";
       string bg_black (Level.to_string t.Logs.lvl) |];
    [| string bg_black "Section";
       string bg_black (Section.full_name t.Logs.section) |];
    [| string bg_black "Message";
       strings bg_black t.Logs.msg |]
  |]

let render_sselection (w, h) s =
  let img = CCArray.foldi (fun acc i section ->
      let bg = if i = s.idx then bg_yellow else bg_black in
      Notty.I.(acc <-> string bg (Section.full_name section))
    ) Notty.I.empty s.choices in
  centered (w, h) @@ bordered @@ Notty.I.pad ~l:1 ~r:1 ~t:1 ~b:1 @@ img

let render_overlay (w, h) =
  match st.overlay with
  | Empty -> Notty.I.empty
  | Log t -> render_log (w, h) t
  | SSelection s -> render_sselection (w, h) s

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
  let overlay = render_overlay (w, h) in
  let img = Notty.I.(
      overlay </> (
        header <-> void 0 1 <->
        body <-> void 0 1 <->
        footer
      )) in
  Notty_unix.Term.image term img

(* Updating the state *)
(* ************************************************************************ *)

let move_cursor = function
  | `Up ->
    if st.cursor_row > 0 then
      st.cursor_row <- st.cursor_row - 1
  | `Down ->
    if st.cursor_row < st.panel_rows - 1 then
      st.cursor_row <- st.cursor_row + 1
  | `Left ->
    if st.cursor_col > 0 then
      st.cursor_col <- st.cursor_col - 1
  | `Right ->
    if st.cursor_col < st.panel_cols - 1 then
      st.cursor_col <- st.cursor_col + 1

let init_sselection () =
  Empty

let update (w, h) mods = function
  | `Escape
  | `Uchar 113 (* 'q' *) ->
    `Exit
  | `Uchar 114 (* 'r' *) ->
    `Stop
  | `Uchar 99 (* 'c' *) ->
    st.overlay <- init_sselection ();
    `Continue
  | `Arrow dir ->
    move_cursor dir;
    `Continue
  | `Enter ->
    begin match st.cursor_log with
      | None -> ()
      | Some t -> st.overlay <- Log t
    end;
    `Continue
  | _ ->
    `Continue

let update_log (w, h) mods = function
  | _ -> `Clear

let update_sselection s = function
  | `Arrow `Up ->
    if s.idx > 0 then s.idx <- s.idx - 1;
    `Continue
  | `Arrow `Down ->
    if s.idx < Array.length s.choices - 1 then
      s.idx <- s.idx + 1;
    `Continue
  | `Enter ->
    let s = s.choices.(s.idx) in
    CCVector.set st.section_tbl st.section_col s;
    `Clear
  | _ ->
    `Continue

let react (w, h) mods key =
  match st.overlay with
  | Empty -> update (w, h) mods key
  | Log _ -> update_log (w, h)  mods key
  | SSelection s -> update_sselection s key

(* Main loop *)
(* ************************************************************************ *)

let init () =
  st.term <- Some (Notty_unix.Term.create ~mouse:false ())

let rec loop term =
  match Notty_unix.Term.event term with
  | `End -> ()
  | `Key (k, mods) ->
    begin match react (Notty_unix.Term.size term) mods k with
      | `Stop -> ()
      | `Exit -> exit 0
      | `Clear ->
        st.overlay <- Empty;
        refresh term
      | `Continue -> refresh term
    end
  | `Mouse _ -> loop term
  | `Resize _ -> refresh term

and refresh term =
  render term;
  loop term

let rec display () =
  match st.term with
  | None -> init (); display ()
  | Some term -> refresh term


