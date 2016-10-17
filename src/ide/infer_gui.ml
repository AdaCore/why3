module Make(Win: sig
    val tools_window_vbox_pack: GObj.widget -> unit
    val set_infer: bool -> unit
  end) = struct

  let ai_frame =
    GBin.frame ~label:"Abstract Interpretation" ~shadow_type:`ETCHED_OUT
      ~packing:Win.tools_window_vbox_pack ()

  let ai_box =
    GPack.button_box `VERTICAL ~border_width:5 ~spacing:5
      ~packing:ai_frame#add ()

  let () =
    let desc = "Use abstract interpretation to infer <i>while</i> and <i>for</i> loop invariants." in
    let b = GButton.toggle_button ~packing:ai_box#add
        ~label:"Infer" ()
    in
    b#misc#set_tooltip_markup desc;
    let callback () =
      Win.set_infer b#active;
    in
    let _ = b#connect#toggled ~callback in
    ()

end
