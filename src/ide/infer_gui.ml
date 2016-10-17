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
    let iter (name,desc,strat,k) =
      let b = GButton.toggle_button ~packing:ai_box#add
          ~label:name ()
      in
      (*b#misc#set_tooltip_markup (string_of_desc (name,desc));
      let i = GMisc.image ~pixbuf:(!image_transf) () in
      let () = b#set_image i#coerce in
      let callback () = apply_strategy_on_selection strat in
      let (_ : GtkSignal.id) = b#connect#pressed ~callback in*)
      let callback () =
        Win.set_infer b#active;
      in
      let _ = b#connect#toggled ~callback in
      ()
    in
    List.iter iter ["Infer", "Use abstract interpretation to infer <i>while</i> and <i>for</i> loop invariants.", None, None]

end
