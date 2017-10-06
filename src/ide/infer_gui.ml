open Why3
open Domain

module Make(Win: sig
    val tools_window_vbox_pack: GObj.widget -> unit
    val set_infer: bool -> int -> (module DOMAIN)-> unit
  end) = struct

  let ai_frame =
    GBin.frame ~label:"Abstract Interpretation" ~shadow_type:`ETCHED_OUT
      ~packing:Win.tools_window_vbox_pack ()

  let ai_box =
    GPack.button_box `VERTICAL ~border_width:2 ~spacing:2
      ~packing:ai_frame#add ()

  let () =
    let desc = "Use abstract interpretation to infer <i>while</i> and <i>for</i> loop invariants." in
    let b = GButton.toggle_button ~packing:ai_box#add
        ~label:"Infer" ()
    in
    b#misc#set_tooltip_markup desc;
    let poly = GButton.radio_button ~packing:ai_box#add ~label:"Polyhedra" () in
    let oct = GButton.radio_button ~group:poly#group ~packing:ai_box#add ~label:"Octogons" () in
    let _box = GButton.radio_button ~group:poly#group ~packing:ai_box#add ~label:"Intervals" () in
    let none = GButton.radio_button ~packing:ai_box#add ~label:"Base domain" () in
    let disj = GButton.radio_button ~group:none#group ~packing:ai_box#add ~label:"Disjunctions" () in
    let trace = GButton.radio_button ~group:disj#group ~packing:ai_box#add ~label:"Trace partitioning" () in
    let widening = GRange.scale ~packing:ai_box#add `HORIZONTAL () in
    let adj = widening#adjustment in
    widening#set_digits 0;
    adj#set_lower 1.0;
    adj#set_upper 51.0;
    adj#set_page_increment 1.0;
    adj#set_page_size 1.0;
    adj#set_step_increment 1.0;
    adj#set_value 5.0;
    let callback () =
      let d =
        if poly#active then
          (module Domain.Polyhedra: DOMAIN)
        else if oct#active then
          (module Domain.Oct:DOMAIN)
        else
          (module Domain.Box:DOMAIN)
      in
      let d =
        if disj#active then
          let module D = (val d: DOMAIN) in
          (module Disjunctive_domain_fast.Make(D) : DOMAIN)
        else
          d
      in
      Win.set_infer b#active (int_of_float adj#value) d;
    in
    let _ = b#connect#toggled ~callback in
    ()

end
