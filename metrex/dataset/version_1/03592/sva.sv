// SVA for fsm_vending_machine
module fsm_vending_machine_sva;
  default clocking cb @(posedge clk); endclocking

  // Sanity
  a_state_known:   assert property (!$isunknown(state));
  a_outputs_known: assert property (!$isunknown({dispense_item, return_coin}));
  a_state_valid:   assert property (state inside {IDLE, ITEM_SELECTED, ITEM_DISPENSED});
  a_reset_to_idle: assert property (reset |-> state == IDLE);

  // Output decode
  a_out_idle: assert property (disable iff (reset) (state==IDLE)          |-> (!dispense_item && !return_coin));
  a_out_sel:  assert property (disable iff (reset) (state==ITEM_SELECTED)  |-> ( dispense_item && !return_coin));
  a_out_disp: assert property (disable iff (reset) (state==ITEM_DISPENSED) |-> (!dispense_item &&  return_coin));
  a_no_both:  assert property (!(dispense_item && return_coin));

  // Transition relation
  a_idle_to_sel: assert property (disable iff (reset)
                                  (state==IDLE && coin_inserted && (item_selected != 2'b00)) |=> state==ITEM_SELECTED);
  a_idle_stay:   assert property (disable iff (reset)
                                  (state==IDLE && !(coin_inserted && (item_selected != 2'b00))) |=> state==IDLE);

  a_sel_to_disp: assert property (disable iff (reset)
                                  (state==ITEM_SELECTED && item_dispensed) |=> state==ITEM_DISPENSED);
  a_sel_stay:    assert property (disable iff (reset)
                                  (state==ITEM_SELECTED && !item_dispensed) |=> state==ITEM_SELECTED);

  a_disp_to_idle: assert property (disable iff (reset) (state==ITEM_DISPENSED) |=> state==IDLE);

  // Forbid one-step illegal jumps
  a_no_idle_to_disp: assert property (disable iff (reset) (state==IDLE)          |=> state!=ITEM_DISPENSED);
  a_no_sel_to_idle:  assert property (disable iff (reset) (state==ITEM_SELECTED) |=> state!=IDLE);

  // Coverage
  c_state_idle: cover property (state==IDLE);
  c_state_sel:  cover property (state==ITEM_SELECTED);
  c_state_disp: cover property (state==ITEM_DISPENSED);

  c_idle_to_sel:  cover property (disable iff (reset)
                                  (state==IDLE && coin_inserted && item_selected!=2'b00) ##1 state==ITEM_SELECTED);
  c_sel_to_disp:  cover property (disable iff (reset)
                                  (state==ITEM_SELECTED && item_dispensed) ##1 state==ITEM_DISPENSED);
  c_disp_to_idle: cover property (disable iff (reset) (state==ITEM_DISPENSED) ##1 state==IDLE);

  c_full_vend: cover property (
    reset ##1 state==IDLE
    ##[1:$] (coin_inserted && item_selected!=2'b00) ##1 (state==ITEM_SELECTED && dispense_item)
    ##[1:$] item_dispensed ##1 (state==ITEM_DISPENSED && return_coin) ##1 state==IDLE
  );

  c_item01: cover property (disable iff (reset)
                            (state==IDLE && coin_inserted && item_selected==2'b01) ##1 state==ITEM_SELECTED);
  c_item10: cover property (disable iff (reset)
                            (state==IDLE && coin_inserted && item_selected==2'b10) ##1 state==ITEM_SELECTED);
  c_item11: cover property (disable iff (reset)
                            (state==IDLE && coin_inserted && item_selected==2'b11) ##1 state==ITEM_SELECTED);
endmodule

bind fsm_vending_machine fsm_vending_machine_sva sva_inst();